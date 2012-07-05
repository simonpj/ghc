%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section[NewDemand]{@NewDemand@: A decoupled implementation of a demand domain}

\begin{code}

module NewDemand (
        LatticeLike,
        StrDmd(..), strBot, strTop, strStr, strProd,
        AbsDmd(..), absBot, absTop, absProd,
        JointDmd(..), mkJointDmd,
	DmdType(..), topDmdType, botDmdType, mkDmdType, mkTopDmdType, 
		dmdTypeDepth, 
	DmdEnv, emptyDmdEnv,
	DmdResult(..), retCPR, isBotRes, returnsCPR, resTypeArgDmd,
        appIsBottom, isBottomingSig, pprIfaceStrictSig, 
	StrictSig(..), mkStrictSig, topSig, botSig, cprSig,
        isTopSig, 	splitStrictSig, increaseStrictSigArity,
     ) where

#include "HsVersions.h"

import StaticFlags
import Outputable
import VarEnv
import UniqFM
import Util
import BasicTypes

\end{code}

%************************************************************************
%*									*
\subsection{Lattice-like structure for domains}
%*									*
%************************************************************************

\begin{code}

class LatticeLike a where
  bot    :: a
  top    :: a
  pre    :: a -> a -> Bool
  lub    :: a -> a -> a 
  both   :: a -> a -> a

-- False < True
instance Lattice Bool where
  bot     = False
  top     = True
  pre x y = (not x) || y
  lub     = (||)
  both    = (&&)


\end{code}


%************************************************************************
%*									*
\subsection{Strictness domain}
%*									*
%************************************************************************

\begin{code}

-- Vanilla strictness domain
data StrDmd
  = HyperStr             -- Hyperstrict 
  | Lazy                 -- Lazy
  | Str                  -- Strict
  | SProd Bool [StrDmd]  -- Possibly deferred roduct or function demand
                         -- False === strict, True === deferred
  deriving ( Eq, Show )


-- Well-formedness preserving constructors for the Strictness domain
strBot, strTop, strStr :: StrDmd
strBot     = HyperStr
strTop     = Lazy
strStr     = Str

strProd :: Bool -> [StrDmd] -> StrDmd
strProd def sx 
  = if all (== Lazy) sx 
      then if def then Lazy else Str
      else if (not def) && (any (== HyperStr) sx) then HyperStr
           else SProd def sx


-- Serialization
instance Outputable StrDmd where
  ppr HyperStr      = char 'B'
  ppr Lazy          = char 'L'
  ppr Str           = char 'S'
  ppr (SProd d sx)  = (char (if d then 'L' else 'S')) <> parens (hcat (map ppr sx))

-- LatticeLike implementation for strictness demands
instance LatticeLike StrDmd where
  bot = HyperStr
  top = Lazy
  
  pre _ Lazy                               = True
  pre HyperStr _                           = True
  pre (SProd False _) Str                  = True
  pre (SProd s1 sx1) (SProd s1 sx2)    
            | s1 `pre` s2 &&    
                length sx1 == length sx2   = all (== True) $ zipWith pre sx1 sx2 
  pre x y                                  = x == y

  lub x y | x == y                         = x 
  lub y x | x `pre` y                      = lub x y
  lub HyperStr s                           = s
  lub _ Lazy                               = absTop
  lub (SProd False _) Str                  = strStr
  lub (SProd d1 sx1) (SProd d2 sx2) 
           | length sx1 == length sx2      = strProd $ d1 `lub` d2 $ zipWith lub sx1 sx2
           | otherwise                     = strStr
  lub _ _                                  = strTop

  both x y | x == y                        = x 
  both y x | x `pre` y                     = both x y
  both HyperStr _                          = strBot
  both s Lazy                              = s
  both s@(SProd False _) Str               = s
  both (SProd d1 sx1) (SProd d2 sx2) 
           | length sx1 == length sx2      = strProd $ d1 `both` d2 $ zipWith both sx1 sx2 
  both _ _                                 = strBot

\end{code}

%************************************************************************
%*									*
\subsection{Absence domain}
%*									*
%************************************************************************

\begin{code}

data AbsDmd
  = Abs                  -- Defenitely unused
  | Used                 -- May be used
  | UProd [AbsDmd]       -- Product
  deriving ( Eq, Show )


-- Serialization
instance Outputable AbsDmd where
  ppr Abs         = char 'A'
  ppr Used        = char 'U'
  ppr (UProd as)  = (char 'U') <> parens (hcat (map ppr as))


-- Well-formedness preserving constructors for the Absence domain
absBot, absTop :: AbsDmd
absBot     = Abs
absTop     = Used

absProd :: [AbsDmd] -> AbsDmd
absProd ux 
  = if all (== Used) ux 
    then Used else UProd ux


instance LatticeLike AbsDmd where
  bot                            = Abs
  top                            = Used
 
  pre Abs _                      = True
  pre _ Used                     = True
  pre (UProd ux1) (UProd ux2)
     | length ux1 == length ux2  = all (== True) $ zipWith pre ux1 ux2 
  pre x y                        = x == y

  lub x y | x == y               = x 
  lub y x | x `pre` y            = lub x y
  lub Abs a                      = a
  lub _ Used                     = absTop
  lub (UProd ux1) (UProd ux2)
     | length ux1 == length ux2  = absProd $ zipWith lub ux1 ux2
  lub _ _                        = absTop

  both                           = lub

\end{code}
  
%************************************************************************
%*									*
\subsection{Joint domain for Strictness and Absence}
%*									*
%************************************************************************

\begin{code}

data JointDmd = JD { str :: StrDmd, abs :: AbsDmd } 
  deriving ( Eq, Show )

instance Outputable JointDmd where
  ppr (JD s a) = angleBrackets (ppr s <> char ',' <> ppr a)

-- Well-formedness preserving constructors for the joint domain
mkJointDmd :: StrDmd -> AbsDmd -> JointDmd
mkJointDmd s a 
 = case (s, a) of 
     (HyperStr, UProd _) -> JD HyperStr Used
     _                   -> JD s a
     
instance LatticeLike JointDmd where
  bot                        = mkJointDmd bot bot
  top                        = mkJointDmd top top

  pre x _ | x == bot         = True
  pre _ x | x == top         = True
  pre (JD s1 a1) (JD s2 a2)  = (pre s1 s2) && (pre a1 a2)

  lub  (JD s1 a1) (JD s2 a2) = mkJointDmd $ lub s1 s2  $ lub a1 a2            
  both (JD s1 a1) (JD s2 a2) = mkJointDmd $ both s1 s2 $ both a1 a2            
  
\end{code}


%************************************************************************
%*									*
\subsection{Demand environments, types and results}
%*									*
%************************************************************************

\begin{code}

type DmdEnv = VarEnv JointDmd

data DmdResult = TopRes	-- Nothing known	
	       | RetCPR	-- Returns a constructed product
	       | BotRes	-- Diverges or errors
	       deriving( Eq, Show )
	-- Equality for fixpoints
	-- Show needed for Show in Lex.Token (sigh)

data DmdType = DmdType 
		    DmdEnv	-- Demand on explicitly-mentioned 
				--	free variables
		    [JointDmd]	-- Demand on arguments
		    DmdResult	-- Nature of result

-- Equality needed for fixpoints in DmdAnal
instance Eq DmdType where
  (==) (DmdType fv1 ds1 res1)
       (DmdType fv2 ds2 res2) =  ufmToList fv1 == ufmToList fv2
			      && ds1 == ds2 && res1 == res2

instance Outputable DmdType where
  ppr (DmdType fv ds res) 
    = hsep [text "DmdType",
	    hcat (map ppr ds) <> ppr res,
	    if null fv_elts then empty
	    else braces (fsep (map pp_elt fv_elts))]
    where
      pp_elt (uniq, dmd) = ppr uniq <> text "->" <> ppr dmd
      fv_elts = ufmToList fv

instance Outputable DmdResult where
  ppr TopRes = empty	  -- Keep these distinct from Demand letters
  ppr RetCPR = char 'm'	  -- so that we can print strictness sigs as
  ppr BotRes = char 'b'   --    DDDr
			  -- without ambiguity
-- This guy lets us switch off CPR analysis
-- by making sure that everything uses TopRes instead of RetCPR
-- Assuming, of course, that they don't mention RetCPR by name.
-- They should onlyu use retCPR
retCPR :: DmdResult
retCPR | opt_CprOff = TopRes
       | otherwise  = RetCPR

emptyDmdEnv :: VarEnv JointDmd
emptyDmdEnv = emptyVarEnv

topDmdType, botDmdType, cprDmdType :: DmdType
topDmdType = DmdType emptyDmdEnv [] TopRes
botDmdType = DmdType emptyDmdEnv [] BotRes
cprDmdType = DmdType emptyVarEnv [] retCPR

isTopDmdType :: DmdType -> Bool
-- Only used on top-level types, hence the assert
isTopDmdType (DmdType env [] TopRes) = ASSERT( isEmptyVarEnv env) True	
isTopDmdType _                       = False

isBotRes :: DmdResult -> Bool
isBotRes BotRes = True
isBotRes _      = False

resTypeArgDmd :: DmdResult -> JointDmd
-- TopRes and BotRes are polymorphic, so that
--	BotRes = Bot -> BotRes
--	TopRes = Top -> TopRes
-- This function makes that concrete
-- We can get a RetCPR, because of the way in which we are (now)
-- giving CPR info to strict arguments.  On the first pass, when
-- nothing has demand info, we optimistically give CPR info or RetCPR to all args
resTypeArgDmd TopRes = top
resTypeArgDmd RetCPR = top
resTypeArgDmd BotRes = bot

returnsCPR :: DmdResult -> Bool
returnsCPR RetCPR = True
returnsCPR _      = False

mkDmdType :: DmdEnv -> [JointDmd] -> DmdResult -> DmdType
mkDmdType fv ds res = DmdType fv ds res

mkTopDmdType :: [JointDmd] -> DmdResult -> DmdType
mkTopDmdType ds res = DmdType emptyDmdEnv ds res

dmdTypeDepth :: DmdType -> Arity
dmdTypeDepth (DmdType _ ds _) = length ds
\end{code}

%************************************************************************
%*									*
\subsection{Strictness signature}
%*									*
%************************************************************************

In a let-bound Id we record its strictness info.  
In principle, this strictness info is a demand transformer, mapping
a demand on the Id into a DmdType, which gives
	a) the free vars of the Id's value
	b) the Id's arguments
	c) an indication of the result of applying 
	   the Id to its arguments

However, in fact we store in the Id an extremely emascuated demand transfomer,
namely 
		a single DmdType
(Nevertheless we dignify StrictSig as a distinct type.)

This DmdType gives the demands unleashed by the Id when it is applied
to as many arguments as are given in by the arg demands in the DmdType.

For example, the demand transformer described by the DmdType
		DmdType {x -> <S(LL),U(UU)>} [V,A] Top
says that when the function is applied to two arguments, it
unleashes demand <S(LL),U(UU)> on the free var x, V on the first arg,
and A on the second.  

[??? -- clarify this]
If this same function is applied to one arg, all we can say is
that it uses x with U*(LL), and its arg with demand <L,U>.

\begin{code}
newtype StrictSig = StrictSig DmdType
		  deriving( Eq )

instance Outputable StrictSig where
   ppr (StrictSig ty) = ppr ty

mkStrictSig :: DmdType -> StrictSig
mkStrictSig dmd_ty = StrictSig dmd_ty

splitStrictSig :: StrictSig -> ([JointDmd], DmdResult)
splitStrictSig (StrictSig (DmdType _ dmds res)) = (dmds, res)

increaseStrictSigArity :: Int -> StrictSig -> StrictSig
-- Add extra arguments to a strictness signature
increaseStrictSigArity arity_increase (StrictSig (DmdType env dmds res))
  = StrictSig (DmdType env (replicate arity_increase top ++ dmds) res)

isTopSig :: StrictSig -> Bool
isTopSig (StrictSig ty) = isTopDmdType ty

topSig, botSig, cprSig :: StrictSig
topSig = StrictSig topDmdType
botSig = StrictSig botDmdType
cprSig = StrictSig cprDmdType
	
-- appIsBottom returns true if an application to n args would diverge
appIsBottom :: StrictSig -> Int -> Bool
appIsBottom (StrictSig (DmdType _ ds BotRes)) n = length ds <= n
appIsBottom _				      _ = False

isBottomingSig :: StrictSig -> Bool
isBottomingSig (StrictSig (DmdType _ _ BotRes)) = True
isBottomingSig _				= False

pprIfaceStrictSig :: StrictSig -> SDoc
-- Used for printing top-level strictness pragmas in interface files
pprIfaceStrictSig (StrictSig (DmdType _ dmds res))
  = hcat (map ppr dmds) <> ppr res
\end{code}
