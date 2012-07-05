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
        JointDmd(..), mkJointDmd, isTop,
	DmdType(..), topDmdType, botDmdType, mkDmdType, mkTopDmdType, 
		dmdTypeDepth, 
	DmdEnv, emptyDmdEnv,
	DmdResult(..), isBotRes, resTypeArgDmd,
        appIsBottom, isBottomingSig, pprIfaceStrictSig, 
	StrictSig(..), mkStrictSig, topSig, botSig,
        isTopSig, 	splitStrictSig, increaseStrictSigArity,
       
        seqStrDmd, seqStrDmdList, seqAbsDmd, seqAbsDmdList,
        seqDemand, seqDemandList, seqDmdType, seqStrictSig, 
     ) where

#include "HsVersions.h"

--import StaticFlags
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
instance LatticeLike Bool where
  bot     = False
  top     = True
-- x `pre` y <==> (x => y)
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
  = HyperStr             -- Hyper-strict 
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
  = if all (== Lazy) sx  -- no demand products with empty lists
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
  pre (SProd d1 sx1) (SProd d2 sx2)    
            | d1 `pre` d2 &&    
              length sx1 == length sx2   = all (== True) $ zipWith pre sx1 sx2 
  pre x y                                  = x == y

  lub x y | x == y                         = x 
  lub y x | x `pre` y                      = lub x y
  lub HyperStr s                           = s
  lub _ Lazy                               = strTop
  lub (SProd False _) Str                  = strStr
  lub (SProd d1 sx1) (SProd d2 sx2) 
           | length sx1 == length sx2      = strProd (d1 `lub` d2) $ zipWith lub sx1 sx2
           | otherwise                     = strProd (d1 `lub` d2) $ []
  lub _ _                                  = strTop

  both x y | x == y                        = x 
  both y x | x `pre` y                     = both x y
  both HyperStr _                          = strBot
  both s Lazy                              = s
  both s@(SProd False _) Str               = s
  both (SProd d1 sx1) (SProd d2 sx2) 
           | length sx1 == length sx2      = strProd (d1 `both` d2) $ zipWith both sx1 sx2 
  both _ _                                 = strBot

-- utility functions to deal with memory leaks
seqStrDmd :: StrDmd -> ()
seqStrDmd (SProd d ds) = d `seq` seqStrDmdList ds
seqStrDmd _            = ()

seqStrDmdList :: [StrDmd] -> ()
seqStrDmdList [] = ()
seqStrDmdList (d:ds) = seqStrDmd d `seq` seqStrDmdList ds

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

-- utility functions
seqAbsDmd :: AbsDmd -> ()
seqAbsDmd (UProd ds) = seqAbsDmdList ds
seqAbsDmd _          = ()

seqAbsDmdList :: [AbsDmd] -> ()
seqAbsDmdList [] = ()
seqAbsDmdList (d:ds) = seqAbsDmd d `seq` seqAbsDmdList ds

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

  lub  (JD s1 a1) (JD s2 a2) = mkJointDmd (lub s1 s2)  $ lub a1 a2            
  both (JD s1 a1) (JD s2 a2) = mkJointDmd (both s1 s2) $ both a1 a2            


isTop :: JointDmd -> Bool
isTop (JD s a) 
      | s == top && a == top = True
isTop _                      = False 

-- More utility functions for strictness
seqDemand :: JointDmd -> ()
seqDemand (JD x y) = x `seq` y `seq` ()

seqDemandList :: [JointDmd] -> ()
seqDemandList [] = ()
seqDemandList (d:ds) = seqDemand d `seq` seqDemandList ds
\end{code}

%************************************************************************
%*									*
\subsection{Demand environments, types and results}
%*									*
%************************************************************************

\begin{code}

type DmdEnv = VarEnv JointDmd

data DmdResult = TopRes	-- Nothing known, assumed to be just lazy	
	       | BotRes	-- Diverges or errors
	       deriving( Eq, Show )
	-- Equality for fixpoints
	-- Show needed for Show in Lex.Token (sigh)

data DmdType = DmdType 
		  DmdEnv	-- Demand on explicitly-mentioned 
		       	        --	free variables
		  [JointDmd]	-- Demand on arguments
		  DmdResult	-- Nature of result
\end{code}

Note [Nature of result demand]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We assume the result in a demand type to be either a top or bottom
in order to represent the information about demand on the function
result, imposed by its definition. There are not so many things we 
can say, though. 

For instance, one can consider a function

        h = \v -> error "urk"

Taking the definition of strictness, we can easily see that 

        h undefined = undefined

that is, h is strict in v. However, v is not used somehow in the body
of h How can we know that h is strict in v? In fact, we know it by
considering a result demand of error and bottom and unleashing it on
all the variables in scope at a call site (in this case, this is only
v). We can also consider a case

       h = \v -> f x

where we know that the result of f is not hyper-strict (i.e, it is
lazy, or top). So, we put the same demand on v, which allow us to
infer a lazy demand that h puts on v.


\begin{code}
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
  ppr BotRes = char 'b'   --    DDDr
			  -- without ambiguity

emptyDmdEnv :: VarEnv JointDmd
emptyDmdEnv = emptyVarEnv

topDmdType, botDmdType :: DmdType
topDmdType = DmdType emptyDmdEnv [] TopRes
botDmdType = DmdType emptyDmdEnv [] BotRes

isTopDmdType :: DmdType -> Bool
-- Only used on top-level types, hence the assert
isTopDmdType (DmdType env [] TopRes) = ASSERT( isEmptyVarEnv env) True	
isTopDmdType _                       = False

isBotRes :: DmdResult -> Bool
isBotRes BotRes = True
isBotRes _      = False

resTypeArgDmd :: DmdResult -> JointDmd
-- TopRes and BotRes are polymorphic, so that
--	BotRes === Bot -> BotRes === ...
--	TopRes === Top -> TopRes === ...
-- This function makes that concrete
resTypeArgDmd TopRes = top
resTypeArgDmd BotRes = bot

mkDmdType :: DmdEnv -> [JointDmd] -> DmdResult -> DmdType
mkDmdType fv ds res = DmdType fv ds res

mkTopDmdType :: [JointDmd] -> DmdResult -> DmdType
mkTopDmdType ds res = DmdType emptyDmdEnv ds res

dmdTypeDepth :: DmdType -> Arity
dmdTypeDepth (DmdType _ ds _) = length ds

seqDmdType :: DmdType -> ()
seqDmdType (DmdType _env ds res) = 
  {- ??? env `seq` -} seqDemandList ds `seq` res `seq` ()

\end{code}

%************************************************************************
%*									*
\subsection{Demand signature}
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

If an Id is applied to less arguments than its arity, it means that
the demand on the function at a call site is weaker than the vanilla
call demand, used for signature inference. Therefore we place a top
demand on all arguments. Otherwise, the demand is specified by Id's
signature.

For example, the demand transformer described by the DmdType
		DmdType {x -> <S(LL),U(UU)>} [V,A] Top
says that when the function is applied to two arguments, it
unleashes demand <S(LL),U(UU)> on the free var x, V on the first arg,
and A on the second.  

If this same function is applied to one arg, all we can say is that it
uses x with <L,U>, and its arg with demand <L,U>.

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

topSig, botSig:: StrictSig
topSig = StrictSig topDmdType
botSig = StrictSig botDmdType
	
\end{code}

Note [Non-full application] 
~~~~~~~~~~~~~~~~~~~~~~~~~~~ 

If a function having bottom as its demand result is applied to a less
number of arguments than its syntactic arity, we cannot say for sure
that it is going to diverge. This is the reason why we use the
function appIsBottom, which, given a strictness signature and a number
of arguments, says conservatively if the function is going to diverge
or not.

\begin{code}

-- appIsBottom returns true if an application to n args would diverge
appIsBottom :: StrictSig -> Int -> Bool
appIsBottom (StrictSig (DmdType _ ds BotRes)) n = not $ lengthExceeds ds n 
appIsBottom _				      _ = False

isBottomingSig :: StrictSig -> Bool
isBottomingSig (StrictSig (DmdType _ _ BotRes)) = True
isBottomingSig _				= False

seqStrictSig :: StrictSig -> ()
seqStrictSig (StrictSig ty) = seqDmdType ty

-- Used for printing top-level strictness pragmas in interface files
pprIfaceStrictSig :: StrictSig -> SDoc
pprIfaceStrictSig (StrictSig (DmdType _ dmds res))
  = hcat (map ppr dmds) <> ppr res
\end{code}
