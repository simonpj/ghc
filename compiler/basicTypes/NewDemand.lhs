%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section[NewDemand]{@NewDemand@: A decoupled implementation of a demand domain}

\begin{code}

module NewDemand (
        StrDmd(..), strBot, strTop, strStr, strProd,
        AbsDmd(..), absBot, absTop, absProd,
        JointDmd(..), mkJointDmd,
        DmdEnv, 
        DmdResult, 
     ) where

#include "HsVersions.h"

import Outputable
import VarEnv

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
  | SProd [StrDmd]     -- Product or function demand
  deriving ( Eq, Show )


-- Well-formedness preserving constructors for the Strictness domain
strBot, strTop, strStr :: StrDmd
strBot     = HyperStr
strTop     = Lazy
strStr     = Str

strProd :: [StrDmd] -> StrDmd
strProd sx 
  = if all (== Lazy) sx then Str else 
      if any (== HyperStr) sx then HyperStr
        else SProd sx


-- Serialization
instance Outputable StrDmd where
  ppr HyperStr    = char 'B'
  ppr Lazy        = char 'L'
  ppr Str         = char 'S'
  ppr (SProd sx)  = (char 'S') <> parens (hcat (map ppr sx))

-- LatticeLike implementation for strictness demands
instance LatticeLike StrDmd where
  bot = HyperStr
  top = Lazy
  
  pre _ Lazy                               = True
  pre HyperStr _                           = True
  pre (SProd _) Str                        = True
  pre (SProd sx1) (SProd sx2)    
            | length sx1 == length sx2     = all (== True) $ zipWith pre sx1 sx2 
  pre x y                                  = x == y

  lub x y | x == y                         = x 
  lub y x | x `pre` y                      = lub x y
  lub HyperStr s                           = s
  lub _ Lazy                               = top
  lub (SProd _) Str                        = Str
  lub (SProd sx1) (SProd sx2) 
           | length sx1 == length sx2      = SProd $ zipWith lub sx1 sx2
           | otherwise                     = Str
  lub _ _                                  = top

  both x y | x == y                        = x 
  both y x | x `pre` y                     = both x y
  both HyperStr _                          = bot
  both s Lazy                              = s
  both s@(SProd _) Str                     = s
  both (SProd sx1) (SProd sx2) 
           | length sx1 == length sx2      = SProd $ zipWith both sx1 sx2 
  both _ _                                 = bot

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
  pre _   Used                   = True
  pre (UProd ux1) (UProd ux2)
     | length ux1 == length ux2  = all (== True) $ zipWith pre ux1 ux2 
  pre x y                        = x == y

  lub x y | x == y               = x 
  lub y x | x `pre` y            = lub x y
  lub Abs a                      = a
  lub _ Used                     = top
  lub (UProd ux1) (UProd ux2)
     | length ux1 == length ux2  = UProd $ zipWith lub ux1 ux2
  lub _ _                        = top

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
  ppr (JD s a) = parens (ppr s <> char ',' <> ppr a)

-- Well-formedness preserving constructors for the joint domain
mkJointDmd :: StrDmd -> AbsDmd -> JointDmd
mkJointDmd s a 
 = case (s, a) of 
     (HyperStr, UProd _) -> JD HyperStr Used
     _                   -> JD s a
     
instance LatticeLike JointDmd where
  bot                        = JD bot bot
  top                        = JD top top

  pre x _ | x == bot         = True
  pre _ x | x == top         = True
  pre (JD s1 a1) (JD s2 a2)  = (pre s1 s2) && (pre a1 a2)

  lub  (JD s1 a1) (JD s2 a2) = JD (lub s1 s2) (lub a1 a2)            
  both (JD s1 a1) (JD s2 a2) = JD (both s1 s2) (both a1 a2)            
  
\end{code}


%************************************************************************
%*									*
\subsection{Demand environments, types and signatures}
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

\end{code}