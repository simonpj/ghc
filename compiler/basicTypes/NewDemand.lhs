%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section[NewDemand]{@NewDemand@: A decoupled implementation of a demand domain}

\begin{code}

module NewDemand (
       ) where

#include "HsVersions.h"

import Outputable


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

class Equivalent a where
  equiv  :: a -> a -> Bool

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


instance Outputable StrDmd where
  ppr HyperStr    = char 'H'
  ppr Lazy        = char 'L'
  ppr Str         = char 'S'
  ppr (SProd sx)  = (char 'S') <> parens (hcat (map ppr sx))


-- Equivalences on strictness demands
instance Equivalent StrDmd where
  -- S(... bot ...) == bot
  equiv (SProd sx) HyperStr     = any (flip equiv HyperStr) sx
  equiv HyperStr (SProd sx)     = equiv (SProd sx) HyperStr
  -- S(L ... L) == S
  equiv (SProd sx) Str          = all (== Lazy) sx
  equiv Str (SProd sx)          = equiv (SProd sx) Str                   
  equiv x y                     = x == y


-- LatticeLike implementation for strictness demands
instance LatticeLike StrDmd where
  bot = HyperStr
  top = Lazy
  
  pre _ Lazy                               = True
  pre s _ | equiv s bot                    = True
  pre (SProd _) Str                        = True
  pre (SProd sx1) (SProd sx2)    
            | length sx1 == length sx2       = all (== True) $ zipWith pre sx1 sx2 
  pre x y                                  = equiv x y

  lub s t | equiv t bot                    = s
  lub t s | equiv t bot                    = s
  lub _ Lazy                               = top
  lub Lazy _                               = top
  lub (SProd _) t | equiv t Str            = t
  lub t (SProd _) | equiv t Str            = t
  lub (SProd sx1) (SProd sx2) 
           | length sx1 == length sx2        = SProd $ zipWith lub sx1 sx2
           | otherwise                       = Str
  lub x y | x == y                         = x 
  lub _ _                                  = top

  both _ t | equiv t bot                   = bot
  both t _ | equiv t bot                   = bot
  both s Lazy                              = s
  both Lazy s                              = s
  both s@(SProd _) t | equiv t Str         = s
  both t s@(SProd _) | equiv t Str         = s
  both (SProd sx1) (SProd sx2) 
           | length sx1 == length sx2        = SProd $ zipWith both sx1 sx2 
  both x y | x == y                        = x 
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

instance Outputable AbsDmd where
  ppr Abs         = char 'A'
  ppr Used        = char 'U'
  ppr (UProd as)  = (char 'U') <> parens (hcat (map ppr as))


-- Equivalences on absense demands
instance Equivalent AbsDmd where
  -- U(U ... U) == U
  equiv (UProd ux) Used      = all (flip equiv Used) ux
  equiv Used (UProd ux)      = equiv (UProd ux) Used
  equiv x y                  = x == y


instance LatticeLike AbsDmd where
  bot                              = Abs
  top                              = Used
 
  pre Abs _                      = True
  pre _   Used                   = True
  pre (UProd ux1) (UProd ux2)
     | length ux1 == length ux2    = all (== True) $ zipWith pre ux1 ux2 
  pre x y                        = equiv x y

  lub Abs a                      = a
  lub a Abs                      = a
  lub Used _                     = top
  lub _ Used                     = top
  lub (UProd ux1) (UProd ux2)
     | length ux1 == length ux2    = UProd $ zipWith lub ux1 ux2
  lub x y | x == y               = x 
  lub _ _                        = top

  both                           = lub

\end{code}
  
%************************************************************************
%*									*
\subsection{Joint domain for Strictness and Absence}
%*									*
%************************************************************************

\begin{code}

type Joint = (StrDmd, AbsDmd)

instance Equivalent Joint where
  equiv (s1, _) (s2, Used) 
      | equiv s1 s2 && s1 /= s2         = True
  equiv (s1, Used) (s2, _) 
      | equiv s1 s2 && s1 /= s2         = True
  equiv (Lazy, UProd _) (Lazy, Used)    = True      
  equiv (Lazy, Used) (Lazy, UProd _)    = True      
  equiv x y                             = x == y
  

instance LatticeLike Joint where
  bot                        = (bot, bot)
  top                        = (top, top)

  pre x _ | equiv x bot      = True
  pre _ x | equiv x top      = True
  pre (s1, a1) (s2, a2)      = (pre s1 s2) && (pre a1 a2)

  lub  (s1, a1) (s2, a2)     = (lub s1 s2, lub a1 a2)            
  both (s1, a1) (s2, a2)     = (both s1 s2, both a1 a2)            
  
\end{code}