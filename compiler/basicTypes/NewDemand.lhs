%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section[NewDemand]{@NewDemand@: A decoupled implementation of a demand domain}

\begin{code}

module NewDemand (
       ) where

#include "HsVersions.h"

\end{code}

%************************************************************************
%*									*
\subsection{Complete Lattices}
%*									*
%************************************************************************

\begin{code}

class Lattice a where
  bot    :: a
  top    :: a
  pre    :: a -> a -> Bool
  lub    :: a -> a -> a 
  glb    :: a -> a -> a

\end{code}


%************************************************************************
%*									*
\subsection{Strictness domain}
%*									*
%************************************************************************

\begin{code}

-- Vanilla strictness domain
data StrDmd
  = HyperStr                  -- Hyperstrict 
  | Lazy                 -- Lazy
  | Str                  -- Strict
  | StrProd [StrDmd]     -- Product or function demand
  deriving ( Eq )

-- Equivalences on strictness demands
isEquivStr :: StrDmd -> StrDmd -> Bool
-- S(... bot ...) == bot
isEquivStr (StrProd sx) HyperStr     = any (flip isEquivStr HyperStr) sx
isEquivStr HyperStr (StrProd sx)     = isEquivStr (StrProd sx) HyperStr
-- S(L ... L) == S
isEquivStr (StrProd sx) Str          = all (== Lazy) sx
isEquivStr Str (StrProd sx)          = isEquivStr (StrProd sx) Str                   
isEquivStr x y                       = x == y

-- Lattice implementation for strictness demands
instance Lattice StrDmd where
  bot = HyperStr
  top = Lazy
  
  _ `pre` Lazy                              = True
  s `pre` _ | isEquivStr s bot              = True
  (StrProd _) `pre` Str                     = True
  (StrProd sx1) `pre` (StrProd sx2)    
            | length sx1 == length sx2      = all (== True) $ zipWith pre sx1 sx2 
  _ `pre` _                                 = False

  s `lub` t | isEquivStr t bot              = s
  t `lub` s | isEquivStr t bot              = s
  _ `lub` Lazy                              = top
  Lazy `lub` _                              = top
  (StrProd _) `lub` t | isEquivStr t Str    = t
  t `lub` (StrProd _) | isEquivStr t Str    = t
  (StrProd sx1) `lub` (StrProd sx2) 
           | length sx1 == length sx2       = StrProd $ zipWith lub sx1 sx2 
  _ `lub` _                                 = top

  _ `glb` t | isEquivStr t bot              = bot
  t `glb` _ | isEquivStr t bot              = bot
  s `glb` Lazy                              = s
  Lazy `glb` s                              = s
  s@(StrProd _) `glb` t | isEquivStr t Str  = s
  t `glb` s@(StrProd _) | isEquivStr t Str  = s
  (StrProd sx1) `glb` (StrProd sx2) 
           | length sx1 == length sx2       = StrProd $ zipWith glb sx1 sx2 
  _ `glb` _                                 = bot

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
  deriving ( Eq )

-- Equivalences on absense demands
_isEquivAbs :: AbsDmd -> AbsDmd -> Bool
-- U(U ... U) == U
_isEquivAbs (UProd ux) Used      = all (flip _isEquivAbs Used) ux
_isEquivAbs Used (UProd ux)      = _isEquivAbs (UProd ux) Used
_isEquivAbs x y                  = x == y

\end{code}
  
