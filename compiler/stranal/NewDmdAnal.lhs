%
% (c) The GRASP/AQUA Project, Glasgow University, 1993-1998
%

			---------------------
			A new demand analysis
			---------------------

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}

module NewDmdAnal ( dmdAnalProgram, 
                    -- dmdAnalTopRhs,
		    -- both {- needed by WwLib -}

                    -- todo cleanup
                    dmdAnal,    
                    emptySigEnv, updSigEnv, sigEnv,
                    addInitialSigs, lookupSigEnv, extendSigEnv, extendAnalEnv,
                    virgin, nonVirgin,
                  ) where

#include "HsVersions.h"

import DynFlags		( DynFlags )
import NewDemand	-- All of it
import CoreSyn
import Outputable
import VarEnv
import BasicTypes	
import FastString
import Data.List
import Id

-- import Var		( Var, isTyVar )
-- import Util
-- import PprCore
-- import StaticFlags	( opt_MaxWorkerArgs )
-- import Coercion		( isCoVarType )
-- import CoreUtils	( exprIsHNF, exprIsTrivial )
-- import CoreArity	( exprArity )
-- import DataCon		( dataConTyCon, dataConRepStrictness )
-- import TyCon		( isProductTyCon, isRecursiveTyCon )
-- import TysWiredIn	( unboxedPairDataCon )
-- import TysPrim		( realWorldStatePrimTy )
-- import UniqFM		( addToUFM_Directly, lookupUFM_Directly,
-- 			  minusUFM, filterUFM )
-- import Type		( isUnLiftedType, eqType, tyConAppTyCon_maybe )
-- import Coercion         ( coercionKind )
-- import Pair



\end{code}

%************************************************************************
%*									*
\subsection{Top level stuff}
%*									*
%************************************************************************

\begin{code}

dmdAnalProgram :: DynFlags -> CoreProgram -> IO CoreProgram
dmdAnalProgram _ binds
  = do {
	let { binds_plus_dmds = do_prog binds } ;
	return binds_plus_dmds
    }
  where
    do_prog :: CoreProgram -> CoreProgram
    do_prog binds = snd $ mapAccumL dmdAnalTopBind emptySigEnv binds


-- Analyse a (group of) top-level binding(s)
dmdAnalTopBind :: SigEnv -> CoreBind -> (SigEnv, CoreBind)
dmdAnalTopBind _sigs (NonRec _id _rhs) = undefined
dmdAnalTopBind _sigs (Rec _pairs) = undefined

\end{code}

%************************************************************************
%*									*
\subsection{The analyser itself}	
%*									*
%************************************************************************

\begin{code}
dmdAnal :: AnalEnv -> Demand -> CoreExpr -> (DmdType, CoreExpr)

dmdAnal _ dmd e 
  | dmd == top 
  = (topDmdType, e)

dmdAnal _ _ _  = undefined

\end{code}

%************************************************************************
%*									*
\subsection{Strictness signatures}
%*									*
%************************************************************************

\begin{code}
data AnalEnv
  = AE { ae_sigs   :: SigEnv
       , ae_virgin :: Bool }  -- True on first iteration only
		              -- See Note [Initialising strictness]
	-- We use the se_env to tell us whether to
	-- record info about a variable in the DmdEnv
	-- We do so if it's a LocalId, but not top-level
	--
	-- The DmdEnv gives the demand on the free vars of the function
	-- when it is given enough args to satisfy the strictness signature

type SigEnv = VarEnv (StrictSig, TopLevelFlag)

instance Outputable AnalEnv where
  ppr (AE { ae_sigs = env, ae_virgin = virgin })
    = ptext (sLit "AE") <+> braces (vcat
         [ ptext (sLit "ae_virgin =") <+> ppr virgin
         , ptext (sLit "ae_sigs =") <+> ppr env ])

emptySigEnv :: SigEnv
emptySigEnv = emptyVarEnv

sigEnv :: AnalEnv -> SigEnv
sigEnv = ae_sigs

updSigEnv :: AnalEnv -> SigEnv -> AnalEnv
updSigEnv env sigs = env { ae_sigs = sigs }

extendAnalEnv :: TopLevelFlag -> AnalEnv -> Id -> StrictSig -> AnalEnv
extendAnalEnv top_lvl env var sig
  = env { ae_sigs = extendSigEnv top_lvl (ae_sigs env) var sig }

extendSigEnv :: TopLevelFlag -> SigEnv -> Id -> StrictSig -> SigEnv
extendSigEnv top_lvl sigs var sig = extendVarEnv sigs var (sig, top_lvl)

lookupSigEnv :: AnalEnv -> Id -> Maybe (StrictSig, TopLevelFlag)
lookupSigEnv env id = lookupVarEnv (ae_sigs env) id

addInitialSigs :: TopLevelFlag -> AnalEnv -> [Id] -> AnalEnv
-- See Note [Initialising strictness]
addInitialSigs top_lvl env@(AE { ae_sigs = sigs, ae_virgin = virgin }) ids
  = env { ae_sigs = extendVarEnvList sigs [ (id, (init_sig id, top_lvl))
                                          | id <- ids ] }
  where
    init_sig | virgin    = \_ -> botSig
             | otherwise = nd_idStrictness

virgin, nonVirgin :: SigEnv -> AnalEnv
virgin    sigs = AE { ae_sigs = sigs, ae_virgin = True }
nonVirgin sigs = AE { ae_sigs = sigs, ae_virgin = False }

\end{code}

Note [Initialising strictness]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
See section 9.2 (Finding fixpoints) of the paper.

Our basic plan is to initialise the strictness of each Id in a
recursive group to "bottom", and find a fixpoint from there.  However,
this group B might be inside an *enclosing* recursiveb group A, in
which case we'll do the entire fixpoint shebang on for each iteration
of A. This can be illustrated by the following example:

Example:

  f [] = []
  f (x:xs) = let g []     = f xs
                 g (y:ys) = y+1 : g ys
              in g (h x)

At each iteration of the fixpoint for f, the analyser has to find a
fixpoint for the enclosed function g. In the meantime, the demand
values for g at each iteration for f are *greater* than those we
encountered in the previous iteration for f. Therefore, we can begin
the fixpoint for g not with the bottom value but rather with the
result of the previous analysis. I.e., when beginning the fixpoint
process for g, we can start from the demand signature computed for g
previously and attached to the binding occurrence of g.

To speed things up, we initialise each iteration of A (the enclosing
one) from the result of the last one, which is neatly recorded in each
binder.  That way we make use of earlier iterations of the fixpoint
algorithm. (Cunning plan.)

But on the *first* iteration we want to *ignore* the current strictness
of the Id, and start from "bottom".  Nowadays the Id can have a current
strictness, because interface files record strictness for nested bindings.
To know when we are in the first iteration, we look at the ae_virgin
field of the AnalEnv.
