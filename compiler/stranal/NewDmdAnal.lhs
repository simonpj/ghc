%
% (c) The GRASP/AQUA Project, Glasgow University, 1993-1998
%

			---------------------
			A new demand analysis
			---------------------

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}

module NewDmdAnal ( dmdAnalProgram, dmdAnalTopRhs,
		    both {- needed by WwLib -}
                  ) where

#include "HsVersions.h"

import DynFlags		( DynFlags )
-- import StaticFlags	( opt_MaxWorkerArgs )
import Demand	-- All of it
import CoreSyn
-- import PprCore	
-- import Coercion		( isCoVarType )
-- import CoreUtils	( exprIsHNF, exprIsTrivial )
-- import CoreArity	( exprArity )
-- import DataCon		( dataConTyCon, dataConRepStrictness )
-- import TyCon		( isProductTyCon, isRecursiveTyCon )
-- import Id		( Id, idType, idInlineActivation,
-- 			  isDataConWorkId, isGlobalId, idArity,
-- 			  idStrictness, 
-- 			  setIdStrictness, idDemandInfo, idUnfolding,
-- 			  idDemandInfo_maybe, setIdDemandInfo
-- 			)
-- import Var		( Var, isTyVar )
-- import VarEnv
-- import TysWiredIn	( unboxedPairDataCon )
-- import TysPrim		( realWorldStatePrimTy )
-- import UniqFM		( addToUFM_Directly, lookupUFM_Directly,
-- 			  minusUFM, filterUFM )
-- import Type		( isUnLiftedType, eqType, tyConAppTyCon_maybe )
-- import Coercion         ( coercionKind )
-- import Util
-- import BasicTypes	( Arity, TopLevelFlag(..), isTopLevel, isNeverActive,
-- 			  RecFlag(..), isRec, isMarkedStrict )
-- import Maybes		( orElse, expectJust )
-- import Outputable
-- import Pair
-- import Data.List
-- import FastString

\end{code}

\begin{code}

dmdAnalProgram :: DynFlags -> CoreProgram -> IO CoreProgram
dmdAnalProgram _ binds
   = do {
       putStrLn "A new demand analysis is bootstrapped!"
     ; return binds     
     }


\end{code}

\begin{code}
dmdAnalTopRhs :: CoreExpr -> (StrictSig, CoreExpr)
dmdAnalTopRhs = undefined

both :: Demand -> Demand -> Demand
both = undefined
\end{code}