%
% (c) The GRASP/AQUA Project, Glasgow University, 1993-1998
%

        	------------------------------------------
		A comparator for demadn analsysis' results
		------------------------------------------

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}

module StrCompare ( comparePgm ) where

import Outputable
import Pretty        ( render )
import CoreSyn
import Id
import Var
import DynFlags
import Demand        ( toNewDmdSig )

comparePgm :: DynFlags -> CoreProgram -> IO CoreProgram
comparePgm dflags binds  = do 
	let table    = traverseBinds [] binds
            ctx      = initSDocContext dflags defaultDumpStyle
            rendered = map (render . flip runSDoc ctx) $ reverse table

        putStrLn  "Comparing Strictness results"
        putStrLn  "========================================"
        mapM_ putStrLn rendered

	return binds

type Acc  = [SDoc]

traverseBinds :: Acc -> CoreProgram -> Acc
traverseBinds acc binds
  = let binders = bindersOfBinds binds
        rhss    = concatMap rhssOfBind binds
        acc1    = foldl record acc binders
        _acc2    = foldl traverseExpr acc1 rhss
     in acc1

traverseExpr :: Acc -> CoreExpr -> Acc
traverseExpr acc (Lit _) = acc
traverseExpr acc (Var _) = acc
traverseExpr acc (Type _) = acc
traverseExpr acc (Coercion _) = acc
traverseExpr acc (Tick _ e) = traverseExpr acc e
traverseExpr acc (Cast e _) = traverseExpr acc e
traverseExpr acc (App e1 e2) = acc2 
  where 
    acc2 = traverseExpr acc1 e2
    acc1 = traverseExpr acc e1
traverseExpr acc (Lam b e) = acc2
  where
    acc2 = traverseExpr acc1 e
    acc1 = record acc b
traverseExpr acc (Let bs e) = acc2
  where
    acc2 = traverseExpr acc1 e
    acc1 = traverseBinds acc [bs]
traverseExpr acc (Case e b _ alts) = acc3
  where acc3 = foldl traverseAlt acc2 alts
        acc2 = traverseExpr acc1 e
        acc1 = record acc b

traverseAlt :: Acc -> Alt Id -> Acc
traverseAlt acc (_, bs, e) = acc2
  where
    acc2 = traverseExpr acc1 e
    acc1 = foldl record acc bs

record :: Acc -> Id -> Acc
record acc id
  = if toNewDmdSig old_str == new_str
    then acc
    else doc : acc
  where
      skip    = text "   "
      name    = varName id
      old_str = idStrictness id
      new_str = nd_idStrictness id
      doc = ppr name <> skip <> 
            ppr old_str <> skip <> ppr new_str

\end{code}