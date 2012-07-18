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
            rendered = map (liftTup4 $ rendr dflags) $ reverse table
            tuples = init_res ++ rendered
            maxs   = foldl (\(a, b, c, d) (w, x, y, z) -> (max a w, max b x, max c y, max d z)) 
                           (0, 0, 0, 0)
                           (map (liftTup4 length) tuples)
                           

        putStrLn  "          Comparing strictness results         "
        putStrLn  "==============================================="
        mapM_ (putStrLn . renTuple maxs) tuples 

	return binds
     where 
        init_res :: Result String
        init_res = [("Id", "Old Signature", "Old as new", "New Signature"), ("", "", "", "")]

type Result a = (a, a, a, a)
type Acc  = [Result SDoc]

traverseBinds :: Acc -> CoreProgram -> Acc
traverseBinds acc binds
  = let binders = bindersOfBinds binds
        rhss    = concatMap rhssOfBind binds
        acc1    = foldl record acc binders
        _acc2   = foldl traverseExpr acc1 rhss
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
  = if old' == new
    then acc
    else rdoc : acc
  where
      name    = varName id
      old     = idStrictness id
      old'    = toNewDmdSig old
      new     = nd_idStrictness id
      rdoc    = (ppr name, ppr old, ppr old', ppr new)

rendr :: DynFlags -> SDoc -> String 
rendr dflags = render . flip runSDoc ctx
  where
    ctx = initSDocContext dflags defaultDumpStyle 

liftTup4 :: (a -> b) -> (a, a, a, a) -> (b, b, b, b)
liftTup4 f (a, b, c, d) = (f a, f b, f c, f d)

renTuple :: Result Int -> Result String -> String
renTuple (m1, m2, m3, _m4) (a, b, c, d) 
  = a ++ skip1 ++ b ++ skip2 ++ c ++ skip3 ++ d
  where 
    skip1 = replicate (m1 + 2 - length a) ' '
    skip2 = replicate (m2 + 2 - length b) ' '
    skip3 = replicate (m3 + 2 - length c) ' '
\end{code}