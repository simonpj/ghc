%
% (c) The GRASP/AQUA Project, Glasgow University, 1993-1998
%

        	-----------------------------------------
		A comparator for demand analsysis results
		-----------------------------------------

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
import NewDemand as ND

comparePgm :: Maybe Bool -> DynFlags -> CoreProgram -> IO CoreProgram
comparePgm better dflags binds  = do 
	let table    = traverseBinds better [] binds
            rendered = map (liftTup4 $ rendr dflags) $ reverse table
            tuples = init_res ++ rendered
            maxs   = foldl (\(a, b, c, d) (w, x, y, z) -> 
                                 (max a w, max b x, max c y, max d z)) 
                           (0, 0, 0, 0)
                           (map (liftTup4 length) tuples)
            header | Just True   <- better  = "          Strictly better new results         "
                   | Just False  <- better  = "          Strictly worse new results          "
                   | Nothing     <- better  = "          Strangely different results         "
                   | otherwise              = ""
                           
        if length table > 0 
           -- Display only if something interesting found
           then do putStrLn  ""
                   putStrLn  header
                   putStrLn  "==============================================="
                   mapM_ (putStrLn . renTuple maxs) tuples 
                   putStrLn  ""

           else return ()
	return binds
     where 
        init_res :: [Result String]
        init_res = [("Id", "Old Signature", "Old as new", "New Signature"), ("", "", "", "")]

type Result a = (a, a, a, a)
type Acc  = [Result SDoc]

traverseBinds :: Maybe Bool -> Acc -> CoreProgram -> Acc
traverseBinds better acc binds
  = let binders = bindersOfBinds binds
     in foldl (record better) acc binders

record :: Maybe Bool -> Acc -> Id -> Acc
record better acc id
  | old' == new                      = acc
  | Just b <- better
  , b && (new `pre` old')            = rdoc : acc
    -- new results are strictly better
  | Just b <- better          
  , (not b) && (old' `pre` new)      = rdoc : acc
      -- new results are strictly worse
  | Nothing <- better          
  , not (old' `pre` new || new `pre` old')
                                     = rdoc : acc 
      -- uncomparable results
  | otherwise                        = acc
  where
      name                 = varName id
      old                  = idStrictness id
      StrictSig old'       = toNewDmdSig old
      StrictSig new        = nd_idStrictness id
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

