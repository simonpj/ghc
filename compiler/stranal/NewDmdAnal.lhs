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
import CoreUtils	( exprIsHNF, exprIsTrivial )
import UniqFM	


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
dmdAnalTopBind sigs (NonRec id rhs)
  = (sigs1, NonRec id1 rhs1)
  where
    (sigs1, _, (id1,   rhs1)) = dmdAnalRhs TopLevel NonRecursive (virgin sigs) (id, rhs)
    -- what about the second step?

dmdAnalTopBind sigs (Rec pairs)
  = (sigs', Rec pairs')
  where
    (sigs', _, pairs')  = dmdFix TopLevel (virgin sigs) pairs

\end{code}

%************************************************************************
%*									*
\subsection{The analyser itself}	
%*									*
%************************************************************************

\begin{code}
dmdAnal :: AnalEnv -> Demand -> CoreExpr -> (DmdType, CoreExpr)

dmdAnal _ dmd e | dmd == top 
  -- top demand does not provide any way to infer something interesting 
  = (topDmdType, e)



dmdAnal _ _ _  = undefined

\end{code}

%************************************************************************
%*									*
\subsection{Bindings}
%*									*
%************************************************************************

\begin{code}

-- Recursive bindings
dmdFix :: TopLevelFlag
       -> AnalEnv 		-- Does not include bindings for this binding
       -> [(Id,CoreExpr)]
       -> (SigEnv, DmdEnv,
	   [(Id,CoreExpr)])	-- Binders annotated with stricness info
dmdFix = undefined

-- Non-recursive bindings
dmdAnalRhs :: TopLevelFlag -> RecFlag
	-> AnalEnv -> (Id, CoreExpr)
	-> (SigEnv,  DmdEnv, (Id, CoreExpr))
-- Process the RHS of the binding, add the strictness signature
-- to the Id, and augment the environment with the signature as well.

dmdAnalRhs top_lvl rec_flag env (id, rhs)
 = (sigs', lazy_fv, (id', rhs'))
 where
  arity		     = idArity id   -- The idArity should be up to date
				    -- The simplifier was run just beforehand
  (rhs_dmd_ty, rhs') = dmdAnal env (vanillaCall arity) rhs
  (lazy_fv, sig_ty)  = WARN( arity /= dmdTypeDepth rhs_dmd_ty && not (exprIsTrivial rhs), ppr id )
                       -- The RHS can be eta-reduced to just a variable, 
                       -- in which case we should not complain. 
		       mkSigTy top_lvl rec_flag id rhs rhs_dmd_ty
  id'		     = id `nd_setIdStrictness` sig_ty
  sigs'		     = extendSigEnv top_lvl (sigEnv env) id' sig_ty


\end{code}

%************************************************************************
%*									*
\subsection{Strictness signatures and types}
%*									*
%************************************************************************

\begin{code}

mkSigTy :: TopLevelFlag -> RecFlag -> Id -> CoreExpr -> DmdType -> (DmdEnv, StrictSig)
mkSigTy top_lvl rec_flag id rhs dmd_ty 
  = mk_sig_ty thunk_cpr_ok rhs dmd_ty
  where
    maybe_id_dmd = nd_idDemandInfo_maybe id

    -- is it okay or not to assign CPR 
    -- (not okay in the first pass)
    thunk_cpr_ok   -- See Note [CPR for thunks]
	| isTopLevel top_lvl       = False	-- Top level things don't get
						-- their demandInfo set at all
	| isRec rec_flag	   = False	-- Ditto recursive things
	| Just dmd <- maybe_id_dmd = isStrictDmd dmd
	| otherwise 		   = True	-- Optimistic, first time round
						-- See notes below

mk_sig_ty :: Bool -> CoreExpr -> DmdType -> (DmdEnv, StrictSig)
mk_sig_ty thunk_cpr_ok rhs (DmdType fv dmds res) 
  = (lazy_fv, mkStrictSig dmd_ty)
	-- Re unused never_inline, see Note [NOINLINE and strictness]
  where
    dmd_ty = mkDmdType strict_fv dmds res'

    -- See Note [Lazy and strict free variables]
    lazy_fv   = filterUFM (not . isStrictDmd) fv
    strict_fv = filterUFM isStrictDmd         fv

        -- final_dmds = setUnpackStrategy dmds
	-- Set the unpacking strategy

    ignore_cpr_info = not (exprIsHNF rhs || thunk_cpr_ok)
    res' = if returnsCPR res && ignore_cpr_info 
	   then topRes
           else res 
\end{code}

Note [CPR for thunks]
~~~~~~~~~~~~~~~~~~~~~
If the rhs is a thunk, we usually forget the CPR info, because
it is presumably shared (else it would have been inlined, and 
so we'd lose sharing if w/w'd it into a function).  E.g.

	let r = case expensive of
		  (a,b) -> (b,a)
	in ...

If we marked r as having the CPR property, then we'd w/w into

	let $wr = \() -> case expensive of
			    (a,b) -> (# b, a #)
	    r = case $wr () of
		  (# b,a #) -> (b,a)
	in ...

But now r is a thunk, which won't be inlined, so we are no further ahead.
But consider

	f x = let r = case expensive of (a,b) -> (b,a)
	      in if foo r then r else (x,x)

Does f have the CPR property?  Well, no.

However, if the strictness analyser has figured out (in a previous 
iteration) that it's strict, then we DON'T need to forget the CPR info.
Instead we can retain the CPR info and do the thunk-splitting transform 
(see WorkWrap.splitThunk).

This made a big difference to PrelBase.modInt, which had something like
	modInt = \ x -> let r = ... -> I# v in
			...body strict in r...
r's RHS isn't a value yet; but modInt returns r in various branches, so
if r doesn't have the CPR property then neither does modInt
Another case I found in practice (in Complex.magnitude), looks like this:
		let k = if ... then I# a else I# b
		in ... body strict in k ....
(For this example, it doesn't matter whether k is returned as part of
the overall result; but it does matter that k's RHS has the CPR property.)  
Left to itself, the simplifier will make a join point thus:
		let $j k = ...body strict in k...
		if ... then $j (I# a) else $j (I# b)
With thunk-splitting, we get instead
		let $j x = let k = I#x in ...body strict in k...
		in if ... then $j a else $j b
This is much better; there's a good chance the I# won't get allocated.

The difficulty with this is that we need the strictness type to
look at the body... but we now need the body to calculate the demand
on the variable, so we can decide whether its strictness type should
have a CPR in it or not.  Simple solution: 
	a) use strictness info from the previous iteration
	b) make sure we do at least 2 iterations, by doing a second
	   round for top-level non-recs.  Top level recs will get at
	   least 2 iterations except for totally-bottom functions
	   which aren't very interesting anyway.

NB: strictly_demanded is never true of a top-level Id, or of a recursive Id.

Note [Optimistic in the Nothing case]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Demand info now has a 'Nothing' state, just like strictness info.
The analysis works from 'dangerous' towards a 'safe' state; so we 
start with botSig for 'Nothing' strictness infos, and we start with
"yes, it's demanded" for 'Nothing' in the demand info.  The
fixpoint iteration will sort it all out.

We can't start with 'not-demanded' because then consider
	f x = let 
		  t = ... I# x
	      in
	      if ... then t else I# y else f x'

In the first iteration we'd have no demand info for x, so assume
not-demanded; then we'd get TopRes for f's CPR info.  Next iteration
we'd see that t was demanded, and so give it the CPR property, but by
now f has TopRes, so it will stay TopRes.  Instead, with the Nothing
setting the first time round, we say 'yes t is demanded' the first
time.

However, this does mean that for non-recursive bindings we must
iterate twice to be sure of not getting over-optimistic CPR info,
in the case where t turns out to be not-demanded.  This is handled
by dmdAnalTopBind.


Note [NOINLINE and strictness]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The strictness analyser used to have a HACK which ensured that NOINLNE
things were not strictness-analysed.  The reason was unsafePerformIO. 
Left to itself, the strictness analyser would discover this strictness 
for unsafePerformIO:
	unsafePerformIO:  C(U(AV))
But then consider this sub-expression
	unsafePerformIO (\s -> let r = f x in 
			       case writeIORef v r s of (# s1, _ #) ->
			       (# s1, r #)
The strictness analyser will now find that r is sure to be eval'd,
and may then hoist it out.  This makes tests/lib/should_run/memo002
deadlock.

Solving this by making all NOINLINE things have no strictness info is overkill.
In particular, it's overkill for runST, which is perfectly respectable.
Consider
	f x = runST (return x)
This should be strict in x.

So the new plan is to define unsafePerformIO using the 'lazy' combinator:

	unsafePerformIO (IO m) = lazy (case m realWorld# of (# _, r #) -> r)

Remember, 'lazy' is a wired-in identity-function Id, of type a->a, which is 
magically NON-STRICT, and is inlined after strictness analysis.  So
unsafePerformIO will look non-strict, and that's what we want.

Now we don't need the hack in the strictness analyser.  HOWEVER, this
decision does mean that even a NOINLINE function is not entirely
opaque: some aspect of its implementation leaks out, notably its
strictness.  For example, if you have a function implemented by an
error stub, but which has RULES, you may want it not to be eliminated
in favour of error!

Note [Lazy and strict free variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We put the strict FVs in the DmdType of the Id, so 
that at its call sites we unleash demands on its strict fvs.
An example is 'roll' in imaginary/wheel-sieve2
Something like this:
	roll x = letrec 
		     go y = if ... then roll (x-1) else x+1
		 in 
		 go ms
We want to see that roll is strict in x, which is because
go is called.   So we put the DmdEnv for x in go's DmdType.

Another example:

	f :: Int -> Int -> Int
	f x y = let t = x+1
	    h z = if z==0 then t else 
		  if z==1 then x+1 else
		  x + h (z-1)
	in h y

Calling h does indeed evaluate x, but we can only see
that if we unleash a demand on x at the call site for t.

Incidentally, here's a place where lambda-lifting h would
lose the cigar --- we couldn't see the joint strictness in t/x

	ON THE OTHER HAND
We don't want to put *all* the fv's from the RHS into the
DmdType, because that makes fixpointing very slow --- the 
DmdType gets full of lazy demands that are slow to converge.

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