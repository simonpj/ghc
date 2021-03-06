-----------------------------------------------------------------------------
--
-- Stg to C--: heap management functions
--
-- (c) The University of Glasgow 2004-2006
--
-----------------------------------------------------------------------------

module StgCmmHeap (
        getVirtHp, setVirtHp, setRealHp,
        getHpRelOffset, hpRel,

        entryHeapCheck, altHeapCheck, altHeapCheckReturnsTo,

        mkVirtHeapOffsets, mkVirtConstrOffsets,
        mkStaticClosureFields, mkStaticClosure,

        allocDynClosure, allocDynClosureCmm,
        emitSetDynHdr
    ) where

#include "HsVersions.h"

import StgSyn
import CLabel
import StgCmmLayout
import StgCmmUtils
import StgCmmMonad
import StgCmmProf
import StgCmmTicky
import StgCmmGran
import StgCmmClosure
import StgCmmEnv

import MkGraph

import Hoopl
import SMRep
import Cmm
import CmmUtils
import CostCentre
import Outputable
import IdInfo( CafInfo(..), mayHaveCafRefs )
import Module
import DynFlags
import FastString( mkFastString, fsLit )
import Constants
import Util

import Control.Monad (when)

-----------------------------------------------------------
--              Initialise dynamic heap objects
-----------------------------------------------------------

allocDynClosure
        :: CmmInfoTable
        -> LambdaFormInfo
        -> CmmExpr              -- Cost Centre to stick in the object
        -> CmmExpr              -- Cost Centre to blame for this alloc
                                -- (usually the same; sometimes "OVERHEAD")

        -> [(NonVoid StgArg, VirtualHpOffset)]  -- Offsets from start of object
                                                -- ie Info ptr has offset zero.
                                                -- No void args in here
        -> FCode CmmExpr -- returns Hp+n

allocDynClosureCmm
        :: CmmInfoTable -> LambdaFormInfo -> CmmExpr -> CmmExpr
        -> [(CmmExpr, VirtualHpOffset)]
        -> FCode CmmExpr -- returns Hp+n

-- allocDynClosure allocates the thing in the heap,
-- and modifies the virtual Hp to account for this.
-- The second return value is the graph that sets the value of the
-- returned LocalReg, which should point to the closure after executing
-- the graph.

-- allocDynClosure returns an (Hp+8) CmmExpr, and hence the result is
-- only valid until Hp is changed.  The caller should assign the
-- result to a LocalReg if it is required to remain live.
--
-- The reason we don't assign it to a LocalReg here is that the caller
-- is often about to call regIdInfo, which immediately assigns the
-- result of allocDynClosure to a new temp in order to add the tag.
-- So by not generating a LocalReg here we avoid a common source of
-- new temporaries and save some compile time.  This can be quite
-- significant - see test T4801.


allocDynClosure info_tbl lf_info use_cc _blame_cc args_w_offsets
  = do  { let (args, offsets) = unzip args_w_offsets
        ; cmm_args <- mapM getArgAmode args     -- No void args
        ; allocDynClosureCmm info_tbl lf_info
                             use_cc _blame_cc (zip cmm_args offsets)
        }

allocDynClosureCmm info_tbl lf_info use_cc _blame_cc amodes_w_offsets
  = do  { virt_hp <- getVirtHp

        -- SAY WHAT WE ARE ABOUT TO DO
        ; let rep = cit_rep info_tbl
        ; tickyDynAlloc rep lf_info
        ; profDynAlloc rep use_cc

        -- FIND THE OFFSET OF THE INFO-PTR WORD
        ; let   info_offset = virt_hp + 1
                -- info_offset is the VirtualHpOffset of the first
                -- word of the new object
                -- Remember, virtHp points to last allocated word,
                -- ie 1 *before* the info-ptr word of new object.

                info_ptr = CmmLit (CmmLabel (cit_lbl info_tbl))

        -- ALLOCATE THE OBJECT
        ; base <- getHpRelOffset info_offset
        ; emitComment $ mkFastString "allocDynClosure"
        ; emitSetDynHdr base info_ptr  use_cc
        ; let (cmm_args, offsets) = unzip amodes_w_offsets
        ; hpStore base cmm_args offsets

        -- BUMP THE VIRTUAL HEAP POINTER
        ; dflags <- getDynFlags
        ; setVirtHp (virt_hp + heapClosureSize dflags rep)

        ; getHpRelOffset info_offset
        }

emitSetDynHdr :: CmmExpr -> CmmExpr -> CmmExpr -> FCode ()
emitSetDynHdr base info_ptr ccs
  = do dflags <- getDynFlags
       hpStore base (header dflags) [0..]
  where
    header :: DynFlags -> [CmmExpr]
    header dflags = [info_ptr] ++ dynProfHdr dflags ccs
        -- ToDo: Gransim stuff
        -- ToDo: Parallel stuff
        -- No ticky header

hpStore :: CmmExpr -> [CmmExpr] -> [VirtualHpOffset] -> FCode ()
-- Store the item (expr,off) in base[off]
hpStore base vals offs
  = emit (catAGraphs (zipWith mk_store vals offs))
  where
    mk_store val off = mkStore (cmmOffsetW base off) val


-----------------------------------------------------------
--              Layout of static closures
-----------------------------------------------------------

-- Make a static closure, adding on any extra padding needed for CAFs,
-- and adding a static link field if necessary.

mkStaticClosureFields
        :: DynFlags
        -> CmmInfoTable
        -> CostCentreStack
        -> CafInfo
        -> [CmmLit]             -- Payload
        -> [CmmLit]             -- The full closure
mkStaticClosureFields dflags info_tbl ccs caf_refs payload
  = mkStaticClosure dflags info_lbl ccs payload padding
        static_link_field saved_info_field
  where
    info_lbl = cit_lbl info_tbl

    -- CAFs must have consistent layout, regardless of whether they
    -- are actually updatable or not.  The layout of a CAF is:
    --
    --        3 saved_info
    --        2 static_link
    --        1 indirectee
    --        0 info ptr
    --
    -- the static_link and saved_info fields must always be in the
    -- same place.  So we use isThunkRep rather than closureUpdReqd
    -- here:

    is_caf = isThunkRep (cit_rep info_tbl)

    padding
        | not is_caf = []
        | otherwise  = ASSERT(null payload) [mkIntCLit 0]

    static_link_field
        | is_caf || staticClosureNeedsLink (mayHaveCafRefs caf_refs) info_tbl
        = [static_link_value]
        | otherwise
        = []

    saved_info_field
        | is_caf     = [mkIntCLit 0]
        | otherwise  = []

        -- For a static constructor which has NoCafRefs, we set the
        -- static link field to a non-zero value so the garbage
        -- collector will ignore it.
    static_link_value
        | mayHaveCafRefs caf_refs  = mkIntCLit 0
        | otherwise                = mkIntCLit 1  -- No CAF refs


mkStaticClosure :: DynFlags -> CLabel -> CostCentreStack -> [CmmLit]
  -> [CmmLit] -> [CmmLit] -> [CmmLit] -> [CmmLit]
mkStaticClosure dflags info_lbl ccs payload padding static_link_field saved_info_field
  =  [CmmLabel info_lbl]
  ++ variable_header_words
  ++ concatMap padLitToWord payload
  ++ padding
  ++ static_link_field
  ++ saved_info_field
  where
    variable_header_words
        =  staticGranHdr
        ++ staticParHdr
        ++ staticProfHdr dflags ccs
        ++ staticTickyHdr

-- JD: Simon had ellided this padding, but without it the C back end asserts
-- failure. Maybe it's a bad assertion, and this padding is indeed unnecessary?
padLitToWord :: CmmLit -> [CmmLit]
padLitToWord lit = lit : padding pad_length
  where width = typeWidth (cmmLitType lit)
        pad_length = wORD_SIZE - widthInBytes width :: Int

        padding n | n <= 0 = []
                  | n `rem` 2 /= 0 = CmmInt 0 W8  : padding (n-1)
                  | n `rem` 4 /= 0 = CmmInt 0 W16 : padding (n-2)
                  | n `rem` 8 /= 0 = CmmInt 0 W32 : padding (n-4)
                  | otherwise      = CmmInt 0 W64 : padding (n-8)

-----------------------------------------------------------
--              Heap overflow checking
-----------------------------------------------------------

{- Note [Heap checks]
   ~~~~~~~~~~~~~~~~~~
Heap checks come in various forms.  We provide the following entry
points to the runtime system, all of which use the native C-- entry
convention.

  * gc() performs garbage collection and returns
    nothing to its caller

  * A series of canned entry points like
        r = gc_1p( r )
    where r is a pointer.  This performs gc, and
    then returns its argument r to its caller.

  * A series of canned entry points like
        gcfun_2p( f, x, y )
    where f is a function closure of arity 2
    This performs garbage collection, keeping alive the
    three argument ptrs, and then tail-calls f(x,y)

These are used in the following circumstances

* entryHeapCheck: Function entry
    (a) With a canned GC entry sequence
        f( f_clo, x:ptr, y:ptr ) {
             Hp = Hp+8
             if Hp > HpLim goto L
             ...
          L: HpAlloc = 8
             jump gcfun_2p( f_clo, x, y ) }
     Note the tail call to the garbage collector;
     it should do no register shuffling

    (b) No canned sequence
        f( f_clo, x:ptr, y:ptr, ...etc... ) {
          T: Hp = Hp+8
             if Hp > HpLim goto L
             ...
          L: HpAlloc = 8
             call gc()  -- Needs an info table
             goto T }

* altHeapCheck: Immediately following an eval
  Started as
        case f x y of r { (p,q) -> rhs }
  (a) With a canned sequence for the results of f
       (which is the very common case since
       all boxed cases return just one pointer
           ...
           r = f( x, y )
        K:      -- K needs an info table
           Hp = Hp+8
           if Hp > HpLim goto L
           ...code for rhs...

        L: r = gc_1p( r )
           goto K }

        Here, the info table needed by the call
        to gc_1p should be the *same* as the
        one for the call to f; the C-- optimiser
        spots this sharing opportunity)

   (b) No canned sequence for results of f
       Note second info table
           ...
           (r1,r2,r3) = call f( x, y )
        K:
           Hp = Hp+8
           if Hp > HpLim goto L
           ...code for rhs...

        L: call gc()    -- Extra info table here
           goto K

* generalHeapCheck: Anywhere else
  e.g. entry to thunk
       case branch *not* following eval,
       or let-no-escape
  Exactly the same as the previous case:

        K:      -- K needs an info table
           Hp = Hp+8
           if Hp > HpLim goto L
           ...

        L: call gc()
           goto K
-}

--------------------------------------------------------------
-- A heap/stack check at a function or thunk entry point.

entryHeapCheck :: ClosureInfo
               -> Maybe LocalReg -- Function (closure environment)
               -> Int            -- Arity -- not same as len args b/c of voids
               -> [LocalReg]     -- Non-void args (empty for thunk)
               -> FCode ()
               -> FCode ()

entryHeapCheck cl_info nodeSet arity args code
  = do dflags <- getDynFlags
       let is_thunk = arity == 0
           is_fastf = case closureFunInfo cl_info of
                           Just (_, ArgGen _) -> False
                           _otherwise         -> True

           args' = map (CmmReg . CmmLocal) args
           node = case nodeSet of
                      Just r  -> CmmReg (CmmLocal r)
                      Nothing -> CmmLit (CmmLabel $ staticClosureLabel cl_info)
           stg_gc_fun    = CmmReg (CmmGlobal GCFun)
           stg_gc_enter1 = CmmReg (CmmGlobal GCEnter1)

           {- Thunks:          jump stg_gc_enter_1

              Function (fast): call (NativeNode) stg_gc_fun(fun, args)

              Function (slow): R1 = fun
                               call (slow) stg_gc_fun(args)
               XXX: this is a bit naughty, we should really pass R1 as an
               argument and use a special calling convention.
           -}
           gc_call upd
               | is_thunk
                 = mkJump dflags stg_gc_enter1 [node] upd

               | is_fastf
                 = mkJump dflags stg_gc_fun (node : args') upd

               | otherwise
                 = mkAssign nodeReg node <*>
                   mkForeignJump dflags Slow stg_gc_fun args' upd

       updfr_sz <- getUpdFrameOff

       loop_id <- newLabelC
       emitLabel loop_id
       heapCheck True (gc_call updfr_sz <*> mkBranch loop_id) code

{-
    -- This code is slightly outdated now and we could easily keep the above
    -- GC methods. However, there may be some performance gains to be made by
    -- using more specialised GC entry points. Since the semi generic GCFun
    -- entry needs to check the node and figure out what registers to save...
    -- if we provided and used more specialised GC entry points then these
    -- runtime decisions could be turned into compile time decisions.

    args'     = case fun of Just f  -> f : args
                            Nothing -> args
    arg_exprs = map (CmmReg . CmmLocal) args'
    gc_call updfr_sz
        | arity == 0 = mkJumpGC (CmmReg (CmmGlobal GCEnter1)) arg_exprs updfr_sz
        | otherwise =
            case gc_lbl args' of
                Just _lbl -> panic "StgCmmHeap.entryHeapCheck: not finished"
                            -- mkJumpGC (CmmLit (CmmLabel (mkRtsCodeLabel lbl)))
                            --         arg_exprs updfr_sz
                Nothing  -> mkCall generic_gc (GC, GC) [] [] updfr_sz

    gc_lbl :: [LocalReg] -> Maybe FastString
    gc_lbl [reg]
        | isGcPtrType ty  = Just (sLit "stg_gc_unpt_r1") -- "stg_gc_fun_1p"
        | isFloatType ty  = case width of
                              W32 -> Just (sLit "stg_gc_f1")
                              W64 -> Just (sLit "stg_gc_d1")
                              _other -> Nothing
        | width == wordWidth = Just (mkGcLabel "stg_gc_unbx_r1")
        | width == W64       = Just (mkGcLabel "stg_gc_l1")
        | otherwise          = Nothing
        where
          ty = localRegType reg
          width = typeWidth ty

    gc_lbl regs = gc_lbl_ptrs (map (isGcPtrType . localRegType) regs)

    gc_lbl_ptrs :: [Bool] -> Maybe FastString
    -- JD: TEMPORARY -- UNTIL THESE FUNCTIONS EXIST...
    --gc_lbl_ptrs [True,True]      = Just (sLit "stg_gc_fun_2p")
    --gc_lbl_ptrs [True,True,True] = Just (sLit "stg_gc_fun_3p")
    gc_lbl_ptrs _ = Nothing
-}


-- ------------------------------------------------------------
-- A heap/stack check in a case alternative


-- If there are multiple alts and we need to GC, but don't have a
-- continuation already (the scrut was simple), then we should
-- pre-generate the continuation.  (if there are multiple alts it is
-- always a canned GC point).

-- altHeapCheck:
-- If we have a return continuation,
--   then if it is a canned GC pattern,
--           then we do mkJumpReturnsTo
--           else we do a normal call to stg_gc_noregs
--   else if it is a canned GC pattern,
--           then generate the continuation and do mkCallReturnsTo
--           else we do a normal call to stg_gc_noregs

altHeapCheck :: [LocalReg] -> FCode a -> FCode a
altHeapCheck regs code
  = case cannedGCEntryPoint regs of
      Nothing -> genericGC code
      Just gc -> do
        dflags <- getDynFlags
        lret <- newLabelC
        let (off, copyin) = copyInOflow dflags NativeReturn (Young lret) regs
        lcont <- newLabelC
        emitOutOfLine lret (copyin <*> mkBranch lcont)
        emitLabel lcont
        cannedGCReturnsTo False gc regs lret off code

altHeapCheckReturnsTo :: [LocalReg] -> Label -> ByteOff -> FCode a -> FCode a
altHeapCheckReturnsTo regs lret off code
  = case cannedGCEntryPoint regs of
      Nothing -> genericGC code
      Just gc -> cannedGCReturnsTo True gc regs lret off code

cannedGCReturnsTo :: Bool -> CmmExpr -> [LocalReg] -> Label -> ByteOff
                  -> FCode a
                  -> FCode a
cannedGCReturnsTo cont_on_stack gc regs lret off code
  = do dflags <- getDynFlags
       updfr_sz <- getUpdFrameOff
       heapCheck False (gc_call dflags gc updfr_sz) code
  where
    reg_exprs = map (CmmReg . CmmLocal) regs
      -- Note [stg_gc arguments]

    gc_call dflags label sp
      | cont_on_stack = mkJumpReturnsTo dflags label GC reg_exprs lret off sp
      | otherwise     = mkCallReturnsTo dflags label GC reg_exprs lret off sp (0,[])

genericGC :: FCode a -> FCode a
genericGC code
  = do updfr_sz <- getUpdFrameOff
       lretry <- newLabelC
       emitLabel lretry
       call <- mkCall generic_gc (GC, GC) [] [] updfr_sz (0,[])
       heapCheck False (call <*> mkBranch lretry) code

cannedGCEntryPoint :: [LocalReg] -> Maybe CmmExpr
cannedGCEntryPoint regs
  = case regs of
      []  -> Just (mkGcLabel "stg_gc_noregs")
      [reg]
          | isGcPtrType ty -> Just (mkGcLabel "stg_gc_unpt_r1")
          | isFloatType ty -> case width of
                                  W32       -> Just (mkGcLabel "stg_gc_f1")
                                  W64       -> Just (mkGcLabel "stg_gc_d1")
                                  _         -> Nothing
        
          | width == wordWidth -> Just (mkGcLabel "stg_gc_unbx_r1")
          | width == W64       -> Just (mkGcLabel "stg_gc_l1")
          | otherwise          -> Nothing
          where
              ty = localRegType reg
              width = typeWidth ty
      _otherwise -> Nothing

-- Note [stg_gc arguments]
-- It might seem that we could avoid passing the arguments to the
-- stg_gc function, because they are already in the right registers.
-- While this is usually the case, it isn't always.  Sometimes the
-- code generator has cleverly avoided the eval in a case, e.g. in
-- ffi/should_run/4221.hs we found
--
--   case a_r1mb of z
--     FunPtr x y -> ...
--
-- where a_r1mb is bound a top-level constructor, and is known to be
-- evaluated.  The codegen just assigns x, y and z, and continues;
-- R1 is never assigned.
--
-- So we'll have to rely on optimisations to eliminatethese
-- assignments where possible.


-- | The generic GC procedure; no params, no results
generic_gc :: CmmExpr
generic_gc = mkGcLabel "stg_gc_noregs"

-- | Create a CLabel for calling a garbage collector entry point
mkGcLabel :: String -> CmmExpr
mkGcLabel s = CmmLit (CmmLabel (mkCmmCodeLabel rtsPackageId (fsLit s)))

-------------------------------
heapCheck :: Bool -> CmmAGraph -> FCode a -> FCode a
heapCheck checkStack do_gc code
  = getHeapUsage $ \ hpHw ->
    -- Emit heap checks, but be sure to do it lazily so
    -- that the conditionals on hpHw don't cause a black hole
    do  { codeOnly $ do_checks checkStack hpHw do_gc
        ; tickyAllocHeap hpHw
        ; doGranAllocate hpHw
        ; setRealHp hpHw
        ; code }

do_checks :: Bool       -- Should we check the stack?
          -> WordOff    -- Heap headroom
          -> CmmAGraph  -- What to do on failure
          -> FCode ()
do_checks checkStack alloc do_gc = do
  gc_id <- newLabelC

  when checkStack $
     emit =<< mkCmmIfGoto sp_oflo gc_id

  when (alloc /= 0) $ do
     emitAssign hpReg bump_hp
     emit =<< mkCmmIfThen hp_oflo (alloc_n <*> mkBranch gc_id)

  emitOutOfLine gc_id $
     do_gc -- this is expected to jump back somewhere

                -- Test for stack pointer exhaustion, then
                -- bump heap pointer, and test for heap exhaustion
                -- Note that we don't move the heap pointer unless the
                -- stack check succeeds.  Otherwise we might end up
                -- with slop at the end of the current block, which can
                -- confuse the LDV profiler.
  where
    alloc_lit = CmmLit (mkIntCLit (alloc*wORD_SIZE)) -- Bytes
    bump_hp   = cmmOffsetExprB (CmmReg hpReg) alloc_lit

    -- Sp overflow if (Sp - CmmHighStack < SpLim)
    sp_oflo = CmmMachOp mo_wordULt
                  [CmmMachOp (MO_Sub (typeWidth (cmmRegType spReg)))
                             [CmmReg spReg, CmmLit CmmHighStackMark],
                   CmmReg spLimReg]

    -- Hp overflow if (Hp > HpLim)
    -- (Hp has been incremented by now)
    -- HpLim points to the LAST WORD of valid allocation space.
    hp_oflo = CmmMachOp mo_wordUGt
                  [CmmReg hpReg, CmmReg (CmmGlobal HpLim)]

    alloc_n = mkAssign (CmmGlobal HpAlloc) alloc_lit

{-

{- Unboxed tuple alternatives and let-no-escapes (the two most annoying
constructs to generate code for!)  For unboxed tuple returns, there
are an arbitrary number of possibly unboxed return values, some of
which will be in registers, and the others will be on the stack.  We
always organise the stack-resident fields into pointers &
non-pointers, and pass the number of each to the heap check code. -}

unbxTupleHeapCheck
        :: [(Id, GlobalReg)]    -- Live registers
        -> WordOff      -- no. of stack slots containing ptrs
        -> WordOff      -- no. of stack slots containing nonptrs
        -> CmmAGraph    -- code to insert in the failure path
        -> FCode ()
        -> FCode ()

unbxTupleHeapCheck regs ptrs nptrs fail_code code
  -- We can't manage more than 255 pointers/non-pointers
  -- in a generic heap check.
  | ptrs > 255 || nptrs > 255 = panic "altHeapCheck"
  | otherwise
  = initHeapUsage $ \ hpHw -> do
        { codeOnly $ do { do_checks 0 {- no stack check -} hpHw
                                    full_fail_code rts_label
                        ; tickyAllocHeap hpHw }
        ; setRealHp hpHw
        ; code }
  where
    full_fail_code  = fail_code `plusStmts` oneStmt assign_liveness
    assign_liveness = CmmAssign (CmmGlobal (VanillaReg 9))      -- Ho ho ho!
                                (CmmLit (mkWordCLit liveness))
    liveness        = mkRegLiveness regs ptrs nptrs
    rts_label       = CmmLit (CmmLabel (mkRtsCodeLabel (sLit "stg_gc_ut")))


{- Old Gransim com -- I have no idea whether it still makes sense (SLPJ Sep07)
For GrAnSim the code for doing a heap check and doing a context switch
has been separated. Especially, the HEAP_CHK macro only performs a
heap check. THREAD_CONTEXT_SWITCH should be used for doing a context
switch. GRAN_FETCH_AND_RESCHEDULE must be put at the beginning of
every slow entry code in order to simulate the fetching of
closures. If fetching is necessary (i.e. current closure is not local)
then an automatic context switch is done. -}


When failing a check, we save a return address on the stack and
jump to a pre-compiled code fragment that saves the live registers
and returns to the scheduler.

The return address in most cases will be the beginning of the basic
block in which the check resides, since we need to perform the check
again on re-entry because someone else might have stolen the resource
in the meantime.

%************************************************************************
%*                                                                      *
     Generic Heap/Stack Checks - used in the RTS
%*                                                                      *
%************************************************************************

\begin{code}
hpChkGen :: CmmExpr -> CmmExpr -> CmmExpr -> FCode ()
hpChkGen bytes liveness reentry
  = do_checks' bytes True assigns stg_gc_gen
  where
    assigns = mkStmts [
                CmmAssign (CmmGlobal (VanillaReg 9))  liveness,
                CmmAssign (CmmGlobal (VanillaReg 10)) reentry
                ]

-- a heap check where R1 points to the closure to enter on return, and
-- we want to assign to Sp[0] on failure (used in AutoApply.cmm:BUILD_PAP).
hpChkNodePointsAssignSp0 :: CmmExpr -> CmmExpr -> FCode ()
hpChkNodePointsAssignSp0 bytes sp0
  = do_checks' bytes True assign stg_gc_enter1
  where assign = oneStmt (CmmStore (CmmReg spReg) sp0)

stg_gc_gen    = CmmLit (CmmLabel (mkRtsCodeLabel (sLit "stg_gc_gen")))
\end{code}

-}
