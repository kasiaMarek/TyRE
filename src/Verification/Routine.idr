module Verification.Routine

import NFA
import Evidence
import Verification.AcceptingPath
import Extra
import Data.List
import Core
import Codes
import Data.SnocList

public export
data ExtendedInstruction = Regular Instruction | Observe Char

public export
ExtendedRoutine : Type
ExtendedRoutine = List ExtendedInstruction

public export
executeRoutineSteps : ExtendedRoutine -> (Maybe Char, VMState)
                    -> (Maybe Char, VMState)
executeRoutineSteps []                    st       = st
executeRoutineSteps (Regular inst :: r)   (mc, vm) =
  executeRoutineSteps r (mc, stepForInstruction mc inst vm)
executeRoutineSteps (Observe c :: r)      (mc, vm) =
  executeRoutineSteps r (Just c, (step c vm))


public export
executeRoutineFrom: ExtendedRoutine -> (Maybe Char, VMState) -> Evidence
executeRoutineFrom routine st = (snd $ executeRoutineSteps routine st).evidence

public export
executeRoutine: ExtendedRoutine -> Evidence
executeRoutine routine = executeRoutineFrom routine (Nothing, initVM)

public export
routineComposition  : (xs: ExtendedRoutine) -> (ys: ExtendedRoutine)
                    -> (st: (Maybe Char, VMState))
                    -> (executeRoutineSteps (xs ++ ys) st
                          = executeRoutineSteps ys (executeRoutineSteps xs st))
routineComposition []                     ys st           = Refl
routineComposition ((Regular inst) :: xs) ys (mc, vm)     =
  routineComposition xs ys (mc, stepForInstruction mc inst vm)
routineComposition ((Observe c) :: xs)    ys (mc, vm)     =
  routineComposition xs ys (Just c, (step c vm))

public export
Cast Routine ExtendedRoutine where
  cast [] = []
  cast (inst :: insts) = (Regular inst)::(cast insts)

public export
castConcat : (xs: Routine) -> (ys: Routine)
          -> ((the ExtendedRoutine $ cast (xs ++ ys)) = cast xs ++ cast ys)
castConcat [] ys = Refl
castConcat (x :: xs) ys = cong (Regular x ::) (castConcat xs ys)

public export
execEqualityPrf : {nfa : NA} -> (vmState : VMState)
                -> (r : Routine) -> (mc : Maybe Char)
                -> (executeRoutineSteps (cast r) (mc, vmState)
                        = (mc, execute mc r vmState))

execEqualityPrf vmState [] mc = Refl
execEqualityPrf vmState (x :: xs) mc =
  execEqualityPrf {nfa} (stepForInstruction mc x vmState) xs mc

parameters {auto sm : SM}

  public export
  stepOfExtractRoutine : {s : sm.State}
                    -> (acc: AcceptingFrom (smToNFA sm) s word)
                    -> ExtendedRoutine

  stepOfExtractRoutine {word=[]} (Accept s prf) = []
  stepOfExtractRoutine {word=c::_} (Step s c t prf acc)
    = Observe c :: (cast $ extractBasedOnFst (sm.next s c) prf)

  public export
  extractRoutineFrom : {s : sm.State}
                    -> (acc: AcceptingFrom (smToNFA sm) s word)
                    -> ExtendedRoutine

  extractRoutineFrom {word=[]} (Accept s prf) = []
  extractRoutineFrom {word=c::_} (Step s c t prf acc) =
    (stepOfExtractRoutine (Step {nfa = (smToNFA sm)} s c t prf acc))
        ++ (extractRoutineFrom acc)

  public export
  extractRoutine : Accepting (smToNFA sm) word -> ExtendedRoutine
  extractRoutine (Start s prf acc) =
    let r         : Routine
        r         = extractBasedOnFst (sm.start) prf
        extr      : ExtendedRoutine
        extr      = cast r
        rest      : ExtendedRoutine
        rest      = extractRoutineFrom acc
    in (extr ++ rest)

  public export
  extractRoutineFromPrf :   (td : Thread sm.State)
                        ->  (acc: AcceptingFrom (smToNFA sm) td.naState word)
                        ->  (mc : Maybe Char)
                        ->  (executeRoutineFrom (extractRoutineFrom acc) (mc, td.vmState)
                              = extractEvidenceFrom td acc)

  extractRoutineFromPrf {word=[]} td (Accept td.naState prf) mc = Refl
  extractRoutineFromPrf {word=c::_} td (Step td.naState c t prf acc) mc =
    let r         : Routine
        r         = extractBasedOnFst (sm.next td.naState c) prf
        td'       : Thread sm.State
        td'       = runFunction c td (t,r)
        extr      : ExtendedRoutine
        extr      =  Observe c :: cast r
        rest      : ExtendedRoutine
        rest      = extractRoutineFrom acc

        restPrf   := extractRoutineFromPrf td' acc (Just c)
        prf       : (executeRoutineSteps (extr ++ rest) (mc, td.vmState)
                      = executeRoutineSteps rest (Just c, td'.vmState))
        prf       = trans
                      (routineComposition extr rest (mc, td.vmState))
                      (cong
                        (executeRoutineSteps rest)
                        (execEqualityPrf {nfa = (smToNFA sm)} _ _ _)
                      )
    in (trans (cong (\e => (snd e).evidence) prf) restPrf)

  public export
  extractRoutinePrf : (acc: Accepting (smToNFA sm) word)
                    -> (executeRoutine (extractRoutine acc) = extractEvidence acc)

  extractRoutinePrf (Start s prf acc) =
    let r        : Routine
        r        = extractBasedOnFst sm.start prf
        td       : Thread sm.State
        td       = initFuction (s,r)
        extr     : ExtendedRoutine
        extr     = cast r
        rest     : ExtendedRoutine
        rest     = extractRoutineFrom acc

        restPrf := extractRoutineFromPrf td acc Nothing
        prf     : (executeRoutineSteps (extr ++ rest) (Nothing, MkVMState False [<] [<])
                    = executeRoutineSteps rest (Nothing, td.vmState))
        prf     = trans
                  (routineComposition extr rest (Nothing, MkVMState False [<] [<]))
                  (cong
                    (executeRoutineSteps rest)
                    (execEqualityPrf {nfa = (smToNFA sm)} _ _ _)
                  )
    in (trans (cong (\e => (snd e).evidence) prf) restPrf)
