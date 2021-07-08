module Verification.Routine

import NFA
import NFA.Thompson
import Evidence
import Verification.AcceptingPath
import Extra
import Data.List
import Core
import Codes
import Data.SnocList
import Data.SnocList.Extra

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

public export
stepOfExtractRoutine : {nfa : NA} -> {prog : Program nfa} -> {s : nfa.State}
                  -> (acc: AcceptingFrom nfa s word)
                  -> ExtendedRoutine

stepOfExtractRoutine {word=[]} {nfa} {prog} (Accept s prf) = []
stepOfExtractRoutine {word=c::_} {nfa} {prog} (Step s c t prf acc)
  = Observe c :: (cast $ extractBasedOnFst (nfa.next s c) (prog.next s c) prf)

public export
extractRoutineFrom : {nfa : NA} -> {prog : Program nfa} -> {s : nfa.State}
                  -> (acc: AcceptingFrom nfa s word)
                  -> ExtendedRoutine

extractRoutineFrom {word=[]} {nfa} {prog} (Accept s prf) = []
extractRoutineFrom {word=c::_} {nfa} {prog} (Step s c t prf acc) =
  (stepOfExtractRoutine {nfa,prog} (Step s c t prf acc))
      ++ (extractRoutineFrom {nfa,prog} acc)

public export
extractRoutine : (nfa: NA) -> Program nfa -> Accepting nfa word -> ExtendedRoutine
extractRoutine nfa prog (Start s prf acc) =
  let r         : Routine
      r         = extractBasedOnFst (nfa.start) (prog.init) prf
      extr      : ExtendedRoutine
      extr      = cast r
      rest      : ExtendedRoutine
      rest      = extractRoutineFrom {nfa, prog} acc
  in (extr ++ rest)

public export
extractRoutineFromPrf : {nfa : NA} -> {prog : Program nfa}
                      -> (td : Thread nfa)
                      -> (acc: AcceptingFrom nfa td.naState word)
                      -> (mc : Maybe Char)
                      -> (executeRoutineFrom (extractRoutineFrom {nfa, prog} acc) (mc, td.vmState)
                            = extractEvidenceFrom td acc)

extractRoutineFromPrf {word=[]} {nfa} {prog} td (Accept td.naState prf) mc = Refl
extractRoutineFromPrf {word=c::_} {nfa} {prog} td (Step td.naState c t prf acc) mc =
  let r         : Routine
      r         = extractBasedOnFst (nfa.next td.naState c) (prog.next td.naState c) prf
      td'       : Thread nfa
      td'       = runFunction c td (t,r)
      extr      : ExtendedRoutine
      extr      =  Observe c :: cast r
      rest      : ExtendedRoutine
      rest      = extractRoutineFrom {nfa,prog} acc

      restPrf   := extractRoutineFromPrf {nfa,prog} td' acc (Just c)
      prf       : (executeRoutineSteps (extr ++ rest) (mc, td.vmState)
                    = executeRoutineSteps rest (Just c, td'.vmState))
      prf       = trans
                    (routineComposition extr rest (mc, td.vmState))
                    (cong
                      (executeRoutineSteps rest)
                      (execEqualityPrf {nfa} _ _ _)
                    )
  in (trans (cong (\e => (snd e).evidence) prf) restPrf)

public export
extractRoutinePrf  : (nfa : NA) -> (prog : Program nfa) -> (acc: Accepting nfa word)
                -> (executeRoutine (extractRoutine nfa prog acc) = extractEvidence acc)

extractRoutinePrf nfa prog (Start s prf acc) =
  let r        : Routine
      r        = extractBasedOnFst (nfa .start) (prog .init) prf
      td       : Thread nfa
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
                  (execEqualityPrf {nfa} _ _ _)
                )
  in (trans (cong (\e => (snd e).evidence) prf) restPrf)
