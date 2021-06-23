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


executeRoutineSteps: ExtendedRoutine -> (Maybe Char, VMState) -> (Maybe Char, VMState)
executeRoutineSteps []                    st       = st
executeRoutineSteps ((Regular inst)::r)   (mc, vm) = executeRoutineSteps r (mc, stepForInstruction mc inst vm)
executeRoutineSteps ((Observe c)::r)      (mc, vm) = executeRoutineSteps r (Just c, (step c vm))

public export
executeRoutineFrom: ExtendedRoutine -> (Maybe Char, VMState) -> Evidence
executeRoutineFrom routine st = (snd $ executeRoutineSteps routine st).evidence

public export
executeRoutine: ExtendedRoutine -> Evidence
executeRoutine routine = executeRoutineFrom routine (Nothing, initVM)

public export
routineComposition  : (xs: ExtendedRoutine) -> (ys: ExtendedRoutine) -> (st:(Maybe Char, VMState))
                  -> (executeRoutineSteps (xs ++ ys) st = executeRoutineSteps ys (executeRoutineSteps xs st))
routineComposition []                     ys st           = Refl
routineComposition ((Regular inst) :: xs) ys (mc, vm)     = routineComposition xs ys (mc, stepForInstruction mc inst vm)
routineComposition ((Observe c) :: xs)    ys (mc, vm)     = routineComposition xs ys (Just c, (step c vm))

public export
mapRoutine : Maybe Char -> Routine -> ExtendedRoutine
mapRoutine Nothing [] = []
mapRoutine Nothing (inst :: insts) = (Regular inst)::(mapRoutine Nothing insts)
mapRoutine (Just c) insts = (Observe c)::(mapRoutine Nothing insts)

public export
execEqualityPrf : {nfa : NA} -> (vmState : VMState) -> (r : Routine) -> (mc : Maybe Char)
                -> (executeRoutineSteps (mapRoutine Nothing r) (mc, vmState) = (mc, execute mc r vmState))
execEqualityPrf vmState [] mc = Refl
execEqualityPrf vmState (x :: xs) mc = execEqualityPrf {nfa} (stepForInstruction mc x vmState) xs mc

public export
stepOfExtractRoutine : {nfa : NA} -> {prog : Program nfa} -> {s : nfa.State}
                  -> (acc: AcceptingFrom nfa s word)
                  -> ExtendedRoutine
stepOfExtractRoutine {word=[]} {nfa} {prog} (Accept s prf) = []
stepOfExtractRoutine {word=c::_} {nfa} {prog} (Step s c t prf acc) = mapRoutine (Just c) (extractBasedOnFst (nfa.next s c) (prog.next s c) t prf)

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
  let r : Routine
      r = extractBasedOnFst (nfa.start) (prog.init) s prf
      extr : ExtendedRoutine
      extr = mapRoutine Nothing r
      nRout : ExtendedRoutine
      nRout = extractRoutineFrom {nfa, prog} acc
  in (extr ++ nRout)

public export
extractRoutineFromPrf : {nfa : NA} -> {prog : Program nfa}
                  -> (td : Thread nfa) -> (acc: AcceptingFrom nfa td.naState word)
                  -> (mc : Maybe Char)
                  -> (executeRoutineFrom (extractRoutineFrom {nfa, prog} acc) (mc, td.vmState) = extractEvidenceFrom td acc)
extractRoutineFromPrf {word=[]} {nfa} {prog} td (Accept td.naState prf) mc = Refl
extractRoutineFromPrf {word=c::_} {nfa} {prog} td (Step td.naState c t prf acc) mc =
  let r : Routine
      r = extractBasedOnFst (nfa.next td.naState c) (prog.next td.naState c) t prf
      td' : Thread nfa
      td' = runFunction c td (t,r)
      nRout : ExtendedRoutine
      nRout = extractRoutineFrom {nfa,prog} acc
      nPrf := extractRoutineFromPrf {nfa,prog} td' acc (Just c)
      extr : ExtendedRoutine
      extr = mapRoutine (Just c) r
      prf0: (executeRoutineSteps extr (mc, td.vmState) = (Just c, td'.vmState))
      prf0 = (execEqualityPrf {nfa} _ _ _)
      prf: (executeRoutineSteps (extr ++ nRout) (mc, td.vmState) = executeRoutineSteps nRout (Just c, td'.vmState))
      prf = trans (routineComposition extr nRout (mc, td.vmState)) (cong (executeRoutineSteps nRout) prf0)
  in (trans (cong (\e => (snd e).evidence) prf) nPrf)

public export
extractRoutinePrf  : (nfa : NA) -> (prog : Program nfa) -> (acc: Accepting nfa word)
                -> (executeRoutine (extractRoutine nfa prog acc) = extractEvidence acc)
extractRoutinePrf nfa prog (Start s prf acc) =
  let r : Routine
      r = extractBasedOnFst (nfa .start) (prog .init) s prf
      td : Thread nfa
      td = initFuction (s,r)
      extr : ExtendedRoutine
      extr = mapRoutine Nothing r
      nRout : ExtendedRoutine
      nRout = extractRoutineFrom acc
      nPrf := extractRoutineFromPrf td acc Nothing
      prf0: (executeRoutineSteps extr (Nothing, MkVMState False [<] [<]) = (Nothing, td.vmState))
      prf0 = (execEqualityPrf {nfa} _ _ _)
      prf: (executeRoutineSteps (extr ++ nRout) (Nothing, MkVMState False [<] [<]) = executeRoutineSteps nRout (Nothing, td.vmState))
      prf = trans (routineComposition extr nRout (Nothing, MkVMState False [<] [<])) (cong (executeRoutineSteps nRout) prf0)
  in (trans (cong (\e => (snd e).evidence) prf) nPrf)
