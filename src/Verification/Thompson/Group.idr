module Verification.Thompson.Group

import Core
import Thompson
import Thompson.GroupThompson
import NFA
import Evidence
import Extra
import Extra.Pred

import Verification.AcceptingPath
import Verification.Routine
import Verification.Thompson.Common
import Syntax.PreorderReasoning

import Data.SnocList
import Data.List.Elem
import Data.List

constIdSpec : (xs : List (Maybe Nat)) 
            -> (isElem : x `Elem` map Builtin.fst (addEmptyRoutine xs)) 
            -> (extractBasedOnFst (addEmptyRoutine xs) isElem = [])
constIdSpec (_ :: _) Here = Refl
constIdSpec (_ :: xs) (There pos) = constIdSpec xs pos

thompsonRoutineFromPrfGroup : (groupSM : GroupSM)
                            -> {word : Word}
                            -> (s : Nat)
                            -> (acc : AcceptingFrom (smToNFA (smFromGroupSM groupSM)) (Just s) word)
                            -> (extractRoutineFrom {sm = (smFromGroupSM groupSM)} acc = (map Observe word) ++ [Regular EmitString])

thompsonRoutineFromPrfGroup groupSM s (Step s c Nothing prf Accept) = 
  let isElemrw1 : ?
      isElemrw1 = addEndRoutineSpecForNothing [EmitString] _ prf
      rw2 : ?
      rw2 = constIdSpec _ isElemrw1.fst
  in rewrite isElemrw1.snd in rewrite rw2 in Refl

thompsonRoutineFromPrfGroup {word = c :: word'} groupSM s (Step s c (Just t) prf acc) = 
  let isElemrw1 : ?
      isElemrw1 = addEndRoutineSpecForJust [EmitString] _ t prf
      rw2 : ?
      rw2 = constIdSpec _ isElemrw1.fst
      tail : ?
      tail = thompsonRoutineFromPrfGroup groupSM t acc
  in cong (Observe c ::) (rewrite isElemrw1.snd in rewrite rw2 in tail)

thompsonRoutinePrfGroupAux : (groupSM : GroupSM)
                          -> {word : Word}
                          -> (acc : Accepting (smToNFA (smFromGroupSM groupSM)) word)
                          -> (extractRoutine {sm = (smFromGroupSM groupSM)} acc === [Regular Record] ++ map Observe word ++ [Regular EmitString])

thompsonRoutinePrfGroupAux (MkGroupSM initStates statesWithNext _) (Start Nothing prf Accept) = 
  let (pos'' ** rw1) = mapRoutineSpec _ _ prf
      (pos' ** rw2) = addEndRoutineSpecForNothing [EmitString] _ pos''
  in Calc $
    |~ (cast (extractBasedOnFst (mapRoutine (Record ::) (addEndRoutine [EmitString] (addEmptyRoutine initStates))) prf) ++ [])
    ~~ (cast (Record :: extractBasedOnFst (addEndRoutine [EmitString] (addEmptyRoutine initStates)) pos'') ++ []) ... cong (\x => cast x ++ []) rw1
    ~~ (cast (Record :: extractBasedOnFst (addEmptyRoutine initStates) pos' ++ [EmitString]) ++ []) ... cong (\x => cast (Record :: x) ++ []) rw2
    ~~ [Regular Record, Regular EmitString] ... cong (\x => Regular Record :: cast (x ++ [EmitString]) ++ []) (constIdSpec _ _)

thompsonRoutinePrfGroupAux groupSM (Start (Just s) prf acc) = 
  let (pos'' ** rw1) = mapRoutineSpec ? ? prf
      (pos' ** rw2) = addEndRoutineSpecForJust  [EmitString]
                                                  _
                                                  s
                                                  pos''
      rw3 = constIdSpec _ pos'
      tail = thompsonRoutineFromPrfGroup groupSM s acc
  in rewrite tail in Calc $ 
      |~ cast (extractBasedOnFst (mapRoutine (Record ::) (addEndRoutine [EmitString] (addEmptyRoutine (groupSM.initStates)))) prf) ++ (map Observe word ++ [Regular EmitString])
      ~~ [Regular Record] ++ cast (extractBasedOnFst (addEndRoutine [EmitString] (addEmptyRoutine groupSM.initStates)) pos'') ++ (map Observe word ++ [Regular EmitString]) ... cong (\x => cast x ++ (map Observe word ++ [Regular EmitString])) rw1
      ~~ [Regular Record] ++ cast (extractBasedOnFst (addEmptyRoutine groupSM.initStates) pos') ++ (map Observe word ++ [Regular EmitString]) ... cong (\x => [Regular Record] ++ cast x ++ (map Observe word ++ [Regular EmitString])) rw2
      ~~ Regular Record :: (map Observe word ++ [Regular EmitString]) ... cong (\x => [Regular Record] ++ cast x ++ (map Observe word ++ [Regular EmitString])) rw3

export
thompsonRoutinePrfGroup : (re : CoreRE)
                        -> {word : Word}
                        -> (acc : Accepting (smToNFA (thompson (Group re))) word)
                        -> (extractRoutine {sm = thompson (Group re)} acc === [Regular Record] ++ map Observe word ++ [Regular EmitString])

thompsonRoutinePrfGroup re acc = thompsonRoutinePrfGroupAux _ acc

export
runGroupRoutine : (word : List Char) 
                -> (mcvm : (Maybe Char, VMState)) 
                -> (snocWord : SnocList Char ** 
                      (Builtin.snd (executeRoutineSteps (map Observe word ++ [Regular EmitString]) mcvm)).evidence = (Builtin.snd mcvm).evidence :< GroupMark snocWord)
runGroupRoutine [] (_, vm) = (vm.memory ** Refl)
runGroupRoutine (x :: xs) (mc, vm) = runGroupRoutine xs (Just x, step x vm)

