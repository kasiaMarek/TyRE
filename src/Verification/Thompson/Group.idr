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

thompsonRoutinePrfGroupAux : (groupSM : GroupSM)
                          -> {word : Word}
                          -> (acc : Accepting (smToNFA (smFromGroupSM groupSM)) word)
                          -> (extractRoutine {sm = (smFromGroupSM groupSM)} acc === [Regular Record] ++ map Observe word ++ [Regular EmitString])

thompsonRoutinePrfGroupAux groupSM acc = believe_me 1

-- thompsonRoutinePrfGroupAux (MkGroupSM initStates statesWithNext _) (Start Nothing prf Accept) = 
--   let (pos'' ** rw1) = mapRoutineSpec ? ? prf
--       (pos' ** rw2) = addEndRoutineSpecForNothing [EmitString] _ pos''
--   in Calc $ ?l

-- thompsonRoutinePrfGroupAux (MkGroupSM initStates statesWithNext _) (Start (Just x) prf (Step x c t y z)) = ?thompsonRoutinePrfGroupAux_rhs_3

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

