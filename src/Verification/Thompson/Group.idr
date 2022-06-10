module Verification.Thompson.Group

import Core
import Thompson
import NFA
import Evidence
import Extra
import Extra.Pred

import Verification.AcceptingPath
import Verification.Routine
import Verification.Thompson.Common

import Data.SnocList
import Data.List.Elem

constIdSpec : (xs : List (state, Routine)) 
            -> (isElem : x `Elem` map Builtin.fst (mapRoutine (const []) xs)) 
            -> (extractBasedOnFst (mapRoutine (const []) xs) isElem = [])
constIdSpec ((st, r) :: xs) Here = Refl
constIdSpec (_       :: xs) (There pos) = constIdSpec xs pos


thompsonRoutineFromPrfGroup : (re : CoreRE)
                            -> {word : Word}
                            -> (s : (thompson (Group re)).State)
                            -> (acc : AcceptingFrom (smToNFA (thompson (Group re))) (Just s) word)
                            -> (extractRoutineFrom {sm = thompson (Group re)} acc = (map Observe word) ++ [Regular EmitString])

thompsonRoutineFromPrfGroup re s (Step s c Nothing prf Accept) = 
  let (isElem ** rw1) = addEndRoutineSpecForNothing [EmitString]
                                                    (mapRoutine (const []) ((thompson re).next s c))
                                                    prf

      rw2 = constIdSpec ((thompson re).next s c) isElem
  in rewrite rw1 in rewrite rw2 in Refl

thompsonRoutineFromPrfGroup {word = c :: word'} re s (Step s c (Just t) prf acc) = 
  let (isElem ** rw1) = addEndRoutineSpecForJust  [EmitString]
                                                  (mapRoutine (const []) ((thompson re).next s c))
                                                  t
                                                  prf

      rw2 = constIdSpec ((thompson re).next s c) isElem
      tail = thompsonRoutineFromPrfGroup {word = word'} re t acc
  in cong (Observe c ::) (rewrite rw1 in rewrite rw2 in tail)


export
thompsonRoutinePrfGroup : (re : CoreRE)
                        -> {word : Word}
                        -> (acc : Accepting (smToNFA (thompson (Group re))) word)
                        -> (extractRoutine {sm = thompson (Group re)} acc === map Observe word ++ [Regular EmitString])

thompsonRoutinePrfGroup re {word = []} (Start Nothing prf Accept) =
  let (isElem ** rw1) = addEndRoutineSpecForNothing [EmitString]
                                                    (mapRoutine (const []) (thompson re).start)
                                                    prf
      rw2 = constIdSpec ((thompson re).start) isElem
  in rewrite rw1 in rewrite rw2 in Refl

thompsonRoutinePrfGroup re {word} (Start (Just s) prf acc) = 
  let (isElem ** rw1) = addEndRoutineSpecForJust  [EmitString]
                                                  (mapRoutine (const []) (thompson re).start)
                                                  s
                                                  prf
      rw2 = constIdSpec (thompson re).start isElem
      tail = thompsonRoutineFromPrfGroup {word} re s acc
  in rewrite rw1 in rewrite rw2 in tail

export
runGroupRoutine : (word : List Char) 
                -> (mcvm : (Maybe Char, VMState)) 
                -> (snocWord : SnocList Char ** 
                      (Builtin.snd (executeRoutineSteps (map Observe word ++ [Regular EmitString]) mcvm)).evidence = (Builtin.snd mcvm).evidence :< GroupMark snocWord)
runGroupRoutine [] (_, vm) = (vm.memory ** Refl)
runGroupRoutine (x :: xs) (mc, vm) = runGroupRoutine xs (Just x, step x vm)

