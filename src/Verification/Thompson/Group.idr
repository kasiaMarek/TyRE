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
import Syntax.PreorderReasoning

import Data.SnocList
import Data.List.Elem
import Data.List

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
                        -> (extractRoutine {sm = thompson (Group re)} acc === [Regular Record] ++ map Observe word ++ [Regular EmitString])

thompsonRoutinePrfGroup re {word = []} (Start Nothing prf Accept) =
  let (pos'' ** rw1) = mapRoutineSpec ? ? prf
      (pos' ** rw2) = addEndRoutineSpecForNothing [EmitString]
                                                    (mapRoutine (const []) (thompson re).start)
                                                    pos''
      rw3 = constIdSpec ((thompson re).start) pos'
  in Calc $
      |~ cast (extractBasedOnFst (mapRoutine (Record::) (addEndRoutine [EmitString] (mapRoutine (const []) (thompson re).start))) prf) ++ []
      ~~ cast (extractBasedOnFst (mapRoutine (Record::) (addEndRoutine [EmitString] (mapRoutine (const []) (thompson re).start))) prf) ... appendNilRightNeutral _
      ~~ (Regular Record) :: cast (extractBasedOnFst (addEndRoutine [EmitString] (mapRoutine (const []) (thompson re) .start)) pos'') ... cong cast rw1
      ~~ (Regular Record) :: cast (extractBasedOnFst (mapRoutine (const []) (thompson re) .start) pos' ++ [EmitString]) ... cong (\x => (Regular Record) :: cast x) rw2
      ~~ [Regular Record, Regular EmitString] ...  cong (\x => (Regular Record) :: cast (x ++ [EmitString])) rw3

thompsonRoutinePrfGroup re {word} (Start (Just s) prf acc) = 
  let (pos'' ** rw1) = mapRoutineSpec ? ? prf
      (pos' ** rw2) = addEndRoutineSpecForJust  [EmitString]
                                                  (mapRoutine (const []) (thompson re).start)
                                                  s
                                                  pos''
      rw3 = constIdSpec (thompson re).start pos'
      tail = thompsonRoutineFromPrfGroup {word} re s acc
  in rewrite tail in Calc $
      |~ cast (extractBasedOnFst (mapRoutine (Record::) (addEndRoutine [EmitString] (mapRoutine (const []) (thompson re) .start))) prf) ++ (map Observe word ++ [Regular EmitString])
      ~~ [Regular Record] ++ cast (extractBasedOnFst (addEndRoutine [EmitString] (mapRoutine (const []) (thompson re) .start)) pos'') ++ (map Observe word ++ [Regular EmitString]) ... cong (\x => cast x ++ (map Observe word ++ [Regular EmitString])) rw1
      ~~ [Regular Record] ++ cast (extractBasedOnFst (mapRoutine (const []) (thompson re) .start) pos') ++ (map Observe word ++ [Regular EmitString]) ... cong (\x => [Regular Record] ++ cast x ++ (map Observe word ++ [Regular EmitString])) rw2
      ~~ [Regular Record] ++ map Observe word ++ [Regular EmitString] ... cong (\x => [Regular Record] ++ cast x ++ (map Observe word ++ [Regular EmitString])) rw3

export
runGroupRoutine : (word : List Char) 
                -> (mcvm : (Maybe Char, VMState)) 
                -> (snocWord : SnocList Char ** 
                      (Builtin.snd (executeRoutineSteps (map Observe word ++ [Regular EmitString]) mcvm)).evidence = (Builtin.snd mcvm).evidence :< GroupMark snocWord)
runGroupRoutine [] (_, vm) = (vm.memory ** Refl)
runGroupRoutine (x :: xs) (mc, vm) = runGroupRoutine xs (Just x, step x vm)

