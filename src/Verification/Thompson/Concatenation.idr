module Verification.Thompson.Concatenation

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

nothingInMapStates : (xs : List (Maybe s, Routine)) 
                  -> Nothing `Elem` map Builtin.fst (mapStates f xs) 
                  -> Nothing `Elem` map Builtin.fst xs
nothingInMapStates [] x = absurd x
nothingInMapStates ((Nothing, _) :: xs) Here = Here
nothingInMapStates (x :: xs) (There pos) = There (nothingInMapStates xs pos)

export
thompsonRoutinePrfConcatTail : (re1 : CoreRE)
                            -> (re2 : CoreRE)
                            -> (s : (thompson re2).State)
                            -> {word : Word}
                            -> (acc : AcceptingFrom (smToNFA (thompson (Concat re1 re2))) (Just (Right s)) word)
                            -> PathFromWithRoutine 
                                re2
                                s
                                (\r2 => extractRoutineFrom {sm = (thompson $ Concat re1 re2)} acc 
                                          = r2 ++ [Regular EmitPair])

thompsonRoutinePrfConcatTail re1 re2 s acc = ?thompsonRoutinePrfConcatTail_rhs_1

export
thompsonRoutinePrfConcatFrom : (re1 : CoreRE)
                            -> (re2 : CoreRE)
                            -> (s : (thompson re1).State)
                            -> {word : Word}
                            -> (acc : AcceptingFrom (smToNFA (thompson (Concat re1 re2))) (Just (Left s)) word)
                            -> PathFromWithRoutine 
                                re1
                                s
                                (\r1 => PathWithRoutine 
                                        re2 
                                        (\r2 => extractRoutineFrom {sm = (thompson $ Concat re1 re2)} acc 
                                                  = r1 ++ r2 ++ [Regular EmitPair]))

export
thompsonRoutinePrfConcat : (re1 : CoreRE)
                        -> (re2 : CoreRE)
                        -> {word : Word}
                        -> (acc : Accepting (smToNFA (thompson (Concat re1 re2))) word)
                        -> PathWithRoutine 
                            re1 
                            (\r1 => PathWithRoutine 
                                    re2 
                                    (\r2 => extractRoutine {sm = (thompson $ Concat re1 re2)} acc 
                                              = r1 ++ r2 ++ [Regular EmitPair]))

thompsonRoutinePrfConcat {word = []} re1 re2 (Start Nothing prf Accept) =
  let (isElem1 ** rw1) := addEndRoutineSpecForNothing [EmitPair] ? prf
      (npos ** (npos' ** rw2)) := addEndTransactionSpecForNothing ? Nothing (\x => absurd x) isElem1
  in PWR  [] 
          (Start {nfa = smToNFA (thompson re1)} Nothing npos (Accept {nfa = smToNFA (thompson re1)})) 
          (PWR  []
                (Start {nfa = smToNFA (thompson re2)} Nothing (nothingInMapStates (thompson re2).start npos') (Accept {nfa = smToNFA (thompson re2)}))
                (?presTail))
thompsonRoutinePrfConcat {word = c::cs} re1 re2 (Start (Just (Right s)) prf (Step (Right s) c t y z)) =
  let (isElem1 ** rw1) := addEndRoutineSpecForJust [EmitPair] ? (Right s) prf
      (npos ** (npos' ** rw2)) := addEndTransactionSpecForNothing ? (Just (Right s)) (\x => absurd (eqForJust x)) isElem1
  in PWR [] 
      (Start {nfa = smToNFA (thompson re1)} Nothing npos (Accept {nfa = smToNFA (thompson re1)})) 
      (PWR  ?word2
            (Start {nfa = smToNFA (thompson re2)} (Just s) ?isElem3 ?acc)
            ?tail2)
thompsonRoutinePrfConcat {word = c::cs} re1 re2 (Start (Just (Left x)) prf (Step (Left x) c t y z)) = ?thompsonRoutinePrfConcat_rhs_3
