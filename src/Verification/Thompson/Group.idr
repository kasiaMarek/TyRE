module Verification.Thompson.Group

import Core
import Evidence
import NFA
import NFA.Thompson
import Verification.Routine
import Verification.AcceptingPath
import Data.SnocList
import Codes
import Data.Vect
import Data.List
import Data.List.Elem
import Extra
import Extra.Reflects

stepInGroupToLeftState  : {0 a : Type} -> (c: Char) -> (s : Either a AState) -> (t : a) -> (acc : a -> Bool)
                        -> (next : a -> Char -> List a) -> (prf: (Left t) `Elem` (fst (nextGroup {a} acc next s c)))
                        -> (extractBasedOnFst (fst (nextGroup acc next s c)) (snd (nextGroup acc next s c)) prf = [])

stepInGroupToLeftState c (Right ASt) t acc next prf = absurd prf
stepInGroupToLeftState c (Left x) t acc next pos with ((findR acc (next x c)).Holds)
  stepInGroupToLeftState c (Left x) t acc next pos | Nothing = (extractBasedOnFstFromRep _ _ _)
  stepInGroupToLeftState c (Left x) t acc next (There pos) | (Just _) = (extractBasedOnFstFromRep _ _ _)

stepInGroupToRightState : {0 a : Type} -> (c: Char) -> (s : Either a AState) -> (acc : a -> Bool)
                        -> (next : a -> Char -> List a) -> (prf: (Right ASt) `Elem` (fst (nextGroup {a} acc next s c)))
                        -> (extractBasedOnFst (fst (nextGroup acc next s c)) (snd (nextGroup acc next s c)) prf = [EmitString])

stepInGroupToRightState c (Right ASt) acc next prf = absurd prf
stepInGroupToRightState c (Left x) acc next pos with ((findR acc (next x c)).Holds)
  stepInGroupToRightState c (Left x) acc next pos | Nothing = absurd (rightCantBeElemOfLeft ASt (next x c) pos)
  stepInGroupToRightState c (Left x) acc next Here | (Just _) = Refl
  stepInGroupToRightState c (Left x) acc next (There pos) | (Just _) = absurd (rightCantBeElemOfLeft _ _ pos)

public export
evidenceForGroup  : (re : CoreRE) -> {s : (thompson (Group re)).nfa.State}
                  -> {mc  : Maybe Char} -> {ev  : Evidence}
                  -> (acc : AcceptingFrom (thompson (Group re)).nfa s word)
                  -> (vm  : VMState)
                  -> (vm.evidence = ev ++ (case acc of {(Accept _ _) => [< GroupMark _]; (Step _ _ _ _ _) => [<]}))
                  -> (word'': SnocList Char **
                      executeRoutineFrom (extractRoutineFrom {nfa = (thompson (Group re)).nfa, prog
                              = (thompson (Group re)).prog} acc) (mc, vm) = ev ++ [< GroupMark word''])

evidenceForGroup re (Accept s prf) vm eqPrf = ([<] ** eqPrf)

evidenceForGroup re (Step s c (Right ASt) prf1 (Accept (Right ASt) prf2)) vm eqPrf =
    let routine = stepInGroupToRightState c s (thompson re).nfa.accepting (thompson re).nfa.next prf1
        word: SnocList Char
        word = (step c vm).memory
    in rewrite routine in (word ** cong (:< GroupMark word) eqPrf)

evidenceForGroup re {mc} {ev} (Step s c (Left t) prf1 (Step (Left t) c' r prf2 acc)) vm eqPrf =
  let routine := stepInGroupToLeftState c s t (thompson re).nfa.accepting (thompson re).nfa.next prf1
      (w ** u) := evidenceForGroup re {mc, ev, s=(Left t)}
                      (Step {nfa = (thompson (Group re)).nfa} (Left t) c' r prf2 acc)
                      (step c vm) eqPrf
  in (w ** rewrite routine in u)
