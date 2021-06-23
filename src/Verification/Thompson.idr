module Verification.Thompson

import Data.SnocList
import Data.Vect
import Data.List
import Data.List.Elem
import Data.SnocList.Extra

import Codes
import Core
import NFA
import NFA.Thompson
import Evidence
import Verification.AcceptingPath
import Extra
import Extra.Reflects
import Data.Vect
import Verification.Thompson.Concat

%default total

extractBasedOnFstFromRep : (xs: List a) -> (rep : b) -> (elem: a) -> (pos: elem `Elem` xs) -> (extractBasedOnFst xs (replicate (length xs) rep) elem pos = rep)
extractBasedOnFstFromRep (_ :: xs) rep elem Here = Refl
extractBasedOnFstFromRep (y :: xs) rep elem (There x) = extractBasedOnFstFromRep xs rep elem x

---Functions for Group proof
stepInGroupToLeftState: {0 a : Type} -> (c: Char) -> (s : Either a AState) -> (t : a) -> (acc : a -> Bool) -> (next : a -> Char -> List a) -> (prf: (Left t) `Elem` (fst (nextGroup {a} acc next s c)))
    -> (extractBasedOnFst (fst (nextGroup acc next s c)) (snd (nextGroup acc next s c)) (Left t) prf = [])
stepInGroupToLeftState c (Right EndState) t acc next prf = absurd prf
stepInGroupToLeftState c (Left x) t acc next pos with ((findR acc (next x c)).Holds)
  stepInGroupToLeftState c (Left x) t acc next pos | Nothing = (extractBasedOnFstFromRep _ _ _ _)
  stepInGroupToLeftState c (Left x) t acc next (There pos) | (Just _) = (extractBasedOnFstFromRep _ _ _ _)

stepInGroupToRightState: {0 a : Type} -> (c: Char) -> (s : Either a AState) -> (acc : a -> Bool) -> (next : a -> Char -> List a) -> (prf: (Right EndState) `Elem` (fst (nextGroup {a} acc next s c)))
    -> (extractBasedOnFst (fst (nextGroup acc next s c)) (snd (nextGroup acc next s c)) (Right EndState) prf = [EmitString])
stepInGroupToRightState c (Right EndState) acc next prf = absurd prf
stepInGroupToRightState c (Left x) acc next pos with ((findR acc (next x c)).Holds)
  stepInGroupToRightState c (Left x) acc next pos | Nothing = absurd (rightCantBeElemOfLeft EndState (next x c) pos)
  stepInGroupToRightState c (Left x) acc next Here | (Just _) = Refl
  stepInGroupToRightState c (Left x) acc next (There pos) | (Just _) = absurd (rightCantBeElemOfLeft _ _ pos)

nextGroupRightIsEmpty : (fst (nextGroup acc next (Right EndState) c) = [])
nextGroupRightIsEmpty = Refl

evidenceForGroup : (re : CoreRE)
        -> (td: Thread (thompson (Group re)).nfa)
        -> (acc: AcceptingFrom (thompson (Group re)).nfa td.naState word)
        -> (td.vmState.evidence = (case acc of {(Accept _ _) => [< GroupMark _]; (Step _ _ _ _ _) => [<]}))
        -> (word'': SnocList Char ** extractEvidenceFrom {nfa = (thompson (Group re)).nfa, prog = (thompson (Group re)).prog} td acc = [< GroupMark word''])

evidenceForGroup re td (Accept td.naState _) prf = ([<] ** prf)
evidenceForGroup re td (Step td.naState c (Right EndState) prf1 (Accept (Right EndState) Refl)) prf =
  let routine = (stepInGroupToRightState c td.naState (thompson re).nfa.accepting (thompson re).nfa.next prf1)
  in rewrite prf in (rewrite routine in ((step {N = (thompson (Group re)).nfa} c td.vmState).memory ** Refl))

evidenceForGroup re td (Step td.naState c (Left s) prf1 (Step (Left s) c' t prf2 acc)) prf =
  let td' : Thread (thompson (Group re)).nfa
      td' = stepOfExtractEvidence {nfa = (thompson (Group re)).nfa, prog = (thompson (Group re)).prog} td c (Left s) prf1
      routine := stepInGroupToLeftState c td.naState s (thompson re).nfa.accepting (thompson re).nfa.next prf1
      stepMaintainsEvidence : (td'.vmState.evidence = td.vmState.evidence)
      stepMaintainsEvidence = rewrite routine in Refl
  in evidenceForGroup re td' (Step {nfa = (thompson (Group re)).nfa} (Left s) c' t prf2 acc) (trans stepMaintainsEvidence prf)

thompsonEvidencePrf : (re : CoreRE)
                              -> (acc: Accepting (thompson re).nfa word)
                              -> (extractEvidence {nfa = (thompson re).nfa, prog = (thompson re).prog} acc `Encodes` [< ShapeCode re])

thompsonEvidencePrf (Pred f) (Start s (There prf) x) = absurd prf
thompsonEvidencePrf {word = []} (Pred f) (Start StartState Here (Accept StartState prf)) = absurd prf
thompsonEvidencePrf {word = c::_} (Pred f) (Start StartState Here (Step StartState c t prf acc)) with (f c)
  thompsonEvidencePrf {word = c::_} (Pred f) (Start StartState Here (Step StartState c t prf acc)) | False = absurd prf
  thompsonEvidencePrf {word = c::_} (Pred f) (Start StartState Here (Step StartState c t (There prf) acc)) | True = absurd prf
  thompsonEvidencePrf {word = c::c'::_} (Pred f) (Start StartState Here (Step StartState c AcceptState Here (Step AcceptState c' t prf acc))) | True = absurd prf
  thompsonEvidencePrf {word = [c]} (Pred f) (Start StartState Here (Step StartState c AcceptState Here (Accept AcceptState Refl))) | True = AChar [<] c

thompsonEvidencePrf (Concat re1 re2) acc =
  let (w1 ** (acc1 ** (w2 ** (acc2 ** prf)))) = concatEvidencePrf re1 re2 acc
      ford : (extractEvidence {nfa = (thompson (Concat re1 re2)).nfa, prog = (thompson (Concat re1 re2)).prog} acc
                        = ([<] ++ (extractEvidence {nfa = (thompson re1).nfa, prog = (thompson re1).prog} acc1 ++ extractEvidence {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2)) :< PairMark)
      ford = trans prf (cong (:<PairMark) (sym appendNilLeftNeutral))
  in APair Lin (thompsonEvidencePrf re1 acc1) (thompsonEvidencePrf re2 acc2) {ford}

thompsonEvidencePrf (Group re) (Start (Right z) initprf y) = absurd (rightCantBeElemOfLeft _ _ initprf)
thompsonEvidencePrf (Group re) (Start (Left z) initprf (Accept (Left z) pos)) = absurd pos
thompsonEvidencePrf (Group re) (Start (Left z) initprf (Step (Left z) c t prf acc)) =
  let td: Thread (thompson (Group re)).nfa
      td = extractEvidenceInitialStep {nfa = (thompson (Group re)).nfa, prog = (thompson (Group re)).prog} (Left z) initprf
      q := extractBasedOnFstFromRep (thompson (Group re)).nfa.start ((the Routine) [Record]) (Left z) initprf
      (w ** ev) := evidenceForGroup re td (Step {nfa = (thompson (Group re)).nfa} td.naState c t prf acc) (rewrite q in Refl)
  in rewrite ev in AGroup [<] w
