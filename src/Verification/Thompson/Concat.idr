module Verification.Thompson.Concat

import Data.SnocList
import Data.Vect
import Data.List
import Data.List.Elem

import Codes
import Core
import NFA
import NFA.Thompson
import Evidence
import Verification.AcceptingPath
import Extra
import Extra.Reflects
import Data.Vect

%default total

data ConcatPhase = Th1P | Th2P

notPrf1 : (s : sm1.nfa.State) -> Not (CTh1 s = CEnd)
notPrf1 s prf = absurd prf

notPrf2 : (s : sm2.nfa.State) -> Not (CTh2 s = CEnd)
notPrf2 s prf = absurd prf

notPrf3 : (s : sm1.nfa.State) -> Not (CTh1 s = CTh2 s')
notPrf3 s prf = absurd prf

-- execConcatPrf : {nfa : NA} -> {nfa1 : NA} -> {nfa2 : NA}
--               -> (r1 : Routine) -> (r2 : Routine) -> (mc : Maybe Char)
--               -> (s: nfa.State) -> (s1 : nfa1.State) -> (s2 : nfa2.State)
--               -> (ev : Evidence)
--               -> ((execute {N = nfa} mc (r1 ++ r2) (MkThread s (MkVMState b0 w0 ev))).vmState.evidence
--                         = (execute {N = nfa1} mc r1 (MkThread s1 (MkVMState b1 w2 ev))).vmState.evidence ++ (execute {N = nfa2} Nothing r2 (MkThread s2 (MkVMState False [<] [<]))).vmState.evidence)
-- execConcatPrf r1 [] mc s s1 s2 ev = ?execConcatPrf_rhs_1
-- execConcatPrf r1 (x :: xs) mc s s1 s2 ev = ?execConcatPrf_rhs_2


aboutAddingStatesNew : (oldStates: List c) -> (rout1: Vect (length oldStates) Routine) -> (accept: c -> Bool) -> (conv: c -> (CState a b))
                        -> (newStart: List (CState a b)) -> (rout2: Vect (length newStart) Routine)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (forAcceptingAddNewStart oldStates rout1 accept conv newStart rout2))
                        -> (oldState : c)
                        -> (conv oldState = state)
                        -> (Not (state `Elem` newStart))
                        -> (prf: oldState `Elem` oldStates ** extractBasedOnFst (fst $ forAcceptingAddNewStart oldStates rout1 accept conv newStart rout2) (snd $ forAcceptingAddNewStart oldStates rout1 accept conv newStart rout2) state prf1 = extractBasedOnFst oldStates rout1 oldState prf)

aboutAddingStatesNew [] [] accept conv newStart rout2 state prf1 oldState prf f = absurd prf1
aboutAddingStatesNew (x :: xs) (y :: ys) accept conv newStart rout2 state prf1 oldState prf f = ?aboutAddingStatesNew_rhs_4

aboutAddingStatesOld : (oldStates: List c) -> (rout1: Vect (length oldStates) Routine) -> (accept: c -> Bool) -> (conv: c -> (CState a b))
                        -> (newStart: List (CState a b)) -> (rout2: Vect (length newStart) Routine)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (forAcceptingAddNewStart oldStates rout1 accept conv newStart rout2))
                        -> ((oldState: c) -> Not (conv oldState = state))
                        -> (oldState : c ** (prf: oldState `Elem` oldStates ** (prf2: state `Elem` newStart ** (accept oldState = True, extractBasedOnFst (fst $ forAcceptingAddNewStart oldStates rout1 accept conv newStart rout2) (snd $ forAcceptingAddNewStart oldStates rout1 accept conv newStart rout2) state prf1 = extractBasedOnFst oldStates rout1 oldState prf ++ extractBasedOnFst newStart rout2 state prf2))))

aboutAddingStatesOld [] [] accept conv newStart rout2 state prf1 f = absurd prf1
aboutAddingStatesOld (x :: xs) (y :: ys) accept conv newStart rout2 state prf1 f with (accept x) proof p
  aboutAddingStatesOld (x :: xs) (y :: ys) accept conv newStart rout2 state prf1 notPrf | True =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let hOrT = hereOrThereExtractBasedOnFst newStart (fst $ forAcceptingAddNewStart xs ys accept conv newStart rout2) (map (y++) rout2) (snd $ forAcceptingAddNewStart xs ys accept conv newStart rout2) state pos
        in case hOrT of
          (Left (pos' ** prf)) => (x ** (Here ** (pos' ** (p, trans prf (mapExtractBasedOnFst _ _ _ _ _)))))
          (Right (pos'** prf)) =>
              let (os ** (opos ** (npos ** (acc, eQ)))) = aboutAddingStatesOld xs ys accept conv newStart rout2 state pos' notPrf
              in (os ** (There opos ** (npos ** (acc, trans prf eQ))))

  aboutAddingStatesOld (x :: xs) (y :: ys) accept conv newStart rout2 state prf1 notPrf | False =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let (os ** (opos ** (npos ** (acc, eQ)))) = aboutAddingStatesOld xs ys accept conv newStart rout2 state pos notPrf
        in (os ** (There opos ** (npos ** (acc, eQ))))

evidenceTh1 : {re1 : CoreRE} -> {re2 : CoreRE} -> (td : Thread (thompson $ Concat re1 re2).nfa)
            -> (acc: AcceptingFrom (thompson $ Concat re1 re2).nfa td.naState word)
            -> (td1 : Thread (thompson re1).nfa)
            -> (td.naState = CTh1 td1.naState)
            -> (td.vmState.evidence = td1.vmState.evidence)
            -> (word': Word ** (acc2: Accepting (thompson re2).nfa word' ** (word'': Word ** (acc1: AcceptingFrom (thompson re1).nfa td1.naState word'' **
                                                                (extractEvidenceFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} td acc =
                                                                    extractEvidenceFrom {nfa = (thompson re1).nfa, prog = (thompson re1).prog} td1 acc1 ++
                                                                    extractEvidence {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2 ++
                                                                    [< PairMark]
                                                                  )
                                                                ))))
evidenceTh1 td acc td1 prf prf1 with (thompson $ Concat re1 re2)
  evidenceTh1 (MkThread naState vmState) acc td1 prf prf1 | sm = ?evidenceTh1_rhs_1

evidenceTh2 : {re1 : CoreRE} -> {re2 : CoreRE} -> (td : Thread (thompson $ Concat re1 re2).nfa)
            -> (acc : AcceptingFrom (thompson $ Concat re1 re2).nfa td.naState word)
            -> (td2 : Thread (thompson re2).nfa)
            -> (ev  : Evidence)
            -> (td.naState = CTh2 td2.naState)
            -> (td.vmState.evidence = ev ++ td2.vmState.evidence)
            -> (word': Word ** (acc2: AcceptingFrom (thompson re2).nfa td2.naState word' **
                                                                (extractEvidenceFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} td acc =
                                                                    ev ++
                                                                    extractEvidenceFrom {nfa = (thompson re2).nfa, prog = (thompson re2).prog} td2 acc2 ++
                                                                    [< PairMark]
                                                                  )))
evidenceTh2 {word} td acc td2 ev prf prf1 with (thompson $ Concat re1 re2)
  evidenceTh2 {word} td acc td2 ev prf prf1 | sm with (thompson re2)
    evidenceTh2 {word=(c::_)} (MkThread (CTh2 s) vmState) (Step (CTh2 s) c t prf1 acc) (MkThread s vmState') ev Refl evEq | sm | sm2 = ?evidenceTh2_rhs_1





public export
concatEvidencePrf : (re1 : CoreRE) -> (re2: CoreRE)
                              -> (acc: Accepting (thompson $ Concat re1 re2).nfa word)
                              -> (word' : Word ** (acc1: Accepting (thompson re1).nfa word' ** (word'' : Word ** (acc2: Accepting (thompson re2).nfa word'' **
                                                        (extractEvidence {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc) =
                                                            extractEvidence {nfa = (thompson re1).nfa, prog = (thompson re1).prog} acc1 ++
                                                            extractEvidence {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2 ++ [< PairMark]
                                                          ))))


concatEvidencePrf re1 re2 (Start CEnd prf (Accept CEnd Refl)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      _ := sm1.nfa.isEq
      _ := sm2.nfa.isEq

      start2 : (xs: List $ CState sm1.nfa.State sm2.nfa.State ** Vect (length xs) Routine)
      start2 = forAcceptingAddNewStart sm2.nfa.start sm2.prog.init sm2.nfa.accepting CTh2 [CEnd] [[EmitPair]]

      (s1 ** (prfInit1 ** (prf2 ** (prfAcc1, rprf)))) := aboutAddingStatesOld sm1.nfa.start sm1.prog.init sm1.nfa.accepting CTh1 (fst start2) (snd start2) CEnd prf notPrf1

      (s2 ** (prfInit2 ** (prff ** (prfAcc2, rprf2)))) := aboutAddingStatesOld sm2.nfa.start sm2.prog.init sm2.nfa.accepting CTh2 [CEnd] [[EmitPair]] CEnd prf2 notPrf2

      rforEnd : (extractBasedOnFst {b = Routine} [CEnd] [[EmitPair]] CEnd prff = [EmitPair])
      rforEnd = case prff of
                  Here => Refl
                  (There pos) => absurd pos

      --TODO proof that execute on (routine1 +++ routine2) = (execute routine1) ++ (execute routine2)
  in ([] ** (Start {nfa = (thompson re1).nfa} s1 prfInit1 (Accept {nfa = (thompson re1).nfa}  s1 prfAcc1)
        ** ([] ** (Start {nfa = (thompson re2).nfa} s2 prfInit2 (Accept {nfa = (thompson re2).nfa} s2 prfAcc2)
            ** rewrite rprf in (rewrite rprf2 in (rewrite rforEnd in ?eqPrf))))))

concatEvidencePrf {word=(c::w)} re1 re2 (Start (CTh2 s) prf (Step (CTh2 s) c t prf1 acc)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2
      sm : SM
      sm = thompson $ Concat re1 re2

      start2 : (xs: List $ CState sm1.nfa.State sm2.nfa.State ** Vect (length xs) Routine)
      start2 = forAcceptingAddNewStart sm2.nfa.start sm2.prog.init sm2.nfa.accepting CTh2 [CEnd] [[EmitPair]]

      (s1 ** (prfInit1 ** (prf2 ** (prfAcc1, rprf)))) := aboutAddingStatesOld sm1.nfa.start sm1.prog.init sm1.nfa.accepting CTh1 (fst start2) (snd start2) (CTh2 s) prf notPrf3

      td : Thread sm.nfa
      td = extractEvidenceInitialStep {nfa = sm.nfa} {prog = sm.prog} (CTh2 s) prf

      td1 : Thread sm1.nfa
      td1 = extractEvidenceInitialStep {nfa = sm1.nfa} {prog = sm1.prog} s1 prfInit1

      (prfInit2 ** rprf') := aboutAddingStatesNew sm2.nfa.start sm2.prog.init sm2.nfa.accepting CTh2 [CEnd] [[EmitPair]] (CTh2 s) prf2 s Refl (\e => case e of {Here impossible ; There pos impossible})

      td2 : Thread sm2.nfa
      td2 = extractEvidenceInitialStep {nfa = sm2.nfa} {prog = sm2.prog} s prfInit2

      acceptingFrom : AcceptingFrom sm.nfa td.naState (c::w)
      acceptingFrom = Step {nfa = sm.nfa} (CTh2 s) c t prf1 acc

      --TODO proof that execute on (routine1 +++ routine2) = (execute routine1) ++ (execute routine2)
      (word' ** (accept2 ** eqPrf)) := evidenceTh2 {re1, re2} td
                                      acceptingFrom
                                      td2 td1.vmState.evidence
                                      Refl
                                      (rewrite rprf in (rewrite rprf' in ?p))

  in ([] ** (Start {nfa = (thompson re1).nfa} s1 prfInit1 (Accept {nfa = (thompson re1).nfa} s1 prfAcc1)
        ** (word' ** (Start {nfa = sm2.nfa} s prfInit2 accept2
            ** eqPrf))))

concatEvidencePrf re1 re2 (Start (CTh1 s) prf (Step (CTh1 s) c t prf1 acc)) = ?concatEvidencePrf_rhs_3
