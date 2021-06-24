module Verification.Routine.Thompson.Concat

import Data.Vect
import Data.List
import Data.List.Elem

import Core
import NFA
import NFA.Thompson
import Verification.AcceptingPath
import Extra
import Verification.Routine
import Verification.Routine.Thompson.Concat.Extra
import Verification.Routine.Thompson.Concat.EqualityPrf

%default total

start2Cons : (sm2 : SM) -> (xs: List $ CState sm1State sm2.nfa.State ** Vect (length xs) Routine)
start2Cons sm2 = forAcceptingAddNewStart sm2.nfa.start sm2.prog.init sm2.nfa.accepting CTh2 [CEnd] [[EmitPair]]

initOne : (sm1: SM) -> (sm2 : SM) -> (AboutAddingData sm1.nfa.State sm2.nfa.State sm1.nfa.State)
initOne sm1 sm2 = MkAboutAddingData sm1.nfa.start sm1.prog.init sm1.nfa.accepting CTh1 (fst (start2Cons sm2)) (snd (start2Cons sm2))

initTwo : (sm1: SM) -> (sm2 : SM) -> (AboutAddingData sm1.nfa.State sm2.nfa.State sm2.nfa.State)
initTwo sm1 sm2 = MkAboutAddingData sm2.nfa.start sm2.prog.init sm2.nfa.accepting CTh2 [CEnd] [[EmitPair]]

nextFromOne : (sm1: SM) -> (sm2 : SM) -> Char -> sm1.nfa.State -> (AboutAddingData sm1.nfa.State sm2.nfa.State sm1.nfa.State)
nextFromOne sm1 sm2 c st = MkAboutAddingData (sm1.nfa.next st c) (sm1.prog.next st c) sm1.nfa.accepting CTh1 (fst (start2Cons sm2)) (snd (start2Cons sm2))

nextFromTwo : (sm2: SM) -> Char -> sm2.nfa.State -> (AboutAddingData a sm2.nfa.State sm2.nfa.State)
nextFromTwo sm2 c st = MkAboutAddingData (sm2.nfa.next st c) (sm2.prog.next st c) sm2.nfa.accepting CTh2 [CEnd] [[EmitPair]]

injectionForCTh1 : (x : a) -> (y: a) -> (CTh1 x = CTh1 y) -> (x = y)
injectionForCTh1 x x Refl = Refl

injectionForCTh2 : (x : a) -> (y: a) -> (CTh2 x = CTh2 y) -> (x = y)
injectionForCTh2 x x Refl = Refl

rforEnd : (pos: CEnd `Elem` [CEnd]) -> (extractBasedOnFst {b = Routine} [CEnd] [[EmitPair]] CEnd pos = [EmitPair])
rforEnd Here = Refl
rforEnd (There _) impossible

ch2NotElemOFEnd : (s : a) -> (CTh2 s `Elem` [CEnd]) -> Void
ch2NotElemOFEnd s (There _) impossible

cannotStepFrom2To1: {0 a : Type} -> (sm2 : SM) -> (s: sm2.nfa.State) -> (c : Char) -> (t: a)
                  -> ((CTh1 t) `Elem` (fst $ forAcceptingAddNewStart' $ nextFromTwo sm2 c s)) -> Void
cannotStepFrom2To1 {a} sm2 s c t pos with (fst $ forAcceptingAddNewStart' $ nextFromTwo {a} sm2 c s)
  cannotStepFrom2To1 {a} sm2 s c t pos | [] impossible
  cannotStepFrom2To1 {a} sm2 s c t pos | (y :: xs) impossible

cTh1NotInStart2Cons : {0 a : Type} -> (sm2 : SM) -> (s : a) -> ((CTh1 s) `Elem` (fst $ start2Cons {sm1State = a} sm2)) -> Void
cTh1NotInStart2Cons sm2 s pos with (sm2.prog.init)
  cTh1NotInStart2Cons sm2 s pos | init with (sm2.nfa.start)
    cTh1NotInStart2Cons sm2 s pos | [] | [] impossible
    cTh1NotInStart2Cons sm2 s pos | (x :: xs) | (y :: ys) with (sm2.nfa.accepting y)
      cTh1NotInStart2Cons sm2 s (There (There pos')) | (x :: xs) | (y :: ys) | True = cTh1NotInStart2Cons sm2 s pos' | xs | ys
      cTh1NotInStart2Cons sm2 s (There pos') | (x :: xs) | (y :: ys) | False = cTh1NotInStart2Cons sm2 s pos' | xs | ys

evidenceTh2 : {re1 : CoreRE} -> {re2 : CoreRE}
            -> {s : (thompson re2).nfa.State}
            -> (acc : AcceptingFrom (thompson $ Concat re1 re2).nfa (CTh2 s) word)
            -> (word': Word ** (acc2: AcceptingFrom (thompson re2).nfa s word' **
                                                        (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc =
                                                            (extractRoutineFrom {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2) ++ [Regular EmitPair]
                                                          )))

evidenceTh2 (Step (CTh2 s) c (CTh1 t) prf1 (Step (CTh1 t) c' r prf2 acc)) = absurd $ cannotStepFrom2To1 (thompson re2) s c t prf1
evidenceTh2 (Step (CTh2 s) c CEnd prf1 (Accept CEnd Refl)) =
  let (s2 ** (prfNext2 ** (prff ** (prfAcc2, rprf2)))) := aboutAddingStatesOld (nextFromTwo (thompson re2) c s) CEnd prf1 notPrf2
      word : Word
      word = [c]
      acc' : AcceptingFrom (thompson re2).nfa s word
      acc' = (Step {nfa = (thompson re2).nfa} s c s2 prfNext2 (Accept {nfa = (thompson re2).nfa} s2 prfAcc2))
  in rewrite rprf2 in (word ** acc' ** rewrite (rforEnd prff) in (eqPrf2E _))

evidenceTh2 (Step (CTh2 s) c (CTh2 t) prf1 acc) =
  let rest : (word': Word ** (acc2: AcceptingFrom (thompson re2).nfa t word' **
                                              (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc =
                                                  (extractRoutineFrom {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2) ++ [Regular EmitPair]
                                                )))
      rest = evidenceTh2 acc
      (word ** (acc2 ** eqPrf)) := rest
      (prfNext2 ** rprf) := aboutAddingStatesNew (nextFromTwo (thompson re2) c s) (CTh2 t) prf1 t injectionForCTh2 Refl (ch2NotElemOFEnd _)

  in (c::word ** (Step {nfa = (thompson re2).nfa} s c t prfNext2 acc2
                          ** rewrite rprf in (rewrite eqPrf in (cong (Observe c ::) (appendAssociative _ _ _)))))



evidenceTh1 : {re1 : CoreRE} -> {re2 : CoreRE}
            -> {s : (thompson re1).nfa.State}
            -> (acc : AcceptingFrom (thompson $ Concat re1 re2).nfa (CTh1 s) word)
            -> (word': Word ** (acc1: AcceptingFrom (thompson re1).nfa s word' ** (word'': Word ** (acc2: Accepting (thompson re2).nfa word'' **
                                      (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc =
                                        (extractRoutineFrom {nfa = (thompson re1).nfa, prog = (thompson re1).prog} acc1) ++
                                          (extractRoutine (thompson re2).nfa (thompson re2).prog acc2) ++ [Regular EmitPair]
                                        )))))

evidenceTh1 (Step (CTh1 s) c (CTh1 t) prf1 acc) =
  let rest : (word': Word ** (acc1: AcceptingFrom (thompson re1).nfa t word' ** (word'': Word ** (acc2: Accepting (thompson re2).nfa word'' **
                            (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc =
                              (extractRoutineFrom {nfa = (thompson re1).nfa, prog = (thompson re1).prog} acc1) ++
                                (extractRoutine (thompson re2).nfa (thompson re2).prog acc2) ++ [Regular EmitPair]
                              )))))
      rest = evidenceTh1 acc
      (word1 ** (acc1 ** (word2 ** (acc2 ** eqPrf)))) := rest
      (prfNext1 ** rprf) := aboutAddingStatesNew (nextFromOne (thompson re1) (thompson re2) c s) (CTh1 t) prf1 t injectionForCTh1 Refl (cTh1NotInStart2Cons (thompson re2) t)
  in (c::word1 ** (Step {nfa = (thompson re1).nfa} s c t prfNext1 acc1 ** (word2 ** (acc2
                          ** rewrite rprf in (rewrite eqPrf in (cong (Observe c ::) (appendAssociative _ _ _)))))))

evidenceTh1 (Step (CTh1 s) c (CTh2 t) prf1 acc) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      rest : (word': Word ** (acc2: AcceptingFrom (thompson re2).nfa t word' **
                                              (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc =
                                                  (extractRoutineFrom {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2) ++ [Regular EmitPair]
                                                )))
      rest = evidenceTh2 acc
      (word2 ** (acc2 ** eqPrf)) := rest

      (s1 ** (prfNext1 ** (prf2 ** (prfAcc1, rprf)))) := aboutAddingStatesOld (nextFromOne sm1 sm2 c s) (CTh2 t) prf1 notPrf3
      (prfInit2 ** rprf2) := aboutAddingStatesNew (initTwo sm1 sm2) (CTh2 t) prf2 t injectionForCTh2 Refl (ch2NotElemOFEnd _)

  in ([c] ** (Step {nfa = sm1.nfa} s c s1 prfNext1 (Accept {nfa = sm1.nfa} s1 prfAcc1)
           ** (word2 ** (Start {nfa = sm2.nfa} t prfInit2 acc2 ** rewrite rprf in rewrite rprf2 in rewrite eqPrf in (cong (Observe c ::) (eqPrfS2 _ _ _))))))


evidenceTh1 (Step (CTh1 s) c CEnd prf1 (Accept CEnd Refl)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      (s1 ** (prfNext1 ** (prf2 ** (prfAcc1, rprf)))) := aboutAddingStatesOld (nextFromOne sm1 sm2 c s) CEnd prf1 notPrf1
      (s2 ** (prfInit2 ** (prff ** (prfAcc2, rprf2)))) := aboutAddingStatesOld (initTwo sm1 sm2) CEnd prf2 notPrf2
  in ([c] ** (Step {nfa = sm1.nfa} s c s1 prfNext1 (Accept {nfa = sm1.nfa} s1 prfAcc1)
        ** ([] ** (Start {nfa = sm2.nfa} s2 prfInit2 (Accept {nfa = sm2.nfa} s2 prfAcc2) ** rewrite rprf in (rewrite rprf2 in (rewrite (rforEnd prff) in (cong (Observe c ::) (threePartEq _ _))))))))

public export
concatEvidencePrf : (re1 : CoreRE) -> (re2: CoreRE)
                              -> (acc: Accepting (thompson $ Concat re1 re2).nfa word)
                              -> (word' : Word ** (acc1: Accepting (thompson re1).nfa word' ** (word'' : Word ** (acc2: Accepting (thompson re2).nfa word'' **
                                                            extractRoutine (thompson $ Concat re1 re2).nfa (thompson $ Concat re1 re2).prog acc =
                                                              extractRoutine (thompson re1).nfa (thompson re1).prog acc1 ++
                                                              extractRoutine (thompson re2).nfa (thompson re2).prog acc2 ++ [Regular EmitPair]
                                                          ))))

concatEvidencePrf re1 re2 (Start CEnd prf (Accept CEnd Refl)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      (s1 ** (prfInit1 ** (prf2 ** (prfAcc1, rprf)))) := aboutAddingStatesOld (initOne sm1 sm2) CEnd prf notPrf1

      (s2 ** (prfInit2 ** (prff ** (prfAcc2, rprf2)))) := aboutAddingStatesOld (initTwo sm1 sm2) CEnd prf2 notPrf2

  in ([] ** (Start {nfa = (thompson re1).nfa} s1 prfInit1 (Accept {nfa = (thompson re1).nfa}  s1 prfAcc1)
        ** ([] ** (Start {nfa = (thompson re2).nfa} s2 prfInit2 (Accept {nfa = (thompson re2).nfa} s2 prfAcc2)
          ** rewrite rprf in (rewrite rprf2 in (rewrite (rforEnd prff) in (threePartEq _ _)))))))

concatEvidencePrf {word=(c::w)} re1 re2 (Start (CTh2 s) prf (Step (CTh2 s) c t prf1 acc)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      (s1 ** (prfInit1 ** (prf2 ** (prfAcc1, rprf)))) := aboutAddingStatesOld (initOne sm1 sm2) (CTh2 s) prf notPrf3
      (prfInit2 ** rprf') := aboutAddingStatesNew (initTwo sm1 sm2) (CTh2 s) prf2 s injectionForCTh2 Refl (ch2NotElemOFEnd _)
      (word' ** (accept2 ** eqPrf)) := evidenceTh2 {re1, re2} (Step {nfa = (thompson $ Concat re1 re2).nfa} (CTh2 s) c t prf1 acc)

  in ([] ** (Start {nfa = (thompson re1).nfa} s1 prfInit1 (Accept {nfa = (thompson re1).nfa} s1 prfAcc1)
          ** (word' ** (Start {nfa = sm2.nfa} s prfInit2 accept2
            ** (rewrite rprf in (rewrite rprf' in rewrite eqPrf in (eqPrfS2 _ _ _)))))))

concatEvidencePrf re1 re2 (Start (CTh1 s) prfInit (Step (CTh1 s) c t prf1 acc)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      allNext : (word': Word ** (acc1: AcceptingFrom (thompson re1).nfa s word' ** (word'': Word ** (acc2: Accepting (thompson re2).nfa word'' **
                                (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} (Step {nfa = (thompson $ Concat re1 re2).nfa} (CTh1 s) c t prf1 acc) =
                                  (extractRoutineFrom {nfa = (thompson re1).nfa, prog = (thompson re1).prog} acc1) ++
                                    (extractRoutine (thompson re2).nfa (thompson re2).prog acc2) ++ [Regular EmitPair]
                                  )))))

      allNext = evidenceTh1 (Step {nfa = (thompson $ Concat re1 re2).nfa} (CTh1 s) c t prf1 acc)
      (prfInit1 ** rprf) := aboutAddingStatesNew (initOne sm1 sm2) (CTh1 s) prfInit s injectionForCTh1 Refl (cTh1NotInStart2Cons sm2 s)

  in ((fst (allNext)) ** ((Start {nfa = (thompson re1).nfa} s prfInit1 (fst $ snd allNext)) ** ((fst $ snd $ snd allNext) ** ((fst $ snd $ snd $ snd allNext)
              ** rewrite rprf in rewrite (snd $ snd $ snd $ snd allNext) in (appendAssociative _ _ _)))))
