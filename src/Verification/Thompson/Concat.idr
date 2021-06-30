module Verification.Thompson.Concat

import Data.Vect
import Data.List
import Data.List.Elem

import Core
import NFA
import NFA.Thompson
import Verification.AcceptingPath
import Extra
import Verification.Routine
import Verification.Thompson.Concat.Extra
import Verification.Thompson.Concat.EqualityPrf

%default total

injectionForCTh1 : (x : a) -> (y: a) -> (CTh1 x = CTh1 y) -> (x = y)
injectionForCTh1 x x Refl = Refl

injectionForCTh2 : (x : a) -> (y: a) -> (CTh2 x = CTh2 y) -> (x = y)
injectionForCTh2 x x Refl = Refl

rforEnd : (pos: CEnd `Elem` [CEnd]) -> (extractBasedOnFst {b = Routine} [CEnd] [[EmitPair]] CEnd pos = [EmitPair])
rforEnd Here = Refl
rforEnd (There _) impossible

ch2NotElemOFEnd : (s : a) -> (CTh2 s `Elem` [CEnd]) -> Void
ch2NotElemOFEnd s (There _) impossible

cannotStepFrom2To1 : {0 a : Type} -> (sm2 : SM) -> (s: sm2.nfa.State) -> (c : Char) -> (t: a)
                  -> ((CTh1 t) `Elem` (fst $ combineTransitions $ nextFromTwo {a} sm2 s c)) -> Void
cannotStepFrom2To1 {a} sm2 s c t pos with (fst $ combineTransitions $ nextFromTwo {a} sm2 s c)
  cannotStepFrom2To1 {a = a} sm2 s c t pos | [] impossible
  cannotStepFrom2To1 {a = a} sm2 s c t pos | (x :: xs) impossible

cTh1NotInStart2Cons : {0 a : Type} -> (sm2 : SM) -> (s : a)
                    -> ((CTh1 s) `Elem` (fst $ start2Cons sm2)) -> Void
cTh1NotInStart2Cons sm2 s pos with (sm2.prog.init)
  cTh1NotInStart2Cons sm2 s pos | init with (sm2.nfa.start)
    cTh1NotInStart2Cons sm2 s pos | [] | [] impossible
    cTh1NotInStart2Cons sm2 s pos | (x :: xs) | (y :: ys) with (sm2.nfa.accepting y)
      cTh1NotInStart2Cons sm2 s (There (There pos')) | (x :: xs) | (y :: ys) | True =
        cTh1NotInStart2Cons sm2 s pos' | xs | ys
      cTh1NotInStart2Cons sm2 s (There pos') | (x :: xs) | (y :: ys) | False =
        cTh1NotInStart2Cons sm2 s pos' | xs | ys

|||Function for a transitions from state in the second automaton
evidenceTh2 : {re1 : CoreRE} -> {re2 : CoreRE}
            -> {s : (thompson re2).nfa.State}
            -> (acc : AcceptingFrom (thompson $ Concat re1 re2).nfa (CTh2 s) word)
            -> (word': Word ** (acc2: AcceptingFrom (thompson re2).nfa s word' **
                  (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc =
                      (extractRoutineFrom {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2) ++ [Regular EmitPair]
                    )))

evidenceTh2 {re2} (Step (CTh2 s) c (CTh1 t) prf1 (Step (CTh1 t) c' r prf2 acc)) = absurd $ cannotStepFrom2To1 (thompson re2) s c t prf1
evidenceTh2 {re2} (Step (CTh2 s) c CEnd prf1 (Accept CEnd Refl)) =
  let sm2 : SM
      sm2 = (thompson re2)
      (s2 ** (prfNext2 ** (prff ** (prfAcc2, rprf2)))) := aboutCombiningTransitionsForNew (nextFromTwo sm2 s c) CEnd prf1 CTh2notEqCEnd
      word : Word
      word = [c]
      acc' : AcceptingFrom (thompson re2).nfa s word
      acc' = (Step {nfa = (thompson re2).nfa} s c s2 prfNext2 (Accept {nfa = (thompson re2).nfa} s2 prfAcc2))
  in rewrite rprf2 in (word ** acc' ** rewrite (rforEnd prff) in (eqPrf2E _))

evidenceTh2 {re2} (Step (CTh2 s) c (CTh2 t) prf1 acc) =
  let rest : (word': Word ** (acc2: AcceptingFrom (thompson re2).nfa t word' **
                (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc =
                    (extractRoutineFrom {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc2) ++ [Regular EmitPair]
                  )))
      rest = evidenceTh2 acc
      (word ** (acc2 ** eqPrf)) := rest
      (prfNext2 ** rprf) := aboutCombiningTransitionsForOld (nextFromTwo (thompson re2) s c) (CTh2 t) prf1 t injectionForCTh2 Refl (ch2NotElemOFEnd _)

  in (c::word ** (Step {nfa = (thompson re2).nfa} s c t prfNext2 acc2
                        ** rewrite rprf in (rewrite eqPrf in (cong (Observe c ::) (appendAssociative _ _ _)))))


-- |||Function for a transitions from state in the first automaton
evidenceTh1 : {re1 : CoreRE} -> {re2 : CoreRE}
            -> {s : (thompson re1).nfa.State}
            -> (acc : AcceptingFrom (thompson $ Concat re1 re2).nfa (CTh1 s) word)
            -> (word': Word ** (acc1: AcceptingFrom (thompson re1).nfa s word' ** (word'': Word ** (acc2: Accepting (thompson re2).nfa word'' **
                                      (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc =
                                        (extractRoutineFrom {nfa = (thompson re1).nfa, prog = (thompson re1).prog} acc1) ++
                                          (extractRoutine (thompson re2).nfa (thompson re2).prog acc2) ++ [Regular EmitPair]
                                        )))))

evidenceTh1 {re1, re2} (Step (CTh1 s) c (CTh1 t) prf1 acc) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2
      rest : (word': Word ** (acc1: AcceptingFrom (thompson re1).nfa t word' ** (word'': Word ** (acc2: Accepting (thompson re2).nfa word'' **
                            (extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc =
                              (extractRoutineFrom {nfa = (thompson re1).nfa, prog = (thompson re1).prog} acc1) ++
                                (extractRoutine (thompson re2).nfa (thompson re2).prog acc2) ++ [Regular EmitPair]
                              )))))
      rest = evidenceTh1 acc
      (word1 ** (acc1 ** (word2 ** (acc2 ** eqPrf)))) := rest
      aos : (aboutCombiningTransitionsForOldType (nextFromOne sm1 sm2  s c) (CTh1 t) prf1 t)
      aos = aboutCombiningTransitionsForOld (nextFromOne sm1 sm2  s c) (CTh1 t) prf1 t injectionForCTh1 Refl (cTh1NotInStart2Cons (thompson re2) t)
  in (c::word1 ** (Step {nfa = (thompson re1).nfa} s c t (fst aos) acc1 ** (word2 ** (acc2
                          ** rewrite (snd aos) in (rewrite eqPrf in (cong (Observe c ::) (appendAssociative _ _ _)))))))

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

      ans : aboutCombiningTransitionsForNewType (nextFromOne sm1 sm2 s c) (CTh2 t) prf1
      ans = aboutCombiningTransitionsForNew (nextFromOne sm1 sm2 s c) (CTh2 t) prf1 CTh2notEqCTh1
      (s1 ** (prfNext1 ** (prf2 ** (prfAcc1, rprf)))) := ans

      (prfInit2 ** rprf2) := aboutCombiningTransitionsForOld (initTwo sm2) (CTh2 t) prf2 t injectionForCTh2 Refl (ch2NotElemOFEnd _)

  in ([c] ** (Step {nfa = sm1.nfa} s c s1 prfNext1 (Accept {nfa = sm1.nfa} s1 prfAcc1)
            ** (word2 ** (Start {nfa = sm2.nfa} t prfInit2 acc2
              ** rewrite rprf in rewrite rprf2 in rewrite eqPrf in (cong (Observe c ::) (eqPrfS2 _ _ _))))))


evidenceTh1 (Step (CTh1 s) c CEnd prf1 (Accept CEnd Refl)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      ans : aboutCombiningTransitionsForNewType (nextFromOne sm1 sm2 s c) CEnd prf1
      ans = aboutCombiningTransitionsForNew (nextFromOne sm1 sm2 s c) CEnd prf1 CTh1notEqCEnd
      (s1 ** (prfNext1 ** (prf2 ** (prfAcc1, rprf)))) := ans

      (s2 ** (prfInit2 ** (prff ** (prfAcc2, rprf2)))) := aboutCombiningTransitionsForNew (initTwo sm2) CEnd prf2 CTh2notEqCEnd

  in ([c] ** (Step {nfa = sm1.nfa} s c s1 prfNext1 (Accept {nfa = sm1.nfa} s1 prfAcc1)
        ** ([] ** (Start {nfa = sm2.nfa} s2 prfInit2 (Accept {nfa = sm2.nfa} s2 prfAcc2)
          ** rewrite rprf in (rewrite rprf2 in (rewrite (rforEnd prff) in (cong (Observe c ::) (threePartEq _ _))))))))

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

      (s1 ** (prfInit1 ** (prf2 ** (prfAcc1, rprf)))) := aboutCombiningTransitionsForNew (initOne sm1 sm2) CEnd prf CTh1notEqCEnd
      (s2 ** (prfInit2 ** (prff ** (prfAcc2, rprf2)))) := aboutCombiningTransitionsForNew (initTwo sm2) CEnd prf2 CTh2notEqCEnd

  in ([] ** (Start {nfa = (thompson re1).nfa} s1 prfInit1 (Accept {nfa = (thompson re1).nfa}  s1 prfAcc1)
        ** ([] ** (Start {nfa = (thompson re2).nfa} s2 prfInit2 (Accept {nfa = (thompson re2).nfa} s2 prfAcc2)
          ** rewrite rprf in (rewrite rprf2 in (rewrite (rforEnd prff) in (threePartEq _ _)))))))

concatEvidencePrf {word=(c::w)} re1 re2 (Start (CTh2 s) prf (Step (CTh2 s) c t prf1 acc)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      (s1 ** (prfInit1 ** (prf2 ** (prfAcc1, rprf)))) := aboutCombiningTransitionsForNew (initOne sm1 sm2) (CTh2 s) prf CTh2notEqCTh1
      (prfInit2 ** rprf') := aboutCombiningTransitionsForOld (initTwo sm2) (CTh2 s) prf2 s injectionForCTh2 Refl (ch2NotElemOFEnd _)
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
      (prfInit1 ** rprf) :=
        aboutCombiningTransitionsForOld (initOne sm1 sm2) (CTh1 s) prfInit s injectionForCTh1 Refl (cTh1NotInStart2Cons sm2 s)

  in ((fst (allNext)) ** ((Start {nfa = (thompson re1).nfa} s prfInit1 (fst $ snd allNext))
          ** ((fst $ snd $ snd allNext) ** ((fst $ snd $ snd $ snd allNext)
              ** rewrite rprf in rewrite (snd $ snd $ snd $ snd allNext) in (appendAssociative _ _ _)))))
