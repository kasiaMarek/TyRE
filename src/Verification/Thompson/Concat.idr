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
import Verification.Thompson.Extra
import Verification.Thompson.Concat.Extra
import Verification.Thompson.Concat.EqualityPrf

%default total

record EvidenceTh2Data  {word' : Word} {re1 : CoreRE} {re2 : CoreRE} {s : (thompson re2).nfa.State}
                        (acc' : AcceptingFrom (thompson $ Concat re1 re2).nfa (CTh2 s) word') where
  constructor MkEvidenceTh2Data
  word: Word
  acc: AcceptingFrom (thompson re2).nfa s word
  routineEq : extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc' =
      (extractRoutineFrom {nfa = (thompson re2).nfa, prog = (thompson re2).prog} acc) ++ [Regular EmitPair]

record EvidenceTh1Data  {word' : Word} {re1 : CoreRE} {re2 : CoreRE} {s : (thompson re1).nfa.State}
                        (acc' : AcceptingFrom (thompson $ Concat re1 re2).nfa (CTh1 s) word') where
  constructor MkEvidenceTh1Data
  word1: Word
  acc1: AcceptingFrom (thompson re1).nfa s word1
  word2: Word
  acc2: Accepting (thompson re2).nfa word2
  routineEq : extractRoutineFrom {nfa = (thompson $ Concat re1 re2).nfa, prog = (thompson $ Concat re1 re2).prog} acc'
                = (extractRoutineFrom {nfa = (thompson re1).nfa, prog = (thompson re1).prog} acc1)
                  ++  (extractRoutine (thompson re2).nfa (thompson re2).prog acc2) ++ [Regular EmitPair]


|||Function for a transitions from state in the second automaton
evidenceTh2 : {re1 : CoreRE} -> {re2 : CoreRE}
            -> {0 word : Word}
            -> {s : (thompson re2).nfa.State}
            -> (acc : AcceptingFrom (thompson $ Concat re1 re2).nfa (CTh2 s) word)
            -> EvidenceTh2Data {re1,re2} acc

evidenceTh2 {re2} (Step (CTh2 s) c (CTh1 t) prf1 (Step (CTh1 t) c' r prf2 acc)) =
  absurd $ cannotStepFrom2To1 (thompson re2) s c t prf1

evidenceTh2 {re2} (Step (CTh2 s) c CEnd prf1 (Accept CEnd Refl)) =
  let sm2 : SM
      sm2 = (thompson re2)
      ans : CombiningTransitionsForNewData (twoToEndConcat sm2 s c) CEnd prf1
      ans = aboutCombiningTransitionsForNew (twoToEndConcat sm2 s c) CEnd prf1 CTh2notEqCEnd
      word : Word
      word = [c]
      acc' : AcceptingFrom (thompson re2).nfa s word
      acc' = (Step {nfa = (thompson re2).nfa} s c ans.oldState ans.oldIsElemOfOld
                  (Accept {nfa = (thompson re2).nfa} ans.oldState ans.oldAccepts))
  in MkEvidenceTh2Data
          word acc'
          rewrite ans.routineEqualityPrf in
            rewrite (rforEndConcat ans.stateIsElemOfNew) in (eqPrf2ToEnd _)

evidenceTh2 {re1, re2} (Step (CTh2 s) c (CTh2 t) prf1 acc) =
  let rest : EvidenceTh2Data {re1,re2} acc
      rest = evidenceTh2 acc
      aos : CombiningTransitionsForOldData (twoToEndConcat (thompson re2) s c) (CTh2 t) prf1 t
      aos = aboutCombiningTransitionsForOld (twoToEndConcat (thompson re2) s c)
                                            (CTh2 t) prf1 t injectionForCTh2
                                            Refl (ch2NotElemOFEnd _)
  in MkEvidenceTh2Data
          (c::rest.word) (Step {nfa = (thompson re2).nfa} s c t aos.oldIsElemOfOld rest.acc)
          rewrite aos.routineEqualityPrf in (rewrite rest.routineEq in
                      (cong (Observe c ::) (appendAssociative _ _ _)))


-- |||Function for a transitions from state in the first automaton
evidenceTh1 : {re1 : CoreRE} -> {re2 : CoreRE}
            -> {0 word : Word}
            -> {s : (thompson re1).nfa.State}
            -> (acc : AcceptingFrom (thompson $ Concat re1 re2).nfa (CTh1 s) word)
            -> EvidenceTh1Data {re1, re2} acc

evidenceTh1 {re1, re2} (Step (CTh1 s) c (CTh1 t) prf1 acc) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2
      rest : EvidenceTh1Data {re1, re2} acc
      rest = evidenceTh1 acc
      aos : CombiningTransitionsForOldData (oneToTwo sm1 sm2  s c) (CTh1 t) prf1 t
      aos = aboutCombiningTransitionsForOld (oneToTwo sm1 sm2  s c) (CTh1 t) prf1
                                            t injectionForCTh1 Refl
                                            (cTh1NotInStart2Cons (thompson re2) t)
  in MkEvidenceTh1Data
          (c::(rest.word1)) (Step {nfa = (thompson re1).nfa} s c t aos.oldIsElemOfOld rest.acc1)
          rest.word2        rest.acc2
          rewrite aos.routineEqualityPrf in (rewrite (rest.routineEq) in
            (cong (Observe c ::) (appendAssociative _ _ _)))

evidenceTh1 (Step (CTh1 s) c (CTh2 t) prf1 acc) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2
      rest : EvidenceTh2Data {re1,re2} acc
      rest = evidenceTh2 acc
      ans : CombiningTransitionsForNewData (oneToTwo sm1 sm2 s c) (CTh2 t) prf1
      ans = aboutCombiningTransitionsForNew (oneToTwo sm1 sm2 s c) (CTh2 t) prf1 CTh2notEqCTh1
      aos : CombiningTransitionsForOldData (initTwoConcat sm2) (CTh2 t) ans.stateIsElemOfNew t
      aos = aboutCombiningTransitionsForOld (initTwoConcat sm2) (CTh2 t)
                                            ans.stateIsElemOfNew t
                                            injectionForCTh2 Refl
                                            (ch2NotElemOFEnd _)
  in MkEvidenceTh1Data
        [c]         (Step {nfa = sm1.nfa} s c ans.oldState ans.oldIsElemOfOld
                        (Accept {nfa = sm1.nfa} ans.oldState ans.oldAccepts))
        rest.word   (Start {nfa = sm2.nfa} t aos.oldIsElemOfOld rest.acc)
        rewrite ans.routineEqualityPrf in rewrite aos.routineEqualityPrf in
          rewrite rest.routineEq in (cong (Observe c ::) (eqPrf1To2 _ _ _))


evidenceTh1 (Step (CTh1 s) c CEnd prf1 (Accept CEnd Refl)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2
      ans1 : CombiningTransitionsForNewData (oneToTwo sm1 sm2 s c) CEnd prf1
      ans1 = aboutCombiningTransitionsForNew (oneToTwo sm1 sm2 s c) CEnd prf1 CTh1notEqCEnd
      ans2 : CombiningTransitionsForNewData (initTwoConcat sm2) CEnd ans1.stateIsElemOfNew
      ans2 = aboutCombiningTransitionsForNew (initTwoConcat sm2) CEnd ans1.stateIsElemOfNew CTh2notEqCEnd
  in MkEvidenceTh1Data
        [c] (Step {nfa = sm1.nfa} s c ans1.oldState ans1.oldIsElemOfOld
                    (Accept {nfa = sm1.nfa} ans1.oldState ans1.oldAccepts))
        []  (Start {nfa = sm2.nfa} ans2.oldState ans2.oldIsElemOfOld
                    (Accept {nfa = sm2.nfa} ans2.oldState ans2.oldAccepts))
        rewrite ans1.routineEqualityPrf in (rewrite ans2.routineEqualityPrf in
          (rewrite (rforEndConcat ans2.stateIsElemOfNew) in (cong (Observe c ::) (eqPrf1ToEnd _ _))))

public export
record ConcatEvidencePrfData  {word : Word} (re1 : CoreRE) (re2: CoreRE)
                              (acc: Accepting (thompson $ Concat re1 re2).nfa word) where
  constructor MkConcatEvidencePrfData
  word1 : Word
  acc1: Accepting (thompson re1).nfa word1
  word2 : Word
  acc2 : Accepting (thompson re2).nfa word2
  routineEq : extractRoutine (thompson $ Concat re1 re2).nfa (thompson $ Concat re1 re2).prog acc =
                extractRoutine (thompson re1).nfa (thompson re1).prog acc1 ++
                extractRoutine (thompson re2).nfa (thompson re2).prog acc2 ++ [Regular EmitPair]

public export
concatEvidencePrf : (re1 : CoreRE) -> (re2: CoreRE)
                  -> {0 word : Word}
                  -> (acc: Accepting (thompson $ Concat re1 re2).nfa word)
                  -> ConcatEvidencePrfData re1 re2 acc

concatEvidencePrf re1 re2 (Start CEnd prf (Accept CEnd Refl)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2
      ans1 : CombiningTransitionsForNewData (concatInit sm1 sm2) CEnd prf
      ans1 = aboutCombiningTransitionsForNew (concatInit sm1 sm2) CEnd prf CTh1notEqCEnd
      ans2 : CombiningTransitionsForNewData (initTwoConcat sm2) CEnd ans1.stateIsElemOfNew
      ans2 = aboutCombiningTransitionsForNew (initTwoConcat sm2) CEnd
                                              ans1.stateIsElemOfNew CTh2notEqCEnd
  in MkConcatEvidencePrfData
        [] (Start {nfa = (thompson re1).nfa} ans1.oldState ans1.oldIsElemOfOld
              (Accept {nfa = (thompson re1).nfa} ans1.oldState ans1.oldAccepts))
        [] (Start {nfa = (thompson re2).nfa} ans2.oldState ans2.oldIsElemOfOld
              (Accept {nfa = (thompson re2).nfa} ans2.oldState ans2.oldAccepts))
        rewrite ans1.routineEqualityPrf in (rewrite ans2.routineEqualityPrf in
            (rewrite (rforEndConcat ans2.stateIsElemOfNew) in (eqPrf1ToEnd _ _)))

concatEvidencePrf {word=(c::w)} re1 re2 (Start (CTh2 s) prf (Step (CTh2 s) c t prf1 acc)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2
      ans : CombiningTransitionsForNewData (concatInit sm1 sm2) (CTh2 s) prf
      ans = aboutCombiningTransitionsForNew (concatInit sm1 sm2) (CTh2 s) prf CTh2notEqCTh1
      aos : CombiningTransitionsForOldData (initTwoConcat sm2) (CTh2 s) ans.stateIsElemOfNew s
      aos = aboutCombiningTransitionsForOld (initTwoConcat sm2) (CTh2 s)
                                            ans.stateIsElemOfNew s
                                            injectionForCTh2 Refl
                                            (ch2NotElemOFEnd _)
      ev2 : EvidenceTh2Data {re1,re2,s} (Step {nfa = (thompson $ Concat re1 re2).nfa} (CTh2 s) c t prf1 acc)
      ev2 = evidenceTh2 {re1, re2} (Step {nfa = (thompson $ Concat re1 re2).nfa} (CTh2 s) c t prf1 acc)
  in MkConcatEvidencePrfData
          []        (Start {nfa = (thompson re1).nfa} ans.oldState ans.oldIsElemOfOld
                          (Accept {nfa = (thompson re1).nfa} ans.oldState ans.oldAccepts))
          ev2.word  (Start {nfa = sm2.nfa} s aos.oldIsElemOfOld ev2.acc)
          (rewrite ans.routineEqualityPrf in (rewrite aos.routineEqualityPrf in
              rewrite ev2.routineEq in (eqPrf1To2 _ _ _)))

concatEvidencePrf re1 re2 (Start (CTh1 s) prfInit (Step (CTh1 s) c t prf1 acc)) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2
      acc' : AcceptingFrom (thompson $ Concat re1 re2).nfa (CTh1 s) word
      acc' = Step {nfa = (thompson $ Concat re1 re2).nfa} (CTh1 s) c t prf1 acc
      allNext : EvidenceTh1Data {re1, re2} acc'
      allNext = evidenceTh1 acc'
      aos : CombiningTransitionsForOldData (concatInit sm1 sm2) (CTh1 s) prfInit s
      aos = aboutCombiningTransitionsForOld (concatInit sm1 sm2) (CTh1 s)
                                            prfInit s injectionForCTh1
                                            Refl (cTh1NotInStart2Cons sm2 s)
  in MkConcatEvidencePrfData
        allNext.word1   (Start {nfa = (thompson re1).nfa} s aos.oldIsElemOfOld allNext.acc1)
        allNext.word2   allNext.acc2
        rewrite aos.routineEqualityPrf in rewrite allNext.routineEq in (appendAssociative _ _ _)
