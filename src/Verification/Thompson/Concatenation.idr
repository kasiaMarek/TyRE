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
import Data.List
import Data.List.Elem
import Syntax.PreorderReasoning

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

thompsonRoutinePrfConcatTail _ _ _ Accept impossible
thompsonRoutinePrfConcatTail {word = c :: cs} re1 re2 s (Step (Right s) c t prf acc) = 
  case acc of 
    Accept => 
      let (pos2' ** rw1) := addEndRoutineSpecForNothing ? ? prf
          (pos2 ** rw2) := mapStatesSpec ? Right Nothing pos2'
      in PFWR [c] 
              (Step {nfa = smToNFA (thompson re2)} s c Nothing pos2 (Accept {nfa = smToNFA (thompson re2)})) 
              (cong (Observe c ::) (Calc $ 
                |~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (mapStates Right ((thompson re2) .next s c))) prf) ++ []
                ~~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (mapStates Right ((thompson re2) .next s c))) prf) ... appendNilRightNeutral _
                ~~ cast (extractBasedOnFst (mapStates Right ((thompson re2) .next s c)) pos2' ++ [EmitPair]) ... cong cast rw1
                ~~ cast (extractBasedOnFst (mapStates Right ((thompson re2) .next s c)) pos2') ++ [Regular EmitPair] ... castConcat _ _
                ~~ cast (extractBasedOnFst ((thompson re2).next s c) pos2) ++ [Regular EmitPair] ... cong (\x => cast x ++ [Regular EmitPair]) rw2
                ~~ (cast (extractBasedOnFst ((thompson re2) .next s c) pos2) ++ []) ++ [Regular EmitPair] ... cong (++ [Regular EmitPair]) (sym (appendNilRightNeutral _))
              ))
    (Step u c' z prf' acc') => 
      case u of
        (Left s') => 
          let (pos2 ** _) := addEndRoutineSpecForJust ? ? (Left s') prf
          in absurd (leftNotElemOfRight pos2)
        (Right s') => 
          let (pos2' ** rw1) := addEndRoutineSpecForJust ? ? (Right s') prf
              (pos2 ** rw2) := mapStatesSpec ((thompson re2).next s c) ? (Just s') pos2'
              (PFWR wordTail accTail eqTail) := thompsonRoutinePrfConcatTail re1 re2 s' (Step {nfa = smToNFA (thompson (Concat re1 re2))} (Right s') c' z prf' acc')
          in (PFWR  (c::wordTail) 
                    (Step {nfa = smToNFA (thompson re2)} s c (Just s') pos2 accTail) 
                    (cong (Observe c ::) (rewrite eqTail in (Calc $
                      |~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (mapStates Right ((thompson re2) .next s c))) prf) ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair])
                      ~~ cast (extractBasedOnFst ((thompson re2) .next s c) pos2) ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair]) ... cong (\x => cast x ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair])) (trans rw1 rw2)
                      ~~ (cast (extractBasedOnFst ((thompson re2) .next s c) pos2) ++ extractRoutineFrom {sm = thompson re2} accTail) ++ [Regular EmitPair] ... appendAssociative _ _ _
                    ))))

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

thompsonRoutinePrfConcatFrom re1 re2 s Accept impossible
thompsonRoutinePrfConcatFrom re1 re2 s (Step (Left s) c t prf acc) = 
  case acc of
    Accept =>
      let (pos1' ** rw1) := addEndRoutineSpecForNothing [EmitPair] ? prf
          (pos1 ** (pos2' ** rw2)) := addEndTransactionSpecForNothing ? Nothing (\x => absurd x) pos1'
          (pos2 ** rw3) := mapStatesSpec (thompson re2).start ? Nothing pos2'
      in PFWR [c] 
              (Step {nfa = smToNFA (thompson re1)} s c Nothing pos1 (Accept {nfa = smToNFA (thompson re1)})) 
              (PWR  []
                    (Start {nfa = smToNFA (thompson re2)} Nothing pos2 (Accept {nfa = smToNFA (thompson re2)}))
                    (cong (Observe c ::) (Calc $ 
                      |~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .next s c))) prf) ++ []
                      ~~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .next s c))) prf) ... appendNilRightNeutral _
                      ~~ cast (extractBasedOnFst (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .next s c)) pos1' ++ [EmitPair]) ... cong cast rw1
                      ~~ cast (extractBasedOnFst (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .next s c)) pos1') ++ [Regular EmitPair] ... castConcat _ _
                      ~~ cast (extractBasedOnFst ((thompson re1) .next s c) pos1 ++ extractBasedOnFst (mapStates Right ((thompson re2) .start)) pos2') ++ [Regular EmitPair] ... cong (\x => cast x ++ [Regular EmitPair]) rw2
                      ~~ cast (extractBasedOnFst ((thompson re1) .next s c) pos1 ++ extractBasedOnFst ((thompson re2) .start) pos2) ++ [Regular EmitPair] ... cong (\x => cast (extractBasedOnFst ((thompson re1) .next s c) pos1 ++ x) ++ [Regular EmitPair]) rw3
                      ~~ (cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ cast (extractBasedOnFst ((thompson re2) .start) pos2)) ++ [Regular EmitPair] ... cong (++ [Regular EmitPair]) (castConcat _ _)
                      ~~ cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ cast (extractBasedOnFst ((thompson re2) .start) pos2) ++ [Regular EmitPair] ... sym (appendAssociative _ _ _)
                      ~~ (cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ []) ++ cast (extractBasedOnFst ((thompson re2) .start) pos2) ++ [Regular EmitPair] ... cong (++ cast (extractBasedOnFst ((thompson re2) .start) pos2) ++ [Regular EmitPair]) (sym (appendNilRightNeutral _))
                      ~~ (cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ []) ++ ((cast (extractBasedOnFst ((thompson re2) .start) pos2) ++ []) ++ [Regular EmitPair]) ... cong (\x => (cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ []) ++ (x ++ [Regular EmitPair])) (sym (appendNilRightNeutral _))
                      )))
    (Step (Left t') c' u prf' acc') => 
      let (PFWR word1 acc1 (PWR word2 acc2 rwTail)) := thompsonRoutinePrfConcatFrom re1 re2 t' (Step {nfa = smToNFA (thompson (Concat re1 re2))} (Left t') c' u prf' acc')
          (pos1' ** rw1) := addEndRoutineSpecForJust [EmitPair] ? (Left t') prf
          (pos1 ** rw2) := addEndTransactionSpecForJust ? t' leftNotElemOfRight pos1'
      in PFWR (c :: word1)
              (Step {nfa = smToNFA (thompson re1)} s c (Just t') pos1 acc1)
              (PWR  word2
                    acc2
                    (cong (Observe c ::) (rewrite rwTail in (Calc $
                      |~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .next s c))) prf) ++ extractRoutineFrom {sm = thompson re1} acc1 ++ extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair]
                      ~~ cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ extractRoutineFrom {sm = thompson re1} acc1 ++ extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair] ... cong (\x => cast x ++ extractRoutineFrom {sm = thompson re1} acc1 ++ extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair]) (trans rw1 rw2)
                      ~~ (cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ extractRoutineFrom {sm = thompson re1} acc1) ++ (extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair]) ... appendAssociative _ _ _
                    ))))
    (Step (Right t') c' u prf' acc') => 
      let (pos1' ** rw1) := addEndRoutineSpecForJust [EmitPair] ? (Right t') prf
          (pos1 ** (pos2' ** rw2)) := addEndTransactionSpecForNothing ? (Just (Right t')) (\x => absurd (eqForJust x)) pos1'
          (pos2 ** rw3) := mapStatesSpec (thompson re2).start ? (Just t') pos2'
          (PFWR wordTail accTail rwTail) := thompsonRoutinePrfConcatTail re1 re2 t' (Step {nfa = smToNFA (thompson (Concat re1 re2))} (Right t') c' u prf' acc')
      in PFWR [c]
              (Step {nfa = smToNFA (thompson re1)} s c Nothing pos1 (Accept {nfa = smToNFA (thompson re1)}))
              (PWR  wordTail
                    (Start {nfa = smToNFA (thompson re2)} (Just t') pos2 accTail)
                    (cong (Observe c ::) (rewrite rwTail in ( Calc $ 
                      |~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .next s c))) prf) ++ extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair]
                      ~~ cast (extractBasedOnFst ((thompson re1).next s c) pos1 ++ extractBasedOnFst (mapStates Right (thompson re2).start) pos2') ++ extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair] ... cong (\x => cast x ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair])) (trans rw1 rw2)
                      ~~ cast (extractBasedOnFst ((thompson re1).next s c) pos1 ++ extractBasedOnFst (thompson re2).start pos2) ++ extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair] ... cong (\x => cast (extractBasedOnFst ((thompson re1).next s c) pos1 ++ x) ++ extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair]) rw3
                      ~~ (cast (extractBasedOnFst ((thompson re1).next s c) pos1) ++ cast (extractBasedOnFst (thompson re2).start pos2)) ++ extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair] ... cong (++ extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair]) (castConcat _ _)
                      ~~ cast (extractBasedOnFst ((thompson re1).next s c) pos1) ++ cast (extractBasedOnFst (thompson re2).start pos2) ++ extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitPair] ... sym (appendAssociative _ _ _)
                      ~~ cast (extractBasedOnFst ((thompson re1).next s c) pos1) ++ (cast (extractBasedOnFst (thompson re2).start pos2) ++ extractRoutineFrom {sm = thompson re2} accTail) ++ [Regular EmitPair] ... cong (cast (extractBasedOnFst ((thompson re1).next s c) pos1) ++) (appendAssociative _ _ _)
                      ~~ (cast (extractBasedOnFst ((thompson re1).next s c) pos1) ++ []) ++ (cast (extractBasedOnFst (thompson re2).start pos2) ++ extractRoutineFrom {sm = thompson re2} accTail) ++ [Regular EmitPair] ... cong (++ (cast (extractBasedOnFst (thompson re2).start pos2) ++ extractRoutineFrom {sm = thompson re2} accTail) ++ [Regular EmitPair]) (sym (appendNilRightNeutral _))
                    ))))


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
      (npos1 ** (posrest ** rw2)) := addEndTransactionSpecForNothing ? Nothing (\x => absurd x) isElem1
      (npos2 ** rw3) := mapStatesSpec (thompson re2).start ? Nothing posrest
  in PWR  [] 
          (Start {nfa = smToNFA (thompson re1)} Nothing npos1 (Accept {nfa = smToNFA (thompson re1)})) 
          (PWR  []
                (Start {nfa = smToNFA (thompson re2)} Nothing npos2 (Accept {nfa = smToNFA (thompson re2)}))
                (Calc $
                  |~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .start))) prf) ++ []
                  ~~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .start))) prf) ... appendNilRightNeutral _
                  ~~ cast (extractBasedOnFst (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .start)) isElem1 ++ [EmitPair]) ... cong cast rw1
                  ~~ cast (extractBasedOnFst (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .start)) isElem1) ++ [Regular EmitPair] ... castConcat _ _
                  ~~ cast (extractBasedOnFst ((thompson re1) .start) npos1 ++ extractBasedOnFst (mapStates Right ((thompson re2) .start)) posrest) ++ [Regular EmitPair] ... cong (\x => cast x ++ [Regular EmitPair]) rw2
                  ~~ (cast (extractBasedOnFst ((thompson re1) .start) npos1) ++ cast (extractBasedOnFst (mapStates Right ((thompson re2) .start)) posrest)) ++ [Regular EmitPair] ... cong (++ [Regular EmitPair]) (castConcat _ _)
                  ~~ (cast (extractBasedOnFst ((thompson re1) .start) npos1) ++ cast (extractBasedOnFst ((thompson re2) .start) npos2)) ++ [Regular EmitPair] ... cong (\x => (cast (extractBasedOnFst ((thompson re1) .start) npos1) ++ cast x) ++ [Regular EmitPair]) rw3
                  ~~ cast (extractBasedOnFst ((thompson re1) .start) npos1) ++ (cast (extractBasedOnFst ((thompson re2) .start) npos2) ++ [Regular EmitPair]) ... sym (appendAssociative _ _ _)
                  ~~ (cast (extractBasedOnFst ((thompson re1) .start) npos1) ++ []) ++ (cast (extractBasedOnFst ((thompson re2) .start) npos2) ++ [Regular EmitPair]) ... cong (++ (cast (extractBasedOnFst ((thompson re2) .start) npos2) ++ [Regular EmitPair])) (sym (appendNilRightNeutral _))
                  ~~ (cast (extractBasedOnFst ((thompson re1) .start) npos1) ++ []) ++ ((cast (extractBasedOnFst ((thompson re2) .start) npos2) ++ []) ++ [Regular EmitPair]) ... cong (\x => (cast (extractBasedOnFst ((thompson re1) .start) npos1) ++ []) ++ (x ++ [Regular EmitPair])) (sym (appendNilRightNeutral _)) 
                ))
thompsonRoutinePrfConcat {word = c::cs} re1 re2 (Start (Just (Right s)) prf (Step (Right s) c t y acc)) =
  let (isElem1 ** rw1) := addEndRoutineSpecForJust [EmitPair] ? (Right s) prf
      (pos1 ** (pos2' ** rw2)) := addEndTransactionSpecForNothing ? (Just (Right s)) (\x => absurd (eqForJust x)) isElem1
      (pos2 ** rw3) := mapStatesSpec (thompson re2).start ? (Just s) pos2'
      path2 := thompsonRoutinePrfConcatTail re1 re2 s (Step {nfa = smToNFA (thompson (Concat re1 re2))} (Right s) c t y acc)
  in PWR [] 
      (Start {nfa = smToNFA (thompson re1)} Nothing pos1 (Accept {nfa = smToNFA (thompson re1)})) 
      (PWR  path2.word
            (Start {nfa = smToNFA (thompson re2)} (Just s) pos2 path2.acc)
            (Calc $
              |~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .start))) prf) ++ Observe c :: (cast (extractBasedOnFst ((thompson (Concat re1 re2)).next (Right s) c) y) ++ extractRoutineFrom {sm = thompson (Concat re1 re2)} acc)
              ~~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .start))) prf) ++ (extractRoutineFrom {sm = thompson re2} path2.acc ++ [Regular EmitPair]) ... cong (cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .start))) prf) ++) path2.predicateProof
              ~~ cast (extractBasedOnFst (thompson re1).start pos1 ++ extractBasedOnFst (mapStates Right ((thompson re2) .start)) pos2') ++ (extractRoutineFrom {sm = thompson re2} path2.acc ++ [Regular EmitPair]) ... cong (\x => cast x ++ (extractRoutineFrom {sm = thompson re2} path2.acc ++ [Regular EmitPair])) (trans rw1 rw2)
              ~~ (cast (extractBasedOnFst (thompson re1).start pos1) ++ cast (extractBasedOnFst (mapStates Right ((thompson re2) .start)) pos2')) ++ (extractRoutineFrom {sm = thompson re2} path2.acc ++ [Regular EmitPair]) ... cong (++ (extractRoutineFrom {sm = thompson re2} path2.acc ++ [Regular EmitPair])) (castConcat _ _)
              ~~ (cast (extractBasedOnFst (thompson re1).start pos1) ++ cast (extractBasedOnFst (thompson re2).start pos2)) ++ (extractRoutineFrom {sm = thompson re2} path2.acc ++ [Regular EmitPair]) ... cong (\x => (cast (extractBasedOnFst ((thompson re1) .start) pos1) ++ cast x) ++ (extractRoutineFrom {sm = thompson re2} path2.acc ++ [Regular EmitPair])) rw3
              ~~ cast (extractBasedOnFst (thompson re1).start pos1) ++ (cast (extractBasedOnFst (thompson re2).start pos2)) ++ (extractRoutineFrom {sm = thompson re2} path2.acc ++ [Regular EmitPair]) ... sym (appendAssociative _ _ _)
              ~~ cast (extractBasedOnFst (thompson re1).start pos1) ++ ((cast (extractBasedOnFst (thompson re2).start pos2) ++ extractRoutineFrom {sm = thompson re2} path2.acc) ++ [Regular EmitPair]) ... cong (cast (extractBasedOnFst (thompson re1).start pos1) ++) (appendAssociative _ _ _)
              ~~ (cast (extractBasedOnFst (thompson re1).start pos1) ++ []) ++ ((cast (extractBasedOnFst (thompson re2).start pos2) ++ extractRoutineFrom {sm = thompson re2} path2.acc) ++ [Regular EmitPair]) ... cong (++ ((cast (extractBasedOnFst (thompson re2).start pos2) ++ extractRoutineFrom {sm = thompson re2} path2.acc) ++ [Regular EmitPair])) (sym (appendNilRightNeutral _))
            ))
thompsonRoutinePrfConcat {word = c::cs} re1 re2 (Start (Just (Left s)) prf (Step (Left s) c t y z)) = 
  let (PFWR word1 acc1 (PWR word2 acc2 rwTail)) := thompsonRoutinePrfConcatFrom re1 re2 s (Step {nfa = smToNFA (thompson (Concat re1 re2))} (Left s) c t y z)
      (pos1' ** rw1) := addEndRoutineSpecForJust [EmitPair] ? (Left s) prf
      (pos1 ** rw2) := addEndTransactionSpecForJust ? s leftNotElemOfRight pos1'
  in PWR  word1
          (Start {nfa = smToNFA (thompson re1)} (Just s) pos1 acc1)
          (PWR word2 acc2 (rewrite rwTail in Calc $
            |~ cast (extractBasedOnFst (addEndRoutine [EmitPair] (addEndTransition (mapStates Right ((thompson re2) .start)) Left ((thompson re1) .start))) prf) ++ extractRoutineFrom {sm = thompson re1} acc1 ++ extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair]
            ~~ cast (extractBasedOnFst (thompson re1).start pos1) ++ extractRoutineFrom {sm = thompson re1} acc1 ++ extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair] ... cong (\x => cast x ++ extractRoutineFrom {sm = thompson re1} acc1 ++ extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair]) (trans rw1 rw2)
            ~~ (cast (extractBasedOnFst (thompson re1) .start pos1) ++ extractRoutineFrom {sm = thompson re1} acc1) ++ (extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair]) ... appendAssociative _ _ _
          ))
export
concatRoutinePrfAux : (mcvm : (Maybe Char, VMState)) -> (snd (executeRoutineSteps [Regular EmitPair] mcvm)).evidence = (snd mcvm).evidence :< PairMark
concatRoutinePrfAux (mc, vm) = Refl
