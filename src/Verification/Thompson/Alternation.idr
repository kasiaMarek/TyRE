module Verification.Thompson.Alternation

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
import Data.List.Elem.Extra

thompsonRoutineFromPrfAltLeft : (re1 : CoreRE)
                              -> (re2 : CoreRE)
                              -> {word : Word}
                              -> (s : (thompson re1).State)
                              -> (acc : AcceptingFrom (smToNFA (thompson (Alt re1 re2))) (Just (Left s)) word)
                              -> PathFromWithRoutine 
                                  re1
                                  s
                                  (\r1 => 
                                    extractRoutineFrom {sm = (thompson $ Alt re1 re2)} acc 
                                    = r1 ++ [Regular EmitLeft])
thompsonRoutineFromPrfAltLeft re1 re2 s (Step (Left s) c t prf acc) = 
  case acc of
    Accept =>
      let (pos1' ** rw1) := mapStatesSpec ? ? Nothing prf
          (pos1 ** rw2) := addEndRoutineSpecForNothing ? ? pos1'
      in PFWR [c]
              (Step {nfa = smToNFA (thompson re1)} s c Nothing pos1 (Accept {nfa = smToNFA (thompson re1)}))
              (cong (Observe c ::) (Calc $
                |~ cast (extractBasedOnFst (mapStates Left (addEndRoutine [EmitLeft] ((thompson re1) .next s c))) prf) ++ []
                ~~ cast (extractBasedOnFst ((thompson re1) .next s c) pos1 ++ [EmitLeft]) ++ [] ... cong (\x => cast x ++ []) (trans rw1 rw2)
                ~~ cast (extractBasedOnFst ((thompson re1) .next s c) pos1 ++ [EmitLeft]) ... appendNilRightNeutral _
                ~~ cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ [Regular EmitLeft] ... castConcat _ _
                ~~ (cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ []) ++ [Regular EmitLeft] ... cong (++ [Regular EmitLeft]) (sym (appendNilRightNeutral _))
              ))
    (Step et c' u prf' acc') => 
      case et of
        (Left t') =>
          let (PFWR wordTail accTail rwTail) := thompsonRoutineFromPrfAltLeft re1 re2 t' (Step {nfa = smToNFA (thompson (Alt re1 re2))} (Left t') c' u prf' acc')
              (pos1' ** rw1) := mapStatesSpec ? ? (Just t') prf
              (pos1 ** rw2) := addEndRoutineSpecForJust ? ? t' pos1'
          in PFWR (c :: wordTail)
                  (Step {nfa = smToNFA (thompson re1)} s c (Just t') pos1 accTail)
                  (cong (Observe c ::) (rewrite rwTail in (Calc $ 
                    |~ cast (extractBasedOnFst (mapStates Left (addEndRoutine [EmitLeft] ((thompson re1) .next s c))) prf) ++ (extractRoutineFrom {sm = thompson re1} accTail ++ [Regular EmitLeft])
                    ~~ cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ (extractRoutineFrom {sm = thompson re1} accTail ++ [Regular EmitLeft]) ... cong (\x => cast x ++ (extractRoutineFrom {sm = thompson re1} accTail ++ [Regular EmitLeft])) (trans rw1 rw2)
                    ~~ (cast (extractBasedOnFst ((thompson re1) .next s c) pos1) ++ extractRoutineFrom {sm = thompson re1} accTail) ++ [Regular EmitLeft] ... appendAssociative _ _ _
                  )))
        (Right t') => absurd (rightNotElemOfLeft prf)


thompsonRoutineFromPrfAltRight : (re1 : CoreRE)
                              -> (re2 : CoreRE)
                              -> {word : Word}
                              -> (s : (thompson re2).State)
                              -> (acc : AcceptingFrom (smToNFA (thompson (Alt re1 re2))) (Just (Right s)) word)
                              -> PathFromWithRoutine 
                                  re2
                                  s
                                  (\r2 => 
                                    extractRoutineFrom {sm = (thompson $ Alt re1 re2)} acc 
                                    = r2 ++ [Regular EmitRight])
thompsonRoutineFromPrfAltRight re1 re2 s (Step (Right s) c t prf acc) = 
  case acc of
    Accept =>
      let (pos2' ** rw1) := mapStatesSpec ? ? Nothing prf
          (pos2 ** rw2) := addEndRoutineSpecForNothing ? ? pos2'
      in PFWR [c]
              (Step {nfa = smToNFA (thompson re2)} s c Nothing pos2 (Accept {nfa = smToNFA (thompson re2)}))
              (cong (Observe c ::) (Calc $
                |~ cast (extractBasedOnFst (mapStates Right (addEndRoutine [EmitRight] ((thompson re2) .next s c))) prf) ++ []
                ~~ cast (extractBasedOnFst ((thompson re2).next s c) pos2 ++ [EmitRight]) ++ [] ... cong (\x => cast x ++ []) (trans rw1 rw2)
                ~~ cast (extractBasedOnFst ((thompson re2).next s c) pos2 ++ [EmitRight]) ... appendNilRightNeutral _
                ~~ cast (extractBasedOnFst ((thompson re2).next s c) pos2) ++ [Regular EmitRight] ... castConcat _ _
                ~~ (cast (extractBasedOnFst ((thompson re2) .next s c) pos2) ++ []) ++ [Regular EmitRight] ... cong (++ [Regular EmitRight]) (sym (appendNilRightNeutral _))
              ))
    (Step et c' u prf' acc') => 
      case et of
        (Left t') => absurd (leftNotElemOfRight prf)
        (Right t') => 
          let (PFWR wordTail accTail rwTail) := thompsonRoutineFromPrfAltRight re1 re2 t' (Step {nfa = smToNFA (thompson (Alt re1 re2))} (Right t') c' u prf' acc')
              (pos2' ** rw1) := mapStatesSpec ? ? (Just t') prf
              (pos2 ** rw2) := addEndRoutineSpecForJust ? ? t' pos2'
          in PFWR (c :: wordTail)
                  (Step {nfa = smToNFA (thompson re2)} s c (Just t') pos2 accTail)
                  (cong (Observe c ::) (rewrite rwTail in (Calc $
                    |~ cast (extractBasedOnFst (mapStates Right (addEndRoutine [EmitRight] ((thompson re2) .next s c))) prf) ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitRight])
                    ~~ cast (extractBasedOnFst ((thompson re2) .next s c) pos2) ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitRight]) ... cong (\x => cast x ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitRight])) (trans rw1 rw2)
                    ~~ (cast (extractBasedOnFst ((thompson re2) .next s c) pos2) ++ extractRoutineFrom {sm = thompson re2} accTail) ++ [Regular EmitRight] ... appendAssociative _ _ _
                  )))

export
thompsonRoutinePrfAlt : (re1 : CoreRE)
                      -> (re2 : CoreRE)
                      -> {word : Word}
                      -> (acc : Accepting (smToNFA (thompson (Alt re1 re2))) word)
                      -> Either 
                          (PathWithRoutine 
                            re1 
                            (\r1 => 
                              extractRoutine {sm = (thompson $ Alt re1 re2)} acc 
                              = r1 ++ [Regular EmitLeft]))
                          (PathWithRoutine 
                            re2 
                            (\r2 => 
                              extractRoutine {sm = (thompson $ Alt re1 re2)} acc 
                              = r2 ++ [Regular EmitRight]))

thompsonRoutinePrfAlt re1 re2 (Start Nothing prf Accept) = 
  case (extractBasedOnFstAppLor ? ? Nothing prf) of
    (Left (pos1'' ** rw1)) =>
      let (pos1' ** rw2) := mapStatesSpec ? ? Nothing pos1''
          (pos1 ** rw3) := addEndRoutineSpecForNothing ? ? pos1' 
      in Left (PWR  [] 
                    (Start {nfa = smToNFA (thompson re1)} Nothing pos1 (Accept {nfa = smToNFA (thompson re1)})) 
                    (Calc $
                      |~ cast (extractBasedOnFst (mapStates Left (addEndRoutine [EmitLeft] (thompson re1).start) ++ mapStates Right (addEndRoutine [EmitRight] (thompson re2).start)) prf) ++ []
                      ~~ cast (extractBasedOnFst (mapStates Left (addEndRoutine [EmitLeft] (thompson re1).start)) pos1'') ++ [] ... cong (\x => cast x ++ []) rw1
                      ~~ cast (extractBasedOnFst (thompson re1) .start pos1 ++ [EmitLeft]) ++ [] ... cong (\x => cast x ++ []) (trans rw2 rw3)
                      ~~ cast (extractBasedOnFst (thompson re1) .start pos1 ++ [EmitLeft]) ... appendNilRightNeutral _
                      ~~ cast (extractBasedOnFst (thompson re1) .start pos1) ++ [Regular EmitLeft] ... castConcat _ _
                      ~~ (cast (extractBasedOnFst (thompson re1) .start pos1) ++ []) ++ [Regular EmitLeft] ... cong (++ [Regular EmitLeft]) (sym (appendNilRightNeutral _))
                    ))
    (Right (pos2'' ** rw1)) =>
      let (pos2' ** rw2) := mapStatesSpec ? ? Nothing pos2''
          (pos2 ** rw3) := addEndRoutineSpecForNothing ? ? pos2' 
      in Right (PWR  [] 
                    (Start {nfa = smToNFA (thompson re2)} Nothing pos2 (Accept {nfa = smToNFA (thompson re2)}))
                    (Calc $
                      |~ cast (extractBasedOnFst (mapStates Left (addEndRoutine [EmitLeft] ((thompson re1) .start)) ++ mapStates Right (addEndRoutine [EmitRight] ((thompson re2) .start))) prf) ++ []
                      ~~ cast (extractBasedOnFst (mapStates Right (addEndRoutine [EmitRight] ((thompson re2) .start))) pos2'') ++ [] ... cong (\x => cast x ++ []) rw1
                      ~~ cast (extractBasedOnFst (mapStates Right (addEndRoutine [EmitRight] ((thompson re2) .start))) pos2'') ... appendNilRightNeutral _
                      ~~ cast (extractBasedOnFst (thompson re2).start pos2 ++ [EmitRight]) ... cong cast (trans rw2 rw3)
                      ~~ cast (extractBasedOnFst (thompson re2).start pos2) ++ [Regular EmitRight] ... castConcat _ _
                      ~~ (cast (extractBasedOnFst ((thompson re2) .start) pos2) ++ []) ++ [Regular EmitRight] ... cong (++ [Regular EmitRight]) (sym (appendNilRightNeutral _))
                    ))

thompsonRoutinePrfAlt re1 re2 (Start (Just (Left s)) prf (Step (Left s) c t prf' acc)) = 
  let (PFWR wordTail accTail rwTail) := thompsonRoutineFromPrfAltLeft re1 re2 s (Step {nfa = smToNFA (thompson (Alt re1 re2))} (Left s) c t prf' acc)
  in case (extractBasedOnFstAppLor ? ? (Just (Left s)) prf) of
      (Left (pos1'' ** rw1)) => 
        let (pos1' ** rw2) := mapStatesSpec ? ? (Just s) pos1''
            (pos1 ** rw3) := addEndRoutineSpecForJust ? ? s pos1' 
        in Left (PWR  wordTail
                (Start {nfa = smToNFA (thompson re1)} (Just s) pos1 accTail)
                (rewrite rwTail in (Calc $
                  |~ cast (extractBasedOnFst (mapStates Left (addEndRoutine [EmitLeft] ((thompson re1) .start)) ++ mapStates Right (addEndRoutine [EmitRight] ((thompson re2) .start))) prf) ++ (extractRoutineFrom {sm = thompson re1} accTail ++ [Regular EmitLeft])
                  ~~ cast (extractBasedOnFst ((thompson re1) .start) pos1) ++ (extractRoutineFrom {sm = thompson re1} accTail ++ [Regular EmitLeft]) ... cong (\x => cast x ++ (extractRoutineFrom {sm = thompson re1} accTail ++ [Regular EmitLeft])) (trans (trans rw1 rw2) rw3)
                  ~~ (cast (extractBasedOnFst ((thompson re1) .start) pos1) ++ extractRoutineFrom {sm = thompson re1} accTail) ++ [Regular EmitLeft] ... appendAssociative _ _ _
                )))
      (Right (pos2'' ** rw1)) => absurd (leftNotElemOfRight pos2'')

thompsonRoutinePrfAlt re1 re2 (Start (Just (Right s)) prf (Step (Right s) c t prf' acc)) = 
  let (PFWR wordTail accTail rwTail) := thompsonRoutineFromPrfAltRight re1 re2 s (Step {nfa = smToNFA (thompson (Alt re1 re2))} (Right s) c t prf' acc)
  in case (extractBasedOnFstAppLor ? ? (Just (Right s)) prf) of
      (Left (pos1'' ** rw1)) => absurd (rightNotElemOfLeft pos1'')
      (Right (pos2'' ** rw1)) =>
        let (pos2' ** rw2) := mapStatesSpec ? ? (Just s) pos2''
            (pos2 ** rw3) := addEndRoutineSpecForJust ? ? s pos2' 
        in Right (PWR wordTail
                      (Start {nfa = smToNFA (thompson re2)} (Just s) pos2 accTail)
                      (rewrite rwTail in (Calc $
                        |~ cast (extractBasedOnFst (mapStates Left (addEndRoutine [EmitLeft] ((thompson re1) .start)) ++ mapStates Right (addEndRoutine [EmitRight] ((thompson re2) .start))) prf) ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitRight])
                        ~~ cast (extractBasedOnFst ((thompson re2) .start) pos2) ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitRight]) ... cong (\x => cast x ++ (extractRoutineFrom {sm = thompson re2} accTail ++ [Regular EmitRight])) (trans (trans rw1 rw2) rw3)
                        ~~ (cast (extractBasedOnFst ((thompson re2) .start) pos2) ++ extractRoutineFrom {sm = thompson re2} accTail) ++ [Regular EmitRight] ... appendAssociative _ _ _
                      )))

export
altLeftRoutineEquality : (mcvm : (Maybe Char, VMState)) -> (snd (executeRoutineSteps [Regular EmitLeft] mcvm)).evidence = (snd mcvm).evidence :< LeftBranchMark
altLeftRoutineEquality (mc, vm) = Refl

export
altRightRoutineEquality : (mcvm : (Maybe Char, VMState)) -> (snd (executeRoutineSteps [Regular EmitRight] mcvm)).evidence = (snd mcvm).evidence :< RightBranchMark
altRightRoutineEquality (mc, vm) = Refl




