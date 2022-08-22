module TyRE.Verification.Thompson.Star

import Data.SnocList
import Data.List
import Data.List.Elem
import Syntax.PreorderReasoning

import TyRE.CoreRE
import TyRE.Thompson
import TyRE.NFA
import TyRE.Evidence
import TyRE.Extra
import TyRE.Extra.Pred

import TyRE.Verification.AcceptingPath
import TyRE.Verification.Routine
import TyRE.Verification.Thompson.Common

nothingInFirstStatesAux : (sm : SM) -> (pos : Nothing `Elem` map Builtin.fst (filter (filterStar {s = sm.State}) sm.start)) -> Void
nothingInFirstStatesAux sm pos with (sm.start)
  nothingInFirstStatesAux sm pos | [] = absurd pos
  nothingInFirstStatesAux sm pos | ((Nothing, y) :: xs) = nothingInFirstStatesAux sm pos | xs
  nothingInFirstStatesAux sm (There pos) | (((Just x), y) :: xs) = nothingInFirstStatesAux sm pos | xs

nothingInFistStates : (sm : SM) -> (pos : Nothing `Elem` map Builtin.fst (firstStar sm)) -> pos = Here
nothingInFistStates sm Here = Refl
nothingInFistStates sm (There pos) = absurd (nothingInFirstStatesAux sm pos)

justInFistStatesAux : (xs : List (Maybe a, Routine)) 
                    -> (s : a) 
                    -> (pos : (Just s) `Elem` map Builtin.fst (filter (filterStar {s = a}) xs)) 
                    -> (posInStart : (Just s) `Elem` map Builtin.fst xs
                            ** extractBasedOnFst (filter (filterStar {s = a}) xs) pos = extractBasedOnFst xs posInStart)
justInFistStatesAux [] s pos = absurd pos
justInFistStatesAux ((Nothing, y) :: xs) s pos =
  let (posInStart ** eq) := justInFistStatesAux xs s pos
  in (There posInStart ** eq)
justInFistStatesAux (((Just x), y) :: xs) x Here = (Here ** Refl)
justInFistStatesAux (((Just x), y) :: xs) s (There pos) =
  let (posInStart ** eq) := justInFistStatesAux xs s pos
  in (There posInStart ** eq)

justInFistStates : (sm : SM) 
                -> (s : sm.State) 
                -> (pos : (Just s) `Elem` map Builtin.fst (firstStar sm)) 
                -> (posInStart : (Just s) `Elem` map Builtin.fst sm.start 
                        ** extractBasedOnFst (firstStar sm) pos = extractBasedOnFst sm.start posInStart)
justInFistStates sm s (There pos) = justInFistStatesAux sm.start s pos

public export
record StarPathFromWithRoutine (re : CoreRE) (s : (thompson re).State) (pred : Pred ExtendedRoutine) where
  constructor StarPFWR
  currWord : Word
  currAcc : AcceptingFrom (smToNFA (thompson re)) (Just s) currWord
  accs : List (word : Word ** Accepting (smToNFA (thompson re)) word)
  predicateProof : pred (extractRoutineFrom {sm = thompson re} currAcc ++ (accs >>= (\acc => extractRoutine {sm = thompson re} (snd acc))))

thompsonRoutinePrfStarTail  : (re : CoreRE)
                            -> (s : (thompson re).State)
                            -> {word : Word}
                            -> (acc : AcceptingFrom (smToNFA (thompson $ Star re)) (Just s) word)
                            -> StarPathFromWithRoutine re s (\r => 
                                      extractRoutineFrom {sm = (thompson $ Star re)} acc
                                        = r ++ [Regular EmitEList])

thompsonRoutinePrfStarTail re s (Step s c Nothing prf Accept) =
  let (pos1 ** (npos ** rw1)) := addEndTransactionSpecForNothing ? ? (\p => absurd p) prf
  in StarPFWR  [c] 
            (Step {nfa = smToNFA (thompson re)} s c Nothing pos1 (Accept {nfa = smToNFA (thompson re)}))
            []
            (cong (Observe c ::) (Calc $
              |~ cast (extractBasedOnFst (addEndTransition (firstStar (thompson re)) id ((thompson re).next s c)) prf) ++ []
              ~~ cast (extractBasedOnFst (addEndTransition (firstStar (thompson re)) id ((thompson re).next s c)) prf) ... appendNilRightNeutral _
              ~~ cast (extractBasedOnFst ((thompson re).next s c) pos1 ++ extractBasedOnFst (firstStar (thompson re)) npos) ... cong cast rw1
              ~~ cast (extractBasedOnFst ((thompson re).next s c) pos1 ++ [EmitEList]) ... cong (\x => cast (extractBasedOnFst ((thompson re).next s c) pos1 ++ extractBasedOnFst (firstStar (thompson re)) x)) (nothingInFistStates (thompson re) npos)
              ~~ cast (extractBasedOnFst ((thompson re).next s c) pos1) ++ [Regular EmitEList] ... castConcat _ _
              ~~ (cast (extractBasedOnFst ((thompson re).next s c) pos1) ++ []) ++ [Regular EmitEList] ... cong (++ [Regular EmitEList]) (sym (appendNilRightNeutral _))
              ~~ ((cast (extractBasedOnFst ((thompson re).next s c) pos1) ++ []) ++ []) ++ [Regular EmitEList] ... cong (++ [Regular EmitEList]) (sym (appendNilRightNeutral _))
            ))

thompsonRoutinePrfStarTail re s (Step s c (Just t) prf (Step t c' u prf' acc)) = 
  let (StarPFWR currWord currAcc accs rw1) := thompsonRoutinePrfStarTail re t (Step {nfa = smToNFA (thompson $ Star re)} t c' u prf' acc)
  in case (addEndTransitionLorR _ _ (Just t) prf) of
    Left (pos ** rw2) =>
      StarPFWR  (c :: currWord)
                (Step {nfa = smToNFA (thompson re)} s c (Just t) pos currAcc)
                accs
                (rewrite rw1 in cong (Observe c ::) (Calc $ 
                  |~ cast (extractBasedOnFst (addEndTransition (firstStar (thompson re)) id ((thompson re) .next s c)) prf) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList])
                  ~~ cast (extractBasedOnFst ((thompson re) .next s c) pos) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList]) ... cong (\x => cast x ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList])) rw2
                  ~~ (cast (extractBasedOnFst ((thompson re) .next s c) pos) ++ (extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs)) ++ [Regular EmitEList] ... appendAssociative _ _ _
                  ~~ ((cast (extractBasedOnFst ((thompson re) .next s c) pos) ++ extractRoutineFrom {sm = thompson re} currAcc) ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList] ... cong (++ [Regular EmitEList]) (appendAssociative _ _ _)
                ))
    Right (npos ** (pos' ** rw2)) =>
      let (pos ** rw3) := justInFistStates (thompson re) t pos'
      in StarPFWR [c]
                  (Step {nfa = smToNFA (thompson re)} s c Nothing npos (Accept {nfa = smToNFA (thompson re)}))
                  ((currWord ** (Start {nfa = smToNFA (thompson re)} (Just t) pos currAcc)) :: accs)
                  (cong (Observe c ::) (
                    rewrite bindConcatPrf accs (currWord ** (Start {nfa = smToNFA (thompson re)} (Just t) pos currAcc)) (\acc => extractRoutine {sm = thompson re} (snd acc)) 
                    in rewrite rw1 in (Calc $ 
                      |~ cast (extractBasedOnFst (addEndTransition (firstStar (thompson re)) id ((thompson re).next s c)) prf) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList])
                      ~~ cast (extractBasedOnFst ((thompson re).next s c) npos ++ extractBasedOnFst (firstStar (thompson re)) pos') ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList]) ... cong (\x => cast x ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList])) rw2
                      ~~ cast (extractBasedOnFst ((thompson re).next s c) npos ++ extractBasedOnFst (thompson re).start pos) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList]) ... cong (\x => cast (extractBasedOnFst ((thompson re).next s c) npos ++ x) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList])) rw3
                      ~~ (cast (extractBasedOnFst ((thompson re).next s c) npos) ++ cast (extractBasedOnFst (thompson re).start pos)) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList]) ... cong (++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList])) (castConcat _ _)
                      ~~ ((cast (extractBasedOnFst ((thompson re).next s c) npos) ++ cast (extractBasedOnFst (thompson re).start pos)) ++ (extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs)) ++ [Regular EmitEList] ... appendAssociative _ _ _
                      ~~ (cast (extractBasedOnFst ((thompson re).next s c) npos) ++ (cast (extractBasedOnFst (thompson re).start pos) ++ (extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs))) ++ [Regular EmitEList] ... cong (++ [Regular EmitEList]) (sym (appendAssociative _ _ _))
                      ~~ (cast (extractBasedOnFst ((thompson re).next s c) npos) ++ ((cast (extractBasedOnFst (thompson re).start pos) ++ extractRoutineFrom {sm = thompson re} currAcc) ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs)) ++ [Regular EmitEList] ... cong (\x => (cast (extractBasedOnFst ((thompson re).next s c) npos) ++ x) ++ [Regular EmitEList]) (appendAssociative _ _ _)
                      ~~ ((cast (extractBasedOnFst ((thompson re).next s c) npos) ++ []) ++ ((cast (extractBasedOnFst (thompson re).start pos) ++ extractRoutineFrom {sm = thompson re} currAcc) ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs)) ++ [Regular EmitEList] ... cong (\x => (x ++ ((cast (extractBasedOnFst (thompson re).start pos) ++ extractRoutineFrom {sm = thompson re} currAcc) ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs)) ++ [Regular EmitEList]) (sym (appendNilRightNeutral _))
                    )))

public export
record StarPathWithRoutine (re : CoreRE) (pred : Pred ExtendedRoutine) where
  constructor StarPWR
  accs : List (word : Word ** Accepting (smToNFA (thompson re)) word)
  predicateProof : pred (accs >>= (\ac => extractRoutine {sm = thompson re} (snd ac)))

export
thompsonRoutinePrfStar : (re : CoreRE)
                      -> {word : Word}
                      -> (acc : Accepting (smToNFA (thompson (Star re))) word)
                      -> (StarPathWithRoutine 
                            re 
                            (\r => extractRoutine {sm = thompson (Star re)} acc 
                              === (Regular EmitBList) :: r ++ [Regular EmitEList]))
thompsonRoutinePrfStar re (Start Nothing prf Accept) = 
  let (pos ** rw1) := mapRoutineSpec (firstStar (thompson re)) ? prf
      rw2 := nothingInFistStates (thompson re) pos
  in StarPWR [] (Calc $ 
      |~ cast (extractBasedOnFst (mapRoutine (EmitBList::) (firstStar (thompson re))) prf) ++ []
      ~~ Regular EmitBList :: cast (extractBasedOnFst (firstStar (thompson re)) pos) ++ [] ... cong (\x => cast x ++ []) rw1
      ~~ [Regular EmitBList, Regular EmitEList] ... cong (\x => Regular EmitBList :: cast (extractBasedOnFst (firstStar (thompson re)) x) ++ []) rw2)
thompsonRoutinePrfStar re (Start (Just s) prf (Step s c t prf' acc)) =
  let (StarPFWR currWord currAcc accs rwTail) := thompsonRoutinePrfStarTail re s (Step {nfa = smToNFA (thompson $ Star re)} s c t prf' acc)
      (pos' ** rw1) := mapRoutineSpec (firstStar (thompson re)) ? prf
      (pos ** rw2) := justInFistStates (thompson re) s pos'
  in StarPWR  ((currWord ** (Start {nfa = smToNFA (thompson re)} (Just s) pos currAcc)) :: accs) 
              (rewrite rwTail 
              in Calc $
                |~ cast (extractBasedOnFst (mapRoutine (EmitBList::) (firstStar (thompson re))) prf) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList]) 
                ~~ (Regular EmitBList :: cast (extractBasedOnFst (firstStar (thompson re)) pos')) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList]) ... cong (\x => cast x ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList])) rw1
                ~~ Regular EmitBList :: cast (extractBasedOnFst (thompson re).start pos) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList]) ... cong (\x => (Regular EmitBList :: cast x) ++ ((extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList])) rw2
                ~~ Regular EmitBList :: (cast (extractBasedOnFst (thompson re).start pos) ++ (extractRoutineFrom {sm = thompson re} currAcc ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs)) ++ [Regular EmitEList] ... cong (Regular EmitBList ::) (appendAssociative _ _ _)
                ~~ Regular EmitBList :: ((cast (extractBasedOnFst (thompson re).start pos) ++ extractRoutineFrom {sm = thompson re} currAcc) ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList] ... cong (\x => Regular EmitBList :: x ++ [Regular EmitEList]) (appendAssociative _ _ _)
                ~~ Regular EmitBList :: (extractRoutine {sm = thompson re} (Start {nfa = smToNFA (thompson re)} (Just s) pos currAcc) ++ listBindOnto (\acc => extractRoutine {sm = thompson re} (acc .snd)) [] accs) ++ [Regular EmitEList] ... Refl
                ~~ Regular EmitBList :: listBindOnto (\ac => extractRoutine {sm = thompson re} (ac .snd)) [] ((currWord ** (Start {nfa = smToNFA (thompson re)} (Just s) pos currAcc))::accs) ++ [Regular EmitEList] ... cong (\x => Regular EmitBList :: x ++ [Regular EmitEList]) (sym (bindConcatPrf accs (currWord ** (Start {nfa = smToNFA (thompson re)} (Just s) pos currAcc)) (\acc => extractRoutine {sm = thompson re} (snd acc))))
              )

export
starRightRoutineEquality : (mcvm : (Maybe Char, VMState)) -> (snd (executeRoutineSteps [Regular EmitEList] mcvm)).evidence = (snd mcvm).evidence :< EList
starRightRoutineEquality (mc, vm) = Refl
