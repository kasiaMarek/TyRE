module Verification.Thompson

import Core
import Thompson
import NFA
import Evidence
import Extra

import Verification.AcceptingPath
import Verification.Routine
import Verification.Thompson.Predicate
import Verification.Thompson.Group
import Verification.Thompson.Concatenation
import Verification.Thompson.Alternation
import Verification.Thompson.Common

import Data.SnocList
import Data.List.Elem
import Syntax.PreorderReasoning

thompsonRoutinePrf : (re : CoreRE)
                  -> {word : Word}
                  -> (acc : Accepting (smToNFA (thompson re)) word)
                  -> (mcvm  : (Maybe Char, VMState))
                  -> (ev  : Evidence
                        ** (executeRoutineFrom (extractRoutine {sm = (thompson re)} acc) mcvm
                              = (snd mcvm).evidence ++ ev, ev `Encodes` [< Right $ ShapeCode re]))

thompsonRoutinePrf Empty {word = []} (Start Nothing Here Accept) (mc, vm) = ([< UnitMark] ** (Refl, AnEmpty [<]))
thompsonRoutinePrf Empty (Start (Just ()) Here acc) (mc, vm) impossible
thompsonRoutinePrf Empty (Start (Just ()) (There _) acc) (mc, vm) impossible

thompsonRoutinePrf (Pred f) acc mcvm = thompsonRoutinePrfPredicate f acc mcvm

thompsonRoutinePrf {word} (Group re) acc mcvm = 
  let routineEq = thompsonRoutinePrfGroup re acc
      (snocWord ** evidanceEq) = runGroupRoutine word mcvm
  in rewrite routineEq in ([< GroupMark snocWord] ** (evidanceEq, AGroup [<] snocWord))
thompsonRoutinePrf (Concat re1 re2) acc mcvm = 
  let (PWR word1 acc1 (PWR word2 acc2 routineEq)) := thompsonRoutinePrfConcat re1 re2 acc
      (ev1 ** (ev1Eq, ev1Encodes)) := thompsonRoutinePrf re1 acc1 mcvm
      mcvm2 : ?
      mcvm2 = executeRoutineSteps (extractRoutine {sm = thompson re1} acc1) mcvm
      (ev2 ** (ev2Eq, ev2Encodes)) := thompsonRoutinePrf re2 acc2 mcvm2
  in ([<] ++ ev1 ++ ev2 ++ [< PairMark] ** 
        ( Calc $ 
          |~ (snd (executeRoutineSteps (extractRoutine {sm = thompson (Concat re1 re2)} acc) mcvm)).evidence
          ~~ (snd (executeRoutineSteps (extractRoutine {sm = thompson re1} acc1 ++ extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair]) mcvm)).evidence ... cong (\x => (snd (executeRoutineSteps x mcvm)).evidence) routineEq
          ~~ (snd (executeRoutineSteps (extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitPair]) (executeRoutineSteps (extractRoutine {sm = thompson re1} acc1 ) mcvm))).evidence ... cong (\x => (snd x).evidence) (routineComposition _ _ _)
          ~~ (snd (executeRoutineSteps [Regular EmitPair] ((executeRoutineSteps (extractRoutine {sm = thompson re2} acc2) (executeRoutineSteps (extractRoutine {sm = thompson re1} acc1) mcvm))))).evidence ... cong (\x => (snd x).evidence) (routineComposition _ _ _)
          ~~ (snd ((executeRoutineSteps (extractRoutine {sm = thompson re2} acc2) (executeRoutineSteps (extractRoutine {sm = thompson re1} acc1) mcvm)))).evidence :< PairMark  ... (concatRoutinePrfAux _)
          ~~ (snd ((executeRoutineSteps (extractRoutine {sm = thompson re1} acc1) mcvm))).evidence ++ ev2 :< PairMark  ... cong (:< PairMark) ev2Eq
          ~~ ((snd mcvm).evidence ++ ev1) ++ ev2 :< PairMark  ... cong (++ ev2 :< PairMark) ev1Eq
          ~~ (snd mcvm).evidence ++ (ev1 ++ ev2) :< PairMark  ... cong (:< PairMark) (sym (appendAssociative _ _ _))
          ~~ ((snd mcvm).evidence ++ ([<] ++ (ev1 ++ ev2))) :< PairMark ... cong (\x => ((snd mcvm).evidence ++ x) :< PairMark) (sym (appendLinLeftNeutral _))
        , APair [<] ev1Encodes ev2Encodes))

thompsonRoutinePrf (Alt re1 re2) acc mcvm = 
  case (thompsonRoutinePrfAlt re1 re2 acc) of
    (Left (PWR word1 acc1 routineEq)) => 
      let (ev1 ** (ev1Eq, ev1Encodes)) := thompsonRoutinePrf re1 acc1 mcvm
      in ([<] ++ ev1 ++ [< LeftBranchMark] ** 
            ((rewrite routineEq in (Calc $
              |~ (snd (executeRoutineSteps (extractRoutine {sm = thompson re1} acc1 ++ [Regular EmitLeft]) mcvm)).evidence
              ~~ (snd (executeRoutineSteps [Regular EmitLeft] (executeRoutineSteps (extractRoutine {sm = thompson re1} acc1) mcvm))).evidence ... cong (\x => (snd x).evidence) (routineComposition _ _ _)
              ~~ (snd (executeRoutineSteps (extractRoutine {sm = thompson re1} acc1) mcvm)).evidence :< LeftBranchMark ... altLeftRoutineEquality _
              ~~ ((snd mcvm).evidence ++ ev1) :< LeftBranchMark ... cong (:< LeftBranchMark) ev1Eq
              ~~ ((snd mcvm).evidence ++ ([<] ++ ev1)) :< LeftBranchMark ... cong (\x => ((snd mcvm).evidence ++ x) :< LeftBranchMark) (sym (appendLinLeftNeutral _))
            ))
            , ALeft [<] ev1Encodes (ShapeCode re2)))
    (Right (PWR word2 acc2 routineEq)) =>
      let (ev2 ** (ev2Eq, ev2Encodes)) := thompsonRoutinePrf re2 acc2 mcvm
      in ([<] ++ ev2 ++ [< RightBranchMark] ** 
            ((rewrite routineEq in (Calc $
              |~ (snd (executeRoutineSteps (extractRoutine {sm = thompson re2} acc2 ++ [Regular EmitRight]) mcvm)).evidence
              ~~ (snd (executeRoutineSteps [Regular EmitRight] (executeRoutineSteps (extractRoutine {sm = thompson re2} acc2) mcvm))).evidence ... cong (\x => (snd x).evidence) (routineComposition _ _ _)
              ~~ (snd (executeRoutineSteps (extractRoutine {sm = thompson re2} acc2) mcvm)).evidence :< RightBranchMark ... altRightRoutineEquality _
              ~~ ((snd mcvm).evidence ++ ev2) :< RightBranchMark ... cong (:< RightBranchMark) ev2Eq
              ~~ ((snd mcvm).evidence ++ ([<] ++ ev2)) :< RightBranchMark ... cong (\x => ((snd mcvm).evidence ++ x) :< RightBranchMark) (sym (appendLinLeftNeutral _))
            ))
            , ARight [<] ev2Encodes (ShapeCode re1)))

thompsonRoutinePrf (Star x) acc mcvm = ?thompsonRoutinePrf_rhs_5

export
thompsonPrf : (re : CoreRE)
            -> {word : Word}
            -> (acc: Accepting (smToNFA (thompson re)) word)
            -> (extractEvidence {sm = thompson re} acc `Encodes` [< Right $ ShapeCode re])

thompsonPrf re acc =
  let sm : SM
      sm = thompson re
      rprf := extractRoutinePrf {sm} acc
      (ev ** (concat, encodes)) := thompsonRoutinePrf re acc (Nothing, initVM)
      prf : (ev = extractEvidence {sm} acc)
      prf = trans (sym (appendLinLeftNeutral ev)) (trans (sym concat) rprf)
  in replace {p=(\e => e `Encodes` [< Right $ ShapeCode re])} prf encodes

