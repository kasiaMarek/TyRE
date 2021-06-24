module Verification.Routine.Thompson.Concat.EqualityPrf

import Verification.Routine
import Evidence
import Data.List
import NFA
import Syntax.PreorderReasoning

public export
eqPrf2E : (a : Routine)
        -> (Observe c :: (mapRoutine Nothing (a ++ [EmitPair]) ++ [])
                = Observe c :: ((mapRoutine Nothing a ++ []) ++ [Regular EmitPair]))

eqPrf2E a = cong (Observe c ::) $ Calc $
          |~ (mapRoutine Nothing (a ++ [EmitPair]) ++ [])
          ~~ (mapRoutine Nothing (a ++ [EmitPair]))                 ...(appendNilRightNeutral _)
          ~~ ((mapRoutine Nothing a) ++ [Regular EmitPair])         ...(mapRoutineConcat _ _ _)
          ~~ ((mapRoutine Nothing a ++ []) ++ [Regular EmitPair])   ...(cong (++ [Regular EmitPair]) (sym (appendNilRightNeutral _)))

public export
threePartEq : (a : Routine) -> (b : Routine)
          -> (mapRoutine Nothing (a ++ b ++ [EmitPair]) ++ []
                = (mapRoutine Nothing a ++ []) ++ (mapRoutine Nothing b ++ []) ++ [Regular EmitPair])

threePartEq a b = Calc $
                |~ mapRoutine Nothing (a ++ b ++ [EmitPair]) ++ []
                ~~ mapRoutine Nothing (a ++ (b ++ [EmitPair]))                                          ...(appendNilRightNeutral _)
                ~~ (mapRoutine Nothing a) ++ mapRoutine Nothing (b ++ [EmitPair])                       ...(mapRoutineConcat _ _ _)
                ~~ (mapRoutine Nothing a) ++ (mapRoutine Nothing b) ++ [Regular EmitPair]               ...(cong ((mapRoutine Nothing a) ++) (mapRoutineConcat _ _ _))
                ~~ (mapRoutine Nothing a ++ []) ++ (mapRoutine Nothing b) ++ [Regular EmitPair]         ...(cong (++ (mapRoutine Nothing b) ++ [Regular EmitPair]) (sym $ appendNilRightNeutral _))
                ~~ (mapRoutine Nothing a ++ []) ++ (mapRoutine Nothing b ++ []) ++ [Regular EmitPair]   ...(cong (\e => (mapRoutine Nothing a ++ []) ++ e ++ [Regular EmitPair]) (sym $ appendNilRightNeutral _))

public export
eqPrfS2 : (a : Routine) -> (b : Routine) -> (extr : ExtendedRoutine)
        -> (mapRoutine Nothing (a ++ b) ++ (extr ++ [Regular EmitPair])
              = (mapRoutine Nothing a ++ []) ++ ((mapRoutine Nothing b ++ extr) ++ [Regular EmitPair]))

eqPrfS2 a b extr = Calc $
                  |~ mapRoutine Nothing (a ++ b) ++ extr ++ [Regular EmitPair]
                  ~~ (mapRoutine Nothing a ++ mapRoutine Nothing b) ++ extr ++ [Regular EmitPair]           ...(cong (++ (extr ++ [Regular EmitPair])) (mapRoutineConcat _ _ _))
                  ~~ mapRoutine Nothing a ++ (mapRoutine Nothing b ++ extr ++ [Regular EmitPair])           ...(sym $ appendAssociative _ _ _)
                  ~~ mapRoutine Nothing a ++ (mapRoutine Nothing b ++ extr) ++ [Regular EmitPair]           ...(cong (mapRoutine Nothing a ++) (appendAssociative _ _ _))
                  ~~ (mapRoutine Nothing a ++ []) ++ (mapRoutine Nothing b ++ extr) ++ [Regular EmitPair]   ...(cong (++ (mapRoutine Nothing b ++ extr) ++ [Regular EmitPair]) (sym $ appendNilRightNeutral _))

concatRoutinePrfAux : (mcvm : (Maybe Char, VMState)) -> (snd (executeRoutineSteps [Regular EmitPair] mcvm)).evidence = (snd mcvm).evidence :< PairMark
concatRoutinePrfAux (mc, vm) = Refl

public export
concatRoutinePrf : (exr1 : ExtendedRoutine) -> (exr2 : ExtendedRoutine) -> (mcvm : (Maybe Char, VMState))
                  -> ((snd $ executeRoutineSteps (exr1 ++ exr2 ++ [Regular EmitPair]) mcvm).evidence
                        = (snd $ executeRoutineSteps exr2 (executeRoutineSteps exr1 mcvm)).evidence :< PairMark)
concatRoutinePrf exr1 exr2 mcvm = Calc $
                                    |~ (snd $ executeRoutineSteps (exr1 ++ exr2 ++ [Regular EmitPair]) mcvm).evidence
                                    ~~ (snd $ (executeRoutineSteps (exr2 ++ [Regular EmitPair]) (executeRoutineSteps exr1 mcvm))).evidence                    ...(cong (\e => (snd $ e).evidence) (routineComposition _ _ _))
                                    ~~ (snd $ (executeRoutineSteps [Regular EmitPair] (executeRoutineSteps exr2 (executeRoutineSteps exr1 mcvm)))).evidence   ...(cong (\e => (snd $ e).evidence) (routineComposition _ _ _))
                                    ~~ ((snd $ executeRoutineSteps exr2 (executeRoutineSteps exr1 mcvm)).evidence :< PairMark)                                ...(concatRoutinePrfAux _)
