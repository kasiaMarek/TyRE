module Verification.Thompson.Concat.EqualityPrf

import Verification.Routine
import Evidence
import Data.List
import NFA
import Syntax.PreorderReasoning

export
eqPrf2ToEnd : (a : Routine)
        -> (Observe c :: (cast (a ++ [EmitPair]) ++ [])
                = Observe c :: ((cast a ++ []) ++ [Regular EmitPair]))

eqPrf2ToEnd a = cong (Observe c ::) $
  Calc $
    |~ (cast (a ++ [EmitPair]) ++ [])
    ~~ (cast (a ++ [EmitPair]))                 ...(appendNilRightNeutral _)
    ~~ ((cast a) ++ [Regular EmitPair])         ...(castConcat _ _)
    ~~ ((cast a ++ []) ++ [Regular EmitPair])   ...(cong (++ [Regular EmitPair]) (sym (appendNilRightNeutral _)))

export
eqPrf1ToEnd : (a : Routine) -> (b : Routine)
          -> (cast (a ++ b ++ [EmitPair]) ++ []
                = (cast a ++ []) ++ (cast b ++ []) ++ [Regular EmitPair])

eqPrf1ToEnd a b =
  Calc $
    |~ cast (a ++ b ++ [EmitPair]) ++ []
    ~~ cast (a ++ (b ++ [EmitPair]))                            ...(appendNilRightNeutral _)
    ~~ (cast a) ++ cast (b ++ [EmitPair])                       ...(castConcat _ _)
    ~~ (cast a) ++ (cast b) ++ [Regular EmitPair]               ...(cong ((cast a) ++) (castConcat _ _))
    ~~ (cast a ++ []) ++ (cast b) ++ [Regular EmitPair]         ...(cong (++ (cast b) ++ [Regular EmitPair]) (sym $ appendNilRightNeutral _))
    ~~ (cast a ++ []) ++ (cast b ++ []) ++ [Regular EmitPair]   ...(cong (\e => (cast a ++ []) ++ e ++ [Regular EmitPair]) (sym $ appendNilRightNeutral _))

export
eqPrf1To2 : (a : Routine) -> (b : Routine) -> (extr : ExtendedRoutine)
        -> (cast (a ++ b) ++ (extr ++ [Regular EmitPair])
              = (cast a ++ []) ++ ((cast b ++ extr) ++ [Regular EmitPair]))

eqPrf1To2 a b extr =
  Calc $
    |~ cast (a ++ b) ++ extr ++ [Regular EmitPair]
    ~~ (cast a ++ cast b) ++ extr ++ [Regular EmitPair]           ...(cong (++ (extr ++ [Regular EmitPair])) (castConcat _ _))
    ~~ cast a ++ (cast b ++ extr ++ [Regular EmitPair])           ...(sym $ appendAssociative _ _ _)
    ~~ cast a ++ (cast b ++ extr) ++ [Regular EmitPair]           ...(cong (cast a ++) (appendAssociative _ _ _))
    ~~ (cast a ++ []) ++ (cast b ++ extr) ++ [Regular EmitPair]   ...(cong (++ (cast b ++ extr) ++ [Regular EmitPair]) (sym $ appendNilRightNeutral _))

concatRoutinePrfAux : (mcvm : (Maybe Char, VMState)) -> (snd (executeRoutineSteps [Regular EmitPair] mcvm)).evidence = (snd mcvm).evidence :< PairMark
concatRoutinePrfAux (mc, vm) = Refl

export
concatRoutinePrf : (exr1 : ExtendedRoutine) -> (exr2 : ExtendedRoutine) -> (mcvm : (Maybe Char, VMState))
                  -> ((snd $ executeRoutineSteps (exr1 ++ exr2 ++ [Regular EmitPair]) mcvm).evidence
                        = (snd $ executeRoutineSteps exr2 (executeRoutineSteps exr1 mcvm)).evidence :< PairMark)
concatRoutinePrf exr1 exr2 mcvm =
  Calc $
    |~ (snd $ executeRoutineSteps (exr1 ++ exr2 ++ [Regular EmitPair]) mcvm).evidence
    ~~ (snd $ (executeRoutineSteps (exr2 ++ [Regular EmitPair]) (executeRoutineSteps exr1 mcvm))).evidence                    ...(cong (\e => (snd $ e).evidence) (routineComposition _ _ _))
    ~~ (snd $ (executeRoutineSteps [Regular EmitPair] (executeRoutineSteps exr2 (executeRoutineSteps exr1 mcvm)))).evidence   ...(cong (\e => (snd $ e).evidence) (routineComposition _ _ _))
    ~~ ((snd $ executeRoutineSteps exr2 (executeRoutineSteps exr1 mcvm)).evidence :< PairMark)                                ...(concatRoutinePrfAux _)
