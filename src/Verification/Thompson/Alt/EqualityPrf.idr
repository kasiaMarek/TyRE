module Verification.Thompson.Alt.EqualityPrf

import Verification.Routine
import Evidence
import Data.List
import NFA
import Syntax.PreorderReasoning

altLeftEqPrfAux : (mcvm : (Maybe Char, VMState))
                -> ((snd $ executeRoutineSteps [Regular EmitLeft] mcvm).evidence =
                    (snd $ mcvm).evidence :< LeftBranchMark)
altLeftEqPrfAux (mc, vm) = Refl

public export
altLeftEqPrf : (exr : ExtendedRoutine) -> (mcvm : (Maybe Char, VMState))
            -> ((snd $ executeRoutineSteps (exr ++ [Regular EmitLeft]) mcvm).evidence
                      = (snd $ executeRoutineSteps exr mcvm).evidence :< LeftBranchMark)
altLeftEqPrf exr mcvm =
  Calc $
   |~ (snd $ executeRoutineSteps (exr ++ [Regular EmitLeft]) mcvm).evidence
   ~~ (snd $ executeRoutineSteps [Regular EmitLeft] (executeRoutineSteps exr mcvm)).evidence ...(cong (\e => (snd $ e).evidence) (routineComposition _ _ _))
   ~~ (snd $ executeRoutineSteps exr mcvm).evidence :< LeftBranchMark ...(altLeftEqPrfAux _)

altRightEqPrfAux : (mcvm : (Maybe Char, VMState))
               -> ((snd $ executeRoutineSteps [Regular EmitRight] mcvm).evidence =
                   (snd $ mcvm).evidence :< RightBranchMark)
altRightEqPrfAux (mc, vm) = Refl

public export
altRightEqPrf : (exr : ExtendedRoutine) -> (mcvm : (Maybe Char, VMState))
           -> ((snd $ executeRoutineSteps (exr ++ [Regular EmitRight]) mcvm).evidence
                     = (snd $ executeRoutineSteps exr mcvm).evidence :< RightBranchMark)
altRightEqPrf exr mcvm =
 Calc $
  |~ (snd $ executeRoutineSteps (exr ++ [Regular EmitRight]) mcvm).evidence
  ~~ (snd $ executeRoutineSteps [Regular EmitRight] (executeRoutineSteps exr mcvm)).evidence ...(cong (\e => (snd $ e).evidence) (routineComposition _ _ _))
  ~~ (snd $ executeRoutineSteps exr mcvm).evidence :< RightBranchMark ...(altRightEqPrfAux _)

export
endEqPrf : (a : Routine) -> (b : Instruction) -> (mapRoutine Nothing (a ++ [b]) ++ [] = ((mapRoutine Nothing a) ++ []) ++ [Regular b])
endEqPrf a b =
  Calc $
    |~ (mapRoutine Nothing (a ++ [b]) ++ [])
    ~~ (mapRoutine Nothing (a ++ [b])) ...(appendNilRightNeutral _)
    ~~ ((mapRoutine Nothing a) ++ [Regular b]) ...(mapRoutineConcat _ _ _)
    ~~ (((mapRoutine Nothing a) ++ []) ++ [Regular b]) ...(cong (++ [Regular b]) (sym $ appendNilRightNeutral _))
