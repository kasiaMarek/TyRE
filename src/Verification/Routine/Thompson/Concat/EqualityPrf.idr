module Verification.Routine.Thompson.Concat.EqualityPrf

import Verification.Routine
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
