module Verification.Routine.Thompson.Concat.EqualityPrf

import Verification.Routine
import Data.List
import NFA
import

public export
eqPrf2E : (a : Routine)
        -> (Observe c :: (mapRoutine Nothing (a ++ [EmitPair]) ++ [])
                = Observe c :: ((mapRoutine Nothing a ++ []) ++ [Regular EmitPair]))
eqPrf2E = ?eqPrf_2E

public export
threePartEq : (a : Routine) -> (b : Routine)
          -> (mapRoutine Nothing (a ++ b ++ [EmitPair]) ++ []
                = (mapRoutine Nothing a ++ []) ++ (mapRoutine Nothing b ++ []) ++ [Regular EmitPair])

threePartEq a b = ?threePartEq_rhs

public export
eqPrfS2 : (a : Routine) -> (b : Routine) -> (extr : ExtendedRoutine)
        -> (mapRoutine Nothing (a ++ b) ++ (extr ++ [Regular EmitPair])
              = (mapRoutine Nothing a ++ []) ++ ((mapRoutine Nothing b ++ extr) ++ [Regular EmitPair]))
