module Verification.Thompson.Star.EqualityPrf

import Verification.Routine
import Evidence
import Data.List
import NFA
import Syntax.PreorderReasoning
import Data.SnocList

export
repRoutinePrf : (r : ExtendedRoutine) -> (mcvm : (Maybe Char, VMState))
              -> ((snd (executeRoutineSteps (r ++ [Regular EmitBList]) mcvm)).evidence =
                    (snd (executeRoutineSteps r mcvm)).evidence :< BList)
repRoutinePrf [] (mc, vm) = Refl
repRoutinePrf ((Regular x) :: xs) (mc, vm) = repRoutinePrf xs _
repRoutinePrf ((Observe x) :: xs) (mc, vm) = repRoutinePrf xs _
