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

export
starEq0 : (r : Routine)
        -> (cast (r ++ [EmitBList]) ++ []
            = (cast r ++ []) ++ [Regular EmitBList])

starEq0 r = Calc $
              |~ cast (r ++ [EmitBList]) ++ []
              ~~ cast (r ++ [EmitBList])                ...(appendNilRightNeutral _)
              ~~ cast r ++ [Regular EmitBList]          ...(castConcat _ _)
              ~~ (cast r ++ []) ++ [Regular EmitBList]  ...(cong (++ [Regular EmitBList]) (sym $ appendNilRightNeutral _))

export
appendAssociative4 : (s : List a) -> (r : List a) -> (e : List a) -> (f : List a)
                  -> (s ++ (r ++ (e ++ f)) = ((s ++ r) ++ e) ++ f)
appendAssociative4 s r e f =
  Calc $
    |~ s ++ (r ++ (e ++ f))
    ~~ s ++ ((r ++ e) ++ f)   ...(cong (s ++) (appendAssociative _ _ _))
    ~~ (s ++ (r ++ e)) ++ f   ...(appendAssociative _ _ _)
    ~~ ((s ++ r) ++ e) ++ f   ...(cong (++ f) (appendAssociative _ _ _))

export
starEq1 : (r, b : Routine) -> (c, e, m : ExtendedRoutine)
        -> ((cast (r ++ b) ++ (c ++ (e ++ m))) =
              ((cast r ++ []) ++ (((cast b ++ c) ++ e) ++ m)))
starEq1 r b c e m =
    Calc $
      |~ cast (r ++ b) ++ (c ++ (e ++ m))
      ~~ (cast r ++ cast b) ++ (c ++ (e ++ m))              ...(cong (++ (c ++ (e ++ m))) (castConcat _ _))
      ~~ cast r ++ (cast b ++ (c ++ (e ++ m)))              ...(sym $ appendAssociative _ _ _)
      ~~ cast r ++ (((cast b ++ c) ++ e) ++ m)              ...(cong (cast r ++) (appendAssociative4 _ _ _ _))
      ~~ (cast r ++ []) ++ (((cast b ++ c) ++ e) ++ m)      ...(cong (++ (((cast b ++ c) ++ e) ++ m)) (sym $ appendNilRightNeutral _))
