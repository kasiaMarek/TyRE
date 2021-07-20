module Verification.Thompson.Concat.Extra

import Data.Vect
import Data.List
import Data.List.Elem

import NFA
import NFA.Thompson

export
rforEndConcat : (pos: CEnd `Elem` [CEnd])
        -> (extractBasedOnFst {b = Routine} [CEnd] [[EmitPair]] pos = [EmitPair])
rforEndConcat Here = Refl
rforEndConcat (There _) impossible

export
cannotStepFrom2To1 : {0 a : Type} -> (sm2 : SM) -> (s: sm2.nfa.State) -> (c : Char) -> (t: a)
                  -> ((CTh1 t) `Elem` (fst $ combineTransitions $ twoToEndConcat {a} sm2 s c)) -> Void
cannotStepFrom2To1 sm2 s c t pos with (sm2.prog.next s c)
  cannotStepFrom2To1 sm2 s c t pos | routine with (sm2.nfa.next s c)
    cannotStepFrom2To1 sm2 s c t pos | [] | [] impossible
    cannotStepFrom2To1 sm2 s c t pos | (x :: xs) | (y :: ys) with (sm2.nfa.accepting y)
      cannotStepFrom2To1 sm2 s c t (There (There pos)) | (x :: xs) | (y :: ys) | True =
        cannotStepFrom2To1 sm2 s c t pos | xs | ys
      cannotStepFrom2To1 sm2 s c t (There pos) | (x :: xs) | (y :: ys) | False =
        cannotStepFrom2To1 sm2 s c t pos | xs | ys

export
cTh1NotInStart2Cons : {0 a : Type} -> (sm2 : SM) -> (s : a)
                    -> ((CTh1 s) `Elem` (fst $ start2Cons sm2)) -> Void
cTh1NotInStart2Cons sm2 s pos with (sm2.prog.init)
  cTh1NotInStart2Cons sm2 s pos | init with (sm2.nfa.start)
    cTh1NotInStart2Cons sm2 s pos | [] | [] impossible
    cTh1NotInStart2Cons sm2 s pos | (x :: xs) | (y :: ys) with (sm2.nfa.accepting y)
      cTh1NotInStart2Cons sm2 s (There (There pos')) | (x :: xs) | (y :: ys) | True =
        cTh1NotInStart2Cons sm2 s pos' | xs | ys
      cTh1NotInStart2Cons sm2 s (There pos') | (x :: xs) | (y :: ys) | False =
        cTh1NotInStart2Cons sm2 s pos' | xs | ys
