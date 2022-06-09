module Verification.Thompson.Common

import Core
import Thompson
import NFA
import Evidence
import Extra
import Extra.Pred

import Verification.AcceptingPath
import Verification.Routine

import Data.List.Elem

public export
record PathWithRoutine (re : CoreRE) (pred : Pred ExtendedRoutine) where
    constructor PWE
    word : Word
    acc : Accepting (smToNFA (thompson re)) word
    predicateProof : pred (extractRoutine {sm = thompson re} acc)

public export
record PathFromWithRoutine (re : CoreRE) (s : (thompson re).State) (pred : Pred ExtendedRoutine) where
    constructor PFWE
    word : Word
    acc : AcceptingFrom (smToNFA (thompson re)) s word
    predicateProof : pred (extractRoutineFrom {sm = thompson re} acc)

statesImmutInMapRoutine : (isEnd : state -> Bool) -> (r : Routine) -> (xs : List (state, Routine)) -> (map Builtin.fst (addEndRoutine isEnd r xs) = map Builtin.fst xs)
statesImmutInMapRoutine isEnd r [] = Refl
statesImmutInMapRoutine isEnd r ((st, rout) :: xs) with (isEnd st)
    statesImmutInMapRoutine isEnd r ((st, rout) :: xs) | True = cong (st ::) (statesImmutInMapRoutine isEnd r xs)
    statesImmutInMapRoutine isEnd r ((st, rout) :: xs) | False = cong (st ::) (statesImmutInMapRoutine isEnd r xs)

export
addEndRoutineSpec : (isEnd : state -> Bool) 
                -> (r : Routine) 
                -> (xs : List (state, Routine)) 
                -> (x : state)
                -> (xInXs : x `Elem` map Builtin.fst (addEndRoutine isEnd r xs))
                -> (xInXs' : x `Elem` map Builtin.fst xs 
                        ** Either 
                            (isEnd x = True, 
                                    extractBasedOnFst (addEndRoutine isEnd r xs) xInXs 
                                =   extractBasedOnFst xs xInXs' ++ r)
                            (isEnd x = False, 
                                    extractBasedOnFst (addEndRoutine isEnd r xs) xInXs 
                                =   extractBasedOnFst xs xInXs'))

addEndRoutineSpec isEnd r [] x xInXs = absurd xInXs
addEndRoutineSpec isEnd r ((x, xr) :: xs) x' pos with (isEnd x) proof p
    addEndRoutineSpec isEnd r ((x, xr) :: xs) x Here | True = (Here ** Left (p, Refl))
    addEndRoutineSpec isEnd r ((x, xr) :: xs) x' (There pos) | True = 
        let (elmTail ** tail) = addEndRoutineSpec isEnd r xs x' pos
        in (There elmTail ** tail)
    addEndRoutineSpec isEnd r ((x, xr) :: xs) x Here | False = (Here ** Right (p, Refl))
    addEndRoutineSpec isEnd r ((x, xr) :: xs) x' (There pos) | False =
        let (elmTail ** tail) = addEndRoutineSpec isEnd r xs x' pos
        in (There elmTail ** tail)



||| Proof that in thompson contruction there are no paths coming out an accepting state.
export
noPathsFromAcceptingState   : (re : CoreRE) 
                            -> (s : (thompson re).State) 
                            -> (c : Char) 
                            -> ((thompson re).accepting s = True) 
                            -> {t : (thompson re).State} 
                            -> (t `Elem` map Builtin.fst ((thompson re).next s c)) 
                            -> Void

noPathsFromAcceptingState (Pred f) StartState c prf isElem = absurd prf
noPathsFromAcceptingState (Pred f) AcceptState c prf isElem = absurd isElem
noPathsFromAcceptingState Empty s c prf isElem = absurd isElem
noPathsFromAcceptingState (Group re) s c prf isElem = 
    let rw1 : ?
        rw1 = statesImmutInMapRoutine (thompson re).accepting [EmitString] (map (bimap id (const [])) ((thompson re).next s c))
        rw2 : ?
        rw2 = biMapOnFst ((thompson re).next s c) id (const [])
        (e' ** isElem') := 
            elemMapRev 
                (map fst ((thompson re).next s c))
                id
                (replace {p = (t `Elem`)} (trans rw1 rw2) isElem)
    in noPathsFromAcceptingState re s c prf isElem'
noPathsFromAcceptingState (Concat re1 re2) (Left _) c prf isElem = absurd prf
noPathsFromAcceptingState (Concat re1 re2) (Right s) c prf isElem = 
    let rw1 : ? 
        rw1 = statesImmutInMapRoutine (thompson (Concat re1 re2)).accepting [EmitPair] (map (bimap Right id) ((thompson re2).next s c))
        rw2 : ?
        rw2 = biMapOnFst ((thompson re2).next s c) Right id
        (e' ** isElem') := 
            elemMapRev 
                (map fst ((thompson re2).next s c))
                Right
                (replace {p = (t `Elem`)} (trans rw1 rw2) isElem)
    in noPathsFromAcceptingState re2 s c prf isElem'
noPathsFromAcceptingState (Alt re1 re2) (Left s) c prf isElem = 
    let rw1 := biMapOnFst (addEndRoutine ((thompson re1) .accepting) [EmitLeft] ((thompson re1) .next s c)) Left id
        rw2 := statesImmutInMapRoutine (thompson re1).accepting [EmitLeft] ((thompson re1) .next s c)
        (e' ** isElem') := 
            elemMapRev 
                (map fst ((thompson re1).next s c))
                Left
                (replace {p = (t `Elem`)} (trans rw1 (cong (map Left) rw2)) isElem)
    in noPathsFromAcceptingState re1 s c prf isElem'
noPathsFromAcceptingState (Alt re1 re2) (Right s) c prf isElem = 
    let rw1 := biMapOnFst (addEndRoutine ((thompson re2) .accepting) [EmitRight] ((thompson re2) .next s c)) Right id
        rw2 := statesImmutInMapRoutine (thompson re2).accepting [EmitRight] ((thompson re2) .next s c)
        (e' ** isElem') := 
            elemMapRev 
                (map fst ((thompson re2).next s c))
                Right
                (replace {p = (t `Elem`)} (trans rw1 (cong (map Right) rw2)) isElem)
    in noPathsFromAcceptingState re2 s c prf isElem'
noPathsFromAcceptingState (Star re) (Left s) c prf isElem = absurd prf
noPathsFromAcceptingState (Star re) (Right ()) c prf isElem = absurd isElem
