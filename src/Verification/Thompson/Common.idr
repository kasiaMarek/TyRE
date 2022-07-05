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
import Data.List.Elem.Extra

public export
record PathWithRoutine (re : CoreRE) (pred : Pred ExtendedRoutine) where
  constructor PWR
  word : Word
  acc : Accepting (smToNFA (thompson re)) word
  predicateProof : pred (extractRoutine {sm = thompson re} acc)

public export
record PathFromWithRoutine (re : CoreRE) (s : (thompson re).State) (pred : Pred ExtendedRoutine) where
  constructor PFWR
  word : Word
  acc : AcceptingFrom (smToNFA (thompson re)) (Just s) word
  predicateProof : pred (extractRoutineFrom {sm = thompson re} acc)

export
addEndRoutineSpecForNothing : (r : Routine) 
                            -> (xs : List (Maybe state, Routine)) 
                            -> (xInXs : Nothing `Elem` map Builtin.fst (addEndRoutine r xs))
                            -> (xInXs' : Nothing `Elem` map Builtin.fst xs **
                                  (   extractBasedOnFst (addEndRoutine r xs) xInXs 
                                  =   extractBasedOnFst xs xInXs' ++ r            ))
addEndRoutineSpecForNothing _ [] Here impossible
addEndRoutineSpecForNothing _ [] (There x) impossible
addEndRoutineSpecForNothing r ((Nothing, xr) :: xs) Here = (Here ** Refl)
addEndRoutineSpecForNothing r ((Nothing, xr) :: xs) (There pos) = 
  let (elmTail ** tail) = addEndRoutineSpecForNothing r xs pos
  in (There elmTail ** tail)
addEndRoutineSpecForNothing r ((Just x, xr) :: xs) (There pos) =
  let (elmTail ** tail) = addEndRoutineSpecForNothing r xs pos
  in (There elmTail ** tail)

export
addEndRoutineSpecForJust  : (r : Routine) 
                          -> (xs : List (Maybe state, Routine))
                          -> (x : state)
                          -> (xInXs : (Just x) `Elem` map Builtin.fst (addEndRoutine r xs))
                          -> (xInXs' : (Just x) `Elem` map Builtin.fst xs **
                                (   extractBasedOnFst (addEndRoutine r xs) xInXs 
                                =   extractBasedOnFst xs xInXs'                  ))

addEndRoutineSpecForJust _ [] st Here impossible
addEndRoutineSpecForJust _ [] st (There x) impossible
addEndRoutineSpecForJust r ((Just st, xr) :: xs) st Here = (Here ** Refl)
addEndRoutineSpecForJust r ((Nothing, xr) :: xs) st (There pos) = 
  let (elmTail ** tail) = addEndRoutineSpecForJust r xs st pos
  in (There elmTail ** tail)
addEndRoutineSpecForJust r ((Just x, xr) :: xs) st (There pos) =
  let (elmTail ** tail) = addEndRoutineSpecForJust r xs st pos
  in (There elmTail ** tail)

export
mapRoutineSpec  : (xs : List (state, Routine)) 
                -> (f : Routine -> Routine) 
                -> (sInMapedXs : s `Elem` map Builtin.fst (mapRoutine f xs)) 
                -> (sInXs : s `Elem` map Builtin.fst xs ** 
                      extractBasedOnFst (mapRoutine f xs) sInMapedXs
                        = f (extractBasedOnFst xs sInXs)             )
mapRoutineSpec [] f sInMapedXs = absurd sInMapedXs
mapRoutineSpec ((s, y) :: xs) f Here = (Here ** Refl)
mapRoutineSpec ((x, y) :: xs) f (There pos) = 
  let (inTail ** eq) = mapRoutineSpec xs f pos
  in (There inTail ** eq)

export
addEndTransactionSpecForNothing : {newStates : List (Maybe state', Routine)}
                                -> {conv : state -> state'}
                                -> (xs: List (Maybe state, Routine))
                                -> (newState : Maybe state')
                                -> ({y : state} -> newState = Just (conv y) -> Void)
                                -> (xInXs : newState `Elem` map Builtin.fst (addEndTransition newStates conv xs))
                                -> (xInXs' : Nothing `Elem`  map Builtin.fst xs ** 
                                    (newStateInNewStates : newState `Elem` map Builtin.fst newStates **
                                      (   extractBasedOnFst (addEndTransition newStates conv xs) xInXs 
                                      =   extractBasedOnFst xs xInXs'  ++  extractBasedOnFst newStates newStateInNewStates)))

addEndTransactionSpecForNothing [] newState newIsNotOld xInXs = absurd xInXs
addEndTransactionSpecForNothing ((Nothing, r) :: xs) st newIsNotOld xInXs = 
  case (extractBasedOnFstAppLor ? ? st xInXs) of
    Right (isElem ** eq1) => 
      let (npos ** (newStateInNewStates ** eq2)) = addEndTransactionSpecForNothing xs st newIsNotOld isElem
      in (There npos ** (newStateInNewStates ** trans eq1 eq2))
    Left (isElem ** eq1) => 
      let (newStateInNewStates ** eq2) = mapRoutineSpec ? ? isElem
      in (Here ** (newStateInNewStates ** trans eq1 eq2))
addEndTransactionSpecForNothing {conv} (((Just x), r) :: xs) (Just (conv x)) newIsNotOld Here = absurd (newIsNotOld Refl)
addEndTransactionSpecForNothing (((Just x), r) :: xs) st newIsNotOld (There pos) = 
  let (npos ** (newStateInNewStates ** eq)) = addEndTransactionSpecForNothing xs st newIsNotOld pos
  in (There npos ** (newStateInNewStates ** eq))

export
addEndTransactionSpecForJust : {newStates : List (Maybe state', Routine)}
                            -> {conv : state -> state'}
                            -> (xs: List (Maybe state, Routine))
                            -> (x : state)
                            -> (xNotInNew : ((Just (conv x)) `Elem` map Builtin.fst newStates) -> Void)
                            -> (xInXs : (Just (conv x)) `Elem` map Builtin.fst (addEndTransition newStates conv xs))
                            -> (xInXs' : (Just x) `Elem` map Builtin.fst xs **
                                  (   extractBasedOnFst (addEndTransition newStates conv xs) xInXs 
                                  =   extractBasedOnFst xs xInXs'))

addEndTransactionSpecForJust [] x xNotInNew xInXs = absurd xInXs
addEndTransactionSpecForJust {conv} ((Nothing, z) :: xs) x xNotInNew xInXs =
  case (extractBasedOnFstAppLor ? ? (Just (conv x)) xInXs) of
    Right (isElem ** eq1) => 
      let (xInXsTail ** eq2) = addEndTransactionSpecForJust xs x xNotInNew isElem
      in (There xInXsTail ** trans eq1 eq2)
    Left (isElem ** eq1) => 
      let (convXInNewStates ** _) = mapRoutineSpec ? ? isElem
      in absurd (xNotInNew convXInNewStates)
addEndTransactionSpecForJust (((Just y), z) :: xs) x xNotInNew (There pos) = 
  let (xInXsTail ** eq) = addEndTransactionSpecForJust xs x xNotInNew pos
  in (There xInXsTail ** eq)
---TODO :: shouldn't Here also be a valid option ? see what's wrong with this...

-- Since only needed for Star we prove it for `id` for simplicity. It can be easily generalised.
export
addEndTransitionLorR : (newStates : List (Maybe state, Routine))
                    -> (xs : List (Maybe state, Routine))
                    -> (x : Maybe state)
                    -> (xInXs : x `Elem` map Builtin.fst (addEndTransition newStates Prelude.Basics.id xs))
                    -> Either (xInXs' : x `Elem` map Builtin.fst xs **
                                  (   extractBasedOnFst (addEndTransition newStates Prelude.Basics.id xs) xInXs 
                                  =   extractBasedOnFst xs xInXs'))
                              (xInXs' : Nothing `Elem`  map Builtin.fst xs ** 
                                    (newStateInNewStates : x `Elem` map Builtin.fst newStates **
                                      (   extractBasedOnFst (addEndTransition newStates Prelude.Basics.id xs) xInXs 
                                      =   extractBasedOnFst xs xInXs'  ++  extractBasedOnFst newStates newStateInNewStates)))
addEndTransitionLorR newStates [] x xInXs = absurd xInXs
addEndTransitionLorR newStates ((Nothing, z) :: xs) x xInXs =
  case (extractBasedOnFstAppLor ? ? x xInXs) of
    Right (isElem ** eq1) =>
      case (addEndTransitionLorR newStates xs x isElem) of
        Left (xInXsTail ** eq2) => Left (There xInXsTail ** trans eq1 eq2)
        Right (npos ** (newStateInNewStates ** eq2)) => Right (There npos ** (newStateInNewStates ** trans eq1 eq2))
    Left (isElem ** eq1) => 
      let (newStateInNewStates ** eq2) = mapRoutineSpec ? ? isElem
      in Right (Here ** (newStateInNewStates ** trans eq1 eq2))
addEndTransitionLorR newStates (((Just y), z) :: xs) (Just y) Here = Left (Here ** Refl)
addEndTransitionLorR newStates (((Just y), z) :: xs) x (There pos) = 
  case (addEndTransitionLorR newStates xs x pos) of
    Left (xInXsTail ** eq) => Left (There xInXsTail ** eq)
    Right (npos ** (newStateInNewStates ** eq)) => Right (There npos ** (newStateInNewStates ** eq))


export
mapStatesSpec : (xs : List (Maybe s, Routine))
              -> (f : s -> s')
              -> (e : Maybe s)
              -> (isElem : map f e `Elem` map Builtin.fst (mapStates f xs))
              -> (isElem': e `Elem` map Builtin.fst xs ** extractBasedOnFst (mapStates f xs) isElem = extractBasedOnFst xs isElem')
mapStatesSpec [] f e pos = absurd pos
mapStatesSpec ((Nothing, _) :: xs) f Nothing Here = (Here ** Refl)
mapStatesSpec (_ :: xs) f Nothing (There pos) = 
  let (isElemTail ** eq) = mapStatesSpec xs f Nothing pos
  in (There isElemTail ** eq)
mapStatesSpec ((y, _) :: xs) f (Just z) (There pos) = 
  let (isElemTail ** eq) = mapStatesSpec xs f (Just z) pos
  in (There isElemTail ** eq)

export
leftNotElemOfRight : {xs : List (Maybe a, Routine)} -> Elem (Just (Left s)) (map Builtin.fst (mapStates Right xs)) -> Void
leftNotElemOfRight {xs = []} pos = absurd pos
leftNotElemOfRight {xs = (Right x) :: xs} Here impossible
leftNotElemOfRight {xs = _ :: xs} (There pos) = leftNotElemOfRight {xs} pos

export
rightNotElemOfLeft : {xs : List (Maybe a, Routine)} -> Elem (Just (Right s)) (map Builtin.fst (mapStates Left xs)) -> Void
rightNotElemOfLeft {xs = []} pos = absurd pos
rightNotElemOfLeft {xs = ((Left _) :: xs)} Here impossible
rightNotElemOfLeft {xs = (_ :: xs)} (There pos) = rightNotElemOfLeft {xs} pos
