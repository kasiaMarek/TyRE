module TyRE.Parser.Thompson

import Data.List
import Data.SortedSet

import TyRE.CoreRE
import TyRE.Parser.NFA
import public TyRE.GroupThompson

%default total

public export
data BaseState = StartState

public export
Eq BaseState where
  StartState  == StartState   = True

public export
mapStates : (s -> s') -> List (Maybe s, Routine) -> List (Maybe s', Routine)
mapStates f states = map (bimap (map f) id) states

public export
mapRoutine : (Routine -> Routine) -> List (s, Routine) -> List (s, Routine)
mapRoutine f xs = map (bimap id f) xs

public export
addEndRoutine : Routine -> List (Maybe state, Routine) -> List (Maybe state, Routine)
addEndRoutine routine [] = []
addEndRoutine routine ((Just x, r) :: xs) = (Just x, r) :: (addEndRoutine routine xs)
addEndRoutine routine ((Nothing, r) :: xs) = (Nothing, r ++ routine) :: (addEndRoutine routine xs)

public export
addEndTransition  : List (Maybe state', Routine) 
                  -> (state -> state') 
                  -> List (Maybe state, Routine) 
                  -> List (Maybe state', Routine)

addEndTransition newTrans conv [] = []
addEndTransition newTrans conv ((Just st, r) :: xs) = (Just (conv st), r) :: (addEndTransition newTrans conv xs)
addEndTransition newTrans conv ((Nothing, r) :: xs) = (mapRoutine (r ++) newTrans) ++ (addEndTransition newTrans conv xs)

--- functions for predicate
public export
nextPred  : (f : Char -> Bool) -> (st: BaseState) -> (c: Char)
          -> List (Maybe BaseState, Routine)
nextPred f StartState c = if (f c) then [(Nothing, [EmitLast])] else []

public export
smForPred : (f : Char -> Bool) -> SM
smForPred f = MkSM BaseState [(Just StartState, [])] (nextPred f)

-- functions for group
public export
addEmptyRoutine : List (Maybe Nat) -> List (Maybe Nat, Routine)
addEmptyRoutine states = map (`MkPair` []) states

public export
groupTransform : List (Maybe Nat) -> List (Maybe Nat, Routine)
groupTransform states = addEndRoutine [EmitString] (addEmptyRoutine states)

public export
smFromGroupSMNext : List (Nat, NextStates) -> Nat -> Char
                  -> List (Maybe Nat, Routine)
smFromGroupSMNext xs s c = groupTransform $
  case (find (\stns => fst stns == s) xs) of
    Nothing => []
    (Just (_, (MkNextStates condition isSat notSat))) => 
      (if (satisfies condition c) then isSat else notSat)

public export
smFromGroupSM : GroupSM -> SM
smFromGroupSM grsm = 
  MkSM  Nat 
        (mapRoutine (Record::) (groupTransform grsm.initStates))
        (smFromGroupSMNext grsm.statesWithNext)
--- functions for Alternation
public export
startAlt : (sm1, sm2 : SM) -> List(Maybe (Either sm1.State sm2.State), Routine)
startAlt sm1 sm2 = mapStates Left (addEndRoutine [EmitLeft] sm1.start) 
                ++ mapStates Right (addEndRoutine [EmitRight] sm2.start)

public export
nextAlt : (sm1, sm2 : SM) 
        -> Either sm1.State sm2.State 
        -> Char 
        -> List(Maybe (Either sm1.State sm2.State), Routine)

nextAlt sm1 sm2 (Left st) c = 
  mapStates Left (addEndRoutine [EmitLeft] (sm1.next st c))
nextAlt sm1 sm2 (Right st) c = 
  mapStates Right (addEndRoutine [EmitRight] (sm2.next st c))

--- functions for Concatenation
public export
startConcat : (sm1, sm2 : SM) -> List (Maybe (Either sm1.State sm2.State), Routine)
startConcat sm1 sm2 = 
  addEndRoutine 
    [EmitPair] 
    (addEndTransition 
      (mapStates Right sm2.start) 
      Left 
      sm1.start)

public export
nextConcat  : (sm1, sm2 : SM) 
            -> Either sm1.State sm2.State 
            -> Char 
            -> List (Maybe (Either sm1.State sm2.State), Routine)
nextConcat sm1 sm2 (Left st) c = 
  addEndRoutine 
    [EmitPair] 
    (addEndTransition
      (mapStates Right sm2.start) 
      Left 
      (sm1.next st c))
nextConcat sm1 sm2 (Right st) c = 
  addEndRoutine 
    [EmitPair]
    (mapStates Right (sm2.next st c))

--- functions for Kleene Star
public export
filterStar : (Maybe s, Routine) -> Bool
filterStar (Nothing, _) = False
filterStar (Just _, _) = True

public export
firstStar : (sm : SM) -> List (Maybe sm.State, Routine)
firstStar sm = (Nothing, [EmitEList]) :: (filter filterStar sm.start)

public export
startStar : (sm : SM) -> List (Maybe sm.State, Routine)
startStar sm = mapRoutine (EmitBList::) (firstStar sm)

public export
nextStar : (sm : SM) -> sm.State -> Char -> List (Maybe sm.State, Routine)
nextStar sm st c = addEndTransition (firstStar sm) id (sm.next st c)

--- Thompson construction
public export
thompson : CoreRE -> SM
thompson (CharPred cond) = smForPred (satisfies cond)
thompson (Empty) = MkSM Unit [(Nothing, [EmitUnit])] (\_,_ => [])
thompson (Group re) = smFromGroupSM (groupSM re)
thompson (Concat re1 re2) =
  let sm1 : SM := thompson re1
      sm2 : SM := thompson re2
      _ := sm1.isEq
      _ := sm2.isEq
  in MkSM (Either sm1.State sm2.State) 
          (startConcat sm1 sm2) 
          (nextConcat sm1 sm2)

thompson (Alt re1 re2) =
  let sm1 : SM := thompson re1
      sm2 : SM := thompson re2
      _ := sm1.isEq
      _ := sm2.isEq
  in MkSM (Either sm1.State sm2.State) 
          (startAlt sm1 sm2) 
          (nextAlt sm1 sm2)

thompson (Star re) =
  let sm : SM := thompson re
      _ := sm.isEq
  in MkSM sm.State
          (startStar sm)
          (nextStar sm)
