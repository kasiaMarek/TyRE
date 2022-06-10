module Thompson

import Core
import NFA
import Data.List

%default total

public export
data BaseState = StartState

public export
Eq BaseState where
  StartState  == StartState   = True

--- helper functions
-- public export
-- mapMaybe : (f : a -> b) -> (Maybe a) -> (Maybe b)
-- mapMaybe f Nothing = Nothing
-- mapMaybe f (Just x) = Just (f x)

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

--- functions for Group
public export
groupTransform : (sm : SM) -> List (Maybe sm.State, Routine) -> List (Maybe sm.State, Routine)
groupTransform sm states = addEndRoutine [EmitString] (mapRoutine (const []) states)

--- functions for Alternation
public export
startAlt : (sm1, sm2 : SM) -> List(Maybe (Either sm1.State sm2.State), Routine)
startAlt sm1 sm2 = mapStates Left (addEndRoutine [EmitLeft] sm1.start) 
                ++ mapStates Right (addEndRoutine [EmitRight] sm2.start)

public export
nextAlt   : (sm1, sm2 : SM) 
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
acceptingStar : Either state () -> Bool
acceptingStar (Left _) = False
acceptingStar (Right ()) = True

public export
startStar : (sm : SM) -> List (Maybe (Either sm.State ()), Routine)
startStar sm = mapRoutine (EmitEList::) ((Just (Right ()), [EmitBList]) :: (mapStates Left sm.start))

public export
nextStar : (sm : SM) -> Either sm.State () -> Char -> List (Maybe (Either sm.State ()), Routine)
nextStar sm (Left st) c = addEndTransition [(Just (Right ()), [EmitBList])] Left (sm.next st c)
nextStar sm (Right ()) c = []

--- Thompson construction
public export
thompson : CoreRE -> SM
thompson (Pred f) = MkSM BaseState [(Just StartState, [])] (nextPred f)
thompson (Empty) = MkSM Unit [(Nothing, [EmitUnit])] (\_,_ => [])
thompson (Group re) =
  let sm : SM := thompson re
      _ := sm.isEq
  in MkSM sm.State 
          (groupTransform sm sm.start) 
          (\st,c => groupTransform sm (sm.next st c))

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
  in MkSM (Either sm.State ()) 
          (startStar sm) 
          (nextStar sm)
