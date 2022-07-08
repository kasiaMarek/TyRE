module Thompson.GroupThompson

import Core
import NFA
import Data.List
import Data.SortedSet

public export
record NextStates where
  constructor MkNextStates
  condition : CharCond
  isSat : List (Maybe Nat)
  notSat : List (Maybe Nat)

public export
record GroupSM where
  constructor MkGroupSM
  initStates : List (Maybe Nat)
  statesWithNext : List (Nat, NextStates)
  max : Nat

public export
mapRoutine : (Routine -> Routine) -> List (s, Routine) -> List (s, Routine)
mapRoutine f xs = map (bimap id f) xs

public export
addEndRoutine : Routine -> List (Maybe state, Routine) -> List (Maybe state, Routine)
addEndRoutine routine [] = []
addEndRoutine routine ((Just x, r) :: xs) = (Just x, r) :: (addEndRoutine routine xs)
addEndRoutine routine ((Nothing, r) :: xs) = (Nothing, r ++ routine) :: (addEndRoutine routine xs)

filterNothing : List (Maybe Nat) -> List (Maybe Nat)

replaceEndInInit : List (Maybe Nat) -> List (Maybe Nat) -> List (Maybe Nat)
replaceEndInInit xs mks =
  case (find (== Nothing) xs) of
    Nothing => xs
    Just _ => mks ++ (filterNothing xs)

replaceEndInNext : List (Nat, NextStates) -> List (Maybe Nat) -> List (Nat, NextStates)
replaceEndInNext [] mks = []
replaceEndInNext ((n, (MkNextStates condition isSat notSat)) :: xs) mks = 
  (n, (MkNextStates condition (replaceEndInInit isSat mks) (replaceEndInInit notSat mks))) :: (replaceEndInNext xs mks)

groupStates : Nat -> CoreRE -> GroupSM
groupStates n (CharPred cond) = 
  MkGroupSM [Just n] [(n, MkNextStates cond [Nothing] [])] (n+1)
groupStates n (Group re) = groupStates n re
groupStates n Empty =  MkGroupSM [Nothing] [] n
groupStates n (Concat re1 re2) = 
  let (MkGroupSM init1 sWN1 n1) := groupStates n re1
      (MkGroupSM init2 sWN2 n2) := groupStates n1 re2
  in MkGroupSM  ((replaceEndInInit init1 init2) ++ init2)
                ((replaceEndInNext sWN1 init2)  ++ sWN2)  
                n2
groupStates n (Alt re1 re2) =
  let (MkGroupSM init1 sWN1 n1) := groupStates n re1
      (MkGroupSM init2 sWN2 n2) := groupStates n1 re2
  in MkGroupSM (init1 ++ init2) (sWN1 ++ sWN2) n2
groupStates n (Star re) = 
  let (MkGroupSM init sWN n') := groupStates n re
  in MkGroupSM (Nothing :: init) (replaceEndInNext sWN (Nothing :: init)) n'

min : GroupSM -> GroupSM
min (MkGroupSM initStates statesWithNext max) = ?min_rhs_0

public export
groupTransform : List (Maybe Nat) -> List (Maybe Nat, Routine)
groupTransform states = addEndRoutine [EmitString] (map (`MkPair` []) states)

public export
smFromGroupSMNext : List (Nat, NextStates) -> Nat -> Char -> List (Maybe Nat, Routine)
smFromGroupSMNext xs s c = groupTransform $
  case (find (\stns => fst stns == s) xs) of
    Nothing => []
    (Just (_, (MkNextStates condition isSat notSat))) => 
      (if (satisfies condition c) then isSat else notSat)

public export
smFromGroupSM : GroupSM -> SM
smFromGroupSM (MkGroupSM initStates statesWithNext max) = 
  MkSM  Nat 
        (mapRoutine (Record::) (groupTransform initStates))
        (smFromGroupSMNext statesWithNext)

public export
groupThompson : CoreRE -> SM
groupThompson re = smFromGroupSM (min (groupStates 0 re))