module TyRE.Parser.GroupThompson

import Data.List
import Data.List1
import Data.SortedSet

import TyRE.Core

%default total

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

filterNothing : List (Maybe Nat) -> List (Maybe Nat)
filterNothing xs = filter (/= Nothing) xs

replaceEndInInit : List (Maybe Nat) -> List (Maybe Nat) -> List (Maybe Nat)
replaceEndInInit xs mks =
  case (find (== Nothing) xs) of
    Nothing => xs
    Just _ => mks ++ (filterNothing xs)

replaceEndInNext : List (Nat, NextStates) -> List (Maybe Nat)
                -> List (Nat, NextStates)
replaceEndInNext [] mks = []
replaceEndInNext ((n, (MkNextStates condition isSat notSat)) :: xs) mks = 
  (n, (MkNextStates condition (replaceEndInInit isSat mks) (replaceEndInInit notSat mks))) :: (replaceEndInNext xs mks)

groupStates : Nat -> TyRE a -> GroupSM
groupStates n (MatchChar cond) = 
  MkGroupSM [Just n] [(n, MkNextStates cond [Nothing] [])] (n+1)
groupStates n (Group re) = groupStates n re
groupStates n Empty =  MkGroupSM [Nothing] [] n
groupStates n (re1 <*> re2) = 
  let (MkGroupSM init1 sWN1 n1) := groupStates n re1
      (MkGroupSM init2 sWN2 n2) := groupStates n1 re2
  in MkGroupSM  (replaceEndInInit init1 init2)
                ((replaceEndInNext sWN1 init2)  ++ sWN2)  
                n2
groupStates n (re1 <|> re2) =
  let (MkGroupSM init1 sWN1 n1) := groupStates n re1
      (MkGroupSM init2 sWN2 n2) := groupStates n1 re2
  in MkGroupSM (init1 ++ init2) (sWN1 ++ sWN2) n2
groupStates n (Rep re) = 
  let (MkGroupSM init sWN n') := groupStates n re
  in MkGroupSM (Nothing :: init) (replaceEndInNext sWN (Nothing :: init)) n'
groupStates n (Conv re f) = groupStates n re

eq : List (Maybe Nat) -> List (Maybe Nat) -> Bool
eq mks mjs = (Data.SortedSet.fromList mks) == (fromList mjs)

min : GroupSM -> GroupSM
min (MkGroupSM initStates statesWithNext max) =
  let (initStates', statesWithNext') := go (length statesWithNext) (initStates, statesWithNext)
  in MkGroupSM initStates' statesWithNext' max where
  go : Nat -> (List (Maybe Nat), List (Nat, NextStates)) -> (List (Maybe Nat), List (Nat, NextStates))
  go 0 xs = xs
  go (S k) (init, xs) = 
    let mappings := getMappings (group xs)
    in if (length mappings == 0) then (init, xs) else go k (squash mappings (init, xs)) where
    group : List (Nat, NextStates) -> List (List1 (Nat, NextStates))
    group xs = groupBy stateEq xs where
      stateEq : (Nat, NextStates) -> (Nat, NextStates) -> Bool
      stateEq (_, (MkNextStates cond  isSat   notSat  )) 
              (_, (MkNextStates cond' isSat'  notSat' )) =
                cond == cond' && (eq isSat isSat') && (eq notSat notSat')
    getMappings : List (List1 (Nat, NextStates)) -> List (Nat, Nat)
    getMappings [] = []
    getMappings (((nh, _) ::: xs) :: ys) = (map (\case (x, _) => (nh, x)) xs) ++ getMappings ys
    applyFilter : (Nat, Nat) -> List (Maybe Nat) -> List (Maybe Nat)
    applyFilter (n, n1) xs = 
      case (find (== Just n1) xs) of
        Nothing => xs
        (Just y) => (Just n) :: filter (\x => not (x == Just n || x == Just n1)) xs
    squash : List (Nat, Nat) -> (List (Maybe Nat), List (Nat, NextStates)) -> (List (Maybe Nat), List (Nat, NextStates))
    squash [] x = x
    squash ((n, n1) :: xs) (init, ys) = 
      squash xs 
            ( filter (\x => x /= (Just n1)) init
            , applyMap ys) where
            applyMap : List (Nat, NextStates) -> List (Nat, NextStates)
            applyMap [] = []
            applyMap ((n', y) :: xs) = 
              if (n' == n1) then applyMap xs
              else  ( n'
                    , MkNextStates  y.condition 
                                    (applyFilter (n, n1) y.isSat) 
                                    (applyFilter (n, n1) y.notSat)) :: applyMap xs

public export
groupSM : TyRE a -> GroupSM
groupSM re = min (groupStates 0 re)