module NewThompson

import Core
import NFA
import Data.List
import Data.Vect
import public Extra
import Extra.Reflects
import Data.List.Elem
import Data.List.Equalities
import NFA.Thompson

%default total

public export
record NewSM where
  constructor MkNewSM
  0 State : Type
  {auto isEq : Eq State}
  accepting : State -> Bool
  start : List (State, Routine)
  next : State -> Char -> List (State, Routine)

---functions for predicate
public export
newNextPred  : (f : Char -> Bool) -> (st: PState) -> (c: Char)
          -> List (PState, Routine)
newNextPred f StartState c = if (f c) then [(AcceptState, [EmitLast])] else []
newNextPred _ AcceptState _ = []

--functions for Group
public export
newNextGroup : (sm : NewSM) -> (Either sm.State AState) -> Char
    -> List (Either sm.State AState, Routine)

newNextGroup sm (Left st) c =
  let mappedNext  : List sm.State
                  := map fst (sm.next st c)
  in case (findR sm.accepting mappedNext).Holds of
        -- case `newThompson re`.next has no accepting states, we maintain the next states and substitute the routine with an empty one
        Nothing => map (\st => (Left st, [])) mappedNext
        -- case `newThompson re`.next has an accepting state, we add `Right ASt` to next states
        Just _ => (Right ASt, [EmitString]) :: map (\st => (Left st, [])) mappedNext

--if the state is `Right ASt` we accept and there is no next for it
newNextGroup _ (Right ASt) _ = []

--functions for Concat and Alt
public export
record NewCombineTransitionData a b c where
  constructor MkNewCTD
  oldStates : List (c, Routine)
  accept : c -> Bool
  conv : c -> (CState a b)
  newStart : List ((CState a b), Routine)

public export
newCombineTransitionsAux  : (oldStates : List (c, Routine))
                      ->  (c -> Bool)
                      ->  (c -> (CState a b))
                      ->  (newStates : List (CState a b, Routine))
                      ->  List ((CState a b), Routine)
newCombineTransitionsAux [] _  _  _  = []
newCombineTransitionsAux ((x,y) :: xs) accepting conv newStart =
    if (accepting x)
    then (conv x, y) :: ((map (\case(st, r) => (st, y ++ r)) newStart) ++ (newCombineTransitionsAux xs accepting conv newStart))
    else (conv x, y) :: (newCombineTransitionsAux xs accepting conv newStart)

public export
newCombineTransitions  : NewCombineTransitionData a b c
                    -> List ((CState a b), Routine)
newCombineTransitions (MkNewCTD oldStates accept conv newStart) =
  newCombineTransitionsAux oldStates accept conv newStart

public export
newInitTwo : (r : Routine) -> (sm2 : NewSM)
        -> (NewCombineTransitionData state1 sm2.State sm2.State)
newInitTwo r sm2 =
  MkNewCTD sm2.start sm2.accepting CTh2 [(CEnd, r)]

public export
newTwoToEnd : (r : Routine) -> (sm2: NewSM) -> sm2.State -> Char
            -> (NewCombineTransitionData a sm2.State sm2.State)
newTwoToEnd r sm2 st c =
  MkNewCTD (sm2.next st c) sm2.accepting CTh2 [(CEnd, r)]

public export
newOneToEnd : (r : Routine) -> (sm1: NewSM) -> sm1.State -> Char
            -> (NewCombineTransitionData sm1.State a sm1.State)
newOneToEnd r sm1 st c =
  MkNewCTD (sm1.next st c) sm1.accepting CTh1 [(CEnd, r)]

--functions for Concat
public export
newInitTwoConcat : (sm2 : NewSM)
        -> (NewCombineTransitionData state1 sm2.State sm2.State)
newInitTwoConcat = newInitTwo [EmitPair]

public export
newStart2Cons : (sm2 : NewSM) -> List (CState state1 sm2.State, Routine)
newStart2Cons sm2 = newCombineTransitions (newInitTwoConcat sm2)

public export
newConcatInit : (sm1: NewSM) -> (sm2 : NewSM)
        -> (NewCombineTransitionData sm1.State sm2.State sm1.State)
newConcatInit sm1 sm2 =
  MkNewCTD sm1.start sm1.accepting CTh1 (newStart2Cons sm2)

public export
newOneToTwo : (sm1: NewSM) -> (sm2 : NewSM) -> sm1.State -> Char
            -> (NewCombineTransitionData sm1.State sm2.State sm1.State)
newOneToTwo sm1 sm2 st c =
  MkNewCTD (sm1.next st c) sm1.accepting CTh1 (newStart2Cons sm2)

public export
newTwoToEndConcat : (sm2: NewSM) -> sm2.State -> Char
            -> (NewCombineTransitionData a sm2.State sm2.State)
newTwoToEndConcat = newTwoToEnd [EmitPair]

public export
newNextConcat : (sm1 : NewSM) -> (sm2 : NewSM)
          -> (CState sm1.State sm2.State) -> Char
          -> List (CState sm1.State sm2.State, Routine)

newNextConcat sm1 sm2 (CTh1 st) c = newCombineTransitions $ newOneToTwo sm1 sm2 st c
newNextConcat sm1 sm2 (CTh2 st) c = newCombineTransitions $ newTwoToEndConcat sm2 st c
newNextConcat sm1 sm2 CEnd      _ = []

--functions for alt
public export
newInitTwoAlt : (sm2 : NewSM)
        -> (NewCombineTransitionData state1 sm2.State sm2.State)
newInitTwoAlt = newInitTwo [EmitRight]

public export
newInitOneAlt : (sm1 : NewSM)
        -> (NewCombineTransitionData sm1.State state2 sm1.State)
newInitOneAlt sm1 =
  MkNewCTD sm1.start sm1.accepting CTh1 [(CEnd, [EmitLeft])]

public export
nextFromTwoAlt : (sm2: NewSM) -> sm2.State -> Char
            -> (NewCombineTransitionData a sm2.State sm2.State)
nextFromTwoAlt = newTwoToEnd [EmitRight]

public export
nextFromOneAlt : (sm1: NewSM) -> sm1.State -> Char
            -> (NewCombineTransitionData sm1.State a sm1.State)
nextFromOneAlt = newOneToEnd [EmitLeft]

public export
newNextAlt : (sm1 : NewSM) -> (sm2 : NewSM)
          -> (CState sm1.State sm2.State) -> Char
          -> List (CState sm1.State sm2.State, Routine)

newNextAlt sm1 sm2 (CTh1 st) c = newCombineTransitions $ nextFromOneAlt sm1 st c
newNextAlt sm1 sm2 (CTh2 st) c = newCombineTransitions $ nextFromTwoAlt sm2 st c
newNextAlt sm1 sm2 CEnd      _ = []

--for Kleene Star
public export
newStarNext : (sm : NewSM) -> List (CState sm.State sm.State, Routine)
newStarNext sm = (CEnd, [EmitBList]) :: (map (\case (st, r) => (CTh2 st, r)) sm.start)

public export
newStarStart : (sm : NewSM) -> List (CState sm.State sm.State, Routine)
newStarStart sm = (map (\case (st, r) => (st, EmitEList :: r)) (newStarNext sm))

public export
newNextStarData : (sm: NewSM) -> sm.State -> Char
            -> (NewCombineTransitionData sm.State sm.State sm.State)
newNextStarData sm s c = MkNewCTD (sm.next s c) sm.accepting CTh1 (newStarNext sm)

public export
newNextStar : (sm : NewSM)
    -> (CState sm.State sm.State) -> Char
    -> List (CState sm.State sm.State, Routine)
newNextStar sm (CTh1 s) c = newCombineTransitions (newNextStarData sm s c)
newNextStar sm (CTh2 s) c = newCombineTransitions (newNextStarData sm s c)
newNextStar sm CEnd c = []

--Thompson construction
public export
newThompson : CoreRE -> NewSM
newThompson (Pred f) = MkNewSM PState acceptingPred [(StartState, [])] (newNextPred f)

newThompson (Empty) = MkNewSM AState (\st => True) [(ASt, [EmitUnit])] (\_,_ => [])
newThompson (Group re) =
  let prev : NewSM := newThompson re
      _ := prev.isEq

      0 state : Type
      state = Either prev.State AState

      accepting : state -> Bool
      accepting (Left _)             = False
      accepting (Right _)            = True

  in MkNewSM state accepting (map (\case (st, r) => (Left st, r)) prev.start) (newNextGroup prev)

newThompson (Concat re1 re2) =
  let sm1 : NewSM := newThompson re1
      sm2 : NewSM := newThompson re2

      0 state : Type
      state = CState sm1.State sm2.State

      _ := sm1.isEq
      _ := sm2.isEq

  in MkNewSM state acceptingConcat (newCombineTransitions $ newConcatInit sm1 sm2) (newNextConcat sm1 sm2)

newThompson (Alt re1 re2) =
  let sm1 : NewSM := newThompson re1
      sm2 : NewSM := newThompson re2

      0 state : Type
      state = CState sm1.State sm2.State

      _ := sm1.isEq
      _ := sm2.isEq

  in MkNewSM state acceptingConcat (newCombineTransitions (newInitOneAlt sm1) ++ newCombineTransitions (newInitTwoAlt sm2)) (newNextAlt sm1 sm2)

newThompson (Star re) =
  let sm : NewSM := newThompson re
      _ := sm.isEq

      0 state : Type
      state = CState sm.State sm.State

  in MkNewSM state acceptStar (newStarStart sm) (newNextStar sm)
