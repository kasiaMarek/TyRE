module NFA.Thompson

import Core
import NFA
import Data.List
import Data.Vect
import public Extra
import Extra.Reflects
import Data.List.Elem
import Data.List.Equalities

%default total

--State for Predicate
public export
data PState = StartState | AcceptState

Eq PState where
  StartState  == StartState   = True
  AcceptState == AcceptState  = True
  _           == _            = False

--When additional end accepting state needed
public export
data AState = ASt

Eq AState where
  _ == _ = True

public export
data CState a b = CTh1 a | CTh2 b | CEnd

public export
Eq a => Eq b => Eq (CState a b) where
  CTh1 x == CTh1 y = x == y
  CTh2 x == CTh2 y = x == y
  CEnd   == CEnd   = True
  x      == y      = False

export
Uninhabited (CTh1 e = CEnd) where
  uninhabited Refl impossible

export
Uninhabited (CTh2 e = CEnd) where
  uninhabited Refl impossible

export
Uninhabited (CTh1 e = CTh2 e') where
  uninhabited Refl impossible

export
Uninhabited (CTh2 e = CTh1 e') where
  uninhabited Refl impossible

public export
record SM where
  constructor MkSM
  nfa: NA
  prog: Program nfa

---functions for predicate
public export
nextNFAPred: (f : Char -> Bool) -> PState -> Char -> List PState
nextNFAPred f StartState   c = if (f c) then [AcceptState] else []
nextNFAPred f AcceptState  _ = []

public export
acceptingPred: PState -> Bool
acceptingPred AcceptState = True
acceptingPred StartState  = False

public export
nextPred  : (f : Char -> Bool) -> (st: PState) -> (c: Char)
          -> Vect (length (nextNFAPred f st c)) Routine
nextPred f StartState c with (f c)
  nextPred _ StartState _ | True = [[EmitLast]]
  nextPred _ StartState _ | False = []
nextPred _ AcceptState _ = []

--functions for Group
public export
nextGroup : (a -> Bool) -> (nextNFA: a -> Char -> List a)
    -> (Either a AState) -> Char
    -> (xs: List (Either a AState) ** Vect (length xs) Routine)

nextGroup accepting nextNFA (Left st) c =
  let mappedNext : List a
      mappedNext = nextNFA st c
  in case (findR accepting mappedNext).Holds of
        -- case `thompson re`.next has no accepting states, we maintain the next states and substitute the routine with an empty one
        Nothing => (map Left mappedNext **
                      replicate (length $ map Left mappedNext) [])
        -- case `thompson re`.next has an accepting state, we add `Right ASt` to next states
        Just _ => ((Right ASt)::(map Left mappedNext) **
                      [EmitString]::(replicate (length $ map Left mappedNext) []))

--if the state is `Right ASt` we accept and there is no next for it
nextGroup accepting nextNFA (Right ASt) _ = ([] ** [])

--functions for Concat and Alt
public export
acceptingConcat : (CState a b) -> Bool
acceptingConcat (CTh1 x) = False
acceptingConcat (CTh2 x) = False
acceptingConcat  CEnd = True

public export
record CombineTransitionData a b c where
  constructor MkCTD
  oldStates: List c
  rout1: Vect (length oldStates) Routine
  accept: c -> Bool
  conv: c -> (CState a b)
  newStart: List (CState a b)
  rout2: Vect (length newStart) Routine

public export
combineTransitionsAux  :
                          (oldStates: List c)
                      ->  (Vect (length oldStates) Routine)
                      ->  (c -> Bool)
                      ->  (c -> (CState a b))
                      ->  (newStart: List (CState a b))
                      ->  (Vect (length newStart) Routine)
                      ->  (states: List (CState a b) ** Vect (length states) Routine)
combineTransitionsAux [] []  _  _  _  _  = ([] ** [])
combineTransitionsAux (x :: xs) (y :: ys) accepting conv newStart newRoutines =
  let next : (states: List (CState a b) ** Vect (length states) Routine)
      next = combineTransitionsAux xs ys accepting conv newStart newRoutines
  in  if (accepting x)
      then ((conv x)::newStart ++ (fst next) **
              y::(replace
                    {p=(\l => Vect l Routine)}
                    (sym $ lengthDistributesOverAppend _ _)
                    ((map (y++) newRoutines) ++ (snd next))))
      else ((conv x)::(fst next) ** y::(snd next))

public export
combineTransitions  : CombineTransitionData a b c
                    -> (states: List (CState a b) ** Vect (length states) Routine)
combineTransitions (MkCTD oldStates rout1 accept conv newStart rout2) =
  combineTransitionsAux oldStates rout1 accept conv newStart rout2

public export
initTwo : (r : Routine) -> (sm2 : SM)
        -> (CombineTransitionData state1 sm2.nfa.State sm2.nfa.State)
initTwo r sm2 =
  MkCTD sm2.nfa.start sm2.prog.init sm2.nfa.accepting CTh2 [CEnd] [r]

public export
twoToEnd : (r : Routine) -> (sm2: SM) -> sm2.nfa.State -> Char
            -> (CombineTransitionData a sm2.nfa.State sm2.nfa.State)
twoToEnd r sm2 st c =
  MkCTD (sm2.nfa.next st c) (sm2.prog.next st c) sm2.nfa.accepting CTh2 [CEnd] [r]

public export
oneToEnd : (r : Routine) -> (sm1: SM) -> sm1.nfa.State -> Char
            -> (CombineTransitionData sm1.nfa.State a sm1.nfa.State)
oneToEnd r sm1 st c =
  MkCTD (sm1.nfa.next st c) (sm1.prog.next st c) sm1.nfa.accepting CTh1 [CEnd] [r]

--functions for Concat
public export
initTwoConcat : (sm2 : SM)
        -> (CombineTransitionData state1 sm2.nfa.State sm2.nfa.State)
initTwoConcat = initTwo [EmitPair]

public export
start2Cons : (sm2 : SM)
          -> (xs: List $ CState state1 sm2.nfa.State ** Vect (length xs) Routine)
start2Cons sm2 = combineTransitions (initTwoConcat sm2)

public export
concatInit : (sm1: SM) -> (sm2 : SM)
        -> (CombineTransitionData sm1.nfa.State sm2.nfa.State sm1.nfa.State)
concatInit sm1 sm2 =
  MkCTD sm1.nfa.start sm1.prog.init sm1.nfa.accepting CTh1 (fst (start2Cons sm2)) (snd (start2Cons sm2))

public export
oneToTwo : (sm1: SM) -> (sm2 : SM) -> sm1.nfa.State -> Char
            -> (CombineTransitionData sm1.nfa.State sm2.nfa.State sm1.nfa.State)
oneToTwo sm1 sm2 st c =
  MkCTD (sm1.nfa.next st c) (sm1.prog.next st c) sm1.nfa.accepting CTh1 (fst (start2Cons sm2)) (snd (start2Cons sm2))

public export
twoToEndConcat : (sm2: SM) -> sm2.nfa.State -> Char
            -> (CombineTransitionData a sm2.nfa.State sm2.nfa.State)
twoToEndConcat = twoToEnd [EmitPair]

public export
nextConcat : (sm1 : SM) -> (sm2 : SM)
          -> (CState sm1.nfa.State sm2.nfa.State) -> Char
          -> (xs: List (CState sm1.nfa.State sm2.nfa.State) ** Vect (length xs) Routine)

nextConcat sm1 sm2 (CTh1 st) c = combineTransitions $ oneToTwo sm1 sm2 st c
nextConcat sm1 sm2 (CTh2 st) c = combineTransitions $ twoToEndConcat sm2 st c
nextConcat sm1 sm2 CEnd      _ = ([] ** [])

--functions for alt
public export
initTwoAlt : (sm2 : SM)
        -> (CombineTransitionData state1 sm2.nfa.State sm2.nfa.State)
initTwoAlt = initTwo [EmitRight]

public export
initOneAlt : (sm1 : SM)
        -> (CombineTransitionData sm1.nfa.State state2 sm1.nfa.State)
initOneAlt sm1 =
  MkCTD sm1.nfa.start sm1.prog.init sm1.nfa.accepting CTh1 [CEnd] [[EmitLeft]]

public export
nextFromTwoAlt : (sm2: SM) -> sm2.nfa.State -> Char
            -> (CombineTransitionData a sm2.nfa.State sm2.nfa.State)
nextFromTwoAlt = twoToEnd [EmitRight]

public export
nextFromOneAlt : (sm1: SM) -> sm1.nfa.State -> Char
            -> (CombineTransitionData sm1.nfa.State a sm1.nfa.State)
nextFromOneAlt = oneToEnd [EmitLeft]

public export
nextAlt : (sm1 : SM) -> (sm2 : SM)
          -> (CState sm1.nfa.State sm2.nfa.State) -> Char
          -> (xs: List (CState sm1.nfa.State sm2.nfa.State) ** Vect (length xs) Routine)

nextAlt sm1 sm2 (CTh1 st) c = combineTransitions $ nextFromOneAlt sm1 st c
nextAlt sm1 sm2 (CTh2 st) c = combineTransitions $ nextFromTwoAlt sm2 st c
nextAlt sm1 sm2 CEnd      _ = ([] ** [])

--for Kleene Star
public export
acceptStar : (CState a a) -> Bool
acceptStar (CTh1 x) = False
acceptStar (CTh2 x) = False
acceptStar CEnd = True

public export
startStar : (sm : SM) -> List (CState sm.nfa.State sm.nfa.State)
startStar sm = CEnd::(map CTh2 sm.nfa.start)

public export
rStartStar : (sm : SM) -> Vect (length $ startStar sm) Routine
rStartStar sm = [EmitBList]::(replace {p=(\l => Vect l Routine)} (sym $ lengthMap _) sm.prog.init)

public export
initStar : (sm : SM) -> Vect (length $ startStar sm) Routine
initStar sm = map (EmitEList::) (rStartStar sm)

public export
nextStarData : (sm: SM) -> sm.nfa.State -> Char
            -> (CombineTransitionData sm.nfa.State sm.nfa.State sm.nfa.State)
nextStarData sm s c = MkCTD (sm.nfa.next s c) (sm.prog.next s c) sm.nfa.accepting CTh1 (startStar sm) (rStartStar sm)

public export
nextStar : (sm : SM)
    -> (CState sm.nfa.State sm.nfa.State) -> Char
    -> (xs: List (CState sm.nfa.State sm.nfa.State) ** Vect (length xs) Routine)
nextStar sm (CTh1 s) c = combineTransitions (nextStarData sm s c)
nextStar sm (CTh2 s) c = combineTransitions (nextStarData sm s c)
nextStar sm CEnd c = ([] ** [])

--Thompson construction
public export
thompson : CoreRE -> SM
thompson (Pred f) = MkSM (MkNFA PState acceptingPred [StartState]
                                (nextNFAPred f)) (MkProgram [[]] (nextPred f))

thompson (Empty) = MkSM (MkNFA AState (\_ => True) [ASt]
                                (\_,_ => [])) (MkProgram [[EmitUnit]] (\_,_ => []))
thompson (Group re) =
  let prev : SM
      prev = thompson re
      _ := prev.nfa.isEq

      0 state : Type
      state = Either prev.nfa.State AState

      accepting : state -> Bool
      accepting (Left _)             = False
      accepting (Right _)            = True

      start : List state
      start = map Left prev.nfa.start

      init: Vect (length start) Routine
      init = replicate (length start) [Record]

      next : state -> Char -> (xs: List state ** Vect (length xs) Routine)
      next st c = nextGroup prev.nfa.accepting prev.nfa.next st c

      nfa : NA
      nfa = MkNFA state accepting start (\st => \c => fst $ next st c)

      prog : Program nfa
      prog = MkProgram init (\st => \c => snd $ next st c)

  in MkSM nfa prog

thompson (Concat re1 re2) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      0 state : Type
      state = CState sm1.nfa.State sm2.nfa.State

      start : (xs: List state ** Vect (length xs) Routine)
      start = combineTransitions $ concatInit sm1 sm2

      next : state -> Char -> (xs: List state ** Vect (length xs) Routine)
      next = nextConcat sm1 sm2

      _ := sm1.nfa.isEq
      _ := sm2.nfa.isEq

      nfa : NA
      nfa = MkNFA state acceptingConcat (fst start) (\st => \c => fst (next st c))

      prog : Program nfa
      prog = MkProgram (snd start) (\st => \c => snd (next st c))

  in MkSM nfa prog

thompson (Alt re1 re2) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      0 state : Type
      state = CState sm1.nfa.State sm2.nfa.State

      _ := sm1.nfa.isEq
      _ := sm2.nfa.isEq

      start1 : (xs: List state ** Vect (length xs) Routine)
      start1 = combineTransitions $ initOneAlt sm1

      start2 : (xs: List state ** Vect (length xs) Routine)
      start2 = combineTransitions $ initTwoAlt sm2

      start : (xs: List state ** Vect (length xs) Routine)
      start = (fst start1 ++ fst start2 **
                replace {p=(\l => Vect l Routine)} (sym $ lengthDistributesOverAppend _ _)
                  (snd start1 ++ snd start2))

      next : state -> Char -> (xs: List state ** Vect (length xs) Routine)
      next = nextAlt sm1 sm2

      nfa : NA
      nfa = MkNFA state  acceptingConcat (fst start) (\st => \c => fst (next st c))

      prog : Program nfa
      prog = MkProgram (snd start) (\st => \c => snd (next st c))

  in MkSM nfa prog

thompson (Star re) =
  let sm : SM
      sm = thompson re
      _ := sm.nfa.isEq

      0 state : Type
      state = CState sm.nfa.State sm.nfa.State

      nfa : NA
      nfa = MkNFA state acceptStar (startStar sm) (\st => \c => fst (nextStar sm st c))

      prog : Program nfa
      prog = MkProgram (initStar sm) (\st => \c => snd (nextStar sm st c))

  in MkSM nfa prog
