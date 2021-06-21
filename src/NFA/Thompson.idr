module NFA.Thompson

import Core
import NFA
import Data.List
import Data.Vect
import Extra
import Extra.Reflects
import Data.List.Elem

--State for Predicate
public export
data PState = StartState | AcceptState

Eq PState where
  StartState  == StartState   = True
  AcceptState == AcceptState  = True
  _           == _            = False

--When additional end accepting state needed
public export
data AState = EndState

Eq AState where
  EndState == EndState = True

public export
data CState a b = CTh1 a | CTh2 b | CEnd

public export
Eq a => Eq b => Eq (CState a b) where
  CTh1 x == CTh1 y = x == y
  CTh2 x == CTh2 y = x == y
  CEnd   == CEnd   = True
  x      == y      = False

public export
flatMap : (f: (a,b) -> (xs' : List c ** Vect (length xs') d)) -> (xs : List a) -> (Vect (length xs) b) -> (ys: List c ** Vect (length ys) d)
flatMap f [] [] = ([] ** [])
flatMap {c,d} f (x :: xs) (y :: ys) =
  let head : (xs' : List c ** Vect (length xs') d)
      head = f (x,y)
      tail : (xs' : List c ** Vect (length xs') d)
      tail = flatMap f xs ys
  in  (fst head ++ (fst tail) ** (replace {p = \l => Vect l d} (lengthOfConcatIsPlus _ _)  (snd head ++ (snd tail))))

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
nextPred : (f : Char -> Bool) -> (st: PState) -> (c: Char) -> Vect (length (nextNFAPred f st c)) Routine
nextPred f StartState c with (f c)
  nextPred _ StartState _ | True = [[EmitLast]]
  nextPred _ StartState _ | False = []
nextPred _ AcceptState _ = []

--functions for Group
public export
nextGroup : (a -> Bool) -> (nextNFA: a -> Char -> List a)
    -> (Either a AState) -> Char -> (xs: List (Either a AState) ** Vect (length xs) Routine)
nextGroup accepting nextNFA (Left st) c =
  let mappedNext : List a
      mappedNext = nextNFA st c
  in case (findR accepting mappedNext).Holds of
        Nothing => (map Left mappedNext ** replicate (length $ map Left mappedNext) [])
        (Just _) => ((Right EndState)::(map Left mappedNext) ** [EmitString]::(replicate (length $ map Left mappedNext) []))
nextGroup accepting nextNFA (Right EndState) _ = ([] ** [])

--functions for Concat
acceptingConcat : (CState a b) -> Bool
acceptingConcat (CTh1 x) = False
acceptingConcat (CTh2 x) = False
acceptingConcat  CEnd = True

forAcceptingAddNewStart : (oldStates: List c) -> (Vect (length oldStates) Routine) -> (accepting: c -> Bool) -> (conv: c -> (CState a b))
                        -> (newStart: List (CState a b)) -> (Vect (length newStart) Routine)
                        -> (states: List (CState a b) ** Vect (length states) Routine)

forAcceptingAddNewStart [] [] accepting conv newStart ys = ([] ** [])
forAcceptingAddNewStart (x :: xs) (y :: ys) accepting conv newStart newRoutines =
  let next : (states: List (CState a b) ** Vect (length states) Routine)
      next = forAcceptingAddNewStart xs ys accepting conv newStart newRoutines
      withElem : (states: List (CState a b) ** Vect (length states) Routine)
      withElem = ((conv x)::(fst next) ** y::(snd next))
  in  if (accepting x)
      then (newStart ++ (fst withElem) ** replace {p=(\l => Vect l Routine)} (lengthOfConcatIsPlus _ _) ((map (y++) newRoutines) ++ (snd withElem)))
      else withElem

nextConcat : (next1: a -> Char -> List a) -> ((st: a) -> (c: Char) -> Vect (length $ next1 st c) Routine) -> (acc1: a -> Bool)
            -> (next2: b -> Char -> List b) -> ((st: b) -> (c: Char) -> Vect (length $ next2 st c) Routine) -> (acc2: b -> Bool)
            -> (xs: List (CState a b) ** Vect (length xs) Routine)
            -> (CState a b) -> Char -> (xs: List (CState a b) ** Vect (length xs) Routine)

nextConcat next1 nextVM1 acc1 next2 nextVM2 acc2 start2 (CTh1 st) c = forAcceptingAddNewStart (next1 st c) (nextVM1 st c) acc1 CTh1 (fst start2) (snd start2)
nextConcat _     nextVM1 acc1 next2 nextVM2 acc2 start2 (CTh2 st) c = forAcceptingAddNewStart (next2 st c) (nextVM2 st c) acc2 CTh2 [CEnd] [[EmitPair]]
nextConcat next1 nextVM1 acc1 next2 nextVM2 acc2 start2 CEnd _ = ([] ** [])

--Thompson construction
public export
thompson : CoreRE -> SM
thompson (Pred f) = MkSM (MkNFA PState acceptingPred [StartState] (nextNFAPred f)) (MkProgram [[]] (nextPred f))

thompson (Concat re1 re2) =
  let sm1 : SM
      sm1 = thompson re1
      sm2 : SM
      sm2 = thompson re2

      0 state : Type
      state = CState sm1.nfa.State sm2.nfa.State

      start2 : (xs: List state ** Vect (length xs) Routine)
      start2 = forAcceptingAddNewStart sm2.nfa.start sm2.prog.init sm2.nfa.accepting CTh2 [CEnd] [[EmitPair]]

      start : (xs: List state ** Vect (length xs) Routine)
      start = forAcceptingAddNewStart sm1.nfa.start sm1.prog.init sm1.nfa.accepting CTh1 (fst start2) (snd start2)

      next : state -> Char -> (xs: List state ** Vect (length xs) Routine)
      next = nextConcat sm1.nfa.next sm1.prog.next sm1.nfa.accepting sm2.nfa.next sm2.prog.next sm2.nfa.accepting start2

      _ := sm1.nfa.isEq
      _ := sm2.nfa.isEq

      nfa : NA
      nfa = MkNFA state acceptingConcat (fst start) (\st => \c => fst (next st c))

      prog : Program nfa
      prog = MkProgram (snd start) (\st => \c => snd (next st c))

  in MkSM nfa prog

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

      nfa : NA
      nfa = MkNFA state accepting start (\st => \c => fst $ nextGroup prev.nfa.accepting prev.nfa.next st c)

      prog : Program nfa
      prog = MkProgram init (\st => \c => snd $ nextGroup prev.nfa.accepting prev.nfa.next st c)

  in MkSM nfa prog
