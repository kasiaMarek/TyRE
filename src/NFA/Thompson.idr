module NFA.Thompson

import Core
import NFA
import Data.List
import Data.Vect
import Extra
import Extra.Reflects

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

--Thompson's construction
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

      accepting : state -> Bool
      accepting (CTh1 x) = False
      accepting (CTh2 x) = False
      accepting CEnd = True

      start : List state
      start = map CTh1 sm1.nfa.start

      nextMapLL : (sm1.nfa.State, Routine) -> (xs: List state ** Vect (length xs) Routine)
      nextMapLL (st,r) =
        let ns : state
            ns = CTh1 st
            mappedStart : List state
            mappedStart = map CTh2 sm2.nfa.start
            initRoutine : Vect (length mappedStart) Routine
            initRoutine = replace {p=(\l => Vect l Routine)} (mapMaintainsLength _ _) $ map (r++ ) sm2.prog.init
        in if (sm1.nfa.accepting st) then (ns::mappedStart ** r::initRoutine) else ([ns] ** [r])

      nextMapLR : (sm2.nfa.State, Routine)-> (xs: List state ** Vect (length xs) Routine)
      nextMapLR (st,r) =
        if (sm2.nfa.accepting st)
        then ([CTh2 st, CEnd] ** [r,r ++ [EmitPair]])
        else ([CTh2 st] ** [r])

      next : state -> Char -> (xs: List state ** Vect (length xs) Routine)
      next (CTh1 st) c = flatMap nextMapLL (sm1.nfa.next st c) (sm1.prog.next st c)
      next (CTh2 st) c = flatMap nextMapLR (sm2.nfa.next st c) (sm2.prog.next st c)
      next CEnd _ = ([] ** [])

      _ := sm1.nfa.isEq
      _ := sm2.nfa.isEq

      nfa : NA
      nfa = MkNFA state accepting start (\st => \c => fst $ next st c)

      init : Vect (length start) Routine
      init = replace {p=(\l => Vect l Routine)} (mapMaintainsLength _ _) sm1.prog.init

      prog : Program nfa
      prog = MkProgram init (\st => \c => snd $ next st c)

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
