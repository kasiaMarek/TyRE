module NFA.Thompson

import Core
import NFA
import Data.List
import Data.Vect

--Useful proofs
mapMaintainsLength: {a,b : Type} -> (xs: List a) -> (f: a -> b) -> (length xs = length (map f xs))
mapMaintainsLength [] f = Refl
mapMaintainsLength (x :: xs) f = cong (1+) (mapMaintainsLength xs f)

lengthOfConcatIsPlus : (xs: List a) -> (ys: List a) -> (length xs + length ys = length (xs ++ ys))
lengthOfConcatIsPlus [] ys = Refl
lengthOfConcatIsPlus (x :: xs) ys = cong (1+) (lengthOfConcatIsPlus xs ys)

--State for Predicate
data PState = StartState | AcceptState

Eq PState where
  StartState  == StartState   = True
  AcceptState == AcceptState  = True
  _           == _            = False

--When additional end accepting state needed
data AState = EndState

Eq AState where
  EndState == EndState = True

flatMap : (f: (a,b) -> (xs' : List c ** Vect (length xs') d)) -> (xs : List a) -> (Vect (length xs) b) -> (ys: List c ** Vect (length ys) d)
flatMap f [] [] = ([] ** [])
flatMap {c,d} f (x :: xs) (y :: ys) =
  let head : (xs' : List c ** Vect (length xs') d)
      head = f (x,y)
      tail : (xs' : List c ** Vect (length xs') d)
      tail = flatMap f xs ys
  in  (fst head ++ (fst tail) ** (replace {p = \l => Vect l d} (lengthOfConcatIsPlus _ _)  (snd head ++ (snd tail))))

record SM where
  constructor MkSM
  nfa: NA
  prog: Program nfa

thompson : CoreRE -> Bool -> SM
thompson (Pred f) recording =
  let nextNFA: PState -> Char -> List PState
      nextNFA StartState    c   = if (f c) then [AcceptState] else []
      nextNFA AcceptState   _   = []

      accepting: PState -> Bool
      accepting AcceptState = True
      accepting StartState  = False

      next : (st: PState) -> (c: Char) -> Vect (length (nextNFA st c)) Routine
      next StartState c with (f c)
        next StartState c | True = if (recording) then [[]] else [[EmitLast]]
        next StartState c | False = []
      next AcceptState c = []

      nfa : NA
      nfa = MkNFA PState accepting [StartState] nextNFA

      prog: Program nfa
      prog = MkProgram [[]] next
  in MkSM nfa prog

thompson (Concat re1 re2) recording =
  let sm1 : SM
      sm1 = thompson re1 recording
      sm2 : SM
      sm2 = thompson re2 recording

      0 state : Type
      state = Either (Either sm1.nfa.State sm2.nfa.State) AState

      accepting : state -> Bool
      accepting (Left  _) = False
      accepting (Right _) = True

      start : List state
      start = map (\s => Left (Left s)) sm1.nfa.start

      nextMapLL : (sm1.nfa.State, Routine) -> (xs: List state ** Vect (length xs) Routine)
      nextMapLL (st,r) =
        let ns : state
            ns = (Left $ Left st)
            mappedStart : List state
            mappedStart = map (\s => Left $ Right s) sm2.nfa.start
            initRoutine : Vect (length mappedStart) Routine
            initRoutine = replace {p=(\l => Vect l Routine)} (mapMaintainsLength _ _) $ map (r++ ) sm2.prog.init
        in if (sm1.nfa.accepting st) then (ns::mappedStart ** r::initRoutine) else ([ns] ** [r])

      nextMapLR : (sm2.nfa.State, Routine)-> (xs: List state ** Vect (length xs) Routine)
      nextMapLR (st,r) =
        if (sm2.nfa.accepting st)
        then
          if (recording)
          then ([Left $ Right st, Right EndState] ** [r,r])
          else ([Left $ Right st, Right EndState] ** [r,r ++ [EmitPair]])
        else ([Left $ Right st] ** [r])

      next : state -> Char -> (xs: List state ** Vect (length xs) Routine)
      next (Left $ Left st) c = flatMap nextMapLL (sm1.nfa.next st c) (sm1.prog.next st c)
      next (Left $ Right st) c = flatMap nextMapLR (sm2.nfa.next st c) (sm2.prog.next st c)
      next (Right _) _ = ([] ** [])

      _ := sm1.nfa.isEq
      _ := sm2.nfa.isEq

      nfa : NA
      nfa = MkNFA state accepting start (\st => \c => fst $ next st c)

      init : Vect (length start) Routine
      init = replace {p=(\l => Vect l Routine)} (mapMaintainsLength _ _) sm1.prog.init

      prog : Program nfa
      prog = MkProgram init (\st => \c => snd $ next st c)

  in MkSM nfa prog

thompson (Group re) recording =
  let prev : SM
      prev = thompson re True
      _ := prev.nfa.isEq

      0 state : Type
      state = Either prev.nfa.State AState

      accepting : state -> Bool
      accepting (Left _)             = False
      accepting (Right _)            = True

      start : List state
      start = map Left prev.nfa.start

      nextMap : (prev.nfa.State, Routine) -> (xs: List state ** Vect (length xs) Routine)
      nextMap (st,r) =
        if (prev.nfa.accepting st)
        then ([Left st, Right EndState] ** [r,r ++ [EmitString]])
        else ([Left st] ** [r])

      next : state -> Char -> (xs: List state ** Vect (length xs) Routine)
      next (Left st) c = flatMap nextMap (prev.nfa.next st c) (prev.prog.next st c)
      next (Right _) _ = ([] ** [])

      init: Vect (length start) Routine
      init = map (Record::) (replace {p = \l => (Vect l Routine)} (mapMaintainsLength prev.nfa.start Left) prev.prog.init)

      nfa : NA
      nfa = MkNFA state accepting start (\st => \c => fst $ next st c)

      prog : Program nfa
      prog = MkProgram init (\st => \c => snd $ next st c)

  in if (recording) then prev else MkSM nfa prog
