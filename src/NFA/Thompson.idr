module NFA.Thompson

import Core
import NFA
import Data.List
import Data.Vect
import Data.Fin
import Syntax.PreorderReasoning
import Data.Nat

--Useful proofs
mapMaintainsLength: {a,b : Type} -> (xs: List a) -> (f: a -> b) -> (length xs = length (map f xs))
mapMaintainsLength [] f = Refl
mapMaintainsLength (x :: xs) f = cong (1+) (mapMaintainsLength xs f)

vectToList: Vect n a -> List a
vectToList [] = []
vectToList (x :: xs) = x :: (vectToList xs)

vectToListMaintainstLength: (v: Vect n a) -> (length (vectToList v) = n)
vectToListMaintainstLength [] = Refl
vectToListMaintainstLength (_ :: xs) = cong (S) (vectToListMaintainstLength xs)

lengthOfConcat : {xs, ys: List a} -> {xs', ys': List b} -> (length xs = length xs') -> (length ys = length ys') -> (length (xs ++ ys) = length (xs' ++ ys'))
lengthOfConcat {xs=[], ys} {xs'=[], ys'} prf prf1 = prf1
lengthOfConcat {xs=[], ys} {xs'=(x'::xss'), ys'} prf prf1 = absurd prf
lengthOfConcat {xs=(x::xss), ys} {xs'=[], ys'} prf prf1 = absurd prf
lengthOfConcat {xs=(x::xss), ys} {xs'=(x'::xss'), ys'} prf prf1 = cong S (lengthOfConcat (succInjective (length xss) (length xss') prf) prf1)

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

--Useful functions
nextList : (state -> List state') -> List state -> List state'
nextList nextMap [] = []
nextList nextMap (x :: xs) = (nextMap x) ++ (nextList nextMap xs)

nextListVM : ((state, Routine) -> List Routine) -> (xs: List state) -> (Vect (length xs) Routine) -> List Routine
nextListVM nextMapVM [] [] = []
nextListVM nextMapVM (x :: xs) (z :: ys) = (nextMapVM (x,z)) ++ (nextListVM nextMapVM xs ys)

--Proof of length equality of nextList and nextListVM given the same list of states
0 nextListPrf  : {nextMap : (state -> List state')}
        -> {nextMapVM : ((state, Routine) -> List Routine)}
        -> (xs: List state)
        -> (ys: Vect (length xs) Routine)
        -> (0 prf1 : (r: Routine) -> (s: state) -> (length (nextMapVM (s,r)) = length (nextMap s)))
        -> length (nextListVM nextMapVM xs ys) = length (nextList nextMap xs)
nextListPrf [] [] prf1 = Refl
nextListPrf (x :: xs) (z :: ys) prf1 = lengthOfConcat (prf1 z x) (nextListPrf xs ys prf1)

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

      nextMapLL : sm1.nfa.State -> List state
      nextMapLL st =
        let ns : state
            ns = (Left $ Left st)
            mappedStart : List state
            mappedStart = map (\s => Left $ Right s) sm2.nfa.start
        in if (sm1.nfa.accepting st) then ns::mappedStart else [ns]

      nextMapLR : sm2.nfa.State -> List state
      nextMapLR st = if (sm2.nfa.accepting st) then [Left $ Right st, Right EndState] else [Left $ Right st]

      next : state -> Char -> List state
      next (Left $ Left st) c = nextList nextMapLL (sm1.nfa.next st c)
      next (Left $ Right st) c = nextList nextMapLR (sm2.nfa.next st c)
      next (Right _) _ = []

      _ := sm1.nfa.isEq
      _ := sm2.nfa.isEq

      nfa : NA
      nfa = MkNFA state accepting start next

      init : Vect (length start) Routine
      init = replace {p=(\l => Vect l Routine)} (mapMaintainsLength _ _) sm1.prog.init

      nextMapVMLL : (sm1.nfa.State, Routine) -> List Routine
      nextMapVMLL (st, r) =
        let initRoutine : List Routine
            initRoutine = map (r++ ) $ vectToList sm2.prog.init
        in if (sm1.nfa.accepting st) then r::initRoutine else [r]

      nextMapVMLR : (sm2.nfa.State, Routine) -> List Routine
      nextMapVMLR (st,r) =
        if (sm2.nfa.accepting st)
        then
          if (recording)
          then [r,r]
          else [r, r ++ [EmitPair]]
        else [r]

      0 prf1 : (r : Routine) -> (st : sm1.nfa.State) -> (length (nextMapVMLL (st,r)) = length (nextMapLL st))
      prf1 r st with (sm1.nfa.accepting st)
        prf1 _ _ | False = Refl
        prf1 r st | True = cong (1+) $ Calc $
          |~ length (map (r ++) (vectToList sm2.prog.init))
          ~~ length (vectToList sm2.prog.init)                    ...(sym $ mapMaintainsLength _ _)
          ~~ length sm2.nfa.start                                 ...(vectToListMaintainstLength _)
          ~~ length (map (\s => Left (Right s)) sm2.nfa.start)    ...(mapMaintainsLength _ _)

      0 prf2 : (r : Routine) -> (st : sm2.nfa.State) -> (length (nextMapVMLR (st,r)) = length (nextMapLR st))
      prf2 _ st with (sm2.nfa.accepting st)
        prf2 _ _ | False = Refl
        prf2 _ _ | True with (recording)
          prf2 _ _ | True | False = Refl
          prf2 _ _ | True | True = Refl

      nextVM : (st : state) -> (c : Char) -> Vect (length $ next st c) Routine
      nextVM (Left $ Left st) c =
        let list : List Routine
            list = nextListVM nextMapVMLL (sm1.nfa.next st c) (sm1.prog.next st c)
        in replace {p= \l => Vect l Routine} (nextListPrf _ _ prf1) (fromList list)
      nextVM (Left $ Right st) c =
        let list : List Routine
            list = nextListVM nextMapVMLR (sm2.nfa.next st c) (sm2.prog.next st c)
        in replace {p= \l => Vect l Routine} (nextListPrf _ _ prf2) (fromList list)
      nextVM (Right _) _ = []

      prog : Program nfa
      prog = MkProgram init nextVM

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

      nextMap : prev.nfa.State -> List state
      nextMap st = if (prev.nfa.accepting st) then [Left st, Right EndState] else [Left st]

      nextMapVM : (prev.nfa.State, Routine) -> List Routine
      nextMapVM (st,r) = if (prev.nfa.accepting st) then [r,r ++ [EmitString]] else [r]

      --Proof of length equality of nextMap and nextMapVM given the same state
      0 prf1 : (r: Routine) -> (s: prev.nfa.State) -> (length (nextMapVM (s,r)) = length (nextMap s))
      prf1 _ s with (prev.nfa.accepting s)
        prf1 _ _ | True = Refl
        prf1 _ _ | False = Refl

      next : state -> Char -> List state
      next (Left x) c = nextList nextMap (prev.nfa.next x c)
      next (Right _) _ = []

      nextVM: (st : state) -> (c : Char) -> Vect (length (next st c)) Routine
      nextVM (Left  st) c =
        let list : List Routine
            list = nextListVM nextMapVM (prev.nfa.next st c) (prev.prog.next st c)
        in replace {p= \l => Vect l Routine} (nextListPrf _ _ prf1) (fromList list)
      nextVM (Right _) _  = []

      init: Vect (length start) Routine
      init = map (Record::) (replace {p = \l => (Vect l Routine)} (mapMaintainsLength prev.nfa.start Left) prev.prog.init)

      nfa : NA
      nfa = MkNFA state accepting start next

      prog : Program nfa
      prog = MkProgram init nextVM

  in if (recording) then prev else MkSM nfa prog
