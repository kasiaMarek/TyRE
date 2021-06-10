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

--State for Group
data GState = GAcceptState

Eq GState where
  GAcceptState == GAcceptState = True

--Functions for Predicate
nextPred: (Char -> Bool) -> PState -> Char -> List PState
nextPred f StartState    c   = if (f c) then [AcceptState] else []
nextPred f AcceptState   _   = []

acceptingPred: PState -> Bool
acceptingPred AcceptState = True
acceptingPred StartState  = False

--Functions for Group
acceptGroup : {0 state' : Type} -> (Either state' state') -> Bool
acceptGroup (Left _)             = False
acceptGroup (Right _)            = True

nextGroupMap : (state' -> Bool) -> state' -> List (Either state' state')
nextGroupMap f x = if (f x) then [Left x, Right x] else [Left x]

nextGroupList : (state' -> Bool) -> List state' -> List (Either state' state')
nextGroupList f [] = []
nextGroupList f (x :: xs) = (nextGroupMap f x) ++ (nextGroupList f xs)

nextGroup : {0 state' : Type} -> (state' -> Char -> List state') -> (state' -> Bool)
          -> (Either state' state') -> Char -> List (Either state' state')
nextGroup next' accept' (Left x) c = nextGroupList accept' (next' x c) -->>= (nextGroupMap accept')
nextGroup next' accept' (Right _) _ = []


|||Thompson construction for NFA
thompsonNFA: CoreRE -> NA
thompsonNFA (Pred f) = MkNFA PState acceptingPred [StartState] (nextPred f)
thompsonNFA (Concat x y) =
  let t1 = thompsonNFA x
      t2 = thompsonNFA y

      accepting: (Either t1.State t2.State) -> Bool
      accepting (Left  _) = False
      accepting (Right x) = t2.accepting x

      start: List (Either t1.State t2.State)
      start = map Left t1.start

      next : (Either t1.State t2.State) -> Char -> List (Either t1.State t2.State)
      next (Left  s) c =
        let t1Next = t1.next s c
        in case (find t1.accepting t1Next) of
              Nothing => (map Left t1Next)
              (Just _) => (map Left (filter t1.accepting t1Next)) ++ (map Right t2.start)
      next (Right s) c = (map Right (t2.next s c))

      _ := t1.isEq
      _ := t2.isEq

  in MkNFA (Either t1.State t2.State) accepting start next

thompsonNFA (Group x) =
  let prev: NA
      prev = thompsonNFA x
      _ := prev.isEq
  in MkNFA (Either prev.State prev.State) acceptGroup (map Left prev.start) (nextGroup prev.next prev.accepting)


record VMrec (re: CoreRE) where
  constructor MkVMrec
  prog: Program (thompsonNFA re)
  next: (st: (thompsonNFA re) .State) -> (c: Char) -> List (thompsonNFA re) .State
  0 nextPrf: next = (thompsonNFA re).next
  accepting: (thompsonNFA re) .State -> Bool
  0 acceptPrf: accepting = (thompsonNFA re).accepting

|||Thompson construction for Program
thompsonVM_rec  : (re: CoreRE) -> Bool -> VMrec re
thompsonVM_rec (Pred f) recording =
  let next : (st: PState) -> (c: Char) -> Vect (length (nextPred f st c)) Routine
      next StartState c with (f c)
        next StartState c | True = if (recording) then [[]] else [[EmitLast]]
        next StartState c | False = []
      next AcceptState c = []

      prog: Program (thompsonNFA (Pred f))
      prog = MkProgram [[]] next
  in MkVMrec prog (nextPred f) Refl acceptingPred Refl

thompsonVM_rec (Concat y z) recording = ?thompsonVM_rec_rhs_2

thompsonVM_rec (Group y) recording =
  let prev: VMrec y
      prev = thompsonVM_rec y True

      init: Vect (length (map Left (thompsonNFA y).start)) Routine
      init = map (Record::) (replace
                                {p = \r => (Vect r Routine)}
                                (mapMaintainsLength ((thompsonNFA y).start) Left)
                                prev.prog.init)

      0 p := (cong2 nextGroup prev.nextPrf prev.acceptPrf)

      nextNFA: (Either (thompsonNFA y).State (thompsonNFA y).State) -> Char -> List (Either (thompsonNFA y).State (thompsonNFA y).State)
      nextNFA = nextGroup prev.next prev.accepting

      f : ((thompsonNFA y).State, Routine) -> List Routine
      f (s,r) = if (prev.accepting s) then [r,r] else [r]

      0 prf1 : (r: Routine) -> (s: (thompsonNFA y).State) -> (length (f (s,r)) = length (nextGroupMap ((thompsonNFA y).accepting) s))
      prf1 r s with (prev.accepting s) proof p1
        prf1 r s | True  with (((thompsonNFA y).accepting) s) proof p2
          prf1 r s | True | True = Refl
          prf1 r s | True | False = absurd (trans (trans (sym p1) (cong (\f => f s) prev.acceptPrf)) p2)
        prf1 r s | False  with (((thompsonNFA y).accepting) s) proof p2
          prf1 r s | False | False = Refl
          prf1 r s | False | True = absurd (trans (trans (sym p1) (cong (\f => f s) prev.acceptPrf)) p2)

      fff : (xs: List ((thompsonNFA y).State)) -> (Vect (length xs) Routine) -> List Routine
      fff [] [] = []
      fff (x :: xs) (z :: ys) = (f (x,z)) ++ (fff xs ys)

      0 prf2  : (xs: List ((thompsonNFA y).State))
              -> (ys: Vect (length xs) Routine)
              -> length (nextGroupList ((thompsonNFA y).accepting) xs) = length (fff xs ys)
      prf2 [] [] = Refl
      prf2 (x :: xs) (z :: ys) = lengthOfConcat (sym (prf1 z x)) (prf2 xs ys)

      next: (st : (thompsonNFA (Group y)).State) -> (c : Char) -> Vect (length ((thompsonNFA (Group y)).next st c)) Routine
      next (Left  st) c =
        let v = (replace {p = \m => Vect (length (m st c)) Routine} (sym prev.nextPrf) (prev.prog.next st c))
            0 l = prf2 (prev.next st c) v
            0 w = cong (\f => length (nextGroupList (.accepting (thompsonNFA y)) (f st c))) prev.nextPrf
        in replace {p= \l => Vect l Routine} (trans (sym l) w) (fromList (fff (prev.next st c) v))
      next (Right _) _  = []

      prog: Program (thompsonNFA (Group y))
      prog = MkProgram init next

  in MkVMrec prog nextNFA p acceptGroup Refl

thompsonVM: (re: CoreRE) -> Program (thompsonNFA re)
