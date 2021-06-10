module NFA.Thompson

import Core
import NFA
import Data.List
import Data.Vect
import Data.Fin

--Useful proofs
mapMaintainsLength: {a,b : Type} -> (xs: List a) -> (f: a -> b) -> (length xs = length (map f xs))
mapMaintainsLength [] f = Refl
mapMaintainsLength (x :: xs) f = cong (1+) (mapMaintainsLength xs f)

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
acceptGroup : {0 state' : Type} -> (Either state' GState) -> Bool
acceptGroup (Left x)             = False
acceptGroup (Right GAcceptState) = True

nextGroup : {0 state' : Type} -> (state' -> Char -> List state') -> (state' -> Bool)
          -> (Either state' GState) -> Char -> List (Either state' GState)
nextGroup next' accept' (Left x)             c =
  let n : List state'
      n = next' x c
  in case (find accept' n) of
      (Just _) => (Right GAcceptState)::(map Left n)
      Nothing  => map Left n
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
  in MkNFA (Either prev.State GState) acceptGroup (map Left prev.start) (nextGroup prev.next prev.accepting)


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
      --(\st => \c => Refl)
  in MkVMrec prog (nextPred f) Refl acceptingPred Refl

thompsonVM_rec (Concat y z) recording = ?thompsonVM_rec_rhs_2

thompsonVM_rec (Group y) recording =
  let prev = thompsonVM_rec y True

      init: Vect (length (map Left (thompsonNFA y).start)) Routine
      init = map (Record::) (replace
                                {p = \r => (Vect r Routine)}
                                (mapMaintainsLength ((thompsonNFA y).start) Left)
                                prev.prog.init)

      0 p := (cong2 nextGroup prev.nextPrf prev.acceptPrf)
      nextNFA: (Either (thompsonNFA y).State GState) -> Char -> List (Either (thompsonNFA y).State GState)
      nextNFA = nextGroup prev.next prev.accepting

      n: (st:(Either (thompsonNFA y).State GState)) -> (c: Char) -> Vect (length ((thompsonNFA (Group y)).next st c)) (Either (thompsonNFA y).State GState)
      n st c = replace {p = \l => Vect l (Either (thompsonNFA y).State GState)} (cong (\e => length (e st c)) p) (fromList (nextNFA st c))
      --0 prf: Vect (length (case find (.accepting (thompsonNFA y)) (.next (thompsonNFA y) x c) of {Just _ => Right GAcceptState :: map Left (n state' x c accept' next'); Nothing => map Left (n state' x c accept' next')})) (List Instruction)
      ---ppr: (st: )
      next: (st : (thompsonNFA (Group y)).State) -> (c : Char) -> Vect (length ((thompsonNFA (Group y)).next st c)) Routine
      -- nextGroup : {0 state' : Type} -> (state' -> Char -> List state') -> (state' -> Bool)
      --           -> (Either state' GState) -> Char -> List (Either state' GState)
      -- nextGroup next' accept' (Left x)             c =
      --   let n : List state'
      --       n = next' x c
      --   in case (find accept' n) of
      --       (Just _) => (Right GAcceptState)::(map Left n)
      --       Nothing  => map Left n
      -- nextGroup next' accept' (Right _) _ = []
      next (Left  x) c =
        let m := case (find (prev.accepting) (prev.next x c)) of
                    Nothing => ?l
                    (Just x) => ::(prev.prog x c)
        in ?hole
      --   let pp = prev.prog.next x c
      --       t = (n (Left  x) c)
      --   in ?hole
      -- next (Right _) _  = []
      -- next (Left  x) c with (find prev.accepting (prev.next x c))
      --   next (Left  x) c | Nothing = ?jjjk
      --   next (Left  x) c | (Just _) = ?jjj

      --next (Right _) _  = []

      prog: Program (thompsonNFA (Group y))
      prog = MkProgram init next

  in MkVMrec prog nextNFA (cong2 nextGroup prev.nextPrf prev.acceptPrf) acceptGroup Refl

thompsonVM: (re: CoreRE) -> Program (thompsonNFA re)
