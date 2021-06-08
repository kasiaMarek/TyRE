module NFA.Thompson

import Core
import NFA
import Data.List

record NatNA where
  constructor MkNatNA
  accepting     : Nat -> Bool
  start         : List Nat
  next          : Nat -> Char -> List Nat

thompson_rec: CoreRE -> Nat -> (NatNA, Nat)

thompson_rec (Pred f) k =
  let startState  = k + 1
      acceptState = k + 2

      accepting: Nat -> Bool
      accepting acceptState = True
      accepting _           = False

      next: Nat -> Char -> List Nat
      next startState    c   = if (f c) then [acceptState] else []
      next _             _   = []

      prev: Nat -> List (Char -> Bool, List Nat)
      prev  acceptState = [(f, [startState])]
      prev  _           = []

  in (MkNatNA accepting [startState] next, k + 2)

thompson_rec (Concat x y) k =
  let (t1, k') = thompson_rec x k
      (t2, k'') = thompson_rec y k'

      next : Nat -> Char -> List Nat
      next n c =
        let merged  : List Nat
            merged  = (t1.next n c) ++ (t2.next n c)
        in case (find t1.accepting merged) of
            Nothing => merged
            (Just _) => filter t1.accepting merged ++ t2.start

  in (MkNatNA t2.accepting t1.start next, k'')


thompson_rec (Group x) k = thompson_rec x k

thompson: CoreRE -> NA
thompson x =
  let natNa = fst (thompson_rec x 0)
  in (MkNFA Nat natNa.accepting natNa.start natNa.next)
