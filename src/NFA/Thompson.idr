module NFA.Thompson

import Core
import NFA
import Data.List

record NatNA where
  constructor MkNatNA
  accepting     : Nat -> Bool
  start         : List Nat
  next          : Nat -> Char -> List Nat

thompson: CoreRE -> NA

thompson (Pred f) =
  let data State = StartState | AcceptState

      Eq State where
        StartState  == StartState   = True
        AcceptState == AcceptState  = True
        _           == _            = False

      accepting: State -> Bool
      accepting AcceptState = True
      accepting StartState  = False

      next: State -> Char -> List State
      next StartState    c   = if (f c) then [AcceptState] else []
      next AcceptState   _   = []

  in MkNFA State accepting [StartState] next

thompson (Concat x y) =
  let t1 = thompson x
      t2 = thompson y

      accepting: (Either t1.State t2.State) -> Bool
      accepting (Left  _) = False
      accepting (Right x) = t2.accepting x

      start: List (Either t1.State t2.State)
      start = map (\s => Left s) t1.start

      next : (Either t1.State t2.State) -> Char -> List (Either t1.State t2.State)
      next (Left  s) c =
        let t1Next = t1.next s c
        in case (find t1.accepting t1Next) of
              Nothing => (map (\s => Left s) t1Next)
              (Just _) => (map (\s => Left s) (filter t1.accepting t1Next)) ++ (map (\s => Right s) t2.start)
      next (Right s) c = (map (\s => Right s) (t2.next s c))

      --TODO:
      Eq (Either t1.State t2.State)

  in MkNFA (Either t1.State t2.State) accepting start next


thompson (Group x) = thompson x
