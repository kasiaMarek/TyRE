module TyRE.Parser.SMConstruction

import Data.List

import TyRE.Core
import TyRE.Parser.SM
import TyRE.Parser.GroupThompson

||| Compile function creates a state machine from an untyped regex
export
compile : {0 a : Type} -> (tyre : TyRE a) -> SM a
--sm for empty language
compile Empty =
  let lookup : Void -> SnocList Type
      lookup _ impossible
      init : InitStatesType () Void lookup
      init = [(Nothing ** ([Push ()] ** [InitPush]))]
      next : NextStatesType () Void lookup
      next _ _ = []
  in MkSM Void lookup init next
--sm for predicate
compile (MatchChar f) =
  let lookup : () -> SnocList Type
      lookup () = [< ]
      init : InitStatesType Char () lookup
      init = [(Just () ** ([] ** []))]
      next : NextStatesType Char () lookup
      next () c =
        if satisfies f c
        then [(Nothing ** [PushChar])]
        else []
  in MkSM () lookup init next
--sm for concatenation
compile ((<*>) {a,b} x y) =
  let MkSM s1 l1 i1 n1 := compile x
      MkSM s2 l2 i2 n2 := compile y
      0 T : Type
      T = Either s1 s2
      0 lookup : T -> SnocList Type
      lookup (Left s)  = l1 s
      lookup (Right s) = [< a] ++ l2 s
      init : InitStatesType (a, b) T lookup
      init =
        (i1 >>=
          (\case
            (Nothing ** r ** p) =>
              map (\case
                    (Nothing ** r2 ** p2) =>
                      (Nothing
                      ** (r ++ lift r2 ++ [ReducePair MkPair])
                      ** (p ++ lift p2 ++ [InitReducePair]))
                    (Just st ** r2 ** p2) =>
                      (Just (Right st)
                      ** (r ++ lift r2)
                      ** (p ++ lift p2)))
              i2
            (Just st ** r) => [(Just (Left st) ** r)]))
      next : NextStatesType (a,b) T lookup
      next (Left st) c =
        (n1 st c >>=
          (\case
            (Nothing ** r) =>
              map (\case
                    (Nothing ** r2 ** _) =>
                      (Nothing
                      ** (r ++ lift r2 ++ [ReducePair MkPair]))
                    (Just s2 ** r2 ** _) =>
                      (Just (Right s2)
                      ** (r ++ lift r2)))
                  i2
            (Just st ** r) => [(Just (Left st) ** r)]))
      next (Right st) c =
        map (\case
                (Nothing ** r) => (Nothing ** (lift r ++ [ReducePair MkPair]))
                (Just st ** r) => (Just (Right st) ** lift r))
              (n2 st c)
  in MkSM T lookup init next
-- sm for alternation
compile ((<|>) {a,b} x y) =
  let MkSM s1 l1 i1 n1 := compile x
      MkSM s2 l2 i2 n2 := compile y
      0 T : Type
      T = Either s1 s2
      0 lookup : T -> SnocList Type
      lookup (Left s)  = l1 s
      lookup (Right s) = l2 s
      init : InitStatesType (Either a b) T lookup
      init = map  (\case
                      (Nothing ** (rt ** p)) =>
                        (Nothing
                        ** (rt ++ [Transform Left])
                        ** (p ++ [InitTransform]))
                      (Just st ** r) => (Just (Left st) ** r))
                  i1
           ++ map (\case
                      (Nothing ** (rt ** p)) =>
                        (Nothing
                        ** (rt ++ [Transform Right]
                        ** (p ++ [InitTransform])))
                      (Just st ** r) => (Just (Right st) ** r))
                  i2
      next : NextStatesType (Either a b) T lookup
      next (Left s) c =
        map (\case
                (Nothing ** rt) =>
                  (Nothing ** rt ++ [Transform Left])
                (Just st ** rt) => (Just (Left st) ** rt))
            (n1 s c)
      next (Right s) c =
        map (\case
                (Nothing ** rt) =>
                  (Nothing ** rt ++ [Transform Right])
                (Just st ** rt) => (Just (Right st) ** rt))
            (n2 s c)
  in MkSM T lookup init next
-- sm for Kleene star
compile (Rep {a} re) =
  let MkSM t lookupPrev initPrev nextPrev := compile re
      0 T : Type
      T = t
      0 lookup : T -> SnocList Type
      lookup s = [< SnocList a] ++ lookupPrev s
      init : InitStatesType (SnocList a) T lookup
      init = (Nothing ** [Push [<]] ** [InitPush])
           :: map (\case
                    (Nothing ** r ** p) => (Nothing ** [Push [<]] ** [InitPush])
                    (Just st ** r ** p) =>
                      (Just st ** (Push Prelude.Basics.Lin :: lift r)
                              ** (InitPush :: (lift p))))
                  initPrev
      next : NextStatesType (SnocList a) T lookup
      next s c =
        (nextPrev s c) >>=
          \case
            (Nothing ** r) =>
                (Nothing ** lift r ++ [ReducePair (:<)])
              :: map (\case
                        (Nothing ** r2 ** _) =>
                          (Nothing ** lift r ++ [ReducePair (:<)])
                        (Just st ** r2 ** _) =>
                          (Just st ** lift r ++ [ReducePair (:<)] ++ lift r2))
                      initPrev
            (Just st ** r) => [(Just st ** lift r)]
  in MkSM T lookup init next
-- sm for group made
compile {a = String} (Group r) = asSM (groupSM r) where
  asSM : GroupSM -> SM String
  asSM (MkGroupSM initStates statesWithNext max) =
    let lookup : Nat -> SnocList Type
        lookup _ = [<]
        init : InitStatesType String Nat lookup
        init = map (\case
                      Just s => (Just s ** [Record] ** [InitRecord])
                      Nothing => (Nothing ** [EmitString] ** [InitEmitString]))
                   initStates
        next : NextStatesType String Nat lookup
        next s c with (find (\case (n, ns) => n == s) statesWithNext)
          next s c | Nothing = []
          next s c | (Just (_, (MkNextStates condition isSat notSat))) =
            let addRoutines : List (Maybe Nat)
                                      -> List (st' : Maybe Nat
                                              ** Routine [<] (mlookup lookup String st'))
                addRoutines n =
                  map (\case
                        Nothing => (Nothing ** [EmitString])
                        Just s => (Just s ** [])) n
                in if satisfies condition c
                        then addRoutines isSat
                        else addRoutines notSat
    in MkSM Nat lookup init next
compile (Conv {a,b} re f) =
  let MkSM t lookup initPrev nextPrev := compile re
      init : InitStatesType b t lookup
      init = map (\case
                    (Nothing ** r ** p) => (Nothing ** r ++ [Transform f]
                                            ** p ++ [InitTransform])
                    (Just st ** rp) => (Just st ** rp))
                 initPrev
      next : NextStatesType b t lookup
      next st c = map (\case
                          (Nothing ** r) => (Nothing ** r ++ [Transform f])
                          (Just st ** r) => (Just st ** r))
                      (nextPrev st c)
  in MkSM t lookup init next
