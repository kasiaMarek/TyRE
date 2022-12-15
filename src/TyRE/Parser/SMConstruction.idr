module TyRE.Parser.SMConstruction

import Data.List

import TyRE.Codes
import TyRE.CoreRE
import TyRE.Parser.SM
import TyRE.Parser.GroupThompson

||| Compile function creates a state machine from an untyped regex
export
compile : (r : CoreRE) -> SM (ShapeCode r)
--sm for empty language
compile Empty =
  let lookup : Void -> SnocList Code
      lookup _ impossible
      init : InitStatesType UnitC Void lookup
      init = [(Nothing ** (RUnit () ** InitRUnit))]
      next : NextStatesType UnitC Void lookup
      next _ _ = []
  in MkSM Void lookup init next
--sm for predicate
compile (CharPred f) =
  let lookup : () -> SnocList Code
      lookup () = [< UnitC]
      init : InitStatesType CharC () lookup
      init = [(Just () ** (RUnit () ** InitRUnit))]
      next : NextStatesType CharC () lookup
      next () c =
        if satisfies f c
        then [(Nothing ** Join PushChar (ReducePair (\_,c => c)))]
        else []
  in MkSM () lookup init next
--sm for concatenation
compile (x `Concat` y) =
  let MkSM s1 l1 i1 n1 := compile x
      MkSM s2 l2 i2 n2 := compile y
      0 T : Type
      T = Either s1 s2
      0 code : Code
      code = PairC (ShapeCode x) (ShapeCode y)
      0 lookup : T -> SnocList Code
      lookup (Left s)  = l1 s
      lookup (Right s) = [< ShapeCode x] ++ l2 s
      init : InitStatesType code T lookup
      init =
        (i1 >>=
          (\case
            (Nothing ** r ** p) =>
              map (\case
                    (Nothing ** r2 ** p2) =>
                      (Nothing
                      ** ((r `Join` (Lift r2)) `Join` (ReducePair MkPair))
                      ** ((p `InitJoin` (InitLift p2)) `InitJoin` InitReducePair))
                    (Just st ** r2 ** p2) =>
                      (Just (Right st)
                      ** (r `Join` (Lift r2))
                      ** (p `InitJoin` (InitLift p2))))
              i2
            (Just st ** r) => [(Just (Left st) ** r)]))
      next : NextStatesType code T lookup
      next (Left st) c =
        (n1 st c >>=
          (\case
            (Nothing ** r) =>
              map (\case
                    (Nothing ** r2 ** _) =>
                      (Nothing
                      ** ((r `Join` (Lift r2)) `Join` ReducePair MkPair))
                    (Just s2 ** r2 ** _) =>
                      (Just (Right s2)
                      ** (r `Join` (Lift r2))))
                  i2
            (Just st ** r) => [(Just (Left st) ** r)]))
      next (Right st) c =
        map (\case
                (Nothing ** r) => (Nothing ** (Lift r `Join` ReducePair MkPair))
                (Just st ** r) => (Just (Right st) ** Lift r))
              (n2 st c)
  in MkSM T lookup init next
-- sm for alternation
compile (x `Alt` y) =
  let MkSM s1 l1 i1 n1 := compile x
      MkSM s2 l2 i2 n2 := compile y
      0 T : Type
      T = Either s1 s2
      0 code : Code
      code = EitherC (ShapeCode x) (ShapeCode y)
      0 lookup : T -> SnocList Code
      lookup (Left s)  = l1 s
      lookup (Right s) = l2 s
      init : InitStatesType code T lookup
      init = map  (\case
                      (Nothing ** (rt ** p)) =>
                        (Nothing
                        ** (Join rt (EmitLeft (ShapeCode y))
                        ** InitJoin p InitEmitLeft))
                      (Just st ** r) => (Just (Left st) ** r))
                  i1
           ++ map (\case
                      (Nothing ** (rt ** p)) =>
                        (Nothing
                        ** (Join rt (EmitRight (ShapeCode x))
                        ** InitJoin p InitEmitRight))
                      (Just st ** r) => (Just (Right st) ** r))
                  i2
      next : NextStatesType code T lookup
      next (Left s) c =
        map (\case
                (Nothing ** rt) =>
                  (Nothing ** Join rt (EmitLeft (ShapeCode y)))
                (Just st ** rt) => (Just (Left st) ** rt))
            (n1 s c)
      next (Right s) c =
        map (\case
                (Nothing ** rt) =>
                  (Nothing ** Join rt (EmitRight (ShapeCode x)))
                (Just st ** rt) => (Just (Right st) ** rt))
            (n2 s c)
  in MkSM T lookup init next
-- sm for Kleene star
compile (Star re) =
  let MkSM t lookupPrev initPrev nextPrev := compile re
      0 T : Type
      T = t
      code : Code
      code = ListC (ShapeCode re)
      0 lookup : T -> SnocList Code
      lookup s = [< ListC (ShapeCode re)] ++ lookupPrev s
      init : InitStatesType code T lookup
      init = (Nothing ** RUnit [<] ** InitRUnit)
           :: map (\case
                    (Nothing ** r ** p) => (Nothing ** RUnit [<] ** InitRUnit)
                    (Just st ** r ** p) =>
                      (Just st ** (RUnit Prelude.Basics.Lin `Join` Lift r)
                              ** (InitRUnit `InitJoin` (InitLift p))))
                  initPrev
      next : NextStatesType code T lookup
      next s c =
        (nextPrev s c) >>=
          \case
            (Nothing ** r) =>
                (Nothing ** (Lift r `Join` ReducePair (:<)))
              :: map (\case
                        (Nothing ** r2 ** _) =>
                          (Nothing ** (Lift r `Join` ReducePair (:<)))
                        (Just st ** r2 ** _) =>
                          (Just st ** ((Lift r `Join` ReducePair (:<)) `Join` Lift r2)))
                      initPrev
            (Just st ** r) => [(Just st ** Lift r)]
  in MkSM T lookup init next
-- sm for group made
compile (Group r) = asSM (groupSM r) where
  asSM : GroupSM -> SM StringC
  asSM (MkGroupSM initStates statesWithNext max) =
    let lookup : Nat -> SnocList Code
        lookup _ = [<]
        init : InitStatesType StringC Nat lookup
        init = map (\case
                      Just s => (Just s ** Record ** InitRecord)
                      Nothing => (Nothing ** EmitString ** InitEmitString))
                   initStates
        next : NextStatesType StringC Nat lookup
        next s c with (find (\case (n, ns) => n == s) statesWithNext)
          next s c | Nothing = []
          next s c | (Just (_, (MkNextStates condition isSat notSat))) =
            let addRoutines : List (Maybe Nat)
                                      -> List (st' : Maybe Nat
                                              ** Routine [<] (mlookup lookup StringC st'))
                addRoutines n =
                  map (\case
                        Nothing => (Nothing ** EmitString)
                        Just s => (Just s ** Same)) n
                in if satisfies condition c
                        then addRoutines isSat
                        else addRoutines notSat
    in MkSM Nat lookup init next