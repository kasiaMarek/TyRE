module TyRE.Parser2

import Data.SnocList
import Data.DPair
import Data.Maybe
import Data.List
import Data.List.Elem
import Data.Void

import TyRE.Codes
import TyRE.CoreRE
import TyRE.GroupThompson

import TyRE.Extra.Reflects

%default total

data Stack : SnocList Code -> Type where
  Lin : Stack [<]
  Snoc : Stack cds -> {0 c : Code} -> Sem c -> Stack (cds :< c)

data Routine : SnocList Code -> SnocList Code -> Type where
  RUnit : {x : Code} -> (Sem x) -> Routine [<] [< x]
  Same : Routine cds cds
  PushChar : Routine cds (cds :< CharC)
  ReducePair : {x,y,z : Code} -> (Sem x -> Sem y -> Sem z)
            -> Routine (cds :< x :< y) (cds :< z)
  EmitLeft : (y : Code) -> Routine (cds :< x) (cds :< EitherC x y)
  EmitRight : (y : Code) -> Routine (cds :< x) (cds :< EitherC y x)
  Join : Routine cds cds' -> Routine cds' cds'' -> Routine cds cds''
  Lift : Routine cds cds' -> Routine (pcds ++ cds) (pcds ++ cds')
  EmitString : Routine cds (cds :< StringC)
  Record : Routine cds cds

data IsInitRoutine : Routine c c' -> Type where
  InitSame : IsInitRoutine Same
  InitRecord : IsInitRoutine Record
  InitRUnit : IsInitRoutine (RUnit elem)
  InitReducePair : IsInitRoutine (ReducePair f)
  InitEmitLeft : IsInitRoutine (EmitLeft y)
  InitEmitRight : IsInitRoutine (EmitRight y)
  InitJoin : IsInitRoutine r1 -> IsInitRoutine r2 -> IsInitRoutine (Join r1 r2)
  InitLift : IsInitRoutine r -> IsInitRoutine (Lift r)
  InitEmitString : IsInitRoutine EmitString

mlookup : (s -> SnocList Code) -> Code -> Maybe s -> SnocList Code
mlookup f c Nothing = [< c]
mlookup f c (Just s) = f s

record SM (c : Code) where
  constructor MkSM
  0 S : Type
  {auto isEq : Eq S}
  0 lookup : S -> SnocList Code
  init : List (st : Maybe S **
                (r : Routine [<] (mlookup lookup c st) **
                  IsInitRoutine r))
  next : (st : S) -> Char
      -> List (st' : Maybe S ** Routine (lookup st) (mlookup lookup c st'))

record ThreadData (code : SnocList Code) where
  constructor MkThreadData
  stack : Stack code
  recorded : SnocList Char
  rec : Bool

record Thread {c : Code} (sm : SM c) where
  constructor MkThread
  state : Maybe sm.S 
  tddata : ThreadData (mlookup sm.lookup c state)

execRoutineAux : {0 scs, scs', p : SnocList Code}
            -> (r : Routine scs scs')
            -> Either Char (IsInitRoutine r)
            -> ThreadData (p ++ scs)
            -> ThreadData (p ++ scs')
execRoutineAux Same c st = st
execRoutineAux Record c (MkThreadData st col rec) =
  MkThreadData st col True
execRoutineAux (RUnit elem) c (MkThreadData st col rec) =
  MkThreadData (Snoc st elem) col rec
execRoutineAux PushChar (Left c) (MkThreadData st col rec) =
  MkThreadData (Snoc st c) col rec
execRoutineAux (ReducePair f) c (MkThreadData (Snoc (Snoc x z) y) col rec) =
  MkThreadData (Snoc x (f z y)) col rec
execRoutineAux (EmitLeft x) c (MkThreadData (Snoc y z) col rec) =
  MkThreadData (Snoc y (Left z)) col rec
execRoutineAux (EmitRight x) c (MkThreadData (Snoc y z) col rec) =
  MkThreadData (Snoc y (Right z)) col rec
execRoutineAux EmitString c (MkThreadData st col rec) =
  MkThreadData (Snoc st (show col)) [<] False
execRoutineAux (Join r1 r2) (Left c) st =
  execRoutineAux r2 (Left c) (execRoutineAux r1 (Left c) st)
execRoutineAux (Join r1 r2) (Right (InitJoin p1 p2)) st =
  execRoutineAux r2 (Right p2) (execRoutineAux r1 (Right p1) st)
execRoutineAux (Lift r) c st =
  let charOrPrf :=
        case c of
          Left c => Left c
          Right (InitLift p) => Right p 
  in replace {p = (ThreadData)}
          (sym $ appendAssociative _ _ _)
          (execRoutineAux r charOrPrf (replace {p = (ThreadData)}
                                       (appendAssociative _ _ _) st))

execRoutine : {0 scs, scs' : SnocList Code}
            -> (r : Routine scs scs')
            -> Either Char (IsInitRoutine r)
            -> ThreadData scs -> ThreadData scs'
execRoutine r c st =
  rewrite (sym $ appendLinLeftNeutral scs') in
    execRoutineAux {p = [<]} r c (rewrite (appendLinLeftNeutral scs) in st)

init : (sm : SM c) -> List (Thread sm)
init sm =
  map (\case
          (st ** (rt ** p)) =>
            MkThread st
                    (execRoutine rt (Right p) (MkThreadData [<] [<] False)))
                    sm.init

execOnThread : (sm : SM c) -> (c : Char) -> Thread sm -> List (Thread sm)
execOnThread sm c (MkThread Nothing info) = []
execOnThread sm c (MkThread (Just st) info) =
  let infoWithChar =
        case info of
          (MkThreadData stack recorded True) =>
            MkThreadData stack (recorded :< c) True
          info => info
  in map (\case (ns ** rt) => MkThread ns (execRoutine rt (Left c) infoWithChar))
         (sm.next st c)

run' : List Char -> (sm : SM c) -> List (Thread sm) -> List (Thread sm)
run' [] sm tds = tds
run' (c :: cs) sm tds = run' cs sm (tds >>= (execOnThread sm c))

compile : (r : CoreRE) -> SM (ShapeCode r)
compile Empty = MkSM Void (\case _ impossible)
                          [(Nothing ** (RUnit () ** InitRUnit))] (\_,_ => [])
compile (CharPred f) =
  MkSM ()
  (\case () => [< UnitC])
  [(Just () ** (RUnit () ** InitRUnit))]
  (\case () => \c => if satisfies f c
                    then [(Nothing ** Join PushChar (ReducePair (\_,c => c)))]
                    else [])
compile (x `Concat` y) =
  let MkSM s1 l1 i1 n1 := compile x
      MkSM s2 l2 i2 n2 := compile y
  in MkSM (Either s1 s2)
          (\case
            Left  s => l1 s
            Right s => [< ShapeCode x] ++ l2 s)
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
          (\case
            Left st =>
              \c => (n1 st c >>=
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
            Right st => \c => map (\case
                                    (Nothing ** r) => (Nothing ** (Lift r `Join` ReducePair MkPair))
                                    (Just st ** r) => (Just (Right st) ** Lift r))
                                  (n2 st c))
compile (x `Alt` y) =
  let sm1 := compile x
      sm2 := compile y
      _ := sm1.isEq
      _ := sm2.isEq
  in MkSM (Either sm1.S sm2.S)
          (\case
            Left  s => sm1.lookup s
            Right s => sm2.lookup s)
          (map (\case
                  (Nothing ** (rt ** p)) =>
                    (Nothing
                    ** (Join rt (EmitLeft (ShapeCode y))
                    ** InitJoin p InitEmitLeft))
                  (Just st ** r) => (Just (Left st) ** r))
                sm1.init
          ++ map (\case
                    (Nothing ** (rt ** p)) =>
                      (Nothing
                      ** (Join rt (EmitRight (ShapeCode x))
                      ** InitJoin p InitEmitRight))
                    (Just st ** r) => (Just (Right st) ** r))
                  sm2.init)
          (\case
            Left s =>
              \c => map (\case
                          (Nothing ** rt) =>
                            (Nothing ** Join rt (EmitLeft (ShapeCode y)))
                          (Just st ** rt) => (Just (Left st) ** rt))
                    (sm1.next s c)
            Right s =>
              \c => map (\case
                          (Nothing ** rt) =>
                            (Nothing ** Join rt (EmitRight (ShapeCode x)))
                          (Just st ** rt) => (Just (Right st) ** rt))
                    (sm2.next s c))
compile (Star re) =
  let sm := compile re
      _ := sm.isEq
  in MkSM sm.S
      (\s => [< ListC (ShapeCode re)] ++ sm.lookup s)
      ((Nothing ** RUnit [<] ** InitRUnit)
      :: map (\case
                (Nothing ** r ** p) => (Nothing ** RUnit [<] ** InitRUnit)
                (Just st ** r ** p) =>
                  (Just st ** (RUnit Prelude.Basics.Lin `Join` Lift r)
                           ** (InitRUnit `InitJoin` (InitLift p))))
             sm.init)
       (\s,c => (sm.next s c) >>=
                  \case
                    (Nothing ** r) =>
                      ((Nothing ** (Lift r `Join` ReducePair (:<)))
                      :: map (\case
                                (Nothing ** r2 ** _) =>
                                  (Nothing ** (Lift r `Join` ReducePair (:<)))
                                (Just st ** r2 ** _) =>
                                  (Just st ** ((Lift r `Join` ReducePair (:<)) `Join` Lift r2)))
                             sm.init)
                    (Just st ** r) => [(Just st ** Lift r)])
compile (Group r) = asSM (groupSM r) where
  asSM : GroupSM -> SM StringC
  asSM (MkGroupSM initStates statesWithNext max) =
    MkSM Nat (const [<])
      (map (\case
              Just s => (Just s ** Record ** InitRecord)
              Nothing => (Nothing ** EmitString ** InitEmitString))
           initStates)
      $ \st, c => case find (\case (n, ns) => n == st) statesWithNext of
                    Nothing => []
                    (Just (_, (MkNextStates condition isSat notSat))) =>
                      let addRoutines : List (Maybe Nat)
                                      -> List (st' : Maybe Nat
                                              ** Routine [<] (mlookup (\value => [<]) StringC st'))
                          addRoutines n =
                            map (\case
                                  Nothing => (Nothing ** EmitString)
                                  Just s => (Just s ** Same)) n
                      in if satisfies condition c
                        then addRoutines isSat
                        else addRoutines notSat

getFromStack : Stack [< c] -> Sem c
getFromStack (Snoc [<] r) = r

public export
parse : (r : CoreRE) -> List Char -> Maybe (Shape r)
parse re cs =
  case findR (\td => isNothing (td.state))
             (run' cs (compile re) (init (compile re))) of
    (Because Nothing p) => Nothing
    (Because (Just (MkThread (Just x) _)) (Indeed prf)) =>
      absurdity {t = Void} (case prf of (y, z) impossible)
    (Because (Just (MkThread Nothing (MkThreadData stck _ _))) _) =>
      Just $ getFromStack stck