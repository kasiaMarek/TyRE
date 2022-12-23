module TyRE.Parser2.SM

import Data.SnocList

import TyRE.Codes
import TyRE.CoreRE

import Data.Maybe
import Data.List
import Data.List.Elem
import Data.Void

import TyRE.Extra.Reflects

%default total

--- definition of SM ---

public export
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

public export
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

public export
mlookup : (s -> SnocList Code) -> Code -> Maybe s -> SnocList Code
mlookup f c Nothing = [< c]
mlookup f c (Just s) = f s

public export
InitStatesType : (c : Code) -> (s : Type) -> (s -> SnocList Code) -> Type
InitStatesType c s lookup =
  List (st : Maybe s
        ** (r : Routine [<] (mlookup lookup c st)
            ** IsInitRoutine r))

public export
NextStatesType : (c : Code) -> (s : Type) -> (s -> SnocList Code) -> Type
NextStatesType c s lookup = 
    (st : s)
  -> Char
  -> List (st' : Maybe s
            ** Routine (lookup st) (mlookup lookup c st'))

public export
record SM (c : Code) where
  constructor MkSM
  0 s : Type
  0 lookup : s -> SnocList Code
  {auto isEq : Eq s}
  init : InitStatesType c s lookup
  next : NextStatesType c s lookup

--- execution of the SM ---

data Stack : SnocList Code -> Type where
  Lin : Stack [<]
  Snoc : Stack cds -> {0 c : Code} -> Sem c -> Stack (cds :< c)

record ThreadData (code : SnocList Code) where
  constructor MkThreadData
  stack : Stack code
  recorded : SnocList Char
  rec : Bool

record Thread {c : Code} (sm : SM c) where
  constructor MkThread
  state : Maybe sm.s 
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
  MkThreadData (Snoc st (fastPack $ cast col)) [<] False
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

getFromStack : Stack [< c] -> Sem c
getFromStack (Snoc [<] r) = r

parameters {c : Code} {auto sm : SM c}
  ||| Distinct function for threads
  distinct : List (Thread sm) -> List (Thread sm)
  distinct tds = distinctRep tds [] where
    distinctRep : List (Thread sm) -> List (Thread sm) -> List (Thread sm)
    distinctRep [] acc = acc
    distinctRep (td :: tds) acc =
      let _ := sm.isEq
      in case find (\t => t.state == td.state) acc of
          (Just _) => distinctRep tds acc
          Nothing  => distinctRep tds (td :: acc)
  ||| Initial list of threads
  init : List (Thread sm)
  init =
    map (\case
            (st ** (rt ** p)) =>
              MkThread st
                      (execRoutine rt (Right p) (MkThreadData [<] [<] False)))
                      sm.init

  namespace StringRunners -- possible modes of running for list of characters
    ||| Run the state machine matching the whole string
    export
    runTillStrEnd : List Char -> List (Thread sm) -> Maybe (Sem c)
    runTillStrEnd [] tds with (findR (\td => isNothing (td.state)) tds)
      runTillStrEnd [] tds | (Because Nothing p) = Nothing
      runTillStrEnd [] tds
        | (Because (Just (MkThread Nothing (MkThreadData stack _ _))) _)
        = Just (getFromStack stack)
      runTillStrEnd [] tds
        | (Because (Just (MkThread (Just x) tddata)) (Indeed prf))
        = absurdity {t = Void} (case prf of (y, z) impossible)
    runTillStrEnd (c :: cs) tds =
      runTillStrEnd cs (distinct $ tds >>= (execOnThread sm c))
    ||| Run the state machine looking for a first matching prefix (non-greedy)
    export
    runTillFirstAccept : List Char -> List (Thread sm)
                      -> (Maybe (Sem c), List Char)
    runTillFirstAccept cs [] = (Nothing, cs)
    runTillFirstAccept cs tds with (findR (\td => isNothing (td.state)) tds)
      runTillFirstAccept [] tds        | (Because Nothing p) = (Nothing, [])
      runTillFirstAccept (x :: xs) tds | (Because Nothing p) =
        runTillFirstAccept xs (distinct $ tds >>= (execOnThread sm x))
      runTillFirstAccept cs tds
        | (Because (Just (MkThread Nothing (MkThreadData stack _ _))) _)
        = (Just (getFromStack stack), cs)
      runTillFirstAccept cs tds
        | (Because (Just (MkThread (Just x) tddata)) (Indeed prf))
        = absurdity {t = Void} (case prf of (y, z) impossible)
    ||| Run the state machine looking for the last matching prefix (greedy)
    export
    runTillLastAccept : List Char -> Maybe (Sem c, List Char)
                      -> List (Thread sm)
                      -> (Maybe (Sem c), List Char)
    runTillLastAccept cs Nothing [] = (Nothing, cs)
    runTillLastAccept cs (Just (tree, rest)) [] = (Just tree, rest)
    runTillLastAccept cs mr tds with (findR (\td => isNothing (td.state)) tds)
      runTillLastAccept [] Nothing tds | (Because Nothing p) = (Nothing, [])
      runTillLastAccept [] (Just (tree, tail)) tds
                        | (Because Nothing p) = (Just tree, tail)
      runTillLastAccept (x :: xs) mr tds | (Because Nothing p) =
        runTillLastAccept xs mr (distinct $ tds >>= (execOnThread sm x))
      runTillLastAccept [] mr tds
        | (Because (Just (MkThread Nothing (MkThreadData stack _ _))) _)
        = (Just (getFromStack stack), [])
      runTillLastAccept (x :: xs) mr tds
        | (Because (Just (MkThread Nothing (MkThreadData stack _ _))) _)
        = runTillLastAccept xs
                            (Just (getFromStack stack, x :: xs))
                            (distinct $ tds >>= (execOnThread sm x))
      runTillLastAccept cs mr tds
        | (Because (Just (MkThread (Just x) tddata)) (Indeed prf))
        = absurdity {t = Void} (case prf of (y, z) impossible)

  namespace StreamRunners -- possible modes of running for streams
    ||| Run the state machine looking for a first matching prefix (non-greedy)
    ||| re return also the leftover stream
    export
    partial
    runTillFirstAccept : Stream Char -> List (Thread sm)
                      -> (Maybe (Sem c), Stream Char)
    runTillFirstAccept cs [] = (Nothing, cs)
    runTillFirstAccept cs tds with (findR (\td => isNothing (td.state)) tds)
      runTillFirstAccept (x :: xs) tds | (Because Nothing p) =
        runTillFirstAccept xs (distinct $ tds >>= (execOnThread sm x))
      runTillFirstAccept cs tds
        | (Because (Just (MkThread Nothing (MkThreadData stack _ _))) _)
        = (Just (getFromStack stack), cs)
      runTillFirstAccept cs tds
        | (Because (Just (MkThread (Just x) tddata)) (Indeed prf))
        = absurdity {t = Void} (case prf of (y, z) impossible)
    ||| Run the state machine looking for the last matching prefix (greedy)
    export
    partial
    runTillLastAccept : Stream Char -> Maybe (Sem c, Stream Char)
                      -> List (Thread sm)
                      -> (Maybe (Sem c), Stream Char)
    runTillLastAccept cs Nothing [] = (Nothing, cs)
    runTillLastAccept cs (Just (tree, rest)) [] = (Just tree, rest)
    runTillLastAccept cs mr tds with (findR (\td => isNothing (td.state)) tds)
      runTillLastAccept (x :: xs) mr tds | (Because Nothing p) =
        runTillLastAccept xs mr (distinct $ tds >>= (execOnThread sm x))
      runTillLastAccept (x :: xs) mr tds
        | (Because (Just (MkThread Nothing (MkThreadData stack _ _))) _)
        = runTillLastAccept xs
                            (Just (getFromStack stack, x :: xs))
                            (distinct $ tds >>= (execOnThread sm x))
      runTillLastAccept cs mr tds
        | (Because (Just (MkThread (Just x) tddata)) (Indeed prf))
        = absurdity {t = Void} (case prf of (y, z) impossible)

  export
  runFromInit : (runFunction : List (Thread sm) -> a) -> a
  runFromInit runFunction = runFunction init
