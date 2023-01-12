module TyRE.Parser.SM

import Data.SnocList

import Data.Maybe
import Data.List
import Data.List.Elem
import Data.Void

import TyRE.Extra.Reflects

%default total

--- definition of SM ---

public export
data Routine : SnocList Type -> SnocList Type -> Type where
  ||| Identity
  Same : Routine tps tps
  ||| Pushes chosen symbol on the stack
  Push : {0 x : Type} -> x -> Routine [<] [< x]
  ||| Pushes currently consumed character on the stack
  PushChar : Routine tps (tps :< Char)
  ||| Reduces two last symbols from the stack accoring to the given funciton
  ReducePair : {0 x,y,z : Type} -> (x -> y -> z)
            -> Routine (tps :< x :< y) (tps :< z)
  ||| Maps the top element of stack
  Transform : {0 x,y : Type} -> (x -> y) -> Routine (tps :< x) (tps :< y)
  ||| Pushes collected string on the stack
  EmitString : Routine tps (tps :< String)
  ||| Raises record flag and starts collecting characters
  Record : Routine tps tps
  ||| Sequences routines
  Join : Routine tps tps' -> Routine tps' tps'' -> Routine tps tps''
  ||| Lifts Routine type
  Lift : Routine tps tps' -> Routine (pcds ++ tps) (pcds ++ tps')

public export
data IsInitRoutine : Routine t t' -> Type where
  InitSame : IsInitRoutine Same
  InitRecord : IsInitRoutine Record
  InitPush : IsInitRoutine (Push elem)
  InitReducePair : IsInitRoutine (ReducePair f)
  InitTransform : IsInitRoutine (Transform f)
  InitJoin : IsInitRoutine r1 -> IsInitRoutine r2 -> IsInitRoutine (Join r1 r2)
  InitLift : IsInitRoutine r -> IsInitRoutine (Lift r)
  InitEmitString : IsInitRoutine EmitString

public export
mlookup : (s -> SnocList Type) -> Type -> Maybe s -> SnocList Type
mlookup f t Nothing = [< t]
mlookup f t (Just s) = f s

public export
InitStatesType : (t : Type) -> (s : Type) -> (s -> SnocList Type) -> Type
InitStatesType t s lookup =
  List (st : Maybe s
        ** (r : Routine [<] (mlookup lookup t st)
            ** IsInitRoutine r))

public export
NextStatesType : (t : Type) -> (s : Type) -> (s -> SnocList Type) -> Type
NextStatesType t s lookup = 
    (st : s)
  -> Char
  -> List (st' : Maybe s
            ** Routine (lookup st) (mlookup lookup t st'))

public export
record SM (t : Type) where
  constructor MkSM
  0 s : Type
  0 lookup : s -> SnocList Type
  {auto isEq : Eq s}
  init : InitStatesType t s lookup
  next : NextStatesType t s lookup

--- execution of the SM ---

data Stack : SnocList Type -> Type where
  Lin : Stack [<]
  Snoc : Stack tps -> {0 t : Type} -> t -> Stack (tps :< t)

record ThreadData (code : SnocList Type) where
  constructor MkThreadData
  stack : Stack code
  recorded : SnocList Char
  rec : Bool

record Thread {t : Type} (sm : SM t) where
  constructor MkThread
  state : Maybe sm.s 
  tddata : ThreadData (mlookup sm.lookup t state)

execRoutineAux : {0 scs, scs', p : SnocList Type}
            -> (r : Routine scs scs')
            -> Either Char (IsInitRoutine r)
            -> ThreadData (p ++ scs)
            -> ThreadData (p ++ scs')
execRoutineAux Same c st = st
execRoutineAux Record c (MkThreadData st col rec) =
  MkThreadData st col True
execRoutineAux (Push elem) c (MkThreadData st col rec) =
  MkThreadData (Snoc st elem) col rec
execRoutineAux PushChar (Left c) (MkThreadData st col rec) =
  MkThreadData (Snoc st c) col rec
execRoutineAux (ReducePair f) c (MkThreadData (Snoc (Snoc x z) y) col rec) =
  MkThreadData (Snoc x (f z y)) col rec
execRoutineAux (Transform f) c (MkThreadData (Snoc y z) col rec) =
  MkThreadData (Snoc y (f z)) col rec
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

execRoutine : {0 scs, scs' : SnocList Type}
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

getFromStack : Stack [< t] -> t
getFromStack (Snoc [<] r) = r

parameters {0 t : Type} {auto sm : SM t}
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
    runTillStrEnd : List Char -> List (Thread sm) -> Maybe t
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
                      -> (Maybe t, List Char)
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
    runTillLastAccept : List Char -> Maybe (t, List Char)
                      -> List (Thread sm)
                      -> (Maybe t, List Char)
    runTillLastAccept cs Nothing [] = (Nothing, cs)
    runTillLastAccept cs (Just (tree, rest)) [] = (Just tree, rest)
    runTillLastAccept cs mr tds with (findR (\td => isNothing (td.state)) tds)
      runTillLastAccept [] Nothing tds | (Because Nothing p) =(Nothing, [])
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
                      -> (Maybe t, Stream Char)
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
    runTillLastAccept : Stream Char -> Maybe (t, Stream Char)
                      -> List (Thread sm)
                      -> (Maybe t, Stream Char)
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
