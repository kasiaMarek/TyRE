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
data Instruction : SnocList Type -> SnocList Type -> Type where
  ||| Pushes chosen symbol on the stack
  Push : {0 x : Type} -> x -> Instruction tps (tps :< x)
  ||| Pushes currently consumed character on the stack
  PushChar : Instruction tps (tps :< Char)
  ||| Reduces two last symbols from the stack accoring to the given funciton
  ReducePair : {0 x,y,z : Type} -> (x -> y -> z)
            -> Instruction (tps :< x :< y) (tps :< z)
  ||| Maps the top element of stack
  Transform : {0 x,y : Type} -> (x -> y) -> Instruction (tps :< x) (tps :< y)
  ||| Pushes collected string on the stack
  EmitString : Instruction tps (tps :< String)
  ||| Raises record flag and starts collecting characters
  Record : Instruction tps tps

public export
liftInst : Instruction tps tps' -> Instruction (pcds ++ tps) (pcds ++ tps')
liftInst (Push x) = Push x
liftInst PushChar = PushChar
liftInst (ReducePair f) = ReducePair f
liftInst (Transform f) = Transform f
liftInst EmitString = EmitString
liftInst Record = Record

public export
data RoutineSnoc : SnocList Type -> SnocList Type -> Type where
  ||| Identity
  Lin : RoutineSnoc tps tps
  ||| Sequences routines
  (:<) : RoutineSnoc tps tps' -> Instruction tps' tps'' -> RoutineSnoc tps tps''

public export
data Routine : SnocList Type -> SnocList Type -> Type where
  ||| Identity
  Nil : Routine tps tps
  ||| Sequences routines
  (::) : Instruction tps tps' -> Routine tps' tps'' -> Routine tps tps''

public export
(++) : RoutineSnoc tps tps' -> RoutineSnoc tps' tps'' -> RoutineSnoc tps tps''
(++) r [<] = r
(++) r (x :< y) = (r ++ x) :< y

public export
lift : RoutineSnoc tps tps' -> RoutineSnoc (pcds ++ tps) (pcds ++ tps')
lift [<] = [<]
lift (x :< y) = (lift x) :< liftInst y

reverseRec : RoutineSnoc ts ts' -> Routine ts' ts'' -> Routine ts ts''
reverseRec [<] y = y
reverseRec (x :< z) y = reverseRec x (z :: y)

reverse : RoutineSnoc tps tps' -> Routine tps tps'
reverse sx = reverseRec sx []


namespace IsInit
  public export
  data IsInitInstruction : Instruction t t' -> Type where
    InitRecord : IsInitInstruction Record
    InitPush : IsInitInstruction (Push elem)
    InitReducePair : IsInitInstruction (ReducePair f)
    InitTransform : IsInitInstruction (Transform f)
    InitEmitString : IsInitInstruction EmitString

  public export
  data IsInitRoutine : Routine t t' -> Type where
    Nil  : IsInitRoutine []
    (::) : IsInitInstruction x -> IsInitRoutine xs -> IsInitRoutine (x :: xs)

  public export
  data IsInitRoutineSnoc : RoutineSnoc t t' -> Type where
    Lin  : IsInitRoutineSnoc [<]
    (:<) : IsInitRoutineSnoc xs -> IsInitInstruction x
        -> IsInitRoutineSnoc (xs :< x)

  public export
  (++) : IsInitRoutineSnoc xs -> IsInitRoutineSnoc xs'
      -> IsInitRoutineSnoc (xs ++ xs')
  (++) x [<] = x
  (++) x (y :< z) = (x ++ y) :< z

  reverseRec : IsInitRoutineSnoc sx -> IsInitRoutine xs
            -> IsInitRoutine (reverseRec sx xs)
  reverseRec [<] y = y
  reverseRec (x :< z) y = reverseRec x (z :: y)

  export
  reverse : IsInitRoutineSnoc sx -> IsInitRoutine (reverse sx)
  reverse sx = reverseRec sx []

  liftInst : IsInitInstruction xs -> IsInitInstruction (liftInst xs)
  liftInst InitRecord = InitRecord
  liftInst InitPush = InitPush
  liftInst InitReducePair = InitReducePair
  liftInst InitTransform = InitTransform
  liftInst InitEmitString = InitEmitString

  public export
  lift : IsInitRoutineSnoc xs -> IsInitRoutineSnoc (lift xs)
  lift [<] = [<]
  lift (x :< y) = (lift x) :< (liftInst y)

public export
mlookup : (s -> SnocList Type) -> Type -> Maybe s -> SnocList Type
mlookup f t Nothing = [< t]
mlookup f t (Just s) = f s

public export
InitStatesType : (t : Type) -> (s : Type) -> (s -> SnocList Type) -> Type
InitStatesType t s lookup =
  List (st : Maybe s
        ** (r : RoutineSnoc [<] (mlookup lookup t st)
            ** IsInitRoutineSnoc r))

public export
NextStatesType : (t : Type) -> (s : Type) -> (s -> SnocList Type) -> Type
NextStatesType t s lookup =
    (st : s)
  -> Char
  -> List (st' : Maybe s
            ** RoutineSnoc (lookup st) (mlookup lookup t st'))

public export
record SM (t : Type) where
  constructor MkSM
  0 s : Type
  0 lookup : s -> SnocList Type
  {auto isEq : Eq s}
  init : InitStatesType t s lookup
  next : NextStatesType t s lookup

--- execution of the SM ---
namespace Stack
  public export
  data Stack : SnocList Type -> Type where
    Lin : Stack [<]
    (:<) : Stack tps -> {0 t : Type} -> t -> Stack (tps :< t)

record ThreadData (code : SnocList Type) where
  constructor MkThreadData
  stack : Stack code
  recorded : SnocList Char
  rec : Bool

record Thread {t : Type} (sm : SM t) where
  constructor MkThread
  state : Maybe sm.s
  tddata : ThreadData (mlookup sm.lookup t state)

execInstructionAux : {0 scs, scs', p : SnocList Type}
                  -> (r : Instruction scs scs')
                  -> Either Char (IsInitInstruction r)
                  -> ThreadData (p ++ scs)
                  -> ThreadData (p ++ scs')
execInstructionAux Record c (MkThreadData st col rec) =
  MkThreadData st col True
execInstructionAux (Push elem) c (MkThreadData st col rec) =
  MkThreadData (st :< elem) col rec
execInstructionAux PushChar (Left c) (MkThreadData st col rec) =
  MkThreadData (st :< c) col rec
execInstructionAux (ReducePair f) c (MkThreadData (x :< z :< y) col rec) =
  MkThreadData (x :< (f z y)) col rec
execInstructionAux (Transform f) c (MkThreadData (y :< z) col rec) =
  MkThreadData (y :< (f z)) col rec
execInstructionAux EmitString c (MkThreadData st col rec) =
  MkThreadData (st :< (fastPack $ cast col)) [<] False

execRoutineAux : {0 scs, scs', p : SnocList Type}
            -> (r : Routine scs scs')
            -> Either Char (IsInitRoutine r)
            -> ThreadData (p ++ scs)
            -> ThreadData (p ++ scs')
execRoutineAux [] c st = st
execRoutineAux (i :: r) (Left c) st =
  execRoutineAux r (Left c) (execInstructionAux i (Left c) st)
execRoutineAux (i :: r) (Right (ip :: ir)) st =
  execRoutineAux r (Right ir) (execInstructionAux i (Right ip) st)

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
  in map (\case (ns ** rt) => MkThread ns (execRoutine (reverse rt) (Left c) infoWithChar))
         (sm.next st c)

getFromStack : Stack [< t] -> t
getFromStack ([< r]) = r

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
                      (execRoutine (reverse rt) (Right $ reverse p) (MkThreadData [<] [<] False)))
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
