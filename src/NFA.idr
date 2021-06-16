module NFA

import Data.Vect
import Data.SnocList
import Data.List
import Data.List.Elem
import Data.Vect.Elem
import Evidence
import Pred

||| A non-deterministic automaton
public export
record NA where
  constructor MkNFA
  ||| States in the automaton. Can be infinite.
  0 State : Type
  ||| A way to compare states
  {auto isEq : Eq State}
  ||| Accepting states
  accepting : State -> Bool
  ||| Initial states
  ||| A list since the same state might have different initialisation routines (more later).
  start : List State
  ||| A list since the same state might have different routines as a result of
  ||| combining NAs (more later).
  next : State -> Char -> List State

public export
Word : Type
Word = List Char

||| The VM we associate with an NFA can record a sub-sequence of characters
||| and act on an evidence
public export
record VMState where
  constructor MkVMState
  recording : Bool
  memory : SnocList Char
  evidence : Evidence

data Instruction =
    ||| Start recording word
    Record
  | ||| Emit the recorded string
    EmitString
  | ||| Emit the last character
    EmitLast
  -- | ||| Emit a unit
  --   EmitUnit
  | ||| Emit that the tape currently stores a pair
    EmitPair

public export
Routine : Type
Routine = List Instruction

||| A program, relative to a NFA, instructs what to do as we run the automaton:
public export
record Program (N : NA) where
  constructor MkProgram
  ||| Which routine to execute when we initialise a thread at each starting state
  init : Vect (length $ N .start) Routine
  ||| Which routine to execute
  next : (st : N .State) -> (c : Char) -> Vect (length $ N .next st c) Routine

public export
0 Thread : NA -> Type
Thread na = (na.State, VMState)

map : (f : (a,b) -> (c,d)) -> (xs : List a) ->
  (ys : Vect (length xs) b) ->
  (xs' : List c ** Vect (length xs') d)

map f [] [] = ([] ** [])
map f (x :: xs) (y :: ys) =
  let mp = f (x,y)
      rest = map f xs ys
  in (fst mp :: (fst rest) ** snd mp :: (snd rest))

public export
mapF : (f : (a,b) -> c) -> (xs : List a) -> (ys : Vect (length xs) b) -> List c
mapF f [] [] = []
mapF f (x :: xs) (y :: ys) = (f (x,y)) :: (mapF f xs ys)

||| Spec for mapF
mapFYImpFstX : (f : (a, b) -> c) -> (q : a -> Type) -> (p : c -> Type) -> (xs: List a) -> (ys: Vect (length xs) b)
        -> ((x' : b) -> (x : a) -> p (f (x, x')) -> q x)
        -> (y: c ** (y `Elem` mapF f xs ys, p y))
        -> (x : a ** (x `Elem` xs, q x))

mapFYImpFstX _ _ _ [] [] _ (_ ** (isElem, _)) = absurd isElem
mapFYImpFstX f q p (x :: xs) (z :: ys) spec (y ** (isElem, satP)) =
  case isElem of
    Here => (x ** (Here, spec z x satP))
    There pos =>
      let (x' ** (isElem', satQ')) = mapFYImpFstX f q p xs ys spec (y ** (pos, satP))
      in (x' ** (There isElem', satQ'))

parameters {auto N : NA}

public export
(.naState) : Thread N -> N .State
(.naState) = fst
public export
(.vmState) : Thread N -> VMState
(.vmState) = snd

public export
0 Step : Type
Step = (td : Thread N) -> Thread N

public export
0 ThreadPredicate : ((td : Thread N) -> Type) -> Type
ThreadPredicate pred = (td : Thread N) -> pred td

public export
step : Char -> Step
step x td =
  let updatedMemory =
    if (td.vmState.recording) then (td.vmState.memory :< x) else (td.vmState.memory)
      vmState = MkVMState (td.vmState.recording) updatedMemory (td.vmState.evidence)
  in (td.naState, vmState)

public export
stepMaintainsState : (c : Char) -> ThreadPredicate $
     (\td => (step c td).naState = td.naState)
  /\ (\td => (step c td).vmState.recording = td.vmState.recording)
  /\ (\td => (step c td).vmState.evidence  = td.vmState.evidence)

stepMaintainsState c td = (Refl,Refl,Refl)

emitChar          : (c : Char) -> Step
emitChar c td     = (td.naState, record {evidence $= (:< CharMark c)} td.vmState)

emitString        : Step
emitString td     =
  let vmState = MkVMState False [<] (td.vmState.evidence :< GroupMark (td.vmState.memory))
  in (td.naState, vmState)

startRecording    : Step
startRecording td = (td.naState, record {recording = True} td.vmState)

emitPair          : Step
emitPair td       = (td.naState, record {evidence $= (:< PairMark)} td.vmState)

stepForInstruction : (mc : Maybe Char) -> Instruction -> Step

stepForInstruction mc       Record      = startRecording
stepForInstruction mc       EmitString  = emitString
stepForInstruction mc       EmitPair    = emitPair
stepForInstruction (Just c) EmitLast    = emitChar c
stepForInstruction Nothing  EmitLast    = (\t => t)

public export
execute : (mc : Maybe Char) -> Routine -> Step
execute mc [] td = td
execute mc (x::xs) td = execute mc xs $ stepForInstruction mc x td

stepForInstructionMaintainsNAState : (mc : Maybe Char) -> (ins: Instruction) -> ThreadPredicate $
  \td => (stepForInstruction mc ins td).naState = td.naState

stepForInstructionMaintainsNAState mc       Record      td = Refl
stepForInstructionMaintainsNAState mc       EmitString  td = Refl
stepForInstructionMaintainsNAState mc       EmitPair    td = Refl
stepForInstructionMaintainsNAState (Just c) EmitLast    td = Refl
stepForInstructionMaintainsNAState Nothing  EmitLast    td = Refl

public export
executeMaintainsNAState : (mc : Maybe Char) -> (routine : Routine) -> ThreadPredicate $
  \td => (execute mc routine td).naState = td.naState

executeMaintainsNAState mc [] td      = Refl
executeMaintainsNAState mc (x::xs) td =
  let recur = executeMaintainsNAState mc xs (stepForInstruction mc x td)
      sfim  = stepForInstructionMaintainsNAState mc x td
  in trans recur sfim

run: Word -> List (N .State) -> Bool
run [] ys = case (find (N .accepting) ys) of
              (Just _)  => True
              Nothing   => False
run (c :: cs) ys = run cs (ys >>= (\s => N .next s c))

parameters  {auto P : Program N}

--implementation of initialise
public export
initVM : VMState
initVM = MkVMState False [<] [<]

public export
initFuction : (N .State, Routine) -> Thread N
initFuction (s,r) = execute Nothing r (s, initVM)

public export
initialise : List (Thread N)
initialise = mapF initFuction (N .start) (P .init)

--implementation of runFrom
public export
runFunction : Char -> Thread N -> (N .State, Routine) -> (N .State, VMState)
runFunction c td (st, r) = (st, snd $ execute (Just c) r td)

public export
runMapping: Char -> Thread N -> List (Thread N)
runMapping c td = mapF (runFunction c td) (N .next (fst td) c) (P .next (fst td) c)

public export
runMain: Char -> List (Thread N) -> List (Thread N)
runMain c tds = tds >>= runMapping c . (step c)

public export
runFrom : Word -> (tds : List $ Thread N) -> Maybe Evidence
runFrom [] tds =  map (\td => (snd td) .evidence) (find (\td => N .accepting (fst td)) tds)
runFrom (c::cs) tds = runFrom cs $ runMain c tds

|||Proof that in a single step executed by runFrom we change the state to one from N .next.
public export
runFromStepState : (c: Char) -> (td: Thread N) -> (td' : Thread N) -> (td' `Elem` runMapping c td) -> td'.naState `Elem` (N .next td.naState c)
runFromStepState c td td' isElem =
  let (x ** (isElem', eq)) =  mapFYImpFstX
                                  (runFunction c td)
                                  (\e => (td'.naState = e))
                                  (\t => (td'.naState = t.naState))
                                  (N .next (fst td) c)
                                  (P .next (fst td) c)
                                  (\_ => \_ => \p => p)
                                  (td' ** (isElem, Refl))
  in replace {p=(\e => e `Elem` (N .next (fst td) c))} (sym eq) isElem'
