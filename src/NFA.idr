module NFA

import Data.Vect
import Data.SnocList
import Data.List
import Evidence



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

Word : Type
Word = List Char

||| The VM we associate with an NFA can record a sub-sequence of characters
||| and act on an evidence
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

Routine : Type
Routine = List Instruction

||| A program, relative to a NFA, instructs what to do as we run the automaton:
record Program (N : NA) where
  constructor MkProgram
  ||| Which routine to execute when we initialise a thread at each starting state
  init : Vect (length $ N .start) Routine
  ||| Which routine to execute
  next : (st : N .State) -> (c : Char) -> Vect (length $ N .next st c) Routine


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

infixr 4 /\
(/\): {a: Type} -> (p : a -> Type) -> (q : a -> Type) -> a -> Type
(/\) {a} p q x = (p x, q x)

parameters {auto N : NA}

(.naState) : Thread N -> N .State
(.naState) = fst
(.vmState) : Thread N -> VMState
(.vmState) = snd

0 Step : Type
Step = (td : Thread N) -> Thread N
0 ThreadPredicate : ((td : Thread N) -> Type) -> Type
ThreadPredicate pred = (td : Thread N) -> pred td

step : Char -> Step
step x td =
  let updatedMemory =
    if (td.vmState.recording) then (td.vmState.memory :< x) else (td.vmState.memory)
      vmState = MkVMState (td.vmState.recording) updatedMemory (td.vmState.evidence)
  in (td.naState, vmState)

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

stepForInstruction: (mc : Maybe Char) -> Instruction -> Step

stepForInstruction mc       Record      = startRecording
stepForInstruction mc       EmitString  = emitString
stepForInstruction mc       EmitPair    = emitPair
stepForInstruction (Just c) EmitLast    = emitChar c
stepForInstruction Nothing  EmitLast    = (\t => t)

execute : (mc : Maybe Char) -> Routine -> Step
execute mc [] td = td
execute mc (x::xs) td = execute mc xs (stepForInstruction mc x td)

stepForInstructionMaintainsNAState : (mc : Maybe Char) -> (ins: Instruction) -> ThreadPredicate $
  \td => (stepForInstruction mc ins td).naState = td.naState

stepForInstructionMaintainsNAState mc       Record      td = Refl
stepForInstructionMaintainsNAState mc       EmitString  td = Refl
stepForInstructionMaintainsNAState mc       EmitPair    td = Refl
stepForInstructionMaintainsNAState (Just c) EmitLast    td = Refl
stepForInstructionMaintainsNAState Nothing  EmitLast    td = Refl

executeMaintainsNAState : (mc : Maybe Char) -> (routine : Routine) -> ThreadPredicate $
  \td => (execute mc routine td).naState = td.naState

executeMaintainsNAState mc [] td      = Refl
executeMaintainsNAState mc (x::xs) td =
  let recur = (executeMaintainsNAState mc xs (stepForInstruction mc x td))
      sfim  = (stepForInstructionMaintainsNAState mc x td)
  in trans recur sfim

parameters (P : Program N)


-- initialise : List (Thread N)
-- initialise =
--   let initVmState : VMState
--       initVmState = MkVMState False [<] [<]
--       f: (N .State, Routine) -> Thread N
--       f (s, r) = execute Nothing r (s, initVmState)
--   in mapF f (N .start) (P .init)
--
-- --TODO:sets
-- runFrom : Word -> (tds : List $ Thread N) -> Maybe Evidence
-- runFrom [] tds =  map (\td => (snd td) .evidence) (find (\td => N .accepting (fst td)) tds)
-- runFrom (c::cs) tds =
--   let m: Thread N -> (.State N, Routine) -> (.State N, VMState)
--       m t (s, r) = (s, snd (execute (Just c) r t))
--       f: Thread N -> List $ Thread N
--       f td = mapF (m td) ((N .next) (fst td) c) (P .next (fst td) c)
--   in runFrom cs (tds >>= f . (step c))

initialise : List (Thread N)
initialise = map (\s => (s, MkVMState False [<] [<])) (N .start)

mapF : (f : (a,b) -> c) -> (xs : List a) -> (ys : Vect (length xs) b) -> List c
mapF f xs ys = fst (map (\x => (f x, ())) xs ys)

add     : (xs: List $ Thread N ** Vect (length xs) Routine)
        -> (ys: List $ Thread N ** Vect (length ys) Routine)
        -> (zs: List $ Thread N ** Vect (length zs) Routine)

add ([] ** []) (t2 ** r2) = (t2 ** r2)
add ((t::t1) ** (r::r1)) (t2 ** r2) =
  let sh : Thread N -> Thread N -> Bool
      sh td1 td2   = ?i--(fst td1) == (fst td2) -- N .isEq
      exsistsState : Maybe $ Thread N
      exsistsState = find (sh t) t2
      added  : (zs: List $ Thread N ** Vect (length zs) Routine)
      added  = add (t1 ** r1) (t2 ** r2)
      added' : (zs: List $ Thread N ** Vect (length zs) Routine)
      added' = add (t1 ** r1) (t::t2 ** r::r2)
  in case exsistsState of
      Nothing => added'
      (Just _) => added -- add (t1 ** r1) (t2 ** r2)
    --  DPair (List (Thread N)) (\ys => Vect (length ys) Routine) -> DPair (List (Thread N)) (\zs => Vect (length zs) Routine)
    --DPair (List (Thread N)) (\zs => Vect (length zs) Routine)

allNext : List $ Thread N -> Char -> (xs: List $ Thread N ** Vect (length xs) Routine)
allNext []        c = ([] ** [])

allNext (td::tds) c =
  let ntAnr         =  map ( \(s, r) => ((s, snd td), r) ) (N .next (fst td) c) (P .next (fst td) c)
      allNext'      =  allNext tds c
  in  add ntAnr allNext'

run_rec : Word -> (tds : List $ Thread N ** Vect (length tds) Routine) -> List $ Thread N
run_rec [] (tds ** rs) = mapF (\(t,r) => execute Nothing r t) tds rs
run_rec (c::cs) (tds ** rs) =
  let newThreads  : List $ Thread N
      newThreads  = mapF (\(t,r) => ((execute (Just c) r) . (step c)) t) tds rs
  in run_rec cs (allNext newThreads c)
