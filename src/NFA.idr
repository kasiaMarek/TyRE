module NFA

import Data.Vect
import Data.SnocList
import Data.List
import Data.List.Elem
import Data.Vect.Elem
import Evidence
import Pred
import Extra.Reflects
import Extra
import Data.Stream

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

public export
data Instruction =
    ||| Start recording word
    Record
  | ||| Emit the recorded string
    EmitString
  | ||| Emit the last character
    EmitLast
  | ||| Emit a unit
    EmitUnit
  | ||| Emit that the tape currently stores a pair
    EmitPair
  |
    EmitLeft
  |
    EmitRight
  |
    EmitBList
  |
    EmitEList

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
record Thread (N : NA) where
  constructor MkThread
  naState : N .State
  vmState : VMState

map : (f : (a,b) -> (c,d)) -> (xs : List a) ->
  (ys : Vect (length xs) b) ->
  (xs' : List c ** Vect (length xs') d)

map f [] [] = ([] ** [])
map f (x :: xs) (y :: ys) =
  let mp = f (x,y)
      rest = map f xs ys
  in (fst mp :: (fst rest) ** snd mp :: (snd rest))

public export
0 Step : Type
Step = VMState -> VMState

public export
step : Char -> Step
step x v = MkVMState (v.recording) (if (v.recording)
                                    then (v.memory :< x)
                                    else (v.memory)) (v.evidence)

public export
emitChar          : (c : Char) -> Step
emitChar c v      = MkVMState v.recording v.memory (v.evidence :< CharMark c)

public export
emitString        : Step
emitString v      = MkVMState False [<] (v.evidence :< GroupMark (v.memory))

public export
startRecording    : Step
startRecording v  = MkVMState True v.memory v.evidence

public export
emitPair          : Step
emitPair v        = MkVMState v.recording v.memory (v.evidence :< PairMark)

public export
emitLeft          : Step
emitLeft v        = MkVMState v.recording v.memory (v.evidence :< LeftBranchMark)

public export
emitRight          : Step
emitRight v        = MkVMState v.recording v.memory (v.evidence :< RightBranchMark)

public export
emitUnit          : Step
emitUnit v        = MkVMState v.recording v.memory (v.evidence :< UnitMark)

public export
emitBList          : Step
emitBList v        = MkVMState v.recording v.memory (v.evidence :< BList)

public export
emitEList          : Step
emitEList v        = MkVMState v.recording v.memory (v.evidence :< EList)

public export
stepForInstruction : (mc : Maybe Char) -> Instruction -> Step

stepForInstruction mc       Record      = startRecording
stepForInstruction mc       EmitString  = emitString
stepForInstruction mc       EmitPair    = emitPair
stepForInstruction mc       EmitLeft    = emitLeft
stepForInstruction mc       EmitRight   = emitRight
stepForInstruction mc       EmitUnit    = emitUnit
stepForInstruction mc       EmitBList   = emitBList
stepForInstruction mc       EmitEList   = emitEList
stepForInstruction (Just c) EmitLast    = emitChar c
stepForInstruction Nothing  EmitLast    = (\t => t)

public export
execute : (mc : Maybe Char) -> Routine -> Step
execute mc [] v = v
execute mc (x::xs) v = execute mc xs $ stepForInstruction mc x v

public export
initVM : VMState
initVM = MkVMState False [<] [<]

parameters {auto N : NA}

  public export
  run: Word -> List (N .State) -> Bool
  run [] ys = case (find (N .accepting) ys) of
                (Just _)  => True
                Nothing   => False
  run (c :: cs) ys = run cs (ys >>= (\s => N .next s c))

  parameters  {auto P : Program N}

    ||| Main body of `initialise`
    public export
    initFuction : (N .State, Routine) -> Thread N
    initFuction (s,r) = MkThread s (execute Nothing r initVM)

    public export
    initialise : List (Thread N)
    initialise = mapF initFuction (N .start) (P .init)

    ||| Main body of `runFrom`
    public export
    runFunction : Char -> Thread N -> (N .State, Routine) -> Thread N
    runFunction c td (st, r) = MkThread st (execute (Just c) r (step c td.vmState))

    public export
    runMapping: Char -> Thread N -> List (Thread N)
    runMapping c td = mapF  (runFunction c td)
                            (N .next td.naState c)
                            (P .next td.naState c)

    public export
    distinct : List (Thread N) -> List (Thread N)
    distinct [] = []
    distinct (td::tds) =
      let _ := N .isEq
      in case find (\t => t.naState == td.naState) tds of
          Nothing => td::(distinct tds)
          (Just _) => distinct tds

    public export
    runMain : Char -> List (Thread N) -> List (Thread N)
    runMain c tds = distinct (tds >>= runMapping c)

    public export
    runFrom : Word -> (tds : List $ Thread N) -> Maybe Evidence
    runFrom [] tds =  map (\td => td.vmState.evidence)
                          (findR (\td => N .accepting td.naState) tds).Holds
    runFrom (c::cs) tds = runFrom cs $ runMain c tds

    public export
    runFromStream : (Stream Char) -> (tds : List $ Thread N) -> Maybe Evidence
    runFromStream cs      []  = Nothing
    runFromStream (c::cs) tds = case (findR (\td => N .accepting td.naState) tds).Holds of
                                        (Just td) => Just td.vmState.evidence
                                        Nothing   => runFromStream cs $ runMain c tds

    public export
    runAutomaton : Word -> Maybe Evidence
    runAutomaton word = runFrom word initialise

    public export
    runAutomatonStream : (Stream Char) -> Maybe Evidence
    runAutomatonStream stream = runFromStream stream initialise
