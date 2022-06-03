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

public export
record SM where
  constructor MkSM
  0 State : Type
  {auto isEq : Eq State}
  accepting : State -> Bool
  start : List (State, Routine)
  next : State -> Char -> List (State, Routine)

public export
smToNFA : SM -> NA
smToNFA sm = MkNFA sm.State {isEq = sm.isEq} sm.accepting (map fst sm.start) (\st,c => map fst (sm.next st c))

public export
record Thread (state : Type) where
  constructor MkThread
  naState : state
  vmState : VMState

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

parameters {auto sm : SM}

  public export
  initFuction : (sm.State, Routine) -> Thread sm.State
  initFuction (s,r) = MkThread s (execute Nothing r initVM)

  public export
  initialise : List (Thread sm.State)
  initialise = map initFuction sm.start

  public export
  runFunction : Char -> Thread sm.State -> (sm.State, Routine) -> Thread sm.State
  runFunction c td (st, r) = MkThread st (execute (Just c) r (step c td.vmState))

  public export
  runMapping: Char -> Thread sm.State -> List (Thread sm.State)
  runMapping c td = map (runFunction c td) (sm.next td.naState c)

  public export
  distinct : List (Thread sm.State) -> {auto eq : Eq sm.State} -> List (Thread sm.State)
  distinct [] = []
  distinct (td::tds) =
    case find (\t => t.naState == td.naState) tds of
      Nothing => td::(distinct tds)
      (Just _) => distinct tds

  public export
  runMain : Char -> List (Thread sm.State) -> List (Thread sm.State)
  runMain c tds = distinct {eq = sm.isEq} (tds >>= runMapping c)

  public export
  runFrom : Word -> (tds : List $ Thread sm.State) -> Maybe Evidence
  runFrom [] tds =  map (\td => td.vmState.evidence)
                        (findR (\td => sm.accepting td.naState) tds).Holds
  runFrom (c::cs) tds = runFrom cs $ runMain c tds

  public export
  runFromStream : (Stream Char) -> (tds : List $ Thread sm.State) -> Maybe Evidence
  runFromStream cs      []  = Nothing
  runFromStream (c::cs) tds = case (findR (\td => sm.accepting td.naState) tds).Holds of
                                      (Just td) => Just td.vmState.evidence
                                      Nothing   => runFromStream cs $ runMain c tds

  public export
  runAutomaton : Word -> Maybe Evidence
  runAutomaton word = runFrom word initialise

  public export
  runAutomatonStream : (Stream Char) -> Maybe Evidence
  runAutomatonStream stream = runFromStream stream initialise
