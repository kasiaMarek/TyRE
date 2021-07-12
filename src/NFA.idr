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
  -- | ||| Emit a unit
  --   EmitUnit
  | ||| Emit that the tape currently stores a pair
    EmitPair
  |
    EmitLeft
  |
    EmitRight
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
mapF : (f : (a,b) -> c) -> (xs : List a) -> (ys : Vect (length xs) b) -> List c
mapF f [] [] = []
mapF f (x :: xs) (y :: ys) = (f (x,y)) :: (mapF f xs ys)

public export
mapFSpec : (f : (a, b) -> c) -> (q : Pred (a,b)) -> (p : Pred c) -> (xs: List a) -> (ys: Vect (length xs) b)
        -> ((x1 : a) -> (x2 : b) -> p(f(x1, x2)) -> q (x1, x2))
        -> (y: c)
        -> (y `Elem` mapF f xs ys, p y)
        -> (x1: a ** (x2:b ** (prf: x1 `Elem` xs ** (extractBasedOnFst xs ys x1 prf = x2, f(x1, x2) = y, q (x1, x2)))))

mapFSpec f q p [] [] spec y (isElem, satP) = absurd isElem
mapFSpec f q p (x1 :: xs) (x2 :: ys) spec y (pos, satP) =
  case pos of
    Here => (x1 ** (x2 ** (Here ** (Refl, Refl, spec x1 x2 satP))))
    There pos =>
      let (x1' ** (x2' ** (pos' ** (ex', eq', satQ')))) = mapFSpec f q p xs ys spec y (pos, satP)
      in (x1' ** (x2' ** (There pos' ** (ex', eq', satQ'))))

public export
0 Step : Type
Step = VMState -> VMState

public export
step : Char -> Step
step x v = MkVMState (v.recording) (if (v.recording) then (v.memory :< x) else (v.memory)) (v.evidence)

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
stepForInstruction : (mc : Maybe Char) -> Instruction -> Step

stepForInstruction mc       Record      = startRecording
stepForInstruction mc       EmitString  = emitString
stepForInstruction mc       EmitPair    = emitPair
stepForInstruction mc       EmitLeft    = emitLeft
stepForInstruction mc       EmitRight   = emitRight
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

--implementation of initialise
public export
initFuction : (N .State, Routine) -> Thread N
initFuction (s,r) = MkThread s (execute Nothing r initVM)

public export
initialise : List (Thread N)
initialise = mapF initFuction (N .start) (P .init)

--implementation of runFrom
public export
runFunction : Char -> Thread N -> (N .State, Routine) -> Thread N
runFunction c td (st, r) = MkThread st (execute (Just c) r (step c td.vmState))

public export
runMapping: Char -> Thread N -> List (Thread N)
runMapping c td = mapF (runFunction c td) (N .next td.naState c) (P .next td.naState c)

public export
runMain: Char -> List (Thread N) -> List (Thread N)
runMain c tds = tds >>= runMapping c

public export
runFrom : Word -> (tds : List $ Thread N) -> Maybe Evidence
runFrom [] tds =  map (\td => td.vmState.evidence) (findR (\td => N .accepting td.naState) tds).Holds
runFrom (c::cs) tds = runFrom cs $ runMain c tds

public export
runAutomaton : Word -> Maybe Evidence
runAutomaton word = runFrom word initialise
