> module Sheets.NFA

> import Data.Vect
> import Data.SnocList
> import Data.List

The purpose of this sheet is to start implementing automata and VM
instructions.

> ||| A non-deterministic automaton
> record NA where
>   constructor MkNFA
>   ||| States in the automaton. Can be infinite.
>   0 State : Type
>   ||| A way to compare states
>   {auto isEq : Eq State}
>   ||| Accepting states
>   accepting : State -> Bool
>   ||| Initial states
>   ||| A list since the same state might have different initialisation routines (more later).
>   start : List State
>   ||| A list since the same state might have different routines as a result of 
>   ||| combining NAs (more later).
>   next : State -> Char -> List State

> Word : Type
> Word = List Char

After we implement the NA operations, we'll look at virtual machine
instructions.

[ ] 1. Export the appropriate definitions from `Evidence` and add it
(and other project modules) to the .ipkg file. Then import `Evidence`
and erase the next line.

> data EvidenceMarker = CharMark Char
> Evidence : Type
> Evidence = SnocList EvidenceMarker

> ||| The VM we associate with an NFA can record a sub-sequence of characters 
> ||| and act on an evidence
> record VMState where
>   constructor MkVMState
>   Recording : Bool
>   memory : SnocList Char
>   evidence : Evidence

> data Instruction =
>     ||| Start recording word
>     Record
>   | ||| Emit the recorded string  
>     EmitString
>   | ||| Emit the last character
>     EmitLast
>   | ||| Emit a unit
>     EmitUnit
>   | ||| Emit that the tape currently stores a pair
>     EmitPair

> Routine : Type
> Routine = List Instruction

> ||| A program, relative to a NFA, instructs what to do as we run the automaton:
> record Program (N : NA) where
>   constructor MkProgram
>   ||| Which routine to execute when we initialise a thread at each starting state
>   init : Vect (length $ N .start) Routine
>   ||| Which routine to execute 
>   next : (st : N .State) -> (c : Char) -> Vect (length $ N .next st c) Routine


> 0 Thread : NA -> Type
> Thread na = (na.State, VMState)

[ ] 3. Since we're indexing a vector by a list, we'll need the following map:

> map : (f : (a,b) -> (c,d)) -> (xs : List a) ->
>   (ys : Vect (length xs) b) -> 
>   (xs' : List c ** Vect (length xs') d)


> infixr 4 /\
> (/\): {a: Type} -> (p : a -> Type) -> (q : a -> Type) -> a -> Type


Fix an NA:
> parameters {auto N : NA}

[ ] 2. Implement the other projection:

>   (.naState) : Thread N -> N .State
>   (.naState) = fst
>   (.vmState) : Thread N -> VMState



To avoid boilerplate: 

>   0 Step : Type
>   Step = (td : Thread N) -> Thread N
>   0 ThreadPredicate : ((td : Thread N) -> Type) -> Type
>   ThreadPredicate pred = (td : Thread N) -> pred td



[ ] 4. Implement the following functions and their specs:

>   step : Char -> Step 
>   stepMaintainsState : (c : Char) -> ThreadPredicate $
>        (\td => (step c td).naState = td.naState)
>     /\ (\td => (step c td).vmState.Recording = td.vmState.Recording)
>     /\ (\td => (step c td).vmState.evidence  = td.vmState.evidence)

We can now interpret the instructions. For example:

>   ||| Add the character to the evidence
>   emitChar : (c : Char) -> Step
>   emitChar c td = (td.naState, record {evidence $= (:< CharMark c)} td.vmState)

[ ] 5. Implement the other instructions:
>   emitString     : Step
>   startRecording : Step
>   emitPair       : Step

>   ||| Execute a routine one instruction at a time
>   execute : (mc : Maybe Char) -> Routine -> Step

NB: use `case` when you match on `c`, this will make sure the
case-tree is the right one.


[ ] 6. Prove that execution maintains the automaton's state:
>   executeMaintainsNAState : (mc : Maybe Char) -> (routine : Routine) -> ThreadPredicate $
>     \td => (execute mc routine td).naState = td.naState

[ ] 7. Implement routines for running the automaton:

>    run : Word -> Step

[ ] 8. Manually construct some automata and run them on some
inputs. Here are some examples:

a. Automaton for language accepting words with even numbers.
b. Automaton for the empty language
c. Automaton recognising the string "foo".

[ ] 9. Implement running a VM

Fix a program for our NA:
>  parameters (P : Program N)
>    initialise : List (Thread N)
>  
>  
>    runFrom : Word -> (tds : List $ Thread N) -> Maybe Evidence

[ ] 10. Implement Thompson's construction

