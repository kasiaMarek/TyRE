module Verification.Thompson.Common

import Core
import Thompson
import NFA
import Evidence
import Extra
import Extra.Pred

import Verification.AcceptingPath
import Verification.Routine

import Data.List.Elem

export
addEndRoutineSpecForNothing : (r : Routine) 
                            -> (xs : List (Maybe state, Routine)) 
                            -> (xInXs : Nothing `Elem` map Builtin.fst (addEndRoutine r xs))
                            -> (xInXs' : Nothing `Elem` map Builtin.fst xs **
                                  (   extractBasedOnFst (addEndRoutine r xs) xInXs 
                                  =   extractBasedOnFst xs xInXs' ++ r            ))
addEndRoutineSpecForNothing _ [] Here impossible
addEndRoutineSpecForNothing _ [] (There x) impossible
addEndRoutineSpecForNothing r ((Nothing, xr) :: xs) Here = (Here ** Refl)
addEndRoutineSpecForNothing r ((Nothing, xr) :: xs) (There pos) = 
  let (elmTail ** tail) = addEndRoutineSpecForNothing r xs pos
  in (There elmTail ** tail)
addEndRoutineSpecForNothing r ((Just x, xr) :: xs) (There pos) =
  let (elmTail ** tail) = addEndRoutineSpecForNothing r xs pos
  in (There elmTail ** tail)

export
addEndRoutineSpecForJust  : (r : Routine) 
                          -> (xs : List (Maybe state, Routine))
                          -> (x : state)
                          -> (xInXs : (Just x) `Elem` map Builtin.fst (addEndRoutine r xs))
                          -> (xInXs' : (Just x) `Elem` map Builtin.fst xs **
                                (   extractBasedOnFst (addEndRoutine r xs) xInXs 
                                =   extractBasedOnFst xs xInXs'                  ))

addEndRoutineSpecForJust _ [] st Here impossible
addEndRoutineSpecForJust _ [] st (There x) impossible
addEndRoutineSpecForJust r ((Just st, xr) :: xs) st Here = (Here ** Refl)
addEndRoutineSpecForJust r ((Nothing, xr) :: xs) st (There pos) = 
  let (elmTail ** tail) = addEndRoutineSpecForJust r xs st pos
  in (There elmTail ** tail)
addEndRoutineSpecForJust r ((Just x, xr) :: xs) st (There pos) =
  let (elmTail ** tail) = addEndRoutineSpecForJust r xs st pos
  in (There elmTail ** tail)