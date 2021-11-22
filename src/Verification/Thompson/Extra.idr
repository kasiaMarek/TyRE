module Verification.Thompson.Extra

import Data.Vect
import Data.List
import Data.List.Elem

import Core
import NFA
import NFA.Thompson
import Verification.AcceptingPath
import Extra

%default total

export
CTh1notEqCEnd : (s : a) -> Not (CTh1 s = CEnd)
CTh1notEqCEnd s prf = absurd prf

export
CTh2notEqCEnd : (s : a) -> Not (CTh2 s = CEnd)
CTh2notEqCEnd s prf = absurd prf

export
CTh2notEqCTh1 : (s : a) -> Not (CTh1 s = CTh2 s')
CTh2notEqCTh1 s prf = absurd prf

export
injectionForCTh1 : (x : a) -> (y: a) -> (CTh1 x = CTh1 y) -> (x = y)
injectionForCTh1 x x Refl = Refl

export
injectionForCTh2 : (x : a) -> (y: a) -> (CTh2 x = CTh2 y) -> (x = y)
injectionForCTh2 x x Refl = Refl

export
ch2NotElemOFEnd : (s : a) -> (CTh2 s `Elem` [CEnd]) -> Void
ch2NotElemOFEnd s (There _) impossible

export
ch1NotElemOFEnd : (s : a) -> (CTh1 s `Elem` [CEnd]) -> Void
ch1NotElemOFEnd s (There _) impossible


-- Hack the termination checker
-- The recursion schemes below recurses on the field `oldStates`.
-- If we make it into an argument, the termination checker can see it's decreasing.
-- A bit annoying, but that'll do for now

record CombineTransitionDataWithOldStates a b c (oldStates : List c) where
  constructor MkCTDwOS
  rout1: Vect (length oldStates) Routine
  accept: c -> Bool
  conv: c -> (CState a b)
  newStart: List (CState a b)
  rout2: Vect (length newStart) Routine

cast : (oldStates' : List c) =>
  (CombineTransitionDataWithOldStates a b c oldStates') ->
  (CombineTransitionData              a b c)
cast d = MkCTD oldStates'
                 { rout1    = d.rout1
                 , accept   = d.accept
                 , conv     = d.conv
                 , newStart = d.newStart
                 , rout2    = d.rout2
                 }
cast' :
  (d : CombineTransitionData              a b c) ->
  (    CombineTransitionDataWithOldStates a b c d.oldStates)
cast' d = MkCTDwOS
         { rout1    = d.rout1
         , accept   = d.accept
         , conv     = d.conv
         , newStart = d.newStart
         , rout2    = d.rout2
         }

eta : (d : CombineTransitionData a b c) -> d === (cast @{d.oldStates} $ cast' d)
eta (MkCTD oldStates rout1 accept conv newStart rout2) = Refl

aboutCombiningTransitionsForOldAux : (oldStates : List c) -> (d : CombineTransitionDataWithOldStates a b c oldStates)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (combineTransitions $ cast d))
                        -> (oldState : c)
                        -> ((x : c) -> (y : c) -> (d.conv x = d.conv y) -> (x = y))
                        -> (d.conv oldState = state)
                        -> (Not (state `Elem` d.newStart))
                        -> (prf: oldState `Elem` oldStates **
                            extractBasedOnFst (fst $ combineTransitions $ cast d)
                                              (snd $ combineTransitions $ cast d) prf1
                                  = extractBasedOnFst oldStates d.rout1 prf)
aboutCombiningTransitionsForOldAux
  [] (MkCTDwOS [] accept conv newStart rout2) state prf1 st convInjective prf f =
    absurd prf1
aboutCombiningTransitionsForOldAux
  (x :: xs) (MkCTDwOS (y :: ys) accept conv newStart rout2)
  state prf1 st convInjective prf f with (accept x) proof p
  aboutCombiningTransitionsForOldAux
    (x :: xs) (MkCTDwOS (y :: ys) accept conv newStart rout2)
    state prf1 st convInjective prf f | True =
    case prf1 of
      Here => (replace {p=(\e => e `Elem` (x::xs))}
                  (sym $ (convInjective _ _ prf)) Here ** Refl)
      (There pos) =>
        let ctd   : CombineTransitionDataWithOldStates a b c xs
            ctd   = MkCTDwOS ys accept conv newStart rout2
            ct    : (states: List (CState a b) ** Vect (length states) Routine)
            ct    = combineTransitions (cast ctd)
        in case hereOrThereExtractBasedOnFst newStart (fst $ ct) (map (y++) rout2) (snd $ ct) pos of
          (Left (pos' ** prf')) => absurd (f pos')
          (Right (pos'** prf')) =>
            let (isElem ** rprf) =
                  aboutCombiningTransitionsForOldAux xs ctd state pos' st convInjective prf f
            in (There isElem ** trans prf' rprf)

  aboutCombiningTransitionsForOldAux
    (x :: xs) (MkCTDwOS (y :: ys) accept conv newStart rout2) state prf1 st convInjective prf f | False =
    case prf1 of
      Here => (replace {p=(\e => e `Elem` (x::xs))}
                      (sym $ (convInjective _ _ prf)) Here ** Refl)
      (There pos) =>
        let ctd   : CombineTransitionDataWithOldStates a b c xs
            ctd   = MkCTDwOS ys accept conv newStart rout2
            (isElem ** rprf) := aboutCombiningTransitionsForOldAux
                                    xs ctd state pos st convInjective prf f
        in (There isElem ** rprf)

aboutCombiningTransitionsForNewAux : (xs : List c) -> (d : CombineTransitionDataWithOldStates a b c xs)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (combineTransitions $ cast d))
                        -> ((oldState: c) -> Not (d.conv oldState = state))
                        ->  (oldState : c **
                            (prf: oldState `Elem` xs **
                            (prf2: state `Elem` d.newStart **
                            (d.accept oldState = True,
                            extractBasedOnFst (fst $ combineTransitions $ cast d)
                                              (snd $ combineTransitions $ cast d) prf1
                              = extractBasedOnFst xs d.rout1 prf
                                  ++ extractBasedOnFst d.newStart d.rout2 prf2))))

aboutCombiningTransitionsForNewAux
  [] (MkCTDwOS [] accept conv newStart rout2) state prf1 f = absurd prf1
aboutCombiningTransitionsForNewAux
  (x :: xs) (MkCTDwOS (y :: ys) accept conv newStart rout2) state prf1 f with (accept x) proof p
  aboutCombiningTransitionsForNewAux
    (x :: xs) (MkCTDwOS (y :: ys) accept conv newStart rout2) state prf1 notPrf | True =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let ctd   : CombineTransitionDataWithOldStates a b c xs
            ctd   = MkCTDwOS ys accept conv newStart rout2
            ct    : (states: List (CState a b) ** Vect (length states) Routine)
            ct    = combineTransitions $ cast ctd
        in case hereOrThereExtractBasedOnFst newStart (fst ct) (map (y++) rout2) (snd ct) pos of
          (Left (pos' ** prf)) =>
            (x ** (Here ** (pos' ** (p, trans prf (mapExtractBasedOnFst _ _ _ _)))))
          (Right (pos'** prf)) =>
              let (os ** (opos ** (npos ** (acc, eQ)))) =
                    aboutCombiningTransitionsForNewAux xs ctd state pos' notPrf
              in (os ** (There opos ** (npos ** (acc, trans prf eQ))))

  aboutCombiningTransitionsForNewAux
      (x :: xs) (MkCTDwOS (y :: ys) accept conv newStart rout2) state prf1 notPrf | False =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let ctd   : CombineTransitionDataWithOldStates a b c xs
            ctd   = MkCTDwOS ys accept conv newStart rout2
            (os ** (opos ** (npos ** (acc, eQ)))) :=
              aboutCombiningTransitionsForNewAux xs ctd state pos notPrf
        in (os ** (There opos ** (npos ** (acc, eQ))))

--Access interface for functions
public export
record CombiningTransitionsForOldData  {a, b, c: Type}
                                        (d : CombineTransitionData a b c)
                                        (state: (CState a b))
                                        (prf: state `Elem` fst (combineTransitions d))
                                        (oldState : c) where
  constructor MkCombiningTransitionsForOldData
  oldIsElemOfOld : oldState `Elem` d.oldStates
  routineEqualityPrf : (extractBasedOnFst (fst $ combineTransitions d)
                                          (snd $ combineTransitions d) prf
                          = extractBasedOnFst d.oldStates d.rout1 oldIsElemOfOld)

export
aboutCombiningTransitionsForOld : (d : CombineTransitionData a b c)
                        -> (state: (CState a b))
                        -> (prf: state `Elem` fst (combineTransitions d))
                        -> (oldState : c)
                        -> ((x : c) -> (y : c) -> (d.conv x = d.conv y) -> (x = y))
                        -> (d.conv oldState = state)
                        -> (Not (state `Elem` d.newStart))
                        -> (CombiningTransitionsForOldData d state prf oldState)

aboutCombiningTransitionsForOld d state prf1 st convInjective prf f =
  case aboutCombiningTransitionsForOldAux d.oldStates (cast' d) state
    (replace {p = \u => state `Elem` fst (combineTransitions u)} (eta d) prf1)
    st convInjective prf f of
    (isElem ** eqPrf) => MkCombiningTransitionsForOldData isElem
      (rewrite eta d in eqPrf)

public export
record CombiningTransitionsForNewData  {a, b, c: Type}
                                        (d : CombineTransitionData a b c)
                                        (state: (CState a b))
                                        (prf: state `Elem` fst (combineTransitions d)) where
  constructor MkCombiningTransitionsForNewData
  oldState : c
  oldIsElemOfOld : oldState `Elem` d.oldStates
  stateIsElemOfNew : state `Elem` d.newStart
  oldAccepts : d.accept oldState = True
  routineEqualityPrf : extractBasedOnFst  (fst $ combineTransitions d)
                                          (snd $ combineTransitions d) prf
                        = extractBasedOnFst d.oldStates d.rout1 oldIsElemOfOld
                            ++ extractBasedOnFst d.newStart d.rout2 stateIsElemOfNew

export
aboutCombiningTransitionsForNew : (d : CombineTransitionData a b c)
                        -> (state: (CState a b))
                        -> (prf: state `Elem` fst (combineTransitions d))
                        -> ((oldState: c) -> Not (d.conv oldState = state))
                        -> (CombiningTransitionsForNewData d state prf)
aboutCombiningTransitionsForNew d state prf conv =
  let (os ** (opos ** (npos ** (acc, eQ)))) :=
            aboutCombiningTransitionsForNewAux d.oldStates (cast' d) state
            (replace {p = \u => state `Elem` fst (combineTransitions u)} (eta d) prf)
            conv
  in MkCombiningTransitionsForNewData os opos npos acc
    (rewrite eta d in eQ)
