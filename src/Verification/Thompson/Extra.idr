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

public export
CTh1notEqCEnd : (s : a) -> Not (CTh1 s = CEnd)
CTh1notEqCEnd s prf = absurd prf

public export
CTh2notEqCEnd : (s : a) -> Not (CTh2 s = CEnd)
CTh2notEqCEnd s prf = absurd prf

public export
CTh2notEqCTh1 : (s : a) -> Not (CTh1 s = CTh2 s')
CTh2notEqCTh1 s prf = absurd prf

public export
injectionForCTh1 : (x : a) -> (y: a) -> (CTh1 x = CTh1 y) -> (x = y)
injectionForCTh1 x x Refl = Refl

public export
injectionForCTh2 : (x : a) -> (y: a) -> (CTh2 x = CTh2 y) -> (x = y)
injectionForCTh2 x x Refl = Refl

public export
ch2NotElemOFEnd : (s : a) -> (CTh2 s `Elem` [CEnd]) -> Void
ch2NotElemOFEnd s (There _) impossible

public export
ch1NotElemOFEnd : (s : a) -> (CTh1 s `Elem` [CEnd]) -> Void
ch1NotElemOFEnd s (There _) impossible


aboutCombiningTransitionsForOldAux : (d : CombineTransitionData a b c)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (combineTransitions d))
                        -> (oldState : c)
                        -> ((x : c) -> (y : c) -> (d.conv x = d.conv y) -> (x = y))
                        -> (d.conv oldState = state)
                        -> (Not (state `Elem` d.newStart))
                        -> (prf: oldState `Elem` d.oldStates **
                            extractBasedOnFst (fst $ combineTransitions d)
                                              (snd $ combineTransitions d) prf1
                                  = extractBasedOnFst d.oldStates d.rout1 prf)

aboutCombiningTransitionsForOldAux
  (MkCTD [] [] accept conv newStart rout2) state prf1 st convInjective prf f =
    absurd prf1
aboutCombiningTransitionsForOldAux
  (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2)
  state prf1 st convInjective prf f with (accept x) proof p
  aboutCombiningTransitionsForOldAux
    (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2)
    state prf1 st convInjective prf f | True =
    case prf1 of
      Here => (replace {p=(\e => e `Elem` (x::xs))}
                  (sym $ (convInjective _ _ prf)) Here ** Refl)
      (There pos) =>
        let ctd   : CombineTransitionData a b c
            ctd   = MkCTD xs ys accept conv newStart rout2
            ct    : (states: List (CState a b) ** Vect (length states) Routine)
            ct    = combineTransitions ctd
        in case hereOrThereExtractBasedOnFst newStart (fst $ ct) (map (y++) rout2) (snd $ ct) pos of
          (Left (pos' ** prf')) => absurd (f pos')
          (Right (pos'** prf')) =>
            let (isElem ** rprf) =
                  aboutCombiningTransitionsForOldAux ctd state pos' st convInjective prf f
            in (There isElem ** trans prf' rprf)

  aboutCombiningTransitionsForOldAux
    (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 st convInjective prf f | False =
    case prf1 of
      Here => (replace {p=(\e => e `Elem` (x::xs))}
                      (sym $ (convInjective _ _ prf)) Here ** Refl)
      (There pos) =>
        let ctd   : CombineTransitionData a b c
            ctd   = MkCTD xs ys accept conv newStart rout2
            (isElem ** rprf) := aboutCombiningTransitionsForOldAux
                                    ctd state pos st convInjective prf f
        in (There isElem ** rprf)

aboutCombiningTransitionsForNewAux : (d : CombineTransitionData a b c)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (combineTransitions d))
                        -> ((oldState: c) -> Not (d.conv oldState = state))
                        ->  (oldState : c **
                            (prf: oldState `Elem` d.oldStates **
                            (prf2: state `Elem` d.newStart **
                            (d.accept oldState = True,
                            extractBasedOnFst (fst $ combineTransitions d)
                                              (snd $ combineTransitions d) prf1
                              = extractBasedOnFst d.oldStates d.rout1 prf
                                  ++ extractBasedOnFst d.newStart d.rout2 prf2))))

aboutCombiningTransitionsForNewAux
  (MkCTD [] [] accept conv newStart rout2) state prf1 f = absurd prf1
aboutCombiningTransitionsForNewAux
  (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 f with (accept x) proof p
  aboutCombiningTransitionsForNewAux
    (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 notPrf | True =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let ctd   : CombineTransitionData a b c
            ctd   = MkCTD xs ys accept conv newStart rout2
            ct    : (states: List (CState a b) ** Vect (length states) Routine)
            ct    = combineTransitions ctd
        in case hereOrThereExtractBasedOnFst newStart (fst ct) (map (y++) rout2) (snd ct) pos of
          (Left (pos' ** prf)) =>
            (x ** (Here ** (pos' ** (p, trans prf (mapExtractBasedOnFst _ _ _ _)))))
          (Right (pos'** prf)) =>
              let (os ** (opos ** (npos ** (acc, eQ)))) =
                    aboutCombiningTransitionsForNewAux ctd state pos' notPrf
              in (os ** (There opos ** (npos ** (acc, trans prf eQ))))

  aboutCombiningTransitionsForNewAux
      (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 notPrf | False =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let ctd   : CombineTransitionData a b c
            ctd   = MkCTD xs ys accept conv newStart rout2
            (os ** (opos ** (npos ** (acc, eQ)))) :=
              aboutCombiningTransitionsForNewAux ctd state pos notPrf
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
  let (isElem ** eqPrf) =
          aboutCombiningTransitionsForOldAux d state prf1 st convInjective prf f
  in MkCombiningTransitionsForOldData isElem eqPrf

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
            aboutCombiningTransitionsForNewAux d state prf conv
  in MkCombiningTransitionsForNewData os opos npos acc eQ
