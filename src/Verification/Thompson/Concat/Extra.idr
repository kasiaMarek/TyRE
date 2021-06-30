module Verification.Thompson.Concat.Extra

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
0 aboutCombiningTransitionsForOldType : (d : CombineTransitionData a b c)
                          -> (state: (CState a b))
                          -> (prf1: state `Elem` fst (combineTransitions d))
                          -> (oldState : c)
                          -> Type

aboutCombiningTransitionsForOldType {a,b,c} d state prf1 oldState =
  (prf: oldState `Elem` d.oldStates
        ** extractBasedOnFst (fst $ combineTransitions d) (snd $ combineTransitions d) state prf1
            = extractBasedOnFst d.oldStates d.rout1 oldState prf)

public export
aboutCombiningTransitionsForOld : (d : CombineTransitionData a b c)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (combineTransitions d))
                        -> (oldState : c)
                        -> ((x : c) -> (y : c) -> (d.conv x = d.conv y) -> (x = y))
                        -> (d.conv oldState = state)
                        -> (Not (state `Elem` d.newStart))
                        -> (aboutCombiningTransitionsForOldType d state prf1 oldState)

aboutCombiningTransitionsForOld (MkCTD [] [] accept conv newStart rout2) state prf1 st convInjective prf f = absurd prf1
aboutCombiningTransitionsForOld (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 st convInjective prf f with (accept x) proof p
  aboutCombiningTransitionsForOld (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 st convInjective prf f | True =
    case prf1 of
      Here => (replace {p=(\e => e `Elem` (x::xs))} (sym $ (convInjective _ _ prf)) Here ** Refl)
      (There pos) =>
        let ctd   : CombineTransitionData a b c
            ctd   = MkCTD xs ys accept conv newStart rout2
            ct    : (states: List (CState a b) ** Vect (length states) Routine)
            ct    = combineTransitions ctd
            hOrT  := hereOrThereExtractBasedOnFst newStart (fst $ ct) (map (y++) rout2) (snd $ ct) state pos
        in case hOrT of
          (Left (pos' ** prf')) => absurd (f pos')
          (Right (pos'** prf')) =>
            let (isElem ** rprf) = aboutCombiningTransitionsForOld ctd state pos' st convInjective prf f
            in (There isElem ** trans prf' rprf)

  aboutCombiningTransitionsForOld (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 st convInjective prf f | False =
    case prf1 of
      Here => (replace {p=(\e => e `Elem` (x::xs))} (sym $ (convInjective _ _ prf)) Here ** Refl)
      (There pos) =>
        let ctd   : CombineTransitionData a b c
            ctd   = MkCTD xs ys accept conv newStart rout2
            (isElem ** rprf) := aboutCombiningTransitionsForOld ctd state pos st convInjective prf f
        in (There isElem ** rprf)

public export
0 aboutCombiningTransitionsForNewType : (d : CombineTransitionData a b c)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (combineTransitions d)) -> Type

aboutCombiningTransitionsForNewType {a,b,c} d state prf1 =
  (oldState : c
      ** (prf: oldState `Elem` d.oldStates
      ** (prf2: state `Elem` d.newStart
      ** (d.accept oldState = True,
      extractBasedOnFst (fst $ combineTransitions d) (snd $ combineTransitions d) state prf1
        = extractBasedOnFst d.oldStates d.rout1 oldState prf
            ++ extractBasedOnFst d.newStart d.rout2 state prf2))))

-- record AboutCombiningTransitionsForNew a b c
--           (d : CombineTransitionData a b c)
--           (state: (CState a b))
--           (prf1: state `Elem` fst (combineTransitions d)) where
--   constructor MkAboutCombiningTransitionsForNew
--   oldState : c
--   oldIsElemOfOld : oldState `Elem` d.oldStates
--   stateIsElemOfNew : state `Elem` d.newStart
--   oldAccepts : d.accept oldState = True
--   routineEqualityPrf : extractBasedOnFst (fst $ combineTransitions d) (snd $ combineTransitions d) state prf1
--                         = extractBasedOnFst d.oldStates d.rout1 oldState oldIsElemOfOld
--                             ++ extractBasedOnFst d.newStart d.rout2 state stateIsElemOfNew

public export
aboutCombiningTransitionsForNew : (d : CombineTransitionData a b c)
                        -> (state: (CState a b))
                        -> (prf1: state `Elem` fst (combineTransitions d))
                        -> ((oldState: c) -> Not (d.conv oldState = state))
                        -> (aboutCombiningTransitionsForNewType d state prf1)

aboutCombiningTransitionsForNew (MkCTD [] [] accept conv newStart rout2) state prf1 f = absurd prf1
aboutCombiningTransitionsForNew (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 f with (accept x) proof p
  aboutCombiningTransitionsForNew (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 notPrf | True =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let ctd   : CombineTransitionData a b c
            ctd   = MkCTD xs ys accept conv newStart rout2
            ct    : (states: List (CState a b) ** Vect (length states) Routine)
            ct    = combineTransitions ctd
            hOrT := hereOrThereExtractBasedOnFst newStart (fst ct) (map (y++) rout2) (snd $ ct) state pos
        in case hOrT of
          (Left (pos' ** prf)) => (x ** (Here ** (pos' ** (p, trans prf (mapExtractBasedOnFst _ _ _ _ _)))))
          (Right (pos'** prf)) =>
              let (os ** (opos ** (npos ** (acc, eQ)))) = aboutCombiningTransitionsForNew ctd state pos' notPrf
              in (os ** (There opos ** (npos ** (acc, trans prf eQ))))

  aboutCombiningTransitionsForNew (MkCTD (x :: xs) (y :: ys) accept conv newStart rout2) state prf1 notPrf | False =
    case prf1 of
      Here => absurd (notPrf x Refl)
      (There pos) =>
        let ctd   : CombineTransitionData a b c
            ctd   = MkCTD xs ys accept conv newStart rout2
            (os ** (opos ** (npos ** (acc, eQ)))) := aboutCombiningTransitionsForNew ctd state pos notPrf
        in (os ** (There opos ** (npos ** (acc, eQ))))
