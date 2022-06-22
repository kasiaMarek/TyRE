module Verification

import Extra
import Extra.Pred
import Extra.Reflects
import NFA
import Evidence
import Verification.AcceptingPath

import Data.List.Elem
import Data.List
import Data.Stream
import Data.Maybe

recordPathHelper : {auto sm: SM} -> (c: Char) -> (td : Thread sm.State)
              -> (td': Thread sm.State ** (td' `Elem` runMapping c td, (acc: AcceptingFrom (smToNFA sm) td'.naState cs ** extractEvidenceFrom td' acc = ev)))
              -> (acc: AcceptingFrom (smToNFA sm) td.naState (c::cs) ** extractEvidenceFrom td acc = ev)

recordPathHelper c (MkThread (Just st) vm) (td' ** (isElemOfF, (accepts ** isEq))) =
  let (x1 ** (x2 ** (isElem ** (eqToExtractFst, ftd', satQ)))) = mapSpec
                                              (runFunction c (MkThread (Just st) vm))
                                              (\e => (td'.naState = fst e))
                                              (\t => (td'.naState = t.naState))
                                              (sm .next st c)
                                              (\x1 => \x2 => \p => p)
                                              td'
                                              (isElemOfF, Refl)
      isElem' : td'.naState `Elem` (liftNext (smToNFA sm).next (Just st) c)
      isElem' = (rewrite satQ in isElem)

      acc : AcceptingFrom (smToNFA sm) (Just st) (c::cs)
      acc = Step {nfa = (smToNFA sm)} st c td'.naState isElem' accepts

      prf : (stepOfExtractEvidence (MkThread (Just st) vm) c td'.naState isElem' = td')
      prf = rewrite satQ in rewrite eqToExtractFst in ftd'
  in (acc ** rewrite prf in isEq)

recordPathHelper c td@(MkThread Nothing vm) (td' ** (isElemOfF, (accepts ** isEq))) = absurd isElemOfF

isElemDistinct : {auto sm : SM}
              -> (tds : List (Thread sm.State)) 
              -> (td : Thread sm.State)
              -> (prf : td `Elem` distinct {eq = sm.isEq} tds)
              -> (td `Elem` tds)

isElemDistinct [] td prf = absurd prf
isElemDistinct {sm} (t :: tds) td prf with (sm.isEq) proof p | (find (\e => e.naState == t.naState) tds)
  isElemDistinct {sm} (t :: tds) t Here | _ | Nothing = Here
  isElemDistinct {sm} (t :: tds) td (There pos) | eq | Nothing =
    There (isElemDistinct tds td (rewrite p in pos))
  isElemDistinct {sm} (t :: tds) td pos | _ | (Just _) =
    There (isElemDistinct tds td (rewrite p in pos))

0 recordPath : {auto sm : SM} -> (tds : List (Thread sm.State)) -> (str : Word)
          -> (prf : runFrom str tds = Just ev)
          -> (td : Thread sm.State ** (td `Elem` tds, (acc: AcceptingFrom (smToNFA sm) td.naState  str ** extractEvidenceFrom td acc = ev)))

recordPath tds [] prf with (findR (\td => isNothing td.naState) tds)
  recordPath tds [] prf | (Nothing `Because` (Otherwise f)) = absurd prf
  recordPath tds [] prf | ((Just (MkThread Nothing vm)) `Because` (Indeed (pos, Refl))) = ((MkThread Nothing vm) ** (pos, (Accept {nfa = (smToNFA sm)} ** eqForJust prf)))
  recordPath tds [] prf | ((Just (MkThread (Just st) vm)) `Because` (Indeed (pos, isEq))) = absurd isEq

recordPath {sm} tds (c :: cs) prf =
  let (td' ** (pos', (acc' ** isEq'))) = recordPath _ cs prf
      (x ** (isElem, satQ , _)) =
        bindSpec
          (runMapping c)
          (\e => (acc: AcceptingFrom (smToNFA sm) e.naState cs ** extractEvidenceFrom e acc = ev))
          (\e => (acc: AcceptingFrom (smToNFA sm) e.naState (c :: cs) ** extractEvidenceFrom e acc = ev))
          (recordPathHelper c)
          tds
          (td' ** (isElemDistinct _ _ pos', (acc' ** isEq')))
  in (x ** (isElem, satQ))

public export
0 extractEvidenceEquality : (sm : SM)
                        -> (str : Word)
                        -> (ev : Evidence)
                        -> (prf : runAutomaton str = Just ev)
                        -> (acc: Accepting (smToNFA sm) str ** extractEvidence acc = ev)

extractEvidenceEquality sm str ev prf =
  let (td ** (pos, (acc ** eq))) = recordPath (NFA.initialise) str prf
      (x1 ** (x2 ** (isElem ** (eqToExtractFst, ftd', satQ)))) = mapSpec
                                                                  (initFuction)
                                                                  (\e => (td.naState = fst e))
                                                                  (\t => (td.naState = t.naState))
                                                                  (sm .start)
                                                                  (\x1 => \x2 => \p => p)
                                                                  td
                                                                  (pos, Refl)
      acc' : AcceptingFrom (smToNFA sm) x1 str
      acc' = replace {p=(\s => AcceptingFrom (smToNFA sm) s str)} satQ acc

      isElem' : td.naState `Elem` (smToNFA sm).start
      isElem' = replace {p=(\s => s `Elem` (smToNFA sm).start)} (sym satQ) isElem

      prf : (extractEvidenceInitialStep td.naState isElem' = td)
      prf = rewrite satQ in rewrite eqToExtractFst in ftd'

  in (Start {nfa = (smToNFA sm)} td.naState (rewrite satQ in isElem) acc ** (rewrite prf in eq))


0 eqForStreamFrom :  (sm : SM)
                  -> (stm : Stream Char)
                  -> (tds : List (Thread sm.State))
                  -> (str : Word ** runFrom str tds = runFromStream stm tds)
eqForStreamFrom sm stm []   = ([] ** Refl)
eqForStreamFrom sm (c::cs) (t::tds) with (findR (\td => isNothing td.naState) (t::tds)) proof p
  eqForStreamFrom sm (c::cs) (t::tds) | ((Just x) `Because` _) = ([] ** rewrite p in Refl)
  eqForStreamFrom sm (c::cs) (t::tds) | (Nothing `Because` _) =
    let nextTds : List (Thread sm.State)
        nextTds = runMain c (t::tds)
        rest : (str : Word ** runFrom str nextTds = runFromStream cs nextTds)
        rest = eqForStreamFrom sm cs nextTds
        (wordTail ** eqRest) := rest
    in (c::wordTail ** eqRest)

public export
0 eqForStream :  (sm : SM)
              -> (stm : Stream Char)
              -> (str : Word ** runAutomaton str = runAutomatonStream stm)
eqForStream sm stm = eqForStreamFrom sm stm initialise
