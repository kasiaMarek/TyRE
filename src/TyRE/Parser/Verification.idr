module TyRE.Parser.Verification

import Data.List.Elem
import Data.List
import Data.Stream
import Data.Maybe
import Data.List.Quantifiers

import TyRE.Extra
import TyRE.Extra.Pred
import TyRE.Extra.Reflects
import TyRE.Parser.NFA
import TyRE.Parser.Evidence
import TyRE.Parser.Verification.AcceptingPath

recordPathHelper  : {auto sm: SM} -> (c: Char) -> (td : Thread sm.State)
                  ->  (td': Thread sm.State 
                      ** (td' `Elem` runMapping c td,
                            (acc: AcceptingFrom (smToNFA sm) td'.naState cs
                            ** extractEvidenceFrom td' acc = ev)))
                  ->  (acc: AcceptingFrom (smToNFA sm) td.naState (c::cs)
                      ** extractEvidenceFrom td acc = ev)

recordPathHelper c (MkThread (Just st) vm) (td' ** (isElemOfF, (accepts ** isEq))) =
  let (x1 ** (x2 ** (isElem ** (eqToExtractFst, ftd', satQ)))) =
        mapSpec (runFunction c (MkThread (Just st) vm))
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

recordPathHelper c td@(MkThread Nothing vm) (td' ** (isElemOfF, (accepts ** isEq)))
  = absurd isElemOfF

isElemDistinct : {auto sm : SM}
              -> (tds : List (Thread sm.State)) 
              -> (td : Thread sm.State)
              -> (prf : td `Elem` distinct {eq = sm.isEq} tds)
              -> (td `Elem` tds)

isElemDistinct [] td prf = absurd prf
isElemDistinct {sm} (t :: tds) td prf with (sm.isEq) proof p
               | (find (\e => e.naState == t.naState) tds)
  isElemDistinct {sm} (t :: tds) t Here | _ | Nothing = Here
  isElemDistinct {sm} (t :: tds) td (There pos) | eq | Nothing =
    There (isElemDistinct tds td (rewrite p in pos))
  isElemDistinct {sm} (t :: tds) td pos | _ | (Just _) =
    There (isElemDistinct tds td (rewrite p in pos))

0 recordPath : {auto sm : SM} -> (tds : List (Thread sm.State)) -> (str : Word)
          -> (prf : runFrom str tds = Just ev)
          -> (td : Thread sm.State 
                ** (td `Elem` tds, (acc : AcceptingFrom (smToNFA sm) td.naState str
                                        ** extractEvidenceFrom td acc = ev)))

recordPath tds [] prf with (findR (\td => isNothing td.naState) tds)
  recordPath tds [] prf | (Nothing `Because` (Otherwise f)) = absurd prf
  recordPath tds [] prf
             | ((Just (MkThread Nothing vm)) `Because` (Indeed (pos, Refl)))
    = ((MkThread Nothing vm) ** (pos, (Accept {nfa = (smToNFA sm)} ** eqForJust prf)))
  recordPath tds [] prf
             | ((Just (MkThread (Just st) vm)) `Because` (Indeed (pos, isEq)))
    = absurd isEq

recordPath {sm} tds (c :: cs) prf =
  let (td' ** (pos', (acc' ** isEq'))) = recordPath _ cs prf
      (x ** (isElem, satQ , _)) =
        bindSpec
          (runMapping c)
          (\e => (acc: AcceptingFrom (smToNFA sm) e.naState cs
            ** extractEvidenceFrom e acc = ev))
          (\e => (acc: AcceptingFrom (smToNFA sm) e.naState (c :: cs)
            ** extractEvidenceFrom e acc = ev))
          (recordPathHelper c)
          tds
          (td' ** (isElemDistinct _ _ pos', (acc' ** isEq')))
  in (x ** (isElem, satQ))

public export
0 extractEvidenceEquality :  (sm  : SM)
                          -> (str : Word)
                          -> (ev  : Evidence)
                          -> (prf : runAutomaton str = Just ev)
                          -> (acc : Accepting (smToNFA sm) str 
                                  ** extractEvidence acc = ev)

extractEvidenceEquality sm str ev prf =
  let (td ** (pos, (acc ** eq))) = recordPath (NFA.initialise) str prf
      (x1 ** (x2 ** (isElem ** (eqToExtractFst, ftd', satQ))))
        = mapSpec (initFuction)
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

  in  (Start {nfa = (smToNFA sm)} td.naState (rewrite satQ in isElem) acc
      ** (rewrite prf in eq))


0 eqForStreamFrom :  (sm : SM)
                  -> (stm : Stream Char)
                  -> (tds : List (Thread sm.State))
                  -> (str : Word ** runFrom str tds
                                  = map Builtin.fst (runFromStream stm tds))
eqForStreamFrom sm stm []   = ([] ** Refl)
eqForStreamFrom sm (c::cs) (t::tds) 
                with (findR (\td => isNothing td.naState) (t::tds)) proof p
  eqForStreamFrom sm (c::cs) (t::tds) | ((Just x) `Because` _) 
    = ([] ** rewrite p in Refl)
  eqForStreamFrom sm (c::cs) (t::tds) | (Nothing `Because` _) =
    let nextTds : List (Thread sm.State)
        nextTds = runMain c (t::tds)
        rest : (str : Word ** runFrom str nextTds
                            = map Builtin.fst (runFromStream cs nextTds))
        rest = eqForStreamFrom sm cs nextTds
        (wordTail ** eqRest) := rest
    in (c::wordTail ** eqRest)

public export
0 eqForStream :  (sm : SM)
              -> (stm : Stream Char)
              -> (str : Word ** runAutomaton str 
                              = map Builtin.fst (runAutomatonStream stm))
eqForStream sm stm = eqForStreamFrom sm stm initialise

0 eqForPrefixFrom :  (sm : SM)
                  -> (stm : Word)
                  -> (tds : List (Thread sm.State))
                  -> (str : Word ** runFrom str tds
                                  = map Builtin.fst (runFromPrefix stm tds))
eqForPrefixFrom sm stm []   = ([] ** Refl)
eqForPrefixFrom sm cs (t::tds) with
    (findR (\td => isNothing td.naState) (t::tds)) proof p
  eqForPrefixFrom sm cs (t::tds) | ((Just x) `Because` _) = ([] ** rewrite p in Refl)
  eqForPrefixFrom sm [] (t::tds) | (Nothing `Because` _) = ([] ** rewrite p in Refl)
  eqForPrefixFrom sm (c :: cs) (t::tds) | (Nothing `Because` _) =
    let nextTds : List (Thread sm.State)
        nextTds = runMain c (t::tds)
        rest : (str : Word ** runFrom str nextTds 
                            = map Builtin.fst (runFromPrefix cs nextTds))
        rest = eqForPrefixFrom sm cs nextTds
        (wordTail ** eqRest) := rest
    in (c::wordTail ** eqRest)

public export
0 eqForPrefix :  (sm : SM)
              -> (stm : Word)
              -> (str : Word ** runAutomaton str 
                              = map Builtin.fst (runAutomatonPrefix stm))
eqForPrefix sm stm = eqForPrefixFrom sm stm initialise


record Result (sm : SM) (T : Type) where
  constructor MkResult
  res : (Evidence, T)
  tds : List (Thread sm.State)
  word : Word
  prf : runFrom word tds = (Just $ fst res)

0 eqForPrefixFromGreedy
  :  (sm : SM)
  -> (cs : Word)
  -> (mres : Maybe (Result sm Word))
  -> (tds : List (Thread sm.State))
  -> (str : Word **
      Either  (runFrom str tds 
                = map Builtin.fst (runFromPrefixGreedy cs tds (map (.res) mres)))
              (isJust : IsJust mres **
                  runFrom str (fromJust mres).tds
                    = map Builtin.fst (runFromPrefixGreedy cs tds (map (.res) mres))))

eqForPrefixFromGreedy sm cs Nothing [] = ([] ** Left Refl)

eqForPrefixFromGreedy sm cs (Just (MkResult res tds word prf)) []
  = (word ** Right (ItIsJust ** prf))

eqForPrefixFromGreedy sm [] Nothing (t :: tds)
                      with (findR (\td => isNothing td.naState) (t::tds)) proof p
  eqForPrefixFromGreedy sm [] Nothing (t :: tds) | ((Just td) `Because` _)
    = ([] ** Left (rewrite p in Refl))
  eqForPrefixFromGreedy sm [] Nothing (t :: tds) | (Nothing `Because` _)
    = ([] ** Left (rewrite p in Refl))

eqForPrefixFromGreedy sm [] (Just y) (t :: tds)
                      with (findR (\td => isNothing td.naState) (t::tds)) proof p
    eqForPrefixFromGreedy sm [] (Just y) (t :: tds) | ((Just td) `Because` _)
      = ([] ** Left (rewrite p in Refl))
    eqForPrefixFromGreedy sm [] (Just (MkResult res xs word prf)) (t :: tds)
      | (Nothing `Because` _)
      = (word ** Right (ItIsJust ** prf))

eqForPrefixFromGreedy sm (c :: cs) res (t :: tds)
                      with (findR (\td => isNothing td.naState) (t::tds)) proof p
    eqForPrefixFromGreedy sm (c :: cs) res (t :: tds) | ((Just td) `Because` _)
      = case eqForPrefixFromGreedy sm cs 
                (Just $ MkResult  (td.vmState.evidence, c::cs)
                                  (t :: tds)
                                  []
                                  (rewrite p in Refl))
                (runMain c (t::tds)) of
          (word ** (Left prf)) => (c::word ** (Left prf))
          (word ** (Right (_ ** prf))) => (word ** Left prf)
    eqForPrefixFromGreedy sm (c :: cs) res (t :: tds) | (Nothing `Because` _)
      = case eqForPrefixFromGreedy sm cs res (runMain c (t::tds)) of
          (word ** (Left prf)) => (c::word ** (Left prf))
          (word ** (Right (ItIsJust ** prf))) => (word ** Right (ItIsJust ** prf))

export
0 eqForPrefixGreedy :  (sm : SM)
                    -> (cs : Word)
                    -> (str : Word ** runAutomaton str 
                              = map Builtin.fst (runAutomatonPrefixGreedy cs))
eqForPrefixGreedy sm cs =
  let (word ** res) := eqForPrefixFromGreedy sm cs Nothing initialise
  in case res of
    (Left eq) => (word ** eq)
    (Right (isJust, _)) impossible


0 eqForStreamGreedyFrom
  :  (sm : SM)
  -> (cs : Stream Char)
  -> (mres : Maybe (Result sm (Stream Char)))
  -> (tds : List (Thread sm.State))
  -> (str : Word **
      Either  (runFrom str tds 
                = map Builtin.fst (runFromStreamGreedy cs tds (map (.res) mres)))
              (isJust : IsJust mres **
                  runFrom str (fromJust mres).tds
                    = map Builtin.fst (runFromStreamGreedy cs tds (map (.res) mres))))

eqForStreamGreedyFrom sm cs Nothing [] = ([] ** Left Refl)
eqForStreamGreedyFrom sm cs (Just (MkResult res tds word prf)) []
  = (word ** Right (ItIsJust ** prf))
eqForStreamGreedyFrom sm (c :: cs) mres (t :: tds)
                      with (findR (\td => isNothing td.naState) (t::tds)) proof p
  eqForStreamGreedyFrom sm (c :: cs) mres (t :: tds) | ((Just td) `Because` _)
    = case eqForStreamGreedyFrom sm cs 
                (Just $ MkResult  (td.vmState.evidence, c::cs)
                                  (t :: tds)
                                  []
                                  (rewrite p in Refl))
                (runMain c (t::tds)) of
        (word ** (Left prf)) => (c::word ** (Left prf))
        (word ** (Right (_ ** prf))) => (word ** Left prf)
  eqForStreamGreedyFrom sm (c :: cs) mres (t :: tds) | (Nothing `Because` _)
    = case eqForStreamGreedyFrom sm cs mres (runMain c (t::tds)) of
        (word ** (Left prf)) => (c::word ** (Left prf))
        (word ** (Right (ItIsJust ** prf))) => (word ** Right (ItIsJust ** prf))


export
0 eqForStreamGreedy :  (sm : SM)
                    -> (cs : Stream Char)
                    -> (str : Word ** runAutomaton str 
                              = map Builtin.fst (runAutomatonStreamGreedy cs))
eqForStreamGreedy sm cs =
  let (word ** res) := eqForStreamGreedyFrom sm cs Nothing initialise
  in case res of
    (Left eq) => (word ** eq)
    (Right (isJust, _)) impossible