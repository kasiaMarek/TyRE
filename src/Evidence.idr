module Evidence

import Codes
import Data.SnocList
import Data.SnocList.Elem
import Data.SnocList.Extra
import Data.List

%default total

public export
data EvidenceMarker =
   PairMark
 | CharMark Char
 | GroupMark (SnocList Char)
 | LeftBranchMark
 | RightBranchMark
 | UnitMark
 | BList
 | EList

public export
Evidence : Type
Evidence = SnocList EvidenceMarker

public export
data Encodes : Evidence -> SnocList (Either () Code) -> Type where
  Lin : [<] `Encodes` [<]
  AnEndMark
    : (prf : evs `Encodes` cs)
    -> (evs :< EList) `Encodes` cs :< Left ()
  AChar
    : (prf : evs `Encodes` cs)
    -> (c : Char)
    -> (evs :< CharMark c) `Encodes` cs :< (Right CharC)
  APair
    : (prf : evs `Encodes` cs)
    -> (prf1 : ev1 `Encodes` [< Right c1])
    -> (prf2 : ev2 `Encodes` [< Right c2])
    -> {auto ford : evs' = evs ++ ev1 ++ ev2}
    -> (evs' :< PairMark) `Encodes` (cs :< (Right $ PairC c1 c2))
  AGroup
    : (prf : evs `Encodes` cs)
    -> (str : SnocList Char)
    -> (evs :< GroupMark str) `Encodes` cs :< (Right StringC)
  ALeft
    : (prf : evs `Encodes` cs)
    -> (prf1 : ev1 `Encodes` [< Right c1])
    -> (c2 : Code)
    -> {auto ford : evs' = evs ++ ev1}
    -> (evs' :< LeftBranchMark) `Encodes` (cs :< (Right $ EitherC c1 c2))
  ARight
    : (prf : evs `Encodes` cs)
    -> (prf2 : ev2 `Encodes` [< Right c2])
    -> (c1 : Code)
    -> {auto ford : evs' = evs ++ ev2}
    -> (evs' :< RightBranchMark) `Encodes` (cs :< (Right $ EitherC c1 c2))
  AnEmpty
    : (prf : evs `Encodes` cs)
    -> (evs :< UnitMark) `Encodes` cs :< (Right UnitC)
  ARepetiton
    : (prf : evs `Encodes` cs)
    -> (prf1: evss `Encodes` (replicate n (Right c)))
    -> {auto ford: ev' = evs :< EList ++ evss}
    -> (ev' :< BList) `Encodes` (cs :< (Right (ListC c)))


record Result (ev : Evidence) (c : Code) (cs : SnocList (Either () Code)) where
  constructor MkResult
  result : Sem c
  rest   : Evidence
  0 restValid : rest `Encodes` cs

export
recontextualise : (prf1 : evs1 `Encodes` cs1)
              -> (prf2 : evs2 `Encodes` cs2)
              -> (evs1 ++ evs2) `Encodes` (cs1 ++ cs2)

recontextualise prf1 [<] = prf1

recontextualise prf1 (AGroup prf str) = AGroup (recontextualise prf1 prf) str

recontextualise prf1 (APair {ford = eqprf} prf prf2' prf1') =
  APair (recontextualise prf1 prf) prf2' prf1'
      {ford = trans (cong (evs1 ++) eqprf) appendAssociative}

recontextualise prf1 (AChar prf c) = AChar (recontextualise prf1 prf) c

recontextualise prf1 (ALeft {ford, ev1, evs} prf prf1' c2) =
  ALeft (recontextualise prf1 prf) prf1' c2
    {ford = trans (cong (evs1 ++) ford) appendAssociative}

recontextualise prf1 (ARight {ford, ev2, evs} prf prf2 c1) =
  ARight (recontextualise prf1 prf) prf2 c1
    {ford = trans (cong (evs1 ++) ford) appendAssociative}

recontextualise prf1 (AnEmpty prf) = AnEmpty (recontextualise prf1 prf)

recontextualise prf1 (AnEndMark prf) = AnEndMark (recontextualise prf1 prf)

recontextualise prf1 (ARepetiton {ford} prf prf') =
  ARepetiton (recontextualise prf1 prf) prf'
    {ford = trans (cong (evs1 ++) ford) appendAssociative}

helper : (0 prf : [<] `Encodes` (cs :< (Left ()) ++ (replicate n (Right c)))) -> Void
helper (AnEndMark prf) impossible
helper (AChar prf x) impossible
helper (APair prf prf1 prf2) impossible
helper (AGroup prf str) impossible
helper (ALeft prf prf1 c2) impossible
helper (ARight prf prf2 c1) impossible
helper (AnEmpty prf) impossible
helper (ARepetiton prf prf1) impossible

mutual
  extractRepRecSucc : (ev : Evidence)
                    -> (0 n : Nat)
                    -> (0 prff : n = (S k))
                    -> (0 prf : ev `Encodes` (cs :< (Left ()) ++ (replicate n (Right c))))
                    -> Result ev (ListC c) cs
  extractRepRecSucc ev {c} (S k) Refl prf =
    let res : Result ev c (cs :< (Left ()) ++ (replicate k (Right c)))
        res = extractResult ev prf
        rest : Result res.rest (ListC c) cs
        rest = extractRepRec res.rest res.restValid
    in MkResult (res.result :: rest.result) rest.rest rest.restValid

  extractRepRecAux : (ev : Evidence)
                    -> (0 prf : ev `Encodes` (cs :< (Left ()) ++ (replicate n (Right c))))
                    -> (0 prf1 : ev = ev' :< e)
                    -> (0 prf2 : e = EList -> Void)
                    -> Result ev (ListC c) cs
  extractRepRecAux (ev' :< e) {n} prf Refl prf2 =
    let 0 eqPrf : (k ** n = (S k))
        eqPrf = case n of
                      0 => case prf of
                            (AnEndMark x) => absurd (prf2 Refl)
                      (S k) => (k ** Refl)
    in extractRepRecSucc (ev' :< e) n (snd eqPrf) prf

  extractRepRec : (ev : Evidence)
                -> (0 prf : ev `Encodes` (cs :< (Left ()) ++ (replicate n (Right c))))
                -> Result ev (ListC c) cs
  extractRepRec [<] prf = absurd (helper prf)
  extractRepRec (sx :< PairMark) prf = extractRepRecAux (sx :< PairMark) prf Refl (\case _ impossible)
  extractRepRec (sx :< (CharMark x)) prf = extractRepRecAux (sx :< (CharMark x)) prf Refl (\case _ impossible)
  extractRepRec (sx :< (GroupMark sy)) prf = extractRepRecAux (sx :< (GroupMark sy)) prf Refl (\case _ impossible)
  extractRepRec (sx :< LeftBranchMark) prf = extractRepRecAux (sx :< LeftBranchMark) prf Refl (\case _ impossible)
  extractRepRec (sx :< RightBranchMark) prf = extractRepRecAux (sx :< RightBranchMark) prf Refl (\case _ impossible)
  extractRepRec (sx :< UnitMark) prf = extractRepRecAux (sx :< UnitMark) prf Refl (\case _ impossible)
  extractRepRec (sx :< BList) prf = extractRepRecAux (sx :< BList) prf Refl (\case _ impossible)
  extractRepRec (sx :< EList) {n, c} prf =
    let 0 eqPrf : (SnocList.Extra.replicate n (Right c) = [<])
        eqPrf = case n of
                  0 => Refl
                  (S k) => case prf of {_ impossible}
    in MkResult [] sx
                (case (replace
                          {p=(\r => (sx :< EList) `Encodes` (cs :< (Left ()) ++ r))}
                            eqPrf prf) of
                        (AnEndMark prf') => prf')

  extractResult : (ev : Evidence) -> (0 prf : ev `Encodes` (cs :< (Right c))) -> Result ev c cs

  extractResult (evs :< CharMark c') (AChar prf c') = MkResult c' evs prf

  extractResult (e@(evs ++ (ev1 ++ ev2)) :< PairMark) (APair {cs, c1, c2, ford=Refl} prf prf1 prf2) =
    let   0 prf1' = recontextualise (recontextualise prf prf1) prf2
          0 eqprf = sym (trans Refl appendAssociative)
          0 prf'  = replace {p=(\x => x `Encodes` (cs :< (Right c1) :< (Right  c2)))} eqprf prf1'
          result2 = extractResult e prf'
          result1 = extractResult result2.rest (result2.restValid)
    in MkResult (result1.result, result2.result) result1.rest result1.restValid

  extractResult (evs :< (GroupMark sx)) (AGroup prf sx) = MkResult (pack $ reverse $ asList sx) evs prf

  extractResult (e@(evs ++ ev) :< LeftBranchMark) (ALeft {ford = Refl} prf prf1 c2) =
    let result = extractResult e (recontextualise prf prf1)
    in MkResult (Left result.result) result.rest result.restValid

  extractResult (e@(evs ++ ev) :< RightBranchMark) (ARight {ford = Refl} prf prf2 c1) =
    let result = extractResult e (recontextualise prf prf2)
    in MkResult (Right result.result) result.rest result.restValid

  extractResult (evs :< UnitMark) (AnEmpty prf) = MkResult () evs prf

  extractResult (evs :< BList) (ARepetiton {ford, n} prf prf1) =
    let res : Result evs c cs
        res = extractRepRec evs (rewrite ford in (recontextualise (AnEndMark prf) prf1))
    in MkResult res.result res.rest res.restValid

public export
extract : (ev : Evidence) -> (0 prf : ev `Encodes` [< Right c]) -> Sem c
extract ev prf = (extractResult ev prf).result
