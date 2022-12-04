module TyRE.Parser.API

import public TyRE.CoreRE
import TyRE.Core
import TyRE.Parser.NFA
import TyRE.Parser.Thompson
import TyRE.Parser.Evidence
import TyRE.DisjointMatches

import TyRE.Parser.Verification
import TyRE.Parser.Verification.AcceptingPath
import TyRE.Parser.Verification.Thompson

import Data.Stream

%default total

runAutomatonSM : SM -> Word -> Maybe Evidence
runAutomatonSM sm word = runAutomaton word

partial
runAutomatonSMStream : SM -> Stream Char -> Maybe (Evidence, Stream Char)
runAutomatonSMStream sm stream = runAutomatonStream stream

match : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
      -> Word -> Maybe (Shape re)
match {re} sm {prf} str with (runAutomatonSM sm str) proof p
  match {re} sm {prf} str | Nothing = Nothing
  match {re} sm {prf} str | Just ev =
    let 0 acc = extractEvidenceEquality (thompson re) str ev (rewrite prf in p)
        0 encodes = thompsonPrf re (fst acc)
    in Just $ extract ev (rewrite (sym $ snd acc) in encodes)

runWord : (re : CoreRE) -> List Char -> Maybe (Shape re)
runWord re str = match (thompson re) str

export
run : (re : CoreRE) -> String -> Maybe (Shape re)
run re str = runWord re (unpack str)

partial
matchStream : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
            -> Stream Char -> Maybe (Shape re, Stream Char)
matchStream {re} sm {prf} stm with (runAutomatonSMStream sm stm) proof p
  matchStream {re} sm {prf} stm | Nothing = Nothing
  matchStream {re} sm {prf} stm | Just (ev, stmTail) =
    let 0 stmEq := eqForStream (thompson re) stm
        0 acc := extractEvidenceEquality (thompson re) (fst stmEq) ev (trans (snd stmEq) (rewrite prf in (cong (map fst) p)))
        0 encodes := thompsonPrf re (fst acc)
    in Just (extract ev (rewrite (sym $ snd acc) in encodes), stmTail)

partial
matchStreamGreedy : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
                  -> Stream Char -> Maybe (Shape re, Stream Char)
matchStreamGreedy {re} sm {prf} stm with (runAutomatonStreamGreedy {sm} stm) proof p
  matchStreamGreedy {re} sm {prf} stm | Nothing = Nothing
  matchStreamGreedy {re} sm {prf} stm | Just (ev, stmTail) =
    let 0 stmEq := eqForStreamGreedy (thompson re) stm
        0 acc := extractEvidenceEquality  (thompson re)
                                          (fst stmEq)
                                          ev
                                          (trans  (snd stmEq)
                                                  (rewrite prf in (cong (map fst) p)))
        0 encodes := thompsonPrf re (fst acc)
    in Just (extract ev (rewrite (sym $ snd acc) in encodes), stmTail)

export
partial
getTokenCore : (re : CoreRE) -> Stream Char -> Bool -> Maybe (Shape re, Stream Char)
getTokenCore re stm False = matchStream       (thompson re) stm
getTokenCore re stm True  = matchStreamGreedy (thompson re) stm

matchPrefix : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
            -> Word -> Maybe (Shape re, Word)
matchPrefix {re} sm {prf} stm with (runAutomatonPrefix stm) proof p
  matchPrefix {re} sm {prf} stm | Nothing = Nothing
  matchPrefix {re} sm {prf} stm | Just (ev, stmTail) =
    let 0 stmEq := eqForPrefix (thompson re) stm
        0 acc := 
          extractEvidenceEquality (thompson re)
                                  (fst stmEq)
                                  ev
                                  (trans  (snd stmEq)
                                          (rewrite prf in (cong (map fst) p)))
        0 encodes := thompsonPrf re (fst acc)
    in Just (extract ev (rewrite (sym $ snd acc) in encodes), stmTail)

matchPrefixGreedy : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
            -> Word -> Maybe (Shape re, Word)
matchPrefixGreedy {re} sm {prf} cs with (runAutomatonPrefixGreedy cs) proof p
  matchPrefixGreedy {re} sm {prf} cs | Nothing = Nothing
  matchPrefixGreedy {re} sm {prf} cs | Just (ev, stmTail) =
    let 0 stmEq := eqForPrefixGreedy (thompson re) cs
        0 acc := extractEvidenceEquality  (thompson re)
                                          (fst stmEq)
                                          ev
                                          (trans  (snd stmEq)
                                                  (rewrite prf in (cong (map fst) p)))
        0 encodes := thompsonPrf re (fst acc)
    in Just (extract ev (rewrite (sym $ snd acc) in encodes), stmTail)

partial -- we should be able to prove this to be total thanks to consuming
asDisjoinMatchesFrom : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
                    -> {auto 0 consuming : IsConsuming re}
                    -> Word -> DisjointMatchesSnoc (Shape re)
                    -> (greedy : Bool)
                    -> DisjointMatchesSnoc (Shape re)
asDisjoinMatchesFrom sm [] dm greedy = dm
asDisjoinMatchesFrom sm {prf} (c :: cs) dm greedy = 
  let f : {re : CoreRE} -> (sm : SM) -> {auto prf : thompson re = sm}
            -> Word -> Maybe (Shape re, Word)
      f = case greedy of False => matchPrefix ; True => matchPrefixGreedy
  in case (f sm {prf} (c :: cs)) of
    Nothing => asDisjoinMatchesFrom sm cs (dm :< c) greedy
    (Just (parse, tail)) => asDisjoinMatchesFrom sm tail (dm :+: parse) greedy

export
partial
asDisjoinMatchesCore : (re : CoreRE) -> {auto 0 consuming : IsConsuming re}
                    -> String -> Bool -> DisjointMatches (Shape re)
asDisjoinMatchesCore re str greedy
  = cast $ asDisjoinMatchesFrom {re} (thompson re) (unpack str) (Prefix [<]) greedy

export
parsePrefix : (re : CoreRE) -> String -> Maybe (Shape re, String)
parsePrefix re cs = map (bimap id pack)
                        (matchPrefixGreedy {re} (thompson re) (unpack cs))
