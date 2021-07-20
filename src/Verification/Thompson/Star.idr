module Verification.Thompson.Star

import Data.Vect
import Data.List
import Data.List.Elem
import Data.SnocList
import Data.SnocList.Extra

import Core
import NFA
import NFA.Thompson
import Verification.AcceptingPath
import Extra
import Verification.Routine
import Evidence
import Verification.Thompson.Star.EqualityPrf

export
starEvidencePrf : (re : CoreRE)
                -> (acc : Accepting (thompson $ Star re).nfa word)
                -> (accs : List (w : Word ** Accepting (thompson re).nfa w)
                      ** (extractRoutine (thompson $ Star re).nfa (thompson $ Star re).prog acc
                            = (Regular EmitEList) ::
                            (accs >>= (\ac => extractRoutine (thompson re).nfa (thompson re).prog (snd ac)))
                              ++ [Regular EmitBList]))

starEvidencePrf _ (Start (CTh2 ASt) (There Here) _) impossible
starEvidencePrf _ (Start (CTh2 ASt) (There (There _)) _) impossible
starEvidencePrf re (Start CEnd       (There Here) (Accept CEnd Refl)) = ([] ** Refl)
starEvidencePrf re (Start (CTh2 ASt) Here         x) = ?l_1
