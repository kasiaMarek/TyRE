module Verification.Thompson

import Core
import Verification.AcceptingPath
import Thompson
import NFA
import Evidence

public export
thompsonPrf : (re : CoreRE)
            -> (acc: Accepting (smToNFA (thompson re)) word)
            -> (extractEvidence {sm = thompson re} acc `Encodes` [< Right $ ShapeCode re])