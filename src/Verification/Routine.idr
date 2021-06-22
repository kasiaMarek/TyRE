module Verification.Routine

import NFA
import Thompson
import Verification.AcceptingPath

ExtInstruction : Type
ExtInstruction = Either Instruction Char
