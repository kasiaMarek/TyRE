import Data.Vect

import TyRE.Parser.NFA
import TyRE.Parser.Evidence

b : NA
b = MkNFA Nat [] (\s => \c => [])

bRejectsExamples : List Word
bRejectsExamples = map unpack ["bhcjbawc", "xua", "cewyubc"]

main : IO ()
main = do putStrLn $ show $ map (runNFA b) bRejectsExamples
