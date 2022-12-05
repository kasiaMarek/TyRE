import Data.Vect

import TyRE.NFA
import TyRE.Evidence

b : NA
b = MkNFA Nat [] (\s => \c => [])

bRejectsExamples : List Word
bRejectsExamples = map unpack ["bhcjbawc", "xua", "cewyubc"]

main : IO ()
main = do putStrLn $ show $ map (runNFA b) bRejectsExamples
