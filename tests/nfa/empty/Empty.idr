import NFA
import Data.Vect
import Evidence

runNFA : NA -> Word -> Bool
runNFA na word = run {N = na} word na.start

b : NA
b = MkNFA Nat (\x => False) [] (\s => \c => [])

bRejectsExamples : List Word
bRejectsExamples = map unpack ["bhcjbawc", "xua", "cewyubc"]

main : IO ()
main = do putStrLn $ show $ map (runNFA b) bRejectsExamples
