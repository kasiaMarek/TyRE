import API
import Core
import Codes
import NFA.Thompson

AorB : CoreRE
AorB = Pred (\c =>  (c == 'a' || c == 'b'))

--matches only word "foo"
Ab: CoreRE
Ab = (Group (AorB `Concat` AorB)) `Concat` AorB

printResult : String -> IO ()
printResult str = putStrLn $ show $ run Ab str

main : IO ()
main = do printResult "bab"
          printResult "bba"
          printResult "aaa"
          printResult "aac"
          printResult "aaaa"
          printResult "ab"
