import Data.Regex
import TyRE.Parser

AorB : CoreRE
AorB = CharPred (Pred (\c =>  (c == 'a' || c == 'b')))

--matches only word "foo"
Ab : CoreRE
Ab = Group (AorB `Concat` AorB) `Concat` AorB

printResult : String -> IO ()
printResult str = putStrLn $ show $ parseFull Ab (unpack str)

main : IO ()
main = do printResult "bab"
          printResult "bba"
          printResult "aaa"
          printResult "aac"
          printResult "aaaa"
          printResult "ab"
