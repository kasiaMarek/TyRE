import TyRE.CoreRE
import TyRE.Codes
import TyRE.Parser

import Data.SnocList

AorB : CoreRE
AorB = CharPred (Pred (\c =>  (c == 'a' || c == 'b')))

AOrBStar: CoreRE
AOrBStar = Star AorB

printResult : String -> IO ()
printResult str = putStrLn $ show $ parseFull AOrBStar (unpack str)

main : IO ()
main = do printResult "bab"
          printResult "bba"
          printResult "aaa"
          printResult "aac"
          printResult "aaaa"
