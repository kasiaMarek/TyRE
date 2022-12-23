import TyRE.CoreRE
import TyRE.Codes
import TyRE.Parser

Exactly: Char -> CoreRE
Exactly x = CharPred (Pred (\c =>  c == x))

Range: Char -> Char -> CoreRE
Range x y = CharPred (Pred (\c =>  x <= c && c <= y))

-- this is similar to time regex but allows ONLY SOME valid times
Time: CoreRE
Time =
    (
        (
          ('0' `Range` '1')
          `Concat`
          ('0' `Range` '2')
        )
        `Concat`
        (Exactly ':')
    ) `Concat`
    (
        ('0' `Range` '5')
        `Concat`
        ('0' `Range` '9')
    )

printResult : String -> IO ()
printResult str = putStrLn $ show $ parseFull Time (unpack str)

main : IO ()
main = do printResult "10:30"
          printResult "00:00"
          printResult "03:02"
          printResult "45:33"
          printResult "o5:33"
