import API
import Core
import Codes
import NFA.Thompson
import Data.List

Exactly: Char -> CoreRE
Exactly x = Pred (\c =>  c == x)

Range: Char -> Char -> CoreRE
Range x y = Pred (\c =>  x <= c && c <= y)

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

exampleStrings : List String
exampleStrings = [
                    --match regex
                    "10:30",
                    "00:00",
                    --don't match regex
                    "03:02",
                    "45:33",
                    "o5:33"

  ]

main : IO ()
main = putStrLn $ show $ map (run Time) exampleStrings
