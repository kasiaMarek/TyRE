module Examples.TimeExample

import API
import Core
import Codes
import System.REPL
import NFA.Thompson

Exactly: Char -> CoreRE
Exactly x = Pred (\c =>  c == x)

Range: Char -> Char -> CoreRE
Range x y = Pred (\c =>  x <= c && c <= y)

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
        ('1' `Range` '5')
        `Concat`
        ('0' `Range` '9')
    )

main : IO ()
main = repl "Enter a string: " (\x => (show (run Time x)) ++ "\n")
