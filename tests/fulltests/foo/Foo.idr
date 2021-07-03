import API
import Core
import Codes
import NFA.Thompson

Exactly: Char -> CoreRE
Exactly x = Pred (\c =>  c == x)

--matches only word "foo"
Foo: CoreRE
Foo = Group (((Exactly 'f') `Concat` (Exactly 'o')) `Concat` (Exactly 'o'))

printResult : String -> IO ()
printResult str = putStrLn $ show $ run Foo str

main : IO ()
main = do printResult "foo"
          printResult "fooo"
          printResult "fo"
