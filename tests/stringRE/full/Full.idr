import API
import Core
import StringRE
import CoreTyRE

main : IO ()
main = do putStrLn $ show $ parse (r "[0-9]")                     "1"
          putStrLn $ show $ parse (r "[aok][aok]")                "ok"
