import API
import Core
import StringRE

printResult : RE -> String -> IO ()
printResult re str = case run (compile re) str of
                          Nothing => putStrLn "Nothing"
                          (Just res) => putStrLn $ showAux res

main : IO ()
main = do printResult (r "[0-9]")                     "1"
          printResult (r "([0-9][0-9]):([0-9][0-9])") "10:30"
          printResult (r "[aok][aok]")                "ok"
          printResult (r "[aok][aok]")                "okk"
