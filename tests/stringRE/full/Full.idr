import API
import Core
import StringRE

printResult : (Maybe RE) -> String -> IO ()
printResult re str =
  let _ := showREResultCond re
  in putStrLn $ show $ runCond re str

main : IO ()
main = do printResult (r "[0-9]")                     "1"
          printResult (r "([0-9][0-9]):([0-9][0-9])") "10:30"
          printResult (r "[aok][aok]")                "ok"
          printResult (r "[aok][aok]")                "okk"
