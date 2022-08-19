import Data.Regex

main : IO ()
main = do putStrLn $ show $ parse (r "[0-9]!") "1"
          putStrLn $ show $ parse (r "([aok][aok])!") "ok"
