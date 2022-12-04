import Data.Regex

main : IO ()
main = do putStrLn $ show $ parse2 (r "[0-9]!") "1"
          putStrLn $ show $ parse2 (r "([aok][aok])!") "ok"
          putStrLn $ show $ parse2 (r "[a-z]+") "a"