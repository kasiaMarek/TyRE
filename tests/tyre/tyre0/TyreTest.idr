import API
import TyRE

regex : TyRE Integer
regex = (\x => cast x - cast '0') `Conv` rep1 (match 'a' <|> match 'b') *> range '0' '9'

main : IO ()
main = do putStrLn $ show $ parse regex "abbbaa9"
          putStrLn $ show $ parse regex "1"
          putStrLn $ show $ parse regex "a1"
          putStrLn $ show $ parse regex "abbbaa"
          putStrLn $ show $ parse regex "abbaa7"
