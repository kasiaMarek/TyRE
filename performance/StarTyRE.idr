import Data.Regex

As : TyRE Nat
As = compile $ Rep0 $ Exactly 'a'

createString : Nat -> String
createString 0 = "a"
createString (S k) = "a" ++ (createString k)

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                in case parse As (createString n) of
                    Just res => putStrLn $ show $ res
                    Nothing => putStrLn "Error"
              else putStrLn "Input is not a number"
