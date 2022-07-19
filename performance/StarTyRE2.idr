import Data.Regex
import Data.Either

||| regex: ((a*c)|a)*b -> counts the number of a's
As : TyRE Nat
As = sum `Conv` rep0 (fromEither `Conv`
                        (length `Conv` rep0 (match 'a') <* (match 'c')) <|>
                        ((\_ => (the Nat) 1) `Conv` match 'a'))
                <* match 'b'

||| string: aa...ab
createString : Nat -> String
createString 0 = "b"
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
