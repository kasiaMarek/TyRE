import Data.Regex

altREType : Nat -> Type
altRE : Nat -> TyRE ()
altRE 0 = match 'a'
altRE (S k) = ignore (altRE k <|> altRE k)

getRE : Bool -> (n : Nat) -> TyRE (Either String (altREType n))
getRE True n = group (altRE n)
getRE False n = (\_ => "") `Conv` (altRE n)

main : IO ()
main =  do  isGroup <- getLine
            str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                    re := getRE (isGroup == "group") n
                in case parse re "a" of
                    Just res => putStrLn res
                    Nothing => putStrLn "Error"
              else putStrLn "Second input should be a number"