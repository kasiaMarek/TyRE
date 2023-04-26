import Text.Lexer
import Text.Parser.Core
import Text.Parser
import Data.List

data PToken = AChar

tokenMap : TokenMap PToken
tokenMap = [(is 'a', \x => AChar)]

Rule : Type -> Type
Rule ty = Grammar () PToken True ty

a : Rule ()
a = terminal "a" (\_ => Just ())

rightGrammar : Nat -> Rule Nat
rightGrammar 0 = map (\_ => 1) a
rightGrammar (S k) = map (\_ => 1) a <|> map (+1) (rightGrammar k)

leftGrammar : Nat -> Rule Nat
leftGrammar 0 = map (\_ => 1) a
leftGrammar (S k) = rightGrammar k <|> map (\_ => (S k)) a

run : (n : Nat) -> Either (List1 (ParsingError PToken))
                      (Nat, List (WithBounds PToken))
run n = parse (rightGrammar n) (fst (lex tokenMap "a"))

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                in case run n of
                    Right (res, _) => putStrLn $ show $ res
                    Left _ => putStrLn "Error"
              else putStrLn "Input should be a number"
