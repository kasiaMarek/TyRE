import Text.Lexer
import public Text.Parser.Core
import public Text.Parser
import Data.List

data PToken = AChar

tokenMap : TokenMap PToken
tokenMap = [(is 'a', \x => AChar)]

Rule : Type -> Type
Rule ty = Grammar (TokenData PToken) True ty

a : Rule ()
a = terminal "a" (\(MkToken _ _ tok) => case tok of {AChar => Just (); _ => Nothing})

rightGrammar : Nat -> Rule Nat
rightGrammar 0 = map (\_ => 1) a
rightGrammar (S k) = map (\_ => 1) a <|> map (+1) (rightGrammar k)

leftGrammar : Nat -> Rule Nat
leftGrammar 0 = map (\_ => 1) a
leftGrammar (S k) = rightGrammar k <|> map (\_ => (S k)) a

run : (n : Nat) -> Either (ParseError (TokenData PToken))
                      (Nat, List (TokenData PToken))
run n = parse (rightGrammar n) (fst (lex tokenMap "a"))

main : IO ()
main =  do  str <- getLine
            if all isDigit (fastUnpack str)
              then
                let n : Nat
                    n = (cast str)
                in case run n of
                    Right (res, _) => putStrLn $ show $ res
                    Left _ => putStrLn "Error"
              else putStrLn "Input should be two numbers"
