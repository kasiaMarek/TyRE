import Text.Lexer
import public Text.Parser.Core
import public Text.Parser
import Data.List

data PToken = AChar | BChar | CChar

tokenMap : TokenMap PToken
tokenMap = [(is 'a', \x => AChar), (is 'b', \x => BChar), (is 'c', \x => CChar)]

Rule : Type -> Type
Rule ty = Grammar (TokenData PToken) True ty

a : Rule ()
a = terminal "a" (\(MkToken _ _ tok) => case tok of {AChar => Just (); _ => Nothing})

b : Rule ()
b = terminal "b" (\(MkToken _ _ tok) => case tok of {BChar => Just (); _ => Nothing})

c : Rule ()
c = terminal "c" (\(MkToken _ _ tok) => case tok of {CChar => Just (); _ => Nothing})

grammar : Rule Nat
grammar = map sum ((many (map length (many a <* c) <|> map (\_ => (the Nat) 1) a)) <* b)

createString : Nat -> String
createString 0 = "b"
createString (S k) = "a" ++ (createString k)

run : (n : Nat) -> Either (ParseError (TokenData PToken))
                      (Nat, List (TokenData PToken))
run n = parse grammar (fst (lex tokenMap (createString n)))

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                in case run n of
                    Right (res, _) => putStrLn (show res)
                    Left _ => putStrLn "Error"
              else putStrLn "Input is not a number"
