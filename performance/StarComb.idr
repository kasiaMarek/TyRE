import Text.Lexer
import public Text.Parser.Core
import public Text.Parser

data AToken = AChar | EndTok

tokenMap : TokenMap AToken
tokenMap = [(is 'a', \x => AChar)]

Rule : Type -> Type
Rule ty = Grammar (TokenData AToken) True ty

a : Rule Char
a = terminal "a" (\(MkToken _ _ tok) => case tok of {AChar => Just 'a'; _ => Nothing})

eoi : Rule ()
eoi = terminal "end" (\(MkToken _ _ tok) => case tok of {EndTok => Just (); _ => Nothing})

grammar : Rule (List Char)
grammar = manyTill eoi a

createString : Nat -> String
createString 0 = ""
createString (S k) = "a" ++ (createString k)

run : (n : Nat) -> Either (ParseError (TokenData AToken))
                      (List Char, List (TokenData AToken))
run n = parse grammar (fst (lex tokenMap (createString n)) ++ [MkToken 0 0 EndTok])

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
