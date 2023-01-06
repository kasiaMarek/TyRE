import TyRE.Text.Lexer
import public TyRE.Text.Parser.Core
import public TyRE.Text.Parser

data AToken = AChar | EndTok

tokenMap : TokenMap AToken
tokenMap = [(is 'a', \x => AChar),
            (is '$', \x => EndTok)]

Rule : Type -> Type
Rule ty = Grammar () AToken True ty

a : Rule Char
a = terminal "a" (\tok => case tok of {AChar => Just 'a'; EndTok => Nothing})

eoi : Rule ()
eoi = terminal "end" (\tok => case tok of {AChar => Nothing; EndTok => Just ()})

grammar : Rule (List Char)
grammar = manyTill eoi a

createString : Nat -> String
createString 0 = "a"
createString (S k) = "a" ++ (createString k)

run : (n : Nat) -> Either (List1 (ParsingError AToken))
                      (List Char, List (WithBounds AToken))
run n = parse grammar (fst (lex tokenMap ((createString n) ++ "$")))

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
