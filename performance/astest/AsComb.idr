module AsComb

import Text.Lexer
import public Text.Parser.Core
import public Text.Parser

data AToken = AChar

aTokenMap : TokenMap AToken
aTokenMap = [(is 'a', \x => AChar)]

Rule : Type -> Type
Rule ty = Grammar (TokenData AToken) True ty

gType : Nat -> Type
gType 0 = Char
gType (S k) = (Char, gType k)

justAGrammar : Rule Char
justAGrammar = terminal "a" (\tok => Just 'a')

getGrammar : (n : Nat) -> (Rule $ gType n)
getGrammar 0 = justAGrammar
getGrammar (S k) = (map MkPair justAGrammar <*> getGrammar k)

createString : Nat -> List Char
createString 0 = ['a']
createString (S k) = 'a'::(createString k)

resToStr  : {auto showChar : Show Char }
          -> {auto showEither : ({a,b : Type} -> (Show a, Show b) => Show (a, b))}
          -> (n: Nat) -> Show (gType n)
resToStr 0 = showChar
resToStr (S k) =
  let _ := resToStr k
  in showEither

run : (n : Nat) -> Either (ParseError (TokenData AToken))
                      (gType n, List (TokenData AToken))
run n = parse (getGrammar n) (fst (lex aTokenMap (pack $ createString n)))

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                    _ := resToStr n
                in case run n of
                    Right (res, _) => putStrLn (show res)
                    Left _ => putStrLn "Error"
              else putStrLn "Input is not a number"
