module Data.Regex.CommonRegexes

import Data.Regex

import Data.String
import Data.List
import Data.Maybe

||| Simple email regex
export
email : TyRE (String, String, String)
email = 
    let firstPart : TyRE String
        firstPart = pack `Conv` rep1 ((letter `or` digitChar) `or` oneOf "%+_.-")
        secondPart : TyRE String
        secondPart = (joinBy ".") `Conv` rep1 (pack `Conv` rep1 (letter `or` digitChar) <* match '.')
        domain : TyRE String
        domain = pack `Conv` repFromTo 2 6 letter
    in firstPart <*> (match '@' *> secondPart <*> domain)

---password validation
data PasswordValidationError    = NoDigit 
                                | NoCapitalLetter 
                                | NoLowerCaseLetter 
                                | NoSpecialCharacter 
                                | ContainsSpace

passwordStrength : List ((TyRE (), PasswordValidationError))
passwordStrength =
    let hasDigit := ignore (r ".*[0-9].*")
        hasCapitalLetter := ignore (r ".*[A-Z].*")
        hasLowerCaseLetter := ignore (r ".*[a-z].*")
        hasSpecialCharacter := ignore (r "[!@#$<>%^&:=,_\\*\\+\\.\\?\\-]")
        doesntHaveSpaces := ignore $ rep0 $ predicate (/= ' ')
    in  [ (hasDigit, NoDigit)
        , (hasCapitalLetter, NoCapitalLetter)
        , (hasLowerCaseLetter, NoLowerCaseLetter)
        , (hasSpecialCharacter, NoSpecialCharacter)
        , (doesntHaveSpaces, ContainsSpace)
        ]

||| Strong password validation 
export
validatePasswordSecurity : String -> List PasswordValidationError
validatePasswordSecurity str = 
    passwordStrength >>= f where
        f : (TyRE (), PasswordValidationError) -> List PasswordValidationError
        f (tyre, error) = if match tyre str then [] else [error]

--- url
namespace UrlRegex
    export
    record URL where
        constructor HTTP
        isSSL : Maybe Bool
        host : (String, String)
        path : List String
        query : Maybe (List (String, String))
        fragment : Maybe String
        
    export
    Show URL where
        show (HTTP isSSL (host, domain) path query fragment) = 
            let protocol := 
                    case isSSL of
                        Nothing => ""
                        (Just True) => "https://"
                        (Just False) => "http://"
                pathPart := joinBy "/" path
                queryPart := map ((joinBy "&") . (map (\case (p, v) => p ++ "=" ++ v))) query
            in protocol ++ host ++ "." ++ domain ++ pathPart ++ fromMaybe "" queryPart ++ fromMaybe "" fragment

    export
    url : TyRE URL
    url = (\case (pr, h, p, q, f) => HTTP pr h p q f) 
          `Conv` 
          (protocol <*> (host <*> (path <*> (query <*> fragment)))) where
            digitLetterOr : String -> TyRE Char
            digitLetterOr str = (digitChar `or` letter) `or` oneOf str
            
            protocol : TyRE (Maybe Bool)
            protocol = (map fst) `Conv` r "(https?://(www)?)?"

            host : TyRE (String, String)
            host =  (pack `Conv` rep1 (digitLetterOr "@:%_~#=.+-\\"))
                    <* match '.' 
                    <*> (pack `Conv` repFromTo 1 6 (digitLetterOr "()"))

            path : TyRE (List String)
            path = rep0 (match '/' *> (pack `Conv` rep1 (digitLetterOr "_-")))

            query : TyRE (Maybe (List (String, String)))
            query = TyRE.option $ match '?' 
                        *> rep1 ((pack `Conv` rep1 (digitLetterOr "_-") 
                            <* match '=') 
                        <*> (pack `Conv` rep1 (digitLetterOr "_-")))

            fragment : TyRE (Maybe String)
            fragment = TyRE.option $ match '#' *> (pack `Conv` rep1 (digitLetterOr "_-"))