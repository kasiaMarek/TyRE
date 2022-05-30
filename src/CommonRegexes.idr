module CommonRegexes

import API
import StringRE

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
    in firstPart <* match '@' <*> (secondPart <*> domain)

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
        f (tyre, error) = if isJust (parse tyre str) then [] else [error]

--- url
export
record URL where
    constructor HTTP
    isSSL : Maybe Bool
    host : String
    path : List String
    query : Maybe (List (String, String))
    fargment : Maybe String

export
url : TyRE URL
url = 
    let digitLetterOr : String -> TyRE Char
        digitLetterOr str = (digitChar `or` letter) `or` oneOf str
        protocol := (map fst) `Conv` r "(https?://(www)?)?"
        host := (\case(fst, snd) => pack (fst ++ snd)) 
                `Conv` 
                    repFromTo 1 256 (digitLetterOr "@:%_~#=.+-\\") 
                    <* match '.' 
                    <*> repFromTo 1 6 (digitLetterOr "()")
        path := rep0 (match '/' *> (pack `Conv` rep1 (digitLetterOr "_-")))
        query := TyRE.option $ match '?' 
                    *> rep1 ((pack `Conv` rep1 (digitLetterOr "_-") 
                        <* match '=') 
                    <*> (pack `Conv` rep1 (digitLetterOr "_-")))
        fragment := TyRE.option $ match '#' *> (pack `Conv` rep1 (digitLetterOr "_-"))
    in  (\case (pr, h, p, q, f) => HTTP pr h p q f) 
        `Conv` 
        (protocol <*> (host <*> (path <*> (query <*> fragment))))