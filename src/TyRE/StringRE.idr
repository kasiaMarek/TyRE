module TyRE.StringRE

import public Data.Maybe

import public TyRE.CoreRE
import public TyRE.Core
import public TyRE.RE
import public TyRE.Text.Lexer
import public TyRE.Text.Parser

public export
data Token =
              OParQ -- [
            | CParQ -- ]
            | OPar -- (
            | CPar -- )
            | Dot -- .
            | BackTic -- `
            | Dash -- -
            | Star -- *
            | Plus -- +
            | QMark -- ?
            | Alt -- |
            | Exclamation
            | CharLit String
            | End -- end of input

||| character literal:
|||   c -- for non special characters
|||   \c -- can be for both special and non special characters
public export
reCharLit : Lexer
reCharLit = (non $ some $ oneOf specialChars) <|> (is '\\' <+> any)

public export
reTokenMap : TokenMap Token
reTokenMap = [
              (is '[',    \x => OParQ),
              (is ']',    \x => CParQ),
              (is '(',    \x => OPar),
              (is ')',    \x => CPar),
              (is '.',    \x => Dot),
              (is '`',    \x => BackTic),
              (is '-',    \x => Dash),
              (is '*',    \x => Star),
              (is '+',    \x => Plus),
              (is '?',    \x => QMark),
              (is '|',    \x => Alt),
              (is '!',    \x => Exclamation),
              (reCharLit, \x => CharLit x)
              ]

public export
Rule : Type -> Type
Rule ty = Grammar (TokenData Token) True ty

----- terminals -----
public export
openParQ : Rule ()
openParQ = terminal "[" (\case {(MkToken _ _  OParQ) => Just (); _ => Nothing})

public export
closedParQ : Rule ()
closedParQ = terminal "]" (\case {(MkToken _ _  CParQ) => Just (); _ => Nothing})

public export
openPar : Rule ()
openPar = terminal "(" (\case {(MkToken _ _  OPar) => Just (); _ => Nothing})

public export
closedPar : Rule ()
closedPar = terminal ")" (\case {(MkToken _ _  CPar) => Just (); _ => Nothing})

public export
backTic : Rule ()
backTic = terminal "`" (\case {(MkToken _ _  BackTic) => Just (); _ => Nothing})

public export
dash : Rule ()
dash = terminal "-" (\case {(MkToken _ _  Dash) => Just (); _ => Nothing})

public export
dot : Rule ()
dot = terminal "." (\case {(MkToken _ _  Dot) => Just (); _ => Nothing})

public export
star : Rule ()
star = terminal "*" (\case {(MkToken _ _  Star) => Just (); _ => Nothing})

public export
plus : Rule ()
plus = terminal "+" (\case {(MkToken _ _  Plus) => Just (); _ => Nothing})

public export
qMark : Rule ()
qMark = terminal "?" (\case {(MkToken _ _  QMark) => Just (); _ => Nothing})

public export
alt : Rule ()
alt = terminal "|" (\case {(MkToken _ _  Alt) => Just (); _ => Nothing})

public export
end : Rule ()
end = terminal "" (\case {(MkToken _ _  End) => Just (); _ => Nothing})

public export
exclamation : Rule ()
exclamation = terminal "!" (\case {(MkToken _ _  Exclamation) => Just (); _ => Nothing})

public export
getCharLit : (TokenData Token) -> Maybe Char
getCharLit (MkToken _ _ (CharLit str)) with (unpack str)
  getCharLit (MkToken _ _ (CharLit str)) | [] = Nothing --should not happen
  getCharLit (MkToken _ _ (CharLit str)) | (c :: []) = Just c
  getCharLit (MkToken _ _ (CharLit str)) | ('\\' :: (c :: [])) = Just c
  getCharLit (MkToken _ _ (CharLit str)) | ('\\' :: (c :: (c' :: cs))) = Nothing --should not happen
  getCharLit (MkToken _ _ (CharLit str)) | (c :: (c' :: cs)) = Nothing --should not happen
getCharLit _ = Nothing

public export
charLit : Rule Char
charLit = terminal "char" getCharLit

----- grammar -----
public export
charLitsRep : Rule (List Char)
charLitsRep = (map (::) charLit <*> charLitsRep) <|> (map (\x => [x]) charLit)

public export
oneOf : Rule RE
oneOf = map OneOf $ openParQ *> charLitsRep <* closedParQ

public export
range : Rule RE
range = (map To ((openParQ *> charLit) <* dash) <*> charLit) <* closedParQ

public export
exactly : Rule RE
exactly = map Exactly charLit

public export
any : Rule RE
any = map (\_ => Any) dot

public export
mapRE : RE -> Maybe (RE -> RE) -> RE
mapRE re Nothing = re
mapRE re (Just f) = f re

mutual
  public export
  unit  : Rule RE
  unit  = exactly <|> any <|> oneOf <|> range -- single character patterns
        <|> (map Group $ backTic *> fullRE <* backTic) -- group
        <|> (openPar *> fullRE <* closedPar) -- with paranthesis

  public export
  postUnit  : Rule (RE -> RE)
  postUnit  = (map (\_ => Maybe) qMark) -- ...?
            <|> (map (\_ => Rep1) plus) -- ...+
            <|> (map (\_ => Rep0) star) -- ...*
            <|> (map (\_ => Keep) exclamation) -- ...!

  public export
  semiUnit : Rule RE
  semiUnit = map mapRE unit <*> optional (postUnit)

  public export
  postSemiUnit : Rule (RE -> RE)
  postSemiUnit =  (map (\y => \x => Alt x y) (alt *> semiUnit)) -- ...|A
              <|> (map (\y => \x => Concat x y) fullRE) -- ...ABC

  public export
  fullRE : Rule RE
  fullRE =  map mapRE semiUnit <*> optional (postSemiUnit)

public export
reWithEnd : Rule RE
reWithEnd = fullRE <* end

--- parsing ---

public export
mapTokens : (List (TokenData Token), (Int, Int, String))
          -> List (TokenData Token)
mapTokens (tokens, (f, l, _)) = tokens ++ [MkToken f l End]

public export
rAux : String -> Maybe RE
rAux str = case (parse reWithEnd (mapTokens (lex reTokenMap str))) of
                    Right (reg, _) => Just reg
                    Left _ => Nothing

public export
toRE : (str : String) -> {auto isJust : IsJust (rAux str)} -> RE
toRE str {isJust} = fromJust (rAux str) @{isJust}

export
r : (str : String) -> {auto isJust : IsJust (rAux str)} -> TyRE (TypeRE $ toRE str {isJust})
r str {isJust} = compile (toRE str {isJust})