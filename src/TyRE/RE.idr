module TyRE.RE

import Data.List
import Data.Maybe

import TyRE.CoreRE
import TyRE.Core

public export
data RE =
    Exactly Char -- x
  | OneOf (List Char) -- [x,y,z]
  | To Char Char -- [x-y]
  | Any -- .
  | Concat RE RE -- AB
  | Alt RE RE -- A|B
  | Maybe RE -- A?
  | Group RE -- `A`
  | Rep0 RE -- A*
  | Rep1 RE -- A+
  | Keep RE

public export
Eq RE where
  (Exactly x) == (Exactly x')                 = x == x'
  (OneOf xs) == (OneOf ys)                    = xs == ys
  (x `To` y) == (x' `To` y')                  = (x == x') && (y == y')
  Any        == Any                           = True
  (re1 `Concat` re2) == (re1' `Concat` re2')  = (re1 == re1') && (re2 == re2')
  (Group x) == (Group x')                     = x == x'
  (Keep x) == (Keep x')                       = x == x'
  (re1 `Alt` re2) == (re1' `Alt` re2')        = (re1 == re1') && (re2 == re2')
  (Maybe re) == (Maybe re')                   = re == re'
  (Rep0 re) == (Rep0 re')                     = re == re'
  (Rep1 re) == (Rep1 re')                     = re == re'
  _ == _                                      = False

public export
specialChars : String
specialChars = "[]()\\`-|?+.*!"

public export
mapChar : Char -> String
mapChar c = case (find (\sc => c == sc) (unpack specialChars)) of {Just _ => "\\" ++ (cast c); Nothing => (cast c)}

public export
isUnit : RE -> Bool
isUnit (Exactly x) = True
isUnit (OneOf xs) = True
isUnit (To x y) = True
isUnit Any = True
isUnit (Concat x y) = False
isUnit (Alt x y) = False
isUnit (Maybe x) = False
isUnit (Group x) = True
isUnit (Keep x) = False
isUnit (Rep0 x) = False
isUnit (Rep1 x) = False

public export
isSemiUnit : RE -> Bool
isSemiUnit (Exactly x) = True
isSemiUnit (OneOf xs) = True
isSemiUnit (To x y) = True
isSemiUnit Any = True
isSemiUnit (Concat x y) = False
isSemiUnit (Alt x y) = False
isSemiUnit (Maybe x) = True
isSemiUnit (Group x) = True
isSemiUnit (Keep x) = True
isSemiUnit (Rep0 x) = True
isSemiUnit (Rep1 x) = True

mutual
  ||| If condintion is satisfied show in parentheses
  public export
  pshow : (RE -> Bool) -> RE -> String
  pshow condition re = if (condition re)
                then showAux re
                else "(" ++ showAux re ++ ")"

  public export
  showAux : RE -> String
  showAux (Exactly c) = mapChar c
  showAux (OneOf xs) = "[" ++ (foldl (++) "" (map mapChar xs)) ++ "]"
  showAux (To x y) = "[" ++ (mapChar x) ++ "-" ++ (mapChar y) ++ "]"
  showAux Any = "."
  showAux (Concat x y) = pshow isSemiUnit x ++ showAux y
  showAux (Alt x y) = pshow isSemiUnit x ++ "|" ++ pshow isSemiUnit y
  showAux (Maybe x) = pshow isUnit x ++ "?"
  showAux (Group x) = "`" ++ showAux x ++ "`"
  showAux (Rep0 x) = pshow isUnit x ++ "*"
  showAux (Rep1 x) = pshow isUnit x ++ "+"
  showAux (Keep x) = pshow isSemiUnit x ++ "!"

public export
Show RE where
  show = showAux

public export
CodeShapeREKeep : RE -> Code
CodeShapeREKeep (Exactly _) = UnitC
CodeShapeREKeep (OneOf _) = CharC
CodeShapeREKeep (To _ _) = CharC
CodeShapeREKeep Any = CharC
CodeShapeREKeep (Concat re1 re2) = PairC (CodeShapeREKeep re1) (CodeShapeREKeep re2)
CodeShapeREKeep (Alt re1 re2) = EitherC (CodeShapeREKeep re1) (CodeShapeREKeep re2)
CodeShapeREKeep (Group _) = StringC
CodeShapeREKeep (Maybe re) = MaybeC (CodeShapeREKeep re)
CodeShapeREKeep (Rep0 re) = ListC (CodeShapeREKeep re)
CodeShapeREKeep (Rep1 re) = ListC (CodeShapeREKeep re)
CodeShapeREKeep (Keep re) = CodeShapeREKeep re

public export
CodeShapeRE : RE -> Code
CodeShapeRE (Exactly _) = IgnoreC
CodeShapeRE (OneOf _) = IgnoreC
CodeShapeRE (To _ _) = IgnoreC
CodeShapeRE Any = IgnoreC
CodeShapeRE (Concat re1 re2) = PairC (CodeShapeRE re1) (CodeShapeRE re2)
CodeShapeRE (Alt re1 re2) = EitherC (CodeShapeRE re1) (CodeShapeRE re2)
CodeShapeRE (Group _) = StringC
CodeShapeRE (Maybe re) = MaybeC (CodeShapeRE re)
CodeShapeRE (Rep0 re) = ListC (CodeShapeRE re)
CodeShapeRE (Rep1 re) = ListC (CodeShapeRE re)
CodeShapeRE (Keep re) = CodeShapeREKeep re

public export
TypeREKeep : RE -> Type
TypeREKeep = (Sem . SimplifyCode . CodeShapeREKeep)

public export
TypeRE : RE -> Type
TypeRE = (Sem . SimplifyCode . CodeShapeRE)

export
pairEq : ((a, x) = (b, y)) -> (a = b, x = y)
pairEq Refl = (Refl, Refl)

export
eitherToMaybeL : Either a () -> Maybe a
eitherToMaybeL (Left x) = Just x
eitherToMaybeL (Right _) = Nothing

export
eitherToMaybeR : Either () a -> Maybe a
eitherToMaybeR (Left _) = Nothing
eitherToMaybeR (Right x) = Just x


mutual
  public export
  altTyREKeep : (re1 : RE) -> (re2 : RE)
          -> ((SimplifyCode (CodeShapeREKeep re1)) = a)
          -> ((SimplifyCode (CodeShapeREKeep re2)) = b)
          -> TyRE $ Either (Sem a) (Sem b)
  altTyREKeep re1 re2 Refl Refl = compileKeep re1 <|> compileKeep re2

  public export
  concatTyREKeep : (re1 : RE) -> (re2 : RE) -> TyRE (TypeREKeep re1, TypeREKeep re2)
  concatTyREKeep re1 re2 = compileKeep re1 <*> compileKeep re2

  public export
  compileKeep                  : (re : RE) -> TyRE $ TypeREKeep re
  compileKeep (Exactly x)      = match x
  compileKeep (OneOf xs)       = oneOfCharsList xs
  compileKeep (To x y)         = range x y
  compileKeep Any              = any
  compileKeep (Group re)       = group (compileKeep re)
  compileKeep (Concat re1 re2) with (SimplifyCode (CodeShapeREKeep re1), SimplifyCode (CodeShapeREKeep re2)) proof p
    compileKeep (Concat re1 re2) | (CharC, CharC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (CharC, (PairC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (CharC, StringC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (CharC, UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* (compileKeep re2)
    compileKeep (Concat re1 re2) | (CharC, (EitherC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (CharC, (MaybeC x)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (CharC, BoolC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (CharC, (ListC z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (CharC, NatC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (CharC, IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* (compileKeep re2)
    compileKeep (Concat re1 re2) | ((PairC x y), CharC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((PairC x y), (PairC z w)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((PairC x y), StringC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((PairC x y), UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* (compileKeep re2)
    compileKeep (Concat re1 re2) | ((PairC x y), (EitherC z w)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((PairC x y), (MaybeC z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((PairC x y), BoolC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((PairC x y), (ListC z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((PairC x y), NatC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((PairC x y), IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* (compileKeep re2)
    compileKeep (Concat re1 re2) | (StringC, CharC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (StringC, (PairC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (StringC, StringC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (StringC, UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* (compileKeep re2)
    compileKeep (Concat re1 re2) | (StringC, (EitherC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (StringC, (MaybeC x)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (StringC, BoolC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (StringC, (ListC z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (StringC, NatC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (StringC, IgnoreC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* (compileKeep re2)
    compileKeep (Concat re1 re2) | (UnitC, CharC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> (compileKeep re2)
    compileKeep (Concat re1 re2) | (UnitC, (PairC x y)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> (compileKeep re2)
    compileKeep (Concat re1 re2) | (UnitC, StringC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> (compileKeep re2)
    compileKeep (Concat re1 re2) | (UnitC, UnitC) = ignore (concatTyREKeep re1 re2)
    compileKeep (Concat re1 re2) | (UnitC, (EitherC x y)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> (compileKeep re2)
    compileKeep (Concat re1 re2) | (UnitC, (MaybeC x)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> (compileKeep re2)
    compileKeep (Concat re1 re2) | (UnitC, BoolC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> (compileKeep re2)
    compileKeep (Concat re1 re2) | (UnitC, (ListC z)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> (compileKeep re2)
    compileKeep (Concat re1 re2) | (UnitC, NatC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> (compileKeep re2)
    compileKeep (Concat re1 re2) | (UnitC, IgnoreC) = ignore (concatTyREKeep re1 re2)
    compileKeep (Concat re1 re2) | ((EitherC x y), CharC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((EitherC x y), (PairC z w)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((EitherC x y), StringC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((EitherC x y), UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* (compileKeep re2)
    compileKeep (Concat re1 re2) | ((EitherC x y), (EitherC z w)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((EitherC x y), (MaybeC z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((EitherC x y), BoolC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((EitherC x y), (ListC z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((EitherC x y), NatC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((EitherC x y), IgnoreC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* (compileKeep re2)
    compileKeep (Concat re1 re2) | ((MaybeC x), CharC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((MaybeC x), (PairC y z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((MaybeC x), StringC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((MaybeC x), UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* compileKeep re2
    compileKeep (Concat re1 re2) | ((MaybeC x), (EitherC y z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((MaybeC x), (MaybeC y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((MaybeC x), BoolC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((MaybeC x), (ListC z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((MaybeC x), NatC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((MaybeC x), IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* compileKeep re2
    compileKeep (Concat re1 re2) | (BoolC, CharC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (BoolC, (PairC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (BoolC, StringC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (BoolC, UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* compileKeep re2
    compileKeep (Concat re1 re2) | (BoolC, (EitherC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (BoolC, (MaybeC x)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (BoolC, BoolC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (BoolC, (ListC z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (BoolC, NatC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (BoolC, IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* compileKeep re2
    compileKeep (Concat re1 re2) | ((ListC z), CharC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((ListC z), (PairC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((ListC z), StringC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((ListC z), UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* compileKeep re2
    compileKeep (Concat re1 re2) | ((ListC z), (EitherC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((ListC z), (MaybeC x)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((ListC z), BoolC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((ListC z), (ListC x)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((ListC z), NatC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | ((ListC z), IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* (compileKeep re2)
    compileKeep (Concat re1 re2) | (NatC, CharC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (NatC, (PairC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (NatC, StringC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (NatC, UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* compileKeep re2
    compileKeep (Concat re1 re2) | (NatC, (EitherC x y)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (NatC, (MaybeC x)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (NatC, BoolC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (NatC, (ListC z)) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (NatC, NatC) = concatTyREKeep re1 re2
    compileKeep (Concat re1 re2) | (NatC, IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compileKeep re1 <* compileKeep re2
    compileKeep (Concat re1 re2) | (IgnoreC, CharC) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> compileKeep re2
    compileKeep (Concat re1 re2) | (IgnoreC, (PairC x y)) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> compileKeep re2
    compileKeep (Concat re1 re2) | (IgnoreC, StringC) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> compileKeep re2
    compileKeep (Concat re1 re2) | (IgnoreC, UnitC) = ignore (compileKeep re1 <*> compileKeep re2)
    compileKeep (Concat re1 re2) | (IgnoreC, (EitherC x y)) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> compileKeep re2
    compileKeep (Concat re1 re2) | (IgnoreC, (MaybeC x)) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> compileKeep re2
    compileKeep (Concat re1 re2) | (IgnoreC, BoolC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> compileKeep re2
    compileKeep (Concat re1 re2) | (IgnoreC, (ListC z)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> compileKeep re2
    compileKeep (Concat re1 re2) | (IgnoreC, NatC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compileKeep re1 *> compileKeep re2
    compileKeep (Concat re1 re2) | (IgnoreC, IgnoreC) = ignore (compileKeep re1 <*> compileKeep re2)

  compileKeep (Alt re1 re2) with (SimplifyCode (CodeShapeREKeep re1)) proof p1
    compileKeep (Alt re1 re2) | sc1 with (SimplifyCode (CodeShapeREKeep re2)) proof p2
      compileKeep (Alt re1 re2) | CharC | CharC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | CharC | (PairC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | CharC | StringC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | CharC | UnitC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | CharC | (EitherC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | CharC | (MaybeC x) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | CharC | BoolC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | CharC | (ListC x) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | CharC | NatC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | CharC | IgnoreC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | CharC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | (PairC z w) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | StringC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | UnitC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | (EitherC z w) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | (MaybeC z) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | BoolC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | (ListC z) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | NatC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (PairC x y) | IgnoreC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | CharC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | (PairC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | StringC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | UnitC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | (EitherC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | (MaybeC x) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | BoolC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | (ListC x) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | NatC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | StringC | IgnoreC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | CharC = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | (PairC x y) = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | StringC = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | UnitC =
        let f : Either () () -> Bool
            f (Left _) = True
            f (Right _) = False
        in f `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | (EitherC x y) = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | (MaybeC x) = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | BoolC = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | (ListC x) = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | NatC = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | UnitC | IgnoreC = (isJust . eitherToMaybeL) `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | CharC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | (PairC z w) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | StringC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | UnitC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | (EitherC z w) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | (MaybeC z) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | BoolC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | (ListC z) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | NatC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (EitherC x y) | IgnoreC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | CharC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | (PairC y z) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | StringC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | UnitC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | (EitherC y z) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | (MaybeC y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | BoolC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | (ListC z) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | NatC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (MaybeC x) | IgnoreC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | CharC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | (PairC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | StringC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | UnitC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | (EitherC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | (MaybeC x) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | BoolC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | (ListC z) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | NatC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | BoolC | IgnoreC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | CharC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | (PairC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | StringC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | UnitC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | (EitherC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | (MaybeC x) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | BoolC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | (ListC x) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | NatC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | (ListC z) | IgnoreC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | CharC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | (PairC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | StringC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | UnitC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | (EitherC x y) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | (MaybeC x) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | BoolC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | (ListC z) = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | NatC = altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | NatC | IgnoreC = eitherToMaybeL `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | CharC = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | (PairC x y) = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | StringC = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | UnitC = (isJust . eitherToMaybeR) `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | (EitherC x y) = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | (MaybeC x) = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | BoolC = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | (ListC z) = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | NatC = eitherToMaybeR `map` altTyREKeep re1 re2 p1 p2
      compileKeep (Alt re1 re2) | IgnoreC | IgnoreC = ignore (compileKeep re1 <|> compileKeep re2)
  compileKeep (Maybe re) with (SimplifyCode (CodeShapeREKeep re)) proof p
    compileKeep (Maybe re) | CharC = (rewrite p in eitherToMaybeL) `map` compileKeep re <|> Untyped Empty
    compileKeep (Maybe re) | (PairC x y) = (rewrite p in eitherToMaybeL) `map` compileKeep re <|> Untyped Empty
    compileKeep (Maybe re) | StringC = (rewrite p in eitherToMaybeL) `map` compileKeep re <|> Untyped Empty
    compileKeep (Maybe re) | UnitC =
      let f : Either () () -> Bool
          f (Left _) = True
          f (Right _) = False
      in (rewrite p in f) `map` compileKeep re <|> Untyped Empty
    compileKeep (Maybe re) | (EitherC x y) = (rewrite p in eitherToMaybeL) `map` compileKeep re <|> Untyped Empty
    compileKeep (Maybe re) | (MaybeC x) =
      let f : Either (Maybe (Sem x)) () -> (Maybe (Sem x))
          f (Left ms) = ms
          f (Right _) = Nothing
      in (rewrite p in f) `map` compileKeep re <|> Untyped Empty
    compileKeep (Maybe re) | BoolC = (rewrite p in eitherToMaybeL) `map` compileKeep re <|> Untyped Empty
    compileKeep (Maybe re) | (ListC z) = (rewrite p in eitherToMaybeL) `map` compileKeep re <|> Untyped Empty
    compileKeep (Maybe re) | NatC = (rewrite p in eitherToMaybeL) `map` compileKeep re <|> Untyped Empty
    compileKeep (Maybe re) | IgnoreC = ignore (option (compileKeep re))

  compileKeep (Rep0 re) with (SimplifyCode (CodeShapeREKeep re)) proof p
    compileKeep (Rep0 re) | CharC = replace {p=(TyRE . SnocList . Sem)} p (Rep (compileKeep re))
    compileKeep (Rep0 re) | (PairC x y) = replace {p=(TyRE . SnocList . Sem)} p (Rep (compileKeep re))
    compileKeep (Rep0 re) | StringC = replace {p=(TyRE . SnocList . Sem)} p (Rep (compileKeep re))
    compileKeep (Rep0 re) | UnitC = length `map` Rep (compileKeep re)
    compileKeep (Rep0 re) | (EitherC x y) = replace {p=(TyRE . SnocList . Sem)} p (Rep (compileKeep re))
    compileKeep (Rep0 re) | (ListC x) = replace {p=(TyRE . SnocList . Sem)} p (Rep (compileKeep re))
    compileKeep (Rep0 re) | (MaybeC x) = replace {p=(TyRE . SnocList . Sem)} p (Rep (compileKeep re))
    compileKeep (Rep0 re) | BoolC = replace {p=(TyRE . SnocList . Sem)} p (Rep (compileKeep re))
    compileKeep (Rep0 re) | NatC = replace {p=(TyRE . SnocList . Sem)} p (Rep (compileKeep re))
    compileKeep (Rep0 re) | IgnoreC = ignore (Rep (compileKeep re))

  compileKeep (Rep1 re) with (SimplifyCode (CodeShapeREKeep re)) proof p
    compileKeep (Rep1 re) | CharC = 
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeREKeep re
        cre = compileKeep re
    compileKeep (Rep1 re) | (PairC x y) =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeREKeep re
        cre = compileKeep re
    compileKeep (Rep1 re) | StringC =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeREKeep re
        cre = compileKeep re
    compileKeep (Rep1 re) | UnitC =
      (\(_,l) => length l + 1) `map` cre <*> Rep cre where
        cre : TyRE $ TypeREKeep re
        cre = compileKeep re
    compileKeep (Rep1 re) | (EitherC x y) =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeREKeep re
        cre = compileKeep re
    compileKeep (Rep1 re) | (ListC x) =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeREKeep re
        cre = compileKeep re
    compileKeep (Rep1 re) | (MaybeC x) =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeREKeep re
        cre = compileKeep re
    compileKeep (Rep1 re) | BoolC =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeREKeep re
        cre = compileKeep re
    compileKeep (Rep1 re) | NatC =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeREKeep re
        cre = compileKeep re
    compileKeep (Rep1 re) | IgnoreC = ignore (rep1 (compileKeep re))
  compileKeep (Keep re) = compileKeep re

mutual
  public export
  altTyRE : (re1 : RE) -> (re2 : RE)
          -> ((SimplifyCode (CodeShapeRE re1)) = a)
          -> ((SimplifyCode (CodeShapeRE re2)) = b)
          -> TyRE $ Either (Sem a) (Sem b)
  altTyRE re1 re2 Refl Refl = compile re1 <|> compile re2

  public export
  concatTyRE : (re1 : RE) -> (re2 : RE) -> TyRE (TypeRE re1, TypeRE re2)
  concatTyRE re1 re2 = compile re1 <*> compile re2

  public export
  compile                  : (re : RE) -> TyRE $ TypeRE re
  compile (Exactly x)      = match x
  compile (OneOf xs)       = ignore (oneOfCharsList xs)
  compile (To x y)         = ignore (range x y)
  compile Any              = ignore any
  compile (Group re)       = Untyped $ Group $ compile $ compile re
  compile (Concat re1 re2) with (SimplifyCode (CodeShapeRE re1), SimplifyCode (CodeShapeRE re2)) proof p
    compile (Concat re1 re2) | (CharC, CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* (compile re2)
    compile (Concat re1 re2) | (CharC, (EitherC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, (MaybeC x)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, (ListC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, NatC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* (compile re2)
    compile (Concat re1 re2) | ((PairC x y), CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), (PairC z w)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* (compile re2)
    compile (Concat re1 re2) | ((PairC x y), (EitherC z w)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), (MaybeC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), (ListC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), NatC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* (compile re2)
    compile (Concat re1 re2) | (StringC, CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* (compile re2)
    compile (Concat re1 re2) | (StringC, (EitherC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, (MaybeC x)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, (ListC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, NatC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, IgnoreC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* (compile re2)
    compile (Concat re1 re2) | (UnitC, CharC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> (compile re2)
    compile (Concat re1 re2) | (UnitC, (PairC x y)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> (compile re2)
    compile (Concat re1 re2) | (UnitC, StringC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> (compile re2)
    compile (Concat re1 re2) | (UnitC, UnitC) = ignore (concatTyRE re1 re2)
    compile (Concat re1 re2) | (UnitC, (EitherC x y)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> (compile re2)
    compile (Concat re1 re2) | (UnitC, (MaybeC x)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> (compile re2)
    compile (Concat re1 re2) | (UnitC, BoolC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> (compile re2)
    compile (Concat re1 re2) | (UnitC, (ListC z)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> (compile re2)
    compile (Concat re1 re2) | (UnitC, NatC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> (compile re2)
    compile (Concat re1 re2) | (UnitC, IgnoreC) = ignore (concatTyRE re1 re2)
    compile (Concat re1 re2) | ((EitherC x y), CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), (PairC z w)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* (compile re2)
    compile (Concat re1 re2) | ((EitherC x y), (EitherC z w)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), (MaybeC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), (ListC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), NatC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), IgnoreC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* (compile re2)
    compile (Concat re1 re2) | ((MaybeC x), CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), (PairC y z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* compile re2
    compile (Concat re1 re2) | ((MaybeC x), (EitherC y z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), (MaybeC y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), (ListC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), NatC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* compile re2
    compile (Concat re1 re2) | (BoolC, CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* compile re2
    compile (Concat re1 re2) | (BoolC, (EitherC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, (MaybeC x)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, (ListC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, NatC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* compile re2
    compile (Concat re1 re2) | ((ListC z), CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((ListC z), (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((ListC z), StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((ListC z), UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* compile re2
    compile (Concat re1 re2) | ((ListC z), (EitherC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((ListC z), (MaybeC x)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((ListC z), BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((ListC z), (ListC x)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((ListC z), NatC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((ListC z), IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* (compile re2)
    compile (Concat re1 re2) | (NatC, CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (NatC, (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (NatC, StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (NatC, UnitC) =
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* compile re2
    compile (Concat re1 re2) | (NatC, (EitherC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (NatC, (MaybeC x)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (NatC, BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (NatC, (ListC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (NatC, NatC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (NatC, IgnoreC) = 
      replace {p = (\s => TyRE (Sem s))} (fst $ pairEq p) 
      $ compile re1 <* compile re2
    compile (Concat re1 re2) | (IgnoreC, CharC) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> compile re2
    compile (Concat re1 re2) | (IgnoreC, (PairC x y)) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> compile re2
    compile (Concat re1 re2) | (IgnoreC, StringC) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> compile re2
    compile (Concat re1 re2) | (IgnoreC, UnitC) = ignore (compile re1 <*> compile re2)
    compile (Concat re1 re2) | (IgnoreC, (EitherC x y)) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> compile re2
    compile (Concat re1 re2) | (IgnoreC, (MaybeC x)) = 
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> compile re2
    compile (Concat re1 re2) | (IgnoreC, BoolC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> compile re2
    compile (Concat re1 re2) | (IgnoreC, (ListC z)) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> compile re2
    compile (Concat re1 re2) | (IgnoreC, NatC) =
      replace {p = (\s => TyRE (Sem s))} (snd $ pairEq p) 
      $ compile re1 *> compile re2
    compile (Concat re1 re2) | (IgnoreC, IgnoreC) = ignore (compile re1 <*> compile re2)

  compile (Alt re1 re2) with (SimplifyCode (CodeShapeRE re1)) proof p1
    compile (Alt re1 re2) | sc1 with (SimplifyCode (CodeShapeRE re2)) proof p2
      compile (Alt re1 re2) | CharC | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | (PairC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | UnitC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | (EitherC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | (MaybeC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | (ListC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | NatC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | IgnoreC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | (PairC z w) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | UnitC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | (EitherC z w) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | (MaybeC z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | (ListC z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | NatC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | IgnoreC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | (PairC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | UnitC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | (EitherC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | (MaybeC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | (ListC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | NatC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | IgnoreC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | CharC = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | (PairC x y) = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | StringC = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | UnitC =
        let f : Either () () -> Bool
            f (Left _) = True
            f (Right _) = False
        in f `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | (EitherC x y) = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | (MaybeC x) = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | BoolC = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | (ListC x) = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | NatC = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | IgnoreC = (isJust . eitherToMaybeL) `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | (PairC z w) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | UnitC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | (EitherC z w) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | (MaybeC z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | (ListC z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | NatC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | IgnoreC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | (PairC y z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | UnitC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | (EitherC y z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | (MaybeC y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | (ListC z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | NatC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | IgnoreC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | (PairC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | UnitC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | (EitherC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | (MaybeC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | (ListC z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | NatC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | IgnoreC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | (PairC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | UnitC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | (EitherC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | (MaybeC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | (ListC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | NatC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (ListC z) | IgnoreC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | (PairC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | UnitC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | (EitherC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | (MaybeC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | (ListC z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | NatC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | NatC | IgnoreC = eitherToMaybeL `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | CharC = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | (PairC x y) = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | StringC = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | UnitC = (isJust . eitherToMaybeR) `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | (EitherC x y) = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | (MaybeC x) = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | BoolC = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | (ListC z) = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | NatC = eitherToMaybeR `map` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | IgnoreC | IgnoreC = ignore (compile re1 <|> compile re2)
  compile (Maybe re) with (SimplifyCode (CodeShapeRE re)) proof p
    compile (Maybe re) | CharC = (rewrite p in eitherToMaybeL) `map` compile re <|> Untyped Empty
    compile (Maybe re) | (PairC x y) = (rewrite p in eitherToMaybeL) `map` compile re <|> Untyped Empty
    compile (Maybe re) | StringC = (rewrite p in eitherToMaybeL) `map` compile re <|> Untyped Empty
    compile (Maybe re) | UnitC =
      let f : Either () () -> Bool
          f (Left _) = True
          f (Right _) = False
      in (rewrite p in f) `map` compile re <|> Untyped Empty
    compile (Maybe re) | (EitherC x y) = (rewrite p in eitherToMaybeL) `map` compile re <|> Untyped Empty
    compile (Maybe re) | (MaybeC x) =
      let f : Either (Maybe (Sem x)) () -> (Maybe (Sem x))
          f (Left ms) = ms
          f (Right _) = Nothing
      in (rewrite p in f) `map` compile re <|> Untyped Empty
    compile (Maybe re) | BoolC = (rewrite p in eitherToMaybeL) `map` compile re <|> Untyped Empty
    compile (Maybe re) | (ListC z) = (rewrite p in eitherToMaybeL) `map` compile re <|> Untyped Empty
    compile (Maybe re) | NatC = (rewrite p in eitherToMaybeL) `map` compile re <|> Untyped Empty
    compile (Maybe re) | IgnoreC = ignore (option (compile re))

  compile (Rep0 re) with (SimplifyCode (CodeShapeRE re)) proof p
    compile (Rep0 re) | CharC = replace {p=(TyRE . SnocList . Sem)} p (Rep (compile re))
    compile (Rep0 re) | (PairC x y) = replace {p=(TyRE . SnocList . Sem)} p (Rep (compile re))
    compile (Rep0 re) | StringC = replace {p=(TyRE . SnocList . Sem)} p (Rep (compile re))
    compile (Rep0 re) | UnitC = length `map` Rep (compile re)
    compile (Rep0 re) | (EitherC x y) = replace {p=(TyRE . SnocList . Sem)} p (Rep (compile re))
    compile (Rep0 re) | (ListC x) = replace {p=(TyRE . SnocList . Sem)} p (Rep (compile re))
    compile (Rep0 re) | (MaybeC x) = replace {p=(TyRE . SnocList . Sem)} p (Rep (compile re))
    compile (Rep0 re) | BoolC = replace {p=(TyRE . SnocList . Sem)} p (Rep (compile re))
    compile (Rep0 re) | NatC = replace {p=(TyRE . SnocList . Sem)} p (Rep (compile re))
    compile (Rep0 re) | IgnoreC = ignore (Rep (compile re))

  compile (Rep1 re) with (SimplifyCode (CodeShapeRE re)) proof p
    compile (Rep1 re) | CharC =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeRE re
        cre = compile re
    compile (Rep1 re) | (PairC x y) =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeRE re
        cre = compile re
    compile (Rep1 re) | StringC =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeRE re
        cre = compile re
    compile (Rep1 re) | UnitC =
      (\(_,l) => length l + 1) `map` cre <*> Rep cre where
        cre : TyRE $ TypeRE re
        cre = compile re
    compile (Rep1 re) | (EitherC x y) =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeRE re
        cre = compile re
    compile (Rep1 re) | (ListC x) =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeRE re
        cre = compile re
    compile (Rep1 re) | (MaybeC x) =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeRE re
        cre = compile re
    compile (Rep1 re) | BoolC =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeRE re
        cre = compile re
    compile (Rep1 re) | NatC =
      (rewrite p in (\(c,l) => [< c] ++ l)) `map` cre <*> Rep cre where
        cre : TyRE $ TypeRE re
        cre = compile re
    compile (Rep1 re) | IgnoreC = ignore (rep1 (compile re))
  compile (Keep re) = compileKeep re
