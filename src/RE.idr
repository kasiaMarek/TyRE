module RE

import public Core
import public CoreTyRE
import Data.List

public export
data RE =
    Exactly Char
  | OneOf (List Char)
  | To Char Char
  | Concat RE RE
  | Alt RE RE
  | Maybe RE
  | Group RE

public export
Eq RE where
  (Exactly x) == (Exactly x')                 = x == x'
  (OneOf xs) == (OneOf ys)                    = xs == ys
  (x `To` y) == (x' `To` y')                  = (x == x') && (y == y')
  (re1 `Concat` re2) == (re1' `Concat` re2')  = (re1 == re1') && (re2 == re2')
  (Group x) == (Group x')                     = x == x'
  (re1 `Alt` re2) == (re1' `Alt` re2')        = (re1 == re1') && (re2 == re2')
  (Maybe re) == (Maybe re')                   = re == re'
  _ == _                                      = False

public export
specialChars : String
specialChars = "[]()\\`-|?"

public export
mapChar : Char -> String
mapChar c = case (find (\sc => c == sc) (unpack specialChars)) of {Just _ => "\\" ++ (cast c); Nothing => (cast c)}

public export
Show RE where
  show (Exactly c) = mapChar c
  show (OneOf xs) = "[" ++ (foldl (++) "" (map mapChar xs)) ++ "]"
  show (x `To` y) = "[" ++ (mapChar x) ++ "-" ++ (mapChar y) ++ "]"

  show (Concat (Concat x z) y) = "(" ++ (show (Concat x z)) ++ ")" ++ (show y)
  show (Concat (Alt x z) y) = "(" ++ (show (Alt x z)) ++ ")" ++ (show y)
  show (Concat (Maybe x) y) = "(" ++ (show (Maybe x)) ++ ")" ++ (show y)
  show (Concat atomX y) = show atomX ++ show y

  show (Alt (Alt x y) (Alt z w)) = "(" ++ show (Alt x y) ++ ")" ++ "|" ++  "(" ++ show (Alt z w) ++ ")"
  show (Alt (Alt x y) z) =  "(" ++ show (Alt x y) ++ ")" ++ "|" ++ show z
  show (Alt z (Alt x y)) =  show z ++ "|" ++  "(" ++ show (Alt x y) ++ ")"
  show (Alt x y) =  show x ++ "|" ++  show y

  show (Group x) = "`" ++ show x ++ "`"

  show (Maybe (Alt x y)) = "(" ++ show (Alt x y) ++ ")" ++ "?"
  show (Maybe (Concat x z)) = "(" ++ show (Concat x z) ++ ")" ++ "?"
  show (Maybe (Maybe x)) = "(" ++ show (Maybe x) ++ ")" ++ "?"
  show (Maybe unitX) = show unitX ++ "?"

public export
CodeShapeRE : RE -> Code
CodeShapeRE (Exactly _) = UnitC
CodeShapeRE (OneOf _) = CharC
CodeShapeRE (To _ _) = CharC
CodeShapeRE (Concat re1 re2) = PairC (CodeShapeRE re1) (CodeShapeRE re2)
CodeShapeRE (Alt re1 re2) = EitherC (CodeShapeRE re1) (CodeShapeRE re2)
CodeShapeRE (Group _) = StringC
CodeShapeRE (Maybe re1) = MaybeC (CodeShapeRE re1)

public export
TypeRE : RE -> Type
TypeRE = (Sem . SimplifyCode . CodeShapeRE)

public export
pairEq : ((a, x) = (b, y)) -> (a = b, x = y)
pairEq Refl = (Refl, Refl)

public export
eitherToMaybe : Either a () -> Maybe a
eitherToMaybe (Left x) = Just x
eitherToMaybe (Right _) = Nothing

public export
eitherToMaybeR : Either () a -> Maybe a
eitherToMaybeR (Left _) = Nothing
eitherToMaybeR (Right x) = Just x

mutual
  public export
  altTyRE : (re1 : RE) -> (re2 : RE)
          -> ((SimplifyCode (CodeShapeRE re1)) = a)
          -> ((SimplifyCode (CodeShapeRE re2)) = b)
          -> CoreTyRE $ Either (Sem a) (Sem b)
  altTyRE re1 re2 Refl Refl = compile re1 <|> compile re2

  public export
  concatTyRE : (re1 : RE) -> (re2 : RE) -> CoreTyRE (TypeRE re1, TypeRE re2)
  concatTyRE re1 re2 = compile re1 <*> compile re2

  public export
  compile                  : (re : RE) -> CoreTyRE $ TypeRE re
  compile (Exactly x)      = (\x => ()) `Conv` Untyped (Pred (\e => e == x))
  compile (OneOf xs)       = Untyped $ Pred (\e => case (find (\x => e == x) xs) of {(Just _) => True ; Nothing => False})
  compile (To x y)         = Untyped $ Pred (\c =>  x <= c && c <= y)
  compile (Group re)       = Untyped $ Group $ compile $ compile re
  compile (Concat re1 re2) with (SimplifyCode (CodeShapeRE re1), SimplifyCode (CodeShapeRE re2)) proof p
    compile (Concat re1 re2) | (CharC, CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, UnitC) =
      let prf : (SimplifyCode (CodeShapeRE re1) = CharC)
          prf = fst $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(x, _) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, (EitherC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, (MaybeC x)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (CharC, BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), (PairC z w)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), UnitC) =
      let prf : (SimplifyCode (CodeShapeRE re1) = (PairC x y))
          prf = fst $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(x, _) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), (EitherC z w)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), (MaybeC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((PairC x y), BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, UnitC) =
      let prf : (SimplifyCode (CodeShapeRE re1) = StringC)
          prf = fst $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(x, _) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, (EitherC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, (MaybeC x)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (StringC, BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, CharC) =
      let prf : (SimplifyCode (CodeShapeRE re2) = CharC)
          prf = snd $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(_,x) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, (PairC x y)) =
      let prf : (SimplifyCode (CodeShapeRE re2) = (PairC x y))
          prf = snd $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(_,x) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, StringC) =
      let prf : (SimplifyCode (CodeShapeRE re2) = StringC)
          prf = snd $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(_,x) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, UnitC) = (\x => ()) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, (EitherC x y)) =
      let prf : (SimplifyCode (CodeShapeRE re2) = (EitherC x y))
          prf = snd $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(_,x) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, (MaybeC x)) =
      let prf : (SimplifyCode (CodeShapeRE re2) = (MaybeC x))
          prf = snd $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(_,x) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (UnitC, BoolC) =
      let prf : (SimplifyCode (CodeShapeRE re2) = BoolC)
          prf = snd $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(_,x) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), (PairC z w)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), UnitC) =
      let prf : (SimplifyCode (CodeShapeRE re1) = (EitherC x y))
          prf = fst $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(x, _) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), (EitherC z w)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), (MaybeC z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((EitherC x y), BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), (PairC y z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), UnitC) =
      let prf : (SimplifyCode (CodeShapeRE re1) = (MaybeC x))
          prf = fst $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(x, _) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), (EitherC y z)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), (MaybeC y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | ((MaybeC x), BoolC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, CharC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, (PairC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, StringC) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, UnitC) =
      let prf : (SimplifyCode (CodeShapeRE re1) = BoolC)
          prf = fst $ pairEq p
      in replace {p = (\s => CoreTyRE (Sem s))} prf $ (\(x, _) => x) `Conv` concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, (EitherC x y)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, (MaybeC x)) = concatTyRE re1 re2
    compile (Concat re1 re2) | (BoolC, BoolC) = concatTyRE re1 re2

  compile (Alt re1 re2) with (SimplifyCode (CodeShapeRE re1)) proof p1
    compile (Alt re1 re2) | sc1 with (SimplifyCode (CodeShapeRE re2)) proof p2
      compile (Alt re1 re2) | CharC | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | (PairC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | UnitC = eitherToMaybe `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | (EitherC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | (MaybeC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | CharC | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | (PairC z w) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | UnitC = eitherToMaybe `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | (EitherC z w) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | (MaybeC z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (PairC x y) | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | (PairC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | UnitC = eitherToMaybe `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | (EitherC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | (MaybeC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | StringC | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | CharC = eitherToMaybeR `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | (PairC x y) = eitherToMaybeR `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | StringC = eitherToMaybeR `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | UnitC =
        let f : Either () () -> Bool
            f (Left _) = True
            f (Right _) = False
        in f `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | (EitherC x y) = eitherToMaybeR `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | (MaybeC x) = eitherToMaybeR `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | UnitC | BoolC = eitherToMaybeR `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | (PairC z w) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | UnitC = eitherToMaybe `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | (EitherC z w) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | (MaybeC z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (EitherC x y) | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | (PairC y z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | UnitC = eitherToMaybe `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | (EitherC y z) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | (MaybeC y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | (MaybeC x) | BoolC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | CharC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | (PairC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | StringC = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | UnitC = eitherToMaybe `Conv` altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | (EitherC x y) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | (MaybeC x) = altTyRE re1 re2 p1 p2
      compile (Alt re1 re2) | BoolC | BoolC = altTyRE re1 re2 p1 p2

  compile (Maybe re) with (SimplifyCode (CodeShapeRE re)) proof p
    compile (Maybe re) | CharC = (rewrite p in eitherToMaybe) `Conv` compile re <|> Untyped Empty
    compile (Maybe re) | (PairC x y) = (rewrite p in eitherToMaybe) `Conv` compile re <|> Untyped Empty
    compile (Maybe re) | StringC = (rewrite p in eitherToMaybe) `Conv` compile re <|> Untyped Empty
    compile (Maybe re) | UnitC =
      let f : Either () () -> Bool
          f (Left _) = True
          f (Right _) = False
      in (rewrite p in f) `Conv` compile re <|> Untyped Empty
    compile (Maybe re) | (EitherC x y) = (rewrite p in eitherToMaybe) `Conv` compile re <|> Untyped Empty
    compile (Maybe re) | (MaybeC x) =
      let f : Either (Maybe (Sem x)) () -> (Maybe (Sem x))
          f (Left ms) = ms
          f (Right _) = Nothing
      in (rewrite p in f) `Conv` compile re <|> Untyped Empty
    compile (Maybe re) | BoolC = (rewrite p in eitherToMaybe) `Conv` compile re <|> Untyped Empty
