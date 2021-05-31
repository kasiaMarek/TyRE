module Core

data CoreRE =
    Pred (Char -> Bool)
    | Concat CoreRE CoreRE
    | Group CoreRE
    | Empty
    | Alt CoreRE CoreRE
    | Star CoreRE

data Code =
    CharC
    | PairC Code Code
    | StringC
    | UnitC
    | EitherC Code Code
    | ListC Code
    | MaybeC Code

Eq Code where
    CharC == CharC = True
    (PairC x z) == (PairC y v) = (x == y) && (z == v)
    StringC == StringC = True
    UnitC == UnitC = True
    (EitherC x z) == (EitherC y v) = ((x == y) && (z == v)) || ((x == v) && (z == y))
    (ListC x) == (ListC y) = x == y
    (MaybeC x) == (MaybeC y) = x == y
    _ == _ = False

    x /= y = not (x == y)

ShapeCode: CoreRE -> Code
ShapeCode (Pred f) = CharC
ShapeCode (Concat x y) = PairC (ShapeCode x) (ShapeCode y)
ShapeCode (Group _) = StringC
ShapeCode Empty = UnitC
ShapeCode (Alt x y) = EitherC (ShapeCode x) (ShapeCode y)
ShapeCode (Star x) = ListC (ShapeCode x)

Sem: Code -> Type
Sem CharC = Char
Sem (PairC x y) = (Sem x, Sem y)
Sem StringC = String
Sem UnitC = ()
Sem (EitherC x y) = Either (Sem x) (Sem y)
Sem (ListC x) = List (Sem x)
Sem (MaybeC x) = Maybe (Sem x)

Shape: CoreRE -> Type
Shape c = Sem (ShapeCode c)

SimplifyCode : Code -> Code
SimplifyCode CharC = CharC
SimplifyCode UnitC = UnitC
SimplifyCode StringC = StringC

SimplifyCode (ListC x) =
  case (SimplifyCode x) of
    UnitC => UnitC
    e => ListC e

SimplifyCode (MaybeC x) =
  let sx = SimplifyCode x
  in case sx of
    UnitC => UnitC
    (MaybeC y) => sx
    CharC => MaybeC sx
    StringC => MaybeC sx
    (PairC y z) => MaybeC sx
    (EitherC y z) => MaybeC sx
    (ListC y) => MaybeC sx


SimplifyCode (PairC x y) =
  let sx: Code = SimplifyCode x
      sy: Code = SimplifyCode y
  in case (sx, sy) of
    (UnitC, x) => x
    (x, UnitC) => x
    _ => PairC sx sy

SimplifyCode (EitherC x y) =
  let sx: Code = SimplifyCode x
      sy: Code = SimplifyCode y
  in case (sx, sy) of
    (UnitC, UnitC) => UnitC
    (UnitC, y) => MaybeC y
    (x, UnitC) => MaybeC x
    (MaybeC x, MaybeC y) => if(x == y) then MaybeC x else EitherC sx sy
    (MaybeC x, y) => if(x == y) then MaybeC x else EitherC sx sy
    (x, MaybeC y) => if(x == y) then MaybeC x else EitherC sx sy
    (x, y) => if(x == y) then x else EitherC x y

ConvertSimplification : (c : Code) -> Sem c -> Sem (SimplifyCode c)
ConvertSimplification CharC m = m
ConvertSimplification StringC m = m
ConvertSimplification UnitC _ = ()

ConvertSimplification (MaybeC x) m with (SimplifyCode x)
  ConvertSimplification (MaybeC x) _ | UnitC = ()
  ConvertSimplification (MaybeC x) Nothing | CharC = Nothing
  
  --It does not recognise that (SimplifyCode x = CharC)
  ConvertSimplification (MaybeC x) (Just y) | CharC = ?holee
    -- let p1: (SimplifyCode x = CharC) = Refl
    --     p2: (Sem CharC = Char) = Refl
    -- in replace {p = Maybe} ?hole123 (Just (ConvertSimplification x y))

  ConvertSimplification (MaybeC x) m | (PairC y z) = ?h_2
  ConvertSimplification (MaybeC x) m | StringC = ?h_3
  ConvertSimplification (MaybeC x) m | (EitherC y z) = ?h_5
  ConvertSimplification (MaybeC x) m | (ListC y) = ?h_6
  ConvertSimplification (MaybeC x) m | (MaybeC y) = ?h_7

ConvertSimplification (ListC x) m with (SimplifyCode x)
  ConvertSimplification (ListC x) m | UnitC = ()
  ConvertSimplification (ListC x) m | e = ?hole
                                  --UnitC => () ; e => map (ConvertSimplification x) m}
ConvertSimplification (PairC x y) m with (SimplifyCode x, SimplifyCode y)
  ConvertSimplification (PairC x y) m | (sx, sy) = ?ll_5

ConvertSimplification (EitherC y z) x = ?ConvertSimplification_rhs_5
