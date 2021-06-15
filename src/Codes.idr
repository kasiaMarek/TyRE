module Codes

import Core

%default total

public export
data Code =
    CharC
    | PairC Code Code
    | StringC
    -- | UnitC
    -- | EitherC Code Code
    -- | ListC Code
    -- | MaybeC Code
    -- | BoolC
    -- | NatC

Eq Code where
    CharC == CharC                  = True
    (PairC x z) == (PairC y v)      = (x == y) && (z == v)
    StringC == StringC              = True
    -- UnitC == UnitC                  = True
    -- (EitherC x z) == (EitherC y v)  = ((x == y) && (z == v))
    -- (ListC x) == (ListC y)          = x == y
    -- (MaybeC x) == (MaybeC y)        = x == y
    _ == _                          = False

public export
ShapeCode: CoreRE -> Code
ShapeCode (Pred f)      = CharC
ShapeCode (Concat x y)  = PairC (ShapeCode x) (ShapeCode y)
ShapeCode (Group _)     = StringC
-- ShapeCode Empty         = UnitC
-- ShapeCode (Alt x y)     = EitherC (ShapeCode x) (ShapeCode y)
-- ShapeCode (Star x)      = ListC (ShapeCode x)

public export
Sem: Code -> Type
Sem CharC         = Char
Sem (PairC x y)   = (Sem x, Sem y)
Sem StringC       = String
-- Sem UnitC         = ()
-- Sem (EitherC x y) = Either (Sem x) (Sem y)
-- Sem (ListC x)     = List (Sem x)
-- Sem (MaybeC x)    = Maybe (Sem x)
-- Sem BoolC         = Bool
-- Sem NatC          = Nat

public export
Shape: CoreRE -> Type
Shape = Sem . ShapeCode

SimplifyCode : Code -> Code

-- SimplifyCode (ListC x) =
--   case (SimplifyCode x) of
--     UnitC => NatC
--     e => ListC e

-- SimplifyCode (MaybeC x) =
--   let sx = SimplifyCode x
--   in case sx of
--     UnitC => BoolC
--     (MaybeC y) => sx
--     e => MaybeC sx

SimplifyCode (PairC x y) =
  let sx: Code = SimplifyCode x
      sy: Code = SimplifyCode y
  in case (sx, sy) of
    -- (UnitC, x) => x
    -- (x, UnitC) => x
    _ => PairC sx sy

-- SimplifyCode (EitherC x y) =
--   let sx: Code = SimplifyCode x
--       sy: Code = SimplifyCode y
--   in case (sx, sy) of
--     (UnitC, UnitC) => BoolC
--     (UnitC, y) => MaybeC y
--     (x, UnitC) => MaybeC x
--     (x,y) => EitherC x y

SimplifyCode code = code

ConvertSimplification : (c : Code) -> Sem c -> Sem (SimplifyCode c)
ConvertSimplification CharC m   = m
ConvertSimplification StringC m = m
-- ConvertSimplification BoolC m   = m
-- ConvertSimplification NatC m    = m
-- ConvertSimplification UnitC _   = ()

-- ConvertSimplification (MaybeC x) Nothing with (SimplifyCode x)
--   ConvertSimplification (MaybeC x) Nothing | CharC          = Nothing
--   ConvertSimplification (MaybeC x) Nothing | (PairC y z)    = Nothing
--   ConvertSimplification (MaybeC x) Nothing | StringC        = Nothing
--   ConvertSimplification (MaybeC x) Nothing | UnitC          = False
--   ConvertSimplification (MaybeC x) Nothing | (EitherC y z)  = Nothing
--   ConvertSimplification (MaybeC x) Nothing | (ListC y)      = Nothing
--   ConvertSimplification (MaybeC x) Nothing | (MaybeC y)     = Nothing
--   ConvertSimplification (MaybeC x) Nothing | NatC           = Nothing
--   ConvertSimplification (MaybeC x) Nothing | BoolC          = Nothing
--
-- ConvertSimplification (MaybeC x) (Just y) with (ConvertSimplification x y)
--   ConvertSimplification (MaybeC x) (Just y) | cs with (SimplifyCode x)
--     ConvertSimplification (MaybeC x) (Just y) | cs | UnitC          = True
--     ConvertSimplification (MaybeC x) (Just y) | cs | (MaybeC z)     = cs
--     ConvertSimplification (MaybeC x) (Just y) | cs | CharC          = Just cs
--     ConvertSimplification (MaybeC x) (Just y) | cs | (PairC z w)    = Just cs
--     ConvertSimplification (MaybeC x) (Just y) | cs | StringC        = Just cs
--     ConvertSimplification (MaybeC x) (Just y) | cs | (EitherC z w)  = Just cs
--     ConvertSimplification (MaybeC x) (Just y) | cs | (ListC z)      = Just cs
--     ConvertSimplification (MaybeC x) (Just y) | cs | NatC           = Just cs
--     ConvertSimplification (MaybeC x) (Just y) | cs | BoolC          = Just cs

-- ConvertSimplification (ListC x) m with (ConvertSimplification x `map` m)
--   ConvertSimplification (ListC x) m | cs with (SimplifyCode x)
--     ConvertSimplification (ListC x) m | cs | CharC          = cs
--     ConvertSimplification (ListC x) m | cs | (PairC y z)    = cs
--     ConvertSimplification (ListC x) m | cs | StringC        = cs
--     ConvertSimplification (ListC x) m | cs | UnitC          = length cs
--     ConvertSimplification (ListC x) m | cs | (EitherC y z)  = cs
--     ConvertSimplification (ListC x) m | cs | (ListC y)      = cs
--     ConvertSimplification (ListC x) m | cs | (MaybeC y)     = cs
--     ConvertSimplification (ListC x) m | cs | BoolC          = cs
--     ConvertSimplification (ListC x) m | cs | NatC           = cs

ConvertSimplification (PairC x y) m with (ConvertSimplification x $ fst m, ConvertSimplification y $ snd m)
  ConvertSimplification (PairC x y) m | (csx, csy) with (SimplifyCode x)
    ConvertSimplification (PairC x y) m | (csx, csy) | sx with (SimplifyCode y)
      ConvertSimplification (PairC x y) m | (csx, csy) | CharC          | CharC         = (csx, csx)
      ConvertSimplification (PairC x y) m | (csx, csy) | CharC          | (PairC z w)   = (csx, csy)
      ConvertSimplification (PairC x y) m | (csx, csy) | CharC          | StringC       = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | CharC          | UnitC         = csx
      -- ConvertSimplification (PairC x y) m | (csx, csy) | CharC          | (EitherC z w) = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | CharC          | (ListC z)     = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | CharC          | (MaybeC z)    = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | CharC          | BoolC         = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | CharC          | NatC          = (csx, csy)

      ConvertSimplification (PairC x y) m | (csx, csy) | (PairC _ _)    | CharC         = (csx, csy)
      ConvertSimplification (PairC x y) m | (csx, csy) | (PairC _ _)    | (PairC v s)   = (csx, csy)
      ConvertSimplification (PairC x y) m | (csx, csy) | (PairC _ _)    | StringC       = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | (PairC _ _)    | UnitC         = csx
      -- ConvertSimplification (PairC x y) m | (csx, csy) | (PairC _ _)    | (EitherC v s) = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | (PairC _ _)    | (ListC v)     = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | (PairC _ _)    | (MaybeC v)    = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | (PairC _ _)    | BoolC         = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | (PairC _ _)    | NatC          = (csx, csy)

      ConvertSimplification (PairC x y) m | (csx, csy) | StringC        | CharC         = (csx, csy)
      ConvertSimplification (PairC x y) m | (csx, csy) | StringC        | (PairC z w)   = (csx, csy)
      ConvertSimplification (PairC x y) m | (csx, csy) | StringC        | StringC       = (csx, csx)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | StringC        | UnitC         = csx
      -- ConvertSimplification (PairC x y) m | (csx, csy) | StringC        | (EitherC z w) = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | StringC        | (ListC z)     = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | StringC        | (MaybeC z)    = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | StringC        | BoolC         = (csx, csy)
      -- ConvertSimplification (PairC x y) m | (csx, csy) | StringC        | NatC          = (csx, csy)

--       ConvertSimplification (PairC x y) m | (csx, csy) | UnitC          | CharC         = csy
--       ConvertSimplification (PairC x y) m | (csx, csy) | UnitC          | (PairC z w)   = csy
--       ConvertSimplification (PairC x y) m | (csx, csy) | UnitC          | StringC       = csy
--       ConvertSimplification (PairC x y) m | (csx, csy) | UnitC          | UnitC         = ()
--       ConvertSimplification (PairC x y) m | (csx, csy) | UnitC          | (EitherC z w) = csy
--       ConvertSimplification (PairC x y) m | (csx, csy) | UnitC          | (ListC z)     = csy
--       ConvertSimplification (PairC x y) m | (csx, csy) | UnitC          | (MaybeC z)    = csy
--       ConvertSimplification (PairC x y) m | (csx, csy) | UnitC          | BoolC         = csy
--       ConvertSimplification (PairC x y) m | (csx, csy) | UnitC          | NatC          = csy
--
--       ConvertSimplification (PairC x y) m | (csx, csy) | (EitherC _ _)  | CharC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (EitherC _ _)  | (PairC z w)   = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (EitherC _ _)  | StringC       = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (EitherC _ _)  | UnitC         = csx
--       ConvertSimplification (PairC x y) m | (csx, csy) | (EitherC _ _)  | (EitherC z w) = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (EitherC _ _)  | (ListC z)     = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (EitherC _ _)  | (MaybeC z)    = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (EitherC _ _)  | BoolC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (EitherC _ _)  | NatC          = (csx, csy)
--
--       ConvertSimplification (PairC x y) m | (csx, csy) | (ListC _)      | CharC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (ListC _)      | (PairC z w)   = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (ListC _)      | StringC       = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (ListC _)      | UnitC         = csx
--       ConvertSimplification (PairC x y) m | (csx, csy) | (ListC _)      | (EitherC z w) = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (ListC _)      | (ListC z)     = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (ListC _)      | (MaybeC z)    = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (ListC _)      | BoolC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (ListC _)      | NatC          = (csx, csy)
--
--       ConvertSimplification (PairC x y) m | (csx, csy) | (MaybeC _)     | CharC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (MaybeC _)     | (PairC z w)   = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (MaybeC _)     | StringC       = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (MaybeC _)     | UnitC         = csx
--       ConvertSimplification (PairC x y) m | (csx, csy) | (MaybeC _)     | (EitherC z w) = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (MaybeC _)     | (ListC z)     = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (MaybeC _)     | (MaybeC z)    = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (MaybeC _)     | BoolC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | (MaybeC _)     | NatC          = (csx, csy)
--
--       ConvertSimplification (PairC x y) m | (csx, csy) | BoolC          | CharC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | BoolC          | (PairC z w)   = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | BoolC          | StringC       = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | BoolC          | UnitC         = csx
--       ConvertSimplification (PairC x y) m | (csx, csy) | BoolC          | (EitherC z w) = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | BoolC          | (ListC z)     = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | BoolC          | (MaybeC z)    = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | BoolC          | BoolC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | BoolC          | NatC          = (csx, csy)
--
--       ConvertSimplification (PairC x y) m | (csx, csy) | NatC          | CharC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | NatC          | (PairC z w)   = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | NatC          | StringC       = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | NatC          | UnitC         = csx
--       ConvertSimplification (PairC x y) m | (csx, csy) | NatC          | (EitherC z w) = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | NatC          | (ListC z)     = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | NatC          | (MaybeC z)    = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | NatC          | BoolC         = (csx, csy)
--       ConvertSimplification (PairC x y) m | (csx, csy) | NatC          | NatC          = (csx, csy)
--
-- ConvertSimplification (EitherC x y) (Left m) with (ConvertSimplification x m)
--   ConvertSimplification (EitherC x y) (Left m) | cs with (SimplifyCode x)
--     ConvertSimplification (EitherC x y) (Left m) | cs | sx with (SimplifyCode y)
--
--       ConvertSimplification (EitherC x y) (Left m) | cs | CharC           | CharC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | CharC           | (PairC z w)     = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | CharC           | StringC         = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | CharC           | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | CharC           | (EitherC _ _)   = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | CharC           | (ListC z)       = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | CharC           | (MaybeC z)      = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | CharC           | BoolC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | CharC           | NatC            = Left cs
--
--       ConvertSimplification (EitherC x y) (Left m) | cs | (PairC _ _)     | CharC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (PairC _ _)     | (PairC z w)     = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (PairC _ _)     | StringC         = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (PairC _ _)     | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (PairC _ _)     | (EitherC _ _)   = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (PairC _ _)     | (ListC z)       = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (PairC _ _)     | (MaybeC z)      = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (PairC _ _)     | BoolC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (PairC _ _)     | NatC            = Left cs
--
--       ConvertSimplification (EitherC x y) (Left m) | cs | StringC         | CharC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | StringC         | (PairC z w)     = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | StringC         | StringC         = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | StringC         | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | StringC         | (EitherC _ _)   = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | StringC         | (ListC z)       = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | StringC         | (MaybeC z)      = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | StringC         | BoolC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | StringC         | NatC            = Left cs
--
--       ConvertSimplification (EitherC x y) (Left m) | cs | UnitC           | CharC           = Nothing
--       ConvertSimplification (EitherC x y) (Left m) | cs | UnitC           | (PairC z w)     = Nothing
--       ConvertSimplification (EitherC x y) (Left m) | cs | UnitC           | StringC         = Nothing
--       ConvertSimplification (EitherC x y) (Left m) | cs | UnitC           | UnitC           = True
--       ConvertSimplification (EitherC x y) (Left m) | cs | UnitC           | (EitherC _ _)   = Nothing
--       ConvertSimplification (EitherC x y) (Left m) | cs | UnitC           | (ListC z)       = Nothing
--       ConvertSimplification (EitherC x y) (Left m) | cs | UnitC           | (MaybeC z)      = Nothing
--       ConvertSimplification (EitherC x y) (Left m) | cs | UnitC           | BoolC           = Nothing
--       ConvertSimplification (EitherC x y) (Left m) | cs | UnitC           | NatC            = Nothing
--
--       ConvertSimplification (EitherC x y) (Left m) | cs | (EitherC _ _)   | CharC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (EitherC _ _)   | (PairC z w)     = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (EitherC _ _)   | StringC         = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (EitherC _ _)   | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (EitherC _ _)   | (EitherC _ _)   = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (EitherC _ _)   | (ListC z)       = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (EitherC _ _)   | (MaybeC z)      = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (EitherC _ _)   | BoolC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (EitherC _ _)   | NatC            = Left cs
--
--       ConvertSimplification (EitherC x y) (Left m) | cs | (ListC _)       | CharC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (ListC _)       | (PairC z w)     = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (ListC _)       | StringC         = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (ListC _)       | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (ListC _)       | (EitherC _ _)   = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (ListC _)       | (ListC z)       = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (ListC _)       | (MaybeC z)      = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (ListC _)       | BoolC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (ListC _)       | NatC            = Left cs
--
--       ConvertSimplification (EitherC x y) (Left m) | cs | (MaybeC _)       | CharC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (MaybeC _)       | (PairC z w)     = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (MaybeC _)       | StringC         = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (MaybeC _)       | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (MaybeC _)       | (EitherC _ _)   = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (MaybeC _)       | (ListC z)       = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (MaybeC _)       | (MaybeC z)      = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (MaybeC _)       | BoolC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | (MaybeC _)       | NatC            = Left cs
--
--       ConvertSimplification (EitherC x y) (Left m) | cs | BoolC           | CharC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | BoolC           | (PairC z w)     = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | BoolC           | StringC         = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | BoolC           | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | BoolC           | (EitherC _ _)   = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | BoolC           | (ListC z)       = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | BoolC           | (MaybeC z)      = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | BoolC           | BoolC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | BoolC           | NatC            = Left cs
--
--       ConvertSimplification (EitherC x y) (Left m) | cs | NatC            | CharC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | NatC            | (PairC z w)     = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | NatC            | StringC         = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | NatC            | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | NatC            | (EitherC _ _)   = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | NatC            | (ListC z)       = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | NatC            | (MaybeC z)      = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | NatC            | BoolC           = Left cs
--       ConvertSimplification (EitherC x y) (Left m) | cs | NatC            | NatC            = Left cs
--
-- ConvertSimplification (EitherC x y) (Right m) with (ConvertSimplification y m)
--   ConvertSimplification (EitherC x y) (Right m) | cs with (SimplifyCode y)
--     ConvertSimplification (EitherC x y) (Right m) | cs | sy with (SimplifyCode x)
--
--       ConvertSimplification (EitherC x y) (Right m) | cs | CharC           | CharC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | CharC           | (PairC z w)     = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | CharC           | StringC         = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | CharC           | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | CharC           | (EitherC _ _)   = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | CharC           | (ListC z)       = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | CharC           | (MaybeC z)      = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | CharC           | BoolC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | CharC           | NatC            = Right cs
--
--       ConvertSimplification (EitherC x y) (Right m) | cs | (PairC _ _)     | CharC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (PairC _ _)     | (PairC z w)     = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (PairC _ _)     | StringC         = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (PairC _ _)     | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (PairC _ _)     | (EitherC _ _)   = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (PairC _ _)     | (ListC z)       = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (PairC _ _)     | (MaybeC z)      = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (PairC _ _)     | BoolC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (PairC _ _)     | NatC            = Right cs
--
--       ConvertSimplification (EitherC x y) (Right m) | cs | StringC         | CharC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | StringC         | (PairC z w)     = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | StringC         | StringC         = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | StringC         | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | StringC         | (EitherC _ _)   = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | StringC         | (ListC z)       = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | StringC         | (MaybeC z)      = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | StringC         | BoolC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | StringC         | NatC            = Right cs
--
--       ConvertSimplification (EitherC x y) (Right m) | cs | UnitC           | CharC           = Nothing
--       ConvertSimplification (EitherC x y) (Right m) | cs | UnitC           | (PairC z w)     = Nothing
--       ConvertSimplification (EitherC x y) (Right m) | cs | UnitC           | StringC         = Nothing
--       ConvertSimplification (EitherC x y) (Right m) | cs | UnitC           | UnitC           = False
--       ConvertSimplification (EitherC x y) (Right m) | cs | UnitC           | (EitherC _ _)   = Nothing
--       ConvertSimplification (EitherC x y) (Right m) | cs | UnitC           | (ListC z)       = Nothing
--       ConvertSimplification (EitherC x y) (Right m) | cs | UnitC           | (MaybeC z)      = Nothing
--       ConvertSimplification (EitherC x y) (Right m) | cs | UnitC           | BoolC           = Nothing
--       ConvertSimplification (EitherC x y) (Right m) | cs | UnitC           | NatC            = Nothing
--
--       ConvertSimplification (EitherC x y) (Right m) | cs | (EitherC _ _)   | CharC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (EitherC _ _)   | (PairC z w)     = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (EitherC _ _)   | StringC         = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (EitherC _ _)   | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (EitherC _ _)   | (EitherC _ _)   = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (EitherC _ _)   | (ListC z)       = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (EitherC _ _)   | (MaybeC z)      = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (EitherC _ _)   | BoolC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (EitherC _ _)   | NatC            = Right cs
--
--       ConvertSimplification (EitherC x y) (Right m) | cs | (ListC _)       | CharC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (ListC _)       | (PairC z w)     = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (ListC _)       | StringC         = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (ListC _)       | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (ListC _)       | (EitherC _ _)   = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (ListC _)       | (ListC z)       = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (ListC _)       | (MaybeC z)      = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (ListC _)       | BoolC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (ListC _)       | NatC            = Right cs
--
--       ConvertSimplification (EitherC x y) (Right m) | cs | (MaybeC _)       | CharC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (MaybeC _)       | (PairC z w)     = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (MaybeC _)       | StringC         = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (MaybeC _)       | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (MaybeC _)       | (EitherC _ _)   = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (MaybeC _)       | (ListC z)       = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (MaybeC _)       | (MaybeC z)      = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (MaybeC _)       | BoolC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | (MaybeC _)       | NatC            = Right cs
--
--       ConvertSimplification (EitherC x y) (Right m) | cs | BoolC           | CharC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | BoolC           | (PairC z w)     = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | BoolC           | StringC         = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | BoolC           | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | BoolC           | (EitherC _ _)   = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | BoolC           | (ListC z)       = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | BoolC           | (MaybeC z)      = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | BoolC           | BoolC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | BoolC           | NatC            = Right cs
--
--       ConvertSimplification (EitherC x y) (Right m) | cs | NatC            | CharC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | NatC            | (PairC z w)     = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | NatC            | StringC         = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | NatC            | UnitC           = Just cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | NatC            | (EitherC _ _)   = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | NatC            | (ListC z)       = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | NatC            | (MaybeC z)      = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | NatC            | BoolC           = Right cs
--       ConvertSimplification (EitherC x y) (Right m) | cs | NatC            | NatC            = Right cs
