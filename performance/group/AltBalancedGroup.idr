import Data.Regex
import Data.Either

import Data.Regex
import Data.Either

import Syntax.PreorderReasoning

data Div2View : Nat -> Type where
  Even : {0 n : Nat} -> (k : Nat) -> {auto 0 ford : n = k + k} -> Div2View n
  Odd : {0 n : Nat} -> (k : Nat) -> {auto 0 ford : n = 1 + k + k} -> Div2View n

div2 : (n : Nat) -> Div2View n
div2 0 = Even 0
div2 (S k) with (div2 k)
  div2 (S (j + j)) | (Even j {ford = Refl}) = Odd j
  div2 (S (S (j + j))) | (Odd j {ford = Refl}) =
    Even (S j) {ford = cong S $ Calc $
                     |~ (1 + j) + j
                     ~~ (j + 1) + j ... cong (+ j) (plusCommutative _ _)
                     ~~ j + (1 + j) ..< plusAssociative _ _ _}

0 typ : (n : Nat) -> Type
typ 0 = ()
typ 1 = ()
typ (S (S k)) with (div2 k)
  typ (S (S k)) | (Even j) = Either (typ (S j)) (typ (S j))
  typ (S (S k)) | (Odd j) = Either (typ (S j)) (typ (S (S j)))

balanced : (n : Nat) -> TyRE (typ n)
balanced 0 = match 'a'
balanced 1 = match 'a'
balanced (S (S k)) with (div2 k)
  balanced (S (S k)) | (Even j) = balanced (S j) <|> balanced (S j)
  balanced (S (S k)) | (Odd j) = balanced (S j) <|> balanced (S (S j))

main : IO ()
main =  do  str <- getLine
            if all isDigit (unpack str)
              then
                let n : Nat
                    n = (cast str)
                in case parse (ignore (balanced n)) "a" of
                    Just res => putStrLn $ show $ res
                    Nothing => putStrLn "Error"
              else putStrLn "Input should be a number"
