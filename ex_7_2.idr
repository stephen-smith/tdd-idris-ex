%default total

||| Arithmetic expressions.
public export
data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

Num lit => Num (Expr lit) where
  (+) x y = Add x y
  (*) x y = Mul x y
  fromInteger = Val . fromInteger

||| Fully parenthesized display.
|||
||| ```idris-repl
||| > show (the (Expr _) (6 + 3 * 12))
||| "(6 + (3 * 12))" : String
||| > show (the (Expr _) (6 * 3 + 12))
||| "((6 * 3) + 12)" : String
||| ```
Show lit => Show (Expr lit) where
	show (Val lit) = show lit
	show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
	show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
	show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
	show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
	show (Abs x)   = "|" ++ show x ++ "|"

||| Evaluate using `Neg`/`Integral` operations.
eval : (Neg lit, Integral lit) => Expr lit -> lit
eval (Val lit) = lit
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x)   = abs (eval x)

||| Eqaulity based on evaluation.
|||
||| ```idris-repl
||| > the (Expr _) (2 + 4) == 3 + 3
||| True : Bool
||| > the (Expr _) (2 + 4) == 3 + 4
||| False : Bool
||| ```
(Eq lit, Neg lit, Integral lit) => Eq (Expr lit) where
	(==) x y = eval x == eval y
	(/=) x y = eval x /= eval y

Cast lit (Expr lit) where
	cast = Val

||| ```idris-repl
||| > let x : Expr Integer = 6 * 3 + 12 in the Integer (cast x)
||| 30 : Integer
||| ```
(Neg lit, Integral lit) => Cast (Expr lit) lit where
	cast = eval
