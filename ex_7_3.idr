import ex_7_2

%default total

||| ```idris-repl
||| > map (*2) (the (Expr _) (1 + 2 * 3))
||| Add (Val 2) (Mul (Val 4) (Val 6)) : Expr Integer
||| > map show (the (Expr _) (1 + 2 * 3))
||| Add (Val "1") (Mul (Val "2") (Val "3")) : Expr String
||| ```
Functor Expr where
	map func (Val x)   = Val (func x)
	map func (Add x y) = Add (map func x) (map func y)
	map func (Sub x y) = Sub (map func x) (map func y)
	map func (Mul x y) = Mul (map func x) (map func y)
	map func (Div x y) = Div (map func x) (map func y)
	map func (Abs x)   = Abs (map func x)

||| Alternative vector implementation.
data Vect : Nat -> Type -> Type where
	Nil : Vect Z ty
	(::) : ty -> Vect k ty -> Vect (S k) ty

||| ```idris-repl
||| > the (Vect _ _) [1,2,3,4] == [1,2,3,4]
||| True : Bool
||| > the (Vect _ _) [1,2,3,4] == [5,6,7,8]
||| False : Bool
||| ```
Eq elem => Eq (Vect k elem) where
	(==) []        []        = True
	(==) (x :: xs) (y :: ys) = x == y && xs == ys
	(/=) []        []        = False
	(/=) (x :: xs) (y :: ys) = x /= y || xs /= ys

||| ```idris-repl
||| > foldr (+) 0 (the (Vect _ _) [1,2,3,4,5])
||| 15 : Integer
||| ```
Foldable (Vect k) where
	foldr _    init []        = init
	foldr func init (x :: xs) = func x (foldr func init xs)
	foldl func init []        = init
	foldl func init (x :: xs) = foldl func (func init x) xs
