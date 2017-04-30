%default total

||| Alternative vector implementation.
data Vect : Nat -> Type -> Type where
	Nil  : Vect Z elem
	(::) : elem -> Vect k elem -> Vect (S k) elem

||| If heads don't match, the vectors don't match.
headUnequal : DecEq a
           => {xs : Vect n a} -> {ys : Vect n a}
           -> (contra: (x = y) -> Void)
           -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

||| If tails don't match, the vectors don't match.
tailUnequal : DecEq a
           => {xs : Vect n a} -> {ys : Vect n a}
           -> (contra : (xs = ys) -> Void)
           -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

||| ```idris-repl
||| > decEq (the (Vect _ _) [1,2,3]) [1,2,3]
||| Yes Refl : Dec ([1, 2, 3] = [1, 2, 3])
||| ```
DecEq a => DecEq (Vect n a) where
	decEq []        []        = Yes Refl
	decEq (x :: xs) (y :: ys) = case decEq x y of
	 No contra => No (headUnequal contra)
	 Yes Refl  => case decEq xs ys of
		 No contra => No (tailUnequal contra)
		 Yes Refl  => Yes Refl
