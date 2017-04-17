%default total

||| Produces a new `Stream` from every second element of an input `Stream`.
|||
||| ```idris-repl
||| > take 10 (every_other [1..])
||| [2, 4, 6, 8, 10, 12, 14, 16, 18, 20] : List Integer
||| ```
every_other : Stream a -> Stream a
every_other (value :: (x :: xs)) = x :: every_other xs

||| Infinite lists.
data InfList : Type -> Type where
	(::) : (value : elem) -> Inf (InfList elem) -> InfList elem

||| ```idris-repl
||| > getPrefix 10 (map (*2) (countFrom 1))
||| [2, 4, 6, 8, 10, 12, 14, 16, 18, 20] : List Integer
||| ```
Functor InfList where
	map func x = map' x
	 where
		map' : InfList a -> InfList b
		map' (value :: x) = func value :: map' x

||| Calculates a finite list from the prefix of an infinite list.
getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z     _            = []
getPrefix (S k) (value :: x) = value :: getPrefix k x

||| Generates an infinite list of numbers.
countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x + 1)

||| The faces of a coin.
data Face = Heads | Tails

getFace : Int -> Face
getFace x = if x < 0 then Heads else Tails

||| Returns a sequence of `count` coin flips using the stream as a source of
||| randomness.
|||
||| NB: The example result differs from the one provided in the book,
||| presumably because our `getFace` function is not the same as Dr. Brady's.
||| The book does not provide an implementation for `getFace`.
|||
||| ```idris-repl
||| > coinFlips 6 (randoms 12345)
||| [Tails, Tails, Heads, Tails, Tails, Heads] : List Face
||| ```
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z     _             = []
coinFlips (S k) (value :: xs) = getFace value :: coinFlips k xs

||| Generates a stream of pseudo-random number from a seed.
export
randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
	(seed' `shiftR` 2) :: randoms seed'

||| Generate a sequence of square-root approximations.
||| ```idris-repl
||| > take 3 (square_root_approx 10 10)
||| [10.0, 5.5, 3.659090909090909] : List Double
||| > take 3 (square_root_approx 100 25)
||| [25.0, 14.5, 10.698275862068964] : List Double
||| ```
square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx = square_root_approx_number approx
 where
	square_root_approx_number approx =
		approx :: square_root_approx_number next
	 where next = (approx + (number / approx)) / 2

||| Finds the first approximate of a square root that's within a desired bound,
||| or within a maximum number of iterations.
square_root_bound : (max : Nat)
                 -> (number : Double) -> (bound : Double)
                 -> (approxs : Stream Double)
                 -> Double
square_root_bound max number bound approxs = srb max approxs
 where
	srb Z      (value :: xs) = value
	srb (S k)  (value :: xs) =
		if abs (value * value - number) < bound
		 then value
		 else srb k  xs

||| Calculates the square root of a `Double` through successive approvimation.
|||
||| ```idris-repl
||| > square_root 6
||| 2.449489742783178 : Double
||| > square_root 2500
||| 50.0 : Double
||| > square_root 2501
||| 50.009999000199954 : Double
||| ```
square_root : (number : Double) -> Double
square_root number =
	square_root_bound 100 number 0.00000000001
	 (square_root_approx number (number / 2))
