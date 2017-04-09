import Data.Vect

||| ```idris-repl
||| > transposeMat [[1,2], [3,4], [5,6]]
||| [[1, 3, 5], [2, 4, 6]] : Vect 2 (Vect 3 Integer)
||| ```
transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = replicate _ []
transposeMat (x :: xs) = zipWith (::) x (transposeMat xs)

||| ```idris-repl
||| > addMatrix [[1,2], [3,4]] [[5,6], [7,8]]
||| [[6, 8], [10, 12]] : Vect 2 (Vect 2 Integer)
||| ```
addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix xs ys = zipWith (zipWith (+)) xs ys

||| Multiplies matrices.
|||
||| ```idris-repl
||| > multMatrix [[1,2], [3,4], [5,6]] [[7,8,9,10], [11,12,13,14]]
||| [[29, 32, 35, 38], [65, 72, 79, 86], [101, 112, 123, 134]]
||| 	: Vect 3 (Vect 4 Integer)
||| ```
multMatrix : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multMatrix xs ys = map (\row => map (sum . zipWith (*) row) (transposeMat ys)) xs
