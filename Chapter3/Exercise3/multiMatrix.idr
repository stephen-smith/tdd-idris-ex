import Data.Vect

transposeMat : Vect n (Vect m a) -> Vect m (Vect n a)
transposeMat [] = replicate _ []
transposeMat (x :: xs) = zipWith (::) x (transposeMat xs)

||| ```idris-repl
||| > multMatrix [[1,2], [3,4], [5,6]] [[7,8,9,10], [11,12,13,14]]
||| [[29, 32, 35, 38], [65, 72, 79, 86], [101, 112, 123, 134]] : Vect 3 (Vect 4 Integer)
||| ```
multiMatrix : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multiMatrix xs ys = map (\row => map (sum . zipWith (*) row) (transposeMat ys)) xs
