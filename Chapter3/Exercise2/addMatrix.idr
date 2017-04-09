import Data.Vect

||| ```idris-repl
||| > addMatrix [[1,2], [3,4]] [[5,6], [7,8]]
||| [[6, 8], [10, 12]] : Vect 2 (Vect 2 Integer)
||| ```
addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix xs ys = zipWith (zipWith (+)) xs ys
