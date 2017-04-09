import Data.Vect

||| ```idris-repl
||| > transposeMat [[1,2], [3,4], [5,6]]
||| transposeMat [[1, 3, 5], [2, 4, 6]]
||| ```
transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = replicate _ []
transposeMat (x :: xs) = zipWith (::) x (transposeMat xs)
