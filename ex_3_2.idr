import Data.Vect

%default total

||| Alternative implementation of `length`.
|||
||| ```idris-repl
||| > my_length [1..10]
||| 10 : Nat
||| ```
my_length : List a -> Nat
my_length [] = 0
my_length (_ :: xs) = S (my_length xs)

||| Alternative implementation of `reverse`.
|||
||| ```idris-repl
||| > my_reverse [1..10]
||| [10, 9, 8, 7, 6, 5, 4, 3, 2, 1] : List Integer
||| ```
my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = reverse xs ++ [x]

||| Alternative implementation of `map` for lists.
|||
||| ```idris-repl
||| > my_map (* 2) [1..10]
||| [2, 4, 6, 8, 10, 12, 14, 16, 18, 20] : List Integer
||| ```
my_map : (a -> b) -> List a -> List b
my_map _ [] = []
my_map f (x :: xs) = f x :: my_map f xs

||| Alternative implementation of `map` for vectors.
|||
||| ```idris-repl
||| > my_vect_map length ["Hot", "Dog", "Jumping", "Frog"]
||| [3, 3, 7, 4] : Vect 4 Nat
||| ```
my_vect_map : (a -> b) -> Vect n a -> Vect n b
my_vect_map _ [] = []
my_vect_map f (x :: xs) = f x :: my_vect_map f xs
