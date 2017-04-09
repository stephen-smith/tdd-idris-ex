module ex_3_2

import Data.Vect

%default total

my_length : List a -> Nat
my_length [] = 0
my_length (_ :: xs) = S (my_length xs)

my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = reverse xs ++ [x]

my_map : (a -> b) -> List a -> List b
my_map _ [] = []
my_map f (x :: xs) = f x :: my_map f xs

my_vect_map : (a -> b) -> Vect n a -> Vect n b
my_vect_map _ [] = []
my_vect_map f (x :: xs) = f x :: my_vect_map f xs
