%default total

||| Allows traversal of a list several elements at a time
data TakeN : List a -> Type where
	Fewer : TakeN xs
	Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

||| Covering function for `TakeN`.
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
	 Fewer => Fewer
	 (Exact n_xs) => Exact (x :: n_xs)

||| Groups lists into sublists with `n` elements each.
|||
||| ```idris-repl
||| > groupByN 3 [1..10]
||| [[1, 2, 3], [4, 5, 6], [7, 8, 9], [10]] : List (List Integer)
||| ```
partial
groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
 groupByN n xs | Fewer = [xs]
 groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

||| Splits a list into two halves.
|||
||| ```idris-repl
||| > halves [1..10]
||| ([1, 2, 3, 4, 5], [6, 7, 8, 9, 10]) : (List Integer, List Integer)
||| > halves [1]
||| ([], [1]) : (List Integer, List Integer)
||| ```
partial
halves : List a -> (List a, List a)
halves xs with (takeN (length xs `div` 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)
