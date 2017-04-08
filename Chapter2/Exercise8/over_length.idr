over_length : Nat -> List String -> Nat
over_length _ [] = 0
over_length k (x :: xs) = (if k < length x then S else id) (over_length k xs)
