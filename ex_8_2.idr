import Data.Vect

%default total

||| `(+) {a = Nat}` is commutative.
myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z     m = sym (plusZeroRightNeutral m)
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in plusSuccRightSucc m k

||| Linear reverse, requiring proof step.
|||
||| ```idris-repl
||| > myReverse [1,2,3,4]
||| [4, 3, 2, 1] : Vect 4 Intege
||| ```
myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
 where
	reverse' : Vect n a -> Vect m a -> Vect (n + m) a
	reverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
	reverse' {n} {m = S k} acc (x :: xs) =
		rewrite sym (plusSuccRightSucc n k) in (reverse' (x::acc) xs)
