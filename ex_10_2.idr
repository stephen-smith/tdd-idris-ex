import Data.List.Views
import Data.Nat.Views
import Data.Vect
import Data.Vect.Views

%default total

||| Return the maximum equal suffix of the two input lists.
|||
||| ```idris-repl
||| > equalSuffix [1,2,4,5] [1..5]
||| [4, 5] : List Integer
||| > equalSuffix [1,2,4,5,6] [1..5]
||| [] : List Integer
||| > equalSuffix [1,2,4,5,6] [1..6]
||| [4, 5, 6] : List Integer
||| ```
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys = equalSuffix' xs ys (snocList xs) (snocList ys)
 where
	equalSuffix' : (xs : List a) -> (ys : List a)
	            -> SnocList xs -> SnocList ys
	            -> List a
	equalSuffix' []          _           Empty     _         = []
	equalSuffix' _           []          _         Empty     = []
	equalSuffix' (xs ++ [x]) (ys ++ [y]) (Snoc sx) (Snoc sy) =
		if x == y then equalSuffix' xs ys sx sy ++ [x] else []

||| Merge sort implemented via recursive vector split view.
mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs = mergeSort' xs (splitRec xs)
 where
	SplitVect : Vect n a -> Type
	SplitVect = Data.Vect.Views.SplitRec

	mergeSort' : Ord a => (xs : Vect n a) -> SplitVect xs -> Vect n a
	mergeSort' []         SplitRecNil              = []
	mergeSort' [x]        SplitRecOne              = [x]
	mergeSort' (xs ++ ys) (SplitRecPair xrec yrec) =
		merge (mergeSort' xs xrec) (mergeSort' ys yrec)

||| Converts a `Nat` to a `String` containing a binary representation of the
||| `Nat`.
|||
||| ```idris-repl
||| > toBinary 42
||| "101010" : String
||| > toBinary 94
||| "1011110" : String
||| ```
toBinary : Nat -> String
toBinary n = toBinary' n (halfRec n)
 where
	toBinary' : (n : Nat) -> HalfRec n -> String
	toBinary' Z           HalfRecZ          = "0"
	toBinary' (x + x)     (HalfRecEven rec) = toBinary' x rec ++ "0"
	toBinary' (S (Z + Z)) (HalfRecOdd rec)  = "1"
	toBinary' (S (x + x)) (HalfRecOdd rec)  = toBinary' x rec ++ "1"

||| Returns whether a list is the same when traversed forwards and backwards.
|||
||| ```idris-repl
||| > palindrome (unpack "abccba")
||| True : Bool
||| > palindrome (unpack "abcba")
||| True : Bool
||| > palindrome (unpack "abcb")
||| False : Bool
||| ```
palindrome : List Char -> Bool
palindrome xs = palindrome' xs (vList xs)
 where
	palindrome' : (xs : List Char) -> VList xs -> Bool
	palindrome' []                 VNil        = True
	palindrome' [x]                VOne        = True
	palindrome' (x :: (ys ++ [y])) (VCons rec) =
		x == y && palindrome' ys rec
