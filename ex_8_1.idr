%default total

||| If you cons the same value to two lists that are equal, the resuls are
||| equal.
same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons prf = cong prf

||| If the head and tail are equal, the lists are equal.
same_lists : {xs : List a}
          -> {ys : List a}
          -> x = y
          -> xs = ys
          -> x :: xs = y :: ys
same_lists Refl prf_tail = cong prf_tail

||| Equality for three values.
data ThreeEq : a -> b -> c -> Type where
	Refl3 : ThreeEq a a a

||| If three nats are equal, their three successors are equal.
allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x Refl3 = Refl3
