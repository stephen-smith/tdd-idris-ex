%default total

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons prf = cong prf

same_lists : {xs : List a}
          -> {ys : List a}
          -> x = y
          -> xs = ys
          -> x :: xs = y :: ys
same_lists Refl prf_tail = cong prf_tail

data ThreeEq : a -> b -> c -> Type where
	Refl3 : ThreeEq a a a

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x Refl3 = Refl3
