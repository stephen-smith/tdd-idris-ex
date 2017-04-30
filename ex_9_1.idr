%default total

||| Proof a list contains a particular value.
data Elem : List e -> e -> Type where
	Here : Elem (x :: _) x
	There : Elem xs x -> Elem (_ :: xs) x

||| Proof a value is the last on in the list
data Last : List a -> a -> Type where
	LastOne : Last [value] value
	LastCons : (prf : Last xs value) -> Last (x :: xs) value

||| Example proof.
last123 : Last [1,2,3] 3
last123 = LastCons (LastCons LastOne)

||| Empty lists do not have a last element.
noElemNil : Last [] value -> Void
noElemNil LastOne      impossible
noElemNil (LastCons _) impossible

||| If the value is not the only one in a singleton list, it isn't the last one
||| in the list.
notOnlyNotLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
notOnlyNotLast contra LastOne            = contra Refl
notOnlyNotLast _ (LastCons LastOne)      impossible
notOnlyNotLast _ (LastCons (LastCons _)) impossible

||| If a value is not the last of a non-empty tail, it isn't the last one in
||| the list.
notLastConsTailNotLast : (contra : Last (y :: ys) value -> Void)
                      -> Last (x :: (y :: ys)) value -> Void
notLastConsTailNotLast contra (LastCons prf) = contra prf

||| Decision procedure for the last element of a list.
|||
||| ```idris-repl
||| > isLast [1,2,3] 3
||| Yes (LastCons (LastCons LastOne)) : Dec (Last [1, 2, 3] 3)
||| ```
isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No noElemNil
isLast (x :: []) value = case decEq x value of
	 Yes Refl  => Yes LastOne
	 No contra => No (notOnlyNotLast contra)
isLast (x :: y :: ys) value = case isLast (y :: ys) value of
	 Yes prf   => Yes (LastCons prf)
	 No contra => No (notLastConsTailNotLast contra)
