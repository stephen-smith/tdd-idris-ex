data Elem : List e -> e -> Type where
	Here : Elem (x :: _) x
	There : Elem xs x -> Elem (_ :: xs) x

data Last : List a -> a -> Type where
	LastOne : Last [value] value
	LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1,2,3] 3
last123 = LastCons (LastCons LastOne)

noElemNil : Last [] value -> Void
noElemNil LastOne      impossible
noElemNil (LastCons _) impossible

notOnlyNotLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
notOnlyNotLast contra LastOne            = contra Refl
notOnlyNotLast _ (LastCons LastOne)      impossible
notOnlyNotLast _ (LastCons (LastCons _)) impossible

notLastConsTailNotLast : (contra : Last (y :: ys) value -> Void)
                      -> Last (x :: (y :: ys)) value -> Void
notLastConsTailNotLast contra (LastCons prf) = contra prf

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
