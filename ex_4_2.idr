import Data.Fin
import Data.Vect

%default total

{- Extended with Electricity constructor -}
data PowerSource = Petrol | Pedal | Electricity

{- Fields in a car vary based on power source, so give them their own type. -}
data CarFields : PowerSource -> Type where
	PetrolCF : (fuel : Nat)-> CarFields Petrol
	ElectricCF : (charge : Nat) -> CarFields Electricity

{- Extended to include unicycles, motorcycles, and trams.  Modified for
 - electric cars.
 -}
data Vehicle : PowerSource -> Type where
	Bicycle : Vehicle Pedal
	Car : CarFields power -> Vehicle power
	Bus : (fuel : Nat) -> Vehicle Petrol
	Unicycle : Vehicle Pedal
	Motorcycle : (fuel : Nat) -> Vehicle Petrol
	Tram : Vehicle Electricity

{- Extended to include unicycles, motorcycles, and trams. -}
wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car _) = 4
wheels (Bus _) = 4
wheels Unicycle = 1
wheels (Motorcycle _) = 2
wheels Tram = 4

{- Extended to include motorcycles.  Modified for electric cars. -}
refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car _) = Car (PetrolCF 100)
refuel (Bus _) = Bus 200
refuel (Motorcycle _) = Motorcycle 50

||| ```idris-repl
||| > vectTake 3 [1,2,3,4,5,6,7]
||| [1, 2, 3] : Vect 3 Integer
||| > vectTake 8 [1,2,3,4,5,6,7]
||| (input):2:12:When checking argument prf to function Data.Fin.fromInteger:
|||         When using 8 as a literal for a Fin 8
|||                 8 is not strictly less than 8
||| ```
vectTake : (k : Fin (S n)) -> Vect n a -> Vect (finToNat k) a
vectTake FZ _ = []
vectTake (FS y) (x :: xs) = x :: vectTake y xs

||| Returns the sum of the entries at positon `pos` in each of the inputs if
||| `pos` is within bounds, or `Nothing` otherwise.
|||
||| ```idris-repl
||| > sumEntries 2 [1,2,3,4] [5,6,7,8]
||| Just 10 : Maybe Integer
||| > sumEntries 4 [1,2,3,4] [5,6,7,8]
||| Nothing : Maybe Integer
||| ```
sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys =
	case integerToFin pos n of
	 Nothing => Nothing
	 (Just fp) => Just (index fp xs + index fp ys)
