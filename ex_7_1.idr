%default total

||| Simple 2D geometric shapes.
data Shape = Triangle  Double Double
           | Rectangle Double Double
           | Circle    Double

||| ```idris-repl
||| > Circle 4 == Circle 4
||| True : Bool
||| > Circle 4 == Circle 5
||| False : Bool
||| > Circle 4 == Triangle 3 2
||| False : Bool
||| ```
Eq Shape where
	(==) (Triangle x z)  (Triangle y w)  = x == y && z == w
	(==) (Triangle _ _)  (Rectangle _ _) = False
	(==) (Triangle _ _)  (Circle _)      = False
	(==) (Rectangle _ _) (Triangle _ _)  = False
	(==) (Rectangle x z) (Rectangle y w) = x == y && z == w
	(==) (Rectangle _ _) (Circle _)      = False
	(==) (Circle _)      (Triangle _ _)  = False
	(==) (Circle _)      (Rectangle _ _) = False
	(==) (Circle x)      (Circle y)      = x == y
	(/=) x = not . (==) x

||| 2D area of a shape.
area : Shape -> Double
area (Triangle w h)  = 0.5 * w * h
area (Rectangle w h) =       w * h
area (Circle r)      =  pi * r * r

||| Comparison by area.
Ord Shape where
	compare x y = compare (area x) (area y)
	(<) x y = compare x y == LT
	(>) x y = compare x y == GT
	(<=) x y = compare x y /= GT
	(>=) x y = compare x y /= LT
	max x y = if x < y then y else x
	min x y = if y < x then y else x

||| Example shapes.
|||
||| ```idris-repl
||| > sort testShapes
||| [Rectangle 2.0 6.0,
|||  Triangle 3.0 9.0,
|||  Rectangle 2.0 7.0,
|||  Circle 3.0,
|||  Circle 4.0] : List Shape
||| ```
testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]
