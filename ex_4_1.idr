%default total

||| Binary Search Tree
data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

insert : Ord a => a -> Tree a -> Tree a
insert x Empty = Node Empty x Empty
insert x orig@(Node left pivot right) =
	case compare x pivot of
	 LT => Node (insert x left) pivot right
	 EQ => orig
	 GT => Node left pivot (insert x right)

||| Inserts every element of a list into a binary search tree.
||| ```idris-repl
||| > listToTree [1,4,3,5,2]
||| Node (Node Empty 1 Empty)
|||      2
|||      (Node (Node Empty 3 (Node Empty 4 Empty)) 5 Empty) : Tree Integer
||| ```
listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

||| _Flattens_ a tree into a list using _in-order_ traversal.
||| ```idris-repl
||| > treeToList (listToTree [4,1,8,7,2,3,9,5,6])
||| [1, 2, 3, 4, 5, 6, 7, 8, 9] : List Integer
||| ```
treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node left pivot right) = treeToList left ++ [pivot] ++ treeToList right

||| Integer Arithmetic Expressions
data Expr =
	||| A single integer
	Val Int |
	||| Addition of an expression to an expression
	Add Expr Expr |
	||| Subtraction of an expression from an expression
	Sub Expr Expr |
	||| Multiplication of an expression with an expression
	Mult Expr Expr

||| Evaluates an integer arithmetic expression.
||| ```idris-repl
||| > evaluate (Mult (Val 10) (Add (Val 6) (Val 3)))
||| 90 : Int
||| ```
evaluate : Expr -> Int
evaluate (Val value) = value
evaluate (Add augend addend) = evaluate addend + evaluate augend
evaluate (Sub subtrahend minuend) = evaluate minuend - evaluate subtrahend
evaluate (Mult multiplicand multiplier) = evaluate multiplier * evaluate multiplicand

||| Returns the larger of the two inputs, or `Nothing` if both inputs are
||| `Nothing`.
|||
||| ```idris-repl
||| > maxMaybe (Just 4) (Just 5)
||| Just 5 : Maybe Integer
||| > maxMaybe (Just 4) Nothing
||| Just 4 : Maybe Integer
||| ```
maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing y = y
maxMaybe x@(Just _) Nothing = x
maxMaybe (Just x) (Just y) = Just (max x y)

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

||| Returns the area of the biggest trinagle in a picture, or `Nothing` if
||| there are no triangles.
||| ```idris-repl
||| > biggestTrinagle testPic1
||| Just 4.0 : Maybe Double
||| > biggestTrinagle testPic2
||| Nothing : Maybe Double
||| ```
biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive (Triangle x y)) = Just (x * y / 2)
biggestTriangle (Primitive (Rectangle _ _)) = Nothing
biggestTriangle (Primitive (Circle _)) = Nothing
biggestTriangle (Combine x y) = maxMaybe (biggestTriangle x) (biggestTriangle y)
biggestTriangle (Rotate _ p) = biggestTriangle p
biggestTriangle (Translate _ _ p) = biggestTriangle p

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3)) (Primitive (Triangle 2 4))

testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3)) (Primitive (Circle 4))
