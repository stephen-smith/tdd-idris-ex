import Control.Monad.State

%default total

||| Updates a state by applying a function to the current state.
|||
||| ```idris-repl
||| > runState (increase 5) 89
||| ((), 94) : ((), Nat)
||| ```
update : (stateType -> stateType) -> State stateType ()
update f = map f get >>= put

||| Stateful function that increases a state by a given value.
increase : Nat -> State Nat ()
increase x = update (+x)

||| Binary trees.
data Tree a = Empty
            | Node (Tree a) a (Tree a)

||| Counts the number of occurences of `Empty` in a tree.
|||
||| ```idris-repl
||| > execState (countEmpty testTree) 0
||| 7 : Nat
||| ```
countEmpty : Tree a -> State Nat ()
countEmpty Empty = update S
countEmpty (Node r _ l) = countEmpty l >>= \_ => countEmpty r

||| An example.
testTree : Tree String
testTree = Node
	(Node (Node Empty "Jim" Empty) "Fred" (Node Empty "Sheila" Empty))
	"Alice"
	(Node Empty "Bob" (Node Empty "Eve" Empty))

||| Counts the number of occurences of both `Empty` and `Node` in a tree.
|||
||| ```idris-repl
||| > execState (countEmptyNode testTree) (0, 0)
||| (7, 6) : (Nat, Nat)
||| ```
countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = update (\(empty, node) => (S empty, node))
countEmptyNode (Node r _ l) = do
	countEmptyNode r
	update (\(empty, node) => (empty, S node))
	countEmptyNode l
