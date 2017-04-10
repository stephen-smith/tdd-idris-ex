import Data.Vect

data DataStore : Type where
	MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size store) newitem = MkData _ (addToData store)
 where
	addToData : Vect oldsize String -> Vect (S oldsize) String
	addToData [] = [newitem]
	addToData (x :: xs) = x :: addToData xs

data Command =
	Add String |
	Get Integer |
	||| Display the number of entries in the store.
	Size |
	||| Display all the entries in the store contaiing a substring
	Search String |
	Quit

{- Added clauses to match "size" and "search". -}
parseCommand : String -> String -> Maybe Command
parseCommand "add"    item      = Just (Add item)
parseCommand "size"   _         = Just Size
parseCommand "search" substring = Just (Search substring)
parseCommand "quit"   _         = Just Quit
parseCommand "get"    val       = if all isDigit (unpack val)
	then Just (Get (cast val))
	else Nothing
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input =
	case span (/= ' ') input of
	 (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = Just (display, store)
 where
	display =
		case integerToFin pos (size store) of
		 Nothing    => "Out of range\n"
		 (Just ndx) => index ndx (items store) ++ "\n"

doSearch : (substring : String) -> (store : DataStore) -> String
doSearch substring store =
	unlines (map displayIndexItem (filter isItemMatch indexed))
 where
	indexed : List (Nat, String)
	indexed = zip [0..(size store)] (toList (items store))
	isItemMatch (_, item) = substring `isInfixOf` item
	displayIndexItem (ndx, item) = show ndx ++ ": " ++ item

{- Added clauses for `Size` and `Search`. -}
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
	case parse input of
	 Nothing                   => Just ("Invalid command\n", store)
	 (Just (Get pos))          => getEntry pos store
	 (Just Size)               => Just (show (size store) ++ "\n", store)
	 (Just (Search substring)) => Just (doSearch substring store, store)
	 (Just Quit)               => Nothing
	 (Just (Add item)) => Just
		("ID " ++ show (size store) ++ "\n"
		, addToStore store item
		)

||| ```idris-repl
||| > :exec
||| Command: add Shearer
||| ID 0
||| Command: add Milburn
||| ID 1
||| Command: add White
||| ID 2
||| Command: size
||| 3
||| Command: search Mil
||| 1:  Milburn
||| Command: quit
||| ```
partial main : IO ()
main = replWith (MkData _ []) "Command: " processInput
