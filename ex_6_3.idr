import Data.Vect

%default total

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) = case xs of
	 [] => Just SString
	 _  => case parseSchema xs of
		 Nothing     => Nothing
		 Just xs_sch => Just (SString .+. xs_sch)
parseSchema ("Int" :: xs) = case xs of
	 [] => Just SInt
	 _  => case parseSchema xs of
		 Nothing     => Nothing
		 Just xs_sch => Just (SInt .+. xs_sch)
parseSchema ("Char" :: xs) = case xs of
	 [] => Just SChar
	 _  => case parseSchema xs of
		 Nothing     => Nothing
		 Just xs_sch => Just (SChar .+. xs_sch)
parseSchema _ = Nothing

SchemaType : Schema -> Type
SchemaType SString   = String
SchemaType SInt      = Int
SchemaType SChar     = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (x .+. y)} (iteml, itemr) =
	display iteml ++ ", " ++ display itemr

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
 where
	getQuoted : List Char -> Maybe (String, String)
	getQuoted ('"' :: xs) = case span (/= '"') xs of
		 (quoted, '"' :: rest) =>
			Just (pack quoted, ltrim (pack rest))
		 _ => Nothing
	getQuoted _ = Nothing
parsePrefix SInt input = case span isDigit input of
	 ("", rest) => Nothing
	 (num, rest) => Just (cast num, ltrim rest)
parsePrefix SChar input = case unpack input of
	 (x :: ' ' :: rest) => Just (x, ltrim (pack rest))
	 _                  => Nothing
parsePrefix (schemal .+. schemar) input = do
	(l_val, input') <- parsePrefix schemal input
	(r_val, input'') <- parsePrefix schemar input'
	pure ((l_val, r_val), input'')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
	 Nothing => Nothing
	 Just (res, "") => Just res
	 Just _ => Nothing

record DataStore where
	constructor MkData
	schema : Schema
	size : Nat
	items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newitem =
	MkData schema _ (addToData items)
 where
	addToData : Vect oldsize (SchemaType schema)
	         -> Vect (S oldsize) (SchemaType schema)
	addToData [] = [newitem]
	addToData (y :: xs) = y :: addToData xs

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = case integerToFin pos (size store) of
	 Nothing => Just ("Out of range\n", store)
	 (Just id) => Just (display (index id (items store)) ++ "\n", store)

{- Instead of `Nat` we should use `Fin k`, but I'm not sure what that looks
 - like.
 -}
mapWithIndex : (Nat -> a -> b) -> Vect k a -> Vect k b
mapWithIndex f xs = mapWithIndex' 0 xs
 where
	mapWithIndex' : Nat -> Vect j a -> Vect j b
	mapWithIndex' n [] = []
	mapWithIndex' n (x :: xs) = f n x :: mapWithIndex' (S n) xs

indexDisplay : Nat -> SchemaType schema -> String
indexDisplay n item = show n ++ ": " ++ display item

getEntries : (store : DataStore) -> String
getEntries store = unlines (toList (mapWithIndex indexDisplay (items store)))

data Command : Schema -> Type where
	SetSchema : (newschema : Schema) -> Command schema
	Add : SchemaType schema -> Command schema
	Get : Maybe Integer -> Command schema
	Quit : Command schema

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand _ "schema" rest = case parseSchema (words rest) of
	 Nothing => Nothing
	 Just schemaok => Just (SetSchema schemaok)
parseCommand schema "add" rest = case parseBySchema schema rest of
	 Just item => Just (Add item)
	 Nothing     => Nothing
parseCommand _ "get" ""  = Just (Get Nothing)
parseCommand _ "get" val = case all isDigit (unpack val) of
	 True  => Just (Get (Just (cast val)))
	 False => Nothing
parseCommand _ "quit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
	 (cmd, args) => parseCommand schema cmd (ltrim args)

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
	 Z     => Just (MkData schema _ [])
	 (S k) => Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse (schema store) input of
	 Nothing               => Just ("Invalid command\n", store)
	 Just Quit             => Nothing
	 Just (Get (Just pos)) => getEntry pos store
	 Just (Get Nothing)    => Just (getEntries store, store)
	 Just (Add item) =>
		Just ("ID " ++ show (size store) ++ "\n"
		     , addToStore store item
		     )
	 Just (SetSchema schema') => case setSchema store schema' of
		 Nothing     => Just ("Can't update schema\n", store)
		 Just store' => Just ("OK\n", store')

||| ```idris-repl
||| *ex_6_3> :exec
||| Command: schema Char Int
||| OK
||| Command: add x 24
||| ID 0
||| Command: add y 17
||| ID 1
||| Command: get 0
||| 'x', 24
||| Command: get
||| 0: 'x', 24
||| 1: 'y', 17
||| ```
partial main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
