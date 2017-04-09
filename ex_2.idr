q1_1 : (String, String, String)
q1_1 = ("A", "B", "C")

q1_2 : List String
q1_2 = ["A", "B", "C"]

q1_3 : ((Char, String), Char)
q1_3 = (('A', "B"), 'C')

||| Returns whether the input reads the same backwqards as forwards.
|||
||| ```idris-repl
||| > palindrome_q2 "racecar"
||| True : Bool
||| > palindrome_q2 "race car"
||| False : Bool
||| ```
palindrome_q2 : String -> Bool
palindrome_q2 s = reverse s == s

||| `palindrome_q2` that is not case sensitive
|||
||| ```idris-repl
||| > palindrome_q3 "Racecar"
||| True : Bool
||| ```
palindrome_q3 : String -> Bool
palindrome_q3 s = reverse l == l
	where
	 l : String
	 l = toLower s

||| `palindrome_q3` that only returns `True` for strings longer than 10
||| characters.
|||
||| ```idris-repl
||| > palindrome_q4 "racecar"
||| False : Bool
||| > palindrome_q4 "able was i ere i saw elba"
||| True : Bool
||| ```
palindrome_q4 : String -> Bool
palindrome_q4 s = 10 < length s && reverse l == l
	where
	 l : String
	 l = toLower s

||| `palindrome_q4` that takes minimum length as an argument instead of
||| hard-coding 10.
|||
||| ```idris-repl
||| > palindrome 10 "racecar"
||| False : Bool
||| > palindrome 5 "racecar"
||| True : Bool
||| ```
palindrome : Nat -> String -> Bool
palindrome n s = n < length s && reverse l == l
	where
	 l : String
	 l = toLower s

||| Return a pair of the number of words in the input and the number of
||| characters in the input.
||| ```idris-repl
||| > counts "Hello, Idris world!"
||| (3, 19) : (Nat, Nat)
||| ```
counts : String -> (Nat, Nat)
counts s = (length (words s), length s)

||| Returns the ten largest values in a list.
||| ```idris-repl
||| > top_ten [1..100]
||| [100, 99, 98, 97, 96, 95, 94, 93, 92, 91] : List Integer
||| ```
top_ten : Ord a => List a -> List a
top_ten l = take 10 (reverse (sort l))

||| Returns the number of strings in the list longer than the given number of
||| characters.
||| ```idris-repl
||| > over_length 3 ["One", "Two", "Three", "Four"]
||| 2 : Nat
||| ```
over_length : Nat -> List String -> Nat
over_length _ [] = 0
over_length k (x :: xs) = (if k < length x then S else id) (over_length k xs)

||| Variant of `repl` that shows the result and adds a newline.
showRepl : Show r => String -> (String -> r) -> IO ()
showRepl prompt function = repl prompt ((++ "\n") . show . function)

||| Combines `palindrome` and `counts` into a function suitable for use with
||| `showRepl`.
paliCount : String -> (Bool, (Nat, Nat))
paliCount s = (palindrome 0 s, counts s)

||| Prompts for an input, calls `paliCount` and prints its output.
||| ```idris-repl
||| > :exec
||| Enter a string: Able was I ere I saw Elba
||| (True, 7, 25)
||| Enter a string: Madam I'm Adam
||| (False, 3, 14)
||| Enter a string:
||| ```
main : IO ()
main = showRepl "Enter a string: " paliCount
