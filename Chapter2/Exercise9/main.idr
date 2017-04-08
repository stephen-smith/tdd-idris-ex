showRepl : Show r => String -> (String -> r) -> IO ()
showRepl prompt function = repl prompt ((++ "\n") . show . function)

paliCount : String -> (Bool, Nat, Nat)
paliCount s = (reverse l == l, length (words s), length s)
	where
	 l : String
	 l = toLower s

main : IO ()
main = showRepl "Enter a string: " paliCount
