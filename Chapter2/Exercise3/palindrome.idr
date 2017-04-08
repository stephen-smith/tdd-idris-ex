palindrome : String -> Bool
palindrome s = reverse l == l
	where
	 l : String
	 l = toLower s
