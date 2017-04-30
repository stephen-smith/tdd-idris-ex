%default total

||| Reads two strings and then displays the length of the longer string.
printLonger_q1 : IO ()
printLonger_q1 = do
	putStr "First string: "
	first <- getLine
	putStr "Second string: "
	second <- getLine
	putStrLn (show (max (length first) (length second)))

||| Same as `printLonger`.
|||
||| ```idris-repl
||| > :exec printLonger
||| First string: short
||| Second string: longer
||| 6
||| ```
printLonger : IO ()
printLonger =
	               putStr "First string: "
	>>= \_      => getLine
	>>= \first  => putStr "Second string: "
	>>= \_      => getLine
	>>= \second => putStrLn (show (max (length first) (length second)))

||| Proof of `do` and bind (>>=) equivalence.
sameProgram : Main.printLonger = Main.printLonger_q1
sameProgram = Refl
