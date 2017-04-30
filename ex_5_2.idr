import Data.String
import System

%default total

||| Sequencing without passing values.
(>>) : Monad m => m () -> m a -> m a
mv >> mx = mv >>= const mx

||| Implements a simple "guess the number" game.
partial
guess_q1 : (target : Nat) -> IO ()
guess_q1 target = loop
 where
	loop = do
		putStr "Guess a number: "
		input <- getLine
		case the (Maybe Nat) (parsePositive input) of
		 (Just inGuess) => case compare inGuess target of
			 LT => putStrLn "Too low."  >> loop
			 EQ => putStrLn "Correct!"
			 GT => putStrLn "Too high." >> loop
		 Nothing => putStrLn "That's not a (positive) number!" >> loop

||| Counts the number of guesses the user has taken and displays the number
||| before the input is read.
partial
guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = loop guesses
 where
	loop guesses = do
		putStrLn (show guesses ++ " guesses so far.")
		putStr "Guess a number: "
		input <- getLine
		case the (Maybe Nat) (parsePositive input) of
		 (Just inGuess) => case compare inGuess target of
			 LT => putStrLn "Too low."  >> loop (S guesses)
			 EQ => putStrLn "Correct!"
			 GT => putStrLn "Too high." >> loop (S guesses)
		 Nothing => do
			putStrLn "That's not a (positive) number!"
			loop guesses

||| Chooses a random number between 1 and 100 and then calls guess.
partial
main : IO ()
main = do
	secs <- time
	guess (fromInteger (secs `mod` 100 + 1)) 0

||| Like `replWith`, but allows the step function to signal termination via
||| `Nothing`.
partial
my_replWith : (initialState : a)
           -> (prompt : String)
           -> (a ->  String -> Maybe (String, a))
           -> IO ()
my_replWith oldstate prompt f = do
	putStr prompt
	input <- getLine
	case f oldstate input of
	 Nothing         => pure ()
	 (Just (output, newstate)) => do
		putStrLn output
		my_replWith newstate prompt f

||| List `repl`, but terminating on `Nothing`.
partial
my_repl : (prompt : String) -> (String -> String) -> IO ()
my_repl prompt f = my_replWith () prompt (\s, input => Just (f input, s))
