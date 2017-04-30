import Data.Primitives.Views
import System

import ex_11_1

%default total

||| Length of time a process can run.
data Fuel = Dry | More (Lazy Fuel)

||| Inifinite fuel.
partial
forever : Fuel
forever = More forever

||| Defines the IO commands that are available. Extended with ability to read
||| and write files.
data Command : Type -> Type where
	PutStr  : String -> Command ()
	GetLine : Command String
	ReadFile : String -> Command (Either FileError String)
	WriteFile : String -> String -> Command (Either FileError ())
	Pure : ty -> Command ty
	Bind : Command a -> (a -> Command b) -> Command b

||| Programs limites to `Command`s.
data ConsoleIO : Type -> Type where
	Quit : a -> ConsoleIO a
	Do   : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace CommandDo
	||| Do notation bind for commands.
	(>>=) : Command a -> (a -> Command b) -> Command b
	(>>=) = Bind

namespace ConsoleDo
	||| Do notation bind for console i/o programs
	(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
	(>>=) = Do

||| `quiz` input.
data Input = Answer Int | QuitCmd

||| Composite command for reading and parsing input.
readInput : (prompt : String) -> Command Input
readInput prompt = do
	PutStr prompt
	answer <- GetLine
	if toLower answer == "quit"
	 then Pure QuitCmd
	 else Pure (Answer (cast answer))

mutual
	||| Loop with updated state on correct answer.
	correct : Stream Int -> (score : Nat) -> Nat -> ConsoleIO (Nat, Nat)
	correct nums score attempts = do
		PutStr "Correct!\n"
		quiz nums (S score) attempts

	||| Loop with updated state on incorrect answer.
	wrong : Stream Int -> Int -> (score : Nat) -> Nat
	     -> ConsoleIO (Nat, Nat)
	wrong nums ans score attempts = do
		PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
		quiz nums score attempts

	||| Updated to keep track of the total number of questions attempted.
	|||
	||| ```idris-repl
	||| > :exec
	||| Score so far: 0 / 0
	||| 9 * 11? 99
	||| Correct!
	||| Score so far: 1 / 1
	||| 6 * 9? 42
	||| Wrong, the answer is 54
	||| Score so far: 1 / 2
	||| 10 * 2? 20
	||| Correct!
	||| Score so far: 2 / 3
	||| 7 * 2? quit
	||| Final score: 2 / 3
	||| ```
	quiz : Stream Int -> (score : Nat) -> Nat -> ConsoleIO (Nat, Nat)
	quiz (num1 :: num2 :: nums) score attempts = do
		PutStr "Score so far: "
		PutStr (show score ++ " / " ++ show attempts ++ "\n")
		input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
		case input of
		 QuitCmd       => Quit (score, attempts)
		 Answer answer =>
			if answer == num1 * num2
			 then correct nums score (S attempts)
			 else wrong nums (num1 * num2) score (S attempts)

||| Generates suitable quiz inputs.
arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
 where
	bound : Int -> Int
	bound x with (divides x 12)
	 bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

||| Run a `ConsoleIO` by using the corresponding I/O action.
runCommand : Command a -> IO a
runCommand (PutStr x)      = putStr x
runCommand GetLine         = getLine
runCommand (ReadFile x)    = readFile x
runCommand (WriteFile x y) = writeFile x y
runCommand (Pure x)        = pure x
runCommand (Bind x f)      = do
	x' <- runCommand x
	runCommand (f x')

||| Run `ConsoleIO`.
run : Fuel -> ConsoleIO a -> IO (Maybe a)
run fuel        (Quit val) = pure (Just val)
run Dry         p          = pure Nothing
run (More fuel) (Do c f) = do
	res <- runCommand c
	run fuel (f res)

||| Generate `Command` from shell input:
|||
||| * `cat [filename]` reads a file and display the contents.
||| * `copy [source] [destination]` reads a source file and writes its contents
|||   to a destination file.
||| * `exit` (`Nothing` return) indicating the shell should exit.
shellCommand : String -> Maybe (Command ())
shellCommand input = case words input of
	 [] => Just (Pure ())
	 ("cat" :: filename :: []) => Just (do
		Right fileContents <- ReadFile filename
		 | Left error =>
			PutStr ("Could not read file: " ++ show error ++ "\n")
		PutStr fileContents
		)
	 ("copy" :: source :: destination :: []) => Just (do
		Right fileContents <- ReadFile source
		 | Left error =>
			PutStr ("Could not read file: " ++ show error ++ "\n")
		Right ok <- WriteFile destination fileContents
		 | Left error =>
			PutStr ("Could not write file: " ++ show error ++ "\n")
		Pure ok
		)
	 ("exit" :: []) => Nothing
	 _ => Just (PutStr ("Invalid command: " ++ input ++ "\n"))

||| Console shell.
shell : ConsoleIO ()
shell = do
	PutStr "> "
	input <- GetLine
	case shellCommand input of
	 Nothing  => Quit ()
	 Just cmd => do
		cmd
		shell

||| Run the console shell forever.
|||
||| ```idris-repl
||| > :exec shellMain
||| > cat test2
||| Could not read file: File Not Found
||| > cat test
||| Idris is productive.
||| > copy test test2
||| > cat test2
||| Idris is productive.
||| > exit
||| ```
partial
shellMain : IO ()
shellMain = do
	Just ok <- run forever shell
	 | Nothing => putStrLn "Ran out of fuel"
	pure ok

||| Execute the quiz and display the final score.
partial
main : IO ()
main = do
	seed <- time
	let myQuiz = quiz (arithInputs (fromInteger seed))
	Just (score, attempts) <- run forever (myQuiz 0 0)
	 | Nothing => putStrLn "Ran out of fuel"
	putStrLn ("Final score: " ++ show score ++ " / " ++ show attempts)
