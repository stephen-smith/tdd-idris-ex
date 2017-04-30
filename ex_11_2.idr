%default total

||| Infinite interactice processes.
data InfIO : Type where
	Do : IO a -> (a -> Inf InfIO) -> InfIO

||| Do notation bind for infinite interactive processes
(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

||| New version of `repl` using `InfIO`.
|||
||| ```idris-repl
||| > :total totalREPL
||| Main.totalREPL is Total
||| > :exec run forever (totalREPL "\n: " toUpper)
|||
||| : Hello [user input]
||| HELLO
||| : World [user input]
||| WORLD
||| ```
totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = loop
 where loop = do
	putStr prompt
	input <- getLine
	putStr (action input)
	loop

||| Length of time a process can run.
data Fuel = Dry | More (Lazy Fuel)

||| Convert an expression of type `InfIO` to an executable `IO` action running
||| for a finite time
run : Fuel -> InfIO -> IO ()
run Dry         p        = putStrLn "Out of fuel"
run (More fuel) (Do c f) = do
	res <- c
	run fuel (f res)

||| Inifinite fuel.
partial
forever : Fuel
forever = More forever
