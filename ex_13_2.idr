import Data.Vect

%default total

||| Stack operations tracking stack height at type level.
data StackCmd : Type -> Nat     -> Nat -> Type where
	Push   : Integer -> StackCmd ()      height     (S height)
	Pop    :            StackCmd Integer (S height) height
	Top    :            StackCmd Integer (S height) (S height)
	GetStr :            StackCmd String  height     height
	PutStr : String  -> StackCmd ()      height     height
	Pure   : ty      -> StackCmd ty      height     height
	(>>=) : StackCmd a height1 height2 -> (a -> StackCmd b height2 height3)
	     -> StackCmd b height1 height3

||| Adds the top two elements on the stack.
doAdd : StackCmd () (S (S height)) (S height)
doAdd = do
	val1 <- Pop
	val2 <- Pop
	Push (val1 + val2)

||| Execute a stack command, with a `Vect` as the stack.
runStack : (stk : Vect inHeight Integer) -> StackCmd ty inHeight outHeight
        -> IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure ((), val :: stk)
runStack (val :: stk) Pop = pure (val, stk)
runStack (val :: stk) Top = pure (val, val :: stk)
runStack stk GetStr = do
	x <- getLine
	pure (x, stk)
runStack stk (PutStr x) = do
	putStr x
	pure ((), stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (x >>= f) = do
	(x', newStk) <- runStack stk x
	runStack newStk (f x')

||| Potentially infinite stack programs.
data StackIO : Nat -> Type where
	Do : StackCmd a height1 height2 -> (a -> Inf (StackIO height2))
	  -> StackIO height1

namespace StackDo
	||| `do` notation for combining stack commands into stack programs
	(>>=) : StackCmd a height1 height2 -> (a -> Inf (StackIO height2))
	     -> StackIO height1
	(>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

||| Infinite Fuel.
partial
forever : Fuel
forever = More forever

||| Do a finite number of steps of a infinite process.
run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run (More fuel) stk (Do c f) = do
	(res, newStk) <- runStack stk c
	run fuel newStk (f res)
run Dry stk p = pure ()

||| Possible user inputs.
data StkInput = Number Integer
              | Add
              | Subtract
              | Multiply
              | Negate
              | Discard
              | Duplicate

||| Reads user input for the stack-based calculator.
strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Subtract
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput "discard" = Just Discard
strToInput "duplicate" = Just Duplicate
strToInput x = if all isDigit (unpack x)
	 then Just (Number (cast x))
	 else Nothing

||| Convert binary operator on `Integer` to a stack command.
doBinOp : (Integer -> Integer -> Integer) -> StackCmd () (S (S h)) (S h)
doBinOp f = do
	y <- Pop
	x <- Pop
	Push (f x y)

mutual
	||| Adds the top two elements on the stack, if present.
	tryAdd : StackIO height
	tryAdd {height = (S (S h))} = do
		doAdd
		result <- Top
		PutStr (show result ++ "\n")
		stackCalc
	tryAdd = do
		PutStr "Fewer than two items on the stack\n"
		stackCalc

	||| Operates on the top two elements on the stack, if present.
	tryBin : ({h : Nat} -> StackCmd _ (S (S h)) (S h)) -> StackIO height
	tryBin {height = (S (S k))} f = do
		f
		result <- Top
		PutStr (show result ++ "\n")
		stackCalc
	tryBin _ = do
		PutStr "Fewer than two items on the stack\n"
		stackCalc

	||| Negates the top of the stack, if present.
	tryNegate : StackIO height
	tryNegate {height = S k} = do
		val <- Pop
		let result = negate val
		Push result
		PutStr (show result ++ "\n")
		stackCalc
	tryNegate = do
		PutStr "No items on the stack\n"
		stackCalc

	||| Discards the top of the stack, if present.
	tryDiscard : StackIO height
	tryDiscard {height = (S k)} = do
		val <- Pop
		PutStr ("Discarded " ++ show val ++ "\n")
		stackCalc
	tryDiscard = do
		PutStr "No items on the stack\n"
		stackCalc

	||| Duplicates the top of the stack, if present.
	tryDuplicate : StackIO height
	tryDuplicate {height = (S k)} = do
		val <- Top
		Push val
		PutStr ("Duplicated " ++ show val ++ "\n")
		stackCalc
	tryDuplicate = do
		PutStr "No items on the stack\n"
		stackCalc

	||| Main loop of interactive calculator.
	stackCalc : StackIO height
	stackCalc = do
		PutStr "> "
		input <- GetStr
		case strToInput input of
		 Just Add       => tryAdd
		 Just Subtract  => tryBin (doBinOp (-))
		 Just Multiply  => tryBin (doBinOp (*))
		 Just Negate    => tryNegate
		 Just Discard   => tryDiscard
		 Just Duplicate => tryDuplicate
		 Nothing => do
			PutStr "Invalid input\n"
			stackCalc
		 Just (Number x) => do
			Push x
			stackCalc

||| ```idris-repl
||| > :exec
||| > 5
||| > 3
||| > subtract
||| 2
||| > 8
||| > multiply
||| 16
||| > 10
||| > negate
||| -10
||| > discard
||| Discarded -10
||| > add
||| Fewer than two items on the stack
||| ```
partial
main : IO ()
main = run forever [] stackCalc
