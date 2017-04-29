import Data.Primitives.Views
import System

%default total

||| Session login status.
public export
data Access = LoggedOut | LoggedIn

||| Result of a password check.
public export
data PwdCheck = Correct | Incorrect

||| State transition function based on password check.
public export
CheckAccess : PwdCheck -> Access
CheckAccess Correct   = LoggedIn
CheckAccess Incorrect = LoggedOut

namespace Q1
	||| Security system in which a user can log in with a password and then
	||| read a secret message.
	data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
		Password : String -> ShellCmd PwdCheck LoggedOut CheckAccess
		Logout : ShellCmd () LoggedIn (const LoggedOut)
		GetSecret : ShellCmd String LoggedIn (const LoggedIn)
		PutStr : String -> ShellCmd () state (const state)
		Pure : (res : ty) -> ShellCmd ty (state_fn res) state_fn
		(>>=) : ShellCmd a state1 state2_fn
		     -> ((res : a) -> ShellCmd b (state2_fn res) state3_fn)
		     -> ShellCmd b state1 state3_fn

||| Example session in our security system.
session : ShellCmd () LoggedOut (const LoggedOut)
session = do
	Correct <- Password "wurzel"
	 | Incorrect => PutStr "Wrong password"
	msg <- GetSecret
	PutStr ("Secret code: " ++ show msg ++ "\n")
	Logout

{-
||| Does not verify, fails to handle incorrect passwrd.
sessionBad : ShellCmd () LoggedOut (const LoggedOut)
sessionBad = do
	Password "wurzel"
	msg <- GetSecret
	PutStr ("Secret code: " ++ show msg ++ "\n")
	Logout
-}

{-
||| Does not verify, forgot to log out.
noLogout : ShellCmd () LoggedOut (const LoggedOut)
noLogout = do
	Correct <- Password "wurzel"
	 | Incorrect => PutStr "Wrong password"
	msg <- GetSecret
	PutStr ("Secret code: " ++ show msg ++ "\n")
-}

||| Alias for vending machine state.
VendState : Type
VendState = (Nat, Nat)

||| Result of inserting a coin.
data CoinResult = Inserted | Rejected

||| State transition functor based on coin insert.
StepCoinResult : VendState -> CoinResult -> VendState
StepCoinResult (p, c) Inserted = (S p, c)
StepCoinResult x      Rejected = x

||| Validated user input to vending machine.
data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

||| Vending machine commands
data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
	InsertCoin
	 : MachineCmd CoinResult
	              (pounds, chocs)
	              (StepCoinResult (pounds, chocs))
	Vend : MachineCmd () (S pounds, S chocs) (const (pounds, chocs))
	GetCoins : MachineCmd () (pounds, chocs) (const (Z, chocs))
	Refill : (bars : Nat)
	      -> MachineCmd () (Z, chocs) (const (Z, bars + chocs))
	Display : String -> MachineCmd () state (const state)
	GetInput : MachineCmd (Maybe Input) state (const state)
	Pure : (res : ty) -> MachineCmd ty (state_fn res) state_fn
	(>>=) : MachineCmd a state1 state2_fn
	     -> ((res : a) -> MachineCmd b (state2_fn res) state3_fn)
	     -> MachineCmd b state1 state3_fn

||| Vending machine programs
data MachineIO : VendState -> Type where
	Do : MachineCmd a state1 state2_fn
	  -> ((res : a) -> Inf (MachineIO (state2_fn res)))
	  -> MachineIO state1

namespace MachineDo
	||| Bind for vending machine programs
	(>>=) : MachineCmd a state1 state2_fn
	     -> ((res : a) -> Inf (MachineIO (state2_fn res)))
	     -> MachineIO state1
	(>>=) = Do

mutual
	||| Attempt to vend, if state correct.
	vend : MachineIO (pounds, chocs)
	vend {pounds = Z} {chocs = chocs} = do
		Display "Insufficient Funds"
		machineLoop
	vend {pounds = (S k)} {chocs = Z} = do
		Display "Out of product"
		machineLoop
	vend {pounds = (S p)} {chocs = (S c)} = do
		Vend
		machineLoop

	||| Attempt to refile, if state correct.
	refill : (num : Nat) -> MachineIO (pounds, chocs)
	refill {pounds = Z} num = do
		Refill num
		machineLoop
	refill {pounds = (S k)} _ = do
		Display "Return change before adding product."
		machineLoop

	||| Our vending machine program
	machineLoop : MachineIO (pounds, chocs)
	machineLoop = do
		Just x <- GetInput
		 | Nothing => do
			Display "Invalid input"
			machineLoop
		case x of
		 COIN => do
			cr <- InsertCoin
			case cr of
			 Inserted => machineLoop
			 Rejected => machineLoop
		 VEND => vend
		 CHANGE => do
			GetCoins
			Display "Change returned"
			machineLoop
		 REFILL num => refill num

||| Random acceptance of inserted coin
intToCoinResult : (rand : Integer) -> CoinResult
intToCoinResult rand with (divides rand 12)
 intToCoinResult ((12 * div) + rem) | (DivBy prf) =
	if 0 == rem then Rejected else Inserted

||| Execute a vending machine command
runCommand : MachineCmd r is os -> IO r
runCommand Vend = putStrLn "*thunk*"
runCommand GetCoins = putStrLn "*clink*"
runCommand (Refill bars) = putStrLn ("*inserts " ++ show bars ++ " chocolates*")
runCommand (Display x) = putStrLn x
runCommand GetInput = do
	input <- getLine
	case words (toLower input) of
	 ["coin"]   => pure (Just COIN)
	 ["vend"]   => pure (Just VEND)
	 ["change"] => pure (Just CHANGE)
	 ["refill", n_str]  => if all isDigit (unpack n_str)
		 then pure (Just (REFILL (cast n_str)))
		 else pure Nothing
	 _ => pure Nothing
runCommand (Pure res) = pure res
runCommand (x >>= f) = runCommand x >>= \v => runCommand (f v)
runCommand InsertCoin = do
	rand <- time
	let result = intToCoinResult rand 
	case result of
	 Inserted => putStrLn "*clank*"
	 Rejected => putStrLn "*clink*"
	pure result

||| Execute a vending machine program
partial
run : (start : VendState) -> MachineIO start -> IO ()
run start (Do x f) = runCommand x >>= (\v => run _ (f v))

||| ```idris-repl
||| *ex_14_2> :exec
||| vend
||| Insufficient Funds
||| coin
||| *clank*
||| vend
||| *thunk*
||| vend
||| Insufficient Funds
||| coin
||| *clink*
||| vend
||| Insufficient Funds
||| coin
||| *clank*
||| vend
||| Out of product
||| refill 5
||| Return change before adding product.
||| change
||| *clink*
||| Change returned
||| refill 5
||| *inserts 5 chocolates*
||| vend
||| Insufficient Funds
||| coin
||| *clank*
||| vend
||| *thunk*
||| ```
partial
main : IO ()
main = run (0, 1) machineLoop
