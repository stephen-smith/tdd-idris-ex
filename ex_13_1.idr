%default total

-- Namespaces to isolate different `(>>=)` and `Pure`.
namespace Q1
	||| All valid door states.
	data DoorState = DoorClosed | DoorOpen

	||| Model of door state machine describing state transitions in the
	||| types of the commands.
	data DoorCmd : Type -> DoorState -> DoorState -> Type where
		Open     :       DoorCmd () DoorClosed DoorOpen
		Close    :       DoorCmd () DoorOpen   DoorClosed
		RingBell :       DoorCmd () state      state
		Pure     : ty -> DoorCmd ty state      state
		(>>=) : DoorCmd a state1 state2
		     -> (a -> DoorCmd b state2 state3)
		     -> DoorCmd b state1 state3

	||| Shows `RingBell` can be used in any state.
	doorProg : DoorCmd () DoorClosed DoorClosed
	doorProg = do
		RingBell
		Open
		RingBell
		Close

namespace Q2
	||| Command for a guessing games where the state is the number of
	||| remaining guesses.
	data GuessCmd : Type -> Nat -> Nat -> Type where
		Try  : Integer -> GuessCmd Ordering (S k) k
		Pure : ty      -> GuessCmd ty       state state
		(>>=) : GuessCmd a state1 state2
		     -> (a -> GuessCmd b state2 state3)
		     -> GuessCmd b state1 state3

	||| Should type check
	threeGuesses: GuessCmd () 3 0
	threeGuesses = do
		Try 10
		Try 20
		Try 15
		Pure ()

	{-
	||| Should not type check (bad type for `Try`)
	noGuesses : GuessCmd () 0 0
	noGuesses = do
		Try 10
		Pure ()
	-}

||| Primary 4 phases of matter.
data Matter = Solid | Liquid | Gas | Plasma

||| Commands with phase transitions named.
data MatterCmd : Type -> Matter -> Matter -> Type where
	Melt      : MatterCmd () Solid Liquid
	Boil      : MatterCmd () Liquid Gas
	Condense  : MatterCmd () Gas Liquid
	Freeze    : MatterCmd () Liquid Solid
	Deposit   : MatterCmd () Gas Solid
	Sublimate : MatterCmd () Solid Gas
	Ionize    : MatterCmd () Gas Plasma
	Recombine : MatterCmd () Plasma Gas
	(>>=) : MatterCmd a is ms -> (a -> MatterCmd b ms os)
	     -> MatterCmd b is os

||| Water transition from `Solid` to `Gas` at normal pressures.
iceSteam : MatterCmd () Solid Gas
iceSteam = do
	Melt
	Boil

||| Water transition from `Gas` to `Solid` at normal pressures.
steamIce : MatterCmd () Gas Solid
steamIce = do
	Condense
	Freeze

{-
||| Invalid phase transition (bad type for second `Melt`).
overMelt : MatterCmd () Solid Gas
overMelt = do
	Melt
	Melt
-}
