%default total

||| Score of a Game.
record Score where
	constructor MkScore
	correct   : Nat
	attempted : Nat

||| State as nested records.
record GameState where
	constructor MkGameState
	score      : Score
	difficulty : Int

||| Suitable for interactive output.
Show GameState where
	show st = show (correct (score st))
	       ++ "/"
	       ++ show (attempted (score st))
	       ++ "\n"
	       ++ "Difficulty: "
	       ++ show (difficulty st)

||| Extended to support game state.
data Command : Type -> Type where
	PutStr       : String                        -> Command ()
	GetLine      :                                  Command String
	GetRandom    :                                  Command Int
	GetGameState :                                  Command GameState
	PutGameState : GameState                     -> Command ()
	Pure         : ty                            -> Command ty
	Bind         : Command a -> (a -> Command b) -> Command b

||| Used in the definitions of `correct` and `wrong` instead of `GetGameState`
||| and `PutGameState`.
updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = Bind GetGameState (PutGameState . f)

||| Update attempts by 1.
addWrong : GameState -> GameState
addWrong = record { score->attempted $= (+1) }

||| Update correct answers and attempts by 1.
addCorrect : GameState -> GameState
addCorrect = record
	{ score->correct $= (+1)
	, score->attempted $= (+1)
	}

||| Programs limited to `Command`s.
data ConsoleIO : Type -> Type where
	Quit : a -> ConsoleIO a
	Do   : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
	||| `do` notation for `ConsoleIO`.
	(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
	(>>=) = Do

mutual
	||| Implemented in terms of `Applicative`.
	Functor Command where
		map func x = Pure func <*> x

	||| Implemented in terms of `Pure` constructor and `Monad`.
	Applicative Command where
		pure = Pure
		(<*>) x y = do
			f <- x
			v <- y
			Pure (f v)

	||| Implemented in terms of `Bind` constructor.
	Monad Command where
		(>>=) x f = Bind x f

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
	||| Example of using updateGameState
	correct : ConsoleIO GameState
	correct = do
		PutStr "Correct!\n"
		updateGameState addCorrect
		quiz

	||| Another example of using updateGameState
	wrong : Int -> ConsoleIO GameState
	wrong ans = do
		PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
		updateGameState addWrong
		quiz

	||| Required by `correct` and `wrong`.
	quiz : ConsoleIO GameState
	quiz = do
		num1 <- GetRandom
		num2 <- GetRandom
		st <- GetGameState
		PutStr (show st ++ "\n")
		input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
		case input of
		 Answer answer => if answer == num1 * num2
			 then correct
			 else wrong (num1 * num2)
		 QuitCmd => Quit st

||| Number of times an article has been upvoted and downvoted.
record Votes where
	constructor MkVotes
	upvotes   : Integer
	downvotes : Integer

||| An article on a social news website.
record Article where
	constructor MkArticle
	title : String
	url   : String
	score : Votes

||| Fresh article at submission time.
initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

||| Calculate the overall score of a given article, where the store is
||| calculated from the number of downvotes subtracted from the number
||| of upvotes..
|||
||| ```idris-repl
||| > getScore goodSite
||| 94 : Integer
||| > getScore badSite
||| -42 : Integer
||| ```
getScore : Article -> Integer
getScore a = upvotes v - downvotes v
 where v = score a

||| Downvotes example.
badSite : Article
badSite = MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 47)

||| Upvoted example.
goodSite : Article
goodSite = MkArticle "Good Page" "http://example.com/good" (MkVotes 101 7)

||| Modify an article's score up.
|||
||| ```idris-repl
||| > addUpvote goodSite
||| MkArticle "Good Page" "http://example.com/good" (MkVotes 102 7) : Article
||| > getScore (addUpvote goodSite)
||| 95 : Integer
||| ```
addUpvote : Article -> Article
addUpvote a = record { score->upvotes $= (+1) } a

||| Modify an article's score down.
|||
||| ```idris-repl
||| > addDownvote badSite
||| MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 48) : Article
||| ```
addDownvote : Article -> Article
addDownvote a = record { score->downvotes $= (+1) } a
