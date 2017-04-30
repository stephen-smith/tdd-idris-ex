import Data.Vect

%default total

||| Matrices represented by nested vectors.
Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

||| Example matrix.
testMatrix : Matrix 2 3
testMatrix = [[0, 0, 0], [0, 0, 0]]

||| New constructors for `%c' and `%f`.
data Format = Number Format
            | Str Format
            | Chr Format
            | Float Format
            | Lit String Format
            | End

||| New clauses to cover expanded `Format`.
PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Str fmt) = (str : String) -> PrintfType fmt
PrintfType (Chr fmt) = (c : Char) -> PrintfType fmt
PrintfType (Float fmt) = (f : Double) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

||| New cluases to cover expanded `format`.
printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \str => printfFmt fmt (acc ++ str)
printfFmt (Chr fmt) acc = \c => printfFmt fmt (acc ++ show c)
printfFmt (Float fmt) acc = \f => printfFmt fmt (acc ++ show f)
printfFmt (Lit lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt End acc = acc

||| New clauses to recognize `%c` and `%f`.
toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chr (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Float (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
	 Lit lit chars' => Lit (strCons c lit) chars'
	 fmt => Lit (strCons c "") fmt

||| Type-safe (toy) printf.
|||
||| ```idris-repl
||| > :t printf "%c %f"
||| printf "%c %f" : Char -> Double -> String
||| > printf "%c %f" 'X' 24
||| "'X' 24.0" : String
||| ```
printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

||| Like vectors, but based on nested (heterogenous) pairs.
TupleVect : Nat -> Type -> Type
TupleVect Z     _  = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

||| Example `TupleVect`.
test : TupleVect 4 Nat
test = (1,2,3,4,())
