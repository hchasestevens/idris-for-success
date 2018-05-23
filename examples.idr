module Main

main : IO ()
main = putStrLn ?x
--
-- boolToInt : Bool -> Int
-- -- boolToInt x = ?boolToInt_rhs
-- boolToInt False = ?boolToInt_rhs_1
-- boolToInt True = ?boolToInt_rhs_2


data Vect : Nat -> Type -> Type where
    Nil  : Vect Z a
    (::) : a -> Vect k a -> Vect (S k) a
--
len : Vect n a -> Int
len {n} x -> n

myList : Vect 3 Int
myList = [1, 2, 3]

zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f [] [] = []
zipWith f (x :: z) (y :: w) = f x y :: zipWith f z w

head : Vect (S n) a -> a
head (x :: _) = x
--
tail : Vect (S n) a -> Vect n a
tail (_ :: xs) = xs

data Fin : Nat -> Type where
  FZ : Fin (S k)
  FS : Fin k -> Fin (S k)

index : Fin n -> Vect n a -> a
index FZ (x :: y) = x
index (FS x) (y :: z) = y


data Format = Number Format
            | Str Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Str fmt) = (str : String) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \str => printfFmt fmt (acc ++ str)
printfFmt (Lit lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                             Lit lit chars' => Lit (strCons c lit) chars'
                             fmt => Lit (strCons c "") fmt
printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""


data DoorState = DoorOpen | DoorClosed

data DoorCmd : Type -> DoorState -> DoorState -> Type where
     Open : DoorCmd () DoorClosed DoorOpen
     Close : DoorCmd () DoorOpen DoorClosed
     RingBell : DoorCmd () DoorClosed DoorClosed

     Pure : ty -> DoorCmd ty state state
     (>>=) : DoorCmd a state1 state2 ->
             (a -> DoorCmd b state2 state3) ->
             DoorCmd b state1 state3

doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do RingBell
              Open
              Close
