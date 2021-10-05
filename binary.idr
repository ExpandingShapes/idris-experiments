module binary

-- Binary literals

data BinChar : Char -> Type Where
  O : BinChar '0'
  I : BinChar '1'

  data Every : (a -> Type) -> List a -> Type where
    Nil : {P : a -> Type} -> Every P []
    (::) : {P : a -> Type} -> P x -> Every P xs -> Every P (x :: xs)

-- For every BinChar in some list get a natural number
-- How many bits do we have?
fromBinChars : Every Binchar xs -> Nat -> Nat
fromBinChars [] _ = 0
fromBinChars (O :: ys) k = fromBinChats ys (k - 1)
fromBinChats (I :: ys) k = pow 2 k + fromBinChats ys (k - 1)

-- Proof?
b: (s : String) -> {auto p: Every BinChar (unpack s)} -> Nat
-- Use the proof
b {p} s = fromBinChats p (length s - 1)

example1 : b"101" = 5
example1 = refl
