module algebraic

-- Algebraic laws

data Bit = O | I

or : Bit -> Bit -> Bit
or 0 x1 = x1
or I x1 = I

orAssociative  : (a : Bit) ->
                 (b : Bit) ->
                 (c : Bit) ->   
                 (a `or` b) `or` c = a `or` (b `or` c)
-- or = ?orAssociative_rhs_1
orAssociative O b c = refl
-- or = ?orAssociative_rhs_2                
orAssociative I b c = refl


BitString : Type
-- list of bits
BitString = List Bit

bsor : BitString -> BitString -> BitString
bsor [] x1 = x1
bsor xs [] = xs
bsor (x :: xs) (y :: ys) = (x `or` y) :: (xs `bsor` ys)
