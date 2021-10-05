module complexity

-- Computation complexity

data Cost : Nat -> Type -> Type where
    MkCost : t -> Cost n t

uncost : Cost n t -> t
uncost (MkCost x) = x

return : t -> Cost n t
return x = MkCost x

-- a Monad!
-- cost of doing dependant computations is the cost of doing both
(>>=) : Cost n a -> (a -> Cost m b) -> Cost (n + m) b
(>>=) (MkCost x) f = MkCost (uncost (f x))

doTimes : Semigroup a =>
          (n : Nat) ->
          Cost m a ->
          a ->
          Cost (n * m) a
doTimes Z _ accum = return accum
doTimes (S k) cost accum = do
    a <- cost
    doTimes k cost (accum <+> a)

-- Complexity of factorial
day : (n : Nat) -> Cost (fact n) String
day Z = return "."
day (S k) = doTimes (S k) (day k) "$"

-- Finite sets are numbers strictly less than some bound
run : (n : Fin 7) -> Cost (fact (finToNat n)) String
run n = day (finToNat n)
