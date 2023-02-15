Introduction to Refinement Types 
---------------------------------

>  module Intro where 

Refinement Types are standard types (here Haskell's) refined with logical predicates. 
For example, we refine the Haskell integer type to encode 
- natural numbers and 
- singletons (here exactly equal to 42). 

> {-@ fourtytwo :: {v:Int | 42 == v } @-}
> fourtytwo :: Int
> fourtytwo = 40


> {-@ zero :: {v:Int | 0 <= v } @-}
> zero :: Int
> zero = 0

Since natural numbers are a common refinement, 
we can define a type alias for them.

> {-@ type Nat = {v:Int | 0 <= v } @-}

> {-@ zero' :: Nat @-}
> zero' :: Int
> zero' = 0


Refinement Types are Preconditions 
e.g., to avoid division by zero.

(/) :: Integral a => x:a -> y:{a | y /= 0} -> a 

> test1 :: Integer 
> test1 = 42 `div` 42 


1. Let's change divisior to 0! 
2. Let's change divisior to a variable! 
 


> {-@ div42 :: x:{Int | x /= 0} -> Int @-}
> div42 :: Int -> Int 
> div42 x = 42 `div` x 

Attention: preconditions must be proved! 

> test2 :: Int 
> test2 = div42 42



Refinement Types for Postconditions 

> {-@ myabs :: x:Int -> {v:Nat | x <= v} @-}
> myabs :: Int -> Int 
> myabs x = if 0 <= x then x else -x 

> test3 :: Int -> Int 
> test3 x = div42 (myabs x + 1)



What is included in the refinement logic? 
- Decidable SMT logic (bools, arithmetic, but not forall/exists)
- SMT data types (e.g., sets and other inductively defined data types)
- Liquid Haskell Constructs (coming next)
    - measures 
    - inlines 
    - reflected functions 



Summary: 
Refinement Types Refine Haskell's types with "SMT" logic (for now)
to define pre- and post-conditions (e.g., no division by zero).    

