> module List where 
> import Prelude hiding (length, take)
> import Data.Set 


> data List a = Nil | Cons a (List a)

Measures: functions on one data type argument 
that can be used in the logic.


> {-@ measure length @-}
> {-@ length :: List a -> Nat @-} 
> length :: List a -> Int 
> length Nil         = 0 
> length (Cons _ xs) = 1 + length xs 


Reasoning about length is automatic! 
(because of its one-argument restriction)

> {-@ append :: xs:List a -> ys:List a 
>            -> {o:List a | length o == length xs + length ys } @-} 
> append :: List a -> List a -> List a 
> append Nil         ys = ys 
> append (Cons x xs) ys = Cons x (append xs ys)



> {-@ test1 :: {xs:List Int | length xs == 4} @-} 
> test1 :: List Int 
> test1 = Cons 1 (Cons 2 Nil) `append` Cons 2 (Cons 3 Nil)




Common Property I: Totality 
Liquid Haskell automatically check that functions are 
_total_, i.e., defined for all inputs. 
Let's make `head` and `tail` total: 

 head :: List a -> a 
 head (Cons x _) = x 

 tail :: List a -> List a 
 tail (Cons _ xs) = xs 




Common Property II: Termination 
- syntactic termination 

 take :: Int -> List a -> List a 
 take 0 _ = Nil 
 take i ys@(Cons x xs) = Cons x (take i ys)

Let's define `take`:
- Make it total.
- Make it terminating. 
- Any interesting postconditions? 


- lexicographic termination 



> {-@ merge :: Ord a
>            => xs:List a -> ys:List a -> List a 
>            / [length xs + length ys]
>   @-}
> merge :: Ord a => List a -> List a -> List a
> merge (Cons a as') (Cons b bs')
>   | a > b     = b `Cons` merge (Cons a as')  bs'
>   | otherwise = a `Cons` merge as' (Cons b bs')
> merge Nil bs            = bs
> merge as Nil            = as

Common Property III: Sets 

> {-@ measure toSet @-}
> toSet :: Ord a => List a -> Set a 
> toSet Nil = empty 
> toSet (Cons x xs) = singleton x `union` toSet xs

Q: Revisit the previous functions to talk about toSet! 




Summary: 
Measures to talk about data type properties 
1. Termination 
2. Totality
3. Sets 

Next: 
- Sortedness 
- Theorem proving
