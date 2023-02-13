> module SortedList where 

We can refine data types to define inductive properties
(like sortedness)

> data SList a = SNil | SCons {lhd :: a, ltl :: SList a}
> {-@ data SList a = SNil 
>                  | SCons {lhd :: a, ltl :: SList {v:a | lhd <= v} } @-}


In this module all lists should be sorted!

> test1 :: SList Int 
> test1 = SCons 1 (SCons 42 SNil)


Let's define insertion sort! 

> insert :: Ord a => a -> SList a -> SList a 
> insert = undefined 


> isort :: Ord a => [a] -> SList a 
> isort = undefined 




Questions: 
- What about build-in Haskell lists?
- Can non-sorded and sorted lists co-exist? 
Liquid Haskell's Answer: Abstract Refinement Types 



Abstract the sortedness predicate from sorted lists: 
{-@ data SList a = SNil 
                  | SCons {lhd :: a, ltl :: SList {v:a | lhd <= v} } @-}


{-@ data AList a = SNil 
                  | SCons {lhd :: a, ltl :: SList {v:a | p lhs v} } @-}


> data List a  = Nil | Cons {llhd :: a, lltl :: List a}
> {-@ data List a <p :: a -> a -> Bool> = 
>             Nil 
>           | Cons {llhd :: a, lltl :: List <p> (a<p llhd>) } @-}


Now this abstract predicate can get instantiated to 
- increasing lists

> {-@ ilist :: List <{\h t -> h <= t}> Int @-}
> ilist :: List Int 
> ilist = Cons 2 (Cons 5 Nil)

- decreasing lists 

> {-@ dlist :: List <{\h t -> h >= t}> Int @-}
> dlist :: List Int 
> dlist = Cons 2 (Cons 1 Nil)

- unique lists 

> {-@ ulist :: List <{\h t -> h /= t}> Int @-}
> ulist :: List Int 
> ulist = Cons 2 (Cons 5 Nil)



These abstract refinement comes, in Liquid Haskell, 
with ghc's build in lists! 

- increasing lists

> {-@ ilist' :: [Int] <{\h t -> h <= t}> @-}
> ilist' :: [Int] 
> ilist' = [2,5]

- decreasing lists 

> {-@ dlist' :: [Int] <{\h t -> h >= t}> @-}
> dlist' :: [Int] 
> dlist' = [2,1]

- unique lists 

> {-@ ulist' :: [Int] <{\h t -> h /= t}> @-}
> ulist' :: [Int] 
> ulist' = [2,5]


Summary: 
Refinements on data types encode inductive properties (e.g., sorteness)
in an encoding that permits _automatic verification_. 
With the abstract refinement technology Liquid Haskell 
  - allows multiple predicates to exist on one data type and 
  - refines build in types (list lists) with inductive predicates. 


Up next: 
 - List Sorting Algorithms
 - Theorem Proving on Lists 









BACK UP, JUST IN CASE isort cannot be defined 

 insert x SNil = SCons x SNil
 insert x (SCons y ys) 
   | x <= y    = SCons x (SCons y ys)
   | otherwise = SCons y (insert x ys)

 isort :: Ord a => [a] -> SList a 
 isort []     = SNil
 isort (x:xs) = insert x (isort xs)




