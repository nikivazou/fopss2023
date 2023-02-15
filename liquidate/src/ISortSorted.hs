{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ISortSorted where 

import Prelude hiding (pure,(<*>),(>>=), length)
import List 
import Language.Haskell.Liquid.ProofCombinators 

import RTick 
import ISort 


theorem :: Ord a => [a] -> [a] -> () 
{-@ theorem :: Ord a => xs:OList a
            -> ys:{[a] | length xs == length ys } 
            -> {tcost (isort xs) <= tcost (isort ys)} @-} 
theorem xs ys = undefined 



















isortSortedVal :: Ord a => [a] -> () 
{-@ isortSortedVal :: Ord a => xs:OList a -> { tval (isort xs) == xs }  @-}
isortSortedVal _ = undefined 
