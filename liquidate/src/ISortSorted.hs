{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ISortSorted where 

import Prelude hiding (pure,(<*>),(>>=), length)
import List 
import Language.Haskell.Liquid.ProofCombinators -- ((***), QED, (=>=), (=<=), (===), (?))

import RTick 
import ISort 


theorem :: Ord a => [a] -> [a] -> () 
{-@ theorem :: Ord a => xs:{OList a | 1 < length xs }
            -> ys:{[a] | length xs == length ys } 
            -> {tcost (isort xs) <= tcost (isort ys)} @-} 
theorem xs ys = theoremLow xs ? theoremUpper ys  

theoremLow :: Ord a => [a] -> () 
{-@ theoremLow :: Ord a => xs:{OList a | 1 < length xs}
            -> { tcost (isort xs) <= length xs - 1 } @-} 
theoremLow [_,_] = () 
theoremLow (x:xs)  
  = theoremLow xs  
  ? isortSortedVal xs 

theoremUpper :: Ord a => [a] -> () 
{-@ theoremUpper :: Ord a => xs: {[a] | 1 < length xs } 
            -> { length xs - 1 <= tcost (isort xs) } @-} 
theoremUpper [x,y] 
  =   tcost (isort [x,y])
  ===  tcost (bbind (length [x,y]) (isort [y]) (insert x)) 
  ===  tcost (isort [y]) + tcost (insert x (tval (isort [y]))) 
  *** QED 
theoremUpper (x:xs)
  =   tcost (isort (x:xs))  
  === tcost (bbind (length xs) (isort xs) (insert x))  
  === tcost (isort xs) + tcost (insert x (tval (isort xs)))
      ? theoremUpper xs 
  =>= length xs - 1 + tcost (insert x (tval (isort xs)))   
  =>= length xs     
  *** QED 

















isortSortedVal :: Ord a => [a] -> () 
{-@ isortSortedVal :: Ord a => xs:OList a 
                   -> { tval (isort xs) == xs }  @-}
isortSortedVal [] = ()
isortSortedVal [_] = ()
isortSortedVal (x:xs) = isortSortedVal xs  
