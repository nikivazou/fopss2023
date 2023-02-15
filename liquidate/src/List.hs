module List where 

import Prelude hiding (length, head)

{-@ measure length @-}
{-@ length :: [a] -> Nat @-} 
length :: [a] -> Int 
length []      = 0 
length (_:xs) = 1 + length xs 

head :: [a] -> a 
{-@ head :: xs:{[a] | 0 < length xs } -> a @-}
head (x:_) = x  