{-@ LIQUID "--reflection" @-}
module ISort where 

import Prelude hiding (pure,(<*>),(>>=), length, head)
import List 
import RTick 


{-@ type OList a = [a]<{\x y -> x <= y}> @-}

{-@ reflect insert @-}
insert :: (Ord a) => a -> [a] -> RTick [a]
{-@ insert :: (Ord a) 
           => x:a -> xs:OList a
           -> {t: RTick {os:(OList a) | length os == length xs + 1} 
                | tcost t <= length xs } @-}
insert x []   = pure [x]
insert x (y:ys) 
  | x <= y    = step (x:y:ys)
  | otherwise = pure ((:) y) </> insert x ys 

{-@ reflect isort @-}
{-@ isort :: Ord a => xs:[a] 
          -> {t: RTick {os:(OList a) | length os == length xs} 
               | tcost t <= length xs * length xs } @-}
isort :: Ord a => [a] -> RTick [a]
isort []     = pure [] 
isort (x:xs) = bbind (length xs) (isort xs) (insert x) 



{-@ iminimum :: Ord a => xs:{[a] | 0 < length xs } 
             -> {t:RTick a | tcost t <= length xs * length xs } @-}
iminimum :: Ord a => [a] -> RTick a 
iminimum xs = pure head <*> isort xs 


