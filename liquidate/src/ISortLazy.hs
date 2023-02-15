{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality"    @-}

module ISortLazy where 
import Prelude hiding (pure,(<*>),(>>=), length)
import List 
import RTick 



data LList a = LNil | LCons a (RTick (LList a))

{-@ data LList a <p :: a -> a -> Bool> = 
      LNil | 
      LCons {lhd :: a, ltl :: RTick (LList <p> (a<p lhd>))} @-}    

{-@ type SLList a = LList <{\x y -> x <= y}> a @-}


-- Q: What is the complexity of minimum? 

{-@ minimum :: Ord a => xs:{[a] | 0 < length xs} 
            -> {t:RTick a | true } @-} 
minimum :: Ord a => [a] -> RTick a 
minimum xs = pure lhead <*> isort xs 


-- Q: What is the complexity of isort? 

{-@ isort :: Ord a => xs:[a] 
         -> {t:RTick (SLList a) | true } @-}
isort :: Ord a => [a] -> RTick (LList a)
isort []     = pure LNil
isort (x:xs) = (isort xs) >>= (insert x) 



-- Q: What is the complexity of insert? 

{-@ insert :: Ord a => a -> xs:SLList a 
           -> {t:RTick (SLList a) | true  } @-}
insert :: Ord a => a -> LList a -> RTick (LList a) 
insert x LNil = pure (LCons x (pure LNil))
insert x (LCons y ys)
  | x <= y    = step (LCons x (pure (LCons y ys))) 
  | otherwise = step (LCons y (ys >>= insert x))












{-@ measure llength @-}
{-@ llength :: LList a -> Nat @-} 
llength :: LList a -> Int 
llength LNil = 0 
llength (LCons _ (RTick _ xs)) = 1 + llength xs

lhead :: LList a -> a 
lhead (LCons x _) = x 
