> module GHCSort where 

Here we prove that the official sorting algorithm 
used by GHC is indeed generating sorted lists.

Yet, proving termination is not trivial, so let's not prove it: 

> {-@ LIQUID "--no-termination" @-}


We define the type alias of ordered lists 

> {-@ type OList a =  [a]<{\hd x -> x >= hd}>  @-}


> {-@ sort :: Ord a => [a] -> OList a  @-}
> sort :: (Ord a) => [a] -> [a]
> sort xs = mergeAll (sequences xs)
>   where
>     sequences (a:b:xs)
>       | a `compare` b == GT = descending b [a]  xs
>       | otherwise           = ascending  b (a:) xs
>     sequences [x] = [[x]]
>     sequences []  = [[]]
> 
>     descending a as (b:bs)
>       | a `compare` b == GT = descending b (a:as) bs
>     descending a as bs      = (a:as):sequences bs
> 
>     ascending a as (b:bs)
>       | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs
>     ascending a as bs       = as [a]:sequences bs
> 
>     mergeAll []  = [] --this case cannot occur, though
>     mergeAll [x] = x
>     mergeAll xs  = mergeAll (mergePairs xs)

> {-@ mergePairs :: Ord a
>                => xss:[(OList a)]
>                -> {v:[(OList a)] | (if ((len xss) > 1) then ((len v) < (len xss)) else ((len v) = (len xss) ))}
>   @-}
> mergePairs :: Ord a => [[a]] -> [[a]]
> mergePairs (a:b:xs) = merge1 a b: mergePairs xs
> mergePairs [x]      = [x]
> mergePairs []       = []


> {-@ merge1 :: Ord a
>            => xs:OList a
>            -> ys:OList a
>            -> {v:OList a | len v == len xs + len ys}
>            / [len xs + len ys]
>   @-}
> merge1 :: Ord a => [a] -> [a] -> [a]
> merge1 (a:as') (b:bs')
>   | a `compare` b == GT = b:merge1 (a:as')  bs'
>   | otherwise           = a:merge1 as' (b:bs')
> merge1 [] bs            = bs
> merge1 as []            = as