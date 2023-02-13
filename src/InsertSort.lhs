> module InsertSort where 

> {-@ type OList a = [a]<{\hd x -> hd <= x}> @-}

> {-@ insert :: Ord a => a -> OList a -> OList a @-}
> insert :: Ord a => a -> [a] -> [a]
> insert x [] = [x]
> insert x (y:ys)
>    | x <= y = x:y:ys
>    | otherwise = y:(insert x ys)


> {-@ isort :: Ord a => OList a -> OList a @-}
> isort :: Ord a => [a] -> [a]
> isort xs = foldr insert [] xs 
