{-@ LIQUID "--reflection" @-}

module RTick where 
import Prelude hiding (pure,(<*>))

data RTick a = RTick Int a  

{-@ measure tcost @-}
tcost :: RTick a -> Int 
tcost (RTick x _) = x 

{-@ measure tval @-}
tval :: RTick a -> a 
tval (RTick _ x) = x 

---------------------------------------------------------
-- | The Applicative Instance ---------------------------
---------------------------------------------------------

{-@ reflect pure @-}
{-@ pure :: x:a -> {t:RTick a | tcost t == 0 && tval t == x } @-}
pure :: a -> RTick a 
pure x = RTick 0 x

{-@ reflect <*> @-}
{-@ (<*>) :: f:RTick (a -> b) -> x:RTick a 
          -> {t:RTick b | tcost t == tcost f + tcost x && tval t == (tval f) (tval x)} @-} 
(<*>) :: RTick (a -> b) -> RTick a -> RTick b 
RTick i f <*> RTick j x = RTick (i+j) (f x)

---------------------------------------------------------
-- | Resource Tracking ----------------------------------
---------------------------------------------------------

{-@ reflect step @-}
{-@ step :: x:a -> {t:RTick a | tcost t == 1 && tval t == x } @-}
step :: a -> RTick a 
step x = RTick 1 x


{-@ reflect </> @-}
{-@ (</>) :: f:RTick (a -> b) -> x:RTick a 
          -> {t:RTick b | tcost t == 1 + tcost f + tcost x && tval t == (tval f) (tval x)} @-} 
(</>) :: RTick (a -> b) -> RTick a -> RTick b 
RTick i f </> RTick j x = RTick (1+i+j) (f x)


---------------------------------------------------------
-- | The Monad Instance ---------------------------------
---------------------------------------------------------


{-@ reflect >>= @-}
{-@ (>>=) :: x:RTick a -> f:(a -> RTick b) 
          -> {t:RTick b | tcost t == tcost x + tcost (f (tval x))} @-} 
(>>=) :: RTick a -> (a -> RTick b) -> RTick b 
RTick i x >>= f = case f x of 
                   RTick j y -> RTick (i + j) y  

{-@ reflect bbind @-}
{-@ bbind :: n:Int -> x:RTick a -> f:(a -> {t:RTick b | tcost t <= n}) 
          -> {t:RTick b | tcost t == tcost x + tcost (f (tval x)) 
                       && tcost t <= tcost x + n
                       && tval  t == tval (f (tval x))} @-} 
bbind :: Int -> RTick a -> (a -> RTick b) -> RTick b 
bbind _ (RTick i x) f = case f x of 
                          RTick j y -> RTick (i + j) y  