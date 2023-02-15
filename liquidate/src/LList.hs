{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}

module LList where 
import Prelude hiding (pure,(<*>),(>>=), length)

import RTick 

data LList a = LNil | LCons a (RTick (LList a))

{-@ data LList a <p :: a -> a -> Bool> = 
      LNil | 
      LCons {lhd :: a, ltl :: RTick (LList <p> (a<p lhd>))} @-}    

{-@ type SLList a = LList <{\x y -> x <= y}> a @-}

{-@ measure llength @-}
{-@ llength :: LList a -> Nat @-} 
llength :: LList a -> Int 
llength LNil = 0 
llength (LCons _ (RTick _ xs)) = 1 + llength xs