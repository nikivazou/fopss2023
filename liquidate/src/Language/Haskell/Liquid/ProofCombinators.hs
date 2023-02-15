module Language.Haskell.Liquid.ProofCombinators (

  Proof

  , (***), QED(..)

  -- * Proof certificate constructors
  , (?)

  -- * These two operators check all intermediate equalities
  , (===) -- proof of equality is implicit eg. x === y
  , (=<=) -- proof of equality is implicit eg. x <= y
  , (=>=) -- proof of equality is implicit eg. x =>= y 

) where

-------------------------------------------------------------------------------
-- | Proof is just a () alias -------------------------------------------------
-------------------------------------------------------------------------------

type Proof = ()

toProof :: a -> Proof
toProof _ = ()

-------------------------------------------------------------------------------
-- | Proof Construction -------------------------------------------------------
-------------------------------------------------------------------------------

-- | proof casting
-- | `x *** QED`: x is a proof certificate* strong enough for SMT to prove your theorem

infixl 3 ***
(***) :: a -> QED -> Proof
_ *** _ = ()

data QED = QED


-------------------------------------------------------------------------------
-- | * Checked Proof Certificates ---------------------------------------------
-------------------------------------------------------------------------------

-- Any (refined) carries proof certificates.
-- For example 42 :: {v:Int | v == 42} is a certificate that
-- the value 42 is equal to 42.
-- But, this certificate will not really be used to proof any fancy theorems.

-- Below we provide a number of equational operations
-- that constuct proof certificates.

-- | Implicit equality

-- x === y returns the proof certificate that
-- result value is equal to both x and y
-- when y == x (as assumed by the operator's precondition)

infixl 3 ===
{-@ (===) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-}
(===) :: a -> a -> a
_ === y  = y

infixl 3 =<=
{-@ (=<=) :: x:a -> y:{a | x <= y} -> {v:a | v <= y} @-}
(=<=) :: a -> a -> a
_ =<= y  = y

infixl 3 =>=
{-@ (=>=) :: x:a -> y:{a | x >= y}  -> {v:a | v == y} @-}
(=>=) :: a -> a -> a
_ =>= y  = y

-------------------------------------------------------------------------------
-- | `?` is basically Haskell's $ and is used for the right precedence
-- | `?` lets you "add" some fact into a proof term
-------------------------------------------------------------------------------

infixl 3 ?

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b<pb> -> a<pa> @-}
(?) :: a -> b -> a 
x ? _ = x 
{-# INLINE (?)   #-} 

