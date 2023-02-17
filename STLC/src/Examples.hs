{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Examples where 

import Syntax 
import Expressions 
import Primitives
import Propositions




-- Some Primitive Integer Expressions 

fourtyTwo, fourty, two :: Expr
fourtyTwo = EPrim (PInt 42) 
fourty    = EPrim (PInt 40) 
two       = EPrim (PInt  2) 

-- add_42 ~~ 40 + 2 
add_42 :: Expr 
add_42 = EApp (EApp (EPrim PAdd) fourty) two


-- Proof of (40 + 2) ->* 42 
-- (40 + 2) -> +_40 2 -> 42
{-@ ex_eval :: Prop (Evals add_42 fourtyTwo) @-}
ex_eval :: Evals 
ex_eval = EStep add_42 ei fourtyTwo 
                step_1                   -- add_42    ->  ei 
                (                        -- ei        ->* fourtyTwo
                  EStep ei fourtyTwo fourtyTwo 
                       step_2            -- ei        ->  fourtyTwo 
                       (ERefl fourtyTwo) -- fourtyTwo ->* fourtyTwo
                )

ei :: Expr 
ei = EApp (EPrim (PIAdd 40)) two


{-@ step_1 :: Prop (Step add_42 ei) @-}
step_1 :: Step 
step_1 = SAppPL (EApp (EPrim PAdd) fourty) (EPrim (PIAdd 40)) two 
                (SAppEP PAdd fourty)     


{-@ step_2 :: Prop (Step ei fourtyTwo) @-}
step_2 :: Step 
step_2 = SAppEP (PIAdd 40) two


-- | Proof of `|- (40+2) :: Int` 

{-@ type_add_42 :: Prop (HasType EEmp add_42 (TPrim TInt)) @-}
type_add_42 :: HasType 
type_add_42 = 
  -- |- (+) 40 2 :: Int 
  TApp EEmp (EApp (EPrim PAdd) fourty) two tInt tInt 
  --       |- (+) 42 :: Int -> Int  
       (assertProp (HasType EEmp (EApp (EPrim PAdd) fourty) (TFun tInt tInt)) (
        TApp EEmp (EPrim PAdd) fourty (TFun tInt tInt) tInt 
  --         |- (+) :: Int -> Int -> Int 
             (TCon EEmp PAdd)
  --         |- 40 :: Int 
             (TCon EEmp (PInt 40))
        ) )
  --       |- 2 :: Int 
       (assertProp (HasType EEmp two tInt) (TCon EEmp (PInt 2)))



            

-- | An example with Lambda: ((\x.x) 42) -> 42 

intLam :: Expr 
intLam = ELam (TPrim TInt) (EBVar 0)

{-@ ex_step :: Prop (Step (EApp intLam fourtyTwo) fourtyTwo) @-}
ex_step :: Step 
ex_step = SAppEL (EBVar 0) fourtyTwo (TPrim TInt)   




-- | Proof of `|- ((\x.x) 42) :: Int` 

{-@ type_intLam :: Prop (HasType EEmp (EApp intLam fourtyTwo) (TPrim TInt)) @-}
type_intLam :: HasType 
type_intLam = 
  -- |- ((\x.x) 42) :: Int 
  TApp EEmp intLam fourtyTwo tInt tInt 
  --       |- (\x.x) :: Int -> Int  
       (assertProp (HasType EEmp intLam (TFun tInt tInt)) (
        TLam EEmp (EBVar 0) tInt tInt xx (
          (TVar (EBind xx tInt EEmp) xx )
        )
        ) )
  --       |- 42 :: Int 
       (assertProp (HasType EEmp fourtyTwo tInt) (TCon EEmp (PInt 42)))









-- | The Integer Type 
{-@ reflect tInt @-}
tInt :: Type 
tInt = TPrim TInt


-- | The Integer Type 
{-@ reflect xx @-}
{-@ xx :: Var @-} 
xx :: Var 
xx = 100


-- | Reflect Everything 

{-@ reflect fourtyTwo @-}
{-@ reflect fourty    @-}
{-@ reflect two       @-}
{-@ reflect intLam @-}
{-@ reflect add_42 @-}
{-@ reflect ei @-}
