Summary: 

1. Liquid Haskell for Light Verification 
   - totality, termination
   - arithmetic, length
2. Liquid Haskell for Deep Verification 
    - append, isort
    by reflecting list append and isort in the logic

What about functions that do not terminate? 
Can we, for example, prove soundness of STLC? 

Yes! 

> {-@ soundness :: eo:Expr -> t:Type -> e:Expr
>               -> Prop (HasType EEmp eo t) 
>               -> Prop (Evals eo e)
>               -> Either {isValue e} (e::Expr, Prop (Step e e'))> @-}


Today: 
1. What is Prop? 
2. Examples 
3. Soundness Theorem
---------------------
4. Keynote on incomplete state of refinement types