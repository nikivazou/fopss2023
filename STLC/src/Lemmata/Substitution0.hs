{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-interpreter" @-}

module Lemmata.Substitution where 

import Syntax 
import Propositions
import Expressions 
import Environments
import Primitives

import Data.Set 
import Helpers.ProofCombinators

{-@ substitution :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty} 
                 -> x:{Var | not (Data.Set.member x (union (dom g1) (dom g2)))} 
                 -> ex:Expr 
                 -> e:{Expr | not (member x (freeVars e))} 
                 -> t:Type -> tx:Type  
                 -> Prop (HasType (eAppend g1 (EBind x tx g2)) (open e (EFVar x)) t)
                 -> Prop (HasType g2 ex tx)
                 -> Prop (HasType (eAppend g1 g2) (open e ex) t) @-}
substitution :: Env -> Env -> Var -> Expr -> Expr -> Type -> Type -> HasType -> HasType -> HasType
substitution g1 g2 x ex e t tx e_hastype_t ex_hastype_tx 
  = substitution_intro e ex x 
  ? substitution_lemma g1 g2 (open e (EFVar x)) ex x t tx ex_hastype_tx e_hastype_t


{-@ substitution_intro :: e:Expr -> ex:Expr 
                       -> x:{Var | not (member x (freeVars e))} 
                       -> { open e ex = subst (open e (EFVar x)) x ex } @-}
substitution_intro :: Expr -> Expr -> Var -> () 
substitution_intro (EApp e1 e2) ex x 
  = substitution_intro e1 ex x ? substitution_intro e2 ex x  
substitution_intro (ELam tx e) ex x
  = undefined  
substitution_intro (EFVar y) ex x
  = undefined 
substitution_intro (EBVar y) ex x
  = undefined 
substitution_intro (EPrim _) ex x
  = () 

{-@ substitution_lemma :: g1:Env -> g2:{Env | intersection (dom g1) (dom g2) == empty } 
                       -> e:Expr -> ex:Expr 
                       -> x:Var
                       -> t:Type -> tx:Type  
                       -> Prop (HasType g2 ex tx)
                       -> Prop (HasType (eAppend g1 (EBind x tx g2)) e t)
                       -> Prop (HasType (eAppend g1 g2) (subst e x ex) t) @-}
substitution_lemma :: Env -> Env -> Expr -> Expr -> Var -> Type -> Type -> HasType -> HasType -> HasType
substitution_lemma = undefined 



{-@ weaken :: g1:Env -> g2:Env -> e:Expr -> t:Type 
           -> Prop (HasType g2 e t)
           -> Prop (HasType (eAppend g1 g2) e t) @-}
weaken :: Env -> Env -> Expr -> Type -> HasType -> HasType 
weaken = undefined 