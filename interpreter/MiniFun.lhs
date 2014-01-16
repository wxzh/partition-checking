> module MiniFun where

Using PHOAS to represent variable binding

> data PExp a b =
>     EFVar b 
>   | EBVar a
>   | EInt Int
>   | EBool Bool
>   | EIf (PExp a b) (PExp a b) (PExp a b)
>   | EEq (PExp a b) (PExp a b)
>   | ELt (PExp a b) (PExp a b)
>   | EAdd (PExp a b) (PExp a b)
>   | EMul (PExp a b) (PExp a b)
>   | ELet (a -> PExp a b) (a -> PExp a b)
>   | ELam (a -> PExp a b)
>   | EApp (PExp a b) (PExp a b)

> newtype InfExp a = Fold {unFold :: PExp (InfExp a) a}

> data Value = VInt Int | VBool Bool | VFun (Value -> Value)

> data SymValue a = 
>     SFVar a -- free variables 
>   | SInt Int 
>   | SBool Bool 
>   | SEq (SymValue a) (SymValue a)
>   | SLt (SymValue a) (SymValue a)
>   | SAdd (SymValue a) (SymValue a)
>   | SMul (SymValue a) (SymValue a)
>   | SFun (SymValue a -> SymValue a)

> type OExp = SymValue Int
>
> data ExecutionTree = Exp OExp | Fork OExp (ExecutionTree) (ExecutionTree) 

> seval :: PExp (InfExp Int) Int -> Int -> ExecutionTree
> seval (EFVar x)         n = Exp (SFVar x)
> seval (EBVar (Fold e))  n = seval e n
> seval (EInt x)          n = Exp (SInt x)
> seval (EBool b)         n = Exp (SBool b)
> seval (EIf e1 e2 e3)    n = propagate (seval e1 n) (seval e2 n) (seval e3 n) -- loses sharing!!
> seval (EAdd e1 e2)      n = merge SAdd (seval e1 n) (seval e2 n) -- loses sharing!!
> seval (EMul e1 e2)      n = merge SMul (seval e1 n) (seval e2 n) -- loses sharing!!
> seval (EEq e1 e2)       n = merge SEq  (seval e1 n) (seval e2 n) -- loses sharing!!
> seval (ELt e1 e2)       n = merge SLt  (seval e1 n) (seval e2 n)
> seval (ELam f)          n = seval (f (Fold (EFVar n))) (n+1)
> seval e@(ELet f g)      n = seval (g (Fold (f (Fold e)))) n -- unrolls the fixpoint
> seval (EApp e1 e2)      n = treeApply (seval e1 n) (seval e2 n)

> pp :: ExecutionTree -> String
> pp (Exp e) = ppSymValue e

> ppSymValue :: SymValue Int -> String
> ppSymValue (SFVar n)    = "x" ++ show n
> ppSymValue (SInt i)     = show i
> ppSymValue (SBool b)    = show b
> ppSymValue (SEq v1 v2)  = "(" ++ ppSymValue v1 ++ " == " ++ ppSymValue v2 ++ ")"
> -- ppSymValue (

> treeApply (Exp (SFun f)) t = apply f t
> treeApply (Fork e1 e2 e3) t = Fork e1 (treeApply e2 t) (treeApply e3 t)

> apply f (Exp e) = Exp (f e) 
> apply f (Fork e1 e2 e3) = Fork e1 (apply f e2) (apply f e3)

let v = seval (f v) n in eval (g v) 

> propagate (Exp e) et1 et2 = Fork e et1 et2
> propagate (Fork e l r) et1 et2 = Fork e (propagate l et1 et2) (propagate r et1 et2)
>
> merge f (Exp e1) (Exp e2) = Exp (f e1 e2)
> merge f (Fork e1 e2 e3) t = Fork e1 (merge f e2 t) (merge f e3 t)
> merge f t (Fork e1 e2 e3) = Fork e1 (merge f t e2) (merge f t e3) 

> instance Show Value where
>   show (VFun _) = "<<function>>"
>   show (VInt x) = show x
>   show (VBool b) = show b

> eval :: PExp Value () -> Value
> eval (EFVar _)       = error "ops! Free variable"
> eval (EBVar v)       = v
> eval (EInt x)        = VInt x
> eval (EBool b)       = VBool b
> eval (EIf e1 e2 e3)  = 
>  case eval e1 of
>     VBool b -> if b then eval e2 else eval e3
> eval (EEq e1 e2)     =
>  case (eval e1, eval e2) of 
>     (VBool v1, VBool v2) -> VBool (v1 == v2)
>     (VInt v1, VInt v2)   -> VBool (v1 == v2)
> eval (ELt e1 e2)     =
>  case (eval e1, eval e2) of
>     (VInt v1, VInt v2) -> VBool (v1 < v2)
> eval (EAdd e1 e2)    =
>  case (eval e1, eval e2) of 
>     (VInt v1, VInt v2) -> VInt (v1 + v2)
> eval (EMul e1 e2)    =
>  case (eval e1, eval e2) of 
>     (VInt v1, VInt v2) -> VInt (v1 * v2)
> eval (ELet f g)      = let v = eval (f v) in eval (g v) 
> eval (ELam f)           = VFun (eval . f)
> eval (EApp e1 e2)       = 
>  case (eval e1) of
>     VFun f -> f (eval e2)

> fact = ELet (\fact -> ELam (\n ->
>   EIf (ELt (EBVar n) (EInt 1))
>       (EInt 1)
>       (EMul (EBVar n) (EApp (EBVar fact) (EAdd (EBVar n) (EInt (-1))))))) EBVar

> t = eval (EApp fact (EInt 10))
