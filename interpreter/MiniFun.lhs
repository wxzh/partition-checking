> module MiniFun where

> import Prelude hiding (EQ,LT)
> import Data.Maybe

Using PHOAS to represent variable binding

Need to represent primitives in a better way?

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
>   -- Adding case analysis and constructors
>   | ECon String [PExp a b]                -- constructor
>   | ECase (PExp a b) [(String, [a] -> PExp a b)]     -- case expression

ECon String (PExp a b)

ECase [Pat a b]

eval 

EPat String ([a] -> PExp a b)

Standard (big-step) interpreter

> data Value = VInt Int | VBool Bool | VFun (Value -> Value) | VCon String [Value]
>
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
> eval (ECon s xs)        = VCon s (map eval xs)
> eval (ECase e clauses)  = 
>  case eval e of
>     VCon s vs -> eval (fromJust (lookup s clauses) vs)

Symbolic interpreter

> data SymValue = 
>     SFVar Int -- free variables 
>   | SInt Int 
>   | SBool Bool 
>   | SEq SymValue SymValue
>   | SLt SymValue SymValue
>   | SAdd SymValue SymValue
>   | SMul SymValue SymValue
>   | SApp SymValue SymValue
>   | SCon String [SymValue]
>   | SFun (ExecutionTree -> ExecutionTree) -- just store the function
>
> data ExecutionTree = Exp SymValue | Fork SymValue (ExecutionTree) (ExecutionTree) 

> data Op = ADD | MUL | LT | EQ

Applies program to symbolic variables

> exec :: ExecutionTree -> ExecutionTree
> exec e = exec' e 0
>
> exec' :: ExecutionTree -> Int -> ExecutionTree
> exec' (Exp (SFun f)) n = exec' (f (Exp (SFVar n))) (n+1)
> exec' e              n = e

> seval :: PExp ExecutionTree Int -> ExecutionTree
> seval (EFVar x)          = Exp (SFVar x)
> seval (EBVar e)          = e
> seval (EInt x)           = Exp (SInt x)
> seval (EBool b)          = Exp (SBool b)
> seval (EIf e1 e2 e3)     = propagate (seval e1) (seval e2) (seval e3) -- loses sharing!!
> seval (EAdd e1 e2)       = merge (SAdd,ADD) (seval e1) (seval e2) -- loses sharing!!
> seval (EMul e1 e2)       = merge (SMul,MUL) (seval e1) (seval e2) -- loses sharing!!
> seval (EEq e1 e2)        = merge (SEq,EQ)  (seval e1) (seval e2) -- loses sharing!!
> seval (ELt e1 e2)        = merge (SLt,LT)  (seval e1) (seval e2)
> seval (ELam f)           = Exp (SFun (seval . f))
> seval (ELet f g)         = let v = seval (f v) in seval (g v)
> seval (EApp e1 e2)       = treeApply (seval e1) (seval e2)
> -- new cases for constructors and case analysis
> seval (ECon s xs)        = mergeList (SCon s) (map seval xs)
> seval (ECase e clauses)  = undefined 

> {-
> eval (ECon s xs)        = VCon s (map eval xs)
> eval (ECase e clauses)  = 
>  case eval e of
>     VCon s vs -> eval (fromJust (lookup s clauses) vs)
> -}

> propagate (Exp e) et1 et2 = Fork e et1 et2
> propagate (Fork e l r) et1 et2 = Fork e (propagate l et1 et2) (propagate r et1 et2)

TODO: Improve code here
 1) Should be possible to use 1 definition for merge instead of "mergeList" and "merge"
    (Also mergeList need to do partial-evaluation as merge)
 2) Deal with operators in a better way

> mergeList f []                    = Exp (f [])
> mergeList f (Exp e : xs)          = mergeList (\es -> f (e:es)) xs
> mergeList f (Fork e1 e2 e3 : xs)  = 
>   Fork e1 (mergeList f (e2:xs)) (mergeList f (e3:xs))
>
> merge (_,MUL) (Exp (SInt x)) (Exp (SInt y)) = Exp (SInt (x*y)) -- partial evaluation
> merge (_,MUL) (Exp (SInt 1)) e = e
> merge (_,MUL) e (Exp (SInt 1)) = e
> merge (_,MUL) (Exp (SInt 0)) e = Exp (SInt 0)
> merge (_,MUL) e (Exp (SInt 0)) = Exp (SInt 0)
> merge (_,ADD) (Exp (SInt x)) (Exp (SInt y)) = Exp (SInt (x+y))
> merge (_,EQ) (Exp (SInt x)) (Exp (SInt y)) = Exp (SBool (x==y))
> merge (_,EQ) (Exp (SBool x)) (Exp (SBool y)) = Exp (SBool (x==y))
> merge (_,LT) (Exp (SInt x)) (Exp (SInt y)) = Exp (SBool (x<y))
> merge f (Exp e1) (Exp e2) = Exp (fst f e1 e2)
> merge f (Fork e1 e2 e3) t = Fork e1 (merge f e2 t) (merge f e3 t)
> merge f t (Fork e1 e2 e3) = Fork e1 (merge f t e2) (merge f t e3) 


> treeApply (Exp (SFVar x)) t = apply (SApp (SFVar x)) t  -- f e
> treeApply (Exp (SFun f)) t  = f t                       -- (\x . e1) e2
> treeApply (Fork e1 e2 e3) t = Fork e1 (treeApply e2 t) (treeApply e3 t)
>
> apply f (Exp e)          = Exp (f e) 
> apply f (Fork e1 e2 e3)  = Fork e1 (apply f e2) (apply f e3)

> pp' :: ExecutionTree -> String -> Int -> (String,Int)
> pp' _ s 0 = ("",0)
> pp' (Exp e) s stop = (s ++ " ==> " ++ ppSymValue e ++ "\n", stop - 1)
> pp' (Fork e1 e2 e3) s stop = 
>  let s1         = ppSymValue e1
>      (s2,stop2) = pp' e2 (s ++ " && " ++ s1) stop
>      (s3,stop3) = pp' e3 (s ++ " && " ++ "not (" ++ s1 ++ ")") stop2
>  in (s2 ++ s3,stop3)

> pp e = fst $ pp' e "True" 5 -- stop after 5 results

> ppSymValue :: SymValue -> String
> ppSymValue (SFVar n)     = "x" ++ show n
> ppSymValue (SInt i)      = show i
> ppSymValue (SBool b)     = show b
> ppSymValue (SEq v1 v2)   = "(" ++ ppSymValue v1 ++ " == " ++ ppSymValue v2 ++ ")"
> ppSymValue (SAdd v1 v2)  = "(" ++ ppSymValue v1 ++ " + " ++ ppSymValue v2 ++ ")"
> ppSymValue (SMul v1 v2)  = "(" ++ ppSymValue v1 ++ " * " ++ ppSymValue v2 ++ ")"
> ppSymValue (SLt v1 v2)   = "(" ++ ppSymValue v1 ++ " < " ++ ppSymValue v2 ++ ")"
> ppSymValue (SApp v1 v2)  = ppSymValue v1 ++ " " ++ ppSymValue v2
> ppSymValue (SFun f)      = "<<function>>"

> instance Show Value where
>   show (VFun _) = "<<function>>"
>   show (VInt x) = show x
>   show (VBool b) = show b


> fact = ELet (\fact -> ELam (\n ->
>   EIf (ELt (EBVar n) (EInt 1))
>       (EInt 1)
>       (EMul (EBVar n) (EApp (EBVar fact) (EAdd (EBVar n) (EInt (-1))))))) EBVar

> sumList = ELet (\sumList -> ELam (\l -> 
>   ECase (EBVar l) [
>     ("Nil", \_ -> EInt 0),
>     ("Cons", \(x:xs:[]) -> EAdd (EBVar x) (EApp (EBVar sumList) (EBVar xs)))
>   ])) EBVar

> isPositive = ELam (\n -> ELt (EInt 0) (EBVar n))

> p1 = ELam (\n -> EIf (ELt (EBVar n) (EInt 10)) (EInt (-1)) (EInt 1))
>
> p2 = ELam (\n -> EIf (ELt (EBVar n) (EInt 5)) (EInt (-1)) (EInt 1))
>
> prop_p1_p2 = ELam (\n -> EEq (EApp p1 (EBVar n)) (EApp p2 (EBVar n))) 

> prop_fact = ELam (\n -> EApp isPositive (EApp fact (EBVar n))) 

> t = eval (EApp fact (EInt 10))

> t1 = eval (EApp sumList (toIntList [1..100]))

> toList :: (a -> PExp b c) -> [a] -> PExp b c
> toList f []      = ECon "Nil" []
> toList f (x:xs)  = ECon "Cons" [f x, toList f xs]
>
> toIntList = toList EInt

> fun e = putStrLn (pp (exec (seval e)))
