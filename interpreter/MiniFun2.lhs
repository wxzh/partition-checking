> {-# OPTIONS -XRecursiveDo #-}

> module MiniFun where

> import Prelude hiding (EQ,LT)
> import Data.Maybe
> import Control.Monad.State

Using PHOAS to represent variable binding

Need to represent primitives in a better way?

> -- Empty type for saying 'no free variables'
> data Void

> -- We need the type of types! - Why :)?
> data PType = TInt | TBool | PType :-> PType
>   deriving (Show, Eq)

> data PExp a b =
>     EFVar b 
>   | EBVar a
>   | EInt Int
>   | EEq (PExp a b) (PExp a b)
>   | ELt (PExp a b) (PExp a b)
>   | EAdd (PExp a b) (PExp a b)
>   | EMul (PExp a b) (PExp a b)
>   | ELet (a -> PExp a b) (a -> PExp a b)
>   | ELam (a -> PExp a b) PType
>   | EApp (PExp a b) (PExp a b)
>   -- Adding case analysis and constructors
>   | ECon String [PExp a b]                -- constructor
>   | ECase (PExp a b) [(String, [a] -> PExp a b)]     -- case expression

ECon String (PExp a b)

ECase [Pat a b]

eval 

EPat String ([a] -> PExp a b)

Standard (big-step) interpreter

> data Value = VInt Int | VFun (Value -> Value) | VCon String [Value]
>
> eval :: PExp Value Void -> Value
> eval (EFVar _)       = error "ops! Free variable"
> eval (EBVar v)       = v
> eval (EInt x)        = VInt x
> eval (EEq e1 e2)     =
>  case (eval e1, eval e2) of 
> --    (VBool v1, VBool v2) -> VCon (show (v1 == v2))
>     (VInt v1, VInt v2)   -> VCon (show (v1 == v2)) []
> eval (ELt e1 e2)     =
>  case (eval e1, eval e2) of
>     (VInt v1, VInt v2) -> VCon (show (v1 < v2)) []
> eval (EAdd e1 e2)    =
>  case (eval e1, eval e2) of 
>     (VInt v1, VInt v2) -> VInt (v1 + v2)
> eval (EMul e1 e2)    =
>  case (eval e1, eval e2) of 
>     (VInt v1, VInt v2) -> VInt (v1 * v2)
> eval (ELet f g)      = let v = eval (f v) in eval (g v) 
> eval (ELam f _)         = VFun (eval . f)
> eval (EApp e1 e2)       = 
>  case (eval e1) of
>     VFun f -> f (eval e2)
> eval (ECon s xs)        = VCon s (map eval xs)
> eval (ECase e clauses)       =
>  case eval e of
>     VCon s vs -> eval (fromJust (lookup s clauses) vs)

Symbolic interpreter

> data SymValue = 
>     SFVar Int PType -- free variables 
>   | SInt Int 
>   | SEq SymValue SymValue
>   | SLt SymValue SymValue
>   | SAdd SymValue SymValue
>   | SMul SymValue SymValue
>   | SApp SymValue SymValue
>   | SCon String [SymValue]
>   | SFun (ExecutionTree -> ExecutionTree) PType -- just store the function

> type Pattern = (String, [Int])

> pname :: Pattern -> String
> pname = fst
>
> pargs :: Pattern -> [Int]
> pargs = snd

> data ExecutionTree = Exp SymValue | Fork SymValue [(String, [ExecutionTree] -> ExecutionTree)]

> data Op = ADD | MUL | LT | EQ

Applies program to symbolic variables

> exec :: ExecutionTree -> ExecutionTree
> exec e = exec' e 0
>
> exec' :: ExecutionTree -> Int -> ExecutionTree
> exec' (Exp (SFun f t)) n = exec' (f (Exp (SFVar n t))) (n+1)
> exec' e                n = e

> seval :: PExp ExecutionTree Void -> ExecutionTree
> --seval (EFVar x)          = Exp (SFVar x)
> seval (EBVar e)          = e
> seval (EInt x)           = Exp (SInt x)
> seval (EAdd e1 e2)       = merge (SAdd,ADD) (seval e1) (seval e2) -- loses sharing!!
> seval (EMul e1 e2)       = merge (SMul,MUL) (seval e1) (seval e2) -- loses sharing!!
> seval (EEq e1 e2)        = merge (SEq,EQ)  (seval e1) (seval e2) -- loses sharing!!
> seval (ELt e1 e2)        = merge (SLt,LT)  (seval e1) (seval e2)
> seval (ELam f t)         = Exp (SFun (seval . f) t)
> seval (ELet f g)         = let v = seval (f v) in seval (g v)
> seval (EApp e1 e2)       = treeApply (seval e1) (seval e2)
> seval (ECon s xs)        = mergeList (SCon s) (map seval xs)
> seval (ECase e clauses)  = propagate (seval e) (map (\(s,c) -> (s, seval . c)) clauses)

> propagate (Exp e) es      = Fork e es 
> propagate (Fork e es) es' = Fork e [(s, \l -> propagate (f l) es') | (s,f) <- es]
                                      

TODO: Improve code here
 1) Should be possible to use 1 definition for merge instead of "mergeList" and "merge"
    (Also mergeList need to do partial-evaluation as merge)
 2) Deal with operators in a better way

> mergeList f []                    = Exp (f [])
> mergeList f (Exp e : xs)          = mergeList (\es -> f (e:es)) xs
> mergeList f (Fork e es : xs)  = 
>   Fork e [ (s, \l -> mergeList f (g l : xs)) | (s,g) <- es]
>
> merge (_,MUL) (Exp (SInt x)) (Exp (SInt y)) = Exp (SInt (x*y)) -- partial evaluation
> merge (_,MUL) (Exp (SInt 1)) e = e
> merge (_,MUL) e (Exp (SInt 1)) = e
> merge (_,MUL) (Exp (SInt 0)) e = Exp (SInt 0)
> merge (_,MUL) e (Exp (SInt 0)) = Exp (SInt 0)
> merge (_,ADD) (Exp (SInt x)) (Exp (SInt y)) = Exp (SInt (x+y))
> merge (_,EQ) (Exp (SInt x)) (Exp (SInt y)) = Exp (SCon (show (x==y)) [])
> -- merge (_,EQ) (Exp (SBool x)) (Exp (SBool y)) = Exp (SBool (x==y))
> merge (_,LT) (Exp (SInt x)) (Exp (SInt y)) = Exp (SCon (show (x < y)) [])
> merge f (Exp e1) (Exp e2) = Exp (fst f e1 e2)
> merge f (Fork e es) t = Fork e [(s, \l -> merge f (v l) t) | (s,v) <- es] -- (merge f e2 t) (merge f e3 t)
> merge f t (Fork e es) = Fork e [(s, \l -> merge f (v l) t) | (s,v) <- es] -- (merge f t e2) (merge f t e3) 

> treeApply (Exp (SFVar x pt)) t = apply (SApp (SFVar x pt)) t  -- f e
> treeApply (Exp (SFun f pt))  t = f t                       -- (\x . e1) e2
> treeApply (Fork e es)    t = Fork e [(s, \l -> treeApply (v l) t) | (s,v) <- es] --(treeApply e2 t) (treeApply e3 t)
>
> apply f (Exp e)      = Exp (f e) 
> apply f (Fork e es)  = Fork e [(s, apply f . v) | (s,v) <- es] -- (apply f e2) (apply f e3)

> {-
> seval1 :: PExp ExecutionTree Void -> Int -> State [Int] ExecutionTree
> seval1 (EBVar e)       n   = return e
> seval1 (EInt x)        n   = return (Exp (SInt x))
> seval1 (EAdd e1 e2)    n   = return (merge (SAdd,ADD)) `ap` (seval1 e1 n) `ap` (seval1 e2 n) -- loses sharing!!
> seval1 (EMul e1 e2)    n   = return (merge (SMul,MUL)) `ap` (seval1 e1 n) `ap` (seval1 e2 n) -- loses sharing!!
> seval1 (EEq e1 e2)     n   = return (merge (SEq,EQ)) `ap`  (seval1 e1 n) `ap` (seval1 e2 n) -- loses sharing!!
> seval1 (ELt e1 e2)     n   = return (merge (SLt,LT)) `ap` (seval1 e1 n) `ap` (seval1 e2 n)
> seval1 (ELam f t)      n   = 
>   do  e <- seval1 (f (Exp (SFVar n t))) (n+1)
>       return (Exp (SFun (\v -> subst n v e) t))
> seval1 (ELet f g)      n   = 
>   do  rec {v <- seval1 (f v) n} 
>       seval1 (g v) n
> seval1 (EApp e1 e2)     n  = return treeApply `ap` (seval1 e1 n) `ap` (seval1 e2 n)
> -- seval (ECon s xs)        = mergeList (SCon s) (map seval xs)

--let (v,l) = evalState (seval1 (f v) n) in put l >> seval (g v) n

Substitution of free variables in ExecutionTree

> subst :: Int -> ExecutionTree -> ExecutionTree -> ExecutionTree
> subst n v (Exp (SFVar i t)) -- var in ExecutionTree?
>   | n == i    = v
>   | otherwise = Exp (SFVar i t)
> subst n v (Exp (SInt i)) = Exp (SInt i)
> subst n v (Exp (SEq v1 v2)) = 
>   let (Exp v1') = subst n v (Exp v1)
>       (Exp v2') = subst n v (Exp v2)
>   in Exp (SEq v1' v2') 
> subst n v (Exp (SAdd v1 v2)) = 
>   let (Exp v1') = subst n v (Exp v1)
>       (Exp v2') = subst n v (Exp v2)
>   in Exp (SAdd v1' v2')
> subst n v (Exp (SMul v1 v2)) = 
>   let (Exp v1') = subst n v (Exp v1)
>       (Exp v2') = subst n v (Exp v2)
>   in Exp (SMul v1' v2')  
> subst n v (Exp (SLt v1 v2)) = 
>   let (Exp v1') = subst n v (Exp v1)
>       (Exp v2') = subst n v (Exp v2)
>   in Exp (SLt v1' v2') 
> subst n v (Exp (SApp v1 v2)) = 
>   let (Exp v1') = subst n v (Exp v1)
>       (Exp v2') = subst n v (Exp v2)
>   in Exp (SApp v1' v2') 
> subst n v (Exp (SCon s vs)) = Exp (SCon s [toSymValue (subst n v (Exp v1)) | v1 <- vs])
> subst n v (Exp (SFun f t)) = Exp (SFun (\v1 -> subst n v (f v1)) t)
> subst n v (Fork e es) = 
>   let (Exp e1) = subst n v (Exp e)
>   in Fork e1 (map (\(s,x) -> (s, subst n v x)) es)

> toSymValue :: ExecutionTree -> SymValue -- Partial
> toSymValue (Exp e) = e

> {-
> seval1 (ELet f g)         = let v = seval1 (f v) in seval1 (g v)
> seval1 (EApp e1 e2)       = treeApply (seval1 e1) (seval1 e2)
> -- new cases for constructors and case analysis
> seval1 (ECon s xs)        = mergeList (SCon s) (map seval1 xs)
> seval1 (ECase e clauses)  = propagate (seval1 e) (map (\(s,c) -> ((s,[]), seval1 (c []))) clauses) -- wrong!
> -}

> {-
>   case (seval e) of cl
>      Exp (SCon s) -> seval (fromJust (lookup s clauses)) 
>      t            -> propagate t (map (\(s,c) -> (s,seval c)) clauses)
> -}
> -}

> pp' :: ExecutionTree -> String -> Int -> Int -> (String,Int)
> pp' _ s 0 n = ("",0)
> pp' (Exp e) s stop n = (s ++ " ==> " ++ ppSymValue e n ++ "\n", stop - 1)
> pp' (Fork e1 [(c2,e2),(c3,e3)]) s stop n = -- fix me! generalize to arbitrary size list
>  let s1         = ppSymValue e1 n
>      (s2,stop2) = pp' (e2 (fresh n)) (s ++ " && " ++ s1 ++ " = " ++ c2) stop n
>      (s3,stop3) = pp' (e3 (fresh n)) (s ++ " && " ++ s1 ++ " = " ++ c3) stop2 n
>  in (s2 ++ s3,stop3)

> fresh n = map (\n -> Exp (SFVar n TInt)) (iterate (+1) n)

> pp e = fst $ pp' e "True" 5 0 -- stop after 5 results

> ppSymValue :: SymValue -> Int -> String
> ppSymValue (SFVar n pt) _   = "x" ++ show n
> ppSymValue (SInt i)     n  = show i
> ppSymValue (SCon s _)     n  = s
> ppSymValue (SEq v1 v2)  n  = "(" ++ ppSymValue v1 n ++ " == " ++ ppSymValue v2 n ++ ")"
> ppSymValue (SAdd v1 v2) n  = "(" ++ ppSymValue v1 n ++ " + " ++ ppSymValue v2 n ++ ")"
> ppSymValue (SMul v1 v2) n  = "(" ++ ppSymValue v1 n ++ " * " ++ ppSymValue v2 n ++ ")"
> ppSymValue (SLt v1 v2)  n  = "(" ++ ppSymValue v1 n ++ " < " ++ ppSymValue v2 n ++ ")"
> ppSymValue (SApp v1 v2) n  = ppSymValue v1 n ++ " " ++ ppSymValue v2 n
> ppSymValue (SFun f t)   n  = "<<function>>" -- "(\\x" ++ show n ++ ". " ++ f (Exp (SFVar n t)) ++ ")" -- <<function>>"

> instance Show Value where
>   show (VFun _)   = "<<function>>"
>   show (VInt x)   = show x
>   show (VCon s [])   = s
> --  show (VCon s xs)   = "(" ++ s ++ " " ++ map show xs ++ ")"

> nLam b = ELam b TInt

> eIf e1 e2 e3 = ECase e1 [("True",\_ -> e2),("False",\_ -> e3)]

> fact = ELet (\fact -> nLam (\n ->
>   eIf (ELt (EBVar n) (EInt 1))
>       (EInt 1)
>       (EMul (EBVar n) (EApp (EBVar fact) (EAdd (EBVar n) (EInt (-1))))))) EBVar

> sumList = ELet (\sumList -> ELam (\l -> 
>   ECase (EBVar l) [
>     ("Nil", \_ -> EInt 0),
>     ("Cons", \(x:xs:_) -> EAdd (EBVar x) (EApp (EBVar sumList) (EBVar xs)))
>   ]) (error "We have no suitable type yet:)")) EBVar

> isPositive = nLam (\n -> ELt (EInt 0) (EBVar n))

> p1 = nLam (\n -> eIf (ELt (EBVar n) (EInt 10)) (EInt (-1)) (EInt 1))
>
> p2 = nLam (\n -> eIf (ELt (EBVar n) (EInt 5)) (EInt (-1)) (EInt 1))
>
> prop_p1_p2 = nLam (\n -> EEq (EApp p1 (EBVar n)) (EApp p2 (EBVar n))) 

> prop_fact = nLam (\n -> EApp isPositive (EApp fact (EBVar n))) 

> t = eval (EApp fact (EInt 10))

> t1 = eval (EApp sumList (toIntList [1..100]))

> toList :: (a -> PExp b c) -> [a] -> PExp b c
> toList f []      = ECon "Nil" []
> toList f (x:xs)  = ECon "Cons" [f x, toList f xs]
>
> toIntList = toList EInt

> fun e = putStrLn (pp (exec (seval e)))

