> module MiniFun where

> import Prelude hiding (EQ,LT)
> import Data.Maybe
> import Data.IntMap (IntMap)
> import qualified Data.IntMap as IM

Using PHOAS to represent variable binding

Need to represent primitives in a better way?

> -- Empty type for saying 'no free variables'
> data Void

> -- We need the type of types!
> data AType = TInt | TBool
>   deriving (Show, Eq)
> data PType = TAtom AType | AType :-> PType
>   deriving (Show, Eq)

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

> data Value = VInt Int | VBool Bool | VFun (Value -> Value) | VCon String [Value]
>
> eval :: PExp Value Void -> Value
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
> eval (ELam f _)         = VFun (eval . f)
> eval (EApp e1 e2)       = 
>  case (eval e1) of
>     VFun f -> f (eval e2)
> eval (ECon s xs)        = VCon s (map eval xs)
> eval (ECase e clauses)  = 
>  case eval e of
>     VCon s vs -> eval (fromJust (lookup s clauses) vs)

Symbolic interpreter

> data SymValue = 
>     SFVar Int PType -- free variables 
>   | SInt Int 
>   | SBool Bool 
>   | SEq SymValue SymValue
>   | SLt SymValue SymValue
>   | SAdd SymValue SymValue
>   | SMul SymValue SymValue
>   | SApp SymValue SymValue
>   | SCon String [SymValue]
>   | SFun (ExecutionTree -> ExecutionTree) PType -- just store the function
>
> -- Add Declare constructor?
> data ExecutionTree = Exp SymValue | Fork SymValue (ExecutionTree) (ExecutionTree) 

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
> seval (EBool b)          = Exp (SBool b)
> seval (EIf e1 e2 e3)     = propagate (seval e1) (seval e2) (seval e3) -- loses sharing!!
> seval (EAdd e1 e2)       = merge (SAdd,ADD) (seval e1) (seval e2) -- loses sharing!!
> seval (EMul e1 e2)       = merge (SMul,MUL) (seval e1) (seval e2) -- loses sharing!!
> seval (EEq e1 e2)        = merge (SEq,EQ)  (seval e1) (seval e2) -- loses sharing!!
> seval (ELt e1 e2)        = merge (SLt,LT)  (seval e1) (seval e2)
> seval (ELam f t)         = Exp (SFun (seval . f) t)
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


> treeApply (Exp (SFVar x pt)) t = apply (SApp (SFVar x pt)) t  -- f e
> treeApply (Exp (SFun f pt))  t = f t                       -- (\x . e1) e2
> treeApply (Fork e1 e2 e3)    t = Fork e1 (treeApply e2 t) (treeApply e3 t)
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

> ppz3' :: ExecutionTree -> String -> IntMap PType -> Int -> [String]
> ppz3' _       s vars 0    = []
> ppz3' (Exp e) s vars stop = [s ++ "\n(check-sat)\n" ++ simplify e ++ "\n(pop)"]
> ppz3' (Fork e1 e2 e3) s vars stop = 
>  let v1 = freeSVars e1
>      undeclared = v1 `IM.difference` vars
>      newdecls   = unlines $ map declare $ IM.assocs undeclared
>      vars'      = vars `IM.union` undeclared
>      s' = s ++ "\n" ++ newdecls
>      s2 = ppz3' e2 (s' ++ assert e1)    vars' (stop - 1)
>      s3 = ppz3' e3 (s' ++ assertNeg e1) vars' (stop - 1)
>  in s2 ++ s3

> declare :: (Int, PType) -> String
> declare (n, TAtom TInt) = "(declare-const " ++ ppSVar n ++ " Int)"

> assert, assertNeg :: SymValue -> String
> assert e    = "(assert "      ++ ppFPNSymValue e ++ ")"
> assertNeg e = "(assert (not " ++ ppFPNSymValue e ++ "))"
> simplify :: SymValue -> String
> simplify e  = "(simplify "    ++ ppFPNSymValue e ++ ")"

> -- Get all SFVars that are mentioned in a symbolic expression and their types
> -- to make sure that they are declared before first use.
> freeSVars :: SymValue -> IntMap PType
> freeSVars (SFVar n pt)  = IM.singleton n pt
> --freeSVars (SInt i)      = IM.empty
> --freeSVars (SBool b)     = IM.empty
> freeSVars (SEq v1 v2)   = freeSVars v1 `IM.union` freeSVars v2
> freeSVars (SAdd v1 v2)  = freeSVars v1 `IM.union` freeSVars v2
> freeSVars (SMul v1 v2)  = freeSVars v1 `IM.union` freeSVars v2
> freeSVars (SLt v1 v2)   = freeSVars v1 `IM.union` freeSVars v2
> freeSVars (SApp v1 v2)  = freeSVars v1 `IM.union` freeSVars v2
> --freeSVars (SFun f _)    = "<<function>>"
> freeSVars _             = IM.empty

> ppSVar :: Int -> String
> ppSVar n = "x" ++ show n

> ppSymValue :: SymValue -> String
> ppSymValue (SFVar n pt)  = ppSVar n
> ppSymValue (SInt i)      = show i
> ppSymValue (SBool b)     = show b
> ppSymValue (SEq v1 v2)   = "(" ++ ppSymValue v1 ++ " == " ++ ppSymValue v2 ++ ")"
> ppSymValue (SAdd v1 v2)  = "(" ++ ppSymValue v1 ++ " + " ++ ppSymValue v2 ++ ")"
> ppSymValue (SMul v1 v2)  = "(" ++ ppSymValue v1 ++ " * " ++ ppSymValue v2 ++ ")"
> ppSymValue (SLt v1 v2)   = "(" ++ ppSymValue v1 ++ " < " ++ ppSymValue v2 ++ ")"
> ppSymValue (SApp v1 v2)  = ppSymValue v1 ++ " " ++ ppSymValue v2
> ppSymValue (SFun f _)    = "<<function>>"

> ppFPNSymValue :: SymValue -> String
> ppFPNSymValue (SFVar n pt)  = ppSVar n
> ppFPNSymValue (SInt i)      = show i
> ppFPNSymValue (SBool True)  = "true"
> ppFPNSymValue (SBool False) = "false"
> ppFPNSymValue (SEq v1 v2)   = "(= " ++ ppFPNSymValue v1 ++ " " ++ ppFPNSymValue v2 ++ ")"
> ppFPNSymValue (SAdd v1 v2)  = "(+ " ++ ppFPNSymValue v1 ++ " " ++ ppFPNSymValue v2 ++ ")"
> ppFPNSymValue (SMul v1 v2)  = "(* " ++ ppFPNSymValue v1 ++ " " ++ ppFPNSymValue v2 ++ ")"
> ppFPNSymValue (SLt v1 v2)   = "(< " ++ ppFPNSymValue v1 ++ " " ++ ppFPNSymValue v2 ++ ")"
> ppFPNSymValue (SApp v1 v2)  = "("   ++ ppFPNSymValue v1 ++ " " ++ ppFPNSymValue v2 ++ ")"
> ppFPNSymValue (SFun f _)    = error "ppFPNSymValue of SFun"

> instance Show Value where
>   show (VFun _)   = "<<function>>"
>   show (VInt x)   = show x
>   show (VBool b)  = show b

> nLam b = ELam b (TAtom TInt)

> fact = ELet (\fact -> nLam (\n ->
>   EIf (ELt (EBVar n) (EInt 1))
>       (EInt 1)
>       (EMul (EBVar n) (EApp (EBVar fact) (EAdd (EBVar n) (EInt (-1))))))) EBVar

> sumList = ELet (\sumList -> ELam (\l -> 
>   ECase (EBVar l) [
>     ("Nil", \_ -> EInt 0),
>     ("Cons", \(x:xs:[]) -> EAdd (EBVar x) (EApp (EBVar sumList) (EBVar xs)))
>   ]) (error "We have no suitable type yet:)")) EBVar

> isPositive = nLam (\n -> ELt (EInt 0) (EBVar n))

> p1 = nLam (\n -> EIf (ELt (EBVar n) (EInt 10)) (EInt (-1)) (EInt 1))
>
> p2 = nLam (\n -> EIf (ELt (EBVar n) (EInt 5)) (EInt (-1)) (EInt 1))
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
> -- This produces a z3 output, but (push) and (pop) don't seem to work,
> -- so pasting individual cases is the way to go for now.
> fun' e = mapM_ putStrLn $ (ppz3' (exec (seval e)) "(push)" IM.empty 6)
