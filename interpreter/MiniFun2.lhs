

> module MiniFun2 where

> import Prelude hiding (EQ,LT)
> import Data.Maybe
> import Control.Monad.State
> import DataTypes
> import Control.Monad

Using PHOAS to represent variable binding

Need to represent primitives in a better way?

> -- Empty type for saying 'no free variables'
> data Void


> data PExp a b =
>     EFVar b 
>   | EBVar a
>   | EInt Int
>   | EEq (PExp a b) (PExp a b)
>   | ELt (PExp a b) (PExp a b)
>   | EAdd (PExp a b) (PExp a b)
>   | EMul (PExp a b) (PExp a b)
>   | ELet (a -> PExp a b) (a -> PExp a b)
>   | ELam (a -> PExp a b) DataType
>   | EApp (PExp a b) (PExp a b)
>   -- Adding case analysis and constructors
>   | ECon Constructor [PExp a b]                -- constructor
>   | ECase DataType (PExp a b) [(Constructor, [a] -> PExp a b)] (Maybe (PExp a b))     -- case expression

          ECase t e [c,e1] (Just e2) 
          ~ 
          case e :: t of 
            c a b -> e1 a b
            _     -> e2

Some convenient functions and instances for writing expressions.

> instance Num (PExp a b) where
>   (+)    = EAdd
>   (*)    = EMul
>   a - b  = a + b * EInt (-1) -- EInt needs to be here or GHC will "optimize" this into an infinite loop.
>   abs    = error "abs not implemented"
>   signum       = error "signum not implemented" -- ELam (\x -> ECase (ELt x (EInt 0)) ...
>   fromInteger  = EInt . fromInteger

> var      = EBVar
> (*$)     = EApp
> (*==)    = EEq
> (*<)     = ELt
> t *\ f   = ELam (f . var) t -- Automatically wraps all variable occurrences in var
> infixr 1 *$
> infix 4 *==
> infix 4 *<
> infixr 0 *\

Default case expressions, infers the type from the constructors matched.

> cases :: PExp a b -> [(Constructor, [PExp a b] -> PExp a b)] -> PExp a b
> cases e alts = caseInf e alts Nothing
>
> casesW :: PExp a b -> [(Constructor, [PExp a b] -> PExp a b)] -> PExp a b -> PExp a b
> casesW e alts w = caseInf e alts (Just w) 
> 

>
> caseInf e alts@((c,_):_) wild = ECase (conType c) e wrapped wild
>   where wrapped = [(c,f . map var) |(c,f) <- alts] 
> caseInf _ [] _                = error "caseInf: empty case" -- Should be translated into "EError" or such?

> nLam b = tInt *\ b
> bLam b = tBool *\ b

> lets :: (PExp a b -> PExp a b) -> (PExp a b -> PExp a b) -> PExp a b
> lets f g = ELet (f . var) (g . var)


Standard (big-step) interpreter

> data Value = VInt Int | VFun (Value -> Value) | VCon Constructor [Value]
>
> eval :: PExp Value Void -> Value
> eval (EFVar _)       = error "ops! Free variable"
> eval (EBVar v)       = v
> eval (EInt x)        = VInt x
> eval (EEq e1 e2)     =
>  case (eval e1, eval e2) of 
> --    (VBool v1, VBool v2) -> VCon (show (v1 == v2))
>     (VInt v1, VInt v2)   -> VCon (litBool (v1 == v2)) []
> eval (ELt e1 e2)     =
>  case (eval e1, eval e2) of
>     (VInt v1, VInt v2) -> VCon (litBool (v1 < v2)) []
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
> eval (ECon s xs)             = VCon s (map eval xs)
> eval (ECase t e clauses wild)       =
>  case eval e of
>     VCon s vs -> eval $ fromJust (fmap ($vs) (lookup s clauses) `mplus` wild)
>     -- VInt ...

Symbolic interpreter

> data SymValue = 
>     SFVar Int DataType -- free variables 
>   | SInt Int 
>   | SEq SymValue SymValue
>   | SLt SymValue SymValue
>   | SAdd SymValue SymValue
>   | SMul SymValue SymValue
>   | SApp SymValue SymValue
>   | SCon Constructor [SymValue]
>   | SFun (ExecutionTree -> ExecutionTree) DataType -- just store the function

> type Pattern = ((String,Int), [Int])

> pname :: Pattern -> String
> pname = fst . fst
>
> pargs :: Pattern -> [Int]
> pargs = snd

> data ExecutionTree = Exp SymValue 
>                    | Fork DataType SymValue [(Constructor, [ExecutionTree] -> ExecutionTree)] (Maybe ExecutionTree)
>                    | NewSymVar Int DataType ExecutionTree -- Not fully implemented yet...

> data Op = ADD | MUL | LT | EQ

Applies program to symbolic variables

> exec :: ExecutionTree -> (ExecutionTree, Int)
> exec e = exec' e 0
>
> exec' :: ExecutionTree -> Int -> (ExecutionTree, Int)
> exec' (Exp (SFun f t)) n = case (exec' (f (Exp (SFVar n t))) (n+1)) of
>   (e,n') -> (NewSymVar n t e,n')
> exec' e                n = (e,n)

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
> seval (ECase t e clauses w)  = propagate t (seval e) (map (\(s,c) -> (s, seval . c)) clauses) (fmap seval w)

> propagate :: DataType -> ExecutionTree -> [(Constructor, [ExecutionTree] -> ExecutionTree)] -> (Maybe ExecutionTree) -> ExecutionTree
> propagate dt  (Exp e) es w              = Fork dt e es w 
> propagate dt' (Fork dt e es w) es' w'   = Fork dt e [(s, \l -> propagate dt' (f l) es' w') | (s,f) <- es] 
>                                                     (fmap (\we -> propagate dt' we es' w') w)
> propagate dt (NewSymVar n t e) es w = NewSymVar n t (propagate dt e es w)

TODO: Improve code here
 1) Should be possible to use 1 definition for merge instead of "mergeList" and "merge"
    (Also mergeList need to do partial-evaluation as merge)
 2) Deal with operators in a better way
 3) Integrate NewSymVar (?)
 
> mergeList f []                    = Exp (f [])
> mergeList f (Exp e : xs)          = mergeList (\es -> f (e:es)) xs
> mergeList f (Fork dt e es w : xs)  = 
>   Fork dt e [ (s, \l -> mergeList f (g l : xs)) | (s,g) <- es] (fmap (\we -> mergeList f (we:xs)) w)
> mergeList f (NewSymVar n d e : xs) = NewSymVar n d (mergeList f (e:xs))
>
> merge (_,MUL) (Exp (SInt x)) (Exp (SInt y)) = Exp (SInt (x*y)) -- partial evaluation
> merge (_,MUL) (Exp (SInt 1)) e = e
> merge (_,MUL) e (Exp (SInt 1)) = e
> merge (_,MUL) (Exp (SInt 0)) e = Exp (SInt 0)
> merge (_,MUL) e (Exp (SInt 0)) = Exp (SInt 0)
> merge (_,ADD) (Exp (SInt x)) (Exp (SInt y)) = Exp (SInt (x+y))
> merge (_,EQ) (Exp (SInt x)) (Exp (SInt y)) = Exp (SCon (litBool (x==y)) [])
> -- merge (_,EQ) (Exp (SBool x)) (Exp (SBool y)) = Exp (SBool (x==y))
> merge (_,LT) (Exp (SInt x)) (Exp (SInt y)) = Exp (SCon (litBool $ (x < y)) [])
> merge f (Exp e1) (Exp e2) = Exp (fst f e1 e2)
> merge f (Fork dt e es w) t = Fork dt e [(s, \l -> merge f (v l) t) | (s,v) <- es] (fmap (\we -> merge f we t) w) -- (merge f e2 t) (merge f e3 t)
> merge f t (Fork dt e es w) = Fork dt e [(s, \l -> merge f t (v l)) | (s,v) <- es] (fmap (\we -> merge f t we) w) -- (merge f t e2) (merge f t e3) 
>                                                                                     -- BUG? This was swapping the params of merge before.
> merge f (NewSymVar n d e) t = NewSymVar n d (merge f e t)
> merge f t (NewSymVar n d e) = NewSymVar n d (merge f t e) -- TODO: Not sure if this is correct, maybe the scope of the symVar is widened here?

Merge is too eager? 


> treeApply (Exp (SFVar x pt)) t = apply (SApp (SFVar x pt)) t  -- f e
> treeApply (Exp (SFun f pt))  t = f t                          -- (\x . e1) e2
> -- treeApply (Exp (SEq _ _))    _ = error "treeApply: Bad function"
> treeApply (Fork dt e es w)   t = Fork dt e [(s, \l -> treeApply (v l) t) | (s,v) <- es] (fmap (\we -> treeApply we t) w)
> treeApply (NewSymVar n d e)  t = NewSymVar n d (treeApply e t)
>
> apply f (Exp e)              = Exp (f e) 
> apply f (Fork t e es w)      = Fork t e [(s, apply f . v) | (s,v) <- es] (fmap (apply f) w) -- (apply f e2) (apply f e3)
> apply f (NewSymVar n d e)    = NewSymVar n d (apply f e)

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
> pp' (Fork t e1 [(c2,e2),(c3,e3)] _) s stop n = -- fix me! generalize to arbitrary size list and wildcards
>  let s1         = ppSymValue e1 n
>      (s2,stop2) = pp' (e2 (fresh n)) (s ++ " && " ++ s1 ++ " = " ++ showConName c2 ++ " " ++  genVars (conArity c2) n) stop (n + conArity c2)
>      (s3,stop3) = pp' (e3 (fresh n)) (s ++ " && " ++ s1 ++ " = " ++ showConName c3 ++ " " ++ genVars (conArity c3) n) stop2 (n + conArity c3)
>  in (s2 ++ s3,stop3)
> pp' (NewSymVar _ _ e) s m n = pp' e s m n


> genVars 0 i = ""
> genVars n i = "x" ++ show i ++ " " ++ genVars (n-1) (i+1)

> fresh n = map (\n -> Exp (SFVar n DataInt)) (iterate (+1) n)

> pp (e,n) = fst $ pp' e "True" 5 n -- stop after 5 results

> ppSymValue :: SymValue -> Int -> String
> ppSymValue (SFVar n pt) _   = "x" ++ show n
> ppSymValue (SInt i)     n  = show i
> ppSymValue (SCon s vs)  n  = showConName s ++ " " ++ concatMap (\v -> "(" ++ ppSymValue v n ++ ") ") vs 
> ppSymValue (SEq v1 v2)  n  = "(" ++ ppSymValue v1 n ++ " == " ++ ppSymValue v2 n ++ ")"
> ppSymValue (SAdd v1 v2) n  = "(" ++ ppSymValue v1 n ++ " + " ++ ppSymValue v2 n ++ ")"
> ppSymValue (SMul v1 v2) n  = "(" ++ ppSymValue v1 n ++ " * " ++ ppSymValue v2 n ++ ")"
> ppSymValue (SLt v1 v2)  n  = "(" ++ ppSymValue v1 n ++ " < " ++ ppSymValue v2 n ++ ")"
> ppSymValue (SApp v1 v2) n  = ppSymValue v1 n ++ " " ++ ppSymValue v2 n
> ppSymValue (SFun f t)   n  = "<<function>>" -- "(\\x" ++ show n ++ ". " ++ f (Exp (SFVar n t)) ++ ")" -- <<function>>"

> ppSymValue' e = ppSymValue e 100 -- The int is not used?

> instance Show Value where
>   show (VFun _)   = "<<function>>"
>   show (VInt x)   = show x
>   show (VCon s [])   = showConName s










> fun e = putStrLn (pp (exec (seval e)))



