> module Z3Backend where

> import Control.Monad (ap, liftM2, when, mplus)
> import Control.Monad.IO.Class (liftIO)
> import Data.List ((\\))
> import Data.IntMap (IntMap, (!))
> import qualified Data.IntMap as IM
> import Z3.Monad

> import MiniFun2
> import DataTypes


> testZ3 e = testZ3T e defaultTarget

> defaultTarget s (SCon c _) | c == cFalse    = do
>     liftIO $ do 
>         putStrLn "\nCounterexample!" 
>         putStrLn $ s ++ " ==> False"
>     (r,Just ()) <- withModel ((>>= (liftIO . putStrLn)) . showModel)
>     return ()
> defaultTarget s e = liftIO $ putStrLn $ s ++ " ==> " ++ ppSymValue' e 

> filterTarget c t' s v@(SCon c' _) | c == c' = liftIO (putStrLn "") >> t' s v
> filterTarget _ _  _ _                       = liftIO (putStr ".")


> testZ3T :: (PExp ExecutionTree,[DataType]) -> (String -> SymValue -> Z3 ()) -> Int -> IO ()
> testZ3T (e,dts) targetCon n = evalZ3 $ do
>   int <- mkIntSort 
>   bool <- mkBoolSort
>   adtSym <- mkStringSymbol "adtSort"
>   adt <- mkUninterpretedSort adtSym -- For now, all ADT values have the same sort
>   -- let adt = int   -- Use ints for ADT values?
>   cfs <- preludeZ3 (bool,int,adt) dts
>   let (ex, nVars) = exec $ seval e
>       env = Z3Env {nextName = nVars+1
>                   , intSort = int, boolSort = bool, adtSort = adt
>                   , conFuns = cfs
>                   , symVars = IM.empty
>                   , target  = targetCon
>                   }
>   pathsZ3 env ex "True" n
> 


We map each constructor to a Z3 function symbol and its parameter sorts. 
Also does some initial assertions.

> preludeZ3 :: (Sort,Sort,Sort) -> [DataType] -> Z3 (ConMap ConFun)
> preludeZ3 sorts dts = do
>   cm <- mkConMapM (conFun sorts) dts
>   mapM_ (mkPrelude cm) dts
>   -- mapM_ (mkInj cm) (concatMap dataCons dts)
>   showContext >>= liftIO . putStrLn
>   return cm

> conFun :: (Sort,Sort,Sort) -> Constructor -> Z3 ConFun
> conFun (bool,int,adt) c = do
>   s <- mkStringSymbol $ "c"++show (conId c) ++ "_" ++ conName c -- Can just use mkIntSymbol?
>   let
>     paramSorts = map dataSort (conParams c)
>   fd <- mkFuncDecl s paramSorts adt
>   projectors <- mapM mkProjector (zip paramSorts [0..])
>   return (fd, zip paramSorts projectors)
>   where
>     mkProjector :: (Sort,Int) -> Z3 FuncDecl
>     mkProjector (s,n) = do
>       symb <- mkStringSymbol $ "p"++show n++"_"++show (conId c)
>       mkFuncDecl symb [adt] s
>     dataSort :: DataType -> Sort
>     dataSort d | isBoolType d  = bool
>                | isIntType d   = int
>                | otherwise     = adt

Assert that constructors are distinct

> mkPrelude :: ConMap ConFun -> DataType -> Z3 ()
> mkPrelude cm dt = do
>   ast <- myForall allSorts (\vars -> mkCon vars cons >>= mkDistinct)
>   assertCnstr ast
>   where allSorts = concatMap (conFunSorts . cm) cons
>         cons     = dataCons dt
>         mkCon [] []      = return []
>         mkCon vs (c:cs)  = do 
>           x  <- mkApp (fst $ cm c) vshere
>           xs <- mkCon vsrest cs
>           return (x : xs)
>           where (vshere, vsrest) = splitAt (length (conParams c)) vs


> myForall :: [Sort] -> ([AST] -> Z3 AST) -> Z3 AST
> myForall sorts f = do 
>   symbs <- mapM (\(s,n) -> mkIntSymbol n >>= \smb -> return (smb,s)) $ zip sorts [0..]
>   bound <- mapM (\(s,n) -> mkBound n s) $ zip sorts [0..]
>   res <- f bound 
>   uncurry (mkForall []) (unzip symbs) res 


ConFun is stored in a ConMap, and used for generating assertions when we encounter a case expression. A ConFun is a constructor function declaration, sorts for the constructor parameters, and a projection function declaration for each parameter.

For example, for Cons :: Int -> [Int] -> [Int], it is (cons :: Int -> ADT -> ADT, [(Int, head :: ADT -> Int), (ADT, tail :: ADT -> ADT]).

> type ConFun = (FuncDecl,[(Sort,FuncDecl)])
> conFunSorts :: ConFun -> [Sort]
> conFunSorts = fst . unzip . snd

> data Z3Env = Z3Env {nextName  :: Int
>                    , boolSort :: Sort
>                    , intSort  :: Sort, adtSort :: Sort
>                    , conFuns  :: ConMap ConFun
>                    , symVars  :: IntMap AST
>                    , target   :: String -> SymValue -> Z3 ()
>                    }

> pathsZ3 :: Z3Env -> ExecutionTree -> String -> Int -> Z3 ()
> pathsZ3 _    _       s stop | stop <= 0  = return ()
> pathsZ3 env (Exp e) s stop               = target env s e
> -- pathsZ3 _    (Exp e) s stop              = liftIO $ putStr $ "."
> pathsZ3 env (NewSymVar n t e) s stop     = do
>  (v,ast) <- declareVar env (n,t)
>  pathsZ3 env{symVars = IM.insert v ast (symVars env)} e s stop
> pathsZ3 env (Fork dt e cs w) s stop     
>   | isBoolType dt  = do 
>     ast <- assertProjs env e
>     let assertBoolCon :: (Constructor, ExecutionTree) -> Z3 ()
>         assertBoolCon (c,ex) 
>           | fromBool c =  local (assertCnstr ast >> whenSat (re ex (s ++ " && "++ppSymValue' e) (stop - 1)))
>           | otherwise  = local (mkNot ast >>= assertCnstr >> whenSat (re ex (s ++ " && not "++ppSymValue' e) (stop - 1)))
>     mapM_ assertBoolCon (map (\(c,f) -> (c, f [])) cs)
>     -- TODO: Deal with wildcard pattern here!
>
>   | isIntType dt    = error "Pattern matching on integers not yet supported"
> {-
>   | SCon c vs <- e, Just exf <- lookup c cs, length (conParams c) == 0 =  do
>     pathsZ3 env (exf []) s (stop-1)
>   | SCon c vs <- e, Just exf <- lookup c cs = do
>     asts <- mapM (symValueZ3 env) vs
>     let cs@(cf,cps) = conFuns env c
>         nVars       = length cps
>         newNext     = nextName env + nVars
>         newNames    = [nextName env..newNext-1]
>     newVars <- sequence [declareVarSort s nn | ((s,p),nn) <- zip cps newNames]
>     let varAsts = map snd newVars
>         env'    = env{nextName = newNext, symVars = IM.union (IM.fromList newVars) (symVars env)}
>     astEqs  <- mapM (uncurry mkEq) (zip asts varAsts) >>= mkAnd
>     assertCnstr astEqs
>     app    <- mkApp cf varAsts
>     mapM (assertProj app) (zip (map snd cps) varAsts)
>     let ex = exf $ map mkExecTree newNames
>     whenSat (pathsZ3 env' ex (s ++ " &&& " ++conName c ++ " " ++ unwords (map (("x"++).show) newNames) ++ " = " ++ ppSymValue' e) (stop-1)) 
>-}
>   | otherwise       = do
>     -- Assert projections for all constructors in the expression on which the case analysis is performed.
>     ast <- assertProjs env e
>     let assertCon :: (Constructor, [ExecutionTree] -> ExecutionTree) -> Z3 ()
>         assertCon cex@(c,exf) = do
>           let cs@(cf,cps) = conFuns env c
>               nVars       = length cps
>               newNext     = nextName env + nVars
>               newNames    = [nextName env..newNext-1]
>           newVars <- sequence [declareVarSort s nn | ((s,p),nn) <- zip cps newNames]
>           let varAsts = map snd newVars
>               env'    = env{nextName = newNext, symVars = IM.union (IM.fromList newVars) (symVars env)}
>           app    <- mkApp cf varAsts
>           astEq  <- mkEq ast app
>           -- Assert equality of the matched expression and the constructor function application from a specific case branch.
>           assertCnstr astEq
>           -- Assert injectivity of the constructor function from a specific case branch.
>           mapM (assertProj app) (zip (map snd cps) varAsts)
>           let ex = exf $ map mkExecTree newNames
>           whenSat (pathsZ3 env' ex (s ++ " && " ++ ppSymValue' e ++ " = " ++ conName c ++ " " ++ unwords (map (("x"++).show) newNames)) (stop-1)) 
>     mapM_ (local . assertCon) cs
>     -- TODO: Deal with wildcard pattern here!
>     let w' = maybe (Bomb "Pattern match failure") id w
>     case dataCons dt \\ map fst cs of
>       []  -> return ()
>       [x] -> assertCon (x, const w')
>       xs  -> undefined
>   where
>     re = pathsZ3 env
>   
>

> mkExecTree n = Exp (SFVar n (error "mkExecTree: Why would I need a type here?"))


Asserts e.g. that head (Cons x xs) = x
By asserting this whenever we pattern match on a Cons value (for the tail as well), we 
assert injectivity of Cons (by giving it a partial inverse) without using universal quantification.

For the example above we would do assertProj (Cons x xs) (head, x)

> assertProj :: AST -> (FuncDecl,AST) -> Z3 ()
> assertProj app (fd, var) = do
>   ast <- mkApp fd [app] >>= mkEq var
>   assertCnstr ast

Assert that all constructor applications in a SymValue are injective, and return the AST corresponding to the SymValue.

Probably this repeats a lot of work when the same SymValue appears in several Forks.

> assertProjs :: Z3Env -> SymValue -> Z3 AST
> assertProjs env@Z3Env{conFuns = cfs, symVars = vars} sv0 = go sv0 where
>   go (SCon c vs) | c == cTrue || c == cFalse = if fromBool c then mkTrue else mkFalse
>   go (SCon c vs) = do
>     asts <- mapM go vs
>     let (cf,cps) = cfs c
>     ast <- mkApp cf asts
>     mapM (assertProj ast) (zip (map snd cps) asts)
>     return ast
>   go (SFVar n pt)  = return $ vars ! n
>   go (SInt i)      = mkInt i
>   go (SEq v1 v2)   = do
>    x1 <- go v1
>    x2 <- go v2
>    mkEq x1 x2
>   go (SLt v1 v2)   = do
>    x1 <- go v1
>    x2 <- go v2
>    mkLt x1 x2
>   go (SAdd v1 v2)  = do
>    x1 <- go v1
>    x2 <- go v2
>    mkAdd [x1, x2]
>   go (SMul v1 v2)  = do
>    x1 <- go v1
>    x2 <- go v2
>    mkMul [x1, x2]
>   go (SApp v1 v2)  = do
>    x1 <- symFunZ3 env v1
>    x2 <- go v2
>    mkApp x1 [x2] -- This will be difficult to implement for partial functions
>   go (SFun f _)    = error "symValueZ3 of SFun"
>  


>
> local :: Z3 a -> Z3 a
> local m = do
>   push 
>   a <- m
>   pop 1
>   return a
> 

> whenSat :: Z3 () -> Z3 ()
> whenSat m = do
>   b <- fmap resToBool check 
>   when b m


> resToBool Sat   = True
> resToBool Unsat = False
> resToBool Undef = error $ "resToBool: Undef"

> declareVar :: Z3Env -> (Int, DataType) -> Z3 (Int, AST)
> declareVar env (n, t)     | isIntType  t = declareVarSort (intSort env) n
>                           | isBoolType t = declareVarSort (boolSort env) n
>                           | otherwise    = declareVarSort (adtSort env) n 

> declareVarSort :: Sort -> Int -> Z3 (Int, AST)
> declareVarSort s n = do
>   x <- mkIntSymbol n
>   c <- mkConst x s
>   return (n,c)

> symFunZ3 :: Z3Env -> SymValue -> Z3 FuncDecl
> symFunZ3 Z3Env{} sv = error "symFunZ3 not implemented yet"





{-

> -- Causes Z3 to loop :(
> mkInj ::ConMap ConFun -> Constructor -> Z3 ()
> mkInj cm c = case cm c of
>   (_,[])      -> return ()
>   cf@(ca,_)  -> do
>      fa <- myForall (ss ++ ss) f
>      assertCnstr fa 
>      where ss = conFunSorts cf
>            f vs = do 
>              app1 <- mkApp ca vsa
>              app2 <- mkApp ca vsb
>              lhs <- mkEq app1 app2
>              eqs <- mkEq (head vsa) (head vsb) >>= return . return -- sequence $ zipWith mkEq vsa vsb
>              rhs <- mkAnd eqs
>              mkImplies lhs rhs
>              where (vsa, vsb) = splitAt (length ss) vs

-}
