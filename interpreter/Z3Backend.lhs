> module Z3Backend where

> import Control.Monad (ap, liftM2, when)
> import Control.Monad.IO.Class (liftIO)
> import Data.IntMap (IntMap, (!))
> import qualified Data.IntMap as IM
> import Z3.Monad

> import MiniFun2
> import DataTypes

> testZ3 :: (PExp ExecutionTree Void,[DataType]) -> Int -> IO ()
> testZ3 (e,dts) n = evalZ3 $ do
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
>                   }
>   pathsZ3 env ex "True" n
> 


We map each constructor to a Z3 function symbol and its parameter sorts. 
Also does some initial assertions.

> preludeZ3 :: (Sort,Sort,Sort) -> [DataType] -> Z3 (ConMap (FuncDecl, [Sort]))
> preludeZ3 sorts dts = do
>   cm <- mkConMapM (conFun sorts) dts
>   mapM_ (mkPrelude cm) dts
>   return cm

> conFun :: (Sort,Sort,Sort) -> Constructor -> Z3 (FuncDecl, [Sort])
> conFun (bool,int,adt) c = do
>   s <- mkStringSymbol $ show (conId c) ++ "_" ++ conName c -- Can just use mkIntSymbol?
>   let
>     paramSorts = map dataSort (conParams c)
>     dataSort :: DataType -> Sort
>     dataSort d | isBoolType d  = bool
>                | isIntType d   = int
>                | otherwise     = adt
>   fd <- mkFuncDecl s paramSorts adt
>   return (fd, paramSorts)

> mkPrelude :: ConMap (FuncDecl, [Sort]) -> DataType -> Z3 ()
> mkPrelude cm dt = do
>   ast <- myForall allSorts (\vars -> mkCon vars cons >>= mkDistinct)
>   assertCnstr ast
>   where allSorts = concatMap (snd . (cm$)) cons
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


> data Z3Env = Z3Env {nextName :: Int, boolSort :: Sort, intSort :: Sort, adtSort :: Sort, conFuns :: ConMap (FuncDecl,[Sort]), symVars :: IntMap AST}

> pathsZ3 :: Z3Env -> ExecutionTree -> String -> Int -> Z3 ()
> pathsZ3 _    _       s stop | stop <= 0  = return ()
> pathsZ3 _    (Exp e) s stop              = liftIO $ putStrLn $ s ++ " ==> " ++ ppSymValue' e
> pathsZ3 env (NewSymVar n t e) s stop    = do
>  (v,ast) <- declareVar env (n,t)
>  pathsZ3 env{symVars = IM.insert v ast (symVars env)} e s stop
> pathsZ3 env (Fork dt e cs w) s stop     
>   | isBoolType dt  = do 
>         ast <- symValueZ3 env e
>         let assertBoolCon :: (Constructor, ExecutionTree) -> Z3 ()
>             assertBoolCon (c,ex) 
>               | fromBool c = local (assertCnstr ast >> whenSat (re ex (s ++ " && "++ppSymValue' e) (stop - 1)))
>               | otherwise  = local (mkNot ast >>= assertCnstr >> whenSat (re ex (s ++ " && "++ppSymValue' e) (stop - 1)))
>         mapM_ assertBoolCon (map (\(c,f) -> (c, f [])) cs)
>         -- Deal with wildcard pattern here!
>           
>   | isIntType dt   = error "Pattern matching on integers not yet supported"
>   | otherwise      = do
>          ast <- symValueZ3 env e
>          let assertCon :: (Constructor, [ExecutionTree] -> ExecutionTree) -> Z3 ()
>              assertCon (c,ex) = do
>                let (cf,cSorts) = conFuns env c
>                    nVars       = length cSorts
>                    newNext     = nextName env + nVars
>                    newNames    = [nextName env..newNext-1]
>                newVars <- mapM (uncurry declareSort) (zip cSorts newNames)
>                let varAsts = map snd newVars
>                    env'    = env{nextName = newNext, symVars = IM.union (IM.fromList newVars) (symVars env)}
>                -- return ()
>                app  <- mkApp cf varAsts
>                ast' <- mkEq ast app
>                assertCnstr ast'
>                whenSat (pathsZ3 env' (ex $ map mkExecTree newNames) (s ++ " && " ++conName c ++ " ~ " ++ ppSymValue' e) (stop-1)) 
>                -- whenSat (re ex (s ++ " && "++conName c ++ " ~ " ++ ppSymValue' e) (stop - 1)))
>          mapM_ (local . assertCon) cs
>          -- Deal with wildcard pattern here!
>   where
>     re = pathsZ3 env
>   
>

> mkExecTree n = Exp (SFVar n (error "mkExecTree: Why would I need a type here?"))

>
> local :: Z3 a -> Z3 a
> local m = do
>   push 
>   a <- m
>   pop 1
>   return a
> 

>  -- let v1 = freeSVars e1
>  --    undeclared = v1 `IM.difference` vars
>  -- newdecls <- mapM (declareVar intSort) $ IM.assocs undeclared
>  -- let vars'      = vars `IM.union` IM.fromList newdecls
>  --    s' = s ++ "\n" ++ newdecls
>  {- ast <- symValueZ3 vars e1
>  push
>  assertCnstr ast
>  whenSat $ re e2 (s ++ " && "++ppSymValue' e1) vars (stop - 1)
>  pop 1
>  ast' <- mkNot ast
>  assertCnstr ast'
>  whenSat $ re e3 (s ++ " && not "++ppSymValue' e1) vars (stop - 1)
>  where
>    re = pathsZ3 intSort -}


  assertCon :: Constructor -> AST
  assertCon (Constructor{con



> whenSat :: Z3 () -> Z3 ()
> whenSat m = do
>   b <- fmap resToBool check 
>   when b m


> resToBool Sat   = True
> resToBool Unsat = False
> resToBool Undef = error $ "resToBool: Undef"

> declareVar :: Z3Env -> (Int, DataType) -> Z3 (Int, AST)
> declareVar env (n, t)     | isIntType  t = declareSort (intSort env) n
>                           | isBoolType t = declareSort (boolSort env) n
>                           | otherwise    = declareSort (adtSort env) n 

> declareSort :: Sort -> Int -> Z3 (Int, AST)
> declareSort s n = do
>   x <- mkIntSymbol n
>   c <- mkConst x s
>   return (n,c)

> symValueZ3 :: Z3Env -> SymValue -> Z3 AST
> symValueZ3 env@Z3Env{symVars = vars, conFuns = cfs} sv = go sv where
>  go :: SymValue -> Z3 AST
>  go (SFVar n pt)  = return $ vars ! n
>  go (SInt i)      = mkInt i
>  go (SCon c vs)   = do
>    xs <- mapM go vs
>    mkApp (fst $ cfs c) xs
>  go (SEq v1 v2)   = do
>    x1 <- go v1
>    x2 <- go v2
>    mkEq x1 x2
>  go (SLt v1 v2)   = do
>    x1 <- go v1
>    x2 <- go v2
>    mkLt x1 x2
>  go (SAdd v1 v2)  = do
>    x1 <- go v1
>    x2 <- go v2
>    mkAdd [x1, x2]
>  go (SMul v1 v2)  = do
>    x1 <- go v1
>    x2 <- go v2
>    mkMul [x1, x2]
>  go (SApp v1 v2)  = do
>    x1 <- symFunZ3 env v1
>    x2 <- go v2
>    mkApp x1 [x2] -- This will be difficult to implement for partial functions
>  go (SFun f _)    = error "symValueZ3 of SFun"

> symFunZ3 :: Z3Env -> SymValue -> Z3 FuncDecl
> symFunZ3 Z3Env{} sv = error "symFunZ3 not implemented yet"

