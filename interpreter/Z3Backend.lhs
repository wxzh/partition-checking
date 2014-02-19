> module Z3Backend where

> import Control.Monad (ap, liftM2, when)
> import Control.Monad.IO.Class (liftIO)
> import Data.IntMap (IntMap, (!))
> import qualified Data.IntMap as IM
> import Z3.Monad

> import MiniFun2
> import DataTypes

> testZ3 e n = evalZ3 $ do
>   intSort <- mkIntSort 
>   pathsZ3 intSort (fst $ exec $ seval e) "True" IM.empty n
> 


> pathsZ3 :: Sort -> ExecutionTree -> String -> IntMap AST -> Int -> Z3 ()
> pathsZ3 intSort _       s vars stop | stop <= 0  = return ()
> pathsZ3 intSort (Exp e) s vars stop              = liftIO $ putStrLn $ s ++ " ==> " ++ ppSymValue' e
> pathsZ3 intSort (NewSymVar n t e) s vars stop    = do
>  (v,ast) <- declareVar intSort (n,t)
>  pathsZ3 intSort e s (IM.insert v ast vars) stop
> pathsZ3 intSort (Fork dt e cs w) s vars stop     
>   | isBoolType dt  = do 
>         ast <- symValueZ3 vars e
>         let assertBoolCon :: (Constructor, ExecutionTree) -> Z3 ()
>             assertBoolCon (c,ex) 
>               | fromBool c = local (assertCnstr ast >> whenSat (re ex (s ++ " && "++ppSymValue' e) vars (stop - 1)))
>               | otherwise  = local (mkNot ast >>= assertCnstr >> whenSat (re ex (s ++ " && "++ppSymValue' e) vars (stop - 1)))
>         mapM_ assertBoolCon (map (\(c,f) -> (c, f [])) cs)
>   where
>     re = pathsZ3 intSort
>


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

> declareVar :: Sort -> (Int, DataType) -> Z3 (Int, AST)
> declareVar intSort (n, t) | isIntType t = do
>   x <- mkIntSymbol n
>   c <- mkConst x intSort
>   return (n, c)

> symValueZ3 :: IntMap AST -> SymValue -> Z3 AST
> symValueZ3 vars sv = go sv where
>  go :: SymValue -> Z3 AST
>  go (SFVar n pt) = return $ vars ! n
>  go (SInt i)      = mkInt i
> --symValueZ3 vars (SBool True)  = "true"
> --symValueZ3 vars (SBool False) = "false"
> --symValueZ3 (SEq v1 v2)   = "(= " ++ symValueZ3 v1 ++ " " ++ symValueZ3 v2 ++ ")"
> --symValueZ3 (SAdd v1 v2)  = "(+ " ++ symValueZ3 v1 ++ " " ++ symValueZ3 v2 ++ ")"
> --symValueZ3 (SMul v1 v2)  = "(* " ++ symValueZ3 v1 ++ " " ++ symValueZ3 v2 ++ ")"
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
> --symValueZ3 vars (SApp v1 v2)  = "("   ++ symValueZ3 v1 ++ " " ++ symValueZ3 v2 ++ ")"
>  go (SFun f _)    = error "symValueZ3 of SFun"


