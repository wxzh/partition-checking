> module Z3Backend where

> import Control.Monad (ap, liftM2)
> import Control.Monad.IO.Class (liftIO)
> import Data.IntMap (IntMap, (!))
> import qualified Data.IntMap as IM
> import Z3.Monad

> import MiniFun

> pathsZ3 :: Sort -> ExecutionTree -> String -> IntMap AST -> Int -> Z3 ()
> pathsZ3 intSort _       s vars 0    = return ()
> pathsZ3 intSort (Exp e) s vars stop = liftIO $ putStrLn $ s ++ " ==> " ++ ppFPNSymValue e
> pathsZ3 intSort (Fork e1 e2 e3) s vars stop = do
>  push
>  let v1 = freeSVars e1
>      undeclared = v1 `IM.difference` vars
>  newdecls <- mapM (declareVar intSort) $ IM.assocs undeclared
>  let vars'      = vars `IM.union` IM.fromList newdecls
>  --    s' = s ++ "\n" ++ newdecls
>  --pathsZ3 e2 (assert e1)    vars' (stop - 1)
>  --pathsZ3 e3 (assertNeg e1) vars' (stop - 1)
>  pop 1

> declareVar :: Sort -> (Int, PType) -> Z3 (Int, AST)
> declareVar intSort (n, TAtom TInt) = do
>   x <- mkIntSymbol n
>   c <- mkConst x intSort
>   return (n, c)

> symValueZ3 :: IntMap AST -> SymValue -> Z3 AST
> symValueZ3 vars (SFVar n pt)  = return $ vars ! n
> symValueZ3 vars (SInt i)      = mkInt i
> --symValueZ3 vars (SBool True)  = "true"
> --symValueZ3 vars (SBool False) = "false"
> --symValueZ3 (SEq v1 v2)   = "(= " ++ symValueZ3 v1 ++ " " ++ symValueZ3 v2 ++ ")"
> --symValueZ3 (SAdd v1 v2)  = "(+ " ++ symValueZ3 v1 ++ " " ++ symValueZ3 v2 ++ ")"
> --symValueZ3 (SMul v1 v2)  = "(* " ++ symValueZ3 v1 ++ " " ++ symValueZ3 v2 ++ ")"
> symValueZ3 vars (SLt v1 v2)   = liftM2 mkLt (symValueZ3 v1) (symValueZ3 v2)
> --symValueZ3 vars (SApp v1 v2)  = "("   ++ symValueZ3 v1 ++ " " ++ symValueZ3 v2 ++ ")"
> symValueZ3 vars (SFun f _)    = error "symValueZ3 of SFun"


