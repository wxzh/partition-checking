> {-# LANGUAGE RecursiveDo #-}

> module TestModule where
> import MiniFun2
> import DataTypes
> import Z3Backend

"Export list"

> ((fact,prop_p3,prop_map_fusion, isCons),types1) = runNames module1
> module1 = do

Prelude, where types are defined

>   rec (tList, [cons, nill]) <- newData [("(:)",[tInt,tList]),("[]",[])]

"Meta-programs"

>   let listLam f = tList *\ f -- Lambdas with [Int] parameters
>   let 
>     toList :: (a -> PExp b c) -> [a] -> PExp b c
>     toList f []      = ECon nill []
>     toList f (x:xs)  = ECon cons [f x, toList f xs]

>     toIntList = toList EInt

Core functions

>   let
>     eIf e1 e2 e3 = cases e1 [(cTrue,\_ -> e2),(cFalse,\_ -> e3)]

Other functions

>   let 
>     isCons = listLam $ \l -> cases l [
>                (cons, \(x:xs:_) -> ECon cTrue []),
>                (nill, \_     -> cases l [
>                  (cons, \(x:xs:_) -> ECon cTrue []),
>                  (nill, \_     -> ECon cFalse [])
>                  ])
>                ]
> 
>     t1    = EApp sumList (toIntList [1..100])
>     p3 = bLam (\e -> 
>       cases e [
>         (cTrue, \_ -> EInt 0),
>         (cFalse, \_ -> EInt 1)
>         ])
>     prop_p3 = bLam (\e -> EApp p3 e *== EApp p3 e)

>     isPositive = nLam (\n -> ELt (EInt 0) n)

>     p1 = nLam (\n -> eIf (n *< 10) (-1) 1)
>     p2 = nLam (\n -> eIf (n *< 5) (-1) 1)
>
>     prop_p1_p2 = nLam (\n -> (EApp p1 n *== p2 *$ n)) 

>     prop_fact = nLam (\n -> isPositive *$ (fact *$ n)) 
>
>     fact = lets (\fact -> nLam (\n ->
>       eIf (n *< 1)
>           1
>           (n * (fact *$ (n - 1))))) id


>     sumList = lets (\sumList -> tList *\ (\l -> 
>       cases l [
>         (nill, \_ -> 0),
>         (cons, \(x:xs:_) -> x + (sumList *$ xs))
>       ])) id

These functions have not yet been rewritten to the new format.

>     funType = tInt *-> tInt
>     prop_map_fusion =  funType *\ \f -> funType *\ \g -> listLam $ \xs -> 
>           (mapList *$ f *$ (mapList *$ g *$ xs))
>           *==
>           (mapList *$ (listLam (\x -> f *$ (g *$ x))) *$ xs)

>     mapList = lets (\mapList -> funType *\ \f -> listLam $ \l -> 
>       cases l [
>         (nill, \_ -> ECon nill []),
>         (cons, \(x:xs:_) -> ECon cons [EApp f x, EApp (mapList *$ f) xs])
>       ]) id

Export list is duplicated here.

>   return (fact,prop_p3,prop_map_fusion, isCons)


> testFact = eval (EApp fact (EInt 10))


> runFact n = testZ3 (fact,types1) n

> z3_1 = testZ3 (isCons,types1)

> z3_2 = testZ3 (prop_map_fusion,types1) -- Not working yet