> {-# LANGUAGE RecursiveDo #-}

> module TestModule where
> import MiniFun2
> import DataTypes
> import Z3Backend

"Export list"

> ((fact,pr2,prop_map_fusion),types1) = runNames module1
> module1 = do

Prelude, where types are defined

>   rec (tList, [cons, nill]) <- newData [("(:)",[tBool,tList]),("[]",[])]

"Meta-programs"

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
>     t1    = EApp sumList (toIntList [1..100])
>     p3 = ELam (\e -> 
>       cases (var e) [
>         (cTrue, \_ -> EInt 0),
>         (cFalse, \_ -> EInt 1)
>         ]) undefined
>     prog3 = undefined

>     prop_p3 = ELam (\e -> EEq (EApp p3 (var e)) (EApp p3 (var e))) undefined -- does not work well!

>     isPositive = nLam (\n -> ELt (EInt 0) (var n))

>     p1 = nLam (\n -> eIf (var n *< 10) (-1) 1)
>
>     p2 = nLam (\n -> eIf (var n *< 5) (-1) 1)
>
>     prop_p1_p2 = nLam (\n -> EEq (EApp p1 (var n)) (EApp p2 (var n))) 

>     prop_fact = nLam (\n -> EApp isPositive (EApp fact (var n))) 



>     fact = ELet (\fact -> nLam (\n ->
>       eIf (var n *< 1)
>           1
>           (var n * (var fact *$ (var n - 1))))) var


>     sumList = ELet (\sumList -> tList *\ (\l -> 
>       cases (var l) [
>         (nill, \_ -> 0),
>         (cons, \(x:xs:_) -> var x + (var sumList *$ var xs))
>       ])) var

These functions have not yet been rewritten to the new format.

>     prop_map_fusion = ELam (\f -> ELam (\g -> ELam (\xs -> 
>       EEq (EApp (EApp mapList (var f)) (EApp (EApp mapList (var g)) (var xs)))
>           (EApp (EApp mapList (ELam (\x -> EApp (var f) (EApp (var g) (var x))) undefined)) (var xs))) (error "ops!")) (error "ops!")) (error "ops!")

>     mapList = ELet (\mapList -> ELam (\f -> ELam (\l -> 
>       cases (var l) [
>         (nill, \_ -> ECon nill []),
>         (cons, \(x:xs:_) -> ECon cons [EApp (var f) (var x), EApp (EApp (var mapList) (var f)) (var xs)])
>       ]) (error "We have no suitable type yet:)")) (error "We have no suitable type yet:)")) var

Export list is duplicated here.

>   return (fact,prop_fact,prop_map_fusion)


> testFact = eval (EApp fact (EInt 10))
