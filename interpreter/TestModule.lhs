> {-# LANGUAGE RecursiveDo #-}

> module TestModule where
> import MiniFun2
> import DataTypes
> import Z3Backend

"Export list"


> module1 = do

Prelude, where types are defined

>   rec (tList, [cons, nill]) <- newData [("(:)",[tInt,tList]),("[]",[])]
>   -- (tTriple, [cTriple,cNoTriple]) <- newData [("Triple",[tList,tInt,tBool,tInt]), ("NoTriple",[])]
>   -- tEitherLN <- newData [("Left", [tInt]),("",[tInt])]

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

>     eTrue  = ECon cTrue []
>     eFalse = ECon cFalse []
>     eNill  = ECon nill []
>     eCons x xs = ECon cons [x,xs]
>
>
>     implies = bLam $ \p -> bLam $ \q -> eIf p q eTrue
>     -- a *==> b = implies *$ a *$ b
>     p *==> q = eIf p q eTrue
>
>     enot a = eIf a eFalse eTrue


Other functions

>   let 
>     isCons = listLam $ \l -> cases l
>                [cons *-> \[x,xs] -> cases l
>                  [nill *-> \[]     -> eTrue -- Unreachable
>                  ,cons *-> \[y,ys] -> eIf (x *== y)
>                                           eTrue
>                                           eFalse  -- (Should be) Unreachable
>                  ]
>                ,nill *-> \_        -> cases l 
>                  [cons *-> \[x,xs] -> eTrue -- Unreachable
>                  ,nill *-> \[]     -> eFalse
>                  ]
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

>     funType = tInt ~> tInt
>     prop_map_fusion =  funType *\ \f -> funType *\ \g -> listLam $ \xs -> 
>           (mapList *$ f *$ (mapList *$ g *$ xs))
>           *==
>           (mapList *$ (listLam (\x -> f *$ (g *$ x))) *$ xs)

>     mapList = function $ \mapList -> funType *\ \f -> listLam $ \l -> 
>       cases l [
>         nill *-> \_        -> eNill,
>         cons *-> \(x:xs:_) -> eCons (f *$ x) (mapList *$ f *$ xs)
>       ]

> -- :: (Int -> Int -> Int) -> [Int] -> Int -> Int
>     foldList = function $ \foldList -> funType *\ \f -> listLam $ \l -> nLam $ \b -> 
>       cases l [
>         nill *-> \_        -> b,
>         cons *-> \(x:xs:_) -> f *$ x *$ (foldList *$ f *$ xs *$ b)
>       ]

>
>     fromTo = function $ \fromTo -> nLam $ \from -> nLam $ \to -> 
>       eIf (to *< from) eNill (eCons from (fromTo *$ (from+1) *$ to))
>
>
>     -- This relies on injectivity (it pattern matches on the same value several times)
>     sorted = function $ \sorted -> listLam $ \l -> 
>       cases l 
>         [nill *-> \_        -> eTrue
>         ,cons *-> \[x,xs]   -> cases xs 
>           [nill *-> \_       -> eTrue
>           ,cons *-> \[y,xys] -> eIf (y *< x) eFalse (sorted *$ (eCons y xys))
>           ]
>         ]
>
>
>     prop_fromToSorted = nLam $ \n -> nLam $ \m -> sorted *$ (fromTo *$ n *$ m)
>
>     insert = function $ \insert -> nLam $ \x -> listLam $ \xs -> 
>       cases xs 
>         [ nill *-> \_ -> eCons x eNill
>         , cons *-> \[x',xs'] -> eIf (x *< x') (eCons x xs) (eCons x' (insert *$ x *$ xs'))
>         ]
>
>     prop_insertSorted = listLam $ \xs -> nLam $ \x -> 
>       (sorted *$ xs) *==> (sorted *$ (insert *$ x *$ xs))
>

Export list is duplicated here.

>   return (eIf, eTrue, eFalse, fact,prop_p3,prop_map_fusion, isCons, fromTo, foldList, sorted, prop_fromToSorted, insert, prop_insertSorted, (*==>))
> (        (eIf, eTrue, eFalse, fact,prop_p3,prop_map_fusion, isCons, fromTo, foldList, sorted, prop_fromToSorted, insert, prop_insertSorted, (*==>))
>      ,types1) = runNames module1

> testFact = eval (EApp fact (EInt 10))


> runFact n = testZ3 (fact,types1) n

> evalIsCons = eval (isCons *$ (fromTo *$ 11 *$ 10))
> z3IsCons = testZ3 (isCons,types1)

> z3_2 = testZ3 (prop_map_fusion,types1) -- Not working yet

> eFromTo    = fromTo *$ 10 *$ 13
> evalFromTo = eval eFromTo
> z3FromTo   = testZ3 (fromTo,types1)

> evalInsert = eval (insert *$ 15 *$ (insert *$ 12 *$ (eFromTo)))

> evalImplies = testZ3 (eIf eTrue eTrue eTrue, types1) 100

> z3Prop_FromTo = testZ3 (prop_fromToSorted,types1)

> z3Prop_Insert = testZ3 (prop_insertSorted, types1)

