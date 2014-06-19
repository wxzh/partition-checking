> {-# LANGUAGE RecursiveDo #-}

> module TestModule where
> import MiniFun2
> import DataTypes
> import Z3Backend

"Export list"


> module1 = do

Prelude, where types are defined

>   rec (tList, [cons, nil]) <- newData [("(:)",[tInt,tList])
>                                        ,("[]",[])]
>   (tMayBool, [nothing, just]) <- newData [("Nothing",[])
>                                          ,("Just",[tBool])]
>   (tOrdering, [lt,eq,gt]) <- newData [("LT",[])
>                                      ,("EQ",[])
>                                      ,("GT",[])]
> 
>   -- (tTriple, [cTriple,cNoTriple]) <- newData [("Triple",[tList,tInt,tBool,tInt]), ("NoTriple",[])]
>   -- tEitherLN <- newData [("Left", [tInt]),("",[tInt])]

"Meta-programs"

>   let listLam f = tList *\ f -- Lambdas with [Int] parameters
>   let 
>     toList :: (a -> PExp b) -> [a] -> PExp b
>     toList f []      = ECon nil []
>     toList f (x:xs)  = ECon cons [f x, toList f xs]

>     toIntList = toList EInt

Core functions

>   let
>     eIf e1 e2 e3 = cases e1 [(cTrue,\_ -> e2),(cFalse,\_ -> e3)]

>     eTrue  = ECon cTrue []
>     eFalse = ECon cFalse []
>     eNil  = ECon nil []
>     eCons x xs = ECon cons [x,xs]
>     eLT = ECon lt []
>     eEQ = ECon eq []
>     eGT = ECon gt []
>
>
>     implies = bLam $ \p -> bLam $ \q -> eIf p q eTrue
>     -- a *==> b = implies *$ a *$ b
>     p *==> q = eIf p q eTrue
>
>     p *?=> q = eIf p (ECon just [q]) (ECon nothing [])
>     enot a = eIf a eFalse eTrue


Other functions

>   let 
>     isCons = listLam $ \l -> cases l
>                [cons *-> \[x,xs] -> cases l
>                  [nil *-> \[]     -> eTrue -- Unreachable
>                  ,cons *-> \[y,ys] -> eIf (x *== y)
>                                           eTrue
>                                           eFalse  -- (Should be) Unreachable
>                  ]
>                ,nil *-> \_        -> cases l 
>                  [cons *-> \[x,xs] -> eTrue -- Unreachable
>                  ,nil *-> \[]     -> eFalse
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
>         (nil, \_ -> 0),
>         (cons, \(x:xs:_) -> x + (sumList *$ xs))
>       ])) id

These functions have not yet been rewritten to the new format.

>     funType = tInt ~> tInt
>     prop_map_fusion =  funType *\ \f -> funType *\ \g -> listLam $ \xs -> constraint $
>           (mapList *$ f *$ (mapList *$ g *$ xs))
>           *==
>           (mapList *$ (listLam (\x -> f *$ (g *$ x))) *$ xs)

>     prop_map_fusion' =  funType *\ \f -> funType *\ \g -> listLam $ \xs -> constraint $ listEq *$
>           (mapList *$ f *$ (mapList *$ g *$ xs)) *$
>           (mapList *$ (listLam (\x -> f *$ (g *$ x))) *$ xs)

>     mapList = function $ \mapList -> funType *\ \f -> listLam $ \l -> 
>       cases l [
>         nil *-> \_        -> eNil,
>         cons *-> \(x:xs:_) -> eCons (f *$ x) (mapList *$ f *$ xs)
>       ]

>     -- less clever list comparison (uses symbolic equality for elements only)
>     listEq = function $ \listEq -> listLam $ \xs -> listLam $ \ys -> cases xs [
>       nil  *-> \_         -> isNil *$ ys,
>       cons *-> \[x,xs']   -> cases ys [
>         nil  *-> \_          -> eFalse,
>         cons *-> \[y,ys']    -> (x *== y) *&& (listEq *$ xs' *$ ys')]]

>     e1 *&& e2 = eIf e1 e2 eFalse
>     e1 *|| e2 = eIf e1 eTrue e2
>     not e1 = eIf e1 eFalse eTrue

>     -- For turning a result into a constraint
>     constraint x = eIf x eTrue eFalse

> -- :: (Int -> Int -> Int) -> [Int] -> Int -> Int
>     foldList = function $ \foldList -> funType *\ \f -> listLam $ \l -> nLam $ \b -> 
>       cases l [
>         nil *-> \_        -> b,
>         cons *-> \(x:xs:_) -> f *$ x *$ (foldList *$ f *$ xs *$ b)
>       ]

>
>     fromTo = function $ \fromTo -> nLam $ \from -> nLam $ \to -> 
>       eIf (to *< from) eNil (eCons from (fromTo *$ (from+1) *$ to))
>
>
>     triangleType = function $ \triangleType -> nLam $ \a -> nLam $ \b -> nLam $ \c -> 
>       eIf (not (c *< a + b)) (EInt 0)
>           (eIf ((a *== b) *&& (b *== c)) (EInt 1) 
>                (eIf ((a *== b) *|| (b *== c)) (EInt 2) (EInt 3)))

>     -- This relies on injectivity (it pattern matches on the same value several times)
>     sorted = function $ \sorted -> listLam $ \l -> 
>       cases l 
>         [nil *-> \_        -> eTrue
>         ,cons *-> \[x,xs]   -> cases xs 
>           [nil *-> \_       -> eTrue
>           ,cons *-> \[y,xys] -> eIf (y *< x) eFalse (sorted *$ (eCons y xys))
>           ]
>         ]
>
>     prop_tri_rev = nLam $ \a ->nLam $ \b ->nLam $ \c ->(triangleType *$ a *$ b *$ c) *== (triangleType *$ c *$ b *$ a)
>
>     prop_fromToSorted = nLam $ \n -> nLam $ \m -> sorted *$ (fromTo *$ n *$ m)
>
>     insert = function $ \insert -> nLam $ \x -> listLam $ \xs -> 
>       cases xs 
>         [ nil *-> \_ -> eCons x eNil
>         , cons *-> \[x',xs'] -> eIf (x *< x') (eCons x xs) (eCons x' (insert *$ x *$ xs'))
>         ]
>
>     prop_insertSorted = listLam $ \xs -> nLam $ \x -> 
>       (sorted *$ xs) *?=> (sorted *$ (insert *$ x *$ xs))
>
>     isNil = listLam $ \l -> casesW l
>                 [nil *-> \_        -> eTrue
>                 ] eFalse

>     compareInt = function $ \compareInt -> nLam $ \x -> nLam $ \y -> 
>                eIf (x *< y) 
>                  eLT
>                  (eIf (y *< x)
>                    eGT
>                    eEQ)

>
>     ehead = listLam $ \xs -> cases xs 
>                 [cons *-> \[x,_]   -> x
>                 ]
>

>     eqInt = function $ \eqInt -> nLam $ \x -> nLam $ \y -> casesW (compareInt *$ x *$ y)
>                 [eq *-> \_ -> eTrue] eFalse

Export list is duplicated here.

>   return (eIf, eTrue, eFalse, fact,prop_p3,prop_map_fusion,prop_map_fusion',prop_tri_rev, 
>           isCons, fromTo, 
>           foldList, sorted, prop_fromToSorted, insert, prop_insertSorted, 
>           isNil, ehead, eqInt, (*==>), just)
> (        (eIf, eTrue, eFalse, fact,prop_p3,prop_map_fusion,prop_map_fusion',prop_tri_rev, 
>           isCons, fromTo, 
>           foldList, sorted, prop_fromToSorted, insert, prop_insertSorted, 
>           isNil, ehead, eqInt, (*==>), just)
>      ,types1) = runNames module1

> testFact = eval (EApp fact (EInt 10))


> runFact n = testZ3 (fact,types1) n

> evalIsCons = eval (isCons *$ (fromTo *$ 11 *$ 10))
> z3IsCons = testZ3 (isCons,types1)

> eFromTo    = fromTo *$ 10 *$ 13
> evalFromTo = eval eFromTo
> z3FromTo   = testZ3 (fromTo,types1)

> evalInsert = eval (insert *$ 15 *$ (insert *$ 12 *$ (eFromTo)))

> evalImplies = testZ3 (eIf eTrue eTrue eTrue, types1) 100

> z3Prop_FromTo = testZ3 (prop_fromToSorted,types1)

> z3Prop_Insert = testZ3T (prop_insertSorted, types1) (filterTarget just defaultTarget)

> z3IsNil = testZ3 (isNil, types1)

> z3Head  = testZ3 (ehead, types1) -- Detects pattern match failure

> z3EqInt = testZ3 (eqInt, types1)

> -- Map fusion with symbolic list equality.
> z3MapFusionS = testZ3 (prop_map_fusion,types1)

> -- Map fusion without symbolic list equality.
> z3MapFusion = testZ3 (prop_map_fusion',types1)

> z3Tri = testZ3 (prop_tri_rev, types1)
