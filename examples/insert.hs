
insert x []                  = [x]
insert x (a:as)  | x > a     = a : insert x as
                 | otherwise = x:a:as

ordered [] = True
ordered [x] = True
ordered (x:y:zs) = x <= y && ordered (y:zs)

prop_insertSet c s =
   ordered s ==> ordered (insert (c :: Char) s)

1.

c = C; x = []

ordered [] ==> ordered (insert c [])

2.

c = C; x = [X]

ordered [X] ==> ordered (insert C [X])

ordered (case C > X of True -> X : [C]; False -> C:[X])

2.1

C > X

ordered (X:[C]) 
=
(X <= C) && ordered [C]
=
...

2.2

not (C > X)

ordered (C:[X])
=
(C <= X) && ordered [X]
=
...

3.
c = C; x = [X,Y]

ordered [X,Y] ==> ordered (insert C [X,Y])
 
ordered (case C > X of True -> X : insert C [Y]; False -> C:[X,Y])

3.1

C > X

ordered (X : insert C [Y])
=
ordered (X : (case C > Y of True -> Y : [C]; False -> C:[Y]))
=
3.1.1

C > Y

ordered [X,Y,C]
= 
X<=Y && Y<=C

3.1.2

not (C >Y)

ordered [X,C,Y]
= 
X<=C && C<=Y

3.2

not (C > X) 

ordered [C,X,Y]






 


