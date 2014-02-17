{-# LANGUAGE RecursiveDo #-}

module DataTypes where
import Control.Monad
import Control.Monad.Fix
import Control.Monad.State.Lazy

{-
-- This is how I envision us writing programs, every self-contained module can export a number of programs (functions) and a list of data types. We can even get a kind of import of functions from another module by just binding its functions (and possibly data types as well). 
((p1,p2,p3),types1) = runNames module1
module1 = do
  
  -- Prelude, where types are defined
  (tBool, [false, true])    <- newData [[],[]]
  rec (tList, [cons, nill]) <- newData [[tBool,tList],[]]
  
  -- Programs, where the types are in scope
  let 
    prog1 = undefined
    prog2 = undefined
    prog3 = undefined
  return (prog1,prog2,prog3)
-}





type ID = Int
defSupply :: [ID]
defSupply = [4..]


idOf :: DataType -> ID
idOf (DataType{dataId = did}) = did
idOf DataInt                  = 0
idOf DataBool                 = 1

-- Globally available types, with special interpreter support
tInt = DataInt
tBool = DataBool
cFalse = Constructor 2 "False" []
cTrue = Constructor 3 "True" []

litBool b = if b then cTrue else cFalse
litInt    = IntegerLit

-- | TODO: Type constructors, function types. String names.
data DataType = DataType {dataId :: ID, dataCons :: [Constructor]} 
              | DataInt
              | DataBool
  deriving Show
instance Eq DataType where
  a == b = idOf a == idOf b

-- | TODO:(Optional) String names.
data Constructor = Constructor {conId :: ID, conName :: String, conParams :: [DataType]}
                 | IntegerLit Integer
instance Show Constructor where
  show c@Constructor{conParams = cps, conId = cid} = show $ (cid,map dataId cps)
  show (IntegerLit n)                              = "litInt " ++ show n
instance Eq Constructor where
  Constructor{conId = a} == Constructor{conId = b} = a == b
  IntegerLit n           == IntegerLit m           = n == m


data S = S {nameSupply :: [ID], dataTypes :: [DataType]}
defS = S{nameSupply = defSupply, dataTypes = []}

type FreshNames = State S


newName :: FreshNames ID 
newName = state $ \s -> case nameSupply s of
  [] -> error "NewName: names exhausted!"
  (x:xs) -> (x, s{nameSupply = xs})

regType :: DataType -> FreshNames ()
regType dt = modify (\s -> s{dataTypes = dt : dataTypes s})

newData :: [(String,[DataType])] -> FreshNames (DataType,[Constructor])
newData cs = do
  dtName  <- newName
  csNames <- sequence (map (const newName) cs)
  
  let cons = zipWith (uncurry . Constructor) csNames cs
      dt = DataType dtName cons
  regType dt
  return (dt, cons)

runNames :: FreshNames a -> (a, [DataType])
runNames m = fmap dataTypes $ runState m defS

conArity :: Constructor -> Int
conArity = length . conParams

-- This can be improved
showConName :: Constructor -> String
showConName Constructor{conName = cname, conId = cid} = cname -- ++ "_" ++ show cid -- If we want to be sure names are unique
showConName (IntegerLit n) = show n
