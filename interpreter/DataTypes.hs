{-# LANGUAGE RecursiveDo #-}

module DataTypes where
import Control.Monad
import Control.Monad.Fix
import Control.Monad.State.Lazy

import Data.Array(array, (!))


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




-- | Constructor Identifiers
type ConID = Int

-- | Data Type Identifiers
type DataID = Int

idBool  = 0
idInt   = 1

idFalse = 0
idTrue  = 1

defConSupply :: [ConID]
defConSupply = [2..]

defDataSupply :: [DataID]
defDataSupply = [2..]


idOf :: DataType -> DataID
idOf (DataType{dataId = did}) = did
idOf DataBool                 = idBool
idOf DataInt                  = idInt
idOf (DataFun _ _)              = error "idOf DataFun"


-- Globally available types, with special interpreter support
tInt   = DataInt
tBool  = DataBool

cFalse = Constructor {conId = idFalse, conName = "False", conParams =  [], conType = tBool}
cTrue  = Constructor {conId = idTrue,  conName = "True",  conParams =  [], conType = tBool}

isIntType DataInt = True
isIntType _       = False

isBoolType DataBool = True
isBoolType _        = False

litBool b = if b then cTrue else cFalse
litInt    = IntegerLit

fromBool :: Constructor -> Bool
fromBool Constructor{conId = cid} | cid == idFalse = False
                                  | cid == idTrue  = True
fromBool _                                         = error "fromBool: not a Boolean"

-- -- | Type constructors
-- data TyCon = TyCon {tyConId :: ID, [DataType] -> DataType}

-- | TODO: String names.
data DataType = DataType {dataId :: DataID, dataCons :: [Constructor]} -- , tyVars :: [DataType]
              | DataInt
              | DataBool
              | DataFun [DataType] DataType
  deriving Show
instance Eq DataType where
  DataFun xs q == b = case b of
    DataFun ys r -> xs == ys && q == r
    _            -> False
  _          == DataFun _ _ = False
  a == b = idOf a == idOf b -- Currently doesn't work for functions.


(*->) :: DataType -> DataType -> DataType
x *-> DataFun xs r = DataFun (x:xs) r
x *-> y            = DataFun [x] y

data Constructor = Constructor {conId :: ConID, conName :: String, conParams :: [DataType], conType :: DataType}
                 | IntegerLit Integer
instance Show Constructor where
  show c@Constructor{conParams = cps, conId = cid} = show $ (cid,map dataId cps)
  show (IntegerLit n)                              = "litInt " ++ show n
instance Eq Constructor where
  Constructor{conId = a} == Constructor{conId = b} = a == b
  IntegerLit n           == IntegerLit m           = n == m


data S = S {dataSupply :: [DataID], conSupply :: [ConID], dataTypes :: [DataType]}
defS = S{dataSupply = defDataSupply, conSupply = defConSupply, dataTypes = []}

type DataTypesM = State S


newDataID :: DataTypesM DataID 
newDataID = state $ \s -> case dataSupply s of
  [] -> error "NewName: data names exhausted!"
  (x:xs) -> (x, s{dataSupply = xs})

newConID :: DataTypesM DataID 
newConID = state $ \s -> case conSupply s of
  [] -> error "NewName: constructor names exhausted!"
  (x:xs) -> (x, s{conSupply = xs})
  
  
regType :: DataType -> DataTypesM ()
regType dt = modify (\s -> s{dataTypes = dt : dataTypes s})

newData :: [(String,[DataType])] -> DataTypesM (DataType,[Constructor])
newData cs = do
  dtName  <- newDataID
  csNames <- sequence (map (const newConID) cs)
  
  let cons = zipWith (\cid (s,dts) -> Constructor{conId = cid, conName = s, conParams = dts, conType = dt}) csNames cs
      dt = DataType dtName cons
  regType dt
  return (dt, cons)


-- newTypeCon :: ([DataType] -> [(String,[DataType])]) -> DataTypesM TyCon
-- newTypeCon csf = do
  


runNames :: DataTypesM a -> (a, [DataType])
runNames m = fmap dataTypes $ runState m defS

conArity :: Constructor -> Int
conArity = length . conParams

-- This can be improved
showConName :: Constructor -> String
showConName Constructor{conName = cname, conId = cid} = cname -- ++ "_" ++ show cid -- If we want to be sure names are unique
showConName (IntegerLit n) = show n


-- | For making efficient mappings from constructors to values
type ConMap a = Constructor -> a

mkConMapM :: Monad m => (Constructor -> m a) -> [DataType] -> m (ConMap a)
mkConMapM f ds = do
  mcons <- mapM (\c -> f c >>= \x -> return (conId c, x)) cons
  let 
  return $ ((mkConArr mcons !) . conId)
  where
    cons = cFalse : cTrue : concatMap dataCons ds
    mkConArr = array (0,maximum (map conId cons))
    
  




