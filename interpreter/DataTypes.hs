{-# LANGUAGE RecursiveDo #-}

import Control.Monad
import Control.Monad.Fix
import Control.Monad.State.Lazy


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






type ID = Int
defSupply :: [ID]
defSupply = [0..]

data DataType = DataType {dataId :: ID, dataCons :: [Constructor]} deriving Show

data Constructor = Constructor {conId :: ID,  conParams :: [DataType]}
instance Show Constructor where
  show Constructor {conParams = cps, conId = cid} = show $ (cid,map dataId cps)


data S = S {nameSupply :: [ID], dataTypes :: [DataType]}
defS = S{nameSupply = defSupply, dataTypes = []}

type FreshNames = State S


newName :: FreshNames ID 
newName = state $ \s -> case nameSupply s of
  [] -> error "NewName: names exhausted!"
  (x:xs) -> (x, s{nameSupply = xs})

regType :: DataType -> FreshNames ()
regType dt = modify (\s -> s{dataTypes = dt : dataTypes s})

newData :: [[DataType]] -> FreshNames (DataType,[Constructor])
newData cs = do
  dtName  <- newName
  csNames <- sequence (map (const newName) cs)
  
  let cons = zipWith Constructor csNames cs
      dt = DataType dtName cons
  regType dt
  return (dt, cons)

runNames :: FreshNames a -> (a, [DataType])
runNames m = fmap dataTypes $ runState m defS




