import Mock
import MockPrelude

import Unique (Uniquable(..))

genBool n = do
  s <- initSupply
  let ids = map unique (nextSupplies n s)
  return $ foldr (\(x,y) acc -> Choice_C_Bool y (ChoiceID x) C_True acc)
                 C_True
                 (zip ids [1..])
boolsSmall = do
  s <- initSupply
  let [id1,id2] = map unique (nextSupplies 2 s)
  return $ Choice_C_Bool 1 (ChoiceID id1) C_True (Choice_C_Bool 2 (ChoiceID id2) undefined C_True)

runMock' val = dfsStrategy (runMock val)

runList val = vsToList (dfsStrategy (runMock val))

runValues :: NormalForm a => a -> C_Values a
runValues val = C_Values (vsToList (dfsStrategy (runMock val)))

fold'    = foldValues d_OP_amp_amp C_True . runValues

isEmpty' :: NormalForm a => a -> Bool
isEmpty' = isEmpty . runValues

foldValues :: (NormalForm a, NormalForm b) => (a -> b -> b) -> b -> C_Values a -> b
foldValues f z (C_Values cList) = d_C_foldr f z cList

foldSequence :: (NormalForm a, NormalForm b) => (a -> b -> b) -> b -> C_ValueSequence a -> b
foldSequence f z (Values cList) = d_C_foldr f z cList

isEmpty :: C_Values a -> Bool
isEmpty (C_Values OP_List) = True
isEmpty (C_Values _)       = False

isEmptyList :: OP_List a -> Bool
isEmptyList OP_List = True
isEmptyList _       = False

isEmptySequence :: C_ValueSequence a -> Bool
isEmptySequence EmptyVS = True
isEmptySequence _       = False

data C_Values a = C_Values (OP_List a)
  deriving Show

main :: IO ()
main = genBool 100000 >>= print . fold'
