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
  return $ Choice_C_Bool 1
                         (ChoiceID id1)
                         C_True
                         (Choice_C_Bool 2 (ChoiceID id2) undefined C_True)

-- runList val = vsToList (dfsStrategy (runMockWSharing val))

runValues :: NormalForm a => Bool -> a -> C_Values a
runValues sharing val = C_Values (vsToList (dfsStrategy (runMock sharing val)))

fold' sharing = foldValues d_OP_amp_amp C_True . runValues sharing

isEmpty' :: NormalForm a => Bool -> a -> Bool
isEmpty' sharing = isEmpty . runValues sharing

foldValues :: (NormalForm a, NormalForm b)
           => (a -> b -> b)
           -> b
           -> C_Values a -> b
foldValues f z (C_Values cList) = d_C_foldr f z cList

foldSequence :: (NormalForm a, NormalForm b)
             => (a -> b -> b)
             -> b
             -> C_ValueSequence a
             -> b
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

sharingExample = do
  s <- initSupply
  let (id1:id2:ids) = map unique (nextSupplies 100002 s)
      x = Choice_C_Bool 2 (ChoiceID id2) C_False C_True
      list = foldr (\(x,y) acc -> Choice_C_Bool y (ChoiceID x) C_True acc)
                   x
                   (zip ids [3..])
  return (Choice_C_Bool 1 (ChoiceID id1) x list)

main :: IO ()
main = do
  arg <- getLine
  let sharing = read arg
  genBool 1000000 >>= print . fold' sharing
