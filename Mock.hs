{-# LANGUAGE RankNTypes, FlexibleInstances, ExistentialQuantification #-}

module Mock ( MonadSearch(..), MonadPlus(..), NormalForm(..), NonDet(..)
            , Cover, ID(..), ConstStore, emptyCs
            , initSupply, IDSupply(..), nextSupplies
            , nfChoice, gnfChoice, liftM, internalError, runMock, trace ) where

import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef)
import Control.Monad
import Control.Monad.State.Lazy as Lazy
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.Map as Map
import qualified Debug.Trace as DT
import qualified Unique as GHC (Unique, getKey)
import UniqSupply
  (UniqSupply, mkSplitUniqSupply, splitUniqSupply, uniqFromSupply)
import GHC.IO  (unsafeDupableInterleaveIO)

debug = False

trace str expr = if debug then DT.trace ("\n\n**\ndebug: " ++ str ++ "\n**\n") expr else expr

runMock :: (MonadSearch m, NormalForm a) => Bool -> a -> m a
runMock sharing expr = encapsulatedSearch sharing expr 1 emptyCs

-- ---------------------------------------------------------------------------
-- Type classes
-- ---------------------------------------------------------------------------

class (NonDet a, Show a) => NormalForm a where
  -- |Apply a continuation to the normal form
  ($!!) :: NonDet b => (a -> Cover -> ConstStore -> b) -> a -> Cover -> ConstStore -> b
  -- |Apply a continuation to the ground normal form
  ($##) :: NonDet b => (a -> Cover -> ConstStore -> b) -> a -> Cover -> ConstStore -> b
  -- show of constructor
  showCons :: a -> String
  showCons = show
  searchNF :: (forall b . NormalForm b => (b -> c) -> b -> c) -> (a -> c) -> a -> c

class NonDet a where
  -- |Construct a binary choice, used by the (?) operator
  choiceCons :: Cover -> ID -> a -> a -> a
  -- /Note:/ This functionality was introduced to render the conversion from
  -- and to the 'Try' structure obsolete. Nonetheless, the performance impact
  -- still is to be analyzed.
  match      :: (Cover -> ID -> a -> a -> b)     -- ^ Binary Choice
             -- -> (Cover -> ID -> [a] -> b)        -- ^ n-ary Choice for narrowed variable
             -- -> (Cover -> ID -> [a] -> b)        -- ^ n-ary Choice for free variable
             -- -> (Cover -> FailInfo -> b)         -- ^ Failure
             -- -> (Cover -> Constraints -> a -> b) -- ^ Constrained value
             -> (a -> b)                         -- ^ Head Normal Form
             -> a                                -- ^ value to apply the functions to
             -> b
  
-- |Auxiliary function to apply the continuation to the normal forms of the
-- two alternatives of a binary choice.
nfChoice :: (NormalForm a, NonDet b) =>
            (a -> Cover -> ConstStore -> b) -> Cover -> ID -> a -> a -> Cover -> ConstStore -> b
nfChoice cont d i x1 x2 cd cs = case i of
  ChoiceID      _ -> choiceCons d i ((cont $!! x1) cd cs) ((cont $!! x2) cd cs)
  _               -> internalError "Basics.nfChoice: no ChoiceID"

-- |Auxiliary function to apply the continuation to the ground normal forms of
-- the two alternatives of a binary choice.
gnfChoice :: (NormalForm a, NonDet b)
          => (a -> Cover -> ConstStore -> b) -> Cover -> ID -> a -> a -> Cover -> ConstStore -> b
gnfChoice cont d i x1 x2 cd cs = case i of
  ChoiceID _ -> choiceCons d i ((cont $## x1) cd cs) ((cont $## x2) cd cs)
  _          -> internalError "Basics.gnfChoice: no ChoiceID"

-- ---------------------------------------------------------------------------
-- search monad
-- ---------------------------------------------------------------------------

class MonadPlus m => MonadSearch m where
  -- szero :: Cover -> FailInfo -> m a
  splus :: Cover -> ID -> m a -> m a -> m a
  -- ssum  :: Cover -> ID -> [m a] -> m a
  -- var   :: m a   -> [m a] -> m a
  -- svar  :: Cover -> ID-> [m a] -> m a
  -- constrainMSearch :: Cover -> Constraints -> m a -> m a

  -- szero _ _   = mzero
  splus _ _   = mplus
  -- ssum  _ _   = msum
  -- svar        = ssum
  -- var   _     = msum

instance MonadSearch m => MonadSearch (Lazy.StateT a m) where
  splus cd i mx my  = Lazy.StateT (\s -> splus cd i (Lazy.runStateT mx s) (Lazy.runStateT my s))
  -- ssum  cd i mxs    = Lazy.StateT (\s -> ssum cd i (map (flip Lazy.runStateT s) mxs))
  -- szero cd info     = Lazy.StateT (\_ -> szero cd info)
  -- svar  cd i mxs    = Lazy.StateT (\s -> svar cd i (map (flip Lazy.runStateT s) mxs))
  -- var   mx   mxs    = Lazy.StateT (\s -> var (Lazy.runStateT mx s) (map (flip Lazy.runStateT s) mxs))
  -- constrainMSearch cd cs mx = Lazy.StateT (\s -> constrainMSearch cd cs (Lazy.runStateT mx s))


-- ---------------------------------------------------------------------------
-- Encapsulated search
-- ---------------------------------------------------------------------------

 -- |Collect results of a non-deterministic computation in a monadic structure
encapsulatedSearch :: (MonadSearch m, NormalForm a) => Bool -> a -> Cover -> ConstStore -> m a
encapsulatedSearch sharing x cd store =
  trace "encapsulatedSearch" $ searchMSearch sharing cd $ ((\y _ _ -> y) $!! x) cd store


-- ---------------------------------------------------------------------------
-- Generic search using MonadPlus instances for the result
-- ---------------------------------------------------------------------------

newtype DecisionMap = DecisionMap { decisionMap :: Map.Map Integer Decision }
  deriving Show

emptyDecisionMap :: DecisionMap
emptyDecisionMap = DecisionMap Map.empty

onDecisionMap :: (Map.Map Integer Decision -> Map.Map Integer Decision)
              -> DecisionMap -> DecisionMap
onDecisionMap f (DecisionMap m) = DecisionMap (f m)

instance Monad m => Store (Lazy.StateT DecisionMap m) where
  getDecisionRaw u        = gets
                          $ Map.findWithDefault defaultDecision (mkInteger u)
                          . decisionMap
  setDecisionRaw u c
    | isDefaultDecision c = unsetDecisionRaw u
    | otherwise           = modify $ onDecisionMap $ Map.insert (mkInteger u) c
  unsetDecisionRaw u      = modify $ onDecisionMap $ Map.delete (mkInteger u)

searchMSearch :: (MonadSearch m, NormalForm a) => Bool -> Cover -> a -> m a
searchMSearch sharing cd x = Lazy.evalStateT (searchMSearch' sharing cd return x) emptyDecisionMap

searchMSearch' :: (NormalForm a, MonadSearch m, Store m) => Bool -> Cover -> (a -> m b) -> a -> m b
searchMSearch' sharing cd cont x = trace "searchM'" $ match mChoice mVal x
  where
  mVal v        = trace "mVal" $ searchNF (searchMSearch' sharing cd) cont v

  mChoice d i a b = (if sharing then lookupDecision i else return NoDecision) >>= follow
    where
    follow ChooseLeft  = trace "ChooseLeft" $ searchMSearch' sharing cd cont a
    follow ChooseRight = trace "ChooseRight" $ searchMSearch' sharing cd cont b
    follow NoDecision  = trace "No decision" $ decide i ChooseLeft a `plus` decide i ChooseRight b
    follow c           = internalError $ "Search.mChoice: Bad decision " ++ show c
    plus = if isCovered d then trace "splus" $ splus d i else trace "mplus" mplus

  decide i c y = (if sharing then setDecision i c else return ()) >> searchMSearch' sharing cd cont y
  isCovered d = d < cd

-- --------------------------------
-- Misc
-- --------------------------------

internalError :: String -> a
internalError = error . ("Internal error: " ++)

-- ---------------------------------------------------------------------------
-- Cover
-- ---------------------------------------------------------------------------

-- |Type used to store information about the covering depth of choices,
-- guards and failures
type Cover = Int

-- |Increase covering depth
incCover :: Cover -> Cover
incCover = (+ 1)

-- |Decrease covering depth
decCover :: Cover -> Cover
decCover = flip (-) 1

initCover :: Cover
initCover = 0

-- ---------------------------------------------------------------------------
-- Decision
-- ---------------------------------------------------------------------------

-- |Type to encode the decision made for a Choice(s) structure
data Decision
    -- |No decision has been made so far
  = NoDecision
    -- |The left value of an (?) is chosen
  | ChooseLeft
    -- |The right value of an (?) is chosen
  | ChooseRight
    -- |ChooseN consIdx argCnt is the choice for the constructor with the
    --  index consIdx which has argCnt arguments
  | ChooseN Int Int
    -- |a free or narrowed variable is bound to the free variable with the
    --  given id; the bindings of the IDs for the arguments have not been
    --  propagated yet
  | BindTo ID
    -- |A free or narrowed variable is bound to the variable with the given
    --  'ID'; the bindings for the n arguments have also been propagated
  | BoundTo ID Int

    deriving Show

instance Eq Decision where
  NoDecision  == NoDecision  = True
  ChooseLeft  == ChooseLeft  = True
  ChooseRight == ChooseRight = True
  ChooseN c _ == ChooseN d _ = c == d
  BindTo  _   == BindTo  _   = internalError "ID.Decision.(==): BindTo"
  BoundTo _ _ == BoundTo _ _ = internalError "ID.Decision.(==): BoundTo"
  _           == _           = False

-- |Default 'Decision'. The default 'Decision' is provided via a function to
-- break recursive dependencies.
defaultDecision :: Decision
defaultDecision = NoDecision

-- |Is the given 'Decision' the 'defaultDecision'?
isDefaultDecision :: Decision -> Bool
isDefaultDecision NoDecision = True
isDefaultDecision _          = False

-- ---------------------------------------------------------------------------
-- ID
-- ---------------------------------------------------------------------------

-- |Type to identify different Choice structures in a non-deterministic result
data ID
    -- |Identifier for a choice introduced by using of the (?) operator
  = ChoiceID Unique
    -- |Identifier for a choice for a free variable
  | FreeID [Int] IDSupply
    -- |Identifier for a choice for a narrowed variable (free before)
  | NarrowedID [Int] IDSupply
    deriving Eq

instance Show ID where
  show (ChoiceID          i) = "?" ++ showUnique i
  show (FreeID          _ i) = "_x" ++ show i
  show (NarrowedID      _ i) = "Narrowed_" ++ show i

-- |Retrieve the 'IDSupply' from an 'ID'
supply :: ID -> IDSupply
supply (ChoiceID          _) = internalError "ID.supply: ChoiceID"
supply (FreeID        _   s) = s
supply (NarrowedID    _   s) = s

-- |Construct an 'ID' for a free variable from an 'IDSupply'
freeID :: [Int] -> IDSupply -> ID
freeID = FreeID

-- |Retrieve the left child 'ID' from a free 'ID'
leftID :: ID -> ID
leftID  (FreeID      _ s) = freeID    [] (leftSupply s)
leftID  _               = internalError "ID.leftID: no FreeID"

-- |Retrieve the right child 'ID' from a free 'ID'
rightID :: ID -> ID
rightID (FreeID      _ s) = freeID [] (rightSupply s)
rightID  _              = internalError "ID.rightID: no FreeID"

getKey :: ID -> Integer
getKey = mkInteger . getUnique

getUnique :: ID -> Unique
getUnique (ChoiceID          u) = u
getUnique (FreeID          _ s) = unique s
getUnique (NarrowedID      _ s) = unique s

-- -- ---------------------------------------------------------------------------
-- -- Tracing
-- -- ---------------------------------------------------------------------------

-- traceLookup :: Show a => (ID -> IO a) -> ID -> IO a
-- traceLookup lookUp i = do
--   d <- lookUp i
--   trace $ "lookup " ++ show i ++ " -> " ++ show d
--   return d

-- traceDecision :: (ID -> Decision -> IO a) -> ID -> Decision -> IO a
-- traceDecision set i c = do
--   reset <- set i c
--   trace $ "set " ++ show i ++ " -> " ++ show c
--   return reset

-- ---------------------------------------------------------------------------
-- Store
-- ---------------------------------------------------------------------------

-- |Type class for a Decision 'Store'
class (Monad m) => Store m where
  -- |Get the stored 'Decision', defaulting to 'defaultDecision'
  getDecisionRaw    :: Unique -> m Decision
  -- |Set the 'Decision'
  setDecisionRaw    :: Unique -> Decision -> m ()
  -- |Unset the 'Decision'
  unsetDecisionRaw  :: Unique -> m ()

instance Store IO where
  getDecisionRaw   = getDecisionRawSupply
  setDecisionRaw   = setDecisionRawSupply
  unsetDecisionRaw = unsetDecisionRawSupply

-- ---------------------------------------------------------------------------
-- Looking up decisions
-- ---------------------------------------------------------------------------

-- |Lookup the 'Decision' an 'ID' ultimately is bound to
lookupDecision :: Store m => ID -> m Decision
lookupDecision i = fst `liftM` lookupDecisionID i

-- |Lookup the 'ID' an 'ID' ultimately is bound to
lookupID :: Store m => ID -> m ID
lookupID i = snd `liftM` lookupDecisionID i

-- |Lookup the 'Decision' and the 'ID' an 'ID' ultimately is bound to
lookupDecisionID :: Store m => ID -> m (Decision, ID)
lookupDecisionID i = getDecisionRaw (getUnique i) >>= follow
  where
    -- follow BindTo
    follow (BindTo j) = do
      retVal@(c, _lastId) <- lookupDecisionID j
      case c of
        NoDecision    -> return ()
        ChooseN _ num -> propagateBind i j num
        _             -> internalError $ "ID.lookupDecisionID: " ++ show c
      return retVal

    -- follow BoundTo
    follow (BoundTo j num) = do
      retVal@(c, _) <- lookupDecisionID j
      case c of
        NoDecision     -> return ()
        ChooseN _ num' -> checkPropagation i j num num'
        _              -> internalError $ "ID.lookupDecisionID: " ++ show c
      return retVal

    -- For all other choices, there are no chains at all
    follow c           = return (c, i)

-- ---------------------------------------------------------------------------
-- Setting decisions
-- ---------------------------------------------------------------------------

-- |Set the 'Decision' for the given 'ID'
setDecision :: Store m => ID -> Decision -> m ()
setDecision i c = setDecisionGetChange i c >> return ()

-- -- Set the given 'Decision' for the given 'ID' and return an action to recover
-- -- the former 'Decision'
-- setUnsetDecision :: Store m => ID -> Decision -> m (m ())
-- setUnsetDecision i c = do
--   mChange <- setDecisionGetChange i c
--   case mChange of
--     Nothing                       -> return (return ())
--     Just (oldDecision, changedId) -> return $ case c of
--       BindTo _ -> resetFreeVar changedId oldDecision
--       _        -> setDecisionRaw (getUnique changedId) oldDecision

-- |Set the 'Decision' for the given 'ID', eventually following a chain and
--  return the ultimately changed 'ID' and its former 'Decision'
setDecisionGetChange :: Store m => ID -> Decision -> m (Maybe (Decision, ID))
-- We do not bind an ID to itself to avoid cycles
setDecisionGetChange i (BindTo j) | supply i == supply j = return Nothing
setDecisionGetChange i c = getDecisionRaw (getUnique i) >>= unchain
  where
  -- BindTo: change the last variable in the chain and propagate the binding
  -- TODO: At the moment the propagation is necessary, but may be removed
  -- later (cf. tests/Unification.curry, goal25)
  unchain (BindTo k)    = do
    retVal <- setDecisionGetChange k c
    case c of
      ChooseN _ num -> propagateBind i k num
      _             -> return ()
    return retVal
  -- BoundTo: change the last variable in the chain
  -- If the new ChooseN has a different propagation number, the old propagation
  -- has to be reset first. Otherwise after a lookup leading to BoundTo
  -- new propagations would be ignored, cf. tests/FunctionPattern.curry, goal2
  unchain (BoundTo k num) = do
    retVal <- setDecisionGetChange k c
    case c of
      ChooseN _ num' -> checkPropagation i k num num'
      _              -> return ()
    return retVal
  unchain oldDecision     = case c of
    BindTo j -> do
      -- Avoid binding i to a variable which is transitively bound to i
      lastId <- lookupID j
      if getKey lastId == getKey i
        then return Nothing
        else setDecisionRaw (getUnique i) c >> return (Just (oldDecision, i))
    _     -> setDecisionRaw (getUnique i) c >> return (Just (oldDecision, i))

-- ---------------------------------------------------------------------------
-- Auxiliary functions
-- ---------------------------------------------------------------------------

checkPropagation :: Store m => ID -> ID -> Int -> Int -> m ()
checkPropagation i j oldNum newNum = when (oldNum /= newNum) $ do
  resetFreeVar i (BindTo j)
  propagateBind i j newNum

-- |Propagate a binding of 'ID' x to 'ID' y for the next cnt independent child
--  'ID's. x as well as y are both expected to be either a free or a narrowed
--  variable
propagateBind :: Store m => ID -> ID -> Int -> m ()
propagateBind x y cnt = do
  -- bind i to j
  setDecisionRaw (getUnique x) (BoundTo y cnt)
  -- propagate the binding to the children
  zipWithM_ (\a b -> setDecision a (BindTo b)) (nextNIDs x cnt) (nextNIDs y cnt)

-- |Reset a free variable to its former 'Decision' and reset its children if
--  the binding has already been propagated
resetFreeVar :: Store m => ID -> Decision -> m ()
resetFreeVar i oldDecision = reset oldDecision i
  where
  reset c j = getDecisionRaw (getUnique j) >>= propagate c j

  propagate c j (BindTo  _    ) = setDecisionRaw (getUnique j) c
  propagate c j (BoundTo _ num) = do
    setDecisionRaw (getUnique j) c
    mapM_ (reset NoDecision) $ nextNIDs j num
  propagate _ _ _ = internalError "ID.resetFreeVar.propagate: no binding"

-- Compute a list of the next n free 'ID's for a given 'ID'
nextNIDs :: ID -> Int -> [ID]
nextNIDs = nextNIDsFromSupply . supply

-- Compute a list of the next n free 'ID's for a given 'IDSupply' s
nextNIDsFromSupply :: IDSupply -> Int -> [ID]
nextNIDsFromSupply s n = map (freeID []) $ nextSupplies n s

-- |Compute the next n independent 'IDSupply's for a given 'IDSupply' s
nextSupplies :: Int -> IDSupply -> [IDSupply]
nextSupplies n s
  | n <  0    = internalError $ "ID.nextNSupplies: " ++ show n
  | n == 0    = []
  | n == 1    = [leftSupply s]
  | otherwise = nextNSupplies' n s
  where
  nextNSupplies' n' s'
    | n' == 1    = [s']
    | otherwise =  nextNSupplies' (n' - halfn) (leftSupply  s')
                ++ nextNSupplies' halfn        (rightSupply s')
    where halfn = n' `div` 2

-- ---------------------------------------------------------
-- IDSupply
-- ---------------------------------------------------------

type Unique = Integer

-- |References to 'Decision's are represented using 'Integer'
newtype IDSupply = IDSupply { unique :: Unique }

instance Eq IDSupply where
  s1 == s2 = unique s1 == unique s2

instance Show IDSupply where
  show = showUnique . unique

-- |Retrieve an 'Integer' representation of the unique identifier
mkInteger :: Unique -> Integer
mkInteger = id

showUnique :: Unique -> String
showUnique = show

-- |Initialize a new 'IDSupply'
initSupply :: IO IDSupply
initSupply = return (IDSupply 1)

leftSupply :: IDSupply -> IDSupply
leftSupply  (IDSupply i) = IDSupply (2 * i)

rightSupply :: IDSupply -> IDSupply
rightSupply (IDSupply i) = IDSupply (2 * i + 1)

-- |Internal store for 'Decision's
store :: IORef (Map.Map Unique Decision)
store = unsafePerformIO (newIORef Map.empty)
{-# NOINLINE store #-}

getDecisionRawSupply :: Unique -> IO Decision
getDecisionRawSupply u = Map.findWithDefault defaultDecision u
                   `liftM` readIORef store

setDecisionRawSupply :: Unique -> Decision -> IO ()
setDecisionRawSupply u c
  | isDefaultDecision c = modifyIORef store $ Map.delete u -- collect garbage
  | otherwise           = modifyIORef store $ Map.insert u c

unsetDecisionRawSupply :: Unique -> IO ()
unsetDecisionRawSupply = modifyIORef store . Map.delete

-- ---------------------------------------------------------------------------
-- Constraint Store
-- ---------------------------------------------------------------------------

type ConstStore = Map.Map Integer Value

data Value = forall a . V a

-- |Empty constraint store
emptyCs :: ConstStore
emptyCs = Map.empty
