{-# Language MagicHash #-}

module MockPrelude where

import GHC.Exts (Int (I#), Int#, (==#), (/=#), (<#), (>#), (<=#))
import Control.Monad (liftM, ap)
import Control.Applicative (Alternative(..))
import Mock

-- ---------------------------------------------------------------------------
-- C_Bool
-- ---------------------------------------------------------------------------

data C_Bool
     = C_False
     | C_True
     | Choice_C_Bool Cover ID C_Bool C_Bool
     -- | Choices_C_Bool Cover ID ([C_Bool])
     -- | Fail_C_Bool Cover FailInfo
     -- | Guard_C_Bool Cover Constraints C_Bool

instance Show C_Bool where
  showsPrec d (Choice_C_Bool cd i x y) = showString "Choice" . showString " "
                                       . showsPrec d x . showString " " . showsPrec d y
  showsPrec _ C_False = showString "False"
  showsPrec _ C_True = showString "True"

instance NonDet C_Bool where
  choiceCons = Choice_C_Bool
  match f _ (Choice_C_Bool cd i x y) = f cd i x y
  match _ f x = f x

instance NormalForm C_Bool where
  ($!!) cont C_False d cs = cont C_False d cs
  ($!!) cont C_True d cs = cont C_True d cs
  ($!!) cont (Choice_C_Bool cd i x y) d cs = nfChoice cont cd i x y cd cs
  ($##) cont C_False d cs = cont C_False d cs
  ($##) cont C_True d cs = cont C_True d cs
  ($##) cont (Choice_C_Bool cd i x y) d cs = gnfChoice cont cd i x y cd cs
  searchNF _ cont C_False = cont C_False
  searchNF _ cont C_True = cont C_True
  searchNF _ _ x = error ("Prelude.Bool.searchNF: no constructor: " ++ (show x))

d_OP_amp_amp :: C_Bool -> C_Bool -> C_Bool
d_OP_amp_amp x1 x2 = case x1 of
     C_True -> trace "C_True" x2
     C_False -> trace "C_False" C_False
     (Choice_C_Bool d i l r) -> trace "Choice_C_Bool" $ narrow d i (d_OP_amp_amp l x2) (d_OP_amp_amp r x2)

-- ---------------------------------------------------------
-- ValueSequence
-- ---------------------------------------------------------

data C_ValueSequence a
  = EmptyVS
  | Values (OP_List a)
  | Choice_VS Cover ID (C_ValueSequence a) (C_ValueSequence a)
  deriving Show

instance NonDet (C_ValueSequence a) where
  choiceCons  = Choice_VS
  match       = error "SearchTree: ValueSequence: match"

instance NormalForm a => NormalForm (C_ValueSequence a) where
 ($!!)    = error "SearchTree: ValueSequence: ($!!)"
 ($##)    = error "SearchTree: ValueSequence: searchNF"
 searchNF = error "SearchTree: ValueSequence: searchNF"

emptyVS :: C_ValueSequence a
emptyVS = EmptyVS

addVS :: a -> C_ValueSequence a -> C_ValueSequence a
addVS x vs = Values (OP_Cons x (getValues vs))

vsToList :: C_ValueSequence a -> (OP_List a)
vsToList (Values                       xs) = xs
vsToList (Choice_VS d i x y)
  = choiceCons d i (vsToList x)
                   (vsToList y)

(|++|) :: NormalForm a => C_ValueSequence a -> C_ValueSequence a -> C_ValueSequence a
EmptyVS             |++| vs = vs
Values     xs       |++| vs = Values (d_OP_plus_plus xs
                                                     (getValues vs)
                                                     (error "ExternalSearchTree: |++| - nesting depth used") emptyCs)
Choice_VS  cd i x y |++| vs = choiceCons  cd i  (x |++| vs) (y |++| vs)

getValues EmptyVS               = OP_List
getValues (Values           xs) = xs
getValues (Choice_VS  cd i x y) = choiceCons cd i (getValues x) (getValues y)

-- ---------------------------------------------------------
-- SearchTree
-- ---------------------------------------------------------

--- Depth-first search strategy.
dfsStrategy :: NormalForm a => C_SearchTree a -> C_ValueSequence a
dfsStrategy (C_Value x) = addVS x emptyVS
dfsStrategy (C_Or x y)  = dfsStrategy x |++| dfsStrategy y

data C_SearchTree t0
     = C_Value t0
     | C_Fail Int
     | C_Or (C_SearchTree t0) (C_SearchTree t0)
     | Choice_C_SearchTree Cover ID (C_SearchTree t0) (C_SearchTree t0)
  deriving Show

instance MonadSearch C_SearchTree where
  splus            = Choice_C_SearchTree

instance Functor C_SearchTree where
  fmap = liftM

instance Applicative C_SearchTree where
  pure = return
  (<*>) = ap
  
instance Monad C_SearchTree where
  return = C_Value

  C_Value   x >>= f = f x
  C_Or    x y >>= f = C_Or (x >>= f) (y >>= f)

  Choice_C_SearchTree  cd i x y >>= f
    = Choice_C_SearchTree  cd i  (x >>= f) (y >>= f)

instance Alternative C_SearchTree where
  empty = mzero
  (<|>) = mplus

instance MonadPlus C_SearchTree where
  mzero = C_Fail (-1)
  mplus = C_Or

instance NonDet (C_SearchTree t0) where
  choiceCons = Choice_C_SearchTree
  match f _ (Choice_C_SearchTree cd i x y) = f cd i x y
  match _ f x = f x


instance NormalForm t0 => NormalForm (C_SearchTree t0) where
  ($!!) cont (C_Value x1) d cs = (((\y1 d cs -> cont (C_Value y1) d cs) $!! x1) d) cs
  ($!!) cont (C_Or x1 x2) d cs = (((\y1 d cs -> (((\y2 d cs -> cont (C_Or y1 y2) d cs) $!! x2) d) cs) $!! x1) d) cs
  ($!!) cont (Choice_C_SearchTree cd i x y) d cs = nfChoice cont cd i x y cd cs
  ($##) cont (C_Value x1) d cs = (((\y1 d cs -> cont (C_Value y1) d cs) $## x1) d) cs
  ($##) cont (C_Or x1 x2) d cs = (((\y1 d cs -> (((\y2 d cs -> cont (C_Or y1 y2) d cs) $## x2) d) cs) $## x1) d) cs
  ($##) cont (Choice_C_SearchTree cd i x y) d cs = gnfChoice cont cd i x y cd cs
  showCons (C_Value _) = "SearchTree.Value _"
  showCons (C_Or _ _) = "SearchTree.Or _ _"
  showCons x = error ("SearchTree.SearchTree.showCons: no constructor: " ++ (show x))
  searchNF search cont (C_Value x1) = search (\y1 -> cont (C_Value y1)) x1
  searchNF search cont (C_Or x1 x2) = search (\y1 -> search (\y2 -> cont (C_Or y1 y2)) x2) x1
  searchNF _ _ x = error ("SearchTree.SearchTree.searchNF: no constructor: " ++ (show x))

-- ---------------------------------------------------------
-- Lists
-- ---------------------------------------------------------

data OP_List t0
     = OP_List
     | OP_Cons t0 (OP_List t0)
     | Choice_OP_List Cover ID (OP_List t0) (OP_List t0)
 deriving Show

instance NonDet (OP_List t0) where
  choiceCons = Choice_OP_List
  match f _  (Choice_OP_List cd i x y) = f cd i x y
  match _ f x = f x

instance NormalForm t0 => NormalForm (OP_List t0) where
  ($!!) cont OP_List d cs = cont OP_List d cs
  ($!!) cont (OP_Cons x1 x2) d cs = (((\y1 d cs -> (((\y2 d cs -> cont (OP_Cons y1 y2) d cs) $!! x2) d) cs) $!! x1) d) cs
  ($!!) cont (Choice_OP_List cd i x y) d cs = nfChoice cont cd i x y cd cs
  ($##) cont OP_List d cs = cont OP_List d cs
  ($##) cont (OP_Cons x1 x2) d cs = (((\y1 d cs -> (((\y2 d cs -> cont (OP_Cons y1 y2) d cs) $## x2) d) cs) $## x1) d) cs
  ($##) cont (Choice_OP_List cd i x y) d cs = gnfChoice cont cd i x y cd cs
  showCons OP_List = "Prelude.[]"
  showCons (OP_Cons _ _) = "Prelude.: _ _"
  showCons x = error ("Prelude.[].showCons: no constructor: " ++ (show x))
  searchNF _ cont OP_List = cont OP_List
  searchNF search cont (OP_Cons x1 x2) = search (\y1 -> search (\y2 -> cont (OP_Cons y1 y2)) x2) x1
  searchNF _ _ x = error ("Prelude.[].searchNF: no constructor: " ++ (show x))

d_OP_plus_plus :: NormalForm t0 => OP_List t0 -> OP_List t0 -> Cover -> ConstStore -> OP_List t0
d_OP_plus_plus x1 x2 cd cs = case x1 of
     OP_List -> x2
     (OP_Cons x3 x4) -> OP_Cons x3 (d_OP_plus_plus x4 x2 cd cs)
     (Choice_OP_List d i l r) -> narrow d i (d_OP_plus_plus l x2 cd cs) (d_OP_plus_plus r x2 cd cs)

d_C_foldr :: (NormalForm t0,NormalForm t1) => (t0 -> t1 -> t1) -> t1 -> OP_List t0 -> t1
d_C_foldr x1 x2 x3 = case x3 of
     OP_List -> x2
     (OP_Cons x4 x5) -> d_apply (d_apply x1 x4) (d_C_foldr x1 x2 x5)
     (Choice_OP_List d i l r) -> narrow d i (d_C_foldr x1 x2 l) (d_C_foldr x1 x2 r)

-- ---------------------------------------------------------
-- Integer
-- ---------------------------------------------------------

data C_Int
     = C_Int Int#
     | C_CurryInt BinInt
     | Choice_C_Int Cover ID C_Int C_Int
  deriving Show
 
instance NonDet C_Int where
  choiceCons = Choice_C_Int
  match f _ (Choice_C_Int cd i x y) = f cd i x y
  match _ f x = f x

instance NormalForm C_Int where
  ($!!) cont x@(C_Int _) cd cs = cont x cd cs
  ($!!) cont (C_CurryInt x1) cd cs = ((\y1 -> cont (C_CurryInt y1)) $!! x1) cd cs
  ($!!) cont (Choice_C_Int d i x y) cd cs = nfChoice cont d i x y cd cs
  ($##) cont x@(C_Int _) cd cs = cont x cd cs
  ($##) cont (C_CurryInt x1) cd cs = ((\y1 -> cont (C_CurryInt y1)) $## x1) cd cs
  ($##) cont (Choice_C_Int d i x y) cd cs = gnfChoice cont d i x y cd cs
  searchNF search cont x@(C_Int _) = cont x
  searchNF search cont (C_CurryInt x1) = search (\y1 -> cont (C_CurryInt y1)) x1
  searchNF _ _ x = error ("Prelude.Int.searchNF: no constructor: " ++ (show x))

data BinInt
     = Neg Nat
     | Zero
     | Pos Nat
     | Choice_BinInt Cover ID BinInt BinInt
  deriving Show

instance NonDet BinInt where
  choiceCons = Choice_BinInt
  match f _ (Choice_BinInt  cd i x y) = f cd i x y
  match _ f x = f x

instance NormalForm BinInt where
  ($!!) cont (Neg x1) cd cs = ((\y1 cd1 cs1 -> cont (Neg y1) cd1 cs1) $!! x1) cd cs
  ($!!) cont Zero cd cs = cont Zero cd cs
  ($!!) cont (Pos x1) cd cs = ((\y1 cd1 cs1 -> cont (Pos y1) cd1 cs1) $!! x1) cd cs
  ($!!) cont (Choice_BinInt d i x y) cd cs = nfChoice cont d i x y cd cs
  ($##) cont (Neg x1) cd cs = ((\y1 cd1 cs1 -> cont (Neg y1) cd1 cs1) $## x1) cd cs
  ($##) cont Zero cd cs = cont Zero cd cs
  ($##) cont (Pos x1) cd cs = ((\y1 cd1 cs1 -> cont (Pos y1) cd1 cs1) $## x1)cd  cs
  ($##) cont (Choice_BinInt d i x y) cd cs = gnfChoice cont d i x y cd cs
  searchNF search cont (Neg x1) = search (\y1 -> cont (Neg y1)) x1
  searchNF _ cont Zero = cont Zero
  searchNF search cont (Pos x1) = search (\y1 -> cont (Pos y1)) x1
  searchNF _ _ x = internalError ("PrimTypes.BinInt.searchNF: no constructor: " ++ (show x))

-- Nats

data Nat
     = IHi
     | O Nat
     | I Nat
     | Choice_Nat Cover ID Nat Nat
  deriving Show

instance NonDet Nat where
  choiceCons = Choice_Nat
  match f _ (Choice_Nat cd i x y) = f cd i x y
  match _ f x = f x

instance NormalForm Nat where
  ($!!) cont IHi cd cs = cont IHi cd cs
  ($!!) cont (O x1) cd cs = ((\y1 cd1 cs1 -> cont (O y1) cd1 cs1) $!! x1) cd cs
  ($!!) cont (I x1) cd cs = ((\y1 cd1 cs1 -> cont (I y1) cd1 cs1) $!! x1) cd cs
  ($!!) cont (Choice_Nat d i x y) cd cs = nfChoice cont d i x y cd cs
  ($##) cont IHi cd  cs = cont IHi cd cs
  ($##) cont (O x1) cd cs = ((\y1 cd1 cs1 -> cont (O y1) cd1 cs1) $## x1) cd cs
  ($##) cont (I x1) cd cs = ((\y1 cd1 cs1 -> cont (I y1) cd1 cs1) $## x1) cd cs
  ($##) cont (Choice_Nat d i x y) cd cs = gnfChoice cont d i x y cd cs
  searchNF _ cont IHi = cont IHi
  searchNF search cont (O x1) = search (\y1 -> cont (O y1)) x1
  searchNF search cont (I x1) = search (\y1 -> cont (I y1)) x1
  searchNF _ _ x = internalError ("PrimTypes.Nat.searchNF: no constructor: " ++ (show x))

-- ---------------------------------------------------------
-- Misc
-- ---------------------------------------------------------

-- |Apply a deterministic function to a value.
d_apply :: (a -> b) -> a -> b
d_apply f a = f a

-- |Lift a choice encountered at pattern matching to the result value.
-- The name of this function is misleading because of historical reasons
-- and should be renamed to sth. like "choice"
narrow :: NonDet a => Cover -> ID -> a -> a -> a
narrow cd i@(ChoiceID      _) = choiceCons cd i
narrow _  _                   = internalError "Basics.narrow: no ChoiceID"
