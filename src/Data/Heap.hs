{-# LANGUAGE DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Heap
-- Copyright   :  (c) Edward Kmett 2010
-- License     :  BSD-style
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- An efficient, asymptotically optimal, implementation of a priority queues
-- extended with support for efficient size, and `Data.Foldable`
--
-- /Note/: Since many function names (but not the type name) clash with
-- "Prelude" names, this module is usually imported @qualified@, e.g.
--
-- >  import Data.Heap (Heap)
-- >  import qualified Data.Heap as Heap
--
-- The implementation of 'Heap' is based on /bootstrapped skew binomial heaps/
-- as described by:
--
--    * G. Brodal and C. Okasaki , <http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.48.973 "Optimal Purely Functional Priority Queues">,
--      /Journal of Functional Programming/ 6:839-857 (1996)
--
-- All time bounds are worst-case.
-----------------------------------------------------------------------------

module Data.Heap
    (
    -- * Heap Type
      Heap -- instance Eq,Ord,Show,Read,Data,Typeable
    -- * Entry type
    , Entry(..) -- instance Eq,Ord,Show,Read,Data,Typeable
    -- * Basic functions
    , empty             -- O(1) :: Heap a
    , null              -- O(1) :: Heap a -> Bool
    , size              -- O(1) :: Heap a -> Int
    , singleton         -- O(1) :: Ord a => a -> Heap a
    , insert            -- O(1) :: Ord a => a -> Heap a -> Heap a
    , minimum           -- O(1) (/partial/) :: Ord a => Heap a -> a
    , deleteMin         -- O(log n) :: Heap a -> Heap a
    , union             -- O(1) :: Heap a -> Heap a -> Heap a
    , uncons, viewMin   -- O(1)\/O(log n) :: Heap a -> Maybe (a, Heap a)
    -- * Transformations
    , mapMonotonic      -- O(n) :: Ord b => (a -> b) -> Heap a -> Heap b
    , map               -- O(n) :: Ord b => (a -> b) -> Heap a -> Heap b
    -- * To/From Lists
    , toUnsortedList    -- O(n) :: Heap a -> [a]
    , fromList          -- O(n) :: Ord a => [a] -> Heap a
    , sort              -- O(n log n) :: Ord a => [a] -> [a]
    , traverse          -- O(n log n) :: (Applicative t, Ord b) => (a -> t b) -> Heap a -> t (Heap b)
    , mapM              -- O(n log n) :: (Monad m, Ord b) => (a -> m b) -> Heap a -> m (Heap b)
    , concatMap         -- O(n) :: Ord b => Heap a -> (a -> Heap b) -> Heap b
    -- * Filtering
    , filter            -- O(n) :: (a -> Bool) -> Heap a -> Heap a
    , partition         -- O(n) :: (a -> Bool) -> Heap a -> (Heap a, Heap a)
    , split             -- O(n) :: a -> Heap a -> (Heap a, Heap a, Heap a)
    , break             -- O(n log n) :: (a -> Bool) -> Heap a -> (Heap a, Heap a)
    , span              -- O(n log n) :: (a -> Bool) -> Heap a -> (Heap a, Heap a)
    , take              -- O(n log n) :: Int -> Heap a -> Heap a
    , drop              -- O(n log n) :: Int -> Heap a -> Heap a
    , splitAt           -- O(n log n) :: Int -> Heap a -> (Heap a, Heap a)
    , takeWhile         -- O(n log n) :: (a -> Bool) -> Heap a -> Heap a
    , dropWhile         -- O(n log n) :: (a -> Bool) -> Heap a -> Heap a
    -- * Grouping
    , group             -- O(n log n) :: Heap a -> Heap (Heap a)
    , groupBy           -- O(n log n) :: (a -> a -> Bool) -> Heap a -> Heap (Heap a)
    , nub               -- O(n log n) :: Heap a -> Heap a
    -- * Intersection
    , intersect         -- O(n log n + m log m) :: Heap a -> Heap a -> Heap a
    , intersectWith     -- O(n log n + m log m) :: Ord b => (a -> a -> b) -> Heap a -> Heap a -> Heap b
    -- * Duplication
    , replicate         -- O(log n) :: Ord a => a -> Int -> Heap a
    ) where

import Prelude hiding
    ( map, null
    , span, dropWhile, takeWhile, break, filter, take, drop, splitAt
    , foldr, minimum, replicate, mapM
    , concatMap
    )
import qualified Data.List as L
import Control.Applicative (Applicative(pure))
import Control.Monad (liftM)
import Data.Monoid (Monoid(mappend, mempty))
import Data.Foldable hiding (minimum, concatMap)
import Data.Function (on)
import Data.Data (DataType, Constr, mkConstr, mkDataType, Fixity(Prefix), Data(..), constrIndex)
import Data.Typeable (Typeable)
import Text.Read
import Text.Show
import qualified Data.Traversable as Traversable
import Data.Traversable (Traversable)

-- | A min-heap of values of type @a@ with priorities @k@
data Heap k a
  = Empty
  | Heap {-# UNPACK #-} !Int {-# UNPACK #-} !(Tree k a)
  deriving (Typeable)

instance (Ord k, Show k, Show a) => Show (Heap k a) where
  showsPrec _ Empty = showString "fromList []"
  showsPrec d (Heap _ _ t) = showParen (d > 10) $
    showString "fromList " .  showsPrec 11 (toList t)

instance (Ord k, Read k, Read a) => Read (Heap k a) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    fromList `fmap` step readPrec

instance (Ord k, Read k, Data k, Data a) => Data (Heap k a) where
  gfoldl k z h = z fromList `k` toUnsortedList h
  toConstr _ = fromListConstr
  dataTypeOf _ = heapDataType
  gunfold k z c = case constrIndex c of
    1 -> k (z fromList)
    _ -> error "gunfold"

heapDataType :: DataType
heapDataType = mkDataType "Data.Heap.Heap" [fromListConstr]

fromListConstr :: Constr
fromListConstr = mkConstr heapDataType "fromList" [] Prefix

-- | /O(1)/. Is the heap empty?
--
-- >>> null empty
-- True
--
-- >>> null (singleton "hello")
-- False
null :: Heap k a -> Bool
null Empty = True
null _ = False
{-# INLINE null #-}

-- | /O(1)/. The number of elements in the heap.
--
-- >>> size empty
-- 0
-- >>> size (singleton "hello")
-- 1
-- >>> size (fromList [4,1,2])
-- 3
size :: Heap k a -> Int
size Empty = 0
size (Heap s _) = s
{-# INLINE size #-}

-- | /O(1)/. The empty heap
--
-- @'empty' ≡ 'fromList' []@
--
-- >>> size empty
-- 0
empty :: Heap k a
empty = Empty
{-# INLINE empty #-}

-- | /O(1)/. A heap with a single element
--
-- @
-- 'singleton' x ≡ 'fromList' [x]
-- 'singleton' x ≡ 'insert' x 'empty'
-- @
--
-- >>> size (singleton "hello")
-- 1
singleton :: Ord a => k -> a -> Heap k a
singletonWith k a = Heap 1 (Node 0 k a Nil)
{-# INLINE singleton #-}

-- | /O(1)/. Insert a new value into the heap.
--
-- >>> insert 2 (fromList [1,3])
-- fromList [1,2,3]
--
-- @
-- 'insert' x 'empty' ≡ 'singleton' x
-- 'size' ('insert' x xs) ≡ 1 + 'size' xs
-- @
insert :: Ord a => k -> a -> Heap k a -> Heap k a
insert :: Ord k => k -> a -> Heap k a -> Heap k a
insert kx x Empty = singletonWith leq x
insert kx x (Heap s t@(Node _ ky y f))
  | kx <= ky  = Heap (s+1) (Node 0 kx x (t `Cons` Nil))
  | otherwise = Heap (s+1) (Node 0 ky y (skewInsert (Node 0 kx x Nil) f))
{-# INLINE insert #-}

-- | /O(1)/. Meld the values from two heaps into one heap.
union :: Ord k => Heap k a -> Heap k a -> Heap k a
union Empty q = q
union q Empty = q
union (Heap s1 t1@(Node _ kx1 x1 f1)) (Heap s2 t2@(Node _ kx2 x2 f2))
  | leq x1 x2 = Heap (s1 + s2) (Node 0 kx1 x1 (skewInsert t2 f1))
  | otherwise = Heap (s1 + s2) (Node 0 kx2 x2 (skewInsert t1 f2))
{-# INLINE union #-}

-- | /O(log n)/. Create a heap consisting of multiple copies of the same value.
--
-- >>> replicate 'a' 10
-- fromList "aaaaaaaaaa"
replicate :: Ord k => k -> a -> Int -> Heap k a
replicate kx0 x0 y0
  | y0 < 0 = error "Heap.replicate: negative length"
  | y0 == 0 = mempty
  | otherwise = f (singleton kx0 x0) y0
  where
    f x y
        | even y = f (union x x) (quot y 2)
        | y == 1 = x
        | otherwise = g (union x x) (quot (y - 1) 2) x
    g x y z
        | even y = g (union x x) (quot y 2) z
        | y == 1 = union x z
        | otherwise = g (union x x) (quot (y - 1) 2) (union x z)
{-# INLINE replicate #-}

-- | Provides both /O(1)/ access to the minimum element and /O(log n)/ access to the remainder of the heap.
-- This is the same operation as 'viewMin'
--
-- >>> uncons (fromList [2,1,3])
-- Just (1,fromList [2,3])
uncons :: Ord k => Heap k a -> Maybe ((k, a), Heap k a)
uncons Empty = Nothing
uncons l@(Heap _ t) = Just (root t, deleteMin l)
{-# INLINE uncons #-}

-- | Same as 'uncons'
viewMin :: Ord k => Heap k a -> Maybe ((k, a), Heap k a)
viewMin = uncons
{-# INLINE viewMin #-}

-- | /O(1)/. Assumes the argument is a non-'null' heap.
minimum :: Heap k a -> (k, a)
minimum Empty = error "Heap.minimum: empty heap"
minimum (Heap _ t) = root t
{-# INLINE minimum #-}

trees :: Forest k a -> [Tree k a]
trees (a `Cons` as) = a : trees as
trees Nil = []

-- | /O(log n)/. Delete the minimum key from the heap and return the resulting heap.
--
-- >>> deleteMin (fromList [3,1,2])
-- fromList [2,3]
deleteMin :: Ord k => Heap k a -> Heap k a
deleteMin Empty = Empty
deleteMin (Heap _ (Node _ _ Nil)) = Empty
deleteMin (Heap s (Node _ _ f0)) = Heap (s - 1) (Node 0 x f3)
  where
    (Node r x cf, ts2) = getMin f0
    (zs, ts1, f1) = splitForest r Nil Nil cf
    f2 = skewMeld (skewMeld ts1 ts2) f1
    f3 = foldr skewInsert f2 (trees zs)
{-# INLINE deleteMin #-}

-- | /O(log n)/. Adjust the minimum key in the heap and return the resulting heap.
--
-- >>> adjustMin (+1) (fromList [1,2,3])
-- fromList [2,2,3]
adjustMin :: Ord k => (k -> k) -> Heap k a -> Heap k a
adjustMin _ Empty = Empty
adjustMin f (Heap s (Node r kx x xs)) = Heap s (heapify (Node r (f kx) x xs))
{-# INLINE adjustMin #-}

type ForestZipper k a = (Forest k a, Forest k a)

zipper :: Forest k a -> ForestZipper k a
zipper xs = (Nil, xs)
{-# INLINE zipper #-}

emptyZ :: ForestZipper k a
emptyZ = (Nil, Nil)
{-# INLINE emptyZ #-}

-- leftZ :: ForestZipper k a -> ForestZipper k a
-- leftZ (x :> path, xs) = (path, x :> xs)

rightZ :: ForestZipper k a -> ForestZipper k a
rightZ (path, x `Cons` xs) = (x `Cons` path, xs)
{-# INLINE rightZ #-}

adjustZ :: (Tree k a -> Tree k a) -> ForestZipper k a -> ForestZipper k a
adjustZ f (path, x `Cons` xs) = (path, f x `Cons` xs)
adjustZ _ z = z
{-# INLINE adjustZ #-}

rezip :: ForestZipper k a -> Forest k a
rezip (Nil, xs) = xs
rezip (x `Cons` path, xs) = rezip (path, x `Cons` xs)

-- assumes non-empty zipper
rootZ :: ForestZipper k a -> (k, a)
rootZ (_ , x `Cons` _) = root x
rootZ _ = error "Heap.rootZ: empty zipper"
{-# INLINE rootZ #-}

minZ :: Ord k => Forest k a -> ForestZipper k a
minZ Nil = emptyZ
minZ xs = minZ' z z
    where z = zipper xs
{-# INLINE minZ #-}

minZ' :: Ord k => ForestZipper k a -> ForestZipper k a -> ForestZipper k a
minZ' lo (_, Nil) = lo
minZ' lo z = minZ' (if rootZ lo <= rootZ z then lo else z) (rightZ z)

heapify :: Ord k => Tree k a -> Tree k a
heapify n@(Node _ _ Nil) = n
heapify n@(Node r a as)
  | a <= a' = n
  | otherwise = Node r a' (rezip (left, heapify (Node r' a as') `Cons` right))
  where
    (left, Node r' a' as' `Cons` right) = minZ as

-- | /O(n)/. Build a heap from a list of values.
--
-- @
-- 'fromList' '.' 'toList' ≡ 'id'
-- 'toList' '.' 'fromList' ≡ 'sort'
-- @

-- >>> size (fromList [1,5,3])
-- 3
fromList :: Ord k => [(k, a)] -> Heap k a
fromList = foldr (uncurry insert) mempty
{-# INLINE fromList #-}

-- | /O(n log n)/. Perform a heap sort
sort :: Ord k => [(k,a)] -> [(k,a)]
sort = toList . fromList
{-# INLINE sort #-}

instance Ord k => Monoid (Heap k a) where
  mempty = empty
  {-# INLINE mempty #-}
  mappend = union
  {-# INLINE mappend #-}

-- | /O(n)/. Returns the elements in the heap in some arbitrary, very likely unsorted, order.
--
-- >>> toUnsortedList (fromList [3,1,2])
-- [1,3,2]
--
-- @'fromList' '.' 'toUnsortedList' ≡ 'id'@
toUnsortedList :: Ord k => Heap k a -> [(k, a)]
toUnsortedList Empty = []
toUnsortedList (Heap _ t) = foldMap return t
{-# INLINE toUnsortedList #-}

instance Foldable (Heap k) where
  foldMap _ Empty = mempty
  foldMap f l@(Heap _ _ t) = f (root t) `mappend` foldMap f (deleteMin l)

ifoldMap :: Monoid m => (k -> a -> m) -> Heap k a -> m
ifoldMap _ Empty = mempty
ifoldMap f l@(Heap _ _ t) = f (root t) `mappend` foldMap f (deleteMin l)

instance Ord k => Traversable (Heap k) where
  traverse f = fmap fromList . traverse go . toList where
    go (k,v) = (,) k `liftM` f v

-- | /O(n)/. Map a monotone increasing function over the heap.
-- Provides a better constant factor for performance than 'map', but no checking is performed that the function provided is monotone increasing. Misuse of this function can cause a Heap to violate the heap property.
--
-- >>> map (+1) (fromList [1,2,3])
-- fromList [2,3,4]
-- >>> map (*2) (fromList [1,2,3])
-- fromList [2,4,6]
mapKeysMonotonic :: Ord j => (i -> j) -> Heap i a -> Heap j b
mapKeysMonotonic _ Empty = Empty
mapKeysMonotonic f (Heap s t) = Heap s (first f t)
{-# INLINE mapMonotonic #-}

-- * Filter

-- | /O(n)/. Filter the heap, retaining only values that satisfy the predicate.
filterWithKey :: Ord k => (k -> a -> Bool) -> Heap k a -> Heap k a
filterWithKey _ Empty = Empty
filterWithKey p (Heap _ leq t) = ifoldMap f t
  where
    f kx x | p kx x = singletonWith leq kx x
           | otherwise = Empty
{-# INLINE filterWithKey #-}


filter :: Ord k => (a -> Bool) -> Heap k a -> Heap k a
filter = filterWithKey . const
{-# INLINE filterWithKey #-}

-- | /O(n)/. Partition the heap according to a predicate. The first heap contains all elements that satisfy the predicate, the second all elements that fail the predicate. See also 'split'.
--
-- >>> partition (>'a') (fromList "ab")
-- (fromList "b",fromList "a")
partitionWithKey :: Ord k => (k -> a -> Bool) -> Heap k a -> (Heap k a, Heap k a)
partitionWithKey _ Empty = (Empty, Empty)
partitionWithKey p (Heap _ t) = ifoldMap f t
  where
    f kx x | p kx x = (singleton kx x, mempty)
           | otherwise = (mempty, singleton kx x)
{-# INLINE partition #-}

-- | /O(n)/. Partition the heap into heaps of the elements that are less than, equal to, and greater than a given value.
split :: Ord k => k -> Heap k a -> (Heap k a, Heap k a, Heap k a)
split a Empty = (Empty, Empty, Empty)
split a (Heap s t) = ifoldMap f t
  where
    f kx x = case compare kx a of
      LT -> (singleton kx x, mempty, mempty)
      EQ -> (mempty, singleton kx x, mempty)
      GT -> (mempty, mempty, singleton kx x)
{-# INLINE split #-}

-- * Subranges

-- | /O(n log n)/. Return a heap consisting of the least @n@ elements of a given heap.
take :: Ord k => Int -> Heap k a -> Heap k a
take = withList . L.take
{-# INLINE take #-}

-- | /O(n log n)/. Return a heap consisting of all members of given heap except for the @n@ least elements.
drop :: Ord k => Int -> Heap k a -> Heap k a
drop n h0
  | n <= 0    = h0
  | otherwise = go n h0 where
  go 0 h = h
  go k h = go (h - 1) (deleteMin h)
{-# INLINE drop #-}

-- | /O(n log n)/. Split a heap into two heaps, the first containing the @n@ least elements, the latter consisting of all members of the heap except for those elements.
splitAt :: Ord k => Int -> Heap k a -> (Heap k a, Heap k a)
splitAt = splitWithList . L.splitAt
{-# INLINE splitAt #-}

-- | /O(n log n)/. 'break' applied to a predicate @p@ and a heap @xs@ returns a tuple where the first element is a heap consisting of the
-- longest prefix the least elements of @xs@ that /do not satisfy/ p and the second element is the remainder of the elements in the heap.
--
-- >>> break (\x -> x `mod` 4 == 0) (fromList [3,5,7,12,13,16])
-- (fromList [3,5,7],fromList [12,13,16])
--
-- 'break' @p@ is equivalent to @'span' ('not' . p)@.
break :: Ord k => (a -> Bool) -> Heap k a -> (Heap k a, Heap k a)
break = splitWithList . L.break . snd
{-# INLINE break #-}

-- | /O(n log n)/. 'span' applied to a predicate @p@ and a heap @xs@ returns a tuple where the first element is a heap consisting of the
-- longest prefix the least elements of xs that satisfy @p@ and the second element is the remainder of the elements in the heap.
--
-- 'span' @p xs@ is equivalent to @('takeWhile' p xs, 'dropWhile p xs)@
span :: Ord k => (a -> Bool) -> Heap k a -> (Heap k a, Heap k a)
span = splitWithList . L.span . snd
{-# INLINE span #-}

-- | /O(n log n)/. 'takeWhile' applied to a predicate @p@ and a heap @xs@ returns a heap consisting of the
-- longest prefix the least elements of @xs@ that satisfy @p@.
--
takeWhile :: Ord k => (a -> Bool) -> Heap k a -> Heap k a
takeWhile = withList . L.takeWhile . snd
{-# INLINE takeWhile #-}

-- | /O(n log n)/. 'dropWhile' @p xs@ returns the suffix of the heap remaining after 'takeWhile' @p xs@.
--
dropWhile :: Ord k => (a -> Bool) -> Heap k a -> Heap k a
dropWhile = withList . L.dropWhile . snd
{-# INLINE dropWhile #-}

-- | /O(n log n)/. Remove duplicate entries from the heap.
nub :: Ord k => Heap k a -> Heap k a
nub Empty = Empty
nub h@(Heap _ t) = uncurry insert x (nub zs)
  where
    x = root t
    xs = deleteMin h
    zs = dropWhile (`leq` x) xs
{-# INLINE nub #-}

-- | /O(n)/. Construct heaps from each element in another heap, and union them together.
--
-- >>> concatMap (\a -> fromList [a,a+1]) (fromList [1,4])
-- fromList [1,4,5,2]
concatMap :: Ord k => (a -> Heap k b) -> Heap k a -> Heap k b
concatMap _ Empty = Empty
concatMap f h@(Heap _ t) = foldMap f t
{-# INLINE concatMap #-}

-- | /O(n log n + m log m)/. Intersect the values in two heaps, returning the value in the left heap that compares as equal
intersect :: Ord k => Heap k a -> Heap k b -> Heap k a
intersect = intersectWith const
{-# INLINE intersect #-}

-- | /O(n log n + m log m)/. Intersect the values in two heaps using a function to generate the elements in the right heap.
intersectWith :: Ord k => (a -> b -> c) -> Heap k a -> Heap k b -> Heap k c
intersectWith _ Empty _ = Empty
intersectWith _ _ Empty = Empty
intersectWith f a@(Heap _ _) b = go f (toList a) (toList b)
  where
    go :: Ord k => (a -> b -> c) -> [(k, a)] -> [(k, b)] -> Heap c
    go f' xxs@((kx,x):xs) yys@((ky,y):ys) = case compare kx ky of
      LT -> go f' xs yys
      EQ -> insert kx (f' x y) (go f' xs ys)
      GT -> go f' xxs ys
    go _ [] _ = empty
    go _ _ [] = empty
{-# INLINE intersectWith #-}

both :: (a -> b) -> (a, a) -> (b, b)
both f (a,b) = (f a, f b)
{-# INLINE both #-}

-- we hold onto the children counts in the nodes for /O(1)/ 'size'
data Tree k a = Node
  { rank    :: {-# UNPACK #-} !Int
  , key     :: k
  , value   :: a
  , _forest :: !(Forest k a)
  } deriving (Show,Read,Typeable)

data Forest k a = !(Tree k a) `Cons` !(Forest k a) | Nil
  deriving (Show,Read,Typeable)
infixr 5 `Cons`

instance Functor (Tree k) where
  fmap f (Node r k a as) = Node r k (f a) (fmap f as)

instance Functor (Forest k) where
  fmap f (a `Cons` as) = fmap f a `Cons` fmap f as
  fmap _ Nil = Nil

-- internal foldable instances that should only be used over commutative monoids
instance Foldable (Tree k) where
  foldMap f (Node _ _ a as) = f a `mappend` foldMap f as

-- internal foldable instances that should only be used over commutative monoids
instance Foldable (Forest k) where
  foldMap f (a `Cons` as) = foldMap f a `mappend` foldMap f as
  foldMap _ Nil = mempty

instance Traversable (Tree k) where
  traverse f (Node r k a as) = Node r k <$> f a <*> traverse f as

instance Traversable (Forest k) where
  traverse f (a `Cons` as) = Cons <$> traverse f a <*> traverse f as
  traverse _ Nil = pure Nil

link :: Ord k => Tree k a -> Tree k a -> Tree k a
link t1@(Node r1 x1 y1 cf1) t2@(Node r2 x2 y2 cf2)
  | x1 <= x2  = Node (r1+1) x1 y1 (t2 `Cons` cf1)
  | otherwise = Node (r2+1) x2 y2 (t1 `Cons` cf2)

skewLink :: Ord k => Tree k a -> Tree k a -> Tree k a -> Tree k a
skewLink t0@(Node _ x0 y0 cf0) t1@(Node r1 x1 y1 cf1) t2@(Node r2 x2 y2 cf2)
  | x1 <= x0 && x1 <= x2 = Node (r1+1) x1 y1 (t0 `Cons` t2 `Cons` cf1)
  | x2 <= x0 && x2 <= x1 = Node (r2+1) x2 y2 (t0 `Cons` t1 `Cons` cf2)
  | otherwise            = Node (r1+1) x0 y0 (t1 `Cons` t2 `Cons` cf0)

ins :: Ord k => Tree k a -> Forest k a -> Forest k a
ins t Nil = t `Cons` Nil
ins t (t' `Cons` ts) -- assumes rank t <= rank t'
  | rank t < rank t' = t `Cons` t' `Cons` ts
  | otherwise = ins (link t t') ts

uniqify :: Ord k => Forest k a -> Forest k a
uniqify Nil = Nil
uniqify (t `Cons` ts) = ins t ts

unionUniq :: Ord k => Forest k a -> Forest k a -> Forest k a
unionUniq Nil ts = ts
unionUniq ts Nil = ts
unionUniq tts1@(t1 `Cons` ts1) tts2@(t2 `Cons` ts2) = case compare (rank t1) (rank t2) of
  LT -> t1 `Cons` unionUniq ts1 tts2
  EQ -> ins (link t1 t2) (unionUniq ts1 ts2)
  GT -> t2 `Cons` unionUniq tts1 ts2

skewInsert :: Ord k => Tree k a -> Forest k a -> Forest k a
skewInsert t ts@(t1 `Cons` t2 `Cons`rest)
  | rank t1 == rank t2 = skewLink t t1 t2 `Cons` rest
  | otherwise          = t `Cons` ts
skewInsert t ts = t `Cons` ts
{-# INLINE skewInsert #-}

skewMeld :: Ord k => Forest k a -> Forest k a -> Forest k a
skewMeld ts ts' = unionUniq (uniqify ts) (uniqify ts')
{-# INLINE skewMeld #-}

getMin :: Ord k => Forest k a -> (Tree k a, Forest k a)
getMin (t `Cons` Nil) = (t, Nil)
getMin (t `Cons` ts)
  | root t <= root t' = (t, ts)
  | otherwise         = (t', t `Cons` ts')
  where (t',ts') = getMin ts
getMin Nil = error "Heap.getMin: empty forest"

splitForest :: Int -> Forest k a -> Forest k a -> Forest k a -> (Forest k a, Forest k a, Forest k a)
splitForest a b c d | a `seq` b `seq` c `seq` d `seq` False = undefined
splitForest 0 zs ts f = (zs, ts, f)
splitForest 1 zs ts (t `Cons` Nil) = (zs, t `Cons` ts, Nil)
splitForest 1 zs ts (t1 `Cons` t2 `Cons` f)
  -- rank t1 == 0
  | rank t2 == 0 = (t1 `Cons` zs, t2 `Cons` ts, f)
  | otherwise    = (zs, t1 `Cons` ts, t2 `Cons` f)
splitForest r zs ts (t1 `Cons` t2 `Cons` cf)
  -- r1 = r - 1 or r1 == 0
  | r1 == r2          = (zs, t1 `Cons` t2 `Cons` ts, cf)
  | r1 == 0           = splitForest (r-1) (t1 `Cons` zs) (t2 `Cons` ts) cf
  | otherwise         = splitForest (r-1) zs (t1 `Cons` ts) (t2 `Cons` cf)
  where
    r1 = rank t1
    r2 = rank t2
splitForest _ _ _ _ = error "Heap.splitForest: invalid arguments"

withList :: Ord k => ([(k,a)] -> [(k,a)]) -> Heap k a -> Heap k a
withList _ Empty = Empty
withList f hp = fromList (f (toList hp))
{-# INLINE withList #-}

splitWithList :: Ord k => ([(k,a)] -> ([(k,a)],[(k,a)])) -> Heap k a -> (Heap k a, Heap k a)
splitWithList _ Empty = (Empty, Empty)
splitWithList f hp = both fromList (f (toList hp))
{-# INLINE splitWithList #-}
