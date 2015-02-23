{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE RoleAnnotations #-}
#endif
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
#if MIN_VERSION_base(4,8,0)
    , traverse
#endif
    )
import qualified Data.List as L
import Control.Applicative (Applicative(pure))
import Control.Monad (liftM)
import Data.Monoid (Monoid(mappend, mempty))
#if MIN_VERSION_base(4,8,0)
import Data.Foldable hiding (minimum, concatMap, null)
#else
import Data.Foldable hiding (minimum, concatMap)
#endif
import Data.Function (on)
import Data.Data (DataType, Constr, mkConstr, mkDataType, Fixity(Prefix), Data(..), constrIndex)
import Data.Typeable (Typeable)
import Text.Read
import Text.Show
import qualified Data.Traversable as Traversable
import Data.Traversable (Traversable)

-- The implementation of 'Heap' must internally hold onto the dictionary entry for ('<='),
-- so that it can be made 'Foldable'. Confluence in the absence of incoherent instances
-- is provided by the fact that we only ever build these from instances of 'Ord' a (except in the case of 'groupBy')


-- | A min-heap of values of type @a@.
data Heap a
  = Empty
  | Heap {-# UNPACK #-} !Int (a -> a -> Bool) {-# UNPACK #-} !(Tree a)
  deriving Typeable

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
type role Heap nominal
#endif

instance Show a => Show (Heap a) where
  showsPrec _ Empty = showString "fromList []"
  showsPrec d (Heap _ _ t) = showParen (d > 10) $
    showString "fromList " .  showsPrec 11 (toList t)

instance (Ord a, Read a) => Read (Heap a) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    fromList `fmap` step readPrec

instance (Ord a, Data a) => Data (Heap a) where
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

instance Eq (Heap a) where
  Empty == Empty = True
  Empty == Heap{} = False
  Heap{} == Empty = False
  a@(Heap s1 leq _) == b@(Heap s2 _ _) = s1 == s2 && go leq (toList a) (toList b)
    where
      go f (x:xs) (y:ys) = f x y && f y x && go f xs ys
      go _ [] [] = True
      go _ _ _ = False

instance Ord (Heap a) where
  Empty `compare` Empty = EQ
  Empty `compare` Heap{} = LT
  Heap{} `compare` Empty = GT
  a@(Heap _ leq _) `compare` b = go leq (toList a) (toList b)
    where
      go f (x:xs) (y:ys) =
          if f x y
          then if f y x
               then go f xs ys
               else LT
          else GT
      go f [] []    = EQ
      go f [] (_:_) = LT
      go f (_:_) [] = GT


-- | /O(1)/. Is the heap empty?
--
-- >>> null empty
-- True
--
-- >>> null (singleton "hello")
-- False
null :: Heap a -> Bool
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
size :: Heap a -> Int
size Empty = 0
size (Heap s _ _) = s
{-# INLINE size #-}

-- | /O(1)/. The empty heap
--
-- @'empty' ≡ 'fromList' []@
--
-- >>> size empty
-- 0
empty :: Heap a
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
singleton :: Ord a => a -> Heap a
singleton = singletonWith (<=)
{-# INLINE singleton #-}

singletonWith :: (a -> a -> Bool) -> a -> Heap a
singletonWith f a = Heap 1 f (Node 0 a Nil)
{-# INLINE singletonWith #-}

-- | /O(1)/. Insert a new value into the heap.
--
-- >>> insert 2 (fromList [1,3])
-- fromList [1,2,3]
--
-- @
-- 'insert' x 'empty' ≡ 'singleton' x
-- 'size' ('insert' x xs) ≡ 1 + 'size' xs
-- @
insert :: Ord a => a -> Heap a -> Heap a
insert = insertWith (<=)
{-# INLINE insert #-}

insertWith :: (a -> a -> Bool) -> a -> Heap a -> Heap a
insertWith leq x Empty = singletonWith leq x
insertWith leq x (Heap s _ t@(Node _ y f))
  | leq x y   = Heap (s+1) leq (Node 0 x (t `Cons` Nil))
  | otherwise = Heap (s+1) leq (Node 0 y (skewInsert leq (Node 0 x Nil) f))
{-# INLINE insertWith #-}

-- | /O(1)/. Meld the values from two heaps into one heap.
--
-- >>> union (fromList [1,3,5]) (fromList [6,4,2])
-- fromList [1,2,6,4,3,5]
-- >>> union (fromList [1,1,1]) (fromList [1,2,1])
-- fromList [1,1,1,2,1,1]
union :: Heap a -> Heap a -> Heap a
union Empty q = q
union q Empty = q
union (Heap s1 leq t1@(Node _ x1 f1)) (Heap s2 _ t2@(Node _ x2 f2))
  | leq x1 x2 = Heap (s1 + s2) leq (Node 0 x1 (skewInsert leq t2 f1))
  | otherwise = Heap (s1 + s2) leq (Node 0 x2 (skewInsert leq t1 f2))
{-# INLINE union #-}

-- | /O(log n)/. Create a heap consisting of multiple copies of the same value.
--
-- >>> replicate 'a' 10
-- fromList "aaaaaaaaaa"
replicate :: Ord a => a -> Int -> Heap a
replicate x0 y0
  | y0 < 0 = error "Heap.replicate: negative length"
  | y0 == 0 = mempty
  | otherwise = f (singleton x0) y0
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
uncons :: Ord a => Heap a -> Maybe (a, Heap a)
uncons Empty = Nothing
uncons l@(Heap _ _ t) = Just (root t, deleteMin l)
{-# INLINE uncons #-}

-- | Same as 'uncons'
viewMin :: Ord a => Heap a -> Maybe (a, Heap a)
viewMin = uncons
{-# INLINE viewMin #-}

-- | /O(1)/. Assumes the argument is a non-'null' heap.
--
-- >>> minimum (fromList [3,1,2])
-- 1
minimum :: Heap a -> a
minimum Empty = error "Heap.minimum: empty heap"
minimum (Heap _ _ t) = root t
{-# INLINE minimum #-}

trees :: Forest a -> [Tree a]
trees (a `Cons` as) = a : trees as
trees Nil = []

-- | /O(log n)/. Delete the minimum key from the heap and return the resulting heap.
--
-- >>> deleteMin (fromList [3,1,2])
-- fromList [2,3]
deleteMin :: Heap a -> Heap a
deleteMin Empty = Empty
deleteMin (Heap _ _ (Node _ _ Nil)) = Empty
deleteMin (Heap s leq (Node _ _ f0)) = Heap (s - 1) leq (Node 0 x f3)
  where
    (Node r x cf, ts2) = getMin leq f0
    (zs, ts1, f1) = splitForest r Nil Nil cf
    f2 = skewMeld leq (skewMeld leq ts1 ts2) f1
    f3 = foldr (skewInsert leq) f2 (trees zs)
{-# INLINE deleteMin #-}

-- | /O(log n)/. Adjust the minimum key in the heap and return the resulting heap.
--
-- >>> adjustMin (+1) (fromList [1,2,3])
-- fromList [2,2,3]
adjustMin :: (a -> a) -> Heap a -> Heap a
adjustMin _ Empty = Empty
adjustMin f (Heap s leq (Node r x xs)) = Heap s leq (heapify leq (Node r (f x) xs))
{-# INLINE adjustMin #-}

type ForestZipper a = (Forest a, Forest a)

zipper :: Forest a -> ForestZipper a
zipper xs = (Nil, xs)
{-# INLINE zipper #-}

emptyZ :: ForestZipper a
emptyZ = (Nil, Nil)
{-# INLINE emptyZ #-}

-- leftZ :: ForestZipper a -> ForestZipper a
-- leftZ (x :> path, xs) = (path, x :> xs)

rightZ :: ForestZipper a -> ForestZipper a
rightZ (path, x `Cons` xs) = (x `Cons` path, xs)
{-# INLINE rightZ #-}

adjustZ :: (Tree a -> Tree a) -> ForestZipper a -> ForestZipper a
adjustZ f (path, x `Cons` xs) = (path, f x `Cons` xs)
adjustZ _ z = z
{-# INLINE adjustZ #-}

rezip :: ForestZipper a -> Forest a
rezip (Nil, xs) = xs
rezip (x `Cons` path, xs) = rezip (path, x `Cons` xs)

-- assumes non-empty zipper
rootZ :: ForestZipper a -> a
rootZ (_ , x `Cons` _) = root x
rootZ _ = error "Heap.rootZ: empty zipper"
{-# INLINE rootZ #-}

minZ :: (a -> a -> Bool) -> Forest a -> ForestZipper a
minZ _ Nil = emptyZ
minZ f xs = minZ' f z z
    where z = zipper xs
{-# INLINE minZ #-}

minZ' :: (a -> a -> Bool) -> ForestZipper a -> ForestZipper a -> ForestZipper a
minZ' _ lo (_, Nil) = lo
minZ' leq lo z = minZ' leq (if leq (rootZ lo) (rootZ z) then lo else z) (rightZ z)

heapify :: (a -> a -> Bool) -> Tree a -> Tree a
heapify _ n@(Node _ _ Nil) = n
heapify leq n@(Node r a as)
  | leq a a' = n
  | otherwise = Node r a' (rezip (left, heapify leq (Node r' a as') `Cons` right))
  where
    (left, Node r' a' as' `Cons` right) = minZ leq as


-- | /O(n)/. Build a heap from a list of values.
--
-- @
-- 'fromList' '.' 'toList' ≡ 'id'
-- 'toList' '.' 'fromList' ≡ 'sort'
-- @

-- >>> size (fromList [1,5,3])
-- 3
fromList :: Ord a => [a] -> Heap a
fromList = foldr insert mempty
{-# INLINE fromList #-}

fromListWith :: (a -> a -> Bool) -> [a] -> Heap a
fromListWith f = foldr (insertWith f) mempty
{-# INLINE fromListWith #-}

-- | /O(n log n)/. Perform a heap sort
sort :: Ord a => [a] -> [a]
sort = toList . fromList
{-# INLINE sort #-}

instance Monoid (Heap a) where
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
toUnsortedList :: Heap a -> [a]
toUnsortedList Empty = []
toUnsortedList (Heap _ _ t) = foldMap return t
{-# INLINE toUnsortedList #-}

instance Foldable Heap where
  foldMap _ Empty = mempty
  foldMap f l@(Heap _ _ t) = f (root t) `mappend` foldMap f (deleteMin l)

-- | /O(n)/. Map a function over the heap, returning a new heap ordered appropriately for its fresh contents
--
-- >>> map negate (fromList [3,1,2])
-- fromList [-3,-1,-2]
map :: Ord b => (a -> b) -> Heap a -> Heap b
map _ Empty = Empty
map f (Heap _ _ t) = foldMap (singleton . f) t
{-# INLINE map #-}

-- | /O(n)/. Map a monotone increasing function over the heap.
-- Provides a better constant factor for performance than 'map', but no checking is performed that the function provided is monotone increasing. Misuse of this function can cause a Heap to violate the heap property.
--
-- >>> map (+1) (fromList [1,2,3])
-- fromList [2,3,4]
-- >>> map (*2) (fromList [1,2,3])
-- fromList [2,4,6]
mapMonotonic :: Ord b => (a -> b) -> Heap a -> Heap b
mapMonotonic _ Empty = Empty
mapMonotonic f (Heap s _ t) = Heap s (<=) (fmap f t)
{-# INLINE mapMonotonic #-}

-- * Filter

-- | /O(n)/. Filter the heap, retaining only values that satisfy the predicate.
--
-- >>> filter (>'a') (fromList "ab")
-- fromList "b"
-- >>> filter (>'x') (fromList "ab")
-- fromList []
-- >>> filter (<'a') (fromList "ab")
-- fromList []
filter :: (a -> Bool) -> Heap a -> Heap a
filter _ Empty = Empty
filter p (Heap _ leq t) = foldMap f t
  where
    f x | p x = singletonWith leq x
        | otherwise = Empty
{-# INLINE filter #-}

-- | /O(n)/. Partition the heap according to a predicate. The first heap contains all elements that satisfy the predicate, the second all elements that fail the predicate. See also 'split'.
--
-- >>> partition (>'a') (fromList "ab")
-- (fromList "b",fromList "a")
partition :: (a -> Bool) -> Heap a -> (Heap a, Heap a)
partition _ Empty = (Empty, Empty)
partition p (Heap _ leq t) = foldMap f t
  where
    f x | p x       = (singletonWith leq x, mempty)
        | otherwise = (mempty, singletonWith leq x)
{-# INLINE partition #-}

-- | /O(n)/. Partition the heap into heaps of the elements that are less than, equal to, and greater than a given value.
--
-- >>> split 'h' (fromList "hello")
-- (fromList "e",fromList "h",fromList "llo")
split :: a -> Heap a -> (Heap a, Heap a, Heap a)
split a Empty = (Empty, Empty, Empty)
split a (Heap s leq t) = foldMap f t
  where
    f x = if leq x a
          then if leq a x
               then (mempty, singletonWith leq x, mempty)
               else (singletonWith leq x, mempty, mempty)
          else (mempty, mempty, singletonWith leq x)
{-# INLINE split #-}

-- * Subranges

-- | /O(n log n)/. Return a heap consisting of the least @n@ elements of a given heap.
--
-- >>> take 3 (fromList [10,2,4,1,9,8,2])
-- fromList [1,2,2]
take :: Int -> Heap a -> Heap a
take = withList . L.take
{-# INLINE take #-}

-- | /O(n log n)/. Return a heap consisting of all members of given heap except for the @n@ least elements.
drop :: Int -> Heap a -> Heap a
drop = withList . L.drop
{-# INLINE drop #-}

-- | /O(n log n)/. Split a heap into two heaps, the first containing the @n@ least elements, the latter consisting of all members of the heap except for those elements.
splitAt :: Int -> Heap a -> (Heap a, Heap a)
splitAt = splitWithList . L.splitAt
{-# INLINE splitAt #-}

-- | /O(n log n)/. 'break' applied to a predicate @p@ and a heap @xs@ returns a tuple where the first element is a heap consisting of the
-- longest prefix the least elements of @xs@ that /do not satisfy/ p and the second element is the remainder of the elements in the heap.
--
-- >>> break (\x -> x `mod` 4 == 0) (fromList [3,5,7,12,13,16])
-- (fromList [3,5,7],fromList [12,13,16])
--
-- 'break' @p@ is equivalent to @'span' ('not' . p)@.
break :: (a -> Bool) -> Heap a -> (Heap a, Heap a)
break = splitWithList . L.break
{-# INLINE break #-}

-- | /O(n log n)/. 'span' applied to a predicate @p@ and a heap @xs@ returns a tuple where the first element is a heap consisting of the
-- longest prefix the least elements of xs that satisfy @p@ and the second element is the remainder of the elements in the heap.
--
-- >>> span (\x -> x `mod` 4 == 0) (fromList [4,8,12,14,16])
-- (fromList [4,8,12],fromList [14,16])
--
-- 'span' @p xs@ is equivalent to @('takeWhile' p xs, 'dropWhile p xs)@

span :: (a -> Bool) -> Heap a -> (Heap a, Heap a)
span = splitWithList . L.span
{-# INLINE span #-}

-- | /O(n log n)/. 'takeWhile' applied to a predicate @p@ and a heap @xs@ returns a heap consisting of the
-- longest prefix the least elements of @xs@ that satisfy @p@.
--
-- >>> takeWhile (\x -> x `mod` 4 == 0) (fromList [4,8,12,14,16])
-- fromList [4,8,12]
takeWhile :: (a -> Bool) -> Heap a -> Heap a
takeWhile = withList . L.takeWhile
{-# INLINE takeWhile #-}

-- | /O(n log n)/. 'dropWhile' @p xs@ returns the suffix of the heap remaining after 'takeWhile' @p xs@.
--
-- >>> dropWhile (\x -> x `mod` 4 == 0) (fromList [4,8,12,14,16])
-- fromList [14,16]
dropWhile :: (a -> Bool) -> Heap a -> Heap a
dropWhile = withList . L.dropWhile
{-# INLINE dropWhile #-}

-- | /O(n log n)/. Remove duplicate entries from the heap.
--
-- >>> nub (fromList [1,1,2,6,6])
-- fromList [1,2,6]
nub :: Heap a -> Heap a
nub Empty = Empty
nub h@(Heap _ leq t) = insertWith leq x (nub zs)
  where
    x = root t
    xs = deleteMin h
    zs = dropWhile (`leq` x) xs
{-# INLINE nub #-}

-- | /O(n)/. Construct heaps from each element in another heap, and union them together.
--
-- >>> concatMap (\a -> fromList [a,a+1]) (fromList [1,4])
-- fromList [1,4,5,2]
concatMap :: Ord b => (a -> Heap b) -> Heap a -> Heap b
concatMap _ Empty = Empty
concatMap f h@(Heap _ _ t) = foldMap f t
{-# INLINE concatMap #-}

-- | /O(n log n)/. Group a heap into a heap of heaps, by unioning together duplicates.
--
-- >>> group (fromList "hello")
-- fromList [fromList "e",fromList "h",fromList "ll",fromList "o"]
group :: Heap a -> Heap (Heap a)
group Empty = Empty
group h@(Heap _ leq _) = groupBy (flip leq) h
{-# INLINE group #-}

-- | /O(n log n)/. Group using a user supplied function.
groupBy :: (a -> a -> Bool) -> Heap a -> Heap (Heap a)
groupBy f Empty = Empty
groupBy f h@(Heap _ leq t) = insert (insertWith leq x ys) (groupBy f zs)
  where
    x = root t
    xs = deleteMin h
    (ys,zs) = span (f x) xs
{-# INLINE groupBy #-}

-- | /O(n log n + m log m)/. Intersect the values in two heaps, returning the value in the left heap that compares as equal
intersect :: Heap a -> Heap a -> Heap a
intersect Empty _ = Empty
intersect _ Empty = Empty
intersect a@(Heap _ leq _) b = go leq (toList a) (toList b)
  where
    go leq' xxs@(x:xs) yys@(y:ys) =
        if leq' x y
        then if leq' y x
             then insertWith leq' x (go leq' xs ys)
             else go leq' xs yys
        else go leq' xxs ys
    go _ [] _ = empty
    go _ _ [] = empty
{-# INLINE intersect #-}

-- | /O(n log n + m log m)/. Intersect the values in two heaps using a function to generate the elements in the right heap.
intersectWith :: Ord b => (a -> a -> b) -> Heap a -> Heap a -> Heap b
intersectWith _ Empty _ = Empty
intersectWith _ _ Empty = Empty
intersectWith f a@(Heap _ leq _) b = go leq f (toList a) (toList b)
  where
    go :: Ord b => (a -> a -> Bool) -> (a -> a -> b) -> [a] -> [a] -> Heap b
    go leq' f' xxs@(x:xs) yys@(y:ys)
        | leq' x y =
            if leq' y x
            then insert (f' x y) (go leq' f' xs ys)
            else go leq' f' xs yys
        | otherwise = go leq' f' xxs ys
    go _ _ [] _ = empty
    go _ _ _ [] = empty
{-# INLINE intersectWith #-}

-- | /O(n log n)/. Traverse the elements of the heap in sorted order and produce a new heap using 'Applicative' side-effects.
traverse :: (Applicative t, Ord b) => (a -> t b) -> Heap a -> t (Heap b)
traverse f = fmap fromList . Traversable.traverse f . toList
{-# INLINE traverse #-}

-- | /O(n log n)/. Traverse the elements of the heap in sorted order and produce a new heap using 'Monad'ic side-effects.
mapM :: (Monad m, Ord b) => (a -> m b) -> Heap a -> m (Heap b)
mapM f = liftM fromList . Traversable.mapM f . toList
{-# INLINE mapM #-}

both :: (a -> b) -> (a, a) -> (b, b)
both f (a,b) = (f a, f b)
{-# INLINE both #-}

-- we hold onto the children counts in the nodes for /O(1)/ 'size'
data Tree a = Node
  { rank :: {-# UNPACK #-} !Int
  , root :: a
  , _forest :: !(Forest a)
  } deriving (Show,Read,Typeable)

data Forest a = !(Tree a) `Cons` !(Forest a) | Nil
  deriving (Show,Read,Typeable)
infixr 5 `Cons`

instance Functor Tree where
  fmap f (Node r a as) = Node r (f a) (fmap f as)

instance Functor Forest where
  fmap f (a `Cons` as) = fmap f a `Cons` fmap f as
  fmap _ Nil = Nil

-- internal foldable instances that should only be used over commutative monoids
instance Foldable Tree where
  foldMap f (Node _ a as) = f a `mappend` foldMap f as

-- internal foldable instances that should only be used over commutative monoids
instance Foldable Forest where
  foldMap f (a `Cons` as) = foldMap f a `mappend` foldMap f as
  foldMap _ Nil = mempty

link :: (a -> a -> Bool) -> Tree a -> Tree a -> Tree a
link f t1@(Node r1 x1 cf1) t2@(Node r2 x2 cf2) -- assumes r1 == r2
  | f x1 x2   = Node (r1+1) x1 (t2 `Cons` cf1)
  | otherwise = Node (r2+1) x2 (t1 `Cons` cf2)

skewLink :: (a -> a -> Bool) -> Tree a -> Tree a -> Tree a -> Tree a
skewLink f t0@(Node _ x0 cf0) t1@(Node r1 x1 cf1) t2@(Node r2 x2 cf2)
  | f x1 x0 && f x1 x2 = Node (r1+1) x1 (t0 `Cons` t2 `Cons` cf1)
  | f x2 x0 && f x2 x1 = Node (r2+1) x2 (t0 `Cons` t1 `Cons` cf2)
  | otherwise          = Node (r1+1) x0 (t1 `Cons` t2 `Cons` cf0)

ins :: (a -> a -> Bool) -> Tree a -> Forest a -> Forest a
ins _ t Nil = t `Cons` Nil
ins f t (t' `Cons` ts) -- assumes rank t <= rank t'
  | rank t < rank t' = t `Cons` t' `Cons` ts
  | otherwise = ins f (link f t t') ts

uniqify :: (a -> a -> Bool) -> Forest a -> Forest a
uniqify _ Nil = Nil
uniqify f (t `Cons` ts) = ins f t ts

unionUniq :: (a -> a -> Bool) -> Forest a -> Forest a -> Forest a
unionUniq _ Nil ts = ts
unionUniq _ ts Nil = ts
unionUniq f tts1@(t1 `Cons` ts1) tts2@(t2 `Cons` ts2) = case compare (rank t1) (rank t2) of
  LT -> t1 `Cons` unionUniq f ts1 tts2
  EQ -> ins f (link f t1 t2) (unionUniq f ts1 ts2)
  GT -> t2 `Cons` unionUniq f tts1 ts2

skewInsert :: (a -> a -> Bool) -> Tree a -> Forest a -> Forest a
skewInsert f t ts@(t1 `Cons` t2 `Cons`rest)
  | rank t1 == rank t2 = skewLink f t t1 t2 `Cons` rest
  | otherwise = t `Cons` ts
skewInsert _ t ts = t `Cons` ts
{-# INLINE skewInsert #-}

skewMeld :: (a -> a -> Bool) -> Forest a -> Forest a -> Forest a
skewMeld f ts ts' = unionUniq f (uniqify f ts) (uniqify f ts')
{-# INLINE skewMeld #-}

getMin :: (a -> a -> Bool) -> Forest a -> (Tree a, Forest a)
getMin _ (t `Cons` Nil) = (t, Nil)
getMin f (t `Cons` ts)
  | f (root t) (root t') = (t, ts)
  | otherwise            = (t', t `Cons` ts')
  where (t',ts') = getMin f ts
getMin _ Nil = error "Heap.getMin: empty forest"

splitForest :: Int -> Forest a -> Forest a -> Forest a -> (Forest a, Forest a, Forest a)
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

withList :: ([a] -> [a]) -> Heap a -> Heap a
withList _ Empty = Empty
withList f hp@(Heap _ leq _) = fromListWith leq (f (toList hp))
{-# INLINE withList #-}

splitWithList :: ([a] -> ([a],[a])) -> Heap a -> (Heap a, Heap a)
splitWithList _ Empty = (Empty, Empty)
splitWithList f hp@(Heap _ leq _) = both (fromListWith leq) (f (toList hp))
{-# INLINE splitWithList #-}

-- | explicit priority/payload tuples
data Entry p a = Entry { priority :: p, payload :: a }
  deriving (Read,Show,Data,Typeable)

instance Functor (Entry p) where
  fmap f (Entry p a) = Entry p (f a)
  {-# INLINE fmap #-}

instance Foldable (Entry p) where
  foldMap f (Entry _ a) = f a
  {-# INLINE foldMap #-}

instance Traversable (Entry p) where
  traverse f (Entry p a) = Entry p `fmap` f a
  {-# INLINE traverse #-}

-- instance Comonad (Entry p) where
--   extract (Entry _ a) = a
--   extend f pa@(Entry p _) Entry p (f pa)

instance Eq p => Eq (Entry p a) where
  (==) = (==) `on` priority
  {-# INLINE (==) #-}

instance Ord p => Ord (Entry p a) where
  compare = compare `on` priority
  {-# INLINE compare #-}
