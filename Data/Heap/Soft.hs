module Data.Heap.Soft where

-- administrivia

newtype Tagged e a = Tagged { unTagged :: a } 

instance Functor (Tagged e) where
    fmap f (Tagged e) = Tagged (f e) 

instance Applicative (Tagged e) where
    pure = Tagged
    Tagged a <*> Tagged b = Tagged (a b)

instance Monad (Tagged e) where
    return = Tagged
    Tagged a >>= f = f a 

data Rank e = Rank { rankNum :: {#- UNPACK #-} !Int, rankSize :: {-# UNPACK #-} !Int }

mkRank :: Int -> Int -> Tagged e (Rank e)
mkRank a b = Tagged (Rank a b)

nextRank :: Epsilon e => Rank e -> Rank e
nextRank (Rank k n) = unTagged $ do
        r <- rho 
        mkRank (k+1) $ 
            if k < r 
            then 1 
            else ceiling (fromIntegral n * 3 / 2)
{-# INLINE nextRank #-}

rankOne :: Rank e 
rankOne = Rank 1 1 

class Epsilon e where
    epsilon :: Tagged e Double
    rho :: Tagged e Int
    rho = do
        e <- epsilon
        return (ceiling (logBase 2 (1 / e)) + 5)

data OneHalf = OneHalf 
instance Epsilon OneHalf where
    epsilon = pure (1/2)

data OneThird = OneThird
instance Epsilon OneThird where
    epsilon = pure (1/3)

data OneFourth = OneFourth
instance Epsilon OneFourth where
    epsilon = pure (1/4)

data Node e a = Bin 
    { rankTuple :: {-# UNPACK #-} !(Rank e)
    , listSize :: {-# UNPACK #-} !Int 
    , ckey :: a 
    , list :: ![a] 
    , left :: !(Node e a) 
    , right :: !(Node e a) 
    } | Tip

data Tree e a = Tree
    { suf :: !Tree e a 
      sufMin :: !Tree e a 
    } | NoTree 

next :: Tree e a -> Tree e a 
next 

rank :: Node e a -> Int
rank = rankNum . rankTuple

size :: Node e a -> Int
size = rankSize . rankTuple

data Heap e a = Heap (a -> a -> Bool) a [Tree e a] | Empty

instance Functor (Tree e) where
    fmap f (Bin r i as l r) = Bin r i (fmap f as) (fmap f l) (fmap f r)


sift x (Node s l 

empty :: Heap e a 
insert :: a -> Heap e a -> Heap e a 
                
