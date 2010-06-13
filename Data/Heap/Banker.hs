module Data.Deque.Banker (module Deque, Deque) where

import Data.Monoid (Monoid(mappend, mempty), Dual(Dual,getDual))

import Prelude hiding (head,tail,last,init,null,reverse)

data ViewL f a = a :< f a | EmptyL
    deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable)

data ViewR f a = f a :> a | EmptyR
    deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable)

c :: Int
c = 3

data Deque a = Deque {-# UNPACK #-} !Int {-# UNPACK #-} !Int [a] [a]

instance Functor Deque where
    fmap f (Deque ll lr l r) = Deque ll (fmap f l) lr (fmap f r)

instance Foldable Deque where
    foldMap f (Deque ll lr l r) = foldMap f l `mappend` getDual (foldMap (Dual . f) r)

traverseReverse :: Applicative t => (a -> t b) -> [a] -> t [b]
traverseReverse (a : as) = flip (:) <$> traverseReverse f as <*> f a
traverseReverse [] = pure []

instance Traversable Deque where
    traverse f (Deque ll lr l r) = Deque ll lr <$> traverse f l <*> traverseReverse f r

check :: Int -> [a] -> Int -> [a] -> Deque a 
check lf lr f r =
    | lf > c*lr + 1 = Deque i j f' r'
    where   
        l = lf+lr 
        i = l `div` 2
        j = l - i
        (f',f'') = splitAt i f
        r' = r ++ reverse f''
check lf f lr r | lr > c*lf + 1 = Deque i j f' r' 
    where 
        l = lf+lr 
        j = l `div` 2
        i = l-j
        (r',r'') = splitAt j r
        f' = f ++ reverse r''
check ls lr f r = Deque lf lr f r

-- /O(1)/
empty :: Deque a 
empty = Deque 0 [] 0 []

-- /O(1)/
null :: Deque a -> Bool
null (Deque lf lr _ _) = lf + lr == 0

-- /O(1)/ amortized
cons :: a -> Deque a -> BankerDeque a 
cons x (Deque lf lr f r) = check (lf+1) lr (x:f) r

-- /O(1)/ amortized
head :: Deque a -> a
head (Deque _ _ (x:_) _) = x
head (Deque _ _ [] [x]) = x
head (Deque _ _ [] _) = error "Deque.head: empty deque"

-- /O(1)/ amortized
tail :: Deque a -> Deque a
tail (Deque lf lr (_:f') r) = check (lf-1) lr f' r
tail (Deque _ _ [] [x]) = empty
tail (Deque _ _ [] _) = error "Deque.tail: empty deque"

-- /O(1)/ amortized
snoc :: Deque a -> a -> Deque a 
snoc (Deque lf lr f r) x = check lf (lr+1) f (x:r)

-- /O(1)/ amortized
last :: Deque a -> a 
last (Deque _ _ [x] [])  = x
last (Deque _ _ _ [])    = error "Deque.last: empty deque"
last (Deque _ _ _ (x:_)) = x

-- /O(1)/ amortized
init :: Deque a -> Deque a 
init (Deque _ lr f (x:r')) = check lf (lr-1) f r'
init (Deque _ _ [x] []) = empty
init (Deque _ _ _ []) = error "Deque.init: empty deque"

-- /O(1)/
reverse :: Deque a -> Deque a 
reverse (Deque lf lr f r) = Deque lr lf r f 


