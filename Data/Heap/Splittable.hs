module Data.Deque.Splittable where

data Split a = 
    = Empty
    | Single a 
    | Deep (Split a) !(Seq a) (Split a) 

-- /O(log n)/
cons :: a -> Split a -> Split a 
cons a Empty = Single a
cons a (Single b) = sa `seq` sb `seq` Deep sa (sa >< sb) sb
    where sa = singleton a
          sb = singleton b
cons a (Deep l m r) 
    | size l <= size r = Deep (cons a l) (cons a m) r
    | otherwise = Deep (cons a l') (cons a m) (cons b r)
        where l' :> b = l

-- /O(1)/
toSeq :: Split a -> Seq a
toSeq (Split _ m _) = m

-- /O(1)/
split :: Split a -> (Split a, Split a)
split Empty = (Empty, Empty)
split s@(Single a) = (Single a, Empty)
split (Deep l _ r) = (l, r)

-- /O(log n)/
uncons Empty = Nothing
uncons (Single a) = Just (a,Empty)
uncons (Deep l m r)
    | size l >= size r = Just (a, Deep l' m r)
    | size r == 1 = Just (a, Single b)
    | otherwise = Just (a, Deep l'' m' (cons b r))
    where a :< m' = viewl m
          l'' :> b = viewl l'
          l' = tail l

-- /O(n log n)/
fromSeq :: Seq a -> Split a 
fromSeq m | sm == 0   = Empty
          | sm == 1   = Single (headSeq sm)
          | otherwise = Deep (fromSeq l) m (fromSeq r)
    sm = Seq.size m 
    (l,r) = split (sm `div` 2) m
