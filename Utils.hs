module Utils
  ( Addr
  , Heap
  , Assoc
  , hInitial
  , hAlloc
  , hLookup
  , mapAccuml
  , aLookup
  ) where

-- A simple heap implementation: addresses are Ints
-- Heap metadata is the next free address and an association list

type Addr = Int

type Heap a = ( Int               -- next free address
              , [(Addr, a)]       -- allocated nodes
              )

type Assoc k v = [(k, v)]

-- | An empty heap
hInitial :: Heap a
hInitial = (0, [])

-- | Allocate a new node, returning the updated heap and its address
hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (next, as) node =
  let addr = next
      heap' = (next + 1, (addr, node) : as)
  in  (heap', addr)

-- | Lookup a node by address, erroring if not found
hLookup :: Heap a -> Addr -> a
hLookup (_, as) addr =
  case lookup addr as of
    Just node -> node
    Nothing   -> error $ "Heap.lookup: address " ++ show addr ++ " not found"

-- | Map over a list, threading an accumulator (e.g., heap)
mapAccuml :: (h -> x -> (h, y)) -> h -> [x] -> (h, [y])
mapAccuml _ acc []     = (acc, [])
mapAccuml f acc (x:xs) =
  let (acc', y)    = f acc x
      (acc'', ys) = mapAccuml f acc' xs
  in  (acc'', y : ys)

-- | Lookup in an association list with a default on failure
aLookup :: Eq k => Assoc k v -> k -> v -> v
aLookup [] _ def = def
aLookup ((k,v):kvs) key def
  | k == key  = v
  | otherwise = aLookup kvs key def
