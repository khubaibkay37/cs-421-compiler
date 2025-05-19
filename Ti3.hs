module Ti3 where

import CoreLanguage                -- CoreProgram, CoreExpr(..), CoreScDefn, IsRec
import Utils                        -- Addr, Heap, Assoc, hInitial, hAlloc, hLookup, mapAccuml, aLookup

-- Machine types for Mark 3: stack, dump, heap, globals
type TiStack   = [Addr]
type TiDump    = [TiStack]
type TiHeap    = Heap Node
type TiGlobals = Assoc Name Addr
type TiState   = (TiStack, TiDump, TiHeap, TiGlobals)

-- Primitive operations for arithmetic

data Primitive = Add | Sub | Mul | Div | Eq | Lt
  deriving (Show)
showHeap :: Heap Node -> String
showHeap (_, as) = unlines [ show addr ++ ": " ++ show node | (addr, node) <- as ]
-- Heap nodes for Mark 3: application, SC, number, indirection, primitive
data Node
  = NAp    Addr Addr           -- application node
  | NSupercomb Name [Name]     -- super-combinator template
  | NNum   Int                 -- integer literal
  | NInd   Addr                -- indirection node
  | NPrim  Name Primitive      -- primitive node
  deriving (Show)

-- | Build initial heap and globals from SC definitions and primitives
buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap progDefs = (heap2, globals)
  where
    -- 1) Super-combinators
    scDefs         = preludeDefs ++ progDefs
    (heap1, scAddrs) = mapAccuml allocateSc hInitial scDefs
    scNames        = [name | (name,_,_) <- scDefs]
    scAssoc        = zip scNames scAddrs

    -- 2) Primitives
    primList       = [("+",Add),("-",Sub),("*",Mul),("/",Div),("==",Eq),("<",Lt)]
    allocPrim (h,gs) (nm,pr)
      = let (h',a) = hAlloc h (NPrim nm pr)
        in (h', (nm,a):gs)
    (heap2, primAssoc) = foldl allocPrim (heap1,[]) primList

    -- 3) globals: primitives first (shadow SCs), then SCs
    globals        = primAssoc ++ scAssoc

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, Addr)
allocateSc heap (name,args,_) = hAlloc heap (NSupercomb name args)

-- | Initialise the machine state: stack with 'main' address
type ProgramDefs = [CoreScDefn]
initialTiState :: ProgramDefs -> TiState
initialTiState progDefs = ([addrMain], [], heap, globals)
  where
    (heap, globals) = buildInitialHeap progDefs
    addrMain        = aLookup globals "main" (error "main is not defined")

-- | Evaluate to a list of states
eval :: CoreProgram -> [TiState]
eval prog = st0 : rest st0
  where
    defs = preludeDefs ++ prog
    st0  = initialTiState defs
    rest st
      | tiFinal st = []
      | otherwise  = let st' = step defs st in st' : rest st'

-- | Final when stack has single address pointing to a number
tiFinal :: TiState -> Bool
tiFinal ([a], [], heap, _) =
  case hLookup heap a of NNum _ -> True; _ -> False
tiFinal _ = False

-- | Perform one transition
type StepFn = ProgramDefs -> TiState -> TiState
step :: ProgramDefs -> TiState -> TiState
step defs state@(stack, dump, heap, globals) =
  let addr = head stack
      node = hLookup heap addr
  in dispatch defs node state

-- | Dispatch rules: Unwind, Indirection, SC-update, Primitive
dispatch :: ProgramDefs -> Node -> TiState -> TiState

-- 1) Unwind: application node, push function part
dispatch _ (NAp a1 _) (stack, dump, heap, globals)
  = (a1 : stack, dump, heap, globals)

-- 2) Indirection: follow it
dispatch _ (NInd a) (stack, dump, heap, globals)
  = (a : stack, dump, heap, globals)

-- 3) Super-combinator: instantiate and update graph
dispatch defs (NSupercomb sc args) (stack, dump, heap, globals)
  | length stack - 1 < length args = error $ "Too few args for super-combinator " ++ sc
  | otherwise =
      let n         = length args
          root      = head stack
          apAddrs   = take n (tail stack)
          argAddrs  = [ case hLookup heap a of NAp _ a2 -> a2; _ -> error "Expected NAp" |
                         a <- apAddrs ]
          env       = zip args argAddrs
          body      = findScBody sc defs
          (heap1,r) = instantiate body heap globals env
          heap2     = hUpdate heap1 root (NInd r)
          stack'    = r : drop (n+1) stack
      in (stack', dump, heap2, globals)

-- 4) Primitive application (two args)
dispatch _ (NPrim nm pr) (stack, dump, heap, globals)
  | hasNArgs 2 stack heap =
      let [a1,a2] = fetchArgAddrs 2 stack heap
          NNum v1  = hLookup heap a1
          NNum v2  = hLookup heap a2
          res      = applyPrim pr v1 v2
          (heap1,r)= hAlloc heap (NNum res)
          stack'   = r : drop 3 stack
      in (stack', dump, heap1, globals)
  | otherwise = error $ "Primitive '" ++ nm ++ "' applied to wrong args"

-- Fallback
dispatch _ _ _ = error "Cannot dispatch this node in Mark 3"

-- | Update a heap node at a given address
hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (n, as) addr nd = (n, map upd as)
  where
    upd (a,x)
      | a == addr = (a, nd)
      | otherwise = (a, x)

-- | Instantiate expressions: variables, numbers, applications, let/letrec
instantiate :: CoreExpr -> TiHeap -> TiGlobals -> [(Name,Addr)] -> (TiHeap, Addr)
instantiate (ENum n)   heap _       _   = hAlloc heap (NNum n)
instantiate (EVar v)   heap globals env
  = case lookup v env of
      Just a  -> (heap, a)
      Nothing -> (heap, aLookup globals v (error $ "Unbound global: " ++ v))
instantiate (EAp e1 e2) heap globals env
  = let (h1,a1) = instantiate e1 heap    globals env
        (h2,a2) = instantiate e2 h1       globals env
    in hAlloc h2 (NAp a1 a2)
-- non-recursive let
instantiate (ELet False binds body) heap globals env
  = let alloc h (_,e)  = instantiate e h globals env
        (heap1,addrs) = mapAccuml alloc heap binds
        env'          = zip (map fst binds) addrs ++ env
    in instantiate body heap1 globals env'
-- recursive let
instantiate (ELet True binds body) heap globals env
  = let names         = map fst binds
        allocInd h _  = hAlloc h (NInd (-1))
        (heap1,addrs) = mapAccuml allocInd heap binds
        env'          = zip names addrs ++ env
        heap2         = foldl (\h ((_,e),a) -> fst $ instantiate e h globals env')
                              heap1 (zip binds addrs)
    in instantiate body heap2 globals env'
-- catch-all
instantiate a _ _ _ = error $ "Cannot instantiate this expression in Mark 3" ++ show a

-- | Helpers for primitive support
hasNArgs :: Int -> TiStack -> TiHeap -> Bool
hasNArgs n stk hp = length stk > n && all isAp (take n $ tail stk)
  where isAp a = case hLookup hp a of NAp _ _ -> True; _ -> False

fetchArgAddrs :: Int -> TiStack -> TiHeap -> [Addr]
fetchArgAddrs n stk hp = [ a2 | ap <- take n (tail stk), NAp _ a2 <- [hLookup hp ap] ]

applyPrim :: Primitive -> Int -> Int -> Int
applyPrim Add x y = x + y
applyPrim Sub x y = x - y
applyPrim Mul x y = x * y
applyPrim Div x y = x `div` y
applyPrim Eq  x y = if x == y then 1 else 0
applyPrim Lt  x y = if x <  y then 1 else 0

-- | Find super-combinator body from definitions
findScBody :: Name -> ProgramDefs -> CoreExpr
findScBody sc defs =
  case [body | (n,_,body) <- defs, n == sc] of
    b:_ -> b
    []  -> error $ "Super-combinator not found: " ++ sc

-- | Pretty-print state for debugging
displayState3 :: TiState -> String
displayState3 (stk,_,hp,gl)
  = "Stack: " ++ show stk ++ "\n"
  ++ "Heap:\n" ++ showHeap hp
  ++ "Globals: " ++ show gl ++ "\n"

-- | Run and print states then final result
test2 :: CoreProgram -> IO ()
test2 prog = mapM_ (putStrLn . displayState3) (eval prog)

-- | Example for Mark 3: local let and arithmetic
exampleProg2 :: CoreProgram
exampleProg2 =
  [ ("main", [], ELet True
        [("double", ELam ["x"] (EAp (EAp (EVar "+") (EVar "x")) (EVar "x")))]
        (EAp (EVar "double") (ENum 5)))
  ]

-- | Default test
test :: IO ()
test = test2 exampleProg2

-- | Non-recursive let:
--   let y = 10 in y + 5  ===> 15
exampleLetNonRec :: CoreProgram
exampleLetNonRec =
  [ ("main", [], 
      ELet False [ ("y", ENum 10) ]
                 (EAp (EAp (EVar "+") (EVar "y")) (ENum 5))
    )
  ]

-- | Recursive let:
--   letrec id = \x -> x in id 7  ===> 7
exampleLetRec :: CoreProgram
exampleLetRec =
  [ ("main", [], 
      ELet True  [ ("id", ELam ["x"] (EVar "x")) ]
                 (EAp (EVar "id") (ENum 7))
    )
  ]
