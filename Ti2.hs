module Ti2 where

import CoreLanguage                -- CoreProgram, CoreExpr, CoreScDefn, preludeDefs
import Utils                        -- Addr, Heap, Assoc, hInitial, hAlloc, hLookup, mapAccuml, aLookup
import Control.Monad                -- for forM_

-- Type synonyms for the machine state
-- Stack, dump, heap, and globals

type TiStack   = [Addr]
type TiDump    = [TiStack]
type TiHeap    = Heap Node
type TiGlobals = Assoc Name Addr
type TiState   = (TiStack, TiDump, TiHeap, TiGlobals)

-- Primitives supported in Mark 2

data Primitive = Add | Sub | Mul | Div | Equals | Lt
  deriving (Show)

-- Heap nodes for Mark 2: adds NPrim to Mark 1 nodes

data Node
  = NAp Addr Addr             -- application node
  | NSupercomb Name [Name]    -- supercombinator template
  | NNum Int                  -- integer literal
  | NPrim Name Primitive      -- primitive node
  deriving (Show)

-- | Build the initial heap and global address map
--   Allocates supercombinators (prelude ++ program) then primitives
buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap programDefs = (heap2, globals)
  where
    -- 1) Supercombinators
    allScDefs        = preludeDefs ++ programDefs
    (heap1, scAddrs) = mapAccuml allocateSc hInitial allScDefs
    scNames          = [name | (name,_,_) <- allScDefs]

    -- 2) Primitives
    primList = [("+",Add), ("-",Sub), ("*",Mul), ("/",Div), ("==",Equals), ("<",Lt)]
    allocPrim (h, gs) (nm, pr)
      = let (h', addr) = hAlloc h (NPrim nm pr)
        in  (h', (nm, addr):gs)
    (heap2, primAssoc) = foldl allocPrim (heap1, []) primList

    -- 3) Globals: primitives first (so they shadow SCs if names collide), then SCs
    globals = primAssoc ++ zip scNames scAddrs

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, Addr)
allocateSc heap (name, args, _) = hAlloc heap (NSupercomb name args)

-- | Initialize the machine state for a given program
type ProgramDefs = [CoreScDefn]
initialTiState :: ProgramDefs -> TiState
initialTiState programDefs = ([addrMain], [], heap, globals)
  where
    (heap, globals) = buildInitialHeap programDefs
    addrMain        = aLookup globals "main" (error "main is not defined")

-- | Evaluate a Core program to the sequence of TI states
eval :: CoreProgram -> [TiState]
eval programDefs =
  let progDefs = preludeDefs ++ programDefs
      state0   = initialTiState progDefs
  in  state0 : rest progDefs state0
  where
    rest defs st
      | tiFinal st = []
      | otherwise  = let st' = step defs st
                     in  st' : rest defs st'

-- | Check for final state: single addr pointing to NNum
--   Dump is unused in Marks 1 & 2
tiFinal :: TiState -> Bool
tiFinal ([addr], [], heap, _) =
  case hLookup heap addr of
    NNum _ -> True
    _      -> False
tiFinal _ = False

-- | Perform one transition, given the program definitions
step :: ProgramDefs -> TiState -> TiState
step defs state@(stack, dump, heap, globals) =
  dispatch defs (hLookup heap (head stack)) state

-- | Dispatch for unwind, supercombinator, or primitive
dispatch :: ProgramDefs -> Node -> TiState -> TiState

-- 1) Unwind: on an application node, push the function part
dispatch _ (NAp a1 _) (stack, dump, heap, globals)
  = (a1 : stack, dump, heap, globals)

-- 2) Supercombinator: instantiate its body
dispatch defs (NSupercomb sc args) (stack, dump, heap, globals)
  | length stack - 1 < length args
    = error $ "Too few args for supercombinator " ++ sc
  | otherwise
    = let n        = length args
          apAddrs  = take n (tail stack)
          argAddrs = [ case hLookup heap ap of
                         NAp _ a2 -> a2
                         _        -> error "Malformed application node"
                     | ap <- apAddrs ]
          env      = zip args argAddrs
          body     = findScBody sc defs
          (heap', root) = instantiate body heap globals env
          newStack = root : drop (n + 1) stack
      in (newStack, dump, heap', globals)

-- 3) Primitive: two-argument built-in
dispatch _ (NPrim name prim) (stack, dump, heap, globals)
  | hasNArgs 2 stack heap
    = let [a1,a2]   = fetchArgAddrs 2 stack heap
          NNum v1   = hLookup heap a1
          NNum v2   = hLookup heap a2
          result    = applyPrim prim v1 v2
          (heap', r)= hAlloc heap (NNum result)
          newStack  = r : drop 3 stack
      in (newStack, dump, heap', globals)
  | otherwise
      = error $ "Primitive '" ++ name ++ "' applied to wrong number of args"

-- Safety net
dispatch _ _ _ = error "Cannot dispatch this node in Mark 2"

-- | Check for saturation of N application nodes on the stack
hasNArgs :: Int -> TiStack -> TiHeap -> Bool
hasNArgs n stack heap =
  length stack > n && all isAp (take n $ tail stack)
  where isAp addr = case hLookup heap addr of NAp _ _ -> True; _ -> False

-- | Fetch the second pointers of n application nodes on the stack
type Env = [(Name, Addr)]
fetchArgAddrs :: Int -> TiStack -> TiHeap -> [Addr]
fetchArgAddrs n stack heap =
  [ a2 | apAddr <- take n (tail stack)
       , NAp _ a2 <- [hLookup heap apAddr] ]

-- | Apply a primitive operation to two Ints
applyPrim :: Primitive -> Int -> Int -> Int
applyPrim Add x y = x +  y
applyPrim Sub x y = x -  y
applyPrim Mul x y = x *  y
applyPrim Div x y = x `div` y
applyPrim Equals  x y = if x == y then 1 else 0
applyPrim Lt  x y = if x <  y then 1 else 0

-- | Instantiate a Core expression into the heap
instantiate :: CoreExpr -> TiHeap -> TiGlobals -> Env -> (TiHeap, Addr)
instantiate (ENum n)   heap _       _   = hAlloc heap (NNum n)
instantiate (EVar v)   heap globals env
  = case lookup v env of
      Just addr -> (heap, addr)
      Nothing   -> (heap, aLookup globals v (error $ "Unbound global: " ++ v))
instantiate (EAp e1 e2) heap globals env
  = let (h1, a1) = instantiate e1 heap    globals env
        (h2, a2) = instantiate e2 h1       globals env
    in hAlloc h2 (NAp a1 a2)
instantiate _ _ _ _ = error "Cannot instantiate this expression in Mark 2"

-- | Look up the body of a supercombinator
findScBody :: Name -> ProgramDefs -> CoreExpr
findScBody name defs =
  case [ body | (n,_,body) <- defs, n == name ] of
    b : _ -> b
    []    -> error $ "Supercombinator not found: " ++ name

showHeap :: Heap Node -> String
showHeap (_, as) = unlines [ show addr ++ ": " ++ show node | (addr, node) <- as ]

-- | Pretty-print a state
displayState :: TiState -> String
displayState (stack, _, heap, globals) =
  "Stack: " ++ show stack ++ "\n" ++
  "Heap:\n" ++ showHeap heap ++
  "Globals: " ++ show globals ++ "\n"

-- | Run a program: print each state then final result
run2 :: CoreProgram -> IO ()
run2 prog = do
  let states = eval prog
  forM_ (zip [0..] states) $ \(i, st) -> do
    putStrLn $ "State " ++ show i
    putStrLn $ displayState st
  let (stk,_,heap,_) = last states
      [addr]         = stk
      NNum result    = hLookup heap addr
  putStrLn $ "Final result = " ++ show result

-- | Example program using '+'
exampleProg2 :: CoreProgram
exampleProg2 =
  [ ("main",   [], EAp (EVar "double") (ENum 21))
  , ("double", ["x"], EAp (EAp (EVar "+") (EVar "x")) (EVar "x"))
  ]

-- | Default test for Mark 2
test2 :: IO ()
test2 = run2 exampleProg2