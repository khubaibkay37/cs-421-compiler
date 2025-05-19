module Ti1 where

import CoreLanguage                -- CoreProgram, CoreExpr, CoreScDefn, preludeDefs
import Utils                        -- Addr, Heap, Assoc, hInitial, hAlloc, hLookup, mapAccuml, aLookup
import Control.Monad                -- for forM_

-- Machine types
-- Stack of node addresses, heap and globals
type TiStack   = [Addr]
type TiDump    = [TiStack]
type TiHeap    = Heap Node
type TiGlobals = [(Name, Addr)]
type TiState   = (TiStack, TiDump, TiHeap, TiGlobals, [CoreScDefn])

-- Heap nodes for Mark 1
data Node
  = NAp Addr Addr             -- application node
  | NSupercomb Name [Name]    -- supercombinator template
  | NNum Int                  -- integer literal
  deriving (Show)

-- Build initial heap and global address map, including prelude + program
buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap defs = (heap', globals)
  where
    names          = [name | (name,_,_) <- defs]
    (heap', addrs) = mapAccuml allocateSc hInitial defs
    globals        = zip names addrs

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, Addr)
allocateSc heap (name, args, _) = hAlloc heap (NSupercomb name args)

-- Initialise machine state: stack at 'main'
initialTiState :: CoreProgram -> TiState
initialTiState program = ([addrMain], [], heap0, globals, program)
  where
    (heap0, globals) = buildInitialHeap (preludeDefs ++ program)
    addrMain         = aLookup globals "main" (error "main is not defined")

-- Evaluate from initial to final state sequence
eval :: CoreProgram -> [TiState]
eval program = state0 : rest state0
  where
    state0 = initialTiState program
    rest st
      | tiFinal st = []
      | otherwise  = let st' = step st in st' : rest st'

-- Final when stack points at NNum
tiFinal :: TiState -> Bool
tiFinal ([addr], [], heap, _, _) =
  case hLookup heap addr of
    NNum _ -> True
    _      -> False
tiFinal _ = False

-- Single transition
step :: TiState -> TiState
step state@(stack, dump, heap, globals, progDefs) =
  dispatch (hLookup heap (head stack)) state

-- Dispatch the two Mark 1 rules
dispatch :: Node -> TiState -> TiState

-- Unwind: application node, push function part
dispatch (NAp a1 _) (stack, dump, heap, globals, progDefs) =
  (a1 : stack, dump, heap, globals, progDefs)

-- Supercombinator: instantiate its body
dispatch (NSupercomb sc args) (stack, dump, heap, globals, progDefs)
  | length stack - 1 < length args = error $ "Too few args for supercombinator " ++ sc
  | otherwise =
      let apAddrs  = take (length args) (tail stack)
          argAddrs = [ case hLookup heap ap of
                         NAp _ a2 -> a2
                         _        -> error "Malformed application node"
                     | ap <- apAddrs ]
          env      = zip args argAddrs
          body     = findScBody sc (preludeDefs ++ progDefs)
          (heap', rootAddr) = instantiate body heap globals env
          newStack = rootAddr : drop (length args + 1) stack
      in  (newStack, dump, heap', globals, progDefs)

dispatch _ _ = error "Cannot dispatch this node in Mark 1"

-- Instantiate CoreExpr into heap, with locals and globals
type Env = [(Name, Addr)]
instantiate :: CoreExpr -> TiHeap -> TiGlobals -> Env -> (TiHeap, Addr)
instantiate (ENum n)   heap _       _   = hAlloc heap (NNum n)
instantiate (EVar v)   heap globals env
  = case lookup v env of
      Just addr -> (heap, addr)
      Nothing   -> (heap, aLookup globals v (error $ "Unbound global: " ++ v))
instantiate (EAp e1 e2) heap globals env
  = let (h1, a1) = instantiate e1 heap    globals env
        (h2, a2) = instantiate e2 h1       globals env
    in  hAlloc h2 (NAp a1 a2)
instantiate _ _ _ _ = error "Cannot instantiate this expression in Mark 1"

-- Lookup supercombinator body
findScBody :: Name -> [CoreScDefn] -> CoreExpr
findScBody name defs =
  case [body | (n, _, body) <- defs, n == name] of
    b : _ -> b
    []    -> error $ "Supercombinator not found: " ++ name

-- Debug printing
showState :: TiState -> String
showState (stack, _, heap, globals, _) =
  "Stack: " ++ show stack ++ "\n" ++
  "Heap:\n" ++ showHeap heap ++
  "Globals: " ++ show globals ++ "\n"

showHeap :: Heap Node -> String
showHeap (_, as) = unlines [ show addr ++ ": " ++ show node | (addr, node) <- as ]

-- | Run and print each state, then final result
run :: CoreProgram -> IO ()
run program = do
  let states = eval program
  forM_ (zip [0..] states) $ \(i, st) -> do
    putStrLn $ "State " ++ show i
    putStrLn $ showState st
  let (stack, _, heap, _, _) = last states
      [finalAddr] = stack
      NNum result = hLookup heap finalAddr
  putStrLn $ "Final result = " ++ show result

-- A tiny example
exampleProg0 :: CoreProgram
exampleProg0 =
  [ ("I",    ["x"], EVar "x")
  , ("main", [],     EAp (EVar "I") (ENum 69))
  ]

-- Default test
test :: IO ()
test = run exampleProg0
