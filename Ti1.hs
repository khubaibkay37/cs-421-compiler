module Ti1 where

import CoreLanguage
import Utils

-- Machine types
type TiStack   = [Addr]
type TiDump    = [TiStack]
type TiHeap    = Heap Node
type TiGlobals = [(Name, Addr)]
type TiState   = (TiStack, TiDump, TiHeap, TiGlobals, [CoreScDefn])

-- Heap nodes (Mark 1 only needs NAp, NSupercomb, NNum)
data Node
  = NAp Addr Addr
  | NSupercomb Name [Name]
  | NNum Int
  deriving Show

-- | Build the initial heap and globals from a list of supercombinator defs
buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap defs
  = (heap', globals)
  where
    names          = [name | (name, _, _) <- defs]
    (heap', addrs) = mapAccuml allocateSc hInitial defs
    globals        = zip names addrs

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, Addr)
allocateSc heap (name, args, _)
  = hAlloc heap (NSupercomb name args)

-- | Initial machine state: stack points at “main”
initialTiState :: CoreProgram -> TiState
initialTiState program
  = ([addrMain], [], heap0, globals, program)
  where
    (heap0, globals) = buildInitialHeap (preludeDefs ++ program)
    addrMain         = aLookup globals "main"
                         (error "main is not defined")

-- | The driver: produce the sequence of states from initial to final
eval :: CoreProgram -> [TiState]
eval program = state0 : rest state0
  where
    state0 = initialTiState program
    rest st
      | tiFinal st = []
      | otherwise  = let st' = step st in st' : rest st'

-- | Final when stack points at a NNum and dump is empty
tiFinal :: TiState -> Bool
tiFinal ([addr], [], heap, _, _)
  = case hLookup heap addr of
      NNum _ -> True
      _      -> False
tiFinal _ = False

-- | One transition
step :: TiState -> TiState
step state@(stack, dump, heap, globals, progDefs) =
  dispatch (hLookup heap (head stack)) state

-- | Apply the two Mark 1 rules: Unwind and Supercomb
dispatch :: Node -> TiState -> TiState

-- Unwind: if top of stack is NAp, push the function address
dispatch (NAp a1 _) (stack, dump, heap, globals, progDefs)
  = (a1 : stack, dump, heap, globals, progDefs)

-- Supercombinator step
dispatch (NSupercomb sc args) (stack, dump, heap, globals, progDefs)
  | length stack - 1 < length args
    = error $ "Too few args for supercombinator " ++ sc
  | otherwise
    = (newStack, dump, heap', globals, progDefs)
  where
    -- Extract the argument addresses from the stack
    argAddrs          = take (length args) (tail stack)
    env               = zip args argAddrs

    -- Lookup the body in our global program defs (prelude ++ user)
    body              = findScBody sc (preludeDefs ++ progDefs)

    -- Instantiate with access to both locals *and* globals
    (heap', rootAddr) = instantiate body heap globals env

    -- New stack: root of instantiated graph replaces old application
    newStack          = rootAddr : drop (length args + 1) stack

-- | Instantiate a CoreExpr into the heap, returning (heap', addr)
instantiate
  :: CoreExpr
  -> TiHeap
  -> TiGlobals
  -> [(Name, Addr)]
  -> (TiHeap, Addr)

instantiate (ENum n) heap _ _ =
  hAlloc heap (NNum n)

-- FIRST try the local env; otherwise fall back to globals
instantiate (EVar v) heap globals env
  = case lookup v env of
      Just addr -> (heap, addr)
      Nothing   -> (heap, aLookup globals v
                              (error $ "Unbound global: " ++ v))

instantiate (EAp e1 e2) heap globals env
  = let (heap1, a1) = instantiate e1 heap    globals env
        (heap2, a2) = instantiate e2 heap1   globals env
    in  hAlloc heap2 (NAp a1 a2)

-- | Find the body of a supercombinator from the defns
findScBody :: Name -> [CoreScDefn] -> CoreExpr
findScBody name defs =
  case [ body | (n, _, body) <- defs, n == name ] of
    b : _ -> b
    []    -> error $ "Supercombinator not found: " ++ name

-- | Pretty-print a state for testing
showState :: TiState -> String
showState (stack, _, heap, globals, _)
  =  "Stack: "  ++ show stack  ++ "\n"
  ++ "Heap:\n" ++ show heap
  ++ "Globals: " ++ show globals ++ "\n"

-- | A tiny example and tester
exampleProg1 :: CoreProgram
exampleProg1 =
  [ ("b",    ["x"], (ENum 5))
      , ("main", [],   EAp (EVar "b") (ENum 3))
  ]

test :: IO ()
test = mapM_ (putStrLn . showState) (eval exampleProg1)
