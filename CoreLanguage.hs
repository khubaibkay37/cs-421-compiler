module CoreLanguage where
import Control.Applicative
import Data.List (intersperse)
import Data.Char (isAlpha, isDigit)

type Name = String
type IsRec = Bool
type CoreExpr = Expr Name
type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name
type CoreProgram = [CoreScDefn]
type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name

data Expr a
    = EVar Name -- variable name
    | ENum Int -- number, int only supported
    | EConstr Int Int -- Pack{tag, arity}
    | EAp (Expr a) (Expr a) -- Application (function . argument)
    | ELet IsRec [(a, Expr a)] (Expr a) -- Let statement , is recursive, [statements] in (final) 
    | ECase (Expr a) [Alter a] -- case of what [cases]
    | ELam [a] (Expr a) -- lambda abstraction [parameters] function
    deriving (Show)

-- Define Recursive and non recursive
recursive, nonRecursive :: IsRec
recursive = True
nonRecursive = False

bindersOf :: [(a, b)] -> [a]
bindersOf defs = [name | (name, _) <- defs]

rhssOf :: [(a, b)] -> [b]
rhssOf defs = [rhs | (_, rhs) <- defs]

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _) = True
isAtomicExpr (ENum _) = True
isAtomicExpr _ = False
-- ======================

-- Standard Prelude Definitions

-- ======================



preludeDefs :: CoreProgram
preludeDefs =
    [ ("I", ["x"], EVar "x")
    , ("K",["x", "y"], EVar "x")
    , ("K1",["x", "y"], EVar "y")
    , ("S",["f", "g", "x"], EAp (EAp (EVar "f") (EVar "x")) (EAp (EVar "g") (EVar "x")))
    , ("compose", ["f", "g", "x"], EAp (EVar "f") (EAp (EVar "g") (EVar "x")))
    , ("twice", ["f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f"))
    ]

-- ====================
-- Pretty Printer
-- ====================

-- Pretty Printing Interface
pprint :: CoreProgram -> String
pprint prog = iDisplay (pprProgram prog)

-- ISeq Type for Pretty Printing
data ISeq = INil
          | IStr String
          | IAppend ISeq ISeq
          | IIndent ISeq
          | INewline

-- aliasing for ease, abstraction
iNil = INil
iStr = IStr
iAppend = IAppend
iIndent = IIndent
iNewline = INewline

-- join together
iConcat :: [ISeq] -> ISeq
iConcat = foldr iAppend iNil
-- join with separator
iInterleave :: ISeq -> [ISeq] -> ISeq
iInterleave sep = iConcat . intersperse sep



iDisplay :: ISeq -> String
-- Starting, indent blocks 0 indent, new line 0 indent
iDisplay seq = flatten 0 [(seq, 0)]

flatten :: Int -> [(ISeq, Int)] -> String
flatten _ [] = ""
flatten col ((INewline, indent):rest) =
    '\n' : space indent ++ flatten indent rest
flatten col ((IIndent seq, _):rest) =
    flatten col ((seq, col):rest)
flatten col ((INil, _):rest) =
    flatten col rest
flatten col ((IStr s, _):rest) =
    s ++ flatten (col + length s) rest
flatten col ((IAppend s1 s2, indent):rest) =
    flatten col ((s1, indent):(s2, indent):rest)

space :: Int -> String
space n = replicate n ' '

iNum :: Int -> ISeq
iNum n = IStr (show n)

-- Use at least width length to show digits
iFWNum :: Int -> Int -> ISeq
iFWNum width n =
    IStr (space (width - length digits) ++ digits)
    where digits = show n

-- useful for printing lists 1) <indented block with seq/element> \n 
iLayn :: [ISeq] -> ISeq
iLayn seqs = iConcat (zipWith (curry layItem) [1..] seqs)
  where
    layItem :: (Int, ISeq) -> ISeq
    layItem (n, seq) = iConcat [iFWNum 4 n, iStr ") ", iIndent seq, iNewline]

-- Pretty Printer Functions

-- Pretty Print Representation for the entire program
-- CoreProgram is a list of super combinators, print everyone of them with ;\n
pprProgram :: CoreProgram -> ISeq
pprProgram prog = iInterleave (iAppend (iStr " ;") iNewline) (map pprSc prog)

-- print supercombinator (top level) funtion
pprSc :: CoreScDefn -> ISeq
pprSc (name, args, body) =
    iConcat [iStr name, iSpace, pprArgs args, iStr " = ", iIndent (pprExpr body)]

-- Print expresions 
pprExpr :: CoreExpr -> ISeq
pprExpr (ENum n) = iNum n
pprExpr (EVar v) = iStr v
pprExpr (EAp (EAp (EVar op) e1) e2)
    | op `elem` ["+", "-", "*", "/", "<", "<=", "==", "~=", ">=", ">", "&", "|"] =
        iConcat [pprAExpr e1, iStr (" " ++ op ++ " "), pprAExpr e2]
pprExpr (EAp e1 e2) =
    iConcat [pprExpr e1, iSpace, pprAExpr e2]
pprExpr (ELet isRec defns expr) =
    iConcat [iStr keyword, iNewline,
             iStr "  ", iIndent (pprDefns defns), iNewline,
             iStr "in ", pprExpr expr]
    where keyword = if isRec then "letrec" else "let"
pprExpr (ECase e alts) =
    iConcat [iStr "case ", pprExpr e, iStr " of", iNewline,
             iStr "  ", iIndent (iInterleave iNl (map pprAlt alts))]
    where iNl = iConcat [iStr ";", iNewline]
pprExpr (ELam args body) =
    iConcat [iStr "(\\", pprArgs args, iStr ". ", iIndent (pprExpr body), iStr ")"]

pprAExpr :: CoreExpr -> ISeq
pprAExpr e | isAtomicExpr e = pprExpr e
pprAExpr e = iConcat [iStr "(", pprExpr e, iStr ")"]

pprArgs :: [Name] -> ISeq
pprArgs = iInterleave iSpace . map iStr

pprDefns :: [(Name, CoreExpr)] -> ISeq
pprDefns defns = iInterleave sep (map pprDefn defns)
    where sep = iConcat [iStr ";", iNewline]


pprDefn :: (Name, CoreExpr) -> ISeq
pprDefn (name, expr) = iConcat [iStr name, iStr " = ", iIndent (pprExpr expr)]

-- print cases
pprAlt :: CoreAlt -> ISeq
pprAlt (tag, args, rhs) =
    iConcat [iStr "<", iNum tag, iStr "> ", pprArgs args, iStr " -> ", iIndent (pprExpr rhs)]

iSpace = iStr " "

-- ======================
-- Example Core Programs
-- ======================

coreExample1 :: CoreProgram
coreExample1 =
    [ ("main", [], EAp (EVar "double") (ENum 21))
    , ("double", ["x"], EAp (EAp (EVar "+") (EVar "x")) (EVar "x"))
    ]

coreExample2 :: CoreProgram
coreExample2 =
    [ ("main", [], EAp (EVar "quadruple") (ENum 20))
    , ("quadruple", ["x"],
        ELet nonRecursive
            [("twice_x", EAp (EAp (EVar "+") (EVar "x")) (EVar "x"))]
            (EAp (EAp (EVar "+") (EVar "twice_x")) (EVar "twice_x")))
    ]

----------------------------------------
-- Lexer & Parser for the Core language
----------------------------------------

-- Token type
data Token
  = TLet       -- "let"
  | TLetRec    -- "letrec"
  | TIn        -- "in"
  | TCase      -- "case"
  | TOf        -- "of"
  | TVar Name  -- identifiers
  | TNum Int   -- integer literals
  | TSym String-- punctuation or operator, e.g. ";", "=", "->", "+", etc.
  deriving (Eq,Show)

-- Whitespace classifier
isSpaceChar :: Char -> Bool
isSpaceChar c = c `elem` [' ', '\t', '\n', '\r']

isLetter :: Char -> Bool
isLetter = isAlpha

isDigitChar :: Char -> Bool
isDigitChar = isDigit

-- is identifier character
isIdChar :: Char -> Bool
isIdChar c = isLetter c || isDigitChar c || c == '_'

-- | Convert a string into a flat token list
clex :: String -> [Token]
clex [] = []
clex inp@(c:cs)
  | isSpaceChar c               = clex cs
  -- line comment “-- ...”
  | c=='-' , Just rest <- stripPrefix "--" inp
                                = clex (dropWhile (/= '\n') rest)
  -- identifier or reserved
  | isLetter c =
      let (name,rest) = span isIdChar inp
      in  case name of
            "let"    -> TLet    : clex rest
            "letrec" -> TLetRec : clex rest
            "in"     -> TIn     : clex rest
            "case"   -> TCase   : clex rest
            "of"     -> TOf     : clex rest
            _        -> TVar name : clex rest
  -- number
  | isDigitChar c =
      let (digits,rest) = span isDigitChar inp
      in TNum (read digits) : clex rest
  -- multi-char symbols first
  | Just rest <- matchSym ["->","<=" ,">=" ,"==","~="] inp =
      TSym (take 2 inp) : clex rest
  -- single-char symbols
  | c `elem` (";=\\.{},()<>+-*/|&" :: String) =
      TSym [c] : clex cs
  -- anything else: treat as single-char symbol
  | otherwise = TSym [c] : clex cs

-- helper to strip a known prefix
stripPrefix :: String -> String -> Maybe String
stripPrefix [] ys         = Just ys
stripPrefix (x:xs) (y:ys)
  | x==y    = stripPrefix xs ys
  | otherwise = Nothing
stripPrefix _  _          = Nothing

-- try to match any of these symbols
matchSym :: [String] -> String -> Maybe String
matchSym [] _ = Nothing
matchSym (s:ss) xs
  | s `isPrefixOf` xs = Just (drop (length s) xs)
  | otherwise         = matchSym ss xs

isPrefixOf :: String -> String -> Bool
isPrefixOf [] _      = True
isPrefixOf _  []     = False
isPrefixOf (a:as) (b:bs) = a==b && isPrefixOf as bs

----------------------------------------
-- A simple Parser combinator library
----------------------------------------

newtype Parser a = P { runP :: [Token] -> [(a,[Token])] }

instance Functor Parser where
  fmap f (P p) = P $ \ts -> do
    (x, ts') <- p ts
    return (f x, ts')

instance Applicative Parser where
  pure x = P $ \ts -> [(x, ts)]

  P pf <*> P px = P $ \ts -> do
    (f, ts')  <- pf ts
    (x, ts'') <- px ts'
    return (f x, ts'')

instance Monad Parser where
  return = pure
  (>>=) :: Parser a -> (a -> Parser b) -> Parser b
  P p >>= f = P $ \ts -> do
    (x, ts')  <- p ts             -- Run the first parser
    (y, ts'') <- runP (f x) ts'   -- Run the parser produced by f x
    return (y, ts'')

instance Alternative Parser where
  empty = P $ const []
  P p <|> P q = P $ \ts ->
    let ps = p ts in
    if null ps then q ts else ps

-- Fail if no tokens
item :: Parser Token
item = P getItem
  where
    getItem []       = []
    getItem (t:ts') = [(t,ts')]

-- Succeed only if predicate matches
sat :: (Token -> Bool) -> Parser Token
sat f = do t <- item; if f t then return t else empty

-- Match and extract
token :: (Token -> Maybe a) -> Parser a
token f = do t <- item; maybe empty return (f t)

-- Basic combinators
many1 :: Parser a -> Parser [a]
many1 p = do x <- p; xs <- many p; return (x:xs)

sepBy1 :: Parser a -> Parser sep -> Parser [a]
sepBy1 p sep = do x <- p; xs <- many (sep >> p); return (x:xs)

-- left associative (1 + (5+6))
chainl1 :: Parser a -> Parser (a->a->a) -> Parser a
chainl1 p op = do
  x <- p
  let go acc = (do f <- op; y <- p; go (f acc y)) <|> return acc
  go x
-- right associative
chainr1 :: Parser a -> Parser (a->a->a) -> Parser a
chainr1 p op = p >>= \x ->
               (do f <- op
                   y <- chainr1 p op
                   return (f x y))
               <|> return x

-- | “expect” a specific token, else fail
sym :: String -> Parser ()
sym s = () <$ sat (\t -> t == TSym s)

-- | Reserved keywords
pLet, pLetRec, pIn, pCase, pOf :: Parser ()
pLet    = () <$ sat (== TLet)
pLetRec = () <$ sat (== TLetRec)
pIn     = () <$ sat (== TIn)
pCase   = () <$ sat (== TCase)
pOf     = () <$ sat (== TOf)

-- | Identifiers and numbers
matchVar :: Token -> Maybe Name
matchVar (TVar v) = Just v
matchVar _        = Nothing

matchNum :: Token -> Maybe Int
matchNum (TNum n) = Just n
matchNum _        = Nothing

pVar :: Parser Name
pVar = token matchVar

pNum :: Parser Int
pNum = token matchNum
----------------------------------------
-- The Core grammar parsers
----------------------------------------
between :: Parser open -> Parser close -> Parser a -> Parser a
between po pc p = po *> p <* pc
try :: Parser a -> Parser a
try p = P $ \ts -> runP p ts
-- Atomic expressions
pAExpr :: Parser (Expr Name)
pAExpr =
      EVar   <$> pVar
  <|> ENum   <$> pNum
  <|> between (sym "{") (sym "}") (do
          t <- pNum; sym ","; EConstr t <$> pNum)
  <|> between (sym "(") (sym ")") pExpr

-- Application
pApp :: Parser (Expr Name)
pApp = do es <- many1 pAExpr
          return $ foldl1 EAp es

-- Operators by precedence
pMul, pAdd, pRel, pAnd, pOr :: Parser (Expr Name)

-- level 1: *, /
pMul = chainl1 pApp (mkOp "*" <|> mkOp "/")

-- level 2: +, -
pAdd = chainl1 pMul (mkOp "+" <|> mkOp "-")

-- level 3: comparisons (treat as left-assoc)
pRel = chainl1 pAdd
  (mkOp "<"  <|> mkOp "<="
   <|> mkOp "==" <|> mkOp "~="
   <|> mkOp ">=" <|> mkOp ">")

-- level 4: &
pAnd = chainr1 pRel (mkOp "&")

-- level 5: |
pOr  = chainr1 pAnd (mkOp "|")

-- helper to build a binary operator AST node
-- Example: EAp (EAp (EVar "+") (ENum 3)) (ENum 4)
mkOp :: String -> Parser (Expr Name -> Expr Name -> Expr Name)
mkOp op = do sym op
             return (EAp . EAp (EVar op))

-- The top expression parser
-- we do pOr as the fallback so that ordinary infix and application expressions 
-- get parsed when the input isn’t one of the few special‐keyword forms.
pExpr :: Parser (Expr Name)
pExpr =
      try (do pLetRec; defs <- pDefs; pIn;  ELet True  defs <$> pExpr;)
  <|> try (do pLet;    defs <- pDefs; pIn;  ELet False defs <$> pExpr;)
  <|> try (do pCase;   scr <- pExpr; pOf;  alts <- sepBy1 pAlt (sym ";")
              return (ECase scr alts))
  <|> try (do sym "\\"; args <- many1 pVar; sym "."; ELam args <$> pExpr)
  <|> pOr

-- Definitions in let/letrec
pDefs :: Parser [(Name,Expr Name)]
pDefs = sepBy1
  (do v <- pVar; sym "="; e <- pExpr; return (v,e))
  (sym ";")

-- Alternatives in case
pAlt :: Parser (Int,[Name],Expr Name)
pAlt = do sym "<"; tag <- pNum; args <- many pVar; sym ">"; sym "->"
          rhs <- pExpr
          return (tag,args,rhs)

-- A supercombinator definition
pScDef :: Parser (Name,[Name],Expr Name)
pScDef = do name <- pVar
            args <- many pVar
            sym "="
            body <- pExpr
            return (name,args,body)

-- The whole program
pProgram :: Parser CoreProgram
pProgram = do
  scs <- sepBy1 pScDef (sym ";")  -- consumes all separators between defs
  optional (sym ";")              -- now allow *one* extra “;” at the very end
  return scs
-- | Run a parser to completion
parseCore :: String -> Either String CoreProgram
parseCore s = case runP pProgram (clex s) of
   [(prog,[])] -> Right prog
   _           -> Left  "Parse error in Core program"


