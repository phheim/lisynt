-------------------------------------------------------------------------------
-- | 
-- Module       :   Reader.BLTL
--
-- The 'Reader' implements lexing, parsing, transformations to get a formula
-- from the custom BLTL format
--
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Reader.BLTL
  ( readBLTL
  , lex
  ) where

-------------------------------------------------------------------------------
import Data.Char (isAlpha, isDigit)
import Data.Set as Set (Set, empty, insert, intersection, union)
import Prelude hiding (lex)
import Text.Read (readMaybe)

import BLTL
import Expansion (optimize)
import Logic

-------------------------------------------------------------------------------
-- | 'Error' is the type of an error message
type Error = String

-------------------------------------------------------------------------------
-- | 'readBLTL' transforms a string into a 'BLTL' formula
readBLTL :: String -> Either Error (BLTL Word)
readBLTL str = do
  tokens <- lex str
  spec <- parse tokens
  f <- specToBLTL spec
  Right (optimize f)

-------------------------------------------------------------------------------
-- | 'Token' describes a lexer token
data Token
  = TkId String
  -- ^ Identifier token
  | TkNumber Word
  -- ^ Positive number token
  | TkLPar
  -- ^ The left parantheses '('
  | TkRPar
  -- ^ The left parantheses ')'
  | TkTrue
  -- ^ The boolean TRUE constant
  | TkFalse
  -- ^ The boolean FALSE constant
  | TkNot
  -- ^ The unary boolean NOT operator '!'
  | TkAnd
  -- ^ The binary boolean AND operator '&&'
  | TkOr
  -- ^ The binary boolean OR operator '||'
  | TkImpl
  -- ^ The binary boolean IMPLICATION operator '->'
  | TkIff
  -- ^ The binary boolean EQUIVALENCE operator '<->'
  | TkNext
  -- ^ The unary temporal NEXT operator 'X'
  | TkGlobally
  -- ^ The unary temporal GLOBALLY operator 'G'
  | TkFinally
  -- ^ The unary temporal EVENTUALLY operator 'F'
  | TkUntil
  -- ^ The binary temporal UNTIL operator 'U'
  | TkWeakUntil
  -- ^ The binary temporal WEAK UNTIL operator 'W'
  | TkRelease
  -- ^ The binary temporal RELEASE operator 'R'
  | TkLBracket
  -- ^ The left bracket '['
  | TkRBracket
  -- ^ The right bracket ']'
  | TkInputs
  -- ^ The 'inputs' keyword 
  | TkOutputs
  -- ^ The 'outputs' keyword 
  | TkSemicolon
  -- ^ The SEMICOLON seperator ';' 
  | TkAlways
  -- ^ The 'always' keyword 
  | TkAssume
  -- ^ The 'assume' keyword 
  | TkGuarantee
  -- ^ The 'guarantee' keyword 
  | TkLBrace
  -- ^ The left brace '{'
  | TkRBrace
  -- ^ The left brace '}'
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
lexon :: String -> Token -> Either Error [Token]
lexon str t = (t :) <$> (lex str)

mapIDs :: String -> Token
mapIDs s =
  findIn
    [ ("True", TkTrue)
    , ("False", TkFalse)
    , ("X", TkNext)
    , ("F", TkFinally)
    , ("G", TkGlobally)
    , ("U", TkUntil)
    , ("W", TkWeakUntil)
    , ("R", TkRelease)
    , ("inputs", TkInputs)
    , ("outputs", TkOutputs)
    , ("always", TkAlways)
    , ("assume", TkAssume)
    , ("guarantee", TkGuarantee)
    ]
  where
    findIn =
      \case
        [] -> TkId s
        ((n, t):tr)
          | n == s -> t
          | otherwise -> findIn tr

lex :: String -> Either Error [Token]
lex =
  \case
    [] -> Right []
    ' ':tr -> lex tr
    '\n':tr -> lex tr
    '\r':tr -> lex tr
    '/':'/':tr -> lexSLComment tr
    '/':'*':tr -> lexMLComment tr
    '(':tr -> lexon tr TkLPar
    ')':tr -> lexon tr TkRPar
    '!':tr -> lexon tr TkNot
    '&':'&':tr -> lexon tr TkAnd
    '|':'|':tr -> lexon tr TkOr
    '-':'>':tr -> lexon tr TkImpl
    '<':'-':'>':tr -> lexon tr TkIff
    '[':tr -> lexon tr TkLBracket
    ']':tr -> lexon tr TkRBracket
    ';':tr -> lexon tr TkSemicolon
    '{':tr -> lexon tr TkLBrace
    '}':tr -> lexon tr TkRBrace
    x:xr
      | isDigit x -> lexNumber 0 (x : xr)
      | isAlpha x -> lexID [x] xr
      | otherwise -> Left ("Lexer error: Unknown symbol '" ++ [x] ++ "' found")

lexSLComment :: String -> Either Error [Token]
lexSLComment =
  \case
    [] -> lex []
    '\n':tr -> lex tr
    _:tr -> lexSLComment tr

lexMLComment :: String -> Either Error [Token]
lexMLComment =
  \case
    [] -> Left "Lexer error: Multi-line comment ended with EOF"
    '*':'/':tr -> lex tr
    _:tr -> lexMLComment tr

lexID :: String -> String -> Either Error [Token]
lexID ident =
  \case
    [] -> Right [mapIDs (reverse ident)]
    s:sr
      | isAlpha s || isDigit s || s == '_' -> lexID (s : ident) sr
      | otherwise -> lexon (s : sr) (mapIDs (reverse ident))

lexNumber :: Word -> String -> Either Error [Token]
lexNumber n =
  \case
    [] -> Right [TkNumber n]
    x:xr
      | isDigit x ->
        case readMaybe [x] :: Maybe Word of
          Nothing -> error "Assertion: Digits should be readable"
          Just m -> lexNumber (10 * n + m) xr
      | otherwise -> lexon (x : xr) (TkNumber n)

-------------------------------------------------------------------------------
-- Parser
-------------------------------------------------------------------------------
type Expr = LTLExpr Word String

binaryOperator :: [Token] -> Maybe (Expr -> Expr -> Expr, Int, Int, [Token])
binaryOperator =
  \case
    TkAnd:tr -> Just (\f g -> eand [f, g], 4, 5, tr)
    TkOr:tr -> Just (\f g -> eor [f, g], 3, 4, tr)
    TkImpl:tr -> Just (eimpl, 2, 3, tr)
    TkIff:tr -> Just (eiff, 2, 3, tr)
    TkWeakUntil:TkLBracket:TkNumber n:TkRBracket:tr -> Just (ebweak n, 1, 2, tr)
    TkWeakUntil:tr -> Just (eweak, 1, 2, tr)
    TkRelease:tr -> Just (erelease, 1, 2, tr)
    TkUntil:TkLBracket:TkNumber n:TkRBracket:tr -> Just (ebuntil n, 0, 1, tr)
    _ -> Nothing

unaryOp :: [Token] -> Maybe (Expr -> Expr, Int, [Token])
unaryOp =
  \case
    TkNot:tr -> Just (enot, 6, tr)
    TkNext:TkLBracket:TkNumber n:TkRBracket:tr -> Just (ebnext n, 6, tr)
    TkGlobally:TkLBracket:TkNumber n:TkRBracket:tr -> Just (ebglobally n, 6, tr)
    TkFinally:TkLBracket:TkNumber n:TkRBracket:tr ->
      Just (ebeventually n, 6, tr)
    TkNext:tr -> Just (enext, 6, tr)
    TkGlobally:tr -> Just (eglobally, 6, tr)
    _ -> Nothing

parsePrimUn :: [Token] -> Either Error (Expr, [Token])
parsePrimUn =
  \case
    TkLPar:tr ->
      case parseExpr tr of
        Left err -> Left err
        Right (e, TkRPar:tr) -> Right (e, tr)
        Right (_, _) -> Left "Parser error: expected ')'"
    TkId ident:tr -> Right (eap ident, tr)
    TkFalse:tr -> Right (efalse, tr)
    TkTrue:tr -> Right (etrue, tr)
    ts ->
      case unaryOp ts of
        Just (op, p, tr) -> do
          (e, tr') <- parseOperator p tr
          Right (op e, tr')
        Nothing -> Left "Parser error: Empty expression pattern"

parseBinary :: Expr -> Int -> [Token] -> Either Error (Expr, [Token])
parseBinary e1 pred =
  \case
    TkRPar:tr -> Right (e1, TkRPar : tr)
    ts ->
      case binaryOperator ts of
        Nothing -> Right (e1, ts)
        Just (op, lp, rp, tr)
          | pred > lp -> Right (e1, ts)
          | otherwise -> do
            (e2, tr') <- parseOperator rp tr
            parseBinary (op e1 e2) pred tr'

parseOperator :: Int -> [Token] -> Either Error (Expr, [Token])
parseOperator predecence ts = do
  (e, tr) <- parsePrimUn ts
  parseBinary e predecence tr

parseExpr :: [Token] -> Either Error (Expr, [Token])
parseExpr = parseOperator 0

data SpecExpr =
  SpecExpr
    { inputs :: Set String
    , outputs :: Set String
    , alwaysAssume :: [Expr]
    , assume :: [Expr]
    , guarantee :: [Expr]
    }
  deriving (Show)

-------------------------------------------------------------------------------
parseIDList :: Set String -> [Token] -> Either Error (Set String, [Token])
parseIDList ids =
  \case
    [] -> Right (ids, [])
    TkId ident:tr -> parseIDList (ident `Set.insert` ids) tr
    ts -> Right (ids, ts)

-------------------------------------------------------------------------------
parseBlock :: [Expr] -> [Token] -> Either Error ([Expr], [Token])
parseBlock exps =
  \case
    [] -> Left "Parser error: Expected '}' but EOF found"
    TkRBrace:tr -> Right (reverse exps, tr)
    ts ->
      case parseExpr ts of
        Left err -> Left err
        Right (e, TkSemicolon:tr) -> parseBlock (e : exps) tr
        Right (e, TkRBrace:tr) -> parseBlock (e : exps) (TkRBrace : tr)
        Right (_, _) ->
          Left "Parser error: Expected ';' or '}' after expression"

-------------------------------------------------------------------------------
parseSpec :: SpecExpr -> [Token] -> Either Error SpecExpr
parseSpec spec =
  \case
    [] -> Right spec
    TkInputs:tr -> do
      (ids, rest) <- parseIDList empty tr
      parseSpec (spec {inputs = inputs spec `union` ids}) rest
    TkOutputs:tr -> do
      (ids, rest) <- parseIDList empty tr
      parseSpec (spec {outputs = outputs spec `union` ids}) rest
    TkAlways:TkAssume:TkLBrace:tr -> do
      (fs, rest) <- parseBlock [] tr
      parseSpec (spec {alwaysAssume = alwaysAssume spec ++ fs}) rest
    TkAssume:TkLBrace:tr -> do
      (fs, rest) <- parseBlock [] tr
      parseSpec (spec {assume = assume spec ++ fs}) rest
    TkGuarantee:TkLBrace:tr -> do
      (fs, rest) <- parseBlock [] tr
      parseSpec (spec {guarantee = guarantee spec ++ fs}) rest
    x:_ ->
      Left
        ("Parser error: Unkown kind of block found, starting with " ++ show x)

parse :: [Token] -> Either Error SpecExpr
parse =
  parseSpec $
  SpecExpr
    { inputs = empty
    , outputs = empty
    , alwaysAssume = []
    , assume = []
    , guarantee = []
    }

specToBLTL :: SpecExpr -> Either Error (BLTL Word)
specToBLTL spec = do
  aA <- helper (map enot (alwaysAssume spec))
  a <- helper (map enot (assume spec))
  g <- helper (guarantee spec)
  Right (Or (AssumeFinally (Or aA) [] : And g : a))
  where
    helper :: [Expr] -> Either Error [BLTL Word]
    helper =
      \case
        [] -> Right []
        e:er -> do
          f <- toBLTL Nothing toAP e
          (f :) <$> (helper er)
    --
    toAP :: String -> Either Error AP
    toAP str
      | str `elem` (inputs spec `intersection` outputs spec) =
        Left $ "Identifier '" ++ str ++ "' is declared as in- and output"
      | str `elem` inputs spec = Right (Input str)
      | str `elem` outputs spec = Right (Output str)
      | otherwise =
        Left $
        "Identifier '" ++ str ++ "' is neither declared as input nor as output"
-------------------------------------------------------------------------------
