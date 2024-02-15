-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Logic
  ( AP(..)
  , Literal
  , neg
  , name
  , nameAP
  , outputAP
  , inputAP
  , isInput
  , isOutput
  , eap
  , etrue
  , efalse
  , enot
  , eand
  , eor
  , eimpl
  , eiff
  , enext
  , eglobally
  , eeventually
  , eweak
  , euntil
  , erelease
  , ebnext
  , ebglobally
  , ebeventually
  , ebweak
  , ebuntil
  , ebrelease
  , PositiveProp(..)
  , PropType(..)
  , toDNF
  , toCNF
  , optimizeCNF
  , isTrue
  , isFalse
  , LTLExpr(..)
  , negNF
  ) where

-------------------------------------------------------------------------------
import Data.Set (empty, fromList, insert, isSubsetOf, singleton, toList)

-------------------------------------------------------------------------------
-- | 'AP' desribes an atomic propostion
data AP
  = Input String
  -- ^ 'Input' is an input atomic proposition
  | Output String
  -- ^ 'Output' is an output atomic propostion
  deriving (Eq, Ord, Show)

nameAP :: AP -> String
nameAP =
  \case
    Input n -> n
    Output n -> n

inputAP :: AP -> Bool
inputAP =
  \case
    Input _ -> True
    Output _ -> False

outputAP :: AP -> Bool
outputAP =
  \case
    Input _ -> False
    Output _ -> True

-------------------------------------------------------------------------------
-- | A 'Literal' is an 'AP' that is either true (positive literal) or 
-- false (negative literal)
type Literal = (Bool, AP)

neg :: Literal -> Literal
neg (val, var) = (not val, var)

name :: Literal -> String
name = nameAP . snd

isInput :: Literal -> Bool
isInput =
  \case
    (_, Input _) -> True
    _ -> False

isOutput :: Literal -> Bool
isOutput =
  \case
    (_, Output _) -> True
    _ -> False

-------------------------------------------------------------------------------
-- Positive Propositional Formula
-------------------------------------------------------------------------------
data PropType a
  = PTTrue
  | PTFalse
  | PTLit Literal
  | PTAnd [a]
  | PTOr [a]
  | PTOther a
  deriving (Eq, Ord, Show)

class PositiveProp a where
  getType :: a -> PropType a
  pttrue :: a
  ptfalse :: a
  ptliteral :: Literal -> a

isTrue :: PositiveProp a => a -> Bool
isTrue f =
  case getType f of
    PTTrue -> True
    _ -> False

isFalse :: PositiveProp a => a -> Bool
isFalse f =
  case getType f of
    PTFalse -> True
    _ -> False

toCNF :: PositiveProp a => a -> [[a]]
toCNF p = splitClause [] [p]
  where
    splitClause :: PositiveProp a => [a] -> [a] -> [[a]]
    splitClause grounded =
      \case
        [] -> [grounded]
        p:pr ->
          case getType p of
            PTTrue -> []
            PTFalse -> splitClause grounded pr
            PTLit l -> splitClause (ptliteral l : grounded) pr
            PTOther l -> splitClause (l : grounded) pr
            PTAnd fs -> concatMap (\f -> splitClause grounded (f : pr)) fs
            PTOr fs -> splitClause grounded (fs ++ pr)

toDNF :: PositiveProp a => a -> [[a]]
toDNF p = splitClause [] [p]
  where
    splitClause :: PositiveProp a => [a] -> [a] -> [[a]]
    splitClause grounded =
      \case
        [] -> [grounded]
        p:pr ->
          case getType p of
            PTFalse -> []
            PTTrue -> splitClause grounded pr
            PTLit l -> splitClause (ptliteral l : grounded) pr
            PTOther l -> splitClause (l : grounded) pr
            PTAnd fs -> splitClause grounded (fs ++ pr)
            PTOr fs -> concatMap (\f -> splitClause grounded (f : pr)) fs

optimizeCNF :: Ord a => [[a]] -> [[a]]
optimizeCNF cnf =
  let scnf = map fromList cnf
   in map toList (toList (h scnf))
  where
    h =
      \case
        [] -> empty
        c:cr
          | null c -> singleton empty
          | otherwise ->
            let cr' = filter (not . isSubsetOf c) cr
             in if any (`isSubsetOf` c) cr'
                  then h cr'
                  else insert c (h cr')

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------
data LTLExpr c l
  = EAP l
    -- Boolean Operators
  | ETrue
  | EFalse
  | ENot (LTLExpr c l)
  | EAnd [LTLExpr c l]
  | EOr [LTLExpr c l]
    -- Standard Temporal Operators
  | ENext (LTLExpr c l)
  | EGlobally (LTLExpr c l)
  | EEventually (LTLExpr c l)
  | EUntil (LTLExpr c l) (LTLExpr c l)
  | EWeak (LTLExpr c l) (LTLExpr c l)
    -- Bounded Temporal Operators
  | EBNext c (LTLExpr c l)
  | EBGlobally c (LTLExpr c l)
  | EBEventually c (LTLExpr c l)
  | EBUntil c (LTLExpr c l) (LTLExpr c l)
  | EBWeak c (LTLExpr c l) (LTLExpr c l)
  deriving (Eq, Ord, Show)

eap :: l -> LTLExpr c l
eap = EAP

etrue :: LTLExpr c l
etrue = ETrue

efalse :: LTLExpr c l
efalse = EFalse

enot :: LTLExpr c l -> LTLExpr c l
enot = ENot

eand :: [LTLExpr c l] -> LTLExpr c l
eand = EAnd

eor :: [LTLExpr c l] -> LTLExpr c l
eor = EOr

eimpl :: LTLExpr c l -> LTLExpr c l -> LTLExpr c l
eimpl f g = eor [enot f, g]

eiff :: LTLExpr c l -> LTLExpr c l -> LTLExpr c l
eiff f g = eand [eimpl f g, eimpl g f]

enext :: LTLExpr c l -> LTLExpr c l
enext = ENext

eglobally :: LTLExpr c l -> LTLExpr c l
eglobally = EGlobally

eeventually :: LTLExpr c l -> LTLExpr c l
eeventually = EEventually

eweak :: LTLExpr c l -> LTLExpr c l -> LTLExpr c l
eweak = EWeak

euntil :: LTLExpr c l -> LTLExpr c l -> LTLExpr c l
euntil = EUntil

erelease :: LTLExpr c l -> LTLExpr c l -> LTLExpr c l
erelease e1 e2 = eweak e2 (eand [e1, e2])

ebnext :: c -> LTLExpr c l -> LTLExpr c l
ebnext = EBNext

ebglobally :: c -> LTLExpr c l -> LTLExpr c l
ebglobally = EBGlobally

ebeventually :: c -> LTLExpr c l -> LTLExpr c l
ebeventually = EBEventually

ebweak :: c -> LTLExpr c l -> LTLExpr c l -> LTLExpr c l
ebweak = EBWeak

ebuntil :: c -> LTLExpr c l -> LTLExpr c l -> LTLExpr c l
ebuntil = EBUntil

ebrelease :: c -> LTLExpr c l -> LTLExpr c l -> LTLExpr c l
ebrelease c e1 e2 = ebweak c e2 (eand [e1, e2])

-------------------------------------------------------------------------------
-- | 'negNF' transforms a formula into negation NF
negNF :: LTLExpr c l -> LTLExpr c l
negNF =
  \case
    EAP l -> EAP l
    ENot (EAP l) -> ENot (EAP l)
        --    
    ETrue -> ETrue
    EFalse -> EFalse
    ENot ETrue -> EFalse
    ENot EFalse -> ETrue
    ENot (ENot f) -> negNF f
    EAnd es -> EAnd (map negNF es)
    ENot (EAnd es) -> EOr (map (negNF . ENot) es)
    EOr es -> EOr (map negNF es)
    ENot (EOr es) -> EAnd (map (negNF . ENot) es)
        -- X 
    ENext e -> ENext (negNF e)
    ENot (ENext e) -> ENext (negNF (ENot e))
    EBNext c e -> EBNext c (negNF e)
    ENot (EBNext c e) -> EBNext c (negNF (ENot e))
        -- G
    EGlobally e -> EGlobally (negNF e)
    ENot (EGlobally e) -> EEventually (negNF (ENot e))
    EBGlobally c e -> EBGlobally c (negNF e)
    ENot (EBGlobally c e) -> EBEventually c (negNF (ENot e))
        -- F
    EEventually e -> EEventually (negNF e)
    ENot (EEventually e) -> EGlobally (negNF (ENot e))
    EBEventually c e -> EBEventually c (negNF e)
    ENot (EBEventually c e) -> EBGlobally c (negNF (ENot e))
        -- W 
    EWeak e1 e2 -> EWeak (negNF e1) (negNF e2)
    ENot (EWeak e1 e2) -> negNF (EUntil (ENot e2) (EAnd [ENot e1, ENot e2]))
    EBWeak c e1 e2 -> EBWeak c (negNF e1) (negNF e2)
    ENot (EBWeak c e1 e2) ->
      negNF (EBUntil c (ENot e2) (EAnd [ENot e1, ENot e2]))
        -- U
    EUntil e1 e2 -> EUntil (negNF e1) (negNF e2)
    ENot (EUntil e1 e2) -> negNF (EWeak (ENot e2) (EAnd [ENot e1, ENot e2]))
    EBUntil c e1 e2 -> EBUntil c (negNF e1) (negNF e2)
    ENot (EBUntil c e1 e2) ->
      negNF (EBWeak c (ENot e2) (EAnd [ENot e1, ENot e2]))
-------------------------------------------------------------------------------
