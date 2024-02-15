{-# LANGUAGE LambdaCase #-}

module BLTL where

import Expansion
  ( LTLExpandable(..)
  , Unsafeness(..)
  , safenessConj
  , safenessDisj
  , setActs
  )
import Logic
import PrettyPrint

import Data.Maybe (fromMaybe)
import Data.Sort (uniqueSort)

-------------------------------------------------------------------------------
-- BLTL 
-------------------------------------------------------------------------------
data BLTL c
  = Lit Literal
  | TTrue
  | FFalse
  | And [BLTL c]
  | Or [BLTL c]
  | Next (BLTL c)
  | BNext c (BLTL c)
  | BGlobally c (BLTL c) [BLTL c]
  -- ^ BGlobally c f fs := "(G[c] f) && (And fs)"
  | BFinally c (BLTL c) [BLTL c]
  -- ^ BFinally c f fs := "(F[c] f) || (Or fs)"
  | BWeakUntil c (BLTL c) (BLTL c) [BLTL c] [BLTL c]
  -- ^ BWeakUntil c a b fs gs := "((a W[c] b) && (And fs)) || (Or gs)"
  | BUntil c (BLTL c) (BLTL c) [BLTL c] [BLTL c]
  -- ^ BUntil c a b fs gs := "((a U[c] b) && (And fs)) || (Or gs)"
  | Globally (BLTL c) [BLTL c]
  -- ^ Globally f fs := "(G f) && (And fs)"
  | WeakUntil (BLTL c) (BLTL c) [BLTL c] [BLTL c]
  -- ^ WeakUntil a b fs gs := "((a W b) && (And fs)) || (Or gs)"
  | AssumeFinally (BLTL c) [BLTL c]
  -- ^ AssumeFinally f fs = (F f) || Or fs.
  -- 'AssumeFinally' is an unbounded Finally that is placeholder for
  -- assumptions. For safety (F f) should be considered equivalent to falsity. 
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Instance Defintions
-------------------------------------------------------------------------------
instance Functor BLTL where
  fmap m =
    \case
      Lit l -> Lit l
      TTrue -> TTrue
      FFalse -> FFalse
      And fs -> And (map (fmap m) fs)
      Or fs -> Or (map (fmap m) fs)
      Next f -> Next (fmap m f)
      BNext c f -> BNext (m c) (fmap m f)
      BGlobally c f fs -> BGlobally (m c) (fmap m f) (map (fmap m) fs)
      BFinally c f fs -> BFinally (m c) (fmap m f) (map (fmap m) fs)
      BWeakUntil c f g fs gs ->
        BWeakUntil
          (m c)
          (fmap m f)
          (fmap m g)
          (map (fmap m) fs)
          (map (fmap m) gs)
      BUntil c f g fs gs ->
        BUntil (m c) (fmap m f) (fmap m g) (map (fmap m) fs) (map (fmap m) gs)
      Globally f fs -> Globally (fmap m f) (map (fmap m) fs)
      WeakUntil f g fs gs ->
        WeakUntil (fmap m f) (fmap m g) (map (fmap m) fs) (map (fmap m) gs)
      AssumeFinally f fs -> AssumeFinally (fmap m f) (map (fmap m) fs)

instance PositiveProp (BLTL c) where
  getType =
    \case
      TTrue -> PTTrue
      FFalse -> PTFalse
      And fs -> PTAnd fs
      Or fs -> PTOr fs
      Lit l -> PTLit l
      BGlobally c f fs
        | null fs -> PTOther (BGlobally c f [])
        | otherwise -> PTAnd (BGlobally c f [] : fs)
      BFinally c f fs
        | null fs -> PTOther (BFinally c f [])
        | otherwise -> PTOr (BFinally c f [] : fs)
      BWeakUntil c f g fs gs
        | null fs && null gs -> PTOther (BWeakUntil c f g [] [])
        | null gs -> PTAnd (BWeakUntil c f g [] [] : fs)
        | otherwise -> PTOr (BWeakUntil c f g fs [] : gs)
      BUntil c f g fs gs
        | null fs && null gs -> PTOther (BUntil c f g [] [])
        | null gs -> PTAnd (BUntil c f g [] [] : fs)
        | otherwise -> PTOr (BUntil c f g fs [] : gs)
      Globally f fs
        | null fs -> PTOther (Globally f [])
        | otherwise -> PTAnd (Globally f [] : fs)
      WeakUntil f g fs gs
        | null fs && null gs -> PTOther (WeakUntil f g [] [])
        | null gs -> PTAnd (WeakUntil f g [] [] : fs)
        | otherwise -> PTOr (WeakUntil f g fs [] : gs)
      AssumeFinally f fs
        | null fs -> PTOther (AssumeFinally f [])
        | otherwise -> PTOr (AssumeFinally f [] : fs)
      f -> PTOther f
    --
  pttrue = TTrue
    --
  ptfalse = FFalse
    --
  ptliteral = Lit

instance PrettyPrintable c => PrettyPrintable (BLTL c) where
  toLine =
    \case
      Lit (True, Input n) -> n
      Lit (True, Output n) -> n
      Lit (False, Input n) -> "!" ++ n
      Lit (False, Output n) -> "!" ++ n
      TTrue -> "True"
      FFalse -> "False"
      And fs -> "(" ++ insertInBetween " && " (map toLine fs) ++ ")"
      Or fs -> "(" ++ insertInBetween " || " (map toLine fs) ++ ")"
      Next f -> "(X " ++ toLine f ++ ")"
      BNext c f -> "(X[" ++ toLine c ++ "] " ++ toLine f ++ ")"
      Globally f fs -> printUn "G" f fs " && "
      BGlobally c f fs -> printUn ("G[" ++ toLine c ++ "]") f fs " && "
      AssumeFinally f fs -> printUn "AsummeF" f fs " || "
      BFinally c f fs -> printUn ("F[" ++ toLine c ++ "]") f fs " || "
      WeakUntil f g fs gs -> printBin " W " f g fs " && " gs " || "
      BWeakUntil c f g fs gs ->
        printBin (" W[" ++ toLine c ++ "] ") f g fs " && " gs " || "
      BUntil c f g fs gs ->
        printBin (" U[" ++ toLine c ++ "] ") f g fs " && " gs " || "
    where
      printUn op f fs sep =
        "(" ++
        op ++
        "{" ++ toLine f ++ "}" ++ insertInBetween sep (map toLine fs) ++ ")"
      printBin op f g fs sep1 gs sep2 =
        "(({" ++
        toLine f ++
        op ++
        toLine g ++
        "}" ++
        sep1 ++
        insertInBetween sep1 (map toLine fs) ++
        ")" ++ sep2 ++ insertInBetween sep2 (map toLine gs) ++ ")"

-------------------------------------------------------------------------------
-- | 'transform' applies a substituion to a 'BLTL' formula in a down to top 
-- manner, i.e. first the leafs are transformed, then the inner nodes an then 
-- the roots
transform :: (BLTL c -> BLTL c) -> BLTL c -> BLTL c
transform subst =
  \case
    And fs -> subst $ And (map (transform subst) fs)
    Or fs -> subst $ Or (map (transform subst) fs)
    Next f -> subst $ Next (transform subst f)
    BNext n f -> subst $ BNext n (transform subst f)
    BGlobally n f fs ->
      subst $ BGlobally n (transform subst f) (map (transform subst) fs)
    BFinally n f fs ->
      subst $ BFinally n (transform subst f) (map (transform subst) fs)
    BWeakUntil n f g fs gs ->
      subst $
      BWeakUntil
        n
        (transform subst f)
        (transform subst g)
        (map (transform subst) fs)
        (map (transform subst) gs)
    BUntil n f g fs gs ->
      subst $
      BUntil
        n
        (transform subst f)
        (transform subst g)
        (map (transform subst) fs)
        (map (transform subst) gs)
    Globally f fs ->
      subst $ Globally (transform subst f) (map (transform subst) fs)
    WeakUntil f g fs gs ->
      subst $
      WeakUntil
        (transform subst f)
        (transform subst g)
        (map (transform subst) fs)
        (map (transform subst) gs)
    AssumeFinally f fs ->
      subst $ AssumeFinally (transform subst f) (map (transform subst) fs)
    f -> subst f

-------------------------------------------------------------------------------
-- Optimizations
-------------------------------------------------------------------------------
-- | An 'Optimization' is a mapping from some type T to 'Maybe' T. An 
-- 'Optimization' should either return a transformed value or 'Nothing' if no 
-- transformation is applied.
type Optimization a = a -> Maybe a

-------------------------------------------------------------------------------
-- | 'optimizations' defines a list of 'Optimizations on 'BLTL' formulas
optimizations :: (TemporalOrd t, Ord t) => Optimization (BLTL t)
optimizations =
  \case
    And [] -> Just TTrue
    And [f] -> Just f
    And fs -> And <$> handleConjunction fs
      --
    Or [] -> Just FFalse
    Or [f] -> Just f
    Or fs -> Or <$> handleDisjunction fs
      --
    Next TTrue -> Just TTrue
    Next FFalse -> Just FFalse
      --
    BNext _ TTrue -> Just TTrue
    BNext _ FFalse -> Just FFalse
      --
    BGlobally _ TTrue fs -> Just (And fs)
    BGlobally _ FFalse _ -> Just FFalse
    BGlobally _ _ [FFalse] -> Just FFalse
    BGlobally t f fs -> BGlobally t f <$> handleConjunction fs
      --
    BFinally _ FFalse fs -> Just (Or fs)
    BFinally _ TTrue _ -> Just TTrue
    BFinally _ _ [TTrue] -> Just TTrue
    BFinally t f fs -> BFinally t f <$> handleDisjunction fs
      -- 
    BWeakUntil _ _ _ [FFalse] _ -> Just FFalse
    BWeakUntil _ _ _ _ [TTrue] -> Just TTrue
    BWeakUntil t f g fs gs ->
      case (handleConjunction fs, handleDisjunction gs) of
        (Just fs', Just gs') -> Just (BWeakUntil t f g fs' gs')
        (Just fs', _) -> Just (BWeakUntil t f g fs' gs)
        (_, Just gs') -> Just (BWeakUntil t f g fs gs')
        _ -> Nothing
     --
    BUntil _ _ _ [FFalse] _ -> Just FFalse
    BUntil _ _ _ _ [TTrue] -> Just TTrue
    BUntil t f g fs gs ->
      case (handleConjunction fs, handleDisjunction gs) of
        (Just fs', Just gs') -> Just (BUntil t f g fs' gs')
        (Just fs', _) -> Just (BUntil t f g fs' gs)
        (_, Just gs') -> Just (BUntil t f g fs gs')
        _ -> Nothing
      -- 
    Globally TTrue _ -> Just TTrue
    Globally FFalse _ -> Just FFalse
    Globally _ [FFalse] -> Just FFalse
    Globally f fs -> Globally f <$> handleConjunction fs
      --
    WeakUntil _ _ [FFalse] _ -> Just FFalse
    WeakUntil _ _ _ [TTrue] -> Just TTrue
    WeakUntil f g fs gs ->
      case (handleConjunction fs, handleDisjunction gs) of
        (Just fs', Just gs') -> Just (WeakUntil f g fs' gs')
        (Just fs', _) -> Just (WeakUntil f g fs' gs)
        (_, Just gs') -> Just (WeakUntil f g fs gs')
        _ -> Nothing
      --
    AssumeFinally FFalse fs -> Just (Or fs)
    AssumeFinally TTrue _ -> Just TTrue
    AssumeFinally _ [TTrue] -> Just TTrue
    AssumeFinally f fs -> AssumeFinally f <$> handleDisjunction fs
      --
    _ -> Nothing

handleDisjunction :: (Ord t, TemporalOrd t) => [BLTL t] -> Maybe [BLTL t]
handleDisjunction =
  optFirst
    [ maintainList TTrue FFalse
    , orLifting
    , pairwiseOpt temporalOpt orTemporalOpts
    , orSubsumption
    ]

handleConjunction :: (Ord t, TemporalOrd t) => [BLTL t] -> Maybe [BLTL t]
handleConjunction =
  optFirst
    [ maintainList FFalse TTrue
    , andLifting
    , pairwiseOpt temporalOpt andTemporalOpts
    , andSubsumption
    ]

maintainList :: Ord t => BLTL t -> BLTL t -> [BLTL t] -> Maybe [BLTL t]
maintainList dominating neutral fs
  | dominating `elem` fs = Just [dominating]
  | neutral `elem` fs = Just (uniqueSort (filter (/= neutral) fs))
  | otherwise =
    let fs' = uniqueSort fs
     in if fs' == fs
          then Nothing
          else Just fs'

andSubsumption :: TemporalOrd t => [BLTL t] -> Maybe [BLTL t]
andSubsumption =
  pairwiseOpt
    (const True)
    (\f g ->
       if f `implies` g
         then Just f
         else if g `implies` f
                then Just g
                else Nothing)

orSubsumption :: TemporalOrd t => [BLTL t] -> Maybe [BLTL t]
orSubsumption =
  pairwiseOpt
    (const True)
    (\f g ->
       if g `implies` f
         then Just f
         else if f `implies` g
                then Just g
                else Nothing)

class Eq t =>
      TemporalOrd t
  where
  tryCompare :: t -> t -> Maybe Ordering
  tryCompare a b
    | a == b = Just EQ
    | otherwise = Nothing

instance TemporalOrd Word where
  tryCompare a b = Just (compare a b)

tryMax :: TemporalOrd a => a -> a -> Maybe a
tryMax a b =
  case tryCompare a b of
    Nothing -> Nothing
    Just LT -> Just b
    Just EQ -> Just b
    Just GT -> Just a

sureLEQ :: TemporalOrd a => a -> a -> Bool
sureLEQ a b =
  case tryCompare a b of
    Just LT -> True
    Just EQ -> True
    _ -> False

sureGEQ :: TemporalOrd a => a -> a -> Bool
sureGEQ a b =
  case tryCompare a b of
    Just GT -> True
    Just EQ -> True
    _ -> False

implies :: TemporalOrd t => BLTL t -> BLTL t -> Bool
implies a b =
  case (a, b) of
    (FFalse, _) -> True
    (_, TTrue) -> True
    (Or fs, g) -> all (\f -> f `implies` g) fs
    (And fs, g) -> any (\f -> f `implies` g) fs
    (f, And gs) -> all (\g -> f `implies` g) gs
    (f, Or gs) -> any (\g -> f `implies` g) gs
    (BFinally m f fs, BFinally n g gs) ->
      f == g && sureLEQ m n && (Or fs `implies` Or (g : gs))
    (BGlobally m f fs, BGlobally n g gs) ->
      f == g && sureGEQ m n && (And (f : fs) `implies` And gs)
    (BWeakUntil t f g fs gs, BWeakUntil t' f' g' fs' gs') ->
      f == f' &&
      g == g' &&
      sureGEQ t t' &&
      (And (f : fs) `implies` And fs') && (Or gs `implies` Or gs')
    (BUntil t f g fs gs, BUntil t' f' g' fs' gs') ->
      f == f' &&
      g == g' &&
      sureLEQ t t' &&
      (And (f : fs) `implies` And fs') && (Or gs `implies` Or gs')
    (Globally f fs, Globally g gs) -> f == g && (And (f : fs) `implies` And gs)
    (WeakUntil f g fs gs, WeakUntil f' g' fs' gs') ->
      f == f' &&
      g == g' && (And (f : fs) `implies` And fs') && (Or gs `implies` Or gs')
    (f, g) -> f == g

andLifting :: [BLTL t] -> Maybe [BLTL t]
andLifting =
  \case
    [] -> Nothing
    And fs:gr ->
      Just $ fromMaybe fs (andLifting fs) ++ fromMaybe gr (andLifting gr)
    f:fr -> (f :) <$> andLifting fr

orLifting :: [BLTL t] -> Maybe [BLTL t]
orLifting =
  \case
    [] -> Nothing
    Or fs:gr ->
      Just $ fromMaybe fs (orLifting fs) ++ fromMaybe gr (orLifting gr)
    f:fr -> (f :) <$> orLifting fr

-------------------------------------------------------------------------------
andTemporalOpts :: TemporalOrd t => BLTL t -> BLTL t -> Maybe (BLTL t)
andTemporalOpts a b =
  case (a, b) of
    (BGlobally m f fs, BGlobally n g gs)
      | f == g -> (\t -> BGlobally t f (fs ++ gs)) <$> tryMax m n
      | otherwise -> Nothing
    (Globally f fs, Globally g gs)
      | f == g -> Just (Globally f (fs ++ gs))
      | otherwise -> Nothing
    _ -> Nothing

-------------------------------------------------------------------------------
orTemporalOpts :: TemporalOrd t => BLTL t -> BLTL t -> Maybe (BLTL t)
orTemporalOpts a b =
  case (a, b) of
    (BFinally m f fs, BFinally n g gs)
      | f == g -> (\t -> BFinally t f (fs ++ gs)) <$> tryMax m n
      | otherwise -> Nothing
    _ -> Nothing

temporalOpt :: BLTL t -> Bool
temporalOpt =
  \case
    BGlobally _ _ _ -> True
    BFinally _ _ _ -> True
    Globally _ _ -> True
    _ -> False

pairwiseOpt :: (a -> Bool) -> (a -> a -> Maybe a) -> [a] -> Maybe [a]
pairwiseOpt p opt =
  \case
    [] -> Nothing
    x:xr ->
      if p x
        then case singleOpt x xr of
               Nothing ->
                 case pairwiseOpt p opt xr of
                   Nothing -> Nothing
                   Just xr' -> Just (x : xr')
               Just xr' -> Just xr'
        else case pairwiseOpt p opt xr of
               Nothing -> Nothing
               Just xr' -> Just (x : xr')
  where
    singleOpt _ [] = Nothing
    singleOpt e (x:xr) =
      case opt e x of
        Just x' -> Just (x' : xr)
        Nothing ->
          case singleOpt e xr of
            Just xr' -> Just (x : xr')
            Nothing -> Nothing

-------------------------------------------------------------------------------
-- | 'optFP' turn an 'Optimization' into a substituion by applying the 
-- 'Optimization' until a fixed-point is reached, i.e. the 'Optimization' 
-- returns 'Nothing'
optFP :: Optimization a -> a -> a
optFP opt f =
  case opt f of
    Nothing -> f
    Just g -> optFP opt g

-------------------------------------------------------------------------------
-- | 'optFirst' turns a list of 'Optimization's into a sinlge one
optFirst :: [Optimization a] -> Optimization a
optFirst opts x =
  case opts of
    [] -> Nothing
    o:or ->
      case o x of
        Nothing -> optFirst or x
        Just y -> Just y

-------------------------------------------------------------------------------
-- | 'optimize' applies different optimizations to a 'BLTL' formula
optimizeBLTL :: (TemporalOrd t, Ord t) => BLTL t -> BLTL t
optimizeBLTL = transform (optFP optimizations)

negNFtoBLTL ::
     Maybe c -> (l -> Either String AP) -> LTLExpr c l -> Either String (BLTL c)
negNFtoBLTL approx toAP =
  \case
    EAP l -> (\a -> Lit (True, a)) <$> toAP l
    ENot (EAP l) -> (\a -> Lit (False, a)) <$> toAP l
    ENot _ -> error "Assertion: LTL expression assumed in NNF"
    ETrue -> Right TTrue
    EFalse -> Right FFalse
    EAnd es -> listAppl And (negNFtoBLTL approx toAP) es
    EOr es -> listAppl Or (negNFtoBLTL approx toAP) es
    ENext e -> Next <$> negNFtoBLTL approx toAP e
    EGlobally e -> (\f -> Globally f []) <$> negNFtoBLTL approx toAP e
    EEventually e ->
      case approx of
        Nothing -> Left "Transform error: Lifeness found"
        Just k -> negNFtoBLTL approx toAP (EBEventually k e)
    EWeak e1 e2 -> do
      f <- negNFtoBLTL approx toAP e1
      g <- negNFtoBLTL approx toAP e2
      Right (WeakUntil f g [] [])
    EUntil e1 e2 ->
      case approx of
        Nothing -> Left "Transform error: Lifeness found"
        Just k -> negNFtoBLTL approx toAP (EBUntil k e1 e2)
    EBNext c e -> BNext c <$> negNFtoBLTL approx toAP e
    EBGlobally c e -> (\f -> BGlobally c f []) <$> negNFtoBLTL approx toAP e
    EBEventually c e -> (\f -> BFinally c f []) <$> negNFtoBLTL approx toAP e
    EBWeak c e1 e2 -> do
      f <- negNFtoBLTL approx toAP e1
      g <- negNFtoBLTL approx toAP e2
      Right (BWeakUntil c f g [] [])
    EBUntil c e1 e2 -> do
      f <- negNFtoBLTL approx toAP e1
      g <- negNFtoBLTL approx toAP e2
      Right (BUntil c f g [] [])
  where
    listAppl op rec = fmap op . sequence . (map rec)

toBLTL ::
     Maybe c -> (l -> Either String AP) -> LTLExpr c l -> Either String (BLTL c)
toBLTL approx toAP = negNFtoBLTL approx toAP . negNF

-------------------------------------------------------------------------------
unexpandNext :: Word -> BLTL Word -> BLTL Word
unexpandNext threshold = transform (\f -> fromMaybe f (unChain 0 f))
  where
    unChain :: Word -> BLTL Word -> Maybe (BLTL Word)
    unChain size =
      \case
        Next f -> unChain (size + 1) f
        BNext n f -> unChain (size + n) f
        f
          | size >= threshold -> Just (BNext size f)
          | otherwise -> Nothing

class (TemporalOrd t, Ord t) =>
      BLTLCounter t
  where
  nextCounter :: t -> Maybe t

instance BLTLCounter Word where
  nextCounter t
    | t > 0 = Just (t - 1)
    | otherwise = Nothing

-------------------------------------------------------------------------------
instance BLTLCounter t => LTLExpandable (BLTL t)
 --
    where
  setActiveLiteral (val, ap) =
    \case
      Lit (val', ap') ->
        if ap' == ap
          then if val' == val
                 then TTrue
                 else FFalse
          else Lit (val', ap')
      TTrue -> TTrue
      FFalse -> FFalse
      And fs ->
        setActs
          (val, ap)
          fs
          FFalse
          TTrue
          (\case
             [] -> TTrue
             [f'] -> f'
             fs' -> And fs')
      Or fs ->
        setActs
          (val, ap)
          fs
          TTrue
          FFalse
          (\case
             [] -> FFalse
             [f'] -> f'
             fs' -> Or fs')
      Next f -> Next f
      BNext t f -> BNext t f
      BGlobally t f fs -> setActs (val, ap) fs FFalse TTrue (BGlobally t f)
      BFinally t f fs -> setActs (val, ap) fs TTrue FFalse (BFinally t f)
      BWeakUntil t f g fs gs ->
        let fs' = filter (/= TTrue) $ map (setActiveLiteral (val, ap)) fs
            gs' = filter (/= FFalse) $ map (setActiveLiteral (val, ap)) gs
         in if TTrue `elem` gs'
              then TTrue
              else if FFalse `elem` fs'
                     then Or gs'
                     else BWeakUntil t f g fs' gs'
      BUntil t f g fs gs ->
        let fs' = filter (/= TTrue) $ map (setActiveLiteral (val, ap)) fs
            gs' = filter (/= FFalse) $ map (setActiveLiteral (val, ap)) gs
         in if TTrue `elem` gs'
              then TTrue
              else if FFalse `elem` fs'
                     then Or gs'
                     else BUntil t f g fs' gs'
      Globally f fs -> setActs (val, ap) fs FFalse TTrue (Globally f)
      WeakUntil f g fs gs ->
        let fs' = filter (/= TTrue) $ map (setActiveLiteral (val, ap)) fs
            gs' = filter (/= FFalse) $ map (setActiveLiteral (val, ap)) gs
         in if TTrue `elem` gs'
              then TTrue
              else if FFalse `elem` fs'
                     then Or gs'
                     else WeakUntil f g fs' gs'
      AssumeFinally f fs -> setActs (val, ap) fs TTrue FFalse (AssumeFinally f)
 --
    where

  step =
    \case
      Lit _ -> error "Assert: All literals should be assigned"
      TTrue -> TTrue
      FFalse -> FFalse
      And fs -> And (map step fs)
      Or fs -> Or (map step fs)
      Next f -> f
      BNext t f -> BNext t f
      BGlobally t f fs -> BGlobally t f (map step fs)
      BFinally t f fs -> BFinally t f (map step fs)
      BWeakUntil t f g fs gs -> BWeakUntil t f g (map step fs) (map step gs)
      BUntil t f g fs gs -> BUntil t f g (map step fs) (map step gs)
      Globally f fs -> Globally f (map step fs)
      WeakUntil f g fs gs -> WeakUntil f g (map step fs) (map step gs)
      AssumeFinally f fs -> AssumeFinally f (map step fs)
  expand =
    \case
      Lit l -> Lit l
      TTrue -> TTrue
      FFalse -> FFalse
      And fs -> And (map expand fs)
      Or fs -> Or (map expand fs)
      Next f -> Next f
      BNext t f ->
        case nextCounter t of
          Nothing -> expand f
          Just t' -> BNext t' f
      BGlobally t f fs ->
        case nextCounter t of
          Nothing -> expand (And (f : fs))
          Just t' -> BGlobally t' f (expandConj f fs)
      BFinally t f fs ->
        case nextCounter t of
          Nothing -> expand (Or (f : fs))
          Just t' -> BFinally t' f (expandDisj f fs)
      Globally f fs -> Globally f (expandConj f fs)
      AssumeFinally f fs -> AssumeFinally f (expandDisj f fs)
    --
    --   (f W g) && fs || gs 
    -- = (X (f W g) && f || g) && fs || gs
    -- = (X (f W g) && f && fs || g && fs || gs
    --
    --   (f W[0] g) && fs || gs 
    -- = (f || g) && fs || gs
    -- = (f && fs) || (g && fs) || gs
      BWeakUntil t f g fs gs ->
        case nextCounter t of
          Nothing ->
            Or (And (expandConj f fs) : And (expandConj g fs) : expandDisj g gs)
          Just t' ->
            let fsg =
                  if And fs `implies` g
                    then fs
                    else g : fs
             in BWeakUntil t' f g (expandConj f fs) (expandDisj (And fsg) gs)
      WeakUntil f g fs gs ->
        let fsg =
              if And fs `implies` g
                then fs
                else g : fs
         in WeakUntil f g (expandConj f fs) (expandDisj (And fsg) gs)
    -- For until the same expansion rules apply as for the weak until
    -- except at the end:
    --
    --   (f U[0] g) && fs || gs 
    -- = g && fs || gs
      BUntil t f g fs gs ->
        case nextCounter t of
          Nothing -> Or (And (expandConj g fs) : expandDisj g gs)
          Just t' ->
            let fsg =
                  if And fs `implies` g
                    then fs
                    else g : fs
             in BUntil t' f g (expandConj f fs) (expandDisj (And fsg) gs)
    where
      expandConj :: BLTLCounter t => BLTL t -> [BLTL t] -> [BLTL t]
      expandConj f fs
        | And fs `implies` f = map expand fs
        | otherwise = map expand (f : fs)
      expandDisj :: BLTLCounter t => BLTL t -> [BLTL t] -> [BLTL t]
      expandDisj f fs
        | f `implies` Or fs = map expand fs
        | otherwise = map expand (f : fs)
  --
  unsafeness =
    \case
      FFalse -> Unsafe
      And fs -> safenessConj (map unsafeness fs)
      Or fs -> safenessDisj (map unsafeness fs)
      Globally _ fs -> safenessConj (map unsafeness fs)
      BGlobally _ _ fs -> safenessConj (map unsafeness fs)
      BWeakUntil _ _ _ fs gs -> hUntils fs gs
      BUntil _ _ _ fs gs -> hUntils fs gs
      WeakUntil _ _ fs gs -> hUntils fs gs
      AssumeFinally _ [TTrue] -> Safe
      AssumeFinally _ _ -> DontKnow
      _ -> Safe -- Other temporal operators belong here as they themself are not bad
    where
      hUntils fs gs =
        safenessDisj (safenessConj (map unsafeness fs) : map unsafeness gs)
  --
  optimize = optimizeBLTL
