-------------------------------------------------------------------------------
-- | 
-- Module       :   TimerGameSafetySolving
--
-- The module 'TimerGameSafetySolving' solves a 'TimerGame' with 
-- safety winning-condition for the system and computes its symbolic attractor
--
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module TimerGameSafetySolving
  ( isSafe
  , sufficentAttractor
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict
  ( Map
  , (!)
  , (!?)
  , foldlWithKey
  , intersectionWith
  , keys
  , keysSet
  , mapWithKey
  )
import qualified Data.Map.Strict as Map
  ( elemAt
  , empty
  , filter
  , fromListWith
  , fromSet
  , insert
  , map
  , singleton
  , toList
  , unionWith
  )

import Data.Set (Set, difference, lookupMin, union, unions)
import qualified Data.Set as Set
  ( empty
  , filter
  , fromList
  , map
  , singleton
  , toList
  )

import System.IO

-------------------------------------------------------------------------------
import OpenList

import PartialOrder as PO (PO, equalPO)
import qualified PartialOrder as PO (conjunct, derive, empty, remap, setLT)

import PrettyPrint
import Remapping as RM
import TimerGame

-------------------------------------------------------------------------------
-- Assumption lowLimit <= upLimit <= duration
data CTX =
  CTX
    { duration :: Word
    , lowLimit :: Word
    , upLimit :: Word
    }

mkCTX :: Word -> Word -> CTX
mkCTX d approxValue
  | 2 * approxValue <= d =
    CTX {duration = d, lowLimit = approxValue, upLimit = d - approxValue}
  | otherwise = CTX {duration = d, lowLimit = d, upLimit = d}

data ApproxType
  = EXACT
  | UNDER
  | OVER
  deriving (Eq, Ord, Show) -- ORDER of constructors matters!

instance PrettyPrintable ApproxType where
  toLines t = [toLine t]
  toLine = show

on :: (a -> Bool) -> a -> Maybe a
on p x
  | p x = Just x
  | otherwise = Nothing

distribute :: (a -> b -> Maybe c) -> [a] -> [b] -> [c]
distribute merge s1 = concatMap (distr merge s1)
  where
    distr :: (a -> b -> Maybe c) -> [a] -> b -> [c]
    distr merge as b =
      case as of
        [] -> []
        a:ar ->
          case merge a b of
            Just m -> m : distr merge ar b
            Nothing -> distr merge ar b

-------------------------------------------------------------------------------
-- | 'Interval' represents an interval of natural numbers
data Interval
  = EmptyI
    -- ^ 'EmptyI' is the empty interval
  | Intv Word Word -- ^ 'Intv' a b is the interval [a,b] where 
    --      a <= b <= duration ctx.
    -- This invariant MUST be maintained by all operation working on intervals
    -- and SHOULD be assumed by all.
  deriving (Eq, Ord, Show)

instance PrettyPrintable Interval where
  toLines t = [toLine t]
  toLine =
    \case
      EmptyI -> "[]"
      Intv a b -> "[" ++ show a ++ "," ++ show b ++ "]"

elemI :: Word -> Interval -> Bool
elemI x =
  \case
    EmptyI -> False
    Intv a b -> a <= x && x <= b

fullI :: CTX -> Interval
fullI ctx = Intv 0 (duration ctx)

emptyI :: Interval
emptyI = EmptyI

intv :: CTX -> Word -> Word -> Interval
intv ctx a b
  | a <= b && b <= duration ctx = Intv a b
  | otherwise = EmptyI

orderIntv :: CTX -> Word -> Ordering -> Interval
orderIntv ctx c =
  \case
    EQ
      | c <= duration ctx -> Intv c c
      | otherwise -> EmptyI
    GT
      | c > 0 -> Intv 0 (min (c - 1) (duration ctx))
      | otherwise -> EmptyI
    LT
      | c < duration ctx -> Intv (c + 1) (duration ctx)
      | otherwise -> EmptyI

isEmptyI :: Interval -> Bool
isEmptyI = (== EmptyI)

intersectI :: Interval -> Interval -> Interval
intersectI =
  \case
    EmptyI -> const EmptyI
    Intv a1 b1 ->
      \case
        EmptyI -> EmptyI
        Intv a2 b2 ->
          let a = max a1 a2
              b = min b1 b2
           in if a > b
                then EmptyI
                else Intv a b

insideI :: Interval -> Interval -> Bool
insideI =
  \case
    EmptyI -> const True
    Intv a b ->
      \case
        EmptyI -> False
        Intv c d -> c <= a && b <= d

unionI :: Interval -> Interval -> Maybe Interval
unionI =
  \case
    EmptyI -> Just
    Intv a b ->
      \case
        EmptyI -> Just $ Intv a b
        Intv c d
          | c <= b + 1 && d + 1 >= a -> Just $ Intv (min a c) (max b d)
          | otherwise -> Nothing

stepI :: CTX -> Interval -> Interval
stepI ctx = kStepI ctx 1

kStepI :: CTX -> Word -> Interval -> Interval
kStepI ctx k =
  \case
    EmptyI -> EmptyI
    Intv a b
      | a + k > duration ctx -> EmptyI
      | otherwise -> Intv (a + k) (min (b + k) (duration ctx))

mustApproxI :: CTX -> Interval -> Bool
mustApproxI ctx =
  \case
    EmptyI -> False
    Intv a b ->
      (b > lowLimit ctx && b < upLimit ctx) ||
      (a > lowLimit ctx && a < upLimit ctx)

overApproxI :: CTX -> Interval -> Interval
overApproxI ctx =
  \case
    EmptyI -> EmptyI
    Intv a b
      | b <= lowLimit ctx -> Intv a b
      | a >= upLimit ctx -> Intv a b
      | otherwise -> Intv (min a (lowLimit ctx)) (max b (upLimit ctx))

underApproxI :: CTX -> Interval -> Interval
underApproxI ctx =
  \case
    EmptyI -> EmptyI
    Intv a b
      | a > lowLimit ctx && b < upLimit ctx -> EmptyI
      | a > lowLimit ctx -> Intv (max (upLimit ctx) a) b
      | b < upLimit ctx -> Intv a (min (lowLimit ctx) b)
      | otherwise -> Intv a b

approxDiffI :: CTX -> Interval -> Set Word
approxDiffI ctx =
  \case
    EmptyI -> Set.empty
    Intv a b ->
      let da =
            if a < upLimit ctx
              then upLimit ctx - a
              else 0
          db =
            if b < lowLimit ctx
              then lowLimit ctx - b
              else 0
       in Set.fromList $ [1 .. db] ++ [da .. (duration ctx - b)]

-------------------------------------------------------------------------------
-- Assumption: Same keys, null
-- Invariant: One Empty -> All empty
type IV t = Map t Interval

isEmptyV :: Ord t => IV t -> Bool
isEmptyV v = not (null v) && isEmptyI (snd (Map.elemAt 0 v))

sanitizeV :: Ord t => IV t -> IV t
sanitizeV v
  | any (isEmptyI . snd) (Map.toList v) = Map.map (const emptyI) v
  | otherwise = v

intersectV :: Ord t => IV t -> IV t -> IV t
intersectV v1 v2 = sanitizeV $ intersectionWith intersectI v1 v2

insideV :: Ord t => IV t -> IV t -> Bool
insideV small big = all (\t -> (small ! t) `insideI` (big ! t)) (keys small)

unionV :: Ord t => IV t -> IV t -> Maybe (IV t)
unionV v1 v2
  | v1 `insideV` v2 = Just v2
  | v2 `insideV` v1 = Just v1
  | otherwise = build v1 v2 Map.empty False (keys v1)
  where
    build :: Ord t => IV t -> IV t -> IV t -> Bool -> [t] -> Maybe (IV t)
    build v1 v2 a unified =
      \case
        [] -> Just a
        t:tr
          | (v1 ! t) == (v2 ! t) ->
            build v1 v2 (Map.insert t (v1 ! t) a) unified tr
          | unified && (v1 ! t) /= (v2 ! t) -> Nothing
          | otherwise ->
            case (v1 ! t) `unionI` (v2 ! t) of
              Nothing -> Nothing
              Just m -> build v1 v2 (Map.insert t m a) True tr

stepV :: Ord t => (t -> CTX) -> IV t -> IV t
stepV ctx iv = sanitizeV $ mapWithKey (\t -> stepI (ctx t)) iv

kStepV :: Ord t => (t -> CTX) -> Word -> IV t -> IV t
kStepV ctx k iv = sanitizeV $ mapWithKey (\t -> kStepI (ctx t) k) iv

mustApproxV :: Ord t => (t -> CTX) -> IV t -> Bool
mustApproxV ctx v = any (\(t, i) -> mustApproxI (ctx t) i) (Map.toList v)

overApproxV :: Ord t => (t -> CTX) -> IV t -> IV t
overApproxV ctx = mapWithKey (overApproxI . ctx)

underApproxV :: Ord t => (t -> CTX) -> IV t -> IV t
underApproxV ctx iv = sanitizeV $ mapWithKey (underApproxI . ctx) iv

approxDiffV :: Ord t => (t -> CTX) -> IV t -> Set Word
approxDiffV ctx iv =
  unions (map (\(t, i) -> approxDiffI (ctx t) i) (Map.toList iv))

remapV :: Ord t => (t -> CTX) -> TimerRemap t -> IV t -> IV t
remapV ctx rm iv =
  let allResetsMatch =
        all
          (\(t, i) ->
             case rm `lkp` t of
               Just _ -> True
               Nothing -> duration (ctx t) `elemI` i)
          (Map.toList iv)
   in if allResetsMatch
        then sanitizeV $
             mapWithKey
               (\t old ->
                  case rm `invLkp` t of
                    Nothing -> fullI (ctx t)
                    Just t'
                      | t == t' -> old
                      | otherwise -> iv ! t')
               iv
        else mapWithKey (const (const EmptyI)) iv

resetsIV :: Ord t => (t -> CTX) -> PO t -> Set t -> Set t -> IV t
resetsIV ctx po timers resets =
  let derived =
        PO.derive po $ map (\t -> (t, duration (ctx t))) $ Set.toList resets
      merged =
        Map.fromListWith intersectI $
        map (\(c, o, t) -> (t, orderIntv (ctx t) c o)) $ Set.toList derived
   in sanitizeV $
      Map.fromSet
        (\t ->
           case merged !? t of
             Just i -> i
             Nothing -> fullI (ctx t))
        timers

tosIV :: Ord t => (t -> CTX) -> Set t -> Set t -> IV t
tosIV ctx timers toTimers =
  Map.fromSet
    (\t ->
       if t `elem` toTimers
         then intv (ctx t) 0 0
         else intv (ctx t) 1 (duration (ctx t)))
    timers

-------------------------------------------------------------------------------
type MIV t = (IV t, ApproxType)

isEmptyM :: Ord t => MIV t -> Bool
isEmptyM = isEmptyV . fst

intersectM :: Ord t => MIV t -> MIV t -> MIV t
intersectM (iv1, at1) (iv2, at2) = (intersectV iv1 iv2, max at1 at2)

unionM :: Ord t => MIV t -> MIV t -> Maybe (MIV t)
unionM (iv1, at1) (iv2, at2)
  | at1 == at2 =
    case unionV iv1 iv2 of
      Nothing -> Nothing
      Just m -> Just (m, at1)
  | otherwise = Nothing

applyApproxM :: Ord t => (t -> CTX) -> MIV t -> Set (MIV t)
applyApproxM ctx (iv, at) =
  case at of
    EXACT
      | mustApproxV ctx iv ->
        Set.fromList [(underApproxV ctx iv, UNDER), (overApproxV ctx iv, OVER)]
      | otherwise -> Set.singleton (iv, EXACT)
    OVER -> Set.singleton (overApproxV ctx iv, OVER)
    UNDER -> Set.singleton (underApproxV ctx iv, UNDER)

stepM :: Ord t => (t -> CTX) -> MIV t -> Set (MIV t)
stepM ctx (iv, at) = applyApproxM ctx (stepV ctx iv, at)

superStepM :: Ord t => (t -> CTX) -> MIV t -> Set (MIV t)
superStepM ctx (iv, at) =
  unions $
  Set.map
    (\k -> applyApproxM ctx (kStepV ctx k iv, at))
    (approxDiffV ctx iv `union` Set.singleton 1)

remapM :: Ord t => (t -> CTX) -> TimerRemap t -> MIV t -> MIV t
remapM ctx rm (tv, at) = (remapV ctx rm tv, at)

isApproxM :: Ord t => MIV t -> Bool
isApproxM (_, at) = at /= EXACT

-------------------------------------------------------------------------------
-- Invariant : No empty MIV
type MIVS t = Set (MIV t)

isEmptyS :: Ord t => MIVS t -> Bool
isEmptyS = null

sanitizeS :: Ord t => MIVS t -> MIVS t
sanitizeS = Set.filter (not . isEmptyM)

intersectS :: Ord t => MIVS t -> MIVS t -> MIVS t
intersectS s1 s2 =
  Set.fromList $
  distribute
    (\m1 m2 -> on (not . isEmptyM) (intersectM m1 m2))
    (Set.toList s1)
    (Set.toList s2)

unionS :: Ord t => MIVS t -> MIVS t -> MIVS t
unionS = union

-- This seems reaaaly expensive but has to be done for a canonic form
canonizeS :: Ord t => MIVS t -> MIVS t
canonizeS ts = Set.fromList (tryUnions [] (Set.toList ts))
  where
    tryUnions :: Ord t => [MIV t] -> [MIV t] -> [MIV t]
    tryUnions seen =
      \case
        [] -> seen
        t:tr ->
          case firstMerge t tr of
            Nothing -> tryUnions (t : seen) tr
            Just (merged, tr') -> tryUnions seen (merged : tr')
    --
    firstMerge :: Ord t => MIV t -> [MIV t] -> Maybe (MIV t, [MIV t])
    firstMerge t =
      \case
        [] -> Nothing
        t':tr ->
          case unionM t t' of
            Nothing ->
              case firstMerge t tr of
                Nothing -> Nothing
                Just (m, tr') -> Just (m, t' : tr')
            Just m -> Just (m, tr)
      --

stepS :: Ord t => (t -> CTX) -> MIVS t -> MIVS t
stepS ctx = sanitizeS . unions . Set.map (stepM ctx)

superStepS :: Ord t => (t -> CTX) -> MIVS t -> MIVS t
superStepS ctx = sanitizeS . unions . Set.map (superStepM ctx)

remapS :: Ord t => (t -> CTX) -> TimerRemap t -> MIVS t -> MIVS t
remapS ctx rm = sanitizeS . Set.map (remapM ctx rm)

isApproxS :: Ord t => MIVS t -> Bool
isApproxS = any isApproxM

cleanApproxS :: Ord t => MIVS t -> MIVS t
cleanApproxS = Set.map (\(t, _) -> (t, EXACT)) . Set.filter ((/= OVER) . snd)

overApproxS :: Ord t => MIVS t -> MIVS t
overApproxS = Set.filter ((/= UNDER) . snd)

exactS :: Ord t => IV t -> MIVS t
exactS iv = sanitizeS (Set.singleton (iv, EXACT))

-------------------------------------------------------------------------------
-- Invariant : Empty MIVS -> remove from map
type TS t = Map (PO t) (MIVS t)

isEmptyTS :: Ord t => TS t -> Bool
isEmptyTS = null

sanitizeTS :: Ord t => TS t -> TS t
sanitizeTS = Map.filter (not . isEmptyS)

canonizeTS :: Ord t => TS t -> TS t
canonizeTS = sanitizeTS . Map.map canonizeS

intersectTS :: Ord t => TS t -> TS t -> TS t
intersectTS ts1 ts2 =
  Map.fromListWith unionS $
  distribute
    (\(p1, s1) (p2, s2) ->
       case PO.conjunct p1 p2 of
         Nothing -> Nothing
         Just po -> on (not . isEmptyS . snd) (po, intersectS s1 s2))
    (Map.toList ts1)
    (Map.toList ts2)

unionTS :: Ord t => TS t -> TS t -> TS t
unionTS = Map.unionWith unionS

stepTS :: Ord t => (t -> CTX) -> TS t -> TS t
stepTS ctx = sanitizeTS . Map.map (stepS ctx)

superStepTS :: Ord t => (t -> CTX) -> TS t -> TS t
superStepTS ctx = sanitizeTS . Map.map (superStepS ctx)

trueTS :: Ord t => (t -> CTX) -> Set t -> TS t
trueTS ctx timers =
  Map.singleton
    PO.empty
    (Set.singleton (Map.fromSet (fullI . ctx) timers, EXACT))

falseTS :: Ord t => TS t
falseTS = Map.empty

remapTS :: Ord t => (t -> CTX) -> TimerRemap t -> Set t -> TS t -> TS t
remapTS ctx rm allTs st =
  let resets = allTs `difference` mapped rm
   in sanitizeTS $
      Map.fromListWith unionS $
      map
        (\(po, s) ->
           ( PO.remap po rm
           , remapS
               ctx
               rm
               (exactS (resetsIV ctx po allTs resets) `intersectS` s))) $
      Map.toList st

initInside :: Ord t => (t -> CTX) -> Set t -> TS t -> Bool
initInside ctx allTs = not . isEmptyTS . canonizeTS . remapTS ctx RM.empty allTs

isApproxTS :: Ord t => TS t -> Bool
isApproxTS = any (isApproxS . snd) . Map.toList

cleanApproxTS :: Ord t => TS t -> TS t
cleanApproxTS st = canonizeTS (Map.map cleanApproxS st)

overApproxTS :: Ord t => TS t -> TS t
overApproxTS st = canonizeTS (Map.map overApproxS st)

-------------------------------------------------------------------------------
type Attractor v t = Map v (TS t)

toPO :: Ord t => Set t -> Set t -> PO t
toPO allTimers toTimers =
  case lookupMin toTimers of
    Nothing -> PO.empty
    Just t ->
      foldl
        (\po' t' ->
           case PO.setLT po' t t' of
             Nothing -> error "Assertion: Should not yield contardication"
             Just po'' -> po'')
        (equalPO toTimers)
        (allTimers `difference` toTimers)

cpreTO ::
     (Ord v, Ord t)
  => (t -> CTX)
  -> Set t
  -> Attractor v t
  -> Set t
  -> (v, TimerRemap t)
  -> TS t
cpreTO ctx timers attr toTimers (v, rm) =
  case attr !? v of
    Nothing -> falseTS
    Just st ->
      let rmTS = remapTS ctx rm timers st
          genPO = toPO timers toTimers
       in Map.fromListWith unionS $
          map
            (\(po, ts) ->
               ( case po `PO.conjunct` genPO of
                   Just po' -> po'
                   Nothing ->
                     error
                       "All timers where a PO is added should have been reset while remapped"
               , exactS (tosIV ctx timers toTimers) `intersectS` ts))
            (Map.toList rmTS)

cpreT ::
     (Ord v, Ord t)
  => (t -> CTX)
  -> Set t
  -> Attractor v t
  -> Transition v t
  -> TS t
cpreT ctx timers attr =
  \case
    Leaf tos ->
      stepTS ctx $
      foldlWithKey
        (\a to l -> a `unionTS` cpreTO ctx timers attr to l)
        falseTS
        tos
    EnvChoice _ tl tr ->
      unionTS (cpreT ctx timers attr tl) (cpreT ctx timers attr tr)
    SysForced _ _ t -> cpreT ctx timers attr t
    SysChoice _ tl tr ->
      intersectTS (cpreT ctx timers attr tl) (cpreT ctx timers attr tr)

cpreL ::
     (Ord v, Ord t)
  => (t -> CTX)
  -> Set t
  -> v
  -> Attractor v t
  -> Map (Set t) (v, TimerRemap t)
  -> Maybe (TS t)
cpreL ctx timers source attr toM =
  let (v, rm) = toM ! Set.empty
   in case attr !? v of
        Nothing -> Nothing
        Just st
          | all (\t -> (rm `lkp` t) == Just t) timers && v == source ->
            Just (superStepTS ctx st)
          | otherwise -> Nothing

withoutChoice :: TT a -> Maybe a
withoutChoice =
  \case
    Leaf a -> Just a
    SysForced _ _ t -> withoutChoice t
    _ -> Nothing

cpreAll ::
     (Ord v, Ord t) => (t -> CTX) -> TimerGame v t -> v -> Attractor v t -> TS t
cpreAll ctx game v attr =
  let transPart =
        case transRel game !? v of
          Nothing -> falseTS
          Just trans ->
            let standard = cpreT ctx (timers game) attr trans
             in case withoutChoice trans >>= cpreL ctx (timers game) v attr of
                  Just ts -> ts `unionTS` standard
                  Nothing -> standard
      attrPart =
        case attr !? v of
          Nothing -> falseTS
          Just ts -> ts
   in canonizeTS $ transPart `unionTS` attrPart

fp ::
     (Ord v, Ord t)
  => (t -> CTX)
  -> TimerGame v t
  -> OpenList v
  -> Attractor v t
  -> IO (Attractor v t)
fp ctx game ol attr = do
  case pop ol of
    Nothing -> return attr
    Just (v, ol') ->
      let old =
            case attr !? v of
              Nothing -> falseTS
              Just x -> x
          new = cpreAll ctx game v attr
       in if new == old
            then fp ctx game ol' attr
            else fp
                   ctx
                   game
                   (predecessors game v `push` ol')
                   (Map.insert v new attr)

sufficentAttractor ::
     (Ord v, Ord t)
  => TimerGame v t
  -> v
  -> Set v
  -> IO (Attractor v t, Bool, Word)
sufficentAttractor game init bad =
  search 1 initAttr (unions $ Set.map (predecessors game) bad) game init
  where
    initAttr =
      Map.fromSet
        (const
           (trueTS
              (\t ->
                 CTX {lowLimit = 1, upLimit = 1, duration = durations game t})
              (timers game)))
        bad
    --
    search ::
         (Ord v, Ord t)
      => Word
      -> Attractor v t
      -> Set v
      -> TimerGame v t
      -> v
      -> IO (Attractor v t, Bool, Word)
    search k oldA oldV game init = do
      _ <- hPutStr stderr $ "Itertaion: " ++ show k ++ "\n"
      let ctx t = mkCTX (durations game t) k
      let last = all (\t -> lowLimit (ctx t) >= upLimit (ctx t)) (timers game)
      attr <- fp ctx game (oldV `push` emptyOpenList) oldA
      case attr !? init of
        Nothing -> return (attr, True, k)
        Just a
          | not (initInside ctx (timers game) (overApproxTS a)) ->
            return (attr, True, k)
          | initInside ctx (timers game) (cleanApproxTS a) ->
            return (attr, False, k)
          | last -> error "Assertion: We should have found a solution by now"
          | otherwise ->
            search
              (k * 2)
              (Map.map cleanApproxTS attr)
              (keysSet (Map.filter isApproxTS attr))
              game
              init

isSafe :: (Ord v, Ord t) => TimerGame v t -> v -> Set v -> IO Bool
isSafe game init bad = do
  (_, res, _) <- sufficentAttractor game init bad
  return res
-------------------------------------------------------------------------------
