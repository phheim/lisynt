-------------------------------------------------------------------------------
-- | 
-- Module       :   LogicToTG
--
-- The module 'LogicToTG' transforms a BLTL formula into a 'TimerGame'
--
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module LogicToTG
  ( formulaToTG
  ) where

-------------------------------------------------------------------------------
import Data.Map (Map, (!), (!?), insertWith, keysSet)
import qualified Data.Map as Map (empty, insert, keys, toList)

import Data.Set (Set, difference, insert, powerSet, size, union, unions)
import qualified Data.Set as Set (empty, filter, fromList, map, singleton)

import Data.Sort (uniqueSort)

-------------------------------------------------------------------------------
import BLTL
import Expansion
import MapFold
import OpenList

import PartialOrder (PO)
import qualified PartialOrder as PO
  ( conjunct
  , disjunct
  , empty
  , notSmallest
  , remapInv
  , setGT
  , setOrdering
  )

import PrettyPrint
import Remapping
import TimerGame

-------------------------------------------------------------------------------
-- | 'Timer' defines the timer type for the timer game. The timers work as
-- "queue per duration". This means that for each duration there are timers
-- 0, 1, 2 .. such that the timer with 'number' zero time outs before the on
-- with number one and so on. 
data Timer =
  Timer
    { duration :: Word
    , number :: Word
    }
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- | 'mkTimer' is a simple timer creation shortcut
mkTimer :: Word -> Word -> Timer
mkTimer d n = Timer {duration = d, number = n}

-------------------------------------------------------------------------------
-- | 'BoundValue' is used for the timing inside the formula. It combines
-- timers (for runing timers), constants (for not yet expanded formula 
-- parts for timers) and explict constants for explicit expansion
data BoundValue
  = BVConst Word
  | BVExplicit Word
  | BVTimer Timer
  deriving (Eq, Ord, Show)

type Formula = BLTL BoundValue

-------------------------------------------------------------------------------
-- | 'genFormula' transform a formula with constants operator steps into
-- one using 'BoundValues'. 
-- In addition modifies the constants for timers such that
-- (a) G, F, W operators time out to a constant instead of a formula, 
--     by incrementing the constant
-- (b) No constant with value < 2 appear to make the computation of 
--     possible timeouts local
genFormula :: Set (BLTL Word) -> BLTL Word -> Formula
genFormula explicits tf =
  case tf of
    Lit l -> Lit l
    TTrue -> TTrue
    FFalse -> FFalse
    And fs -> And (gens fs)
    Or fs -> Or (gens fs)
    Next f -> Next (gen f)
    BNext t f
      | tf `elem` explicits -> BNext (BVExplicit t) (gen f)
      | t > 1 -> BNext (BVConst t) (gen f)
      | t == 1 -> Next (gen f)
      | otherwise -> gen f
    BGlobally t f fs
      | tf `elem` explicits -> BGlobally (BVExplicit t) (gen f) (gens fs)
      | t > 0 -> BGlobally (BVConst (t + 1)) (gen f) (gens fs)
      | otherwise -> And (gens (f : fs))
    BFinally t f fs
      | tf `elem` explicits -> BFinally (BVExplicit t) (gen f) (gens fs)
      | t > 0 -> BFinally (BVConst (t + 1)) (gen f) (gens fs)
      | otherwise -> Or (gens (f : fs))
    BWeakUntil t f g fs gs
      | tf `elem` explicits ->
        BWeakUntil (BVExplicit t) (gen f) (gen g) (gens fs) (gens gs)
      | t > 0 ->
        BWeakUntil (BVConst (t + 1)) (gen f) (gen g) (gens fs) (gens gs)
      | otherwise -> Or (And (gens (f : fs)) : And (gens (g : fs)) : gens gs)
    BUntil t f g fs gs
      | tf `elem` explicits ->
        BUntil (BVExplicit t) (gen f) (gen g) (gens fs) (gens gs)
      | t > 0 -> BUntil (BVConst (t + 1)) (gen f) (gen g) (gens fs) (gens gs)
      | otherwise -> Or (And (gens (g : fs)) : gens gs)
    Globally f fs -> Globally (gen f) (gens fs)
    WeakUntil f g fs gs -> WeakUntil (gen f) (gen g) (gens fs) (gens gs)
    AssumeFinally f fs -> AssumeFinally (gen f) (gens fs)
  where
    gen = genFormula explicits
    gens = map gen

-------------------------------------------------------------------------------
-- 'backGen' inverts 'genFormula'
backGen :: Formula -> BLTL Word
backGen =
  \case
    Lit l -> Lit l
    TTrue -> TTrue
    FFalse -> FFalse
    And fs -> And (gens fs)
    Or fs -> Or (gens fs)
    Next f -> Next (gen f)
    BNext t f -> BNext (back 0 t) (gen f)
    BGlobally t f fs -> BGlobally (back 1 t) (gen f) (gens fs)
    BFinally t f fs -> BFinally (back 1 t) (gen f) (gens fs)
    BWeakUntil t f g fs gs ->
      BWeakUntil (back 1 t) (gen f) (gen g) (gens fs) (gens gs)
    BUntil t f g fs gs -> BUntil (back 1 t) (gen f) (gen g) (gens fs) (gens gs)
    Globally f fs -> Globally (gen f) (gens fs)
    WeakUntil f g fs gs -> WeakUntil (gen f) (gen g) (gens fs) (gens gs)
    AssumeFinally f fs -> AssumeFinally (gen f) (gens fs)
  where
    gen = backGen
    gens = map gen
    back o =
      \case
        BVConst c -> c + o
        BVExplicit n -> n
        BVTimer _ ->
          error
            "Assertion: Timers should not be found in freshly generated formulas"

-------------------------------------------------------------------------------
-- Instance Defintions
-------------------------------------------------------------------------------
instance TemporalOrd BoundValue where
  tryCompare b1 b2 =
    case (b1, b2) of
      (BVConst c1, BVConst c2) -> Just $ compare c1 c2
      (BVExplicit n1, BVExplicit n2) -> Just $ compare n1 n2
      (BVTimer t1, BVTimer t2)
        | duration t1 == duration t2 -> Just $ compare (number t1) (number t2)
        | otherwise -> Nothing
      --
      (BVConst c, BVExplicit n) -> Just $ compare c n
      (BVExplicit n, BVConst c) -> Just $ compare n c
      --
      (BVConst c, BVTimer t)
        | c >= duration t -> Just GT
        | otherwise -> Nothing
      (BVTimer t, BVConst c)
        | c >= duration t -> Just LT
        | otherwise -> Nothing
      --
      (BVExplicit n, BVTimer t)
        | n >= duration t -> Just GT
        | otherwise -> Nothing
      (BVTimer t, BVExplicit n)
        | n >= duration t -> Just LT
        | otherwise -> Nothing

instance PrettyPrintable Timer where
  toLine t = "T" ++ show (number t) ++ "(" ++ show (duration t) ++ ")"

instance PrettyPrintable BoundValue where
  toLine =
    \case
      BVTimer t -> toLine t
      BVConst c -> show c
      BVExplicit c -> show c

instance BLTLCounter BoundValue where
  nextCounter =
    \case
      BVConst c -> Just (BVConst c) -- This is right because we expand, 
                                     -- and AFTERWARDS introduce timers!
      BVExplicit n
        | n == 0 -> Nothing
        | otherwise -> Just (BVExplicit (n - 1))
      BVTimer t -> Just (BVTimer t)

-------------------------------------------------------------------------------
-- | 'expand' expands a formula. Note that temporal operators should not be
-- put behind a next as this hides their bool sub-parts. Implicitly they are 
-- guarded by a 'Next'. 'expand' should also do some implication base pruning
-- for expanding operator.
expandF :: Formula -> Formula
expandF = expand

-------------------------------------------------------------------------------
-- | 'expandTO' generates the formula one gets when a certain timing values
-- time out. Note that 'genFormula' ensures that the original part of some 
-- operators can time out to a constant instead of a formula (this is done to 
-- keep the generated games less complex).
expandTO :: (t -> Bool) -> BLTL t -> BLTL t
expandTO to =
  \case
    Lit l -> Lit l
    TTrue -> TTrue
    FFalse -> FFalse
    And fs -> And (expTOs fs)
    Or fs -> Or (expTOs fs)
    Next f -> Next f
    BNext t f
      | to t -> f
      | otherwise -> BNext t f
    BGlobally t f fs
      | to t -> And (expTOs fs)
      | otherwise -> BGlobally t f (expTOs fs)
    BFinally t f fs
      | to t -> Or (expTOs fs)
      | otherwise -> BFinally t f (expTOs fs)
    BWeakUntil t f g fs gs
      | to t -> Or (And (expTOs fs) : expTOs gs)
      | otherwise -> BWeakUntil t f g (expTOs fs) (expTOs gs)
    BUntil t f g fs gs
      | to t -> Or (expTOs gs)
      | otherwise -> BUntil t f g (expTOs fs) (expTOs gs)
    Globally f fs -> Globally f (expTOs fs)
    WeakUntil f g fs gs -> WeakUntil f g (expTOs fs) (expTOs gs)
    AssumeFinally f fs -> AssumeFinally f (expTOs fs)
  where
    expTOs = map (expandTO to)

-------------------------------------------------------------------------------
-- | 'activeTiming' retruns the active top level timing values
activeTiming :: Ord t => BLTL t -> Set t
activeTiming =
  \case
    Lit _ -> Set.empty
    TTrue -> Set.empty
    FFalse -> Set.empty
    And fs -> actives fs
    Or fs -> actives fs
    Next _ -> Set.empty
    BNext t _ -> Set.singleton t
    BGlobally t _ fs -> t `insert` actives fs
    BFinally t _ fs -> t `insert` actives fs
    BWeakUntil t _ _ fs gs -> t `insert` (actives fs `union` actives gs)
    BUntil t _ _ fs gs -> t `insert` (actives fs `union` actives gs)
    Globally _ fs -> actives fs
    WeakUntil _ _ fs gs -> actives fs `union` actives gs
    AssumeFinally _ fs -> actives fs
  where
    actives = unions . map activeTiming

-------------------------------------------------------------------------------
-- | 'introduceTimer' introduces timers where necessary (top-level constants).
-- The timer get the next highest queue number for their duration (see 'Timer')
introduceTimer :: (Word -> Word) -> Formula -> Formula
introduceTimer indexPerDuration =
  \case
    Lit l -> Lit l
    TTrue -> TTrue
    FFalse -> FFalse
    And fs -> And (intros fs)
    Or fs -> Or (intros fs)
    Next f -> Next f
    BNext t f -> BNext (genTimer t) f
    BGlobally t f fs -> BGlobally (genTimer t) f (intros fs)
    BFinally t f fs -> BFinally (genTimer t) f (intros fs)
    BWeakUntil t f g fs gs ->
      BWeakUntil (genTimer t) f g (intros fs) (intros gs)
    BUntil t f g fs gs -> BUntil (genTimer t) f g (intros fs) (intros gs)
    Globally f fs -> Globally f (intros fs)
    WeakUntil f g fs gs -> WeakUntil f g (intros fs) (intros gs)
    AssumeFinally f fs -> AssumeFinally f (intros fs)
  where
    genTimer =
      \case
        BVConst cv ->
          BVTimer $ Timer {duration = cv, number = indexPerDuration cv}
        BVTimer t -> BVTimer t
        BVExplicit n -> BVExplicit n
    --
    intros = map (introduceTimer indexPerDuration)

-------------------------------------------------------------------------------
indicesPerDuration :: Set Timer -> Map Word [Word]
indicesPerDuration = fmap uniqueSort . foldl h Map.empty
  where
    h :: Map Word [Word] -> Timer -> Map Word [Word]
    h m t =
      case m !? duration t of
        Nothing -> Map.insert (duration t) [number t] m
        Just inds -> Map.insert (duration t) (number t : inds) m

splitTimers :: Set BoundValue -> (Set Timer, Set Word)
splitTimers =
  foldl
    (\(ts, cs) ->
       \case
         BVConst c -> (ts, c `insert` cs)
         BVTimer t -> (t `insert` ts, cs)
         BVExplicit _ -> (ts, cs))
    (Set.empty, Set.empty)

activeTimers :: Formula -> Set Timer
activeTimers = fst . splitTimers . activeTiming

generateTimer :: Formula -> Maybe (Formula, PO Timer)
generateTimer f =
  let (oldT, constants) = splitTimers (activeTiming f)
      indices = reverse <$> indicesPerDuration oldT
      maxIndex =
        \d ->
          case indices !? d of
            Just (t:_) -> t + 1
            _ -> 0
      newTimers = Set.map (\d -> mkTimer d (maxIndex d)) constants
   in if any (\t -> number t > duration t) newTimers
        then Nothing
        else let po = fold2 addCompNO PO.empty newTimers oldT
                 po' = fold2 addCompNN po newTimers newTimers
              in Just (introduceTimer maxIndex f, po')
  where
    addCompNO :: PO Timer -> Timer -> Timer -> PO Timer
    addCompNO po newTimer oldTimer
      | duration newTimer > duration oldTimer =
        case PO.setGT po newTimer oldTimer of
          Just po' -> po'
          Nothing -> error "Assertion: New contradiction should not be created"
      | otherwise = po
    --
    addCompNN :: PO Timer -> Timer -> Timer -> PO Timer
    addCompNN po a b =
      case PO.setOrdering (compare (duration a) (duration b)) po a b of
        Just po' -> po'
        Nothing ->
          error "Assertion: New timers should not generate a contradiction"

fold2 :: Foldable t => (c -> a -> b -> c) -> c -> t a -> t b -> c
fold2 f init t1 = foldl (\c b -> foldl (\c' a -> f c' a b) c t1) init

sanitize :: Formula -> (Formula, TimerRemap Timer)
sanitize f =
  let timerMatrix = indicesPerDuration (activeTimers f)
      rm =
        foldl
          (\rm d -> genTimerSwap d (timerMatrix ! d) rm)
          Remapping.empty
          (Map.keys timerMatrix)
   in (fmap (h rm) f, rm)
  where
    genTimerSwap :: Word -> [Word] -> TimerRemap Timer -> TimerRemap Timer
    genTimerSwap d indices rm =
      foldl
        (\rm (old, new) -> rmTo rm (mkTimer d new) (mkTimer d old))
        rm
        (zip (uniqueSort indices) [0 ..])
        --
    h :: TimerRemap Timer -> BoundValue -> BoundValue
    h rm =
      \case
        BVTimer t ->
          case rm `invLkp` t of
            Nothing -> error "Assertion: All timers should have been remapped"
            Just t' -> BVTimer t'
        BVConst c -> BVConst c
        BVExplicit n -> BVExplicit n

type State = Word

-- Only assign if determined safe over the whole expansion!
safeState :: Word
safeState = 0

data ExpState =
  ExpState
    { states :: Map Formula State
    , stateValue :: Map State (Formula, PO Timer)
    , expansionOL :: OpenList State
    , propagationOL :: OpenList State
    , nextState :: State
    , game :: TimerGame State Timer
    }

reinsertPO :: PO Timer -> ExpState -> State -> ExpState
reinsertPO po eSt st
  | st == safeState = eSt
  | otherwise =
    let (f, poOld) = stateValue eSt ! st
        po' = po `PO.disjunct` poOld
     in if poOld == po'
          then eSt
          else eSt
                 { stateValue = Map.insert st (f, po') (stateValue eSt)
                 , propagationOL = Set.singleton st `push` propagationOL eSt
                 }

insertFormula :: ExpState -> Formula -> PO Timer -> (ExpState, State)
insertFormula eSt f po =
  case states eSt !? f of
    Just state -> (reinsertPO po eSt state, state)
    Nothing ->
      ( eSt
          { states = Map.insert f (nextState eSt) (states eSt)
          , stateValue = Map.insert (nextState eSt) (f, po) (stateValue eSt)
          , expansionOL = Set.singleton (nextState eSt) `push` expansionOL eSt
          , nextState = nextState eSt + 1
          }
      , nextState eSt)

-------------------------------------------------------------------------------
-- 
-- Assumes not timer with druation one
-- Ignore EQ as: (a) This should not happen (b) would still be sound this way
possibleTO :: Formula -> PO Timer -> Set (Set Timer)
possibleTO f po =
  let candidates =
        Set.filter
          ((== 0) . number) -- should still be okay, as even if timers disappear the other cannot timeout
          (activeTimers f `difference` PO.notSmallest po)
   in powerSet candidates

handleState ::
     PO Timer -> ExpState -> Formula -> ((State, TimerRemap Timer), ExpState)
handleState propagatedPO eSt f =
  let (f', remap) = sanitize (optimize (expandF (optimize f)))
   in case generateTimer f' of
        Nothing ->
          ( (safeState, remap)
          , eSt {states = Map.insert f' safeState (states eSt)})
        Just (f'', generatedPO) ->
          let newPO =
                case generatedPO `PO.conjunct` PO.remapInv propagatedPO remap of
                  Just po' -> po'
                  Nothing ->
                    error
                      "Assertion: The generation of new formulas should ensure validity"
              (eSt', state) = insertFormula eSt f'' newPO
           in ((state, remap), eSt')

handleTO ::
     PO Timer
  -> Formula
  -> (Map (Set Timer) (State, TimerRemap Timer), ExpState)
  -> Set Timer
  -> (Map (Set Timer) (State, TimerRemap Timer), ExpState)
handleTO po f (toM, eSt) tos =
  let ((st, rm), eSt') =
        handleState
          po
          eSt
          (optimize
             (expandTO
                (\case
                   BVConst _ -> False
                   BVExplicit _ -> False
                   BVTimer t -> t `elem` tos)
                f))
   in (Map.insert tos (st, rm) toM, eSt')

expandNode :: ExpState -> State -> ExpState
expandNode eSt state
  | state == safeState = eSt
  | otherwise =
    let (f, po) = stateValue eSt ! state
        tt = optimize <$> genTT (optimize f)
        (trans, eSt') =
          mapFold
            (\e fl -> foldl (handleTO po fl) (Map.empty, e) (possibleTO f po))
            eSt
            tt
     in eSt' {game = addTrans state trans (game eSt)}

doExpansion :: Formula -> (ExpState, State)
doExpansion f =
  let ((initSt, _), initESt) =
        handleState
          PO.empty
          (ExpState
             { states = Map.empty
             , stateValue = Map.empty
             , expansionOL = emptyOpenList
             , propagationOL = emptyOpenList
             , nextState = safeState + 1
             , game = emptyTG duration
             })
          f
   in (fp initESt, initSt)
  where
    fp :: ExpState -> ExpState
    fp eSt =
      case pop (expansionOL eSt) of
        Just (st, ol) -> fp (expandNode (eSt {expansionOL = ol}) st)
        Nothing ->
          case pop (propagationOL eSt) of
            Just (st, ol) -> fp (expandNode (eSt {propagationOL = ol}) st)
            Nothing -> eSt

-------------------------------------------------------------------------------
-- Expansion Analysis
-------------------------------------------------------------------------------
explicitlyExpand :: Set Timer -> Set (Formula) -> Set (BLTL Word)
explicitlyExpand timers formulas =
  let timerCandidates =
        Set.map duration (Set.filter (\t -> number t == duration t) timers)
   in if null timerCandidates
        then Set.empty
        else foldl
               (\s -> (s `union`) . analyseCM . getCM timerCandidates Map.empty)
               Set.empty
               formulas

type CountingMap = Map (Word, BLTL Word) Word

analyseCM :: CountingMap -> Set (BLTL Word)
analyseCM =
  Set.fromList .
  map (\((_, f), _) -> f) .
  filter (\((d, _), n) -> 2 ^ toInteger n >= toInteger d) . Map.toList

getCM :: Set Word -> CountingMap -> Formula -> CountingMap
getCM durations cm =
  \case
    Lit _ -> cm
    TTrue -> cm
    FFalse -> cm
    And fs -> getCMs fs
    Or fs -> getCMs fs
    Next _ -> cm
    BNext t f -> timeOp t [] (\n -> BNext n (backGen f))
    BGlobally t f fs -> timeOp t fs (\n -> BGlobally (n - 1) (backGen f) [])
    BFinally t f fs -> timeOp t fs (\n -> BFinally (n - 1) (backGen f) [])
    BWeakUntil t f g fs gs ->
      timeOp
        t
        (fs ++ gs)
        (\n -> BWeakUntil (n - 1) (backGen f) (backGen g) [] [])
    BUntil t f g fs gs ->
      timeOp t (fs ++ gs) (\n -> BUntil (n - 1) (backGen f) (backGen g) [] [])
    Globally _ fs -> getCMs fs
    WeakUntil _ _ fs gs -> getCMs (fs ++ gs)
    AssumeFinally _ fs -> getCMs fs
  where
    getCMs = foldl (getCM durations) cm
    inc duration f = insertWith (+) (duration, f) 1
    timeOp t fs op =
      case t of
        BVTimer tm
          | (duration tm) `elem` durations ->
            inc (duration tm) (op (duration tm)) (getCMs fs)
          | otherwise -> getCMs fs
        _ -> getCMs fs

-------------------------------------------------------------------------------
-- Total Generation
-------------------------------------------------------------------------------
formulaToTG ::
     BLTL Word
  -> ( TimerGame State Timer
     , State
     , Set State
     , Map State (Formula, PO Timer)
     , Int)
formulaToTG f = rec f Set.empty
  where
    rec f explicits =
      let (eSt, st) = doExpansion (genFormula explicits f)
          expl = explicitlyExpand (timers (game eSt)) (keysSet (states eSt))
       in if null expl
            then ( game eSt
                 , st
                 , Set.fromList
                     [ s
                     | (f, s) <- Map.toList (states eSt)
                     , unsafeness f /= Safe
                     ]
                 , stateValue eSt
                 , size explicits)
            else rec f (explicits `union` expl)
-------------------------------------------------------------------------------
