-------------------------------------------------------------------------------
-- | 
-- Module       :   TimerGame
--
-- The module 'TimerGame' defines timer games, and some creation, access, 
-- and modification functions.
--
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module TimerGame
  ( TT(..)
  , leafs
  , TimerRemap
  , Transition
  , TimerGame
  , vertecies
  , timers
  , durations
  , transRel
  , emptyTG
  , addTrans
  , predecessors
  , successors
  , prettyPrint
  ) where

-------------------------------------------------------------------------------
import Data.Map.Strict (Map, (!?), elems, findWithDefault, keysSet)
import qualified Data.Map.Strict as Map (empty, insert, insertWith)

import Data.Set (Set, singleton, singleton, union, unions)
import qualified Data.Set as Set (empty, fromList, insert, map, toList)

-------------------------------------------------------------------------------
import PrettyPrint
import Remapping (Remap, mapped, mappedTargets)
import TransitionTree

-------------------------------------------------------------------------------
-- | 'TimerRemap' represents the remapping of the timer. If a timer is not 
-- remapped, the is corresponds to a reset
type TimerRemap t = Remap t t

-------------------------------------------------------------------------------
type Transition v t = TT (Map (Set t) (v, TimerRemap t))

-------------------------------------------------------------------------------
data TimerGame v t =
  TimerGame
    { vertecies :: Set v
    , timers :: Set t
    , durations :: t -> Word
    , transRel :: Map v (Transition v t)
    , preds :: Map v (Set v)
    -- ^ 'preds' is a precomputed version of the predcessor relation. It must
    -- be assigned correcttly according to the transition relation 'transRel'
    }

-------------------------------------------------------------------------------
predecessors :: (Ord v, Ord t) => TimerGame v t -> v -> Set v
predecessors game v = findWithDefault Set.empty v (preds game)

successors :: (Ord v, Ord t) => TimerGame v t -> v -> Set v
successors game v =
  case transRel game !? v of
    Nothing -> Set.empty
    Just tt -> unions (Set.map (Set.fromList . map fst . elems) (leafs tt))

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------
--
-------------------------------------------------------------------------------
-- | 'emptyTG' genrates a 'TimerGame' with no vertecies or timers given a 
-- function to compute the timers duration
emptyTG :: (Ord v, Ord t) => (t -> Word) -> TimerGame v t
emptyTG d =
  TimerGame
    { vertecies = Set.empty
    , timers = Set.empty
    , durations = d
    , transRel = Map.empty
    , preds = Map.empty
    }

addVertecies :: (Ord v, Ord t) => Set v -> TimerGame v t -> TimerGame v t
addVertecies vs game = foldl addVertex game vs
  where
    addVertex :: (Ord v, Ord t) => TimerGame v t -> v -> TimerGame v t
    addVertex game v = game {vertecies = v `Set.insert` vertecies game}

addTimers :: (Ord v, Ord t) => Set t -> TimerGame v t -> TimerGame v t
addTimers ts game = game {timers = timers game `union` ts}

addPreds :: (Ord v, Ord t) => v -> Set v -> TimerGame v t -> TimerGame v t
addPreds pre sucs game = foldl (addPred pre) game sucs
  where
    addPred :: (Ord v, Ord t) => v -> TimerGame v t -> v -> TimerGame v t
    addPred pre game suc =
      game {preds = Map.insertWith union suc (singleton pre) (preds game)}

-------------------------------------------------------------------------------
-- | 'addTrans' adds a transition to a 'TimerGame' 
addTrans ::
     (Ord v, Ord t) => v -> Transition v t -> TimerGame v t -> TimerGame v t
addTrans v tt game =
  let lfs = leafs tt
      sucessors = unions (Set.map (Set.fromList . map fst . elems) lfs)
      toTimers = unions (unions (Set.map keysSet lfs))
      remaps = unions (Set.map (Set.fromList . map snd . elems) lfs)
      timers =
        toTimers `union` unions (Set.map mapped remaps) `union`
        unions (Set.map mappedTargets remaps)
   in (addPreds v sucessors .
       addTimers timers . addVertecies sucessors . addVertecies (singleton v))
        (game {transRel = Map.insert v tt (transRel game)})

-------------------------------------------------------------------------------
-- Pretty Printing
-------------------------------------------------------------------------------
prettyPrint ::
     (PrettyPrintable v, PrettyPrintable t, Ord t, Ord v)
  => TimerGame v t
  -> String
prettyPrint game =
  unlines $
  [ "## Vertecies ###"
  , toLine (vertecies game)
  , "### Timers ###"
  , toLine (timers game)
  ] ++
  ["### Durations ###"] ++
  [toLine t ++ ": " ++ show (durations game t) | t <- Set.toList (timers game)] ++
  ["### Transitions ###"] ++
  (concatMap
     (\v ->
        [ toLine v ++ ":"
        , case transRel game !? v of
            Nothing -> "NO TRANS"
            Just t -> unlines (toLines t)
        , "---"
        ])
     (Set.toList (vertecies game))) ++
  ["### Preds ###"] ++ toLines (preds game)
-------------------------------------------------------------------------------
