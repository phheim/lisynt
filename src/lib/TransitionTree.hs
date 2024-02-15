{-# LANGUAGE LambdaCase #-}

module TransitionTree where

import Data.Set (Set, singleton, union)
import MapFold
import PrettyPrint

-------------------------------------------------------------------------------
-- | 'TT' represents a transition tree which is a mixed-decisions tree for
-- environment and system choices
data TT a
  = Leaf a
  -- ^ 'Leaf' is the succesors or target of the transition
  | EnvChoice String (TT a) (TT a)
  -- ^ 'EnvChoice' represents the choice of the environment with input name
  -- and first a sub-tree for a true input and lastly one for a false input
  | SysForced String Bool (TT a)
  -- ^ 'SysForced' represents an output that that has to be set by the 
  -- system to a specific value
  | SysChoice String (TT a) (TT a)
  -- ^ 'SysChoice' is a choice of the system with the same convention as 
  -- 'EnvChoice'
  deriving (Eq, Ord, Show)

instance Functor TT where
  fmap m =
    \case
      Leaf a -> Leaf (m a)
      EnvChoice n tl tr -> EnvChoice n (fmap m tl) (fmap m tr)
      SysChoice n tl tr -> SysChoice n (fmap m tl) (fmap m tr)
      SysForced n v t -> SysForced n v (fmap m t)

instance MapFold TT where
  mapFold m b =
    \case
      Leaf a ->
        let (a', b') = m b a
         in (Leaf a', b')
      EnvChoice n lt rt ->
        let (lt', b') = mapFold m b lt
            (rt', b'') = mapFold m b' rt
         in (EnvChoice n lt' rt', b'')
      SysForced n v t ->
        let (t', b') = mapFold m b t
         in (SysForced n v t', b')
      SysChoice n lt rt ->
        let (lt', b') = mapFold m b lt
            (rt', b'') = mapFold m b' rt
         in (SysChoice n lt' rt', b'')

instance PrettyPrintable a => PrettyPrintable (TT a) where
  toLines = indentLines . ppTT
  toLine = indentUnlines . ppTT

ppTT :: PrettyPrintable a => TT a -> [(Int, String)]
ppTT =
  \case
    Leaf a -> [(1, toLine a)]
    EnvChoice n t1 t2 ->
      [(0, "EnvChoice " ++ n), (1, n ++ " = True:")] ++
      indentL (ppTT t1) ++ [(1, n ++ " = False:")] ++ indentL (ppTT t2)
    SysChoice n t1 t2 ->
      [(0, "SysChoice " ++ n), (1, n ++ " = True:")] ++
      indentL (ppTT t1) ++ [(1, n ++ " = False:")] ++ indentL (ppTT t2)
    SysForced n b t ->
      (0, "SysForce " ++ n ++ " = " ++ show b) : indentL (ppTT t)

leafs :: Ord a => TT a -> Set a
leafs =
  \case
    Leaf v -> singleton v
    EnvChoice _ t1 t2 -> leafs t1 `union` leafs t2
    SysChoice _ t1 t2 -> leafs t1 `union` leafs t2
    SysForced _ _ t -> leafs t
