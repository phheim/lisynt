{-# LANGUAGE LambdaCase #-}

module Expansion where

import Data.Set (Set, empty, singleton, unions)
import Logic
import TransitionTree (TT(..))

-- Order does matter: Safe < DontKnow < Unsafe
data Unsafeness
  = Safe
  | DontKnow
  | Unsafe
  deriving (Eq, Ord, Show)

safenessConj :: [Unsafeness] -> Unsafeness
safenessConj fs = maximum (Safe : fs)

safenessDisj :: [Unsafeness] -> Unsafeness
safenessDisj fs = minimum (Unsafe : fs)

------------------------------------------------------------------------------
class PositiveProp f =>
      LTLExpandable f
  where
  step :: f -> f
  expand :: f -> f
    -- ^ 'expand' expands a formula. Note that temporal operators should not be
    -- put behind a next as this hides their bool sub-parts. Implicitly they are 
    -- guarded by a 'Next'. 'expand' should also do some implication base pruning
    -- for expanding operator.
  setActiveLiteral :: (Bool, AP) -> f -> f
  unsafeness :: f -> Unsafeness
  optimize :: f -> f

-------------------------------------------------------------------------------
-- | 'pick' returns the first Just value in the given list
pick :: (a -> Maybe b) -> [a] -> Maybe b
pick m =
  \case
    [] -> Nothing
    x:xr ->
      case m x of
        Just y -> Just y
        Nothing -> pick m xr

pickAndForced :: PositiveProp f => (Literal -> Bool) -> f -> Maybe Literal
pickAndForced p f =
  case getType f of
    PTLit l
      | p l -> Just l
      | otherwise -> Nothing
    PTAnd fs -> pick (pickAndForced p) fs
    _ -> Nothing

pickOrForced :: PositiveProp f => (Literal -> Bool) -> f -> Maybe Literal
pickOrForced p f =
  case getType f of
    PTLit l
      | p l -> Just l
      | otherwise -> Nothing
    PTOr fs -> pick (pickOrForced p) fs
    _ -> Nothing

pickActive :: PositiveProp f => (Literal -> Bool) -> f -> Maybe Literal
pickActive p f =
  case getType f of
    PTLit l
      | p l -> Just l
      | otherwise -> Nothing
    PTAnd fs -> pick (pickActive p) fs
    PTOr fs -> pick (pickActive p) fs
    _ -> Nothing

pickUnique :: PositiveProp f => (Literal -> Bool) -> f -> Maybe Literal
pickUnique p f = pickU f
  where
    getActiveLiterals :: PositiveProp f => f -> Set Literal
    getActiveLiterals f =
      case getType f of
        PTLit lit -> singleton lit
        PTAnd fs -> unions (map getActiveLiterals fs)
        PTOr fs -> unions (map getActiveLiterals fs)
        _ -> empty
    --
    acts = getActiveLiterals f
    --
    pickU f =
      case getType f of
        PTLit l
          | p l && (neg l) `notElem` acts -> Just l
          | otherwise -> Nothing
        PTAnd fs -> pick pickU fs
        PTOr fs -> pick pickU fs
        _ -> Nothing

setActs ::
     (Eq f, LTLExpandable f) => (Bool, AP) -> [f] -> f -> f -> ([f] -> f) -> f
setActs (val, ap) fs dominating neutral op =
  let fs' = map (setActiveLiteral (val, ap)) fs
   in if dominating `elem` fs'
        then dominating
        else op (filter (/= neutral) fs')

-------------------------------------------------------------------------------
-- | 'optTTLayer' prunes the top-level layer of the generated 'TT's
optTTLayer :: LTLExpandable f => TT f -> TT f
optTTLayer tt =
  case tt of
    SysForced _ _ (Leaf f)
      | isFalse f -> Leaf ptfalse
      | otherwise -> tt
    SysChoice n (Leaf f) t2
      | isTrue f -> SysForced n True $ Leaf pttrue
      | isFalse f -> SysForced n False t2
      | otherwise -> tt
    SysChoice n t1 (Leaf f)
      | isTrue f -> SysForced n False $ Leaf pttrue
      | isFalse f -> SysForced n True t1
      | otherwise -> tt
    EnvChoice _ (Leaf f) t2
      | isFalse f -> Leaf ptfalse
      | isTrue f -> t2
      | otherwise -> tt
    EnvChoice _ t1 (Leaf f)
      | isFalse f -> Leaf ptfalse
      | isTrue f -> t1
      | otherwise -> tt
    f -> f

-------------------------------------------------------------------------------
-- | 'genTT' generate the transition tree for an expanded formula. It applies
-- DDPL-like pruning techniques.
genTT :: LTLExpandable f => f -> TT f
genTT f =
  case pickAndForced isInput f of
    Just l -> choose f (neg l) (const id)
    Nothing ->
      case pickOrForced isInput f of
        Just l -> choose f (neg l) (const id)
        Nothing ->
          case pickAndForced isOutput f of
            Just l -> choose f l (SysForced (name l))
            Nothing ->
              case pickOrForced isOutput f of
                Just l -> choose f l (SysForced (name l))
                Nothing ->
                  case pickUnique isInput f of
                    Just l -> choose f (neg l) (const id)
                    Nothing ->
                      case pickUnique isOutput f of
                        Just l -> choose f l (SysForced (name l))
                        Nothing ->
                          case pickActive isInput f of
                            Just l -> branch f l (EnvChoice (name l))
                            Nothing ->
                              case pickActive isOutput f of
                                Just l -> branch f l (SysChoice (name l))
                                Nothing -> Leaf (step f)
  where
    choose :: LTLExpandable f => f -> Literal -> (Bool -> TT f -> TT f) -> TT f
    choose f (val, var) op =
      optTTLayer $ op val (genTT (setActiveLiteral (val, var) f))
    --
    branch :: LTLExpandable f => f -> Literal -> (TT f -> TT f -> TT f) -> TT f
    branch f (_, var) op =
      optTTLayer $
      op
        (genTT (setActiveLiteral (True, var) f))
        (genTT (setActiveLiteral (False, var) f))
