{-# LANGUAGE LambdaCase #-}

module PartialOrder
  ( PO
  , empty
  , isEQ
  , isGT
  , isLT
  , setOrdering
  , setEQ
  , setGT
  , delete
  , setLT
  , equalPO
  , remap
  , remapInv
  , conjunct
  , disjunct
  , notSmallest
  , derive
  ) where

import Data.Map.Strict (Map, (!?), foldlWithKey, withoutKeys)
import qualified Data.Map.Strict as Map
  ( empty
  , filter
  , fromList
  , insert
  , intersectionWith
  , map
  , singleton
  , size
  , toList
  )

import Data.Set (Set, union)
import qualified Data.Set as Set (empty, fromList, insert, singleton, toList)

import Data.Maybe (fromJust, isJust)

import PrettyPrint

import Remapping (Remap, invert, lkp)

toList :: Ord a => PO a -> [(a, a, Ordering)]
toList (PO p) =
  concatMap
    (\(x, m) -> map (\(y, t) -> (x, y, t)) (Map.toList m))
    (Map.toList p)

empty :: Ord a => PO a
empty = PO (Map.empty)

sizePO :: Ord a => PO a -> Int
sizePO (PO po) = Map.size po

conjunct :: Ord a => PO a -> PO a -> Maybe (PO a)
conjunct p1 p2
  | sizePO p1 >= sizePO p2 = propagate p1 Set.empty (toList p2)
  | otherwise = propagate p2 Set.empty (toList p1)

disjunct :: Ord a => PO a -> PO a -> PO a
disjunct (PO p1) (PO p2) =
  PO $
  Map.filter
    (/= Map.empty)
    (Map.intersectionWith
       (\m1 m2 ->
          clean
            (Map.intersectionWith
               (\t1 t2 ->
                  if t1 == t2
                    then Just t1
                    else Nothing)
               m1
               m2))
       p1
       p2)
  where
    clean = Map.map fromJust . Map.filter isJust

newtype PO a =
  PO (Map a (Map a Ordering))
  deriving (Eq, Ord, Show)

get :: Ord a => PO a -> a -> a -> Maybe Ordering
get (PO p) x y
  | x == y = Just EQ
  | otherwise =
    case p !? x of
      Nothing -> Nothing
      Just m -> m !? y

set :: Ord a => PO a -> a -> a -> Ordering -> PO a
set (PO p) x y t
  | x == y = PO p
  | otherwise =
    case p !? x of
      Nothing -> PO $ Map.insert x (Map.singleton y t) p
      Just m -> PO $ Map.insert x (Map.insert y t m) p

propagate ::
     Ord a => PO a -> Set (a, a, Ordering) -> [(a, a, Ordering)] -> Maybe (PO a)
propagate po done =
  \case
    [] -> Just po
    (x, y, t):pr
      | (x, y, t) `elem` done -> propagate po done pr
      | otherwise ->
        case get po x y of
          Just t'
            | t == t' -> propagate po done pr
            | otherwise -> Nothing
          Nothing ->
            let po' = set po x y t
                done' = (x, y, t) `Set.insert` done
                subs = getSubs po' x
                pr' =
                  case t of
                    EQ -> [(y, z, t) | (z, t) <- subs]
                    LT ->
                      (y, x, GT) :
                      [(z, y, LT) | (z, t) <- subs, t `elem` [EQ, GT]]
                    GT ->
                      (y, x, LT) :
                      [(z, y, GT) | (z, t) <- subs, t `elem` [EQ, LT]]
             in propagate po' done' (pr ++ pr')
  where
    getSubs (PO p) x =
      case p !? x of
        Nothing -> [(x, EQ)]
        Just m -> (x, EQ) : Map.toList m

setOrdering :: Ord a => Ordering -> PO a -> a -> a -> Maybe (PO a)
setOrdering order po x y = propagate po Set.empty [(x, y, order)]

setEQ :: Ord a => PO a -> a -> a -> Maybe (PO a)
setEQ = setOrdering EQ

setLT :: Ord a => PO a -> a -> a -> Maybe (PO a)
setLT = setOrdering LT

setGT :: Ord a => PO a -> a -> a -> Maybe (PO a)
setGT = setOrdering GT

isEQ :: Ord a => PO a -> a -> a -> Bool
isEQ po x y = get po x y == Just EQ

isLT :: Ord a => PO a -> a -> a -> Bool
isLT po x y = get po x y == Just LT

isGT :: Ord a => PO a -> a -> a -> Bool
isGT po x y = get po x y == Just GT

equalPO :: Ord a => Set a -> PO a
equalPO xs =
  case propagate empty Set.empty (equalPO' (Set.toList xs)) of
    Nothing -> error "Assertion: Only equalities should not contradict"
    Just po -> po
  where
    equalPO' =
      \case
        x:y:xr -> (x, y, EQ) : equalPO' (y : xr)
        _ -> []

delete :: Ord a => PO a -> Set a -> PO a
delete (PO po) ds = PO ((Map.map (`withoutKeys` ds) po) `withoutKeys` ds)

derive :: (Ord a, Ord c) => PO a -> [(a, c)] -> Set (c, Ordering, a)
derive (PO po) =
  \case
    [] -> Set.empty
    (a, c):xr ->
      let constraints =
            case po !? a of
              Nothing -> Set.fromList [(c, EQ, a)]
              Just m -> Set.fromList [(c, o, a') | (a', o) <- Map.toList m]
       in constraints `union` derive (PO po) xr

remapMap :: (Ord a, Ord b) => Remap a b -> Map a c -> Map b c
remapMap rm m = Map.fromList (rmap rm (Map.toList m))
  where
    rmap :: (Ord a, Ord b) => Remap a b -> [(a, c)] -> [(b, c)]
    rmap rm =
      \case
        [] -> []
        (a, c):lr ->
          case rm `lkp` a of
            Nothing -> rmap rm lr
            Just b -> (b, c) : rmap rm lr

remap :: (Ord a, Ord b) => PO a -> Remap a b -> PO b
remap (PO m) rm = PO $ remapMap rm (Map.map (remapMap rm) m)

remapInv :: (Ord a, Ord b) => PO b -> Remap a b -> PO a
remapInv po rm = remap po (invert rm)

notSmallest :: Ord a => PO a -> Set a
notSmallest (PO po) =
  foldlWithKey
    (\nsmalls a sM ->
       if a `elem` nsmalls
         then nsmalls
         else let (gt, bEQs) = biggerEQ sM
               in if gt
                    then nsmalls `union` bEQs `union` Set.singleton a
                    else nsmalls)
    Set.empty
    po
  where
    biggerEQ :: Ord a => Map a Ordering -> (Bool, Set a)
    biggerEQ =
      foldlWithKey
        (\(gt, bEQs) a ->
           \case
             GT -> (True, bEQs)
             _ -> (gt, a `Set.insert` bEQs))
        (False, Set.empty)

-------------------------------------------------------------------------------
instance (Ord a, PrettyPrintable a) => PrettyPrintable (PO a) where
  toLines po = [toLine po]
  toLine po =
    insertInBetween
      ","
      (map
         (\(a, b, o) ->
            case o of
              GT -> toLine a ++ ">" ++ toLine b
              LT -> toLine a ++ "<" ++ toLine b
              EQ -> toLine a ++ "=" ++ toLine b)
         (toList po))
