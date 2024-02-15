{-# LANGUAGE LambdaCase #-}

module OpenList
  ( OpenList
  , toSet
  , pop
  , push
  , emptyOpenList
  ) where

import Data.Set (Set, delete, difference, empty, toList, union)

newtype OpenList a =
  OpenList ([a], Set a)
  deriving (Eq, Ord, Show)

toSet :: Ord a => OpenList a -> Set a
toSet (OpenList (_, s)) = s

pop :: Ord a => OpenList a -> Maybe (a, OpenList a)
pop =
  \case
    OpenList ([], _) -> Nothing
    OpenList (o:or, s) -> Just (o, OpenList (or, o `delete` s))

push :: Ord a => Set a -> OpenList a -> OpenList a
push new (OpenList (list, set)) =
  let reallyNew = new `difference` set
   in OpenList (list ++ toList reallyNew, set `union` reallyNew)

emptyOpenList :: Ord a => OpenList a
emptyOpenList = OpenList ([], empty)
