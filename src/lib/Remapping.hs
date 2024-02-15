{-# LANGUAGE LambdaCase #-}

module Remapping where

import Data.Set (Set)

import Data.Map as Map (Map, (!?))
import qualified Data.Map as Map (empty, insert, keysSet)

import PrettyPrint

data Remap a b =
  Remap
    { mapping :: Map a b
    , revMapping :: Map b a
    }
  deriving (Eq, Ord, Show)

instance (PrettyPrintable a, PrettyPrintable b) =>
         PrettyPrintable (Remap a b) where
  toLines = toLines . mapping
  toLine = toLine . mapping

invert :: (Ord a, Ord b) => Remap a b -> Remap b a
invert rm = Remap {mapping = revMapping rm, revMapping = mapping rm}

empty :: (Ord a, Ord b) => Remap a b
empty = Remap {mapping = Map.empty, revMapping = Map.empty}

mapped :: (Ord a, Ord b) => Remap a b -> Set a
mapped = Map.keysSet . mapping

mappedTargets :: (Ord a, Ord b) => Remap a b -> Set b
mappedTargets = Map.keysSet . revMapping

lkp :: (Ord a, Ord b) => (Remap a b) -> a -> Maybe b
lkp rm a = mapping rm !? a

invLkp :: (Ord a, Ord b) => (Remap a b) -> b -> Maybe a
invLkp rm b = revMapping rm !? b

rmTo :: (Ord a, Ord b) => Remap a b -> a -> b -> Remap a b
rmTo rm s t =
  case mapping rm !? s of
    Nothing ->
      case revMapping rm !? t of
        Nothing ->
          rm
            { mapping = Map.insert s t (mapping rm)
            , revMapping = Map.insert t s (revMapping rm)
            }
        Just _ -> error "Assertion: Mapping to already mapped value"
    Just _ -> error "Assertion: Remapping mapped values is not allowed"
