-------------------------------------------------------------------------------
-- | 
-- Module       :   PrettyPrint
--
-- 'PrettyPrint' provides the type class 'PrettyPrintable', that is more
-- detailed than 'Show', instances for different common types, and useful
-- operations for them.
--
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module PrettyPrint where

-------------------------------------------------------------------------------
import qualified Data.Map.Strict as SM (Map, toList)
import qualified Data.Set as Set (Set, toList)

-------------------------------------------------------------------------------
-- | 'PrettyPrintable' defines types that can be printed in a more 
-- human-readable way than with 'show'
class PrettyPrintable a where
  toLine :: a -> String
  -- ^ 'toLine' prints the value as a single line string
  toLines :: a -> [String]
  -- ^ 'toLines' prints the value as a list of string, each representing one
  -- line
  toLines s = [toLine s]

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------
indent :: Int -> String
indent n
  | n <= 0 = ""
  | otherwise = "  " ++ indent (n - 1)

indentL :: [(Int, String)] -> [(Int, String)]
indentL = map (\(i, s) -> (i + 1, s))

indentLines :: [(Int, String)] -> [String]
indentLines = map (\(i, s) -> indent i ++ s)

indentUnlines :: [(Int, String)] -> String
indentUnlines = insertInBetween " " . map snd

insertInBetween :: String -> [String] -> String
insertInBetween x =
  \case
    [] -> []
    [s] -> s
    s:sr -> s ++ x ++ insertInBetween x sr

-------------------------------------------------------------------------------
-- Instance Defintions
-------------------------------------------------------------------------------
instance PrettyPrintable Int where
  toLines k = [show k]
  toLine = show

instance PrettyPrintable Word where
  toLines k = [show k]
  toLine = show

instance (PrettyPrintable a, PrettyPrintable b) => PrettyPrintable (a, b) where
  toLines (a, b) = toLines a ++ toLines b
  toLine (a, b) = "(" ++ toLine a ++ ", " ++ toLine b ++ ")"

instance PrettyPrintable a => PrettyPrintable ([a]) where
  toLines = map toLine
  toLine s = "[" ++ insertInBetween ", " (toLines s) ++ "]"

instance PrettyPrintable a => PrettyPrintable (Set.Set a) where
  toLines = map toLine . Set.toList
  toLine s = "{" ++ insertInBetween ", " (toLines s) ++ "}"

instance (PrettyPrintable k, PrettyPrintable a) =>
         PrettyPrintable (SM.Map k a) where
  toLines = map (\(k, a) -> toLine k ++ " -> " ++ toLine a) . SM.toList
  toLine s = "{" ++ insertInBetween ", " (toLines s) ++ "}"
-------------------------------------------------------------------------------
