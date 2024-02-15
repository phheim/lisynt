module LISynt
  ( parseFormula
  , printTG
  , Result(..)
  , BLTL
  , solve
  , SolverQuery(..)
  , Format(..)
  , SolverType(..)
  ) where

import BLTL (BLTL)

import LogicToTG (formulaToTG)

import TimerGameSafetySolving (isSafe, sufficentAttractor)

import TimerGame (prettyPrint)

import PrettyPrint (toLine, toLines)

import Reader.BLTL (readBLTL)

import Reader.TLSF (tlsfToBLTL)

data Format
  = FmtTLSF
  | FmtCustom
  deriving (Eq, Ord, Show)

data SolverType
  = STTimerGame
  | STPrintFormula

data SolverQuery =
  SolverQuery
    { format :: Format
    , solverType :: SolverType
    , debugging :: Bool
    }

data Result
  = Safe
  | Unsafe
  | TrivialSafe
  | DontKnow
  deriving (Eq, Ord, Show)

solve :: SolverQuery -> String -> Either String (IO Result)
solve q input = do
  f <-
    case format q of
      FmtCustom -> readBLTL input
      FmtTLSF -> tlsfToBLTL 2 input
  Right
    (case solverType q of
       STTimerGame ->
         if debugging q
           then solveTGExt f
           else solveTG f
       STPrintFormula -> do
         putStrLn (toLine f)
         return DontKnow)

parseFormula :: Bool -> String -> Either String (BLTL Word)
parseFormula tlsf content
  | tlsf = tlsfToBLTL 2 content
  | otherwise = readBLTL content

printTG :: BLTL Word -> String
printTG f =
  let (game, _, _, map, _) = formulaToTG f
   in unlines (prettyPrint game : toLines map)

solveTG :: BLTL Word -> IO Result
solveTG f =
  let (game, init, bad, _, _) = formulaToTG f
   in if null bad
        then return TrivialSafe
        else do
          res <- isSafe game init bad
          if res
            then return Safe
            else return Unsafe

solveTGExt :: BLTL Word -> IO Result
solveTGExt f = do
  putStrLn (show f)
  putStrLn (toLine f)
  let (game, init, bad, _, _) = formulaToTG f
  putStrLn (prettyPrint game)
  putStrLn ("Init: " ++ toLine init)
  putStrLn ("Bad: " ++ toLine bad)
  if null bad
    then return TrivialSafe
    else do
      (attr, res, _) <- sufficentAttractor game init bad
      putStrLn (unlines (toLines attr))
      if res
        then return Safe
        else return Unsafe
