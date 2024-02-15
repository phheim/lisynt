{-# LANGUAGE LambdaCase #-}

module Main where

import System.Environment (getArgs)
import System.IO

import LISynt

help :: IO ()
help = putStrLn "USAGE: lisynt FORMAT SOLVER"

parseQuery :: [String] -> Maybe SolverQuery
parseQuery args =
  case args of
    [fmtArg, solverArg] -> do
      fmt <-
        case fmtArg of
          "tlsf" -> Just FmtTLSF
          "custom" -> Just FmtCustom
          _ -> Nothing
      (solver, debug) <-
        case solverArg of
          "tg" -> Just (STTimerGame, False)
          "tgverbose" -> Just (STTimerGame, True)
          "printf" -> Just (STPrintFormula, False)
          _ -> Nothing
      Just (SolverQuery {format = fmt, solverType = solver, debugging = debug})
    _ -> Nothing

main :: IO ()
main = do
  args <- getArgs
  case parseQuery args of
    Nothing -> help
    Just query -> do
      input <- getContents
      case solve query input of
        Left err -> hPutStr stderr (err ++ "\n")
        Right res -> res >>= print
