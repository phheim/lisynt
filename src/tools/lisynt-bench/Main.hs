{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Set hiding (null)
import Data.Time

import System.Environment
import System.Exit
import System.IO
import System.Timeout

import LISynt
import LogicToTG (formulaToTG)
import TimerGame (timers, vertecies)
import TimerGameSafetySolving (sufficentAttractor)

timeDiff :: UTCTime -> UTCTime -> Integer
timeDiff tEnd tStart = round (1000 * toRational (diffUTCTime tEnd tStart))

run :: IO ()
run = do
  input <- getContents
  formula <-
    case parseFormula False input of
      Left e1 ->
        case parseFormula True input of
          Left e2 -> do
            hPutStr stderr ("Custom Parser: " ++ e1 ++ "\n")
            hPutStr stderr ("TLSF Parser: " ++ e2 ++ "\n")
            exitFailure
          Right f -> return f
      Right f -> return f
  tStart <- getCurrentTime
  (game, init, bad, _, _) <- return (formulaToTG formula)
  tEnd <- getCurrentTime
  putStr "|Locations|: "
  putStrLn (show (size (vertecies game)))
  putStr "|Timers|: "
  putStrLn (show (size (timers game)))
  putStr "Generation Time (ms): "
  putStrLn (show (timeDiff tEnd tStart))
  if null bad
    then do
      putStrLn "Approximation (k): 0"
      putStrLn "Realizable: True"
    else do
      (_, res, k) <- sufficentAttractor game init bad
      putStr "Approximation (k): "
      putStrLn (show k)
      putStr "Realizable: "
      putStrLn (show res)

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  args <- getArgs
  let tm =
        case args of
          [] -> 10
          tm:_ -> read tm :: Int
  tStart <- getCurrentTime
  out <- timeout (tm * 1000000) run
  tEnd <- getCurrentTime
  putStr "Runtime (ms): "
  case out of
    Just _ -> print (timeDiff tEnd tStart)
    Nothing -> putStrLn "TO"
