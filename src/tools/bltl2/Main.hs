{-# LANGUAGE LambdaCase #-}

module Main where

import System.Environment
import System.IO

import LISynt
import Writer.BLTL

help :: IO ()
help = hPutStr stderr ("Usage: bltl2 [tlsf | custom-smv]\n")

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["tlsf"] -> do
      input <- getContents
      case parseFormula False input of
        Left e -> hPutStr stderr (e ++ "\n")
        Right f -> putStrLn (writeTLSF f)
    ["custom-smv"] -> do
      input <- getContents
      case parseFormula False input of
        Left e -> hPutStr stderr (e ++ "\n")
        Right f -> putStrLn (writeCustomSMV f)
    _ -> help
