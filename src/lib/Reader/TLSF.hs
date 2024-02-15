-------------------------------------------------------------------------------
-- | 
-- Module       :   Reader.TLSF
--
-- 'FromTLSF' reads formulas given in the TLSF format using syfco.
--
-------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}

-------------------------------------------------------------------------------
module Reader.TLSF
  ( fromTLSF
  , syf2expr
  , tlsfToBLTL
  ) where

-------------------------------------------------------------------------------
import BLTL (BLTL, toBLTL, unexpandNext)
import Expansion (optimize)
import Logic

import qualified Syfco (Atomic(..), Formula(..), applyF, defaultCfg, fromTLSF)

-------------------------------------------------------------------------------
-- | 'tlsfToBLTL' reads a TLSF formula with syfco and transform it to 'BLTL'
-- formula by approximating all eventually operators with its bound version 
-- using the given bound. In addition a threshold is used to unexpand next
-- chains
tlsfToBLTL :: Word -> String -> Either String (BLTL Word)
tlsfToBLTL threshold content = do
  expr <- fromTLSF content
  bf <- toBLTL Nothing Right expr
  Right (unexpandNext threshold (optimize bf))

-------------------------------------------------------------------------------
-- | 'fromTLSF' reads a TLSF formula with syfco and transform it to an 
-- 'LTLExpr'
fromTLSF :: String -> Either String (LTLExpr Word AP)
fromTLSF content =
  case Syfco.fromTLSF content of
    Left err -> Left (show err)
    Right spec ->
      case Syfco.applyF Syfco.defaultCfg spec of
        Left err -> Left (show err)
        Right f -> Right (syf2expr f)

-------------------------------------------------------------------------------
-- | 'syf2expr' transforms a 'Syfco' formula into an equivalent 'LTLExpr'
syf2expr :: Syfco.Formula -> LTLExpr Word AP
syf2expr =
  \case
    Syfco.TTrue -> etrue
    Syfco.FFalse -> efalse
    Syfco.Atomic (Syfco.Input s) -> eap (Input s)
    Syfco.Atomic (Syfco.Output s) -> eap (Output s)
    Syfco.Not f -> un enot f
    Syfco.And fs -> mult eand fs
    Syfco.Or fs -> mult eor fs
    Syfco.Implies f g -> bin eimpl f g
    Syfco.Equiv f g -> bin eiff f g
    Syfco.Next f -> un enext f
    Syfco.Globally f -> un eglobally f
    Syfco.Finally f -> un eeventually f
    Syfco.Weak f g -> bin eweak f g
    Syfco.Until f g -> bin euntil f g
    Syfco.Release f g -> bin erelease f g
    _ -> error "Past operators are not supported yet"
  where
    un op f = op (syf2expr f)
    bin op f g = op (syf2expr f) (syf2expr g)
    mult op fs = op (map syf2expr fs)
-------------------------------------------------------------------------------
