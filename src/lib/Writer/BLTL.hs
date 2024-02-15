{-# LANGUAGE LambdaCase #-}

module Writer.BLTL
  ( writeTLSF
  , writeCustomSMV
  ) where

import BLTL
import Logic

import Data.Set as Set (Set, empty, singleton, toList, unions)

addOp :: a -> [a] -> [a]
addOp op =
  \case
    [] -> []
    [f] -> [f]
    f:fr -> f : op : addOp op fr

writeTLSF :: BLTL Word -> String
writeTLSF f =
  let ins = nameAP <$> filter inputAP (toList (litsBLTL f))
      outs = nameAP <$> filter outputAP (toList (litsBLTL f))
   in unlines $
      [ "INFO {"
      , " TITLE: \"BLTL formula\""
      , " DESCRIPTION: \"Formula generated out of BLTL file\""
      , " SEMANTICS: Mealy"
      , " TARGET: Mealy"
      , "}"
      , "MAIN {"
      , " INPUTS {"
      ] ++
      map (++ ";") ins ++
      ["}", " OUTPUTS {"] ++
      map (++ ";") outs ++
      ["}", "GUARANTEE {"] ++ ["  " ++ bltl2TLSF f] ++ [" }", "}"]

writeCustomSMV :: BLTL Word -> String
writeCustomSMV f =
  let ins = nameAP <$> filter inputAP (toList (litsBLTL f))
      outs = nameAP <$> filter outputAP (toList (litsBLTL f))
   in unlines
        [ toCSMV f
        , "INPUT: " ++ concat (addOp ", " ins)
        , "OUTPUT: " ++ concat (addOp ", " outs)
        ]

toCSMV :: BLTL Word -> String
toCSMV =
  \case
    Lit (val, var)
      | val -> nameAP var
      | otherwise -> "(! " ++ nameAP var ++ ")"
    TTrue -> "TRUE"
    FFalse -> "FALSE"
    And fs -> rAnd fs
    Or fs -> rOr fs
    Next f -> "(X " ++ toCSMV f ++ ")"
    BNext c f -> "(" ++ rep c ++ toCSMV f ++ ")"
    BGlobally c f fs -> par $ bOpUn "G[0," c f ++ " & " ++ rAnd fs
    BFinally c f fs -> par $ bOpUn "F[0," c f ++ " | " ++ rOr fs
    Globally f fs -> par $ "(G " ++ toCSMV f ++ ") & " ++ rAnd fs
    _ -> error "TODO: Not supported yet"
  where
    recL :: String -> String -> [BLTL Word] -> String
    recL neutral op fs =
      case fs of
        [] -> neutral
        [f] -> toCSMV f
        _ -> "(" ++ concat (addOp op (map toCSMV fs)) ++ ")"
    rep c
      | c <= 0 = ""
      | otherwise = "X " ++ rep (c - 1)
    par s = "(" ++ s ++ ")"
    bOpUn op k f = "(" ++ op ++ show k ++ "] " ++ toCSMV f ++ ")"
    rOr = recL "FALSE" " | "
    rAnd = recL "TRUE" " & "

bltl2TLSF :: BLTL Word -> String
bltl2TLSF =
  \case
    Lit (val, var)
      | val -> nameAP var
      | otherwise -> "(! " ++ nameAP var ++ ")"
    TTrue -> "true"
    FFalse -> "false"
    And fs -> rAnd fs
    Or fs -> rOr fs
    Next f -> "(X " ++ bltl2TLSF f ++ ")"
    BNext c f -> bOpUn "X[" c f
    BGlobally c f fs -> par $ bOpUn "G[0:" c f ++ " && " ++ rAnd fs
    BFinally c f fs -> par $ bOpUn "F[0:" c f ++ " || " ++ rOr fs
    Globally f fs -> par $ "(G " ++ bltl2TLSF f ++ ") && " ++ rAnd fs
    WeakUntil f g fs gs ->
      par $
      "((" ++
      bltl2TLSF f ++
      " W " ++ bltl2TLSF g ++ ") && " ++ rAnd fs ++ ") || " ++ rOr gs
    -- WARNING: This is quite hacky
    AssumeFinally f fs -> "((F " ++ bltl2TLSF f ++ ") ||" ++ rOr fs ++ ")"
    _ -> error "TODO: Not supported yet"
  where
    recL :: String -> String -> [BLTL Word] -> String
    recL neutral op fs =
      case fs of
        [] -> neutral
        [f] -> bltl2TLSF f
        _ -> "(" ++ concat (addOp op (map bltl2TLSF fs)) ++ ")"
    par s = "(" ++ s ++ ")"
    bOpUn op k f = "(" ++ op ++ show k ++ "] " ++ bltl2TLSF f ++ ")"
    rOr = recL "false" " || "
    rAnd = recL "true" " && "

litsBLTL :: BLTL Word -> Set AP
litsBLTL =
  \case
    Lit (_, ap) -> singleton ap
    TTrue -> empty
    FFalse -> empty
    And fs -> unions (map litsBLTL fs)
    Or fs -> unions (map litsBLTL fs)
    Next f -> litsBLTL f
    BNext _ f -> litsBLTL f
    BGlobally _ f fs -> rec2 f fs
    BFinally _ f fs -> rec2 f fs
    BWeakUntil _ f g fs gs -> rec4 f g fs gs
    BUntil _ f g fs gs -> rec4 f g fs gs
    Globally f fs -> rec2 f fs
    WeakUntil f g fs gs -> rec4 f g fs gs
    AssumeFinally f fs -> rec2 f fs
  where
    rec2 f fs = unions (litsBLTL f : map litsBLTL fs)
    rec4 f g fs gs =
      unions (litsBLTL f : litsBLTL g : map litsBLTL fs ++ map litsBLTL gs)
