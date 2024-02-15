{-# LANGUAGE LambdaCase #-}

module MapFold where

class MapFold t where
  mapFold :: (b -> a -> (c, b)) -> b -> t a -> (t c, b)

instance MapFold [] where
  mapFold m b =
    \case
      [] -> ([], b)
      x:xr ->
        let (x', b') = m b x
            (xr', b'') = mapFold m b' xr
         in (x' : xr', b'')
