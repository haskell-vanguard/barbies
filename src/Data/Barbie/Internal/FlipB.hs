{-# LANGUAGE CPP #-}
{-# LANGUAGE PolyKinds #-}
#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE QuantifiedConstraints #-}
#endif
module Data.Barbie.Internal.FlipB
  ( FlipB(..)
  ) where

import Data.Barbie.Internal.Functor(FunctorB(..), FunctorB_(..))

import Data.Kind(Type)


-- | Convert a 'FunctorB_' into a 'FunctorB' and vice-versa, etc.
newtype FlipB b (f :: k1 -> Type)  (g :: k2 -> Type)
  = FlipB { runFlipB :: b g f }

instance FunctorB_ b => FunctorB (FlipB b f) where
  bmap h (FlipB bfx)
    = FlipB (bmap_ h bfx)
  {-# INLINE bmap #-}


#if __GLASGOW_HASKELL__ >= 806
-- ** The following instances require QuantifiedConstraints ** --

instance (forall f. FunctorB (b f)) => FunctorB_ (FlipB b) where
  bmap_ h (FlipB bxf)
    = FlipB (bmap h bxf)
  {-# INLINE bmap_ #-}

#endif
