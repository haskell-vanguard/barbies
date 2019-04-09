{-# LANGUAGE ImpredicativeTypes #-} -- needed due to bug in ghc 8.6.x, see https://gitlab.haskell.org/ghc/ghc/issues/16140
{-# LANGUAGE QuantifiedConstraints #-}
module Data.Barbie.Bi
  ( -- * Bifunctor
    BifunctorB
  , bfirst
  , bsecond
  , bbimap

  ) where

import Data.Barbie.Internal.Functor(FunctorB(..), FunctorB_(..))


-- | A barbie-functor on two arguments
type BifunctorB b
  = (FunctorB_ b, (forall f. FunctorB (b f)))

-- | Map covariantly over the first argument.
bfirst :: BifunctorB b => (forall a. f a -> f' a) -> b f g -> b f' g
bfirst = bmap_
{-# INLINE bfirst #-}

-- | Map covariantly over the second argument.
bsecond :: BifunctorB b => (forall a. g a -> g' a) -> b f g -> b f g'
bsecond = bmap
{-# INLINE bsecond #-}

-- | Map over both arguments simultaneously
bbimap :: BifunctorB b => (forall a. f a -> f' a) -> (forall a. g a -> g' a) -> b f g -> b f' g'
bbimap h i
  = bfirst h . bsecond i
{-# INLINE bbimap #-}

