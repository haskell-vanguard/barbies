{-# LANGUAGE QuantifiedConstraints #-}
module Data.Barbie.Internal.Nested
  ( Nested(..)
  , runNestedF
  , runNestedA
  ) where

import Data.Barbie.Internal.Functor (FunctorB(..), FunctorB_(..))

import qualified Data.Functor.Yo as Yo

newtype Nested c b f
  = Nested (b (Yo.Yo c f) f)

runNestedF :: (Functor f, FunctorB_ b) => Nested Functor b f -> b f f
runNestedF (Nested byf)
  = bmap_ Yo.lowerYo byf

runNestedA :: (Applicative f, FunctorB_ b) => Nested Functor b f -> b f f
runNestedA (Nested byf)
  = bmap_ Yo.lowerYo byf

instance (FunctorB_ b, forall f. (FunctorB (b (Yo.Yo c f)))) => FunctorB (Nested c b) where
  bmap h (Nested byf)
    = Nested $ bmap_ (Yo.hoistYo h) $ bmap h byf

