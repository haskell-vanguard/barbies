{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeFamilies        #-}
module Data.Barbie.Internal.Functor
  ( FunctorB(..)
  , FunctorB_(..)

  , GFunctorB(..)
  , CanDeriveFunctorB
  , CanDeriveFunctorB_
  )

where

import Data.Functor.Compose   (Compose (..))
import Data.Functor.Const     (Const (..))
import Data.Functor.Product   (Product (..))
import Data.Functor.Sum       (Sum (..))
import Data.Generics.GenericN
import Data.Proxy             (Proxy (..))
import Data.Kind              (Type)

-- | Barbie-types that can be mapped over. Instances of 'FunctorB' should
--   satisfy the following laws:
--
-- @
--   'bmap' 'id' = 'id'
--   'bmap' f . 'bmap' g = 'bmap' (f . g)
-- @
--
-- There is a default 'bmap' implementation for 'Generic' types, so
-- instances can derived automatically.
class FunctorB (b :: (k -> Type) -> Type) where
  bmap :: (forall a . f a -> g a) -> b f -> b g

  default bmap
    :: forall f g
    .  CanDeriveFunctorB b f g
    => (forall a . f a -> g a) -> b f -> b g
  bmap h
    = toN . gbmap @0 h . fromN
  {-# INLINE bmap #-}

-- | @'CanDeriveFunctorB' B f g@ is in practice a predicate about @B@ only.
--   Intuitively, it says that the following holds, for any arbitrary @f@:
--
--     * There is an instance of @'Generic' (B f)@.
--
--     * @B f@ can contain fields of type @b f@ as long as there exists a
--       @'FunctorB' b@ instance. In particular, recursive usages of @B f@
--       are allowed.
--
--     * @B f@ can also contain usages of @b f@ under a @'Functor' h@.
--       For example, one could use @'Maybe' (B f)@ when defining @B f@.
type CanDeriveFunctorB b f g
  = ( GenericN (b f)
    , GenericN (b g)
    , GFunctorB 0 f g (RepN (b f)) (RepN (b g))
    )

-- | A version of 'FunctorB' where the argument is in the next to last
--   position. This includes monad transformers and bifunctors (see
--   'Data.Barbie.Internal.Bi.BifunctorB').
--
--   A 'FunctorB_' can be used as a 'FunctorB' via
--   'Data.Barbie.Internal.FlipB.FlipB'.
class FunctorB_ (b :: (k -> Type) -> k2 -> Type) where
  bmap_ :: (forall a . f a -> g a) -> b f x -> b g x

  default bmap_
    :: forall f g x
    .  CanDeriveFunctorB_ b f g x
    => (forall a . f a -> g a) -> b f x -> b g x
  bmap_ h
    = toN . gbmap @1 h . fromN
  {-# INLINE bmap_ #-}


-- | See 'CanDeriveFunctorB'
type CanDeriveFunctorB_ b f g x
  = ( GenericN (b f x)
    , GenericN (b g x)
    , GFunctorB 1 f g (RepN (b f x)) (RepN (b g x))
    )

class GFunctorB n f g repbf repbg where
  gbmap :: (forall a . f a -> g a) -> repbf x -> repbg x


-- ----------------------------------
-- Trivial cases
-- ----------------------------------

instance GFunctorB n f g bf bg => GFunctorB n f g (M1 i c bf) (M1 i c bg) where
  gbmap h = M1 . gbmap @n h . unM1
  {-# INLINE gbmap #-}

instance GFunctorB n f g V1 V1 where
  gbmap _ _ = undefined

instance GFunctorB n f g U1 U1 where
  gbmap _ = id
  {-# INLINE gbmap #-}

instance(GFunctorB n f g l l', GFunctorB n f g r r') => GFunctorB n f g (l :*: r) (l' :*: r') where
  gbmap h (l :*: r) = (gbmap @n h l) :*: gbmap @n h r
  {-# INLINE gbmap #-}

instance(GFunctorB n f g l l', GFunctorB n f g r r') => GFunctorB n f g (l :+: r) (l' :+: r') where
  gbmap h = \case
    L1 l -> L1 (gbmap @n h l)
    R1 r -> R1 (gbmap @n h r)
  {-# INLINE gbmap #-}


-- --------------------------------
-- The interesting cases
-- --------------------------------

type P = Param

instance GFunctorB n f g (Rec (P n f a) (f a))
                         (Rec (P n g a) (g a)) where
  gbmap h (Rec (K1 fa)) = Rec (K1 (h fa))
  {-# INLINE gbmap #-}

instance
  ( SameOrParam b b'
  , FunctorB b'
  ) => GFunctorB n f g (Rec (b (P n f)) (b' f))
                       (Rec (b (P n g)) (b' g)) where
  gbmap h (Rec (K1 bf)) = Rec (K1 (bmap h bf))
  {-# INLINE gbmap #-}

instance
  ( SameOrParam h h'
  , SameOrParam b b'
  , Functor h'
  , FunctorB b'
  ) => GFunctorB n f g (Rec (h (b (P n f))) (h' (b' f)))
                       (Rec (h (b (P n g))) (h' (b' g))) where
  gbmap h (Rec (K1 hbf)) = Rec (K1 (fmap (bmap h) hbf))
  {-# INLINE gbmap #-}

instance GFunctorB n f g (Rec x x) (Rec x x) where
  gbmap _ = id
  {-# INLINE gbmap #-}


-- --------------------------------
-- Instances for base types
-- --------------------------------

instance FunctorB Proxy where
  bmap _ _ = Proxy
  {-# INLINE bmap #-}

instance (FunctorB a, FunctorB b) => FunctorB (Product a b) where
  bmap f (Pair x y) = Pair (bmap f x) (bmap f y)
  {-# INLINE bmap #-}

instance (FunctorB a, FunctorB b) => FunctorB (Sum a b) where
  bmap f (InL x) = InL (bmap f x)
  bmap f (InR x) = InR (bmap f x)
  {-# INLINE bmap #-}

instance FunctorB (Const x) where
  bmap _ (Const x) = Const x
  {-# INLINE bmap #-}

instance (Functor f, FunctorB b) => FunctorB (f `Compose` b) where
  bmap h (Compose x) = Compose (bmap h <$> x)
  {-# INLINE bmap #-}
