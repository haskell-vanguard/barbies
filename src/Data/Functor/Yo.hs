{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | @'Yo' 'Functor' f@, @'Yo' 'Applicative' f@, and @'Yo' 'Monad' f@ are
--   naturally isomorphic to @f@, via `liftYo` and `lowerYo`, whenever @f@ is
--   a 'Functor', 'Applicative' or 'Monad', respectively. The 'Functor',
--   'Applicative' and 'Monad' instances for @'Yo' c f@ have no requierments
--   on @f@.
module Data.Functor.Yo
  ( Yo
  , Lemma(..)
  , liftYo
  , hoistYo
  )

where


type family c :<= d where
  c :<= c = 'True
  Functor :<= Applicative = 'True
  Functor :<= Monad = 'True
  Applicative :<= Monad = 'True
  _ :<= _ = 'False

type c |- d
  = d :<= c ~ 'True


data Yo c f a where
  Lift  :: f a -> Yo c f a
  Hoist :: (forall x. f x -> g x) -> Yo c f a -> Yo c g a
  Map   :: c |- Functor => (a -> b) -> Yo c f a -> Yo c f b
  Pure  :: c |- Applicative => a -> Yo c f a
  Apply :: c |- Applicative => Yo c f (a -> b) -> Yo c f a -> Yo c f b
  Bind  :: c |- Monad  => Yo c f a -> (a -> Yo c f b) -> Yo c f b


liftYo :: f a -> Yo c  f a
liftYo = Lift

hoistYo :: (forall x. f x -> g x) -> Yo c f a -> Yo c g a
hoistYo = Hoist

instance c |- Functor => Functor (Yo c f) where
  fmap = Map

instance (c |- Functor, c |- Applicative) => Applicative (Yo c f) where
  pure
    = Pure
   
  (<*>)
    = Apply

instance Monad (Yo Monad f) where
  (>>=) = Bind

-- | @'Lemma' c@, together with 'liftYo' give us a
--   isomorphism between @'Yo' c f@ and @f@.
class Lemma c where
  lowerYo :: c f => Yo c f a -> f a

instance Lemma Functor where
  lowerYo = go id id
    where
      go :: Functor g => (a -> b) -> (forall x. f x -> g x) -> Yo Functor f a -> g b
      go f h = \case
        Lift fa    -> f <$> h fa
        Hoist i fa -> go f (h . i) fa
        Map   g fa -> go (f . g) h fa

instance Lemma Applicative where
  lowerYo = go id id
    where
      go :: Applicative g => (a -> b) -> (forall x. f x -> g x) -> Yo Applicative f a -> g b
      go f h = \case
        Lift fa     -> f <$> h fa
        Hoist i fa  -> go f (h . i) fa
        Map   g fa  -> go (f . g) h fa
        Pure  a     -> pure (f a)
        Apply ff fa -> f <$> (go id  h ff <*> go id  h fa)

instance Lemma Monad where
  lowerYo = go id id
    where
      go :: Monad g => (a -> b) -> (forall x. f x -> g x) -> Yo Monad f a -> g b
      go f h = \case
        Lift fa      -> f <$> h fa
        Hoist i fa   -> go f (h . i) fa
        Map   g fa   -> go (f . g) h fa
        Pure  a      -> pure (f a)
        Apply ff fa  -> f <$> (go id  h ff <*> go id  h fa)
        Bind fa afb  -> go id h fa >>= \a -> go f h (afb a)
