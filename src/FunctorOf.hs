{-# language DeriveFunctor #-}
{-# Language FlexibleContexts #-}
{-# lAnguage FlexibleInstances #-}
{-# laNguage GADTs #-}
{-# lanGuage InstanceSigs #-}
{-# langUage MultiParamTypeClasses #-}
{-# languAge NamedFieldPuns #-}
{-# languaGe PolyKinds #-}
{-# languagE RankNTypes #-}
{-# lAnGuAgE TypeOperators #-}
{-# LaNgUaGe UndecidableInstances #-}

module FunctorOf where

import Data.Monoid (Endo(..))
import Data.Kind (Type)
import Prelude ((==), id, Bool, Int, String, Functor(..), ($), show, read, (+), (.))
import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Contravariant (Contravariant(..), Op(..), Predicate(..))
import Data.Profunctor (Profunctor(..))

class FunctorOf (p :: k -> k -> Type) (q :: l -> l -> Type) f where
  map :: p a b -> q (f a) (f b)

---------------------------------------------------------------------------------
-- Functor
instance Functor f => FunctorOf (->) (->) f where
  map :: forall a b. (a -> b) -> f a -> f b
  map = fmap

functorExample :: [String]
functorExample = map show ([1, 2, 3, 4] :: [Int])

---------------------------------------------------------------------------------
-- Bifunctor
newtype (~>) f g = Natural (forall x. f x -> g x)
  
instance Bifunctor f => FunctorOf (->) (~>) f where
  map :: forall a b. (a -> b) -> f a ~> f b
  map f = Natural $ first f

bimap'
  :: forall a b c d f
  .  FunctorOf (->) (->) (f a)
  => FunctorOf (->) (~>) f
  => (a -> b)
  -> (c -> d)
  -> f a c
  -> f b d
bimap' f g fac =
  case map f of
    Natural a2b -> a2b (map g fac)

bifunctorExample :: (String, String)
bifunctorExample = bimap' show show (1 :: Int, 1 :: Int)

---------------------------------------------------------------------------------
-- Contravariant
instance Contravariant f => FunctorOf Op (->) f where
  map :: forall a b. (Op b a) -> f b -> f a
  map (Op f) = contramap f

cmap
  :: forall a b f
  .  FunctorOf Op (->) f
  => (b -> a)
  -> f a
  -> f b
cmap f fa = map (Op f) fa

contraExample :: Predicate Int
contraExample = cmap show (Predicate (== "5"))

---------------------------------------------------------------------------------
-- Profunctor
instance Profunctor p => FunctorOf Op (~>) p where
  map :: forall a b. (Op b a) -> p b ~> p a
  map (Op f) = Natural $ lmap f

dimap'
  :: forall a b c d p
  .  FunctorOf (->) (->) (p a)
  => FunctorOf Op   (~>) p
  => (b -> a)
  -> (c -> d)
  -> p a c
  -> p b d
dimap' f g pac =
  case map (Op f) of
    Natural b2a -> b2a (map g pac)

profunctorExample :: String -> String
profunctorExample = dimap' read show (+ (1 :: Int))

---------------------------------------------------------------------------------
-- Tri..functor
newtype (~~>) f g = NatNat (forall x. f x ~> g x)

data Triple a b c = Triple a b c deriving (Functor)

instance {-# overlapping #-} FunctorOf (->) (~>) (Triple x) where
  map :: forall a b. (a -> b) -> Triple x a ~> Triple x b
  map f = Natural $ \(Triple x a y) -> Triple x (f a) y

instance FunctorOf (->) (~~>) Triple where
  map :: (a -> b) -> Triple a ~~> Triple b
  map f = NatNat $ Natural $ \(Triple a x y) -> Triple (f a) x y

triple
  :: forall a b c d e f t
  .  FunctorOf (->) (->)  (t a c)
  => FunctorOf (->) (~>)  (t a)
  => FunctorOf (->) (~~>) t
  => (a -> b)
  -> (c -> d)
  -> (e -> f)
  -> t a c e
  -> t b d f
triple f g h = a2b . c2d . map h
  where
    (Natural c2d) = map g
    (NatNat (Natural a2b)) = map f

tripleExample :: Triple String String String
tripleExample = triple show show show (Triple (1 :: Int) (2 :: Int) (3 :: Int))

---------------------------------------------------------------------------------
-- Invariant
data Iso a b = Iso
  { to   :: a -> b
  , from :: b -> a
  }

instance FunctorOf Iso (->) Endo where
  map :: forall a b. Iso a b -> Endo a -> Endo b
  map Iso { to, from } (Endo f) = Endo $ to . f . from

endo :: Endo String
endo = map (Iso show read) (Endo (+ (1 :: Int)))

---------------------------------------------------------------------------------
-- Isomorphisms
instance FunctorOf (->) (->) f => FunctorOf Iso Iso f where
  map :: Iso a b -> Iso (f a) (f b)
  map Iso { to, from } = Iso (map to) (map from)

---------------------------------------------------------------------------------
-- Refl
data x :~: y where
  Refl :: x :~: x
 
instance FunctorOf (:~:) (->) ((:~:) x) where
  map :: forall a b. a :~: b -> x :~: a -> x :~: b
  map Refl Refl = Refl

proof :: Int :~: String -> Bool :~: Int -> Bool :~: String
proof = map

instance FunctorOf (:~:) (~>) (:~:) where
  map :: forall a b. a :~: b -> (:~:) a ~> (:~:) b
  map Refl = Natural $ id

proof' :: Int :~: String -> Int :~: Bool -> String :~: Bool
proof' i2s i2b =
  case map i2s of
    Natural nat -> nat i2b
