{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-} -- See Note [Impredicative Σ?]
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Singletons.Sigma
-- Copyright   :  (C) 2017 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines 'Sigma', a dependent pair data type, and related functions.
--
----------------------------------------------------------------------------

module Data.Singletons.Sigma
    ( Sigma(..), Σ, SSigma(..), SΣ
    , projSigma1, projSigma2, ProjSigma1, ProjSigma2
    , mapSigma, zipSigma, currySigma, uncurrySigma
    ) where

import Data.Kind (Type)
import Data.Singletons.Internal

-- | A dependent pair.
data Sigma (s :: Type) :: (s ~> Type) -> Type where
  (:&:) :: forall s t fst. Sing (fst :: s) -> t @@ fst -> Sigma s t
infixr 4 :&:

-- | Unicode shorthand for 'Sigma'.
type Σ = Sigma

-- | TODO RGS: Docs
data SSigma :: forall s (t :: s ~> Type). Sigma s t -> Type where
  (:%&:) :: forall s t (fst :: s) (sfst :: Sing fst) (snd :: t @@ fst).
            Sing ('WrapSing sfst) -> Sing snd -> SSigma (sfst ':&: snd :: Sigma s t)
infixr 4 :%&:
type instance Sing = SSigma

-- | Unicode shorthand for 'SSigma'.
type SΣ = SSigma

{-
Note [Impredicative Σ?]
~~~~~~~~~~~~~~~~~~~~~~~
The definition of Σ currently will not typecheck without the use of
ImpredicativeTypes. There isn't a fundamental reason that this should be the
case, and the only reason that GHC currently requires this is due to Trac
#13408. If someone ever fixes that bug, we could remove the use of
ImpredicativeTypes.
-}

-- | Project the first element out of a dependent pair.
projSigma1 :: forall s t. SingKind s => Sigma s t -> Demote s
projSigma1 (a :&: _) = fromSing a

-- | TODO RGS: Docs
type family ProjSigma1 (sig :: Sigma s t) :: s where
  ProjSigma1 ((_ :: Sing fst) ':&: _) = fst

-- | Project the second element out of a dependent pair.
projSigma2 :: forall s t (sig :: Sigma s t).
              SingKind (t @@ ProjSigma1 sig)
           => Sing sig -> Demote (t @@ ProjSigma1 sig)
projSigma2 (_ :%&: b) = fromSing b

-- | TODO RGS: Docs
type family ProjSigma2 (sig :: Sigma s t) :: t @@ ProjSigma1 sig where
  ProjSigma2 (_ ':&: t) = t

-- | Map across a 'Sigma' value in a dependent fashion.
mapSigma :: Sing (f :: a ~> b) -> (forall (x :: a). p @@ x -> q @@ (f @@ x))
         -> Sigma a p -> Sigma b q
mapSigma f g ((x :: Sing (fst :: a)) :&: y) = (f @@ x) :&: (g @fst y)

-- | Zip two 'Sigma' values together in a dependent fashion.
zipSigma :: Sing (f :: a ~> b ~> c)
         -> (forall (x :: a) (y :: b). p @@ x -> q @@ y -> r @@ (f @@ x @@ y))
         -> Sigma a p -> Sigma b q -> Sigma c r
zipSigma f g ((a :: Sing (fstA :: a)) :&: p) ((b :: Sing (fstB :: b)) :&: q) =
  (f @@ a @@ b) :&: (g @fstA @fstB p q)

-- | TODO RGS: Docs
currySigma :: forall a (b :: a ~> Type) (c :: Sigma a b ~> Type).
              (forall (p :: Sigma a b). Sing p -> c @@ p)
           -> (forall (x :: a) (sx :: Sing x) (y :: b @@ x).
                 Sing ('WrapSing sx) -> Sing y -> c @@ (sx ':&: y))
currySigma f x y = f (x :%&: y)

-- | TODO RGS: Docs
uncurrySigma :: forall a (b :: a ~> Type) (c :: Sigma a b ~> Type).
                (forall (x :: a) (sx :: Sing x) (y :: b @@ x).
                   Sing ('WrapSing sx) -> Sing y -> c @@ (sx ':&: y))
             -> (forall (p :: Sigma a b). Sing p -> c @@ p)
uncurrySigma f (x :%&: y) = f x y
