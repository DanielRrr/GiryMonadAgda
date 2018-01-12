{-# OPTIONS --allow-unsolved-metas #-}

module Implementations where

open import Measure
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Float
open import Agda.Builtin.Float
open import Function
open import CategoryStructures
open import Level

functorMeasure : ∀ {α} → Functor (Measure {α})
functorMeasure = record { fmap = mapMeasure}

applicativeMeasure : ∀ {α} {{fun : Functor (Measure {α})}}→ Applicative (Measure {α})
applicativeMeasure = record { pure = pureMeasure ; _<*>_ = apMeasure}

monadMeasure : ∀ {α} {{fun : Functor (Measure {α})}} {{app : Applicative (Measure {α})}} → Monad (Measure {α})
monadMeasure = mkMonad pureMeasure measureBind



