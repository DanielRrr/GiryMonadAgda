module NumericalStuff where

open import Data.Float
open import Agda.Builtin.Float
open import Agda.Builtin.Int
open import Agda.Builtin.Nat
open import Data.List

nList : Nat → List Nat
nList zero = [ zero ]
nList (suc x) = suc x ∷ nList x

orderednList : Nat → List Nat
orderednList x = reverse (nList x)
