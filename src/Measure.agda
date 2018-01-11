module Measure where

open import Data.Float 
open import Agda.Builtin.Float 
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat
open import Function

data Measure {α} (A : Set α) : Set α  where
  measure : ((A → Float) → Float) → Measure A 

integrate : ∀ {α} {A : Set α} → (A → Float) → Measure A → Float
integrate f (measure x) = x f

integrateProp₁ : ∀ {α} {A : Set α} → (mu : Measure A) → (f g : A → Float) → (f ≡ g) → (integrate f mu) ≡ (integrate g mu)
integrateProp₁ mu f g refl = refl

integrateProp₂ : ∀ {α} {A : Set α} → (mu₁ mu₂ : Measure A) → (f : A → Float) → (mu₁ ≡ mu₂) → (integrate f mu₁) ≡ (integrate f mu₂)
integrateProp₂ mu₁ mu₂ f refl = refl

plusOne : Float → Float
plusOne x = primFloatPlus (primNatToFloat 1) x

measurePlusOne : Measure Float → Float
measurePlusOne mu = integrate plusOne mu

plusN : (n : ℕ) → Float
plusN zero = primNatToFloat zero
plusN (suc n) = primFloatPlus (primNatToFloat 1) (plusN n)

measurePlusN : Measure ℕ → Float
measurePlusN mu = integrate plusN mu

mapMeasure : ∀ {α β} {A : Set α}{B : Set β} → (A → B) → Measure A → Measure B
mapMeasure f mu = measure (λ g → integrate (g ∘ f) mu)

pureMeasure : ∀ {α} {A : Set α} → A → Measure A
pureMeasure x = measure λ f → f x

apMeasure : ∀ {α β} {A : Set α}{B : Set β} → Measure (A → B) → Measure A → Measure B
apMeasure (measure f) (measure x) = measure (λ g → f (λ h → x (g ∘ h)))

measureBind : ∀ {α β} {A : Set α}{B : Set β} → Measure A → (A → Measure B) → Measure B
measureBind x f = measure λ g → integrate (λ h → integrate g (f h)) x

join : ∀ {α} {A : Set α} → Measure (Measure A) → Measure A
join f = measureBind f id

