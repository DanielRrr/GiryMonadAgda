module Measure where

open import Data.Float
open import Agda.Builtin.Float
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Nat
open import Function
open import Data.Product

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

expectation : Measure Float → Float
expectation = integrate id

dublicate : ∀ {α} {A : Set α} → Measure A → Measure (Measure A)
dublicate nu = pureMeasure nu

extendMeasure : ∀ {α} {A : Set α} {B : Set α} → (Measure A → B) → Measure A → Measure B
extendMeasure f nu = mapMeasure (f ∘ pureMeasure) nu

operationMeasure : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} → (A → B → C) → Measure A → Measure B → Measure C
operationMeasure f nu₁ nu₂ = apMeasure (apMeasure (pureMeasure f) nu₁) nu₂

addMeasureFloat : Measure Float → Measure Float → Measure Float
addMeasureFloat nu₁ nu₂ = operationMeasure primFloatPlus nu₁ nu₂

multMeasureFloat : Measure Float → Measure Float → Measure Float
multMeasureFloat nu₁ nu₂ = operationMeasure primFloatTimes nu₁ nu₂

2DArea : Float × Float → Float × Float → Float
2DArea (proj₃ , proj₄) (proj₅ , proj₆) = primFloatTimes (primFloatMinus proj₅ proj₃) (primFloatMinus proj₆ proj₄)

2DAreaMeasure : Measure (Float × Float) → Measure (Float × Float) → Measure Float
2DAreaMeasure nu₁ nu₂ = operationMeasure 2DArea nu₁ nu₂

chooseFun : ∀ {A : Set} → Float → Measure A → Measure A → Measure A
chooseFun num (measure x) (measure x₁) = measureBind (measure x) λ x → measureBind ((measure x₁)) λ y → measure λ g → num
