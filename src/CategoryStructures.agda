module CategoryStructures where

open import Function
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Float
open import Agda.Builtin.Float


record Functor {α} (F : Set α → Set α) : Set (suc α) where
  constructor mkFunctor
  infixl 4 _<$>_ _<$_ _$>_
  field
    fmap : ∀ {A B : Set α} → (A → B) → F A → F B
  _<$>_ : ∀ {A B : Set α} → (A → B) → F A → F B
  _<$>_ = fmap
  _<$_ : ∀ {A B : Set α} → A → F B → F A
  _<$_ = fmap ∘ const
  _$>_ : ∀ {A B : Set α} → F A → B → F B
  _$>_ = flip (fmap ∘ const)
open Functor {{...}} public

record Applicative {α} (F : Set α → Set α) {{fun : Functor F}} : Set (suc α) where
  constructor mkApplicative
  infixl 2 _<*>_ _<**>_ _<*_ _*>_
  field
    pure : ∀ {A : Set α} → A → F A
    _<*>_ : ∀ {A B : Set α} → F (A → B) → F A → F B
  liftA : ∀ {A B : Set α} → (A → B) → F A → F B
  liftA f x = (pure f) <*> x

  _<**>_ : ∀ {A B : Set α} → F A → F (A → B) → F B
  _<**>_ = flip _<*>_
open Applicative {{...}} public

record Monad {α} (F : Set α → Set α) {{fun : Functor F}} {{app : Applicative F}} : Set (suc α) where
  constructor mkMonad
  infixl 1 _>>=_ _>>_
  field
    return : ∀ {A : Set α} → A → F A
    _>>=_ : ∀ {A B : Set α} → F A → (A → F B) → F B
  infixr 1 _=<<_
  _=<<_ : ∀ {A B : Set α} → (A → F B) → F A → F B
  f =<< x = x >>= f

  bind : ∀ {A B : Set α} → (A → F B) → F A → F B
  bind f x = x >>= f
  _>>_ : ∀ {A B : Set α} → F A → F B → F B
  mx >> my = mx >>= (const my)
  liftM : ∀ {A B : Set α} → (A → B) → F A → F B
  liftM f x = x >>= (λ x → return (f x))
  join : ∀ {A : Set α} → F (F A) → F A
  join f = f >>= id
open Monad {{...}} public

record ProvabilityMonad (F : Set → Set) {{fun : Functor F}} {{app : Applicative F}} {{m : Monad F}} : Set₁ where
  constructor mkProvabilityMonad
  field
    choose : {A : Set} → Float → F A → F A → F A
open ProvabilityMonad {{...}} public

record VerifiedFunctor {α} (F : Set α → Set α) {{fun : Functor F}} : Set (suc α) where
  constructor mkVerifiedFunctor
  field
    resp-id : ∀ {A : Set α} → (x : F A) → (fmap id x) ≡ x
    resp-∘ : {A B C : Set α}(g : B → C)(f : A → B)(fx : F A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx
open VerifiedFunctor {{...}} public
