{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic
open import Basic

open Σ

data ∥_∥ {u} (A : Type u) : Type u where
  ∣_∣ : A → ∥ A ∥

module _ {u} {A : Type u} (a b : ∥ A ∥) where
  postulate
    merely-hprop   : C I (λ _ → ∥ A ∥)
    merely-hprop-0 : ap merely-hprop 0 ↦ a
    merely-hprop-1 : ap merely-hprop 1 ↦ a

  {-# REWRITE merely-hprop-0 merely-hprop-1 #-}

data ∥_∥₀ {u} (A : Type u) : Type u where
  ∣_∣₀ : A → ∥ A ∥₀
