{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Axioms
open import Proto
open import Logic

open Σ

data ∥_∥ {u} (A : Type u) : Type u where
  ∣_∣ : A → ∥ A ∥

module _ {u} {A : Type u} (a b : ∥ A ∥) where
  postulate
    merely-hprop   : Path ∥ A ∥ (η a) (η b)

data ∥_∥₀ {u} (A : Type u) : Type u where
  ∣_∣₀ : A → ∥ A ∥₀
