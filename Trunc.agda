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
    merely-hprop   : Path ∥ A ∥ a b

data ∥_∥₀ {u} (A : Type u) : Type u where
  ∣_∣₀ : A → ∥ A ∥₀
