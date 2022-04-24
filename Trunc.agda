{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic
open import Basic

open Σ

data ∥_∥ {u} (A : Type u) : Type u where
  ∣_∣ : A → ∥ A ∥

module _ {u} {A : Type u} (a b : ∥ A ∥) where
  merely-hprop : I → ∥ A ∥
  merely-hprop i₀ = a 
  merely-hprop i₁ = b

  postulate merely-hprop-C : C merely-hprop

module _ {u v} {A : Type u}
         (B : ∥ A ∥ → Type v)
         (ι : (x : A) → B ∣ x ∣)
         (p : (x : ∥ A ∥) → hprop (B x)) where
  merely-ind : (x : ∥ A ∥) → B x
  merely-ind ∣ x ∣ = ι x

postulate merely-ind-C : ∀ {u v w} {X : Type u} (A : X → Type v) (B : (x : X) → ∥ A x ∥ → Type w)
                           (ι : (x : X) → (a : A x) → B x ∣ a ∣) (p : (x : X) → (a : ∥ A x ∥) → hprop (B x a)) →
                           (f : (x : X) → ∥ A x ∥) → C A → C B → C² ι → C² p → C f → C (λ x → merely-ind (B x) (ι x) (p x) (f x))

data ∥_∥₀ {u} (A : Type u) : Type u where
  ∣_∣₀ : A → ∥ A ∥₀

module _ {u} (A : Type u) {a b : ∥ A ∥₀} (p q : Path ∥ A ∥₀ a b) where
  set-trunc-hset : I → Path ∥ A ∥₀ a b
  set-trunc-hset i₀ = p
  set-trunc-hset i₁ = q

  postulate set-trunc-hset-C : C set-trunc-hset

module _ {u v} {A : Type u}
         (B : ∥ A ∥₀ → Type v)
         (ι : (x : A) → B ∣ x ∣₀)
         (p : (x : ∥ A ∥₀) → hset (B x)) where
  set-trunc-ind : (x : ∥ A ∥₀) → B x
  set-trunc-ind ∣ x ∣₀ = ι x

postulate set-trunc-ind-C : ∀ {u v w} {X : Type u} (A : X → Type v) (B : (x : X) → ∥ A x ∥₀ → Type w)
                              (ι : (x : X) → (a : A x) → B x ∣ a ∣₀) (p : (x : X) → (a : ∥ A x ∥₀) → hset (B x a)) →
                              (f : (x : X) → ∥ A x ∥₀) → C A → C B → C² ι → C² p → C f → C (λ x → set-trunc-ind (B x) (ι x) (p x) (f x))
