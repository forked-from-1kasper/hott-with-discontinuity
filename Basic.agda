{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic

open Σ

postulate
  C  : ∀ {u v} (A : Type u) → (A → Type v) → Type (u ⊔ v)
  ap : ∀ {u v} {A : Type u} {B : A → Type v} → C A B → Π A B

data I : Set where
  i₀ : I
  i₁ : I

instance
  I-number : number I
  I-number =
    record { constraint = λ { zero → 𝟏; (succ zero) → 𝟏; _ → 𝟎 };
             from-nat   = λ { zero → i₀; (succ zero) → i₁ } }

neg : I → I
neg i₀ = i₁
neg i₁ = i₀

◻ : ℕ → Set
◻ zero            = 𝟏
◻ (succ zero)     = I
◻ (succ (succ n)) = ◻ n × I

Map : ∀ {u v} (A : Type u) → (A → Type v) → Type (u ⊔ v)
Map A B = (n : ℕ) → (f : C (◻ n) (λ _ → A)) → C (◻ n) (B ∘ ap f)

postulate
  C-λ       : ∀ {u v} {A : Type u} {B : A → Type v} → Map A B → C A B
  coe       : ∀ {u} (A : C I (λ _ → Type u)) → C (I × ap A 0) (ap A ∘ pr₁)

data PathP {u} (A : C I (λ _ → Type u)) : ap A 0 → ap A 1 → Type u where
  weg : (f : C I (ap A)) → PathP A (ap f 0) (ap f 1)
