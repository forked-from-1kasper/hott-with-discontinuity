{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic

open Σ

postulate
  C    : ∀ {u v} (A : Type u) → (A → Type v) → Type (u ⊔ v)
  ap   : ∀ {u v} {A : Type u} {B : A → Type v} → C A B → Π A B

  Path : ∀ {u} (A : Type u) → A → A → Type u
  idp  : ∀ {u} {A : Type u} (a : A) → Path A a a
  _⁻¹  : ∀ {u} {A : Type u} {a b : A} → Path A a b → Path A b a
  _⬝_  : ∀ {u} {A : Type u} {a b c : A} → Path A a b → Path A b c → Path A a c

  coe  : ∀ {u v} {A : Type u} {B : A → Type v} {a b : A} → Path A a b → C (B a) (λ _ → B b)

PathP : ∀ {u v} {A : Type u} {B : A → Type v} {a b : A} → Path A a b → B a → B b → Type v
PathP {B = B} {b = b} p x y = Path (B b) (ap (coe p) x) y

◻ : ∀ {u} (A : Type u) → ℕ → Type u
◻ A zero     = A
◻ A (succ n) = Σ² (◻ A n) (Path (◻ A n))

◼ : ∀ {u v} {A : Type u} (B : A → Type v) → (n : ℕ) → ◻ A n → Type v
◼ B zero       = B
◼ B (succ n) σ = Σ (◼ B n (pr₁ (pr₁ σ)) × ◼ B n (pr₂ (pr₁ σ)))
                   (λ w → PathP {B = ◼ B n} (pr₂ σ) (pr₁ w) (pr₂ w))

Map : ∀ {u v} (A : Type u) → (A → Type v) → Type (u ⊔ v)
Map A B = (n : ℕ) → Π (◻ A n) (◼ B n)

--record functorial {u v} {A : Type u} {B : A → Type v} (g : Map A B) : Set (u ⊔ v) where
--  field
--    tt : 𝟏

--postulate
--  C-λ       : ∀ {u v} {A : Type u} {B : A → Type v} → (g : Map A B) → functorial {B = B} g → C A B
