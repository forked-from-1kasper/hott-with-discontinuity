{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive

Type : (u : Level) → Set (lsuc u)
Type u = Set u

postulate _↦_ : ∀ {u} {A : Type u} → A → A → Type u
{-# BUILTIN REWRITE _↦_ #-}

idfun : ∀ {u} (A : Type u) → A → A
idfun A a = a

const : ∀ {u v} (A : Type u) (B : Type v) → A → B → A
const A B a b = a

_∘_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

com : ∀ {u v w} {A : Type u} {B : Type v} {C : B → Type w} →
        ((b : B) → C b) → (g : A → B) → ((a : A) → C (g a))
com f g x = f (g x)

data 𝟎 : Set where

data 𝟏 : Set where
  ★ : 𝟏

instance
  𝟏-instance : 𝟏
  𝟏-instance = ★

data 𝟐 : Set where
  0₂ : 𝟐
  1₂ : 𝟐

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

record number {u} (A : Type u) : Type (lsuc u) where
  field
    constraint : ℕ → Type u
    from-nat : (n : ℕ) {{_ : constraint n}} → A

open number {{...}} public using (from-nat)

{-# BUILTIN FROMNAT from-nat #-}

instance
  ℕ-number : number ℕ
  ℕ-number = record { constraint = λ _ → 𝟏; from-nat = λ n → n }

Π : ∀ {u v} (A : Type u) (B : A → Type v) → Type (u ⊔ v)
Π A B = (x : A) → B x

record Σ {u v} (A : Type u) (B : A → Type v) : Type (u ⊔ v) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁

open Σ

Σ-ind : ∀ {u v w} {A : Type u} {B : A → Type v} (C : Σ A B → Type w) →
          ((a : A) → (b : B a) → C (a , b)) → (w : Σ A B) → C w
Σ-ind C d (a , b) = d a b

infix 9 _×_

Σ² : ∀ {u v} (A : Type u) → (A → A → Type v) → Type (u ⊔ v)
Σ² A B = Σ A (λ x → Σ A (B x))

_×_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A × B = Σ A (λ _ → B)

curry : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} → (A × B → C) → (A → B → C)
curry f a b = f (a , b)

uncurry : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} → (A → B → C) → (A × B → C)
uncurry f w = f (pr₁ w) (pr₂ w)

data _+_ {u v} (A : Type u) (B : Type v) : Type (u ⊔ v) where
  inl : A → A + B
  inr : B → A + B

+-ind : ∀ {u v w} {A : Type u} {B : Type v} (C : A + B → Type w) →
          ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
+-ind C f g (inl a) = f a
+-ind C f g (inr b) = g b
