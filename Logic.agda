{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto

data ⊥ {u} : Prop u where

data ⊤ {u} : Prop u where
  truth : ⊤

¬ : ∀ {u} → Prop u → Prop (lsuc u)
¬ A = A → ⊥

data _∧_ {u v} (A : Prop u) (B : Prop v) : Prop (u ⊔ v) where
  ∧-intro : A → B → A ∧ B

_⟷_ : ∀ {u v} → Prop u → Prop v → Prop (u ⊔ v)
A ⟷ B = (A → B) ∧ (B → A)

∧-left : ∀ {u v} {A : Prop u} {B : Prop v} → A ∧ B → A
∧-left (∧-intro a b) = a

∧-right : ∀ {u v} {A : Prop u} {B : Prop v} → A ∧ B → B
∧-right (∧-intro a b) = b
