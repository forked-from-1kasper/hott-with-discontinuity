{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic
open import Basic

open Σ

data S¹ : Set where
  base : S¹

loop : I → S¹
loop i₀ = base
loop i₁ = base

postulate loop-C : C loop

loop-S¹ : Path S¹ base base
loop-S¹ = weg loop loop-C

module _ {u} (B : S¹ → Type u) (μ : C B) (b : B base)
         (p : PathP (B ∘ loop) (C-∘ μ loop-C) b b) where

  S¹-ind : (x : S¹) → B x
  S¹-ind base = b

  postulate S¹-β : (i : I) → S¹-ind (loop i) ↦ (∂ p) i
  {-# REWRITE S¹-β #-}

postulate S¹-ind-C : ∀ {u v} {X : Type u} (B : X → S¹ → Type v) (μ : (x : X) → C (B x)) (b : (x : X) → B x base)
                       (p : (x : X) → PathP (B x ∘ loop) (C-∘ (μ x) loop-C) (b x) (b x)) (f : X → S¹) →
                       C B → C b → C p → C f → C (λ x → S¹-ind (B x) (μ x) (b x) (p x) (f x))

S¹-rec : ∀ {u} (B : Type u) (b : B) → Path B b b → S¹ → B
S¹-rec B b p = S¹-ind (λ _ → B) (C-const _ _ B) b p

S¹-rec-C : ∀ {u v} {X : Type u} (B : X → Type v) (b : (x : X) → B x)
             (p : (x : X) → Path (B x) (b x) (b x)) (f : X → S¹) →
             C B → C b → C p → C f → C (λ x → S¹-rec (B x) (b x) (p x) (f x))
S¹-rec-C B b p f α β γ δ =
  S¹-ind-C (λ x _ → B x) (λ x → C-const _ _ (B x)) b p f
    (C-∘ (C-const′ _ S¹) α) β γ δ
