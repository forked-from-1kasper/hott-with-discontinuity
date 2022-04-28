{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic
open import Basic

open Σ

data S¹ : Set where
  base : S¹

postulate
  loop   : C I (λ _ → S¹)
  loop-0 : ap loop 0 ↦ base
  loop-1 : ap loop 1 ↦ base

  {-# REWRITE loop-0 loop-1 #-}
