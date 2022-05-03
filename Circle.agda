{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Axioms
open import Proto
open import Logic

open Σ

data S¹ : Set where
  base : S¹

postulate
  loop : Path S¹ (η base) (η base)
