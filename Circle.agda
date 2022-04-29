{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic
open import Basic

open Σ

data S¹ : Set where
  base : S¹

postulate
  loop   : Path S¹ base base
