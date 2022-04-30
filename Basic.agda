{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic

open Σ

postulate
  C  : ∀ {u v} (A : Type u) → (A → Type v) → Type (u ⊔ v)
  id : ∀ {u} (A : Type u) → C A (λ _ → A)

-- do not confuse with continuosly differentiable functions
C¹ = C

C² : ∀ {u v} (A : Type u) → (A → A → Type v) → Type (u ⊔ v)
C² A B = C A (λ a → C A (B a))

C³ : ∀ {u v} (A : Type u) → (A → A → A → Type v) → Type (u ⊔ v)
C³ A B = C A (λ a → C A (λ b → C A (B a b)))

postulate
  ap    : ∀ {u v} {A : Type u} {B : A → Type v} → C A B → Π A B
  id-ap : ∀ {u} (A : Type u) → ap (id A) ↦ idfun A
  {-# REWRITE id-ap #-}

postulate
  P : ∀ {u} → C (Type u) (λ A → C A (λ _ → C A (λ _ → Type u)))

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A a b = ap (ap (ap P A) a) b

postulate
  con : ∀ {u} (A : Type u) → C¹ A (λ a → Path A a a)
  rev : ∀ {u} {A : Type u} → C² A (λ a b → C (Path A a b) (λ _ → Path A b a))
  com : ∀ {u} {A : Type u} → C³ A (λ a b c → C (Path A a b) (λ _ → C (Path A b c) (λ _ → Path A a c)))
  coe : ∀ {u v} {A : Type u} {B : A → Type v} {a b : A} → Path A a b → C (B a) (λ _ → B b)

idp : ∀ {u} {A : Type u} (a : A) → Path A a a
idp {A = A} = ap (con A)

_⁻¹ : ∀ {u} {A : Type u} {a b : A} → Path A a b → Path A b a
_⁻¹ {a = a} {b = b} = ap (ap (ap rev a) b)

_⬝_ : ∀ {u} {A : Type u} {a b c : A} → Path A a b → Path A b c → Path A a c
_⬝_ {a = a} {b = b} {c = c} p q = ap (ap (ap (ap (ap com a) b) c) p) q

postulate
  rev-con : ∀ {u} (A : Type u) → C A (λ a → Path (Path A a a) (idp a ⁻¹)      (idp a))
  com-con : ∀ {u} (A : Type u) → C A (λ a → Path (Path A a a) (idp a ⬝ idp a) (idp a))
  coe-idp : ∀ {u v} {A : Type u} (B : A → Type v) (a : A) → coe {B = B} (idp a) ↦ id (B a)
  {-# REWRITE coe-idp #-}

PathP : ∀ {u v} {A : Type u} {B : A → Type v} {a b : A} → Path A a b → B a → B b → Type v
PathP {B = B} {b = b} p x y = Path (B b) (ap (coe p) x) y

◻ : ∀ {u} (A : Type u) → ℕ → Type u
◻ A zero     = A
◻ A (succ n) = Σ² (◻ A n) (Path (◻ A n))

◻-idp : ∀ {u} {A : Type u} (n : ℕ) → ◻ A n → ◻ A (succ n)
◻-idp n σ = ((σ , σ) , idp σ)

◼ : ∀ {u v} {A : Type u} (B : A → Type v) → (n : ℕ) → ◻ A n → Type v
◼ B zero       = B
◼ B (succ n) σ = Σ (◼ B n (pr₁ (pr₁ σ)) × ◼ B n (pr₂ (pr₁ σ)))
                   (λ w → PathP {B = ◼ B n} (pr₂ σ) (pr₁ w) (pr₂ w))

◼-idp : ∀ {u v} {A : Type u} {B : A → Type v} (n : ℕ) → {σ : ◻ A n} → ◼ B n σ → ◼ B (succ n) (◻-idp n σ)
◼-idp n ε = ((ε , ε) , idp ε)

Map : ∀ {u v} (A : Type u) → (A → Type v) → Type (u ⊔ v)
Map A B = (n : ℕ) → Π (◻ A n) (◼ B n)

record functorial {u v} {A : Type u} {B : A → Type v} (g : Map A B) : Set (u ⊔ v) where
  field
    respects-left  : (n : ℕ) → (σ : ◻ A (succ n)) → Id (◼ B n (pr₁ (pr₁ σ))) (pr₁ (pr₁ (g (succ n) σ))) (g n (pr₁ (pr₁ σ)))
    respects-right : (n : ℕ) → (σ : ◻ A (succ n)) → Id (◼ B n (pr₂ (pr₁ σ))) (pr₂ (pr₁ (g (succ n) σ))) (g n (pr₂ (pr₁ σ)))
    respects-idp   : (n : ℕ) → (σ : ◻ A n) → Id (◼ B (succ n) (◻-idp n σ)) (g (succ n) (◻-idp n σ)) (◼-idp n (g n σ))
    -- reversals
    -- composition

module _ {u v} {A : Type u} {B : A → Type v} where
  postulate
    Cλ      : (g : Map A B) → functorial {B = B} g → C A B
    C-elim  : C A B → Map A B
    C-coh   : (g : C A B) → functorial (C-elim g)
    C-η     : (g : C A B) → Cλ (C-elim g) (C-coh g) ↦ g
    ap-elim : (g : C A B) → (x : A) → Id (B x) (ap g x) (C-elim g 0 x)
  {-# REWRITE C-η #-}
