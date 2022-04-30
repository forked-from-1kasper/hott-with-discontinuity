{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic

open Σ

postulate
  C     : ∀ {u v} (A : Type u) → (A → Type v) → Type (u ⊔ v)
  id    : ∀ {u} (A : Type u) → C A (λ _ → A)
  const : ∀ {u v} (A : Type u) (B : Type v) → C A (λ _ → C B (λ _ → A))

-- do not confuse with continuosly differentiable functions
C¹ = C

C² : ∀ {u v} (A : Type u) → (A → A → Type v) → Type (u ⊔ v)
C² A B = C A (λ a → C A (B a))

C³ : ∀ {u v} (A : Type u) → (A → A → A → Type v) → Type (u ⊔ v)
C³ A B = C A (λ a → C A (λ b → C A (B a b)))

postulate
  ap       : ∀ {u v} {A : Type u} {B : A → Type v} → C A B → Π A B
  id-ap    : ∀ {u} (A : Type u) → ap (id A) ↦ idfun A
  const-ap : ∀ {u v} (A : Type u) (B : Type v) (a : A) (b : B) → ap (ap (const A B) a) b ↦ a
  {-# REWRITE id-ap const-ap #-}

postulate
  P : ∀ {u} → C (Type u) (λ A → C A (λ _ → C A (λ _ → Type u)))

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A a b = ap (ap (ap P A) a) b

postulate
  con  : ∀ {u} (A : Type u) → C¹ A (λ a → Path A a a)
  hrev : ∀ {u} {A : Type u} → C² A (λ a b → C (Path A a b) (λ _ → Path A b a))
  hcom : ∀ {u} {A : Type u} → C³ A (λ a b c → C (Path A a b) (λ _ → C (Path A b c) (λ _ → Path A a c)))
  coe  : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) {a b : A} → Path A a b → C (ap B a) (λ _ → ap B b)

idp : ∀ {u} {A : Type u} (a : A) → Path A a a
idp {A = A} = ap (con A)

_⁻¹ : ∀ {u} {A : Type u} {a b : A} → Path A a b → Path A b a
_⁻¹ {a = a} {b = b} = ap (ap (ap hrev a) b)

infix 30 _⬝_

_⬝_ : ∀ {u} {A : Type u} {a b c : A} → Path A a b → Path A b c → Path A a c
_⬝_ {a = a} {b = b} {c = c} p q = ap (ap (ap (ap (ap hcom a) b) c) p) q

postulate
  rev-con : ∀ {u} (A : Type u) → C A (λ a → Path (Path A a a) (idp a ⁻¹)      (idp a))
  com-con : ∀ {u} (A : Type u) → C A (λ a → Path (Path A a a) (idp a ⬝ idp a) (idp a))

  coe-idp : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) (a : A) → coe B (idp a) ↦ id (ap B a)
  coe-con : ∀ {u v} (A : Type u) (B : Type v) (a b : A) (p : Path A a b) → coe {A = A} (ap (const _ _) B) p ↦ id B
  coe-com : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) {a b c : A} (p : Path A a b) (q : Path A b c)
              (x : ap B a) → ap (coe B q) (ap (coe B p) x) ↦ ap (coe B (p ⬝ q)) x
  {-# REWRITE coe-idp coe-con coe-com #-}

PathP : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) {a b : A} → Path A a b → ap B a → ap B b → Type v
PathP B {b = b} p x y = Path (ap B b) (ap (coe B p) x) y

postulate
  apd : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) {a b : A}
          (g : C A (ap B)) → (p : Path A a b) → PathP B p (ap g a) (ap g b)

cong : ∀ {u v} {A : Type u} {B : Type v} {a b : A} (g : C A (λ _ → B)) →
         Path A a b → Path B (ap g a) (ap g b)
cong {A = A} {B = B} g p = apd {A = A} (ap (const _ _) B) g p

com : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) {a b c : A} (p : Path A a b) (q : Path A b c)
        {x : ap B a} {y : ap B b} {z : ap B c} → PathP B p x y → PathP B q y z → PathP B (p ⬝ q) x z
com B p q α β = cong (coe B q) α ⬝ β

◻ : ∀ {u} (A : Type u) → ℕ → Type u
◻ A zero     = A
◻ A (succ n) = Σ² (◻ A n) (Path (◻ A n))

◻-idp : ∀ {u} {A : Type u} (n : ℕ) → ◻ A n → ◻ A (succ n)
◻-idp n σ = ((σ , σ) , idp σ)

module _ {u v} {A : Type u} (B : C A (λ _ → Type v)) where
  postulate
    ◼      : (n : ℕ) → C (◻ A n) (λ _ → Type v)
    ◼-zero : ◼ zero ↦ B

  {-# REWRITE ◼-zero #-}

postulate
  ◼-succ : (n : ℕ) → {u v : Level} → {A : Type u} → (B : C A (λ _ → Type v)) →
           (σ : ◻ A (succ n)) → ap (◼ B (succ n)) σ ↦
           Σ (ap (◼ B n) (pr₁ (pr₁ σ)) × ap (◼ B n) (pr₂ (pr₁ σ)))
             (λ w → PathP (◼ B n) (pr₂ σ) (pr₁ w) (pr₂ w))

-- can anyone explain to me why do I need these things
-- to get ◼-succ works properly at 0/1/2?
◼-1 = ◼-succ 0
◼-2 = ◼-succ 1
◼-3 = ◼-succ 2

{-# REWRITE ◼-succ ◼-1 ◼-2 ◼-3 #-}

◼-idp : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) (n : ℕ) →
          {σ : ◻ A n} → ap (◼ B n) σ → ap (◼ B (succ n)) (◻-idp n σ)
◼-idp B n ε = ((ε , ε) , idp ε)

Map : ∀ {u v} (A : Type u) → (C A (λ _ → Type v)) → Type (u ⊔ v)
Map A B = (n : ℕ) → Π (◻ A n) (ap (◼ B n))

record functorial {u v} {A : Type u} {B : C A (λ _ → Type v)} (g : Map A B) : Set (u ⊔ v) where
  field
    respects-left  : (n : ℕ) → (σ : ◻ A (succ n)) → Id (ap (◼ B n) (pr₁ (pr₁ σ))) (pr₁ (pr₁ (g (succ n) σ))) (g n (pr₁ (pr₁ σ)))
    respects-right : (n : ℕ) → (σ : ◻ A (succ n)) → Id (ap (◼ B n) (pr₂ (pr₁ σ))) (pr₂ (pr₁ (g (succ n) σ))) (g n (pr₂ (pr₁ σ)))
    respects-idp   : (n : ℕ) → (σ : ◻ A n) → Id (ap (◼ B (succ n)) (◻-idp n σ)) (g (succ n) (◻-idp n σ)) (◼-idp B n (g n σ))
    -- reversals
    -- compositions

module _ {u v} {A : Type u} {B : C A (λ _ → Type v)} where
  postulate
    Cλ      : (g : Map A B) → functorial {B = B} g → C A (ap B)
    C-elim  : C A (ap B) → Map A B
    C-coh   : (g : C A (ap B)) → functorial (C-elim g)

    C-β     : (g : Map A B) → (ρ : functorial {B = B} g) → C-elim (Cλ g ρ) ↦ g
    C-η     : (g : C A (ap B)) → Cλ (C-elim g) (C-coh g) ↦ g

    C-left  : (g : C A (ap B)) → (n : ℕ) → (σ : ◻ A (succ n)) → pr₁ (pr₁ (C-elim g (succ n) σ)) ↦ C-elim g n (pr₁ (pr₁ σ))
    C-right : (g : C A (ap B)) → (n : ℕ) → (σ : ◻ A (succ n)) → pr₂ (pr₁ (C-elim g (succ n) σ)) ↦ C-elim g n (pr₂ (pr₁ σ))
    ap-def  : (g : C A (ap B)) → (x : A) → ap g x ↦ C-elim g 0 x
  {-# REWRITE C-β C-η C-left C-right ap-def #-}

  postulate
    apd-def : (g : C A (ap B)) (a b : A) (p : Path A a b) → apd B g p ↦ pr₂ (C-elim g 1 ((a , b) , p))
  {-# REWRITE apd-def #-}
