{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic

open Σ

postulate
  -- type of continuous functions
  -- they carry additional structure
  -- which determines their action on the paths
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
  -- type of paths itself defines continuous function in path space
  P : ∀ {u} → C (Type u) (λ A → C A (λ _ → C A (λ _ → Type u)))

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A a b = ap (ap (ap P A) a) b

postulate
  hcon : ∀ {u} (A : Type u) → C¹ A (λ a → Path A a a) -- constant path
  hrev : ∀ {u} {A : Type u} → C² A (λ a b → C (Path A a b) (λ _ → Path A b a)) -- path reversal
  hcom : ∀ {u} {A : Type u} → C³ A (λ a b c → C (Path A a b) (λ _ → C (Path A b c) (λ _ → Path A a c))) -- path composition
  coe  : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) {a b : A} → Path A a b → C (ap B a) (λ _ → ap B b)

idp : ∀ {u} {A : Type u} (a : A) → Path A a a
idp {A = A} = ap (hcon A)

_⁻¹ : ∀ {u} {A : Type u} {a b : A} → Path A a b → Path A b a
_⁻¹ {a = a} {b = b} = ap (ap (ap hrev a) b)

infix 30 _⬝_

_⬝_ : ∀ {u} {A : Type u} {a b c : A} → Path A a b → Path A b c → Path A a c
_⬝_ {a = a} {b = b} {c = c} p q = ap (ap (ap (ap (ap hcom a) b) c) p) q

postulate
  -- classically reversal of constant path (as composition of these) is equal to constant path
  -- not only up to homotopy, but pointwise; so we expect the same thing here,
  -- but not for “p ⬝ idp b” or “idp a ⬝ p” or “p ⬝ (q ⬝ r)” and “(p ⬝ q) ⬝ r”
  rev-con : ∀ {u} (A : Type u) (a : A) → ap (ap (ap hrev a) a) (idp a) ↦ idp a
  com-con : ∀ {u} (A : Type u) (a : A) → ap (ap (ap (ap (ap hcom a) a) a) (idp a)) (idp a) ↦ idp a

  coe-idp : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) (a : A) → coe B (idp a) ↦ id (ap B a)
  coe-con : ∀ {u v} (A : Type u) (B : Type v) (a b : A) (p : Path A a b) → coe {A = A} (ap (const _ _) B) p ↦ id B
  coe-com : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) {a b c : A} (p : Path A a b) (q : Path A b c)
              (x : ap B a) → ap (coe B q) (ap (coe B p) x) ↦ ap (coe B (p ⬝ q)) x
  {-# REWRITE rev-con com-con coe-idp coe-con coe-com #-}

PathP : ∀ {u v} {A : Type u} (B : C A (λ _ → Type v)) {a b : A} →
          Path A a b → ap B a → ap B b → Type v
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

-- type of hypercubes in A
◻ : ∀ {u} (A : Type u) → ℕ → Type u
◻ A zero     = A
◻ A (succ n) = Σ² (◻ A n) (Path (◻ A n))

◻-idp : ∀ {u} {A : Type u} (n : ℕ) → ◻ A n → ◻ A (succ n)
◻-idp n σ = ((σ , σ) , idp σ)

module _ {u v} {A : Type u} (B : C A (λ _ → Type v)) where
  postulate
    -- type of dependent hypercubes in B over A
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

infix 10 _~_

_~_ : ∀ {u v} {A : Type u} {B : A → Type v} (f g : (x : A) → B x) → Type (u ⊔ v)
_~_ {A = A} {B = B} f g = C A (λ x → Path (B x) (f x) (g x))

linv : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
linv {A = A} {B = B} f = Σ (B → A) (λ g → g ∘ f ~ idfun A)

rinv : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
rinv {A = A} {B = B} f = Σ (B → A) (λ g → f ∘ g ~ idfun B)

qinv : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
qinv {A = A} {B = B} f = Σ (B → A) (λ g → g ∘ f ~ idfun A × f ∘ g ~ idfun B)

biinv : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
biinv f = linv f × rinv f

_≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ (A → B) biinv

hprop : ∀ {u} (A : Type u) → Type u
hprop A = C (A × A) (λ w → Path A (pr₁ w) (pr₂ w))

prop : ∀ {u} (A : Type u) → Type u
prop A = C (A × A) (λ w → Id A (pr₁ w) (pr₂ w))

truncated : ∀ {u} (A : Type u) → ℕ → Type u
truncated A n = hprop (◻ A n)

strict-truncated : ∀ {u} (A : Type u) → ℕ → Type u
strict-truncated A n = prop (◻ A n)

hset : ∀ {u} (A : Type u) → Type u
hset A = truncated A 1

set : ∀ {u} (A : Type u) → Type u
set A = strict-truncated A 1

hgroupoid : ∀ {u} (A : Type u) → Type u
hgroupoid A = truncated A 2

Id→Path : ∀ {u} {A : Type u} {a b : A} → Id A a b → Path A a b
Id→Path {A = A} {a = a} {b = b} = idJ (λ a b _ → Path A a b) idp a b

infix 10 _≡_

_≡_ : ∀ {u v} {A : Type u} {B : A → Type v} (f g : (x : A) → B x) → Type (u ⊔ v)
_≡_ {A = A} {B = B} f g = (x : A) → Id (B x) (f x) (g x)

bijective : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
bijective {A = A} {B = B} f = Σ (B → A) (λ g → g ∘ f ≡ idfun A × f ∘ g ≡ idfun B)

_≅_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≅ B = Σ (A → B) bijective
