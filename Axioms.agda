{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic

open Σ

postulate
  ◇     : ∀ {u} → Type u → Type u
  η      : ∀ {u} {A : Type u} → A → ◇ A
  join   : ∀ {u} {A : Type u} → ◇ (◇ A) → ◇ A
  join-η : ∀ {u} (A : Type u) (x : ◇ A) → join (η x) ↦ x
  η-join : ∀ {u} (A : Type u) (x : ◇ (◇ A)) → η (join x) ↦ x
  {-# REWRITE join-η η-join #-}

-- type of continuous functions
-- they carry additional structure
-- which determines their action on the paths
C : ∀ {u v} (A : Type u) → (◇ A → Type v) → Type (u ⊔ v)
C A B = Π (◇ A) (◇ ∘ B)

id : ∀ {u} (A : Type u) → C A (λ _ → A)
id A a = a

-- do not confuse with continuosly differentiable functions
C¹ = C

C² : ∀ {u v} (A : Type u) → (◇ A → ◇ A → Type v) → Type (u ⊔ v)
C² A B = C A (λ a → C A (B a))

C³ : ∀ {u v} (A : Type u) → (◇ A → ◇ A → ◇ A → Type v) → Type (u ⊔ v)
C³ A B = C A (λ a → C A (λ b → C A (B a b)))

postulate
  -- type of paths itself defines continuous function in path space
  Path : ∀ {u} (A : Type u) → ◇ A → ◇ A → Type u
  idp  : ∀ {u} {A : Type u} → (a : ◇ A) → Path A a a -- constant path
  hrev : ∀ {u} {A : Type u} → {a b : ◇ A} → ◇ (Path A a b) → Path A b a -- path reversal
  hcom : ∀ {u} {A : Type u} → {a b c : ◇ A} → ◇ (Path A a b) → ◇ (Path A b c) → Path A a c -- path composition
  coe  : ∀ {u v} {A : Type u} (B : ◇ A → Type v) {a b : ◇ A} → ◇ (Path A a b) → ◇ (B a) → ◇ (B b)

_⁻¹ : ∀ {u} {A : Type u} {a b : ◇ A} → Path A a b → Path A b a
_⁻¹ = hrev ∘ η

infix 30 _⬝_

_⬝_ : ∀ {u} {A : Type u} {a b c : ◇ A} → Path A a b → Path A b c → Path A a c
p ⬝ q = hcom (η p) (η q)

postulate
  -- classically reversal of constant path (as composition of these) is equal to constant path
  -- not only up to homotopy, but pointwise; so we expect the same thing here,
  -- but not for “p ⬝ idp b” or “idp a ⬝ p” or “p ⬝ (q ⬝ r)” and “(p ⬝ q) ⬝ r”
  rev-idp : ∀ {u} (A : Type u) (a : ◇ A) → hrev (η (idp a)) ↦ idp a
  com-idp : ∀ {u} (A : Type u) (a : ◇ A) → hcom (η (idp a)) (η (idp a)) ↦ idp a

  coe-idp   : ∀ {u v} {A : Type u} (B : ◇ A → Type v) (a : ◇ A) → coe B (η (idp a)) ↦ idfun (◇ (B a))
  coe-const : ∀ {u v} (A : Type u) (B : Type v) (a b : ◇ A) (p : ◇ (Path A a b)) → coe {A = A} (λ _ → B) p ↦ idfun (◇ B)
  coe-com   : ∀ {u v} {A : Type u} (B : ◇ A → Type v) {a b c : ◇ A} (p : ◇ (Path A a b)) (q : ◇ (Path A b c))
                (x : ◇ (B a)) → coe B q (coe B p x) ↦ coe B (η (hcom p q)) x
  {-# REWRITE rev-idp com-idp coe-idp coe-const coe-com #-}


PathP : ∀ {u v} {A : Type u} (B : ◇ A → Type v) {a b : ◇ A} →
          ◇ (Path A a b) → ◇ (B a) → ◇ (B b) → Type v
PathP B {b = b} p x y = Path (B b) (coe B p x) y

postulate
  apd : ∀ {u v} {A : Type u} (B : ◇ A → Type v) {a b : ◇ A}
          (g : C A B) → (p : ◇ (Path A a b)) → PathP B p (g a) (g b)

cong : ∀ {u v} {A : Type u} {B : Type v} (g : C A (λ _ → B))
         {a b : ◇ A} → ◇ (Path A a b) → Path B (g a) (g b)
cong {A = A} {B = B} g p = apd {A = A} (λ _ → B) g p

com : ∀ {u v} {A : Type u} (B : ◇ A → Type v) {a b c : ◇ A} (p : ◇ (Path A a b)) (q : ◇ (Path A b c))
        {x : ◇ (B a)} {y : ◇ (B b)} {z : ◇ (B c)} → ◇ (PathP B p x y) → ◇ (PathP B q y z) → PathP B (η (hcom p q)) x z
com B p q α β = hcom (η (cong (coe B q) α)) β

module _ {u v} {A : Type u} {B : A → Type v} where
  postulate
    -- ???
    π₁   : ◇ (Σ A B) → A
    π₂   : (w : ◇ (Σ A B)) → B (π₁ w)
    π₁-β : (a : A) (b : B a) → π₁ (η (a , b)) ↦ a
    {-# REWRITE π₁-β #-}

    π₂-β : (a : A) (b : B a) → π₂ (η (a , b)) ↦ b
    {-# REWRITE π₂-β #-}

-- type of hypercubes in A
◻ : ∀ {u} (A : Type u) → ℕ → Type u
◻ A zero     = A
◻ A (succ n) = Σ² (◇ (◻ A n)) (λ a b → ◇ (Path (◻ A n) a b))

◻-idp : ∀ {u} {A : Type u} (n : ℕ) → ◇ (◻ A n) → ◻ A (succ n)
◻-idp n σ = ((σ , σ) , η (idp σ))

◼ : ∀ {u v} {A : Type u} (B : ◇ A → Type v) → (n : ℕ) → ◇ (◻ A n) → Type v
◼ B zero       = B
◼ B (succ n) σ = Σ (◇ (◼ B n (pr₁ (π₁ σ))) × ◇ (◼ B n (pr₂ (π₁ σ))))
                   (λ w → ◇ (PathP (◼ B n) (π₂ σ) (pr₁ w) (pr₂ w)))

Map : ∀ {u v} (A : Type u) → (◇ A → Type v) → Type (u ⊔ v)
Map A B = (n : ℕ) → Π (◇ (◻ A n)) (◼ B n)

◼-idp : ∀ {u v} {A : Type u} (B : ◇ A → Type v) (n : ℕ) →
          {σ : ◇ (◻ A n)} → ◼ B n σ → ◼ B (succ n) (η (◻-idp n σ))
◼-idp B n ε = ((η ε , η ε) , η (idp (η ε)))

module _ {u v} {A : Type u} {B : ◇ A → Type v} where
  postulate
    C-elim    : C A B → Map A B
    C-left    : (g : C A B) → (n : ℕ) → (σ : ◇ (◻ A (succ n))) → pr₁ (pr₁ (C-elim g (succ n) σ)) ↦ η (C-elim g n (pr₁ (π₁ σ)))
    C-right   : (g : C A B) → (n : ℕ) → (σ : ◇ (◻ A (succ n))) → pr₂ (pr₁ (C-elim g (succ n) σ)) ↦ η (C-elim g n (pr₂ (π₁ σ)))
    elim-zero : (g : C A B) → (x : ◇ A) → η (C-elim g 0 x) ↦ g x
  {-# REWRITE C-left C-right elim-zero #-}

  postulate
    apd-def : (g : C A B) (σ : ◇ (◻ A 1)) → pr₂ (C-elim g 1 σ) ↦ η (apd B g (π₂ σ))
  {-# REWRITE apd-def #-}

infix 10 _~_

_~_ : ∀ {u v} {A : Type u} {B : ◇ A → Type v} (f g : C A B) → Type (u ⊔ v)
_~_ {A = A} {B = B} f g = (x : ◇ A) → Path (B x) (f x) (g x)

linv : ∀ {u v} {A : Type u} {B : Type v} → (◇ A → ◇ B) → Type (u ⊔ v)
linv {A = A} {B = B} f = Σ (◇ B → ◇ A) (λ g → g ∘ f ~ idfun (◇ A))

rinv : ∀ {u v} {A : Type u} {B : Type v} → (◇ A → ◇ B) → Type (u ⊔ v)
rinv {A = A} {B = B} f = Σ (◇ B → ◇ A) (λ g → f ∘ g ~ idfun (◇ B))

qinv : ∀ {u v} {A : Type u} {B : Type v} → (◇ A → ◇ B) → Type (u ⊔ v)
qinv {A = A} {B = B} f = Σ (◇ B → ◇ A) (λ g → g ∘ f ~ idfun (◇ A) × f ∘ g ~ idfun (◇ B))

biinv : ∀ {u v} {A : Type u} {B : Type v} → (◇ A → ◇ B) → Type (u ⊔ v)
biinv f = linv f × rinv f

_≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ (◇ A → ◇ B) biinv

hprop : ∀ {u} (A : Type u) → Type u
hprop A = (a b : ◇ A) → Path A a b

postulate
  Id◇   : ∀ {u} (A : Type u) → ◇ A → ◇ A → Type u
  refl◇ : ∀ {u} {A : Type u} (a : ◇ A) → Id◇ A a a
  -- J?
  Id◇-β : ∀ {u} (A : Type u) (a b : A) → Id◇ A (η a) (η b) ↦ Id A a b
  {-# REWRITE Id◇-β #-}

prop : ∀ {u} (A : Type u) → Type u
prop A = (a b : ◇ A) → Id◇ A a b

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

Id→Path : ∀ {u} {A : Type u} {a b : A} → Id A a b → Path A (η a) (η b)
Id→Path {A = A} {a = a} {b = b} = idJ (λ a b _ → Path A (η a) (η b)) (λ x → idp (η x)) a b

infix 10 _≡_

_≡_ : ∀ {u v} {A : Type u} {B : A → Type v} (f g : (x : A) → B x) → Type (u ⊔ v)
_≡_ {A = A} {B = B} f g = (x : A) → Id (B x) (f x) (g x)

bijective : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → Type (u ⊔ v)
bijective {A = A} {B = B} f = Σ (B → A) (λ g → g ∘ f ≡ idfun A × f ∘ g ≡ idfun B)

_≅_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≅ B = Σ (A → B) bijective
