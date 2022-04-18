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

data _∧_ {u v} (A : Prop u) (B : Prop v) : Prop (u ⊔ v) where
  ∧-intro : A → B → A ∧ B

_⟷_ : ∀ {u v} → Prop u → Prop v → Prop (u ⊔ v)
A ⟷ B = (A → B) ∧ (B → A)

∧-left : ∀ {u v} {A : Prop u} {B : Prop v} → A ∧ B → A
∧-left (∧-intro a b) = a

∧-right : ∀ {u v} {A : Prop u} {B : Prop v} → A ∧ B → B
∧-right (∧-intro a b) = b

data I : Set where
  i₀ : I
  i₁ : I

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

data Σ {u v} (A : Type u) (B : A → Type v) : Type (u ⊔ v) where
  _,_ : (a : A) → B a → Σ A B

pr₁ : ∀ {u v} {A : Type u} {B : A → Type v} → Σ A B → A
pr₁ (a , b) = a

pr₂ : ∀ {u v} {A : Type u} {B : A → Type v} (w : Σ A B) → B (pr₁ w)
pr₂ (a , b) = b

postulate Σ-η : ∀ {u v} (A : Type u) (B : A → Type v) (w : Σ A B) → (pr₁ w , pr₂ w) ↦ w
{-# REWRITE Σ-η #-}

Σ-ind : ∀ {u v w} {A : Type u} {B : A → Type v} (C : Σ A B → Type w) →
          ((a : A) (b : B a) → C (a , b)) → (w : Σ A B) → C w
Σ-ind C d (a , b) = d a b

_×_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A × B = Σ A (λ _ → B)

instance
  I-number : number I
  I-number =
    record { constraint = λ { zero → 𝟏; (succ zero) → 𝟏; _ → 𝟎 };
             from-nat   = λ { zero → i₀; (succ zero) → i₁ } }

  ℕ-number : number ℕ
  ℕ-number = record { constraint = λ _ → 𝟏; from-nat = λ n → n }

neg : I → I
neg i₀ = i₁
neg i₁ = i₀

□ : ℕ → Set
□ zero     = I
□ (succ n) = □ n × I

postulate continuous : ∀ {u v} {A : Type u} {B : A → Type v} → ((x : A) → B x) → Prop

postulate
  continuous-const : ∀ {u v} (A : Type u) (B : Type v) (a : A) → continuous (const A B a)
  continuous-neg   : continuous neg

  continuous-def   : ∀ {u v} (A : Type u) (B : A → Type v) (f : (x : A) → B x) →
    continuous f ⟷ ((n : ℕ) → (g : □ n → A) → continuous g → continuous (com f g))

postulate
  pr₁-continuous : ∀ {u v} {A : Type u} (B : A → Type v) → continuous (pr₁ {B = B})
  pr₂-continuous : ∀ {u v} {A : Type u} (B : A → Type v) → continuous (pr₂ {B = B})

postulate
  coe            : ∀ {u} (A : I → Type u) → continuous A → (i : I) → A 0 → A i
  coe-continuous : ∀ {u} (A : I → Type u) (μ : continuous A) (i : I) → continuous (coe A μ i)
  coe-const      : ∀ {u} (A : Type u) (i : I) → coe (λ _ → A) (continuous-const _ _ A) i ↦ idfun A
  coe-idfun      : ∀ {u} (A : I → Type u) (μ : continuous A) → coe A μ 0 ↦ idfun (A 0)
{-# REWRITE coe-const coe-idfun #-}

continuous-idfun : ∀ {u} (A : Type u) → continuous (idfun A)
continuous-idfun A = ∧-right (continuous-def A (λ _ → A) (idfun A)) (λ (n : ℕ) (g : □ n → A) (μ : continuous g) → μ)

continuous-com   : ∀ {u v w} {A : Type u} {B : Type v} {C : B → Type w} →
                     (f : (b : B) → C b) → (g : A → B) →
                     continuous f → continuous g → continuous (com f g)
continuous-com {A = A} {B = B} {C = C} f g μ η = ∧-right (continuous-def A (C ∘ g) (com f g))
  (λ (n : ℕ) (h : □ n → A) (σ : continuous h) →
    ∧-left (continuous-def B C f) μ n (g ∘ h)
      (∧-left (continuous-def A (λ _ → B) g) η n h σ))

continuous-∘ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} {f : B → C} {g : A → B} →
  continuous f → continuous g → continuous (f ∘ g)
continuous-∘ {A = A} {B = B} {C = C} {f = f} {g = g} μ η =
  continuous-com {B = B} {C = λ _ → C} f g μ η

data PathP {u} (A : I → Type u) (μ : continuous A) : A 0 → A 1 → Type u where
  weg : (f : (i : I) → A i) → continuous f → PathP A μ (f 0) (f 1)

module Application {u} {A : I → Type u} {μ : continuous A} {a : A 0} {b : A 1} where
  at : PathP A μ a b → (i : I) → A i
  at (weg φ _) i = φ i

  at-continuous : (p : PathP A μ a b) → continuous (at p)
  at-continuous (weg _ μ) = μ

  postulate at-0 : (p : PathP A μ a b) → (at p 0) ↦ a
  postulate at-1 : (p : PathP A μ a b) → (at p 1) ↦ b
  {-# REWRITE at-0 at-1 #-}

open Application

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A = PathP (λ _ → A) (continuous-const _ _ A)

idp : ∀ {u} {A : Type u} (a : A) → Path A a a
idp {A = A} a = weg (λ _ → a) (continuous-const A I a)

_⁻¹ : ∀ {u} {A : I → Type u} {μ : continuous A} {a : A 0} {b : A 1} →
        PathP A μ a b → PathP (A ∘ neg) (continuous-∘ μ continuous-neg) b a
_⁻¹ {A = A} (weg φ μ) = weg (com {A = I} {B = I} {C = A} φ neg)
                            (continuous-com φ neg μ continuous-neg)

transport : ∀ {u} {A B : Type u} → Path (Type u) A B → A → B
transport (weg φ μ) = coe φ μ 1

transport-continuous : ∀ {u} {A B : Type u} (p : Path (Type u) A B) → continuous (transport p)
transport-continuous (weg φ μ) = coe-continuous φ μ 1

seg : Path I 0 1
seg = weg (idfun I) (continuous-idfun I)

I-rec : ∀ {u} {A : Type u} (a b : A) → Path A a b → I → A
I-rec a b p = at p

I-rec-continuous : ∀ {u} {A : Type u} {a b : A} (p : Path A a b) → continuous (I-rec a b p)
I-rec-continuous p = at-continuous p

ap : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → continuous f →
     {a b : A} → Path A a b → Path B (f a) (f b)
ap f μ (weg φ η) = weg (f ∘ φ) (continuous-∘ μ η)

_~_ : ∀ {u v} {A : Type u} {B : A → Type v} (f g : (x : A) → B x) → Type (u ⊔ v)
_~_ {A = A} {B = B} f g = (x : A) → Path (B x) (f x) (g x)

hprop : ∀ {u} (A : Type u) → Type u
hprop A = (a b : A) → Path A a b

hset : ∀ {u} (A : Type u) → Type u
hset A = (a b : A) → hprop (Path A a b)

data Id {u} (A : Type u) : A → A → Type u where
  refl : (a : A) → Id A a a

Id⇒Path : ∀ {u} {A : Type u} {a b : A} → Id A a b → Path A a b
Id⇒Path (refl a) = idp a

data S¹ : Set where
  base : S¹

loop : I → S¹
loop i₀ = base
loop i₁ = base

postulate loop-continuous : continuous loop

loop-S¹ : Path S¹ base base
loop-S¹ = weg loop loop-continuous

module Circle {u} (C : S¹ → Type u) (μ : continuous C) (c : C base)
              (p : PathP (C ∘ loop) (continuous-∘ μ loop-continuous) c c) where

  S¹-ind : (x : S¹) → C x
  S¹-ind base = c

  postulate S¹-β : (i : I) → S¹-ind (loop i) ↦ at p i
  {-# REWRITE S¹-β #-}

  postulate S¹-ind-continuous : continuous S¹-ind

open Circle

S¹-rec : ∀ {u} (C : Type u) (c : C) → Path C c c → S¹ → C
S¹-rec C c p = S¹-ind (λ _ → C) (continuous-const _ _ C) c p

S¹-rec-continuous : ∀ {u} (C : Type u) (c : C) (p : Path C c c) → continuous (S¹-rec C c p)
S¹-rec-continuous C c p = S¹-ind-continuous (λ _ → C) (continuous-const _ _ C) c p
