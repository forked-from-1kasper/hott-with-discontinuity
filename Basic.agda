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

postulate continuous : ∀ {u v} {A : Type u} {B : A → Type v} → ((x : A) → B x) → Prop

postulate
  continuous-idfun : ∀ {u} (A : Type u) → continuous (idfun A)
  continuous-const : ∀ {u v} (A : Type u) (B : Type v) (a : A) → continuous (const A B a)
  continuous-com   : ∀ {u v w} {A : Type u} {B : Type v} {C : B → Type w} →
                       (f : (b : B) → C b) → (g : A → B) →
                       continuous f → continuous g → continuous (com f g)

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

data Nat : Set where
  zero : Nat
  succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

record number {u} (A : Type u) : Type (lsuc u) where
  field
    constraint : Nat → Type u
    from-nat : (n : Nat) {{_ : constraint n}} → A

open number {{...}} public using (from-nat)

{-# BUILTIN FROMNAT from-nat #-}

instance
  I-nat : number I
  I-nat = record { constraint = λ { zero → 𝟏; (succ zero) → 𝟏; _ → 𝟎 };
                   from-nat   = λ { zero → i₀; (succ zero) → i₁ } }

neg : I → I
neg i₀ = i₁
neg i₁ = i₀

postulate continuous-neg : continuous neg

postulate
  coe            : ∀ {u} (A : I → Type u) → continuous A → (i : I) → A 0 → A i
  coe-continuous : ∀ {u} (A : I → Type u) (μ : continuous A) (i : I) → continuous (coe A μ i)
  coe-const      : ∀ {u} (A : Type u) (i : I) → coe (λ _ → A) (continuous-const _ _ A) i ↦ idfun A
  coe-idfun      : ∀ {u} (A : I → Type u) (μ : continuous A) → coe A μ 0 ↦ idfun (A 0)
{-# REWRITE coe-const coe-idfun #-}

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

data Id {u} (A : Type u) : A → A → Type u where
  refl : (a : A) → Id A a a

data Σ {u v} (A : Type u) (B : A → Type v) : Type (u ⊔ v) where
  _,_ : (a : A) → B a → Σ A B

pr₁ : ∀ {u v} {A : Type u} {B : A → Type v} → Σ A B → A
pr₁ (a , b) = a

pr₂ : ∀ {u v} {A : Type u} {B : A → Type v} (w : Σ A B) → B (pr₁ w)
pr₂ (a , b) = b

_×_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A × B = Σ A (λ _ → B)

postulate Σ-η : ∀ {u v} (A : Type u) (B : A → Type v) (w : Σ A B) → (pr₁ w , pr₂ w) ↦ w
{-# REWRITE Σ-η #-}
