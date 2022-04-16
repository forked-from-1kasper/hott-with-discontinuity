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

com : ∀ {u v w} {A : Type u} {B : A → Type v} {C : Σ A B → Type w} →
        ((w : Σ A B) → C w) → (g : (a : A) → B a) → ((a : A) → C (a , g a))
com f g x = f (x , g x)

postulate continuous : ∀ {u v} {A : Type u} {B : A → Type v} → ((x : A) → B x) → Prop

postulate
  continuous-idfun : ∀ {u} (A : Type u) → continuous (idfun A)
  continuous-const : ∀ {u v} (A : Type u) (B : Type v) (a : A) → continuous (const A B a)
  continuous-com   : ∀ {u v w} {A : Type u} {B : A → Type v} {C : Σ A B → Type w} →
                       (f : (w : Σ A B) → C w) → (g : (a : A) → B a) →
                       continuous f → continuous g → continuous (com f g)

  -- ???
  continuous-pr₁   : ∀ {u v w} {A : Type u} {B : A → Type v} {C : Type w} {f : A → C} →
                       continuous f → continuous (f ∘ pr₁ {A = A} {B = B})
  continuous-pr₂   : ∀ {u v w} {A : Type u} {B : Type v} {C : B → Type w} {f : (b : B) → C b} →
                       continuous f → continuous (λ (w : A × B) → f (pr₂ w))

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
                   from-nat = λ { zero → i₀; (succ zero) → i₁ } }

neg : I → I
neg i₀ = i₁
neg i₁ = i₀

postulate continuous-neg : continuous neg

continuous-∘ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} {f : B → C} {g : A → B} →
  continuous f → continuous g → continuous (f ∘ g)
continuous-∘ {A = A} {B = B} {C = C} {f = f} {g = g} μ η =
  continuous-com {B = λ _ → B} {C = λ _ → C} (λ w → f (pr₂ w)) g
    (continuous-pr₂ μ) η

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

idp : ∀ {u} {A : Type u} (a : A) → PathP (λ _ → A) (continuous-const _ _ A) a a
idp {A = A} a = weg (λ _ → a) (continuous-const A I a)

_⁻¹ : ∀ {u} {A : I → Type u} {μ : continuous A} {a : A 0} {b : A 1} →
        PathP A μ a b → PathP (A ∘ neg) (continuous-∘ μ continuous-neg) b a
_⁻¹ {A = A} (weg φ μ) = weg (com {A = I} {B = λ _ → I} {C = A ∘ pr₂} (λ w → φ (pr₂ w)) neg)
                            (continuous-com (λ w → φ (pr₂ w)) neg (continuous-pr₂ μ) continuous-neg)

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A = PathP (λ _ → A) (continuous-const _ _ A)

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
