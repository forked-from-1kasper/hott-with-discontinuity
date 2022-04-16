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

com : ∀ {u v w} {A : Type u} {B : A → Type v} {C : {x : A} → B x → Type w} →
        ((a : A) → (b : B a) → C b) → (g : (a : A) → B a) → ((a : A) → C (g a))
com f g x = f x (g x)

postulate continuous : ∀ {u v} {A : Type u} {B : A → Type v} → ((x : A) → B x) → Prop

postulate
  continuous-idfun : ∀ {u} (A : Type u) → continuous (idfun A)
  continuous-const : ∀ {u v} (A : Type u) (B : Type v) (a : A) → continuous (const A B a)
  continuous-com   : ∀ {u v w} {A : Type u} {B : A → Type v} {C : {x : A} → B x → Type w} →
                       (f : (a : A) → (b : B a) → C b) → (g : (a : A) → B a) →
                       ((a : A) → continuous (f a)) → continuous g → continuous (com f g)

data I : Set where
  i₀ : I
  i₁ : I

neg : I → I
neg i₀ = i₁
neg i₁ = i₀

postulate continuous-neg : continuous neg

continuous-∘ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} {f : B → C} {g : A → B} →
                 continuous f → continuous g → continuous (f ∘ g)
continuous-∘ {A = A} {B = B} {C = C} {f = f} {g = g} μ η = continuous-com {B = λ _ → B} {C = λ _ → C} (λ _ → f) g (λ _ → μ) η

data PathP {u} (A : I → Type u) (μ : continuous A) : A i₀ → A i₁ → Type u where
  weg : (f : (i : I) → A i) → continuous f → PathP A μ (f i₀) (f i₁)

idp : ∀ {u} {A : Type u} (a : A) → PathP (λ _ → A) (continuous-const _ _ A) a a
idp {A = A} a = weg (λ _ → a) (continuous-const A I a)

_⁻¹ : ∀ {u} {A : I → Type u} {μ : continuous A} {a : A i₀} {b : A i₁} →
        PathP A μ a b → PathP (A ∘ neg) (continuous-∘ μ continuous-neg) b a
_⁻¹ {A = A} (weg φ μ) = weg (com {A = I} {B = λ _ → I} {C = A} (λ _ → φ) neg)
                            (continuous-com (λ _ → φ) neg (λ _ → μ) continuous-neg)

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A = PathP (λ _ → A) (continuous-const _ _ A)

seg : Path I i₀ i₁
seg = weg (idfun I) (continuous-idfun I)

data Id {u} (A : Type u) : A → A → Type u where
  refl : (a : A) → Id A a a

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
{-# BUILTIN NATURAL Nat #-}
