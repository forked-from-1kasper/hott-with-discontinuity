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

data ⊥ {u} : Prop u where

data ⊤ {u} : Prop u where
  truth : ⊤

¬ : ∀ {u} → Prop u → Prop (lsuc u)
¬ A = A → ⊥

data _∧_ {u v} (A : Prop u) (B : Prop v) : Prop (u ⊔ v) where
  ∧-intro : A → B → A ∧ B

_⟷_ : ∀ {u v} → Prop u → Prop v → Prop (u ⊔ v)
A ⟷ B = (A → B) ∧ (B → A)

∧-left : ∀ {u v} {A : Prop u} {B : Prop v} → A ∧ B → A
∧-left (∧-intro a b) = a

∧-right : ∀ {u v} {A : Prop u} {B : Prop v} → A ∧ B → B
∧-right (∧-intro a b) = b

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

instance
  ℕ-number : number ℕ
  ℕ-number = record { constraint = λ _ → 𝟏; from-nat = λ n → n }

Π : ∀ {u v} (A : Type u) (B : A → Type v) → Type (u ⊔ v)
Π A B = (x : A) → B x

record Σ {u v} (A : Type u) (B : A → Type v) : Type (u ⊔ v) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁

open Σ

_×_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A × B = Σ A (λ _ → B)

curry : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} → (A × B → C) → (A → B → C)
curry f a b = f (a , b)

uncurry : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} → (A → B → C) → (A × B → C)
uncurry f w = f (pr₁ w) (pr₂ w)

data _+_ {u v} (A : Type u) (B : Type v) : Type (u ⊔ v) where
  inl : A → A + B
  inr : B → A + B

+-ind : ∀ {u v w} {A : Type u} {B : Type v} (C : A + B → Type w) →
          ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
+-ind C f g (inl a) = f a
+-ind C f g (inr b) = g b

data I : Set where
  i₀ : I
  i₁ : I

instance
  I-number : number I
  I-number =
    record { constraint = λ { zero → 𝟏; (succ zero) → 𝟏; _ → 𝟎 };
             from-nat   = λ { zero → i₀; (succ zero) → i₁ } }

neg : I → I
neg i₀ = i₁
neg i₁ = i₀

□ : ℕ → Set
□ zero     = I
□ (succ n) = □ n × I

postulate continuous : ∀ {u v} {A : Type u} {B : A → Type v} → ((x : A) → B x) → Prop

record CΠ {u v} (A : Type u) (B : A → Type v) : Type (u ⊔ v) where
  constructor ⟨_,_⟩
  field
    inj  : Π A B
    pres : continuous inj

open CΠ

continuous² : ∀ {u v w} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type w} →
                ((a : A) → (b : B a) → C a b) → Prop u
continuous² {A = A} φ = continuous φ ∧ ((a : A) → continuous (φ a))

postulate
  continuous-neg   : continuous neg

  continuous-const  : ∀ {u v} (A : Type u) (B : Type v) (a : A) → continuous (const A B a)
  continuous-const′ : ∀ {u v} (A : Type u) (B : Type v) → continuous (const A B)
  continuous-def    : ∀ {u v} (A : Type u) (B : A → Type v) (f : (x : A) → B x) →
    continuous f ⟷ ((n : ℕ) → (g : □ n → A) → continuous g → continuous (com f g))

postulate
  coe            : ∀ {u} (A : I → Type u) → continuous A → (i : I) → A 0 → A i
  continuous-coe : ∀ {u v} {X : Type u} (A : X → I → Type v) (μ : (x : X) → continuous (A x)) (f : X → I) (g : (x : X) → A x 0) →
                     continuous A → continuous f → continuous g → continuous (λ x → coe (A x) (μ x) (f x) (g x))
  coe-const      : ∀ {u} (A : Type u) (i : I) → coe (λ _ → A) (continuous-const _ _ A) i ↦ idfun A
  coe-idfun      : ∀ {u} (A : I → Type u) (μ : continuous A) → coe A μ 0 ↦ idfun (A 0)
{-# REWRITE coe-const coe-idfun #-}

data PathP {u} (A : I → Type u) (μ : continuous A) : A 0 → A 1 → Type u where
  weg : (f : (i : I) → A i) → continuous f → PathP A μ (f 0) (f 1)

module _ {u} {A : I → Type u} {μ : continuous A} {a : A 0} {b : A 1} where
  ∂ : PathP A μ a b → (i : I) → A i
  ∂ (weg φ _) = φ

  ∂-continuous : (p : PathP A μ a b) → continuous (∂ p)
  ∂-continuous (weg _ μ) = μ

  postulate ∂-0 : (p : PathP A μ a b) → (∂ p) 0 ↦ a
  postulate ∂-1 : (p : PathP A μ a b) → (∂ p) 1 ↦ b
  {-# REWRITE ∂-0 ∂-1 #-}

postulate
  PathP-continuous : ∀ {u v} {X : Type u} (A : X → I → Type v) (μ : (x : X) → continuous (A x)) (a : (x : X) → A x 0) (b : (x : X) → A x 1) →
                       continuous A → continuous a → continuous b → continuous (λ (x : X) → PathP (A x) (μ x) (a x) (b x))
  continuous-weg   : ∀ {u v} {X : Type u} (A : X → I → Type v) (μ : (x : X) → continuous (A x)) (f : (x : X) → (i : I) → A x i)
                       (η : (x : X) → continuous (f x)) → continuous f → continuous (λ x → weg {A = A x} {μ = μ x} (f x) (η x))
  continuous-∂     : ∀ {u v} {X : Type u} (A : X → I → Type v) (μ : (x : X) → continuous (A x)) (a : (x : X) → A x 0) (b : (x : X) → A x 1)
                       (p : (x : X) → PathP (A x) (μ x) (a x) (b x)) (f : X → I) → continuous a → continuous b →
                       continuous p → continuous f → continuous (λ x → ∂ (p x) (f x))
  continuous-inj   : ∀ {u v} (A : Type u) (B : A → Type v) → continuous (inj {A = A} {B = B})
  continuous-⟨⟩    : ∀ {u v w} {X : Type u} (A : X → Type v) (B : (x : X) → A x → Type w)
                       (f : (x : X) → (a : A x) → B x a) (μ : (x : X) → continuous (f x)) →
                       continuous f → continuous (λ x → ⟨ f x , μ x ⟩)

postulate
  Π-continuous : ∀ {u v w} {X : Type u} (A : X → Type v) (B : (x : X) → A x → Type w) →
                   continuous A → continuous B → continuous (λ (x : X) → Π (A x) (B x))

postulate
  Σ-continuous    : ∀ {u v w} {X : Type u} (A : X → Type v) (B : (x : X) → A x → Type w) →
                      continuous A → continuous B → continuous (λ (x : X) → Σ (A x) (B x))
  continuous-pr₁  : ∀ {u v} {A : Type u} (B : A → Type v) → continuous (pr₁ {B = B})
  continuous-pr₂  : ∀ {u v} {A : Type u} (B : A → Type v) → continuous (pr₂ {B = B})
  continuous-Σ-mk : ∀ {u v w} (X : Type u) (A : X → Type v) (B : (x : X) → A x → Type w)
                      (f : (x : X) → A x) (g : (x : X) → B x (f x)) → continuous f → continuous g →
                      continuous {B = λ x → Σ (A x) (B x)} (λ x → (f x , g x))

postulate
  +-continuous     : ∀ {u v w} {X : Type u} (A : X → Type v) (B : X → Type w) →
                       continuous A → continuous B → continuous (λ x → A x + B x)
  continuous-inl   : ∀ {u v w} {X : Type u} (A : X → Type v) (B : X → Type w) → (f : (x : X) → A x) →
                       continuous f → continuous (λ x → inl {A = A x} {B = B x} (f x))
  continuous-inr   : ∀ {u v w} {X : Type u} (A : X → Type v) (B : X → Type w) → (g : (x : X) → B x) →
                       continuous g → continuous (λ x → inr {A = A x} {B = B x} (g x))
  continuous-+-ind : ∀ {u v w k} (X : Type u) {A : X → Type v} {B : X → Type w} (C : (x : X) → A x + B x → Type k) →
                       (f : (x : X) → (a : A x) → C x (inl a)) → (g : (x : X) → (b : B x) → C x (inr b)) →
                       (h : (x : X) → A x + B x) → continuous C → continuous² f → continuous² g → continuous h →
                       continuous (λ x → +-ind (C x) (f x) (g x) (h x))

continuous-idfun : ∀ {u} (A : Type u) → continuous (idfun A)
continuous-idfun A = ∧-right (continuous-def A (λ _ → A) (idfun A)) (λ (n : ℕ) (g : □ n → A) (μ : continuous g) → μ)

continuous-com : ∀ {u v w} {A : Type u} {B : Type v} {C : B → Type w} → (f : (b : B) → C b) → (g : A → B) →
                   continuous f → continuous g → continuous (com f g)
continuous-com {A = A} {B = B} {C = C} f g μ η = ∧-right (continuous-def A (C ∘ g) (com f g))
  (λ (n : ℕ) (h : □ n → A) (σ : continuous h) →
    ∧-left (continuous-def B C f) μ n (g ∘ h)
      (∧-left (continuous-def A (λ _ → B) g) η n h σ))

continuous-∘ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} {f : B → C} {g : A → B} →
  continuous f → continuous g → continuous (f ∘ g)
continuous-∘ {A = A} {B = B} {C = C} {f = f} {g = g} μ η =
  continuous-com {B = B} {C = λ _ → C} f g μ η

continuous-×-mk : ∀ {u v w} (X : Type u) (A : X → Type v) (B : X → Type w) {f : (x : X) → A x} {g : (x : X) → B x} →
                   continuous f → continuous g → continuous (λ x → (f x , g x))
continuous-×-mk X A B {f = f} {g = g} = continuous-Σ-mk X A (λ x _ → B x) f g

swap : ∀ {u v} {A : Type u} {B : Type v} → A × B → B × A
swap w = (pr₂ w , pr₁ w)

swap-continuous : ∀ {u v} (A : Type u) (B : Type v) → continuous (swap {A = A} {B = B})
swap-continuous A B = continuous-×-mk (A × B) (λ _ → B) (λ _ → A) (continuous-pr₂ (λ _ → B)) (continuous-pr₁ (λ _ → B))

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A = PathP (λ _ → A) (continuous-const _ _ A)

Path-continuous : ∀ {u v} {A : Type u} {B : A → Type v} {f g : (x : A) → B x} → continuous B →
                    continuous f → continuous g → continuous (λ x → Path (B x) (f x) (g x))
Path-continuous {A = A} {B = B} {f = f} {g = g} α β γ =
  PathP-continuous {X = A} (const _ I ∘ B) (λ x → continuous-const _ _ (B x)) f g
    (continuous-∘ (continuous-const′ _ I) α) β γ

idp : ∀ {u} {A : Type u} (a : A) → Path A a a
idp {A = A} a = weg (λ _ → a) (continuous-const A I a)

coe-continuous : ∀ {u} (A : I → Type u) (μ : continuous A) (i : I) → continuous (coe A μ i)
coe-continuous A μ i = continuous-coe (λ _ → A) (λ _ → μ) (λ _ → i) (idfun (A 0))
  (continuous-const _ _ A) (continuous-const _ _ i) (continuous-idfun (A 0))

_⁻¹ : ∀ {u} {A : I → Type u} {μ : continuous A} {a : A 0} {b : A 1} →
        PathP A μ a b → PathP (A ∘ neg) (continuous-∘ μ continuous-neg) b a
_⁻¹ {A = A} (weg φ μ) = weg (com {A = I} {B = I} {C = A} φ neg)
                            (continuous-com φ neg μ continuous-neg)

transport : ∀ {u} {A B : Type u} → Path (Type u) A B → A → B
transport p = coe (∂ p) (∂-continuous p) 1

transport-continuous : ∀ {u} {A B : Type u} (p : Path (Type u) A B) → continuous (transport p)
transport-continuous {A = A} p = coe-continuous (∂ p) (∂-continuous p) 1

seg : Path I 0 1
seg = weg (idfun I) (continuous-idfun I)

I-rec : ∀ {u} {A : Type u} (a b : A) → Path A a b → I → A
I-rec a b p = ∂ p

I-rec-continuous : ∀ {u} {A : Type u} {a b : A} (p : Path A a b) → continuous (I-rec a b p)
I-rec-continuous = ∂-continuous

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

  postulate S¹-β : (i : I) → S¹-ind (loop i) ↦ (∂ p) i
  {-# REWRITE S¹-β #-}

  postulate S¹-ind-continuous : continuous S¹-ind

open Circle

S¹-rec : ∀ {u} (C : Type u) (c : C) → Path C c c → S¹ → C
S¹-rec C c p = S¹-ind (λ _ → C) (continuous-const _ _ C) c p

S¹-rec-continuous : ∀ {u} (C : Type u) (c : C) (p : Path C c c) → continuous (S¹-rec C c p)
S¹-rec-continuous C c p = S¹-ind-continuous (λ _ → C) (continuous-const _ _ C) c p
