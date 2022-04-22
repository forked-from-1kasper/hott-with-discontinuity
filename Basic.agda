{-# OPTIONS --without-K --rewriting --prop #-}

open import Agda.Primitive
open import Proto
open import Logic

open Σ

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

-- continuous function
postulate C : ∀ {u v} {A : Type u} {B : A → Type v} → ((x : A) → B x) → Prop

record CΠ {u v} (A : Type u) (B : A → Type v) : Type (u ⊔ v) where
  constructor ⟨_,_⟩
  field
    inj  : Π A B
    pres : C inj

open CΠ

-- do not consufe with smooth functions
C¹ : ∀ {u v} {A : Type u} {B : A → Type v} → ((x : A) → B x) → Prop
C¹ = C

C² : ∀ {u v w} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type w} →
       ((a : A) → (b : B a) → C a b) → Prop u
C² {A = A} φ = C φ ∧ ((a : A) → C (φ a))

C³ : ∀ {u v w k} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type w}
       {D : (a : A) → (b : B a) → C a b → Type k} →
       ((a : A) → (b : B a) → (c : C a b) → D a b c) → Prop (u ⊔ v)
C³ {A = A} φ = C φ ∧ ((a : A) → C² (φ a))

postulate
  C-neg   : C neg

  C-const  : ∀ {u v} (A : Type u) (B : Type v) (a : A) → C (const A B a)
  C-const′ : ∀ {u v} (A : Type u) (B : Type v) → C (const A B)
  C-def    : ∀ {u v} (A : Type u) (B : A → Type v) (f : (x : A) → B x) →
    C f ⟷ ((n : ℕ) → (g : □ n → A) → C g → C (com f g))

postulate
  coe       : ∀ {u} (A : I → Type u) → C A → (i : I) → A 0 → A i
  C-coe     : ∀ {u v} {X : Type u} (A : X → I → Type v) (μ : (x : X) → C (A x)) (f : X → I) (g : (x : X) → A x 0) →
                C A → C f → C g → C (λ x → coe (A x) (μ x) (f x) (g x))
  coe-const : ∀ {u} (A : Type u) (i : I) → coe (λ _ → A) (C-const _ _ A) i ↦ idfun A
  coe-idfun : ∀ {u} (A : I → Type u) (μ : C A) → coe A μ 0 ↦ idfun (A 0)
{-# REWRITE coe-const coe-idfun #-}

data PathP {u} (A : I → Type u) (μ : C A) : A 0 → A 1 → Type u where
  weg : (f : (i : I) → A i) → C f → PathP A μ (f 0) (f 1)

module _ {u} {A : I → Type u} {μ : C A} {a : A 0} {b : A 1} where
  ∂ : PathP A μ a b → (i : I) → A i
  ∂ (weg φ _) = φ

  ∂-C : (p : PathP A μ a b) → C (∂ p)
  ∂-C (weg _ μ) = μ

  postulate ∂-0 : (p : PathP A μ a b) → (∂ p) 0 ↦ a
  postulate ∂-1 : (p : PathP A μ a b) → (∂ p) 1 ↦ b
  {-# REWRITE ∂-0 ∂-1 #-}

postulate
  PathP-C : ∀ {u v} {X : Type u} (A : X → I → Type v) (μ : (x : X) → C (A x)) (a : (x : X) → A x 0) (b : (x : X) → A x 1) →
              C A → C a → C b → C (λ (x : X) → PathP (A x) (μ x) (a x) (b x))
  C-weg   : ∀ {u v} {X : Type u} (A : X → I → Type v) (μ : (x : X) → C (A x)) (f : (x : X) → (i : I) → A x i)
              (η : (x : X) → C (f x)) → C A → C f → C (λ x → weg {A = A x} {μ = μ x} (f x) (η x))
  C-∂     : ∀ {u v} {X : Type u} (A : X → I → Type v) (μ : (x : X) → C (A x)) (a : (x : X) → A x 0) (b : (x : X) → A x 1)
              (p : (x : X) → PathP (A x) (μ x) (a x) (b x)) (f : X → I) →
              C A → C a → C b → C p → C f → C (λ x → ∂ (p x) (f x))

  C-inj   : ∀ {u v} (A : Type u) (B : A → Type v) → C (inj {A = A} {B = B})
  C-⟨⟩    : ∀ {u v w} {X : Type u} (A : X → Type v) (B : (x : X) → A x → Type w)
              (f : (x : X) → (a : A x) → B x a) (μ : (x : X) → C (f x)) →
              C A → C B → C f → C (λ x → ⟨ f x , μ x ⟩)

postulate
  Π-C : ∀ {u v w} {X : Type u} (A : X → Type v) (B : (x : X) → A x → Type w) →
          C A → C B → C (λ (x : X) → Π (A x) (B x))

postulate
  Σ-C     : ∀ {u v w} {X : Type u} (A : X → Type v) (B : (x : X) → A x → Type w) →
              C A → C B → C (λ (x : X) → Σ (A x) (B x))
  C-pr₁   : ∀ {u v} {A : Type u} (B : A → Type v) → C (pr₁ {B = B})
  C-pr₂   : ∀ {u v} {A : Type u} (B : A → Type v) → C (pr₂ {B = B})
  C-Σ-mk  : ∀ {u v w} (X : Type u) (A : X → Type v) (B : (x : X) → A x → Type w)
              (f : (x : X) → A x) (g : (x : X) → B x (f x)) → C f → C g →
              C {B = λ x → Σ (A x) (B x)} (λ x → (f x , g x))
  C-Σ-ind : ∀ {u v w k} {X : Type u} (A : X → Type v) (B : (x : X) → A x → Type w)
              (P : (x : X) → Σ (A x) (B x) → Type k) (f : (x : X) → (a : A x) → (b : B x a) → P x (a , b))
              (g : (x : X) → Σ (A x) (B x)) → C A → C B → C P → C³ f → C g → C (λ x → Σ-ind (P x) (f x) (g x))

postulate
  +-C     : ∀ {u v w} {X : Type u} (A : X → Type v) (B : X → Type w) →
              C A → C B → C (λ x → A x + B x)
  C-inl   : ∀ {u v w} {X : Type u} (A : X → Type v) (B : X → Type w) → (f : (x : X) → A x) →
              C f → C (λ x → inl {A = A x} {B = B x} (f x))
  C-inr   : ∀ {u v w} {X : Type u} (A : X → Type v) (B : X → Type w) → (g : (x : X) → B x) →
              C g → C (λ x → inr {A = A x} {B = B x} (g x))
  C-+-ind : ∀ {u v w k} (X : Type u) {A : X → Type v} {B : X → Type w} (P : (x : X) → A x + B x → Type k) →
              (f : (x : X) → (a : A x) → P x (inl a)) → (g : (x : X) → (b : B x) → P x (inr b)) →
              (h : (x : X) → A x + B x) → C A → C B → C P → C² f → C² g → C h →
              C (λ x → +-ind (P x) (f x) (g x) (h x))

C-idfun : ∀ {u} (A : Type u) → C (idfun A)
C-idfun A = ∧-right (C-def A (λ _ → A) (idfun A)) (λ (n : ℕ) (g : □ n → A) (μ : C g) → μ)

C-com : ∀ {u v w} {A : Type u} {B : Type v} {P : B → Type w} →
          (f : (b : B) → P b) → (g : A → B) → C f → C g → C (com f g)
C-com {A = A} {B = B} {P = P} f g μ η = ∧-right (C-def A (P ∘ g) (com f g))
  (λ (n : ℕ) (h : □ n → A) (σ : C h) →
    ∧-left (C-def B P f) μ n (g ∘ h)
      (∧-left (C-def A (λ _ → B) g) η n h σ))

C-∘ : ∀ {u v w} {X : Type u} {Y : Type v} {Z : Type w}
        {f : Y → Z} {g : X → Y} → C f → C g → C (f ∘ g)
C-∘ {X = X} {Y = Y} {Z = Z} {f = f} {g = g} μ η =
  C-com {B = Y} {P = λ _ → Z} f g μ η

C-×-mk : ∀ {u v w} (X : Type u) (A : X → Type v) (B : X → Type w)
           {f : (x : X) → A x} {g : (x : X) → B x} →
           C f → C g → C (λ x → (f x , g x))
C-×-mk X A B {f = f} {g = g} = C-Σ-mk X A (λ x _ → B x) f g

swap : ∀ {u v} {A : Type u} {B : Type v} → A × B → B × A
swap w = (pr₂ w , pr₁ w)

swap-C : ∀ {u v} (A : Type u) (B : Type v) → C (swap {A = A} {B = B})
swap-C A B = C-×-mk (A × B) (λ _ → B) (λ _ → A) (C-pr₂ (λ _ → B)) (C-pr₁ (λ _ → B))

Path : ∀ {u} (A : Type u) → A → A → Type u
Path A = PathP (λ _ → A) (C-const _ _ A)

Path-C : ∀ {u v} {A : Type u} {B : A → Type v} {f g : (x : A) → B x} → C B →
           C f → C g → C (λ x → Path (B x) (f x) (g x))
Path-C {A = A} {B = B} {f = f} {g = g} α β γ =
  PathP-C {X = A} (const _ I ∘ B) (λ x → C-const _ _ (B x)) f g
    (C-∘ (C-const′ _ I) α) β γ

idp : ∀ {u} {A : Type u} (a : A) → Path A a a
idp {A = A} a = weg (λ _ → a) (C-const A I a)

coe-C : ∀ {u} (A : I → Type u) (μ : C A) (i : I) → C (coe A μ i)
coe-C A μ i = C-coe (λ _ → A) (λ _ → μ) (λ _ → i) (idfun (A 0))
  (C-const _ _ A) (C-const _ _ i) (C-idfun (A 0))

_⁻¹ : ∀ {u} {A : I → Type u} {μ : C A} {a : A 0} {b : A 1} →
        PathP A μ a b → PathP (A ∘ neg) (C-∘ μ C-neg) b a
_⁻¹ {A = A} p = weg (com {A = I} {B = I} {C = A} (∂ p) neg)
                    (C-com (∂ p) neg (∂-C p) C-neg)

_⬝_ : ∀ {u} {A : Type u} {a b c : A} → Path A a b → Path A b c → Path A a c
_⬝_ {A = A} {a = a} {b = b} {c = c} p q = coe (Path A a ∘ ∂ q)
  (Path-C {f = λ _ → a} (C-const _ _ A)
    (C-const _ _ a) (∂-C q)) 1 p

transport : ∀ {u} {A B : Type u} → Path (Type u) A B → A → B
transport p = coe (∂ p) (∂-C p) 1

transport-C : ∀ {u} {A B : Type u} (p : Path (Type u) A B) → C (transport p)
transport-C {A = A} p = coe-C (∂ p) (∂-C p) 1

seg : Path I 0 1
seg = weg (idfun I) (C-idfun I)

I-rec : ∀ {u} {A : Type u} (a b : A) → Path A a b → I → A
I-rec a b p = ∂ p

I-rec-C : ∀ {u} {A : Type u} {a b : A} (p : Path A a b) → C (I-rec a b p)
I-rec-C = ∂-C

ap : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → C f →
     {a b : A} → Path A a b → Path B (f a) (f b)
ap f μ p = weg (f ∘ ∂ p) (C-∘ μ (∂-C p))

_~_ : ∀ {u v} {A : Type u} {B : A → Type v} (f g : (x : A) → B x) → Type (u ⊔ v)
_~_ {A = A} {B = B} f g = CΠ A (λ x → Path (B x) (f x) (g x))

funext : ∀ {u v} {A : Type u} {B : A → Type v} {f g : Π A B} →
           C f → C g → f ~ g → Path (Π A B) f g
funext μ η p = weg (λ i → λ x → ∂ (inj p x) i) _

data Id {u} (A : Type u) : A → A → Type u where
  refl : (a : A) → Id A a a

hprop : ∀ {u} (A : Type u) → Type u
hprop A = (a b : A) → Path A a b

hset : ∀ {u} (A : Type u) → Type u
hset A = (a b : A) → hprop (Path A a b)

hgroupoid : ∀ {u} (A : Type u) → Type u
hgroupoid A = (a b : A) → hset (Path A a b)

prop : ∀ {u} (A : Type u) → Type u
prop A = (a b : A) → Id A a b

set : ∀ {u} (A : Type u) → Type u
set A = (a b : A) → prop (Path A a b)

Id⇒Path : ∀ {u} {A : Type u} {a b : A} → Id A a b → Path A a b
Id⇒Path (refl a) = idp a

data S¹ : Set where
  base : S¹

loop : I → S¹
loop i₀ = base
loop i₁ = base

postulate loop-C : C loop

loop-S¹ : Path S¹ base base
loop-S¹ = weg loop loop-C

module _ {u} (B : S¹ → Type u) (μ : C B) (b : B base)
         (p : PathP (B ∘ loop) (C-∘ μ loop-C) b b) where

  S¹-ind : (x : S¹) → B x
  S¹-ind base = b

  postulate S¹-β : (i : I) → S¹-ind (loop i) ↦ (∂ p) i
  {-# REWRITE S¹-β #-}

postulate S¹-ind-C : ∀ {u v} {X : Type u} (B : X → S¹ → Type v) (μ : (x : X) → C (B x)) (b : (x : X) → B x base)
                       (p : (x : X) → PathP (B x ∘ loop) (C-∘ (μ x) loop-C) (b x) (b x)) (f : X → S¹) →
                       C B → C b → C p → C f → C (λ x → S¹-ind (B x) (μ x) (b x) (p x) (f x))

S¹-rec : ∀ {u} (B : Type u) (b : B) → Path B b b → S¹ → B
S¹-rec B b p = S¹-ind (λ _ → B) (C-const _ _ B) b p

S¹-rec-C : ∀ {u v} {X : Type u} (B : X → Type v) (b : (x : X) → B x)
             (p : (x : X) → Path (B x) (b x) (b x)) (f : X → S¹) →
             C B → C b → C p → C f → C (λ x → S¹-rec (B x) (b x) (p x) (f x))
S¹-rec-C B b p f α β γ δ =
  S¹-ind-C (λ x _ → B x) (λ x → C-const _ _ (B x)) b p f
    (C-∘ (C-const′ _ S¹) α) β γ δ
