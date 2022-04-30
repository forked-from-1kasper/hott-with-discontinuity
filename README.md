The goal of this project is to build an extension of Homotopy Type Theory capable of reasoning about discontinuous functions
such as, for example, f : ∥A∥ → A defined as f(|x|) = x, where |_| : A → ∥A∥ is a constructor of propositional truncation.

This seems to have at least following uses:
1. For each type we can define its “skeleton”, i.e a type containing all its points, but not containing any paths.
This is different from 0-truncation, because, for example, 0-truncation of homotopical reals equivalent to just singleton type
(homotopical reals itself equivalent to singleton), but their skeleton must be equivalent to ℤ.
Skeleton of interval type should be boolean, of S¹—singleton. In the ordinary HoTT we are unable to reason about such type,
since natural projection from A to its skeleton would be obviously discontinuous.
2. Now suppose we have some 1-Type A, its skeleton S(A), obvious map g : S(A) → A, and unit interval (0-Type) I = [0; 1].
We may define new HIT (for some equality with K axiom denoted as “Id”) T(A) with constructors:
ε : S(A) → T(A), ρ : Π (a b : S(A)), Path(A, g(a), g(b)) → I → T(A), ρ₀ : Id(T(A), ρ(a, b, p, 0), ε(a)), and ρ₁ : Id(T(A), ρ(a, b, p, 1), ε(b)).
For example, we expect T(R) (R is homotopical reals) to be equivalent to ℝ, T(S¹) to a circle in ℝ, and T(T(A)) to T(A).
Possibly, this may give another solution to “the problem of the two circles”.
3. Moreover, previous contruction should have nice generalization for ∞-Type. It should be, in some sense,
a reverse of [“shape” ʃ](https://homotopytypetheory.org/2015/09/25/realcohesion/) from real-cohesive HoTT.
4. Let R(A) be HIT (for Path-equaility) with following constructors: base : R(A), loop : A → base = base. For each 1-Type we probably can define some discontinuous f : ∥A∥₀ → U such that there should be a nice equivalence: A ≃ Σ (x : ∥A∥₀), R(f(x)). Knowing that fundamental group of R(A) is a free group on A allows us to calculate fundamental group of any 1-Type.