-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Anomalous regularization of passive scalars: the main results

A standalone, Mathlib-only statement of the main results of S. Armstrong and V. Vicol,
*Anomalous regularization of passive scalars up to the Obukhov–Corrsin exponent*: Theorems A, B
and C and Corollary D for the velocity field constructed in Section 2 of the paper, and
Theorems A and B also in an existential form. Theorem and equation numbers refer to the paper.

We work on the torus `𝕋² = ℝ²/ℤ²`, realized by `ℤ²`-periodic functions on `ℝ² = Fin 2 → ℝ`;
integrals over `𝕋²` are integrals over the open unit square `(0,1)²`. Mathlib's norm `‖·‖` on
`Fin 2 → ℝ` is the sup norm; Euclidean lengths are written with `normSq`. For a velocity field
`b(t,x)` and a diffusivity `κ > 0`, solutions of the advection–diffusion equation

  `∂ₜθ + b·∇θ = κΔθ`  on `(t₁, t₂) × 𝕋²`,  `θ(t₁,·) = f`,

are understood in the weak (energy) sense of `IsWeakSolutionOn` below.

* **Theorems A and B, existential form** (the first part of the file, self-contained). For
  `0 < α < 1/3` and `0 < s < (1-α)/2` there are a bounded, periodic, divergence-free velocity
  field `b ∈ C^{0,α}(ℝ × 𝕋²)` and disjoint diffusivity bands `𝒦 = ⋃_M [κ_M/2, 2κ_M]`, `κ_M ↓ 0`,
  such that, uniformly in `κ ∈ 𝒦`: every weak solution is bounded in `C^{0,s}(𝕋²)` at positive
  times by `C ‖f‖_{L²}` (`interior_regularity`); and every weak solution dissipates a fixed
  fraction of the variance of its datum on each unit time interval, so that its variance decays
  exponentially (`uniform_anomalous_dissipation`). Both hold for one velocity field and one set
  of bands (`interior_regularity_and_dissipation`).
* **The construction, and Theorems A–D for it.** The definitions of Section 2: the parameters
  `q` and `ζ` (2.1)–(2.2), the exponents and scales (2.3)–(2.4), the shears, cutoffs and labels
  (2.6)–(2.10), the flow (2.11), the stream recursion (2.12) and the bands (2.18). For every
  integer `Λ ≥ Λ₀` the recursion can be carried out and its velocity fields converge to a limit
  `b`, for which Theorems A and B hold with the bands (2.18)
  (`interior_regularity_construction`, `uniform_anomalous_dissipation_construction`), together
  with the local interior regularity of Theorem C (`local_interior_regularity`) and the
  vanishing-diffusivity limits of Corollary D (`vanishing_diffusivity_limits`,
  `vanishing_diffusivity_limits_local`).

Three further theorems certify that the hypotheses of the construction can be met: a fast profile
exists (`exists_isFastProfile`), the recursion can be carried out for every `Λ ≥ 128`
(`exists_isOCStreamSeq`), and the velocity field of an admissible stream has a unique flow
(`existsUnique_streamFlow`), from which the flow `streamFlow` of the recursion is defined.
-/

@[expose] public section

open Filter MeasureTheory Topology

noncomputable section

namespace AVRegularityChallenge

/-! ## Euclidean plane, torus and Sobolev notions -/

/-- The Euclidean dot product on `ℝ² = Fin 2 → ℝ`. -/
def dot (x y : Fin 2 → ℝ) : ℝ := ∑ i, x i * y i

/-- The squared Euclidean length on `ℝ²`. -/
def normSq (x : Fin 2 → ℝ) : ℝ := dot x x

/-- The open unit square `(0,1)²`, a full-measure fundamental cell of `𝕋²`. -/
def unitCube : Set (Fin 2 → ℝ) := Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1

/-- `ℤ²`-periodicity: `f (x + n) = f x` for all `n ∈ ℤ²` and `x ∈ ℝ²`. -/
def IsZ2Periodic {β : Type*} (f : (Fin 2 → ℝ) → β) : Prop :=
  ∀ (n : Fin 2 → ℤ) (x : Fin 2 → ℝ), f (x + fun i => (n i : ℝ)) = f x

/-- `‖f‖²_{L²(𝕋²)} = ∫_{(0,1)²} f²`. -/
def l2NormSq (f : (Fin 2 → ℝ) → ℝ) : ℝ := ∫ x in unitCube, f x ^ 2

/-- The classical gradient of `f : ℝ² → ℝ`, coordinatewise. -/
def spaceGrad (f : (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun x i => fderiv ℝ f x (Pi.single i (1 : ℝ))

/-- `u ∈ L²(U)`. -/
abbrev MemL2On (U : Set (Fin 2 → ℝ)) (u : (Fin 2 → ℝ) → ℝ) : Prop :=
  MemLp u 2 (volume.restrict U)

/-- Each component of `Du` lies in `L²(U)`. -/
def GradMemL2On (U : Set (Fin 2 → ℝ)) (Du : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ i : Fin 2, MemL2On U (fun x => Du x i)

/-- `gi` is the weak `i`-th partial derivative of `u` on `U`. -/
def HasWeakPartialDerivOn (U : Set (Fin 2 → ℝ)) (i : Fin 2)
    (u gi : (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (Pi.single i (1 : ℝ)) = -∫ x in U, gi x * φ x

/-- `Du` is the weak gradient of `u` on `U`. -/
def HasWeakGradientOn (U : Set (Fin 2 → ℝ)) (u : (Fin 2 → ℝ) → ℝ)
    (Du : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ i : Fin 2, HasWeakPartialDerivOn U i u (fun x => Du x i)

/-- `u ∈ H¹(𝕋²)` with weak gradient `Du`: both periodic, square integrable on the cell, and
`Du` is the weak gradient of `u` on all of `ℝ²`. -/
def IsPeriodicH1With (u : (Fin 2 → ℝ) → ℝ) (Du : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  IsZ2Periodic u ∧ IsZ2Periodic Du ∧ MemL2On unitCube u ∧ GradMemL2On unitCube Du ∧
    HasWeakGradientOn Set.univ u Du

/-! ## Velocity fields, weak solutions and the Hölder norm -/

/-- The velocity class of Theorem A: `b ∈ C^{0,α}(ℝ × 𝕋²)` is bounded, `ℤ²`-periodic in space
and `1`-periodic in time, jointly `α`-Hölder for the distance `|t - u| + |x - y|` (Euclidean
`|x - y|`; an upper bound only, so smoother fields also qualify), and divergence free in the
sense of distributions on every time slice. -/
def IsHolderDivFreeVelocity (α : ℝ) (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  (∀ t, IsZ2Periodic (b t)) ∧
  (∀ t x, b (t + 1) x = b t x) ∧
  (∃ C : ℝ, ∀ t x, ‖b t x‖ ≤ C) ∧
  (∃ C : ℝ, ∀ t u : ℝ, ∀ x y : Fin 2 → ℝ,
    ‖b t x - b u y‖ ≤ C * (|t - u| + Real.sqrt (normSq (x - y))) ^ α) ∧
  (∀ t : ℝ, ∀ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, dot (b t x) (spaceGrad φ x) = 0)

/-- Test functions for a weak solution on `[t₁, t₂] × 𝕋²`: smooth on `ℝ × ℝ²`, `ℤ²`-periodic in
space, vanishing for `t ≥ t₂`. -/
def IsWindowTestFunction (t₂ : ℝ) (φ : ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin 2 → ℝ) => φ p.1 p.2) ∧
  (∀ t, IsZ2Periodic (φ t)) ∧ ∀ t, t₂ ≤ t → ∀ x, φ t x = 0

/-- `θ` is a weak solution on `[t₁, t₂] × 𝕋²` of `∂ₜθ + b·∇θ − κΔθ = 0`, `θ(t₁) = f`, with
spatial weak gradient `Dθ`: `θ ∈ L^∞_t L²_x ∩ L²_t H¹_x`, weakly continuous in time on the closed
window, the drift term `b·Dθ` is integrable (so every integral below is a genuine Lebesgue
integral), and the
weak formulation holds against every window test function. -/
def IsWeakSolutionOnGrad (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (κ t₁ t₂ : ℝ) (f : (Fin 2 → ℝ) → ℝ)
    (θ : ℝ → (Fin 2 → ℝ) → ℝ) (Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  (∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
    (∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, l2NormSq (θ t) ≤ C) ∧
    MemLp (fun p : ℝ × (Fin 2 → ℝ) => θ p.1 p.2) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) ∧
    (∀ i : Fin 2, MemLp (fun p : ℝ × (Fin 2 → ℝ) => Dθ p.1 p.2 i) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsPeriodicH1With (θ t) (Dθ t)) ∧
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => dot (b p.1 p.2) (Dθ p.1 p.2))
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) ∧
    (∀ ψ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ContinuousOn (fun t => ∫ x in unitCube, θ t x * ψ x) (Set.Icc t₁ t₂)) ∧
    (∀ φ : ℝ → (Fin 2 → ℝ) → ℝ, IsWindowTestFunction t₂ φ →
      ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube,
        (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
          + dot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
          + κ * dot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
        = ∫ x in unitCube, f x * φ t₁ x)

/-- `θ` is a weak solution on `[t₁, t₂] × 𝕋²` of `∂ₜθ + b·∇θ − κΔθ = 0`, `θ(t₁) = f`, for some
spatial weak gradient. -/
def IsWeakSolutionOn (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (κ t₁ t₂ : ℝ) (f : (Fin 2 → ℝ) → ℝ)
    (θ : ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  ∃ Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ, IsWeakSolutionOnGrad b κ t₁ t₂ f θ Dθ

/-- The torus distance `d(x,y) = min_{n ∈ ℤ²} |x - y - n|`, with the Euclidean norm on `ℝ²`. -/
def torusDist (x y : Fin 2 → ℝ) : ℝ :=
  ⨅ n : Fin 2 → ℤ, Real.sqrt (normSq (x - y - fun i => (n i : ℝ)))

/-- The Hölder-norm bound (3.1),
`‖g‖_{C^{0,s}(𝕋²)} = ‖g‖_∞ + sup_{x ≠ y} |g x - g y| / d(x,y)^s ≤ K`, with the torus distance `d`.
Written pointwise: `sup_x A x + sup_{y ≠ z} B y z ≤ K` iff `A x + B y z ≤ K` for all `x` and all
`y, z` at positive torus distance, so no convention for suprema enters. -/
def CsNormLe (s : ℝ) (g : (Fin 2 → ℝ) → ℝ) (K : ℝ) : Prop :=
  ∀ x y z : Fin 2 → ℝ, torusDist y z ≠ 0 →
    |g x| + |g y - g z| / torusDist y z ^ s ≤ K

/-! ## Theorems A and B, existential form -/

/-- **Theorem A (interior regularity), existential form.** For `0 < α < 1/3` and
`0 < s < (1-α)/2` there are a bounded, periodic, divergence-free velocity field
`b ∈ C^{0,α}(ℝ × 𝕋²)` and disjoint diffusivity bands `𝒦 = ⋃_M [κ_M/2, 2κ_M]`, `κ_M ↓ 0`, such
that for every `0 < t₀ < T` there is `C` with: for all `a ∈ ℝ`, `κ ∈ 𝒦` and `f ∈ L²(𝕋²)`, a weak
solution on `[a, a+T]` with `θ(a) = f` exists, and every such solution has a representative
jointly continuous on `[a+t₀, a+T] × 𝕋²` with
`sup_{a+t₀ ≤ t ≤ a+T} ‖θ(t)‖_{C^{0,s}(𝕋²)} ≤ C ‖f‖₂`. -/
theorem interior_regularity (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) :
    ∃ b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
      ∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
      ∀ f : (Fin 2 → ℝ) → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
        ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
          ∃ Θ : ℝ → (Fin 2 → ℝ) → ℝ,
            ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) => Θ p.1 p.2)
              (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
            ∀ t ∈ Set.Icc (a + t₀) (a + T),
              IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
              CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) := by
  sorry

/-- **Theorem B (uniform anomalous dissipation), existential form.** For `0 < α < 1/3` there are
a bounded, periodic, divergence-free velocity field `b ∈ C^{0,α}(ℝ × 𝕋²)`, disjoint diffusivity
bands `𝒦 = ⋃_M [κ_M/2, 2κ_M]`, `κ_M ↓ 0`, and `c > 0` such that for all `a ∈ ℝ`, `κ ∈ 𝒦` and
`f ∈ L²(𝕋²)`, with `(f) = ∫_{𝕋²} f`:
(i) a weak solution `θ` on `[a, a+1]` with `θ(a) = f` exists, and every such solution, with
gradient `Dθ`, has `κ ∫_a^{a+1} ∫_{𝕋²} |Dθ|² ≥ c ‖f - (f)‖₂²`;
(ii) for every `t > a`, a weak solution `θ` on `[a, t]` with `θ(a) = f` exists, and every such
solution has `‖θ(t) - (f)‖₂² ≤ 4 e^{-2c(t-a)} ‖f - (f)‖₂²`. -/
theorem uniform_anomalous_dissipation (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    ∃ c : ℝ, 0 < c ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
        ∀ f : (Fin 2 → ℝ) → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → (Fin 2 → ℝ) → ℝ, ∃ Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ) ∧
        ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, ∀ Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ →
            c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
              κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, normSq (Dθ p.1 p.2)) ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
        ∀ f : (Fin 2 → ℝ) → ℝ, MemL2On unitCube f →
        ∀ t : ℝ, a < t →
        (∃ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a t f θ) ∧
        ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a t f θ →
          l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
            4 * Real.exp (-2 * c * (t - a)) *
              l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  sorry

/-- **Theorems A and B for one velocity field.** For `0 < α < 1/3` and `0 < s < (1-α)/2` there
are a bounded, periodic, divergence-free velocity field `b ∈ C^{0,α}(ℝ × 𝕋²)` and disjoint
diffusivity bands `𝒦 = ⋃_M [κ_M/2, 2κ_M]`, `κ_M ↓ 0`, such that the conclusions of
`interior_regularity` and of `uniform_anomalous_dissipation` hold for this `b` and `𝒦`. -/
theorem interior_regularity_and_dissipation (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) :
    ∃ b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
      ∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
      ∀ f : (Fin 2 → ℝ) → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
        ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
          ∃ Θ : ℝ → (Fin 2 → ℝ) → ℝ,
            ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) => Θ p.1 p.2)
              (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
            ∀ t ∈ Set.Icc (a + t₀) (a + T),
              IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
              CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))) ∧
    ∃ c : ℝ, 0 < c ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
        ∀ f : (Fin 2 → ℝ) → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → (Fin 2 → ℝ) → ℝ, ∃ Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ) ∧
        ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, ∀ Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ →
            c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
              κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, normSq (Dθ p.1 p.2)) ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
        ∀ f : (Fin 2 → ℝ) → ℝ, MemL2On unitCube f →
        ∀ t : ℝ, a < t →
        (∃ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a t f θ) ∧
        ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a t f θ →
          l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
            4 * Real.exp (-2 * c * (t - a)) *
              l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  sorry

/-! ## The construction (Section 2)

Throughout, `β = 1 + α`. -/

/-- The admissible range (2.1) of the scale separation parameter:
`1 < q < min{17/16, (2-β)/(2(β-1)), (1-s)/(β-1+s)}`. -/
def IsAdmissibleQ (α s q : ℝ) : Prop :=
  1 < q ∧ q < 17 / 16 ∧ q < (2 - (1 + α)) / (2 * ((1 + α) - 1)) ∧
    q < (1 - s) / ((1 + α) - 1 + s)

/-- The cutoff function (2.2): an even `ζ ∈ C_c^∞((-2/3, 2/3))` with `0 ≤ ζ ≤ 1`,
`∑_{k ∈ ℤ} ζ(t - k) = 1` and `∫ ζ² = 9/10`. For each `t` at most two terms of the sum are
nonzero. -/
def IsFastProfile (ζ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ t, ζ (-t) = ζ t) ∧ tsupport ζ ⊆ Set.Ioo (-(2 / 3)) (2 / 3) ∧
    (∀ t, 0 ≤ ζ t ∧ ζ t ≤ 1) ∧ (∀ t, ∑' k : ℤ, ζ (t - k) = 1) ∧
    ∫ t, ζ t ^ 2 = 9 / 10

/-- A cutoff function as in (2.2) exists. -/
theorem exists_isFastProfile : ∃ ζ : ℝ → ℝ, IsFastProfile ζ := by
  sorry

/-- The exponent `γ = (q-1)β/(q+1)` of (2.3). -/
def ocGamma (α q : ℝ) : ℝ := (q - 1) * (1 + α) / (q + 1)

/-- The exponent `δ = (q-1)/4 · (1 - (2q+1)β/(2q+2))` of (2.3). -/
def ocDelta (α q : ℝ) : ℝ := (q - 1) / 4 * (1 - (2 * q + 1) * (1 + α) / (2 * q + 2))

/-- The wavelengths (2.4): `ε_0 = 1` and `ε_m = ⌈Λ^{q^m/(q-1)}⌉⁻¹` for `m ≥ 1`. -/
def ocEpsilon (q : ℝ) (Λ : ℕ) (m : ℕ) : ℝ :=
  if m = 0 then 1 else ((⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊ : ℕ) : ℝ)⁻¹

/-- `a_m = ε_m^{β-2}`, the size of `∇b_m` up to a constant (Subsection 2.4). It does not appear in
the paper's statements; it is used only in the general form of Theorem C (and of Corollary D(b)). -/
def ocA (α q : ℝ) (Λ m : ℕ) : ℝ := ocEpsilon q Λ m ^ ((1 + α) - 2)

/-- The factor `L_m = 4⌈ε_{m-1}^{-δ}⌉ + 1` of (2.4), used for `m ≥ 1`, so that `τ'_m = h_m/L_m` and
`τ_m = h_m/L_m²`. -/
def ocL (α q : ℝ) (Λ m : ℕ) : ℕ :=
  4 * ⌈ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)⌉₊ + 1

/-- The renewal time `h_m = 2^{-25} / ⌈ε_{m-1}^{-(2-β+2δ)}⌉` of (2.4), used for `m ≥ 1`. -/
def ocTauPP (α q : ℝ) (Λ m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-25 : ℤ) /
    (⌈ocEpsilon q Λ (m - 1) ^ (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊ : ℝ)

/-- The margin length `τ_m′ = h_m / L_m` of (2.4). -/
def ocTauP (α q : ℝ) (Λ m : ℕ) : ℝ := ocTauPP α q Λ m / (ocL α q Λ m : ℝ)

/-- The pulse time `τ_m = h_m / L_m²` of (2.4). -/
def ocTau (α q : ℝ) (Λ m : ℕ) : ℝ := ocTauPP α q Λ m / (ocL α q Λ m : ℝ) ^ 2

/-- The label `l_{m,k} = ⌊(kτ_m + (h_m - τ_m)/2) / h_m⌋` of (2.8). -/
def ocLabel (α q : ℝ) (Λ m : ℕ) (k : ℤ) : ℤ :=
  ⌊((k : ℝ) * ocTau α q Λ m + (ocTauPP α q Λ m - ocTau α q Λ m) / 2) / ocTauPP α q Λ m⌋

/-- The slow cutoff (2.9), `ζ̂_{m,l}(t) = 𝖧((t - A_l - τ_m′)/τ_m′) 𝖧((B_l - τ_m′ - t)/τ_m′)`, with
`A_l = (l - 1/2)h_m`, `B_l = (l + 1/2)h_m` and `𝖧 = Real.smoothTransition`, which is
`f(t)/(f(t) + f(1-t))` with `f(t) = exp(-1/t)` for `t > 0` and `f(t) = 0` otherwise. -/
def slowEnvelope (α q : ℝ) (Λ m : ℕ) (l : ℤ) (t : ℝ) : ℝ :=
  Real.smoothTransition
      ((t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) / ocTauP α q Λ m) *
    Real.smoothTransition
      ((((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) / ocTauP α q Λ m)

/-- `ψ_{0,k}(x) = sin(2π x₁)` for `k ∈ 4ℤ + 1`, `sin(2π x₂)` for `k ∈ 4ℤ + 3`, and `0` for even
`k` (the coordinates `x₁, x₂` are `x 0, x 1`). -/
def psi0 (k : ℤ) (x : Fin 2 → ℝ) : ℝ :=
  if k % 4 = 1 then Real.sin (2 * Real.pi * x 0)
  else if k % 4 = 3 then Real.sin (2 * Real.pi * x 1)
  else 0

/-- The shear profiles (2.6), `ψ_{m,k}(y) = ε_m^β ψ_{0,k}(y/ε_m)`. -/
def ocShear (α q : ℝ) (Λ m : ℕ) (k : ℤ) (y : Fin 2 → ℝ) : ℝ :=
  ocEpsilon q Λ m ^ (1 + α) * psi0 k ((ocEpsilon q Λ m)⁻¹ • y)

/-- The rotation `σ = (0 -1; 1 0)`. -/
def sigmaMat : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The velocity field `∇^⊥ φ = σ ∇_x φ = (-∂₂φ, ∂₁φ)` of a stream function `φ`. -/
def streamVel (φ : ℝ → (Fin 2 → ℝ) → ℝ) (t : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  sigmaMat.mulVec (spaceGrad (φ t) x)

/-- Admissible stream functions: `C^∞` in `(t,x)` and `ℤ × ℤ²`-periodic. -/
def IsAdmissibleStream (φ : ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ) ∧
  ∀ (n : ℤ) (k : Fin 2 → ℤ) (t : ℝ) (x : Fin 2 → ℝ),
    φ (t + (n : ℝ)) (x + fun i => (k i : ℝ)) = φ t x

/-- `X` is the flow of the time-dependent field `b` on `ℝ²`: `X t x s` solves
`∂ₜ X(t,x,s) = b(t, X(t,x,s))` for all `t ∈ ℝ`, with `X(s,x,s) = x`. -/
def IsFlow (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (X : ℝ → (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) : Prop :=
  (∀ x s, X s x s = x) ∧
  (∀ x s t, HasDerivAt (fun r => X r x s) (b t (X t x s)) t)

/-- The velocity field of an admissible stream has exactly one flow. -/
theorem existsUnique_streamFlow (φ : ℝ → (Fin 2 → ℝ) → ℝ) (hφ : IsAdmissibleStream φ) :
    ∃! X : ℝ → (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ, IsFlow (streamVel φ) X := by
  sorry

/-- The flow (2.11) of the velocity field `∇^⊥ φ` of an admissible stream `φ`: the unique `X` with
`IsFlow (streamVel φ) X`. It depends only on the statement of `existsUnique_streamFlow`, not on
its proof. -/
def streamFlow (φ : ℝ → (Fin 2 → ℝ) → ℝ) (hφ : IsAdmissibleStream φ) :
    ℝ → (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ :=
  Classical.choose (existsUnique_streamFlow φ hφ).exists

/-- One step of the recursion (2.12): `φ_m(t,x)` equals
`φ_{m-1}(t,x) + ∑_{k ∈ ℤ} ζ̂_{m,l_{m,k}}(t) ζ_{m,k}(t) ψ_{m,k}(X_{m-1}(l_{m,k} h_m, x, t))`, with
the fast cutoff `ζ_{m,k}(t) = ζ((t - kτ_m)/τ_m)` (2.7) and `X_{m-1}` the flow (2.11) of
`∇^⊥ φ_{m-1}`. For each `t` only finitely many `k` contribute, so the `tsum` is a finite sum. -/
def ocNextStream (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (φ : ℝ → (Fin 2 → ℝ) → ℝ) (hφ : IsAdmissibleStream φ) : ℝ → (Fin 2 → ℝ) → ℝ :=
  fun t x => φ t x + ∑' k : ℤ,
    slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
      ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) *
      ocShear α q Λ m k
        (streamFlow φ hφ ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m) x t)

/-- The stream sequence of (2.12): `φ_0 = 0` and, for `m ≥ 1`, `φ_{m-1}` is admissible and `φ_m`
is obtained from it by `ocNextStream`. The velocity fields are `b_m = ∇^⊥ φ_m = streamVel (Φ m)`.
The sequence is determined by `α, q, Λ, ζ`. -/
def IsOCStreamSeq (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  Φ 0 = (fun _ _ => 0) ∧
    ∀ m : ℕ, 1 ≤ m →
      ∃ h : IsAdmissibleStream (Φ (m - 1)), Φ m = ocNextStream α q Λ ζ m (Φ (m - 1)) h

/-- For every integer `Λ ≥ 128` the recursion (2.12) can be carried out. -/
theorem exists_isOCStreamSeq (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ Φ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ, IsOCStreamSeq α q Λ ζ Φ := by
  sorry

/-- The permitted diffusivities (2.18): `𝒦 = ⋃_{M ≥ 1} 𝒦_M`,
`𝒦_M = [ε_M^{β-γ}/2, 2ε_M^{β-γ}]`. -/
def ocBandSet (α q : ℝ) (Λ : ℕ) : Set ℝ :=
  ⋃ M : ℕ, ⋃ (_ : 1 ≤ M),
    Set.Icc (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2)
      (2 * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q))

/-- An explicit absolute constant `c_* = (10A)⁻¹`, `A = 2C_r`, `C_r = 4cosh(10πr)/r²`, `r = 1/100`
(`c_* ≈ 1.19·10⁻⁶`). It does not appear in the paper. It enters only the hypothesis
`8T a_{n-2} ≤ c_*` of the general form of Theorem C (and of Corollary D(b)), which holds in the
paper's case `T = h_{n-1}`: `8h_{m+1}ε_m^{β-2} ≤ 2^{-22} < c_*` by (2.13). -/
def ocCStar : ℝ :=
  (10 * (2 * (4 * Real.cosh (10 * Real.pi * (1 / 100)) / (1 / 100) ^ 2)))⁻¹

/-! ## Theorems A and B for the construction -/

/-- **Theorem A for the construction.** Fix `0 < α < 1/3`, `0 < s < (1-α)/2`, `q` as in (2.1)
and `ζ` as in (2.2). There is `Λ₀ ≥ 128` such that for every integer `Λ ≥ Λ₀` the recursion
(2.12) can be carried out, its velocity fields `b_M = ∇^⊥ φ_M` converge to a bounded, periodic,
divergence-free `b ∈ C^{0,α}`, and, with the bands `𝒦` of (2.18), for every `0 < t₀ < T` there
is `C` such that for all `a ∈ ℝ`, `κ ∈ 𝒦`, `f ∈ L²(𝕋²)` a weak solution on `[a, a+T]` with
`θ(a) = f` exists and every such solution has a jointly continuous representative on
`[a+t₀, a+T] × 𝕋²` with `sup_{a+t₀ ≤ t ≤ a+T} ‖θ(t)‖_{C^{0,s}(𝕋²)} ≤ C ‖f‖₂`. -/
theorem interior_regularity_construction (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∃ Φ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ, IsOCStreamSeq α q Λ ζ Φ) ∧
      ∀ Φ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          IsHolderDivFreeVelocity α b ∧
          ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
            ∀ a : ℝ,
            ∀ κ ∈ ocBandSet α q Λ,
            ∀ f : (Fin 2 → ℝ) → ℝ, MemL2On unitCube f →
              (∃ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
              ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
                ∃ Θ : ℝ → (Fin 2 → ℝ) → ℝ,
                  ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) => Θ p.1 p.2)
                    (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                  ∀ t ∈ Set.Icc (a + t₀) (a + T),
                    IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                    CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) := by
  sorry

/-- **Theorem B for the construction (uniform anomalous dissipation).** Fix `0 < α < 1/3`,
`0 < s < (1-α)/2`, `q` as in (2.1) and `ζ` as in (2.2). There is `Λ₀ ≥ 128` such that for every
integer `Λ ≥ Λ₀` the recursion (2.12) can be carried out, its velocity fields `b_M = ∇^⊥ φ_M`
converge to a bounded, periodic, divergence-free `b ∈ C^{0,α}`, and, with the bands `𝒦` of
(2.18), there is `c > 0` such that for all `a ∈ ℝ`, `κ ∈ 𝒦` and `f ∈ L²(𝕋²)`, with
`(f) = ∫_{𝕋²} f`:
(i) a weak solution `θ` on `[a, a+1]` with `θ(a) = f` exists, and every such solution, with
gradient `Dθ`, has `κ ∫_a^{a+1} ∫_{𝕋²} |Dθ|² ≥ c ‖f - (f)‖₂²`;
(ii) for every `t > a`, a weak solution `θ` on `[a, t]` with `θ(a) = f` exists, and every such
solution has `‖θ(t) - (f)‖₂² ≤ 4 e^{-2c(t-a)} ‖f - (f)‖₂²`. -/
theorem uniform_anomalous_dissipation_construction (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∃ Φ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ, IsOCStreamSeq α q Λ ζ Φ) ∧
      ∀ Φ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          IsHolderDivFreeVelocity α b ∧
          ∃ c : ℝ, 0 < c ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : (Fin 2 → ℝ) → ℝ, MemL2On unitCube f →
              (∃ θ : ℝ → (Fin 2 → ℝ) → ℝ, ∃ Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
                IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ) ∧
              ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, ∀ Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
                IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ →
                  c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
                    κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, normSq (Dθ p.1 p.2)) ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : (Fin 2 → ℝ) → ℝ, MemL2On unitCube f →
              ∀ t : ℝ, a < t →
              (∃ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a t f θ) ∧
              ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolutionOn b κ a t f θ →
                l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
                  4 * Real.exp (-2 * c * (t - a)) *
                    l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  sorry

/-! ## Theorem C: local interior regularity -/

/-- The open Euclidean disc `B_r(c) = {y : |y - c| < r}` in `ℝ²`. -/
def euclidBall (c : Fin 2 → ℝ) (r : ℝ) : Set (Fin 2 → ℝ) := {y | normSq (y - c) < r ^ 2}

/-- The tube `𝒯 = {(t, F_t(y)) : t₁ - 8T < t < t₁, |y| < R}` of (9.11), for a flow `F`. -/
def outerPipe (F : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (t₁ T R : ℝ) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | t₁ - 8 * T < p.1 ∧ p.1 < t₁ ∧ ∃ y ∈ euclidBall 0 R, p.2 = F p.1 y}

/-- `θ` is a local energy solution of `∂ₜθ + b·∇θ - κΔθ = 0` in the tube `𝒯`: it is square
integrable there and satisfies the equation in the sense of distributions against smooth tests
compactly supported in `𝒯` (with `b·∇θ = div(bθ)` for divergence-free `b`), and its pullback
`U(t,y) = θ(t, F_t(y))` lies in `L^∞_t L²(B_R) ∩ L²_t H¹(B_R)` on `(t₁ - 8T, t₁)`, with weak
gradient `DU`. No lateral data are prescribed. -/
def IsLocalEnergySolution (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (κ : ℝ)
    (F : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (t₁ T R : ℝ) (θ : ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  MemLp (fun p : ℝ × (Fin 2 → ℝ) => θ p.1 p.2) 2 (volume.restrict (outerPipe F t₁ T R)) ∧
  (∀ φ : ℝ × (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ outerPipe F t₁ T R →
    ∫ p in outerPipe F t₁ T R, θ p.1 p.2 *
      (fderiv ℝ φ p (1, 0) + ∑ i : Fin 2, b p.1 p.2 i * fderiv ℝ φ p (0, Pi.single i (1 : ℝ))
        + κ * ∑ i : Fin 2,
          fderiv ℝ (fun p' => fderiv ℝ φ p' (0, Pi.single i (1 : ℝ))) p
            (0, Pi.single i (1 : ℝ))) = 0) ∧
  ∃ DU : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
    (∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      MemL2On (euclidBall 0 R) (fun y => θ t (F t y)) ∧
      ∫ y in euclidBall 0 R, θ t (F t y) ^ 2 ≤ C) ∧
    (∀ i : Fin 2, MemLp (fun p : ℝ × (Fin 2 → ℝ) => DU p.1 p.2 i) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => θ t (F t y)) (DU t))

/-- **Theorem C (local interior regularity), general form.** There is `Λ₀ ≥ 128` such that, for
every `Λ ≥ Λ₀` and the stream functions `Φ` of the construction, with `b` their limit velocity
field, and for constants `c_T, C_T > 0`, there is a constant `C₁` such that for tube data
`n ≥ 2`, `T, R > 0`, `0 < ϱ < 1/8`, `0 < ϑ < 4` with `c_T h_{n-1} ≤ T ≤ C_T h_{n-1}`,
`8T a_{n-2} ≤ c_*` and `C₁ max{ε_{n-1}^α T, √(κ_max T)} ≤ R ≤ 1/8` (`κ_max = sup 𝒦`), there is `C`
such that for every `t₁`, with `F_t` the flow of `b_{n-2}` normalized by `F_{t₁} = I`, every
`κ ∈ 𝒦` and every local energy solution `θ` in the tube `𝒯` of (9.11) (`outerPipe`): for each
`t ∈ I = [t₁ - ϑT, t₁]` the local trace of `θ(t)` (the `L²` limit from below of the pulled-back
slices) has a representative continuous on `K_t = F_t(B_{ϱR})` with
`‖θ(t)‖_{L^∞(K_t)} + [θ(t)]_{C^{0,s}(K_t)} ≤ C A`, where `A = (|𝒯|⁻¹ ∬_𝒯 |θ|²)^{1/2}`.

The paper's Theorem C is the case `c_T = C_T = 1`, `T = h_{n-1}`, with `m = n - 2`, `r_tube = R`,
`r_obs = ϱR`, `t₀ = (8 - ϑ)h_{m+1}` and `t_f = t₁`. Then the hypotheses on `R` are (9.13), the
condition `8T a_{n-2} ≤ c_*` holds by (2.13) (`8h_{m+1}ε_m^{β-2} ≤ 2^{-22} < c_*`), and the bound on
`K_t = X_m(t, D_{r_obs}, t_f)` gives the paper's bound for `U(t,·) = θ(t, X_m(t,·,t_f))` on
`D_{r_obs}` with `2C` in place of `C`. -/
theorem local_interior_regularity (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R ϱ ϑ : ℝ), 2 ≤ n → 0 < T → 0 < R → 0 < ϱ → ϱ < 1 / 8 →
              0 < ϑ → ϑ < 4 →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ κ ∈ ocBandSet α q Λ, ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ,
                  IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ →
                  ∃ Θ : ℝ → (Fin 2 → ℝ) → ℝ, ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 (ϱ * R)) ∧
                    Tendsto (fun r => ∫ y in euclidBall 0 (ϱ * R),
                        (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2)
                      (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (normSq (y - z)) ^ s ≤
                        C * Real.sqrt
                          ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                            ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2) := by
  sorry

/-! ## Corollary D: vanishing-diffusivity limits -/

/-- **Corollary D, global part (vanishing-diffusivity limits).** There is `Λ₀ ≥ 128` such that,
for every `Λ ≥ Λ₀` and the stream functions `Φ` of the construction, with `b` their limit velocity
field, there are constants `C(t₀,T)` such that: let `κ_i ∈ 𝒦`, `κ_i → 0`,
and let `θ_i` be weak solutions from a common time `a` with data `‖f_i‖₂ ≤ F`. A subsequence has
`f_i ⇀ f_*` in `L²`, and continuous representatives of `θ_i` converge locally uniformly on
`(a,∞) × 𝕋²` to a distributional solution of `∂ₜθ + b·∇θ = 0` with weak initial trace `f_*`,
which satisfies the bound of Theorem A with right side `C F` and is locally `C^{0,s/(1+s)}` in
time, uniformly in space. For any choice `κ_i ∈ 𝒦_{M_i}`, the solutions with velocity field
`b_{M_i}`, diffusivity `κ_i` and datum `f_i` differ from `θ_i` by a sequence tending to zero in
distributions, hence have the same distributional cluster limits. -/
theorem vanishing_diffusivity_limits (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∃ Cthm : ℝ → ℝ → ℝ,
          ∀ (a F : ℝ) (κ : ℕ → ℝ) (f : ℕ → (Fin 2 → ℝ) → ℝ) (θ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ),
            (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
            (∀ i, MemL2On unitCube (f i) ∧ Real.sqrt (l2NormSq (f i)) ≤ F) →
            (∀ i, ∀ T : ℝ, 0 < T → IsWeakSolutionOn b (κ i) a (a + T) (f i) (θ i)) →
            ∃ (σ : ℕ → ℕ) (fstar : (Fin 2 → ℝ) → ℝ) (Θ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ)
                (θstar : ℝ → (Fin 2 → ℝ) → ℝ),
              StrictMono σ ∧ MemL2On unitCube fstar ∧
              (∀ g : (Fin 2 → ℝ) → ℝ, MemL2On unitCube g →
                Tendsto (fun i => ∫ x in unitCube, f (σ i) x * g x) atTop
                  (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
              (∀ i, ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) => Θ i p.1 p.2)
                  (Set.Ioi a ×ˢ Set.univ) ∧
                ∀ t, a < t → IsZ2Periodic (Θ i t) ∧ Θ i t =ᵐ[volume.restrict unitCube] θ i t) ∧
              TendstoLocallyUniformlyOn (fun i (p : ℝ × (Fin 2 → ℝ)) => Θ (σ i) p.1 p.2)
                (fun p : ℝ × (Fin 2 → ℝ) => θstar p.1 p.2) atTop (Set.Ioi a ×ˢ Set.univ) ∧
              (∀ φ : ℝ × (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ →
                ∫ p, θstar p.1 p.2 *
                  (fderiv ℝ φ p (1, 0) +
                    ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, Pi.single j (1 : ℝ)))
                  = 0) ∧
              (∀ g : (Fin 2 → ℝ) → ℝ, MemL2On unitCube g →
                Tendsto (fun t => ∫ x in unitCube, θstar t x * g x) (𝓝[>] a)
                  (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
              (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∀ t ∈ Set.Icc (a + t₀) (a + T),
                IsZ2Periodic (θstar t) ∧ CsNormLe s (θstar t) (Cthm t₀ T * F)) ∧
              (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C' : ℝ,
                ∀ t ∈ Set.Icc (a + t₀) (a + T), ∀ t' ∈ Set.Icc (a + t₀) (a + T),
                ∀ x : Fin 2 → ℝ,
                  |θstar t x - θstar t' x| ≤ C' * |t - t'| ^ (s / (1 + s))) ∧
              (∀ (Mi : ℕ → ℕ) (θ' : ℕ → ℝ → (Fin 2 → ℝ) → ℝ),
                (∀ i, 1 ≤ Mi i ∧ κ i ∈ Set.Icc
                  (ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q) / 2)
                  (2 * ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q))) →
                (∀ i, ∀ T : ℝ, 0 < T →
                  IsWeakSolutionOn (streamVel (Φ (Mi i))) (κ i) a (a + T) (f i) (θ' i)) →
                ∀ φ : ℝ × (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                  tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ →
                  Tendsto (fun i => ∫ p, (θ i p.1 p.2 - θ' i p.1 p.2) * φ p) atTop (𝓝 0)) := by
  sorry

/-- **Corollary D, local part.** There is `Λ₀ ≥ 128` such that, for every `Λ ≥ Λ₀` and the stream
functions `Φ` of the construction, with `b` their limit velocity field, and for tube data
`n, T, R` as in `local_interior_regularity` (with its own `C₁`) and constants `C(ϱ, ϑ)`: local
energy solutions on one fixed tube with `κ_i ∈ 𝒦`,
`κ_i → 0` and normalized `L²` averages at most `F` have continuous representatives, a
subsequence of which converges uniformly on compact subsets of
`S = {(t, F_t(y)) : t₁ - 4T < t ≤ t₁, |y| < R/8}`. The limit is continuous on `S` (so it has the
one-sided top trace), solves `∂ₜθ + b·∇θ = 0` in the sense of distributions on the interior of
`S`, and satisfies every estimate of Theorem C on the inner tubes (all `0 < ϱ < 1/8`, `0 < ϑ < 4`) with
right side `C(ϱ, ϑ) F`. -/
theorem vanishing_diffusivity_limits_local (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R : ℝ), 2 ≤ n → 0 < T → 0 < R →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ → ℝ → ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ (F : ℝ) (κ : ℕ → ℝ) (θ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ),
                  (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
                  (∀ i, IsLocalEnergySolution b (κ i) (fun t y => X t y t₁) t₁ T R (θ i)) →
                  (∀ i, Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ i p.1 p.2 ^ 2) ≤ F) →
                  ∃ (σ : ℕ → ℕ) (Θ : ℕ → ℝ → (Fin 2 → ℝ) → ℝ) (θstar : ℝ → (Fin 2 → ℝ) → ℝ),
                    StrictMono σ ∧
                    (∀ i, ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) => Θ i p.1 p.2)
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                      (fun p : ℝ × (Fin 2 → ℝ) => Θ i p.1 p.2) =ᵐ[volume.restrict
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}]
                        (fun p : ℝ × (Fin 2 → ℝ) => θ i p.1 p.2)) ∧
                    (∀ K ⊆ {p : ℝ × (Fin 2 → ℝ) | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}, IsCompact K →
                      TendstoUniformlyOn (fun i (p : ℝ × (Fin 2 → ℝ)) => Θ (σ i) p.1 p.2)
                        (fun p : ℝ × (Fin 2 → ℝ) => θstar p.1 p.2) atTop K) ∧
                    ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) => θstar p.1 p.2)
                      {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                        ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                    (∀ φ : ℝ × (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                      tsupport φ ⊆ interior {p : ℝ × (Fin 2 → ℝ) | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} →
                      ∫ p, θstar p.1 p.2 *
                        (fderiv ℝ φ p (1, 0) +
                          ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, Pi.single j (1 : ℝ))) = 0) ∧
                    ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 →
                    ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |θstar t x| + |θstar t y - θstar t z| /
                        Real.sqrt (normSq (y - z)) ^ s ≤ C ϱ ϑ * F := by
  sorry

end AVRegularityChallenge
