-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleEvolution.CellMean
public import AVRegularity.Statements.Intermediate.CycleReference.OcEll
public import AVRegularity.Definitions.CycleReference.OcRefCorrector
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsCellSolution
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellEnergyNorm
public import Mathlib.Analysis.Matrix.MeasurableSpace

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The `L^∞` size of a matrix-valued cell field. -/

/-- `‖G‖_∞ = sup_{t,z,i,j} |G_{ij}(t,z)|` in `[0, ∞]` (supremum of entries; any fixed matrix norm
gives an equivalent size). -/
def cellMetricSupNorm (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (z : Vec 2) (i : Fin 2) (j : Fin 2), ‖G t z i j‖ₑ

end AVRegularity
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity

/-! Factorial jet sums `∑ ρ^{|α|}/α! N_α`. -/

/-- `∑_{α ∈ S} ρ^{|α|}/α! · N_α` in `[0, ∞]`, `α! = a! b!` for `α = (a,b)`. -/
def factorialJetSum (S : Finset (ℕ × ℕ)) (ρ : ℝ) (N : ℕ × ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ p ∈ S, ENNReal.ofReal (ρ ^ (p.1 + p.2) / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))) * N p

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The vector source of the graph equation. -/

/-- The field `2i√η Gξ ρ` whose divergence is the first term of the graph equation. -/
def fibreGraphFlux (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ)
    (ρ : ℝ → Vec 2 → ℂ) : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fun t x => WithLp.toLp 2 fun k =>
    2 * Complex.I * (Real.sqrt η : ℂ) * (∑ j, (G t k j : ℂ) * ξ j) * ρ t x

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! The monomial `ξ^α`. -/

/-- `ξ^α = ξ₁^a ξ₂^b` for `α = (a,b)`. -/
def fibreMonomial (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) : ℂ := ξ 0 ^ p.1 * ξ 1 ^ p.2

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The Euclidean norm of a complex fibre frequency. -/

/-- `|ξ| = (|ξ₁|² + |ξ₂|²)^{1/2}` for `ξ ∈ ℂ²`. -/
def fibreNorm (ξ : Fin 2 → ℂ) : ℝ := Real.sqrt (∑ i, ‖ξ i‖ ^ 2)

/-! The bilinear form `ξ·Mξ` for complex `ξ`. -/

/-- `ξ·Mξ = ∑_{ij} ξ_i M_{ij} ξ_j` for a real matrix `M` and `ξ ∈ ℂ²` (bilinear, no conjugate:
the holomorphic continuation of the real quadratic form). -/
def fibreQuad (M : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, ξ i * (M i j : ℂ) * ξ j

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! Admissible cell metrics, `G` measurable, symmetric, `½I ≤ G ≤ 2I`. -/

/-- `G(t,z)` is jointly measurable, `ℤ²`-periodic in `z`, symmetric, and
`½|ξ|² ≤ ξ·Gξ ≤ 2|ξ|²` for every real `ξ`, at every `(t,z)`. -/
def IsCellMetric (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Measurable (fun p : ℝ × Vec 2 => G p.1 p.2) ∧
  (∀ t, AVenhance.IsZ2Periodic (G t)) ∧
  (∀ t z, (G t z).IsSymm) ∧
  ∀ t z (ξ : Vec 2),
    (1 / 2) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * G t z i j * ξ j ∧
      ∑ i, ∑ j, ξ i * G t z i j * ξ j ≤ 2 * ∑ i, ξ i ^ 2

end AVRegularity
end
end

section
@[expose] public section
open Filter Topology
open scoped ENNReal
namespace AVRegularity

/-! Families that are `C^K` in the slow parameter `Y` into a normed time space.
The time spaces `L^∞`, `L²_ul`, `ℰ` are not Banach-space
carriers in this development, so the notion is presented by a family of partial-derivative jets
converging in an extended norm. -/

/-- `J (a,b) Y` is the jet `∂₁^a ∂₂^b u(Y)` of a family `Y ↦ J (0,0) Y` of elements of a `𝕜`-module
`X`, on an open set `U ⊆ 𝕜²`, measured in the extended norm `N : X → [0,∞]`: for every
`|(a,b)| ≤ K` the jet is `N`-continuous at every `Y ∈ U`, and for `|(a,b)| < K` the partial
derivatives in the two coordinate directions exist in the `N`-sense at every `Y ∈ U` and equal
`J (a+1,b)` and `J (a,b+1)`. For `𝕜 = ℝ` this is `C^K` with continuous partial derivatives; for
`𝕜 = ℂ` it is complex differentiability. -/
def IsNormJetFamily {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X]
    (N : X → ℝ≥0∞) (K : ℕ) (U : Set (Fin 2 → 𝕜)) (J : ℕ × ℕ → (Fin 2 → 𝕜) → X) : Prop :=
  (∀ p : ℕ × ℕ, p.1 + p.2 ≤ K → ∀ Y ∈ U, Tendsto (fun Y' => N (J p Y' - J p Y)) (𝓝 Y) (𝓝 0)) ∧
  ∀ p : ℕ × ℕ, p.1 + p.2 < K → ∀ Y ∈ U,
    Tendsto (fun h : 𝕜 => N (h⁻¹ • (J p (Y + h • Pi.single 0 1) - J p Y) - J (p.1 + 1, p.2) Y))
      (𝓝[≠] 0) (𝓝 0) ∧
    Tendsto (fun h : 𝕜 => N (h⁻¹ • (J p (Y + h • Pi.single 1 1) - J p Y) - J (p.1, p.2 + 1) Y))
      (𝓝[≠] 0) (𝓝 0)

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! The multi-indices `|α| ≤ K` in two slow variables. -/

/-- The multi-indices `α = (a,b) ∈ ℕ²` with `|α| = a + b ≤ K`. -/
def jetIndices (K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (K + 1) ×ˢ Finset.range (K + 1)).filter fun p => p.1 + p.2 ≤ K

/-! The degree-`n` homogeneous part of a Taylor-coefficient family. -/

/-- `∑_{|α| = n} ξ^α a_α`, a finite sum in any complex module `X`. -/
def fibreHomogeneous {X : Type*} [AddCommMonoid X] [Module ℂ X] (a : ℕ × ℕ → X)
    (ξ : Fin 2 → ℂ) (n : ℕ) : X :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, fibreMonomial ξ p • a p

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The Taylor series of a scalar time-dependent coefficient family, e.g. the symbol
`λ(ξ)(t) = ∑ λ_α(t) ξ^α`. -/

/-- `λ(ξ)(t) = ∑'_α ξ^α λ_α(t)`. Used only where absolute summability is asserted. -/
def fibreSeriesC (a : ℕ × ℕ → ℝ → ℂ) (ξ : Fin 2 → ℂ) : ℝ → ℂ :=
  fun t => ∑' p, fibreMonomial ξ p * a p t

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The Taylor series of a time-dependent cell-function coefficient family, e.g. the row
`ℓ(ξ)(s) = ∑ ℓ_α(s) ξ^α`. -/

/-- `f(ξ)(t)(x) = ∑'_α ξ^α f_α(t)(x)`, pointwise in `(t,x)`. -/
def fibreSeriesFun (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (ξ : Fin 2 → ℂ) : ℝ → Vec 2 → ℂ :=
  fun t x => ∑' p, fibreMonomial ξ p * a p t x

end AVRegularity
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Admissible cell drifts, `v` bounded and divergence free. -/

/-- `v(t,z)` is jointly measurable, bounded, `ℤ²`-periodic in `z`, and weakly divergence free
for every `t`: `∫_{𝕋²} v(t)·∇φ = 0` for every real periodic `H¹` test `φ`. -/
def IsCellDrift (v : ℝ → Vec 2 → Vec 2) : Prop :=
  Measurable (fun p : ℝ × Vec 2 => v p.1 p.2) ∧
  (∃ M : ℝ, ∀ t z, ∑ i, v t z i ^ 2 ≤ M ^ 2) ∧
  (∀ t, AVenhance.IsZ2Periodic (v t)) ∧
  ∀ t (φ : TorusHkFunction 1 ℝ),
    ∫ x in AVenhance.unitCube,
      ∑ k : Fin 2, v t x k * φ.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x = 0

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The Taylor series of a coefficient family of cell trajectories, e.g. the graph
`r(ξ) = ∑ r_α ξ^α`. -/

/-- `D(ξ)(t)(a)(x) = ∑'_α ξ^α D_α(t)(a)(x)` for every jet index `a`, pointwise. The series is
pointwise, because the carrier of weak jets has only a real structure. -/
def fibreSeriesJet (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (ξ : Fin 2 → ℂ) : ℝ → RawJet2 1 ℂ :=
  fun t a x => ∑' p, fibreMonomial ξ p * r p t a x

/-! The covariant gradient `D_ξ = ∇_z + i√η ξ`. -/

/-- `D_θ h = ∇h + iθ h` for the Bloch shift `θ = √η ξ ∈ ℂ²`, applied to a raw order-one jet
(for complex `ξ` this is the holomorphic continuation). -/
def cellCovGradient (θ : Fin 2 → ℂ) (D : RawJet2 1 ℂ) : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fun x => WithLp.toLp 2 fun k => cellGradComp D k x + Complex.I * θ k * D (valueIndex2 1) x

/-! The metric-jet flux in the jet equation of the cell problem. -/

/-- At a fixed slow point, with metric jets `Gj β = ∂_Y^β G` and solution jets
`cj α = ∂_Y^α c`: the field `∑_{0<β≤α} C(α,β) (∂_Y^β G) ∇∂_Y^{α-β} c` of the jet equation,
`C(α,β) = C(a₁,b₁)·C(a₂,b₂)`. -/
def cellMetricJetFlux (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fun t x => WithLp.toLp 2 fun k => ∑ β ∈ (Finset.Iic α).filter (fun β => β ≠ 0),
    ((α.1.choose β.1 * α.2.choose β.2 : ℕ) : ℂ) *
      ∑ j : Fin 2, (Gj β t x k j : ℂ) * cellGradComp (cj (α.1 - β.1, α.2 - β.2) t) j x

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The mean-free projection `Q₀ = I - P₀`. -/

/-- `Q₀ u = u - ⟨u⟩`. -/
def cellQ0 (u : Vec 2 → ℂ) : Vec 2 → ℂ := fun x => u x - cellMean u

/-! The coefficients of the fibre operator `𝒢_ξ - λ`. -/

/-- The fibre operator at `ξ ∈ ℂ²` for contrast `η`: the cell metric is the `z`-independent
frozen metric `G(t)`, the drift is `v`, the Bloch shift is `θ = √η ξ` and the potential is
`κ = -lam`. Thus `lam = 0` is `𝒢_ξ = D_ξ·(G D_ξ ·) - v·D_ξ` (which expands to
`A + 2i√η(Gξ)·∇ - iw·ξ - ηξ·Gξ`, `w = √η v`) and `lam = λ` is `𝒢̃_ξ = 𝒢_ξ - λ`. -/
def fibreCoefficients (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (ξ : Fin 2 → ℂ) (lam : ℝ → ℂ) : CellCoefficients where
  G := fun t _ => G t
  v := v
  θ := fun k => (Real.sqrt η : ℂ) * ξ k
  κ := fun t => -lam t

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The effective fibre diffusivity `D^G = ηG + sym⟨w⊗χ⟩`. -/

/-- `D^G_{ij}(t) = ηG_{ij}(t) + ½(⟨w_i χ_j⟩ + ⟨w_j χ_i⟩)(t)` with `w = √η v` and
`χ_j` the cell trajectories (`χ_j = 𝒦_G w_j`). -/
def fibreBridgeMatrix (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (χ : Fin 2 → ℝ → RawJet2 1 ℂ) (t : ℝ) (i j : Fin 2) : ℂ :=
  (η : ℂ) * (G t i j : ℂ) + (1 / 2) *
    (cellMean (fun x => ((Real.sqrt η * v t x i : ℝ) : ℂ) * cellValue (χ j) t x) +
     cellMean (fun x => ((Real.sqrt η * v t x j : ℝ) : ℂ) * cellValue (χ i) t x))

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The scalar source of the graph equation. -/

/-- `-iQ₀(w·ξ(1+ρ)) + iρ⟨w·ξρ⟩` at time `t`, `w = √η v`, for a trial graph value `ρ`. -/
def fibreGraphSource (η : ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
    (ρ : ℝ → Vec 2 → ℂ) : ℝ → Vec 2 → ℂ :=
  fun t x =>
    cellQ0 (fun y => -Complex.I *
      (((Real.sqrt η : ℂ) * ∑ k, (v t y k : ℂ) * ξ k) * (1 + ρ t y))) x
      + Complex.I * ρ t x *
        cellMean (fun y => ((Real.sqrt η : ℂ) * ∑ k, (v t y k : ℂ) * ξ k) * ρ t y)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity

/-! Admissible intervals. -/

/-- The interval `[ta, ta + T]` of physical time (`S = T/ℓ²`) is admissible with thresholds
`Θ₀`, mark length `θs·ℓ²` and `c_adm = (1 - exp(-2))/288`: `τ/ℓ² ≥ Θ₀`, `S ≥ Θ₀`,
`∫_I J ≥ c_adm B T I` (as quadratic forms), and for each orientation `j` (index `0` is
`Π = e₁⊗e₁`, `k ≡ 3 (mod 4)`; index `1` is `Π = e₂⊗e₂`, `k ≡ 1 (mod 4)`) there are at least
`c_adm S/θs` pairwise disjoint marks `[a, a + θs ℓ²] ⊆ I`, each contained in a complete core
`[(k-1/3)τ, (k+1/3)τ]` of orientation `j`. -/
def IsOCAdmissibleInterval (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν B Θ₀ θs ta T : ℝ) :
    Prop :=
  Θ₀ ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 ∧ Θ₀ ≤ T / ocEll q Λ m ν ^ 2 ∧
  (∀ w : Vec 2, (1 - Real.exp (-2)) / 288 * B * T * vecDot w w
      ≤ ∫ t in ta..(ta + T), vecDot w ((ocRefFlux α q Λ ζ m ν t).mulVec w)) ∧
  ∀ j : Fin 2, ∃ marks : Finset ℝ,
    (1 - Real.exp (-2)) / 288 * (T / ocEll q Λ m ν ^ 2) / θs ≤ (marks.card : ℝ) ∧
    (∀ a ∈ marks, ta ≤ a ∧ a + θs * ocEll q Λ m ν ^ 2 ≤ ta + T ∧
      ∃ k : ℤ, k % 4 = (if j = 0 then 3 else 1) ∧
        IsOCCompleteCore α q Λ m (ocLabel α q Λ m k) k ∧
        ((k : ℝ) - 1 / 3) * ocTau α q Λ m ≤ a ∧
        a + θs * ocEll q Λ m ν ^ 2 ≤ ((k : ℝ) + 1 / 3) * ocTau α q Λ m) ∧
    ∀ a ∈ marks, ∀ b ∈ marks, a ≠ b →
      a + θs * ocEll q Λ m ν ^ 2 ≤ b ∨ b + θs * ocEll q Λ m ν ^ 2 ≤ a

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The norm `‖h‖_{𝒳_ξ(I)}`. -/

/-- `‖h‖_{𝒳_ξ(I)} = sup_{t∈I} ‖h(t)‖₂ + ‖D_ξ h‖_{L²(I×𝕋²)}` in `[0, ∞]`, `D_ξ = ∇ + iθ`,
`θ = √η ξ`. -/
def fibreXNorm (θ : Fin 2 → ℂ) (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ) : ℝ≥0∞ :=
  (⨆ t ∈ I, cellL2Norm (cellValue D t)) +
    (∫⁻ τ in I, cellL2Norm (cellCovGradient θ (D τ)) ^ 2) ^ (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The relation `D = 𝒦_G[src + div F]`, without choosing an operator: the inverse is a
relation. -/

/-- `D` is a bounded all-time mean-zero solution of `(∂ₜ - A)D = src + div F`: an energy
solution on all of `ℝ`, with `⟨D(t)⟩ = 0` for every `t`, and finite energy norm. By
`cycle_cell_inverse` such a `D` is unique (as a family of `L²` traces) and it is the
`𝒦_G` of the source. The energy solution is `IsCellSolution` (`H¹` jets a.e. in time). -/
def IsCellInverseValue (C : CellCoefficients) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (D : ℝ → RawJet2 1 ℂ) : Prop :=
  IsCellSolution Set.univ C src F D ∧ (∀ t, cellMean (cellValue D t) = 0) ∧
    cellEnergyNorm Set.univ D < ⊤

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The holomorphic fibre graph `ℛ = 1 + r` and symbol `λ`, presented by Taylor
coefficients. -/

/-- `(r, lam)` is a fibre graph of radius `ξ₀` and size `Cg` for contrast `η`, frozen metric `G(t)`
and drift `v` (`w = √η v`): `lam_α = 0` for `|α| ≤ 1`; for every complex `ξ` with `|ξ| < ξ₀`
the two Taylor series converge absolutely (in the energy norm, resp. uniformly in time), the
series value `r(ξ) = ∑ ξ^α r_α` is the bounded mean-zero all-time cell solution
`r = 𝒦_G[div(2i√η Gξ r) - iQ₀(w·ξ(1+r)) + ir⟨w·ξ r⟩]`, the symbol is
`λ(ξ) = -ηξ·Gξ - i⟨w·ξ r⟩`, and `‖r(ξ)‖_ℰ ≤ Cg|ξ|`; and the degree-`n`
homogeneous parts of `r` and `lam` are bounded by `Cg (2/ξ₀)^n |ξ|^n` in the energy norm, resp. the
uniform-in-time norm, for every complex `ξ`. The cell inverse uses all-time `G(t)`, `v(t)`:
histories are fixed. -/
def IsFibreGraph (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (ξ₀ Cg : ℝ) (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ) : Prop :=
  (∀ p : ℕ × ℕ, p.1 + p.2 ≤ 1 → ∀ t, lam p t = 0) ∧
  (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < ξ₀ →
    (∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * cellEnergyNorm Set.univ (r p) < ⊤) ∧
    (∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * ⨆ t, ‖lam p t‖ₑ < ⊤) ∧
    IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fibreGraphSource η v ξ (cellValue (fibreSeriesJet r ξ)))
      (fibreGraphFlux η G ξ (cellValue (fibreSeriesJet r ξ))) (fibreSeriesJet r ξ) ∧
    (∀ t, fibreSeriesC lam ξ t = -(η : ℂ) * fibreQuad (G t) ξ - Complex.I *
      cellMean (fun x => ((Real.sqrt η : ℂ) * ∑ k, (v t x k : ℂ) * ξ k) *
        cellValue (fibreSeriesJet r ξ) t x)) ∧
    cellEnergyNorm Set.univ (fibreSeriesJet r ξ) ≤ ENNReal.ofReal (Cg * fibreNorm ξ)) ∧
  (∀ (n : ℕ) (ξ : Fin 2 → ℂ),
    cellEnergyNorm Set.univ (fibreHomogeneous r ξ n) ≤
      ENNReal.ofReal (Cg * (2 / ξ₀) ^ n * fibreNorm ξ ^ n)) ∧
  ∀ (n : ℕ) (ξ : Fin 2 → ℂ) (t : ℝ),
    ‖fibreHomogeneous lam ξ n t‖ ≤ Cg * (2 / ξ₀) ^ n * fibreNorm ξ ^ n

end AVRegularity
end
end
