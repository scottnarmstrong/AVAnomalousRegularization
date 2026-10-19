-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.DiagSample
public import AVRegularity.Sobolev.Norms
public import AVRegularity.Statements.Intermediate.CycleComparison.IsBoxSmooth
public import AVRegularity.Statements.Intermediate.CycleComparison.IsFastIndependentOn
public import AVRegularity.Statements.Intermediate.Families.JetSup
public import AVRegularity.Statements.Intermediate.CycleComparison.IsTransverseOn
public import AVRegularity.Definitions.Families.MarkedLedger
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftMean

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The uniform-time cell-`L²` slow jet norm of order `j` of a coefficient `f(t,X,z)`,
`sup_{t∈I,X} ‖D_X^j f(t,X,·)‖_{L²(𝕋²)}`; the tail coefficients of the lift have such jets
through `K` bounded by `C Θ_ind^h`. -/

/-- `⨆_{t∈I} ⨆_X ‖z ↦ D_X^j (f t · z)(X)‖_{L²(𝕋²)}`. -/
def cellL2Jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ) (j : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → E) : ℝ≥0∞ :=
  ⨆ t ∈ I, ⨆ X : Vec 2,
    eLpNorm (fun z => iteratedFDeriv ℝ j (fun X' => f t X' z) X) 2
      (volume.restrict AVenhance.unitCube)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The time-free part of the cell operator `𝒫_0 = ∂_𝗍 - div_z(G∇_z) + v·∇_z` on the torus
variable `z` (with `A = div(G∇) - v·∇`, `∂_𝗍 - A = 𝒫_0`). The metric `G` is symmetric and
independent of `z`, so `div_z(G∇_zψ) = ∑ G_{ij} ∂_i ∂_j ψ`. -/

/-- `(-div(G∇ψ) + v·∇ψ)(z) = -∑_{ij} G_{ij} ∂_i ∂_j ψ(z) + ∑_k v_k(z) ∂_k ψ(z)`. -/
def cellOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Gt : Fin 2 → Fin 2 → ℝ) (vt : Vec 2 → Vec 2) (ψ : Vec 2 → E) : Vec 2 → E :=
  fun z => (∑ k : Fin 2, vt z k • fderiv ℝ ψ z (basisVec k))
    - ∑ i : Fin 2, ∑ j : Fin 2,
        Gt i j • fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec j)) z (basisVec i)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity

/-! The supremum norm `‖M‖_∞ = sup_{t ∈ I} ‖M(t)‖` of a spatially constant, time-dependent
`2 × 2` matrix (as in `ω = ‖H_cov‖_∞/ρ²`, `δ_H`, `k₀ = B⁻¹‖𝖩 - B I‖_∞` for the coarse
covariance). The matrix norm
is the supremum of the entries (equal to the operator norm up to a fixed factor 2; the finite
order constants of the statement absorb it); the value is in `[0,∞]` so that an unbounded matrix
is `⊤`, never a junk zero. -/

/-- `sup_{t ∈ [t₀,t₁]} max_{i,j} |M t i j|`, in `[0, ∞]`. -/
def matrixSupNorm (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (t₀ t₁ : ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc t₀ t₁, ⨆ i : Fin 2, ⨆ j : Fin 2, ENNReal.ofReal |M t i j|

/-! The mass-conjugated row and column sums of a block of nonnegative entry norms,
`max{sup_v ∑_u √(π_u/π_v) N_{vu}, sup_u ∑_v √(π_u/π_v) N_{vu}}`: for every coefficient norm one
takes positive constituent sums, then both mass-conjugated row and column sums, and denotes their
maximum by `‖·‖_{𝒳;π}`. Values in `[0,∞]`. The entry norms `N_{vu}` are those of the operator
entries (the positive constituent sum is taken over the left-coefficient arrays by the
callers). -/

/-- `max (⨆_v ∑_u √(π_u/π_v) N v u) (⨆_u ∑_v √(π_u/π_v) N v u)`. -/
def schurSums {ι : Type*} [Fintype ι] (π : ι → ℝ) (N : ι → ι → ℝ≥0∞) : ℝ≥0∞ :=
  max (⨆ v, ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * N v u)
    (⨆ u, ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * N v u)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The uniform-time slow jet norm of order `j` of a coefficient `f(t,X,z)`,
`sup_{t∈I,X,z} ‖D_X^j f(t,X,z)‖` (the slow part of `jetSup`; the means of the lift have uniform-time
slow jets through `K`). For a cell-independent coefficient the supremum in `z` is vacuous. -/

/-- `⨆_{t∈I} ⨆_X ⨆_z ‖D_X^j (f t · z)(X)‖`, in `[0,∞]`. -/
def slowJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ) (j : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → E) : ℝ≥0∞ :=
  ⨆ t ∈ I, ⨆ X : Vec 2, ⨆ z : Vec 2, ‖iteratedFDeriv ℝ j (fun X' => f t X' z) X‖ₑ

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The pointwise-fast (Wiener) jet norm of order `L` in the fast variable and `j` in the slow
variable of a coefficient `f(t,X,z)` on the torus variable `z`,
`𝔚_{L,j}(f) = ∑_{k ∈ ℤ²} (1 + |k|)^L sup_{t∈I,X} ‖D_X^j f̂_k(t,X)‖`, the norm
`∑_j (1+|j|)^b sup_{𝗍,X} ‖ĉ_j‖_op` of the coefficients (with `c_1 = 0`). For a coefficient
independent of `z_∥` only the modes `(0,k_⊥)` contribute, which is the transverse Fourier norm of
the source; the sum over `ℤ²` is the two-dimensional norm needed by the weak cell. The Fourier
coefficient `f̂_k = ∫ f e^{-2πi k·z} dz` of a real-valued field is measured by its two real parts
(cosine and sine integrals), whose norms sum; this is equivalent to the modulus (operator norm)
up to a factor 2, absorbed in the constants. `|k| = max{|k_0|,|k_1|}`. -/

/-- `∑'_{k : ℤ²} (1+|k|)^L ⨆_{t∈I, X} (‖D_X^j f̂^{cos}_k(t,X)‖ + ‖D_X^j f̂^{sin}_k(t,X)‖)`. -/
def wienerJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ) (L j : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → E) : ℝ≥0∞ :=
  ∑' k : Fin 2 → ℤ,
    ENNReal.ofReal ((1 + max |(k 0 : ℝ)| |(k 1 : ℝ)|) ^ L) *
      ⨆ t ∈ I, ⨆ X : Vec 2,
        (‖iteratedFDeriv ℝ j (fun X' => ∫ z in AVenhance.unitCube,
            Real.cos (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) • f t X' z) X‖ₑ
          + ‖iteratedFDeriv ℝ j (fun X' => ∫ z in AVenhance.unitCube,
            Real.sin (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) • f t X' z) X‖ₑ)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The sampled flux of a cleanup chain, `e ∑_{j<A_cl} ϑ^j (V_j)_diag`, `ϑ = e/ρ`; the physical
presentations `R_h`, `R_{c,h}` of the residual are multiples of it. -/

/-- `(t,x) ↦ (k ↦ e ∑_{j<A} (e/ρ)^j (V_j)_diag(t,x)_k)`; `c` is the cell-time factor `ℓ^{-2}`. -/
def cleanupFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c ρ e : ℝ) (A : ℕ)
    (V : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) : ℝ → Vec 2 → Fin 2 → E :=
  fun t x k => e • ∑ j ∈ Finset.range A, (e / ρ) ^ j • diagSample c ρ e (fun τ X z => V j τ X z k) t x

/-! The slow source of the next cleanup step, `f_j = -div_X V_{j-1}`. -/

/-- `f_j(X,z) = -∑_k ∂_{X_k} V_{j-1}(X,z)_k`. -/
def cleanupSource {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℕ → Vec 2 → Vec 2 → Fin 2 → E) (j : ℕ) : Vec 2 → Vec 2 → E :=
  fun X z => -∑ k : Fin 2, slowPartial k (fun X' z' => V (j - 1) X' z' k) X z

end AVRegularity
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! A mean operator in divergence form with operator coefficients,
`(b a)(t,X) = ∑_{d} ∑_{|α|=d-1} div_X(b_{d,α}(t,X) ∂_X^α a(X))`, `b_{d,α}(t,X) ∈ (𝗁_u → 𝗁_v)_{v,u}`
with a flux index `k ∈ {0,1}`, as in the dimensional form of the means of the lift,
`ℓ^{-2} ε_c^n L_n^{(h)} = ∑_{d=2}^n ∑_{|α|=d-1} div_x(B^{(h)}_{n,α} ∂_x^α)`. -/

/-- The type of flux coefficient arrays: order `d`, word `α` of length `d - 1`, then `(t,X)`, the
flux direction `k` and the operator matrix. -/
abbrev MeanCoeff (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] : Type _ :=
  (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ∀ v u : ι, h u →L[ℝ] h v

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The factorial norm of order `m` of a smooth periodic field,
`|w|²_{ρ,m} = ∑_{j=0}^m ρ^{2j} ‖∇^j w‖₂² / (j!)²` with the Euclidean tensor of ordered derivatives,
computed from classical derivatives on the unit cell
(the carrier `factorialNormSq` reads weak jets; for the `C^∞` fields of the residual they agree). -/

/-- `∑_{j≤m} (ρ^{2j}/(j!)²) ∑_{|w|=j} ∫⁻_{𝕋²} ‖∂^w g‖²`. -/
def classicalFactorialSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (m : ℕ)
    (g : Vec 2 → E) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
    ∑ w : DerivativeWord2 j, ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2

/-! The gradient factorial norm of order `m` of a smooth periodic field,
`|∇w|²_{ρ,m} = ∑_{j=0}^m ρ^{2j} ‖∇^{j+1} w‖₂² / (j!)²`, from classical
derivatives on the unit cell. -/

/-- `∑_{j≤m} (ρ^{2j}/(j!)²) ∑_{|w|=j+1} ∫⁻_{𝕋²} ‖∂^w g‖²`. -/
def classicalGradFactorialSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ)
    (m : ℕ) (g : Vec 2 → E) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
    ∑ w : DerivativeWord2 (j + 1), ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The factorial norm of order `m` of a jet of order `K ≥ m`,
`|w|²_{ρ,m} = ∑_{j=0}^m ρ^{2j}‖∇^j w‖₂²/(j!)²`,
computed from the first `m + 1` derivative levels of a higher-order ambient jet. For `K ≥ m` it
equals `factorialNormSq` of the truncation; the cycle statements use it only with `K ≥ m`
(never a silently shortened norm). -/

/-- `∑_{j ≤ m, j ≤ K} ρ^{2j}/(j!)² ‖∇^j w‖²` from the order-`K` ambient jet. -/
def factorialNormSqUpTo {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (m : ℕ) (D : JetL2 μ K E) : ℝ :=
  ∑ j : Fin (K + 1), if j.val ≤ m then factorialWeight ρ j.val * derivativeNormSq D j else 0

/-! The gradient factorial seminorm of order `m` from a jet of order
`K ≥ m + 1`, `|∇w|²_{ρ,m} = ∑_{j=0}^m ρ^{2j}‖∇^{j+1} w‖₂²/(j!)²` (the factorial norm applied to
`∇w`; compare `gradFactorialNormSq`, which reads a jet of order exactly `m + 1`). -/

/-- `∑_{1 ≤ j ≤ m+1, j ≤ K} ρ^{2(j-1)}/((j-1)!)² ‖∇^j w‖²` from the order-`K` ambient jet. -/
def gradFactorialNormSqUpTo {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (m : ℕ) (D : JetL2 μ K E) : ℝ :=
  ∑ j : Fin (K + 1),
    if 1 ≤ j.val ∧ j.val ≤ m + 1 then factorialWeight ρ (j.val - 1) * derivativeNormSq D j else 0

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! `V = 𝒜_z f` for `𝒜_z = ∇_z Δ_z^{-1}` acting on the fast variable of a centered field. The
multiplier of `𝒜_z` is `-ij/(2π|j|²)` on nonzero modes; it is bounded on cell `L²`, centered and
commutes with slow derivatives. `𝒜_z` is characterized, so it is a relation:
`V(X,·)` is the gradient `∇_z φ(X,·)` of a smooth periodic mean-zero potential
`φ(X,·)` with `Δ_z φ = div_z V = f(X,·)`; `V` is smooth in `(X,z)` (slow derivatives commute with
`𝒜_z`). For a smooth periodic mean-zero `f` the field `V` exists and is unique (mean-zero Poisson
problem). Fixed time. -/

/-- `V = ∇_z Δ_z^{-1} f` fibrewise: `V = ∇_zφ`, `P_0 φ = 0`, `div_z V = f`. -/
def IsCellAntidivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (sX sZ : ℕ)
    (f : Vec 2 → Vec 2 → E) (V : Vec 2 → Vec 2 → Fin 2 → E) : Prop :=
  IsBoxSmooth sX sZ V ∧
  (∀ X, AVenhance.IsZ2Periodic (V X)) ∧
  ∃ φ : Vec 2 → Vec 2 → E,
    IsBoxSmooth sX (sZ + 1) φ ∧
    (∀ X, AVenhance.IsZ2Periodic (φ X)) ∧
    (∀ X, fieldCellMean (φ X) = 0) ∧
    (∀ X z k, V X z k = fderiv ℝ (φ X) z (basisVec k)) ∧
    (∀ X z, ∑ k : Fin 2, fderiv ℝ (fun z' => V X z' k) z (basisVec k) = f X z)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The weighted block norm of a coefficient array in the uniform-time cell-`L²` slow jet norm. -/

/-- `schurSums π (v u ↦ ∑_a sup_{t,X} ‖D_X^j c_a · · · v u‖_{L²_z})`. -/
def schurCellL2Jet {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ] (π : ι → ℝ) (I : Set ℝ) (j : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v) : ℝ≥0∞ :=
  schurSums π fun v u => ∑ a : κ, cellL2Jet I j (fun t X z => c a t X z v u)

/-! The factorial coefficient norm with both positive sums,
`𝒜_{E,K;π}(c) = schurSums(v u ↦ ∑_a ∑_{j≤K} E^j/j! sup_{t,x}‖D^j c_a(t,x)_{vu}‖)`, for a
cell-independent coefficient. -/

/-- `schurSums π (v u ↦ ∑_a ∑_{j ≤ K} (E^j/j!) sup_{t,x} ‖D_x^j c_a · · · v u‖)`. -/
def schurFactorialJet {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ] (π : ι → ℝ) (I : Set ℝ) (E : ℝ) (K : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v) : ℝ≥0∞ :=
  schurSums π fun v u => ∑ a : κ, ∑ j ∈ Finset.range (K + 1),
    ENNReal.ofReal (E ^ j / (j.factorial : ℝ)) * slowJet I j (fun t X z => c a t X z v u)

/-! The weighted block norm of a left-coefficient array in the uniform-time slow jet norm (the
means of the lift have uniform-time slow jets through `K`). -/

/-- `schurSums π (v u ↦ ∑_a sup_{t,X,z} ‖D_X^j c_a · · · v u‖)`. -/
def schurSlowJet {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ] (π : ι → ℝ) (I : Set ℝ) (j : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v) : ℝ≥0∞ :=
  schurSums π fun v u => ∑ a : κ, slowJet I j (fun t X z => c a t X z v u)

/-! The weighted block norm of a left-coefficient array in the Wiener (pointwise-fast) jet
norm. -/

/-- `schurSums π (v u ↦ ∑_a 𝔚_{L,j}(c_a · · · v u))`. -/
def schurWienerJet {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ] (π : ι → ℝ) (I : Set ℝ) (L j : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v) : ℝ≥0∞ :=
  schurSums π fun v u => ∑ a : κ, wienerJet I L j (fun t X z => c a t X z v u)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The norm `‖F‖_{L²(I;H_{ρ,m;π})}` of a flux field `F(t,x) ∈ ℝ² ⊗ 𝗁_π`,
`(∫_I ∑_v π_v⁻¹ ∑_k |F_{k,v}(t)|²_{ρ,m})^{1/2}` (the norm `‖F_c‖_{L²H_{ρ,k;π}}` of the coarse
flux of the residual), from classical derivatives. -/

/-- `(∫⁻_I ∑_v π_v⁻¹ ∑_k |F_{k,v}(t)|²_{ρ,m})^{1/2}`. -/
def classicalFluxL2H {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (ρ : ℝ) (π : ι → ℝ) (I : Set ℝ) (m : ℕ)
    (F : ℝ → Vec 2 → Fin 2 → ∀ i, h i) : ℝ≥0∞ :=
  (∫⁻ t in I, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
    ∑ k : Fin 2, classicalFactorialSq ρ m (fun x => F t x k v)) ^ (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The sampled remainder of a cleanup chain, `ϑ^{A_cl} (f_{A_cl})_diag`, `ϑ = e/ρ`,
`f_{A_cl} = -div_X V_{A_cl-1}`; the scalar presentations `q_h`, `q_{c,h}` of the residual are
multiples of it. -/

/-- `(t,x) ↦ (e/ρ)^A (f_A)_diag(t,x)` with `f_A = cleanupSource V A`. -/
def cleanupRemainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c ρ e : ℝ) (A : ℕ)
    (V : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) : ℝ → Vec 2 → E :=
  fun t x => (e / ρ) ^ A • diagSample c ρ e (fun τ X z => cleanupSource (fun j => V j τ) A X z) t x

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The action of a divergence-form mean operator of tested orders
`2 ≤ d ≤ n` on a coarse field. The divergence is taken by
`fderiv` of the flux, in whichever variable `(t,X)` or `(t,x)` the coefficients and the field use. -/

/-- `(b a)(t,X)_v = ∑_{d=2}^n ∑_α ∑_k ∂_{X_k}(∑_u b_{d,α}(t,X)_{k,vu} (∂^α a(t,·))(X)_u)`. -/
def meanApply {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (n : ℕ) (b : MeanCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) :
    ℝ → Vec 2 → ∀ i, h i :=
  fun t X v => ∑ d ∈ Finset.Icc 2 n, ∑ α : DerivativeWord2 (d - 1), ∑ k : Fin 2,
    fderiv ℝ (fun X' (v' : ι) => ∑ u : ι, b d α t X' k v' u (orderedDerivative α (a t) X' u))
      X (basisVec k) v

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! Independent slow/fast coefficient jets, for recording actual quiet entrance traces.
No physical residual bound is part of this definition. -/

/-- Uniform-time cell L² norm of an ordered slow word followed by an independent fast word. -/
def mixedCellL2Jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set ℝ) (p q : ℕ) (f : ℝ → Vec 2 → Vec 2 → E) : ℝ≥0∞ :=
  ⨆ t ∈ I, ⨆ X : Vec 2, ⨆ α : DerivativeWord2 p, ⨆ β : DerivativeWord2 q,
    eLpNorm (fun z => orderedDerivative α
      (fun X' => orderedDerivative β (f t X') z) X) 2 (volume.restrict AVenhance.unitCube)

/-- Both positive mass-conjugated Schur sums of all coefficient constituents. -/
def schurMixedCellL2Jet {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {κ : Type*} [Fintype κ] (π : ι → ℝ) (I : Set ℝ) (p q : ℕ)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v) : ℝ≥0∞ :=
  schurSums π fun v u => ∑ a : κ, mixedCellL2Jet I p q (fun t X z => c a t X z v u)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The strong component energy of order `m` of a smooth periodic physical field `a(t,x)` on the
window `I`, `𝓔^B_{ρ,m;π}(a) = (∑_v π_v⁻¹ (sup_I |a_v|²_{ρ,m} + B ∫_I |∇a_v|²_{ρ,m}))^{1/2}`
with each component's time supremum before its mass sum (the `[0,∞]`-valued classical
counterpart of `strongEnergy`). -/

/-- `(∑_v π_v⁻¹ (⨆_{t∈I} |a_v(t)|²_{ρ,m} + B ∫⁻_I |∇a_v|²_{ρ,m}))^{1/2}`. -/
def classicalStrongEnergy {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (ρ B : ℝ) (π : ι → ℝ) (I : Set ℝ) (m : ℕ)
    (a : ℝ → Vec 2 → ∀ i, h i) : ℝ≥0∞ :=
  (∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
    ((⨆ t ∈ I, classicalFactorialSq ρ m (fun x => a t x v))
      + ENNReal.ofReal B * ∫⁻ t in I, classicalGradFactorialSq ρ m (fun x => a t x v))) ^ (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! `D` is the maximal edge order: `D = max d_{vu}`, and `D = 2` at `H = 0`. `ConstituentEdges D`
already bounds
the orders by `D`; tightness says that `D = 2` or some edge has order exactly `D`. -/

/-- `D = 2`, or some edge list of order exactly `D` is nonempty. -/
def IsTightOrder {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (edge : ConstituentEdges D h) : Prop :=
  D = 2 ∨ ∃ v u, ∃ d : Finset.Icc 2 D, d.1 = D ∧ edge v u d ≠ []

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The truncated lift `C^{[N]} = ∑_{n=0}^N ε^n C_n` at grade `hh`,
applied to a coarse field. -/

/-- `(C^{[N],(hh)} a)(t,X,z) = ∑_{n=0}^N ε^n (C_n^{(hh)} a)(t,X,z)`. -/
def liftPolyField {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ) (ε : ℝ) (hh : ℕ)
    (a : ℝ → Vec 2 → ∀ i, h i) : ℝ → Vec 2 → Vec 2 → ∀ i, h i :=
  fun t X z => ∑ n ∈ Finset.range (N + 1), ε ^ n • liftApply n (Cc hh n) a t X z

/-! The flux part `F_a` of the divided tail of the lift,
`(F_a)_k = ∑_{n=N+1}^{2N+D} ε^{n-N-1} (F_n)_k a`, applied to a coarse field. -/

/-- `((F_a a)(t,X,z))_k = ∑_{n=N+1}^{2N+D} ε^{n-N-1} ((F_n)_k a)(t,X,z)`. -/
def tailFluxField {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (F : ℕ → Fin 2 → LiftCoeff ι h) (N D : ℕ) (ε : ℝ)
    (a : ℝ → Vec 2 → ∀ i, h i) : ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i :=
  fun t X z k => ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
    ε ^ (n - N - 1) • liftApply (2 * N + D) (F n k) a t X z

/-! The scalar part `f_a` of the divided tail of the lift,
`f_a = ∑_{n=N+1}^{2N+D} ε^{n-N-1} f_n a`, applied to a coarse
field. The arrays `f n` are the centered presentation arrays of `IsLiftTailPresentation`. -/

/-- `(f_a a)(t,X,z) = ∑_{n=N+1}^{2N+D} ε^{n-N-1} (f_n a)(t,X,z)`. -/
def tailScalarField {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (f : ℕ → LiftCoeff ι h) (N D : ℕ) (ε : ℝ)
    (a : ℝ → Vec 2 → ∀ i, h i) : ℝ → Vec 2 → Vec 2 → ∀ i, h i :=
  fun t X z => ∑ n ∈ Finset.Icc (N + 1) (2 * N + D),
    ε ^ (n - N - 1) • liftApply (2 * N + D) (f n) a t X z

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The cleanup recursion of the residual: for a centered tail `f₀ + div_z F₀`,
`V_0 = F₀ + 𝒜_z f₀`, `f_j = -div_X V_{j-1}`, `V_j = 𝒜_z f_j` for `1 ≤ j ≤ A_cl` (the last
source `f_{A_cl}` is not inverted; the sequence `V_j` is listed for `j < A_cl`). A relation:
`V` is a cleanup chain of length `A`. -/

/-- `V 0 = F₀ + 𝒜_z f₀` and `V j = 𝒜_z (cleanupSource V j)` for `1 ≤ j < A`. -/
def IsCleanupChain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (sX sZ A : ℕ)
    (f₀ : Vec 2 → Vec 2 → E) (F₀ : Vec 2 → Vec 2 → Fin 2 → E)
    (V : ℕ → Vec 2 → Vec 2 → Fin 2 → E) : Prop :=
  (∃ W₀ : Vec 2 → Vec 2 → Fin 2 → E, IsCellAntidivergence sX sZ f₀ W₀ ∧
    V 0 = fun X z k => F₀ X z k + W₀ X z k) ∧
  ∀ j, 1 ≤ j → j < A → IsCellAntidivergence sX sZ (cleanupSource V j) (V j)

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! The times `S` are quiet for the cell drift `w` and the source edges: `w = 0` on `S`, and all
independent source coefficients, with their actual histories, are fast independent on `S`. -/

/-- `w(t,z) = 0` for all `t ∈ S`, `z`, and every edge coefficient is fast independent on `S` (at the abstract-coefficient tier phase independence is fast independence, so there is no separate predicate). -/
def IsQuietOn {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (edge : ConstituentEdges D h) (w : ℝ → Vec 2 → Vec 2)
    (S : Set ℝ) : Prop :=
  (∀ t ∈ S, ∀ z, w t z = 0) ∧ ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsFastIndependentOn S (γ.coeff α)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The independent source envelope of the lift: a positive edge
matrix `A`, here in the conjugated form `b_{vu} = √(π_u/π_v) A_{vu}`, majorizes every reserved
`(β,γ)` constituent jet by `C_{β,γ} A_{vu} λ_s^{|β|}`, with both weighted sums at most `Θ_ind` and no
smallness. It is the analytic envelope
`IsAnalyticEnvelope` with the slow scale `λ_s = ρ/E` of the lift variable `X = x/ρ` and constants
depending on the jet order, as in `jetSup`. The constants `C_{β,γ}` are fixed before the data. -/

/-- `b ≥ 0` with row and column sums `≤ Θ`, and for all `r ≤ Ks`, `q ≤ Ls`:
`√(π_u/π_v) ∑_d ∑_γ ‖C_γ‖ ∑_α sup‖D_X^r D_z^q a_{γ,α}‖ ≤ C_{r,q} λ^r b_{vu}`. -/
structure IsScaledJetEnvelope {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) {D : ℕ}
    (edge : ConstituentEdges D h) (I : Set ℝ) (lam : ℝ) (Cj : ℕ → ℕ → ℝ) (Ks Ls : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) : Prop where
  nonneg : ∀ v u, 0 ≤ b v u
  row_sum : ∀ v, ∑ u, b v u ≤ Θ
  col_sum : ∀ u, ∑ v, b v u ≤ Θ
  jets : ∀ v u, ∀ r, r ≤ Ks → ∀ q, q ≤ Ls →
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ =>
        ENNReal.ofReal ‖γ.map‖ * ∑ α, jetSup I r q (γ.coeff α)).sum
      ≤ ENNReal.ofReal (Cj r q * lam ^ r * b v u)

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! The source coefficients of an edge family are transverse on every enlarged pulse, with the
orientation of that pulse. The enlarged pulses `pulse p` (time sets) and their orientations
`e_∥ = orient p` are data of the construction, supplied by the consumer. -/

/-- Every constituent coefficient `γ.coeff α` of every edge is `IsTransverseOn (orient p) (pulse p)`
for every pulse index `p`. -/
def IsTransverseOnPulses {κ : Type*} {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (edge : ConstituentEdges D h) (pulse : κ → Set ℝ)
    (orient : κ → Fin 2) : Prop :=
  ∀ p v u d, ∀ γ ∈ edge v u d, ∀ α, IsTransverseOn (orient p) (pulse p) (γ.coeff α)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The source of one transition of the time partition, and the quiet entrance traces of a lift.

Remark: the source is that of a single transition, `ψ(t) [(𝒯 - I)a]^(hh)` for one lift and a
free time weight `ψ`, rather than a partition sum over a common window. The consumer applies it to
each rising and falling piece of each `ϖ_k'` and sums with bounded overlap. The sampling is that of
`pulsePhysicalLift` (`diagSample` with cell time `t/ℓ²`), so a charted lift is this field for
the chart pull-back of the coarse field, read at the chart label. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- `ψ(t) [(𝒯 - I) a]^(hh)(t,x) = ψ(t) ∑_{n=1}^N ε_c^n (C_n^(hh) a_ρ)_diag(t,x)`.
The identity is removed by starting at `n = 1`. No history or mean is reset. Spatial
derivatives do not act on the time weight. -/
def transitionSourceField (N hh : ℕ) (ℓ ρ e εc : ℝ) (ψ : ℝ → ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  ψ t • diagSample (ℓ ^ 2)⁻¹ ρ e (fun s X z => ∑ n ∈ Finset.Icc 1 N,
    εc ^ n • liftApply n (Cc hh n) (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) s X z) t x

/-- Actual quiet entrance traces of the positive-degree lift coefficients at the cell time `s`:
the mixed jets (slow order `p ≤ K` after fast order `q ≤ L`) of every grade-`b` coefficient are
at most `I b · lam^p`.

These are coefficient trace bounds, not residual conclusions. They record arbitrary memory
and earlier forcing present at entrance. The normalization is by `lam^p` only, not by the lift
grading `lam^(n-m+p)`. This is weaker but sufficient, because the price
uses only `ε_c^n ≤ ε_c` and positive field jets; the grading is not recovered from `I b`. -/
def HasQuietEntranceTrace (π : ι → ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h) (s lam : ℝ)
    (N H K L : ℕ) (I : ℕ → ℝ) : Prop :=
  (∀ b, b ≤ H → 0 ≤ I b) ∧
  ∀ b, b ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n →
    ∀ p, p ≤ K → ∀ q, q ≤ L →
      schurMixedCellL2Jet π {s} p q (Cc b n m) ≤ ENNReal.ofReal (I b * lam ^ p)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The coefficient `H_j` of `ε^j` in the source flux of an
`ε`-dependent field, `∑_α a_α D_ε^α ∑_j ε^j C_j = ∑_j ε^j H_j`. `Φ ε` is the field
`C^{[N]}(ε) a = ∑_n ε^n C_n a`, a polynomial in `ε`; `H_j` is the `j`-th Taylor coefficient at
`ε = 0` of the flux. -/

/-- `(H_j)_k(X,z) = (1/j!) (d/dε)^j|_{ε=0} flux_k[Φ ε](X,z)`. -/
def sourceFluxCoeff {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (edge : ConstituentEdges D h) (η : ℝ) (j : ℕ) (t : ℝ)
    (Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) : Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z => ((j.factorial : ℝ)⁻¹) •
    iteratedDeriv j (fun ε : ℝ => sourceFlux edge η ε t (Φ ε) k X z) 0

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The premises of the finite lift on one pulse, for the system of display (9.13) of the paper:

* scales `ℓ = e/√ν`, `η = ν/B ≤ 1`, `d_* = ℓ√B`, `ε_c = d_*/ρ ≤ 1`, `λ_s = ρ/E ≤ 1`;
* one enlarged pulse: the drift is the transverse shear `v = V(𝗍,z_⊥) e_∥` with zero mean,
  every source coefficient is independent of `z_∥` (`IsTransverseOn`); histories, phases and slow
  labels are fixed; the lift starts at `t₀` (window `[t₀,t₁]`; the data before `t₀` is zero);
* a finite Hilbert family with masses `π_v > 0` and an acyclic graph of path depth `H`, the
  maximal order `D` (an upper bound on the edge orders; tightness is not required),
  the reserves `q_s = K + 4(H+1)(N+D)²`,
  `q_f = max{k, L+2} + HD + 2N + 2D`;
* `3I/4 ≤ G ≤ 5I/4`, `‖∂_X^β G‖_∞ ≤ C_β λ_s^{|β|}` through `q_s`, the fast jets of `w = √η v`
  through `q_f` bounded independently of `η`, the source envelope `IsScaledJetEnvelope`; time dependence is measurable.

Regularity: `G` is `C^{q_s}` in `X`, the shear profile `V` is `C^{q_f}`, the independent source
coefficients are box smooth `IsBoxSmooth q_s q_f` (slow order `q_s`, fast jets to `q_f`: exactly the reserved jets, as in `jetSup`);
the coarse test fields stay `C^∞`. The relations below require of the lifts the box orders `(s_X, s_Z)`.
The orders and the constants `C_β`, `C_q`, `C_{β,γ}` are fixed before the data. -/

/-- The premises of the finite lift on one pulse, for the system of display (9.13) of the
paper. -/
structure IsLiftSetting {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    (Q : LiftOperatorData ι h D) (π : ι → ℝ) (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ)
    (par : Fin 2) (V : ℝ → ℝ → ℝ) (H N K k L qs qf : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (b : ι → ι → ℝ) (Θ : ℝ) : Prop where
  window : t₀ ≤ t₁
  e_pos : 0 < e
  ν_pos : 0 < ν
  B_pos : 0 < B
  ρ_pos : 0 < ρ
  E_pos : 0 < E
  ℓ_eq : ℓ = e / Real.sqrt ν
  η_eq : Q.η = ν / B
  η_le : Q.η ≤ 1
  dstar_eq : dstar = ℓ * Real.sqrt B
  εc_eq : εc = dstar / ρ
  εc_le : εc ≤ 1
  lam_eq : lam = ρ / E
  lam_le : lam ≤ 1
  N_ge : 1 ≤ N
  D_ge : 2 ≤ D
  qs_eq : qs = K + 4 * (H + 1) * (N + D) ^ 2
  qf_eq : qf = max k (L + 2) + H * D + 2 * N + 2 * D
  mass_pos : ∀ v, 0 < π v
  G_symm : ∀ t X i j, Q.G t X i j = Q.G t X j i
  G_meas : ∀ X i j, Measurable fun t => Q.G t X i j
  G_smooth : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, ContDiff ℝ (qs : ℕ∞) fun X => Q.G t X i j
  G_ellip : ∀ t ∈ Set.Icc t₀ t₁, ∀ X, ∀ ξ : Vec 2,
    (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ∧
      ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2
  G_jets : ∀ r, r ≤ qs →
    (⨆ t ∈ Set.Icc t₀ t₁, ⨆ X : Vec 2, ‖iteratedFDeriv ℝ r (fun X' => Q.G t X') X‖ₑ)
      ≤ ENNReal.ofReal (CG r * lam ^ r)
  v_shear : ∀ t z, Q.v t z = V t (z par.rev) • basisVec par
  V_smooth : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (qf : ℕ∞) (V t)
  V_per : ∀ t ∈ Set.Icc t₀ t₁, Function.Periodic (V t) 1
  V_mean : ∀ t ∈ Set.Icc t₀ t₁, ∫ s in (0 : ℝ)..1, V t s = 0
  v_meas : ∀ z, Measurable fun t => Q.v t z
  w_jets : ∀ q, q ≤ qf →
    (⨆ t ∈ Set.Icc t₀ t₁, ⨆ z : Vec 2,
      ‖iteratedFDeriv ℝ q (fun z' => Real.sqrt Q.η • Q.v t z') z‖ₑ) ≤ ENNReal.ofReal (Cw q)
  depth : HasDepthAtMost Q.edge H
  transverse : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
    IsTransverseOn par (Set.Icc t₀ t₁) (γ.coeff α)
  coeff_meas : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z, Measurable fun t => γ.coeff α t X z
  coeff_smooth : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, ∀ t ∈ Set.Icc t₀ t₁,
    IsBoxSmooth qs qf (γ.coeff α t)
  envelope : IsScaledJetEnvelope π Q.edge (Set.Icc t₀ t₁) lam Cj qs qf b Θ

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The truncated mean operator without the time derivative,
`∑_{n=2}^{N+D} ε^n L_n^{(hh)}` applied to a coarse field. The `∂_𝗍` part is not stored: all statements use
time-independent test fields, for which `C ∂_𝗍 a = 0`, and treat `∂_𝗍` of the coefficients in
integrated form. -/

/-- `(∑_{n=2}^{N+D} ε^n L_n^{(hh)} a)(t,X)`. -/
def liftMeanPoly {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ) (ε : ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (hh : ℕ) :
    ℝ → Vec 2 → ∀ i, h i :=
  fun t X => ∑ n ∈ Finset.Icc 2 (N + D), ε ^ n • liftMean Q Cc a hh n t X

/-! The exact tail coefficient of the grade-`hh` lift,
`R_n^{(hh)} = ℬ_1 C_{n-1} + ℬ_2 C_{n-2} - ∑_{j=0}^D 𝒮_j C_{n-j} - ∑_{r+l=n, 0≤r≤N, 2≤l≤N+D} C_r L_l`
at grade `hh` (graded products, source terms from grade `hh - 1`), for `N + 1 ≤ n ≤ 2N + D`; in the
lift identity and its tail, `R_n` is the coefficient of `ε^n`. It is `A_n - ∑_{r+l=n} C_r L_l`. -/

/-- `(R_n^{(hh)} a)(t,X,z)`. -/
def liftTailCoeff {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) :
    Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z =>
    liftA Q Cc a hh n t X z
      - ∑ r ∈ Finset.range (N + 1),
          if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
            ∑ p ∈ Finset.antidiagonal hh,
              liftApply r (Cc p.1 r) (liftMean Q Cc a p.2 (n - r)) t X z
          else 0

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! `(f,F)` is a centered presentation of the exact tail coefficient
`R_n^{(hh)}` of the lift: for every smooth
time-independent coarse field `a`, `R_n^{(hh)} a = f a + div_z F a` with `P_0 f a = P_0 F a = 0`,
in positive tested orders at most `2N + D`, the scalar tail ends at `2N + 1`, with uniform-time
cell-`L²` coefficient jets through `K` bounded by `C Θ^hh`. `f` and `F` are symmetric word arrays of
smooth `ℤ²`-periodic coefficients (`LiftCoeff`; one array per flux direction). The statement is
made for each power `ε^n`; the divided tail of the source is
`∑_n ε^{n-N-1} (f_n a + div_z F_n a)`. -/

/-- `(f,F)` presents `R_n^{(hh)}` as above, with the cell-`L²` jet bound `C Θ^hh` through order `K`. -/
def IsLiftTailPresentation {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (sX sZ : ℕ)
    (π : ι → ℝ) (t₀ t₁ : ℝ) (N K : ℕ) (C Θ : ℝ) (hh n : ℕ) (f : LiftCoeff ι h)
    (F : Fin 2 → LiftCoeff ι h) : Prop :=
  (∀ m α t X z v u, (m = 0 ∨ 2 * N + D < m) → f m α t X z v u = 0) ∧
  (∀ k m α t X z v u, (m = 0 ∨ 2 * N + D < m) → F k m α t X z v u = 0) ∧
  (2 * N + 1 < n → ∀ m α t X z v u, f m α t X z v u = 0) ∧
  (∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), f m (α ∘ σ) = f m α) ∧
  (∀ k m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), F k m (α ∘ σ) = F k m α) ∧
  (∀ m α v u, ∀ t ∈ Set.Icc t₀ t₁,
    IsBoxSmooth sX sZ (fun X z => f m α t X z v u) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => f m α t X z v u)) ∧
  (∀ k m α v u, ∀ t ∈ Set.Icc t₀ t₁,
    IsBoxSmooth sX sZ (fun X z => F k m α t X z v u) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => F k m α t X z v u)) ∧
  (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
    liftTailCoeff Q Cc N (fun _ => a₀) hh n t X z
      = liftApply (2 * N + D) f (fun _ => a₀) t X z
        + ∑ k : Fin 2, fastPartial k
            (fun X' z' => liftApply (2 * N + D) (F k) (fun _ => a₀) t X' z') X z) ∧
  (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
    fieldCellMean (fun z => liftApply (2 * N + D) f (fun _ => a₀) t X z) = 0 ∧
    ∀ k, fieldCellMean (fun z => liftApply (2 * N + D) (F k) (fun _ => a₀) t X z) = 0) ∧
  (∀ j, j ≤ K → ∀ m,
    schurCellL2Jet π (Set.Icc t₀ t₁) j (f m) ≤ ENNReal.ofReal (C * Θ ^ hh) ∧
    schurCellL2Jet π (Set.Icc t₀ t₁) j
      (fun p : DerivativeWord2 m × Fin 2 => F p.2 m p.1) ≤ ENNReal.ofReal (C * Θ ^ hh))

end AVRegularity
end
end
