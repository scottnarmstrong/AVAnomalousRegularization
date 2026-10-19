-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
public import AVRegularity.Definitions.Families.MarkedLedger
public import AVRegularity.Statements.Intermediate.Families.IsAnalyticEnvelope
public import AVRegularity.Definitions.CycleWords.IsGeometryCover
public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionPlane

section
section
@[expose] public section
namespace AVRegularity

/-! The time structure of a block in cell time used by the word and seam statements: the whole
interval is H/V admissible, the orientation regions lie in the common domains of the actual and the
single-orientation extensions with past and future quiet buffers, including the first and last
graph factors, and quiet middle regions cover all remaining source times; `B_p` counts the joins
and `D_q` is the minimum buffer, including terminal extraction. The pulses are the orientation
regions (closed intervals `[lo_p, hi_p]`) with their orientation `e_∥`, `quiet` is the set of quiet
times, the marks are the starting times of the admissible marks of each orientation, `joins` is the
number `B_p` of joins and `buffer` the minimum quiet buffer `D_q`. The record carries no
hypothesis; the package structures assert how it relates to the drift. -/

/-- Orientation regions, quiet times, marks, joins and buffer of a block. -/
structure BlockRegions where
  /-- The number of orientation regions (enlarged pulses). -/
  P : ℕ
  /-- Left endpoint of the `p`th region. -/
  lo : Fin P → ℝ
  /-- Right endpoint of the `p`th region. -/
  hi : Fin P → ℝ
  /-- The orientation `e_∥` of the `p`th region. -/
  orient : Fin P → Fin 2
  /-- The quiet times. -/
  quiet : Set ℝ
  /-- The starting times of the marks of orientation `j`. -/
  marks : Fin 2 → Finset ℝ
  /-- The number `B_p` of joins. -/
  joins : ℕ
  /-- The minimum quiet buffer `D_q` (cell time). -/
  buffer : ℝ

/-! The two-variable multi-indices of order at most `n`, used by the moment norms of
`cycle_mixed_words` (`|α| ≤ n`) and of the geometry estimates. -/

/-- `{β ∈ ℕ² : β₁ + β₂ ≤ n}`. -/
def momentIndices (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun β => β.1 + β.2 ≤ n

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The Péclet-type factor `P_e = 1 + η^{-1/2}` of `cycle_mixed_words`. -/

/-- `P_e = 1 + η^{-1/2}`. -/
def peFactor (η : ℝ) : ℝ := 1 + (Real.sqrt η)⁻¹

end AVRegularity
end
end

section
@[expose] public section
namespace AVRegularity

/-! The numerical constants of a scalar package: the quantities that the proofs of the word and seam
statements may use from the scalar input, fixed before the finite orders and independent of the
particular cell problem. The package structures (`CoreScalarPackage`, `ScalarPackage`) assert
the properties of these constants for a given cell problem; this record carries no hypothesis. -/

/-- The constants of a scalar package. `ξ0` is the radius of the low disc of the graph and the
row, `ξlo` the high-frequency cutoff `ξ_*` of the word statement, `Cg` the graph constant, `Cw`
the bound on `‖w‖_∞ = √η‖v‖_∞`, `g0` the smallness of the metric deviation, `cGauss` the rate in
`Re Ξ ≤ -c S|ξ|²`, `θs` the length (in cell time) of a mark and `cadm` the density of marks,
`Cj, cj, Qj` the constant, rate and `P_e`-power of the decay and smoothing at Sobolev order
`j`, `Cneg` the constant of the weighted adjoint propagation at order `k`, weight exponent `p`,
`Qneg` its power at order `k` (independent of the weight), `Cwt` the weight comparison constants and `Cvj` the drift-jet bounds (premises of the word and seam
statements; the duration multiplier `C_H` of the seam is a parameter of that statement, not a package constant). -/
structure ScalarConstants where
  /-- Radius of the low disc. -/
  ξ0 : ℝ
  /-- The high-frequency cutoff `ξ_*`. -/
  ξlo : ℝ
  /-- Graph constant. -/
  Cg : ℝ
  /-- Bound `‖w‖_∞ ≤ Cw`. -/
  Cw : ℝ
  /-- Metric smallness `g₀`. -/
  g0 : ℝ
  /-- The Gaussian rate. -/
  cGauss : ℝ
  /-- Mark length in cell time. -/
  θs : ℝ
  /-- Mark density constant. -/
  cadm : ℝ
  /-- Constants of the decay and smoothing at Sobolev order `j`. -/
  Cj : ℕ → ℝ
  /-- Rates of the decay at Sobolev order `j`. -/
  cj : ℕ → ℝ
  /-- Powers of `P_e` at Sobolev order `j`. -/
  Qj : ℕ → ℕ
  /-- Constants of the weighted adjoint propagation at order `k`, weight `p`. -/
  Cneg : ℕ → ℕ → ℝ
  /-- Powers of the weighted adjoint propagation at order `k` (independent of the weight). -/
  Qneg : ℕ → ℕ
  /-- Weight comparison constants. -/
  Cwt : ℕ → ℝ
  /-- Bounds `‖D^j(√η v)‖ ≤ Cvj j` of the jets of the normalized drift `w = √η v`. -/
  Cvj : ℕ → ℝ

/-! The fast reserve `J_* = 2K_* + max_i d_i + 2` of `cycle_mixed_words` (for no letters
`max_i d_i = 0`: `Finset.sup` over `Fin 0` is `0`). -/

/-- `J_* = 2K_* + max_i d_i + 2`, with `max` over no letters equal to `0`. -/
def wordReserveJstar {Nw : ℕ} (Kstar : ℕ) (d : Fin Nw → ℕ) : ℕ :=
  2 * Kstar + Finset.univ.sup d + 2

/-! The slow reserve `K_* = K_f + n + ∑_i d_i + 2` of `cycle_mixed_words`. -/

/-- `K_* = K_f + n + ∑_i d_i + 2`. -/
def wordReserveKstar {Nw : ℕ} (Kf n : ℕ) (d : Fin Nw → ℕ) : ℕ := Kf + n + ∑ i, d i + 2

/-! The input moment reserve `n = m + ∑_i K_i` of `cycle_mixed_words`. -/

/-- `n = m + ∑_i K_i`. -/
def wordReserveN {Nw : ℕ} (m : ℕ) (K : Fin Nw → ℕ) : ℕ := m + ∑ i, K i

/-! The polynomial degree `p = 4N_w + 2∑_i K_i + 2m + 4` of the Gaussian amplitude in
`cycle_mixed_words` (`N_w` counts the letters). -/

/-- `p = 4N_w + 2∑_i K_i + 2m + 4`. -/
def wordReserveP {Nw : ℕ} (m : ℕ) (K : Fin Nw → ℕ) : ℕ := 4 * Nw + 2 * ∑ i, K i + 2 * m + 4

/-! A letter of a source word: a letter of order `d_i ≥ 2` is
`𝒞_i = D_ξ·∑_{1≤|α|≤d_i-1} a_{i,α}(t,X,z) D_ξ^α`, in Taylor form, and the independent coefficients
retain all histories and component maps.
The independent coefficients are the constituents of the edge family `edge` (kept unmerged), in the
normalized slow variable `X = x/E` and the fast variable `z` (cell-normalized, so no
scale enters). `order` is `d_i`, `slow` is the Taylor order `K_i`, `theta` is `θ_i` and `majorant`
the conjugated positive matrix `√(π_u/π_v)(b_i)_{vu}` of the source. `positive` marks a
positive-degree metric Taylor letter (its Taylor expansion starts at degree one, so each
monomial carries a factor `η_g`). The record carries no hypothesis; see `IsCycleLetter`. -/

/-- A letter: order `d_i`, slow order `K_i`, positive-degree flag, edge family, `θ_i`, majorant. -/
structure CycleLetter (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (D : ℕ) where
  /-- The order `d_i`. -/
  order : ℕ
  /-- The slow Taylor order `K_i`. -/
  slow : ℕ
  /-- Positive-degree (metric Taylor) letter. -/
  positive : Bool
  /-- The independent coefficients. -/
  edge : ConstituentEdges D h
  /-- The bound `θ_i` of the two sums. -/
  theta : ℝ
  /-- The conjugated positive matrix `√(π_u/π_v)(b_i)_{vu}`. -/
  majorant : ι → ι → ℝ

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The cell-time end of the part of the window `[ta, ta+T]` that lies
in the renewal block `I_{m,l}` (see `ocPieceStart`). -/

/-- `min(ta+T, (l+½)h)/ℓ²`. -/
def ocPieceEnd (α q : ℝ) (Λ m : ℕ) (ν ta T : ℝ) (l : ℤ) : ℝ :=
  min (ta + T) (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2

/-! The cell-time start of the part of the window `[ta, ta+T]` that
lies in the renewal block `I_{m,l} = [(l-½)h, (l+½)h]` (`h = τ''_m`), in
cell time `𝗍 = t/ℓ²`. -/

/-- `max(ta, (l-½)h)/ℓ²`. -/
def ocPieceStart (α q : ℝ) (Λ m : ℕ) (ν ta : ℝ) (l : ℤ) : ℝ :=
  max ta (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity

/-! The change of label at a renewal in cell variables
(`θ̃_{l+1} = θ̃_l∘Υ_l`, `Υ_l = X_{m-1}(lh,·,(l+1)h)`): the cell point
`z'` of chart `l+1` (centre `y'`) is the cell point `z = (Υ_l(y' + e z') - y)/e` of chart `l`
(centre `y`). -/

/-- `z' ↦ (Υ_l(y' + e z') - y)/e`. -/
def ocCellTransition (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (l : ℤ) (y y' : Vec 2) (z' : Vec 2) : Vec 2 :=
  (ocEpsilon q Λ m)⁻¹ • (ocTransition α q Λ m φ hφ l (l + 1) (y' + ocEpsilon q Λ m • z') - y)

end AVRegularity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity

/-! The amplitude `Θ_w = ∏_i θ_i` of a word,
where a positive-degree metric Taylor letter
contributes `Cgη_g` in place of its `θ_i` (the `η_g` is explicit here, `C` is the constant of
the estimate). `ηg = R/E`. -/

/-- `Θ_w = ∏_i θ_i · (η_g if the letter is of positive degree else 1)`. -/
def wordTheta {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D Nw : ℕ} (ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) : ℝ :=
  ∏ i, ((letters i).theta * (if (letters i).positive then ηg else 1))

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The cell-frame view of one piece of a charted family.
A charted family lives in output time `t` and in the physical fast variable `y/e`; the cell
chains of the geometry estimates live in cell time `𝗍 = t/ℓ²` and in the cell point
`z = (y - y_c)/e` around the centre `y_c` of the chart (`ocCellCentre`). So the fast variable of the coefficient at
the cell point `z` is `y/e = z + y_c/e` and its output time is `t = ℓ² 𝗍`. `timeFastShift s φ`
re-indexes a one-chart edge family in this way (`coeff α τ X z := coeff α (s τ) X (z + φ)`;
`s = ℓ²`, `φ = y_c/e`), and `cellFiber F s φ p c` is the re-indexed chart-frame view of the piece
`p` in the context `c`. The slow label `X` is not changed: it stays the absolute normalized label
`Y/E` (the slow evaluation, centred at `y_c/E`, is a parameter of the chain data). -/

/-- The edge family seen in cell time `τ ↦ s τ` and with the fast variable shifted by `φ`. -/
def ConstituentEdges.timeFastShift {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (s : ℝ) (φ : Vec 2) (edge : ConstituentEdges D h) :
    ConstituentEdges D h :=
  fun v u d => (edge v u d).map fun γ =>
    { map := γ.map
      coeff := fun α τ X z => γ.coeff α (s * τ) X (z + φ)
      periodic := fun α τ X n z => by
        simpa [add_right_comm] using γ.periodic α (s * τ) X n (z + φ)
      record := γ.record
      birthExcess_ge := γ.birthExcess_ge }

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The cell-frame (cell time, shifted fast variable) view of the piece `p` in the context `c`. -/
def cellFiber (F : ChartedFamily ι h D P Ctx) (s : ℝ) (φ : Vec 2) (p : P) (c : Ctx p) :
    ConstituentEdges D h :=
  (F.fiber p c).timeFastShift s φ

end ChartedFamily

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The source seen by the cell chain of the chart whose cell
centre is the label `y`. It is
the cell-frame view (`ChartedFamily.cellFiber`) of the piece `p` in the context `c`, with cell time
`𝗍 = t/ℓ²` (`s = ℓ²`, `ℓ = e/√ν`) and the fast phase `φ = y/e` of the centre, so that the fast
variable of the cell point `z` is `y/e + z = (y + e z)/e`. -/

/-- The chart-frame source of the piece `p` in the context `c` in the cell variables of the cell
centred at `y`. -/
def ocCellFiber {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (q : ℝ) (Λ m : ℕ) (ν : ℝ) (y : Vec 2) (p : P) (c : Ctx p) :
    ConstituentEdges D h :=
  F.cellFiber (ocEll q Λ m ν ^ 2) ((ocEpsilon q Λ m)⁻¹ • y) p c

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! The premises on a letter of `cycle_mixed_words`:
order `2 ≤ d_i` (edges of higher order empty, the common
bound `D` of the edge type is at least `d_i`), the sum of independent coefficient jets through slow
order `K_i` and fast order `J_*`, normalized by `(E/ρ)^{|a|}` (that is, the jets in the normalized
slow variable `X = x/E`), is bounded entrywise by a positive matrix `b_i`, and both sums of
`√(π_u/π_v)(b_i)_{vu}` are at most `θ_i` (`IsAnalyticEnvelope` with constant `1`), and the edges
of an inherited letter (`positive = false`) follow a finite acyclic graph of depth `H`.
Component preservation of metric letters is not a premise.

The envelope is uniform over a declared domain
`dom ⊆ ℝ × Vec 2` of pairs `(t, X)` (cell time and normalized slow variable: the patch and Taylor
segments the word uses) instead of a time set with all `X`. The letter is a one-chart object, so
its envelope is that of the one-piece family `ChartedFamily.ofFiber L.edge`, at slow scale `E = 1`
(the coefficients are already in the normalized variable). -/

/-- The premises on a letter, for masses `π`, the domain `dom`, the fast reserve `Jstar` and
the depth `H`. -/
structure IsCycleLetter {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (π : ι → ℝ) (L : CycleLetter ι h D) (dom : Set (ℝ × Vec 2))
    (Jstar H : ℕ) : Prop where
  order_ge : 2 ≤ L.order
  order_le : L.order ≤ D
  edge_order : ∀ v u (o : Finset.Icc 2 D), L.order < o.1 → L.edge v u o = []
  theta_nonneg : 0 ≤ L.theta
  nonneg : ∀ v u, 0 ≤ L.majorant v u
  row_sum : ∀ v, ∑ u, L.majorant v u ≤ L.theta
  col_sum : ∀ u, ∑ v, L.majorant v u ≤ L.theta
  analytic : IsAnalyticEnvelope (ChartedFamily.ofFiber L.edge) π (fun _ _ => dom) 1 1 L.slow Jstar
    L.majorant
  depth : L.positive = false → HasDepthAtMost L.edge H

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The cosine part of the Bloch fibre of a plane function
(in the cell variable `z = (y-y₀)/e`):
`f̂(ξ,z) = (e√η/2π) ∑_{n∈ℤ²} exp(-iθ·(z+n)) f(z+n) = (e√η/2π)(blochCos θ f z - i blochSin θ f z)`,
`θ = √η ξ`. The real and imaginary parts are kept apart so that the real Hilbert components need no
complexification. The lattice sum is a `tsum`; it converges for a.e. `z` under the moment premise of
the statement that uses it, and is used only inside integrals over `z`. -/

/-- `∑_{n∈ℤ²} cos(θ·(z+n)) • g(z+n)`. -/
def blochCos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (θ : Vec 2) (g : Vec 2 → E)
    (z : Vec 2) : E :=
  ∑' k : Fin 2 → ℤ, Real.cos (vecDot θ (z + fun i => (k i : ℝ))) • g (z + fun i => (k i : ℝ))

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The weighted gradient factorial norm of the geometry estimates
(`|∇V|_{W_n,ρ,k}`, the same norm of the gradient:
`∑_{r≤k} ρ^{2r} ∫ W_n |∇^{r+1} V|²/(r!)²`), computed from the order-`K'+1` lift of the energy
solution. Cell variable as in `weightedFactorialNormSq`. -/

/-- `∑_{j≤K} (r^{2j}/(j!)²) ∫ (1 + ϖ²|z - zc|²)^n ‖∇^{j+1} U(z)‖² dz`. -/
def weightedGradFactorialNormSq {K' : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (n : ℕ)
    (ϖ : ℝ) (zc : Vec 2) (r : ℝ) (K : ℕ) (U : PlaneHk Set.univ K' E) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (K + 1),
    ENNReal.ofReal (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
        ∑ w : DerivativeWord2 (j + 1), ‖planeJetOrder U (j + 1) w z‖ ^ 2)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The left-hand side of the Gaussian clause of `cycle_mixed_words`:
`∑_{|β|≤m} ‖δ_ξ^β a[f](ξ)‖_π/β!`, for the
retained amplitude pair `(A, B)` (`Ã = A - iB`) in the cell frequency `θ = √ηξ`, `δ_ξ = ϖ∂_θ`, with the
inverse-mass component norm `|x|²_π = ∑_v π_v⁻¹‖x_v‖²` of the complex amplitude (`‖A‖² + ‖B‖²`). -/

/-- `∑_{β₁+β₂≤m} (ϖ^{β₁+β₂}/β!) (∑_x π_x⁻¹(‖∂_θ^β A_x(θ)‖² + ‖∂_θ^β B_x(θ)‖²))^{1/2}`. -/
def amplitudeJetNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (m : ℕ) (ϖ : ℝ) (A B : ∀ x, Vec 2 → h x)
    (θ : Vec 2) : ℝ≥0∞ :=
  ∑ β ∈ momentIndices m,
    ENNReal.ofReal (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
      (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal (‖thetaPartial β.1 β.2 (A x) θ‖ ^ 2) +
          ENNReal.ofReal (‖thetaPartial β.1 β.2 (B x) θ‖ ^ 2))) ^ (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The datum norm `𝔇_n(F)` of the geometry estimates:

`𝔇_n(F)² = ∑_v π_v⁻¹ |F_v|²_{W_n,ρ_*,K_v}`. -/

/-- `𝔇_n(F) = (∑_v π_v⁻¹ |F_v|²_{W_n,ρ_*,K_v})^{1/2}` in `[0,∞]`. -/
def geometryDataNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (π : ι → ℝ) (Kslot : ι → ℕ) (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (r : ℝ) (F : ∀ v, PlaneHk Set.univ (Kslot v) (h v)) : ℝ≥0∞ :=
  (∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ zc r (Kslot v) (F v)) ^
    (1 / 2 : ℝ)

/-! The forcing norm `ν^{-1/2}‖F_flux‖_{L²H_{ρ_*,k;n}}` of the
geometry estimates, with the inverse-mass component
sum (suffix `;π`) at the slots `K_v`: `(∫_I ∑_v π_v⁻¹ |F_v(t)|²_{W_n,ρ_*,K_v} dt)^{1/2}`
(`ν = 1` in cell variables). -/

/-- `(∫_I ∑_v π_v⁻¹ |F_v(t)|²_{W_n,ρ_*,K_v} dt)^{1/2}` for a flux forcing, in `[0,∞]`. -/
def geometryFluxNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (π : ι → ℝ) (Kslot : ι → ℕ) (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (r : ℝ) (t₀ t₁ : ℝ)
    (F : ∀ v, ℝ → PlaneHk Set.univ (Kslot v) (PiLp 2 (fun _ : Fin 2 => h v))) : ℝ≥0∞ :=
  (∫⁻ t in Set.Icc t₀ t₁, ∑ v, ENNReal.ofReal ((π v)⁻¹) *
    weightedFactorialNormSq n ϖ zc r (Kslot v) (F v t)) ^ (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The coefficient operator of an order-`d` edge list acting on the
word array of an input, with a chosen evaluation of the independent slow variable
(Taylor evaluation, or sampled evaluation on the diagonal). The cell-normalized coefficients of
the edge are used, so in cell variables (`ν = 1`) the flux coefficient is exactly `a^♭`
(`e^{d-2}ν` cancels the cell scaling; compare `physicalCoefficient`). The evaluation `ev`
turns the slow function `X ↦ a^♭_{γ,α,k}(t,X,z)` (fast variable `z` fixed) into a number at the
cell point `z`; it is `fun f z => f (δ • z)` (sampled) or the Taylor polynomial (`taylorSlow`). -/

/-- `g ↦ (k ↦ ∑_γ ∑_α ev(X ↦ γ.coeff α t X z k)(z) • C_γ (g α))` for an edge list of order `d`. -/
def slowEvalCoefficient {Hu Hv : Type*} [NormedAddCommGroup Hu] [NormedSpace ℝ Hu]
    [NormedAddCommGroup Hv] [NormedSpace ℝ Hv] {d : ℕ} (ev : (Vec 2 → ℝ) → Vec 2 → ℝ)
    (edge : List (Constituent d Hu Hv)) (t : ℝ) (z : Vec 2) :
    (PiLp 2 (fun _ : DerivativeWord2 (d - 1) => Hu)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => Hv)) :=
  (edge.map fun γ =>
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => Hv)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k : Fin 2 =>
        ∑ α : DerivativeWord2 (d - 1), (ev (fun X => γ.coeff α t X z k) z) •
          γ.map.comp (PiLp.proj 2 (fun _ : DerivativeWord2 (d - 1) => Hu) α))).sum

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The right-hand fibre norm of the Gaussian clause of `cycle_mixed_words`:
`‖δ_ξ^α(χ_lo f̂)(ξ)‖_{L²_z(𝗁_π)}`, up to the common prefactor `e√η/2π` of the Bloch transform, which
is a numerical constant on both sides. The lattice sums are `tsum`s: where they are not summable
(and where `g` is not smooth enough for the iterated derivative) the value is the junk `0`. Under the
moment premise of the statement that uses it (`cycle_mixed_words`, conjunct 4: `L²` moments of order
`n + 2`) the sums converge for a.e. `z` and the norm, an integral over `z`, does not see the
representative of the datum. With `θ = √ηξ` and `χ(θ) = χ_lo(θ/√η)`, it is the unit-cell
`L²_z(𝗁_π)` norm of the pair `∂_θ^α[χ blochCos θ f]`, `∂_θ^α[χ blochSin θ f]` (the modulus of the
complex number `χ(blochCos - i blochSin)`), `∑_v π_v⁻¹‖·‖²`. The common factor `ϖ^{|α|}` of
`δ_ξ^α = (ϖ∂_θ)^α` is applied by the statement. In `[0,∞]`. -/

/-- `(∫_{𝕋²} ∑_v π_v⁻¹(‖∂_θ^α[χ·blochCos θ g_v](z)‖² + ‖∂_θ^α[χ·blochSin θ g_v](z)‖²) dz)^{1/2}`. -/
def blochFibreDerivNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (χ : Vec 2 → ℝ) (α : ℕ × ℕ)
    (g : ∀ x, Vec 2 → h x) (θ : Vec 2) : ℝ≥0∞ :=
  (∫⁻ z in AVenhance.unitCube, ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    (ENNReal.ofReal (‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochCos θ' (g x) z) θ‖ ^ 2) +
      ENNReal.ofReal (‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochSin θ' (g x) z) θ‖ ^ 2))) ^
    (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The energy norm `𝔈_n(V)` of the geometry estimates:

`𝔈_n(V)² = ∑_v π_v⁻¹ [sup_I |V_v|²_{W_n,ρ_*,K_v} + ν ∫_I |∇V_v|²_{W_n,ρ_*,K_v} dt]`;
each component's time supremum precedes the mass sum. In cell variables `ν = 1` and the cell time
(the factors `ν ℓ²/e² = 1` and `e²` of the volume cancel). `V` is the trajectory and `Vw` its
order-`K_v+1` lift, on `I = [t₀,t₁]`. -/

/-- `𝔈_n(V) = (∑_v π_v⁻¹ [⨆_{t∈I} |V_v(t)|² + ∫_I |∇V_v|²])^{1/2}` in `[0,∞]`. -/
def geometryEnergyNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (π : ι → ℝ) (Kslot : ι → ℕ) (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (r : ℝ) (t₀ t₁ : ℝ) (V : ∀ v, ℝ → PlaneHk Set.univ (Kslot v) (h v))
    (Vw : ∀ v, ℝ → PlaneHk Set.univ (Kslot v + 1) (h v)) : ℝ≥0∞ :=
  (∑ v, ENNReal.ofReal ((π v)⁻¹) *
    ((⨆ t ∈ Set.Icc t₀ t₁, weightedFactorialNormSq n ϖ zc r (Kslot v) (V v t)) +
      ∫⁻ t in Set.Icc t₀ t₁, weightedGradFactorialNormSq n ϖ zc r (Kslot v) (Vw v t))) ^
    (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! The data of a chain of forced plane equations over a Hilbert
family (time-ordered words are chains of forced solutions). Level `j` of the chain
solves, in cell variables (`ν = 1`, cell time),
`∂ₜ u_j + v·∇u_j - div(G∇u_j) - 𝒮_self u_j = div(P ∇u_{j-1}) + 𝒮_{j-1} u_{j-1} (+ div F_j)`,
where `𝒮_self` is the flux operator of `selfEdge` and `𝒮_{j-1}` that of `subEdge (j-1)`, each with
its slow evaluation, `P = subMetric`. Words:
`selfEdge = ∅`, `subEdge = ` the Taylor letters, `subMetric = 0`. The weighted comparison:
`G = G₀`, `selfEdge` = source with its
slow Taylor polynomial, `subEdge = ∅`, `subMetric = P_K`; the actual equation is the chain of length
one with `selfEdge` evaluated on the diagonal. -/

/-- Principal metric `G(t,z)`, self-level source edges with their evaluation, sub-diagonal letters
(for each of the `N` links) with their evaluation, and the sub-diagonal metric flux. -/
structure PlaneChainData (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (D N : ℕ) where
  /-- The principal metric `G(t,z)` of every level. -/
  G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ
  /-- The source edges acting within a level. -/
  selfEdge : ConstituentEdges D h
  /-- The slow evaluation of the self-level coefficients. -/
  selfEval : (Vec 2 → ℝ) → Vec 2 → ℝ
  /-- The letters between level `j` and level `j + 1`. -/
  subEdge : Fin N → ConstituentEdges D h
  /-- The slow evaluation of each letter's coefficients. -/
  subEval : Fin N → (Vec 2 → ℝ) → Vec 2 → ℝ
  /-- The matrix `P(t,z)` of the sub-diagonal metric flux `div(P ∇u_{j-1})`. -/
  subMetric : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The chain data of the actual equation of the geometry estimates
(`U` solves `(L - 𝒮)U = 0` with the same full datum,
`L = L_G`, `(𝒮u)_v = div ∑ a_{vu,d}(t,X,X/e)∇^{d-1}u_u`): one level, the metric `G(t,z)` of the chart,
and the independent source evaluated on the diagonal `X = X₀ + δ z` (`δ = e/E`; fast variable `z`; `X₀ = y/E` the normalized label of the
cell centre `y`, the cell point `z = 0`). The slow label is absolute. -/

/-- Actual metric `G(t,z)`, source on the diagonal `X = X0 + δ z`, no letters. -/
def geometryActualData {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (edge : ConstituentEdges D h) (X0 : Vec 2) (δ : ℝ) : PlaneChainData ι h D 0 where
  G := G
  selfEdge := edge
  selfEval := fun f z => f (X0 + δ • z)
  subEdge := fun i => i.elim0
  subEval := fun i => i.elim0
  subMetric := fun _ _ => 0

/-! The chain data of a scalar equation without source,
`∂ₜ V + v·∇V - div(G∇V) = div F_flux`, componentwise on a family (the
actual scalar equation and every frozen scalar equation): one level, metric `G`, no edges. -/

/-- Metric `G(t,z)`, no source edges, no letters. -/
def geometryScalarData {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (D : ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    PlaneChainData ι h D 0 where
  G := G
  selfEdge := fun _ _ _ => []
  selfEval := fun _ _ => 0
  subEdge := fun i => i.elim0
  subEval := fun i => i.elim0
  subMetric := fun _ _ => 0

end AVRegularity
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity

/-! The chain data of the homogeneous scalar equation
`∂ₜ u + v·∇u - div(G∇u) = 0` on the plane in cell variables (one level, one scalar component, no
source). It is used to state propagation estimates of the actual and of the adjoint (time-reversed)
scalar equation in the scalar package (weighted order-zero
propagation and the reversed adjoint for negative spaces). -/

/-- Scalar component `ℝ`, maximal order `2`, one level, metric `G`, no source edges. -/
def homogeneousChainData (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    PlaneChainData Unit (fun _ : Unit => ℝ) 2 0 where
  G := G
  selfEdge := fun _ _ _ => []
  selfEval := fun _ _ => 0
  subEdge := fun i => i.elim0
  subEval := fun i => i.elim0
  subMetric := fun _ _ => 0

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The fast part of the adjoint of the fibre evolution (the fibre decomposition transposed,
for the same estimate for the reversed adjoint). The adjoint (transpose under the bilinear
pairing) of `𝒢_ξ = D_ξ·(G D_ξ ·) - v·D_ξ` is `D_{-ξ}·(G D_{-ξ} ·) + v·D_{-ξ}`; a
backward solution `ψ` on `[s,t]` is read as the forward solution `Ψ(τ) = ψ(-τ)` of the transposed
coefficients `(G(-τ), -v(-τ), -ξ)` on `[-t,-s]`. Since `U_ξ(t,s) = ℛ(t)e^{Ξ}ℒ(s) + ℱ`, the transpose
is `ψ(s) = ℓ(s) e^{Ξ(t,s)} ∫ (ℛ(t)ψ(t)) + ℱ^T ψ(t)`. -/

/-- `x ↦ Ψ(-s)(x) - ℓ(ξ)(s)(x) exp(∫_s^t λ(ξ)) ∫_{𝕋²} (1 + r(ξ)(t)) Ψ(-t)`. -/
def fibreAdjointFastPart (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (ell : ℕ × ℕ → ℝ → Vec 2 → ℂ) (ξ : Fin 2 → ℂ) (Ψ : ℝ → RawJet2 1 ℂ) (s t : ℝ) :
    Vec 2 → ℂ :=
  fun x => cellValue Ψ (-s) x
    - fibreSeriesFun ell ξ s x * Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)
      * ∫ y in AVenhance.unitCube, (1 + cellValue (fibreSeriesJet r ξ) t y) * cellValue Ψ (-t) y

/-! The fast part `ℱ_ξ(t,s)h(s)` of a fibre solution,
`h(t) - ℛ(t) e^{Ξ(t,s)} ℒ(s)h(s)`,
for the graph `ℛ = 1 + r`, the symbol `λ` and the row `ℒ(s)f = ∫ ℓ(s) f` given by Taylor
coefficient families, as in `cycle_fibre_graph`. -/

/-- `x ↦ h(t,x) - (1 + r(ξ)(t,x)) exp(∫_s^t λ(ξ)) ∫_{𝕋²} ℓ(ξ)(s) h(s)`, with `h = cellValue D`. -/
def fibreFastPart (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (ell : ℕ × ℕ → ℝ → Vec 2 → ℂ) (ξ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ) (s t : ℝ) :
    Vec 2 → ℂ :=
  fun x => cellValue D t x
    - (1 + cellValue (fibreSeriesJet r ξ) t x) * Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)
      * ∫ y in AVenhance.unitCube, fibreSeriesFun ell ξ s y * cellValue D s y

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity

/-! The chain data of the finite Taylor responses of
the geometry estimates:
`(L₀ - 𝒮_K)Z₀ = 0`, `Z₀(s) = F`, `(L₀ - 𝒮_K)Z_j = D_P Z_{j-1}`, `Z_j(s) = 0` for `j ≥ 1`, with
`L₀` the equation with the metric `G₀(t) = G(t,zc)` frozen at the chart center, `𝒮_K` the slow Taylor
polynomial through degree `K` at `X₀ + δ·zc` (`X₀ = y/E` the normalized label of the cell centre `y`) of the independent source (`edge`, evaluated at
`(X, z)` with `X - X₀ = δ(z - zc)`, `δ = e/E`), and `D_P = div(P_K∇·)`,
`P_K = G^{[K]} - G₀` (`metricTaylor 1 K`). The chain has levels `0..J`. -/

/-- Frozen metric, Taylor source, no letters, sub-diagonal flux `P_K`. -/
def geometryResponseData {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (J K : ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (zc : Vec 2) (edge : ConstituentEdges D h) (X0 : Vec 2) (δ : ℝ) : PlaneChainData ι h D J where
  G := fun t _ => G t zc
  selfEdge := edge
  selfEval := fun f z => taylorSlow 0 K f (X0 + δ • zc) (δ • (z - zc))
  subEdge := fun _ _ _ _ => []
  subEval := fun _ _ _ => 0
  subMetric := fun t z => metricTaylor 1 K G t zc z

/-! The chain data of a source word: the frozen cell metric `G(t)` (independent of `z`), no
self-level source, and between consecutive levels the Taylor letter `𝒞_i^T`,
`𝒞_i^T u = div ∑_{α, lo_i ≤ |γ| ≤ K_i} (∂_X^γ a_{i,α}(t,X₀,z)/γ!) (δ z)^γ ∇^α u`, `δ = e/E`
(since `X - X₀ = (y-y₀)/E = (e/E) z`; this is the source's `(E/ρ)^{|γ|}∂_X^γ a/γ! (iη_gδ_ξ)^γ` with
the slow variable normalized by `E`). `lo_i = 1` for a positive-degree letter and `0` otherwise. -/

/-- The chain data of the word of `letters`, Taylor center `X₀`, `δ = e/E`. -/
def wordChainData {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D Nw : ℕ} (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ) : PlaneChainData ι h D Nw where
  G := fun t _ => G t
  selfEdge := fun _ _ _ => []
  selfEval := fun _ _ => 0
  subEdge := fun i => (letters i).edge
  subEval := fun i f z =>
    taylorSlow (if (letters i).positive then 1 else 0) (letters i).slow f X₀ (δ • z)
  subMetric := fun _ _ => 0

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity

/-! The coupling array `A` of the coupled-energy statement
 that encodes a chain of forced equations as one coupled system on the
index set `Fin (N+1) × ι` (level, component). Entry `(i, i', d)`:
* same level (`i.1 = i'.1`): the metric deviation `G(t,z) - I` on the diagonal component at order
  `d = 2` (so `div(G∇u) = Δu + div((G - I)∇u)`), plus the self-level edge of order `d`;
* consecutive levels (`i.1 = i'.1 + 1`): the sub-diagonal metric flux `P` at `d = 2` on the diagonal
  component, plus the letter `subEdge i'.1` of order `d` (target `i.2`, source `i'.2`);
* otherwise zero.
Orders outside `admissibleOrders` carry zero coefficients; the statements that use this
array assume the slots `κ` make every nonempty edge list admissible. -/

/-- The coupling array of a chain with slots `κ j x` at level `j`, component `x`. -/
def planeChainCoefficient {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D N : ℕ} (cd : PlaneChainData ι h D N)
    (κ : Fin (N + 1) → ι → ℕ) :
    ∀ (i i' : Fin (N + 1) × ι) (d : admissibleOrders (fun p => κ p.1 p.2) D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i'.2)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i.2)) :=
  fun i i' d t z =>
    (if i.1 = i'.1 then
        (if hv : i.2 = i'.2 ∧ d.1 = 2 then
            metricFlux (cd.G t z - 1) (d.1 - 1) hv.1 (by omega) else 0) +
          slowEvalCoefficient cd.selfEval
            (cd.selfEdge i.2 i'.2 ⟨d.1, (Finset.mem_filter.1 d.2).1⟩) t z
      else 0) +
    (if hs : i.1.val = i'.1.val + 1 then
        (if hv : i.2 = i'.2 ∧ d.1 = 2 then
            metricFlux (cd.subMetric t z) (d.1 - 1) hv.1 (by omega) else 0) +
          slowEvalCoefficient (cd.subEval ⟨i'.1.val, by omega⟩)
            (cd.subEdge ⟨i'.1.val, by omega⟩ i.2 i'.2 ⟨d.1, (Finset.mem_filter.1 d.2).1⟩) t z
      else 0)

end AVRegularity
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! A chain of forced second-order energy solutions on the plane
(the chronological word, whose
Duhamel form `u_N(S)` for `u₀ = 𝒰f`, `(∂ₜ - 𝒢)u_j = 𝒞_j u_{j-1}`, `u_j(0) = 0` is the word;
genuine second-order responses in graph
order). It is the solution class `IsCoupledWeakSolutionPlane` of the coupled energy estimate for the
index set `Fin (N+1) × ι`, `ν = 1` (cell units), drift `v`, couplings `planeChainCoefficient`, the
datum `f` at level `0` and zero datum at the other levels, the flux forcing `F` and no scalar
forcing. -/

/-- `(u, w)` is the chain of solutions on `[t₀, t₁]` from the level-`0` datum `f`, with slots
`κ j x`, level-`j` flux forcing `F j`. -/
def IsPlaneChain {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D N : ℕ} (cd : PlaneChainData ι h D N) (κ : Fin (N + 1) → ι → ℕ) (t₀ t₁ : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (F : ∀ (j : Fin (N + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)) : Prop :=
  IsCoupledWeakSolutionPlane (ι := Fin (N + 1) × ι) (h := fun p => h p.2) 1 t₀ t₁ v D
    (fun p => κ p.1 p.2) (planeChainCoefficient cd κ)
    (fun p => match p with
      | (j, x) => if hj : j = 0 then (by subst hj; exact f x) else 0)
    (fun p => F p.1 p.2) (fun _ => fun _ => 0)
    (fun p => u p.1 p.2) (fun p => w p.1 p.2)

end AVRegularity
end
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! A chain of forced second-order energy solutions on the plane with
an initial datum at every level (the continuation of a chain after a change of label, which
retains its full traces under exact label changes). It is
`IsCoupledWeakSolutionPlane` for the index set `Fin (N+1) × ι` with the couplings
`planeChainCoefficient`; `IsPlaneChain` is the case of datum `f` at level `0` and zero above. -/

/-- `(u, w)` is the chain of solutions on `[t₀, t₁]` from the initial values `f j x` at level `j`. -/
def IsPlaneChainFrom {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D N : ℕ} (cd : PlaneChainData ι h D N) (κ : Fin (N + 1) → ι → ℕ) (t₀ t₁ : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (f : ∀ (j : Fin (N + 1)) (x : ι), PlaneHk Set.univ (κ j x) (h x))
    (F : ∀ (j : Fin (N + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)) : Prop :=
  IsCoupledWeakSolutionPlane (ι := Fin (N + 1) × ι) (h := fun p => h p.2) 1 t₀ t₁ v D
    (fun p => κ p.1 p.2) (planeChainCoefficient cd κ) (fun p => f p.1 p.2)
    (fun p => F p.1 p.2) (fun _ => fun _ => 0) (fun p => u p.1 p.2) (fun p => w p.1 p.2)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity

/-! The output norm `D^{ρ_*}_{m,K}` of `cycle_mixed_words`: it also sums the
`L²_{ξ,z}(𝗁_π)` norms of `δ_ξ^α[(ρ_*/e)^a D_ξ^a f̂]/(α! a!)` for `a ≤ K`; in physical variables
it is `∑_{α≤m, a≤K} ‖((y-y₀)/R)^α (ρ_*∇)^a f‖/(α! a!)`. Cell variable `z = (y-y₀)/e`,
`(y-y₀)/R = s z` with `s = e/R` and `ρ_*∇_y = r ∇_z` with `r = ρ_*/e`. The derivatives are given as
a family of raw jets `J v a w` (order `a`, ordered word `w`), so that the same norm measures a
weak jet of a carrier element and a classical derivative of a smooth function. -/

/-- `∑_{β₁+β₂≤m} ∑_{a≤K} (β₁!β₂!a!)⁻¹ (∑_v π_v⁻¹ ‖(s z₀)^{β₁}(s z₁)^{β₂} r^a |J_v^{(a)}|‖₂²)^{1/2}`,
where `|J_v^{(a)}|` is the Euclidean norm of the array of order-`a` jets, in `[0,∞]`. -/
def jetOutputNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    (π : ι → ℝ) (m K : ℕ) (s r : ℝ)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) : ℝ≥0∞ :=
  ∑ β ∈ momentIndices m, ∑ a ∈ Finset.range (K + 1),
    ENNReal.ofReal ((((β.1.factorial * β.2.factorial * a.factorial : ℕ)) : ℝ)⁻¹) *
      (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2 * r ^ a) *
          Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity

/-! The input moment norm `‖f‖_{D_n}` of `cycle_mixed_words` (equivalent to
finitely many physical moments about the patch center `y₀`, at radius `R`):
`‖f‖_{D_n} = ∑_{|α| ≤ n} ‖((y-y₀)/R)^α f‖_{L²(𝗁_π)}/α!`, `|x|²_π = ∑_v π_v⁻¹‖x_v‖²`.
It is written in the cell variable `z = (y-y₀)/e`, so `(y-y₀)/R = s z` with `s = e/R`. -/

/-- `‖f‖_{D_n} = ∑_{β₁+β₂≤n} (β₁!β₂!)⁻¹ (∑_v π_v⁻¹ ‖(s z₀)^{β₁}(s z₂)^{β₂} f_v‖₂²)^{1/2}` in `[0,∞]`
for a family of component functions on the plane (`z = (z 0, z 1)`; the value `∞` records
unbounded moments, there is no junk value). -/
def momentNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (n : ℕ) (s : ℝ) (f : ∀ v, Vec 2 → h v) : ℝ≥0∞ :=
  ∑ β ∈ momentIndices n,
    ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
      (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • f v z) 2 volume ^ 2) ^
          (1 / 2 : ℝ)

end AVRegularity
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The graph, row and fibre-propagator input of the scalar package
for one drift (the low graph and normalized row jets;
centered forward and adjoint decay and finite-order smoothing). For the frozen metric `G(t)` and
drift `v` (cell variables, cell time) on the window `[t₀, t₀+S]`, at real frequencies `|ξ| < ξ₀`:
a fibre graph `ℛ = 1 + r`, symbol `λ`, row `ℒ = ∫ ℓ ·` with `ℒℛ = 1`, `‖ℒ - P₀‖ ≤ Cg|ξ|`
(the clauses of `cycle_fibre_graph`), their `H^j` jets
(`‖r‖_{H^j}, ‖ℓ - 1‖_{H^j} ≤ C_j P_e^{Q_j}|ξ|` for the chosen representatives), the forward decay
of the fast part `‖ℱ(t,s)h‖_{H^j} ≤ C_j P_e^{Q_j} e^{-c_j(t-s)}‖h‖_{H^j}`, the smoothing from `L²`
(`C_j P_e^{Q_j}(1 + (t-s)^{-j/2}) e^{-c_j(t-s)}`), and the same two estimates for the transposed
evolution (centered adjoint decay and smoothing). The fast parts are bounded through their (unique, continuous)
`C^j` representative, since the raw jets of a solution are only defined up to null sets. The same structure serves the actual drift and
the single-orientation extensions. The data `r, lam, ell` are the Taylor coefficient families. -/

/-- Graph `r`, symbol `lam`, row `ell` with their bounds on the window `[t₀, t₀+S]`.

Decay entrances and all decay/smoothing outputs are periodic representatives.
`fast_decay`, `fast_smoothing`, `adjoint_decay`, `adjoint_smoothing` range over `IsCellSolution` (`L²` data). -/
structure FibreScalarData (K : ScalarConstants) (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (t₀ S : ℝ) where
  /-- Taylor coefficients of the graph `r(ξ) = ∑ ξ^α r_α`. -/
  r : ℕ × ℕ → ℝ → RawJet2 1 ℂ
  /-- Taylor coefficients of the symbol `λ(ξ) = ∑ ξ^α λ_α`. -/
  lam : ℕ × ℕ → ℝ → ℂ
  /-- Taylor coefficients of the row `ℓ(ξ) = ∑ ξ^α ℓ_α`. -/
  ell : ℕ × ℕ → ℝ → Vec 2 → ℂ
  graph : IsFibreGraph η G v K.ξ0 K.Cg r lam
  row_summable : ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < K.ξ0 →
    ∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * ⨆ s, cellL2Norm (ell p s) < ⊤
  row_mean : ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < K.ξ0 → ∀ s : ℝ,
    Integrable (fun x => fibreSeriesFun ell ξ s x * (1 + cellValue (fibreSeriesJet r ξ) s x))
        (volume.restrict AVenhance.unitCube) ∧
      (∫ x in AVenhance.unitCube,
        fibreSeriesFun ell ξ s x * (1 + cellValue (fibreSeriesJet r ξ) s x)) = 1 ∧
      cellL2Norm (fun x => fibreSeriesFun ell ξ s x - 1) ≤ ENNReal.ofReal (K.Cg * fibreNorm ξ)
  row_taylor : ∀ (n : ℕ) (ξ : Fin 2 → ℂ) (s : ℝ),
    cellL2Norm (fibreHomogeneous ell ξ n s) ≤
      ENNReal.ofReal (K.Cg * (2 / K.ξ0) ^ n * fibreNorm ξ ^ n)
  real_ratio : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 → ∀ s t : ℝ, s ≤ t →
    ENNReal.ofReal ‖Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)‖ *
        cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) t x) ≤
      cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) s x) ∧
    cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) s x) ≤
      ENNReal.ofReal K.Cg * cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) t x)
  graph_jets : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 → ∀ t : ℝ,
    ContDiff ℝ j (cellValue (fibreSeriesJet r ξ) t) ∧
      cellSobolevNorm j (cellValue (fibreSeriesJet r ξ) t) ≤
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ)
  row_jets : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 → ∀ t : ℝ,
    ContDiff ℝ j (fun x => fibreSeriesFun ell ξ t x - 1) ∧
      cellSobolevNorm j (fun x => fibreSeriesFun ell ξ t x - 1) ≤
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ)
  fast_decay : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s ≤ t → t ≤ t₀ + S → ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      ∀ g₀ : Vec 2 → ℂ, ContDiff ℝ j g₀ → AVenhance.IsZ2Periodic g₀ → cellValue D s =ᵐ[volume.restrict AVenhance.unitCube] g₀ →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
        fibreFastPart r lam ell ξ D s t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * Real.exp (-(K.cj j) * (t - s))) *
            cellSobolevNorm j g₀
  fast_smoothing : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s < t → t ≤ t₀ + S → ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
        fibreFastPart r lam ell ξ D s t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j *
              (1 + (t - s) ^ (-(j : ℝ) / 2)) * Real.exp (-(K.cj j) * (t - s))) *
            cellL2Norm (cellValue D s)
  adjoint_decay : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s ≤ t → t ≤ t₀ + S → ∀ Ψ : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc (-t) (-s))
        (fibreCoefficients η (fun τ => G (-τ)) (fun τ z => -(v (-τ) z)) (fun k => -(ξ k))
          (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) Ψ →
      ∀ g₀ : Vec 2 → ℂ, ContDiff ℝ j g₀ → AVenhance.IsZ2Periodic g₀ →
        cellValue Ψ (-t) =ᵐ[volume.restrict AVenhance.unitCube] g₀ →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
        fibreAdjointFastPart r lam ell ξ Ψ s t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * Real.exp (-(K.cj j) * (t - s))) *
            cellSobolevNorm j g₀
  adjoint_smoothing : ∀ (j : ℕ) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s < t → t ≤ t₀ + S → ∀ Ψ : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc (-t) (-s))
        (fibreCoefficients η (fun τ => G (-τ)) (fun τ z => -(v (-τ) z)) (fun k => -(ξ k))
          (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) Ψ →
      ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
        fibreAdjointFastPart r lam ell ξ Ψ s t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
        cellSobolevNorm j g₁ ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j *
              (1 + (t - s) ^ (-(j : ℝ) / 2)) * Real.exp (-(K.cj j) * (t - s))) *
            cellL2Norm (cellValue Ψ (-t))

/-! The part of the scalar input package that holds on every piece of a block, complete or partial,
for one cell problem (contrast `η`, frozen metric `G(t)`, drift `v`, window `[t₀, t₀+S]` in cell
time) and the weight scale `ϖ = e/R`:

* the low graph and normalized row jets, and centered forward and adjoint decay and finite-order
  smoothing for the actual drift (`actual`);
* `L²` contraction of the real fibre evolution,
  and the exact quiet identities (`quiet_mean`, `quiet_gap`: on quiet times the drift vanishes, the
  scalar mean evolves by the explicit symbol with its original history and the nonconstant
  harmonics have the fixed gap);
* the full-band Sobolev smoothing of the forward and reversed fibre propagators with a polynomial
  cost in the length, `P_e^{Q_j}(1+(t-s))^{Q_j}(1+(t-s)^{-j/2})` (`high_smoothing`: the
  differentiated bounds cost fixed polynomials in the length, by the energy argument
  `Y_j' + cY_{j+1} ≤ C_jP_eY_j`), which uses the drift jets `K.Cvj` (a premise of the
  statements);
* the pulse-local transverse source structure: for each orientation region a single-orientation
  extension of the drift (a transverse shear, zero mean, bounded) with its own graph, row and
  propagator estimates (`ext`, `ext_local`), agreeing with the actual drift on the region and its
  quiet buffers (`ext_agree`), and the buffered replacement estimates between the actual and the
  local graph, symbol and row, which gain `e^{-c D_q}`;
* the chart, weight and duration bounds (`weights`) and the
  weighted propagation of the transposed scalar equation in negative-weight positive Sobolev norms,
  which is the dual form of the negative-order propagation on short pieces.
  

The two sums of the source (`b_i`), the letters and the histories are not part of the package: they
are premises of the word and seam statements. -/

/-- The package on every piece.

`contraction`, `high_smoothing`, `quiet_mean`, `quiet_gap` range over `IsCellSolution`
(`L²` data). -/
structure CoreScalarPackage (K : ScalarConstants) (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (t₀ S ϖ : ℝ)
    (reg : BlockRegions) where
  consts_pos : 0 < K.ξ0 ∧ 0 < K.ξlo ∧ 2 * K.ξlo < K.ξ0 ∧ 0 < K.Cg ∧ 0 < K.cGauss ∧
    0 < K.θs ∧ 0 < K.cadm ∧ (∀ j, 0 < K.Cj j ∧ 0 < K.cj j) ∧ (∀ m, 0 < K.Cwt m) ∧
    (2 + K.Cw * K.Cg) * (2 * K.ξlo) ^ 2 ≤ Real.pi ^ 2 / 16
  /-- Graph, row, decay and smoothing for the actual drift. -/
  actual : FibreScalarData K η G v t₀ S
  contraction : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → ∀ s t : ℝ, t₀ ≤ s → s ≤ t →
    t ≤ t₀ + S → ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      cellL2Norm (cellValue D t) ≤ cellL2Norm (cellValue D s)
  high_smoothing : ∀ (j : ℕ) (ξ : Fin 2 → ℂ),
    (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η) →
    ∀ s t : ℝ, t₀ ≤ s → s < t → t ≤ t₀ + S →
      (∀ D : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Set.Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) D →
        ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧
          cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
          cellSobolevNorm j g₁ ≤
            ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * (1 + (t - s)) ^ K.Qj j *
              (1 + (t - s) ^ (-(j : ℝ) / 2))) * cellL2Norm (cellValue D s)) ∧
      (∀ Ψ : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Set.Icc (-t) (-s))
          (fibreCoefficients η (fun τ => G (-τ)) (fun τ z => -(v (-τ) z)) (fun k => -(ξ k))
            (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) Ψ →
        ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧
          cellValue Ψ (-s) =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
          cellSobolevNorm j g₁ ≤
            ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * (1 + (t - s)) ^ K.Qj j *
              (1 + (t - s) ^ (-(j : ℝ) / 2))) * cellL2Norm (cellValue Ψ (-t)))
  quiet_zero : ∀ t ∈ reg.quiet ∩ Set.Icc t₀ (t₀ + S), ∀ z, v t z = 0
  quiet_mean : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → ∀ a b : ℝ, a ≤ b →
    Set.Icc a b ⊆ reg.quiet → Set.Icc a b ⊆ Set.Icc t₀ (t₀ + S) → ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc a b) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      cellMean (cellValue D b) =
        Complex.exp (-(η : ℂ) * ∫ τ in a..b, fibreQuad (G τ) ξ) * cellMean (cellValue D a)
  quiet_gap : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η) →
    ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ reg.quiet → Set.Icc a b ⊆ Set.Icc t₀ (t₀ + S) →
      ∀ D : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Set.Icc a b) (fibreCoefficients η G v ξ (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) D →
        cellL2Norm (cellQ0 (cellValue D b)) ≤
          ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2) * (b - a))) *
            cellL2Norm (cellQ0 (cellValue D a))
  cover : ∀ t ∈ Set.Icc t₀ (t₀ + S), t ∈ reg.quiet ∨ ∃ p, t ∈ Set.Icc (reg.lo p) (reg.hi p)
  buffer_nonneg : 0 ≤ reg.buffer
  buffer_le : reg.buffer ≤ S
  joins_ge : 2 * reg.P ≤ reg.joins
  buffer_inside : ∀ p, Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer) ⊆
    Set.Icc t₀ (t₀ + S)
  buffer_quiet : ∀ p, Set.Ico (reg.lo p - reg.buffer) (reg.lo p) ⊆ reg.quiet ∧
    Set.Ioc (reg.hi p) (reg.hi p + reg.buffer) ⊆ reg.quiet
  /-- The single-orientation extension of the drift on the `p`th region. -/
  ext : Fin reg.P → ℝ → Vec 2 → Vec 2
  ext_local : ∀ p, FibreScalarData K η G (ext p) t₀ S
  ext_shear : ∀ p, ∃ V : ℝ → ℝ → ℝ,
    ∀ t z, ext p t z = V t (z (reg.orient p).rev) • basisVec (reg.orient p)
  ext_drift : ∀ p, IsCellDrift (ext p) ∧ (∀ t (k : Fin 2), cellMean (fun x => (ext p t x k : ℂ)) = 0) ∧
    ∀ t x, Real.sqrt η * Real.sqrt (∑ i, ext p t x i ^ 2) ≤ K.Cw
  ext_agree : ∀ p, ∀ t ∈ Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer), ∀ z,
    ext p t z = v t z
  replace_graph : ∀ (j : ℕ) (p : Fin reg.P) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) →
    fibreNorm ξ < K.ξ0 → ∀ t ∈ Set.Icc (reg.lo p) (reg.hi p + reg.buffer),
      cellSobolevNorm j (fun x => cellValue (fibreSeriesJet actual.r ξ) t x -
          cellValue (fibreSeriesJet (ext_local p).r ξ) t x) ≤
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ *
          Real.exp (-(K.cj j) * reg.buffer))
  replace_row : ∀ (j : ℕ) (p : Fin reg.P) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) →
    fibreNorm ξ < K.ξ0 → ∀ s ∈ Set.Icc (reg.lo p - reg.buffer) (reg.hi p),
      cellSobolevNorm j (fun x => fibreSeriesFun actual.ell ξ s x -
          fibreSeriesFun (ext_local p).ell ξ s x) ≤
        ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ *
          Real.exp (-(K.cj j) * reg.buffer))
  replace_symbol : ∀ (p : Fin reg.P) (ξ : Fin 2 → ℂ), (∀ i, (ξ i).im = 0) →
    fibreNorm ξ < K.ξ0 → ∀ t ∈ Set.Icc (reg.lo p) (reg.hi p + reg.buffer),
      ‖fibreSeriesC actual.lam ξ t - fibreSeriesC (ext_local p).lam ξ t‖ ≤
        K.Cj 0 * peFactor η ^ K.Qj 0 * fibreNorm ξ ^ 2 * Real.exp (-(K.cj 0) * reg.buffer)
  /-- The chart, weight and duration bounds, for every moment reserve. -/
  weights : ∀ M : ℕ, ChartWeights (fun t _ => G t) v t₀ S ϖ 0 M K.Cwt
  neg_adjoint : ∀ (k p : ℕ) (s t : ℝ), t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
    ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
      (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
      (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
      IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
        (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
      weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
          (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
        ENNReal.ofReal (K.Cneg k p * peFactor η ^ K.Qneg k * (1 + (t - s)) ^ K.Qneg k) *
          weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (f x) a w')

end AVRegularity
end
end
