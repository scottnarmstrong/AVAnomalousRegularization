-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleWords.ScalarPackage
public import AVRegularity.CycleWords.PlaneRealDriftMultiplierCongr
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp pass: quiet `H^s` decay (statement)

On a quiet interval the drift vanishes. The metric of the fibre problems is constant in space
(`fun t _ => G t`), and the potential vanishes, so the fibre generator is diagonal in the Fourier
modes of the cell. Mode `k` decays at the rate `(2πk + θ)ᵀG(2πk + θ) ≥ ½|2πk + θ|²`, which is
`≥ π²/2` for `k ≠ 0` and a real shift with `|θ_i| ≤ π`. So the mean-free part of a cell curve
contracts in every `H^s` at the rate `π²/2`, with constant `1` (`QuietHsDecayStatement`). The
package's `quiet_gap` is the case `s = 0`. The sharp fast decay uses this across quiet
buffers. -/

/-- **Quiet `H^s` decay.**

For `s = 0` this is the package's `quiet_gap` (in `L²`). For `θ = 0` it is the heat flow, whose
mean-free modes decay at `≥ ½(2π)² ≥ π²/2`. For `a₁ = b₁` take `w = w₀`. A single Fourier mode
`k ≠ 0` decays at `exp(-∫ (2πk+θ)ᵀG(2πk+θ))`, at least `e^{-π²(b₁-a₁)/2}`. There
is no constant (the factor is `1`). -/
def QuietHsDecayStatement : Prop :=
  ∀ (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (a₁ b₁ : ℝ) (u : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ), a₁ ≤ b₁ →
    (∀ t ∈ Icc a₁ b₁, ∀ x, C.v t x = 0) → (∀ t x y, C.G t x = C.G t y) → (∀ t, C.κ t = 0) →
    (∀ i, (C.θ i).im = 0 ∧ |(C.θ i).re| ≤ Real.pi) →
    CellWeakHilbertCurve a₁ b₁ u slice
      (fun τ => cellDualDerivative C hG V hv hb τ (slice τ) 0 0) →
    ∀ (s : ℕ) (w₀ : TorusHk s ℂ), torusHkValueCLM w₀ = cellQ0CLM (u a₁) →
      ∃ w : TorusHk s ℂ, torusHkValueCLM w = cellQ0CLM (u b₁) ∧
        ‖w‖ ≤ Real.exp (-(Real.pi ^ 2 / 2) * (b₁ - a₁)) * ‖w₀‖

end AVRegularity.CycleWords.Assembly
end
end

section
/-! The ingredients of `cycle_seam`.

Notation of the statement, in cell variables: `ϖ = e/R = √(η/S)`, scale ratio `1` for `e`-jets and
`ϖ⁻¹` for `R`-jets, weight `⟨ϖz⟩^p`. Negative orders are defined by duality (`negJetNorm`).
With `g = V₋f` the old output and `𝒯_Υ g = g ∘ Υ`, the statement splits as
`Z₊𝒯_Υg - K₊𝒯_ΥΠ₋g = (Z₊ - K₊)𝒯_Υg + K₊𝒯_Υ(I - Π₋)g`, and the ingredients are:

* `SeamOldNegativeStatement`: `‖g‖_{e,-k;p} ≤ CΘ₋P_e^Q(1+S)^Q‖f‖_{2;p+ΣK_i}`, `Q` independent of the
  weight;
* `SeamOldScalarStatement`: `‖Π₋g‖_{R,-m;p} ≤ CΘ₋‖f‖_{2;p+q}` at the stipulated scales,
  `m, q` chosen after the weight;
* `SeamFutureKernelStatement`: the future retained kernel `K₊` (a linear map from the future block
  only) with `K₊ : (R,-L;p_in) → (r,M;p_out)` for every `L, M` and the fast remainder
  `‖Z₊h - K₊h‖_{ρ_*,K_out;p_out} ≤ CΘ₊P_e^Q(1+S)^Q[e^{-cS} + (1+B_p)e^{-cD_q} + e^{-ca}]‖h‖_{e,-k;p_in}`;
  
* `SeamTransportStatement`: weighted negative norms under `𝒯_Υ`, at the same weight;
  
* `SeamCutoffComplementStatement`: `‖(I-Π₋)g‖_{R,-(N+k);p} ≤ CS^{-N/2}‖g‖_{e,-k;p}`, the cutoff
  bound of Lemma 11.13(c) of the paper.

Order of the constants: the metric threshold `g₁` depends on `K` only; the
integer orders and exponents (`Q`, `m₋`, `q₋`, `p_in`) on the shape and the weights only, with
`p_in` first and `m₋, q₋` after the weight; the real constants come after the real parameters
(`C_H`, `C₀`, `χ₋`, `C_out`, `C_U`). The transport keeps the weight (the first-order bound of
the transition is global) and uses the transition at order `max L 2` and the smoothness of its
inverse. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- The negative-order weighted jet norm `‖g‖_{r,-j;p} = sup |⟨g, φ⟩_π|` over smooth compactly
supported tests with `‖φ‖_{r,j;-p} ≤ 1` (negative order by duality), with the inverse-mass
pairing `Σ_v π_v⁻¹⟨g_v, φ_v⟩`. -/
def negJetNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    (g : ∀ x, Vec 2 → h x) : ℝ≥0∞ :=
  ⨆ (φ : ∀ x, Vec 2 → h x) (_ : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (φ x) ∧ HasCompactSupport (φ x))
    (_ : weightedJetNorm π (-p) j s r (fun x _ wd z => orderedDerivative wd (φ x) z) ≤ 1),
    ENNReal.ofReal |∑ x, (π x)⁻¹ * ∫ z, inner ℝ (g x z) (φ x z)|

/-- The chain hypothesis of a seam piece (a word chain with zero source), named so that the seam
statements and their consumers share one elaborated form of the zero source. -/
def seamChain {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (letters : Fin N → CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)) : Prop :=
  IsPlaneChain (wordChainData G letters X₀ δ) κ a b v f (fun _ _ _ => 0) u w

/-- The fixed parameters of the seam: package constants, orders, reserves and the shapes of the
old and future letters (fixed before the constants of the statement). -/
structure SeamShape where
  K : ScalarConstants
  D : ℕ
  H : ℕ
  Kmax : ℕ
  pout : ℕ
  k : ℕ
  Nm : ℕ
  Np : ℕ
  dO : Fin Nm → ℕ
  KsO : Fin Nm → ℕ
  posO : Fin Nm → Bool
  dF : Fin Np → ℕ
  KsF : Fin Np → ℕ
  posF : Fin Np → Bool
  hD : 2 ≤ D
  hk : Kmax + ∑ i, dO i + 2 ≤ k

/-- The common fast reserve of the seam letters. -/
def SeamShape.Jstar (σ : SeamShape) : ℕ :=
  2 * (σ.k + σ.Kmax + σ.pout + (∑ i, σ.KsO i + ∑ i, σ.KsF i) + ∑ i, σ.dF i + 2) +
    max (Finset.univ.sup σ.dO) (Finset.univ.sup σ.dF) + 2

/-- **Old negative bound.** The old partial word, of duration at most `C_H S`, is bounded from the
weighted `L²` norm of its datum into the `e`-scale negative norm, at cost `CΘ₋P_e^Q(1+S)^Q`,
`Q` independent of the weight `p`. The datum vanishes outside some ball (qualitative: it gives
the forward chain finite polynomial energies, so that every letter flux is in `L²`); `cycle_seam`
supplies this. -/
def SeamOldNegativeStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ σ : SeamShape, σ.K = K →
  ∃ Q : ℕ, ∀ CH : ℝ, 0 < CH → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ lettersO : Fin σ.Nm → CycleLetter ι h σ.D,
    (∀ i, (lettersO i).order = σ.dO i ∧ (lettersO i).slow = σ.KsO i ∧
      (lettersO i).positive = σ.posO i) →
  ∀ η S ηg ϖ δ : ℝ, 0 < η → η ≤ 1 → 1 ≤ S → 0 < ηg → ηg ≤ 1 → ϖ = Real.sqrt (η / S) →
    δ = ϖ * ηg →
  ∀ (tO SO aO bO : ℝ) (GO : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vO : ℝ → Vec 2 → Vec 2) (gO : ℝ),
    IsCellMetric (fun t _ => GO t) → IsCellDrift vO →
    (∀ t (k : Fin 2), cellMean (fun x => (vO t x k : ℂ)) = 0) →
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (vO t)) →
    (∀ t x, Real.sqrt η * Real.sqrt (∑ i, vO t x i ^ 2) ≤ σ.K.Cw) →
    (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vO t z') z‖ ≤ σ.K.Cvj j) →
    0 ≤ gO → gO ≤ σ.K.g0 → gO ≤ g₁ → IsMetricNearIdentity (fun t _ => GO t) gO →
  ∀ (regO : BlockRegions), CoreScalarPackage σ.K η GO vO tO SO ϖ regO →
    tO ≤ aO ∧ aO ≤ bO ∧ bO ≤ tO + SO → bO - aO ≤ CH * S →
    (∀ i, IsCycleLetter π (lettersO i) (Set.Icc aO bO ×ˢ Set.univ) σ.Jstar σ.H) →
    (∀ i, IsTransverseOnPulses (lettersO i).edge
      (fun p : Fin regO.P => Set.Icc (regO.lo p) (regO.hi p)) regO.orient) →
    (∀ i, IsQuietOn (lettersO i).edge vO (regO.quiet ∩ Set.Icc tO (tO + SO))) →
    (∀ i x y o, ∀ γ ∈ (lettersO i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z) →
  ∀ (X₀O : Vec 2) (κO : Fin (σ.Nm + 1) → ι → ℕ),
    (∀ (j : Fin σ.Nm) x y (o : Finset.Icc 2 σ.D), (lettersO j).edge x y o ≠ [] →
      κO j.succ x + o.1 ≤ κO j.castSucc y + 2) →
  ∀ (f : ∀ x, PlaneHk Set.univ (κO 0 x) (h x))
    (uO : ∀ (j : Fin (σ.Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x) (h x))
    (wO : ∀ (j : Fin (σ.Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x + 1) (h x)),
    (∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0) →
    seamChain GO lettersO X₀O δ κO aO bO vO f uO wO →
    negJetNorm π p σ.k ϖ 1 (fun x => planeValue (uO (Fin.last σ.Nm) x bO)) ≤
      ENNReal.ofReal (C * wordTheta ηg lettersO * peFactor η ^ Q * (1 + S) ^ Q) *
        weightedJetNorm π ((p + ∑ i, σ.KsO i : ℕ) : ℝ) 0 ϖ 1
          (fun x a wd z => planeJetOrder (f x) a wd z)

/-- **Old scalar bound.** After the low cutoff `Π₋ = χ₋(θ/√η)`, the old output is bounded in the
`R`-scale negative norm of an order `m` from the weighted `L²` norm of the datum with an extra
weight `q`, without powers of `P_e` or `S`, at the stipulated scales
`P_e^Q(1+S)^Q e^{-cD_q} ≤ C₀` when the old word ends in a quiet buffer of length `D_q`. The orders
`m, q` and the power `Q` come after the weight `p` (each frequency jet of the gauge on a partial
window costs a factor `1 + √S|ξ|`, absorbed by the negative order). The datum vanishes outside
some ball, as in `SeamOldNegativeStatement`. The weight is at most
`2 K_max + p_out + ∑K_s^F + ∑d^F + 2`, which covers the input weight of the future kernel; then the
moment reserve of the old word fits in `J_*` (`SeamShape.oldReserve_le`; reserve interface). -/
def SeamOldScalarStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ σ : SeamShape, σ.K = K →
  ∀ p : ℕ, p ≤ 2 * σ.Kmax + σ.pout + ∑ i, σ.KsF i + ∑ i, σ.dF i + 2 → ∃ m q Q : ℕ,
  ∀ (CH C0 : ℝ) (χm : Vec 2 → ℝ), 0 < CH →
    ContDiff ℝ (⊤ : ℕ∞) χm → (∀ ξ, χm (-ξ) = χm ξ) →
    (∀ ξ, 2 * σ.K.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → χm ξ = 1) →
  ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ lettersO : Fin σ.Nm → CycleLetter ι h σ.D,
    (∀ i, (lettersO i).order = σ.dO i ∧ (lettersO i).slow = σ.KsO i ∧
      (lettersO i).positive = σ.posO i) →
  ∀ η S ηg ϖ δ : ℝ, 0 < η → η ≤ 1 → 1 ≤ S → 0 < ηg → ηg ≤ 1 → ϖ = Real.sqrt (η / S) →
    δ = ϖ * ηg →
  ∀ (tO SO aO bO : ℝ) (GO : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vO : ℝ → Vec 2 → Vec 2) (gO : ℝ),
    IsCellMetric (fun t _ => GO t) → IsCellDrift vO →
    (∀ t (k : Fin 2), cellMean (fun x => (vO t x k : ℂ)) = 0) →
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (vO t)) →
    (∀ t x, Real.sqrt η * Real.sqrt (∑ i, vO t x i ^ 2) ≤ σ.K.Cw) →
    (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vO t z') z‖ ≤ σ.K.Cvj j) →
    0 ≤ gO → gO ≤ σ.K.g0 → gO ≤ g₁ → IsMetricNearIdentity (fun t _ => GO t) gO →
  ∀ (regO : BlockRegions), CoreScalarPackage σ.K η GO vO tO SO ϖ regO →
    tO ≤ aO ∧ aO ≤ bO ∧ bO ≤ tO + SO → bO - aO ≤ CH * S →
    peFactor η ^ Q * (1 + S) ^ Q * (1 + regO.joins) * Real.exp (-c * regO.buffer) ≤ C0 →
  ∀ Dq : ℝ, 0 ≤ Dq → Set.Icc (bO - Dq) bO ⊆ regO.quiet ∩ Set.Icc tO (tO + SO) →
    peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-c * Dq) ≤ C0 →
    (∀ i, IsCycleLetter π (lettersO i) (Set.Icc aO bO ×ˢ Set.univ) σ.Jstar σ.H) →
    (∀ i, IsTransverseOnPulses (lettersO i).edge
      (fun p : Fin regO.P => Set.Icc (regO.lo p) (regO.hi p)) regO.orient) →
    (∀ i, IsQuietOn (lettersO i).edge vO (regO.quiet ∩ Set.Icc tO (tO + SO))) →
    (∀ i x y o, ∀ γ ∈ (lettersO i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z) →
  ∀ (X₀O : Vec 2) (κO : Fin (σ.Nm + 1) → ι → ℕ),
    (∀ (j : Fin σ.Nm) x y (o : Finset.Icc 2 σ.D), (lettersO j).edge x y o ≠ [] →
      κO j.succ x + o.1 ≤ κO j.castSucc y + 2) →
  ∀ (f : ∀ x, PlaneHk Set.univ (κO 0 x) (h x))
    (uO : ∀ (j : Fin (σ.Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x) (h x))
    (wO : ∀ (j : Fin (σ.Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x + 1) (h x)),
    (∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0) →
    seamChain GO lettersO X₀O δ κO aO bO vO f uO wO →
    negJetNorm π p m ϖ ϖ⁻¹
        (fun x => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
          (planeValue (uO (Fin.last σ.Nm) x bO))) ≤
      ENNReal.ofReal (C * wordTheta ηg lettersO) *
        weightedJetNorm π ((p + q : ℕ) : ℝ) 0 ϖ 1 (fun x a wd z => planeJetOrder (f x) a wd z)

/-- **Future retained kernel.** From the future complete block alone there is a linear map `K₊`
with smooth outputs on `L²` data, bounded from `(R,-L;p_in)` into `(r,M;p_out)` for every `L, M`
and every scale `r ≤ max 1 C_out · ϖ⁻¹` at cost `C_{L,M}Θ₊`, such that the future word minus
`K₊` (the fast part `E₊`) is bounded from `(e,-k;p_in)` into `(ρ_*,K_out;p_out)` by
`CΘ₊P_e^Q(1+S)^Q[e^{-cS} + (1+B_p)e^{-cD_q} + e^{-ca}]`. The input weight is at most
`p_out + ∑K_s^F + 2`: the output moment `p_out` (through `x = (x - y) + y`) and the slow Taylor
moments of the future letters (reserve interface). The fast clause assumes the
datum has `p_out + ∑K_s^F + 2` finite moments (qualitative: chains exist only from compact data
and every limit tool controls the endpoint by a weighted `L²` norm; `cycle_seam` supplies it from the
compact old datum). -/
def SeamFutureKernelStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ σ : SeamShape, σ.K = K →
  ∃ pin Q : ℕ, pin ≤ σ.pout + ∑ i, σ.KsF i + 2 ∧ ∀ Cout : ℝ, 0 < Cout →
  ∃ (C c : ℝ) (CK : ℕ → ℕ → ℝ), 0 ≤ C ∧ 0 < c ∧ (∀ L M, 0 ≤ CK L M) ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ lettersF : Fin σ.Np → CycleLetter ι h σ.D,
    (∀ i, (lettersF i).order = σ.dF i ∧ (lettersF i).slow = σ.KsF i ∧
      (lettersF i).positive = σ.posF i) →
  ∀ η S ηg rstar ϖ δ : ℝ, 0 < η → η ≤ 1 → 1 ≤ S → 0 < ηg → ηg ≤ 1 → 0 < rstar →
    rstar ≤ Cout → ϖ = Real.sqrt (η / S) → δ = ϖ * ηg →
  ∀ (tF : ℝ) (GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vF : ℝ → Vec 2 → Vec 2) (gF : ℝ),
    IsCellMetric (fun t _ => GF t) → IsCellDrift vF →
    (∀ t (k : Fin 2), cellMean (fun x => (vF t x k : ℂ)) = 0) →
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (vF t)) →
    (∀ t x, Real.sqrt η * Real.sqrt (∑ i, vF t x i ^ 2) ≤ σ.K.Cw) →
    (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vF t z') z‖ ≤ σ.K.Cvj j) →
    0 ≤ gF → gF ≤ σ.K.g0 → gF ≤ g₁ → IsMetricNearIdentity (fun t _ => GF t) gF →
  ∀ (regF : BlockRegions), ScalarPackage σ.K η GF vF tF S ϖ regF →
    (∀ i, IsCycleLetter π (lettersF i) (Set.Icc tF (tF + S) ×ˢ Set.univ) σ.Jstar σ.H) →
    (∀ i, IsTransverseOnPulses (lettersF i).edge
      (fun p : Fin regF.P => Set.Icc (regF.lo p) (regF.hi p)) regF.orient) →
    (∀ i, IsQuietOn (lettersF i).edge vF (regF.quiet ∩ Set.Icc tF (tF + S))) →
    (∀ i x y o, ∀ γ ∈ (lettersF i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z) →
  ∀ a : ℝ, 0 ≤ a → a ≤ S → Set.Icc tF (tF + a) ⊆ regF.quiet →
  ∀ X₀F : Vec 2,
  ∃ Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x),
    (∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
      ∀ x (M : ℕ), ContDiff ℝ M (Kp g x)) ∧
    (∀ (L M : ℕ) (r : ℝ) (g : ∀ x, Vec 2 → h x), 0 < r → r ≤ max 1 Cout * ϖ⁻¹ →
      (∀ x, MemLp (g x) 2 volume) →
      weightedJetNorm π (σ.pout : ℝ) M ϖ r
          (fun x _ wd z => orderedDerivative wd (Kp g x) z) ≤
        ENNReal.ofReal (CK L M * wordTheta ηg lettersF) * negJetNorm π pin L ϖ ϖ⁻¹ g) ∧
    ∀ (κF : Fin (σ.Np + 1) → ι → ℕ) (Kout : ι → ℕ), (∀ x, Kout x ≤ σ.Kmax) →
    (∀ x, Kout x ≤ κF (Fin.last σ.Np) x) →
    (∀ (j : Fin σ.Np) x y (o : Finset.Icc 2 σ.D), (lettersF j).edge x y o ≠ [] →
      κF j.succ x + o.1 ≤ κF j.castSucc y + 2) →
    (∀ (fF : ∀ x, PlaneHk Set.univ (κF 0 x) (h x))
      (uF : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x) (h x))
      (wF : ∀ (j : Fin (σ.Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x + 1) (h x)),
      momentNorm π ((σ.pout + ∑ i, σ.KsF i + 2 : ℕ)) ϖ (fun x => planeValue (fF x)) < ⊤ →
      seamChain GF lettersF X₀F δ κF tF (tF + S) vF fF uF wF →
      weightedJetNorm π (σ.pout : ℝ) σ.Kmax ϖ rstar
          (fun x a wd z => if a ≤ Kout x then planeJetOrder (uF (Fin.last σ.Np) x (tF + S)) a wd z -
            orderedDerivative wd (Kp (fun x' => planeValue (fF x')) x) z else 0) ≤
        ENNReal.ofReal (C * wordTheta ηg lettersF * peFactor η ^ Q * (1 + S) ^ Q *
            (Real.exp (-c * S) + (1 + regF.joins) * Real.exp (-c * regF.buffer) +
              Real.exp (-c * a))) *
          negJetNorm π pin σ.k ϖ 1 (fun x => planeValue (fF x)))

/-- **Transport.** Composition with a centered volume-preserving transition (`δ = ϖη_g`,
`η_g ≤ 1`) maps weighted negative norms at any scale `r ≤ ϖ⁻¹` into themselves, at the same
weight (the first-order bound of the transition is global). -/
def SeamTransportStatement : Prop :=
  ∀ (L p : ℕ) (CU g0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (Υ Υinv : Vec 2 → Vec 2) (gU δ ϖ ηg r : ℝ), 0 ≤ gU → gU ≤ g0 →
    IsCenteredTransition Υ Υinv gU δ CU (max L 2) → ContDiff ℝ (⊤ : ℕ∞) Υinv →
    0 < ϖ → ϖ ≤ 1 → 0 ≤ ηg → ηg ≤ 1 →
    δ = ϖ * ηg → 0 < r → r ≤ ϖ⁻¹ →
  ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
    negJetNorm π p L ϖ r (fun x z => g x (Υ z)) ≤ ENNReal.ofReal C * negJetNorm π p L ϖ r g

/-- **Cutoff complement.** The complement of the low cutoff `Π₋ = χ₋(θ/√η)` gains `S^{-N/2}`
from the `e`-scale negative norm of order `k` to the `R`-scale negative norm of order `N + k`. -/
def SeamCutoffComplementStatement : Prop :=
  ∀ (ξ0 : ℝ) (χm : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) χm → (∀ ξ, χm (-ξ) = χm ξ) →
    (∀ ξ, ξ0 ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → χm ξ = 1) →
  ∀ k N p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ η S ϖ : ℝ, 0 < η → η ≤ 1 → 1 ≤ S → ϖ = Real.sqrt (η / S) →
  ∀ g : ∀ x, Vec 2 → h x, (∀ x, MemLp (g x) 2 volume) →
    negJetNorm π p (N + k) ϖ ϖ⁻¹
        (fun x z => g x z - fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (g x) z) ≤
      ENNReal.ofReal (C * S ^ (-(N : ℝ) / 2)) * negJetNorm π p k ϖ 1 g

end AVRegularity.CycleWords.Assembly

namespace AVRegularity

/-- A centered transition of order `q` is one of every lower order. -/
theorem IsCenteredTransition.mono {Υ Υinv : Vec 2 → Vec 2} {g δ C : ℝ} {q q' : ℕ}
    (h : IsCenteredTransition Υ Υinv g δ C q) (hq : q' ≤ q) :
    IsCenteredTransition Υ Υinv g δ C q' where
  centered := h.centered
  left_inv := h.left_inv
  right_inv := h.right_inv
  smooth := ⟨h.smooth.1.of_le (by exact_mod_cast hq), h.smooth.2.of_le (by exact_mod_cast hq)⟩
  volume := h.volume
  dev := h.dev
  jets := fun j hj hjq z => h.jets j hj (hjq.trans hq) z

end AVRegularity
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp pass: the transverse projection on `H^s` (statement)

The transverse projection `cellTransverseProjection e` keeps the Fourier modes `n` with `n_e = 0`,
i.e. it averages along `e`. It commutes with every derivative, so it acts on `H^s` with norm at most
`1` and the same values (`TransverseHsProjectionStatement`). The sharp pass needs it to make the
admissible remainders exactly transverse, `Pφ − c'·Pq`, with `H^s` representatives. -/

/-- **The transverse projection on `H^s`.**

For `s = 0` this is the `L²` projection, of norm `≤ 1` (`cellTransverseProjection_norm_le`).
Constants are kept (mode `0`), `e^{2πi z_e}` is removed, and a function of `z_{e.rev}` only is kept,
with all its jets. There is no constant (the norm bound is `1`). -/
def TransverseHsProjectionStatement : Prop :=
  ∀ (e : Fin 2) (s : ℕ), ∃ P : TorusHk s ℂ →L[ℝ] TorusHk s ℂ,
    (∀ U, torusHkValueCLM (P U) = cellTransverseProjection e (torusHkValueCLM U)) ∧
    ∀ U, ‖P U‖ ≤ ‖U‖

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Assembly

/-! # The fast reserve of the old seam letters at a jet count

The factorization of the retained amplitude (`RetainedAmplitudeFactorStatement`, X1 of
`SeamOldScalarStatement`) at jet count `m` asks the old letters for the fast reserve
`wordReserveJstar (wordReserveKstar 0 (wordReserveN m KsO) dO) dO`. The common seam reserve
`σ.Jstar` contains it as soon as `m ≤ 2 Kmax + pout + ∑ KsF + ∑ dF + 2`
(`SeamShape.oldReserve_le`), in particular at the future input weight `pout + ∑ KsF + 2`. -/

/-- **The seam reserve covers the old letters at every jet count up to the future input weight.**
-/
theorem SeamShape.oldReserve_le (σ : SeamShape) {m : ℕ}
    (hm : m ≤ 2 * σ.Kmax + σ.pout + ∑ i, σ.KsF i + ∑ i, σ.dF i + 2) :
    wordReserveJstar (wordReserveKstar 0 (wordReserveN m σ.KsO) σ.dO) σ.dO ≤ σ.Jstar := by
  have hk := σ.hk
  have hsup : Finset.univ.sup σ.dO ≤ max (Finset.univ.sup σ.dO) (Finset.univ.sup σ.dF) :=
    le_max_left _ _
  unfold wordReserveJstar wordReserveKstar wordReserveN SeamShape.Jstar
  omega

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! Norm facts of the seam assembly: a.e. congruence of the negative norm, the triangle inequality
of the weighted jet norm, the weighted `L²` norm of supported data, `L²` closure of the cutoff and
of the transport, and measurability of jets. -/

section Negative

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

theorem negJetNorm_congr_ae (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ) {g g' : ∀ x, Vec 2 → h x}
    (hg : ∀ x, g x =ᵐ[volume] g' x) :
    negJetNorm π p j s r g = negJetNorm π p j s r g' := by
  have hi : ∀ (φ : ∀ x, Vec 2 → h x) x,
      ∫ z, inner ℝ (g x z) (φ x z) = ∫ z, inner ℝ (g' x z) (φ x z) := fun φ x =>
    integral_congr_ae ((hg x).mono fun z hz => by simp only [hz])
  unfold negJetNorm
  simp only [hi]

end Negative

/-- Minkowski for the word norm `√(Σ_w ‖x_w‖²)` of a jet. -/
theorem word_norm_add_le {a : ℕ} {E : Type*} [NormedAddCommGroup E]
    (x y : DerivativeWord2 a → E) :
    Real.sqrt (∑ w, ‖x w + y w‖ ^ 2) ≤
      Real.sqrt (∑ w, ‖x w‖ ^ 2) + Real.sqrt (∑ w, ‖y w‖ ^ 2) := by
  have hn := norm_add_le (WithLp.toLp 2 x : PiLp 2 (fun _ : DerivativeWord2 a => E))
    (WithLp.toLp 2 y)
  rw [← WithLp.toLp_add, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2] at hn
  simpa only [PiLp.toLp_apply, Pi.add_apply] using hn

/-- Minkowski in the weighted `ℓ²` sum over components. -/
theorem ennreal_weighted_l2_add_le {ι : Type*} [Fintype ι] (c E X Y : ι → ℝ≥0∞)
    (hE : ∀ v, E v ≤ X v + Y v) :
    (∑ v, c v * E v ^ 2) ^ (1 / 2 : ℝ) ≤
      (∑ v, c v * X v ^ 2) ^ (1 / 2 : ℝ) + (∑ v, c v * Y v ^ 2) ^ (1 / 2 : ℝ) := by
  have hsq : ∀ v (Z : ℝ≥0∞), c v * Z ^ 2 = (c v ^ (1 / 2 : ℝ) * Z) ^ (2 : ℝ) := by
    intro v Z
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ENNReal.rpow_two]
    norm_num
  have hL := ENNReal.Lp_add_le (s := Finset.univ) (f := fun v => c v ^ (1 / 2 : ℝ) * X v)
    (g := fun v => c v ^ (1 / 2 : ℝ) * Y v) (p := 2) (by norm_num)
  simp only [← hsq] at hL
  refine le_trans ?_ hL
  gcongr with v
  rw [← mul_add, ← hsq]
  gcongr
  exact hE v

section Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]

theorem weight_continuous (s p : ℝ) :
    Continuous fun z : Vec 2 => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) := by
  have hc : Continuous fun z : Vec 2 => 1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by fun_prop
  exact hc.rpow_const fun z => Or.inl (ne_of_gt (by positivity))

theorem weighted_word_norm_aestronglyMeasurable {a : ℕ} {E : Type*} [NormedAddCommGroup E]
    (s p : ℝ) (J : DerivativeWord2 a → Vec 2 → E)
    (hJ : ∀ w, AEStronglyMeasurable (J w) volume) :
    AEStronglyMeasurable (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
      Real.sqrt (∑ w, ‖J w z‖ ^ 2)) volume := by
  have hsum : AEStronglyMeasurable (fun z => ∑ w, ‖J w z‖ ^ 2) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun w _ => ((hJ w).norm.pow 2)
  exact (weight_continuous s p).aestronglyMeasurable.mul
    (Real.continuous_sqrt.comp_aestronglyMeasurable hsum)

/-- The triangle inequality of the weighted jet norm. -/
theorem weightedJetNorm_add_le (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    (J₁ J₂ : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (h₁ : ∀ v a w, AEStronglyMeasurable (J₁ v a w) volume)
    (h₂ : ∀ v a w, AEStronglyMeasurable (J₂ v a w) volume) :
    weightedJetNorm π p j s r (fun v a w z => J₁ v a w z + J₂ v a w z) ≤
      weightedJetNorm π p j s r J₁ + weightedJetNorm π p j s r J₂ := by
  unfold weightedJetNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_add]
  gcongr
  apply ennreal_weighted_l2_add_le
  intro v
  have hw : ∀ z : Vec 2, 0 ≤ (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) := fun z =>
    Real.rpow_nonneg (by positivity) _
  have hle : eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
      Real.sqrt (∑ w, ‖J₁ v a w z + J₂ v a w z‖ ^ 2)) 2 volume ≤
      eLpNorm ((fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
        Real.sqrt (∑ w, ‖J₁ v a w z‖ ^ 2)) +
        (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
        Real.sqrt (∑ w, ‖J₂ v a w z‖ ^ 2))) 2 volume := by
    apply eLpNorm_mono_real
      (weighted_word_norm_aestronglyMeasurable s p _ fun w => (h₁ v a w).add (h₂ v a w))
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw z) (Real.sqrt_nonneg _)),
      Pi.add_apply, ← mul_add]
    exact mul_le_mul_of_nonneg_left
      (word_norm_add_le (fun w => J₁ v a w z) (fun w => J₂ v a w z)) (hw z)
  exact hle.trans (eLpNorm_add_le (by norm_num))

theorem weightedJetNorm_congr (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    {J₁ J₂ : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v}
    (hJ : ∀ v a w z, J₁ v a w z = J₂ v a w z) :
    weightedJetNorm π p j s r J₁ = weightedJetNorm π p j s r J₂ := by
  have : J₁ = J₂ := by
    funext v a w z
    exact hJ v a w z
  rw [this]

end Weighted

section Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

theorem planeJetOrder_aestronglyMeasurable {K : ℕ} (U : PlaneHk Set.univ K E) (a : ℕ)
    (w : DerivativeWord2 a) : AEStronglyMeasurable (planeJetOrder U a w) volume := by
  by_cases ha : a ≤ K
  · exact (planeJetOrder_memLp ha U w).aestronglyMeasurable
  · have hz : planeJetOrder U a w = fun _ => 0 := by
      funext x
      simp only [planeJetOrder, ha, dite_false]
    rw [hz]
    exact aestronglyMeasurable_const

theorem planeValue_memLp {K : ℕ} (U : PlaneHk Set.univ K E) :
    MemLp (planeValue U) 2 volume :=
  planeJetOrder_memLp (Nat.zero_le K) U _

omit [MeasurableSpace E] [BorelSpace E] in
/-- The literal cutoff maps `L²` into `L²`. -/
theorem fourierCutoff_memLp_of_memLp (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    {g : Vec 2 → E} (hg : MemLp g 2 volume) : MemLp (fourierCutoff m g) 2 volume := by
  have h1 := seamFourierCutoff_memLp m R hm hs (hg.toLp g)
  have h2 : fourierCutoff m (hg.toLp g) = fourierCutoff m g := by
    funext y
    unfold fourierCutoff
    apply integral_congr_ae
    have ht : (fun x : Vec 2 => (hg.toLp g) (y - x)) =ᵐ[volume] fun x => g (y - x) :=
      ((volume : Measure (Vec 2)).measurePreserving_sub_left y).quasiMeasurePreserving.ae_eq_comp
        hg.coeFn_toLp
    filter_upwards [ht] with x hx
    rw [hx]
  rwa [h2] at h1

end Plane

/-- Data supported in `|z| ≤ C_s/ϖ` have weighted `L²` norm at most `(1 + C_s²)^p` times their
`L²` norm. -/
theorem weightedJetNorm_value_le_of_support {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {κ : ι → ℕ} (π : ι → ℝ) (ϖ Cs : ℝ) (hϖ : 0 < ϖ) (p : ℕ)
    (f : ∀ x, PlaneHk Set.univ (κ x) (h x))
    (hsupp : ∀ x, ∀ᵐ z : Vec 2 ∂volume, (Cs / ϖ) ^ 2 < z 0 ^ 2 + z 1 ^ 2 →
      planeValue (f x) z = 0) :
    weightedJetNorm π (p : ℝ) 0 ϖ 1 (fun x a wd z => planeJetOrder (f x) a wd z) ≤
      ENNReal.ofReal ((1 + Cs ^ 2) ^ p) * momentNorm π 0 ϖ (fun x => planeValue (f x)) := by
  have hϖ0 : ϖ ≠ 0 := hϖ.ne'
  have hm0 : momentIndices 0 = {(0, 0)} := by decide
  have hdef : ∀ (x : ι) (w : DerivativeWord2 0), planeJetOrder (f x) 0 w = planeValue (f x) :=
    fun x w => by
      rw [Subsingleton.elim w (fun i => i.elim0)]
      rfl
  have hword : ∀ (x : ι) (z : Vec 2),
      Real.sqrt (∑ w : DerivativeWord2 0, ‖planeJetOrder (f x) 0 w z‖ ^ 2) =
        ‖planeValue (f x) z‖ := by
    intro x z
    rw [Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _), hdef]
  have hK : ∀ v, eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) *
      ‖planeValue (f v) z‖) 2 volume ≤
      ENNReal.ofReal ((1 + Cs ^ 2) ^ p) * eLpNorm (planeValue (f v)) 2 volume := by
    intro v
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    · exact (weight_continuous ϖ p).aestronglyMeasurable.mul
        (planeValue_memLp (f v)).aestronglyMeasurable.norm
    · filter_upwards [hsupp v] with z hz
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _))]
      by_cases hzs : (Cs / ϖ) ^ 2 < z 0 ^ 2 + z 1 ^ 2
      · rw [hz hzs, norm_zero, mul_zero, mul_zero]
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have h1 : ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) ≤ Cs ^ 2 := by
          calc ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) ≤ ϖ ^ 2 * (Cs / ϖ) ^ 2 :=
                mul_le_mul_of_nonneg_left (not_lt.mp hzs) (by positivity)
            _ = Cs ^ 2 := by
                rw [div_pow]
                field_simp
        have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        calc (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2)
            ≤ (1 + Cs ^ 2) ^ ((p : ℝ) / 2) :=
              Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
          _ ≤ (1 + Cs ^ 2) ^ (p : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg Cs))
                (by linarith)
          _ = (1 + Cs ^ 2) ^ p := Real.rpow_natCast _ _
  unfold weightedJetNorm momentNorm
  rw [hm0, Finset.sum_singleton, zero_add, Finset.sum_range_one]
  simp only [hword, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one,
    one_mul, mul_one, inv_one, one_smul]
  calc (∑ v, ENNReal.ofReal (π v)⁻¹ * eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^
          ((p : ℝ) / 2) * ‖planeValue (f v) z‖) 2 volume ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal ((1 + Cs ^ 2) ^ p) *
          eLpNorm (planeValue (f v)) 2 volume) ^ 2) ^ (1 / 2 : ℝ) := by
        gcongr with v
        exact hK v
    _ = ENNReal.ofReal ((1 + Cs ^ 2) ^ p) * (∑ v, ENNReal.ofReal (π v)⁻¹ *
          eLpNorm (planeValue (f v)) 2 volume ^ 2) ^ (1 / 2 : ℝ) := by
        have hsum : ∀ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal ((1 + Cs ^ 2) ^ p) *
            eLpNorm (planeValue (f v)) 2 volume) ^ 2 =
            ENNReal.ofReal ((1 + Cs ^ 2) ^ p) ^ 2 *
              (ENNReal.ofReal (π v)⁻¹ * eLpNorm (planeValue (f v)) 2 volume ^ 2) := fun v => by
          ring
        simp only [hsum, ← Finset.mul_sum]
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

theorem orderedDerivative_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℕ} (w : DerivativeWord2 a) {g : Vec 2 → F} (hg : ContDiff ℝ (a : ℕ∞) g) :
    Continuous (orderedDerivative w g) := by
  rw [orderedDerivative_eq_iteratedFDeriv w hg]
  exact (continuous_eval_const _).comp
    (hg.continuous_iteratedFDeriv le_rfl)


/-- Zeroing the jets above a per-component order lowers the weighted jet norm. -/
theorem weightedJetNorm_ite_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ) (K : ι → ℕ)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) :
    weightedJetNorm π p j s r (fun v a w z => if a ≤ K v then J v a w z else 0) ≤
      weightedJetNorm π p j s r J := by
  unfold weightedJetNorm
  refine Finset.sum_le_sum fun a _ => ?_
  gcongr with v
  by_cases hav : a ≤ K v
  · simp only [hav, ↓reduceIte, le_refl]
  · simp only [hav, ↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, Real.sqrt_zero, mul_zero]
    rw [show (fun _ : Vec 2 => (0 : ℝ)) = 0 from rfl, eLpNorm_zero]
    exact zero_le

end AVRegularity.CycleWords.Assembly
end
end
