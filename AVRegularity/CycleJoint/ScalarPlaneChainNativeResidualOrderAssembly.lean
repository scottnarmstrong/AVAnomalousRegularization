-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.WeightedGradientLiftComparison
public import AVRegularity.CycleJoint.PlaneFluxChartPull
public import AVRegularity.CycleWords.NativeCoupledFluxLinearReadouts
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Each original family piece has an actual smooth reference-chart transition, preserving its integer translation structure. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {φ : ℝ → Vec 2 → ℝ}

variable (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ)
    (s : ℝ) (p : P) (t : ℝ)

def pieceReferenceMaterial : Vec 2 ≃ₜ Vec 2 :=
  ((F.piece p).material t).trans (streamFlowHomeomorph hφ t s).symm

theorem pieceReferenceMaterial_smooth :
    ContDiff ℝ (⊤ : ℕ∞) ⇑(pieceReferenceMaterial F hφ s p t) :=
  (streamFlow_spatial_smooth hφ s t).comp ((F.piece p).material_smooth t)

theorem pieceReferenceMaterial_symm_smooth :
    ContDiff ℝ (⊤ : ℕ∞) ⇑(pieceReferenceMaterial F hφ s p t).symm :=
  ((F.piece p).material_symm_smooth t).comp (streamFlow_spatial_smooth hφ t s)

theorem pieceReferenceMaterial_equivariant (E : ℝ) (actual : ∀ p, Ctx p)
    (hT : IsTorusCompatible F actual E) (n : Fin 2 → ℤ) (y : Vec 2) :
    pieceReferenceMaterial F hφ s p t (y + latticeShift n) =
      pieceReferenceMaterial F hφ s p t y + latticeShift n := by
  change streamFlow φ hφ s ((F.piece p).material t (y + latticeShift n)) t = _
  rw [hT.1 p t n y, streamFlow_lattice_equivariant]
  rfl

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The genuine coefficient product has the exact scalar-weighted factorial energy budget. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- Polynomial or other scalar moments retain the exact coefficient factorial multiplier budget. -/
theorem planeMulCoefficient_weighted_factorialEnergy_le {K : ℕ} (U : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (q : Vec 2 → ℝ) (hD : JetMemL2On Set.univ (fun β x => q x • U.toFunction.jet β x))
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    storedChartFactorialEnergy ρ (fun x => q x ^ 2) (U.mulCoefficient C hC hb) ≤
      ENNReal.ofReal ((∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l) ^ 2) *
        storedChartFactorialEnergy ρ (fun x => q x ^ 2) U := by
  let hP := planeMulCoefficient_weight_memL2On U C hC hb q hD
  let hL := multiplicationRawJet_weight_memL2On C hC U.toFunction.jet q hD hb
  have hJ : jetToL2 (fun β x => q x • (U.mulCoefficient C hC hb).toFunction.jet β x) hP =
      jetToL2 (fun β x => q x • multiplicationRawJet C U.toFunction.jet β x) hL := by
    apply PiLp.ext
    intro β
    apply Lp.ext
    have hr : (U.mulCoefficient C hC hb).toFunction.jet β =ᵐ[volume.restrict Set.univ]
        multiplicationRawJet C U.toFunction.jet β := by
      simpa only [Measure.restrict_univ] using planeMulCoefficient_rawJet_ae U C hC hb β
    filter_upwards [(hP β).coeFn_toLp, (hL β).coeFn_toLp, hr] with x hp hl hrx
    change ((hP β).toLp (fun x => q x • (U.mulCoefficient C hC hb).toFunction.jet β x)) x =
      ((hL β).toLp (fun x => q x • multiplicationRawJet C U.toFunction.jet β x)) x
    rw [hp, hl, hrx]
  have hA (l : Fin (K + 1)) : 0 ≤ A l :=
    (norm_nonneg (coefficientDerivativeArray C l.val 0)).trans (hb l 0)
  have hW (l : ℕ) : 0 ≤ factorialRootWeight ρ l :=
    div_nonneg (pow_nonneg hρ l) (by positivity)
  have hB : 0 ≤ ∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (hW l.val) (hA l))
  have hn := multiplication_weighted_factorialNorm_le C hC U.toFunction.jet q hD hb hρ
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hB (Real.sqrt_nonneg _))).mpr hn
  rw [Real.sq_sqrt (factorialNormSq_nonneg _ _), mul_pow,
    Real.sq_sqrt (factorialNormSq_nonneg _ _)] at hs
  rw [storedChartFactorialEnergy_weighted_jet_readout ρ q _ hP,
    storedChartFactorialEnergy_weighted_jet_readout ρ q U hD, hJ]
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hs

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite normalized-time geometry energy implies finite physical-time geometry energy. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem geometryEnergyNorm_lt_top_of_time_dilation (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (K : ι → ℕ) (n : ℕ) (ϖ : ℝ) (z : Vec 2) (ρ a b ν : ℝ) (hν : 0 < ν)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (he : geometryEnergyNorm π K n ϖ z ρ (ν * a) (ν * b)
      (fun i t => u i (ν⁻¹ * t)) (fun i t => w i (ν⁻¹ * t)) < ⊤) :
    geometryEnergyNorm π K n ϖ z ρ a b u w < ⊤ := by
  have hfinite (i : ι) :
      ((⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ z ρ (K i) (u i t)) +
        ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ z ρ (K i) (w i t)) ≠ ⊤ := by
    obtain ⟨C, _, hb, hg⟩ := finite_geometry_energy_component π hπ K n ϖ z ρ
      (ν * a) (ν * b) (fun i t => u i (ν⁻¹ * t)) (fun i t => w i (ν⁻¹ * t)) he i
    have hs : (⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ z ρ (K i) (u i t)) ≠ ⊤ := by
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      apply iSup₂_le
      intro t ht
      have hh := hb (ν * t)
        ⟨mul_le_mul_of_nonneg_left ht.1 hν.le, mul_le_mul_of_nonneg_left ht.2 hν.le⟩
      simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using hh
    have hprod : ENNReal.ofReal ν *
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ z ρ (K i) (w i t)) ≠ ⊤ := by
      rw [← lintegral_comp_inv_mul_restrict_Icc ν a b hν]
      exact hg
    have hg' : (∫⁻ t in Set.Icc a b,
        weightedGradFactorialNormSq n ϖ z ρ (K i) (w i t)) ≠ ⊤ := by
      intro hh
      apply hprod
      rw [hh, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hν).ne']
    exact ENNReal.add_ne_top.mpr ⟨hs, hg'⟩
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact ENNReal.sum_ne_top.mpr (fun i _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite i))

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Finite geometry energy is independent of the chosen positive finite derivative radius. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Decreasing the radius decreases the true weighted gradient factorial square. -/
theorem weightedGradFactorialNormSq_radius_mono {K' : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (K : ℕ) (U : PlaneHk Set.univ K' E) :
    weightedGradFactorialNormSq n ϖ zc r K U ≤
      weightedGradFactorialNormSq n ϖ zc R K U := by
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul' _ le_rfl
  exact ENNReal.ofReal_le_ofReal (factorial_weight_radius_mono hr hrR j)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A finite reserve price transfers finite geometry energy to any other positive radius. -/
theorem geometryEnergyNorm_lt_top_of_radius_transfer
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ)
    (n : ℕ) (ϖ : ℝ) (z : Vec 2) (r R a b : ℝ) (hr : 0 < r) (hR : 0 < R)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (he : geometryEnergyNorm π K n ϖ z r a b u w < ⊤) :
    geometryEnergyNorm π K n ϖ z R a b u w < ⊤ := by
  let L := max 1 (R / r)
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hRr : R / L ≤ r := by
    apply (div_le_iff₀ hLp).mpr
    have hh := (div_le_iff₀ hr).mp (le_max_right 1 (R / r))
    simpa only [mul_comm] using hh
  have hfinite (i : ι) :
      ((⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ z R (K i) (u i t)) +
        ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ z R (K i) (w i t)) ≠ ⊤ := by
    obtain ⟨C, _, hb, hg⟩ := finite_geometry_energy_component π hπ K n ϖ z r a b u w he i
    let P := ENNReal.ofReal (L ^ (2 * K i))
    have hu (t : ℝ) : weightedFactorialNormSq n ϖ z R (K i) (u i t) ≤
        P * weightedFactorialNormSq n ϖ z r (K i) (u i t) :=
      (weightedFactorialNormSq_radius_reserve n ϖ z R L hL _ _).trans
        (mul_le_mul' le_rfl (weightedFactorialNormSq_radius_mono n ϖ z
          (div_pos hR hLp).le hRr _ _))
    have hs : (⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ z R (K i) (u i t)) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      apply iSup₂_le
      intro t ht
      exact (hu t).trans (mul_le_mul' le_rfl (hb t ht))
    have hg' : (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ z R (K i) (w i t)) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg)
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro t
      exact (weightedGradFactorialNormSq_radius_reserve n ϖ z R L hL _ _).trans
        (mul_le_mul' le_rfl (weightedGradFactorialNormSq_radius_mono n ϖ z
          (div_pos hR hLp).le hRr _ _))
    exact ENNReal.add_ne_top.mpr ⟨hs, hg'⟩
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact ENNReal.sum_ne_top.mpr (fun i _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite i))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The construction cover supplies every drift premise of the native coupled
feedback estimate on each certified subwindow. -/

theorem windowCover_native_drift_data
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (ic : Fin (P + 2)) (a b : ℝ)
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P ic) :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let v := ocCellDrift α q Λ ζ m ν yc
    (∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ C) ∧
    Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2) ∧
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) ∧
    (∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ Kmax → ∀ t ∈ Set.Icc a b, ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) j x‖ ≤
        strain * B₀ ^ j * (j.factorial : ℝ) * lam ^ ((1 : ℤ) - j)) := by
  dsimp only
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
  have he := Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hell : 0 < ocEll q Λ m ν ^ 2 := by
    rw [CycleReference.ocEll_sq_eq cov.pos.1]
    exact div_pos (sq_pos_of_pos he) cov.pos.1
  have hfull := hwindow.trans (clipped_scaled_time_window_subset _ _ _ _ _ hell)
  obtain ⟨C, hC⟩ := cellDrift_norm_bound (α := α) (q := q) (m := m) hΛ hζ ν yc
  refine ⟨⟨C, fun t _ x => hC t x⟩,
    cellDrift_window_measurable (α := α) (q := q) (m := m) hΛ hζ ν yc a b,
    fun t _ => cellDrift_spatial_contDiff (α := α) (q := q) (m := m) hΛ hζ ν t yc,
    fun t _ x => cellDrift_divergence_zero (α := α) (q := q) (m := m) hΛ hζ ν t yc x,
    fun j hj hjK t ht x => cov.drift_jets ic j hj hjK t (hfull ht) x⟩

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Native material flux and gradient pairings equal the physical pairings. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1ChartPull_flux_pairing {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (z : PlaneHk univ 1 E) (F : PlaneFluxL2 E) :
    (∫ y, ∑ k : Fin 2, inner ℝ (planeH1GradientOperator (planeH1ChartPull hφ t s z) k y)
      (planeFluxChartPull hφ t s F k y)) =
      ∫ x, ∑ k : Fin 2, inner ℝ (planeH1GradientOperator z k x) (F k x) := by
  calc
    _ = ∫ y, ∑ k : Fin 2,
        inner ℝ (planeH1GradientOperator z k (AVRegularity.streamFlow φ hφ t y s))
          (F k (AVRegularity.streamFlow φ hφ t y s)) := by
      apply integral_congr_ae
      have hz := ae_all_iff.mpr (fun k => planeH1ChartPull_gradient_ae hφ t s z k)
      have hF := ae_all_iff.mpr (fun k => planeFluxChartPull_ae hφ t s F k)
      filter_upwards [hz, hF] with y hzy hFy
      simp_rw [hzy, hFy]
      exact hilbertMatrixAction_inverse_pair
        (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)
        (by rw [streamFlow_jacMatrix_det_one hφ]; exact isUnit_one) _ _
    _ = _ := integral_streamFlow hφ t s (fun x => ∑ k : Fin 2,
      inner ℝ (planeH1GradientOperator z k x) (F k x))

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Compact scalar-direction tests determine every continuous linear functional on native plane H1. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_CLM_ext_scalar_compact (L M : PlaneHk univ 1 E →L[ℝ] ℝ)
    (h : ∀ (q : Vec 2 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hs : HasCompactSupport q) (e : E),
      L (compactSmoothHilbertH1 (fun x => q x • e) (hq.smul contDiff_const) (hs.smul_right)) =
      M (compactSmoothHilbertH1 (fun x => q x • e) (hq.smul contDiff_const) (hs.smul_right))) :
    L = M := by
  apply planeH1_CLM_ext_compact_smooth
  intro f hf hs
  have he := compactSmoothHilbertH1_basis_decomposition f hf hs
  dsimp only at he
  rw [he, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  let b := stdOrthonormalBasis ℝ E
  exact h (fun x => inner ℝ (b k) (f x)) ((innerSL ℝ (b k)).contDiff.comp hf)
    (hs.comp_left (inner_zero_right (b k))) (b k)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A unit-bounded scalar contracts the true finite factorial density almost everywhere. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeFactorialDensity_smul_ae {K : ℕ} (ρ c : ℝ) (U : PlaneHk Set.univ K E) :
    ∀ᵐ z ∂volume, planeFactorialDensity ρ (c • U) z = c ^ 2 * planeFactorialDensity ρ U z := by
  have hjet (a : JetIndex2 K) :
      planeJetOrder (c • U) a.1.val a.2 =ᵐ[volume]
        fun z => c • planeJetOrder U a.1.val a.2 z := by
    simp only [planeJetOrder_eq_stored (Nat.le_of_lt_succ a.1.isLt)]
    exact planeCarrier_jet_smul_ae c U a
  filter_upwards [ae_all_iff.mpr hjet] with z hz
  unfold planeFactorialDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hz a, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Interval coefficient seminorms control scalar-weighted carrier multiplication. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [FiniteDimensional ℝ F] in
/-- The same multiplier budget `coefficientSeminorm` applies after scalar weighting of every
stored jet. -/
theorem planeMultiplyIntervalCoefficient_weighted_factorialEnergy_le
    (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K : ℕ) (A t))
    (w : PlaneHk Set.univ K E) (q : Vec 2 → ℝ)
    (hD : JetMemL2On Set.univ (fun β x => q x • w.toFunction.jet β x)) :
    storedChartFactorialEnergy ρ (fun x => q x ^ 2)
        (planeMultiplyIntervalCoefficient ρ hρ K a b A hA t ht hC w) ≤
      ENNReal.ofReal ((coefficientSeminorm ρ K a b A).toReal ^ 2) *
        storedChartFactorialEnergy ρ (fun x => q x ^ 2) w := by
  have h := planeMulCoefficient_weighted_factorialEnergy_le w (A t) hC
    (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t ht x) q hD hρ.le
  rw [coefficientSeminorm_eq_sum_real_budget ρ hρ K a b A hA] at h
  exact h

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! External forcing and the actual inherited source row are reallocated with their literal signs. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The actual source row can be moved to the forcing while retaining an existing external flux. -/
theorem planeForced_split_flux_solution {a b : ℝ} (hab : a ≤ b)
    (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (B : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K
      (fun i j d r x => B i j d r x + A i j d r x) f F g u w) :
    IsCoupledWeakSolutionPlane ν a b v D K B f
      (fun i t => F i t + planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)
      g u w := by
  refine ⟨(fun p => hs.1 p), (fun p => hs.2.1 p),
    (fun p => hs.2.2.1 p), (fun p => hs.2.2.2.1 p), ?_⟩
  intro p t ht φ
  have hold := hs.2.2.2.2 p t ht φ
  simp only [Measure.restrict_univ] at hold ⊢
  apply coupledWeakIdentity_flux_reallocation volume ν a t v _ _ _ _ _ _
    (fun r => planeRawCouplingFlux K D r B (fun i => w i r) p) _ _ _ _ hold
  intro r hr
  have hrab : r ∈ Set.Icc a b := ⟨hr.1.le, hr.2.trans ht.2⟩
  let Q := planeCouplingFluxRow hab ρ hρ K D A hA hc w p r
  have hread : Q.toFunction.jet (valueIndex2 (K p)) =ᵐ[volume]
      planeRawCouplingFlux K D r A (fun i => w i r) p := by
    have hq := (univToPlane_ae (Q.val (valueIndex2 (K p)))).symm
    apply hq.trans
    exact planeCouplingFluxRow_raw_value_ae hab ρ hρ K D A hA hc w p r hrab
  filter_upwards [hread, planeCarrier_jet_add_ae (F p r) Q (valueIndex2 (K p))]
    with x hx hadd
  change planeRawCouplingFlux K D r
      (fun i j d t z => B i j d t z + A i j d t z) (fun i => w i r) p x +
        (F p r).toFunction.jet (valueIndex2 (K p)) x =
    planeRawCouplingFlux K D r B (fun i => w i r) p x +
      (F p r + Q).toFunction.jet (valueIndex2 (K p)) x
  rw [planeRawCouplingFlux_add, hadd, hx]
  abel

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! A change to the common material reference chart retains the original independent fields, constituent identities, contexts, and time partition exactly. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {φ : ℝ → Vec 2 → ℝ}

variable (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ) (s : ℝ)

def referenceChartedFamily : ChartedFamily ι h D P Ctx :=
  { F with
    piece := fun p =>
      { F.piece p with
        material := pieceReferenceMaterial F hφ s p
        material_smooth := pieceReferenceMaterial_smooth F hφ s p
        material_symm_smooth := pieceReferenceMaterial_symm_smooth F hφ s p } }

theorem referenceChartedFamily_isDescending (K : ι → ℕ) (hdesc : F.IsDescending K) :
    (referenceChartedFamily F hφ s).IsDescending K := hdesc

theorem referenceChartedFamily_isSmoothOn_window (a b E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n) :
    (referenceChartedFamily F hφ s).IsSmoothOn
      (ChartedFamily.Domain.onWindow (referenceChartedFamily F hφ s) (Set.Icc a b)) E n := hs

theorem referenceChartedFamily_isTorusCompatible (E : ℝ) (actual : ∀ p, Ctx p)
    (hT : IsTorusCompatible F actual E) :
    IsTorusCompatible (referenceChartedFamily F hφ s) actual E := by
  exact ⟨fun p t n y => pieceReferenceMaterial_equivariant F hφ s p t E actual hT n y, hT.2⟩

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual scalar responses transfer to the coupled equation with a literal residual forcing at the original edge-order bound. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {a b : ℝ} {K : ι → ℕ} {D : ℕ} {v : ℝ → Vec 2 → Vec 2}

variable (ρ : ℝ) (hρ : 0 < ρ) (hD : 2 ≤ D)
  (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
  {A' : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
  {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
  {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
  {Ferr : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
  {u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
  {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}

variable
  (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b
    (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1) i j d) ≠ ⊤)
  (hA' : ∀ i j d, coefficientSeminorm ρ (K i) a b (A' i j d) ≠ ⊤)
  (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ)
    (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1) i j d t))
  (hC' : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A' i j d t))

include hρ hD hA hA' hC hC' in
theorem scalarPlaneChain_native_residual_order_assembly
    (hread : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (F i t).toFunction.jet (valueIndex2 (K i)) =ᵐ[volume]
        fun z => planeRawCouplingFlux K D t A' (fun j => w j t) i z -
          planeRawCouplingFlux K D t
            (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1))
            (fun j => w j t) i z +
          (Ferr i t).toFunction.jet (valueIndex2 (K i)) z)
    (hs : IsPlaneChainFrom (geometryScalarData 2 G) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i)) :
    IsCoupledWeakSolutionPlane 1 a b v D K A' f Ferr (fun _ _ => 0) u w := by
  apply planeWeakSolution_total_flux_time_ae_congr ρ hρ hA hA' hC hC' _
    (scalarPlaneChain_diagonalMetric_order_solution K D hD a b v G f F u w hs)
  intro i
  filter_upwards [hread i] with t ht
  filter_upwards [ht] with z hz
  rw [hz]
  abel

end AVRegularity.CycleJointProofs
end
