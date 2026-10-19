-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.Assembly.CentreFlowWindow
public import AVRegularity.CycleJoint.PlaneAllMomentNativeResidualBudget
public import AVRegularity.CycleJoint.Assembly.MeanNormalizedBlocks
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import AVRegularity.CycleJoint.PeriodicOperatorImageBudget
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.NormNum.RealSqrt

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs.Assembly

/-! Scale facts of one preparation window used by the level-B assembly: the patch scale
`R = √(B τ'')` is in `(0, 1]` and dominates `e`, the incoming radius is at most `C_old e`, and the
endpoint `t_p = (l₀ + 3/2) τ''` lies in `[t_S, t_S + 2 τ'']` where the short-flow bound holds. -/

/-- The scale facts of the preparation window. -/
theorem patch_scale_facts {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {Λ : ℕ} (hΛ : 128 ≤ Λ) {M' : ℕ} {κ : ℕ → ℝ} (hband : IsOCBandChain α q Λ ζ M' κ)
    {m : ℕ} (hm2 : 2 ≤ m) (hmM : m ≤ M') {ν B : ℝ} (hν : κ m = ν) (hB : κ (m - 1) = B)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream (Φ (m - 1))}
    {tS ρs g g₀ a B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + 2 * ocTauPP α q Λ m) ρs g g₀ a B₀ lam Cb
      qJ Kmax CG l₀ P y₀)
    {cOld COld ρold : ℝ} (hcOld : 0 < cOld)
    (hρold : cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤ ρold ∧
      ρold ≤ COld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)) :
    0 < Real.sqrt (B * ocTauPP α q Λ m) ∧ Real.sqrt (B * ocTauPP α q Λ m) ≤ 1 ∧
      ocEpsilon q Λ m ≤ Real.sqrt (B * ocTauPP α q Λ m) ∧ 0 < ρold ∧ 0 < COld ∧
      ρold ≤ COld * ocEpsilon q Λ m ∧
      tS ≤ ((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m ∧
      ((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m - tS ≤ 2 * ocTauPP α q Λ m ∧
      ∀ t ∈ Set.Icc tS (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m), ∀ y : Vec 2,
        ocTauPP α q Λ m * ‖fderiv ℝ (streamVel (Φ (m - 1)) t) y‖ ≤ g := by
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hΛ
  have hτ : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos hΛ1
  have hν0 : 0 < ν := cov.pos.1
  have hB0 : 0 < B := cov.pos.2.1
  have hexp := AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have he := AVRegularity.Scales.epsilon_basic (m := m) hq.1 hΛ
  have hE := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 hΛ
  have hνB : ν ≤ B := by
    have h := CycleReference.bandChain_step_ge hΛ1 hζ hband (by omega : 1 ≤ m) hmM
    rwa [hν, hB] at h
  have hepow : 0 < ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) :=
    Real.rpow_pos_of_pos he.1 _
  have hρ0 : 0 < ρold := lt_of_lt_of_le (mul_pos hcOld hepow) hρold.1
  have hCOld : 0 < COld := by
    by_contra hc
    have : COld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) hepow.le
    linarith [hρold.2]
  have hwin := cov.window
  refine ⟨Real.sqrt_pos.2 (mul_pos hB0 hτ), cov.RE.trans hE.2.1, ?_, hρ0, hCOld, ?_, ?_, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    have hell := cov.ellT
    have hell2 : ocEll q Λ m ν ^ 2 = ocEpsilon q Λ m ^ 2 / ν := by
      unfold ocEll
      rw [div_pow, Real.sq_sqrt hν0.le]
    rw [hell2, div_le_iff₀ hν0] at hell
    calc ocEpsilon q Λ m ^ 2 ≤ ocTauPP α q Λ m * ν := hell
      _ ≤ ocTauPP α q Λ m * B := mul_le_mul_of_nonneg_left hνB hτ.le
      _ = B * ocTauPP α q Λ m := mul_comm _ _
  · refine hρold.2.trans (mul_le_mul_of_nonneg_left ?_ hCOld.le)
    calc ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)
        ≤ ocEpsilon q Λ m ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge he.1 he.2.1 (by linarith [hexp.1, hexp.2.1])
      _ = ocEpsilon q Λ m := Real.rpow_one _
  · nlinarith [hwin.2.1]
  · nlinarith [hwin.1]
  · intro t ht y
    apply cov.short1 t _ y
    constructor
    · exact (min_le_left _ _).trans ht.1
    · refine ht.2.trans (le_trans ?_ (le_max_left _ _))
      nlinarith [hwin.1]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The glue of the one-patch statement after the seam: statements**.

`WeightedPullbackStatement` : the factorial norm with the moment weight
`(1 + ϖ²|z - z_c|²)^n` of the pullback `U ∘ X` by a measure-preserving smooth homeomorphism `X`
whose inverse is `L`-Lipschitz, centred at `X⁻¹ z_c`, is at most `L^{2n}` times the square of the
composition constant of the unweighted bound (`planeHkScaledPullback_factorial_norm_le`) times the
weighted norm of `U` centred at `z_c`. It converts the moments of the cell model and of the cell
curves through the return to physical variables (the chart flow is volume preserving with a
Lipschitz inverse). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

universe u

namespace AVRegularity.CycleJointProofs.Assembly

/-- **The moment-weighted pullback bound.** -/
def WeightedPullbackStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    {ρ : ℝ} (_hρ : 0 ≤ ρ) (C : ℕ → ℝ) (_hscale : ∀ j, 1 ≤ j → j ≤ K → ρ ^ (j - 1) * B j ≤ C j)
    (L : ℝ) (_hL : 1 ≤ L)
    (_hlip : ∀ a b : Vec 2, (X.symm a 0 - X.symm b 0) ^ 2 + (X.symm a 1 - X.symm b 1) ^ 2 ≤
      L ^ 2 * ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2))
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (U : PlaneHk Set.univ K E),
    weightedFactorialNormSq n ϖ (X.symm zc) ρ K (planeHkSmoothPullback X hX hμ B hB hb U) ≤
      ENNReal.ofReal (L ^ (2 * n) * compositionFactorialNormBound C K ^ 2) *
        weightedFactorialNormSq n ϖ zc ρ K U

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs.Assembly

/-! Mean normalization preserves the joint error with the prescribed factor four. -/

universe u v w x

section Mass
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Removing each mean costs at most two in the family factorial norm. -/
theorem meanComplement_mass_le (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (f : ∀ i, TorusHk (K i) (h i)) :
    Real.sqrt (massNormSq ρ π (fun i => (meanComplement (K i) (f i)).val)) ≤
      2 * Real.sqrt (massNormSq ρ π (fun i => (f i).val)) := by
  have hs : massNormSq ρ π (fun i => (meanComplement (K i) (f i)).val) ≤
      4 * massNormSq ρ π (fun i => (f i).val) := by
    unfold massNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := torusHkNorm_complement ρ (le_refl (K i)) (f i)
    rw [torusHkNorm_full, torusHkNorm_full] at hh
    have hb := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * Real.sqrt _)).mpr hh
    rw [mul_pow, Real.sq_sqrt (factorialNormSq_nonneg _ _),
      Real.sq_sqrt (factorialNormSq_nonneg _ _)] at hb
    have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (hπ i).le)
    nlinarith [hm]
  have hh := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
  norm_num at hh ⊢
  exact hh

end Mass

/-- Raw triangular models and their joint errors admit the prescribed exact normalization. -/
theorem meanNormalization : NormalizationStatement.{u, v, w, x} := by
  intro ι _ _ h _ _ _ _ _ _ D' P' Ctx F K Mout H D A Θ E Pacc ρm C CP Cth
    hC hCP hE hCth hΘ₀ hΘ₁ ν tS tp ρs ρold b Acoef Pd Pg
  refine ⟨meanNormalizedDiagonal K Mout Pd, meanNormalizedSource K Mout Pg, ?_⟩
  intro π hπ hA hrow hcol hr herr hmean
  refine ⟨meanNormalizedBlocks_model F π hπ K Mout H A hA Θ E Pacc ρm C CP Cth hC hCP hE hCth
      hΘ₀ hΘ₁ hrow hcol Pd Pg hr, ?_⟩
  intro f Fv hf u w hu
  let c : ∀ i, h i := fun i => torusMean (f i)
  let fc : ∀ i, TorusHk (K i) (h i) := fun i => torusConstantCarrier (K i) (c i)
  let g : ∀ i, TorusHk 0 (h i) := fun i => truncateTorusHk (Nat.zero_le _) (f i)
  let gc : ∀ i, TorusHk 0 (h i) := fun i => torusConstantCarrier 0 (c i)
  let P := jointOperator K Mout H Pd Pg
  let e : ∀ i, TorusHk (K i) (h i) := fun i =>
    u i tp - truncateTorusHk (le_max_right Mout (K i)) (P g i)
  let ec : ∀ i, TorusHk (K i) (h i) := fun i =>
    fc i - truncateTorusHk (le_max_right Mout (K i)) (P gc i)
  have he := herr f Fv hf u w hu
  change Real.sqrt (massNormSq ρs π (fun i => (e i).val)) ≤ _ at he
  have hfc : ∀ i, torusHkNorm ρold (le_refl (K i)) (fc i) ≤ Fv i := by
    intro i
    rw [torusHkNorm_constant]
    exact (torusMean_norm_le ρold (le_refl (K i)) (f i)).trans (hf i)
  have hec := herr fc Fv hfc (fun i _ => fc i)
    (fun i _ => torusConstantCarrier (K i + 1) (c i))
    (torusConstantCoupledSolution K D ν tS tp b Acoef c)
  change Real.sqrt (massNormSq ρs π (fun i => (ec i).val)) ≤ _ at hec
  have heq : (fun i => u i tp - truncateTorusHk (le_max_right Mout (K i))
      (jointOperator K Mout H (meanNormalizedDiagonal K Mout Pd)
        (meanNormalizedSource K Mout Pg) g i)) =
      (fun i => meanComplement (K i) (e i)) - (fun i => meanComplement (K i) (ec i)) := by
    funext i
    exact meanNormalized_error_identity K Mout H Pd Pg g i (u i tp) (hmean f u w hu i)
  change Real.sqrt (massNormSq ρs π (fun i =>
    (u i tp - truncateTorusHk (le_max_right Mout (K i))
      (jointOperator K Mout H (meanNormalizedDiagonal K Mout Pd)
        (meanNormalizedSource K Mout Pg) g i)).val)) ≤ _
  simp_rw [congrFun heq]
  let L := massWeightedCarrierCLM (E := h) K ρs π
  have hqe := meanComplement_mass_le K ρs π hπ e
  have hqec := meanComplement_mass_le K ρs π hπ ec
  rw [← massWeightedCarrierCLM_norm K ρs π hπ]
  rw [(massWeightedCarrierCLM (E := h) K ρs π).map_sub
    (fun i => meanComplement (K i) (e i)) (fun i => meanComplement (K i) (ec i))]
  apply (norm_sub_le _ _).trans
  change ‖L (fun i => meanComplement (K i) (e i))‖ +
    ‖L (fun i => meanComplement (K i) (ec i))‖ ≤ _
  simp only [L, massWeightedCarrierCLM_norm K ρs π hπ]
  calc
    _ ≤ 2 * Real.sqrt (massNormSq ρs π (fun i => (e i).val)) +
        2 * Real.sqrt (massNormSq ρs π (fun i => (ec i).val)) := add_le_add hqe hqec
    _ ≤ 2 * (CP * E ^ Pacc * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2)) +
        2 * (CP * E ^ Pacc * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hec (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev AVRegularity.CycleWords
open scoped Topology
namespace AVRegularity.CycleJointProofs.Assembly

/-! Pointwise moment comparison and the sharp chain rule for the actual rough pullback. -/

/-- The square root of the polynomial moment weight. -/
def pullbackMomentRoot (n : ℕ) (ϖ : ℝ) (zc z : Vec 2) : ℝ :=
  Real.sqrt (1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n

theorem pullbackMomentRoot_nonneg (n : ℕ) (ϖ : ℝ) (zc z : Vec 2) :
    0 ≤ pullbackMomentRoot n ϖ zc z := pow_nonneg (Real.sqrt_nonneg _) _

theorem pullbackMomentRoot_continuous (n : ℕ) (ϖ : ℝ) (zc : Vec 2) :
    Continuous (pullbackMomentRoot n ϖ zc) := by
  unfold pullbackMomentRoot
  fun_prop

theorem pullbackMomentRoot_sq (n : ℕ) (ϖ : ℝ) (zc z : Vec 2) :
    pullbackMomentRoot n ϖ zc z ^ 2 =
      (1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n := by
  unfold pullbackMomentRoot
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt (by positivity)]

theorem pullbackMomentRoot_comp_le (X : Vec 2 ≃ₜ Vec 2) (L : ℝ) (hL : 1 ≤ L)
    (hlip : ∀ a b : Vec 2, (X.symm a 0 - X.symm b 0) ^ 2 +
      (X.symm a 1 - X.symm b 1) ^ 2 ≤
        L ^ 2 * ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2))
    (n : ℕ) (ϖ : ℝ) (zc y : Vec 2) :
    pullbackMomentRoot n ϖ (X.symm zc) y ≤ L ^ n * pullbackMomentRoot n ϖ zc (X y) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hL2 : 1 ≤ L ^ 2 := by nlinarith only [hL]
  have hd := hlip (X y) zc
  simp only [Homeomorph.symm_apply_apply] at hd
  have hw := mul_le_mul_of_nonneg_left hd (sq_nonneg ϖ)
  have hb : 1 + ϖ ^ 2 * ((y 0 - X.symm zc 0) ^ 2 + (y 1 - X.symm zc 1) ^ 2) ≤
      L ^ 2 * (1 + ϖ ^ 2 * ((X y 0 - zc 0) ^ 2 + (X y 1 - zc 1) ^ 2)) := by
    nlinarith only [hw, hL2]
  have hs := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL0] at hs
  unfold pullbackMomentRoot
  simpa only [mul_pow] using pow_le_pow_left₀ (Real.sqrt_nonneg _) hs n

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem smoothPullback_scaled_word_budget_ae {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (C : ℕ → ℝ)
    (hscale : ∀ j, 1 ≤ j → j ≤ K → ρ ^ (j - 1) * B j ≤ C j)
    (U : PlaneHk Set.univ K E) (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    ∀ᵐ z ∂volume,
      ρ ^ j * ‖planeJetOrder (planeHkSmoothPullback X hX hμ B hB hb U) j w z‖ ≤
        ∑ a : (Σ c : OrderedFinpartition j, DerivativeWord2 c.length),
          (∏ i : Fin a.1.length, C (a.1.partSize i)) *
            (ρ ^ a.1.length * ‖planeJetOrder U a.1.length a.2 (X z)‖) := by
  obtain ⟨UN, fN, hUN, hfN, hvN⟩ := exists_smooth_planeHk_approximation U
  have hV := ((planeHkSmoothPullback_continuous X hX hμ B hB hb).tendsto U).comp hUN
  have hVs : Tendsto (fun N => smoothPlanePullback (UN N) (fN N) (hfN N) (hvN N)
      X hX hμ B hb) atTop (𝓝 (planeHkSmoothPullback X hX hμ B hB hb U)) := by
    exact hV.congr (fun N => planeHkSmoothPullback_eq_smooth X hX hμ B hB hb
      (UN N) (fN N) (hfN N) (hvN N))
  have hp := planeSobolev_pullback_word_budget_of_smooth_limit U
    (planeHkSmoothPullback X hX hμ B hB hb U) UN fN hUN hfN hvN
    X hX hμ B hb hVs j hj w
  filter_upwards [hp] with z hz
  apply (mul_le_mul_of_nonneg_left hz (pow_nonneg hρ j)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hs := scaled_partition_product_le a.1 hρ B C
    (fun l hl hlJ => hB l hl (hlJ.trans hj))
    (fun l hl hlJ => hscale l hl (hlJ.trans hj))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right hs (norm_nonneg (planeJetOrder U a.1.length a.2 (X z)))

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! Lower-integral factorial norms and their individual weighted jet readouts. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The extended weighted norm of one ordered derivative. -/
def pullbackWeightedJetNorm {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (U : PlaneHk Set.univ K E) (j : ℕ) (w : DerivativeWord2 j) : ℝ≥0∞ :=
  eLpNorm (fun z => pullbackMomentRoot n ϖ zc z * ‖planeJetOrder U j w z‖) 2 volume

theorem pullbackWeightedJet_measurable {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (U : PlaneHk Set.univ K E) (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    AEStronglyMeasurable (fun z => pullbackMomentRoot n ϖ zc z * ‖planeJetOrder U j w z‖)
      volume :=
  (pullbackMomentRoot_continuous n ϖ zc).aestronglyMeasurable.mul
    (planeJetOrder_memLp hj U w).aestronglyMeasurable.norm

private theorem weightedPullback_eLpNorm_two_sq (f : Vec 2 → ℝ)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume ^ 2 = ∫⁻ z, ENNReal.ofReal (f z ^ 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  refine lintegral_congr fun z => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem pullbackWeightedJetNorm_sq {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (U : PlaneHk Set.univ K E) (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    pullbackWeightedJetNorm n ϖ zc U j w ^ 2 =
      ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
        ‖planeJetOrder U j w z‖ ^ 2) := by
  rw [pullbackWeightedJetNorm, weightedPullback_eLpNorm_two_sq _
    (pullbackWeightedJet_measurable n ϖ zc U j hj w)]
  exact lintegral_congr fun z => by rw [mul_pow, pullbackMomentRoot_sq]

theorem weightedFactorialNormSq_eq_jetNormSum {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc ρ K U =
      ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2) *
        ∑ w : DerivativeWord2 j, pullbackWeightedJetNorm n ϖ zc U j w ^ 2 := by
  unfold weightedFactorialNormSq
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
  simp only [pullbackWeightedJetNorm_sq n ϖ zc U j hjK]
  have hm (w : DerivativeWord2 j) : AEMeasurable (fun z =>
      ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
        ‖planeJetOrder U j w z‖ ^ 2)) volume := by
    have hh := ((pullbackMomentRoot_continuous n ϖ zc).aestronglyMeasurable.mul
      (planeJetOrder_memLp hjK U w).aestronglyMeasurable.norm).aemeasurable.pow_const 2
        |>.ennreal_ofReal
    simpa only [Pi.mul_apply, mul_pow, pullbackMomentRoot_sq] using hh
  calc
    _ = ∫⁻ z, ∑ w : DerivativeWord2 j,
        ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
          ‖planeJetOrder U j w z‖ ^ 2) := by
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => by positivity), ← Finset.mul_sum]
    _ = _ := lintegral_finsetSum' _ (fun w _ => hm w)

/-- A single scaled jet is controlled by the square root of the whole factorial norm. -/
theorem pullbackWeightedJetNorm_scaled_le {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (U : PlaneHk Set.univ K E)
    (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    ENNReal.ofReal (ρ ^ j) * pullbackWeightedJetNorm n ϖ zc U j w ≤
      ENNReal.ofReal (j.factorial : ℝ) * weightedFactorialNormSq n ϖ zc ρ K U ^ (1 / 2 : ℝ) := by
  have hf : (0 : ℝ) < j.factorial := Nat.cast_pos.2 (Nat.factorial_pos j)
  have hs : (ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
      pullbackWeightedJetNorm n ϖ zc U j w) ^ 2 ≤ weightedFactorialNormSq n ϖ zc ρ K U := by
    rw [weightedFactorialNormSq_eq_jetNormSum, mul_pow,
      ← ENNReal.ofReal_pow (div_nonneg (pow_nonneg hρ _) hf.le)]
    have he : (ρ ^ j / (j.factorial : ℝ)) ^ 2 = ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2 := by
      rw [div_pow, ← pow_mul, Nat.mul_comm j 2]
    rw [he]
    apply (mul_le_mul_right (Finset.single_le_sum
      (f := fun v : DerivativeWord2 j => pullbackWeightedJetNorm n ϖ zc U j v ^ 2)
      (fun _ _ => zero_le) (Finset.mem_univ w)) _).trans
    exact Finset.single_le_sum (f := fun l =>
      ENNReal.ofReal (ρ ^ (2 * l) / (l.factorial : ℝ) ^ 2) *
        ∑ v : DerivativeWord2 l, pullbackWeightedJetNorm n ϖ zc U l v ^ 2)
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hr := ENNReal.rpow_le_rpow hs (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hr
  norm_num at hr
  have hh := mul_le_mul_right hr (ENNReal.ofReal (j.factorial : ℝ))
  have he : ENNReal.ofReal (j.factorial : ℝ) * ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) =
      ENNReal.ofReal (ρ ^ j) := by
    rw [← ENNReal.ofReal_mul hf.le]
    congr 1
    field_simp
  simpa only [← mul_assoc, he] using hh

/-- Scaled bounds for each word assemble with exactly the ordered-word multiplicity. -/
theorem weightedFactorialNormSq_le_of_scaled_jets {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (U : PlaneHk Set.univ K E) (M : ℕ → ℝ)
    (hM : ∀ j, j ≤ K → 0 ≤ M j) (F : ℝ≥0∞)
    (hb : ∀ j, j ≤ K → ∀ w : DerivativeWord2 j,
      ENNReal.ofReal (ρ ^ j) * pullbackWeightedJetNorm n ϖ zc U j w ≤
        ENNReal.ofReal (M j) * F ^ (1 / 2 : ℝ)) :
    weightedFactorialNormSq n ϖ zc ρ K U ≤
      ENNReal.ofReal (∑ j : Fin (K + 1), (2 : ℝ) ^ j.val *
        (M j.val / (j.val.factorial : ℝ)) ^ 2) * F := by
  rw [weightedFactorialNormSq_eq_jetNormSum, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
    Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ENNReal.ofReal ((2 : ℝ) ^ j * (M j / (j.factorial : ℝ)) ^ 2) * F)]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _w : DerivativeWord2 j, ENNReal.ofReal ((M j / (j.factorial : ℝ)) ^ 2) * F := by
      refine Finset.sum_le_sum fun w _ => ?_
      have hs := pow_le_pow_left' (hb j hjK w) 2
      have hr : (F ^ (1 / 2 : ℝ)) ^ 2 = F := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      rw [mul_pow, mul_pow, hr] at hs
      have hf : (0 : ℝ) < j.factorial := Nat.cast_pos.2 (Nat.factorial_pos j)
      have hh := mul_le_mul_right hs (ENNReal.ofReal ((j.factorial : ℝ)⁻¹ ^ 2))
      rw [← ENNReal.ofReal_pow (pow_nonneg hρ _),
        ← ENNReal.ofReal_pow (hM j hjK), ← mul_assoc,
        ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_assoc,
        ← ENNReal.ofReal_mul (sq_nonneg _)] at hh
      have he₁ : (j.factorial : ℝ)⁻¹ ^ 2 * (ρ ^ j) ^ 2 = ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2 := by
        rw [← pow_mul, Nat.mul_comm j 2, div_eq_mul_inv, inv_pow]; ring
      have he₂ : (j.factorial : ℝ)⁻¹ ^ 2 * M j ^ 2 = (M j / (j.factorial : ℝ)) ^ 2 := by
        rw [div_pow, div_eq_mul_inv, inv_pow]; ring
      simpa only [he₁, he₂] using hh
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, DerivativeWord2,
        DerivativeWord, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      have he : (2 : ℝ≥0∞) ^ j = ENNReal.ofReal ((2 : ℝ) ^ j) := by
        simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      rw [he, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
end

/-! Weighted Minkowski estimates for each derivative of the actual rough pullback. -/

section
private theorem weightedPullback_eLpNorm_const_mul (a : ℝ) (ha : 0 ≤ a) (f : Vec 2 → ℝ) :
    eLpNorm (fun z => a * f z) 2 volume = ENNReal.ofReal a * eLpNorm f 2 volume := by
  have he : (fun z => a * f z) = a • f := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [he, eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ha]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedPullback_component_scaled_le {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (C : ℕ → ℝ)
    (hscale : ∀ j, 1 ≤ j → j ≤ K → ρ ^ (j - 1) * B j ≤ C j)
    (L : ℝ) (hL : 1 ≤ L)
    (hlip : ∀ a b : Vec 2, (X.symm a 0 - X.symm b 0) ^ 2 +
      (X.symm a 1 - X.symm b 1) ^ 2 ≤
        L ^ 2 * ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2))
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (U : PlaneHk Set.univ K E)
    (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    ENNReal.ofReal (ρ ^ j) * pullbackWeightedJetNorm n ϖ (X.symm zc)
      (planeHkSmoothPullback X hX hμ B hB hb U) j w ≤
      ENNReal.ofReal (L ^ n * compositionFactorialOrderBound C j) *
        weightedFactorialNormSq n ϖ zc ρ K U ^ (1 / 2 : ℝ) := by
  classical
  let V := planeHkSmoothPullback X hX hμ B hB hb U
  let J := Σ c : OrderedFinpartition j, DerivativeWord2 c.length
  let p (a : J) := ∏ i : Fin a.1.length, C (a.1.partSize i)
  let f (z : Vec 2) := pullbackMomentRoot n ϖ (X.symm zc) z * ‖planeJetOrder V j w z‖
  let g (a : J) (z : Vec 2) :=
    pullbackMomentRoot n ϖ zc z * ‖planeJetOrder U a.1.length a.2 z‖
  have hC l (hl : 1 ≤ l) (hlK : l ≤ K) : 0 ≤ C l :=
    (mul_nonneg (pow_nonneg hρ _) (hB l hl hlK)).trans (hscale l hl hlK)
  have hp (a : J) : 0 ≤ p a := Finset.prod_nonneg fun i _ =>
    hC _ (a.1.partSize_pos i) ((a.1.partSize_le i).trans hj)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hf : AEStronglyMeasurable f volume :=
    pullbackWeightedJet_measurable n ϖ (X.symm zc) V j hj w
  have hg (a : J) : AEStronglyMeasurable (g a) volume :=
    pullbackWeightedJet_measurable n ϖ zc U a.1.length (a.1.length_le.trans hj) a.2
  have hpt : ∀ᵐ z ∂volume, ‖ρ ^ j * f z‖ ≤
      ∑ a : J, (L ^ n * p a) * (ρ ^ a.1.length * g a (X z)) := by
    filter_upwards [smoothPullback_scaled_word_budget_ae X hX hμ B hB hb hρ C hscale U j hj w]
      with z hz
    have hq := pullbackMomentRoot_comp_le X L hL hlip n ϖ zc z
    have hs : 0 ≤ ∑ a : J, p a * (ρ ^ a.1.length * ‖planeJetOrder U a.1.length a.2 (X z)‖) :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hp a)
        (mul_nonneg (pow_nonneg hρ _) (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hρ _)
      (mul_nonneg (pullbackMomentRoot_nonneg _ _ _ _) (norm_nonneg _)))]
    calc
      _ = pullbackMomentRoot n ϖ (X.symm zc) z * (ρ ^ j * ‖planeJetOrder V j w z‖) := by
        ring
      _ ≤ pullbackMomentRoot n ϖ (X.symm zc) z *
          ∑ a : J, p a * (ρ ^ a.1.length * ‖planeJetOrder U a.1.length a.2 (X z)‖) :=
        mul_le_mul_of_nonneg_left hz (pullbackMomentRoot_nonneg _ _ _ _)
      _ ≤ (L ^ n * pullbackMomentRoot n ϖ zc (X z)) *
          ∑ a : J, p a * (ρ ^ a.1.length * ‖planeJetOrder U a.1.length a.2 (X z)‖) :=
        mul_le_mul_of_nonneg_right hq hs
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; dsimp only [g]; ring
  have hnorm : ENNReal.ofReal (ρ ^ j) * pullbackWeightedJetNorm n ϖ (X.symm zc) V j w ≤
      ∑ a : J, ENNReal.ofReal (L ^ n * p a) *
        (ENNReal.ofReal (ρ ^ a.1.length) * pullbackWeightedJetNorm n ϖ zc U a.1.length a.2) := by
    calc
      _ = eLpNorm (fun z => ρ ^ j * f z) 2 volume :=
        (weightedPullback_eLpNorm_const_mul _ (pow_nonneg hρ _) f).symm
      _ ≤ eLpNorm (fun z => ∑ a : J, (L ^ n * p a) * (ρ ^ a.1.length * g a (X z))) 2 volume :=
        eLpNorm_mono_ae_real (hf.const_mul _) hpt
      _ = eLpNorm (∑ a : J, (L ^ n * p a) • (fun z => ρ ^ a.1.length * g a (X z))) 2 volume := by
        congr 1; funext z; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ ≤ ∑ a : J, eLpNorm ((L ^ n * p a) • (fun z => ρ ^ a.1.length * g a (X z))) 2 volume :=
        eLpNorm_sum_le (by norm_num)
      _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (pow_nonneg hL0 _) (hp a))]
        rw [weightedPullback_eLpNorm_const_mul _ (pow_nonneg hρ _)]
        have he : eLpNorm (fun z => g a (X z)) 2 volume = eLpNorm (g a) 2 volume :=
          eLpNorm_comp_measurePreserving (hg a) hμ
        rw [he]
        rfl
  apply hnorm.trans
  calc
    _ ≤ ∑ a : J, ENNReal.ofReal (L ^ n * p a) *
        (ENNReal.ofReal (a.1.length.factorial : ℝ) *
          weightedFactorialNormSq n ϖ zc ρ K U ^ (1 / 2 : ℝ)) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_right
        (pullbackWeightedJetNorm_scaled_le n ϖ zc hρ U a.1.length (a.1.length_le.trans hj) a.2) _
    _ = _ := by
      simp only [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hL0 _) (hp _)),
        ← Finset.sum_mul]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ =>
        mul_nonneg (mul_nonneg (pow_nonneg hL0 _) (hp a)) (Nat.cast_nonneg _))]
      congr 2
      rw [Fintype.sum_sigma]
      unfold compositionFactorialOrderBound
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      change (∑ _v : DerivativeWord2 c.length,
        (L ^ n * (∏ i : Fin c.length, C (c.partSize i))) * (c.length.factorial : ℝ)) =
          L ^ n * ((∏ i : Fin c.length, C (c.partSize i)) * 2 ^ c.length *
            (c.length.factorial : ℝ))
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul, DerivativeWord2, DerivativeWord,
        Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      ring
end

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! The exact moment-weighted factorial pullback estimate, including infinite weighted norms. -/

public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal

universe u

namespace AVRegularity.CycleJointProofs.Assembly

/-- A smooth measure-preserving chart transports the moment-weighted factorial norm. -/
theorem weightedPullback : WeightedPullbackStatement.{u} := by
  intro E _ _ _ _ _ _ K X hX hμ B hB hb ρ hρ C hscale L hL hlip n ϖ zc U
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hC j (hj : 1 ≤ j) (hjK : j ≤ K) : 0 ≤ C j :=
    (mul_nonneg (pow_nonneg hρ _) (hB j hj hjK)).trans (hscale j hj hjK)
  have hs := weightedFactorialNormSq_le_of_scaled_jets n ϖ (X.symm zc) hρ
    (planeHkSmoothPullback X hX hμ B hB hb U)
    (fun j => L ^ n * compositionFactorialOrderBound C j)
    (fun j hj => mul_nonneg (pow_nonneg hL0 _)
      (compositionFactorialOrderBound_nonneg C j (fun l hl hlj => hC l hl (hlj.trans hj))))
    (weightedFactorialNormSq n ϖ zc ρ K U)
    (fun j hj w => weightedPullback_component_scaled_le X hX hμ B hB hb hρ C hscale
      L hL hlip n ϖ zc U j hj w)
  have hsum : 0 ≤ ∑ j : Fin (K + 1), (2 : ℝ) ^ j.val *
      (compositionFactorialOrderBound C j.val / (j.val.factorial : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg (by norm_num) _) (sq_nonneg _)
  have he : (∑ j : Fin (K + 1), (2 : ℝ) ^ j.val *
      (L ^ n * compositionFactorialOrderBound C j.val / (j.val.factorial : ℝ)) ^ 2) =
      L ^ (2 * n) * compositionFactorialNormBound C K ^ 2 := by
    rw [compositionFactorialNormBound, Real.sq_sqrt hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.mul_comm 2 n, pow_mul]
    ring
  exact he ▸ hs

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! The plane model extends to the full L² entrance, with its exact weighted budget. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

local instance planeModelTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance planeModelTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance planeModelTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance
local instance planeModelPlaneNormed {U : Set (Vec 2)} {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (PlaneHk U K E) := inferInstance
local instance planeModelPlaneInner {U : Set (Vec 2)} {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (PlaneHk U K E) := inferInstance
local instance planeModelPlaneSpace {U : Set (Vec 2)} {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (PlaneHk U K E) := inferInstance
local instance planeModelTorusPiAdd {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    AddCommMonoid (∀ i, TorusHk (K i) (h i)) := inferInstance
local instance planeModelTorusPiModule {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    Module ℝ (∀ i, TorusHk (K i) (h i)) := inferInstance
local instance planeModelPlanePiAdd {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (U : Set (Vec 2)) (K : ι → ℕ) :
    AddCommMonoid (∀ i, PlaneHk U (K i) (h i)) := inferInstance
local instance planeModelPlanePiModule {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (U : Set (Vec 2)) (K : ι → ℕ) :
    Module ℝ (∀ i, PlaneHk U (K i) (h i)) := inferInstance

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The product truncation used as the dense entrance map. -/
def planeModelEntrance (K : ι → ℕ) :
    (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, TorusHk 0 (h i)) :=
  LinearMap.pi (fun i => (truncateTorusHk (Nat.zero_le (K i))).toLinearMap.comp (LinearMap.proj i))

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
@[simp] theorem planeModelEntrance_apply (K : ι → ℕ) (f : ∀ i, TorusHk (K i) (h i)) :
    planeModelEntrance K f = fun i => truncateTorusHk (Nat.zero_le (K i)) (f i) := rfl

omit [Fintype ι] in
/-- The product entrance is dense in the L² family. -/
theorem planeModelEntrance_dense (K : ι → ℕ) : DenseRange (planeModelEntrance (h := h) K) :=
  DenseRange.piMap (fun i => truncateTorusHk_denseRange (Nat.zero_le (K i)))

/-- The continuous extension in the unweighted carrier. Its weighted estimates are proved below. -/
def planeModelExtendedOperator (K M : ι → ℕ)
    (P : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (M i) (h i))) :
    (∀ i, TorusHk 0 (h i)) →L[ℝ] (∀ i, PlaneHk Set.univ (M i) (h i)) :=
  P.extendOfNorm (planeModelEntrance K)

variable (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K M : ι → ℕ) (Mb n : ℕ)
  (hM : ∀ i, M i ≤ Mb) (ϖ r C : ℝ) (hr : 0 < r) (y : Vec 2)
  (ℓ : ∀ i, TorusHk 0 (h i) →L[ℝ] PlaneHk Set.univ 0 (h i))
  (P : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (M i) (h i)))
  (hP : ∀ f, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y r Mb (P f i) ≤
    ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ *
      ‖ℓ i (truncateTorusHk (Nat.zero_le (K i)) (f i))‖ ^ 2))

include hπ hM hr hP

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The model has a finite Hilbert bound in the entrance truncation. -/
theorem planeModel_truncation_bound : ∃ A : ℝ, ∀ f, ‖P f‖ ≤ A * ‖planeModelEntrance K f‖ := by
  obtain ⟨A, _, hA⟩ := planeModel_exists_norm_bound π hπ M Mb n hM ϖ r C hr y ℓ
    (planeModelEntrance K) P hP
  exact ⟨A, hA⟩

/-- The weighted budget makes the unweighted extension agree with the initial model. -/
theorem planeModelExtendedOperator_agrees (f : ∀ i, TorusHk (K i) (h i)) :
    planeModelExtendedOperator K M P (planeModelEntrance K f) = P f := by
  exact LinearMap.extendOfNorm_eq (f := P) (e := planeModelEntrance K) (planeModelEntrance_dense K)
    (planeModel_truncation_bound π hπ K M Mb n hM ϖ r C hr y ℓ P hP) f

/-- Continuous clips pass the original weighted budget through the dense entrance. -/
theorem planeModelExtendedOperator_budget (g : ∀ i, TorusHk 0 (h i)) :
    ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ y r Mb (planeModelExtendedOperator K M P g i) ≤
    ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ * ‖ℓ i (g i)‖ ^ 2) := by
  refine (planeModelEntrance_dense K).induction_on g ?_ ?_
  · apply planeModel_energy_property_closed π M Mb n hM ϖ r y
      (planeModelExtendedOperator K M P) (planeModelExtendedOperator K M P).continuous
    exact continuous_const.mul (continuous_finsetSum _ (fun i _ =>
      continuous_const.mul (((ℓ i).continuous.comp (continuous_apply i)).norm.pow 2)))
  · intro f
    rw [planeModelExtendedOperator_agrees π hπ K M Mb n hM ϖ r C hr y ℓ P hP]
    exact hP f

/-- A competing weighted-bounded linear extension is continuous and equal on the dense entrance. -/
theorem planeModelExtendedOperator_unique (C' : ℝ)
    (Q' : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (M i) (h i)))
    (heq : ∀ f, Q' (planeModelEntrance K f) = P f)
    (hbudget : ∀ g, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y r Mb (Q' g i) ≤
      ENNReal.ofReal (C' ^ 2 * ∑ i, (π i)⁻¹ * ‖ℓ i (g i)‖ ^ 2)) :
    Q' = (planeModelExtendedOperator K M P).toLinearMap := by
  obtain ⟨A', _, hA'⟩ := planeModel_exists_norm_bound π hπ M Mb n hM ϖ r C' hr y ℓ
    id Q' hbudget
  have hc : Continuous Q' := (Q'.mkContinuous A' hA').continuous
  apply LinearMap.ext
  apply congrFun
  exact (planeModelEntrance_dense K).equalizer hc (planeModelExtendedOperator K M P).continuous
    (funext (fun f => (heq f).trans
      (planeModelExtendedOperator_agrees π hπ K M Mb n hM ϖ r C hr y ℓ P hP f).symm))

omit [∀ i, FiniteDimensional ℝ (h i)] hπ hM hr hP in
/-- Dense extension of a finite family plane model, preserving the weighted energy constant. -/
theorem planeModelExtension : PlaneModelExtensionStatement.{u, v} := by
  classical
  intro ι _ h _ _ _ _ _ _ π hπ K M Mb n hM hn ϖ r C hϖ hr y ℓ P hP
  refine ⟨(planeModelExtendedOperator K M P).toLinearMap,
    planeModelExtendedOperator_agrees π hπ K M Mb n hM ϖ r C hr y ℓ P hP,
    planeModelExtendedOperator_budget π hπ K M Mb n hM ϖ r C hr y ℓ P hP, ?_,
    planeModelExtendedOperator_unique π hπ K M Mb n hM ϖ r C hr y ℓ P hP⟩
  intro g i
  apply planeModel_radial_moments (hM i) n hn ϖ r hϖ hr y
    (planeModelExtendedOperator K M P g i)
  exact finite_weighted_sum_component (fun i => (π i)⁻¹)
    (fun i => inv_pos.mpr (hπ i)) _
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (planeModelExtendedOperator_budget π hπ K M Mb n hM ϖ r C hr y ℓ P hP g)) i

end AVRegularity.CycleJointProofs.Assembly
end
end
