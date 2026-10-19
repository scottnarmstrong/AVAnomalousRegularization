-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.FactorOfMomentsCutoffJets
import AVRegularity.CycleJoint.Assembly.SeamAllocationLetterFacts
import AVRegularity.CycleWords.MixedWords.Discard.PlainPassStage
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleWords.MixedWords.Discard.FullFieldWindowFamily
import AVRegularity.CycleWords.MixedWords.Discard.QuietOp
import AVRegularity.CycleWords.MixedWords.Discard.WeakContinuity
import AVRegularity.CycleWords.MixedWords.Discard.FullFieldProved
public import AVRegularity.CycleWords.MixedWords.Discard.BandRep
import AVRegularity.CycleWords.MixedWords.RetainedAmplitudeFactor
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the multiplier of the marks band

`marksMu K η χlo = zoneCutoff - retainedCutoff`, the multiplier `b(θ)(1 - χ_lo(θ/√η))`. It is
smooth, even, supported in `ξ_lo √η ≤ |θ| ≤ π/2`, its jets of order `l ≤ m` are at most
`B/ϖ^l` (with `B` depending on `K`, `χ_lo`, `m` only, for `ϖ ≤ min 1 √η`), and the literal cutoff
of an `L²` function by `marksMu` is the difference of the two cutoffs. -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleJointProofs.Assembly

/-- The multiplier of the marks band: the zone factor minus the retained cutoff. -/
def marksMu (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ) (θ : Vec 2) : ℝ :=
  zoneCutoff K χlo θ - retainedCutoff K η χlo θ

theorem marksMu_vecDot_nonneg (θ : Vec 2) : 0 ≤ vecDot θ θ :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem marksMu_contDiff {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (η : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (marksMu K η χlo) :=
  (zoneCutoff_contDiff hχ).sub (retainedCutoff_contDiff hχ η)

theorem marksMu_even {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (η : ℝ) (θ : Vec 2) : marksMu K η χlo (-θ) = marksMu K η χlo θ := by
  simp only [marksMu, zoneCutoff, retainedCutoff, smul_neg, hχ.even]

theorem marksMu_eq_zero_top {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (hξlo : 0 < K.ξlo) (η : ℝ) {θ : Vec 2} (hθ : Real.pi / 2 ≤ Real.sqrt (vecDot θ θ)) :
    marksMu K η χlo θ = 0 := by
  rw [marksMu, zoneCutoff_eq_zero hχ hξlo θ hθ, retainedCutoff_eq_zero hχ η hθ, sub_zero]

theorem marksMu_eq_zero_low {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    {η : ℝ} (hη : 0 < η) {θ : Vec 2}
    (hθ : Real.sqrt (vecDot θ θ) < K.ξlo * Real.sqrt η) : marksMu K η χlo θ = 0 := by
  have hs := Real.sqrt_pos.2 hη
  have h1 : χlo ((Real.sqrt η)⁻¹ • θ) = 1 := by
    apply hχ.one
    rw [sqrt_vecDot_smul, abs_of_pos (inv_pos.2 hs)]
    rw [inv_mul_le_iff₀ hs, mul_comm]
    exact hθ.le
  rw [marksMu, retainedCutoff_eq_zone, h1, one_mul, sub_self]

/-- The support of the multiplier: `ρ₁² ≤ |θ|²` with `ρ₁ = ξ_lo √η`, and `|θ| ≤ π/2`. -/
theorem marksMu_support {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (hξlo : 0 < K.ξlo) {η : ℝ} (hη : 0 < η) {θ : Vec 2} (hne : marksMu K η χlo θ ≠ 0) :
    (K.ξlo * Real.sqrt η) ^ 2 ≤ vecDot θ θ ∧ vecDot θ θ ≤ (Real.pi / 2) ^ 2 := by
  have hv := marksMu_vecDot_nonneg θ
  have hsq := Real.sq_sqrt hv
  have h1 : K.ξlo * Real.sqrt η ≤ Real.sqrt (vecDot θ θ) :=
    not_lt.1 fun h => hne (marksMu_eq_zero_low hχ hη h)
  have h2 : Real.sqrt (vecDot θ θ) < Real.pi / 2 :=
    not_le.1 fun h => hne (marksMu_eq_zero_top hχ hξlo η h)
  have h0 : 0 ≤ K.ξlo * Real.sqrt η := by positivity
  refine ⟨?_, ?_⟩
  · calc (K.ξlo * Real.sqrt η) ^ 2 ≤ Real.sqrt (vecDot θ θ) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = vecDot θ θ := hsq
  · calc vecDot θ θ = Real.sqrt (vecDot θ θ) ^ 2 := hsq.symm
      _ ≤ (Real.pi / 2) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2.le 2

/-- The band condition in the two forms: `ρ₁² ≤ |θ|²` iff `ρ₁ ≤ |θ|`. -/
theorem marksMu_band_iff {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : Vec 2) :
    ρ ^ 2 ≤ vecDot θ θ ↔ ρ ≤ Real.sqrt (vecDot θ θ) := by
  have hsq := Real.sq_sqrt (marksMu_vecDot_nonneg θ)
  constructor
  · intro h
    exact le_trans (le_abs_self ρ) (Real.abs_le_sqrt h)
  · intro h
    calc ρ ^ 2 ≤ Real.sqrt (vecDot θ θ) ^ 2 := pow_le_pow_left₀ hρ h 2
      _ = vecDot θ θ := hsq

/-- The literal cutoff by `marksMu` of an `L²` function is the difference of the cutoffs. -/
theorem fourierCutoff_marksMu {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (hξlo : 0 < K.ξlo) (η : ℝ) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : Vec 2 → E} (hg : MemLp g 2 volume) :
    fourierCutoff (marksMu K η χlo) g =
      fun y => fourierCutoff (zoneCutoff K χlo) g y - fourierCutoff (retainedCutoff K η χlo) g y := by
  have hz0 : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → zoneCutoff K χlo ξ = 0 :=
    fun ξ hξ => zoneCutoff_eq_zero hχ hξlo ξ hξ
  have hr0 : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → retainedCutoff K η χlo ξ = 0 :=
    fun ξ hξ => retainedCutoff_eq_zero hχ η hξ
  have hvd : ∀ x : Vec 2, Continuous fun θ : Vec 2 => Real.cos (vecDot θ x) := by
    intro x
    unfold vecDot
    fun_prop
  have hint : ∀ (m : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) m →
      (∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) → ∀ x : Vec 2,
      Integrable (fun θ => m θ * Real.cos (vecDot θ x)) := by
    intro m hm h0 x
    refine Continuous.integrable_of_hasCompactSupport (hm.continuous.mul (hvd x)) ?_
    exact (seamCutoff_hasCompactSupport m (Real.pi / 2) h0).mul_right
  have hk : ∀ x, cutoffKernel (marksMu K η χlo) x =
      cutoffKernel (zoneCutoff K χlo) x - cutoffKernel (retainedCutoff K η χlo) x := by
    intro x
    unfold cutoffKernel marksMu
    rw [← mul_sub, ← integral_sub (hint _ (zoneCutoff_contDiff hχ) hz0 x)
      (hint _ (retainedCutoff_contDiff hχ η) hr0 x)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [sub_mul]
  funext y
  unfold fourierCutoff
  simp only [hk, sub_smul]
  exact integral_sub (fourierCutoff_integrand_integrable _ (Real.pi / 2) hz0
    (zoneCutoff_contDiff hχ) hg y) (fourierCutoff_integrand_integrable _ (Real.pi / 2) hr0
    (retainedCutoff_contDiff hχ η) hg y)

/-- The jets of the multiplier: `ϖ^l ‖D^l μ‖ ≤ B` for `ϖ ≤ min 1 √η`, `l ≤ m`. -/
theorem marksMu_jets {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (η ϖ : ℝ), 0 < η → 0 < ϖ → ϖ ≤ 1 → ϖ ≤ Real.sqrt η →
      ∀ l ≤ m, ∀ θ, ‖iteratedFDeriv ℝ l (marksMu K η χlo) θ‖ ≤ B / ϖ ^ l := by
  obtain ⟨H, hH1, hHb⟩ := factorCutoff_finite_jet_bound (χ := χlo)
    (fun i => exists_bound_iteratedFDeriv_of_hasCompactSupport hχ.smooth hχ.hasCompactSupport i) m
  obtain ⟨Hz, hHz1, hHzb⟩ := factorCutoff_finite_jet_bound (χ := zoneCutoff K χlo)
    (fun i => exists_bound_iteratedFDeriv_comp_smul hχ.smooth hχ.hasCompactSupport
      (4 * K.ξlo / Real.pi) i) m
  have hA0 : 0 ≤ max H Hz := (zero_le_one.trans hH1).trans (le_max_left _ _)
  refine ⟨Hz + 2 ^ m * (max H Hz) ^ 2, by positivity, ?_⟩
  intro η ϖ hη hϖ hϖ1 hϖη l hl θ
  have hs := Real.sqrt_pos.2 hη
  have hscale : ϖ * |(Real.sqrt η)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.2 hs), ← div_eq_mul_inv, div_le_one hs]
    exact hϖη
  have hχa : ContDiff ℝ (⊤ : ℕ∞) fun z : Vec 2 => χlo ((Real.sqrt η)⁻¹ • z) :=
    hχ.smooth.comp (contDiff_id.const_smul _)
  have hj1 : ∀ i ≤ m, ϖ ^ i * ‖iteratedFDeriv ℝ i (fun z : Vec 2 => χlo ((Real.sqrt η)⁻¹ • z)) θ‖
      ≤ max H Hz := fun i hi =>
    (factorCutoff_scaled_normalized_jet_le hχ.smooth (zero_le_one.trans hH1) hHb hϖ.le hscale θ
      hi).trans (le_max_left _ _)
  have hj2 : ∀ i ≤ m, ϖ ^ i * ‖iteratedFDeriv ℝ i (zoneCutoff K χlo) θ‖ ≤ max H Hz := fun i hi =>
    (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hϖ.le hϖ1)).trans
      ((hHzb i hi θ).trans (le_max_right _ _))
  have hprod := factorCutoff_mul_normalized_jet_le hχa (zoneCutoff_contDiff hχ) hϖ.le hA0 θ hj1 hj2
    hl
  have hret : retainedCutoff K η χlo =
      fun z => χlo ((Real.sqrt η)⁻¹ • z) * zoneCutoff K χlo z := rfl
  have hsub : iteratedFDeriv ℝ l (marksMu K η χlo) θ =
      iteratedFDeriv ℝ l (zoneCutoff K χlo) θ - iteratedFDeriv ℝ l (retainedCutoff K η χlo) θ :=
    iteratedFDeriv_sub_apply ((zoneCutoff_contDiff hχ).contDiffAt.of_le (by exact_mod_cast le_top))
      ((retainedCutoff_contDiff hχ η).contDiffAt.of_le (by exact_mod_cast le_top))
  rw [le_div_iff₀ (pow_pos hϖ l), hsub]
  have hr : ϖ ^ l * ‖iteratedFDeriv ℝ l (retainedCutoff K η χlo) θ‖ ≤ 2 ^ m * max H Hz ^ 2 := by
    rw [hret]
    exact hprod
  have hz : ϖ ^ l * ‖iteratedFDeriv ℝ l (zoneCutoff K χlo) θ‖ ≤ Hz :=
    (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hϖ.le hϖ1)).trans (hHzb l hl θ)
  calc ‖iteratedFDeriv ℝ l (zoneCutoff K χlo) θ - iteratedFDeriv ℝ l (retainedCutoff K η χlo) θ‖ *
        ϖ ^ l ≤ (‖iteratedFDeriv ℝ l (zoneCutoff K χlo) θ‖ +
          ‖iteratedFDeriv ℝ l (retainedCutoff K η χlo) θ‖) * ϖ ^ l :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg hϖ.le _)
    _ = ϖ ^ l * ‖iteratedFDeriv ℝ l (zoneCutoff K χlo) θ‖ +
          ϖ ^ l * ‖iteratedFDeriv ℝ l (retainedCutoff K η χlo) θ‖ := by ring
    _ ≤ Hz + 2 ^ m * max H Hz ^ 2 := add_le_add hz hr

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the marks band from its fibres

`marksBandAssembly : MarksBandAssembly`. The frame of the chain (`b1wCappedFrame`), the fibre
bound at every frequency of the band (`MarksBandFibreStatement`), the identification of the output
means with the terminal stage means (`outMeanSq_eq_terminal`), the integral over the zone of the
squared stage values at the start (`StageDatumStatement`) and the band output norm
(`BandOutputStatement`) with the multiplier `marksMu`. All bounds are in `ℓ²` form, so no
constant depends on the number of stages. A word with `Θ_w = 0` has no endpoint
(`zeroAmplitudeWord`). -/

universe u v

theorem momentNorm_congr {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (n : ℕ) (s : ℝ)
    {F G : ∀ x, Vec 2 → h x} (hFG : ∀ x, F x =ᵐ[volume] G x) :
    momentNorm π n s F = momentNorm π n s G := by
  have key : ∀ (β : ℕ × ℕ) x, eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • F x z)
      2 volume = eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G x z) 2 volume := by
    intro β x
    refine eLpNorm_congr_ae ?_
    filter_upwards [hFG x] with z hz
    rw [hz]
  simp only [momentNorm, key]

theorem sq_rpow_half'' (a : ℝ≥0∞) : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- With `Θ_w = 0` the output norm of the marks band vanishes. -/
theorem jetOutputNorm_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (m Kf : ℕ)
    (s r : ℝ) (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (hJ : ∀ v a (w : DerivativeWord2 a) z, J v a w z = 0) : jetOutputNorm π m Kf s r J = 0 := by
  have : J = fun _ _ _ _ => 0 := by
    funext v a w z
    exact hJ v a w z
  subst this
  simp [jetOutputNorm]

/-- **`MarksBandStatement` from the fibres.** -/
theorem marksBandAssembly : MarksBandAssembly.{u, v} := by
  intro hF hO hD K
  obtain ⟨g₁, hg₁, hFK⟩ := hF K
  refine ⟨g₁, hg₁, ?_⟩
  intro χlo hχ Nw D H Kf m Cout hCout d Ks pos
  obtain ⟨CF, c, Q, hCF, hc, hFs⟩ := hFK Nw D m d Ks pos
  obtain ⟨CB, hCB, hBs⟩ := hO Kf m Cout hCout
  obtain ⟨CD, hCD, hDs⟩ := hD K Nw D m Ks
  obtain ⟨Bμ, hBμ, hjets⟩ := marksMu_jets hχ m
  refine ⟨CB * (Bμ + 1) * CF * Real.sqrt CD, c, Q, by positivity, hc, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg hB hJ hrstar
    hrstarC X₀ κ hκf hκ f u w hcd hch
  have hξlo : 0 < K.ξlo := pkg.consts_pos.2.1
  have hη := hB.hη
  have hS1 := hB.hS
  have hϖ := hB.ϖ_pos
  have hϖη := hB.ϖ_le
  have hϖ1 : ϖ ≤ 1 := hϖη.trans (Real.sqrt_le_one.2 hB.hη1)
  -- the frame
  obtain ⟨φ, hφ, hfφ⟩ := hcd.exists_family
  have hJ0 : wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J := by
    have := hJ
    unfold wordReserveJstar wordReserveKstar wordReserveN at this ⊢
    omega
  have hcap : ∀ j x, cappedWordSlots κ 0 d j x ≤ J := fun j x =>
    (cappedWordSlots_le_reserve κ 0 m d Ks j x).trans hJ0
  let F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁ :=
    b1wCappedFrame K g₁ H J π letters d (fun i => (hletters i).1) η S ηg t₀ S ϖ t₀ (t₀ + S) G v g
      reg pkg.toCoreScalarPackage hB.toPiece le_rfl (by linarith) le_rfl X₀ κ hκ hcap φ
      (fun x => ⟨(hφ x).1.continuous.stronglyMeasurable, (hφ x).2⟩) f u w hfφ hch
  have hUeq : (fun x => planeValue (F.u (Fin.last Nw) x F.b)) =
      fun x => planeValue (u (Fin.last Nw) x (t₀ + S)) :=
    funext fun x => planeValue_truncate _ _
  have hΘ0 := hB.wordTheta_nonneg
  by_cases hΘ : wordTheta ηg letters = 0
  · -- no endpoint
    have hz := zeroAmplitudeWord K g₁ F hΘ
    have hz' : ∀ x, planeValue (u (Fin.last Nw) x (t₀ + S)) =ᵐ[volume] 0 := fun x => by
      have := hz x F.b ⟨F.ordered, le_rfl⟩
      rwa [congrFun hUeq x] at this
    have hcut : ∀ mc : Vec 2 → ℝ, ∀ x, fourierCutoff mc (planeValue (u (Fin.last Nw) x (t₀ + S))) =
        fun _ => 0 := by
      intro mc x
      rw [fourierCutoff_congr_ae' mc (hz' x)]
      funext y
      simp [fourierCutoff]
    rw [jetOutputNorm_zero]
    · exact zero_le
    · intro x a wd z
      rw [hcut, hcut]
      change orderedDerivative wd (fun _ => (0 : h x)) z - orderedDerivative wd (fun _ => (0 : h x)) z
        = 0
      rw [orderedDerivative_zero_function, sub_self]
  · have hΘpos : 0 < wordTheta ηg letters := lt_of_le_of_ne hΘ0 (Ne.symm hΘ)
    have hρ0 : 0 ≤ K.ξlo * Real.sqrt η := by positivity
    have hP := one_le_peFactor η
    have hP0 : 0 ≤ peFactor η := by linarith
    have hS0 : 0 ≤ S := by linarith
    have hX0 : 0 ≤ CF * peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-c * S) := by positivity
    have hUL2 : ∀ x, MemLp (planeValue (u (Fin.last Nw) x (t₀ + S))) 2 volume :=
      fun x => planeValue_memLp _
    have hmom : ∀ x, ∀ β ∈ momentIndices m, Integrable (fun y : Vec 2 =>
        (y 0 ^ β.1 * y 1 ^ β.2) • planeValue (u (Fin.last Nw) x (t₀ + S)) y) := by
      intro x β hβ
      have := amplitudeIdMoments K g₁ F (Fin.last Nw) x F.b ⟨F.ordered, le_rfl⟩ m β hβ
      have e : planeValue (F.u (Fin.last Nw) x F.b) = planeValue (u (Fin.last Nw) x (t₀ + S)) :=
        congrFun hUeq x
      rw [e] at this
      exact this
    have hint : ∀ x, Integrable (planeValue (u (Fin.last Nw) x (t₀ + S))) volume := by
      intro x
      have h00 : ((0 : ℕ), (0 : ℕ)) ∈ momentIndices m := by simp [momentIndices]
      simpa using hmom x (0, 0) h00
    have hzc : HasCompactSupport (zoneCutoff K χlo) :=
      seamCutoff_hasCompactSupport _ (Real.pi / 2) fun ξ hξ => zoneCutoff_eq_zero hχ hξlo ξ hξ
    have hrc : HasCompactSupport (retainedCutoff K η χlo) :=
      seamCutoff_hasCompactSupport _ (Real.pi / 2) fun ξ hξ => retainedCutoff_eq_zero hχ η hξ
    have hJeq : (fun x (a : ℕ) (wd : DerivativeWord2 a) z =>
        orderedDerivative wd (fourierCutoff (zoneCutoff K χlo)
          (planeValue (u (Fin.last Nw) x (t₀ + S)))) z -
        orderedDerivative wd (fourierCutoff (retainedCutoff K η χlo)
          (planeValue (u (Fin.last Nw) x (t₀ + S)))) z) =
        fun x _ wd z => orderedDerivative wd (fourierCutoff (marksMu K η χlo)
          (planeValue (u (Fin.last Nw) x (t₀ + S)))) z := by
      funext x a wd z
      rw [fourierCutoff_marksMu hχ hξlo η (hUL2 x),
        orderedDerivative_sub wd
          ((fourierCutoff_contDiff _ (zoneCutoff_contDiff hχ) hzc (hint x)).of_le
            (by exact_mod_cast le_top))
          ((fourierCutoff_contDiff _ (retainedCutoff_contDiff hχ η) hrc (hint x)).of_le
            (by exact_mod_cast le_top))]
    have hmain := hBs π hB.hπ ϖ rstar (K.ξlo * Real.sqrt η) (Bμ + 1) hϖ hϖ1 hrstar hrstarC hρ0
      (by linarith) (marksMu K η χlo) (marksMu_contDiff hχ η) (marksMu_even hχ η)
      (fun θ hne => marksMu_support hχ hξlo hη hne)
      (fun l θ hl => (hjets η ϖ hη hϖ hϖ1 hϖη l hl θ).trans
        (div_le_div_of_nonneg_right (by linarith) (pow_pos hϖ l).le))
      (fun x => planeValue (u (Fin.last Nw) x (t₀ + S))) (fun x => (hUL2 x).aestronglyMeasurable)
      hmom
    have hM : momentNorm F.π (wordReserveN m Ks) F.ϖ F.φ =
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) :=
      momentNorm_congr π _ ϖ (fun x => (hfφ x).symm)
    have hnn : 0 ≤ wordTheta ηg letters * (CF * peFactor η ^ Q * (1 + S) ^ Q *
        Real.exp (-c * S)) * Real.sqrt CD := by positivity
    have hband : ∫⁻ θ in freqCube, (if (K.ξlo * Real.sqrt η) ^ 2 ≤ vecDot θ θ then
        outMeanSq π ϖ m θ (fun x => planeValue (u (Fin.last Nw) x (t₀ + S))) else 0) ≤
        ENNReal.ofReal ((wordTheta ηg letters * (CF * peFactor η ^ Q * (1 + S) ^ Q *
          Real.exp (-c * S)) * Real.sqrt CD) ^ 2) *
          momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) ^ 2 := by
      calc _ ≤ ∫⁻ θ in freqCube, ENNReal.ofReal ((wordTheta ηg letters *
              (CF * peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-c * S))) ^ 2) *
              stageDatumSq F m Ks θ := by
            refine setLIntegral_mono' measurableSet_freqCube fun θ hθ => ?_
            split_ifs with hb
            · have hb' := (marksMu_band_iff hρ0 θ).1 hb
              have hf := hFs F θ (fun l => ⟨(hletters l).1, (hletters l).2.1, (hletters l).2.2⟩)
                hJ0 pkg rfl rfl hS1 hθ hb'
              have hterm := outMeanSq_eq_terminal F m Ks θ hB.hπ hΘ
              rw [hUeq] at hterm
              calc _ = ENNReal.ofReal (wordTheta ηg letters ^ 2) *
                      stageTerminalMeanSq F m Ks θ := hterm
                _ ≤ ENNReal.ofReal (wordTheta ηg letters ^ 2) * (ENNReal.ofReal
                      ((CF * peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-c * S)) ^ 2) *
                        stageDatumSq F m Ks θ) := mul_le_mul_right hf _
                _ = _ := by
                  rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]
            · exact zero_le
        _ = ENNReal.ofReal ((wordTheta ηg letters *
              (CF * peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-c * S))) ^ 2) *
              ∫⁻ θ in freqCube, stageDatumSq F m Ks θ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal ((wordTheta ηg letters *
              (CF * peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-c * S))) ^ 2) *
              (ENNReal.ofReal CD * momentNorm F.π (wordReserveN m Ks) F.ϖ F.φ ^ 2) :=
            mul_le_mul_right (hDs g₁ F fun l => (hletters l).2.1) _
        _ = _ := by
            rw [hM, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
            congr 2
            rw [mul_pow _ (Real.sqrt CD), Real.sq_sqrt hCD.le]
    rw [hJeq]
    refine hmain.trans ?_
    calc _ ≤ ENNReal.ofReal (CB * (Bμ + 1)) * ((ENNReal.ofReal (wordTheta ηg letters *
            (CF * peFactor η ^ Q * (1 + S) ^ Q * Real.exp (-c * S)) * Real.sqrt CD) *
            momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))) ^ 2) ^
              (1 / 2 : ℝ) := by
          refine mul_le_mul_right (ENNReal.rpow_le_rpow ?_ (by norm_num)) _
          refine hband.trans (le_of_eq ?_)
          rw [mul_pow (ENNReal.ofReal _) _ 2, ← ENNReal.ofReal_pow hnn]
      _ = _ := by
          rw [sq_rpow_half'', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the full-field bound on compact data, from the fibres

`chainFullFieldCompactAssembly : ChainFullFieldCompactAssembly`. The frame of the chain
(`b1wCappedFrame`, as in the marks-band construction), the output norm from the Bloch fibres with the multiplier `0`
(`BlochOutputStatement`, `ρ = 0`: every mode), the identification of the output band with `Θ_w²`
times the terminal stage band (`ffc_outBandSq_eq_terminal`), the fibre bound
(`FullFieldFibreStatement`, a block has duration `S ≥ 1`) and the stage datum
(`StageDatumStatement`). A word with `Θ_w = 0` has no endpoint (`zeroAmplitudeWord`): its output
band vanishes. All bounds are in `ℓ²` form. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- The band norm of a constant multiple. -/
theorem ffc_cellBandSq_const_mul (k : ℕ) (ρ : ℝ) (θ : Vec 2) (c : ℂ) (g : Vec 2 → ℂ) :
    cellBandSq k ρ θ (fun y => c * g y) = ENNReal.ofReal (‖c‖ ^ 2) * cellBandSq k ρ θ g := by
  unfold cellBandSq
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  split_ifs
  · rw [cellFourierCoeff_const_mul, ← ENNReal.ofReal_mul (sq_nonneg _), norm_mul, mul_pow]
    congr 1
    ring
  · rw [mul_zero]

/-- The band norm of a cell function vanishing almost everywhere. -/
theorem ffc_cellBandSq_eq_zero (k : ℕ) (ρ : ℝ) (θ : Vec 2) {g : Vec 2 → ℂ}
    (hg : g =ᵐ[volume.restrict AVenhance.unitCube] 0) : cellBandSq k ρ θ g = 0 := by
  have hc : ∀ n, cellFourierCoeff g n = 0 := fun n => by
    unfold cellFourierCoeff
    rw [integral_congr_ae (g := fun _ => (0 : ℂ))]
    · simp
    · filter_upwards [hg] with z hz
      rw [hz, Pi.zero_apply, zero_mul]
  unfold cellBandSq
  simp [hc]

/-- The literal cutoff with the multiplier `0` is `0`. -/
theorem ffc_fourierCutoff_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Vec 2 → E) : fourierCutoff (fun _ => (0 : ℝ)) g = fun _ => 0 := by
  funext y
  unfold fourierCutoff cutoffKernel
  simp

section Sum

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- One terminal stage: its scaled band times `Θ_w²` is the output band term. -/
theorem ffc_outBand_term_eq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (k : ℕ) (ρ : ℝ) (θ : Vec 2) (hπ : ∀ x, 0 < F.π x)
    (hΘ : wordTheta F.ηg F.letters ≠ 0)
    (x : ι) (β : ℕ × ℕ) (hβ : β ∈ momentIndices (b1wLevelMoments m Ks (Fin.last Nw)))
    (e : Fin (Module.finrank ℝ (h x))) :
    ENNReal.ofReal (wordTheta F.ηg F.letters ^ 2) *
        cellBandSq k ρ θ (stageScaled F θ
          (⟨Fin.last Nw, x, ⟨β, hβ⟩, e⟩ : B1WIndex ι h Nw m Ks) F.b) =
      ENNReal.ofReal ((F.π x)⁻¹ *
        (F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        cellBandSq k ρ θ (planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e)
            (planeValue (F.u (Fin.last Nw) x F.b) y))) := by
  have hs : stageScaled F θ (⟨Fin.last Nw, x, ⟨β, hβ⟩, e⟩ : B1WIndex ι h Nw m Ks) F.b =
      fun y => b1wScale F.π F.ϖ F.ηg F.letters (⟨Fin.last Nw, x, ⟨β, hβ⟩, e⟩ : B1WIndex ι h Nw m Ks)
          * planeBlochC θ (fun y => momentWeight β y * inner ℝ (stdOrthonormalBasis ℝ (h x) e)
            (planeValue (F.u (Fin.last Nw) x F.b) y)) y := rfl
  rw [hs, ffc_cellBandSq_const_mul, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 2
  have hA : b1wAmp F.ηg F.letters (Fin.last Nw) = wordTheta F.ηg F.letters :=
    b1wAmp_last F.ηg F.letters
  have hsc : ‖b1wScale F.π F.ϖ F.ηg F.letters
      (⟨Fin.last Nw, x, ⟨β, hβ⟩, e⟩ : B1WIndex ι h Nw m Ks)‖ ^ 2 =
      (F.π x)⁻¹ * (F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2 *
        (wordTheta F.ηg F.letters)⁻¹ ^ 2 := by
    unfold b1wScale
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    change ((F.π x ^ (-(1 / 2 : ℝ)) * F.ϖ ^ (β.1 + β.2) /
      ((β.1.factorial * β.2.factorial : ℕ) : ℝ) * (b1wAmp F.ηg F.letters (Fin.last Nw))⁻¹)) ^ 2 = _
    rw [hA, mul_pow, div_pow, mul_pow, rpow_neg_half_sq_eq _ (hπ x), div_pow]
    ring
  rw [hsc]
  field_simp

/-- The output band over the terminal stages. -/
theorem ffc_outBandSq_eq_terminal {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (k : ℕ) (ρ : ℝ) (θ : Vec 2) (hπ : ∀ x, 0 < F.π x)
    (hΘ : wordTheta F.ηg F.letters ≠ 0) :
    outBandSq F.π F.ϖ m k ρ θ (fun x => planeValue (F.u (Fin.last Nw) x F.b)) =
      ENNReal.ofReal (wordTheta F.ηg F.letters ^ 2) * stageTerminalBandSq F m Ks k ρ θ := by
  classical
  unfold stageTerminalBandSq outBandSq
  rw [Finset.mul_sum]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last Nw)]
  · simp only [ite_true]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hm := b1wLevelMoments_last m Ks
    have key : ∀ (βs : {β // β ∈ momentIndices (b1wLevelMoments m Ks (Fin.last Nw))})
        (e : Fin (Module.finrank ℝ (h x))), ENNReal.ofReal (wordTheta F.ηg F.letters ^ 2) *
          cellBandSq k ρ θ (stageScaled F θ
            (⟨Fin.last Nw, x, βs, e⟩ : B1WIndex ι h Nw m Ks) F.b) =
          ENNReal.ofReal ((F.π x)⁻¹ *
            (F.ϖ ^ (βs.1.1 + βs.1.2) / ((βs.1.1.factorial * βs.1.2.factorial : ℕ) : ℝ)) ^ 2) *
            cellBandSq k ρ θ (planeBlochC θ (fun y => momentWeight βs.1 y *
              inner ℝ (stdOrthonormalBasis ℝ (h x) e)
                (planeValue (F.u (Fin.last Nw) x F.b) y))) :=
      fun βs e => ffc_outBand_term_eq F m Ks k ρ θ hπ hΘ x βs.1 βs.2 e
    rw [Finset.sum_congr rfl fun βs _ => Finset.sum_congr rfl fun e _ => key βs e]
    rw [Finset.sum_coe_sort (momentIndices (b1wLevelMoments m Ks (Fin.last Nw)))
      (fun β => ∑ e : Fin (Module.finrank ℝ (h x)), ENNReal.ofReal ((F.π x)⁻¹ *
        (F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        cellBandSq k ρ θ (planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e)
            (planeValue (F.u (Fin.last Nw) x F.b) y))))]
    rw [hm]
  · intro j _ hj
    simp [hj]
  · intro hj
    exact absurd (Finset.mem_univ _) hj

end Sum

/-- The output band of a field vanishing almost everywhere. -/
theorem ffc_outBandSq_eq_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] (π : ι → ℝ) (ϖ : ℝ) (m k : ℕ) (ρ : ℝ) (θ : Vec 2)
    {U : ∀ x, Vec 2 → h x} (hU : ∀ x, U x =ᵐ[volume] 0) : outBandSq π ϖ m k ρ θ U = 0 := by
  unfold outBandSq
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun β _ =>
    Finset.sum_eq_zero fun b _ => ?_
  have h0 : (fun y => momentWeight β y * inner ℝ (stdOrthonormalBasis ℝ (h x) b) (U x y))
      =ᵐ[volume] fun _ => (0 : ℝ) := by
    filter_upwards [hU x] with y hy
    rw [hy, Pi.zero_apply, inner_zero_right, mul_zero]
  have hB : planeBlochC θ (fun y => momentWeight β y *
      inner ℝ (stdOrthonormalBasis ℝ (h x) b) (U x y))
      =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
    filter_upwards [planeBlochC_congr_ae θ h0] with z hz
    rw [hz]
    simp [planeBlochC]
  rw [ffc_cellBandSq_eq_zero k ρ θ hB, mul_zero]

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # tools

* The zone factor `zoneCutoff K χlo`: even, `1` on `|θ| < π/4`, compactly supported, with bounded
  jets (`qh_zoneCutoff_neg`, `qh_zoneCutoff_eq_one`, `qh_zoneCutoff_hasCompactSupport`,
  `qh_zoneCutoff_jets`).
* The band norms decrease in the radius (`qh_cellBandSq_anti`, `qh_stageTerminalBandSq_anti`).
* The end of the window is quiet across less than the buffer (`qh_quiet_terminal`): a time later
  than `t₀ + S - D_q` lies in no region, since every region keeps the buffer inside the window. -/

open AVRegularity.CycleWords.Assembly

universe u v

theorem qh_vecDot_smul (c : ℝ) (θ : Vec 2) : vecDot (c • θ) (c • θ) = c ^ 2 * vecDot θ θ := by
  unfold vecDot
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem qh_zoneCutoff_neg {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (θ : Vec 2) : zoneCutoff K χlo (-θ) = zoneCutoff K χlo θ := by
  unfold zoneCutoff
  rw [smul_neg, hχ.even]

theorem qh_zoneCutoff_eq_one {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (hξlo : 0 < K.ξlo) (θ : Vec 2) (hθ : vecDot θ θ < (Real.pi / 4) ^ 2) :
    zoneCutoff K χlo θ = 1 := by
  unfold zoneCutoff
  apply hχ.one
  have hc : 0 ≤ 4 * K.ξlo / Real.pi := by positivity
  rw [qh_vecDot_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]
  have hs : Real.sqrt (vecDot θ θ) ≤ Real.pi / 4 :=
    Real.sqrt_le_iff.2 ⟨by positivity, hθ.le⟩
  calc 4 * K.ξlo / Real.pi * Real.sqrt (vecDot θ θ) ≤ 4 * K.ξlo / Real.pi * (Real.pi / 4) :=
        mul_le_mul_of_nonneg_left hs hc
    _ = K.ξlo := by field_simp

theorem qh_zoneCutoff_hasCompactSupport {K : ScalarConstants} {χlo : Vec 2 → ℝ}
    (hχ : IsLowCutoff K χlo) (hξlo : 0 < K.ξlo) : HasCompactSupport (zoneCutoff K χlo) :=
  seamCutoff_hasCompactSupport _ (Real.pi / 2) fun ξ hξ => zoneCutoff_eq_zero hχ hξlo ξ hξ

/-- The jets of the zone factor through order `n` are bounded. -/
theorem qh_zoneCutoff_jets {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (hξlo : 0 < K.ξlo) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (l : ℕ) θ, l ≤ n → ‖iteratedFDeriv ℝ l (zoneCutoff K χlo) θ‖ ≤ B := by
  have hb : ∀ l : ℕ, ∃ B : ℝ, ∀ θ, ‖iteratedFDeriv ℝ l (zoneCutoff K χlo) θ‖ ≤ B := fun l =>
    ((zoneCutoff_contDiff hχ).continuous_iteratedFDeriv (by exact_mod_cast le_top)
      ).bounded_above_of_compact_support
      ((qh_zoneCutoff_hasCompactSupport hχ hξlo).iteratedFDeriv l)
  choose B hB using hb
  refine ⟨∑ l ∈ Finset.range (n + 1), |B l|, Finset.sum_nonneg fun l _ => abs_nonneg _,
    fun l θ hl => (hB l θ).trans ((le_abs_self (B l)).trans ?_)⟩
  exact Finset.single_le_sum (f := fun l => |B l|) (fun l _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hl))

/-- The jets of the zone factor through order `n` are bounded (no sign condition on `ξ_lo`: if
`ξ_lo ≤ 0` the low cutoff vanishes identically). -/
theorem qh_zoneCutoff_jets' {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (l : ℕ) θ, l ≤ n → ‖iteratedFDeriv ℝ l (zoneCutoff K χlo) θ‖ ≤ B := by
  rcases lt_or_ge 0 K.ξlo with hξ | hξ
  · exact qh_zoneCutoff_jets hχ hξ n
  · have h0 : zoneCutoff K χlo = fun _ => 0 := by
      funext θ
      unfold zoneCutoff
      exact hχ.supp _ (by linarith [Real.sqrt_nonneg (vecDot ((4 * K.ξlo / Real.pi) • θ)
        ((4 * K.ξlo / Real.pi) • θ))])
    refine ⟨0, le_rfl, fun l θ _ => ?_⟩
    rw [h0]
    simp [iteratedFDeriv_fun_zero]

/-- The constant of the quiet regime. -/
theorem qh_quiet_scalar {CQ CF cQ P S b : ℝ} {QQ QF : ℕ} (hCQ : 0 < CQ) (hCF : 0 < CF)
    (hP : 1 ≤ P) (hS : 0 ≤ S) :
    CQ * P ^ QQ * (1 + S) ^ QQ * Real.exp (-cQ * (b / 2)) ≤
      (CQ + CF * Real.exp cQ) * P ^ (QQ + QF) * (1 + S) ^ (QQ + QF) *
        Real.exp (-(cQ / 2) * b) := by
  have he : Real.exp (-cQ * (b / 2)) = Real.exp (-(cQ / 2) * b) := by ring_nf
  rw [he]
  have h1 : CQ ≤ CQ + CF * Real.exp cQ := le_add_of_nonneg_right (by positivity)
  have h2 : P ^ QQ ≤ P ^ (QQ + QF) := pow_le_pow_right₀ hP (by omega)
  have h3 : (1 + S) ^ QQ ≤ (1 + S) ^ (QQ + QF) := pow_le_pow_right₀ (by linarith) (by omega)
  have hP0 : 0 ≤ P ^ QQ := by positivity
  have hS0 : 0 ≤ (1 + S) ^ QQ := by positivity
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_mul (mul_le_mul h1 h2 hP0 (by positivity)) h3 hS0 (by positivity)

/-- The constant of the short-buffer regime. -/
theorem qh_full_scalar {CQ CF cQ P S b : ℝ} {QQ QF : ℕ} (hCQ : 0 < CQ) (hCF : 0 < CF)
    (hcQ : 0 < cQ) (hP : 1 ≤ P) (hS : 0 ≤ S) (hb2 : b < 2) :
    CF * P ^ QF * (1 + S) ^ QF ≤
      (CQ + CF * Real.exp cQ) * P ^ (QQ + QF) * (1 + S) ^ (QQ + QF) *
        Real.exp (-(cQ / 2) * b) := by
  have he : 1 ≤ Real.exp cQ * Real.exp (-(cQ / 2) * b) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by nlinarith)
  have h1 : CF ≤ (CQ + CF * Real.exp cQ) * Real.exp (-(cQ / 2) * b) := by
    calc CF = CF * 1 := (mul_one _).symm
      _ ≤ CF * (Real.exp cQ * Real.exp (-(cQ / 2) * b)) := mul_le_mul_of_nonneg_left he hCF.le
      _ ≤ (CQ + CF * Real.exp cQ) * Real.exp (-(cQ / 2) * b) := by
        rw [← mul_assoc, add_mul]
        exact le_add_of_nonneg_left (by positivity)
  have h2 : P ^ QF ≤ P ^ (QQ + QF) := pow_le_pow_right₀ hP (by omega)
  have h3 : (1 + S) ^ QF ≤ (1 + S) ^ (QQ + QF) := pow_le_pow_right₀ (by linarith) (by omega)
  have hP0 : 0 ≤ P ^ QF := by positivity
  have hS0 : 0 ≤ (1 + S) ^ QF := by positivity
  calc CF * P ^ QF * (1 + S) ^ QF
      ≤ ((CQ + CF * Real.exp cQ) * Real.exp (-(cQ / 2) * b)) * P ^ (QQ + QF) *
          (1 + S) ^ (QQ + QF) :=
        mul_le_mul (mul_le_mul h1 h2 hP0 (by positivity)) h3 hS0 (by positivity)
    _ = _ := by ring

/-- The band norm decreases in the radius. -/
theorem qh_cellBandSq_anti (k : ℕ) {ρ₁ ρ₂ : ℝ} (h0 : 0 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (θ : Vec 2)
    (g : Vec 2 → ℂ) : cellBandSq k ρ₂ θ g ≤ cellBandSq k ρ₁ θ g := by
  unfold cellBandSq
  refine ENNReal.tsum_le_tsum fun n => ?_
  split_ifs with h2 h1
  · exact le_rfl
  · exact absurd ((pow_le_pow_left₀ h0 h12 2).trans h2) h1
  · exact zero_le
  · exact le_rfl

section Frames

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- The terminal band norms decrease in the radius. -/
theorem qh_stageTerminalBandSq_anti {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (k : ℕ) {ρ₁ ρ₂ : ℝ} (h0 : 0 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) (θ : Vec 2) :
    stageTerminalBandSq F m Ks k ρ₂ θ ≤ stageTerminalBandSq F m Ks k ρ₁ θ := by
  unfold stageTerminalBandSq
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · exact qh_cellBandSq_anti k h0 h12 θ _
  · exact le_rfl

end Frames

/-- **The end of the window is quiet** across less than the buffer. -/
theorem qh_quiet_terminal {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ} {reg : BlockRegions}
    (pkg : ScalarPackage K η G v t₀ S ϖ reg) {t : ℝ} (ht : t₀ + S - reg.buffer < t)
    (ht' : t ≤ t₀ + S) : t ∈ reg.quiet := by
  have hb0 := pkg.buffer_nonneg
  have hbS := pkg.buffer_le
  rcases pkg.cover t ⟨by linarith, ht'⟩ with hq | ⟨p, hp⟩
  · exact hq
  · exfalso
    have hin := pkg.buffer_inside p ⟨by linarith [hp.1, hp.2], le_rfl⟩
    linarith [hin.2, hp.2]

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # `chainFullFieldCompactAssembly`

See `ChainFullFieldCompactProof.lean`. Constants: `C = C_B C_F √C_D` (Bloch output with `μ = 0`,
`ρ = 0`; fibre bound; stage datum), `Q` that of the fibre bound. `chainFullFieldCompact`: the
assembly applied to the proved fibre bound (`fullFieldFibre`), the Bloch output
(`blochOutput`) and the stage datum (`BandDatum.stageDatumStatement`). -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- **The full-field bound on compact data from the fibres.** -/
theorem chainFullFieldCompactAssembly : ChainFullFieldCompactAssembly.{u, v} := by
  intro hFF hO hD K
  obtain ⟨g₁, hg₁, hFK⟩ := hFF K
  refine ⟨g₁, hg₁, ?_⟩
  intro Nw D H Kf m Cout hCout d Ks pos
  obtain ⟨CF, Q, hCF, hFs⟩ := hFK Nw D m Kf d Ks pos
  obtain ⟨CB, hCB, hBs⟩ := hO Kf m Cout 0 0 hCout le_rfl le_rfl
  obtain ⟨CD, hCD, hDs⟩ := hD K Nw D m Ks
  refine ⟨CB * CF * Real.sqrt CD, Q, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg hB hJ hrstar
    hrstarC X₀ κ hκf hκ f u w hcd hch
  have hη := hB.hη
  have hS1 := hB.hS
  have hϖ := hB.ϖ_pos
  have hϖη := hB.ϖ_le
  have hϖ1 : ϖ ≤ 1 := hϖη.trans (Real.sqrt_le_one.2 hB.hη1)
  -- the frame
  obtain ⟨φ, hφ, hfφ⟩ := hcd.exists_family
  have hJ0 : wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J := by
    have := hJ
    unfold wordReserveJstar wordReserveKstar wordReserveN at this ⊢
    omega
  have hcap : ∀ j x, cappedWordSlots κ 0 d j x ≤ J := fun j x =>
    (cappedWordSlots_le_reserve κ 0 m d Ks j x).trans hJ0
  let F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁ :=
    b1wCappedFrame K g₁ H J π letters d (fun i => (hletters i).1) η S ηg t₀ S ϖ t₀ (t₀ + S) G v g
      reg pkg.toCoreScalarPackage hB.toPiece le_rfl (by linarith) le_rfl X₀ κ hκ hcap φ
      (fun x => ⟨(hφ x).1.continuous.stronglyMeasurable, (hφ x).2⟩) f u w hfφ hch
  have hUeq : (fun x => planeValue (F.u (Fin.last Nw) x F.b)) =
      fun x => planeValue (u (Fin.last Nw) x (t₀ + S)) :=
    funext fun x => planeValue_truncate _ _
  have hΘ0 := hB.wordTheta_nonneg
  have hP := one_le_peFactor η
  have hP0 : 0 ≤ peFactor η := by linarith
  have hS0 : 0 ≤ S := by linarith
  -- the output from the Bloch fibres with the multiplier `0`
  have hmom : ∀ x, ∀ β ∈ momentIndices m, Integrable (fun y : Vec 2 =>
      (y 0 ^ β.1 * y 1 ^ β.2) • planeValue (u (Fin.last Nw) x (t₀ + S)) y) := by
    intro x β hβ
    have := amplitudeIdMoments K g₁ F (Fin.last Nw) x F.b ⟨F.ordered, le_rfl⟩ m β hβ
    have e : planeValue (F.u (Fin.last Nw) x F.b) = planeValue (u (Fin.last Nw) x (t₀ + S)) :=
      congrFun hUeq x
    rw [e] at this
    exact this
  have hmain := hBs π hB.hπ ϖ rstar hϖ hϖ1 hrstar hrstarC (fun _ => (0 : ℝ)) contDiff_const
    HasCompactSupport.zero (fun _ => rfl)
    (fun l θ _ => by simp [iteratedFDeriv_fun_zero])
    (fun θ hθ => absurd hθ (not_lt.2 (by
      rw [sq, mul_zero]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)))
    (κ (Fin.last Nw)) hκf (fun x => u (Fin.last Nw) x (t₀ + S)) hmom
  have hJeq : (fun x (a : ℕ) (wd : DerivativeWord2 a) z =>
      planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
        orderedDerivative wd (fourierCutoff (fun _ => (0 : ℝ))
          (planeValue (u (Fin.last Nw) x (t₀ + S)))) z) =
      fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z := by
    funext x a wd z
    rw [ffc_fourierCutoff_zero, orderedDerivative_zero_function, sub_zero]
  rw [hJeq] at hmain
  refine hmain.trans ?_
  -- the output band from the fibres and the datum
  have hM : momentNorm F.π (wordReserveN m Ks) F.ϖ F.φ =
      momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) :=
    momentNorm_congr π _ ϖ (fun x => (hfφ x).symm)
  have hX0 : 0 ≤ CF * peFactor η ^ Q * (1 + S) ^ Q := by positivity
  have hnn : 0 ≤ wordTheta ηg letters * (CF * peFactor η ^ Q * (1 + S) ^ Q) * Real.sqrt CD := by
    positivity
  have hband : ∫⁻ θ in freqCube,
      outBandSq π ϖ m Kf 0 θ (fun x => planeValue (u (Fin.last Nw) x (t₀ + S))) ≤
      ENNReal.ofReal ((wordTheta ηg letters * (CF * peFactor η ^ Q * (1 + S) ^ Q) *
        Real.sqrt CD) ^ 2) *
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) ^ 2 := by
    by_cases hΘ : wordTheta ηg letters = 0
    · -- no endpoint
      have hz := zeroAmplitudeWord K g₁ F hΘ
      have hz' : ∀ x, planeValue (u (Fin.last Nw) x (t₀ + S)) =ᵐ[volume] 0 := fun x => by
        have := hz x F.b ⟨F.ordered, le_rfl⟩
        rwa [congrFun hUeq x] at this
      simp only [ffc_outBandSq_eq_zero π ϖ m Kf 0 _ hz', lintegral_zero]
      exact zero_le
    calc ∫⁻ θ in freqCube,
          outBandSq π ϖ m Kf 0 θ (fun x => planeValue (u (Fin.last Nw) x (t₀ + S)))
        ≤ ∫⁻ θ in freqCube, ENNReal.ofReal ((wordTheta ηg letters *
            (CF * peFactor η ^ Q * (1 + S) ^ Q)) ^ 2) * stageDatumSq F m Ks θ := by
          refine setLIntegral_mono' measurableSet_freqCube fun θ hθ => ?_
          have hf := hFs F θ (fun l => ⟨(hletters l).1, (hletters l).2.1, (hletters l).2.2⟩)
            hJ (by show t₀ + 1 ≤ t₀ + S; linarith) hθ
          have hba : F.b - F.a = S := by
            show t₀ + S - t₀ = S
            ring
          rw [hba] at hf
          have hterm := ffc_outBandSq_eq_terminal F m Ks Kf 0 θ hB.hπ hΘ
          rw [hUeq] at hterm
          calc _ = ENNReal.ofReal (wordTheta ηg letters ^ 2) *
                  stageTerminalBandSq F m Ks Kf 0 θ := hterm
            _ ≤ ENNReal.ofReal (wordTheta ηg letters ^ 2) * (ENNReal.ofReal
                  ((CF * peFactor η ^ Q * (1 + S) ^ Q) ^ 2) * stageDatumSq F m Ks θ) :=
                mul_le_mul_right hf _
            _ = _ := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]
      _ = ENNReal.ofReal ((wordTheta ηg letters * (CF * peFactor η ^ Q * (1 + S) ^ Q)) ^ 2) *
            ∫⁻ θ in freqCube, stageDatumSq F m Ks θ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((wordTheta ηg letters * (CF * peFactor η ^ Q * (1 + S) ^ Q)) ^ 2) *
            (ENNReal.ofReal CD * momentNorm F.π (wordReserveN m Ks) F.ϖ F.φ ^ 2) :=
          mul_le_mul_right (hDs g₁ F fun l => (hletters l).2.1) _
      _ = _ := by
          rw [hM, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
          congr 2
          rw [mul_pow _ (Real.sqrt CD), Real.sq_sqrt hCD.le]
  calc _ ≤ ENNReal.ofReal CB * ((ENNReal.ofReal (wordTheta ηg letters *
          (CF * peFactor η ^ Q * (1 + S) ^ Q) * Real.sqrt CD) *
          momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))) ^ 2) ^
            (1 / 2 : ℝ) := by
        refine mul_le_mul_right (ENNReal.rpow_le_rpow ?_ (by norm_num)) _
        refine hband.trans (le_of_eq ?_)
        rw [mul_pow (ENNReal.ofReal _) _ 2, ← ENNReal.ofReal_pow hnn]
    _ = _ := by
        rw [sq_rpow_half'', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- **The full-field bound on compact data.** -/
theorem chainFullFieldCompact : ChainFullFieldCompactStatement.{u, v} :=
  chainFullFieldCompactAssembly fullFieldFibre blochOutput BandDatum.stageDatumStatement

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # the full-field bound on rough data

`chainFullFieldAssembly : ChainFullFieldAssembly`: `rff_core` with the compact bound
(`ChainFullFieldCompactStatement`) and weak continuity (`ChainWeakContinuityStatement`), both read
at the capped slots of the chain; the threshold is the minimum of the two thresholds and `1/4`
(for the compact chains of `exists_compactChain_capped`), the constants are those of the compact
bound. `chainFullField : ChainFullFieldStatement`: the assembly applied to `chainFullFieldCompact`
and `chainWeakContinuity`. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- **The full-field bound on rough data from compact data and weak continuity.** -/
theorem chainFullFieldAssembly : ChainFullFieldAssembly.{u, v} := by
  intro hFc hWC K
  obtain ⟨g₁C, hg₁C, hFcK⟩ := hFc K
  obtain ⟨g₁W, hg₁W, hWCK⟩ := hWC K
  refine ⟨min (min g₁C g₁W) (1 / 4), lt_min (lt_min hg₁C hg₁W) (by norm_num), ?_⟩
  intro Nw D H Kf m Cout hCout d Ks pos
  obtain ⟨C, Q, hC, hFcs⟩ := hFcK Nw D H Kf m Cout hCout d Ks pos
  refine ⟨C, Q, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg hB hJ hrstar
    hrstarC X₀ κ hκf hκ f u w hfin hch
  have hcapW := cappedWordSlots_isWordSlots hB.hlet (fun i => (hletters i).1) hκ Kf
  have hcapf : ∀ x, Kf ≤ cappedWordSlots κ Kf d (Fin.last Nw) x :=
    fun x => (cappedWordSlots_last κ Kf d x (hκf x)).ge
  exact rff_core (min_le_right _ _) hletters pkg hB hJ X₀ hrstar hκf hκ hfin hch
    ENNReal.ofReal_ne_top
    (fun fk uk wk hcd hchk => hFcs J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg
      (hB.mono ((min_le_left _ _).trans (min_le_left _ _))) hJ hrstar hrstarC X₀ _ hcapf hcapW
      fk uk wk hcd hchk)
    (fun Φ hΦ => by
      obtain ⟨CΦ, hCΦ, hW⟩ := hWCK Nw D H Kf m d Ks pos J π letters hletters η S ηg t₀ ϖ G v g
        reg pkg (hB.mono ((min_le_left _ _).trans (min_le_right _ _))) hJ X₀ Φ hΦ
      exact ⟨CΦ, hCΦ, fun f' u' w' hfin' hchk => hW _ hcapf hcapW f' u' w' hfin' hchk⟩)

/-- **The full-field bound.** -/
theorem chainFullField : ChainFullFieldStatement.{u, v} :=
  chainFullFieldAssembly chainFullFieldCompact chainWeakContinuity

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # `quietHighAssembly`

`QuietHighStatement` from the fibres. The frame of the chain (`b1wCappedFrame`, as in pieces 8
and 15); the output norm of `U - b(D)U` from the Bloch fibres (`BlochOutputStatement` with the zone
factor `b = zoneCutoff K χlo` and `ρ = π/4`); the output band as `Θ_w²` times the terminal stage
band; at each frequency of the zone, the terminal band at radius `π/4`:
* buffer `D_q ≥ 2`: the last `D_q/2` of the window is quiet (`qh_quiet_terminal`) with zero drift
  (`quiet_zero`), and `QuietHighFibreStatement` with the stretch `D_q/2 ≥ 1` gives the factor
  `e^{-c_Q D_q/2}`;
* buffer `D_q < 2`: the band at radius `π/4` is at most the full band
  (`qh_stageTerminalBandSq_anti`), and `FullFieldFibreStatement` with `e^{c_Q} e^{-c_Q D_q/2} ≥ 1`;
then the stage datum (`StageDatumStatement`). Constants: `C = C_B (C_Q + C_F e^{c_Q}) √C_D`,
`c = c_Q/2`, `Q = Q_Q + Q_F`; the threshold is the minimum of the two fibre thresholds.
`quietHigh`: the assembly applied to the proved inputs (`quietHighFibreAssembly plainStage
plainKernel stageFamilyZone`, `fullFieldFibre`, `blochOutput`,
`BandDatum.stageDatumStatement`). -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- The quiet high frequencies from the fibres. -/
theorem quietHighAssembly : QuietHighAssembly.{u, v} := by
  intro hQ hFF hO hD K
  obtain ⟨g₁Q, hg₁Q, hQK⟩ := hQ K
  obtain ⟨g₁F, hg₁F, hFK⟩ := hFF K
  refine ⟨min g₁Q g₁F, lt_min hg₁Q hg₁F, ?_⟩
  intro χlo hχ Nw D H Kf m Cout hCout d Ks pos
  obtain ⟨CQ, cQ, QQ, hCQ, hcQ, hQs⟩ := hQK Nw D m Kf d Ks pos
  obtain ⟨CF, QF, hCF, hFs⟩ := hFK Nw D m Kf d Ks pos
  obtain ⟨Bμ, hBμ0, hBμ⟩ := qh_zoneCutoff_jets' hχ (m + Kf)
  obtain ⟨CB, hCB, hBs⟩ := hO Kf m Cout (Real.pi / 4) Bμ hCout (by positivity) hBμ0
  obtain ⟨CD, hCD, hDs⟩ := hD K Nw D m Ks
  refine ⟨CB * (CQ + CF * Real.exp cQ) * Real.sqrt CD, cQ / 2, QQ + QF, by positivity,
    by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg hB hJ hrstar
    hrstarC X₀ κ hκf hκ f u w hcd hch
  have hξlo : 0 < K.ξlo := pkg.consts_pos.2.1
  have hS1 := hB.hS
  have hϖ := hB.ϖ_pos
  have hϖη := hB.ϖ_le
  have hϖ1 : ϖ ≤ 1 := hϖη.trans (Real.sqrt_le_one.2 hB.hη1)
  have hb0 := pkg.buffer_nonneg
  have hbS := pkg.buffer_le
  -- the frame
  obtain ⟨φ, hφ, hfφ⟩ := hcd.exists_family
  have hJ0 : wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J := by
    have := hJ
    unfold wordReserveJstar wordReserveKstar wordReserveN at this ⊢
    omega
  have hcap : ∀ j x, cappedWordSlots κ 0 d j x ≤ J := fun j x =>
    (cappedWordSlots_le_reserve κ 0 m d Ks j x).trans hJ0
  let F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K (min g₁Q g₁F) :=
    b1wCappedFrame K (min g₁Q g₁F) H J π letters d (fun i => (hletters i).1) η S ηg t₀ S ϖ t₀
      (t₀ + S) G v g reg pkg.toCoreScalarPackage hB.toPiece le_rfl (by linarith) le_rfl X₀ κ hκ
      hcap φ (fun x => ⟨(hφ x).1.continuous.stronglyMeasurable, (hφ x).2⟩) f u w hfφ hch
  have hUeq : (fun x => planeValue (F.u (Fin.last Nw) x F.b)) =
      fun x => planeValue (u (Fin.last Nw) x (t₀ + S)) :=
    funext fun x => planeValue_truncate _ _
  have hΘ0 := hB.wordTheta_nonneg
  have hP := one_le_peFactor η
  have hS0 : 0 ≤ S := by linarith
  -- the output from the Bloch fibres with the zone factor
  have hmom : ∀ x, ∀ β ∈ momentIndices m, Integrable (fun y : Vec 2 =>
      (y 0 ^ β.1 * y 1 ^ β.2) • planeValue (u (Fin.last Nw) x (t₀ + S)) y) := by
    intro x β hβ
    have := amplitudeIdMoments K (min g₁Q g₁F) F (Fin.last Nw) x F.b ⟨F.ordered, le_rfl⟩ m β hβ
    have e : planeValue (F.u (Fin.last Nw) x F.b) = planeValue (u (Fin.last Nw) x (t₀ + S)) :=
      congrFun hUeq x
    rw [e] at this
    exact this
  have hmain := hBs π hB.hπ ϖ rstar hϖ hϖ1 hrstar hrstarC (zoneCutoff K χlo)
    (zoneCutoff_contDiff hχ) (qh_zoneCutoff_hasCompactSupport hχ hξlo) (qh_zoneCutoff_neg hχ)
    (fun l θ hl => hBμ l θ hl) (fun θ hθ => qh_zoneCutoff_eq_one hχ hξlo θ hθ)
    (κ (Fin.last Nw)) hκf (fun x => u (Fin.last Nw) x (t₀ + S)) hmom
  refine hmain.trans ?_
  -- the fibre bound at radius `π/4`, both regimes
  set X : ℝ := (CQ + CF * Real.exp cQ) * peFactor η ^ (QQ + QF) * (1 + S) ^ (QQ + QF) *
    Real.exp (-(cQ / 2) * reg.buffer) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hba : F.b - F.a = S := by
    show t₀ + S - t₀ = S
    ring
  have hfib : ∀ θ ∈ freqCube, stageTerminalBandSq F m Ks Kf (Real.pi / 4) θ ≤
      ENNReal.ofReal (X ^ 2) * stageDatumSq F m Ks θ := by
    intro θ hθ
    have hlet : ∀ l, (letters l).order = d l ∧ (letters l).slow = Ks l ∧
        (letters l).positive = pos l := fun l =>
      ⟨(hletters l).1, (hletters l).2.1, (hletters l).2.2⟩
    by_cases hbuf : 2 ≤ reg.buffer
    · -- the quiet regime
      have ha : t₀ ≤ t₀ + S - reg.buffer / 2 := by linarith
      have hquiet : Icc (t₀ + S - reg.buffer / 2) (t₀ + S) ⊆ reg.quiet := fun t ht =>
        qh_quiet_terminal pkg (by linarith [ht.1]) ht.2
      have hv0 : ∀ t ∈ Icc (t₀ + S - reg.buffer / 2) (t₀ + S), ∀ z, v t z = 0 := fun t ht z =>
        pkg.quiet_zero t ⟨hquiet ht, by linarith [ht.1], ht.2⟩ z
      have hq := hQs (F.mono (min_le_left g₁Q g₁F)) θ hlet hJ hθ (reg.buffer / 2)
        (by linarith) ha hquiet hv0
      have hba' : (F.mono (min_le_left g₁Q g₁F)).b - (F.mono (min_le_left g₁Q g₁F)).a = S := hba
      rw [hba'] at hq
      have hle : CQ * peFactor η ^ QQ * (1 + S) ^ QQ * Real.exp (-cQ * (reg.buffer / 2)) ≤ X :=
        qh_quiet_scalar hCQ hCF hP hS0
      exact hq.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (by positivity) hle 2)) le_rfl)
    · -- the short-buffer regime
      have hf := hFs (F.mono (min_le_right g₁Q g₁F)) θ hlet hJ
        (by show t₀ + 1 ≤ t₀ + S; linarith) hθ
      have hba' : (F.mono (min_le_right g₁Q g₁F)).b - (F.mono (min_le_right g₁Q g₁F)).a = S := hba
      rw [hba'] at hf
      have hle : CF * peFactor η ^ QF * (1 + S) ^ QF ≤ X :=
        qh_full_scalar hCQ hCF hcQ hP hS0 (not_le.1 hbuf)
      exact (qh_stageTerminalBandSq_anti F m Ks Kf le_rfl (by positivity) θ).trans
        (hf.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (by positivity) hle 2)) le_rfl))
  -- the output band from the fibres and the datum
  have hM : momentNorm F.π (wordReserveN m Ks) F.ϖ F.φ =
      momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) :=
    momentNorm_congr π _ ϖ (fun x => (hfφ x).symm)
  have hnn : 0 ≤ wordTheta ηg letters * X * Real.sqrt CD := by positivity
  have hband : ∫⁻ θ in freqCube, outBandSq π ϖ m Kf (Real.pi / 4) θ
      (fun x => planeValue (u (Fin.last Nw) x (t₀ + S))) ≤
      ENNReal.ofReal ((wordTheta ηg letters * X * Real.sqrt CD) ^ 2) *
        momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) ^ 2 := by
    by_cases hΘ : wordTheta ηg letters = 0
    · -- no endpoint
      have hz := zeroAmplitudeWord K (min g₁Q g₁F) F hΘ
      have hz' : ∀ x, planeValue (u (Fin.last Nw) x (t₀ + S)) =ᵐ[volume] 0 := fun x => by
        have := hz x F.b ⟨F.ordered, le_rfl⟩
        rwa [congrFun hUeq x] at this
      simp only [ffc_outBandSq_eq_zero π ϖ m Kf _ _ hz', lintegral_zero]
      exact zero_le
    calc ∫⁻ θ in freqCube, outBandSq π ϖ m Kf (Real.pi / 4) θ
          (fun x => planeValue (u (Fin.last Nw) x (t₀ + S)))
        ≤ ∫⁻ θ in freqCube, ENNReal.ofReal ((wordTheta ηg letters * X) ^ 2) *
            stageDatumSq F m Ks θ := by
          refine setLIntegral_mono' measurableSet_freqCube fun θ hθ => ?_
          have hterm := ffc_outBandSq_eq_terminal F m Ks Kf (Real.pi / 4) θ hB.hπ hΘ
          rw [hUeq] at hterm
          calc _ = ENNReal.ofReal (wordTheta ηg letters ^ 2) *
                  stageTerminalBandSq F m Ks Kf (Real.pi / 4) θ := hterm
            _ ≤ ENNReal.ofReal (wordTheta ηg letters ^ 2) *
                  (ENNReal.ofReal (X ^ 2) * stageDatumSq F m Ks θ) :=
                mul_le_mul_right (hfib θ hθ) _
            _ = _ := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]
      _ = ENNReal.ofReal ((wordTheta ηg letters * X) ^ 2) *
            ∫⁻ θ in freqCube, stageDatumSq F m Ks θ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((wordTheta ηg letters * X) ^ 2) *
            (ENNReal.ofReal CD * momentNorm F.π (wordReserveN m Ks) F.ϖ F.φ ^ 2) :=
          mul_le_mul_right (hDs (min g₁Q g₁F) F fun l => (hletters l).2.1) _
      _ = _ := by
          rw [hM, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
          congr 2
          rw [mul_pow _ (Real.sqrt CD), Real.sq_sqrt hCD.le]
  calc _ ≤ ENNReal.ofReal CB * ((ENNReal.ofReal (wordTheta ηg letters * X * Real.sqrt CD) *
          momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))) ^ 2) ^
            (1 / 2 : ℝ) := by
        refine mul_le_mul_right (ENNReal.rpow_le_rpow ?_ (by norm_num)) _
        refine hband.trans (le_of_eq ?_)
        rw [mul_pow (ENNReal.ofReal _) _ 2, ← ENNReal.ofReal_pow hnn]
    _ = _ := by
        rw [sq_rpow_half'', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [hXdef]
        ring

/-- The quiet high frequencies. -/
theorem quietHigh : QuietHighStatement.{u, v} :=
  quietHighAssembly (quietHighFibreAssembly plainStage plainKernel stageFamilyZone)
    fullFieldFibre blochOutput BandDatum.stageDatumStatement

end AVRegularity.CycleWords.Discard
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Discard

/-! # `cycle_mixed_words` from the band jets

Every input of `cycle_mixed_words_of_ingredients` is proved except the band jets
(`BandDatum.BandJetStatement`):
* `MarksBandStatement` = `marksBandAssembly` of `marksBandFibre`, the band output
  (`BandDatum.bandOutputStatement_of_steps` of `bandRepStatement`, `bandAmpOutputStatement` and the band
  jets) and the stage datum;
* `ChainFullFieldStatement` = `chainFullField`, `QuietHighStatement` =
  `quietHigh`, `RetainedAmplitudeFactorStatement` = `retainedAmplitudeFactor`.

The theorem `cycle_mixed_words` then reads
`cycle_mixed_words_of_ingredients h.1 h.2.1 h.2.2.1 h.2.2.2 chainFullField K` with
`h = mixedWordsIngredients_of_bandJet hBJ`. -/

open AVRegularity.CycleWords.Assembly

universe u v

/-- **The marks band from the band jets.** -/
theorem marksBand_of_bandJet (hBJ : BandDatum.BandJetStatement.{u, v}) :
    MarksBandStatement.{u, v} :=
  marksBandAssembly marksBandFibre
    (BandDatum.bandOutputStatement_of_steps BandDatum.bandRepStatement BandDatum.bandAmpOutputStatement hBJ)
    BandDatum.stageDatumStatement

/-- **The ingredients of `cycle_mixed_words` from the band jets.** -/
theorem mixedWordsIngredients_of_bandJet (hBJ : BandDatum.BandJetStatement.{u, v}) :
    RetainedMapExistsStatement.{u, v} ∧ RetainedModelJetsStatement.{u, v} ∧
      ChainDiscardStatement.{u, v} ∧ RetainedGaussianStatement.{u, v} :=
  mixedWordsIngredients_of_discard chainFullField quietHigh (marksBand_of_bandJet hBJ)

end AVRegularity.CycleWords.Discard
end
end
