-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.Assembly.SeamStatement
import AVRegularity.CycleJoint.ReferencePhysicalSpatialSmooth
import AVRegularity.CycleComparison.Coarse.Energy.Zero
public import AVRegularity.CycleWords.Assembly.InteriorScalarIngredients
import AVRegularity.CycleWords.MixedWords.TransformBoundSchur
public import AVRegularity.CycleJoint.PlaneH1Average
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! Uniform higher moments upgrade the native continuous trace to every fixed moment. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- At moment order zero the public energy is a continuous finite native quadratic form. -/
private theorem amplitudeId_zero_moment_eq {k : ℕ} (U : PlaneHk Set.univ k E) (ϖ r : ℝ) :
    weightedFactorialNormSq 0 ϖ 0 r k U = ENNReal.ofReal (factorialNormSq r U.val) := by
  rw [Weighted.weightedFactorialNormSq_stored_readout,
    ← CycleJointProofs.storedChartFactorialEnergy_one]
  congr 1

/-- Uniform bounds on a higher polynomial moment make every fixed weighted difference tend to zero. -/
theorem amplitudeId_moment_difference_tendsto {X : Type*} [TopologicalSpace X]
    {k : ℕ} (U : X → PlaneHk Set.univ k E) (s : Set X) (hU : ContinuousOn U s)
    (ϖ r : ℝ) (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ t ∈ s,
      weightedFactorialNormSq n ϖ 0 r k (U t) ≤ ENNReal.ofReal C)
    (n : ℕ) (t₀ : X) (ht₀ : t₀ ∈ s) :
    Tendsto (fun t => weightedFactorialNormSq n ϖ 0 r k (U t - U t₀))
      (𝓝[s] t₀) (𝓝 0) := by
  have hdiff : Tendsto (fun t => (U t - U t₀).val) (𝓝[s] t₀) (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, ZeroMemClass.coe_zero] using
      continuous_subtype_val.continuousAt.tendsto.comp ((hU t₀ ht₀).sub_const (U t₀))
  have hzero : Tendsto (fun t => weightedFactorialNormSq 0 ϖ 0 r k (U t - U t₀))
      (𝓝[s] t₀) (𝓝 0) := by
    simp only [amplitudeId_zero_moment_eq]
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((CycleComparison.Coarse.continuous_factorialNormSq r k).continuousAt.tendsto.comp hdiff)
    simpa only [Function.comp_def, factorialNormSq, derivativeNormSq, PiLp.zero_apply, norm_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, ENNReal.ofReal_zero] using h
  rcases n with _ | n
  · exact hzero
  obtain ⟨C, hC⟩ := hb (2 * (n + 1))
  have hbound (t : X) (ht : t ∈ s) :
      weightedFactorialNormSq (2 * (n + 1)) ϖ 0 r k (U t - U t₀) ≤
        4 * ENNReal.ofReal C := by
    apply (weightedFactorialNormSq_sub_le _ _ _ _ _ _).trans
    calc
      2 * (weightedFactorialNormSq (2 * (n + 1)) ϖ 0 r k (U t) +
          weightedFactorialNormSq (2 * (n + 1)) ϖ 0 r k (U t₀)) ≤
        2 * (ENNReal.ofReal C + ENNReal.ofReal C) := mul_le_mul' le_rfl (add_le_add (hC t ht) (hC t₀ ht₀))
      _ = 4 * ENNReal.ofReal C := by ring
  have hθ : ((n + 1 : ℕ) : ℝ) / ((2 * (n + 1) : ℕ) : ℝ) = 1 / 2 := by
    rw [Nat.cast_mul]
    norm_num
    field_simp
  have hinterp (t : X) :
      weightedFactorialNormSq (n + 1) ϖ 0 r k (U t - U t₀) ≤
        (weightedFactorialNormSq 0 ϖ 0 r k (U t - U t₀)) ^ (1 / 2 : ℝ) *
          (weightedFactorialNormSq (2 * (n + 1)) ϖ 0 r k (U t - U t₀)) ^ (1 / 2 : ℝ) := by
    have h := CycleJointProofs.Assembly.massInterpolation (ι := Unit) (h := fun _ => E)
      (fun _ => 1) (fun _ => k) (fun _ => k) (fun _ => U t - U t₀)
      (n + 1) (2 * (n + 1)) (by omega) (by omega) ϖ 0 r
    simpa only [Fintype.sum_unique, one_mul, hθ, sub_half] using h
  have hlim := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hzero
  have hmul := ENNReal.Tendsto.mul_const (b := (4 * ENNReal.ofReal C) ^ (1 / 2 : ℝ)) hlim
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (ENNReal.mul_ne_top (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) ENNReal.ofReal_ne_top)))
  have hfinal : Tendsto (fun t =>
      (weightedFactorialNormSq 0 ϖ 0 r k (U t - U t₀)) ^ (1 / 2 : ℝ) *
        (4 * ENNReal.ofReal C) ^ (1 / 2 : ℝ)) (𝓝[s] t₀) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2), zero_mul] using hmul
  have hmem : ∀ᶠ t in 𝓝[s] t₀, t ∈ s := self_mem_nhdsWithin
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfinal
    (Eventually.of_forall (fun _ => (bot_le : (0 : ℝ≥0∞) ≤ _)))
    (hmem.mono (fun t ht =>
      (hinterp t).trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hbound t ht) (by norm_num)))))

/-- The weighted value is a summand of the full factorial jet energy. -/
theorem amplitudeId_weighted_value_energy_le {k : ℕ} (V : PlaneHk Set.univ k E)
    (ϖ r : ℝ) (n : ℕ) :
    Weighted.chartScalarEnergy (fun y => (polynomialMomentRoot ϖ y ^ n) ^ 2)
        (Weighted.planeJetReadoutOperator k (valueIndex2 k) V) ≤
      weightedFactorialNormSq n ϖ 0 r k V := by
  let q := fun y => polynomialMomentRoot ϖ y ^ n
  let L := Weighted.planeJetReadoutOperator (E := E) k (valueIndex2 k)
  have hqs : (fun y => q y ^ 2) = Weighted.planeMomentPolynomial n ϖ 0 :=
    funext (fun y => polynomialMomentRoot_pow_sq ϖ y n)
  rw [hqs, Weighted.weightedFactorialNormSq_stored_readout]
  dsimp only [Weighted.storedChartFactorialEnergy, L]
  have h := Finset.single_le_sum
    (f := fun a : JetIndex2 k => ENNReal.ofReal (factorialWeight r a.1.val) *
      Weighted.chartScalarEnergy (Weighted.planeMomentPolynomial n ϖ 0)
        (Weighted.planeJetReadoutOperator k a V))
    (fun _ _ => bot_le) (Finset.mem_univ (valueIndex2 k))
  simpa only [valueIndex2, valueIndex, Fin.val_zero,
    factorialWeight, Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow,
    div_one, ENNReal.ofReal_one, one_mul] using h

/-- The canonical polynomially weighted value readout preserves every continuous native trace. -/
theorem amplitudeId_weighted_trace_continuousOn {X : Type*} [TopologicalSpace X]
    {k : ℕ} (U : X → PlaneHk Set.univ k E) (s : Set X) (hU : ContinuousOn U s)
    (ϖ r : ℝ) (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ t ∈ s,
      weightedFactorialNormSq n ϖ 0 r k (U t) ≤ ENNReal.ofReal C) (n : ℕ) :
    ContinuousOn (fun t => Weighted.weightedPlaneLpReadout
      (fun y => polynomialMomentRoot ϖ y ^ n) ((polynomialMomentRoot_continuous ϖ).pow n)
      (Weighted.planeJetReadoutOperator k (valueIndex2 k) (U t))) s := by
  let q := fun y => polynomialMomentRoot ϖ y ^ n
  have hq : Continuous q := (polynomialMomentRoot_continuous ϖ).pow n
  let L := Weighted.planeJetReadoutOperator (E := E) k (valueIndex2 k)
  let R := fun V : PlaneHk Set.univ k E => Weighted.weightedPlaneLpReadout q hq (L V)
  have henergy (V : PlaneHk Set.univ k E) := amplitudeId_weighted_value_energy_le V ϖ r n
  have hfinite (t : X) (ht : t ∈ s) :
      Weighted.chartScalarEnergy (fun y => q y ^ 2) (L (U t)) ≠ ⊤ := by
    obtain ⟨C, hC⟩ := hb n
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((henergy _).trans (hC t ht))
  intro t₀ ht₀
  have hmem : ∀ᶠ t in 𝓝[s] t₀, t ∈ s := self_mem_nhdsWithin
  have hdiffFinite (t : X) (ht : t ∈ s) :
      Weighted.chartScalarEnergy (fun y => q y ^ 2) (L (U t - U t₀)) ≠ ⊤ := by
    obtain ⟨C, hC⟩ := hb n
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
    exact (henergy _).trans ((weightedFactorialNormSq_sub_le _ _ _ _ _ _).trans
      (mul_le_mul' le_rfl (add_le_add (hC t ht) (hC t₀ ht₀))))
  have hdiff (t : X) (ht : t ∈ s) : R (U t) - R (U t₀) = R (U t - U t₀) := by
    apply Lp.ext
    have hsub : L (U t - U t₀) = L (U t) - L (U t₀) := map_sub L _ _
    filter_upwards [Lp.coeFn_sub (R (U t)) (R (U t₀)),
      Weighted.weightedPlaneLpReadout_ae q hq (L (U t)) (hfinite t ht),
      Weighted.weightedPlaneLpReadout_ae q hq (L (U t₀)) (hfinite t₀ ht₀),
      Weighted.weightedPlaneLpReadout_ae q hq (L (U t - U t₀)) (hdiffFinite t ht),
      Lp.coeFn_sub (L (U t)) (L (U t₀))] with y hy hyt hys hyd hyL
    rw [hy]
    change (Weighted.weightedPlaneLpReadout q hq (L (U t)) : Vec 2 → E) y -
      (Weighted.weightedPlaneLpReadout q hq (L (U t₀)) : Vec 2 → E) y = _
    change _ = (Weighted.weightedPlaneLpReadout q hq (L (U t - U t₀)) : Vec 2 → E) y
    rw [hyt, hys, hyd, hsub, hyL]
    exact (smul_sub (q y) _ _).symm
  have hnorm : Tendsto (fun t => ENNReal.ofReal (‖R (U t) - R (U t₀)‖ ^ 2))
      (𝓝[s] t₀) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (amplitudeId_moment_difference_tendsto U s hU ϖ r hb n t₀ ht₀)
      (Eventually.of_forall (fun _ => bot_le))
    filter_upwards [hmem] with t ht
    rw [hdiff t ht]
    exact (Weighted.weightedPlaneLpReadout_energy q hq (L (U t - U t₀))
      (hdiffFinite t ht)).trans_le (henergy _)
  have hreal : Tendsto (fun t => ‖R (U t) - R (U t₀)‖ ^ 2) (𝓝[s] t₀) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hnorm
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_zero] using h
  have hdist : Tendsto (fun t => dist (R (U t)) (R (U t₀))) (𝓝[s] t₀) (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hreal
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, dist_eq_norm] using h
  exact (tendsto_iff_dist_tendsto_zero).mpr hdist

end AVRegularity.CycleWords.Assembly
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! Polynomial normalization turns Bloch periodization into a bounded map on ordinary L2. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Bounded continuous coefficients preserve the spatial L2 class. -/
theorem amplitudeId_bounded_memLp (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, ‖C y‖ ≤ A) (f : Lp E 2 (volume : Measure (Vec 2))) :
    MemLp (fun y => C y (f y)) 2 volume := by
  apply ((Lp.memLp f).const_smul A).of_le
    ((ContinuousLinearMap.apply ℝ F).flip.aestronglyMeasurable_comp₂
      hC.aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro y
  change ‖C y (f y)‖ ≤ ‖A • f y‖
  rw [norm_smul, Real.norm_of_nonneg hA]
  exact (C y).le_opNorm (f y) |>.trans (mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _))

/-- A continuous bounded operator coefficient acts on actual spatial L2 classes. -/
def amplitudeId_boundedLpOperator (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, ‖C y‖ ≤ A) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp F 2 (volume : Measure (Vec 2)) :=
  variableL2Operator volume C (amplitudeId_bounded_memLp C hC A hA hb) A
    (Filter.Eventually.of_forall (fun y e => (C y).le_opNorm e |>.trans
      (mul_le_mul_of_nonneg_right (hb y) (norm_nonneg e))))

/-- The bounded map has the literal pointwise coefficient readout. -/
theorem amplitudeId_boundedLpOperator_ae (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, ‖C y‖ ≤ A) (f : Lp E 2 (volume : Measure (Vec 2))) :
    amplitudeId_boundedLpOperator C hC A hA hb f =ᵐ[volume] fun y => C y (f y) :=
by
  change variableL2LinearMap volume C (amplitudeId_bounded_memLp C hC A hA hb) f =ᵐ[volume] _
  exact variableL2LinearMap_ae volume C _ f

/-- Its norm is bounded by the same pointwise constant. -/
theorem amplitudeId_boundedLpOperator_norm_le (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, ‖C y‖ ≤ A) (f : Lp E 2 (volume : Measure (Vec 2))) :
    ‖amplitudeId_boundedLpOperator C hC A hA hb f‖ ≤ A * ‖f‖ :=
by
  change ‖variableL2LinearMap volume C (amplitudeId_bounded_memLp C hC A hA hb) f‖ ≤ _
  exact variableL2LinearMap_norm_le volume C _ A
    (Filter.Eventually.of_forall (fun y e => (C y).le_opNorm e |>.trans
      (mul_le_mul_of_nonneg_right (hb y) (norm_nonneg e)))) f

/-- A fourth-order decaying coefficient gives a summable operator norm for every integer image. -/
theorem amplitudeId_decay_image_norm_le (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A)
    (n : Fin 2 → ℤ) :
    ‖(CycleJointProofs.translatedPlaneLpCLM AVenhance.unitCube (AVenhance.latticeShift n)).comp
      (amplitudeId_boundedLpOperator C hC A hA
        (fun y => (le_mul_of_one_le_left (norm_nonneg (C y)) (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg y)))).trans (hb y)))‖ ≤
      (3 ^ 4 * A) * (1 / CycleJointProofs.spatialLatticeWeight n) ^ 2 := by
  let hb₀ := fun y => (le_mul_of_one_le_left (norm_nonneg (C y))
    (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg y)))).trans (hb y)
  let L := amplitudeId_boundedLpOperator C hC A hA hb₀
  let W := fun y : Vec 2 => (1 + ‖y‖) ^ 4 • C y
  have hW : Continuous W := (by fun_prop : Continuous (fun y : Vec 2 => (1 + ‖y‖) ^ 4)).smul hC
  have hbW (y : Vec 2) : ‖W y‖ ≤ A := by
    simpa only [W, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + ‖y‖) ^ 4)] using hb y
  let LW := amplitudeId_boundedLpOperator W hW A hA hbW
  have hpoint (f : Lp E 2 (volume : Measure (Vec 2))) :
      ‖CycleJointProofs.translatedPlaneLpCLM AVenhance.unitCube
        (AVenhance.latticeShift n) (L f)‖ ≤
        ((3 : ℝ) ^ 4 * A) * (1 / CycleJointProofs.spatialLatticeWeight n) ^ 2 * ‖f‖ := by
    have hew : LW f =ᵐ[volume] fun y => (1 + ‖y‖) ^ 4 • L f y := by
      filter_upwards [amplitudeId_boundedLpOperator_ae W hW A hA hbW f,
        amplitudeId_boundedLpOperator_ae C hC A hA hb₀ f] with y hy hz
      rw [hy, hz]
      rfl
    have he := (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume
        CycleJointProofs.unitCube_subset_ball_two)).trans
      (CycleJointProofs.radialMoment_image_eLpNorm_le (L f) 0 2 (by norm_num)
        (Lp.memLp _).aestronglyMeasurable
        (by simpa only [sub_zero] using (Lp.memLp (LW f)).aestronglyMeasurable.congr hew) n)
    have heimage := CycleJointProofs.translatedPlaneLpCLM_ae AVenhance.unitCube
      (AVenhance.latticeShift n) (L f)
    rw [← eLpNorm_congr_ae heimage] at he
    simp only [sub_zero] at he
    rw [← eLpNorm_congr_ae hew] at he
    have hreal := ENNReal.toReal_mono (by finiteness) he
    rw [ENNReal.toReal_mul, ← Lp.norm_def, ← Lp.norm_def,
      ENNReal.toReal_ofReal (by positivity)] at hreal
    simp only [norm_zero, add_zero] at hreal
    have hnorm := amplitudeId_boundedLpOperator_norm_le W hW A hA hbW f
    calc
      _ ≤ (1 + 2 : ℝ) ^ 4 * (1 / CycleJointProofs.spatialLatticeWeight n) ^ 2 * ‖LW f‖ := hreal
      _ ≤ (1 + 2 : ℝ) ^ 4 * (1 / CycleJointProofs.spatialLatticeWeight n) ^ 2 * (A * ‖f‖) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = _ := by norm_num; ring
  exact ((CycleJointProofs.translatedPlaneLpCLM AVenhance.unitCube
    (AVenhance.latticeShift n)).comp L).opNorm_le_bound (by positivity) hpoint

/-- Decay bounds imply the ordinary uniform coefficient bound. -/
theorem amplitudeId_decay_coefficient_le (C : Vec 2 → E →L[ℝ] F)
    (A : ℝ) (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A) (y : Vec 2) : ‖C y‖ ≤ A :=
  (le_mul_of_one_le_left (norm_nonneg (C y))
    (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg y)))).trans (hb y)

/-- A single integer image of a decaying continuous coefficient. -/
def amplitudeId_decayImage (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A)
    (n : Fin 2 → ℤ) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp F 2 (volume.restrict AVenhance.unitCube) :=
  (CycleJointProofs.translatedPlaneLpCLM AVenhance.unitCube (AVenhance.latticeShift n)).comp
    (amplitudeId_boundedLpOperator C hC A hA (amplitudeId_decay_coefficient_le C A hb))

/-- The integer-image operator norms are summable. -/
theorem amplitudeId_decayImage_summable_norm (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A) :
    Summable (fun n : Fin 2 → ℤ => ‖amplitudeId_decayImage C hC A hA hb n‖) := by
  exact Summable.of_nonneg_of_le (fun n => (amplitudeId_decayImage C hC A hA hb n).opNorm_nonneg)
    (fun n => amplitudeId_decay_image_norm_le C hC A hA hb n)
    (CycleJointProofs.spatialLatticeReciprocal_square_summable.mul_left (3 ^ 4 * A))

variable [CompleteSpace F]

/-- Periodization of a decaying operator coefficient is a bounded map on plane L2. -/
def amplitudeId_decayPeriodizeCLM (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp F 2 (volume.restrict AVenhance.unitCube) :=
  ∑' n : Fin 2 → ℤ, amplitudeId_decayImage C hC A hA hb n

/-- The bounded periodization map reads the literal integer-image series almost everywhere. -/
theorem amplitudeId_decayPeriodizeCLM_readout (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A)
    (f : Lp E 2 (volume : Measure (Vec 2))) :
    (amplitudeId_decayPeriodizeCLM C hC A hA hb f =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => ∑' n : Fin 2 → ℤ, C (z + AVenhance.latticeShift n) (f (z + AVenhance.latticeShift n))) ∧
    ∀ᵐ z ∂volume.restrict AVenhance.unitCube,
      Summable (fun n : Fin 2 → ℤ => ‖C (z + AVenhance.latticeShift n) (f (z + AVenhance.latticeShift n))‖) := by
  let L := amplitudeId_boundedLpOperator C hC A hA (amplitudeId_decay_coefficient_le C A hb)
  let I := amplitudeId_decayImage C hC A hA hb
  have hsum := amplitudeId_decayImage_summable_norm C hC A hA hb
  have hi : (∑' n, ‖I n f‖ₑ) < ⊤ := by
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_))
      ((hsum.mul_right ‖f‖).tsum_ofReal_lt_top)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((I n).le_opNorm f)
  have hread (n : Fin 2 → ℤ) : I n f =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => C (z + AVenhance.latticeShift n) (f (z + AVenhance.latticeShift n)) := by
    have hp := amplitudeId_boundedLpOperator_ae C hC A hA
      (amplitudeId_decay_coefficient_le C A hb) f
    have ht := ((measurePreserving_add_right volume (AVenhance.latticeShift n)).quasiMeasurePreserving.ae_eq_comp hp).restrict (s := AVenhance.unitCube)
    exact (CycleJointProofs.translatedPlaneLpCLM_ae AVenhance.unitCube
      (AVenhance.latticeShift n) (L f)).trans ht
  have hliteral : (∑' n : Fin 2 → ℤ,
      eLpNorm (fun z => C (z + AVenhance.latticeShift n) (f (z + AVenhance.latticeShift n))) 2
        (volume.restrict AVenhance.unitCube)) < ⊤ := by
    have he : (fun n : Fin 2 → ℤ =>
        eLpNorm (fun z => C (z + AVenhance.latticeShift n) (f (z + AVenhance.latticeShift n))) 2
          (volume.restrict AVenhance.unitCube)) = fun n => ‖I n f‖ₑ := by
      funext n
      rw [Lp.enorm_def, eLpNorm_congr_ae (hread n)]
    rw [he]
    exact hi
  refine ⟨?_, (CycleEvolution.cellLpSeries_memLp_bound _ _ hliteral).2.2⟩
  have hcoe := Lp.coeFn_tsum (f := fun n => I n f) hi.ne
  have hall := ae_all_iff.mpr hread
  change ((∑' n, I n) f : Vec 2 → F) =ᵐ[_] _
  have hoperators : Summable I := Summable.of_norm (f := I) hsum
  have hmap := (ContinuousLinearMap.apply ℝ
    (Lp F 2 (volume.restrict AVenhance.unitCube)) f).map_tsum hoperators
  simp only [ContinuousLinearMap.apply_apply] at hmap
  rw [hmap]
  filter_upwards [hcoe, hall] with z hz hh
  exact hz.trans (tsum_congr (fun n => hh n))

omit [CompleteSpace F] in
/-- A coefficient with polynomial growth becomes radially decaying after normalization. -/
theorem amplitudeId_normalized_decay (q : Vec 2 → ℝ) (hq0 : ∀ y, 0 < q y)
    (C : Vec 2 → E →L[ℝ] F) (A : ℝ)
    (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A * q y) (y : Vec 2) :
    (1 + ‖y‖) ^ 4 * ‖(q y)⁻¹ • C y‖ ≤ A := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hq0 y).le)]
  calc
    _ = (q y)⁻¹ * ((1 + ‖y‖) ^ 4 * ‖C y‖) := by ring
    _ ≤ (q y)⁻¹ * (A * q y) :=
      mul_le_mul_of_nonneg_left (hb y) (inv_nonneg.mpr (hq0 y).le)
    _ = A := by rw [mul_left_comm, inv_mul_cancel₀ (hq0 y).ne', mul_one]

/-- Bounded periodization of a coefficient on a polynomially weighted input. -/
def amplitudeId_weightedPeriodizeCLM (q : Vec 2 → ℝ) (hq : Continuous q)
    (hq0 : ∀ y, 0 < q y) (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A * q y) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp F 2 (volume.restrict AVenhance.unitCube) :=
  amplitudeId_decayPeriodizeCLM (fun y => (q y)⁻¹ • C y)
    ((hq.inv₀ (fun y => (hq0 y).ne')).smul hC) A hA
    (amplitudeId_normalized_decay q hq0 C A hb)

/-- The coefficient norm is bounded by the monomial times the tested vector norm. -/
theorem amplitudeId_momentCoefficient_norm_le (θ : Vec 2) (β : ℕ × ℕ) (e : E) (y : Vec 2) :
    ‖amplitudeId_momentCoefficient θ β e y‖ ≤ |momentWeight β y| * ‖e‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
  intro z
  change ‖(Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (momentWeight β y : ℂ)) *
    (inner ℝ e z : ℂ)‖ ≤ _
  rw [norm_mul, norm_mul, norm_planePhase, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm e z) (abs_nonneg _)

/-- A fixed polynomial moment coefficient satisfies the normalized fourth-decay bound. -/
theorem amplitudeId_momentCoefficient_growth (θ : Vec 2) (β : ℕ × ℕ) (e : E)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (y : Vec 2) :
    (1 + ‖y‖) ^ 4 * ‖amplitudeId_momentCoefficient θ β e y‖ ≤
      ((2 + (ϖ ^ 2)⁻¹) ^ (β.1 + β.2 + 4) * ‖e‖) *
        polynomialMomentRoot ϖ y ^ (2 * (β.1 + β.2 + 4)) := by
  let d := β.1 + β.2
  let B := 2 + (ϖ ^ 2)⁻¹
  let W := 1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)
  have hx (i : Fin 2) : |y i| ≤ 1 + ‖y‖ :=
    (norm_le_pi_norm y i).trans (le_add_of_nonneg_left zero_le_one)
  have hm : |momentWeight β y| ≤ (1 + ‖y‖) ^ d := by
    simp only [momentWeight, abs_mul, abs_pow]
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hx 0) β.1)
      (pow_le_pow_left₀ (abs_nonneg _) (hx 1) β.2) (by positivity) (by positivity)
  have hr : (1 + ‖y‖) ^ (d + 4) ≤ B ^ (d + 4) * W ^ (d + 4) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity)
      (amplitudeId_radial_weight_bound ϖ hϖ y) (d + 4)
  have hroot : polynomialMomentRoot ϖ y ^ (2 * (d + 4)) = W ^ (d + 4) := by
    rw [pow_mul, polynomialMomentRoot, Real.sq_sqrt (by positivity)]
  rw [hroot]
  calc
    _ ≤ (1 + ‖y‖) ^ 4 * (|momentWeight β y| * ‖e‖) :=
      mul_le_mul_of_nonneg_left (amplitudeId_momentCoefficient_norm_le θ β e y) (by positivity)
    _ ≤ (1 + ‖y‖) ^ 4 * ((1 + ‖y‖) ^ d * ‖e‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm (norm_nonneg _)) (by positivity)
    _ = (1 + ‖y‖) ^ (d + 4) * ‖e‖ := by rw [pow_add]; ring
    _ ≤ (B ^ (d + 4) * W ^ (d + 4)) * ‖e‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    _ = _ := by ring

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The normalization cancels on the actual finite-energy weighted readout. -/
theorem amplitudeId_weightedPeriodizeCLM_readout (q : Vec 2 → ℝ) (hq : Continuous q)
    (hq0 : ∀ y, 0 < q y) (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ y, (1 + ‖y‖) ^ 4 * ‖C y‖ ≤ A * q y)
    (U : Lp E 2 (volume : Measure (Vec 2)))
    (he : Weighted.chartScalarEnergy (fun y => q y ^ 2) U ≠ ⊤) :
    (amplitudeId_weightedPeriodizeCLM q hq hq0 C hC A hA hb
      (Weighted.weightedPlaneLpReadout q hq U) =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => ∑' n : Fin 2 → ℤ, C (z + AVenhance.latticeShift n) (U (z + AVenhance.latticeShift n))) ∧
    ∀ᵐ z ∂volume.restrict AVenhance.unitCube,
      Summable (fun n : Fin 2 → ℤ => ‖C (z + AVenhance.latticeShift n) (U (z + AVenhance.latticeShift n))‖) := by
  have hn := amplitudeId_decayPeriodizeCLM_readout (fun y => (q y)⁻¹ • C y)
    ((hq.inv₀ (fun y => (hq0 y).ne')).smul hC) A hA
    (amplitudeId_normalized_decay q hq0 C A hb) (Weighted.weightedPlaneLpReadout q hq U)
  have hw := Weighted.weightedPlaneLpReadout_ae q hq U he
  have hshift (n : Fin 2 → ℤ) := ((measurePreserving_add_right volume (AVenhance.latticeShift n)).quasiMeasurePreserving.ae_eq_comp hw).restrict (s := AVenhance.unitCube)
  have heq : ∀ᵐ z ∂volume.restrict AVenhance.unitCube, ∀ n : Fin 2 → ℤ,
      ((q (z + AVenhance.latticeShift n))⁻¹ • C (z + AVenhance.latticeShift n))
        (Weighted.weightedPlaneLpReadout q hq U (z + AVenhance.latticeShift n)) =
      C (z + AVenhance.latticeShift n) (U (z + AVenhance.latticeShift n)) := by
    filter_upwards [ae_all_iff.mpr hshift] with z hh
    simp only [Function.comp_def] at hh
    intro n
    rw [hh n]
    simp only [smul_apply, map_smul, smul_smul, mul_inv_cancel₀ (hq0 _).ne', one_smul]
  refine ⟨hn.1.trans (heq.mono (fun _ hh => tsum_congr hh)), ?_⟩
  filter_upwards [hn.2, heq] with z hs hh
  exact hs.congr (fun n => congrArg norm (hh n))

/-- The canonical cell readout of one phase-weighted monomial coordinate. -/
def amplitudeId_momentBlochReadout (ϖ : ℝ) (hϖ : 0 < ϖ)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (U : Lp E 2 (volume : Measure (Vec 2))) :
    CycleEvolution.ComplexCellL2 :=
  let n := 2 * (β.1 + β.2 + 4)
  let q := fun y => polynomialMomentRoot ϖ y ^ n
  let hq := (polynomialMomentRoot_continuous ϖ).pow n
  let hq0 := fun y => pow_pos (lt_of_lt_of_le zero_lt_one (polynomialMomentRoot_one_le ϖ y)) n
  let A := (2 + (ϖ ^ 2)⁻¹) ^ (β.1 + β.2 + 4) * ‖e‖
  let hA : 0 ≤ A := by dsimp only [A]; positivity
  amplitudeId_weightedPeriodizeCLM q hq hq0 (amplitudeId_momentCoefficient θ β e)
    (amplitudeId_momentCoefficient_contDiff θ β e).continuous A hA
    (amplitudeId_momentCoefficient_growth θ β e ϖ hϖ)
    (Weighted.weightedPlaneLpReadout q hq U)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The readout gives the literal Bloch sum with absolutely summable image terms. -/
theorem amplitudeId_momentBlochReadout_readout (ϖ : ℝ) (hϖ : 0 < ϖ)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (U : Lp E 2 (volume : Measure (Vec 2)))
    (he : Weighted.chartScalarEnergy
      (fun y => (polynomialMomentRoot ϖ y ^ (2 * (β.1 + β.2 + 4))) ^ 2) U ≠ ⊤) :
    (amplitudeId_momentBlochReadout ϖ hϖ θ β e U =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight β y * inner ℝ e (U y))) ∧
    ∀ᵐ z ∂volume.restrict AVenhance.unitCube, Summable (fun j : Fin 2 → ℤ =>
      ‖Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift j) : ℂ))) *
        ((momentWeight β (z + AVenhance.latticeShift j) *
          inner ℝ e (U (z + AVenhance.latticeShift j)) : ℝ) : ℂ)‖) := by
  let n := 2 * (β.1 + β.2 + 4)
  let q := fun y => polynomialMomentRoot ϖ y ^ n
  have hq : Continuous q := (polynomialMomentRoot_continuous ϖ).pow n
  have hq0 (y : Vec 2) : 0 < q y := pow_pos
    (lt_of_lt_of_le zero_lt_one (polynomialMomentRoot_one_le ϖ y)) n
  let A := (2 + (ϖ ^ 2)⁻¹) ^ (β.1 + β.2 + 4) * ‖e‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have h := amplitudeId_weightedPeriodizeCLM_readout q hq hq0
    (amplitudeId_momentCoefficient θ β e) (amplitudeId_momentCoefficient_contDiff θ β e).continuous
    A hA (amplitudeId_momentCoefficient_growth θ β e ϖ hϖ) U he
  have hv (y : Vec 2) (v : E) : amplitudeId_momentCoefficient θ β e y v =
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * ((momentWeight β y * inner ℝ e v : ℝ) : ℂ) := by
    simp only [amplitudeId_momentCoefficient, smul_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with z hz
    exact hz.trans (tsum_congr (fun j => hv _ _))
  · simpa only [hv] using h.2

variable [FiniteDimensional ℝ E]

omit [BorelSpace E] [CompleteSpace E] in
/-- A native L2 time curve with the required moment supplies its literal cell moment curve. -/
theorem amplitudeId_momentBlochReadout_time (ϖ : ℝ) (hϖ : 0 < ϖ)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (μ : Measure ℝ)
    (U : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hU : MemLp U 2 μ)
    (he : (∫⁻ t, Weighted.chartScalarEnergy
      (fun y => (polynomialMomentRoot ϖ y ^ (2 * (β.1 + β.2 + 4))) ^ 2) (U t) ∂μ) ≠ ⊤) :
    MemLp (fun t => amplitudeId_momentBlochReadout ϖ hϖ θ β e (U t)) 2 μ ∧
      ∀ᵐ t ∂μ, amplitudeId_momentBlochReadout ϖ hϖ θ β e (U t) =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y => momentWeight β y * inner ℝ e (U t y)) := by
  let n := 2 * (β.1 + β.2 + 4)
  let q := fun y => polynomialMomentRoot ϖ y ^ n
  have hq : Continuous q := (polynomialMomentRoot_continuous ϖ).pow n
  have hq0 (y : Vec 2) : 0 < q y := pow_pos
    (lt_of_lt_of_le zero_lt_one (polynomialMomentRoot_one_le ϖ y)) n
  have hw := Weighted.weightedPlaneLpReadout_time_memLp q hq hq0 μ U hU he
  let A := (2 + (ϖ ^ 2)⁻¹) ^ (β.1 + β.2 + 4) * ‖e‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let P := amplitudeId_weightedPeriodizeCLM q hq hq0 (amplitudeId_momentCoefficient θ β e)
    (amplitudeId_momentCoefficient_contDiff θ β e).continuous A hA
    (amplitudeId_momentCoefficient_growth θ β e ϖ hϖ)
  refine ⟨P.comp_memLp' hw, ?_⟩
  have hm := Weighted.chartScalarEnergy_stationary_time_aemeasurable
    (fun y => q y ^ 2) (hq.pow 2) (fun y => sq_pos_of_pos (hq0 y)) μ U hU
  filter_upwards [ae_lt_top' hm he] with t ht
  exact (amplitudeId_momentBlochReadout_readout ϖ hϖ θ β e (U t) ht.ne).1

omit [FiniteDimensional ℝ E] in

/-- Every moment Bloch value has a continuous cell L2 trace, at every frequency. -/
theorem amplitudeId_moment_bloch_trace {X : Type*} [TopologicalSpace X]
    {k : ℕ} (U : X → PlaneHk Set.univ k E) (s : Set X) (hU : ContinuousOn U s)
    (ϖ r : ℝ) (hϖ : 0 < ϖ) (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ t ∈ s,
      weightedFactorialNormSq n ϖ 0 r k (U t) ≤ ENNReal.ofReal C)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) :
    ∃ L : X → CycleEvolution.ComplexCellL2, ContinuousOn L s ∧
      ∀ t ∈ s, L t =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (U t) y)) := by
  let n := 2 * (β.1 + β.2 + 4)
  let q := fun y => polynomialMomentRoot ϖ y ^ n
  have hq : Continuous q := (polynomialMomentRoot_continuous ϖ).pow n
  have hq0 (y : Vec 2) : 0 < q y := pow_pos (lt_of_lt_of_le zero_lt_one (polynomialMomentRoot_one_le ϖ y)) n
  let A := (2 + (ϖ ^ 2)⁻¹) ^ (β.1 + β.2 + 4) * ‖e‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC := (amplitudeId_momentCoefficient_contDiff θ β e).continuous
  have hg := amplitudeId_momentCoefficient_growth θ β e ϖ hϖ
  let P := amplitudeId_weightedPeriodizeCLM q hq hq0 (amplitudeId_momentCoefficient θ β e) hC A hA hg
  let R := fun t => Weighted.weightedPlaneLpReadout q hq
    (Weighted.planeJetReadoutOperator k (valueIndex2 k) (U t))
  refine ⟨fun t => P (R t), P.continuous.comp_continuousOn
    (amplitudeId_weighted_trace_continuousOn U s hU ϖ r hb n), ?_⟩
  intro t ht
  have hfinite : Weighted.chartScalarEnergy (fun y => q y ^ 2)
      (Weighted.planeJetReadoutOperator k (valueIndex2 k) (U t)) ≠ ⊤ := by
    obtain ⟨C, hC⟩ := hb n
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((amplitudeId_weighted_value_energy_le (U t) ϖ r n).trans (hC t ht))
  have hp := (amplitudeId_weightedPeriodizeCLM_readout q hq hq0
    (amplitudeId_momentCoefficient θ β e) hC A hA hg _ hfinite).1
  have hv : Weighted.planeJetReadoutOperator k (valueIndex2 k) (U t) =ᵐ[volume]
      planeValue (U t) := by
    filter_upwards [Analysis.Convolution.univToPlane_ae ((U t).val (valueIndex2 k))] with y hy
    change Analysis.Convolution.univToPlane ((U t).val (valueIndex2 k)) y = _
    rw [hy, planeValue_eq_stored]
  have hshift (j : Fin 2 → ℤ) := ((measurePreserving_add_right volume (AVenhance.latticeShift j)).quasiMeasurePreserving.ae_eq_comp hv).restrict (s := AVenhance.unitCube)
  filter_upwards [hp, ae_all_iff.mpr hshift] with z hz hh
  exact hz.trans (tsum_congr (fun j => by
    simp only [Function.comp_def] at hh
    rw [hh j]
    simp only [amplitudeId_momentCoefficient, smul_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul, Complex.ofReal_mul,
      mul_assoc]
    rfl))

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # the same-level transform bound, assembled from pairwise operators

`SameLevelTransformBoundStatement` is reduced to `SameLevelOpsStatement`: for every pair
of stages `(i, i')` there is a bounded real-linear map `T_{i,i'} : H^N → H^n` of the torus whose
value is the scaled classical transform, with `‖T_{i,i'}‖ ≤ C₀` when `i, i'` are related by one of
the five shifts of the moment and `T_{i,i'} = 0` otherwise.  The output is
`Φ_{i'} = ∑_{i ∈ stage k} T_{i,i'} ψ_i`; the bound is the Schur test (`elem_schur`) with the
fibre counts `≤ 5` of the relation (`sameRel_card_left`, `sameRel_card_right`). -/

section
universe u v

section Index

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Nw m : ℕ} {Ks : Fin Nw → ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- A stage is determined by its level, component, moment and the value of its basis index. -/
theorem b1w_ext {i j : B1WIndex ι h Nw m Ks} (h1 : i.1 = j.1) (h2 : i.2.1 = j.2.1)
    (h3 : b1wMom i = b1wMom j) (h4 : i.2.2.2.val = j.2.2.2.val) : i = j := by
  obtain ⟨a, x, ⟨β, hβ⟩, b⟩ := i
  obtain ⟨a', x', ⟨β', hβ'⟩, b'⟩ := j
  simp only [b1wMom] at h1 h2 h3 h4
  subst h1 h2 h3
  have : b = b' := Fin.ext h4
  subst this
  rfl

/-- The five moment shifts of the same-level transform. -/
def sameShifts : Finset (ℕ × ℕ) := {(2, 0), (1, 1), (0, 2), (1, 0), (0, 1)}

theorem sameShifts_card : sameShifts.card = 5 := by decide

/-- The stages related by a same-level shift: same level, component and basis index, and the
moment of `i` is that of `i'` plus one of the five shifts. -/
def SameRel (i i' : B1WIndex ι h Nw m Ks) : Prop :=
  i.1 = i'.1 ∧ i.2.1 = i'.2.1 ∧ i.2.2.2.val = i'.2.2.2.val ∧
    ∃ s ∈ sameShifts, b1wMom i = ((b1wMom i').1 + s.1, (b1wMom i').2 + s.2)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
open Classical in
theorem sameRel_card_left (i' : B1WIndex ι h Nw m Ks) :
    (Finset.univ.filter fun i : B1WIndex ι h Nw m Ks => SameRel i i').card ≤ 5 := by
  refine (Finset.card_le_card_of_injOn b1wMom (t := sameShifts.image fun s =>
    ((b1wMom i').1 + s.1, (b1wMom i').2 + s.2)) ?_ ?_).trans
    (Finset.card_image_le.trans sameShifts_card.le)
  · intro i hi
    obtain ⟨-, -, -, s, hs, hm⟩ := (Finset.mem_filter.1 hi).2
    exact Finset.mem_image.2 ⟨s, hs, hm.symm⟩
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    exact b1w_ext (hi.1.trans hj.1.symm) (hi.2.1.trans hj.2.1.symm) hij
      (hi.2.2.1.trans hj.2.2.1.symm)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
open Classical in
theorem sameRel_card_right (i : B1WIndex ι h Nw m Ks) :
    (Finset.univ.filter fun i' : B1WIndex ι h Nw m Ks => SameRel i i').card ≤ 5 := by
  refine (Finset.card_le_card_of_injOn b1wMom (t := sameShifts.image fun s =>
    ((b1wMom i).1 - s.1, (b1wMom i).2 - s.2)) ?_ ?_).trans
    (Finset.card_image_le.trans sameShifts_card.le)
  · intro i' hi'
    obtain ⟨-, -, -, s, hs, hm⟩ := (Finset.mem_filter.1 hi').2
    refine Finset.mem_image.2 ⟨s, hs, ?_⟩
    rw [hm]
    simp
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    exact b1w_ext (hi.1.symm.trans hj.1) (hi.2.1.symm.trans hj.2.1) hij
      (hi.2.2.1.symm.trans hj.2.2.1)

end Index

/-- A finite sum of almost-everywhere representations. -/
theorem torusHk_value_sum_ae {n : ℕ} {J : Type*} (s : Finset J) (U : J → TorusHk n ℂ)
    (f : J → Vec 2 → ℂ)
    (hf : ∀ j ∈ s, (torusHkValueCLM (U j) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] f j) :
    (torusHkValueCLM (∑ j ∈ s, U j) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun z => ∑ j ∈ s, f j z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, map_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with z hz
    simpa using hz
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, map_add]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    filter_upwards [Lp.coeFn_add (torusHkValueCLM (U a)) (torusHkValueCLM (∑ j ∈ s, U j)), h1, h2]
      with z hz hz1 hz2
    rw [hz, Finset.sum_insert ha]
    simp only [Pi.add_apply, hz1, hz2]

open Classical in
/-- **pairwise same-level operators.** For every pair of stages there is a
bounded real-linear map `H^N → H^n` whose value is `(c_i/c_{i'}) conj T^{same}_{i,i'}(conj ψ̃)`,
of norm at most `C₀` when `i, i'` are related by one of the five shifts and `0` otherwise
(then the map is `0`: the coefficient vanishes, or the component or basis index differs). It is
built from the maps `truncate`, multiplication by the real coefficient `√η v` (with `ϖ ≤ √η`) and
the twisted derivatives `∂_k + iθ_k`. -/
def SameLevelOpsStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (ρ : ℝ) (n : ℕ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ k, |θ k| ≤ ρ) →
  ∀ r ∈ Icc F.a F.b, ∀ (N : ℕ), n + 1 ≤ N → (Finset.univ.sup d) + 3 ≤ N →
  ∀ i i' : B1WIndex ι h Nw m Ks,
    ∃ T : TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
      ‖T‖ ≤ (if SameRel i i' then C0 else 0) ∧
      ∀ ψ : TorusHk N ℂ, (torusHkValueCLM (T ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wSameTransform θ (F.G r) (F.v r) i i'
              (fun y => star (torusHigherClassicalValue N ψ y)) z)

open Classical in
/-- **Assembly of the same-level bound** from the pairwise operators (Schur test with fibre
counts `5`). -/
theorem sameLevelTransformBoundZone_of_ops (hO : SameLevelOpsStatement.{u, v}) :
    SameLevelTransformBoundZoneStatement.{u, v} := by
  intro K Nw D m d Ks ρ n
  obtain ⟨C0, hC0, hC⟩ := hO K Nw D m d Ks ρ n
  refine ⟨5 * C0, by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hρ r hr k k' _hlev N hnN hdN ψ
  have hT := fun i i' => hC g₁ F θ hρ r hr N hnN hdN i i'
  choose T hTn hTv using hT
  refine ⟨fun i' => if i' ∈ stageSet b1wSt k' then ∑ i ∈ stageSet b1wSt k, T i i' (ψ i) else 0,
    ?_, ?_⟩
  · intro i' hi'
    simp only [hi', ↓reduceIte]
    exact torusHk_value_sum_ae (stageSet b1wSt k) (fun i => T i i' (ψ i)) _
      (fun i _ => hTv i i' (ψ i))
  · have hw0 : ∀ i i' : B1WIndex ι h Nw m Ks, 0 ≤ (if SameRel i i' then C0 else 0) := by
      intro i i'
      split_ifs <;> simp [hC0]
    have hcount : ∀ (S : Finset (B1WIndex ι h Nw m Ks)) (P : B1WIndex ι h Nw m Ks → Prop),
        (Finset.univ.filter P).card ≤ 5 → ∑ x ∈ S, (if P x then C0 else 0) ≤ 5 * C0 := by
      intro S P hP
      calc ∑ x ∈ S, (if P x then C0 else 0) ≤ ∑ x, (if P x then C0 else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => by
              split_ifs <;> simp [hC0]
        _ = (Finset.univ.filter P).card * C0 := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ 5 * C0 := mul_le_mul_of_nonneg_right (by exact_mod_cast hP) hC0
    have key := elem_schur (stageSet b1wSt k) (stageSet b1wSt k')
      (fun i i' => T i i' (ψ i)) (fun i i' => if SameRel i i' then C0 else 0) (fun i => ‖ψ i‖)
      hw0 (fun i _ i' _ => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hTn i i') (norm_nonneg _)))
      (A := 5 * C0) (B := 5 * C0)
      (fun i _ => hcount _ (fun i' => SameRel i i') (sameRel_card_right i))
      (fun i' _ => hcount _ (fun i => SameRel i i') (sameRel_card_left i')) (by positivity)
    calc ∑ i' ∈ stageSet b1wSt k', ‖(if i' ∈ stageSet b1wSt k' then
            ∑ i ∈ stageSet b1wSt k, T i i' (ψ i) else 0)‖ ^ 2
        = ∑ i' ∈ stageSet b1wSt k', ‖∑ i ∈ stageSet b1wSt k, T i i' (ψ i)‖ ^ 2 :=
          Finset.sum_congr rfl fun i' hi' => by simp only [hi', ↓reduceIte]
      _ ≤ 5 * C0 * (5 * C0) * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 := key
      _ = (5 * C0) ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 := by ring
end

/-! # the letter transform bound, assembled from block operators

`LetterTransformBoundAEStatement` is reduced to `LetterOpsStatement`: for a letter `l`
there are bounded real-linear maps `T_{i,i'} : H^N → H^n` (`i` at level `l + 1`, `i'` at level `l`)
whose values are the scaled classical transforms, and whose blocks over the basis indices (the
stages with the same component and moment) obey the Parseval-type bound
`∑_{i'} ‖∑_i T_{i,i'} f_i‖² ≤ (C₀ κ(β,β') w_l(x,x'))² ∑_i ‖f_i‖²`, with `κ` the indicator of a
bounded moment shift and `w_l(x,x') = majorant(x,x')/θ_l` (`0` if `θ_l = 0`).  The output is
`Φ_{i'} = ∑_{i ∈ stage k} T_{i,i'} ψ_i`; the bound is the Schur test over the pairs
`(component, moment)` (row and column sums of `w_l` are `≤ 1`, shift counts `≤ (S+D+1)²`). -/

section
universe u v

/-- The relation `β → β'` of moments: `β'` is at most `S` above and `D` below `β`. -/
def LetterMomRel (S D : ℕ) (β β' : ℕ × ℕ) : Prop :=
  β'.1 ≤ β.1 + S ∧ β.1 ≤ β'.1 + D ∧ β'.2 ≤ β.2 + S ∧ β.2 ≤ β'.2 + D

instance (S D : ℕ) (β β' : ℕ × ℕ) : Decidable (LetterMomRel S D β β') := by
  unfold LetterMomRel; infer_instance

/-- The component weight `majorant(x,x')/θ` of a letter (`0` if `θ = 0`). -/
def letterCompWeight {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (L : CycleLetter ι h D) (x x' : ι) : ℝ :=
  if L.theta = 0 then 0 else L.majorant x x' / L.theta

/-- The `(component, moment)` key of a stage. -/
def b1wKey {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}
    (i : B1WIndex ι h Nw m Ks) : ι × (ℕ × ℕ) := (i.2.1, i.2.2.1.1)

theorem card_box_le (S D : ℕ) (a b : ℕ) :
    ((Finset.Icc (a - D) (a + S)) ×ˢ (Finset.Icc (b - D) (b + S))).card ≤ (S + D + 1) ^ 2 := by
  rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc, sq]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- Row sums of the moment relation against a nonnegative component weight. -/
theorem letterMom_row {ι : Type*} [Fintype ι] (S D : ℕ) (β : ℕ × ℕ)
    (S' : Finset (ι × (ℕ × ℕ))) (c : ι → ℝ) (hc : ∀ x, 0 ≤ c x) :
    ∑ g' ∈ S', (if LetterMomRel S D β g'.2 then 1 else 0) * c g'.1 ≤
      (((S + D + 1) ^ 2 : ℕ) : ℝ) * ∑ x, c x := by
  classical
  calc ∑ g' ∈ S', (if LetterMomRel S D β g'.2 then 1 else 0) * c g'.1
      = ∑ g' ∈ S'.filter (fun g' => LetterMomRel S D β g'.2), c g'.1 := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun g' _ => by split_ifs <;> simp
    _ ≤ ∑ g' ∈ (Finset.univ : Finset ι) ×ˢ ((Finset.Icc (β.1 - D) (β.1 + S)) ×ˢ
          (Finset.Icc (β.2 - D) (β.2 + S))), c g'.1 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun g' _ _ => hc _
        intro g' hg'
        obtain ⟨hg'S, hrel⟩ := Finset.mem_filter.1 hg'
        obtain ⟨h1, h2, h3, h4⟩ := hrel
        simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
        omega
    _ = ((Finset.Icc (β.1 - D) (β.1 + S)) ×ˢ (Finset.Icc (β.2 - D) (β.2 + S))).card *
          ∑ x, c x := by
        rw [Finset.sum_product]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
    _ ≤ (((S + D + 1) ^ 2 : ℕ) : ℝ) * ∑ x, c x := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun x _ => hc x)
        exact_mod_cast card_box_le S D β.1 β.2

/-- Column sums of the moment relation against a nonnegative component weight. -/
theorem letterMom_col {ι : Type*} [Fintype ι] (S D : ℕ) (β' : ℕ × ℕ)
    (S₀ : Finset (ι × (ℕ × ℕ))) (c : ι → ℝ) (hc : ∀ x, 0 ≤ c x) :
    ∑ g ∈ S₀, (if LetterMomRel S D g.2 β' then 1 else 0) * c g.1 ≤
      (((S + D + 1) ^ 2 : ℕ) : ℝ) * ∑ x, c x := by
  classical
  calc ∑ g ∈ S₀, (if LetterMomRel S D g.2 β' then 1 else 0) * c g.1
      = ∑ g ∈ S₀.filter (fun g => LetterMomRel S D g.2 β'), c g.1 := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun g' _ => by split_ifs <;> simp
    _ ≤ ∑ g ∈ (Finset.univ : Finset ι) ×ˢ ((Finset.Icc (β'.1 - S) (β'.1 + D)) ×ˢ
          (Finset.Icc (β'.2 - S) (β'.2 + D))), c g.1 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun g' _ _ => hc _
        intro g' hg'
        obtain ⟨hg'S, hrel⟩ := Finset.mem_filter.1 hg'
        obtain ⟨h1, h2, h3, h4⟩ := hrel
        simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
        omega
    _ = ((Finset.Icc (β'.1 - S) (β'.1 + D)) ×ˢ (Finset.Icc (β'.2 - S) (β'.2 + D))).card *
          ∑ x, c x := by
        rw [Finset.sum_product]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
    _ ≤ (((S + D + 1) ^ 2 : ℕ) : ℝ) * ∑ x, c x := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun x _ => hc x)
        have := card_box_le D S β'.1 β'.2
        rw [add_comm D S] at this
        exact_mod_cast this

section Weight

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {L : CycleLetter ι h D} {π : ι → ℝ}
  {dom : Set (ℝ × Vec 2)} {Jstar H : ℕ}

theorem letterCompWeight_nonneg (hL : IsCycleLetter π L dom Jstar H) (x x' : ι) :
    0 ≤ letterCompWeight L x x' := by
  unfold letterCompWeight
  split_ifs
  · exact le_rfl
  · exact div_nonneg (hL.nonneg x x') hL.theta_nonneg

theorem letterCompWeight_row (hL : IsCycleLetter π L dom Jstar H) (x : ι) :
    ∑ x', letterCompWeight L x x' ≤ 1 := by
  unfold letterCompWeight
  split_ifs with h0
  · simp
  · rw [← Finset.sum_div]
    exact (div_le_one (lt_of_le_of_ne hL.theta_nonneg (Ne.symm h0))).2 (hL.row_sum x)

theorem letterCompWeight_col (hL : IsCycleLetter π L dom Jstar H) (x' : ι) :
    ∑ x, letterCompWeight L x x' ≤ 1 := by
  unfold letterCompWeight
  split_ifs with h0
  · simp
  · rw [← Finset.sum_div]
    exact (div_le_one (lt_of_le_of_ne hL.theta_nonneg (Ne.symm h0))).2 (hL.col_sum x')

end Weight

open Classical in
/-- **block letter operators.** For a letter `l` there are bounded real-linear
maps `T_{i,i'} : H^N → H^n` (`i` at level `l + 1`, `i'` at level `l`) whose values are
`(c_i/c_{i'}) conj T^{letter}_{i,i'}(conj ψ̃)`, and such that for the stages `S` of one component
`x` and moment `β` and the stages `S'` of one component `x'` and moment `β'` the block bound holds:
`∑_{i'∈S'} ‖∑_{i∈S} T_{i,i'} f_i‖² ≤ (C₀ κ(β,β') majorant(x,x')/θ_l)² ∑_{i∈S} ‖f_i‖²`, where `κ`
is the indicator of the bounded moment shift `LetterMomRel`.  This is the scale-ratio identity,
Parseval on the basis (`‖γ.map‖` on the standard bases), the analytic envelope (jets of order
`≤ slow` in `X` and `≤ n + d` in `z`) and the Sobolev multiplier and twisted-derivative maps. -/
def LetterOpsStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ), n + d l ≤ N → (Finset.univ.sup d) + 3 ≤ N →
  ∃ T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (T i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) ∧
    ∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
      (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
      (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
      ∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 ≤
          (C0 * (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
              then 1 else 0) * letterCompWeight (F.letters l) x x') ^ 2 *
            ∑ i ∈ S, ‖f i‖ ^ 2


/-- `LetterOpsStatement` at every frequency of the zone. -/
def LetterOpsZoneStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    (∀ k, |θ k| ≤ ρ) →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ), n + d l ≤ N →
    (Finset.univ.sup d) + 3 ≤ N →
  ∃ T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (T i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) ∧
    ∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
      (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
      (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
      ∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 ≤
          (C0 * (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
              then 1 else 0) * letterCompWeight (F.letters l) x x') ^ 2 *
            ∑ i ∈ S, ‖f i‖ ^ 2


open Classical in
/-- **Assembly of the letter bound** from the block operators (Schur test over the pairs
`(component, moment)`). -/
theorem letterTransformBoundAEZone_of_ops (hO : LetterOpsZoneStatement.{u, v}) :
    LetterTransformBoundAEZoneStatement.{u, v} := by
  intro K Nw D m d Ks pos ρ n
  obtain ⟨C0, hC0, hC⟩ := hO K Nw D m d Ks pos ρ n
  have hcnt0 : 0 ≤ ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  refine ⟨C0 * ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ),
    mul_nonneg hC0 hcnt0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  filter_upwards [hC g₁ F θ hlet hJ hρ] with r hr
  intro l k k' hk hk' N hnN hdN ψ
  obtain ⟨T, hTv, hTb⟩ := hr l N hnN hdN
  refine ⟨fun i' => if i' ∈ stageSet b1wSt k' then ∑ i ∈ stageSet b1wSt k, T i i' (ψ i) else 0,
    ?_, ?_⟩
  · intro i' hi'
    simp only [hi', ↓reduceIte]
    exact torusHk_value_sum_ae (stageSet b1wSt k) (fun i => T i i' (ψ i)) _
      (fun i hi => hTv i i' (hk i hi) (hk' i' hi') (ψ i))
  · have hL := F.piece.hlet l
    have key := fibre_schur (G := ι × (ℕ × ℕ)) b1wKey
      (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k)
      (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k')
      (fun i i' => T i i' (ψ i)) (fun i => ‖ψ i‖)
      (fun g g' => C0 * (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) g.2 g'.2
        then 1 else 0) * letterCompWeight (F.letters l) g.1 g'.1)
      (fun g g' => mul_nonneg (mul_nonneg hC0 (by split_ifs <;> simp))
        (letterCompWeight_nonneg hL _ _))
      (A := C0 * ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ))
      (Bc := C0 * ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ))
      (fun g _ => by
        have h1 := letterMom_row (Finset.univ.sup Ks) (Finset.univ.sup d + 1) g.2
          ((stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k').image b1wKey)
          (letterCompWeight (F.letters l) g.1) (letterCompWeight_nonneg hL _)
        have h2 := letterCompWeight_row hL g.1
        calc _ = C0 * ∑ g' ∈ (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks))
                k').image b1wKey, (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1)
                g.2 g'.2 then 1 else 0) * letterCompWeight (F.letters l) g.1 g'.1 := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun g' _ => by ring
          _ ≤ C0 * (_ * 1) := mul_le_mul_of_nonneg_left
              (h1.trans (mul_le_mul_of_nonneg_left h2 hcnt0)) hC0
          _ = _ := by ring)
      (fun g' _ => by
        have h1 := letterMom_col (Finset.univ.sup Ks) (Finset.univ.sup d + 1) g'.2
          ((stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k).image b1wKey)
          (fun x => letterCompWeight (F.letters l) x g'.1)
          (fun x => letterCompWeight_nonneg hL _ _)
        have h2 := letterCompWeight_col hL g'.1
        calc _ = C0 * ∑ g ∈ (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks))
                k).image b1wKey, (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1)
                g.2 g'.2 then 1 else 0) * letterCompWeight (F.letters l) g.1 g'.1 := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun g _ => by ring
          _ ≤ C0 * (_ * 1) := mul_le_mul_of_nonneg_left
              (h1.trans (mul_le_mul_of_nonneg_left h2 hcnt0)) hC0
          _ = _ := by ring)
      (mul_nonneg hC0 hcnt0)
      (fun g hg g' hg' => by
        obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hg'
        refine hTb _ _ (b1wKey i₀).1 (b1wKey i₁).1 (b1wKey i₀).2 (b1wKey i₁).2
          (fun i hi => ⟨hk i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
          (fun i' hi' => ⟨hk' i' (Finset.mem_filter.1 hi').1, (Finset.mem_filter.1 hi').2⟩) ψ)
    calc _ = ∑ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
          ‖∑ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
            T i i' (ψ i)‖ ^ 2 :=
          Finset.sum_congr rfl fun i' hi' => by simp only [hi', ↓reduceIte]
      _ ≤ _ := key
      _ = _ := by ring
end

end AVRegularity.CycleWords.Assembly
end
