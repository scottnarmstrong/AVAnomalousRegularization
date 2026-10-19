-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.CategoryTheory.Category.Basic
public import AVenhance.Infra.Torus.FourierCalculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.LinearAlgebra.Lagrange
import AVenhance.Infra.Torus.Slicing
import Mathlib.MeasureTheory.SpecificCodomains.Pi

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Common degree reserves support the actual recurrence under the fixed ambient data budget. -/

def ambientDegreeSlowReserve (P R n : ℕ) : ℕ := P + (R - n)

def ambientDegreeFastReserve (Q D H R hh n : ℕ) : ℕ :=
  Q + (H - hh) * D + 2 * (R - n)

theorem ambientDegreeSlowReserve_data (P R n qs : ℕ) (h : P + R ≤ qs) :
    ambientDegreeSlowReserve P R n ≤ qs := by
  unfold ambientDegreeSlowReserve
  omega

theorem ambientDegreeSlowReserve_source (P R n j : ℕ) (hn : n ≤ R) (hj : j ≤ n) :
    ambientDegreeSlowReserve P R n + j = ambientDegreeSlowReserve P R (n - j) := by
  unfold ambientDegreeSlowReserve
  omega

theorem ambientDegreeSlowReserve_coefficient (P R n : ℕ) (hn : 1 ≤ n) (hR : n ≤ R) :
    ambientDegreeSlowReserve P R n + 1 ≤ P + R := by
  unfold ambientDegreeSlowReserve
  omega

theorem ambientDegreeFastReserve_cross (Q D H R hh n j : ℕ) (hn : n ≤ R) (hj : j ≤ n) :
    ambientDegreeFastReserve Q D H R hh n + 2 * j =
      ambientDegreeFastReserve Q D H R hh (n - j) := by
  unfold ambientDegreeFastReserve
  omega

theorem ambientDegreeFastReserve_source (Q D H R hh n j : ℕ)
    (hhpos : 1 ≤ hh) (hhH : hh ≤ H) (hn : n ≤ R) (hj : j ≤ n) (hjD : j ≤ D) :
    ambientDegreeFastReserve Q D H R hh n + (D - j) ≤
      ambientDegreeFastReserve Q D H R (hh - 1) (n - j) := by
  have he : H - (hh - 1) = (H - hh) + 1 := by omega
  unfold ambientDegreeFastReserve
  rw [he, Nat.add_mul, Nat.one_mul]
  omega

theorem ambientDegreeFastReserve_original_orders (Q D H N hh n : ℕ) (hn : n ≤ N) :
    Q + 2 * D ≤ ambientDegreeFastReserve Q D H (N + D) hh n := by
  unfold ambientDegreeFastReserve
  omega

/-! A finite degree block makes every actual lift recurrence predecessor strictly earlier. -/

def ambientRecurrenceRank (R hh n : ℕ) : ℕ := hh * (R + 1) + n

theorem ambientRecurrenceRank_degree (R hh n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    ambientRecurrenceRank R hh (n - j) < ambientRecurrenceRank R hh n := by
  unfold ambientRecurrenceRank
  omega

theorem ambientRecurrenceRank_height (R hh n hh' n' : ℕ)
    (hh'lt : hh' < hh) (hn' : n' ≤ R) :
    ambientRecurrenceRank R hh' n' < ambientRecurrenceRank R hh n := by
  have hm : hh' * (R + 1) + (R + 1) ≤ hh * (R + 1) := by
    simpa only [Nat.add_mul, Nat.one_mul] using
      Nat.mul_le_mul_right (R + 1) (show hh' + 1 ≤ hh by omega)
  unfold ambientRecurrenceRank
  omega

theorem ambientRecurrenceRank_source (R hh n j : ℕ)
    (hhpos : 1 ≤ hh) (hn : n ≤ R) :
    ambientRecurrenceRank R (hh - 1) (n - j) < ambientRecurrenceRank R hh n := by
  exact ambientRecurrenceRank_height R hh n (hh - 1) (n - j)
    (by omega) (by omega)

theorem ambientRecurrenceRank_composition (R hh n hh' j : ℕ)
    (hh'le : hh' ≤ hh) (hn : n ≤ R) (hj : j < n) :
    ambientRecurrenceRank R hh' j < ambientRecurrenceRank R hh n := by
  rcases lt_or_eq_of_le hh'le with hlt | rfl
  · exact ambientRecurrenceRank_height R hh n hh' j hlt (by omega)
  · unfold ambientRecurrenceRank
    omega

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! The ordered corrections add heights and use only strictly lower degrees. -/

def ambientCorrectionScalarBudget (hh n : ℕ) (B M : ℕ → ℕ → ℝ)
    (K : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n - 2), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
    K j * B ab.1 j * M ab.2 (n - j)

def ambientCenteredScalarBudget (p hh n : ℕ) (uncentered : ℝ)
    (B M : ℕ → ℕ → ℝ) (K : ℕ → ℝ) : ℝ :=
  (1 + (2 : ℝ) ^ p) * uncentered + ambientCorrectionScalarBudget hh n B M K

/-! Plain finite-vector projections give the diagonal identity blocks without dependent casts. -/

section
variable {ι : Type*} [DecidableEq ι] (h : ι → Type*)
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def blockIdentityEntry (v u : ι) : h u →L[ℝ] h v :=
  (ContinuousLinearMap.proj v).comp (ContinuousLinearMap.single ℝ h u)

theorem blockIdentityEntry_apply (v u : ι) (ξ : h u) :
    blockIdentityEntry h v u ξ = Pi.single u ξ v := rfl

theorem blockIdentityEntry_ne (v u : ι) (hne : v ≠ u) : blockIdentityEntry h v u = 0 := by
  ext ξ
  simp only [blockIdentityEntry_apply, Pi.single_eq_of_ne hne, zero_apply]

theorem blockIdentityEntry_norm_le (v u : ι) :
    ‖blockIdentityEntry h v u‖ ≤ if v = u then (1 : ℝ) else 0 := by
  by_cases hvu : v = u
  · subst v
    rw [ite_eq_left (show u = u from rfl)]
    apply (blockIdentityEntry h u u).opNorm_le_bound (by norm_num)
    intro ξ
    simpa only [blockIdentityEntry_apply, Pi.single_eq_same, one_mul] using (le_rfl : ‖ξ‖ ≤ ‖ξ‖)
  · rw [blockIdentityEntry_ne h v u hvu, norm_zero, ite_eq_right hvu]
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Absolute integration of uniformly bounded series on finite measure spaces. -/

variable {J X E : Type*} [Countable J] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [IsFiniteMeasure μ]

omit [Countable J] [NormedSpace ℝ E] [CompleteSpace E] in
theorem boundedSeries_integral_norm_summable (f : J → X → E) (B : J → ℝ)
    (hB : Summable B) (hm : ∀ j, AEStronglyMeasurable (f j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖f j x‖ ≤ B j) :
    Summable (fun j => ∫ x, ‖f j x‖ ∂μ) := by
  have hi (j : J) : Integrable (f j) μ :=
    (memLp_one_iff_integrable).mp (MemLp.of_bound (hm j) (B j) (hb j))
  apply Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _) ?_
    (hB.mul_right (μ.real Set.univ))
  intro j
  have hh := integral_mono_ae (hi j).norm (integrable_const (B j)) (hb j)
  simpa only [integral_const, smul_eq_mul, mul_comm] using hh

omit [CompleteSpace E] in
theorem boundedSeries_integral_tsum (f : J → X → E) (B : J → ℝ)
    (hB : Summable B) (hm : ∀ j, AEStronglyMeasurable (f j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖f j x‖ ≤ B j) :
    (∫ x, ∑' j, f j x ∂μ) = ∑' j, ∫ x, f j x ∂μ := by
  apply (integral_tsum_of_summable_integral_norm ?_
    (boundedSeries_integral_norm_summable f B hB hm hb)).symm
  intro j
  exact memLp_one_iff_integrable.mp (MemLp.of_bound (hm j) (B j) (hb j))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Compact-window absolute series bounds for assembling actual Fourier Hilbert curves. -/

variable {J E : Type*} [Countable J] [NormedAddCommGroup E] [CompleteSpace E]

omit [Countable J] [CompleteSpace E] in
theorem boundedSeries_norm_le (f : J → E) (B : J → ℝ) (hB : Summable B)
    (hf : ∀ j, ‖f j‖ ≤ B j) : ‖∑' j, f j‖ ≤ ∑' j, B j := by
  have hn : Summable (fun j => ‖f j‖) := by
    apply hB.of_norm_bounded
    intro j
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hf j
  exact (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum hf hn hB)

omit [Countable J] in
theorem boundedTimeSeries_continuousOn (f : J → ℝ → E) (B : J → ℝ) (hB : Summable B)
    (a b : ℝ) (hc : ∀ j, ContinuousOn (f j) (Icc a b))
    (hf : ∀ j t, t ∈ Icc a b → ‖f j t‖ ≤ B j) :
    ContinuousOn (fun t => ∑' j, f j t) (Icc a b) :=
  continuousOn_tsum hc hB hf

theorem boundedTimeSeries_memLp {p : ENNReal} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (f : J → ℝ → E) (B : J → ℝ) (hB : Summable B) (a b : ℝ)
    (hm : ∀ j, AEStronglyMeasurable (f j) (volume.restrict (Icc a b)))
    (hf : ∀ j t, t ∈ Icc a b → ‖f j t‖ ≤ B j) :
    MemLp (fun t => ∑' j, f j t) p (volume.restrict (Icc a b)) := by
  apply MemLp.of_bound
    ((AEMeasurable.tsum (fun j => (hm j).aemeasurable)).aestronglyMeasurable) (∑' j, B j)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact boundedSeries_norm_le (fun j => f j t) B hB (fun j => hf j t ht)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! The compiled torus character has exactly the cosine/sine phase in the Wiener target. -/

theorem torusCharacter_eq_exp_phase (k : Fin 2 → ℤ) (z : Vec 2) :
    torusCharacter k z = Complex.exp
      ((-(2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) : ℝ) * Complex.I) := by
  have he : torusCharacter k z =
      ∏ i : Fin 2, Complex.exp (2 * Real.pi * Complex.I * (-(k i : ℂ)) * z i) := by
    simp only [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      toUnitTorus, fourier_coe_apply]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    push_cast
    simp only [Pi.neg_apply, Int.cast_neg]
    ring_nf
  rw [he, ← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_intCast]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  norm_num
  ring


theorem torusCharacter_re_phase (k : Fin 2 → ℤ) (z : Vec 2) :
    (torusCharacter k z).re = Real.cos (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) := by
  rw [torusCharacter_eq_exp_phase, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem torusCharacter_im_phase (k : Fin 2 → ℤ) (z : Vec 2) :
    (torusCharacter k z).im = -Real.sin (2 * Real.pi * ∑ i : Fin 2, (k i : ℝ) * z i) := by
  rw [torusCharacter_eq_exp_phase, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Real and imaginary parameter jets each cost at most the full complex jet norm. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complex_reCLM_norm_le_one : ‖Complex.reCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z

theorem complex_imCLM_norm_le_one : ‖Complex.imCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simpa only [Complex.imCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_im_le_norm z

theorem norm_iteratedFDeriv_re_le (p r : ℕ) (hr : r ≤ p) (F : E → ℂ)
    (hF : ContDiff ℝ (p : ℕ∞) F) (X : E) :
    ‖iteratedFDeriv ℝ r (fun Y => (F Y).re) X‖ ≤ ‖iteratedFDeriv ℝ r F X‖ := by
  have hh := Complex.reCLM.norm_iteratedFDeriv_comp_left (x := X) hF.contDiffAt
    (n := r) (by exact_mod_cast hr)
  have hb := mul_le_mul_of_nonneg_right complex_reCLM_norm_le_one
    (norm_nonneg (iteratedFDeriv ℝ r F X))
  simpa only [Function.comp_def, Complex.reCLM_apply, one_mul] using! hh.trans hb

theorem norm_iteratedFDeriv_im_le (p r : ℕ) (hr : r ≤ p) (F : E → ℂ)
    (hF : ContDiff ℝ (p : ℕ∞) F) (X : E) :
    ‖iteratedFDeriv ℝ r (fun Y => (F Y).im) X‖ ≤ ‖iteratedFDeriv ℝ r F X‖ := by
  have hh := Complex.imCLM.norm_iteratedFDeriv_comp_left (x := X) hF.contDiffAt
    (n := r) (by exact_mod_cast hr)
  have hb := mul_le_mul_of_nonneg_right complex_imCLM_norm_le_one
    (norm_nonneg (iteratedFDeriv ℝ r F X))
  simpa only [Function.comp_def, Complex.imCLM_apply, one_mul] using! hh.trans hb

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! A one-coordinate field has exactly its scalar interval integral as cell average. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem unitCell_volume_one (d : ℕ) : (volume : Measure (Vec d)) (unitCell d) = 1 := by
  unfold unitCell unitCellAt
  simp only [zero_add]
  have he : {x : Vec d | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioc (0 : ℝ) 1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
  rw [he]
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioc]

theorem integral_coordinate_eq_intervalIntegral (q : Fin 2) (f : ℝ → E) (hf : Continuous f) :
    (∫ z in AVenhance.unitCube, f (z q)) = ∫ s in (0 : ℝ)..1, f s := by
  have hi : IntegrableOn (fun z : Vec 2 => f (z q)) (unitCell 2) :=
    Calculus.continuous_integrableOn_unitCell (hf.comp (continuous_apply q))
  rw [← integral_unitCell_eq_unitCube, integral_unitCell2_peel_coord q hi]
  simp only [Fin.insertNth_apply_same, integral_const, Measure.real, Measure.restrict_apply_univ,
    unitCell_volume_one, ENNReal.toReal_one, one_smul]
  exact (intervalIntegral.integral_of_le (f := f) (by norm_num : (0 : ℝ) ≤ 1)).symm

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Integer cell periodicity restricts to unit periodicity on each coordinate line. -/

theorem coordinate_line_periodic {E : Type*} (f : Vec 2 → E)
    (hp : AVenhance.IsZ2Periodic f) (i : Fin 2) :
    Function.Periodic (fun x : ℝ => f (x • basisVec i)) 1 := by
  intro x
  let k : Fin 2 → ℤ := fun j => if j = i then 1 else 0
  have he : (x + 1) • basisVec i = x • basisVec i + AVenhance.latticeShift k := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [k, AVenhance.latticeShift, basisVec_apply]
  change f ((x + 1) • basisVec i) = f (x • basisVec i)
  rw [he]
  exact hp k (x • basisVec i)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! A zero-mean shear profile has zero cell mean in either coordinate. -/

theorem integral_coordinate_mean_zero (q : Fin 2) (f : ℝ → ℝ) (hf : Continuous f)
    (hm : ∫ s in (0 : ℝ)..1, f s = 0) :
    (∫ z in AVenhance.unitCube, f (z q)) = 0 := by
  have hi : IntegrableOn (fun z : Vec 2 => f (z q)) (unitCell 2) :=
    Calculus.continuous_integrableOn_unitCell (hf.comp (continuous_apply q))
  rw [← integral_unitCell_eq_unitCube, integral_unitCell2_peel_coord q hi]
  have hm' : (∫ s in Set.Ioc (0 : ℝ) 1, f s) = 0 := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact hm
  simp only [Fin.insertNth_apply_same, hm', integral_zero]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! The transverse propagator's scalar mass is the reciprocal damping rate. -/

theorem hasDerivAt_decayPrimitive (c : ℝ) (hc : 0 < c) (t s : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (-c * (t - r)) / c)
      (Real.exp (-c * (t - s))) s := by
  have hh := ((((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-c)).exp).div_const c
  simpa [hc.ne'] using hh

theorem integral_decayKernel (c : ℝ) (hc : 0 < c) (a t : ℝ) :
    (∫ s in a..t, Real.exp (-c * (t - s))) =
      (1 - Real.exp (-c * (t - a))) / c := by
  have hcont : Continuous (fun s : ℝ => Real.exp (-c * (t - s))) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_decayPrimitive c hc t s) (hcont.intervalIntegrable a t)
  rw [hh]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

theorem integral_decayKernel_le (c : ℝ) (hc : 0 < c) (a t : ℝ) :
    (∫ s in a..t, Real.exp (-c * (t - s))) ≤ 1 / c := by
  rw [integral_decayKernel c hc]
  exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hc.le

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Dimensional energy factors simplify in abstract real algebra before any functional estimates. -/

theorem dimensional_scale_identity (ℓ B dstar ρ E : ℝ)
    (hℓ : ℓ ≠ 0) (hdstar : dstar ≠ 0) (hρ : ρ ≠ 0) (hE : E ≠ 0)
    (hsq : dstar ^ 2 = ℓ ^ 2 * B) (n d r : ℕ) (hn : 2 ≤ n) (hd : d ≤ n) :
    E ^ r * ((ℓ ^ 2)⁻¹ * (dstar / ρ) ^ n * ρ ^ d) * (ρ⁻¹) ^ r *
        (ρ / E) ^ (n - d + r) = B * dstar ^ (n - 2) * (E ^ d / E ^ n) := by
  rw [pow_add, div_pow, div_pow, div_pow, inv_pow]
  rw [pow_sub₀ ρ hρ hd, pow_sub₀ E hE hd, pow_sub₀ dstar hdstar hn]
  have hdstar2 : dstar ^ 2 ≠ 0 := pow_ne_zero _ hdstar
  field_simp
  nlinarith [hsq]

/-! Real dual bounds recover multilinear operator norms without basis or dimension constants. -/

section
variable {ι : Type*} [Fintype ι] {D : ι → Type*}
  [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace ℝ (D i)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem multilinear_norm_le_from_real_duals
    (f : ContinuousMultilinearMap ℝ D E) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ l : E →L[ℝ] ℝ, ‖l.compContinuousMultilinearMap f‖ ≤ C * ‖l‖) : ‖f‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro x
  apply NormedSpace.norm_le_dual_bound (𝕜 := ℝ) (f x)
    (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  intro l
  have hh := (l.compContinuousMultilinearMap f).le_opNorm x
  calc
    ‖l (f x)‖ ≤ ‖l.compContinuousMultilinearMap f‖ * ∏ i, ‖x i‖ := hh
    _ ≤ (C * ‖l‖) * ∏ i, ‖x i‖ :=
      mul_le_mul_of_nonneg_right (hf l) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (C * ∏ i, ‖x i‖) * ‖l‖ := by ring
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Exact interpolation identity for exponential differences, used by metric propagator comparisons. -/

theorem exponential_difference_integral (A B : ℝ) :
    Real.exp (A + B) - Real.exp A =
      ∫ θ in (0 : ℝ)..1, Real.exp (A + θ * B) * B := by
  have hd (θ : ℝ) : HasDerivAt (fun θ => Real.exp (A + θ * B))
      (Real.exp (A + θ * B) * B) θ := by
    simpa only [id_eq, one_mul] using (((hasDerivAt_id θ).mul_const B).const_add A).exp
  have hi : IntervalIntegrable (fun θ => Real.exp (A + θ * B) * B) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ) hi
  simpa only [one_mul, zero_mul, add_zero] using he.symm

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! A scalar exponential retains its damping factor in every finite derivative estimate. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_real_exp (j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ j Real.exp x‖ = Real.exp x := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have he : iteratedDeriv j Real.exp = Real.exp := by
    simpa using (iteratedDeriv_exp_const_mul j (1 : ℝ))
  rw [he, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]

theorem norm_iteratedFDeriv_exp_comp_le (n : ℕ) (u : E → ℝ)
    (hu : ContDiff ℝ (n : ℕ∞) u) (x : E) (D : ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j u x‖ ≤ D ^ j) :
    ‖iteratedFDeriv ℝ n (fun y => Real.exp (u y)) x‖ ≤
      n.factorial * Real.exp (u x) * D ^ n := by
  have he : ContDiff ℝ (n : ℕ∞) Real.exp := Real.contDiff_exp
  apply norm_iteratedFDeriv_comp_le he hu (by simp) x (C := Real.exp (u x))
  · intro j _
    exact (norm_iteratedFDeriv_real_exp j (u x)).le
  · exact hb

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace AVRegularity.CycleComparison.Lift

/-! Exponentiation preserves absolute continuity on a finite time window, using its compact range. -/

theorem absolutelyContinuousOnInterval_exp {a b : ℝ} {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => Real.exp (f t)) a b := by
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hf.continuousOn
  let C : ℝ≥0 := ⟨Real.exp M, (Real.exp_pos M).le⟩
  have he : LipschitzOnWith C Real.exp (Icc (-M) M) :=
    (convex_Icc (-M) M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun x hx => by
        change ‖Real.exp x‖ ≤ Real.exp M
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
        exact Real.exp_le_exp.mpr hx.2)
  apply he.comp_absolutelyContinuousOnInterval ?_ hf
  intro x hx
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hM x hx)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! First derivatives of dilated real fields have their exact scalar factor, without extra smoothness premises. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_dilation_smul (f : Vec 2 → E) (a c : ℝ) (X Y : Vec 2) :
    fderiv ℝ (fun Z => c • f (a • Z)) X Y = (c * a) • fderiv ℝ f (a • X) Y := by
  change fderiv ℝ (c • (fun Z => f (a • Z))) X Y = _
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply]
  rw [fderiv_comp_smul]
  simp only [smul_apply, smul_smul]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Finite real dual coordinates recover genuine vector integrability. -/

section
variable {J E : Type*} [MeasurableSpace J] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem integrable_of_all_real_duals (f : J → E) (μ : Measure J)
    (h : ∀ l : E →L[ℝ] ℝ, Integrable (fun x => l (f x)) μ) : Integrable f μ := by
  let e := (Module.finBasis ℝ E).equivFunL
  have hc : Integrable (fun x => e (f x)) μ := by
    apply integrable_pi_iff.mpr
    intro i
    exact h ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)
  have hr := e.symm.toContinuousLinearMap.integrable_comp hc
  change Integrable (fun x => e.symm (e (f x))) μ at hr
  simpa only [e.symm_apply_apply] using hr

theorem intervalIntegrable_of_all_real_duals (f : ℝ → E) (μ : Measure ℝ) (a b : ℝ)
    (h : ∀ l : E →L[ℝ] ℝ, IntervalIntegrable (fun x => l (f x)) μ a b) :
    IntervalIntegrable f μ a b := by
  apply intervalIntegrable_iff.mpr
  exact integrable_of_all_real_duals f (μ.restrict (Set.uIoc a b))
    (fun l => intervalIntegrable_iff.mp (h l))
end

/-! Finite dual coordinates recover measurability of genuine finite-dimensional fields. -/

section
variable {T : Type*} [MeasurableSpace T] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem measurable_of_all_real_duals (f : T → E)
    (hm : ∀ l : E →L[ℝ] ℝ, Measurable (fun t => l (f t))) : Measurable f := by
  let e := (Module.finBasis ℝ E).equivFunL
  have hc : Measurable (fun t => e (f t)) := by
    apply Measurable.of_eval
    intro i
    exact hm ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)
  have hr := e.symm.continuous.measurable.comp hc
  simpa only [Function.comp_def, e.symm_apply_apply] using! hr
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Classical regularity of positive finite constituent presentations. -/

section
variable {E F κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_list_sum_map (l : List κ) (f : κ → E → F) (n : ℕ∞)
    (hf : ∀ a ∈ l, ContDiff ℝ n (f a)) :
    ContDiff ℝ n (fun x => (l.map fun a => f a x).sum) := by
  induction l with
  | nil => simpa using (contDiff_const : ContDiff ℝ n (fun _ : E => (0 : F)))
  | cons a l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (hf a List.mem_cons_self).add (ih (fun b hb => hf b (List.mem_cons_of_mem _ hb)))
end

/-! One finite fixed-data sum bounds every supported height, degree, word order and jet order. -/

def finiteFourBudget (A B C D : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
    ∑ c ∈ Finset.range (C + 1), ∑ d ∈ Finset.range (D + 1), F a b c d

theorem finiteFourBudget_nonneg (A B C D : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ a b c d, 0 ≤ F a b c d) : 0 ≤ finiteFourBudget A B C D F := by
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => hF a b c d

theorem finiteFourBudget_le (A B C D : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ a b c d, 0 ≤ F a b c d)
    (a b c d : ℕ) (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) :
    F a b c d ≤ finiteFourBudget A B C D F := by
  let G := fun a b c => ∑ d ∈ Finset.range (D + 1), F a b c d
  let H := fun a b => ∑ c ∈ Finset.range (C + 1), G a b c
  let I := fun a => ∑ b ∈ Finset.range (B + 1), H a b
  have hG a b c : 0 ≤ G a b c := Finset.sum_nonneg fun d _ => hF a b c d
  have hH a b : 0 ≤ H a b := Finset.sum_nonneg fun c _ => hG a b c
  have hI a : 0 ≤ I a := Finset.sum_nonneg fun b _ => hH a b
  have h1 : F a b c d ≤ G a b c :=
    Finset.single_le_sum (fun d _ => hF a b c d) (Finset.mem_range.mpr (by omega))
  have h2 : G a b c ≤ H a b :=
    Finset.single_le_sum (fun c _ => hG a b c) (Finset.mem_range.mpr (by omega))
  have h3 : H a b ≤ I a :=
    Finset.single_le_sum (fun b _ => hH a b) (Finset.mem_range.mpr (by omega))
  have h4 : I a ≤ finiteFourBudget A B C D F :=
    Finset.single_le_sum (fun a _ => hI a) (Finset.mem_range.mpr (by omega))
  exact h1.trans (h2.trans (h3.trans h4))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Finite constituent lists and finite jet sums can be interchanged without identifying repeated constituents. -/

theorem list_finset_sum_interchange {α β M : Type*} [AddCommMonoid M]
    (l : List α) (s : Finset β) (f : α → β → M) :
    (l.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Finite nonnegative matrices carry row and column budgets stable under products and sums. -/

variable {ι : Type*} [Fintype ι]

structure HasRealSchurBudget (A : ι → ι → ℝ) (C : ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  row_sum : ∀ i, ∑ j, A i j ≤ C
  col_sum : ∀ j, ∑ i, A i j ≤ C

def finiteMatrixProduct (A B : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => ∑ r, A i r * B r j

theorem HasRealSchurBudget.product {A B : ι → ι → ℝ} {C D : ℝ}
    (hA : HasRealSchurBudget A C) (hB : HasRealSchurBudget B D)
    (hC : 0 ≤ C) (hD : 0 ≤ D) : HasRealSchurBudget (finiteMatrixProduct A B) (C * D) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hA.nonneg i r) (hB.nonneg r j)
  · intro i
    unfold finiteMatrixProduct
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ r, A i r * D := Finset.sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_left (hB.row_sum r) (hA.nonneg i r)
      _ = (∑ r, A i r) * D := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hA.row_sum i) hD
  · intro j
    unfold finiteMatrixProduct
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    calc
      _ ≤ ∑ r, C * B r j := Finset.sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_right (hA.col_sum r) (hB.nonneg r j)
      _ = C * ∑ r, B r j := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hB.col_sum j) hC

theorem HasRealSchurBudget.add {A B : ι → ι → ℝ} {C D : ℝ}
    (hA : HasRealSchurBudget A C) (hB : HasRealSchurBudget B D) :
    HasRealSchurBudget (fun i j => A i j + B i j) (C + D) := by
  constructor
  · intro i j
    exact add_nonneg (hA.nonneg i j) (hB.nonneg i j)
  · intro i
    simpa only [Finset.sum_add_distrib] using add_le_add (hA.row_sum i) (hB.row_sum i)
  · intro j
    simpa only [Finset.sum_add_distrib] using add_le_add (hA.col_sum j) (hB.col_sum j)

theorem HasRealSchurBudget.const_mul {A : ι → ι → ℝ} {C : ℝ}
    (hA : HasRealSchurBudget A C) (K : ℝ) (hK : 0 ≤ K) :
    HasRealSchurBudget (fun i j => K * A i j) (K * C) := by
  constructor
  · intro i j
    exact mul_nonneg hK (hA.nonneg i j)
  · intro i
    simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left (hA.row_sum i) hK
  · intro j
    simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left (hA.col_sum j) hK

theorem hasRealSchurBudget_diagonal [DecidableEq ι] :
    HasRealSchurBudget (fun i j : ι => if i = j then 1 else 0) 1 := by
  constructor
  · intro i j
    split <;> norm_num
  · intro i
    simp
  · intro j
    simp

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Finite input coordinates recover scalar-dual measurability of operator-valued fields. -/

variable {T E F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem operator_dual_measurable_of_applied_duals (f : T → E →L[ℝ] F)
    (hm : ∀ x : E, ∀ l : F →L[ℝ] ℝ, Measurable (fun t => l (f t x)))
    (l : (E →L[ℝ] F) →L[ℝ] ℝ) : Measurable (fun t => l (f t)) := by
  let b := Module.finBasis ℝ E
  let e := b.equivFunL
  let R := fun i => ((ContinuousLinearMap.compL ℝ E ℝ F).flip
      ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)).comp
        (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have he (t : T) : f t = ∑ i, R i (f t (b i)) := by
    ext x
    simp only [sum_apply]
    change f t x = ∑ i, e x i • f t (b i)
    calc
      f t x = f t (∑ i, e x i • b i) := congrArg (f t) (b.sum_equivFun x).symm
      _ = _ := by simp only [map_sum, map_smul]
  have hfun : (fun t => l (f t)) = fun t => ∑ i, (l.comp (R i)) (f t (b i)) := by
    funext t
    calc
      l (f t) = l (∑ i, R i (f t (b i))) := congrArg l (he t)
      _ = _ := by rw [map_sum]; rfl
  rw [hfun]
  exact Finset.measurable_sum _ (fun i _ => hm (b i) (l.comp (R i)))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Fixed finite scalar interpolation extracts vector-valued polynomial coefficients. -/

open Polynomial

noncomputable def polynomialExtractionWeight (n m : ℕ) (j : Fin (n + 1)) : ℝ :=
  (Lagrange.basis Finset.univ (fun i : Fin (n + 1) => (i : ℝ)) j).coeff m

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_polynomial_coefficient_interpolation (n m : ℕ) (hm : m ≤ n) (c : ℕ → E) :
    (∑ j : Fin (n + 1), polynomialExtractionWeight n m j •
      ∑ i ∈ Finset.range (n + 1), (j : ℝ) ^ i • c i) = c m := by
  classical
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro l
  let P : ℝ[X] := ∑ i ∈ Finset.range (n + 1), monomial i (l (c i))
  have hcoeff (k : ℕ) : P.coeff k = if k ≤ n then l (c k) else 0 := by
    simp [P, coeff_monomial, Finset.mem_range]
  have hdeg : P.degree < (n + 1 : ℕ) := by
    apply (degree_lt_iff_coeff_zero P (n + 1)).mpr
    intro k hk
    rw [hcoeff, ite_eq_right (by omega)]
  have hinj : Set.InjOn (fun j : Fin (n + 1) => (j : ℝ)) (↑(Finset.univ : Finset (Fin (n + 1)))) := by
    intro i _ j _ hij
    apply Fin.ext
    change (i.val : ℝ) = (j.val : ℝ) at hij
    exact_mod_cast hij
  have hi := Lagrange.eq_interpolate hinj (by simpa using hdeg)
  have he := congrArg (fun R : ℝ[X] => R.coeff m) hi
  have hev (j : Fin (n + 1)) : P.eval (j : ℝ) =
      ∑ i ∈ Finset.range (n + 1), (j : ℝ) ^ i * l (c i) := by
    simp only [P, eval_finsetSum, eval_monomial]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  simp only [hcoeff, hm, ite_true, Lagrange.interpolate_apply, finsetSum_coeff,
    coeff_C_mul, hev] at he
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  rw [polynomialExtractionWeight, mul_comm]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Finite scalar synthesis preserves genuine time primitives. -/

variable {J E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finset_time_primitives [CompleteSpace E] (S : Finset J) (w : J → ℝ)
    (u : J → E) (R : J → ℝ → E) (a b : ℝ)
    (h : ∀ j ∈ S, IntervalIntegrable (R j) volume a b ∧ u j = ∫ s in a..b, R j s) :
    IntervalIntegrable (fun s => ∑ j ∈ S, w j • R j s) volume a b ∧
      (∑ j ∈ S, w j • u j) = ∫ s in a..b, ∑ j ∈ S, w j • R j s := by
  have hi (j : J) (hj : j ∈ S) : IntervalIntegrable (fun s => w j • R j s) volume a b :=
    (h j hj).1.smul (w j)
  refine ⟨?_, ?_⟩
  · have he : (∑ j ∈ S, fun s => w j • R j s) = fun s => ∑ j ∈ S, w j • R j s := by
      funext s
      simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum S (fun j hj => hi j hj)
  rw [intervalIntegral.integral_finsetSum (fun j hj => hi j hj)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(h j hj).2, intervalIntegral.integral_smul]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Two finite collections of fixed-data constants admit one nonnegative budget. -/

theorem finite_uniform_pair_budget {α : Type*} [Fintype α] (f g : α → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, f a ≤ C ∧ g a ≤ C := by
  obtain ⟨C, hC⟩ := (Set.finite_range (fun a => |f a| + |g a|)).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro a
  have ha : |f a| + |g a| ≤ C := hC (Set.mem_range_self a)
  constructor
  · exact (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans
      (ha.trans (le_max_left _ _)))
  · exact (le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans
      (ha.trans (le_max_left _ _)))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Bilinear coefficient products preserve their exact nonnegative slow grading. -/

variable {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_bilinear_graded_le (n r s : ℕ)
    (T : E →L[ℝ] F →L[ℝ] G) (hT : ‖T‖ ≤ 1) (f : X → E) (g : X → F)
    (hf : ContDiff ℝ (n : ℕ∞) f) (hg : ContDiff ℝ (n : ℕ∞) g)
    (x : X) (lam : ℝ) (hlam : 0 ≤ lam) (A B : ℕ → ℝ)
    (hA : ∀ j ≤ n, 0 ≤ A j) (hB : ∀ j ≤ n, 0 ≤ B j)
    (hbA : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ A j * lam ^ (r + j))
    (hbB : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ B j * lam ^ (s + j)) :
    ‖iteratedFDeriv ℝ n (fun y => T (f y) (g y)) x‖ ≤
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * A j * B (n - j)) * lam ^ (r + s + n) := by
  apply (T.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hg x (by simp) hT).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := by have hh := Finset.mem_range.mp hj; omega
  have hAj := hA j hjn
  have hBj := hB (n - j) (Nat.sub_le n j)
  calc
    _ ≤ (n.choose j : ℝ) * (A j * lam ^ (r + j)) * (B (n - j) * lam ^ (s + (n - j))) := by
      gcongr
      · exact hbA j hjn
      · exact hbB (n - j) (Nat.sub_le n j)
    _ = ((n.choose j : ℝ) * A j * B (n - j)) * lam ^ (r + s + n) := by
      have hp : lam ^ (r + j) * lam ^ (s + (n - j)) = lam ^ (r + s + n) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ = ((n.choose j : ℝ) * A j * B (n - j)) *
          (lam ^ (r + j) * lam ^ (s + (n - j))) := by ring
        _ = _ := by rw [hp]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Classical profile jet bounds follow from the reserved cell jets by explicit linear restriction. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedDeriv_linear_profile_le (f : Vec 2 → E) (q j : ℕ)
    (hf : ContDiff ℝ (q : ℕ∞) f) (hj : j ≤ q) (L : ℝ →L[ℝ] Vec 2) (x : ℝ) :
    ‖iteratedDeriv j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * ‖L‖ ^ j := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hj)]
  simpa using (iteratedFDeriv ℝ j f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

theorem norm_iteratedDeriv_dual_linear_profile_le (f : Vec 2 → E) (q j : ℕ)
    (hf : ContDiff ℝ (q : ℕ∞) f) (hj : j ≤ q)
    (L : ℝ →L[ℝ] Vec 2) (A : E →L[ℝ] ℂ) (x : ℝ) :
    ‖iteratedDeriv j (A ∘ f ∘ L) x‖ ≤
      ‖A‖ * (‖iteratedFDeriv ℝ j f (L x)‖ * ‖L‖ ^ j) := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hh : ‖iteratedFDeriv ℝ j (A ∘ (f ∘ L)) x‖ ≤
      ‖A‖ * ‖iteratedFDeriv ℝ j (f ∘ L) x‖ :=
    A.norm_iteratedFDeriv_comp_left ((hf.comp L.contDiff).contDiffAt) (by exact_mod_cast hj)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedDeriv_linear_profile_le f q j hf hj L x

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The transverse scalar metric inherits precisely the ellipticity constants of the lift setting. -/

theorem metric_diagonal_bounds (G : Fin 2 → Fin 2 → ℝ) (lo hi : ℝ)
    (hG : ∀ ξ : Vec 2,
      lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j ∧
      (∑ i, ∑ j, G i j * ξ i * ξ j) ≤ hi * ∑ i, ξ i ^ 2) (p : Fin 2) :
    lo ≤ G p p ∧ G p p ≤ hi := by
  simpa [basisVec_apply] using hG (basisVec p)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The zeroth fast jet is an isometric copy and introduces no quantitative loss. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_fast_zero_eq (r : ℕ) (f : Vec 2 → Vec 2 → E) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ 0 (f Y) z) X‖ =
      ‖iteratedFDeriv ℝ r (fun Y => f Y z) X‖ := by
  change ‖iteratedFDeriv ℝ r ((continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm ∘
    (fun Y => f Y z)) X‖ = _
  exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.norm_iteratedFDeriv_comp_left _ X r
end

/-! A zero-order fast jet changes only the isometric codomain representation. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_jet_fast_zero (r : ℕ) (f : Vec 2 → Vec 2 → E) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ 0 (f Y) z) X‖ =
      ‖iteratedFDeriv ℝ r (fun Y => f Y z) X‖ := by
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.norm_iteratedFDeriv_comp_left
    (fun Y => f Y z) X r
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Extract the first Taylor coefficient of a finite positive-degree flux polynomial. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_power_smul_zero (m : ℕ) (hm : 1 ≤ m) (c : E) :
    HasDerivAt (fun ε : ℝ => ε ^ m • c) (if m = 1 then c else 0) 0 := by
  have hh := (hasDerivAt_pow m (0 : ℝ)).smul_const c
  by_cases h1 : m = 1
  · subst m
    simpa using hh
  · simpa only [zero_pow (show m - 1 ≠ 0 by omega), mul_zero, zero_smul,
      ite_eq_right h1] using hh
end

/-! Fixed multilinear evaluation is a bounded linear map on the coefficient space. -/

section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def multilinearEvaluationMap (x : ∀ i, E i) :
    ContinuousMultilinearMap ℝ E F →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (∏ i, ‖x i‖) (fun f => by
      change ‖f x‖ ≤ (∏ i, ‖x i‖) * ‖f‖
      simpa only [mul_comm] using f.le_opNorm x)

theorem multilinearEvaluationMap_apply (x : ∀ i, E i)
    (f : ContinuousMultilinearMap ℝ E F) : multilinearEvaluationMap x f = f x := rfl
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Postcomposition of multilinear maps costs only the norm of the actual output map. -/

variable {ι : Type*} [Fintype ι] {D : ι → Type*}
  [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace ℝ (D i)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem multilinear_postcomposition_norm_le (L : E →L[ℝ] F) :
    ‖ContinuousLinearMap.compContinuousMultilinearMapL ℝ D E F L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro f
  exact L.norm_compContinuousMultilinearMap_le f

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Normalized exponential tests preserve the first cross operator's single grading power. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalizedCellB1MixedConstant (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M W C : ℝ) : ℝ :=
  let Cexp := 2 ^ ((p + 1) + 2 * (q + 1)) * max 1 ‖A‖ ^ (p + 1) * C
  (2 ^ (p + 2 * q) * max 1 ‖A‖ ^ p) *
    (2 * (2 ^ (p + 2 * q) * W * Cexp) +
      4 * ((2 ^ (p + 2 * q) + 2 ^ ((p + 1) + 2 * q)) * M * Cexp))

end AVRegularity.CycleComparison.Lift
end
end
