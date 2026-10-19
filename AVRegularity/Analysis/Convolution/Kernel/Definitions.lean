-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.Core
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Homogenization.Ambient.HilbertFinite

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Analysis.Convolution

/-! Change of variables for convolution by an invertible spatial map. -/

/-- Literal transported density for an invertible spatial linear map. -/
def transportedKernel (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ) : Vec 2 → ℝ :=
  fun y => |LinearMap.det R.toLinearEquiv.toLinearMap|⁻¹ * κ (R.symm y)

 theorem integral_comp_continuousLinearEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (R : Vec 2 ≃L[ℝ] Vec 2) (f : Vec 2 → F) :
    ∫ z, f (R z) = |LinearMap.det R.toLinearEquiv.toLinearMap|⁻¹ • ∫ y, f y := by
  have hm : Measure.map R (volume : Measure (Vec 2)) =
      ENNReal.ofReal |LinearMap.det R.toLinearEquiv.toLinearMap|⁻¹ • volume := by
    simpa only [abs_inv, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] using Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (Vec 2)) (f := R.toLinearEquiv.toLinearMap) R.toLinearEquiv.isUnit_det'.ne_zero
  have hi := integral_map_equiv (μ := (volume : Measure (Vec 2))) R.toHomeomorph.toMeasurableEquiv f
  change (∫ y, f y ∂Measure.map R volume) = ∫ x, f (R x) at hi
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))] at hi
  exact hi.symm

 theorem integral_eq_transported_convolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ) (f : Vec 2 → E) (x : Vec 2) :
    (∫ z : Vec 2, κ z • f (x-R z)) =
      convolution (transportedKernel R κ) f (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have hi := integral_comp_continuousLinearEquiv R
    (fun y => κ (R.symm y) • f (x-y))
  simp only [R.symm_apply_apply] at hi
  unfold convolution transportedKernel
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [show (fun z => (|LinearMap.det R.toLinearEquiv.toLinearMap|⁻¹ * κ (R.symm z)) • f (x-z)) =
      fun z => |LinearMap.det R.toLinearEquiv.toLinearMap|⁻¹ • (κ (R.symm z) • f (x-z)) by
    funext z; exact mul_smul _ _ _, integral_smul]
  exact hi

 theorem hasCompactSupport_transportedKernel (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ) : HasCompactSupport (transportedKernel R κ) :=
  (hc.comp_homeomorph R.symm.toHomeomorph).mul_left

theorem contDiff_transportedKernel (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hd : ContDiff ℝ (⊤ : ℕ∞) κ) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedKernel R κ) :=
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => |LinearMap.det R.toLinearEquiv.toLinearMap|⁻¹) := contDiff_const
  by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => |LinearMap.det R.toLinearEquiv.toLinearMap|⁻¹ * κ (R.symm x))
    exact hc.mul (hd.comp R.symm.contDiff)

end AVRegularity.Analysis.Convolution
end
end
end

section
public noncomputable section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.Analysis.Convolution

/-! Strong L² approximation by the literal normalized averages. Used to
extend the Fourier weak derivative identity from smooth to weak data. -/

variable {X E : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- Shrinking any continuous translation map gives strong L² approximation, for an L¹ kernel. -/
theorem tendsto_averagingOperator_of_tendsto_zero
    (ρ : ℕ → Vec 2 →+ X) (hρ : ∀ n, Continuous (ρ n))
    (hzero : ∀ z, Tendsto (fun n => ρ n z) atTop (𝓝 0))
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) (hmass : ∫ z, κ z = 1) (f : L2 E μ) :
    Tendsto (fun n => averagingOperator (ρ n) (hρ n) κ hκ f) atTop (𝓝 f) := by
  have hlim : Tendsto (fun n => ∫ z : Vec 2, κ z • translation (ρ n z) f)
      atTop (𝓝 (∫ z : Vec 2, κ z • f)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖κ z‖ * ‖f‖)
    · exact Eventually.of_forall fun n => (integrable_average_integrand (ρ n) (hρ n) hκ f).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun z => by
        rw [norm_smul, translation_norm]
    · exact hκ.norm.mul_const ‖f‖
    · exact Eventually.of_forall fun z => by
        have ht := ((continuous_translation f).tendsto 0).comp (hzero z)
        simpa only [translation_zero, Function.comp_def] using ht.const_smul (κ z)
  simpa only [averagingOperator_apply, integral_smul_const, hmass, one_smul] using hlim

end AVRegularity.Analysis.Convolution
end
end

section
section
@[expose] public section
noncomputable section
open MeasureTheory
namespace AVRegularity.Analysis.Convolution

/-! Exact factorial integral remainder bound for a Banach-valued line path. -/

 theorem integral_one_sub_pow (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..1, (1-t)^n) = 1 / (n+1 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^n) 1]
  simp only [sub_self, sub_zero, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]

end AVRegularity.Analysis.Convolution
end
end
end

section
public section
namespace AVRegularity.Analysis.Convolution

/-! Positivity and contraction of the finite polynomial used by the high-order
compactly supported mollifier. These are operator lemmas; identifying the
actual averaging/convolution operator and its derivative bounds is separate. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric operator with quadratic form in `[0, ‖x‖²]` is a contraction. -/
theorem norm_le_one_of_quadratic_bounds (T : E →L[ℝ] E)
    (hT : T.IsSymmetric)
    (hl : ∀ x, 0 ≤ inner ℝ (T x) x)
    (hu : ∀ x, inner ℝ (T x) x ≤ ‖x‖ ^ 2) : ‖T‖ ≤ 1 := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  change |inner ℝ (T x) x / ‖x‖ ^ 2| ≤ 1
  rw [abs_of_nonneg (div_nonneg (hl x) (sq_nonneg _))]
  exact div_le_one_of_le₀ (hu x) (sq_nonneg _)

/-- The complement of a positive contraction is a positive contraction. -/
theorem positive_complement (T : E →L[ℝ] E) (hT : T.IsPositive) (hn : ‖T‖ ≤ 1) :
    (1 - T).IsPositive ∧ ‖1 - T‖ ≤ 1 := by
  have hupper (x : E) : inner ℝ (T x) x ≤ ‖x‖ ^ 2 := by
    calc
      inner ℝ (T x) x ≤ ‖T x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _)
      _ ≤ (1 * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hn (norm_nonneg _)) (norm_nonneg _)
      _ = ‖x‖ ^ 2 := by rw [one_mul, pow_two]
  have hsym : (1 - T).IsSymmetric := LinearMap.IsSymmetric.id.sub hT.isSymmetric
  have hl (x : E) : 0 ≤ inner ℝ ((1 - T) x) x := by
    simp only [sub_apply, one_apply_eq_self,
      inner_sub_left, real_inner_self_eq_norm_sq]
    exact sub_nonneg.mpr (hupper x)
  have hu (x : E) : inner ℝ ((1 - T) x) x ≤ ‖x‖ ^ 2 := by
    simp only [sub_apply, one_apply_eq_self,
      inner_sub_left, real_inner_self_eq_norm_sq]
    exact sub_le_self _ (hT.inner_nonneg_left x)
  exact ⟨(ContinuousLinearMap.isPositive_iff _).mpr ⟨hsym, hl⟩,
    norm_le_one_of_quadratic_bounds (1 - T) hsym hl hu⟩

variable [CompleteSpace E]

/-- Every natural power of a positive operator is positive, without a spectral theorem. -/
theorem positive_pow (T : E →L[ℝ] E) (hT : T.IsPositive) (n : ℕ) :
    (T ^ n).IsPositive := by
  induction n using Nat.twoStepInduction with
  | zero => simpa only [pow_zero] using (ContinuousLinearMap.isPositive_one (𝕜 := ℝ) (E := E))
  | one => simpa only [pow_one] using hT
  | more n ih _ =>
    have h := ih.adjoint_conj T
    rw [hT.isSelfAdjoint.adjoint_eq] at h
    change (T * T ^ n * T).IsPositive at h
    simpa only [← pow_succ', ← pow_succ] using h

/-- The finite high-order regularizer associated to a positive contraction is contractive. -/
theorem regularizer_polynomial_norm_le (T : E →L[ℝ] E)
    (hT : T.IsPositive) (hn : ‖T‖ ≤ 1) (n : ℕ) :
    (1 - (1 - T) ^ n).IsPositive ∧ ‖1 - (1 - T) ^ n‖ ≤ 1 := by
  obtain ⟨hp, hnorm⟩ := positive_complement T hT hn
  have hpow : ∀ k : ℕ, ‖(1 - T) ^ k‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
    | succ k ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans
        ((mul_le_mul ih hnorm (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  exact positive_complement ((1 - T) ^ n) (positive_pow _ hp n) (hpow n)

/-- Applied to `A* A`, only the contraction bound for the original averaging operator is needed. -/
theorem autocorrelation_regularizer_norm_le (A : E →L[ℝ] E) (hA : ‖A‖ ≤ 1) (n : ℕ) :
    (1 - (1 - A.adjoint * A) ^ n).IsPositive ∧
      ‖1 - (1 - A.adjoint * A) ^ n‖ ≤ 1 := by
  have hnorm : ‖A.adjoint * A‖ ≤ 1 := by
    change ‖A.adjoint.comp A‖ ≤ 1
    rw [ContinuousLinearMap.norm_adjoint_comp_self]
    simpa only [pow_two] using (pow_le_pow_left₀ (norm_nonneg _) hA 2).trans_eq (one_pow 2)
  exact regularizer_polynomial_norm_le (A.adjoint * A)
    (ContinuousLinearMap.isPositive_adjoint_comp_self A) hnorm n

end AVRegularity.Analysis.Convolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped Pointwise
namespace AVRegularity.Analysis.Convolution

/-! Literal compactly supported kernel in the paired smoothing construction. -/

/-- The template scaled by the factor `2n`. -/
def scaledTemplate (φ₀ : Vec 2 → ℝ) (n : ℕ+) : Vec 2 → ℝ :=
  fun z => (2 * ((n : ℕ) : ℝ)) ^ 2 * φ₀ ((2 * ((n : ℕ) : ℝ)) • z)

/-- An actual positive convolution power; the zeroth index denotes one copy. -/
def positiveConvolutionPower (q : Vec 2 → ℝ) : ℕ → Vec 2 → ℝ
  | 0 => q
  | m + 1 => kernelConvolution q (positiveConvolutionPower q m)

/-- The signed binomial regularizer of an autocorrelation kernel. -/
def momentKernel (φ₀ : Vec 2 → ℝ) (n : ℕ+) : Vec 2 → ℝ :=
  ∑ l ∈ Finset.Icc 1 (n : ℕ),
    ((-1 : ℝ) ^ (l + 1) * ((n : ℕ).choose l : ℝ)) •
      positiveConvolutionPower
        (kernelConvolution (scaledTemplate φ₀ n) (reflection (scaledTemplate φ₀ n))) (l - 1)

/-- The Euclidean realization of the vector coordinates' norm, via `PiLp 2`. -/
def euclideanNorm (z : Vec 2) : ℝ := ‖Homogenization.HilbertVec.ofVec z‖

theorem euclideanNorm_continuous : Continuous euclideanNorm := by
  change Continuous (fun z : Vec 2 => ‖(Homogenization.HilbertVec.continuousLinearEquivVec 2).symm z‖)
  exact continuous_norm.comp (Homogenization.HilbertVec.continuousLinearEquivVec 2).symm.continuous

@[simp] theorem euclideanNorm_add (x y : Vec 2) : euclideanNorm (x + y) ≤
    euclideanNorm x + euclideanNorm y := by
  unfold euclideanNorm
  have hxy : Homogenization.HilbertVec.ofVec (x + y) =
      Homogenization.HilbertVec.ofVec x + Homogenization.HilbertVec.ofVec y := by
    apply PiLp.ext
    intro i
    rfl
  rw [hxy]
  exact norm_add_le _ _

@[simp] theorem euclideanNorm_smul (c : ℝ) (x : Vec 2) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  unfold euclideanNorm
  have hcx : Homogenization.HilbertVec.ofVec (c • x) =
      c • Homogenization.HilbertVec.ofVec x := by
    apply PiLp.ext
    intro i
    rfl
  rw [hcx, norm_smul, Real.norm_eq_abs]

@[simp] theorem euclideanNorm_neg (x : Vec 2) : euclideanNorm (-x) = euclideanNorm x := by
  rw [show -x = (-1 : ℝ) • x by simp, euclideanNorm_smul, abs_neg, abs_one, one_mul]

/-- The closed Euclidean unit ball in the kernel coordinates. -/
def closedEuclideanUnitBall : Set (Vec 2) := {z | euclideanNorm z ≤ 1}

@[simp] theorem reflection_apply (q : Vec 2 → ℝ) (z : Vec 2) :
    reflection q z = q (-z) := rfl

end AVRegularity.Analysis.Convolution
end
end
end
