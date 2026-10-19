-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real

/-! Finite orthonormal projections in real Hilbert spaces. -/

@[expose] public section

namespace AVRegularity.CoupledEnergy.Galerkin

open MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

local instance twoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance oneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

abbrev HilbertL2 (α : Type*) [MeasurableSpace α] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] (μ : Measure α) := Lp E 2 μ

/-- Coefficients against a finite orthonormal family in a real `L²` Hilbert space. -/
noncomputable def finiteProjectionCoefficients {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ) (x : HilbertL2 α E μ) :
    PiLp 2 (fun _ : ι => ℝ) :=
  WithLp.toLp 2 (fun i => inner ℝ x (v i))

/-- Synthesis from coefficients in a finite orthonormal family. -/
noncomputable def finiteProjectionSynthesis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ) (c : PiLp 2 (fun _ : ι => ℝ)) :
    HilbertL2 α E μ :=
  ∑ i : ι, c i • v i

/-- The continuous coefficient map associated to a finite family. -/
noncomputable def finiteProjectionCoefficientsCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ) :
    HilbertL2 α E μ →L[ℝ] PiLp 2 (fun _ : ι => ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => InnerProductSpace.toDual ℝ _ (v i))

/-- The continuous synthesis map associated to a finite family. -/
noncomputable def finiteProjectionSynthesisCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ) :
    PiLp 2 (fun _ : ι => ℝ) →L[ℝ] HilbertL2 α E μ :=
  ∑ i : ι,
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (v i)).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i)

/-- The finite orthogonal projection determined by an orthonormal family. -/
noncomputable def finiteOrthonormalProjection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ) :
    HilbertL2 α E μ →L[ℝ] HilbertL2 α E μ :=
  (finiteProjectionSynthesisCLM v).comp (finiteProjectionCoefficientsCLM v)

@[simp] theorem finiteProjectionCoefficientsCLM_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ) (x : HilbertL2 α E μ) (i : ι) :
    finiteProjectionCoefficientsCLM v x i = inner ℝ x (v i) := by
  change inner ℝ (v i) x = inner ℝ x (v i)
  exact real_inner_comm _ _

@[simp] theorem finiteProjectionSynthesisCLM_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ) (c : PiLp 2 (fun _ : ι => ℝ)) :
    finiteProjectionSynthesisCLM v c = finiteProjectionSynthesis v c := by
  simp [finiteProjectionSynthesisCLM, finiteProjectionSynthesis,
    sum_apply, PiLp.proj_apply]

@[simp] theorem finiteOrthonormalProjection_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ) (x : HilbertL2 α E μ) :
    finiteOrthonormalProjection v x =
      finiteProjectionSynthesis v (finiteProjectionCoefficients v x) := by
  change finiteProjectionSynthesisCLM v (finiteProjectionCoefficientsCLM v x) = _
  rw [finiteProjectionSynthesisCLM_apply]
  congr 1
  apply PiLp.ext
  intro i
  simp [finiteProjectionCoefficients, finiteProjectionCoefficientsCLM_apply]

/-- An orthonormal finite synthesis recovers its coefficient vector. -/
theorem finiteProjectionCoefficients_synthesis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (c : PiLp 2 (fun _ : ι => ℝ)) :
    finiteProjectionCoefficients v (finiteProjectionSynthesis v c) = c := by
  apply PiLp.ext
  intro i
  change inner ℝ (finiteProjectionSynthesis v c) (v i) = c i
  rw [finiteProjectionSynthesis, sum_inner]
  simp_rw [real_inner_smul_left, hv]
  simp

/-- Orthogonal projection onto a finite orthonormal family is idempotent. -/
theorem finiteOrthonormalProjection_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (x : HilbertL2 α E μ) :
    finiteOrthonormalProjection v (finiteOrthonormalProjection v x) =
      finiteOrthonormalProjection v x := by
  rw [finiteOrthonormalProjection_apply, finiteOrthonormalProjection_apply]
  rw [finiteProjectionCoefficients_synthesis v hv]

/-- The finite orthogonal projection is self-adjoint in the ambient Hilbert inner product. -/
theorem finiteOrthonormalProjection_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ) (x y : HilbertL2 α E μ) :
    inner ℝ (finiteOrthonormalProjection v x) y =
      inner ℝ x (finiteOrthonormalProjection v y) := by
  rw [finiteOrthonormalProjection_apply, finiteOrthonormalProjection_apply]
  unfold finiteProjectionSynthesis
  rw [inner_sum, sum_inner]
  simp only [real_inner_smul_left, real_inner_smul_right]
  simp [finiteProjectionCoefficients, real_inner_comm]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteProjectionSynthesis_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (c d : PiLp 2 (fun _ : ι => ℝ)) :
    inner ℝ (finiteProjectionSynthesis v c) (finiteProjectionSynthesis v d) =
      inner ℝ c d := by
  classical
  rw [finiteProjectionSynthesis, finiteProjectionSynthesis, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, hv]
  simp [PiLp.inner_apply, mul_comm]

theorem finiteProjectionSynthesis_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (c : PiLp 2 (fun _ : ι => ℝ)) :
    ‖finiteProjectionSynthesis v c‖ = ‖c‖ := by
  have hinner := finiteProjectionSynthesis_inner v hv c c
  have hleft := real_inner_self_eq_norm_sq (finiteProjectionSynthesis v c)
  have hright := real_inner_self_eq_norm_sq c
  rw [hinner] at hleft
  nlinarith [hleft, hright, norm_nonneg (finiteProjectionSynthesis v c), norm_nonneg c]

/-- Orthogonal projection coefficients do not increase the Hilbert norm. -/
theorem finiteProjectionCoefficients_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (x : HilbertL2 α E μ) :
    ‖finiteProjectionCoefficients v x‖ ≤ ‖x‖ := by
  classical
  let c := finiteProjectionCoefficients v x
  let s := finiteProjectionSynthesis v c
  have hc (i : ι) : c i = inner ℝ x (v i) := by
    simp [c, finiteProjectionCoefficients]
  have hxs : inner ℝ (x - s) s = 0 := by
    rw [inner_sub_left]
    have hfirst : inner ℝ x s = ∑ i : ι, c i ^ 2 := by
      rw [show s = ∑ i : ι, c i • v i by rfl, inner_sum]
      simp_rw [real_inner_smul_right, hc]
      simp [pow_two]
    have hsecond : inner ℝ s s = ∑ i : ι, c i ^ 2 := by
      have h := finiteProjectionSynthesis_inner v hv c c
      calc
        inner ℝ s s = inner ℝ c c := by simpa [s] using h
        _ = ∑ i : ι, c i ^ 2 := by
          rw [PiLp.inner_apply]
          simp [pow_two]
    rw [hfirst, hsecond]
    ring
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - s) s hxs
  have hpyth : ‖x‖ ^ 2 = ‖x - s‖ ^ 2 + ‖s‖ ^ 2 := by
    have hx : ‖x‖ * ‖x‖ = ‖x - s‖ * ‖x - s‖ + ‖s‖ * ‖s‖ := by
      simpa [sub_add_cancel] using hp
    nlinarith
  have hs := finiteProjectionSynthesis_norm v hv c
  have hle : ‖c‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← hs]
    nlinarith [hpyth, sq_nonneg ‖x - s‖]
  exact (sq_le_sq₀ (norm_nonneg c) (norm_nonneg x)).mp hle

theorem finiteOrthonormalProjection_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → HilbertL2 α E μ)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (x : HilbertL2 α E μ) :
    ‖finiteOrthonormalProjection v x‖ ≤ ‖x‖ := by
  rw [finiteOrthonormalProjection_apply]
  calc
    ‖finiteProjectionSynthesis v (finiteProjectionCoefficients v x)‖ =
        ‖finiteProjectionCoefficients v x‖ :=
          finiteProjectionSynthesis_norm v hv _
    _ ≤ ‖x‖ := finiteProjectionCoefficients_norm_le v hv x

end AVRegularity.CoupledEnergy.Galerkin
