-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.FourierParameterJetContinuity
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Operator-valued mixed multilinear norms are controlled by all input evaluations with constant one. -/
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {D : ι → Type*} {G : κ → Type*}
  [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace ℝ (D i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance : NormedAddCommGroup (ContinuousMultilinearMap ℝ G (E →L[ℝ] F)) :=
  ContinuousMultilinearMap.normedAddCommGroup

local instance : NormedSpace ℝ (ContinuousMultilinearMap ℝ G (E →L[ℝ] F)) :=
  ContinuousMultilinearMap.normedSpace

theorem mixed_multilinear_operator_norm_le_from_apply
    (f : ContinuousMultilinearMap ℝ D (ContinuousMultilinearMap ℝ G (E →L[ℝ] F)))
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ ξ : E, ‖(ContinuousLinearMap.compContinuousMultilinearMapL ℝ G
      (E →L[ℝ] F) F (ContinuousLinearMap.apply ℝ F ξ)).compContinuousMultilinearMap f‖ ≤ C * ‖ξ‖) :
    ‖f‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro x
  have hx : 0 ≤ ∏ i, ‖x i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC hx)
  intro y
  have hy : 0 ≤ ∏ i, ‖y i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hC hx) hy)
  intro ξ
  let A := ContinuousLinearMap.compContinuousMultilinearMapL ℝ G (E →L[ℝ] F) F
    (ContinuousLinearMap.apply ℝ F ξ)
  have hs := (A.compContinuousMultilinearMap f).le_opNorm x
  have ht := (A (f x)).le_opNorm y
  calc
    ‖f x y ξ‖ ≤ ‖A (f x)‖ * ∏ i, ‖y i‖ := ht
    _ ≤ (‖A.compContinuousMultilinearMap f‖ * ∏ i, ‖x i‖) * ∏ i, ‖y i‖ :=
      mul_le_mul_of_nonneg_right hs hy
    _ ≤ ((C * ‖ξ‖) * ∏ i, ‖x i‖) * ∏ i, ‖y i‖ := by
      gcongr
      exact hf ξ
    _ = ((C * ∏ i, ‖x i‖) * ∏ i, ‖y i‖) * ‖ξ‖ := by ring

end AVRegularity.CycleComparison.Lift
