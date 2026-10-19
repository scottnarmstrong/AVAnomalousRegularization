-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
public import AVRegularity.Weighted.PlaneH1Readouts
public import AVRegularity.Weighted.MetricWordCoefficientArrayBound

/-! The drift coefficient is a fixed bounded linear readout of the velocity vector. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.Weighted

local instance : IsBoundedSMul ℝ ((PiLp 2 (fun _ : Fin 2 => ℝ)) →L[ℝ] ℝ) :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := (PiLp 2 (fun _ : Fin 2 => ℝ)) →L[ℝ] ℝ)

def driftCoefficientEmbedding : Vec 2 →L[ℝ] ((PiLp 2 (fun _ : Fin 2 => ℝ)) →L[ℝ] ℝ) :=
  ∑ k : Fin 2, (ContinuousLinearMap.proj k).smulRight
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) k)

theorem driftCoefficientEmbedding_apply (v : Vec 2 → Vec 2) (x : Vec 2) :
    driftCoefficientEmbedding (v x) = driftCoefficient v x := by
  simp only [driftCoefficientEmbedding, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, driftCoefficient]

theorem coefficient_array_norm_le_card_iterated {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (hC : ContDiff ℝ (j : ℕ) C) (x : Vec 2) :
    ‖coefficientDerivativeArray C j x‖ ≤
      (Fintype.card (DerivativeWord2 j) : ℝ) * ‖iteratedFDeriv ℝ j C x‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    _ ≤ ∑ w : DerivativeWord2 j, ‖coefficientDerivativeArray C j x z w‖ :=
      finitePiLp_norm_le_sum _
    _ ≤ ∑ _w : DerivativeWord2 j, ‖iteratedFDeriv ℝ j C x‖ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro w _
      exact (ContinuousLinearMap.le_opNorm (orderedCoefficientDerivative C j w x) z).trans
        (mul_le_mul_of_nonneg_right (orderedCoefficientDerivative_norm_le C j hC w x)
          (norm_nonneg z))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem driftCoefficient_array_norm_le_iterated (v : Vec 2 → Vec 2) (j : ℕ)
    (hv : ContDiff ℝ (j : ℕ) v) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftCoefficient v) j x‖ ≤
      ((Fintype.card (DerivativeWord2 j) : ℝ) * ‖driftCoefficientEmbedding‖) *
        ‖iteratedFDeriv ℝ j v x‖ := by
  have he : driftCoefficient v = driftCoefficientEmbedding ∘ v :=
    funext (fun x => (driftCoefficientEmbedding_apply v x).symm)
  rw [he]
  have hh := coefficient_array_norm_le_card_iterated _ j
    (driftCoefficientEmbedding.contDiff.comp hv) x
  have hi := driftCoefficientEmbedding.iteratedFDeriv_comp_left (x := x) hv.contDiffAt
    (by norm_cast : (j : WithTop ℕ∞) ≤ j)
  rw [hi] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (driftCoefficientEmbedding.norm_compContinuousMultilinearMap_le _) (by positivity)).trans_eq
      (by ring))

end AVRegularity.Weighted
