-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.PlaneH1Readouts
public import AVRegularity.Weighted.MetricWordCoefficientArrayBound
public import AVRegularity.CoupledEnergy.Variational.TorusCoupledFluxValue

/-! Finite velocity jets bound the actual Hilbert fiber drift coefficient. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.Weighted

namespace AVRegularity.EntryWeakProofs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local instance : IsBoundedSMul ℝ ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] E) :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] E))

theorem driftFiberCoefficient_eq_sum (v : Vec 2 → Vec 2) :
    driftFiberCoefficient (E := E) v = fun x => ∑ k : Fin 2, v x k •
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  rw [driftFiberCoefficient_apply]
  simp

theorem finite_driftFiberCoefficient_contDiff (K : ℕ) (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (K : ℕ∞) v) :
    ContDiff ℝ (K : ℕ∞) (driftFiberCoefficient (E := E) v) := by
  rw [driftFiberCoefficient_eq_sum]
  exact ContDiff.sum (fun k _ => (contDiff_pi.mp hv k).smul_const _)

theorem finite_driftFiberCoefficient_word_bound (j : ℕ) (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (j : ℕ∞) v) (Cv : ℝ)
    (hb : ∀ k x, ‖iteratedFDeriv ℝ j (fun y => v y k) x‖ ≤ Cv)
    (w : DerivativeWord2 j) (x : Vec 2) :
    ‖orderedCoefficientDerivative (driftFiberCoefficient (E := E) v) j w x‖ ≤
      ∑ k : Fin 2, Cv * ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k‖ := by
  rw [driftFiberCoefficient_eq_sum, orderedCoefficientDerivative_finset_sum Finset.univ _ j
    (fun k _ => (contDiff_pi.mp hv k).smul_const _) w]
  dsimp only
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [congrFun (orderedCoefficientDerivative_smul_const (fun y => v y k) j
    (contDiff_pi.mp hv k) _ w) x, norm_smul]
  exact mul_le_mul_of_nonneg_right
    ((orderedScalarDerivative_norm_le _ j (contDiff_pi.mp hv k) w x).trans (hb k x))
    (norm_nonneg _)

theorem finite_driftFiberCoefficient_array_bound (j : ℕ) (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (j : ℕ∞) v) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hb : ∀ k x, ‖iteratedFDeriv ℝ j (fun y => v y k) x‖ ≤ Cv) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftFiberCoefficient (E := E) v) j x‖ ≤
      (Fintype.card (DerivativeWord2 j) : ℝ) *
        (∑ k : Fin 2, Cv * ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  calc
    _ ≤ ∑ w : DerivativeWord2 j,
        ‖coefficientDerivativeArray (driftFiberCoefficient (E := E) v) j x u w‖ :=
      finitePiLp_norm_le_sum _
    _ ≤ ∑ _w : DerivativeWord2 j,
        (∑ k : Fin 2, Cv * ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k‖) * ‖u‖ := by
      apply Finset.sum_le_sum
      intro w _
      exact (ContinuousLinearMap.le_opNorm _ u).trans
        (mul_le_mul_of_nonneg_right
          (finite_driftFiberCoefficient_word_bound j v hv Cv hb w x) (norm_nonneg u))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end AVRegularity.EntryWeakProofs
