-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Applications.Global.CompactRangeMain

/-! The terminal schedule pays the inverse weak readout wavelength. -/

@[expose] public noncomputable section

open AVenhance

namespace AVRegularity.EntryTerminal.Route

/-- The schedule's strict exponent margin absorbs the weak readout at every large level. -/
theorem readoutScale : ReadoutScaleStatement := by
  intro X
  refine ⟨128, le_rfl, ?_⟩
  intro A hΛ hA Cread Cid CE
  obtain ⟨a, ha, heps⟩ := Applications.eps_iter_ge X.hq.1 hΛ (A.Jw + 1)
  let K := |Cread * CE| * a ^ (-(1 + X.s))
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ha.le _)
  refine ⟨max Cid K, ?_⟩
  intro C hC
  refine ⟨2, ?_⟩
  intro M hM D hD
  have hCid : Cid ≤ C := (le_max_left _ _).trans hC
  have hKC : K ≤ C := (le_max_right _ _).trans hC
  have hE : 0 < ocEpsilon X.q A.Λ (M - 1) := Applications.eps_pos X.hq.1 hΛ
  have hE1 : ocEpsilon X.q A.Λ (M - 1) ≤ 1 := Applications.eps_le_one X.hq.1 hΛ
  have hchild := heps (M - 1) (by omega)
  rw [show M - 1 + (A.Jw + 1) = M + A.Jw by omega] at hchild
  have hp : ocEpsilon X.q A.Λ (M + A.Jw) ^ (-(1 + X.s)) ≤
      (a * ocEpsilon X.q A.Λ (M - 1) ^ (X.q ^ (A.Jw + 1))) ^ (-(1 + X.s)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos ha (Real.rpow_pos_of_pos hE _)) hchild
      (by linarith only [X.hs₀])
  have hgap := hA.2.2.2.2.2.1.2.1
  change A.PT + X.q ^ (A.Jw + 1) * (1 + X.s) + 2 < A.QT / 2 at hgap
  have hexp : A.PT ≤ X.q ^ (A.Jw + 1) * (-(1 + X.s)) + A.QT / 2 := by
    linarith only [hgap]
  change _ ≤ _ ∧ Cid ≤ C
  refine ⟨?_, hCid⟩
  simp only [OCData.eps, hD.2.1, hD.2.2.1]
  calc
    _ = (Cread * CE) * (ocEpsilon X.q A.Λ (M + A.Jw) ^ (-(1 + X.s)) *
        ocEpsilon X.q A.Λ (M - 1) ^ (A.QT / 2)) := by ring
    _ ≤ |Cread * CE| * (ocEpsilon X.q A.Λ (M + A.Jw) ^ (-(1 + X.s)) *
        ocEpsilon X.q A.Λ (M - 1) ^ (A.QT / 2)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (Real.rpow_nonneg (Applications.eps_pos X.hq.1 hΛ).le _)
        (Real.rpow_nonneg hE.le _))
    _ ≤ |Cread * CE| * ((a * ocEpsilon X.q A.Λ (M - 1) ^ (X.q ^ (A.Jw + 1))) ^ (-(1 + X.s)) *
        ocEpsilon X.q A.Λ (M - 1) ^ (A.QT / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hE.le _))
        (abs_nonneg _)
    _ = K * ocEpsilon X.q A.Λ (M - 1) ^
        (X.q ^ (A.Jw + 1) * (-(1 + X.s)) + A.QT / 2) := by
      rw [Real.mul_rpow ha.le (Real.rpow_nonneg hE.le _), ← Real.rpow_mul hE.le,
        mul_assoc, ← Real.rpow_add hE]
      exact (mul_assoc _ _ _).symm
    _ ≤ K * ocEpsilon X.q A.Λ (M - 1) ^ A.PT :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hE hE1 hexp) hK
    _ ≤ C * ocEpsilon X.q A.Λ (M - 1) ^ A.PT :=
      mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg hE.le _)

end AVRegularity.EntryTerminal.Route
