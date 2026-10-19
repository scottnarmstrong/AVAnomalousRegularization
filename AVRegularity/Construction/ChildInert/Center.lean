-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.Gen.ParShift
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.SingleModeFlux
import AVRegularity.CycleReference.ChartDerivativeBounded
public import AVRegularity.Statements.Construction.IsFastProfile
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

section
open Homogenization AVRegularity.CycleReference
namespace AVRegularity.ChildInert

/-! The anchor `s_k = l_{m,k} τ_m''` of the slot `k` is within `τ_m''` of every time `t` where the
cutoff `ϖ_{m,k}(t)` is nonzero, and the one-norm of the shear velocity is at most the amplitude
`2π ε^{1+α}/ε`. -/

theorem ocL_ge_five (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) :
    (5 : ℝ) ≤ (ocL α q Λ m : ℝ) := by
  have h : 1 ≤ ⌈ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)⌉₊ :=
    Nat.ceil_pos.2 (Real.rpow_pos_of_pos
      (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ) _)
  have : 5 ≤ ocL α q Λ m := by unfold ocL; omega
  exact_mod_cast this

theorem anchor_dist (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) (k : ℤ) (t : ℝ)
    (hcut : ocCutoff α q Λ m k t ≠ 0) :
    |t - (ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m| ≤ ocTauPP α q Λ m := by
  set h := ocTauPP α q Λ m with hh
  set τ := ocTau α q Λ m with hτ
  have hh0 : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  have hτ0 : 0 < τ := AVRegularity.Construction.Stream.ocTau_pos hΛ
  have hL := ocL_ge_five α q hΛ m
  have hτle : τ ≤ h / 25 := by
    have hτeq : τ = h / (ocL α q Λ m : ℝ) ^ 2 := rfl
    rw [hτeq]
    apply div_le_div_of_nonneg_left hh0.le (by norm_num)
    nlinarith
  have hpos : 0 < 5 / 2 - 2 * |t - (k : ℝ) * τ| / τ := by
    by_contra hneg
    exact hcut (Real.smoothTransition.zero_of_nonpos (not_lt.1 hneg))
  have habs : |t - (k : ℝ) * τ| < 5 * τ / 4 := by
    have h1 : 2 * |t - (k : ℝ) * τ| / τ < 5 / 2 := by linarith
    rw [div_lt_iff₀ hτ0] at h1
    linarith
  set l := ocLabel α q Λ m k with hl
  have hf1 : (l : ℝ) ≤ ((k : ℝ) * τ + (h - τ) / 2) / h := Int.floor_le _
  have hf2 : ((k : ℝ) * τ + (h - τ) / 2) / h < l + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hh0] at hf1
  rw [div_lt_iff₀ hh0] at hf2
  have habs' := abs_lt.1 habs
  rw [abs_le]
  constructor <;> nlinarith [habs'.1, habs'.2]

theorem shearVel_l1_le (α q : ℝ) (Λ m : ℕ) (k : ℤ) (y : Vec 2) :
    ∑ a : Fin 2, |ocShearVel α q Λ m k y a| ≤
      2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ := by
  have hamp : 0 ≤ 2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ := by
    have : 0 ≤ ocEpsilon q Λ m := by
      unfold ocEpsilon; split_ifs
      · norm_num
      · positivity
    have := Real.rpow_nonneg this (1 + α)
    positivity
  by_cases h1 : k % 4 = 1
  · rw [ocShearVel_horizontal h1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero, zero_add]
    rw [abs_mul]
    have hc := Real.abs_cos_le_one (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0)
    rw [abs_of_nonneg hamp]
    calc _ ≤ _ * 1 := mul_le_mul_of_nonneg_left hc hamp
      _ = _ := mul_one _
  · by_cases h3 : k % 4 = 3
    · rw [ocShearVel_vertical h3]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero, add_zero]
      rw [abs_mul, abs_neg]
      have hc := Real.abs_cos_le_one (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
      rw [abs_of_nonneg hamp]
      calc _ ≤ _ * 1 := mul_le_mul_of_nonneg_left hc hamp
        _ = _ := mul_one _
    · have h0 : ocShearVel α q Λ m k y = 0 := by
        have hψ : ocShear α q Λ m k = fun _ => 0 := by
          funext w
          rw [ocShear_sine_formula]
          simp [h1, h3]
        change AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad (ocShear α q Λ m k) y) = 0
        have hg : AVenhance.spaceGrad (fun _ : Vec 2 => (0 : ℝ)) y = 0 := by
          funext i; simp [AVenhance.spaceGrad]
        rw [hψ, hg, Matrix.mulVec_zero]
      rw [h0]
      simpa using hamp

/-! The center of the appended child is below `3bε_{m-1}/4` where the cutoff is nonzero:
the integral of the pulse of level `m-1` between `t` and the anchor
is at most their distance, at most `τ_m''`, and `2 a_{m-1} τ_m'' ≤ b/(64·8π²)`. -/

theorem center_bound (D : OCData) {i : ℕ} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {bw : ℝ}
    (hbw : 0 < bw)
    (hstart : 2 * ocA D.α D.q D.Λ i * ocTauPP D.α D.q D.Λ (i + 1) ≤
      bw / (64 * (8 * Real.pi ^ 2)))
    (pc k : ℤ) (t : ℝ) (hcut : ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0) (ζf : Vec 2) :
    ∑ a : Fin 2, |(D.eps i • D.relDisp i pc (D.slotAnchor (i + 1) k) t ζf) a| <
      (1 + 2) * bw / 4 * D.eps i := by
  have hε : 0 < D.eps i := AVRegularity.Construction.Stream.ocEpsilon_pos hΛ
  set ε := D.eps i with hεd
  set h := ocTauPP D.α D.q D.Λ (i + 1) with hh
  have hh0 : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  set I := ∫ v in t..(D.slotAnchor (i + 1) k), ocPulse D.α D.q D.Λ D.ζ i pc v with hI
  have hrel : ε • D.relDisp i pc (D.slotAnchor (i + 1) k) t ζf =
      I • ocShearVel D.α D.q D.Λ i pc (ε • ζf) := by
    unfold OCData.relDisp
    rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hI1 : |I| ≤ h := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := D.slotAnchor (i + 1) k)
      (f := fun v => ocPulse D.α D.q D.Λ D.ζ i pc v) (C := 1)
      (fun v _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (ocPulse_range hζ pc v).1]
        exact (ocPulse_range hζ pc v).2)
    rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [one_mul, abs_sub_comm]
    exact anchor_dist D.α D.q hΛ (i + 1) k t hcut
  have hsum : ∑ a : Fin 2, |(I • ocShearVel D.α D.q D.Λ i pc (ε • ζf)) a| =
      |I| * ∑ a : Fin 2, |ocShearVel D.α D.q D.Λ i pc (ε • ζf) a| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [abs_mul]
  have hV := shearVel_l1_le D.α D.q D.Λ i pc (ε • ζf)
  have hpow : ε ^ (1 + D.α) = ocA D.α D.q D.Λ i * ε ^ 2 := by
    have h1 : ocA D.α D.q D.Λ i = ε ^ ((1 + D.α) - 2) := rfl
    rw [h1, ← Real.rpow_two, ← Real.rpow_add hε]
    congr 1; ring
  rw [hrel, hsum]
  have hV' : ∑ a : Fin 2, |ocShearVel D.α D.q D.Λ i pc (ε • ζf) a| ≤
      2 * Real.pi * (ocA D.α D.q D.Λ i * ε) := by
    refine hV.trans (le_of_eq ?_)
    change 2 * Real.pi * ε ^ (1 + D.α) * ε⁻¹ = _
    rw [hpow]; field_simp
  have hA0 : 0 ≤ ocA D.α D.q D.Λ i := by
    unfold ocA; exact Real.rpow_nonneg hε.le _
  have hpi := Real.pi_gt_three
  have hmain : |I| * ∑ a : Fin 2, |ocShearVel D.α D.q D.Λ i pc (ε • ζf) a| ≤
      2 * Real.pi * (ocA D.α D.q D.Λ i * h) * ε := by
    calc _ ≤ h * (2 * Real.pi * (ocA D.α D.q D.Λ i * ε)) :=
          mul_le_mul hI1 hV' (Finset.sum_nonneg fun _ _ => abs_nonneg _) hh0.le
      _ = _ := by ring
  have hkey : 2 * Real.pi * (ocA D.α D.q D.Λ i * h) ≤ bw / 2 := by
    have h1 : ocA D.α D.q D.Λ i * h ≤ bw / (64 * (8 * Real.pi ^ 2)) / 2 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    refine h2.trans ?_
    rw [show 2 * Real.pi * (bw / (64 * (8 * Real.pi ^ 2)) / 2) = bw / (512 * Real.pi) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc _ ≤ 2 * Real.pi * (ocA D.α D.q D.Λ i * h) * ε := hmain
    _ ≤ bw / 2 * ε := mul_le_mul_of_nonneg_right hkey hε.le
    _ < (1 + 2) * bw / 4 * ε := by
        have : bw / 2 < (1 + 2) * bw / 4 := by linarith
        exact mul_lt_mul_of_pos_right this hε

end AVRegularity.ChildInert
end
