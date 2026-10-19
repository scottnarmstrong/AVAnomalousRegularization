-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Velocity.Port.StreamRegularity
public import AVRegularity.Velocity.Port.Section2FlowRegularity
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Section4.Amnr.MaterialCalculus
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
section
@[expose] public section
noncomputable section
open Homogenization AVenhance AVenhance.Infra.Section4
namespace AVRegularity.Velocity

/-! Low-order consequences of the ported spatial/material words. -/

/-- Spatial word of length one is smooth on space-time. -/
theorem spatial_word_one_smooth {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrOp b (some i) f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Eulerian time derivative of a spatial gradient: the material commutator
and vertical differential expansion provide its three actual terms. -/
theorem gradient_time_deriv_formula {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin 2) (t : ℝ) (x : Vec 2) :
    deriv (fun r => amnrOp b (some i) f (r, x)) t =
      amnrOp b (some i) (amnrOp b none f) (t, x) -
        ∑ p : Fin 2, amnrVelocityGradient b p i (t, x) * amnrOp b (some p) f (t, x) -
        ∑ p : Fin 2, b (t, x) p * amnrOp b (some p) (amnrOp b (some i) f) (t, x) := by
  let g := amnrOp b (some i) f
  have hg := spatial_word_one_smooth hf i (b := b)
  have htime := (hg.differentiable (by simp) (t, x)).hasFDerivAt.comp t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasFDerivAt
  have ht : deriv (fun r => g (r, x)) t = fderiv ℝ g (t, x) (1, 0) := by
    simpa [g, Function.comp_def] using htime.hasDerivAt.deriv
  have hv := amnrFDeriv_vertical g (t, x) (b (t, x))
  have hsplit : amnrOp b none g (t, x) =
      fderiv ℝ g (t, x) (1, 0) +
        ∑ p : Fin 2, b (t, x) p * amnrOp b (some p) g (t, x) := by
    change fderiv ℝ g (t, x) (1, b (t, x)) = _
    rw [show ((1, b (t, x)) : AmnrSpace) = (1, 0) + (0, b (t, x)) by simp,
      map_add, hv]
    rfl
  have hc := amnr_material_spatial_commutator
    (hb.differentiable (by simp) (t, x)) (hf.of_le (by simp)).contDiffAt i
  change amnrOp b none g (t, x) = _ at hc
  rw [ht]
  linarith only [hc, hsplit]

/-- Quantitative version of the exact Eulerian derivative identity. -/
theorem gradient_time_deriv_bound {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {A H T B G : ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G)
    (ha : ∀ p z, |amnrOp b (some p) f z| ≤ A)
    (hh : ∀ p i z, |amnrOp b (some p) (amnrOp b (some i) f) z| ≤ H)
    (ht : ∀ i z, |amnrOp b (some i) (amnrOp b none f) z| ≤ T)
    (hbnd : ∀ p z, |b z p| ≤ B)
    (hgb : ∀ p i z, |amnrVelocityGradient b p i z| ≤ G)
    (i : Fin 2) (t : ℝ) (x : Vec 2) :
    |deriv (fun r => amnrOp b (some i) f (r, x)) t| ≤ T + 2 * G * A + 2 * B * H := by
  rw [gradient_time_deriv_formula hb hf i t x]
  have hsumG : |∑ p : Fin 2,
      amnrVelocityGradient b p i (t, x) * amnrOp b (some p) f (t, x)| ≤ 2 * G * A := by
    calc
      _ ≤ ∑ p : Fin 2, |amnrVelocityGradient b p i (t, x) *
          amnrOp b (some p) f (t, x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Fin 2, G * A := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul (hgb p i _) (ha p _) (abs_nonneg _) hG
      _ = _ := by simp; ring
  have hsumB : |∑ p : Fin 2, b (t, x) p *
      amnrOp b (some p) (amnrOp b (some i) f) (t, x)| ≤ 2 * B * H := by
    calc
      _ ≤ ∑ p : Fin 2, |b (t, x) p *
          amnrOp b (some p) (amnrOp b (some i) f) (t, x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Fin 2, B * H := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul (hbnd p _) (hh p i _) (abs_nonneg _) hB
      _ = _ := by simp; ring
  exact (abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add (ht i _) hsumG)) hsumB)

/-- Two spatial coordinate bounds give a scalar gradient's spatial Lipschitz bound. -/
theorem gradient_spatial_lipschitz {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {H : ℝ} (hH : 0 ≤ H)
    (hh : ∀ p i z, |amnrOp b (some p) (amnrOp b (some i) f) z| ≤ H)
    (i : Fin 2) (t : ℝ) (x y : Vec 2) :
    |amnrOp b (some i) f (t, x) - amnrOp b (some i) f (t, y)| ≤
      2 * H * ‖x - y‖ := by
  let g := amnrOp b (some i) f
  have hg := spatial_word_one_smooth hf i (b := b)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec 2 => g (t, z)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  have hbnd (z : Vec 2) : ‖fderiv ℝ (fun w => g (t, w)) z‖ ≤ 2 * H := by
    apply timeIncrement_clm_norm_le_two_basis hH
    · have he := amnrOp_space (b := b) (hg.differentiable (by simp) (t, z)) 0
      have h := hh 0 i (t, z)
      rw [he] at h
      exact h
    · have he := amnrOp_space (b := b) (hg.differentiable (by simp) (t, z)) 1
      have h := hh 1 i (t, z)
      rw [he] at h
      exact h
  have hL : LipschitzWith (2 * H).toNNReal (fun z : Vec 2 => g (t, z)) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
    intro z
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
    exact hbnd z
  simpa only [dist_eq_norm, Real.norm_eq_abs,
    Real.coe_toNNReal (2 * H) (mul_nonneg (by norm_num) hH)]
    using hL.dist_le_mul x y

/-- A scalar Eulerian derivative bound gives its time Lipschitz bound. -/
theorem gradient_time_lipschitz {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {T : ℝ}
    (ht : ∀ i t x, |deriv (fun r => amnrOp b (some i) f (r, x)) t| ≤ T)
    (i : Fin 2) (t u : ℝ) (x : Vec 2) :
    |amnrOp b (some i) f (t, x) - amnrOp b (some i) f (u, x)| ≤ T * |t - u| := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun r => amnrOp b (some i) f (r, x)) :=
    (spatial_word_one_smooth hf i (b := b)).comp (contDiff_id.prodMk contDiff_const)
  have hL : LipschitzWith T.toNNReal (fun r => amnrOp b (some i) f (r, x)) := by
    apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (by simp))
    intro r
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ ((abs_nonneg _).trans (ht i r x))]
    exact ht i r x
  have hT : 0 ≤ T := (abs_nonneg _).trans (ht i t x)
  simpa only [Real.dist_eq, Real.coe_toNNReal _ hT] using hL.dist_le_mul t u

end AVRegularity.Velocity
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance AVenhance.Infra.Section4
open AVRegularity.Velocity.Port
open AVRegularity.Velocity.Port.MaterialAuxiliaryWords
open AVRegularity.Velocity.Port.Section2Induction
namespace AVRegularity.Velocity

/-- Stream increment on the joint coordinate carrier. -/
def jointStreamIncrement (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ) : AmnrSpace → ℝ :=
  fun z => Φ m z.1 z.2 - Φ (m - 1) z.1 z.2

/-- The preceding finite velocity on the joint carrier. -/
def previousJointVelocity (Φ : ℕ → ℝ → Vec 2 → ℝ) (m : ℕ) : AmnrSpace → Vec 2 :=
  fun z => streamVel (Φ (m - 1)) z.1 z.2

/-- One common constant for the low spatial/material increment words. -/
def incrementJetConstant {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) : ℝ := materialAuxStreamMixedCurrentConstant D 2

theorem incrementJetConstant_nonneg {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) : 0 ≤ incrementJetConstant D :=
  materialAuxStreamMixedCurrentConstant_nonneg D 2

theorem jointStreamIncrement_smooth {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (jointStreamIncrement Φ m) :=
  (streamSeq_admissible D.hζ D.hΛ hseq m).1.sub
    (streamSeq_admissible D.hζ D.hΛ hseq (m - 1)).1

theorem previousJointVelocity_smooth {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (previousJointVelocity Φ m) :=
  (AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (streamSeq_admissible D.hζ D.hΛ hseq (m - 1))).smooth

private theorem amplitude_times_epsilon {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (m : ℕ) :
    D.velocityAmplitude m * D.epsilon m = D.epsilon m ^ α := by
  rw [D.velocityAmplitude_eq]
  simpa using (Real.rpow_add (D.epsilon_pos m) (α - 1) 1).symm

/-- The first spatial word has the velocity increment's amplitude. -/
theorem increment_gradient_word_bound {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ)
    {C : ℝ} (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (i : Fin 2) (z : AmnrSpace) :
    |amnrOp (previousJointVelocity Φ m) (some i) (jointStreamIncrement Φ m) z| ≤
      incrementJetConstant D * D.epsilon m ^ α := by
  have hN : 3 ≤ AVenhance.Nstar (1 + α) := by have := D.nstar_ge_256; omega
  have h := material_aux_streamIncrement_mixed_current_abs_le_of_A3
    D hseq hreg hm [i] 0 (Nspace := 2) (by simp) (by simp only [List.length_cons, List.length_nil]; omega) z
  simp only [amnrMixedWord, List.map_cons, List.map_nil, List.replicate_zero,
    List.append_nil, amnrWord, List.length_cons, List.length_nil, Nat.zero_add, pow_zero,
    pow_one, mul_one] at h
  have he := D.epsilon_pos m
  have hid : (incrementJetConstant D * D.velocityAmplitude m * D.epsilon m ^ 2) *
      (D.epsilon m)⁻¹ = incrementJetConstant D * D.epsilon m ^ α := by
    rw [← amplitude_times_epsilon D m]
    field_simp [ne_of_gt he]
  change |amnrOp (previousJointVelocity Φ m) (some i) (jointStreamIncrement Φ m) z| ≤
    (incrementJetConstant D * D.velocityAmplitude m * D.epsilon m ^ 2) *
      (D.epsilon m)⁻¹ at h
  rwa [hid] at h

/-- Two spatial letters give the joint Lipschitz scale. -/
theorem increment_hessian_word_bound {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ)
    {C : ℝ} (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (p i : Fin 2) (z : AmnrSpace) :
    |amnrOp (previousJointVelocity Φ m) (some p)
      (amnrOp (previousJointVelocity Φ m) (some i) (jointStreamIncrement Φ m)) z| ≤
      incrementJetConstant D * D.velocityAmplitude m := by
  have hN : 2 ≤ AVenhance.Nstar (1 + α) := by have := D.nstar_ge_256; omega
  have h := material_aux_streamIncrement_mixed_current_abs_le_of_A3
    D hseq hreg hm [p, i] 0 (Nspace := 2) (by simp) (by simp only [List.length_cons, List.length_nil]; omega) z
  simp only [amnrMixedWord, List.map_cons, List.map_nil, List.replicate_zero,
    List.append_nil, amnrWord, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, pow_zero,
    mul_one] at h
  have he := D.epsilon_pos m
  have hid : (incrementJetConstant D * D.velocityAmplitude m * D.epsilon m ^ 2) *
      (D.epsilon m)⁻¹ ^ 2 = incrementJetConstant D * D.velocityAmplitude m := by
    field_simp [ne_of_gt he]
  change |amnrOp (previousJointVelocity Φ m) (some p)
      (amnrOp (previousJointVelocity Φ m) (some i) (jointStreamIncrement Φ m)) z| ≤
    (incrementJetConstant D * D.velocityAmplitude m * D.epsilon m ^ 2) *
      (D.epsilon m)⁻¹ ^ 2 at h
  rwa [hid] at h

/-- One spatial and one material letter are bounded at the Lipschitz scale. -/
theorem increment_spatial_material_word_bound {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ)
    {C : ℝ} (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (i : Fin 2) (z : AmnrSpace) :
    |amnrOp (previousJointVelocity Φ m) (some i)
      (amnrOp (previousJointVelocity Φ m) none (jointStreamIncrement Φ m)) z| ≤
      incrementJetConstant D * D.velocityAmplitude m := by
  have hN : 3 ≤ AVenhance.Nstar (1 + α) := by have := D.nstar_ge_256; omega
  have h := material_aux_streamIncrement_mixed_current_abs_le_of_A3
    D hseq hreg hm [i] 1 (Nspace := 2) (by simp) (by simp only [List.length_cons, List.length_nil]; omega) z
  simp only [amnrMixedWord, List.map_cons, List.map_nil, List.replicate_one,
    List.cons_append, List.nil_append, amnrWord, List.length_cons, List.length_nil, Nat.zero_add,
    pow_one] at h
  have he := D.epsilon_pos m
  have hid : (incrementJetConstant D * D.velocityAmplitude m * D.epsilon m ^ 2) *
      (D.epsilon m)⁻¹ * D.velocityAmplitude m =
      incrementJetConstant D * D.epsilon m ^ α * D.velocityAmplitude m := by
    rw [← amplitude_times_epsilon D m]
    field_simp [ne_of_gt he]
  change |amnrOp (previousJointVelocity Φ m) (some i)
      (amnrOp (previousJointVelocity Φ m) none (jointStreamIncrement Φ m)) z| ≤
    (incrementJetConstant D * D.velocityAmplitude m * D.epsilon m ^ 2) *
      (D.epsilon m)⁻¹ * D.velocityAmplitude m at h
  rw [hid] at h
  refine h.trans ?_
  have hp := Real.rpow_le_one he.le (D.epsilon_le_one m) D.hαpos.le
  have ha : 0 ≤ D.velocityAmplitude m := by rw [D.velocityAmplitude_eq]; positivity
  have hK := incrementJetConstant_nonneg D
  nlinarith [mul_le_mul_of_nonneg_left hp hK]

/-- Rotation identifies the increment velocity with its spatial word. -/
theorem increment_velocity_components {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (t : ℝ) (x : Vec 2) :
    streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x =
      ![-amnrOp (previousJointVelocity Φ m) (some 1) (jointStreamIncrement Φ m) (t, x),
        amnrOp (previousJointVelocity Φ m) (some 0) (jointStreamIncrement Φ m) (t, x)] := by
  have hs := amnrOp_space (b := previousJointVelocity Φ m) ((jointStreamIncrement_smooth D hseq m).differentiable
    (by simp) (t, x))
  have hcur := (streamSeq_admissible D.hζ D.hΛ hseq m).1.comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hprev := (streamSeq_admissible D.hζ D.hΛ hseq (m - 1)).1.comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  rw [hs 1, hs 0]
  have hder := fderiv_sub (hcur.differentiable (by simp) x)
    (hprev.differentiable (by simp) x)
  change fderiv ℝ (fun y => Φ m t y - Φ (m - 1) t y) x =
    fderiv ℝ (Φ m t) x - fderiv ℝ (Φ (m - 1) t) x at hder
  ext i
  fin_cases i <;>
    simp [streamVel, sigmaMat, spaceGrad, dotProduct,
      Fin.sum_univ_two, jointStreamIncrement, hder]
  ring

end AVRegularity.Velocity
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance AVenhance.Infra.Section4
open AVRegularity.Velocity.Port.Section2Induction
namespace AVRegularity.Velocity

/-- The low-order stream display bounds every finite velocity uniformly. -/
theorem finite_velocity_bound {α s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (hC : 0 < C)
    (hreg : OCStreamRegularityBounds D C Φ) (m : ℕ) (t : ℝ) (x : Vec 2) :
    ‖streamVel (Φ m) t x‖ ≤ C ^ 2 := by
  by_cases hm : 1 ≤ m
  · have hf : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) :=
      (streamSeq_admissible D.hζ D.hΛ hseq m).1.comp
        (contDiff_const.prodMk contDiff_id)
    have he := D.epsilon_pos m
    have hR : 0 < C * (D.epsilon m)⁻¹ := by positivity
    have hcoord (j : Fin 2) : ‖fderiv ℝ (Φ m t) x (basisVec j)‖ ≤ C ^ 2 / 4 := by
      have h := barNorm_iterated_pointwise (f := Φ m t) (fun _ : Fin 1 => j)
        (continuous_iteratedCoordinate hf (fun _ => j)) hR
        (by positivity : 0 ≤ C * D.epsilon m)
        (by simpa using (hreg m hm t).2.2 1 (by norm_num)) x
      have hid : (C * D.epsilon m) / (4 * (C * (D.epsilon m)⁻¹)⁻¹) = C ^ 2 / 4 := by
        field_simp [hC.ne', he.ne']
      simpa only [iteratedFDeriv_one_apply, Nat.factorial_one, Nat.cast_one,
        one_add_one_eq_two, show (2 : ℝ) ^ 2 / 1 = 4 by norm_num, pow_one, hid] using h
    have hder := timeIncrement_clm_norm_le_two_basis (by positivity : 0 ≤ C ^ 2 / 4)
      (hcoord 0) (hcoord 1)
    rw [streamVel_eq_timeIncrementRotate]
    exact (timeIncrementRotate_norm_le _).trans (by nlinarith [hder])
  · have hz : m = 0 := by omega
    subst m
    rw [hseq.1]
    have hzv : streamVel (fun _ _ => 0) t x = (0 : Vec 2) := by
      ext i
      fin_cases i <;> simp [streamVel, spaceGrad]
    rw [hzv, norm_zero]
    exact sq_nonneg C

/-- The amplitude increases with the level because its exponent is negative. -/
theorem previous_amplitude_le {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {m : ℕ} (hm : 1 ≤ m) :
    D.velocityAmplitude (m - 1) ≤ D.velocityAmplitude m := by
  have hr := D.epsilon_ratio m hm
  have hΛ : (1 : ℝ) ≤ Λ := by exact_mod_cast (show 1 ≤ Λ by have := D.hΛ; omega)
  have he := D.epsilon_pos m
  have hmul := (le_div_iff₀ he).mp hr
  have heprev : D.epsilon m ≤ D.epsilon (m - 1) :=
    (le_mul_of_one_le_left he.le hΛ).trans hmul
  rw [D.velocityAmplitude_eq, D.velocityAmplitude_eq]
  exact Real.rpow_le_rpow_of_nonpos he heprev (by linarith [D.hαlt])

end AVRegularity.Velocity
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance AVenhance.Infra.Section4
open AVRegularity.Velocity.Port.Section2Induction
open AVRegularity.Velocity.Port.MaterialAuxiliaryFlow
namespace AVRegularity.Velocity

/-- Time differentiation budget after expanding the material commutator. -/
def incrementTimeConstant {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (C : ℝ) : ℝ :=
  incrementJetConstant D * (1 + 2 * amnrSpatialVelocityConstant 0 + 2 * C ^ 2)

theorem incrementTimeConstant_nonneg {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (C : ℝ) : 0 ≤ incrementTimeConstant D C := by
  have hK := incrementJetConstant_nonneg D
  have hG := amnrSpatialVelocityConstant_pos 0
  unfold incrementTimeConstant
  positivity

/-- The actual Eulerian time derivative of an increment gradient is bounded
at the same scale as its spatial derivative. -/
theorem increment_gradient_time_bound {α s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (hC : 0 < C)
    (hreg : OCStreamRegularityBounds D C Φ) {m : ℕ} (hm : 1 ≤ m)
    (i : Fin 2) (t : ℝ) (x : Vec 2) :
    |deriv (fun r => amnrOp (previousJointVelocity Φ m) (some i)
      (jointStreamIncrement Φ m) (r, x)) t| ≤
      incrementTimeConstant D C * D.velocityAmplitude m := by
  let K := incrementJetConstant D
  let G := amnrSpatialVelocityConstant 0
  let e := D.epsilon m
  let a := D.velocityAmplitude m
  let ap := D.velocityAmplitude (m - 1)
  have hK : 0 ≤ K := incrementJetConstant_nonneg D
  have hG : 0 ≤ G := (amnrSpatialVelocityConstant_pos 0).le
  have ha : 0 < a := by
    dsimp [a]
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos m) _
  have hap : 0 < ap := by
    dsimp [ap]
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_pos_of_pos (D.epsilon_pos _) _
  have hbnd : ∀ p z, |previousJointVelocity Φ m z p| ≤ C ^ 2 := by
    intro p z
    have hn := norm_le_pi_norm (previousJointVelocity Φ m z) p
    exact (show |previousJointVelocity Φ m z p| ≤ ‖previousJointVelocity Φ m z‖ by
      simpa only [Real.norm_eq_abs] using hn).trans
      (finite_velocity_bound D hseq hC hreg (m - 1) z.1 z.2)
  have hgb : ∀ p i z, |amnrVelocityGradient (previousJointVelocity Φ m) p i z| ≤ G * ap := by
    intro p i z
    have h := previous_velocityGradient_spatial_bound hseq hreg hm []
      (N := 0) (by simp) p i z
    change |amnrVelocityGradient (fun y => streamVel (Φ (m - 1)) y.1 y.2) p i z| ≤
      amnrSpatialVelocityConstant 0 * D.velocityAmplitude (m - 1)
    simpa only [List.map_nil, amnrWord, List.length_nil, pow_zero, mul_one] using h
  have h := gradient_time_deriv_bound (previousJointVelocity_smooth D hseq m)
    (jointStreamIncrement_smooth D hseq m) (sq_nonneg C) (mul_nonneg hG hap.le)
    (increment_gradient_word_bound D hseq hreg hm)
    (increment_hessian_word_bound D hseq hreg hm)
    (increment_spatial_material_word_bound D hseq hreg hm) hbnd hgb i t x
  refine h.trans ?_
  have hep : e ^ α ≤ 1 :=
    Real.rpow_le_one (D.epsilon_pos m).le (D.epsilon_le_one m) D.hαpos.le
  have hprev : ap ≤ a := previous_amplitude_le D hm
  have hpa : ap * e ^ α ≤ a :=
    (mul_le_of_le_one_right hap.le hep).trans hprev
  have hterm : 2 * (G * ap) * (K * e ^ α) ≤ 2 * G * K * a := by
    calc
      _ = (2 * G * K) * (ap * e ^ α) := by ring
      _ ≤ (2 * G * K) * a := mul_le_mul_of_nonneg_left hpa (by positivity)
      _ = _ := by ring
  change K * a + 2 * (G * ap) * (K * e ^ α) + 2 * C ^ 2 * (K * a) ≤ _
  calc
    _ ≤ K * a + 2 * G * K * a + 2 * C ^ 2 * (K * a) := by linarith only [hterm]
    _ = incrementTimeConstant D C * D.velocityAmplitude m := by
      dsimp [incrementTimeConstant, K, G, a]
      ring

end AVRegularity.Velocity
end
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.Velocity

/-! The three spatial stream estimates for the literal OC construction. -/

/-- OC analogue of the upstream stream-regularity theorem, with every
primitive scale/cutoff premise discharged by the construction. -/
theorem stream_regularity
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
      (∀ n : ℕ, barNorm n (2 ^ 7 * (ocEpsilon q Λ m)⁻¹)
        (Φ m t - Φ (m - 1) t) ≤ ENNReal.ofReal (10 * ocEpsilon q Λ m ^ (1 + α))) ∧
      (∀ n : ℕ, 2 ≤ n → barNorm n (2 ^ 8 * (ocEpsilon q Λ m)⁻¹) (Φ m t) ≤
        ENNReal.ofReal (2 ^ 5 * ocA α q Λ m * ocEpsilon q Λ m ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) ∧
      (∀ n : ℕ, n ≤ 1 → barNorm n (C * (ocEpsilon q Λ m)⁻¹) (Φ m t) ≤
        ENNReal.ofReal (C * ocEpsilon q Λ m ^ n)) := by
  let D := ocJetRecursionData α s hα₀ hα₁ hs₀ hs₁ q hq Λ hΛ ζ hζ
  let C : ℝ := 11 + 768 / α
  have hC : 1 ≤ C := by
    have hnonneg : 0 ≤ 768 / α := div_nonneg (by norm_num) hα₀.le
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  exact Port.StreamRegularity.stream_regularity D hΦ

end AVRegularity.Velocity
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance AVenhance.Infra.Section4
open AVRegularity.Velocity.Port.Section2Induction
namespace AVRegularity.Velocity

/-- The sup norm of `Vec 2` is at most the Euclidean norm. -/
theorem velocity_norm_le_vecEuclidean (v : Vec 2) : ‖v‖ ≤ Real.sqrt (vecNormSq v) := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  have hsq := sq_apply_le_vecNormSq v i
  have hroot := Real.sq_sqrt (vecNormSq_nonneg v)
  have habs : |v i| ≤ Real.sqrt (vecNormSq v) := by
    have habsSq : |v i| ^ 2 ≤ Real.sqrt (vecNormSq v) ^ 2 := by
      simpa [sq_abs] using hsq.trans_eq hroot.symm
    nlinarith [abs_nonneg (v i), Real.sqrt_nonneg (vecNormSq v)]
  simpa only [Real.norm_eq_abs] using habs

private theorem rotate_norm_le {a b R : ℝ} (hR : 0 ≤ R)
    (ha : |a| ≤ R) (hb : |b| ≤ R) : ‖(![-a, b] : Vec 2)‖ ≤ R := by
  rw [pi_norm_le_iff_of_nonneg hR]
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

private theorem rotate_sub_norm_le {a b c d R : ℝ} (hR : 0 ≤ R)
    (ha : |a - c| ≤ R) (hb : |b - d| ≤ R) :
    ‖(![-a, b] : Vec 2) - ![-c, d]‖ ≤ R := by
  have heq : (![-a, b] : Vec 2) - ![-c, d] = ![-(a - c), b - d] := by
    ext i
    fin_cases i <;> simp
    ring
  rw [heq]
  exact rotate_norm_le hR ha hb

/-- A common amplitude and joint Lipschitz constant. -/
def jointIncrementConstant {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (C : ℝ) : ℝ :=
  2 * incrementJetConstant D + incrementTimeConstant D C

theorem jointIncrementConstant_nonneg {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (C : ℝ) : 0 ≤ jointIncrementConstant D C := by
  unfold jointIncrementConstant
  exact add_nonneg (mul_nonneg (by norm_num) (incrementJetConstant_nonneg D))
    (incrementTimeConstant_nonneg D C)

/-- The ported low-order jets bound the actual velocity increment amplitude. -/
theorem velocity_increment_amplitude {α s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (hreg : OCStreamRegularityBounds D C Φ)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (x : Vec 2) :
    ‖streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x‖ ≤
      incrementJetConstant D * D.epsilon m ^ α := by
  rw [increment_velocity_components D hseq]
  exact rotate_norm_le (mul_nonneg (incrementJetConstant_nonneg D)
    (Real.rpow_nonneg (D.epsilon_pos m).le _))
    (increment_gradient_word_bound D hseq hreg hm 1 (t, x))
    (increment_gradient_word_bound D hseq hreg hm 0 (t, x))

/-- Joint time-space Lipschitz bound at the increment wavelength. -/
theorem velocity_increment_joint_lipschitz {α s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (hC : 0 < C)
    (hreg : OCStreamRegularityBounds D C Φ) {m : ℕ} (hm : 1 ≤ m)
    (t u : ℝ) (x y : Vec 2) :
    ‖(streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) -
      (streamVel (Φ m) u y - streamVel (Φ (m - 1)) u y)‖ ≤
      jointIncrementConstant D C *
        (|t - u| + Real.sqrt (vecNormSq (x - y))) * D.velocityAmplitude m := by
  let K := incrementJetConstant D
  let L := incrementTimeConstant D C
  let a := D.velocityAmplitude m
  have hK : 0 ≤ K := incrementJetConstant_nonneg D
  have hL : 0 ≤ L := incrementTimeConstant_nonneg D C
  have ha : 0 ≤ a := by
    dsimp [a]
    rw [D.velocityAmplitude_eq]
    exact Real.rpow_nonneg (D.epsilon_pos m).le _
  have hJ : 0 ≤ jointIncrementConstant D C := jointIncrementConstant_nonneg D C
  have hscalar (i : Fin 2) :
      |amnrOp (previousJointVelocity Φ m) (some i) (jointStreamIncrement Φ m) (t, x) -
        amnrOp (previousJointVelocity Φ m) (some i) (jointStreamIncrement Φ m) (u, y)| ≤
      jointIncrementConstant D C *
        (|t - u| + Real.sqrt (vecNormSq (x - y))) * a := by
    have htime := gradient_time_lipschitz (jointStreamIncrement_smooth D hseq m)
      (increment_gradient_time_bound D hseq hC hreg hm) i t u x
    have hspace := gradient_spatial_lipschitz (jointStreamIncrement_smooth D hseq m)
      (mul_nonneg hK ha) (increment_hessian_word_bound D hseq hreg hm) i u x y
    have htriangle := abs_sub_le
      (amnrOp (previousJointVelocity Φ m) (some i) (jointStreamIncrement Φ m) (t, x))
      (amnrOp (previousJointVelocity Φ m) (some i) (jointStreamIncrement Φ m) (u, x))
      (amnrOp (previousJointVelocity Φ m) (some i) (jointStreamIncrement Φ m) (u, y))
    have hsqrt := velocity_norm_le_vecEuclidean (x - y)
    have hspace' := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 2 * (K * a))
    have hval := htriangle.trans (add_le_add htime (hspace.trans hspace'))
    refine hval.trans ?_
    change L * a * |t - u| + 2 * (K * a) * Real.sqrt (vecNormSq (x - y)) ≤ _
    dsimp [jointIncrementConstant]
    change L * a * |t - u| + 2 * (K * a) * Real.sqrt (vecNormSq (x - y)) ≤
      (2 * K + L) * (|t - u| + Real.sqrt (vecNormSq (x - y))) * a
    nlinarith [mul_nonneg (mul_nonneg hK ha) (abs_nonneg (t - u)),
      mul_nonneg (mul_nonneg hL ha) (Real.sqrt_nonneg (vecNormSq (x - y)))]
  rw [increment_velocity_components D hseq, increment_velocity_components D hseq]
  apply rotate_sub_norm_le (by positivity)
  · exact hscalar 1
  · exact hscalar 0

/-- The amplitude and joint Lipschitz estimates combine into the endpoint
scale-splitting envelope, with no analytic hypothesis remaining. -/
theorem velocity_increment_envelope {α s q C : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsOCStreamSeq α q Λ ζ Φ) (hC : 0 < C)
    (hreg : OCStreamRegularityBounds D C Φ) {m : ℕ} (hm : 1 ≤ m)
    (t u : ℝ) (x y : Vec 2) :
    ‖(streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) -
      (streamVel (Φ m) u y - streamVel (Φ (m - 1)) u y)‖ ≤
      jointIncrementConstant D C * min (D.epsilon m ^ α)
        ((|t - u| + Real.sqrt (vecNormSq (x - y))) * D.epsilon m ^ (α - 1)) := by
  rw [mul_min_of_nonneg _ _ (jointIncrementConstant_nonneg D C)]
  refine le_min ?_ ?_
  · have ha := norm_sub_le
      (streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x)
      (streamVel (Φ m) u y - streamVel (Φ (m - 1)) u y)
    have hb := ha.trans (add_le_add (velocity_increment_amplitude D hseq hreg hm t x)
      (velocity_increment_amplitude D hseq hreg hm u y))
    have hL := incrementTimeConstant_nonneg D C
    have hp := Real.rpow_nonneg (D.epsilon_pos m).le α
    dsimp [jointIncrementConstant]
    nlinarith [mul_nonneg hL hp]
  · simpa only [D.velocityAmplitude_eq, mul_assoc, mul_left_comm, mul_comm] using
      velocity_increment_joint_lipschitz D hseq hC hreg hm t u x y

end AVRegularity.Velocity
end
end
end
end

section
@[expose] public section
open Homogenization AVenhance Filter Topology
open AVRegularity.Velocity.Port.Section2Induction
namespace AVRegularity.Velocity

/-! Endpoint joint Hölder velocity for the literal OC construction. -/

/-- The velocities of the literal OC stream recursion converge to a bounded,
space/time-periodic, distributionally divergence-free field at the endpoint
joint Hölder exponent `α`. Every analytic input is proved by the ported
Section 2 induction and the instantiated recursion data. -/
theorem exists_limit_velocity
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) :
    ∃ b : ℝ → Vec 2 → Vec 2,
      (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
      IsHolderDivFreeVelocity α b := by
  let D := ocJetRecursionData α s hα₀ hα₁ hs₀ hs₁ q hq Λ hΛ ζ hζ
  let C : ℝ := 11 + 768 / α
  have hC : 0 < C := by dsimp [C]; positivity
  have hreg : OCStreamRegularityBounds D C Φ :=
    Port.StreamRegularity.stream_regularity D hΦ
  let J := jointIncrementConstant D C
  have hJ : 0 ≤ J := jointIncrementConstant_nonneg D C
  have hKJ : incrementJetConstant D ≤ J := by
    have hK := incrementJetConstant_nonneg D
    have hL := incrementTimeConstant_nonneg D C
    dsimp [J, jointIncrementConstant]
    linarith
  have hamplitude : ∀ m t x,
      ‖streamVel (Φ (m + 1)) t x - streamVel (Φ m) t x‖ ≤
        J * ocEpsilon q Λ (m + 1) ^ α := by
    intro m t x
    have h := velocity_increment_amplitude D hΦ hreg (by omega : 1 ≤ m + 1) t x
    have h' := h.trans (mul_le_mul_of_nonneg_right hKJ
      (Real.rpow_nonneg (D.epsilon_pos (m + 1)).le α))
    simpa only [Nat.add_sub_cancel, D.epsilon_eq_oc] using h'
  have hincrement : ∀ m t u x y,
      ‖(streamVel (Φ (m + 1)) t x - streamVel (Φ m) t x) -
        (streamVel (Φ (m + 1)) u y - streamVel (Φ m) u y)‖ ≤
        J * min (ocEpsilon q Λ (m + 1) ^ α)
          ((|t - u| + Real.sqrt (vecNormSq (x - y))) *
            ocEpsilon q Λ (m + 1) ^ (α - 1)) := by
    intro m t u x y
    simpa only [Nat.add_sub_cancel, D.epsilon_eq_oc] using
      velocity_increment_envelope D hΦ hC hreg (by omega : 1 ≤ m + 1) t u x y
  obtain ⟨b, hconv, hholder⟩ := exists_limit_velocity_of_increment_bounds
    α s hα₀ hα₁ q hq Λ hΛ ζ Φ hΦ J hJ hamplitude hincrement
  exact ⟨b, hconv, holderDivFree_of_streamSeq_limit hζ hΛ hΦ
    (finite_velocity_bound D hΦ hC hreg) hconv hholder⟩

end AVRegularity.Velocity
end
end
