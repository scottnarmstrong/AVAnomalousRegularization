-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.NativeScalarErrorChain
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleWords.FiniteSmoothPeriodicCarrier
import AVRegularity.CycleReference.ChartTestCalculus
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.MixedTail.Energy
import AVRegularity.CycleEvolution.CellDriftComplexMultiplier
import AVRegularity.Weighted.PlaneIntervalCoefficients
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.CycleWords

/-! At any time at most one odd slot contributes to the adjoint coordinate. -/

def adjointSlotCoefficient (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν : ℝ) (k : ℤ) (t : ℝ) : ℝ :=
  ocCutoff α q Λ m k t * adjointPulseMemory α q Λ ζ m ν k t

theorem adjointSlot_nonzero_window {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ)
    (hne : adjointSlotCoefficient α q Λ ζ m ν k t ≠ 0) :
    ((k : ℝ) - 5 / 4) * ocTau α q Λ m < t ∧
      t < ((k : ℝ) + 2 / 3) * ocTau α q Λ m := by
  have hc : ocCutoff α q Λ m k t ≠ 0 := fun hc => hne (by simp [adjointSlotCoefficient, hc])
  have hM : adjointPulseMemory α q Λ ζ m ν k t ≠ 0 :=
    fun hM => hne (by simp [adjointSlotCoefficient, hM])
  have hh := CycleReference.cutoff_nonzero_distance hΛ k t hc
  refine ⟨by have hlo := (abs_lt.mp hh).1; nlinarith only [hlo], ?_⟩
  by_contra h
  exact hM (adjointPulseMemory_zero_after hΛ hζ ν k t (le_of_not_gt h))

theorem adjointSlot_nonzero_unique {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (k j : ℤ)
    (hk : Odd k) (hj : Odd j)
    (hck : adjointSlotCoefficient α q Λ ζ m ν k t ≠ 0)
    (hcj : adjointSlotCoefficient α q Λ ζ m ν j t ≠ 0) : k = j := by
  have hkt := adjointSlot_nonzero_window hΛ hζ ν k t hck
  have hjt := adjointSlot_nonzero_window hΛ hζ ν j t hcj
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hkj : (k : ℝ) < (j : ℝ) + 2 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h) hτ.le
    nlinarith only [hm, hkt.1, hjt.2, hτ]
  have hjk : (j : ℝ) < (k : ℝ) + 2 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h) hτ.le
    nlinarith only [hm, hjt.1, hkt.2, hτ]
  have hkj' : k < j + 2 := by exact_mod_cast hkj
  have hjk' : j < k + 2 := by exact_mod_cast hjk
  rcases hk with ⟨a, ha⟩
  rcases hj with ⟨b, hb⟩
  omega

theorem adjointCoordinate_eq_single {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (k : {k : ℤ // Odd k})
    (hck : adjointSlotCoefficient α q Λ ζ m ν k.1 t ≠ 0) (y : Vec 2) (j : Fin 2) :
    adjointCoordinate α q Λ ζ m ν t y j = y j +
      adjointSlotCoefficient α q Λ ζ m ν k.1 t * ocShearVel α q Λ m k.1 y j := by
  unfold adjointCoordinate
  congr 1
  apply tsum_eq_single k
  intro l hl
  have hc : adjointSlotCoefficient α q Λ ζ m ν l.1 t = 0 := by
    by_contra hc
    exact hl (Subtype.ext (adjointSlot_nonzero_unique hΛ hζ ν t l.1 k.1 l.2 k.2 hc hck))
  exact mul_eq_zero_of_left hc _

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Fast coefficient jets and polynomial slow displacement share the physical normalized radius. -/

theorem variableMultilinear_scaled_normalized_jet_budget (r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : Type*}
      (a : T → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) ℝ),
      (∀ t, ContDiff ℝ (J : ℕ) (a t)) → ∀ (ϖ ρ B : ℝ),
      0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 → 0 ≤ B →
      (∀ t (w : DerivativeWord2 r) j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => a t z (fun i => basisVec (w i))) z‖ ≤ B) →
      ∀ t j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => a t z (fun _ => ϖ • z)) z‖ ≤
          C * B * polynomialMomentRoot ϖ z ^ r := by
  obtain ⟨C, hC, hb⟩ := variableMultilinear_normalized_polynomial_jet_budget r J
  refine ⟨C * 2 ^ r, by positivity, ?_⟩
  intro T a ha ϖ ρ B hϖ hρ hscale hB hab t j hj z
  let a' := fun t (x : Vec 2) => a t (ϖ⁻¹ • x)
  have ha' (t : T) : ContDiff ℝ (J : ℕ) (a' t) :=
    (ha t).comp (contDiff_id.const_smul ϖ⁻¹)
  have hab' (t : T) (w : DerivativeWord2 r) (k : ℕ) (hk : k ≤ J) (x : Vec 2) :
      (ρ * ϖ) ^ k * ‖iteratedFDeriv ℝ k (fun x => a' t x (fun i => basisVec (w i))) x‖ ≤ B := by
    have hf : ContDiff ℝ (k : ℕ) (fun z => a t z (fun i => basisVec (w i))) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) ℝ
        (fun i => basisVec (w i))).contDiff.comp ((ha t).of_le (by exact_mod_cast hk))
    change (ρ * ϖ) ^ k * ‖iteratedFDeriv ℝ k
      (fun x => (fun z => a t z (fun i => basisVec (w i))) (ϖ⁻¹ • x)) x‖ ≤ B
    rw [normalizedJet_rescaling_eq k hf, abs_of_pos (inv_pos.mpr hϖ), mul_assoc,
      mul_inv_cancel₀ hϖ.ne', mul_one]
    exact hab t w k hk (ϖ⁻¹ • x)
  let f := fun x : Vec 2 => a' t x (fun _ => x)
  have hf : ContDiff ℝ (j : ℕ) f := by
    have hh := Weighted.multilinear_diagonal_contDiff J (a' t) (ha' t) 1
    simpa only [f, one_smul] using hh.of_le (by exact_mod_cast hj)
  have he : (fun z : Vec 2 => a t z (fun _ => ϖ • z)) = fun z => f (ϖ • z) := by
    funext y
    dsimp only [f, a']
    rw [smul_smul, inv_mul_cancel₀ hϖ.ne', one_smul]
  rw [he, normalizedJet_rescaling_eq j hf, abs_of_pos hϖ]
  have hh := hb a' ha' (ρ * ϖ) B (mul_nonneg hρ hϖ.le) hscale hB hab' t j hj (ϖ • z)
  have hroot : 1 + ‖ϖ • z‖ ≤ 2 * polynomialMomentRoot ϖ z := by
    rw [norm_smul, Real.norm_of_nonneg hϖ.le]
    linarith [polynomialMomentRoot_one_le ϖ z, scaledNorm_le_polynomialMomentRoot hϖ.le z]
  apply hh.trans
  have hr := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hroot r) (mul_nonneg hC hB)
  rw [mul_pow] at hr
  convert hr using 1; ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Actual transition Jacobian seminorms control the operator norms needed in the finite chain rule. -/

theorem iteratedFDeriv_norm_from_jacobian_bar {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ n i a, barNorm n R
      (fun x => jacMatrix F x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal B)
    (n : ℕ) (hn : 1 ≤ n) (x : Vec 2) :
    ‖iteratedFDeriv ℝ (n + 1) F x‖ ≤
      2 ^ (n + 1) * (B * (n.factorial : ℝ) * R ^ n) := by
  have hbudget : 0 ≤ B * (n.factorial : ℝ) * R ^ n := by positivity
  have hden : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    have hh : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith only [hh]
  have hw (w : DerivativeWord2 (n + 1)) :
      ‖iteratedFDeriv ℝ (n + 1) F x (fun i => basisVec (w i))‖ ≤
        B * (n.factorial : ℝ) * R ^ n := by
    apply (pi_norm_le_iff_of_nonneg hbudget).mpr
    intro i
    have hp := CycleReference.jacMatrix_partial_bound hF hR hB hb n hn
      (fun k => w k.castSucc) x i (w (Fin.last n))
    have he : Fin.snoc (fun k : Fin n => basisVec (w k.castSucc))
        (basisVec (w (Fin.last n))) = (fun k => basisVec (w k)) := by
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
    rw [he] at hp
    exact hp.trans (div_le_self hbudget hden)
  calc
    _ ≤ ∑ w : DerivativeWord2 (n + 1),
        ‖iteratedFDeriv ℝ (n + 1) F x (fun i => basisVec (w i))‖ :=
      ChartTransport.norm_le_sum_basisVec _
    _ ≤ ∑ _ : DerivativeWord2 (n + 1), B * (n.factorial : ℝ) * R ^ n :=
      Finset.sum_le_sum (fun w _ => hw w)
    _ = _ := by simp [DerivativeWord2, DerivativeWord]

theorem cell_rescaled_iteratedFDeriv_norm_from_bar {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ n i a, barNorm n R
      (fun x => jacMatrix F x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal B)
    (e : ℝ) (he : 0 < e) (y y' : Vec 2) (n : ℕ) (hn : 1 ≤ n) (z : Vec 2) :
    ‖iteratedFDeriv ℝ (n + 1) (fun z : Vec 2 => e⁻¹ • (F (y' + e • z) - y)) z‖ ≤
      2 ^ (n + 1) * (B * (n.factorial : ℝ) * (e * R) ^ n) := by
  rw [cell_rescaled_iteratedFDeriv_norm F hF e he y y' (n + 1) (by omega) z,
    Nat.add_sub_cancel]
  calc
    _ ≤ e ^ n * (2 ^ (n + 1) * (B * (n.factorial : ℝ) * R ^ n)) :=
      mul_le_mul_of_nonneg_left (iteratedFDeriv_norm_from_jacobian_bar hF hR hB hb n hn _)
        (by positivity)
    _ = _ := by rw [mul_pow]; ring

end AVRegularity.CycleWords
end

section
open Homogenization Filter Topology
namespace AVRegularity.CycleWords

/-! Zero adjoint coefficients also annihilate the pulse and cutoff residual terms. -/

theorem adjointPulseMemory_zero_imp_pulse_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ)
    (hz : adjointPulseMemory α q Λ ζ m ν k t = 0) : ocPulse α q Λ ζ m k t = 0 := by
  have hmin : IsLocalMin (adjointPulseMemory α q Λ ζ m ν k) t := by
    filter_upwards [] with s
    rw [hz]
    exact futureMemory_nonneg _ _ (fun r => (CycleReference.ocPulse_range hζ k r).1) s
  have hd := (adjointPulseMemory_hasDerivAt (α := α) (q := q) (m := m) hΛ hζ ν k t).deriv
  rw [hmin.deriv_eq_zero, hz] at hd
  linarith only [hd]

theorem cutoff_zero_imp_deriv_zero {α q : ℝ} {Λ m : ℕ} (k : ℤ) (t : ℝ)
    (hz : ocCutoff α q Λ m k t = 0) : deriv (ocCutoff α q Λ m k) t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards [] with s
  rw [hz]
  exact Real.smoothTransition.nonneg _

theorem adjointSlot_zero_residual {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ)
    (hz : adjointSlotCoefficient α q Λ ζ m ν k t = 0) :
    deriv (ocCutoff α q Λ m k) t * adjointPulseMemory α q Λ ζ m ν k t = 0 ∧
      ocCutoff α q Λ m k t * ocPulse α q Λ ζ m k t = 0 := by
  rcases mul_eq_zero.mp hz with hc | hM
  · exact ⟨by rw [cutoff_zero_imp_deriv_zero k t hc, zero_mul], by rw [hc, zero_mul]⟩
  · exact ⟨by rw [hM, mul_zero], by rw [adjointPulseMemory_zero_imp_pulse_zero hΛ hζ ν k t hM, mul_zero]⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Exact spatial derivatives reduce to the one surviving transverse shear. -/

theorem adjointCoordinate_gradient_single {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (k : {k : ℤ // Odd k})
    (hck : adjointSlotCoefficient α q Λ ζ m ν k.1 t ≠ 0)
    (y : Vec 2) (j i : Fin 2) :
    fderiv ℝ (fun z => adjointCoordinate α q Λ ζ m ν t z j) y (basisVec i) =
      (if i = j then 1 else 0) + adjointSlotCoefficient α q Λ ζ m ν k.1 t *
        fderiv ℝ (fun z => ocShearVel α q Λ m k.1 z j) y (basisVec i) := by
  have he := funext (fun z => adjointCoordinate_eq_single hΛ hζ ν t k hck z j)
  rw [he]
  have hu := (ocShearVel_component_contDiff (α := α) (q := q) (Λ := Λ) (m := m) k.2 j).differentiable
    (by simp) y
  rw [fderiv_fun_add (differentiableAt_apply j y) (hu.const_mul _), fderiv_const_mul hu]
  rw [(hasFDerivAt_apply (𝕜 := ℝ) j y).fderiv]
  simp [basisVec]
  fin_cases i <;> fin_cases j <;> rfl

/-! Exact diffusion and drift parts of the adjoint coordinate equation. -/

theorem adjointCoordinate_eq_coordinate {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν t : ℝ) (hz : ∀ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t = 0)
    (y : Vec 2) (j : Fin 2) : adjointCoordinate α q Λ ζ m ν t y j = y j := by
  have hh : (fun k : {k : ℤ // Odd k} =>
      ocCutoff α q Λ m k.1 t * adjointPulseMemory α q Λ ζ m ν k.1 t *
        ocShearVel α q Λ m k.1 y j) = (fun _ => 0) := by
    funext k
    exact mul_eq_zero_of_left (hz k) _
  unfold adjointCoordinate
  rw [hh, tsum_zero, add_zero]

theorem ocMu_eq_laplacian_frequency (q : ℝ) (Λ m : ℕ) (ν : ℝ) :
    ocMu q Λ m ν = ν * (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 := by
  unfold ocMu
  simp only [div_eq_mul_inv]
  ring

theorem adjointCoordinate_diffusion_equation {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    ν * (∑ i : Fin 2, fderiv ℝ (fun z => fderiv ℝ
      (fun x => adjointCoordinate α q Λ ζ m ν t x j) z (basisVec i)) y (basisVec i)) =
        -ocMu q Λ m ν * (adjointCoordinate α q Λ ζ m ν t y j - y j) := by
  classical
  by_cases ha : ∃ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t ≠ 0
  · obtain ⟨k, hk⟩ := ha
    have he := funext (fun z => adjointCoordinate_eq_single hΛ hζ ν t k hk z j)
    rw [he, congrFun he y, add_sub_cancel_left,
      coordinate_add_laplacian _ _
        ((ocShearVel_component_contDiff (α := α) (q := q) (Λ := Λ) (m := m) k.2 j).of_le (by simp)),
      ocShearVel_component_laplacian k.2, ocMu_eq_laplacian_frequency]
    ring
  · have hz : ∀ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t = 0 := by
      intro k
      by_contra hne
      exact ha ⟨k, hne⟩
    have he := funext (fun z => adjointCoordinate_eq_coordinate ν t hz z j)
    rw [he, congrFun he y, sub_self, mul_zero]
    have hh : (fun z => fderiv ℝ (fun x : Vec 2 => x j) z) = fun _ => ContinuousLinearMap.proj j :=
      funext (fun z => (hasFDerivAt_apply (𝕜 := ℝ) j z).fderiv)
    simp [hh]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleWords

/-! The time part of the exact adjoint coordinate equation for the literal pulse stream. -/

def adjointResidual (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν t : ℝ) (y : Vec 2) (j : Fin 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) t *
    adjointPulseMemory α q Λ ζ m ν k.1 t * ocShearVel α q Λ m k.1 y j

theorem cutoff_mul_pulse_eq_pulse {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (k : ℤ) (t : ℝ) :
    ocCutoff α q Λ m k t * ocPulse α q Λ ζ m k t = ocPulse α q Λ ζ m k t := by
  by_cases hp : ocPulse α q Λ ζ m k t = 0
  · rw [hp, mul_zero]
  · rw [CycleReference.ocCutoff_eq_one_of_pulse_ne_zero hΛ hζ hp, one_mul]

theorem adjointCoordinate_time_equation {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    deriv (fun s => adjointCoordinate α q Λ ζ m ν s y j) t =
      adjointResidual α q Λ ζ m ν t y j +
        ocMu q Λ m ν * (adjointCoordinate α q Λ ζ m ν t y j - y j) -
          streamVel (ocPulseStream α q Λ ζ m) t y j := by
  classical
  obtain ⟨S, hS⟩ := CycleReference.cutoff_locally_finite (α := α) (q := q) (m := m) hΛ t
  have hct : ∀ k : {k : ℤ // Odd k}, k ∉ S → ocCutoff α q Λ m k.1 t = 0 := hS.self_of_nhds
  have hres : adjointResidual α q Λ ζ m ν t y j = ∑ k ∈ S,
      deriv (ocCutoff α q Λ m k.1) t * adjointPulseMemory α q Λ ζ m ν k.1 t *
        ocShearVel α q Λ m k.1 y j := by
    apply tsum_eq_sum
    intro k hk
    rw [cutoff_zero_imp_deriv_zero k.1 t (hct k hk), zero_mul, zero_mul]
  have hval : adjointCoordinate α q Λ ζ m ν t y j - y j = ∑ k ∈ S,
      ocCutoff α q Λ m k.1 t * adjointPulseMemory α q Λ ζ m ν k.1 t *
        ocShearVel α q Λ m k.1 y j := by
    unfold adjointCoordinate
    rw [add_sub_cancel_left]
    apply tsum_eq_sum
    intro k hk
    rw [hct k hk, zero_mul, zero_mul]
  have hv : streamVel (ocPulseStream α q Λ ζ m) t y j = ∑ k ∈ S,
      (ocCutoff α q Λ m k.1 t * ocPulse α q Λ ζ m k.1 t) * ocShearVel α q Λ m k.1 y j := by
    simp_rw [cutoff_mul_pulse_eq_pulse hΛ hζ]
    rw [pulseVelocity_eq_shear_sum hΛ hζ]
    apply tsum_eq_sum
    intro k hk
    have hp : ocPulse α q Λ ζ m k.1 t = 0 := by
      have hh := cutoff_mul_pulse_eq_pulse (α := α) (q := q) (m := m) hΛ hζ k.1 t
      rw [hct k hk, zero_mul] at hh
      exact hh.symm
    rw [hp, zero_mul]
  have heq : (fun s => adjointCoordinate α q Λ ζ m ν s y j) =ᶠ[𝓝 t]
      (fun s => y j + ∑ k ∈ S, ocCutoff α q Λ m k.1 s *
        adjointPulseMemory α q Λ ζ m ν k.1 s * ocShearVel α q Λ m k.1 y j) := by
    filter_upwards [hS] with s hs
    unfold adjointCoordinate
    congr 1
    apply tsum_eq_sum
    intro k hk
    rw [hs k hk, zero_mul, zero_mul]
  have hder : deriv (fun s => adjointCoordinate α q Λ ζ m ν s y j) t = ∑ k ∈ S,
      (deriv (ocCutoff α q Λ m k.1) t * adjointPulseMemory α q Λ ζ m ν k.1 t +
        ocCutoff α q Λ m k.1 t *
          (ocMu q Λ m ν * adjointPulseMemory α q Λ ζ m ν k.1 t - ocPulse α q Λ ζ m k.1 t)) *
            ocShearVel α q Λ m k.1 y j := by
    rw [heq.deriv_eq]
    apply HasDerivAt.deriv
    apply HasDerivAt.const_add
    apply HasDerivAt.fun_sum
    intro k _
    exact (((CycleReference.ocCutoff_contDiff hΛ k.1).differentiable (by simp) t).hasDerivAt.mul
      (adjointPulseMemory_hasDerivAt hΛ hζ ν k.1 t)).mul_const _
  rw [hder, hres, hval, hv, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Uniform displacement of the future-memory coordinate. -/

theorem adjointSlotCoefficient_range {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (k : ℤ) (t : ℝ) :
    0 ≤ adjointSlotCoefficient α q Λ ζ m ν k t ∧
      adjointSlotCoefficient α q Λ ζ m ν k t ≤ (ocMu q Λ m ν)⁻¹ := by
  have hc0 : 0 ≤ ocCutoff α q Λ m k t := Real.smoothTransition.nonneg _
  have hc1 : ocCutoff α q Λ m k t ≤ 1 := Real.smoothTransition.le_one _
  have hm := adjointPulseMemory_range (α := α) (q := q) (m := m) hΛ hζ hν k t
  exact ⟨mul_nonneg hc0 hm.1,
    (mul_le_mul_of_nonneg_right hc1 hm.1).trans (by simpa using hm.2)⟩

theorem adjointCoordinate_displacement_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (t : ℝ) (y : Vec 2) (j : Fin 2) :
    |adjointCoordinate α q Λ ζ m ν t y j - y j| ≤
      (ocMu q Λ m ν)⁻¹ *
        |2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) * (ocEpsilon q Λ m)⁻¹| := by
  classical
  by_cases ha : ∃ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t ≠ 0
  · obtain ⟨k, hk⟩ := ha
    rw [adjointCoordinate_eq_single hΛ hζ ν t k hk y j, add_sub_cancel_left, abs_mul]
    have hc := adjointSlotCoefficient_range (α := α) (q := q) (m := m) hΛ hζ hν k.1 t
    rw [abs_of_nonneg hc.1]
    exact mul_le_mul hc.2 (ocShearVel_component_abs_le k.2 y j) (abs_nonneg _) (by
      have hm := adjointPulseMemory_range (α := α) (q := q) (m := m) hΛ hζ hν k.1 t
      exact hm.1.trans hm.2)
  · have hz : ∀ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t = 0 := by
      simpa only [not_exists, not_not] using ha
    rw [adjointCoordinate_eq_coordinate ν t hz y j, sub_self, abs_zero]
    have hm := adjointPulseMemory_range (α := α) (q := q) (m := m) hΛ hζ hν 1 t
    exact mul_nonneg (hm.1.trans hm.2) (abs_nonneg _)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.FastJets
namespace AVRegularity.CycleWords

/-! Coordinate mixed words are bounded by their actual mixed operator jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem odL_append (γ δ : List (Fin 2)) (f : Vec 2 → E) :
    odL (γ ++ δ) f = odL δ (odL γ f) := by simp [odL, List.foldl_append]

theorem slowL_append (γ δ : List (Fin 2)) (f : Vec 2 → Vec 2 → E) :
    slowL (γ ++ δ) f = slowL δ (slowL γ f) := by
  funext X z
  exact congrFun (odL_append γ δ (fun X => f X z)) X

theorem norm_mixL_le {f : Vec 2 → Vec 2 → E} (γ δ : List (Fin 2))
    (hf : IsBoxSmooth γ.length δ.length f) (X z : Vec 2) :
    ‖mixL γ δ f X z‖ ≤
      ‖iteratedFDeriv ℝ γ.length (fun X' => iteratedFDeriv ℝ δ.length (f X') z) X‖ := by
  let wγ : DerivativeWord2 γ.length := fun i => γ.get i
  let wδ : DerivativeWord2 δ.length := fun i => δ.get i
  have heγ : List.ofFn wγ = γ := List.ofFn_get γ
  have heδ : List.ofFn wδ = δ := List.ofFn_get δ
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin δ.length => Vec 2) E
    (fun i => basisVec (wδ i.rev))
  have he (X' : Vec 2) : odL δ (f X') z = L (iteratedFDeriv ℝ δ.length (f X') z) := by
    conv_lhs => rw [← heδ, ← orderedDerivative_eq_odL,
      orderedDerivative_eq_iteratedFDeriv wδ (hf.1 X')]
    rfl
  change ‖odL γ (fun X' => odL δ (f X') z) X‖ ≤ _
  simp_rw [he]
  conv_lhs => rw [← heγ, ← orderedDerivative_eq_odL,
    orderedDerivative_clm_comp L wγ (hf.2.1 δ.length le_rfl z)]
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro A
    simpa only [L, ContinuousMultilinearMap.apply_apply, norm_basisVec,
      Finset.prod_const_one, mul_one, one_mul] using A.le_opNorm (fun i => basisVec (wδ i.rev))
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
    (by simpa only [one_mul, List.length_ofFn] using norm_orderedDerivative_le (hf.2.1 δ.length le_rfl z) wγ X))

theorem mixL_slowL_eq {N : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : ContDiff ℝ (N : ℕ) (Function.uncurry f)) (w γ δ : List (Fin 2))
    (hN : w.length + γ.length + δ.length ≤ N) :
    mixL γ δ (slowL w f) = mixL (w ++ γ) δ f := by
  have hb : IsBoxSmooth w.length δ.length f :=
    Weighted.isBoxSmooth_of_joint_contDiff _ _ _
      (hf.of_le (by exact_mod_cast (by omega : w.length + δ.length ≤ N)))
  rw [mixL, MixedTail.fastL_slowL_comm w δ hb, ← slowL_append]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The adjoint coordinate defect has the exponentially small early pulse tail. -/

theorem adjointResidual_eq_single {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (k : {k : ℤ // Odd k})
    (hck : adjointSlotCoefficient α q Λ ζ m ν k.1 t ≠ 0) (y : Vec 2) (j : Fin 2) :
    adjointResidual α q Λ ζ m ν t y j =
      deriv (ocCutoff α q Λ m k.1) t * adjointPulseMemory α q Λ ζ m ν k.1 t *
        ocShearVel α q Λ m k.1 y j := by
  unfold adjointResidual
  apply tsum_eq_single k
  intro l hl
  have hc : adjointSlotCoefficient α q Λ ζ m ν l.1 t = 0 := by
    by_contra hc
    exact hl (Subtype.ext (adjointSlot_nonzero_unique hΛ hζ ν t l.1 k.1 l.2 k.2 hc hck))
  rw [(adjointSlot_zero_residual hΛ hζ ν l.1 t hc).1, zero_mul]

theorem adjointResidual_eq_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ)
    (hz : ∀ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t = 0)
    (y : Vec 2) (j : Fin 2) : adjointResidual α q Λ ζ m ν t y j = 0 := by
  have hh : (fun k : {k : ℤ // Odd k} =>
      deriv (ocCutoff α q Λ m k.1) t * adjointPulseMemory α q Λ ζ m ν k.1 t *
        ocShearVel α q Λ m k.1 y j) = (fun _ => 0) := by
    funext k
    rw [(adjointSlot_zero_residual hΛ hζ ν k.1 t (hz k)).1, zero_mul]
  unfold adjointResidual
  rw [hh, tsum_zero]

theorem adjointResidual_abs_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m)
    (t : ℝ) (y : Vec 2) (j : Fin 2) :
    |adjointResidual α q Λ ζ m ν t y j| ≤
      ((K / ocTau α q Λ m) *
        (Real.exp (-ocMu q Λ m ν * (ocTau α q Λ m / 12)) * (ocMu q Λ m ν)⁻¹)) *
          |2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) * (ocEpsilon q Λ m)⁻¹| := by
  classical
  by_cases ha : ∃ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t ≠ 0
  · obtain ⟨k, hk⟩ := ha
    rw [adjointResidual_eq_single hΛ hζ ν t k hk y j, abs_mul]
    apply mul_le_mul (adjointPulseMemory_cutoff_derivative_bound hΛ hζ hν K hK hb k.1 t)
      (ocShearVel_component_abs_le k.2 y j) (abs_nonneg _)
    have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
    have hm := adjointPulseMemory_range (α := α) (q := q) (m := m) hΛ hζ hν k.1 t
    exact mul_nonneg (div_nonneg hK hτ.le) (mul_nonneg (Real.exp_pos _).le (hm.1.trans hm.2))
  · have hz : ∀ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t = 0 := by
      simpa only [not_exists, not_not] using ha
    rw [adjointResidual_eq_zero hΛ hζ ν t hz y j, abs_zero]
    have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
    have hm := adjointPulseMemory_range (α := α) (q := q) (m := m) hΛ hζ hν 1 t
    exact mul_nonneg
      (mul_nonneg (div_nonneg hK hτ.le) (mul_nonneg (Real.exp_pos _).le (hm.1.trans hm.2)))
      (abs_nonneg _)

/-! Transverse transport of the adjoint correction vanishes for the literal pulse velocity. -/

theorem pulseVelocity_eq_adjoint_slot {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (k : {k : ℤ // Odd k})
    (hk : adjointSlotCoefficient α q Λ ζ m ν k.1 t ≠ 0) (y : Vec 2) :
    streamVel (ocPulseStream α q Λ ζ m) t y =
      ocPulse α q Λ ζ m k.1 t • ocShearVel α q Λ m k.1 y := by
  by_cases hp : ocPulse α q Λ ζ m k.1 t = 0
  · have hquiet : ∀ l : ℤ, Odd l → ocPulse α q Λ ζ m l t = 0 := by
      intro l hl
      by_contra hpl
      by_cases he : l = k.1
      · subst l
        exact hpl hp
      · have hc := CycleReference.ocCutoff_eq_zero_of_other_slot hΛ hζ hl k.2 (Ne.symm he) hpl
        exact hk (by simp [adjointSlotCoefficient, hc])
    rw [CycleReference.pulseStreamVel_eq_zero_of_quiet hquiet y, hp, zero_smul]
  · exact CycleReference.pulseStreamVel_eq_active hΛ hζ k.2 hp y

theorem adjointCoordinate_transport_equation {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, streamVel (ocPulseStream α q Λ ζ m) t y i *
      fderiv ℝ (fun z => adjointCoordinate α q Λ ζ m ν t z j) y (basisVec i)) =
        streamVel (ocPulseStream α q Λ ζ m) t y j := by
  classical
  by_cases ha : ∃ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t ≠ 0
  · obtain ⟨k, hk⟩ := ha
    rw [pulseVelocity_eq_adjoint_slot hΛ hζ ν t k hk y]
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [adjointCoordinate_gradient_single hΛ hζ ν t k hk]
    calc
      _ = (∑ i : Fin 2, ocPulse α q Λ ζ m k.1 t * ocShearVel α q Λ m k.1 y i *
          (if i = j then 1 else 0)) +
          (ocPulse α q Λ ζ m k.1 t * adjointSlotCoefficient α q Λ ζ m ν k.1 t) *
            ∑ i : Fin 2, ocShearVel α q Λ m k.1 y i *
              fderiv ℝ (fun z => ocShearVel α q Λ m k.1 z j) y (basisVec i) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [ocShearVel_self_transport_zero k.2, mul_zero, add_zero]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · have hz : ∀ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t = 0 := by
      intro k
      by_contra hne
      exact ha ⟨k, hne⟩
    have he := funext (fun z => adjointCoordinate_eq_coordinate ν t hz z j)
    rw [he]
    have hg (i : Fin 2) : fderiv ℝ (fun z : Vec 2 => z j) y (basisVec i) =
        if i = j then 1 else 0 := by
      rw [(hasFDerivAt_apply (𝕜 := ℝ) j y).fderiv]
      fin_cases i <;> fin_cases j <;> rfl
    simp_rw [hg]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end AVRegularity.CycleWords
end

section
open MeasureTheory Filter AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped Topology ENNReal
namespace AVRegularity.CycleWords

/-! Uniform higher Sobolev bounds close under pointwise convergence of native H1 test moments. -/

theorem cellHigher_pointwise_closure (K : ℕ) (u : ℕ → TorusHk K ℂ)
    (v : ComplexCellL2) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R)
    (hm : ∀ z : TorusHk 1 ℂ,
      Tendsto (fun n => inner ℝ (torusHkValueCLM (u n)) (torusHkValueCLM z)) atTop
        (𝓝 (inner ℝ v (torusHkValueCLM z)))) :
    ∃ w : TorusHk K ℂ, torusHkValueCLM w = v ∧ ‖w‖ ≤ R := by
  let : SecondCountableTopology (TorusHk K ℂ) := by
    let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
    infer_instance
  obtain ⟨w, φ, hφ, hw⟩ := cellHilbert_weak_subsequence_clm u R hu
  refine ⟨w, ?_, hilbertWeak_norm_le (fun n => u (φ n)) w R (fun n => hu (φ n)) hw⟩
  apply cellL2_eq_of_H1_pairings
  intro z
  let ell : TorusHk K ℂ →L[ℝ] ℝ :=
    (innerSL ℝ (torusHkValueCLM z)).comp (torusHkValueCLM (E := ℂ) (K := K))
  have hl := hw ell
  change Tendsto (fun n => inner ℝ (torusHkValueCLM z) (torusHkValueCLM (u (φ n))))
    atTop (𝓝 (inner ℝ (torusHkValueCLM z) (torusHkValueCLM w))) at hl
  have he : (fun n => inner ℝ (torusHkValueCLM z) (torusHkValueCLM (u (φ n)))) =
      fun n => inner ℝ (torusHkValueCLM (u (φ n))) (torusHkValueCLM z) := by
    funext n
    exact real_inner_comm _ _
  rw [he, ← real_inner_comm (torusHkValueCLM z) (torusHkValueCLM w)] at hl
  exact tendsto_nhds_unique hl ((hm z).comp hφ.tendsto_atTop)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.FastJets
namespace AVRegularity.CycleWords

/-! Mixed words of a slow Taylor coefficient use the total reserved mixed jet. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slowCoefficient_eq_slowL {r : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth r 0 f) (w : DerivativeWord2 r) :
    (fun X z => iteratedFDeriv ℝ r (fun X' => f X' z) X (fun i => basisVec (w i))) =
      slowL (List.ofFn (fun i : Fin r => w i.rev)) f := by
  funext X z
  change _ = orderedDerivative (fun i : Fin r => w i.rev) (fun X' => f X' z) X
  rw [orderedDerivative_eq_iteratedFDeriv _ (hf.contDiff_slow z)]
  simp only [Fin.rev_rev]

theorem norm_slowCoefficient_mixL_le {r J : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : ContDiff ℝ (J + r : ℕ) (Function.uncurry f)) (w : DerivativeWord2 r)
    (γ δ : List (Fin 2)) (hJ : γ.length + δ.length ≤ J) (X z : Vec 2) :
    ‖mixL γ δ (fun X z => iteratedFDeriv ℝ r (fun X' => f X' z) X
      (fun i => basisVec (w i))) X z‖ ≤
      ‖iteratedFDeriv ℝ (r + γ.length) (fun X' => iteratedFDeriv ℝ δ.length (f X') z) X‖ := by
  have hr : IsBoxSmooth r 0 f := Weighted.isBoxSmooth_of_joint_contDiff _ _ _
    (hf.of_le (by exact_mod_cast (by omega : r + 0 ≤ J + r)))
  rw [slowCoefficient_eq_slowL hr w,
    mixL_slowL_eq hf _ γ δ (by simp only [List.length_ofFn]; omega)]
  have hb : IsBoxSmooth (List.ofFn (fun i : Fin r => w i.rev) ++ γ).length δ.length f :=
    Weighted.isBoxSmooth_of_joint_contDiff _ _ _
      (hf.of_le (by exact_mod_cast (by simp only [List.length_append, List.length_ofFn]; omega)))
  have hh := norm_mixL_le _ _ hb X z
  have hlen : (List.ofFn (fun i : Fin r => w i.rev) ++ γ).length = r + γ.length := by simp
  rw [hlen] at hh
  exact hh

end AVRegularity.CycleWords
end

section
open MeasureTheory Filter AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped Topology
namespace AVRegularity.CycleWords

/-! Pointwise weak closure preserves the literal higher norm-square budget. -/

theorem cellHigher_pointwise_square_closure (K : ℕ) (u : ℕ → TorusHk K ℂ)
    (v : ComplexCellL2) (C : ℝ) (hC : 0 ≤ C) (hu : ∀ n, ‖u n‖ ^ 2 ≤ C)
    (hm : ∀ z : TorusHk 1 ℂ,
      Tendsto (fun n => inner ℝ (torusHkValueCLM (u n)) (torusHkValueCLM z)) atTop
        (𝓝 (inner ℝ v (torusHkValueCLM z)))) :
    ∃ w : TorusHk K ℂ, torusHkValueCLM w = v ∧ ‖w‖ ^ 2 ≤ C := by
  have hn (n : ℕ) : ‖u n‖ ≤ Real.sqrt C := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mp
    rw [Real.sq_sqrt hC]
    exact hu n
  obtain ⟨w, hv, hw⟩ := cellHigher_pointwise_closure K u v (Real.sqrt C) hn hm
  refine ⟨w, hv, ?_⟩
  have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mpr hw
  rwa [Real.sq_sqrt hC] at hs

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Complex scalar multiplication on the original real higher torus carrier. -/

def torusHigherScalarCLM (K : ℕ) (c : ℂ) : TorusHk K ℂ →L[ℝ] TorusHk K ℂ :=
  mapTorusHkCLM K (ContinuousLinearMap.mul ℝ ℂ c)

theorem torusHigherScalarCLM_value (K : ℕ) (c : ℂ) (U : TorusHk K ℂ) :
    torusHkValueCLM (torusHigherScalarCLM K c U) = cellScalarCLM c (torusHkValueCLM U) := by
  apply Lp.ext
  have hleft := mapTorusHk_jet_ae (ContinuousLinearMap.mul ℝ ℂ c) U (valueIndex2 K)
  have hright := cellScalarCLM_ae c (torusHkValueCLM U)
  rw [torusHigherScalarCLM, mapTorusHkCLM_apply]
  exact hleft.trans hright.symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Spatial gradient control for the future-memory coordinate. -/

theorem adjointCoordinate_gradient_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (t : ℝ) (y : Vec 2) (j i : Fin 2) :
    |fderiv ℝ (fun z => adjointCoordinate α q Λ ζ m ν t z j) y (basisVec i)| ≤
      1 + (ocMu q Λ m ν)⁻¹ *
        |(2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
          (2 * Real.pi * (ocEpsilon q Λ m)⁻¹)| := by
  classical
  have hm := adjointPulseMemory_range (α := α) (q := q) (m := m) hΛ hζ hν 1 t
  have hμ : 0 ≤ (ocMu q Λ m ν)⁻¹ := hm.1.trans hm.2
  by_cases ha : ∃ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t ≠ 0
  · obtain ⟨k, hk⟩ := ha
    rw [adjointCoordinate_gradient_single hΛ hζ ν t k hk y j i]
    have hc := adjointSlotCoefficient_range (α := α) (q := q) (m := m) hΛ hζ hν k.1 t
    have hd : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    calc
      _ ≤ |(if i = j then (1 : ℝ) else 0)| +
          |adjointSlotCoefficient α q Λ ζ m ν k.1 t *
            fderiv ℝ (fun z => ocShearVel α q Λ m k.1 z j) y (basisVec i)| := abs_add_le _ _
      _ ≤ _ := add_le_add hd (by
        rw [abs_mul, abs_of_nonneg hc.1]
        exact mul_le_mul hc.2 (ocShearVel_gradient_abs_le k.2 y j i) (abs_nonneg _) hμ)
  · have hz : ∀ k : {k : ℤ // Odd k}, adjointSlotCoefficient α q Λ ζ m ν k.1 t = 0 := by
      simpa only [not_exists, not_not] using ha
    have he := funext (fun z => adjointCoordinate_eq_coordinate ν t hz z j)
    rw [he, (hasFDerivAt_apply (𝕜 := ℝ) j y).fderiv]
    have hd : |ContinuousLinearMap.proj (R := ℝ) j (basisVec i)| ≤ (1 : ℝ) := by
      fin_cases i <;> fin_cases j <;> norm_num [basisVec]
    exact hd.trans (le_add_of_nonneg_right (mul_nonneg hμ (abs_nonneg _)))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Genuine native cell multiplier fields are strongly measurable, also on moving L2 states. -/

theorem cellCoefficient_fixed_stronglyMeasurable
    (c : ℝ → Vec 2 → ℂ) (hc : Measurable (Function.uncurry c))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖c t x‖ ≤ M) (u : ComplexCellL2) :
    StronglyMeasurable (fun t => cellCoefficientCLM (c t)
      ((hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      M hM (hb t) u) := by
  let : SecondCountableTopology ComplexCellL2 := by
    let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
    exact Lp.SecondCountableTopology
  have hmem (t : ℝ) : MemLp (fun x => c t x * u x) 2
      (volume.restrict AVenhance.unitCube) :=
    (memLp_top_of_bound
      (hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall (hb t))).mul (Lp.memLp u)
  have hj : StronglyMeasurable (fun p : ℝ × Vec 2 => c p.1 p.2 * u p.2) :=
    hc.stronglyMeasurable.mul ((Lp.stronglyMeasurable u).comp_measurable measurable_snd)
  have hs := bochnerL2Slice_stronglyMeasurable (volume.restrict AVenhance.unitCube)
    (fun t x => c t x * u x) hj hmem
  have he : (fun t => cellCoefficientCLM (c t)
      ((hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      M hM (hb t) u) = (fun t => (hmem t).toLp (fun x => c t x * u x)) := by
    funext t
    apply Lp.ext
    exact (cellCoefficientCLM_ae _ _ M hM (hb t) u).trans (hmem t).coeFn_toLp.symm
  rw [he]
  exact hs

theorem cellCoefficient_variable_stronglyMeasurable
    (c : ℝ → Vec 2 → ℂ) (hc : Measurable (Function.uncurry c))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖c t x‖ ≤ M)
    (u : ℝ → ComplexCellL2) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun t => cellCoefficientCLM (c t)
      ((hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      M hM (hb t) (u t)) := by
  let : SecondCountableTopology ComplexCellL2 := by
    let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
    exact Lp.SecondCountableTopology
  let : MeasurableSpace ComplexCellL2 := borel _
  let : BorelSpace ComplexCellL2 := ⟨rfl⟩
  exact caratheodoryFamily_stronglyMeasurable _ (fun t =>
    (cellCoefficientCLM (c t)
      ((hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      M hM (hb t)).continuous)
    (cellCoefficient_fixed_stronglyMeasurable c hc M hM hb) u hu

theorem cellCoefficient_variable_aestronglyMeasurable {μ : Measure ℝ}
    (c : ℝ → Vec 2 → ℂ) (hc : Measurable (Function.uncurry c))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖c t x‖ ≤ M)
    (u : ℝ → ComplexCellL2) (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun t => cellCoefficientCLM (c t)
      ((hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      M hM (hb t) (u t)) μ := by
  apply (cellCoefficient_variable_stronglyMeasurable c hc M hM hb
    (hu.mk u) hu.stronglyMeasurable_mk).aestronglyMeasurable.congr
  filter_upwards [hu.ae_eq_mk] with t ht
  rw [ht]

theorem cellCoefficient_variable_memLp {μ : Measure ℝ}
    (c : ℝ → Vec 2 → ℂ) (hc : Measurable (Function.uncurry c))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖c t x‖ ≤ M)
    (u : ℝ → ComplexCellL2) (hu : MemLp u 2 μ) :
    MemLp (fun t => cellCoefficientCLM (c t)
      ((hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      M hM (hb t) (u t)) 2 μ := by
  apply (hu.const_smul M).of_le
    (cellCoefficient_variable_aestronglyMeasurable c hc M hM hb u hu.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hM]
  exact measurableCoefficientL2_norm_le _
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable
      ((hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)) M hM
    (fun x => (scalarMultiply_norm_bound (c t x)).trans (hb t x)) (u t)

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! A metric controlled only on a time window `[a, b]` is clamped in time to that window. The
clamp agrees with the metric on the window and is globally near the identity. -/

/-- `‖G - I‖_∞ ≤ g` at every time of the set `s`. -/
def IsMetricNearIdentityOn (s : Set ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) :
    Prop :=
  ∀ t ∈ s, ∀ z (ξ : Vec 2),
    |∑ i, ∑ j, ξ i * (G t z - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤ g * ∑ i, ξ i ^ 2

/-- The metric frozen in time outside `[a, b]`: `G (max a (min t b))`. -/
def metricClamp (a b : ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun t z => G (max a (min t b)) z

theorem metricClamp_of_mem {a b t : ℝ} (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (ht : t ∈ Set.Icc a b) : metricClamp a b G t = G t := by
  funext z
  simp only [metricClamp, min_eq_left ht.2, max_eq_right ht.1]

theorem clampTime_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : max a (min t b) ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem isMetricNearIdentity_metricClamp {a b g : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsMetricNearIdentityOn (Set.Icc a b) G g) :
    IsMetricNearIdentity (metricClamp a b G) g :=
  fun t z ξ => hG _ (clampTime_mem hab t) z ξ

/-- The entry bound of `nearIdentity_entry_abs_le` at a time of the window. -/
theorem nearIdentityOn_entry_abs_le {a b g : ℝ} (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentityOn (Set.Icc a b) G g) {t : ℝ}
    (ht : t ∈ Set.Icc a b) (z : Vec 2) (hsym : (G t z).IsSymm) (i j : Fin 2) :
    |G t z i j| ≤ 5 / 4 := by
  have hc := metricClamp_of_mem G ht
  have h := Weighted.nearIdentity_entry_abs_le (metricClamp a b G) g hg4
    (isMetricNearIdentity_metricClamp (ht.1.trans ht.2) hG) t z (by rw [hc]; exact hsym) i j
  rwa [hc] at h

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Complex multiplication on native periodic jets has its exact scalar norm. -/

theorem torusHigherScalarCLM_val (K : ℕ) (c : ℂ) (U : TorusHk K ℂ) :
    (torusHigherScalarCLM K c U).val = c • U.val := by
  apply PiLp.ext
  intro a
  apply Lp.ext
  have hh := mapTorusHk_jet_ae (ContinuousLinearMap.mul ℝ ℂ c) U a
  rw [torusHigherScalarCLM, mapTorusHkCLM_apply]
  filter_upwards [hh, Lp.coeFn_smul c (U.val a)] with x hl hr
  change (mapTorusHk (ContinuousLinearMap.mul ℝ ℂ c) U).val a x = (c • U.val a) x
  rw [hl, hr]
  rfl

theorem torusHigherScalarCLM_norm (K : ℕ) (c : ℂ) (U : TorusHk K ℂ) :
    ‖torusHigherScalarCLM K c U‖ = ‖c‖ * ‖U‖ := by
  change ‖(torusHigherScalarCLM K c U).val‖ = ‖c‖ * ‖U.val‖
  rw [torusHigherScalarCLM_val, norm_smul]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Literal scalar algebra on the original native higher torus carriers. -/

theorem torusHigherScalarCLM_real (K : ℕ) (r : ℝ) (U : TorusHk K ℂ) :
    torusHigherScalarCLM K (r : ℂ) U = r • U := by
  apply TorusHk.ext_value
  change torusHkValueCLM (torusHigherScalarCLM K (r : ℂ) U) = torusHkValueCLM (r • U)
  rw [torusHigherScalarCLM_value, map_smul]
  apply Lp.ext
  filter_upwards [cellScalarCLM_ae (r : ℂ) (torusHkValueCLM U),
    Lp.coeFn_smul r (torusHkValueCLM U)] with x hl hr
  rw [hl, hr]
  exact Complex.real_smul.symm

theorem torusHigherScalarCLM_add (K : ℕ) (c d : ℂ) (U : TorusHk K ℂ) :
    torusHigherScalarCLM K (c + d) U = torusHigherScalarCLM K c U + torusHigherScalarCLM K d U := by
  apply TorusHk.ext_value
  change torusHkValueCLM (torusHigherScalarCLM K (c + d) U) =
    torusHkValueCLM (torusHigherScalarCLM K c U + torusHigherScalarCLM K d U)
  rw [map_add, torusHigherScalarCLM_value, torusHigherScalarCLM_value, torusHigherScalarCLM_value]
  apply Lp.ext
  filter_upwards [cellScalarCLM_ae (c + d) (torusHkValueCLM U),
    cellScalarCLM_ae c (torusHkValueCLM U), cellScalarCLM_ae d (torusHkValueCLM U),
    Lp.coeFn_add (cellScalarCLM c (torusHkValueCLM U)) (cellScalarCLM d (torusHkValueCLM U))]
    with x hcd hc hd ha
  rw [hcd, ha]
  change _ = cellScalarCLM c (torusHkValueCLM U) x + cellScalarCLM d (torusHkValueCLM U) x
  rw [hc, hd, add_mul]

theorem torusHigherScalarCLM_mul (K : ℕ) (c d : ℂ) (U : TorusHk K ℂ) :
    torusHigherScalarCLM K (c * d) U = torusHigherScalarCLM K c (torusHigherScalarCLM K d U) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (torusHigherScalarCLM K (c * d) U) =
    torusHkValueCLM (torusHigherScalarCLM K c (torusHigherScalarCLM K d U))
  rw [torusHigherScalarCLM_value, torusHigherScalarCLM_value, torusHigherScalarCLM_value]
  apply Lp.ext
  filter_upwards [cellScalarCLM_ae (c * d) (torusHkValueCLM U),
    cellScalarCLM_ae c (cellScalarCLM d (torusHkValueCLM U)),
    cellScalarCLM_ae d (torusHkValueCLM U)] with x hcd hc hd
  rw [hcd, hc, hd, mul_assoc]

theorem torusHigherScalarCLM_real_im (K : ℕ) (c : ℂ) (U : TorusHk K ℂ) :
    torusHigherScalarCLM K c U = c.re • U + c.im • torusHigherScalarCLM K Complex.I U := by
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  calc
    torusHigherScalarCLM K c U = torusHigherScalarCLM K
        ((c.re : ℂ) + (c.im : ℂ) * Complex.I) U := congrArg (fun z => torusHigherScalarCLM K z U) hc
    _ = _ := by rw [torusHigherScalarCLM_add, torusHigherScalarCLM_mul,
      torusHigherScalarCLM_real, torusHigherScalarCLM_real]

end AVRegularity.CycleWords
end

section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! Constant complex scalar multiplication commutes with ordered native weak derivatives. -/

theorem torusHigherScalarCLM_derivative {K r : ℕ} (w : DerivativeWord2 r)
    (c : ℂ) (U : TorusHk (K + r) ℂ) :
    derivativeTorusHk w (torusHigherScalarCLM (K + r) c U) =
      torusHigherScalarCLM K c (derivativeTorusHk w U) := by
  apply Subtype.ext
  apply PiLp.ext
  intro j
  simp only [derivativeTorusHk_apply, torusHigherScalarCLM,
    mapTorusHkCLM_apply, mapTorusHk_jet_eq_compLp]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Every chart selected by the cover has a nonempty physical and cell-time piece. -/

theorem geometryCover_piece_nonempty {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {Φ : ℕ → ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream (Φ (m - 1))}
    {ν B T ta ρs g g0 a B₀ lam Cb CT : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsGeometryCover α q Λ m ζ Φ hφ ν B T ta ρs g g0 a B₀ lam Cb CT qJ Kmax CG l₀ P y₀)
    (i : Fin P) :
    ocPieceStart α q Λ m ν ta (l₀ + i) ≤ ocPieceEnd α q Λ m ν ta T (l₀ + i) := by
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hi : (i.val : ℝ) ≤ (P : ℝ) - 1 := by
    have hi' : (i.val : ℝ) + 1 ≤ (P : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    linarith
  have hlo : ((l₀ : ℝ) + (i.val : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ta + T := by
    have hlast := cov.window.2.2.1
    nlinarith only [hlast, hi, hh]
  have hhi : ta ≤ ((l₀ : ℝ) + (i.val : ℝ) + 1 / 2) * ocTauPP α q Λ m := by
    have hfirst := cov.window.2.1
    have hi0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    nlinarith only [hfirst, hi0, hh]
  have hm : max ta (((l₀ : ℝ) + (i.val : ℝ) - 1 / 2) * ocTauPP α q Λ m) ≤
      min (ta + T) (((l₀ : ℝ) + (i.val : ℝ) + 1 / 2) * ocTauPP α q Λ m) := by
    apply le_min
    · exact max_le (by linarith [cov.pos.2.2.1]) hlo
    · exact max_le hhi (by nlinarith only [hh])
  unfold ocPieceStart ocPieceEnd
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  simpa only [Int.cast_add, Int.cast_natCast] using hm

end AVRegularity.CycleWords
end
