-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneCoefficientZeroCarrier
public import AVRegularity.Statements.Intermediate.Families.TransitionT
public import AVRegularity.Weighted.PlaneH1Readouts
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.OcGamma
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurCondition
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import Mathlib.Algebra.Order.Star.Real

section
section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A scalar metric deviation is an explicitly computed diagonal order-two coupled coefficient array. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def familyDiagonalIdentity (v u : ι) : h u →L[ℝ] h v := by
  classical
  exact if he : u = v then by subst u; exact ContinuousLinearMap.id ℝ (h v) else 0

theorem familyDiagonalIdentity_self (v : ι) :
    familyDiagonalIdentity (h := h) v v = ContinuousLinearMap.id ℝ (h v) := by
  simp [familyDiagonalIdentity]

theorem familyDiagonalIdentity_of_ne (v u : ι) (huv : u ≠ v) :
    familyDiagonalIdentity (h := h) v u = 0 := by
  simp only [familyDiagonalIdentity, dite_eq_right huv]

def planeDiagonalGradientCoefficient (K : ι → ℕ) (D : ℕ)
    (G : ∀ _v : ι, ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v u : ι) (d : admissibleOrders K D v u) (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v) :=
  if d.1 = 2 then
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => h v)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun k => ∑ j : Fin 2, G v t x k j •
        (familyDiagonalIdentity v u).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)
            (fun _ => j))))
  else 0

theorem planeDiagonalGradientCoefficient_of_order_ne (K : ι → ℕ) (D : ℕ)
    (G : ∀ _v : ι, ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v u : ι) (d : admissibleOrders K D v u) (t : ℝ) (x : Vec 2) (hd : d.1 ≠ 2) :
    planeDiagonalGradientCoefficient (h := h) K D G v u d t x = 0 := by
  simp only [planeDiagonalGradientCoefficient, ite_eq_right hd]

theorem planeDiagonalGradientCoefficient_apply_of_two (K : ι → ℕ) (D : ℕ)
    (G : ∀ _v : ι, ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v u : ι) (d : admissibleOrders K D v u) (t : ℝ) (x : Vec 2) (hd : d.1 = 2)
    (g : DerivativeWord2 (d.1 - 1) → h u) (k : Fin 2) :
    planeDiagonalGradientCoefficient K D G v u d t x (WithLp.toLp 2 g) k =
      ∑ j : Fin 2, G v t x k j • familyDiagonalIdentity v u (g (fun _ => j)) := by
  rw [planeDiagonalGradientCoefficient, ite_eq_left hd]
  change (∑ j : Fin 2, G v t x k j •
    (familyDiagonalIdentity v u).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)
        (fun _ => j))) (WithLp.toLp 2 g) = _
  simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Positive time normalization preserves the complete window supremum, including infinite energies. -/

theorem iSup_comp_inv_mul_Icc {L : Type*} [CompleteLattice L]
    (ν a b : ℝ) (hν : 0 < ν) (f : ℝ → L) :
    (⨆ t ∈ Set.Icc (ν * a) (ν * b), f (ν⁻¹ * t)) = ⨆ t ∈ Set.Icc a b, f t := by
  apply le_antisymm
  · apply iSup₂_le
    intro t ht
    exact le_iSup₂_of_le (ν⁻¹ * t) (positiveTimeNormalization_mem_Icc hν ht) le_rfl
  · apply iSup₂_le
    intro t ht
    have hm : ν * t ∈ Set.Icc (ν * a) (ν * b) :=
      ⟨mul_le_mul_of_nonneg_left ht.1 hν.le, mul_le_mul_of_nonneg_left ht.2 hν.le⟩
    have hh : f (ν⁻¹ * (ν * t)) ≤ ⨆ r ∈ Set.Icc (ν * a) (ν * b), f (ν⁻¹ * r) :=
      le_iSup₂_of_le (ν * t) hm le_rfl
    simpa only [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The finite response estimate only requests insertion bounds within the selected finite moment reserve. -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem finiteResponse_reserved_energy_le (M S : Module.End ℝ E)
    (energy : ℕ → E → ℝ≥0∞) (a b : ℕ → ℝ≥0∞) (p N : ℕ)
    (hadd : ∀ n x y, energy n (x + y) ≤ 2 * (energy n x + energy n y))
    (hM : ∀ n, n + p ≤ N → ∀ x, energy n (M x) ≤ a n * energy (n + p) x)
    (hS : ∀ n, n + p ≤ N → ∀ x, energy n (S x) ≤ b n * energy (n + p) x)
    (f : E) (n j h : ℕ) (hN : n + (j + h) * p ≤ N) :
    energy n (finiteResponse 1 M S f j h) ≤
      shiftedResponseEnergyBudget a b p n j h * energy (n + (j + h) * p) f := by
  simp only [Nat.add_mul] at hN
  induction j generalizing n h with
  | zero =>
    induction h generalizing n with
    | zero => simp only [finiteResponse, shiftedResponseEnergyBudget,
         Nat.zero_mul, Nat.add_zero, one_mul, le_refl]
    | succ h ih =>
      simp only [Nat.zero_mul, Nat.succ_mul] at hN
      rw [finiteResponse, Module.End.one_apply, shiftedResponseEnergyBudget]
      have hb := (hS n (by omega) _).trans (mul_le_mul_of_nonneg_left (ih (n + p) (by omega)) zero_le)
      simpa only [Nat.zero_add, Nat.add_zero, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm, mul_assoc] using hb
  | succ j ih =>
    induction h generalizing n with
    | zero =>
      simp only [Nat.zero_mul, Nat.succ_mul] at hN
      rw [finiteResponse, Module.End.one_apply, shiftedResponseEnergyBudget]
      have hb := (hM n (by omega) _).trans (mul_le_mul_of_nonneg_left (ih (n + p) 0 (by omega)) zero_le)
      simpa only [Nat.add_zero, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm, mul_assoc] using hb
    | succ h ihh =>
      simp only [Nat.succ_mul] at hN
      rw [finiteResponse, Module.End.one_apply, Module.End.one_apply, shiftedResponseEnergyBudget]
      have hm := (hM n (by omega) _).trans (mul_le_mul_of_nonneg_left (ih (n + p) (h + 1) (by simp only [Nat.succ_mul]; omega)) zero_le)
      have hs := (hS n (by omega) _).trans (mul_le_mul_of_nonneg_left (ihh (n + p) (by simp only [Nat.succ_mul]; omega)) zero_le)
      have hm' : energy n (M (finiteResponse 1 M S f j (h + 1))) ≤
          (a n * shiftedResponseEnergyBudget a b p (n + p) j (h + 1)) *
            energy (n + ((j + 1) + (h + 1)) * p) f := by
        simpa only [Nat.add_mul, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm, ← mul_assoc] using hm
      have hs' : energy n (S (finiteResponse 1 M S f (j + 1) h)) ≤
          (b n * shiftedResponseEnergyBudget a b p (n + p) (j + 1) h) *
            energy (n + ((j + 1) + (h + 1)) * p) f := by
        simpa only [Nat.add_mul, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm, ← mul_assoc] using hs
      have hb := (hadd n _ _).trans
        (mul_le_mul_of_nonneg_left (add_le_add hm' hs') zero_le)
      simpa only [add_mul, mul_assoc] using hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Explicit insertion words for the Taylor response, listed with the last insertion first. -/

def responseInsertionWords : ℕ → ℕ → List (List Bool)
  | 0, 0 => [[]]
  | j + 1, 0 => (responseInsertionWords j 0).map (false :: ·)
  | 0, h + 1 => (responseInsertionWords 0 h).map (true :: ·)
  | j + 1, h + 1 => (responseInsertionWords j (h + 1)).map (false :: ·) ++
      (responseInsertionWords (j + 1) h).map (true :: ·)
termination_by j h => j + h

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def responseWordOperator (R D S : Module.End ℝ E) : List Bool → Module.End ℝ E
  | [] => 1
  | b :: w => (if b then R * S else R * D) * responseWordOperator R D S w

theorem responseWordOperator_sum_cons (R D S : Module.End ℝ E)
    (b : Bool) (ws : List (List Bool)) :
    ((ws.map (b :: ·)).map (responseWordOperator R D S)).sum =
      (if b then R * S else R * D) * (ws.map (responseWordOperator R D S)).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.sum_cons, responseWordOperator, ih, mul_add]

theorem finiteResponseOperator_eq_word_sum (R D S : Module.End ℝ E) (j h : ℕ) :
    finiteResponseOperator R D S j h =
      ((responseInsertionWords j h).map (responseWordOperator R D S)).sum := by
  induction j generalizing h with
  | zero =>
    induction h with
    | zero => simp [finiteResponseOperator, responseInsertionWords, responseWordOperator]
    | succ h ih =>
      rw [finiteResponseOperator, responseInsertionWords, responseWordOperator_sum_cons, ih]
      rfl
  | succ j ih =>
    induction h with
    | zero =>
      rw [finiteResponseOperator, responseInsertionWords, responseWordOperator_sum_cons, ih]
      rfl
    | succ h ihh =>
      rw [finiteResponseOperator, responseInsertionWords, List.map_append, List.sum_append,
        responseWordOperator_sum_cons, responseWordOperator_sum_cons, ih, ihh]
      rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! One fixed finite scalar response reserve controls both actual insertion prices. -/

def scalarResponseTwoInsertionCommonPrice (Kmax : ℕ) (L : ℝ) (Cw : ℕ → ℝ)
    (N : ℕ) (Dm Ds : ℝ≥0∞) : ℝ≥0∞ :=
  scalarResponseGradientReservePrice Kmax L Cw N * (Dm + Ds + 1)

theorem scalarResponseTwoInsertionCommonPrice_ne_top (Kmax : ℕ) (L : ℝ) (Cw : ℕ → ℝ)
    (N : ℕ) (Dm Ds : ℝ≥0∞) (hm : Dm ≠ ⊤) (hs : Ds ≠ ⊤) :
    scalarResponseTwoInsertionCommonPrice Kmax L Cw N Dm Ds ≠ ⊤ := by
  exact ENNReal.mul_ne_top (scalarResponseGradientReservePrice_ne_top Kmax L Cw N)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hm, hs⟩, ENNReal.one_ne_top⟩)

theorem scalarResponseTwoInsertionCommonPrice_metric (Kmax : ℕ) (L : ℝ) (Cw : ℕ → ℝ)
    (N n : ℕ) (hn : n ≤ N) (Dm Ds η : ℝ≥0∞) :
    scalarResponseGradientPrice Kmax L Cw n * Dm * η ^ 2 ≤
      scalarResponseTwoInsertionCommonPrice Kmax L Cw N Dm Ds * η ^ 2 := by
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply mul_le_mul' (scalarResponseGradientPrice_le_reserve Kmax L Cw N n hn)
  exact (show Dm ≤ Dm + Ds from le_self_add).trans le_self_add

theorem scalarResponseTwoInsertionCommonPrice_source (Kmax : ℕ) (L : ℝ) (Cw : ℕ → ℝ)
    (N : ℕ) (Dm Ds θ : ℝ≥0∞) :
    (scalarResponseGradientReservePrice Kmax L Cw N * Ds) * θ ^ 2 ≤
      scalarResponseTwoInsertionCommonPrice Kmax L Cw N Dm Ds * θ ^ 2 := by
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply mul_le_mul_of_nonneg_left _ zero_le
  calc
    Ds ≤ Ds + Dm := le_self_add
    _ = Dm + Ds := add_comm _ _
    _ ≤ Dm + Ds + 1 := le_self_add

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Row displacements of all torus patch images are the same full-lattice sum. -/

def latticeDisplacementEquiv (i : Fin 2 → ℤ) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun k := k - i
  invFun k := k + i
  left_inv k := sub_add_cancel k i
  right_inv k := add_sub_cancel_right k i

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The finite quadratic response price retains separate metric and source powers. -/

theorem shiftedResponseEnergyBudget_const_homogeneous (a b : ℝ≥0∞) (p n j h : ℕ) :
    shiftedResponseEnergyBudget (fun _ => a) (fun _ => b) p n j h =
      shiftedResponseEnergyBudget (fun _ => 1) (fun _ => 1) p n j h * a ^ j * b ^ h := by
  induction j generalizing n h with
  | zero =>
    induction h generalizing n with
    | zero => simp only [shiftedResponseEnergyBudget, pow_zero, one_mul]
    | succ h ih =>
      rw [shiftedResponseEnergyBudget, shiftedResponseEnergyBudget, ih (n + p), pow_succ]
      simp only [one_mul, pow_zero, mul_one]
      ring
  | succ j ih =>
    induction h generalizing n with
    | zero =>
      rw [shiftedResponseEnergyBudget, shiftedResponseEnergyBudget, ih (n + p) 0, pow_succ]
      simp only [one_mul, pow_zero, mul_one]
      ring
    | succ h ihh =>
      rw [shiftedResponseEnergyBudget, shiftedResponseEnergyBudget,
        ih (n + p) (h + 1), ihh (n + p), pow_succ a, pow_succ b]
      simp only [one_mul]
      ring

theorem shiftedResponseEnergyBudget_unit_ne_top (p n j h : ℕ) :
    shiftedResponseEnergyBudget (fun _ => 1) (fun _ => 1) p n j h ≠ ⊤ := by
  induction j generalizing n h with
  | zero =>
    induction h generalizing n with
    | zero => simp only [shiftedResponseEnergyBudget, ne_eq, ENNReal.one_ne_top, not_false_eq_true]
    | succ h ih =>
      rw [shiftedResponseEnergyBudget, one_mul]
      exact ih (n + p)
  | succ j ih =>
    induction h generalizing n with
    | zero =>
      rw [shiftedResponseEnergyBudget, one_mul]
      exact ih (n + p) 0
    | succ h ihh =>
      rw [shiftedResponseEnergyBudget, one_mul, one_mul]
      exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.add_ne_top.mpr ⟨ih (n + p) (h + 1), ihh (n + p)⟩)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! The exhausting cutoffs have uniformly bounded derivatives tending to zero. -/

theorem spatialApproximationCutoff_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x v,
      |fderiv ℝ (spatialApproximationCutoff n) x v| ≤
        C * spatialApproximationScale n * ‖v‖ := by
  have hbum : ContDiff ℝ (⊤ : ℕ∞) (spatialApproximationBump : Vec 2 → ℝ) :=
    spatialApproximationBump.contDiff
  have hc : Continuous (fderiv ℝ (spatialApproximationBump : Vec 2 → ℝ)) :=
    hbum.continuous_fderiv (by simp)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support
    (spatialApproximationBump.hasCompactSupport.fderiv ℝ)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro n x v
  have hp := (hbum.differentiable (by simp)
    (spatialApproximationEquiv n x)).hasFDerivAt.comp x
    (spatialApproximationEquiv n).hasFDerivAt
  have he := congrArg (fun A : Vec 2 →L[ℝ] ℝ => A v) hp.fderiv
  change fderiv ℝ (spatialApproximationCutoff n) x v =
    fderiv ℝ spatialApproximationBump (spatialApproximationEquiv n x)
      (spatialApproximationScale n • v) at he
  rw [he]
  calc
    _ = ‖fderiv ℝ spatialApproximationBump (spatialApproximationEquiv n x)
        (spatialApproximationScale n • v)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ spatialApproximationBump (spatialApproximationEquiv n x)‖ *
        ‖spatialApproximationScale n • v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ max B 0 * ‖spatialApproximationScale n • v‖ :=
      mul_le_mul_of_nonneg_right ((hB _).trans (le_max_left _ _)) (norm_nonneg _)
    _ = _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (spatialApproximationScale_pos n)]
      ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Exact support of the order-lowering transition array. -/

theorem transitionT_zero_above_native_order
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (I A : List (Fin 2))
    (h : I.length < A.length) : transitionT K I A = 0 := by
  induction I generalizing A with
  | nil =>
    cases A with
    | nil => simp at h
    | cons a A => rfl
  | cons i I ih =>
    cases A with
    | nil => simp at h
    | cons a A =>
      have hI : I.length < (a :: A).length := by simp only [List.length_cons] at *; omega
      have hA : I.length < A.length := by simp only [List.length_cons] at h; omega
      funext x
      simp [transitionT, ih (a :: A) hI, ih A hA]

theorem transitionT_empty_output_nonempty_native
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (I : List (Fin 2)) :
    transitionT K (i :: I) [] = 0 := by
  induction I generalizing i with
  | nil =>
    funext x
    simp [transitionT]
  | cons j I ih =>
    funext x
    change (∑ b : Fin 2, K x b i *
      fderiv ℝ (transitionT K (j :: I) []) x (basisVec b)) + 0 = 0
    rw [ih j]
    simp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Pulling each lattice-cell integral back to the same fundamental cell. -/

theorem cellAt_add_shift_preimage (n : Fin 2 → ℤ) :
    (fun x : Vec 2 => x + AVenhance.latticeShift n) ⁻¹' Applications.cellAt n =
      Applications.cellI := by
  ext x
  simp [Applications.cellAt]

theorem lintegral_cellAt_translate (n : Fin 2 → ℤ) (f : Vec 2 → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x in Applications.cellAt n, f x ∂volume) =
      ∫⁻ x in Applications.cellI, f (x + AVenhance.latticeShift n) ∂volume := by
  have hm : MeasurePreserving (fun x : Vec 2 => x + AVenhance.latticeShift n)
      (volume.restrict Applications.cellI) (volume.restrict (Applications.cellAt n)) := by
    simpa only [cellAt_add_shift_preimage] using
      (measurePreserving_add_right (volume : Measure (Vec 2))
        (AVenhance.latticeShift n)).restrict_preimage (Applications.measurableSet_cellAt n)
  exact (hm.lintegral_comp hf).symm

theorem lintegral_tiling_translate (f : Vec 2 → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂volume =
      ∑' n : Fin 2 → ℤ, ∫⁻ x in Applications.cellI,
        f (x + AVenhance.latticeShift n) ∂volume := by
  rw [lintegral_cell_tiling]
  exact tsum_congr (fun n => lintegral_cellAt_translate n f hf)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! A finite positive jet majorant for one literal K B T Piola summand. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem triple_product_weighted_jet_bound (f g k : E → ℝ) (x : E) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ) f) (hg : ContDiff ℝ (n : ℕ) g) (hk : ContDiff ℝ (n : ℕ) k)
    (ρ A B C : ℝ) (hρ : 0 ≤ ρ)
    (hfj : ∀ j ≤ n, ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgj : ∀ j ≤ n, ρ ^ j * ‖iteratedFDeriv ℝ j g x‖ ≤ B)
    (hkj : ∀ j ≤ n, ρ ^ j * ‖iteratedFDeriv ℝ j k x‖ ≤ C) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => f y * g y * k y) x‖ ≤
      ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * A * B * C := by
  have hA : 0 ≤ A := (mul_nonneg (pow_nonneg hρ _) (norm_nonneg _)).trans (hfj 0 (Nat.zero_le _))
  have hB : 0 ≤ B := (mul_nonneg (pow_nonneg hρ _) (norm_nonneg _)).trans (hgj 0 (Nat.zero_le _))
  let AB := (n + 1 : ℕ) * (2 : ℝ) ^ n * A * B
  have hab : ∀ j ≤ n, ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => f y * g y) x‖ ≤ AB := by
    intro j hj
    have hh := uniform_product_weighted_jet_bound f g x j
      (hf.of_le (by exact_mod_cast hj)) (hg.of_le (by exact_mod_cast hj)) ρ A B hρ
      (fun l hl => hfj l (hl.trans hj)) (fun l hl => hgj l (hl.trans hj))
    apply hh.trans
    dsimp [AB]
    have hc : ((j + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hj 1
    have hp : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
    gcongr
  have hh := uniform_product_weighted_jet_bound (fun y => f y * g y) k x n
    (hf.mul hg) hk ρ AB C hρ hab hkj
  apply hh.trans_eq
  dsimp [AB]
  ring

end AVRegularity.CycleJointProofs
end
end

section
public section
namespace AVRegularity.CycleJointProofs

/-! A single integer reserve absorbs all adjoint weight prices up to a fixed
moment order, as required by the joint preparation's natural reserves. -/

theorem exists_uniform_natural_scalar_square_reserve (Cw : ℕ → ℝ) (N : ℕ) :
    ∃ Ls : ℕ, 1 ≤ Ls ∧ ∀ k ≤ N, Real.exp (18 * Cw k) / (Ls : ℝ) ^ 2 ≤ 1 / 16 := by
  obtain ⟨L, hL, hreserve⟩ := exists_uniform_scalar_square_reserve Cw N
  obtain ⟨Ls, hLs⟩ := exists_nat_ge L
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hLs1 : 1 ≤ Ls := by exact_mod_cast hL.trans hLs
  refine ⟨Ls, hLs1, ?_⟩
  intro k hk
  have hsquare : L ^ 2 ≤ (Ls : ℝ) ^ 2 :=
    (sq_le_sq₀ hLp.le (Nat.cast_nonneg Ls)).mpr hLs
  exact (div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_pos hLp) hsquare).trans
    (hreserve k hk)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Product-rule algebra for localizing the actual coupled weak integrand. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def coupledWeakRhs (ν : ℝ) (v : Vec 2) (φ : H) (dφ du : Fin 2 → H)
    (flux F : Fin 2 → H) (g : H) : ℝ :=
  -(∑ k : Fin 2, v k * inner ℝ (du k) φ)
    - ν * ∑ k : Fin 2, inner ℝ (du k) (dφ k)
    - ∑ k : Fin 2, inner ℝ (flux k + F k) (dφ k)
    + inner ℝ g φ

theorem coupledWeakRhs_cutoff (ν χ : ℝ) (dχ v : Vec 2) (φ : H)
    (dφ du flux F : Fin 2 → H) (g : H) :
    coupledWeakRhs ν v (χ • φ) (fun k => dχ k • φ + χ • dφ k) du flux F g =
      χ * coupledWeakRhs ν v φ dφ du flux F g -
        ∑ k : Fin 2, dχ k * (ν * inner ℝ (du k) φ + inner ℝ (flux k + F k) φ) := by
  simp only [coupledWeakRhs, Fin.sum_univ_two, inner_add_right, inner_smul_right]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual source insertion uses one finite chart-response reserve and the original graph budget. -/

theorem actualTaylorSourceInsertionPrice_ennreal_budget
    (D p : ℕ) (Cprep Cgraph θ ζ : ℝ) (hθ : 0 ≤ θ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    2 * (ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2) +
      ENNReal.ofReal ((ζ ^ p * (Cgraph * θ)) ^ 2)) ≤
      ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph) * (ENNReal.ofReal θ) ^ 2 := by
  have he := ENNReal.ofReal_le_ofReal
    (actualTaylorSourceInsertionPrice_budget D p Cprep Cgraph θ ζ hζ hζ1)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ENNReal.ofReal_mul (actualTaylorSourceInsertionPrice_nonneg D Cprep Cgraph),
    ENNReal.ofReal_pow hθ 2] at he
  simpa only [ENNReal.ofReal_ofNat] using he

theorem actualTaylorSourceInsertionPrice_le_response_reserve
    (D p Kmax N n : ℕ) (hn : n ≤ N) (L : ℝ) (Cw : ℕ → ℝ)
    (Cprep Cgraph θ ζ : ℝ) (hθ : 0 ≤ θ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    scalarResponseGradientPrice Kmax L Cw n *
      (2 * (ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2) +
        ENNReal.ofReal ((ζ ^ p * (Cgraph * θ)) ^ 2))) ≤
      (scalarResponseGradientReservePrice Kmax L Cw N *
        ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph)) * (ENNReal.ofReal θ) ^ 2 := by
  have he := mul_le_mul'
    (scalarResponseGradientPrice_le_reserve Kmax L Cw N n hn)
    (actualTaylorSourceInsertionPrice_ennreal_budget D p Cprep Cgraph θ ζ hθ hζ hζ1)
  simpa only [mul_assoc] using he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Exact signed weak-test integration over all integer images of the fundamental cell. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem integral_cell_tiling (f : Vec 2 → E) (hf : Integrable f volume) :
    ∫ x, f x ∂volume = ∑' n : Fin 2 → ℤ, ∫ x in Applications.cellAt n, f x ∂volume := by
  have hfi : IntegrableOn f (⋃ n : Fin 2 → ℤ, Applications.cellAt n) volume := by
    simpa only [cellAt_iUnion, IntegrableOn, Measure.restrict_univ] using hf
  simpa only [cellAt_iUnion, Measure.restrict_univ] using
    integral_iUnion Applications.measurableSet_cellAt
      (fun _ _ h => Applications.cellAt_disjoint h) hfi

omit [CompleteSpace E] in
theorem integral_cellAt_translate (n : Fin 2 → ℤ) (f : Vec 2 → E) :
    (∫ x in Applications.cellAt n, f x ∂volume) =
      ∫ x in Applications.cellI, f (x + AVenhance.latticeShift n) ∂volume := by
  have hm : MeasurePreserving (fun x : Vec 2 => x + AVenhance.latticeShift n)
      (volume.restrict Applications.cellI) (volume.restrict (Applications.cellAt n)) := by
    simpa only [cellAt_add_shift_preimage] using
      (measurePreserving_add_right (volume : Measure (Vec 2))
        (AVenhance.latticeShift n)).restrict_preimage (Applications.measurableSet_cellAt n)
  exact (hm.integral_comp (MeasurableEquiv.addRight (AVenhance.latticeShift n)).measurableEmbedding f).symm

omit [CompleteSpace E] in
theorem integral_tiling_translate (f : Vec 2 → E) (hf : Integrable f volume) :
    ∫ x, f x ∂volume = ∑' n : Fin 2 → ℤ, ∫ x in Applications.cellI,
      f (x + AVenhance.latticeShift n) ∂volume := by
  rw [integral_cell_tiling f hf]
  exact tsum_congr (fun n => integral_cellAt_translate n f)

omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem summable_cell_integral_norm (f : Vec 2 → E) (hf : Integrable f volume) :
    Summable (fun n : Fin 2 → ℤ => ∫ x in Applications.cellI,
      ‖f (x + AVenhance.latticeShift n)‖ ∂volume) := by
  have hfi : IntegrableOn (fun x => ‖f x‖)
      (⋃ n : Fin 2 → ℤ, Applications.cellAt n) volume := by
    simpa only [cellAt_iUnion, IntegrableOn, Measure.restrict_univ] using hf.norm
  have hs := (hasSum_integral_iUnion Applications.measurableSet_cellAt
    (fun _ _ h => Applications.cellAt_disjoint h) hfi).summable
  simpa only [integral_cellAt_translate] using hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped Matrix
namespace AVRegularity.CycleJointProofs

/-! Contravariant fluxes pair with pulled gradients exactly as physical fluxes do. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hilbertMatrixAction_inverse_pair (J : Matrix (Fin 2) (Fin 2) ℝ)
    (hJ : IsUnit J.det) (G H : Fin 2 → E) :
    (∑ k : Fin 2, inner ℝ (hilbertMatrixAction Jᵀ G k)
      (hilbertMatrixAction J⁻¹ H k)) = ∑ k : Fin 2, inner ℝ (G k) (H k) := by
  rw [hilbertMatrixAction_pair, Matrix.transpose_transpose,
    ← hilbertMatrixAction_mul, Matrix.mul_nonsing_inv J hJ, hilbertMatrixAction_one]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The homogeneous coupled weak equation has three literal groups of integrable atoms. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def homogeneousWeakRhsAtom (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (j : Fin 3) (s : ℝ) (x : Vec 2) : ℝ :=
  if j = 0 then -(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
  else if j = 1 then -ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
  else -(∑ k : Fin 2, inner ℝ (flux s x k) (dφ k x))

theorem homogeneousWeakRhsAtom_sum (ν s : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) :
    (fun x => ∑ j : Fin 3, homogeneousWeakRhsAtom ν v φ dφ du flux j s x) =
      weakIdentityRhs ν v φ dφ du flux 0 0 s := by
  funext x
  simp [Fin.sum_univ_three, homogeneousWeakRhsAtom, weakIdentityRhs, sub_eq_add_neg]

theorem coupledWeakIdentity_homogeneous_atoms (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E) (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hw : CoupledWeakIdentity μ ν a t v u f φ dφ du flux 0 0)
    (hi : ∀ s ∈ Set.Ioc a t, ∀ j, Integrable
      (homogeneousWeakRhsAtom ν v φ dφ du flux j s) μ) :
    (∫ x, inner ℝ (u x) (φ x) ∂μ) - (∫ x, inner ℝ (f x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a t, ∑ j : Fin 3, ∫ x, homogeneousWeakRhsAtom ν v φ dφ du flux j s x ∂μ := by
  refine hw.2.2.2.2.trans (integral_congr_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  change (∫ x, weakIdentityRhs ν v φ dφ du flux 0 0 s x ∂μ) = _
  rw [← homogeneousWeakRhsAtom_sum]
  exact integral_finsetSum Finset.univ (fun j _ => hi s hs j)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Periodic coefficients and actual periodic Sobolev readouts make every weak RHS atom periodic. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weakIdentityRhs_periodic (ν s : ℝ) (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hv : AVenhance.IsZ2Periodic (v s)) (hφ : AVenhance.IsZ2Periodic φ)
    (hdφ : ∀ k, AVenhance.IsZ2Periodic (dφ k))
    (hdu : ∀ k, AVenhance.IsZ2Periodic (du s k))
    (hflux : AVenhance.IsZ2Periodic (flux s)) (hF : AVenhance.IsZ2Periodic (F s))
    (hg : AVenhance.IsZ2Periodic (g s)) :
    AVenhance.IsZ2Periodic (weakIdentityRhs ν v φ dφ du flux F g s) := by
  intro n x
  have hd : ∀ k, du s k (x + AVenhance.latticeShift n) = du s k x := fun k => hdu k n x
  have hp : ∀ k, dφ k (x + AVenhance.latticeShift n) = dφ k x := fun k => hdφ k n x
  simp only [weakIdentityRhs, hv n x, hφ n x, hd, hp, hflux n x, hF n x, hg n x]

theorem weakCutoffCorrection_periodic (ν : ℝ) (φ du : Vec 2 → E)
    (flux F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (k : Fin 2)
    (hφ : AVenhance.IsZ2Periodic φ) (hdu : AVenhance.IsZ2Periodic du)
    (hflux : AVenhance.IsZ2Periodic flux) (hF : AVenhance.IsZ2Periodic F) :
    AVenhance.IsZ2Periodic (fun x => ν * inner ℝ (du x) (φ x) +
      inner ℝ (flux x k + F x k) (φ x)) := by
  intro n x
  change ν * inner ℝ (du (x + AVenhance.latticeShift n)) (φ (x + AVenhance.latticeShift n)) +
    inner ℝ (flux (x + AVenhance.latticeShift n) k + F (x + AVenhance.latticeShift n) k)
      (φ (x + AVenhance.latticeShift n)) = _
  rw [hdu n x, hφ n x, hflux n x, hF n x]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Any finite patch weights with a bounded image sum have a uniform periodic L2 budget. -/

theorem periodic_weight_integral_budget {J : Type*} [Fintype J]
    (w : J → Vec 2 → ℝ≥0∞) (hw : ∀ j, Measurable (w j))
    (B : ℝ≥0∞) (hb : ∀ x, (∑ j, ∑' n : Fin 2 → ℤ, w j (x + AVenhance.latticeShift n)) ≤ B)
    (g : Vec 2 → ℝ≥0∞) (hg : Measurable g) (hper : AVenhance.IsZ2Periodic g) :
    (∑ j, ∫⁻ x, w j x * g x ∂volume) ≤ B * ∫⁻ x in Applications.cellI, g x ∂volume := by
  have hper' (n : Fin 2 → ℤ) (x : Vec 2) :
      g (x + AVenhance.latticeShift n) = g x := hper n x
  have ht (j : J) : (∫⁻ x, w j x * g x ∂volume) =
      ∫⁻ x in Applications.cellI, (∑' n : Fin 2 → ℤ, w j (x + AVenhance.latticeShift n)) * g x ∂volume := by
    rw [lintegral_tiling_translate (fun x => w j x * g x) ((hw j).mul hg)]
    simp only [hper']
    rw [← lintegral_tsum (f := fun n x => w j (x + AVenhance.latticeShift n) * g x)
      (fun n => (((hw j).comp (measurable_id.add measurable_const)).mul hg).aemeasurable)]
    simp only [ENNReal.tsum_mul_right]
  simp_rw [ht]
  have hwm (j : J) : Measurable (fun x =>
      (∑' n : Fin 2 → ℤ, w j (x + AVenhance.latticeShift n)) * g x) :=
    (Measurable.tsum (fun n => (hw j).comp (measurable_id.add measurable_const))).mul hg
  rw [← lintegral_finsetSum Finset.univ
    (f := fun j x => (∑' n : Fin 2 → ℤ, w j (x + AVenhance.latticeShift n)) * g x)
    (fun j _ => hwm j)]
  have he : (∫⁻ x in Applications.cellI,
      (∑ j, (∑' n : Fin 2 → ℤ, w j (x + AVenhance.latticeShift n)) * g x) ∂volume) ≤
      ∫⁻ x in Applications.cellI, B * g x ∂volume := by
    apply lintegral_mono
    intro x
    change (∑ j, (∑' n : Fin 2 → ℤ, w j (x + AVenhance.latticeShift n)) * g x) ≤ B * g x
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hb x) (show 0 ≤ g x from zero_le)
  exact he.trans_eq (lintegral_const_mul B hg)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The second-order metric perturbation retains its exact matrix under cell normalization. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem planeDiagonalGradientCoefficient_cell_scaling (K : ι → ℕ) (D : ℕ)
    (G : ∀ _v : ι, ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (e : ℝ) (he : e ≠ 0) (y : Vec 2) (v u : ι) (d : admissibleOrders K D v u)
    (t : ℝ) (z : Vec 2) :
    (e * (e ^ (d.1 - 1))⁻¹) • planeDiagonalGradientCoefficient (h := h) K D G v u d
      (e ^ 2 * t) (y + e • z) =
      planeDiagonalGradientCoefficient K D (fun i r x => G i (e ^ 2 * r) (y + e • x)) v u d t z := by
  by_cases hd : d.1 = 2
  · have hprice : e * (e ^ (d.1 - 1))⁻¹ = 1 := by
      simp only [hd, Nat.reduceSub, pow_one, mul_inv_cancel₀ he]
    rw [hprice, one_smul]
    rfl
  · rw [planeDiagonalGradientCoefficient_of_order_ne K D G v u d _ _ hd,
      planeDiagonalGradientCoefficient_of_order_ne K D _ v u d _ _ hd]
    apply ContinuousLinearMap.ext
    intro g
    simp only [smul_apply, zero_apply, smul_zero]
end

/-! The literal diagonal metric perturbation plus inherited source array,
independent of its later energy estimates. -/

/-- The actual metric perturbation plus the original source coefficient. -/
def planeMetricSourceCoefficient {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (K : ι → ℕ) (D : ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ∀ i u, (d : admissibleOrders K D i u) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) :=
  fun i u d t z => planeDiagonalGradientCoefficient (h := h) K D
    (fun _ r x => G r x - 1) i u d t z + A i u d t z

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Translate the full integrated plane weak identity, retaining every integrability clause. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_translate (ν a t : ℝ) (z : Vec 2)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (h : CoupledWeakIdentity volume ν a t v u f (fun y => φ (y - z))
      (fun k y => dφ k (y - z)) du flux F g) :
    CoupledWeakIdentity volume ν a t (fun s x => v s (x + z))
      (fun x => u (x + z)) (fun x => f (x + z)) φ dφ
      (fun s k x => du s k (x + z)) (fun s x => flux s (x + z))
      (fun s x => F s (x + z)) (fun s x => g s (x + z)) := by
  let R := weakIdentityRhs ν v (fun y => φ (y - z)) (fun k y => dφ k (y - z)) du flux F g
  let R' := weakIdentityRhs ν (fun s x => v s (x + z)) φ dφ
    (fun s k x => du s k (x + z)) (fun s x => flux s (x + z))
    (fun s x => F s (x + z)) (fun s x => g s (x + z))
  change Integrable _ volume ∧ Integrable _ volume ∧
    (∀ s ∈ Set.Ioc a t, Integrable (R s) volume) ∧
    IntegrableOn (fun s => ∫ x, R s x) (Set.Ioc a t) ∧ _ at h
  rcases h with ⟨hu, hf, hs, htime, he⟩
  have hr (s : ℝ) : R' s = fun x => R s (x + z) := by
    funext x
    simp only [R', R, weakIdentityRhs, add_sub_cancel_right]
  have hpair (q : Vec 2 → E) : (∫ x, inner ℝ (q (x + z)) (φ x)) =
      ∫ y, inner ℝ (q y) (φ (y - z)) := by
    simpa only [add_sub_cancel_right] using integral_add_right_eq_self
      (μ := (volume : Measure (Vec 2))) (fun y => inner ℝ (q y) (φ (y - z))) z
  have hi (s : ℝ) : (∫ x, R' s x) = ∫ x, R s x := by
    rw [hr s]
    exact integral_add_right_eq_self (μ := (volume : Measure (Vec 2))) (R s) z
  change Integrable _ volume ∧ Integrable _ volume ∧
    (∀ s ∈ Set.Ioc a t, Integrable (R' s) volume) ∧
    IntegrableOn (fun s => ∫ x, R' s x) (Set.Ioc a t) ∧ _
  refine ⟨?_, ?_, ?_, htime.congr (Filter.Eventually.of_forall (fun s => (hi s).symm)), ?_⟩
  · simpa only [Function.comp_def, add_sub_cancel_right] using
      ((measurePreserving_add_right volume z).integrable_comp hu.aestronglyMeasurable).mpr hu
  · simpa only [Function.comp_def, add_sub_cancel_right] using
      ((measurePreserving_add_right volume z).integrable_comp hf.aestronglyMeasurable).mpr hf
  · intro s ht
    rw [hr s]
    exact ((measurePreserving_add_right volume z).integrable_comp (hs s ht).aestronglyMeasurable).mpr (hs s ht)
  · change (∫ x, inner ℝ (u (x + z)) (φ x)) - (∫ x, inner ℝ (f (x + z)) (φ x)) =
      ∫ s in Set.Ioc a t, ∫ x, R' s x
    rw [hpair u, hpair f]
    simp_rw [hi]
    exact he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The spatial cell prices cancel in each atom of the genuine weak equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem planeWeakSpatialRhs_affine (ν e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (t : ℝ) (z : Vec 2) :
    planeWeakSpatialRhs (ν * (e⁻¹) ^ 2) (fun r x => e⁻¹ • v r (y + e • x))
      (fun x => φ (y + e • x)) (fun k x => e • dφ k (y + e • x))
      (fun r k x => e • du r k (y + e • x))
      (fun r x => e⁻¹ • flux r (y + e • x))
      (fun r x => e⁻¹ • F r (y + e • x)) (fun r x => g r (y + e • x)) t z =
      planeWeakSpatialRhs ν v φ dφ du flux F g t (y + e • z) := by
  simp only [planeWeakSpatialRhs, Pi.smul_apply, PiLp.smul_apply, ← smul_add,
    real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
  have hconvection (k : Fin 2) :
      (e⁻¹ * v t (y + e • z) k) *
        (e * inner ℝ (du t k (y + e • z)) (φ (y + e • z))) =
      v t (y + e • z) k * inner ℝ (du t k (y + e • z)) (φ (y + e • z)) := by
    field_simp
  simp_rw [hconvection]
  simp only [← mul_assoc e e⁻¹, mul_inv_cancel₀ he, one_mul]
  simp_rw [← mul_assoc e e]
  rw [← Finset.mul_sum]
  congr 2
  field_simp

end AVRegularity.CycleJointProofs
end
end

section
public section
namespace AVRegularity.CycleJointProofs

/-! Admissibility gives the positive scale exponents spent by joint preparation. -/

theorem preparation_gamma_pos {α s q : ℝ} (hα : 0 < α) (hq : IsAdmissibleQ α s q) :
    0 < ocGamma α q := by
  have hq1 : 1 < q := hq.1
  exact div_pos (mul_pos (sub_pos.mpr hq1) (by linarith only [hα]))
    (by linarith only [hq1])

theorem preparation_delta_pos {α s q : ℝ} (hα : 0 < α) (hq : IsAdmissibleQ α s q) :
    0 < ocDelta α q := by
  have hq1 : 1 < q := hq.1
  have hq3 := hq.2.2.1
  have hid : (2 - (1 + α)) / (2 * ((1 + α) - 1)) = (1 - α) / (2 * α) := by ring
  rw [hid, lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hα)] at hq3
  have hnum : (2 * q + 1) * (1 + α) < 2 * q + 2 := by nlinarith only [hq3]
  have hfrac : (2 * q + 1) * (1 + α) / (2 * q + 2) < 1 :=
    (div_lt_one (by linarith only [hq1])).mpr hnum
  exact mul_pos (div_pos (sub_pos.mpr hq1) (by norm_num)) (sub_pos.mpr hfrac)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Every finite nonnegative strictly triangular matrix admits positive Schur-small masses. -/

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem rankMassConjugated_entry_le (r : ι → ℕ) (A : Matrix ι ι ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (hr : ∀ v u, A v u ≠ 0 → r u < r v)
    (L B : ℝ) (hL : 1 ≤ L) (hb : ∀ v u, A v u ≤ B) (v u : ι) :
    massConjugatedMatrix (rankMass r L) A v u ≤ B / L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  by_cases hz : A v u = 0
  · have hB : 0 ≤ B := (hA v u).trans (hb v u)
    simpa only [massConjugatedMatrix, hz, mul_zero] using div_nonneg hB hLp.le
  · have ht := mul_le_mul (rankMass_sqrt_ratio_le_inv r L hL v u (hr v u hz))
      (hb v u) (hA v u) (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hLp.le)
    simpa only [massConjugatedMatrix, one_div_mul_eq_div] using ht

theorem rankMass_schurCondition (r : ι → ℕ) (A : Matrix ι ι ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (hr : ∀ v u, A v u ≠ 0 → r u < r v)
    (L B : ℝ) (hL : 1 ≤ L) (hb : ∀ v u, A v u ≤ B)
    (hscale : 8 * (Fintype.card ι : ℝ) * B ≤ L) :
    SchurCondition (massConjugatedMatrix (rankMass r L) A) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hs : (Fintype.card ι : ℝ) * B / L ≤ 1 / 8 := by
    apply (div_le_iff₀ hLp).mpr
    linarith only [hscale]
  constructor
  · intro v
    calc
      _ ≤ ∑ _u : ι, B / L := Finset.sum_le_sum (fun u _ =>
        rankMassConjugated_entry_le r A hA hr L B hL hb v u)
      _ = (Fintype.card ι : ℝ) * B / L := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc]
      _ ≤ 1 / 8 := hs
  · intro u
    calc
      _ ≤ ∑ _v : ι, B / L := Finset.sum_le_sum (fun v _ =>
        rankMassConjugated_entry_le r A hA hr L B hL hb v u)
      _ = (Fintype.card ι : ℝ) * B / L := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc]
      _ ≤ 1 / 8 := hs

theorem exists_rankMass_schurCondition (r : ι → ℕ) (A : Matrix ι ι ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (hr : ∀ v u, A v u ≠ 0 → r u < r v) :
    ∃ π : ι → ℝ, (∀ v, 0 < π v) ∧ SchurCondition (massConjugatedMatrix π A) := by
  let B : ℝ := ∑ v, ∑ u, A v u
  have hb (v u : ι) : A v u ≤ B :=
    (Finset.single_le_sum (fun j _ => hA v j) (Finset.mem_univ u)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hA i j)) (Finset.mem_univ v))
  let L : ℝ := max 1 (8 * (Fintype.card ι : ℝ) * B)
  have hL : 1 ≤ L := le_max_left _ _
  refine ⟨rankMass r L, rankMass_pos r L (lt_of_lt_of_le zero_lt_one hL), ?_⟩
  exact rankMass_schurCondition r A hA hr L B hL hb (le_max_right _ _)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The finite selected moment reserve controls every chronological response price by fixed uniform insertion prices. -/

theorem shiftedResponseEnergyBudget_reserved_le_constant
    (a b : ℕ → ℝ≥0∞) (A B : ℝ≥0∞) (p N n j h : ℕ)
    (ha : ∀ k ≤ N, a k ≤ A) (hb : ∀ k ≤ N, b k ≤ B)
    (hN : n + (j + h) * p ≤ N) :
    shiftedResponseEnergyBudget a b p n j h ≤
      shiftedResponseEnergyBudget (fun _ => A) (fun _ => B) p n j h := by
  simp only [Nat.add_mul] at hN
  induction j generalizing n h with
  | zero =>
    induction h generalizing n with
    | zero => simp only [shiftedResponseEnergyBudget, le_refl]
    | succ h ih =>
      simp only [Nat.zero_mul, Nat.succ_mul] at hN
      rw [shiftedResponseEnergyBudget, shiftedResponseEnergyBudget]
      exact mul_le_mul' (hb n (by omega)) (ih (n + p) (by omega))
  | succ j ih =>
    induction h generalizing n with
    | zero =>
      simp only [Nat.zero_mul, Nat.succ_mul] at hN
      rw [shiftedResponseEnergyBudget, shiftedResponseEnergyBudget]
      exact mul_le_mul' (ha n (by omega)) (ih (n + p) 0 (by omega))
    | succ h ihh =>
      simp only [Nat.succ_mul] at hN
      rw [shiftedResponseEnergyBudget, shiftedResponseEnergyBudget]
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul' (ha n (by omega))
          (ih (n + p) (h + 1) (by simp only [Nat.succ_mul]; omega)))
        (mul_le_mul' (hb n (by omega))
          (ihh (n + p) (by simp only [Nat.succ_mul]; omega)))) zero_le

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Explicit response words have precisely the metric and source grades requested. -/

theorem responseInsertionWords_grade (j h : ℕ) (w : List Bool)
    (hw : w ∈ responseInsertionWords j h) : w.length = j + h ∧ w.count true = h := by
  have hfalse {j h : ℕ} {w : List Bool}
      (hg : w.length = j + h ∧ w.count true = h) :
      (false :: w).length = j + 1 + h ∧ (false :: w).count true = h := by
    constructor
    · simp only [List.length_cons]; omega
    · simpa using hg.2
  have htrue {j h : ℕ} {w : List Bool}
      (hg : w.length = j + h ∧ w.count true = h) :
      (true :: w).length = j + (h + 1) ∧ (true :: w).count true = h + 1 := by
    constructor
    · simp only [List.length_cons]; omega
    · simpa using hg.2
  induction j generalizing h w with
  | zero =>
    induction h generalizing w with
    | zero =>
      have hz : w = [] := by simpa [responseInsertionWords] using hw
      subst w
      simp
    | succ h ih =>
      rw [responseInsertionWords, List.mem_map] at hw
      obtain ⟨w, hw, rfl⟩ := hw
      exact htrue (ih w hw)
  | succ j ih =>
    induction h generalizing w with
    | zero =>
      rw [responseInsertionWords, List.mem_map] at hw
      obtain ⟨w, hw, rfl⟩ := hw
      exact hfalse (ih 0 w hw)
    | succ h ihh =>
      rw [responseInsertionWords, List.mem_append, List.mem_map, List.mem_map] at hw
      rcases hw with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
      · exact hfalse (ih (h + 1) w hw)
      · exact htrue (ihh w hw)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! The signed drift, diffusion, and coupling atoms retain their image price under real scaling. -/

variable {X N : Type*} [MeasurableSpace X]

theorem pairing_spacetime_readout_const_mul (μ : Measure X) (G : N → X → ℝ) (P : X → ℝ)
    (hi : ∀ n, Integrable (G n) μ)
    (hs : Summable (fun n => ∫ t, ‖G n t‖ ∂μ)) (hP : Integrable P μ)
    (he : (∑' n, ∫ t, G n t ∂μ) = ∫ t, P t ∂μ) (c : ℝ) :
    (∀ n, Integrable (fun t => c * G n t) μ) ∧
    Summable (fun n => ∫ t, ‖c * G n t‖ ∂μ) ∧
    Integrable (fun t => c * P t) μ ∧
    (∑' n, ∫ t, c * G n t ∂μ) = ∫ t, c * P t ∂μ := by
  refine ⟨fun n => (hi n).const_mul c, ?_, hP.const_mul c, ?_⟩
  · apply (hs.mul_left ‖c‖).congr
    intro n
    simp_rw [norm_mul]
    exact (integral_const_mul ‖c‖ (fun t => ‖G n t‖)).symm
  · simp_rw [integral_const_mul]
    rw [tsum_mul_left, he]

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Every cutoff derivative correction is integrable for the actual periodic L2 weak fields. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem compact_weakCorrection_integrable (ν : ℝ) (φ du : Vec 2 → E)
    (flux F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (k : Fin 2)
    (hφ : MemLp φ 2 (volume.restrict AVenhance.unitCube))
    (hdu : MemLp du 2 (volume.restrict AVenhance.unitCube))
    (hflux : MemLp (fun x => flux x k) 2 (volume.restrict AVenhance.unitCube))
    (hF : MemLp (fun x => F x k) 2 (volume.restrict AVenhance.unitCube))
    (hφp : AVenhance.IsZ2Periodic φ) (hdup : AVenhance.IsZ2Periodic du)
    (hflp : AVenhance.IsZ2Periodic flux) (hFp : AVenhance.IsZ2Periodic F)
    (χ : Vec 2 → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ) :
    Integrable (fun x => (ν * inner ℝ (du x) (φ x) +
      inner ℝ (flux x k + F x k) (φ x)) * χ x) volume := by
  have hid := fun (f : Vec 2 → E) (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
      (hfp : AVenhance.IsZ2Periodic f) =>
    periodic_compact_coefficient_pairing_integrable f φ hf hφ hfp hφp
      (fun _ => ContinuousLinearMap.id ℝ E) continuous_const 1 (by norm_num)
      (fun _ => ContinuousLinearMap.norm_id_le) χ hχ hcχ
  have hiu : Integrable (fun x => inner ℝ (du x) (φ x) * χ x) volume := by
    simpa only [ContinuousLinearMap.id_apply] using hid du hdu hdup
  have hp : AVenhance.IsZ2Periodic (fun x => flux x k + F x k) := by
    intro n x
    change flux (x + AVenhance.latticeShift n) k + F (x + AVenhance.latticeShift n) k = _
    rw [hflp n x, hFp n x]
  have hif : Integrable (fun x => inner ℝ (flux x k + F x k) (φ x) * χ x) volume := by
    simpa only [ContinuousLinearMap.id_apply, Pi.add_apply] using hid _ (hflux.add hF) hp
  apply ((hiu.const_mul ν).add hif).congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.add_apply]
  ring

end AVRegularity.CycleJointProofs
end
end
