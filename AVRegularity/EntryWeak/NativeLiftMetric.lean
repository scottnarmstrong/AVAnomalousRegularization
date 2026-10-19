-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.BoxJoint
public import AVRegularity.CycleEvolution.TimeEnergy
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.StrainPhysical.Context
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Set.Finite.List

section
section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Finite resource maxima are bounded without unfolding the resource function. -/

theorem finiteNatMenu_entry_le_sum (f : ℕ → ℕ) (R h : ℕ) (hh : h ≤ R) :
    f h ≤ ∑ j : Fin (R + 1), f j.val := by
  let j : Fin (R + 1) := ⟨h, by omega⟩
  have hs : f j.val ≤ ∑ k : Fin (R + 1), f k.val :=
    Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin (R + 1) => f k.val)
      (fun k _ => Nat.zero_le (f k.val)) (Finset.mem_univ j)
  exact hs

/-! A finite sum fixes one common predecessor constant before actual lift data are chosen. -/

def finitePriorRankBudget (r : ℕ) (C : Fin r → ℝ) : ℝ := 1 + ∑ p, C p

theorem finitePriorRankBudget_one_le (r : ℕ) (C : Fin r → ℝ)
    (hC : ∀ p, 0 ≤ C p) : 1 ≤ finitePriorRankBudget r C :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun p _ => hC p))

theorem priorRankBudget_le_common (r : ℕ) (C : Fin r → ℝ)
    (hC : ∀ p, 0 ≤ C p) (p : Fin r) : C p ≤ finitePriorRankBudget r C := by
  have h := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ) => hC q)
    (Finset.mem_univ p)
  exact h.trans (le_add_of_nonneg_left (by exact zero_le_one))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! A finite word menu has one numerical budget before every parameter point. -/

theorem finite_word_uniform_budget_exists (d N : ℕ) (R : List (Fin d) → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w, w.length ≤ N → R w ≤ B := by
  let S := (List.finite_length_le (Fin d) N).toFinset
  let B := ∑ w ∈ S, max 0 (R w)
  have hB : 0 ≤ B := Finset.sum_nonneg fun w _ => le_max_left _ _
  refine ⟨B, hB, ?_⟩
  intro w hw
  have hm : w ∈ S := by simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hw
  exact (le_max_right 0 (R w)).trans
    (Finset.single_le_sum (fun p _ => le_max_left 0 (R p)) hm)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Scalar Young inequalities for the molecular higher energy estimate. -/

theorem higherEnergy_arithmetic (E H Q D T S B U W F : ℝ)
    (hD : (3 / 4) * H ≤ D) (hT : |T| ≤ B * W * U) (hS : |S| ≤ F * U)
    (hU : U ^ 2 = E) (hW : W ^ 2 = H) (hF : F ^ 2 = Q) :
    2 * (-D - T + S) + H ≤ (1 + 4 * B ^ 2) * E + Q := by
  have hy := sq_nonneg (W / 2 - 2 * B * U)
  have hz := sq_nonneg (F - U)
  have hn := neg_le_abs T
  have hp := le_abs_self S
  nlinarith

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Exact positive-order jets of the identity map. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem identity_iteratedFDeriv_eq_zero (n : ℕ) (hn : 2 ≤ n) (x : E) :
    iteratedFDeriv ℝ n (fun y : E => y) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  change iteratedFDeriv ℝ (2 + k) (id : E → E) x = 0
  rw [show 2 + k = (k + 1) + 1 by omega, iteratedFDeriv_succ_eq_comp_right]
  simp only [fderiv_id]
  rw [iteratedFDeriv_const_of_ne (by omega : k + 1 ≠ 0)]
  exact (continuousMultilinearCurryRightEquiv' ℝ (k + 1) E E).symm.map_zero

theorem identity_positive_derivative_norm_le (n : ℕ) (hn : 1 ≤ n) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y : E => y) x‖ ≤ 1 := by
  by_cases h : n = 1
  · subst n
    change ‖iteratedFDeriv ℝ 1 (id : E → E) x‖ ≤ 1
    rw [norm_iteratedFDeriv_one, fderiv_id]
    exact ContinuousLinearMap.norm_id_le
  · rw [identity_iteratedFDeriv_eq_zero n (by omega) x, norm_zero]
    norm_num

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Ordered product-rule terms for independent-parameter inverse differentiation. -/

variable {I : Type*}

/-- Differentiating a metric-gradient term either differentiates the metric or the inverse. -/
def independentWordNext (i : I) (p : List I × List I) : List (List I × List I) :=
  [(i :: p.1, p.2), (p.1, i :: p.2)]

/-- The nonempty metric words in an inverse derivative equation, with multiplicity. -/
def independentWordForcing : List I → List (List I × List I)
  | [] => []
  | i :: w => ([i], w) :: (independentWordForcing w).flatMap (independentWordNext i)

theorem independentWordForcing_lengths (w : List I) (p : List I × List I)
    (hp : p ∈ independentWordForcing w) :
    0 < p.1.length ∧ p.1.length + p.2.length = w.length ∧ p.2.length < w.length := by
  induction w generalizing p with
  | nil => simp [independentWordForcing] at hp
  | cons i w ih =>
    simp only [independentWordForcing, List.mem_cons, List.mem_flatMap] at hp
    rcases hp with rfl | ⟨q, hq, hp⟩
    · simp [Nat.add_comm]
    · obtain ⟨hpos, hsum, hlt⟩ := ih q hq
      simp only [independentWordNext, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp only [List.length_cons] <;> omega

/-- Exact product-rule expansion, keeping repeated terms rather than suppressing multiplicity. -/
theorem independentWordForcing_cons_sum {E : Type*} [AddCommMonoid E]
    (i : I) (w : List I) (B : List I → List I → E) :
    ((independentWordForcing (i :: w)).map (fun p => B p.1 p.2)).sum =
      B [i] w + ((independentWordForcing w).map
        (fun p => B (i :: p.1) p.2 + B p.1 (i :: p.2))).sum := by
  simp only [independentWordForcing, List.map_cons, List.sum_cons]
  congr 1
  induction independentWordForcing w with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append,
      independentWordNext, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [ih]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Positive derivative composition estimates do not require bounded chart values. -/

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDeriv_sub_constant (f : E → F)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (hn : 1 ≤ n) (a : F) (x : E) :
    iteratedFDeriv ℝ n (fun y => f y - a) x = iteratedFDeriv ℝ n f x := by
  change iteratedFDeriv ℝ n (f - fun _ => a) x = _
  rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by simp)) contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega : n ≠ 0)]
  simp only [Pi.zero_apply, sub_zero]

theorem positive_order_composition_norm_le (g : F → G) (f : E → F)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (hn : 1 ≤ n) (x : E) (C D : ℝ) (hC₀ : 0 ≤ C)
    (hC : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * D ^ n := by
  let g₀ := fun y => g y - g (f x)
  have hg₀ : ContDiff ℝ (⊤ : ℕ∞) g₀ := hg.sub contDiff_const
  have hC' : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g₀ (f x)‖ ≤ C := by
    intro i hi
    by_cases hz : i = 0
    · subst i
      simpa [g₀] using hC₀
    · rw [iteratedFDeriv_sub_constant g hg i (by omega) (g (f x))]
      exact hC i (by omega) hi
  have h := norm_iteratedFDeriv_comp_le hg₀ hf (by simp) x hC' hD
  have he : g₀ ∘ f = fun y => (g ∘ f) y - g (f x) := rfl
  rw [he, iteratedFDeriv_sub_constant (g ∘ f) (hg.comp hf) n hn] at h
  exact h

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Canonical coordinate words for the two-index real derivatives. -/

def realParameterCanonicalWord (p : ℕ × ℕ) : Fin (p.1 + p.2) → Fin 2 → ℝ :=
  Fin.append (fun _ : Fin p.1 => Pi.single 0 1) (fun _ : Fin p.2 => Pi.single 1 1)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open scoped ContDiff
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Genuine ordered real parameter jets, evaluated in a Banach space. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realParameterWordJet (f : Vec 2 → E) (n : ℕ)
    (w : Fin n → Vec 2) (Y : Vec 2) : E := iteratedFDeriv ℝ n f Y w

theorem realParameterWordJet_derivative_cons (f : Vec 2 → E) (n : ℕ)
    (w : Fin n → Vec 2) (v Y : Vec 2) :
    (fderiv ℝ (iteratedFDeriv ℝ n f) Y).flipMultilinear w v =
      realParameterWordJet f (n + 1) (Fin.cons v w) Y := by
  change fderiv ℝ (iteratedFDeriv ℝ n f) Y v w =
    iteratedFDeriv ℝ (n + 1) f Y (Fin.cons v w)
  rw [iteratedFDeriv_succ_apply_left]
  simp only [Fin.cons_zero, Fin.tail_cons]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Pure real dimensional bookkeeping for the actual weak physical mean flux. -/

theorem weakFlux_dimensional_count (e ρ κ : ℝ) (he : 0 < e) (hρ : 0 < ρ)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ((e ^ 2 / κ)⁻¹ * (e / ρ) ^ n * ρ) * ρ ^ (d - 1) =
      κ * e ^ (n - 2) * ρ ^ ((d : ℝ) - (n : ℝ)) := by
  have hen : e ^ n = e ^ (n - 2) * e ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hρd : ρ ^ d = ρ * ρ ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [inv_div, div_pow, Real.rpow_sub hρ, Real.rpow_natCast, Real.rpow_natCast]
  field_simp
  rw [hen, hρd]
  ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Separate readout continuity and a measurable carrier produce joint time/fast measurability. -/

theorem carrier_joint_readout_measurable {U : Type*} [TopologicalSpace U]
    (f : U → Vec 2 → ℝ) (hc : ∀ z, Continuous (fun u => f u z))
    (hf : ∀ u, Continuous (f u)) (u : ℝ → U) (hu : StronglyMeasurable u) :
    Measurable (fun X : ℝ × Vec 2 => f (u X.1) X.2) := by
  let g := fun z : Vec 2 => fun t : ℝ => f (u t) z
  have hm (z : Vec 2) : Measurable (g z) := ((hc z).comp_stronglyMeasurable hu).measurable
  have hg (t : ℝ) : Continuous (fun z => g z t) := hf (u t)
  have hh : Measurable (Function.uncurry g) :=
    measurable_uncurry_of_continuous_of_measurable hg hm
  exact hh.comp measurable_swap

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Coordinate derivatives on any finite independent real parameter space. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteCoordinateDerivative (n : ℕ) (g : Fin n → E) : Vec n →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (g i)).comp (ContinuousLinearMap.proj i)

theorem finiteCoordinateDerivative_apply (n : ℕ) (g : Fin n → E) (Y : Vec n) :
    finiteCoordinateDerivative n g Y = ∑ i, Y i • g i := by
  simp [finiteCoordinateDerivative]

def finiteHeadEquiv (n : ℕ) : Vec (n + 1) ≃L[ℝ] ℝ × Vec n :=
  (show Vec (n + 1) ≃ₗ[ℝ] ℝ × Vec n from
    { toFun := fun Y => (Y 0, Fin.tail Y)
      invFun := fun X => Fin.cons X.1 X.2
      left_inv := fun Y => by ext i; refine Fin.cases (by simp) (fun j => rfl) i
      right_inv := fun X => by simp
      map_add' := fun Y Z => rfl
      map_smul' := fun r Y => rfl }).toContinuousLinearEquiv

theorem finiteHeadEquiv_apply (n : ℕ) (Y : Vec (n + 1)) :
    finiteHeadEquiv n Y = (Y 0, Fin.tail Y) := rfl

theorem finiteHeadEquiv_symm_apply (n : ℕ) (X : ℝ × Vec n) :
    (finiteHeadEquiv n).symm X = Fin.cons X.1 X.2 := rfl

theorem finiteCoordinateDerivative_continuous {S : Type*} [TopologicalSpace S]
    (n : ℕ) (g : Fin n → S → E) (hg : ∀ i, Continuous (g i)) :
    Continuous (fun X => finiteCoordinateDerivative n (fun i => g i X)) := by
  unfold finiteCoordinateDerivative
  apply continuous_finsetSum
  intro i _
  exact ((ContinuousLinearMap.compL ℝ (Vec n) ℝ E).flip
    (ContinuousLinearMap.proj i)).continuous.comp
      (((ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous).comp
        (hg i))

theorem finiteCoordinateDerivative_head (n : ℕ) (g : Fin (n + 1) → E) :
    ((ContinuousLinearMap.toSpanSingleton ℝ (g 0)).coprod
      (finiteCoordinateDerivative n (fun i => g i.succ))).comp
        (finiteHeadEquiv n).toContinuousLinearMap = finiteCoordinateDerivative (n + 1) g := by
  ext Y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearEquiv.coe_coe, finiteHeadEquiv_apply,
    ContinuousLinearMap.toSpanSingleton_apply, finiteCoordinateDerivative_apply,
    Fin.sum_univ_succ, Fin.tail]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization Set
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Finite first and second real derivatives give uniform Taylor control. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_parameter_lipschitz (f : Vec 2 → E) (hf : ContDiff ℝ 1 f)
    (C : ℝ) (hC : ∀ Y, ‖fderiv ℝ f Y‖ ≤ C) (X Y : Vec 2) :
    ‖f Y - f X‖ ≤ C * ‖Y - X‖ := by
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun Z _ => (hf.differentiable (by norm_num)) Z) (fun Z _ => hC Z)
    (mem_univ X) (mem_univ Y)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! A finite flat positive-jet budget is stable under composition. -/

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem finite_positive_jet_composition_bound (g : F → G) (f : E → F)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (x : E) (B : ℝ) (hB : 1 ≤ B)
    (hG : ∀ i, 1 ≤ i → i ≤ K → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ B)
    (hF : ∀ i, 1 ≤ i → i ≤ K → ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ K.factorial * B ^ (K + 1) := by
  have hb₀ : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans hB
  have h := positive_order_composition_norm_le g f hg hf n hn x B B hb₀
    (fun i hi hin => hG i hi (hin.trans hnK))
    (fun i hi hin => (hF i hi (hin.trans hnK)).trans (le_self_pow₀ hB (by omega)))
  refine h.trans ?_
  calc
    (n.factorial : ℝ) * B * B ^ n = n.factorial * B ^ (n + 1) := by rw [pow_succ]; ring
    _ ≤ K.factorial * B ^ (K + 1) := mul_le_mul
      (by exact_mod_cast Nat.factorial_le hnK)
      (pow_le_pow_right₀ hB (by omega)) (by positivity) (by positivity)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Real parameter word jets use only their finite derivative reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_realParameterWordJet_hasFDerivAt (f : Vec 2 → E) (n : ℕ)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (w : Fin n → Vec 2) (Y : Vec 2) :
    HasFDerivAt (realParameterWordJet f n w)
      ((fderiv ℝ (iteratedFDeriv ℝ n f) Y).flipMultilinear w) Y := by
  have hd : ContDiff ℝ 1 (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + n ≤ n + 1 by omega))
  exact (hd.differentiable (by norm_num) Y).hasFDerivAt.continuousMultilinear_apply_const w

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! A normalized direction embeds into the existing planar parameter API by a contracting map. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentDirectionPlane (w : P) : Vec 2 →L[ℝ] P :=
  (ContinuousLinearMap.toSpanSingleton ℝ w).comp (ContinuousLinearMap.proj (0 : Fin 2))

theorem independentDirectionPlane_apply (w : P) (X : Vec 2) :
    independentDirectionPlane w X = X 0 • w := rfl

theorem independentDirectionPlane_norm_le (w : P) : ‖independentDirectionPlane w‖ ≤ ‖w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w)
  intro X
  rw [independentDirectionPlane_apply, norm_smul]
  exact (mul_le_mul_of_nonneg_right (norm_le_pi_norm X 0) (norm_nonneg w)).trans_eq (mul_comm _ _)

theorem independentDirectionPlane_basis_smul (w : P) (h : ℝ) :
    independentDirectionPlane w (h • basisVec 0) = h • w := by
  change (h * basisVec 0 0) • w = _
  simp only [basisVec, Pi.single_eq_same, mul_one]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Positive jets of a continuous linear map cost only its operator norm. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem linear_positive_derivative_norm_le (L : E →L[ℝ] F) (n : ℕ) (hn : 1 ≤ n) (x : E) :
    ‖iteratedFDeriv ℝ n L x‖ ≤ ‖L‖ := by
  have hh := L.norm_iteratedFDeriv_comp_left
    ((contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (id : E → E)).contDiffAt)
    (n := n) (by simp) (x := x)
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (identity_positive_derivative_norm_le n hn x) (norm_nonneg L)).trans_eq (mul_one _))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Small-transport absorption also retains regular divergence forcing. -/

theorem smallTransportFluxEnergy_arithmetic (E H Q R D T S J B U W F V : ℝ)
    (hD : (3 / 4) * H ≤ D) (hT : |T| ≤ B * W * U)
    (hS : |S| ≤ F * U) (hJ : |J| ≤ V * W)
    (hU : U ^ 2 = E) (hW : W ^ 2 = H) (hF : F ^ 2 = Q) (hV : V ^ 2 = R)
    (hU0 : 0 ≤ U) (hW0 : 0 ≤ W) (hUW : U ≤ W) (hB : B ≤ 1 / 8) :
    2 * (-D - T + S - J) + H / 2 ≤ 4 * (Q + R) := by
  have hWU : W * U ≤ W ^ 2 := by
    nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hUW)]
  have hTW : |T| ≤ H / 8 := by
    have hb := mul_le_mul_of_nonneg_right hB (mul_nonneg hW0 hU0)
    nlinarith
  have hSW : 2 * S ≤ H / 4 + 4 * Q := by
    have hy := sq_nonneg (U / 2 - 2 * F)
    have hp := le_abs_self S
    have hEH : E ≤ H := by nlinarith
    nlinarith
  have hJW : -2 * J ≤ H / 4 + 4 * R := by
    have hy := sq_nonneg (W / 2 - 2 * V)
    have hp := neg_le_abs J
    nlinarith
  have ht := neg_le_abs T
  have hH : 0 ≤ H := by nlinarith [sq_nonneg W]
  linarith

/-! Lower tested orders retain the birth excess after normalization at a coarser scale. -/

theorem weak_birth_ratio_count (b e : ℝ) (he : 0 < e) (n d : ℕ)
    (hn : 2 ≤ n) (hd : 2 ≤ d) :
    b ^ (n - 2) * e ^ ((d : ℝ) - (n : ℝ)) = e ^ (d - 2) * (b / e) ^ (n - 2) := by
  have hen : e ^ n = e ^ (n - 2) * e ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hed : e ^ d = e ^ (d - 2) * e ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [Real.rpow_sub he, Real.rpow_natCast, Real.rpow_natCast, div_pow]
  field_simp
  rw [hen, hed]
  ring

theorem weak_birth_dimensional_le (b e : ℝ) (hb : 0 ≤ b) (he : 0 < e)
    (hbe : b ≤ e) (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    b ^ (n - 2) * e ^ ((d : ℝ) - (n : ℝ)) ≤ e ^ (d - 2) := by
  rw [weak_birth_ratio_count b e he n d hn hd]
  have hr : 0 ≤ b / e := div_nonneg hb he.le
  have hr1 : b / e ≤ 1 := (div_le_one he).mpr hbe
  have hp : (b / e) ^ (n - 2) ≤ 1 := pow_le_one₀ hr hr1
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (pow_nonneg he.le _)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Piola lowering changes the coarse dimensional power exactly once per lost derivative. -/

theorem weak_piola_lowering_dimensional_count (E : ℝ) (hE : 0 < E)
    (n d r : ℕ) (hd : r + 1 ≤ d) :
    E ^ ((d : ℝ) - (n : ℝ)) * E⁻¹ ^ (d - 1 - r) =
      E ^ (((r + 1 : ℕ) : ℝ) - (n : ℝ)) := by
  have hp : E⁻¹ ^ (d - 1 - r) = E ^ (-((d - 1 - r : ℕ) : ℝ)) := by
    rw [Real.rpow_neg hE.le, Real.rpow_natCast, inv_pow]
  rw [hp, ← Real.rpow_add hE]
  congr 1
  rw [Nat.cast_sub (by omega : r ≤ d - 1), Nat.cast_sub (by omega : 1 ≤ d)]
  push_cast
  ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.EntryWeakProofs

/-! Genuine continuous coordinate line derivatives give a Fréchet derivative in every finite dimension. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteContinuousPartials_hasFDerivAt (n : ℕ) (f : Vec n → E)
    (g : Fin n → Vec n → E)
    (hd : ∀ i Y, HasDerivAt (fun h : ℝ => f (Y + h • basisVec i)) (g i Y) 0)
    (hg : ∀ i, Continuous (g i)) (Y : Vec n) :
    HasFDerivAt f (finiteCoordinateDerivative n (fun i => g i Y)) Y := by
  induction n with
  | zero =>
    have he : f = fun _ => f 0 := by
      funext X
      exact congrArg f (Subsingleton.elim X 0)
    rw [he]
    simpa [finiteCoordinateDerivative] using hasFDerivAt_const (f 0) Y
  | succ n ih =>
    let e := finiteHeadEquiv n
    let F : ℝ → Vec n → E := fun a Z => f (e.symm (a, Z))
    let d₀ : ℝ → Vec n → ℝ →L[ℝ] E := fun a Z =>
      ContinuousLinearMap.toSpanSingleton ℝ (g 0 (e.symm (a, Z)))
    let d₁ : ℝ → Vec n → Vec n →L[ℝ] E := fun a Z =>
      finiteCoordinateDerivative n (fun i => g i.succ (e.symm (a, Z)))
    have h₀ (a : ℝ) (Z : Vec n) : HasFDerivAt (fun x => F x Z) (d₀ a Z) a := by
      apply HasDerivAt.hasFDerivAt
      rw [hasDerivAt_iff_tendsto_slope_zero]
      have he (h : ℝ) : e.symm (a + h, Z) = e.symm (a, Z) + h • basisVec 0 := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [e, finiteHeadEquiv_symm_apply, basisVec]
      simpa only [F, he, zero_add, zero_smul, add_zero] using
        (hd 0 (e.symm (a, Z))).tendsto_slope_zero
    have h₁ (a : ℝ) (Z : Vec n) : HasFDerivAt (F a) (d₁ a Z) Z := by
      change HasFDerivAt (F a)
        (finiteCoordinateDerivative n (fun i => g i.succ (e.symm (a, Z)))) Z
      apply ih (F a) (fun i W => g i.succ (e.symm (a, W)))
      · intro i W
        have he (h : ℝ) : e.symm (a, W + h • basisVec i) =
            e.symm (a, W) + h • basisVec i.succ := by
          ext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simp [e, finiteHeadEquiv_symm_apply, basisVec]
          · by_cases hk : k = i <;> simp [e, finiteHeadEquiv_symm_apply, basisVec,
              hk, Fin.succ_inj]
        simpa only [F, he] using hd i.succ (e.symm (a, W))
      · intro i
        exact (hg i.succ).comp (e.symm.continuous.comp (continuous_const.prodMk continuous_id))
    have hc₀ : Continuous (fun X : ℝ × Vec n => d₀ X.1 X.2) :=
      (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous.comp
        ((hg 0).comp e.symm.continuous)
    have hc₁ : Continuous (fun X : ℝ × Vec n => d₁ X.1 X.2) :=
      finiteCoordinateDerivative_continuous n (fun i X => g i.succ (e.symm X))
        (fun i => (hg i.succ).comp e.symm.continuous)
    have hh := (hasStrictFDerivAt_uncurry_coprod (u := e Y) (f := F) (f₁ := d₀) (f₂ := d₁)
      (Filter.Eventually.of_forall fun X => h₀ X.1 X.2)
      (Filter.Eventually.of_forall fun X => h₁ X.1 X.2)
      hc₀.continuousAt hc₁.continuousAt).hasFDerivAt
    have hh' := hh.comp Y e.hasFDerivAt
    change HasFDerivAt (fun X => f (e.symm (e X)))
      (((ContinuousLinearMap.toSpanSingleton ℝ (g 0 (e.symm (e Y)))).coprod
        (finiteCoordinateDerivative n (fun i => g i.succ (e.symm (e Y))))).comp
          e.toContinuousLinearMap) Y at hh'
    simp only [e.symm_apply_apply] at hh'
    have heq := finiteCoordinateDerivative_head n (fun i => g i Y)
    change ((ContinuousLinearMap.toSpanSingleton ℝ (g 0 Y)).coprod
      (finiteCoordinateDerivative n (fun i => g i.succ Y))).comp
        e.toContinuousLinearMap = _ at heq
    rw [heq] at hh'
    exact hh'

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Explicit finite positive-jet budgets for successive chart compositions. -/

def positiveJetCompositionBudget (K : ℕ) (B : ℝ) : ℝ := K.factorial * B ^ (K + 1)

theorem positiveJetCompositionBudget_ge_self (K : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    B ≤ positiveJetCompositionBudget K B := by
  have hK : (1 : ℝ) ≤ K.factorial := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos K)
  calc
    B ≤ B ^ (K + 1) := le_self_pow₀ hB (by omega)
    _ ≤ K.factorial * B ^ (K + 1) := le_mul_of_one_le_left (by positivity) hK

theorem positiveJetCompositionBudget_ge_one (K : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    1 ≤ positiveJetCompositionBudget K B := hB.trans (positiveJetCompositionBudget_ge_self K B hB)

/-! Joint derivative menus for the paired maps in centered chart composition. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem independent_multilinear_pair_norm_le (n : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G) :
    ‖A.prod B‖ ≤ max ‖A‖ ‖B‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound ((norm_nonneg A).trans (le_max_left _ _))
  intro w
  change max ‖A w‖ ‖B w‖ ≤ max ‖A‖ ‖B‖ * ∏ i, ‖w i‖
  have hp : 0 ≤ ∏ i, ‖w i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  exact max_le ((A.le_opNorm w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp))
    ((B.le_opNorm w).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp))

theorem independent_joint_pair_jet_bound (f : E → F) (g : E → G) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ∞) f) (hg : ContDiff ℝ (n : ℕ∞) g) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => (f y, g y)) x‖ ≤
      max ‖iteratedFDeriv ℝ n f x‖ ‖iteratedFDeriv ℝ n g x‖ := by
  rw [iteratedFDeriv_prodMk hf.contDiffAt hg.contDiffAt (le_refl _)]
  exact independent_multilinear_pair_norm_le n _ _
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Genuine mixed real parameter derivatives in canonical coordinate order. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realParameterCanonicalJet (f : Vec 2 → E) (p : ℕ × ℕ) : Vec 2 → E :=
  realParameterWordJet f (p.1 + p.2) (realParameterCanonicalWord p)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Uniform genuine slice variation upgrades separate parameter continuity to joint continuity. -/

variable {P Q : Type*} [TopologicalSpace P] [NormedAddCommGroup Q]
variable {E : Type*} [NormedAddCommGroup E]

theorem joint_continuous_of_uniform_slice_variation (f : P → Q → E)
    (hc : ∀ z, Continuous (fun Y => f Y z))
    (C : ℝ) (hb : ∀ Y z w, ‖f Y z - f Y w‖ ≤ C * ‖z - w‖) :
    Continuous (fun X : P × Q => f X.1 X.2) := by
  apply continuous_iff_continuousAt.mpr
  intro X
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hzcont : Continuous (fun Z : P × Q => C * ‖Z.2 - X.2‖) :=
    continuous_const.mul (continuous_snd.sub continuous_const).norm
  have hYcont : Continuous (fun Z : P × Q => ‖f Z.1 X.2 - f X.1 X.2‖) :=
    (((hc X.2).comp continuous_fst).sub continuous_const).norm
  have hz : Tendsto (fun Z : P × Q => C * ‖Z.2 - X.2‖) (𝓝 X) (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using hzcont.continuousAt.tendsto (x := X)
  have hY : Tendsto (fun Z : P × Q => ‖f Z.1 X.2 - f X.1 X.2‖) (𝓝 X) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using hYcont.continuousAt.tendsto (x := X)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hz.add hY) (fun _ => norm_nonneg _)
  intro Z
  calc
    ‖f Z.1 Z.2 - f X.1 X.2‖ ≤ ‖f Z.1 Z.2 - f Z.1 X.2‖ + ‖f Z.1 X.2 - f X.1 X.2‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (hb Z.1 Z.2 X.2) (le_refl _)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! A finite geometric reserve pays for each default-budget inverse step before the actual family is chosen. -/

def weakJointRecurrenceReserve (factor base rankMax rank : ℕ) : ℕ :=
  factor ^ (rankMax - rank) * (base + 1)

theorem weakJointRecurrenceReserve_base (factor base rankMax rank : ℕ)
    (hf : 1 ≤ factor) :
    base + 1 ≤ weakJointRecurrenceReserve factor base rankMax rank := by
  unfold weakJointRecurrenceReserve
  have hp : 1 ≤ factor ^ (rankMax - rank) := Nat.one_le_pow _ _ hf
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right (base + 1) hp

theorem weakJointRecurrenceReserve_predecessor (factor base rankMax rank prior : ℕ)
    (hf : 1 ≤ factor) (hr : rank ≤ rankMax) (hp : prior < rank) :
    factor * weakJointRecurrenceReserve factor base rankMax rank ≤
      weakJointRecurrenceReserve factor base rankMax prior := by
  unfold weakJointRecurrenceReserve
  have hexp : rankMax - rank + 1 ≤ rankMax - prior := by omega
  calc
    factor * (factor ^ (rankMax - rank) * (base + 1)) =
        factor ^ (rankMax - rank + 1) * (base + 1) := by
          rw [pow_succ']
          exact (Nat.mul_assoc _ _ _).symm
    _ ≤ factor ^ (rankMax - prior) * (base + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hf hexp)

theorem weakJointRecurrenceReserve_inverse_room (base degree rankMax rank prior : ℕ)
    (hr : rank ≤ rankMax) (hp : prior < rank) :
    4 * weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax rank + degree + 5 ≤
      weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax prior := by
  let R := weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax rank
  have hR : 1 ≤ R := le_trans (by omega : 1 ≤ base + 1)
    (weakJointRecurrenceReserve_base (4 * (degree + 4)) base rankMax rank (by omega))
  have hroom : 4 * R + degree + 5 ≤ (4 * (degree + 4)) * R := by
    have hd := Nat.mul_le_mul_left degree hR
    have hh := Nat.mul_le_mul_left 4 hR
    rw [Nat.mul_one] at hd hh
    rw [Nat.mul_assoc, Nat.add_mul, Nat.mul_add]
    omega
  exact hroom.trans (weakJointRecurrenceReserve_predecessor
    (4 * (degree + 4)) base rankMax rank prior (by omega) hr hp)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Finite composition retains a recorded source weight to the first power, including weight zero. -/

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem finite_weighted_jet_composition_bound (g : F → G) (f : E → F)
    (K n : ℕ) (hn : n ≤ K) (hg : ContDiff ℝ (K : ℕ∞) g)
    (hf : ContDiff ℝ (K : ℕ∞) f) (x : E) (θ C B : ℝ)
    (hθ : 0 ≤ θ) (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hG : ∀ i ≤ K, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ θ * C)
    (hF : ∀ i, 1 ≤ i → i ≤ K → ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ θ * (K.factorial * C * B ^ K) := by
  have hb : 0 ≤ B := zero_le_one.trans hB
  have hh := norm_iteratedFDeriv_comp_le hg hf (by exact_mod_cast hn) x
    (fun i hi => hG i (hi.trans hn))
    (fun i hi hiN => (hF i hi (hiN.trans hn)).trans (le_self_pow₀ hB (by omega)))
  apply hh.trans
  have hfac : (n.factorial : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_le hn
  have hpow : B ^ n ≤ B ^ K := pow_le_pow_right₀ hB hn
  calc
    _ = θ * C * ((n.factorial : ℝ) * B ^ n) := by ring
    _ ≤ θ * C * ((K.factorial : ℝ) * B ^ K) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hfac hpow (pow_nonneg hb _)
        (by positivity)) (mul_nonneg hθ hC)
    _ = _ := by ring

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Continuous genuine coordinate-word jets produce finite full parameter regularity. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteCoordinateDerivative_contDiff {S : Type*}
    [NormedAddCommGroup S] [NormedSpace ℝ S] {r : ℕ∞}
    (d : ℕ) (g : Fin d → S → E) (hg : ∀ i, ContDiff ℝ r (g i)) :
    ContDiff ℝ r (fun X => finiteCoordinateDerivative d (fun i => g i X)) := by
  unfold finiteCoordinateDerivative
  apply ContDiff.sum
  intro i _
  have hid : ContDiff ℝ r (fun _ : S => ContinuousLinearMap.id ℝ ℝ) := contDiff_const
  have hp : ContDiff ℝ r (fun _ : S => (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) :=
    contDiff_const
  exact (hid.smulRight (hg i)).clm_comp hp

theorem finite_coordinate_word_family_contDiff (d K : ℕ)
    (J : List (Fin d) → Vec d → E)
    (hc : ∀ w, w.length ≤ K → Continuous (J w))
    (hd : ∀ w, w.length < K → ∀ i Y,
      HasDerivAt (fun h : ℝ => J w (Y + h • basisVec i)) (J (i :: w) Y) 0)
    (w : List (Fin d)) (r : ℕ) (hr : w.length + r ≤ K) :
    ContDiff ℝ (r : ℕ∞) (J w) := by
  induction r generalizing w with
  | zero => exact contDiff_zero.mpr (hc w (by omega))
  | succ r ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun Y => finiteCoordinateDerivative d (fun i => J (i :: w) Y), ?_, ?_⟩
    · apply finiteCoordinateDerivative_contDiff
      intro i
      exact ih (i :: w) (by simp only [List.length_cons]; omega)
    · exact finiteContinuousPartials_hasFDerivAt d (J w) (fun i => J (i :: w))
        (hd w (by omega)) (fun i => hc (i :: w) (by simp only [List.length_cons]; omega))
end

/-! Actual derivatives of the two slices identify a differentiable joint field. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_fderiv_apply_of_slice_derivatives (d : ℕ) (f : Vec d → Vec 2 → E)
    (X : Vec d × Vec 2) (A : Vec d →L[ℝ] E) (B : Vec 2 →L[ℝ] E)
    (hj : DifferentiableAt ℝ (Function.uncurry f) X)
    (ha : HasFDerivAt (fun Y => f Y X.2) A X.1)
    (hb : HasFDerivAt (f X.1) B X.2) (V : Vec d × Vec 2) :
    fderiv ℝ (Function.uncurry f) X V = A V.1 + B V.2 := by
  have hj' : HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) X) X := hj.hasFDerivAt
  have hp : HasFDerivAt (fun Y => f Y X.2)
      ((fderiv ℝ (Function.uncurry f) X).comp (ContinuousLinearMap.inl ℝ (Vec d) (Vec 2))) X.1 := by
    have h := hj'.comp X.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) X.1 X.2)
    simpa only [Function.comp_def, Function.uncurry] using h
  have hq : HasFDerivAt (f X.1)
      ((fderiv ℝ (Function.uncurry f) X).comp (ContinuousLinearMap.inr ℝ (Vec d) (Vec 2))) X.2 := by
    have h := hj'.comp X.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) X.1 X.2)
    simpa only [Function.comp_def, Function.uncurry] using h
  have h₁ := hp.unique ha
  have h₂ := hq.unique hb
  calc
    fderiv ℝ (Function.uncurry f) X V =
        fderiv ℝ (Function.uncurry f) X ((V.1, 0) + (0, V.2)) := by simp only [Prod.mk_add_mk, add_zero, zero_add]
    _ = fderiv ℝ (Function.uncurry f) X (V.1, 0) +
        fderiv ℝ (Function.uncurry f) X (0, V.2) := map_add _ _ _
    _ = A V.1 + B V.2 := by
      change ((fderiv ℝ (Function.uncurry f) X).comp (ContinuousLinearMap.inl ℝ (Vec d) (Vec 2))) V.1 +
        ((fderiv ℝ (Function.uncurry f) X).comp (ContinuousLinearMap.inr ℝ (Vec d) (Vec 2))) V.2 = _
      rw [h₁, h₂]
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Higher slow derivatives of coordinate jets retain the full derivative bound. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realParameterCanonicalWord_norm_le_one (p : ℕ × ℕ)
    (i : Fin (p.1 + p.2)) : ‖realParameterCanonicalWord p i‖ ≤ 1 := by
  unfold realParameterCanonicalWord
  exact Fin.addCases (fun _ => by simp [Pi.norm_single])
    (fun _ => by simp [Pi.norm_single]) i

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Physical monomial tests scale to the literal slow-variable monomials. -/

theorem scaled_word_monomial (m : ℕ) (α : DerivativeWord2 m)
    (ρ : ℝ) (hρ : ρ ≠ 0) (y X : Vec 2) :
    (∏ j : Fin m, (ρ • X - y) (α j)) =
      ρ ^ m * Providers.GenSem.mono (ρ⁻¹ • y) α X := by
  have he (i : Fin 2) : (ρ • X - y) i = ρ * (X - ρ⁻¹ • y) i := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hρ, one_mul]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Providers.GenSem.mono]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! The finite rank reserve supplies the exact metric, forcing, and Taylor orders of each inverse step. -/

/-- Every inverse allocation retains a nonzero joint regularity order. -/
theorem weakJointRecurrenceReserve_positive (base degree rankMax rank : ℕ) :
    1 ≤ weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax rank := by
  exact (show 1 ≤ base + 1 by omega).trans
    (weakJointRecurrenceReserve_base (4 * (degree + 4)) base rankMax rank (by omega))

/-- A fixed metric reserve, chosen before the family, covers every rank. -/
theorem weakJointRecurrenceReserve_metric_room (base degree rankMax rank : ℕ) :
    weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax rank + 2 ≤
      weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax 0 + 2 := by
  by_cases h : rank = 0
  · subst rank
    exact le_rfl
  · by_cases hr : rank ≤ rankMax
    · have hp := weakJointRecurrenceReserve_predecessor (4 * (degree + 4))
        base rankMax rank 0 (by omega) hr (by omega)
      have hf : 1 ≤ 4 * (degree + 4) := by omega
      have hm := Nat.mul_le_mul_right
        (weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax rank) hf
      rw [Nat.one_mul] at hm
      exact Nat.add_le_add_right (hm.trans hp) 2
    · unfold weakJointRecurrenceReserve
      rw [Nat.sub_eq_zero_of_le (by omega : rankMax ≤ rank), pow_zero, Nat.one_mul]
      exact Nat.add_le_add_right
        (weakJointRecurrenceReserve_base (4 * (degree + 4)) base rankMax 0 (by omega)) 2

/-- Ordered mean corrections also pay their left-application order before constructing the mean source. -/
theorem weakJointRecurrenceReserve_composition_source_room (base degree rankMax rank prior : ℕ)
    (hr : rank ≤ rankMax) (hp : prior < rank) :
    let H := weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax rank
    let P := weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax prior
    4 * H + 2 * degree + 7 ≤ P := by
  let H := weakJointRecurrenceReserve (4 * (degree + 4)) base rankMax rank
  have hH : 1 ≤ H := weakJointRecurrenceReserve_positive base degree rankMax rank
  have hmul := Nat.mul_le_mul_left (4 * degree + 12) hH
  rw [Nat.mul_one] at hmul
  have hroom : 4 * H + 2 * degree + 7 ≤ (4 * (degree + 4)) * H := by
    have he : (4 * (degree + 4)) * H = 4 * H + (4 * degree + 12) * H := by ring
    rw [he]
    omega
  exact hroom.trans (weakJointRecurrenceReserve_predecessor
    (4 * (degree + 4)) base rankMax rank prior (by omega) hr hp)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! History-independent Hilbert energy bounds for bounded scalar production. -/

theorem strongTime_normSq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {u du : ℝ → H} (h : StrongTimeRegularity a b u du) :
    StrongTimeRegularity a b (fun t => ‖u t‖ ^ 2)
      (fun t => 2 * inner ℝ (u t) (du t)) := by
  refine ⟨h.norm_sq_ac, ?_⟩
  filter_upwards [h.derivative] with t ht
  exact ht.norm_sq

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Joint smoothness follows from actual continuous word derivatives and fast derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coordinate_word_joint_contDiff (d N K : ℕ)
    (J : List (Fin d) → Vec d → Vec 2 → E)
    (hc : ∀ w, w.length ≤ N → ∀ n, n ≤ K →
      Continuous (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n (J w X.1) X.2))
    (hf : ∀ w, w.length ≤ N → ∀ Y, ContDiff ℝ (K : ℕ∞) (J w Y))
    (hd : ∀ w, w.length < N → ∀ n, n ≤ K → ∀ i Y z,
      HasDerivAt (fun h : ℝ => iteratedFDeriv ℝ n (J w (Y + h • basisVec i)) z)
        (iteratedFDeriv ℝ n (J (i :: w) Y) z) 0)
    (w : List (Fin d)) (r n : ℕ) (hN : w.length + r ≤ N) (hK : n + r ≤ K) :
    ContDiff ℝ (r : ℕ∞) (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n (J w X.1) X.2) := by
  induction r generalizing w n with
  | zero => exact contDiff_zero.mpr (hc w (by omega) n (by omega))
  | succ r ih =>
    let A := fun Y z => finiteCoordinateDerivative d
      (fun i => iteratedFDeriv ℝ n (J (i :: w) Y) z)
    let C := fun q : Vec 2 [×n + 1]→L[ℝ] E => q.curryLeft
    have hC : @IsBoundedLinearMap ℝ (Vec 2 [×n + 1]→L[ℝ] E)
        (Vec 2 →L[ℝ] Vec 2 [×n]→L[ℝ] E)
        (inferInstance : NontriviallyNormedField ℝ).toNormedField.toField.toSemifield.toSemiring
        (inferInstance : NormedAddCommGroup (Vec 2 [×n + 1]→L[ℝ] E)).toSeminormedAddCommGroup
        (inferInstance : NormedSpace ℝ (Vec 2 [×n + 1]→L[ℝ] E)).toModule
        (inferInstance : NormedAddCommGroup (Vec 2 →L[ℝ] Vec 2 [×n]→L[ℝ] E)).toSeminormedAddCommGroup
        (inferInstance : NormedSpace ℝ (Vec 2 →L[ℝ] Vec 2 [×n]→L[ℝ] E)).toModule C := by
      refine { map_add := ?_, map_smul := ?_, bound := ⟨1, zero_lt_one, ?_⟩ }
      · intro x y; rfl
      · intro c x; rfl
      · intro q
        change ‖q.curryLeft‖ ≤ 1 * ‖q‖
        rw [ContinuousMultilinearMap.curryLeft_norm, one_mul]
    let B := fun Y z => C (iteratedFDeriv ℝ (n + 1) (J w Y) z)
    have ha : ContDiff ℝ (r : ℕ∞) (fun X : Vec d × Vec 2 => A X.1 X.2) := by
      apply finiteCoordinateDerivative_contDiff
      intro i
      exact ih (i :: w) n (by simp only [List.length_cons]; omega) (by omega)
    have hb : ContDiff ℝ (r : ℕ∞) (fun X : Vec d × Vec 2 => B X.1 X.2) := by
      have hh := hC.contDiff.comp
        (ih w (n + 1) (by omega) (by omega))
      exact hh
    have hpa Y z : HasFDerivAt (fun Y => iteratedFDeriv ℝ n (J w Y) z) (A Y z) Y :=
      finiteContinuousPartials_hasFDerivAt d (fun Y => iteratedFDeriv ℝ n (J w Y) z)
        (fun i Y => iteratedFDeriv ℝ n (J (i :: w) Y) z)
        (fun i Y => hd w (by omega) n (by omega) i Y z)
        (fun i => (hc (i :: w) (by simp only [List.length_cons]; omega) n (by omega)).comp
          (continuous_id.prodMk continuous_const)) Y
    have hpb Y z : HasFDerivAt (iteratedFDeriv ℝ n (J w Y)) (B Y z) z := by
      have hreg : ContDiff ℝ 1 (iteratedFDeriv ℝ n (J w Y)) :=
        (hf w (by omega) Y).iteratedFDeriv_right
          (by exact_mod_cast (show 1 + n ≤ K by omega))
      have hh := hreg.differentiable (by norm_num) z
      have he : fderiv ℝ (iteratedFDeriv ℝ n (J w Y)) z = B Y z := by
        rw [fderiv_iteratedFDeriv]
        rfl
      rw [← he]
      exact hh.hasFDerivAt
    have hj X : HasFDerivAt
        (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n (J w X.1) X.2)
        ((A X.1 X.2).coprod (B X.1 X.2)) X :=
      (hasStrictFDerivAt_uncurry_coprod (u := X)
        (f := fun Y z => iteratedFDeriv ℝ n (J w Y) z) (f₁ := A) (f₂ := B)
        (Filter.Eventually.of_forall fun X => hpa X.1 X.2)
        (Filter.Eventually.of_forall fun X => hpb X.1 X.2)
        ha.continuous.continuousAt hb.continuous.continuousAt).hasFDerivAt
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun X => (A X.1 X.2).coprod (B X.1 X.2), ?_, hj⟩
    have he : (fun X : Vec d × Vec 2 => (A X.1 X.2).coprod (B X.1 X.2)) =
        fun X => (A X.1 X.2).comp (ContinuousLinearMap.fst ℝ (Vec d) (Vec 2)) +
          (B X.1 X.2).comp (ContinuousLinearMap.snd ℝ (Vec d) (Vec 2)) := by
      funext X
      apply ContinuousLinearMap.ext
      intro V
      simp only [ContinuousLinearMap.coprod_apply, add_apply,
        ContinuousLinearMap.comp_apply]
      rfl
    rw [he]
    exact (ha.clm_comp contDiff_const).add (hb.clm_comp contDiff_const)

end AVRegularity.EntryWeakProofs
end
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! Renewal windows shrink along the weak block. -/

theorem renewal_window_antitone {α q : ℝ} {Λ : ℕ}
    (hα : α < 1) (hδ : 0 ≤ ocDelta α q) (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    Antitone (ocTauPP α q Λ) := by
  intro i j hij
  have he := EntryScales.epsilon_antitone hq hΛ (Nat.sub_le_sub_right hij 1)
  have hi : 0 < ocEpsilon q Λ (i - 1) := (Scales.epsilon_basic hq hΛ).1
  have hj : 0 < ocEpsilon q Λ (j - 1) := (Scales.epsilon_basic hq hΛ).1
  have hp := Real.rpow_le_rpow_of_nonpos hj he
    (show -(2 - (1 + α) + 2 * ocDelta α q) ≤ 0 by linarith)
  have hc := Nat.ceil_mono hp
  unfold ocTauPP
  apply div_le_div_of_nonneg_left (by positivity)
    ((Real.rpow_pos_of_pos hi _).trans_le (Nat.le_ceil _))
  exact_mod_cast hc

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The actual native lift metric is the Gram matrix of the coarse-flow inverse Jacobian. -/

theorem native_familyLiftData_metric {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (D : OCData) (m : ℕ) (hm : 1 ≤ m) (slot : ℤ) (ρ : ℝ)
    (edge : ConstituentEdges Dm h) (s : ℝ) (X : Vec 2) :
    (familyLiftData D m slot (nativeChain m slot) ρ edge).G s X =
      (jacMatrix (fun y => D.flowOf (m - 1) (D.cellScaleSq m * s) y (D.slotAnchor m slot))
          (ρ • X))⁻¹ *
        Matrix.transpose (jacMatrix (fun y =>
          D.flowOf (m - 1) (D.cellScaleSq m * s) y (D.slotAnchor m slot)) (ρ • X))⁻¹ := by
  change ((nativeChain m slot).recenter D (ρ • X)).famMetric D (D.cellScaleSq m * s) = _
  unfold nativeChain
  rw [StrainPhysical.recenter_native]
  simp only [zero_add]
  unfold RealChain.famMetric RealChain.famJac
  rw [StrainPhysical.geom_native D m hm slot (ρ • X)]

end AVRegularity.EntryWeakProofs
end
end
