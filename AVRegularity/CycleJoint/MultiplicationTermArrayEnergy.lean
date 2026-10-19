-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVenhance.Infra.FaaDiBruno.Composition
public import AVRegularity.Applications.TorusEnergy.With
public import AVRegularity.CycleEvolution.TimeEnergy
public import AVRegularity.CycleJoint.WeightedLocalLpBound
import AVRegularity.Weighted.JointRegularityBoxSmooth
public import AVRegularity.Definitions.CycleWords.IsGeometryCover
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.PSeries

section
section
public section
namespace AVRegularity.CycleJointProofs

/-! The incoming partial block and following full block fit inside duration two,
with the second reference time inside the preparation window. -/

theorem preparation_two_block_time_geometry (s l T : ℝ) (hT : 0 < T)
    (hlo : (l - 1 / 2) * T ≤ s) (hhi : s < (l + 1 / 2) * T) :
    s < (l + 1 / 2) * T ∧
    (l + 1 / 2) * T ≤ s + T ∧
    s + T < (l + 3 / 2) * T ∧
    (l + 3 / 2) * T ≤ s + 2 * T ∧
    (l + 1) * T ∈ Set.Icc s (s + 2 * T) ∧
    Set.Icc s ((l + 1 / 2) * T) ⊆
      Set.Icc (max s ((l - 1) * T)) (min (s + 2 * T) ((l + 1) * T)) ∧
    Set.Icc ((l + 1 / 2) * T) ((l + 3 / 2) * T) ⊆
      Set.Icc (max s (l * T)) (min (s + 2 * T) ((l + 2) * T)) := by
  have hseam : (l + 1 / 2) * T ≤ s + T := by linarith only [hlo]
  have hend : (l + 3 / 2) * T ≤ s + 2 * T := by linarith only [hlo]
  refine ⟨hhi, hseam, ?_, hend, ?_, ?_, ?_⟩
  · linarith only [hhi]
  · constructor <;> linarith only [hlo, hhi, hT]
  · intro t ht
    exact ⟨max_le ht.1 (by linarith only [ht.1, hlo, hT]),
      le_min (by linarith only [ht.2, hseam, hT]) (by linarith only [ht.2, hT])⟩
  · intro t ht
    exact ⟨max_le (hhi.le.trans ht.1) (by linarith only [ht.1, hT]),
      le_min (ht.2.trans hend) (by linarith only [ht.2, hT])⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Combining the three literal residual fluxes pays a fixed factor, independent of all family indices. -/

variable {E : Type*} [AddCommMonoid E]

theorem quadratic_energy_three_sum_le (energy : E → ℝ≥0∞)
    (ha : ∀ x y, energy (x + y) ≤ 2 * (energy x + energy y)) (x y z : E) :
    energy (x + y + z) ≤ 4 * (energy x + energy y + energy z) := by
  have hz : energy z ≤ 2 * energy z := by
    calc
      energy z = 1 * energy z := (one_mul _).symm
      _ ≤ 2 * energy z := mul_le_mul_of_nonneg_right (by norm_num) zero_le
  calc
    energy (x + y + z) ≤ 2 * (energy (x + y) + energy z) := ha _ _
    _ ≤ 2 * (2 * (energy x + energy y) + 2 * energy z) :=
      mul_le_mul_of_nonneg_left (add_le_add (ha x y) hz) zero_le
    _ = 4 * (energy x + energy y + energy z) := by ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Finite drift prices admit a positive absorption radius and an arbitrarily large reserve. -/

/-- Every finite nonnegative price can be absorbed by a finite reserve square. -/
theorem exists_scalar_square_reserve (A : ℝ) (hA : 0 ≤ A) :
    ∃ L : ℝ, 1 ≤ L ∧ A / L ^ 2 ≤ 1 / 16 := by
  let L := max 1 (4 * Real.sqrt A)
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hroot : 4 * Real.sqrt A ≤ L := le_max_right _ _
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ 4 * Real.sqrt A) hLp.le).mpr hroot
  rw [mul_pow, Real.sq_sqrt hA] at hs
  refine ⟨L, hL, (div_le_iff₀ (sq_pos_of_pos hLp)).mpr ?_⟩
  nlinarith

/-! Radius normalization preserves the explicit scale spent by native order lowering. -/

theorem radius_lowering_bound (E ρ C a : ℝ) (n r : ℕ)
    (hE : 0 < E) (hρ : 0 ≤ ρ) (hρE : ρ ≤ E) (hC : 0 ≤ C)
    (ha : E ^ (n + r) * a ≤ C) :
    ρ ^ n * a ≤ C * E⁻¹ ^ r := by
  have hp : 0 < E ^ (n + r) := pow_pos hE _
  have hb : a ≤ C / E ^ (n + r) := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using ha)
  have hr : 0 ≤ ρ / E := div_nonneg hρ hE.le
  have hr1 : ρ / E ≤ 1 := (div_le_one₀ hE).mpr hρE
  calc
    _ ≤ ρ ^ n * (C / E ^ (n + r)) := mul_le_mul_of_nonneg_left hb (pow_nonneg hρ _)
    _ = (C * E⁻¹ ^ r) * (ρ / E) ^ n := by
      rw [pow_add, div_pow, div_eq_mul_inv, mul_inv, inv_pow]
      ring
    _ ≤ (C * E⁻¹ ^ r) * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) (by positivity)
    _ = _ := mul_one _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! A strictly descending source rank can make every mass-conjugated edge arbitrarily small. -/

def rankMass {ι : Type*} (r : ι → ℕ) (L : ℝ) (v : ι) : ℝ := (L ^ r v) ^ 2

theorem rankMass_pos {ι : Type*} (r : ι → ℕ) (L : ℝ) (hL : 0 < L) (v : ι) :
    0 < rankMass r L v := sq_pos_of_pos (pow_pos hL _)

theorem rankMass_sqrt_ratio {ι : Type*} (r : ι → ℕ) (L : ℝ) (hL : 0 ≤ L) (v u : ι) :
    Real.sqrt (rankMass r L u / rankMass r L v) = L ^ r u / L ^ r v := by
  unfold rankMass
  rw [← div_pow, Real.sqrt_sq (div_nonneg (pow_nonneg hL _) (pow_nonneg hL _))]

theorem rankMass_sqrt_ratio_le_inv {ι : Type*} (r : ι → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (v u : ι) (hr : r u < r v) : Real.sqrt (rankMass r L u / rankMass r L v) ≤ 1 / L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [rankMass_sqrt_ratio r L hLp.le, div_le_div_iff₀ (pow_pos hLp _) hLp, one_mul,
    ← pow_succ]
  exact pow_le_pow_right₀ hL (Nat.succ_le_of_lt hr)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! The rank discount is chosen from fixed scalar and source constants before the family. -/

/-- The explicit discount `L = 1 + 64 C B²` (explicit, so that the rank scale is monotone in
the source strength). -/
theorem real_source_feedback_discount_explicit (C B : ℝ) (hC : 0 ≤ C) :
    1 ≤ 1 + 64 * C * B ^ 2 ∧ 32 * C * (B / (1 + 64 * C * B ^ 2)) ^ 2 ≤ 1 / 2 := by
  set L := 1 + 64 * C * B ^ 2 with hLdef
  have hx : 0 ≤ 64 * C * B ^ 2 := mul_nonneg (by linarith only [hC]) (sq_nonneg B)
  have hL : 1 ≤ L := by rw [hLdef]; linarith only [hx]
  have hLp : 0 < L := zero_lt_one.trans_le hL
  refine ⟨hL, ?_⟩
  have hs : 64 * C * B ^ 2 ≤ L ^ 2 := by
    have hsq := sq_nonneg (64 * C * B ^ 2)
    rw [hLdef]
    nlinarith only [hx, hsq]
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hLp)).mpr
  nlinarith only [hs]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The real Taylor remainder prices retain their small powers when transferred
to nonnegative extended-real energy bounds. -/

theorem residual_squared_power_factorization (B c ζ : ℝ) (hB : 0 ≤ B) (hζ : 0 ≤ ζ)
    (p : ℕ) :
    ENNReal.ofReal (B * (c * ζ ^ p) ^ 2) =
      ENNReal.ofReal (B * c ^ 2) * ENNReal.ofReal ζ ^ (2 * p) := by
  rw [mul_pow, ← pow_mul, Nat.mul_comm p 2, ← mul_assoc,
    ENNReal.ofReal_mul (mul_nonneg hB (sq_nonneg c)), ENNReal.ofReal_pow hζ]

theorem source_remainder_squared_power_factorization (c ζ : ℝ) (hζ : 0 ≤ ζ) (p : ℕ) :
    ENNReal.ofReal ((ζ ^ p * c) ^ 2) =
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal ζ ^ (2 * p) := by
  rw [mul_comm (ζ ^ p) c]
  simpa only [one_mul] using residual_squared_power_factorization 1 c ζ zero_le_one hζ p

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Finite response recursions telescope without discarding their last metric insertion. -/

variable {E : Type*} [AddCommGroup E]

theorem sum_range_zero_predecessor (f : ℕ → E) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), if j = 0 then 0 else f (j - 1)) =
      ∑ j ∈ Finset.range N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! A scalar coefficient multiplying a fixed operator preserves its jet norm majorant. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem scalar_fixed_vector_jet_norm_le (f : E → ℝ) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ) f) (v : F) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f y • v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ n f x‖ := by
  let L : ℝ →L[ℝ] F := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hL : ‖L‖ ≤ ‖v‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
    intro a
    simp only [L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul]
    exact le_of_eq (mul_comm _ _)
  exact (L.norm_iteratedFDeriv_comp_left hf.contDiffAt le_rfl).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The fixed scalar response price separates chart and slot constants from the metric and original source gains. -/

def scalarResponseGradientPrice (Kmax : ℕ) (L : ℝ) (Cw : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
    (ENNReal.ofReal (Cw n) * ENNReal.ofReal (Cw n) *
      ENNReal.ofReal (3 * Real.exp (18 * Cw n))) * 16

theorem scalarResponseGradientPrice_ne_top (Kmax : ℕ) (L : ℝ) (Cw : ℕ → ℝ) (n : ℕ) :
    scalarResponseGradientPrice Kmax L Cw n ≠ ⊤ := by
  unfold scalarResponseGradientPrice
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  · norm_num

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open AVenhance.FaaDiBruno
namespace AVRegularity.CycleJointProofs

/-! Radius powers cancel the derivative-scale loss in each finite composition partition. -/

theorem scaled_partition_product_le {n : ℕ} (c : OrderedFinpartition n)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (B C : ℕ → ℝ)
    (hB : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ρ ^ (j - 1) * B j ≤ C j) :
    ρ ^ n * (∏ i : Fin c.length, B (c.partSize i)) ≤
      ρ ^ c.length * (∏ i : Fin c.length, C (c.partSize i)) := by
  have he : (∏ i : Fin c.length, ρ ^ c.partSize i) = ρ ^ n := by
    rw [Finset.prod_pow_eq_pow_sum, Composition.composition_partSize_sum]
  rw [← he, ← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ i : Fin c.length, ρ * C (c.partSize i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (pow_nonneg hρ _) (hB _ (c.partSize_pos i) (c.partSize_le i))
      · intro i _
        have hp : c.partSize i - 1 + 1 = c.partSize i := Nat.sub_add_cancel (c.partSize_pos i)
        rw [← hp, pow_succ]
        have hh := mul_le_mul_of_nonneg_left
          (hb _ (c.partSize_pos i) (c.partSize_le i)) hρ
        simpa only [hp, mul_assoc, mul_left_comm, mul_comm] using hh
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Time and spatial derivatives of smooth spacetime tests commute. -/

section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem smoothField_directional_derivative_eq (f : X → Y)
    (hf : ContDiff ℝ 2 f) (p u d : X) :
    fderiv ℝ (fun q => fderiv ℝ f q u) p d =
      fderiv ℝ (fderiv ℝ f) p d u := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  let ev := ContinuousLinearMap.apply ℝ Y u
  have hh := ev.hasFDerivAt.comp p (hdf p).hasFDerivAt
  change fderiv ℝ (ev ∘ fderiv ℝ f) p d = _
  rw [hh.fderiv]
  rfl

theorem smoothField_directional_derivative_commute (f : X → Y)
    (hf : ContDiff ℝ 2 f) (p v w : X) :
    fderiv ℝ (fun q => fderiv ℝ f q v) p w =
      fderiv ℝ (fun q => fderiv ℝ f q w) p v := by
  rw [smoothField_directional_derivative_eq f hf p v w,
    smoothField_directional_derivative_eq f hf p w v]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num [minSmoothness])).eq w v
end

/-! A summable two-dimensional spatial majorant, independent of torus patch count. -/

def spatialLatticeWeight (k : Fin 2 → ℤ) : ℝ :=
  (1 + |(k 0 : ℝ)|) * (1 + |(k 1 : ℝ)|)

theorem spatialLatticeWeight_pos (k : Fin 2 → ℤ) : 0 < spatialLatticeWeight k := by
  unfold spatialLatticeWeight
  positivity

theorem spatialIntegerReciprocal_square_summable :
    Summable (fun n : ℤ => (1 / (1 + |(n : ℝ)|)) ^ 2) := by
  have h : Summable (fun n : ℕ => (1 / (1 + (n : ℝ))) ^ 2) := by
    have hh := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    exact hh.congr (fun n => by
      rw [Real.rpow_two, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1),
        one_div_pow, add_comm])
  apply Summable.of_nat_of_neg
  · exact h.congr (fun n => by rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)])
  · exact h.congr (fun n => by rw [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg n)])

theorem spatialLatticeReciprocal_square_summable :
    Summable (fun k : Fin 2 → ℤ => (1 / spatialLatticeWeight k) ^ 2) := by
  have h := spatialIntegerReciprocal_square_summable
  have hnorm : Summable (fun n : ℤ => ‖(1 / (1 + |(n : ℝ)|)) ^ 2‖) :=
    h.congr (fun n => by rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (1 / (1 + |(n : ℝ)|)))])
  have hh := summable_mul_of_summable_norm hnorm hnorm
  have ht := hh.comp_injective (finTwoArrowEquiv ℤ).injective
  exact ht.congr (fun k => by
    change (1 / (1 + |(k 0 : ℝ)|)) ^ 2 * (1 / (1 + |(k 1 : ℝ)|)) ^ 2 = _
    rw [← mul_pow, one_div_mul_one_div]
    rfl)

end AVRegularity.CycleJointProofs
end
end

section
public section
namespace AVRegularity.CycleJointProofs

/-! Abstract real power algebra for the preparation diffusion length. -/

theorem sqrt_product_power_div_le {e b t Cb Ct p r : ℝ}
    (he : 0 < e) (hb : 0 ≤ b) (hCt : 0 ≤ Ct) (hCb : 0 ≤ Cb)
    (hboundB : b ≤ Cb * e ^ p) (hboundT : t ≤ Ct * e ^ r) :
    Real.sqrt (b * t) / e ≤ Real.sqrt (Cb * Ct) * e ^ ((p + r) / 2 - 1) := by
  have hprod : b * t ≤ (Cb * Ct) * e ^ (p + r) := by
    calc
      b * t ≤ b * (Ct * e ^ r) := mul_le_mul_of_nonneg_left hboundT hb
      _ ≤ (Cb * e ^ p) * (Ct * e ^ r) :=
        mul_le_mul_of_nonneg_right hboundB (mul_nonneg hCt (Real.rpow_nonneg he.le _))
      _ = (Cb * Ct) * e ^ (p + r) := by
        rw [Real.rpow_add he]
        ring
  have hs := Real.sqrt_le_sqrt hprod
  rw [Real.sqrt_mul (mul_nonneg hCb hCt), Real.sqrt_eq_rpow (e ^ (p + r)),
    ← Real.rpow_mul he.le] at hs
  calc
    Real.sqrt (b * t) / e ≤
        (Real.sqrt (Cb * Ct) * e ^ ((p + r) * (1 / 2 : ℝ))) / e :=
      div_le_div_of_nonneg_right hs he.le
    _ = Real.sqrt (Cb * Ct) * e ^ ((p + r) / 2 - 1) := by
      have hexp : (p + r) * (1 / 2 : ℝ) = (p + r) / 2 := by ring
      rw [Real.rpow_sub_one he.ne', mul_div_assoc, hexp]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Elementary pointwise budgets for a static weight with its gradient as flux. -/

/-- A bounded drift and relative gradient give a finite defect rate in two coordinates. -/
theorem staticWeight_drift_budget {A M W : ℝ} (hM : 0 ≤ M)
    (hW : 0 ≤ W) (v d : Fin 2 → ℝ)
    (hv : ∀ k, |v k| ≤ M) (hd : ∀ k, |d k| ≤ A * W) :
    (∑ k : Fin 2, v k * d k) ≤ (4 * A ^ 2 + 4 * M ^ 2 + 1) * W := by
  have hh (k : Fin 2) : v k * d k ≤ M * (A * W) := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul (hv k) (hd k) (abs_nonneg _) hM
  have hr : 2 * M * A ≤ 4 * A ^ 2 + 4 * M ^ 2 + 1 := by
    nlinarith only [sq_nonneg (A - M), sq_nonneg A, sq_nonneg M]
  have hs := mul_le_mul_of_nonneg_right hr hW
  simp only [Fin.sum_univ_two]
  nlinarith only [hh 0, hh 1, hs]

/-- The relative gradient and identical weight flux share one finite quadratic rate. -/
theorem staticWeight_gradient_flux_budget {A M W : ℝ} (hA : 0 ≤ A)
    (hW : 0 < W) (d : Fin 2 → ℝ) (hd : ∀ k, |d k| ≤ A * W) :
    (∑ k : Fin 2, d k ^ 2) / W ^ 2 + (∑ k : Fin 2, d k ^ 2) / W ^ 2 ≤
      4 * A ^ 2 + 4 * M ^ 2 + 1 := by
  have hh (k : Fin 2) : d k ^ 2 ≤ (A * W) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (d k)) (mul_nonneg hA hW.le)).mpr (hd k)
  rw [← add_div, div_le_iff₀ (sq_pos_of_pos hW)]
  simp only [Fin.sum_univ_two]
  have hp := mul_nonneg (sq_nonneg M) (sq_nonneg W)
  nlinarith only [hh 0, hh 1, hp, sq_nonneg W]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Set Filter
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! A uniformly Lipschitz strongly continuous action preserves continuous moving traces. -/

variable {X : Type*} [NormedAddCommGroup X]

theorem strongAction_trace_continuousOn (S : Set ℝ) (T : ℝ → X → X) (C : ℝ)
    (hT : ∀ x, ContinuousOn (fun t => T t x) S)
    (hbound : ∀ t ∈ S, ∀ x y, ‖T t x - T t y‖ ≤ C * ‖x - y‖)
    (u : ℝ → X) (hu : ContinuousOn u S) :
    ContinuousOn (fun t => T t (u t)) S := by
  intro t ht
  have hU : Tendsto (fun r => C * ‖u r - u t‖) (𝓝[S] t) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_iff_norm_sub_tendsto_zero.mp (hu t ht)).const_mul C
  have hfixed := tendsto_iff_norm_sub_tendsto_zero.mp (hT (u t) t ht)
  have hlim : Tendsto (fun r => C * ‖u r - u t‖ + ‖T r (u t) - T t (u t)‖)
      (𝓝[S] t) (𝓝 0) := by simpa only [zero_add] using hU.add hfixed
  have hb : ∀ᶠ r in 𝓝[S] t, ‖T r (u r) - T t (u t)‖ ≤
      C * ‖u r - u t‖ + ‖T r (u t) - T t (u t)‖ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    calc
      _ ≤ ‖T r (u r) - T r (u t)‖ + ‖T r (u t) - T t (u t)‖ := by
        simpa only [dist_eq_norm] using dist_triangle (T r (u r)) (T r (u t)) (T t (u t))
      _ ≤ _ := add_le_add (hbound r hr (u r) (u t)) le_rfl
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Filter.Eventually.of_forall fun r => norm_nonneg _) hb hlim)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace AVRegularity.CycleJointProofs

/-! A summable spatial price and an actual L2 time majorant close the full time series. -/

variable {X J E : Type*} [MeasurableSpace X] [Countable J]
  [NormedAddCommGroup E] [CompleteSpace E]

theorem memLp_tsum_of_summable_majorant (μ : Measure X) (g : J → X → E)
    (hg : ∀ j, AEStronglyMeasurable (g j) μ) (a : J → ℝ)
    (hs : Summable a) (M : X → ℝ) (hM : MemLp M 2 μ)
    (hb : ∀ᵐ t ∂μ, ∀ j, ‖g j t‖ ≤ a j * ‖M t‖) :
    MemLp (fun t => ∑' j, g j t) 2 μ := by
  have hn : ∀ᵐ t ∂μ, Summable (fun j => ‖g j t‖) := by
    filter_upwards [hb] with t ht
    exact (hs.mul_right ‖M t‖).of_nonneg_of_le (fun j => norm_nonneg _) ht
  have ht : ∀ᵐ t ∂μ, Tendsto (fun s : Finset J => ∑ j ∈ s, g j t) atTop (𝓝 (∑' j, g j t)) :=
    hn.mono (fun t h => (Summable.of_norm h).hasSum)
  have hm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun s : Finset J => s.aestronglyMeasurable_fun_sum (fun j _ => hg j)) ht
  apply hM.of_le_mul (c := ∑' j, a j) hm
  filter_upwards [hb, hn] with t ht hnt
  apply (norm_tsum_le_tsum_norm hnt).trans
  have hh := hnt.tsum_le_tsum ht (hs.mul_right ‖M t‖)
  simpa only [tsum_mul_right] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! A summable spatial price passes actual integrated weak equations through their image series. -/

section
variable {X J E : Type*} [MeasurableSpace X] [Countable J]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [Countable J] [NormedSpace ℝ E] [CompleteSpace E] in
theorem summable_integral_norm_of_majorant (μ : Measure X) (F : J → X → E)
    (hF : ∀ j, Integrable (F j) μ) (p : J → ℝ) (hp : Summable p)
    (M : X → ℝ) (hM : Integrable M μ)
    (hb : ∀ᵐ x ∂μ, ∀ j, ‖F j x‖ ≤ p j * ‖M x‖) :
    Summable (fun j => ∫ x, ‖F j x‖ ∂μ) := by
  have hbound (j : J) : (∫ x, ‖F j x‖ ∂μ) ≤ p j * ∫ x, ‖M x‖ ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hF j).norm (hM.norm.const_mul (p j)) (hb.mono (fun _ hx => hx j))
  exact (hp.mul_right (∫ x, ‖M x‖ ∂μ)).of_nonneg_of_le
    (fun j => integral_nonneg (fun _ => norm_nonneg _)) hbound
end

/-! A weight bounded on the actual support has its stated L2 cost. -/

section
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [MeasurableSpace X] in
theorem supported_weight_norm_le (q : X → ℝ) (f : X → E) (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ x, f x ≠ 0 → |q x| ≤ C) (x : X) : ‖q x • f x‖ ≤ C * ‖f x‖ := by
  by_cases hx : f x = 0
  · have hn := mul_nonneg hC (norm_nonneg (f x))
    simpa only [hx, smul_zero, norm_zero] using hn
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hq x hx) (norm_nonneg _)

theorem supported_weight_memLp (μ : Measure X) (q : X → ℝ) (f : X → E)
    (hf : MemLp f 2 μ) (hm : AEStronglyMeasurable q μ)
    (C : ℝ) (hC : 0 ≤ C) (hq : ∀ x, f x ≠ 0 → |q x| ≤ C) :
    MemLp (fun x => q x • f x) 2 μ := by
  apply hf.of_le_mul (c := C) (hm.smul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (supported_weight_norm_le q f C hC hq)
end

/-! Almost-everywhere superposition gives a genuine linear map of time-integrable curves. -/

section
variable {X E : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

def timeLpCurveLinearMap (μ : Measure ℝ) (w : X → ℝ → E)
    (hw : ∀ x, MemLp (w x) 2 μ)
    (hadd : ∀ x y, w (x + y) =ᵐ[μ] fun t => w x t + w y t)
    (hsmul : ∀ (c : ℝ) x, w (c • x) =ᵐ[μ] fun t => c • w x t) : X →ₗ[ℝ] Lp E 2 μ where
  toFun x := (hw x).toLp (w x)
  map_add' x y := (MemLp.toLp_congr (hw (x + y)) ((hw x).add (hw y)) (hadd x y)).trans
    (MemLp.toLp_add (hw x) (hw y))
  map_smul' c x := (MemLp.toLp_congr (hw (c • x)) ((hw x).const_smul c) (hsmul c x)).trans
    (MemLp.toLp_const_smul c (hw x))
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Function addition in time is assembled before specializing to native Sobolev carriers. -/

theorem timeMemLp_add {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {p : ℝ≥0∞}
    (f g : X → E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (fun t => f t + g t) p μ :=
  hf.add hg

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Finite order lowering can be summed either by output order or by original order. -/

variable {E : Type*} [AddCommMonoid E]

theorem triangular_jet_order_sum (D : ℕ) (f : ℕ → ℕ → E) :
    (∑ r ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc (r + 1) D, f r d) =
      ∑ d ∈ Finset.Icc 2 D, ∑ r ∈ Finset.Icc 1 (d - 1), f r d := by
  classical
  have hleft : ∀ r ∈ Finset.Icc 1 D,
      (∑ d ∈ Finset.Icc (r + 1) D, f r d) =
        ∑ d ∈ Finset.Icc 2 D, if r < d then f r d else 0 := by
    intro r hr
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext d
      simp only [Finset.mem_filter, Finset.mem_Icc] at *
      omega
    · intro d hd
      rfl
  rw [Finset.sum_congr rfl hleft]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext r
    simp only [Finset.mem_filter, Finset.mem_Icc] at *
    omega
  · intro r hr
    rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Original-data normalization of the two-block physical error. The retained
higher-moment price is derived from actual endpoint stability and error. -/

open scoped ENNReal

def twoBlockOriginalEnergyPrice
    (Creturn Cpost Cseam Cfirst εlow εhigh εpost : ℝ≥0∞) : ℝ≥0∞ :=
  Creturn * 2 * (Cpost * Cseam * εlow + εpost * (2 * (Cfirst + εhigh)))

theorem twoBlock_original_energy_budget
    (Ein Efirst EretHigh EpreLow EpreHigh Epost Ephysical : ℝ≥0∞)
    (Creturn Cpost Cseam Cfirst εlow εhigh εpost : ℝ≥0∞)
    (hfirst : Efirst ≤ Cfirst * Ein)
    (hlow : EpreLow ≤ εlow * Ein)
    (hhigh : EpreHigh ≤ εhigh * Ein)
    (hretained : EretHigh ≤ 2 * (Efirst + EpreHigh))
    (hpost : Epost ≤ εpost * EretHigh)
    (hphysical : Ephysical ≤ Creturn * (2 * (Cpost * (Cseam * EpreLow) + Epost))) :
    Ephysical ≤ twoBlockOriginalEnergyPrice Creturn Cpost Cseam Cfirst εlow εhigh εpost * Ein := by
  have hret : EretHigh ≤ (2 * (Cfirst + εhigh)) * Ein := by
    calc
      _ ≤ 2 * (Efirst + EpreHigh) := hretained
      _ ≤ 2 * (Cfirst * Ein + εhigh * Ein) :=
        mul_le_mul_right (add_le_add hfirst hhigh) 2
      _ = _ := by ring
  calc
    _ ≤ Creturn * (2 * (Cpost * (Cseam * EpreLow) + Epost)) := hphysical
    _ ≤ Creturn * (2 * (Cpost * (Cseam * (εlow * Ein)) +
        εpost * ((2 * (Cfirst + εhigh)) * Ein))) := by
      apply mul_le_mul_right _ Creturn
      apply mul_le_mul_right _ 2
      exact add_le_add
        (mul_le_mul_right (mul_le_mul_right hlow Cseam) Cpost)
        (hpost.trans (mul_le_mul_right hret εpost))
    _ = _ := by unfold twoBlockOriginalEnergyPrice; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Exact nonnegative integration over the disjoint half-open lattice cells. -/

theorem cellAt_iUnion : (⋃ n : Fin 2 → ℤ, Applications.cellAt n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨fun i => ⌊x i⌋, Applications.mem_cellAt_floor x⟩

theorem lintegral_cell_tiling (f : Vec 2 → ℝ≥0∞) :
    ∫⁻ x, f x ∂volume = ∑' n : Fin 2 → ℤ, ∫⁻ x in Applications.cellAt n, f x ∂volume := by
  simpa only [cellAt_iUnion, Measure.restrict_univ] using
    lintegral_iUnion Applications.measurableSet_cellAt
      (fun _ _ h => Applications.cellAt_disjoint h) f

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Ambient strong time regularity lifts to a closed Hilbert subspace. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem closedSubspace_strong_time (S : ClosedSubmodule ℝ H) {a b : ℝ}
    (z dz : ℝ → S)
    (h : CycleEvolution.StrongTimeRegularity a b (fun t => (z t : H))
      (fun t => (dz t : H))) :
    CycleEvolution.StrongTimeRegularity a b z dz := by
  have hp := h.map S.toSubmodule.orthogonalProjectionOnto
  have hz : (fun t => S.toSubmodule.orthogonalProjectionOnto (z t : H)) = z := by
    funext t
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (z t)
  have hd : (fun t => S.toSubmodule.orthogonalProjectionOnto (dz t : H)) = dz := by
    funext t
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (dz t)
  rw [hz, hd] at hp
  exact hp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A native derivative word splits uniquely into its first coordinate and its remaining word. -/

variable {E : Type*} [AddCommMonoid E]

theorem derivativeWord_cons_sum (n : ℕ) (f : DerivativeWord2 (n + 1) → E) :
    (∑ A : DerivativeWord2 (n + 1), f A) =
      ∑ a : Fin 2, ∑ A : DerivativeWord2 n, f (Fin.cons a A) := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2))]
  rw [Fintype.sum_prod_type]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A coordinate derivative spends one spatial jet, without increasing its operator norm. -/

theorem directional_derivative_jet_norm_le (f : Vec 2 → ℝ) (n : ℕ)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) (x : Vec 2) (i : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (basisVec i)) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  let L : (Vec 2 →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (basisVec i)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    have hb : ‖basisVec i‖ = 1 := by simp [basisVec, Pi.norm_single]
    simpa only [L, ContinuousLinearMap.apply_apply, hb, mul_one, one_mul] using
      T.le_opNorm (basisVec i)
  have hd : ContDiff ℝ (n : ℕ) (fderiv ℝ f) :=
    hf.fderiv_right (by exact_mod_cast le_refl (n + 1))
  change ‖iteratedFDeriv ℝ n (L ∘ fderiv ℝ f) x‖ ≤ _
  apply (L.norm_iteratedFDeriv_comp_left hd.contDiffAt le_rfl).trans
  rw [← norm_iteratedFDeriv_fderiv]
  exact mul_le_of_le_one_left (norm_nonneg _) hL

/-! Exact coordinate derivative scaling for a scalar native transition factor. -/

theorem directional_derivative_rescaling (f : Vec 2 → ℝ)
    (hf : Differentiable ℝ f) (c E : ℝ) (x : Vec 2) (v : Vec 2) :
    fderiv ℝ (fun y => c * f (E • y)) x v = c * E * fderiv ℝ f (E • x) v := by
  have hs : HasFDerivAt (fun y : Vec 2 => E • y)
      (E • ContinuousLinearMap.id ℝ (Vec 2)) x :=
    (E • ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt
  have hh := ((hf (E • x)).hasFDerivAt.comp x hs).const_smul c
  have hh' : HasFDerivAt (fun y : Vec 2 => c * f (E • y))
      (c • (fderiv ℝ f (E • x)).comp (E • ContinuousLinearMap.id ℝ (Vec 2))) x := hh
  rw [hh'.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite dissipation yields finite total error energy before the actual source feedback is absorbed. -/

theorem finite_gradient_source_feedback_absorb
    (E G I F C b : ℝ≥0∞)
    (hG : G ≠ ⊤) (hI : I ≠ ⊤) (hF : F ≠ ⊤) (hC : C ≠ ⊤) (hb : b ≠ ⊤)
    (h : E ≤ C * (I + 32 * (F + b * G))) (hGE : G ≤ E)
    (hsmall : C * (32 * b) ≤ (1 / 2 : ℝ≥0∞)) :
    E ≤ 2 * C * (I + 32 * F) := by
  have h32 : (32 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hbudget : I + 32 * F ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hI, ENNReal.mul_ne_top h32 hF⟩
  have hright : C * (I + 32 * (F + b * G)) ≠ ⊤ :=
    ENNReal.mul_ne_top hC (ENNReal.add_ne_top.mpr ⟨hI,
      ENNReal.mul_ne_top h32 (ENNReal.add_ne_top.mpr ⟨hF, ENNReal.mul_ne_top hb hG⟩)⟩)
  have hE := ne_top_of_le_ne_top hright h
  have hstep : E ≤ C * ((I + 32 * F) + (32 * b) * E) := by
    calc
      E ≤ C * (I + 32 * (F + b * G)) := h
      _ ≤ C * (I + 32 * (F + b * E)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left hGE zero_le)) zero_le)) zero_le
      _ = C * ((I + 32 * F) + (32 * b) * E) := by ring
  exact finite_source_feedback_absorb E (I + 32 * F) C (32 * b) hE hbudget hC
    (ENNReal.mul_ne_top h32 hb) hstep hsmall

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! The finite native order sum preserves positive jet majorants. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_jet_finset_sum_norm_le {J : Type*} (s : Finset J)
    (f : J → E → F) (n : ℕ) (hf : ∀ j ∈ s, ContDiff ℝ (n : ℕ) (f j)) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => ∑ j ∈ s, f j y) x‖ ≤
      ∑ j ∈ s, ‖iteratedFDeriv ℝ n (f j) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun j hj => (hf j hj).contDiffAt)]
  exact norm_sum_le _ _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Component quadratic addition estimates preserve the original finite masses after time integration. -/

theorem finite_mass_time_quadratic_addition {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (c : ι → ℝ≥0∞) (J G H : ι → X → ℝ≥0∞)
    (hJ : ∀ i, AEMeasurable (J i) μ) (hG : ∀ i, AEMeasurable (G i) μ)
    (hH : ∀ i, AEMeasurable (H i) μ)
    (hb : ∀ i, (∫⁻ t, J i t ∂μ) ≤ 2 *
      ((∫⁻ t, G i t ∂μ) + ∫⁻ t, H i t ∂μ)) :
    (∫⁻ t, ∑ i, c i * J i t ∂μ) ≤ 2 *
      ((∫⁻ t, ∑ i, c i * G i t ∂μ) + ∫⁻ t, ∑ i, c i * H i t ∂μ) := by
  classical
  have hGM : AEMeasurable (fun t => ∑ i, c i * G i t) μ :=
    Finset.aemeasurable_fun_sum _ (fun i _ => (hG i).const_mul _)
  have he : (fun t => ∑ i, c i * (G i t + H i t)) =
      (fun t => (∑ i, c i * G i t) + ∑ i, c i * H i t) := by
    funext t
    simp only [mul_add, Finset.sum_add_distrib]
  have h := finite_mass_time_integral_budget μ c J (fun i t => G i t + H i t) 2
    hJ (fun i => (hG i).add (hH i)) (fun i => by
      rw [lintegral_add_left' (hG i) _]
      exact hb i)
  rw [he, lintegral_add_left' hGM _] at h
  exact h

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! The absolute spacetime price survives finite source and direction assembly. -/

variable {X N J : Type*} [MeasurableSpace X]

theorem finite_pairing_time_summable (μ : Measure X) (S : Finset J)
    (F : J → N → X → ℝ) (hi : ∀ j ∈ S, ∀ n, Integrable (F j n) μ)
    (hs : ∀ j ∈ S, Summable (fun n => ∫ t, ‖F j n t‖ ∂μ)) :
    Summable (fun n => ∫ t, ‖∑ j ∈ S, F j n t‖ ∂μ) := by
  have hmajor : Summable (fun n => ∑ j ∈ S, ∫ t, ‖F j n t‖ ∂μ) :=
    summable_sum hs
  apply hmajor.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
  intro n
  rw [← integral_finsetSum S (fun j hj => (hi j hj n).norm)]
  exact integral_mono
    (integrable_finsetSum S (fun j hj => hi j hj n)).norm
    (integrable_finsetSum S (fun j hj => (hi j hj n).norm))
    (fun t => norm_sum_le S (fun j => F j n t))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Linear response blocks preserve the order of all metric and source insertions. -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def finiteResponseOperator (R D S : Module.End ℝ E) : ℕ → ℕ → Module.End ℝ E
  | 0, 0 => 1
  | j + 1, 0 => R * D * finiteResponseOperator R D S j 0
  | 0, h + 1 => R * S * finiteResponseOperator R D S 0 h
  | j + 1, h + 1 => R * D * finiteResponseOperator R D S j (h + 1) +
      R * S * finiteResponseOperator R D S (j + 1) h
termination_by j h => j + h

theorem finiteResponseOperator_apply (R D S : Module.End ℝ E) (f : E) (j h : ℕ) :
    finiteResponseOperator R D S j h f = finiteResponse R D S f j h := by
  induction j generalizing h with
  | zero =>
    induction h with
    | zero => simp only [finiteResponseOperator, finiteResponse, Module.End.one_apply]
    | succ h ih => simp only [finiteResponseOperator, finiteResponse, Module.End.mul_apply, ih]
  | succ j ih =>
    induction h with
    | zero => simp only [finiteResponseOperator, finiteResponse, Module.End.mul_apply, ih]
    | succ h ihh =>
      simp only [finiteResponseOperator, finiteResponse, LinearMap.add_apply,
        Module.End.mul_apply, ih, ihh]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Spacetime readouts of individual atoms assemble the complete image equation. -/

variable {X N J : Type*} [MeasurableSpace X] [Countable N]

theorem finite_weakEquation_integral_readout (μ : Measure X) (S : Finset J)
    (u f : N → ℝ) (hu : Summable u) (hf : Summable f) (F : J → N → X → ℝ)
    (hi : ∀ j ∈ S, ∀ n, Integrable (F j n) μ)
    (hs : ∀ j ∈ S, Summable (fun n => ∫ t, ‖F j n t‖ ∂μ))
    (he : ∀ n, u n - f n = ∫ t, ∑ j ∈ S, F j n t ∂μ)
    (G : J → X → ℝ) (hG : ∀ j ∈ S, Integrable (G j) μ)
    (hreadout : ∀ j ∈ S, (∑' n, ∫ t, F j n t ∂μ) = ∫ t, G j t ∂μ) :
    Integrable (fun t => ∑ j ∈ S, G j t) μ ∧
      (∑' n, u n) - (∑' n, f n) = ∫ t, ∑ j ∈ S, G j t ∂μ := by
  have hsj : ∀ j ∈ S, Summable (fun n => ∫ t, F j n t ∂μ) := by
    intro j hj
    exact (hasSum_integral_of_summable_integral_norm (hi j hj) (hs j hj)).summable
  refine ⟨integrable_finsetSum S hG, ?_⟩
  calc
    _ = ∑' n, (u n - f n) := (hu.tsum_sub hf).symm
    _ = ∑' n, ∫ t, ∑ j ∈ S, F j n t ∂μ := tsum_congr he
    _ = ∑' n, ∑ j ∈ S, ∫ t, F j n t ∂μ :=
      tsum_congr (fun n => integral_finsetSum S (fun j hj => hi j hj n))
    _ = ∑ j ∈ S, ∑' n, ∫ t, F j n t ∂μ := Summable.tsum_finsetSum hsj
    _ = ∑ j ∈ S, ∫ t, G j t ∂μ := Finset.sum_congr rfl hreadout
    _ = _ := (integral_finsetSum S hG).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Real spatial matrices act on Hilbert-valued flux components and preserve bounded-coefficient L2. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hilbertMatrixAction (M : Matrix (Fin 2) (Fin 2) ℝ) (G : Fin 2 → E) : Fin 2 → E :=
  fun k => ∑ j : Fin 2, M k j • G j

theorem hilbertMatrixAction_inner (M : Matrix (Fin 2) (Fin 2) ℝ)
    (G : Fin 2 → E) (e : E) (k : Fin 2) :
    inner ℝ e (hilbertMatrixAction M G k) =
      M.mulVec (fun j => inner ℝ e (G j)) k := by
  simp only [hilbertMatrixAction, inner_sum, real_inner_smul_right, Matrix.mulVec, dotProduct]

theorem hilbertMatrixAction_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (M : X → Matrix (Fin 2) (Fin 2) ℝ) (G : Fin 2 → X → E)
    (hM : ∀ k j, AEStronglyMeasurable (fun x => M x k j) μ)
    (C : ℝ) (hb : ∀ x k j, |M x k j| ≤ C) (hG : ∀ j, MemLp (G j) 2 μ) (k : Fin 2) :
    MemLp (fun x => hilbertMatrixAction (M x) (fun j => G j x) k) 2 μ := by
  apply memLp_finsetSum
  intro j _
  have hc := memLp_top_of_bound (hM k j) C
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x k j))
  exact hc.smul (hG j)

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Measurable slow Taylor evaluation permits moving centres, phases and increments. -/

variable {T : Type*} [MeasurableSpace T]

theorem moving_slow_taylor_measurable (lo K : ℕ)
    (f : T → Vec 2 → Vec 2 → ℝ)
    (hm : ∀ X z, Measurable (fun t => f t X z))
    (hf : ∀ t, ContDiff ℝ (K : ℕ) (Function.uncurry (f t)))
    (X z v : T → Vec 2) (hX : Measurable X) (hz : Measurable z) (hv : Measurable v) :
    Measurable (fun t => taylorSlow lo K (fun Y => f t Y (z t)) (X t) (v t)) := by
  unfold taylorSlow
  apply Finset.measurable_fun_sum
  intro r hr
  apply Measurable.const_mul
  have hrK := (Finset.mem_Icc.mp hr).2
  let H := fun t (w : Vec 2 × (Vec 2 × Vec 2)) =>
    iteratedFDeriv ℝ r (fun Y => f t Y w.2.1) w.1 (fun _ => w.2.2)
  have hcont (t : T) : Continuous (H t) := by
    have hf0 : ContDiff ℝ (0 + r : ℕ) (Function.uncurry (f t)) :=
      (hf t).of_le (by exact_mod_cast (show 0 + r ≤ K by omega))
    have hj := (Weighted.joint_partialIteratedFDeriv_left_contDiff 0 r
      (Function.uncurry (f t)) hf0).continuous
    exact continuous_eval.comp
      ((hj.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_pi (fun _ => continuous_snd.comp continuous_snd)))
  have htime (w : Vec 2 × (Vec 2 × Vec 2)) : Measurable (fun t => H t w) := by
    exact Weighted.parameter_iteratedFDeriv_apply_measurable
      (fun t Y => f t Y w.2.1) (fun Y => hm Y w.2.1) K r
      (fun t => (hf t).comp (contDiff_id.prodMk contDiff_const)) hrK w.1 (fun _ => w.2.2)
  have hjoint : Measurable (fun p : T × (Vec 2 × (Vec 2 × Vec 2)) => H p.1 p.2) :=
    (measurable_uncurry_of_continuous_of_measurable hcont htime).comp measurable_swap
  exact hjoint.comp (measurable_id.prodMk (hX.prodMk (hz.prodMk hv)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The exact array identity retains spatial overlap before taking coefficient bounds. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem multiplicationTerm_sumSq_eq_array {K j : ℕ} (hj : j ≤ K)
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) (m : PositionMask j) (x : Vec 2) :
    (∑ w : DerivativeWord2 j, ‖multiplicationTerm hj C D m w x‖ ^ 2) =
      ∑ v : DerivativeWord2 (maskRightLength j m),
        ‖coefficientDerivativeArray C (maskLeftLength j m) x
          (D ⟨⟨maskRightLength j m,
            Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩ x)‖ ^ 2 := by
  let f := fun p : DerivativeWord2 (maskLeftLength j m) × DerivativeWord2 (maskRightLength j m) =>
    ‖orderedCoefficientDerivative C (maskLeftLength j m) p.1 x
      (D ⟨⟨maskRightLength j m,
        Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, p.2⟩ x)‖ ^ 2
  have he : (∑ w : DerivativeWord2 j, ‖multiplicationTerm hj C D m w x‖ ^ 2) = ∑ p, f p :=
    Fintype.sum_equiv (maskWordEquiv 2 j m) _ _ (fun _ => rfl)
  rw [he, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  exact (coefficientDerivativeArray_normSq C (maskLeftLength j m) x
    (D ⟨⟨maskRightLength j m,
      Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩ x)).symm

end AVRegularity.CycleJointProofs
end
end
