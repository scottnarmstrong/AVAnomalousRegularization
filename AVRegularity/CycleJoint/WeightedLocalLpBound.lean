-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Sobolev.WeakDerivatives
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleJointProofs

/-! A compact spacetime spatial slice transfers transport to the smooth test derivative. -/

theorem compact_weak_divfree_transport {u : Vec 2 → ℝ} {g : Fin 2 → Vec 2 → ℝ}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hw : ∀ i, HasWeakPartialDerivOn univ i u (g i))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ (fun y => v y i) x (basisVec i) = 0)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hs : HasCompactSupport q) :
    (∫ x, q x * ∑ i : Fin 2, v x i * g i x) =
      -(∫ x, (∑ i : Fin 2, v x i * fderiv ℝ q x (basisVec i)) * u x) := by
  let c := fun i x => q x * v x i
  have hc i : ContDiff ℝ (⊤ : ℕ∞) (c i) := hq.mul (contDiff_pi.mp hv i)
  have hsc i : HasCompactSupport (c i) := hs.mul_right
  have hcm i : MemLp (c i) 2 volume := (hc i).continuous.memLp_of_hasCompactSupport (hsc i)
  have hdc i : MemLp (fun x => fderiv ℝ (c i) x (basisVec i)) 2 volume :=
    ((hc i).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.memLp_of_hasCompactSupport ((hsc i).fderiv_apply ℝ (basisVec i))
  have hleft i : Integrable (fun x => g i x * c i x) volume :=
    memLp_one_iff_integrable.mp ((hg i).fun_mul (hcm i))
  have hright i : Integrable (fun x => u x * fderiv ℝ (c i) x (basisVec i)) volume :=
    memLp_one_iff_integrable.mp (hu.fun_mul (hdc i))
  have he i : (∫ x, g i x * c i x) = -(∫ x, u x * fderiv ℝ (c i) x (basisVec i)) := by
    have h := hw i (c i) (hc i) (hsc i) (subset_univ _)
    simp only [Measure.restrict_univ] at h
    linarith only [h]
  have hd x i : fderiv ℝ (c i) x (basisVec i) =
      q x * fderiv ℝ (fun y => v y i) x (basisVec i) +
        v x i * fderiv ℝ q x (basisVec i) := by
    rw [show c i = (fun y => q y * v y i) from rfl,
      fderiv_fun_mul (hq.differentiable (by simp) x)
        ((contDiff_pi.mp hv i).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hsum x : (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) =
      ∑ i : Fin 2, v x i * fderiv ℝ q x (basisVec i) := by
    simp_rw [hd]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdiv x, mul_zero, zero_add]
  have hl x : q x * ∑ i : Fin 2, v x i * g i x = ∑ i : Fin 2, g i x * c i x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [c]
    ring
  simp_rw [hl]
  rw [integral_finsetSum _ (fun i _ => hleft i)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hright i)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change (∑ i : Fin 2, u x * fderiv ℝ (c i) x (basisVec i)) = _
    rw [← Finset.mul_sum, hsum, mul_comm])

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Windowed coefficient regularity transfers to normalized diffusion time. -/

/-- Positive inverse dilation maps the scaled closed time interval to the physical interval. -/
theorem inv_mul_mem_Icc_of_scaled {ν a b t : ℝ} (hν : 0 < ν)
    (ht : t ∈ Set.Icc (ν * a) (ν * b)) : ν⁻¹ * t ∈ Set.Icc a b := by
  rw [show ν⁻¹ * t = t / ν by rw [div_eq_mul_inv, mul_comm]]
  exact ⟨(le_div_iff₀ hν).mpr (by simpa only [mul_comm] using ht.1),
    (div_le_iff₀ hν).mpr (by simpa only [mul_comm] using ht.2)⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Only measurability on the physical window is needed for the normalized coefficient. -/
theorem diffusionNormalizedCoefficient_joint_measurable {ν a b : ℝ} (hν : 0 < ν)
    (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2)) :
    Measurable (fun p : Set.Icc (ν * a) (ν * b) × Vec 2 => ν⁻¹ • A (ν⁻¹ * p.1) p.2) := by
  let T (p : Set.Icc (ν * a) (ν * b) × Vec 2) : Set.Icc a b × Vec 2 :=
    (⟨ν⁻¹ * p.1, inv_mul_mem_Icc_of_scaled hν p.1.property⟩, p.2)
  have hT : Measurable T :=
    (((measurable_const (a := ν⁻¹)).mul
      (measurable_subtype_coe.comp measurable_fst)).subtype_mk).prodMk
      measurable_snd
  exact (measurable_const (a := ν⁻¹)).smul (hA.comp hT)

end AVRegularity.CycleJointProofs
end
end

section
section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! A fixed source insertion price absorbs the actual omitted Taylor remainder without a graph-size factor. -/

def actualTaylorSourceInsertionPrice (D : ℕ) (Cprep Cgraph : ℝ) : ℝ :=
  2 * ((2 : ℝ) ^ D * Cprep ^ 2 + Cgraph ^ 2)

theorem actualTaylorSourceInsertionPrice_nonneg (D : ℕ) (Cprep Cgraph : ℝ) :
    0 ≤ actualTaylorSourceInsertionPrice D Cprep Cgraph := by
  unfold actualTaylorSourceInsertionPrice
  positivity

theorem actualTaylorSourceInsertionPrice_budget (D p : ℕ) (Cprep Cgraph θ ζ : ℝ)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    2 * ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2 +
      (ζ ^ p * (Cgraph * θ)) ^ 2) ≤ actualTaylorSourceInsertionPrice D Cprep Cgraph * θ ^ 2 := by
  have hz : (ζ ^ p) ^ 2 ≤ 1 := pow_le_one₀ (pow_nonneg hζ p) (pow_le_one₀ hζ hζ1)
  have hs : (ζ ^ p * (Cgraph * θ)) ^ 2 ≤ (Cgraph * θ) ^ 2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right hz (sq_nonneg (Cgraph * θ))).trans_eq (one_mul _)
  calc
    _ ≤ 2 * ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2 + (Cgraph * θ) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hs) (by norm_num)
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ D)]
      unfold actualTaylorSourceInsertionPrice
      ring

/-! Exact scale conversion for coefficients sampled in affine cell coordinates. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affineSample_scaled_jet_identity (j : ℕ) (f : E → F)
    (hf : ContDiff ℝ (j : ℕ) f) (e ρ : ℝ) (he : 0 < e) (yc z : E) :
    (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun x => f (yc + e • x)) z‖ =
      ρ ^ j * ‖iteratedFDeriv ℝ j f (yc + e • z)‖ := by
  have hg : ContDiff ℝ (j : ℕ) (fun x => f (yc + x)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [congrFun (iteratedFDeriv_comp_const_smul e hg) z,
    iteratedFDeriv_comp_add_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos he j), ← mul_assoc, ← mul_pow, div_mul_cancel₀ _ he.ne']
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace AVRegularity.CycleJointProofs

/-! Bochner L2 curves admit finite-valued approximations in their exact L2 carrier. -/

theorem exists_bochner_simple_approximation {T H : Type*} [MeasurableSpace T]
    [NormedAddCommGroup H] (μ : Measure T) (u : T → H) (hu : MemLp u 2 μ) :
    ∃ s : ℕ → SimpleFunc T H, ∃ hs : ∀ n, MemLp (s n) 2 μ,
      Tendsto (fun n => (hs n).toLp (s n)) atTop (𝓝 (hu.toLp u)) := by
  have hd : Dense (Lp.simpleFunc H 2 μ : Set (Lp H 2 μ)) :=
    Lp.simpleFunc.dense (by norm_num)
  obtain ⟨B, hBs, hB⟩ := mem_closure_iff_seq_limit.mp (hd (hu.toLp u))
  let C : ℕ → Lp.simpleFunc H 2 μ := fun n => ⟨B n, hBs n⟩
  let s := fun n => Lp.simpleFunc.toSimpleFunc (C n)
  have hs : ∀ n, MemLp (s n) 2 μ := fun n => Lp.simpleFunc.memLp (C n)
  refine ⟨s, hs, ?_⟩
  have he : (fun n => (hs n).toLp (s n)) = B := by
    funext n
    exact congrArg Subtype.val (Lp.simpleFunc.toLp_toSimpleFunc (C n))
  rw [he]
  exact hB

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! The cell coefficient factor cancels exactly with the molecular Schur denominator. -/

theorem cell_source_schur_price (ν e ρ x : ℝ) (hν : ν ≠ 0) (he : e ≠ 0)
    (hρ : ρ ≠ 0) (d : ℕ) (hd : 2 ≤ d) :
    (((e * (e ^ (d - 1))⁻¹) * ν⁻¹) * x) / ((ρ / e) ^ (d - 2)) =
      x / (ν * ρ ^ (d - 2)) := by
  have horder : d - 1 = (d - 2) + 1 := by omega
  rw [horder, pow_succ, div_pow]
  field_simp

/-! Every clipped chart window remains inside the original physical window after positive time scaling. -/

theorem clipped_scaled_time_window_subset (a b c d scale : ℝ) (hscale : 0 < scale) :
    Set.Icc (max a c / scale) (min b d / scale) ⊆ Set.Icc (a / scale) (b / scale) := by
  intro t ht
  exact ⟨(div_le_div_of_nonneg_right (le_max_left a c) hscale.le).trans ht.1,
    ht.2.trans (div_le_div_of_nonneg_right (min_le_left b d) hscale.le)⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Product-component time integrability lifts to a closed native Hilbert graph. -/

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace T]

theorem closedSubspace_memLp (S : ClosedSubmodule ℝ H) (μ : Measure T)
    (u : T → S) (hu : MemLp (fun t => (u t : H)) 2 μ) : MemLp u 2 μ := by
  have hp := S.toSubmodule.orthogonalProjectionOnto.comp_memLp' hu
  have he : (fun t => S.toSubmodule.orthogonalProjectionOnto (u t : H)) = u := by
    funext t
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (u t)
  change MemLp (fun t => S.toSubmodule.orthogonalProjectionOnto (u t : H)) 2 μ at hp
  rw [he] at hp
  exact hp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Set MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! A compact spacetime support gives a common compact spatial support for its slices. -/

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [Zero E]

theorem compactSpacetime_slice_compact (f : X × Y → E)
    (hs : HasCompactSupport f) (t : X) : HasCompactSupport (fun x => f (t, x)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_snd)
  intro x hx
  exact ⟨(t, x), subset_closure hx, rfl⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! A single finite jet price controls every lower chart-transport order. -/

theorem factorialChartPrice_mono {j n : ℕ} (hjn : j ≤ n) {D : ℝ} (hD : 1 ≤ D) :
    (j.factorial : ℝ) * D ^ j * (j + 1 : ℕ) ≤
      (n.factorial : ℝ) * D ^ n * (n + 1 : ℕ) := by
  have hfac : (j.factorial : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hjn
  have hpow : D ^ j ≤ D ^ n := pow_le_pow_right₀ hD hjn
  have hnat : ((j + 1 : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hjn 1
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  exact mul_le_mul (mul_le_mul hfac hpow (pow_nonneg hD0 j) (by positivity)) hnat
    (by positivity) (mul_nonneg (by positivity) (pow_nonneg hD0 n))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Pointwise finite sum bounds for the exact iterated spatial derivatives. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_jet_add_norm_le (f g : E → F) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ) f) (hg : ContDiff ℝ (n : ℕ) g) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n g x‖ := by
  rw [fun_iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt]
  exact norm_add_le _ _

theorem finite_jet_sum_norm_le {J : Type*} [Fintype J]
    (f : J → E → F) (n : ℕ) (hf : ∀ j, ContDiff ℝ (n : ℕ) (f j)) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => ∑ j, f j y) x‖ ≤
      ∑ j, ‖iteratedFDeriv ℝ n (f j) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => (hf j).contDiffAt)]
  exact norm_sum_le _ _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Finite factorial-normalized coefficient reserves have a uniform menu-dependent cost. -/

theorem finite_jet_seminorm_constant (K Kmax : ℕ) (hK : K ≤ Kmax) :
    (∑ j ∈ Finset.range (K + 1), (2 : ℝ) ^ j / (j.factorial : ℝ)) ≤
      (Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax := by
  have hj (j : ℕ) (hj : j ∈ Finset.range (K + 1)) :
      (2 : ℝ) ^ j / (j.factorial : ℝ) ≤ (2 : ℝ) ^ Kmax := by
    have hf : (1 : ℝ) ≤ j.factorial := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos j))
    exact (div_le_self (by positivity) hf).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hK))
  apply (Finset.sum_le_sum hj).trans
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.add_le_add_right hK 1) (by positivity)

/-! A finite order-lowering recursion has the same sum as its differentiated layers when the top coefficient vanishes. -/

section
variable {E : Type*} [AddCommMonoid E]

theorem finite_layer_recursion_sum (n : ℕ) (new coeff next : ℕ → E)
    (hzero : new 0 = coeff 0)
    (hstep : ∀ r, new (r + 1) = coeff (r + 1) + next r)
    (htop : coeff (n + 1) = 0) :
    (∑ r ∈ Finset.range (n + 2), new r) =
      ∑ r ∈ Finset.range (n + 1), (coeff r + next r) := by
  rw [Finset.sum_range_succ', hzero]
  simp_rw [hstep]
  rw [Finset.sum_add_distrib]
  calc
    _ = (coeff 0 + ∑ r ∈ Finset.range (n + 1), coeff (r + 1)) +
        ∑ r ∈ Finset.range (n + 1), next r := by ac_rfl
    _ = (∑ r ∈ Finset.range (n + 2), coeff r) +
        ∑ r ∈ Finset.range (n + 1), next r := by
      congr 1
      exact (add_comm _ _).trans (Finset.sum_range_succ' coeff (n + 1)).symm
    _ = (∑ r ∈ Finset.range (n + 1), coeff r) +
        ∑ r ∈ Finset.range (n + 1), next r := by rw [Finset.sum_range_succ, htop, add_zero]
    _ = _ := (Finset.sum_add_distrib).symm
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Component time-integral bounds sum with their original nonnegative masses. -/

theorem finite_mass_time_integral_budget {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (c : ι → ℝ≥0∞) (G F : ι → X → ℝ≥0∞) (B : ℝ≥0∞)
    (hG : ∀ i, AEMeasurable (G i) μ) (hF : ∀ i, AEMeasurable (F i) μ)
    (hb : ∀ i, (∫⁻ t, G i t ∂μ) ≤ B * ∫⁻ t, F i t ∂μ) :
    (∫⁻ t, ∑ i, c i * G i t ∂μ) ≤ B * (∫⁻ t, ∑ i, c i * F i t ∂μ) := by
  classical
  have hGpull i : (∫⁻ t, c i * G i t ∂μ) = c i * ∫⁻ t, G i t ∂μ :=
    lintegral_const_mul'' (c i) (hG i)
  have hFpull i : (∫⁻ t, c i * F i t ∂μ) = c i * ∫⁻ t, F i t ∂μ :=
    lintegral_const_mul'' (c i) (hF i)
  rw [lintegral_finsetSum' _ (fun i _ => (hG i).const_mul _),
    lintegral_finsetSum' _ (fun i _ => (hF i).const_mul _)]
  simp_rw [hGpull, hFpull]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    c i * (∫⁻ t, G i t ∂μ) ≤ c i * (B * ∫⁻ t, F i t ∂μ) :=
      mul_le_mul_of_nonneg_left (hb i) zero_le
    _ = B * (c i * ∫⁻ t, F i t ∂μ) := mul_left_comm _ _ _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! The finite native transport jet constant is uniform over the reserved derivative orders. -/

theorem finite_native_transport_constant (N Kmax D n d : ℕ)
    (hn : n ≤ Kmax) (hd : d ≤ D) (C : ℝ) (hC : 1 ≤ C) :
    ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C *
      (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1) ≤
    ((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * C *
      (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ D := by
  have hL : 1 ≤ 3 * (N + 1 : ℕ) * (2 : ℝ) ^ N * C := by
    calc
      (1 : ℝ) = 1 * 1 * 1 * 1 := by norm_num
      _ ≤ 3 * (N + 1 : ℕ) * (2 : ℝ) ^ N * C := by
        gcongr
        · norm_num
        · exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
        · exact one_le_pow₀ (by norm_num)
  have hn' : ((n + 1 : ℕ) : ℝ) ≤ ((Kmax + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hn 1
  have hpow : (2 : ℝ) ^ n ≤ 2 ^ Kmax := pow_le_pow_right₀ (by norm_num) hn
  have hd' : d - 1 ≤ D := (Nat.sub_le d 1).trans hd
  have hLp := pow_le_pow_right₀ hL hd'
  gcongr

/-! A finite Leibniz majorant retaining the molecular radius at each derivative order. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_product_weighted_jet_bound (f g : E → ℝ) (x : E) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ) f) (hg : ContDiff ℝ (n : ℕ) g)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (Bf Bg : ℕ → ℝ)
    (hfj : ∀ j ≤ n, ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ Bf j)
    (hgj : ∀ j ≤ n, ρ ^ j * ‖iteratedFDeriv ℝ j g x‖ ≤ Bg j) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * Bf j * Bg (n - j) := by
  have hm := mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_mul_le hf hg x (n := n) le_rfl) (pow_nonneg hρ n)
  apply hm.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hpow : ρ ^ n = ρ ^ j * ρ ^ (n - j) := by rw [← pow_add, Nat.add_sub_of_le hjn]
  calc
    _ = (n.choose j : ℝ) * ((ρ ^ j * ‖iteratedFDeriv ℝ j f x‖) *
        (ρ ^ (n - j) * ‖iteratedFDeriv ℝ (n - j) g x‖)) := by rw [hpow]; ring
    _ ≤ (n.choose j : ℝ) * (Bf j * Bg (n - j)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact mul_le_mul (hfj j hjn) (hgj (n - j) (Nat.sub_le _ _))
        (mul_nonneg (pow_nonneg hρ _) (norm_nonneg _))
        ((mul_nonneg (pow_nonneg hρ _) (norm_nonneg _)).trans (hfj j hjn))
    _ = _ := (mul_assoc _ _ _).symm
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Quadratic addition controls a finite response-index sum; the only cardinality is that fixed finite reserve. -/

variable {E I : Type*} [AddCommMonoid E]

theorem finite_quadratic_energy_sum_le (energy : E → ℝ≥0∞) (hz : energy 0 = 0)
    (ha : ∀ x y, energy (x + y) ≤ 2 * (energy x + energy y))
    (s : Finset I) (f : I → E) :
    energy (∑ i ∈ s, f i) ≤ (2 : ℝ≥0∞) ^ s.card * ∑ i ∈ s, energy (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, hz, Finset.card_empty, pow_zero, mul_zero, le_refl]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    have hp : (1 : ℝ≥0∞) ≤ 2 ^ s.card := by
      simpa only [one_pow] using pow_le_pow_left' (by norm_num : (1 : ℝ≥0∞) ≤ 2) s.card
    have hei : energy (f i) ≤ 2 ^ s.card * energy (f i) :=
      (one_mul (energy (f i))).symm.le.trans (mul_le_mul_of_nonneg_right hp zero_le)
    calc
      energy (f i + ∑ j ∈ s, f j) ≤ 2 * (energy (f i) + energy (∑ j ∈ s, f j)) := ha _ _
      _ ≤ 2 * (2 ^ s.card * energy (f i) + 2 ^ s.card * ∑ j ∈ s, energy (f j)) :=
        mul_le_mul_of_nonneg_left (add_le_add hei ih) zero_le
      _ = _ := by ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Actual finite response recursion keeps metric and source insertions in chronological order. -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def finiteResponse (R D S : E →ₗ[ℝ] E) (f : E) : ℕ → ℕ → E
  | 0, 0 => f
  | j + 1, 0 => R (D (finiteResponse R D S f j 0))
  | 0, h + 1 => R (S (finiteResponse R D S f 0 h))
  | j + 1, h + 1 => R (D (finiteResponse R D S f j (h + 1))) +
      R (S (finiteResponse R D S f (j + 1) h))
termination_by j h => j + h

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite physical error energy absorbs a quantitatively discounted source row. -/

theorem finite_source_feedback_absorb
    (E F C b : ℝ≥0∞) (hE : E ≠ ⊤) (hF : F ≠ ⊤) (hC : C ≠ ⊤) (hb : b ≠ ⊤)
    (h : E ≤ C * (F + b * E)) (hsmall : C * b ≤ (1 / 2 : ℝ≥0∞)) :
    E ≤ 2 * C * F := by
  have hprod := ENNReal.mul_ne_top hb hE
  have hright := ENNReal.mul_ne_top hC (ENNReal.add_ne_top.mpr ⟨hF, hprod⟩)
  have hre := ENNReal.toReal_mono hright h
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hF hprod, ENNReal.toReal_mul] at hre
  have hreal : E.toReal ≤ C.toReal * F.toReal + (C.toReal * b.toReal) * E.toReal := by
    simpa only [mul_add, mul_assoc] using hre
  have hs := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) hsmall
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat] at hs
  have hfb := mul_le_mul_of_nonneg_right hs (ENNReal.toReal_nonneg (a := E))
  have he : E.toReal ≤ 2 * C.toReal * F.toReal := by
    linarith only [hreal, hfb]
  apply (ENNReal.toReal_le_toReal hE
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hC) hF)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using he

end AVRegularity.CycleJointProofs
end
end

section
public section
namespace AVRegularity.CycleJointProofs

/-! A first spatial jet bound gives the global Lipschitz constant used to
transport localization support through preparation charts. -/

theorem lipschitzWith_of_first_jet_bound
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (X : E → G) (hX : Differentiable ℝ X) (L : NNReal)
    (hb : ∀ x, ‖iteratedFDeriv ℝ 1 X x‖ ≤ (L : ℝ)) :
    LipschitzWith L X := by
  apply lipschitzWith_of_nnnorm_fderiv_le hX
  intro x
  change ‖fderiv ℝ X x‖ ≤ (L : ℝ)
  simpa only [norm_iteratedFDeriv_one] using hb x

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CycleJointProofs

/-! A four-entry scalar expansion has a fixed operator budget. -/

theorem fourEntry_smul_sum_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Fin 2 → Fin 2 → ℝ) (T : Fin 2 → Fin 2 → E) (g : ℝ) (hg : 0 ≤ g)
    (hM : ∀ i j, |M i j| ≤ g) (hT : ∀ i j, ‖T i j‖ ≤ 1) :
    ‖∑ i, ∑ j, M i j • T i j‖ ≤ 4 * g := by
  calc
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖M i j • T i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, g := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (hM i j) (hT i j) (norm_nonneg (T i j)) hg).trans_eq (mul_one g)
    _ = _ := by simp only [Fin.sum_univ_two]; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Summable actual Hilbert fields pass through each fixed weak-test pairing. -/

variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem summable_hilbert_pairing {f : J → E} (hf : Summable f) (g : E) :
    Summable (fun j => inner ℝ (f j) g) := by
  have hs := (innerSL ℝ g).summable hf
  simpa only [innerSL_apply_apply, real_inner_comm] using hs

theorem inner_hilbert_tsum {f : J → E} (hf : Summable f) (g : E) :
    inner ℝ (∑' j, f j) g = ∑' j, inner ℝ (f j) g := by
  have he := (innerSL ℝ g).map_tsum hf
  simpa only [innerSL_apply_apply, real_inner_comm] using he

end AVRegularity.CycleJointProofs
end
end

section
public section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Joint measurability passes to a smaller closed time window. -/

theorem jointMeasurable_subwindow {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (a b c d : ℝ) (hsub : Set.Icc a b ⊆ Set.Icc c d) (f : ℝ → X → Y)
    (hf : Measurable (fun p : Set.Icc c d × X => f p.1 p.2)) :
    Measurable (fun p : Set.Icc a b × X => f p.1 p.2) := by
  let T : Set.Icc a b → Set.Icc c d := fun t => ⟨t.val, hsub t.property⟩
  have hT : Measurable T := measurable_subtype_coe.subtype_mk
  exact hf.comp (hT.prodMap measurable_id)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! One finite constant covers individual model blocks and their positive source-degree sum. -/

def jointModelConstant (C Cth : ℝ) (H : ℕ) : ℝ :=
  C * (1 + ∑ n ∈ Finset.Icc 1 H, Cth ^ n)

theorem le_jointModelConstant (C Cth : ℝ) (H : ℕ) (hC : 0 ≤ C) (hCth : 0 ≤ Cth) :
    C ≤ jointModelConstant C Cth H := by
  have hs : 0 ≤ ∑ n ∈ Finset.Icc 1 H, Cth ^ n :=
    Finset.sum_nonneg (fun n _ => pow_nonneg hCth n)
  exact (mul_one C).symm.le.trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hs) hC)

theorem source_sum_le_jointModelConstant (C Cth : ℝ) (H : ℕ)
    (hC : 0 ≤ C) :
    C * ∑ n ∈ Finset.Icc 1 H, Cth ^ n ≤ jointModelConstant C Cth H :=
  mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hC

end AVRegularity.CycleJointProofs
end
end

section
public section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Two Bochner L2 time fields have an integrable real Hilbert pairing. -/

variable {T H : Type*} [MeasurableSpace T] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem memLp_two_inner_integrable (μ : Measure T) (f g : T → H)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => inner ℝ (f t) (g t)) μ := by
  have hi := L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  apply hi.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t hft hgt
  rw [hft, hgt]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Intermediate component masses cancel in every finite source-path product. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def massConjugatedMatrix (π : ι → ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun v u => Real.sqrt (π u / π v) * A v u

omit [Fintype ι] [DecidableEq ι] in
theorem sqrt_mass_ratio_mul (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (v k u : ι) :
    Real.sqrt (π k / π v) * Real.sqrt (π u / π k) = Real.sqrt (π u / π v) := by
  rw [← Real.sqrt_mul (div_nonneg (hπ k).le (hπ v).le)]
  congr 1
  field_simp [ne_of_gt (hπ k), ne_of_gt (hπ v)]

omit [DecidableEq ι] in
theorem massConjugatedMatrix_mul (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A B : Matrix ι ι ℝ) :
    massConjugatedMatrix π (A * B) = massConjugatedMatrix π A * massConjugatedMatrix π B := by
  ext v u
  simp only [massConjugatedMatrix, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show Real.sqrt (π k / π v) * A v k *
      (Real.sqrt (π u / π k) * B k u) =
      (Real.sqrt (π k / π v) * Real.sqrt (π u / π k)) * (A v k * B k u) by ring,
    sqrt_mass_ratio_mul π hπ]

omit [Fintype ι] in
theorem massConjugatedMatrix_one (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    massConjugatedMatrix π (1 : Matrix ι ι ℝ) = 1 := by
  ext v u
  by_cases hvu : v = u
  · subst u
    simp [massConjugatedMatrix, ne_of_gt (hπ v)]
  · simp [massConjugatedMatrix, hvu]

theorem massConjugatedMatrix_pow (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : Matrix ι ι ℝ) (n : ℕ) :
    massConjugatedMatrix π (A ^ n) = massConjugatedMatrix π A ^ n := by
  induction n with
  | zero => simpa using massConjugatedMatrix_one π hπ
  | succ n ih => rw [pow_succ, massConjugatedMatrix_mul π hπ, ih, pow_succ]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Finite reserve bounds make the material sampling constant independent of the component slot. -/

theorem material_sample_constant_monotone (n N : ℕ) (hn : n ≤ N)
    (C B : ℝ) (hC : 1 ≤ C) (hB : 0 ≤ B) :
    (n.factorial : ℝ) * C ^ n * ((n + 1 : ℕ) * B) ≤
      (N.factorial : ℝ) * C ^ N * ((N + 1 : ℕ) * B) := by
  have hf : (n.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hn
  have hp : C ^ n ≤ C ^ N := pow_le_pow_right₀ hC hn
  have ha : ((n + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hn 1
  gcongr

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Clamping time preserves measurability of the frozen matrix coefficient. -/

theorem matrix_time_clamp_measurable {M : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hM : Measurable M) (a b : ℝ) :
    Measurable (fun t => M (max a (min t b))) := by
  exact hM.comp ((continuous_const.max (continuous_id.min continuous_const)).measurable)

end AVRegularity.CycleJointProofs
end
end

section
public section
open Homogenization MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Restricting a jointly measurable matrix field to a time window. -/

theorem matrixTimeWindow_measurable (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : Measurable (fun p : ℝ × Vec 2 => G p.1 p.2)) (a b : ℝ) :
    Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2) := by
  have hp : Measurable (fun p : Set.Icc a b × Vec 2 => ((p.1 : ℝ), p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  exact hG.comp hp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Dimensional source normalization cancels exactly against native transition rescaling. -/

theorem nativePiola_cell_prefactor (e ν : ℝ) (he : e ≠ 0) (hν : ν ≠ 0)
    (r d : ℕ) (hr : 1 ≤ r) (hd : r + 1 ≤ d) :
    (e * (e ^ r)⁻¹ * ν⁻¹) * (ν * e ^ (d - 2)) = e ^ (d - 1 - r) := by
  have hpow : e * e ^ (d - 2) = e ^ r * e ^ (d - 1 - r) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  field_simp
  exact hpow

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Full flux decomposition cancels the retained metric and source rows with their literal signs. -/

variable {R V Q : Type*} [Semiring R] [AddCommGroup V] [Module R V] [AddCommGroup Q] [Module R Q]

theorem nativeResidual_of_two_remainder_decomposition
    (full diag metric source metricRemainder sourceRemainder : V →ₗ[R] Q)
    (hfull : full = diag + metric + source + metricRemainder + sourceRemainder)
    (W T : V) :
    -((metric W + source W - metric T) - full W + diag W) =
      metricRemainder W + sourceRemainder W + metric T := by
  rw [hfull]
  simp only [LinearMap.add_apply]
  abel

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Positive native derivative order r corresponds exactly to source order d = r + 1. -/

variable {E : Type*} [AddCommMonoid E]

theorem native_source_order_shift (D : ℕ) (f : ℕ → E) :
    (∑ r ∈ Finset.Icc 1 (D - 1), f r) = ∑ d ∈ Finset.Icc 2 D, f (d - 1) := by
  apply Finset.sum_bij (fun r _ => r + 1)
  · intro r hr
    simp only [Finset.mem_Icc] at *
    omega
  · intro r hr s hs he
    omega
  · intro d hd
    refine ⟨d - 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at *
      omega
    · have hh := Finset.mem_Icc.mp hd
      omega
  · intro r hr
    simp only [Nat.add_sub_cancel]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A fixed derivative-word square price converts to its literal Hilbert norm price. -/

theorem norm_le_of_ennreal_card_square_budget
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : X) (y : Y) (N : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ENNReal.ofReal (‖y‖ ^ 2) ≤ ENNReal.ofReal (a ^ 2) *
      ((N : ℝ≥0∞) * (ENNReal.ofReal (b ^ 2) * ENNReal.ofReal (‖x‖ ^ 2)))) :
    ‖y‖ ≤ Real.sqrt (N : ℝ) * a * b * ‖x‖ := by
  rw [show (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by simp,
    ← ENNReal.ofReal_mul (sq_nonneg b),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ← ENNReal.ofReal_mul (sq_nonneg a)] at h
  have hs : ‖y‖ ^ 2 ≤ a ^ 2 * ((N : ℝ) * (b ^ 2 * ‖x‖ ^ 2)) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg a)
      (mul_nonneg (Nat.cast_nonneg N) (mul_nonneg (sq_nonneg b) (sq_nonneg ‖x‖))))).mp h
  have he : a ^ 2 * ((N : ℝ) * (b ^ 2 * ‖x‖ ^ 2)) =
      (Real.sqrt (N : ℝ) * a * b * ‖x‖) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  exact (sq_le_sq₀ (norm_nonneg y)
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) ha) hb) (norm_nonneg x))).mp
      (hs.trans_eq he)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Exact positive jet scaling for a centred cell-coordinate map. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_normalizedAffineIncrement
    (p : ℕ) (hp : p ≠ 0) (f : E → F) (hf : ContDiff ℝ (p : ℕ) f)
    (e : ℝ) (he : 0 < e) (yc z : E) :
    ‖iteratedFDeriv ℝ p (fun x => e⁻¹ • (f (yc + e • x) - f yc)) z‖ =
      e ^ (p - 1) * ‖iteratedFDeriv ℝ p f (yc + e • z)‖ := by
  let g := fun x : E => f (yc + x) - f yc
  have hg : ContDiff ℝ (p : ℕ) g :=
    (hf.comp (contDiff_const.add contDiff_id)).sub contDiff_const
  have hj (x : E) : iteratedFDeriv ℝ p g x = iteratedFDeriv ℝ p f (yc + x) := by
    dsimp only [g]
    change iteratedFDeriv ℝ p ((fun x => f (yc + x)) - (fun _ => f yc)) x = _
    rw [iteratedFDeriv_sub_apply (f := fun x => f (yc + x)) (g := fun _ => f yc)
      (hf.comp (contDiff_const.add contDiff_id)).contDiffAt contDiffAt_const,
      congrFun (iteratedFDeriv_const_of_ne hp (f yc)) x, Pi.zero_apply, sub_zero,
      iteratedFDeriv_comp_add_left]
  change ‖iteratedFDeriv ℝ p (fun x => e⁻¹ • g (e • x)) z‖ = _
  rw [iteratedFDeriv_const_smul_apply' (f := fun x => g (e • x))
      (a := (e⁻¹ : ℝ)) ((hg.comp (contDiff_id.const_smul e)).contDiffAt),
    congrFun (iteratedFDeriv_comp_const_smul e hg) z, hj (e • z), norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he), abs_of_pos (pow_pos he p),
    ← mul_assoc]
  have hpow : e⁻¹ * e ^ p = e ^ (p - 1) := by
    have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
    conv_lhs => rw [← Nat.sub_add_cancel hp1, pow_succ]
    rw [mul_left_comm, inv_mul_cancel₀ he.ne', mul_one]
  rw [hpow]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Scalar removal of a positive mass conjugation and molecular normalization. -/

theorem normalized_physical_budget (w z den fac C A : ℝ)
    (hw : 0 < w) (hden : 0 < den) (hfac : 0 < fac)
    (hb : w * (z / den * fac) ≤ C * (w * A)) :
    z ≤ C * den / fac * A := by
  have h₁ : z / den * fac ≤ C * A := by
    apply (mul_le_mul_iff_of_pos_left hw).mp
    simpa only [mul_assoc, mul_left_comm] using hb
  have h₂ : z / den ≤ (C * A) / fac := (le_div_iff₀ hfac).mpr h₁
  have h₃ := (div_le_iff₀ hden).mp h₂
  calc
    z ≤ (C * A) / fac * den := h₃
    _ = C * den / fac * A := by ring

/-! Torus patches and all their integer images enumerate the full spatial lattice once. -/

def periodImageIndexEquiv (N : ℕ) (hN : 0 < N) : (Fin N × ℤ) ≃ ℤ where
  toFun p := (p.1 : ℤ) + (N : ℤ) * p.2
  invFun k := (⟨(k % (N : ℤ)).toNat, by
    have hpos : (0 : ℤ) < N := by exact_mod_cast hN
    have hlo := Int.emod_nonneg k (ne_of_gt hpos)
    have hhi := Int.emod_lt_of_pos k hpos
    omega⟩, k / (N : ℤ))
  left_inv p := by
    obtain ⟨r, k⟩ := p
    have hpos : (0 : ℤ) < N := by exact_mod_cast hN
    have hh := (Int.ediv_emod_unique hpos).mpr
      (show (r : ℤ) + (N : ℤ) * k = (r : ℤ) + (N : ℤ) * k ∧
        0 ≤ (r : ℤ) ∧ (r : ℤ) < N from ⟨rfl, by omega, by exact_mod_cast r.isLt⟩)
    apply Prod.ext
    · apply Fin.ext
      simp only [hh.2, Int.toNat_natCast]
    · exact hh.1
  right_inv k := by
    have hpos : (0 : ℤ) < N := by exact_mod_cast hN
    simp only [Int.toNat_of_nonneg (Int.emod_nonneg k (ne_of_gt hpos))]
    exact Int.emod_add_mul_ediv k N

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Finite weighted sums of genuine L2 carriers read their literal weighted representatives almost everywhere. -/

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]

theorem planeLp_weighted_fintype_sum_ae
    (c : J → ℝ) (U : J → Lp E 2 (volume : Measure (Vec 2))) :
    (∑ j : J, c j • U j : Lp E 2 volume) =ᵐ[volume]
      fun x => ∑ j : J, c j • U j x := by
  have ha : ∀ᵐ x ∂volume, ∀ j : J, (c j • U j : Lp E 2 volume) x = c j • U j x :=
    ae_all_iff.mpr (fun j => Lp.coeFn_smul (c j) (U j))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => c j • U j), ha] with x hs ha
  simp only [Finset.sum_apply] at hs
  exact hs.trans (Finset.sum_congr rfl (fun j _ => ha j))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite time-Lp assembly independent of Sobolev coefficient data. -/

/-- A finite collection of time-Lp functions has a time-Lp sum. -/
theorem memLp_fintype_sum {α E J : Type*} [MeasurableSpace α]
    [TopologicalSpace E] [ESeminormedAddCommMonoid E] [ContinuousAdd E] [Fintype J] {μ : Measure α} {p : ℝ≥0∞}
    (f : J → α → E) (hf : ∀ j, MemLp (f j) p μ) :
    MemLp (fun t => ∑ j, f j t) p μ :=
  memLp_finsetSum Finset.univ (fun j _ => hf j)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CycleJointProofs

/-! Positive source powers retain both Schur sums independently of the number of components. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveMatrix_pow_nonneg (B : Matrix ι ι ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (n : ℕ) (v u : ι) : 0 ≤ (B ^ n) v u := by
  induction n generalizing v u with
  | zero => simp only [pow_zero, Matrix.one_apply]; split <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih v k) (hB k u))

theorem positiveMatrix_pow_row_sum (B : Matrix ι ι ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (θ : ℝ) (hθ : 0 ≤ θ) (hrow : ∀ v, ∑ u, B v u ≤ θ) (n : ℕ) (v : ι) :
    ∑ u, (B ^ n) v u ≤ θ ^ n := by
  induction n with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    calc
      ∑ u, (B ^ (n + 1)) v u = ∑ k, (B ^ n) v k * (∑ u, B k u) := by
        simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ ∑ k, (B ^ n) v k * θ := Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (hrow k) (positiveMatrix_pow_nonneg B hB n v k))
      _ = (∑ k, (B ^ n) v k) * θ := (Finset.sum_mul _ _ _).symm
      _ ≤ θ ^ n * θ := mul_le_mul_of_nonneg_right ih hθ
      _ = θ ^ (n + 1) := (pow_succ θ n).symm

theorem positiveMatrix_pow_col_sum (B : Matrix ι ι ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (θ : ℝ) (hθ : 0 ≤ θ) (hcol : ∀ u, ∑ v, B v u ≤ θ) (n : ℕ) (u : ι) :
    ∑ v, (B ^ n) v u ≤ θ ^ n := by
  have ht := positiveMatrix_pow_row_sum B.transpose (fun v u => hB u v) θ hθ hcol n u
  simpa only [← Matrix.transpose_pow, Matrix.transpose_apply] using ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Positive time dilation preserves the exact restricted measure, Lp class and almost-everywhere data. -/

theorem map_volume_restrict_Icc_inv_mul (ν a b : ℝ) (hν : 0 < ν) :
    Measure.map (fun t : ℝ => ν⁻¹ * t) (volume.restrict (Set.Icc (ν * a) (ν * b))) =
      ENNReal.ofReal ν • volume.restrict (Set.Icc a b) := by
  have hf : MeasurableEmbedding (fun t : ℝ => ν⁻¹ * t) :=
    (Homeomorph.mulLeft₀ ν⁻¹ (inv_ne_zero hν.ne')).isClosedEmbedding.measurableEmbedding
  have he : (fun t : ℝ => ν⁻¹ * t) ⁻¹' Set.Icc a b = Set.Icc (ν * a) (ν * b) := by
    ext t
    change (a ≤ ν⁻¹ * t ∧ ν⁻¹ * t ≤ b) ↔ (ν * a ≤ t ∧ t ≤ ν * b)
    have ht : ν⁻¹ * t = t / ν := by rw [div_eq_mul_inv, mul_comm]
    rw [ht, le_div_iff₀ hν, div_le_iff₀ hν]
    simp only [mul_comm]
  rw [← he, ← hf.restrict_map volume (Set.Icc a b),
    Real.map_volume_mul_left (inv_ne_zero hν.ne'), Measure.restrict_smul]
  simp only [inv_inv, abs_of_pos hν]

variable {E : Type*} [NormedAddCommGroup E]

theorem memLp_comp_inv_mul_restrict_Icc {ν a b : ℝ} (hν : 0 < ν)
    {p : ℝ≥0∞} {f : ℝ → E} (hf : MemLp f p (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => f (ν⁻¹ * t)) p (volume.restrict (Set.Icc (ν * a) (ν * b))) := by
  have hm := hf.smul_measure (c := ENNReal.ofReal ν) ENNReal.ofReal_ne_top
  rw [← map_volume_restrict_Icc_inv_mul ν a b hν] at hm
  exact hm.comp_of_map (measurable_const.mul measurable_id).aemeasurable

theorem ae_comp_inv_mul_restrict_Icc {ν a b : ℝ} (hν : 0 < ν) {p : ℝ → Prop}
    (hp : ∀ᵐ t ∂volume.restrict (Set.Icc a b), p t) :
    ∀ᵐ t ∂volume.restrict (Set.Icc (ν * a) (ν * b)), p (ν⁻¹ * t) := by
  have hf : MeasurableEmbedding (fun t : ℝ => ν⁻¹ * t) :=
    (Homeomorph.mulLeft₀ ν⁻¹ (inv_ne_zero hν.ne')).isClosedEmbedding.measurableEmbedding
  have hm := Measure.ae_smul_measure hp (ENNReal.ofReal ν)
  rw [← map_volume_restrict_Icc_inv_mul ν a b hν] at hm
  exact hf.ae_map_iff.mp hm

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! The physical velocity retains its spatial regularity under positive time normalization. -/

/-- Physical drift written in normalized diffusion time. -/
def timeNormalizedVelocity (ν : ℝ) (v : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t x => ν⁻¹ • v (ν⁻¹ * t) x

/-- Spatial normalization preserves each supplied differentiability order. -/
theorem timeNormalizedVelocity_contDiff (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (N : ℕ∞) (hv : ContDiff ℝ N (v (ν⁻¹ * t))) :
    ContDiff ℝ N (timeNormalizedVelocity ν v t) :=
  hv.const_smul ν⁻¹

/-- Positive viscosity scales a physical uniform velocity bound by its inverse. -/
theorem timeNormalizedVelocity_norm_le {ν M : ℝ} (hν : 0 < ν)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hv : ∀ x, ‖v (ν⁻¹ * t) x‖ ≤ M) (x : Vec 2) :
    ‖timeNormalizedVelocity ν v t x‖ ≤ ν⁻¹ * M := by
  change ‖ν⁻¹ • v (ν⁻¹ * t) x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hν)]
  exact mul_le_mul_of_nonneg_left (hv x) (inv_nonneg.mpr hν.le)

/-- Spatial divergence remains zero in normalized diffusion time. -/
theorem timeNormalizedVelocity_divergence_zero (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (hv : ContDiff ℝ 1 (v (ν⁻¹ * t)))
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (v (ν⁻¹ * t)) x (basisVec k) k = 0)
    (x : Vec 2) :
    ∑ k : Fin 2, fderiv ℝ (timeNormalizedVelocity ν v t) x (basisVec k) k = 0 := by
  have hd := ((hv.differentiable (by norm_num)) x).hasFDerivAt.const_smul ν⁻¹
  change ∑ k : Fin 2, fderiv ℝ (ν⁻¹ • v (ν⁻¹ * t)) x (basisVec k) k = 0
  rw [hd.fderiv]
  simp only [smul_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hdiv, mul_zero]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Local lower bounds on a moment weight give local L2 decay of its field. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weightedLocal_eLpNorm_le (f : Vec 2 → E) (q : Vec 2 → ℝ)
    (μ : Measure (Vec 2)) (c : ℝ) (hc : 0 ≤ c)
    (hf : AEStronglyMeasurable f μ) (hq : ∀ᵐ x ∂μ, 1 ≤ c * q x) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal c * eLpNorm (fun x => q x • f x) 2 μ := by
  have he : eLpNorm f 2 μ ≤ eLpNorm (fun x => c • (q x • f x)) 2 μ := by
    apply eLpNorm_mono_ae hf
    filter_upwards [hq] with x hx
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc]
    have hh : 1 ≤ c * |q x| := hx.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hc)
    nlinarith only [mul_le_mul_of_nonneg_right hh (norm_nonneg (f x))]
  change eLpNorm f 2 μ ≤ eLpNorm (c • (fun x => q x • f x)) 2 μ at he
  rw [eLpNorm_const_smul] at he
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hc] using he

end AVRegularity.CycleJointProofs
end
end
