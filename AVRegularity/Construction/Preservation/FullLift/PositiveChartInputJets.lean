-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.GradFactorialNormSq
public import AVRegularity.CycleComparison.Lift.TransverseModeFactor
public import AVRegularity.Definitions.Construction.Gen.ParShift
public import AVRegularity.Statements.Intermediate.CycleComparison.CovOperator
public import AVRegularity.Statements.Intermediate.CycleOutput.LiftEdges
public import AVRegularity.Analysis.Convolution.Kernel.Spatial
public import AVRegularity.Statements.Intermediate.CycleOutput.GluedLift
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
public import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Finite pulse degrees and heights collapse to one positive matrix before time suprema. -/

open CycleComparison.Lift
variable {ι κ : Type*} [Fintype ι]

theorem finite_sum_real_schur_budget (s : Finset κ) (M : κ → ι → ι → ℝ) (C : κ → ℝ)
    (hM : ∀ a ∈ s, HasRealSchurBudget (M a) (C a)) :
    HasRealSchurBudget (fun v u => ∑ a ∈ s, M a v u) (∑ a ∈ s, C a) := by
  constructor
  · intro v u
    exact Finset.sum_nonneg (fun a ha => (hM a ha).nonneg v u)
  · intro v
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun a ha => (hM a ha).row_sum v)
  · intro u
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun a ha => (hM a ha).col_sum u)

theorem finite_pulse_degree_height_sum_le (H N : ℕ) (M : ℕ → ι → ι → ℝ)
    (hM : ∀ hh ≤ H, ∀ v u, 0 ≤ M hh v u) (K : ℕ → ℝ) (hK : ∀ n ≤ N, 0 ≤ K n)
    (x : ι → ℝ) (hx : ∀ u, 0 ≤ x u) (v : ι) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
      ε ^ n * (K n * ∑ u, M hh v u * x u)) ≤
      (∑ n ∈ Finset.range (N + 1), K n) *
        ∑ u, (∑ hh ∈ Finset.range (H + 1), M hh v u) * x u := by
  calc
    _ ≤ ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
        K n * ∑ u, M hh v u * x u := by
      apply Finset.sum_le_sum
      intro hh hhh
      have hhh' : hh ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)
      apply Finset.sum_le_sum
      intro n hn
      have hn' : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hε0 hε1)
        (mul_nonneg (hK n hn') (Finset.sum_nonneg
          (fun u _ => mul_nonneg (hM hh hhh' v u) (hx u))))).trans_eq (one_mul _)
    _ = ∑ n ∈ Finset.range (N + 1), K n *
        (∑ hh ∈ Finset.range (H + 1), ∑ u, M hh v u * x u) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = (∑ n ∈ Finset.range (N + 1), K n) *
        (∑ hh ∈ Finset.range (H + 1), ∑ u, M hh v u * x u) :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by
      apply congrArg (fun z : ℝ => (∑ n ∈ Finset.range (N + 1), K n) * z)
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Move each finite positive mass and diffusivity inside its component time operations. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem classicalStrongEnergy_weighted_components (ρ ν : ℝ) (π : ι → ℝ)
    (I : Set ℝ) (K : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) :
    classicalStrongEnergy ρ ν π I K a =
      (∑ i, ((⨆ t ∈ I, ENNReal.ofReal (π i)⁻¹ *
        classicalFactorialSq ρ K (fun x => a t x i)) +
        ∫⁻ t in I, ENNReal.ofReal ν * (ENNReal.ofReal (π i)⁻¹ *
          classicalGradFactorialSq ρ K (fun x => a t x i)))) ^ (1 / 2 : ℝ) := by
  unfold classicalStrongEnergy
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfinite : ENNReal.ofReal (π i)⁻¹ ≠ ∞ := ENNReal.ofReal_ne_top
  rw [mul_add]
  congr 1
  · simp_rw [ENNReal.mul_iSup]
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ hfinite, mul_left_comm]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Coefficient order comparison and radius independence of the order-zero price. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientSeminorm_order_mono (ρ : ℝ) {K L : ℕ} (hKL : K ≤ L)
    (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F) :
    coefficientSeminorm ρ K a b A ≤ coefficientSeminorm ρ L a b A := by
  unfold coefficientSeminorm
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.succ_le_succ hKL)
  · intro _ _ _
    exact zero_le

theorem coefficientSeminorm_order_zero_radius (ρ R : ℝ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) :
    coefficientSeminorm ρ 0 a b A = coefficientSeminorm R 0 a b A := by
  unfold coefficientSeminorm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, ENNReal.ofReal_one, one_mul, zero_add]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Enlarging a factorial radius costs a fixed power of its ratio, at the same jet order. -/

theorem factorialWeight_mul_radius (A ρ : ℝ) (j : ℕ) :
    factorialWeight (A * ρ) j = A ^ (2 * j) * factorialWeight ρ j := by
  simp only [factorialWeight, mul_pow, mul_div_assoc]

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {μ : Measure (Vec 2)} {K : ℕ}

theorem factorialNormSq_mul_radius_le {A : ℝ} (hA : 1 ≤ A) (ρ : ℝ) (D : JetL2 μ K E) :
    factorialNormSq (A * ρ) D ≤ A ^ (2 * K) * factorialNormSq ρ D := by
  simp only [factorialNormSq, factorialWeight_mul_radius]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hp : A ^ (2 * j.val) ≤ A ^ (2 * K) :=
    pow_le_pow_right₀ hA (Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp j.isLt))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (factorialWeight_nonneg ρ j.val)) (derivativeNormSq_nonneg D j)

theorem gradFactorialNormSq_mul_radius_le {A : ℝ} (hA : 1 ≤ A) (ρ : ℝ)
    (D : JetL2 μ (K + 1) E) :
    gradFactorialNormSq (A * ρ) D ≤ A ^ (2 * K) * gradFactorialNormSq ρ D := by
  simp only [gradFactorialNormSq, factorialWeight_mul_radius]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hp : A ^ (2 * j.val) ≤ A ^ (2 * K) :=
    pow_le_pow_right₀ hA (Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp j.isLt))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (factorialWeight_nonneg ρ j.val))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The coarse identity and the positive lift share one mass-conjugated matrix budget. -/

open CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mass_conjugated_identity_add_schur_budget
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (M : ι → ι → ℝ) {C K : ℝ}
    (hM : HasRealSchurBudget (massConjugatedMatrix π M) C) (hK : 0 ≤ K) :
    HasRealSchurBudget (massConjugatedMatrix π
      (fun v u => (if v = u then 1 else 0) + K * M v u)) (1 + K * C) := by
  have heq : massConjugatedMatrix π
      (fun v u => (if v = u then 1 else 0) + K * M v u) =
      fun v u => (if v = u then 1 else 0) + K * massConjugatedMatrix π M v u := by
    funext v u
    by_cases h : v = u
    · subst u
      simp only [massConjugatedMatrix, div_self (hπ v).ne', Real.sqrt_one,
        one_mul]
    · simp only [massConjugatedMatrix, ite_eq_right h, zero_add]
      ring
  rw [heq]
  exact hasRealSchurBudget_diagonal.add (hM.const_mul K hK)

theorem identity_add_matrix_action (M : ι → ι → ℝ) (K : ℝ) (x : ι → ℝ) (v : ι) :
    x v + K * ∑ u, M v u * x u =
      ∑ u, ((if v = u then 1 else 0) + K * M v u) * x u := by
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  congr 1
  simp

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Positive-degree pulse sums use one fixed component matrix, independently of time. -/

section
variable {ι : Type*} [Fintype ι]

theorem finite_pulse_degree_height_sum_eq (hs ns : Finset ℕ)
    (M : ℕ → ι → ι → ℝ) (K : ℕ → ℝ) (x : ι → ℝ) (v : ι) :
    (∑ hh ∈ hs, ∑ n ∈ ns, K n * ∑ u, M hh v u * x u) =
      (∑ n ∈ ns, K n) * ∑ u, (∑ hh ∈ hs, M hh v u) * x u := by
  calc
    _ = ∑ n ∈ ns, K n * (∑ hh ∈ hs, ∑ u, M hh v u * x u) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = (∑ n ∈ ns, K n) * (∑ hh ∈ hs, ∑ u, M hh v u * x u) :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by
      apply congrArg (fun z : ℝ => (∑ n ∈ ns, K n) * z)
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]

/-- Every retained degree carries at least one scale power before the height matrix sum. -/
theorem finite_positive_pulse_degree_height_sum_le (H N : ℕ) (M : ℕ → ι → ι → ℝ)
    (hM : ∀ hh ≤ H, ∀ v u, 0 ≤ M hh v u) (K : ℕ → ℝ) (hK : ∀ n ≤ N, 0 ≤ K n)
    (x : ι → ℝ) (hx : ∀ u, 0 ≤ x u) (v : ι) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range N,
      ε ^ (n + 1) * (K (n + 1) * ∑ u, M hh v u * x u)) ≤
      ε * (∑ n ∈ Finset.range N, K (n + 1)) *
        ∑ u, (∑ hh ∈ Finset.range (H + 1), M hh v u) * x u := by
  cases N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero, mul_zero, zero_mul, le_refl]
  | succ N =>
    have hb := finite_pulse_degree_height_sum_le H N M hM (fun n => K (n + 1))
      (fun n hn => hK _ (Nat.add_le_add_right hn 1)) x hx v hε0 hε1
    calc
      _ = ε * (∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
          ε ^ n * (K (n + 1) * ∑ u, M hh v u * x u)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun hh _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [pow_succ]
        ring
      _ ≤ ε * ((∑ n ∈ Finset.range (N + 1), K (n + 1)) *
          ∑ u, (∑ hh ∈ Finset.range (H + 1), M hh v u) * x u) :=
        mul_le_mul_of_nonneg_left hb hε0
      _ = _ := by rw [mul_assoc]
end

/-! A selected widest record is one of the original path records. -/

theorem widestTags_mem {ts : List ProvTags} {t : ProvTags} (ht : widestTags ts = some t) : t ∈ ts := by
  induction ts with
  | nil => simp only [widestTags, reduceCtorEq] at ht
  | cons x xs ih =>
    simp only [widestTags] at ht
    cases hw : widestTags xs with
    | none =>
      rw [hw] at ht
      have he : x = t := Option.some.inj ht
      exact he ▸ List.mem_cons_self
    | some y =>
      rw [hw] at ht
      dsimp only at ht
      split_ifs at ht with hxy
      · have he : y = t := Option.some.inj ht
        exact List.mem_cons_of_mem _ (ih (hw.trans (congrArg some he)))
      · have he : x = t := Option.some.inj ht
        exact he ▸ List.mem_cons_self

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual constant covariance operator preserves reserved classical regularity and periodicity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covOperator_contDiff (Hc : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ)
    (u : Vec 2 → E) (hu : ContDiff ℝ ((n + 2 : ℕ) : ℕ∞) u) :
    ContDiff ℝ (n : ℕ∞) (covOperator Hc u) := by
  have hd (j : Fin 2) : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞)
      (fun x => fderiv ℝ u x (basisVec j)) :=
    (hu.fderiv_right (by exact_mod_cast (by omega : n + 1 + 1 ≤ n + 2))).clm_apply contDiff_const
  have hdd (i j : Fin 2) : ContDiff ℝ (n : ℕ∞)
      (fun x => fderiv ℝ (fun y => fderiv ℝ u y (basisVec j)) x (basisVec i)) :=
    ((hd j).fderiv_right (by exact_mod_cast (le_refl (n + 1)))).clm_apply contDiff_const
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.smul (hdd i j)

theorem covOperator_periodic (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (u : Vec 2 → E) (hu : ContDiff ℝ 2 u) (hp : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (covOperator Hc u) := by
  have hDp := fderiv_isZ2Periodic (hu.differentiable (by norm_num)) hp
  have hd (j : Fin 2) : ContDiff ℝ 1 (fun x => fderiv ℝ u x (basisVec j)) :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hddp (j : Fin 2) := fderiv_isZ2Periodic ((hd j).differentiable (by norm_num))
    (fun n x => congrArg (fun L => L (basisVec j)) (hDp n x))
  intro n x
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun L => Hc i j • L (basisVec i)) (hddp j n x)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Increasing a nonnegative lift price increases both factors of its component energy bound. -/

open CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem identity_plus_matrix_energy_mono
    (π : ι → ℝ) (hπ : ∀ u, 0 < π u) (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u)
    {B C s t : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hst : s ≤ t)
    (Z : ι → ℝ≥0∞) (v : ι) :
    ENNReal.ofReal (B * (1 + s * C)) *
      (∑ u, ENNReal.ofReal (massConjugatedMatrix π
        (fun v u => (if v = u then 1 else 0) + s * M v u) v u * (π u)⁻¹) * Z u) ≤
    ENNReal.ofReal (B * (1 + t * C)) *
      (∑ u, ENNReal.ofReal (massConjugatedMatrix π
        (fun v u => (if v = u then 1 else 0) + t * M v u) v u * (π u)⁻¹) * Z u) := by
  apply mul_le_mul'
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_right hst hC) 1) hB)
  · refine Finset.sum_le_sum fun u _ => mul_le_mul' ?_ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (hπ u).le)
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact add_le_add_right (mul_le_mul_of_nonneg_right hst (hM v u)) _

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Reparametrizing coefficients preserves the actual source graph and its depth. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftEdges_empty_iff (c lam : ℝ) (edge : ConstituentEdges D h)
    (v u : ι) (d : Finset.Icc 2 D) :
    liftEdges c lam edge v u d = [] ↔ edge v u d = [] := by
  simp only [liftEdges, List.map_eq_nil_iff]

theorem liftEdges_depth (c lam : ℝ) (edge : ConstituentEdges D h) {H : ℕ}
    (hdepth : HasDepthAtMost edge H) : HasDepthAtMost (liftEdges c lam edge) H := by
  intro path
  obtain ⟨k, hk⟩ := hdepth path
  exact ⟨k, fun d => (liftEdges_empty_iff c lam edge _ _ d).mpr (hk d)⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Effective masses give precisely the marked record matrix of the stage invariant. -/

theorem sqrt_effective_mass_ratio {pu pv wu wv : ℝ}
    (hpu : 0 ≤ pu) (hpv : 0 < pv) (hwu : 0 < wu) (hwv : 0 < wv) :
    Real.sqrt ((pu / wu ^ 2) / (pv / wv ^ 2)) =
      wv / wu * Real.sqrt (pu / pv) := by
  rw [Real.sqrt_div (div_nonneg hpu (sq_nonneg wu)),
    Real.sqrt_div hpu, Real.sqrt_sq hwu.le,
    Real.sqrt_div hpv.le, Real.sqrt_sq hwv.le, Real.sqrt_div hpu]
  field_simp [hwu.ne', hwv.ne', (Real.sqrt_pos.mpr hpv).ne']

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem recordMajorant_effective_mass (F : ChartedFamily ι h D P Ctx)
    (π w : ι → ℝ) (hπ : ∀ i, 0 < π i) (hw : ∀ i, 0 < w i) (v u : ι) :
    recordMajorant (fun i => π i / w i ^ 2) F v u =
      w v / w u * recordMajorant π F v u := by
  unfold recordMajorant
  rw [sqrt_effective_mass_ratio (hπ u).le (hπ v) (hw u) (hw v)]
  exact mul_assoc _ _ _

theorem recordMajorant_effective_mass_schur [Fintype ι]
    (F : ChartedFamily ι h D P Ctx) (π w : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (hw : ∀ i, 0 < w i) (S : ℝ)
    (hrow : ∀ v, ∑ u, w v / w u * recordMajorant π F v u ≤ S)
    (hcol : ∀ u, ∑ v, w v / w u * recordMajorant π F v u ≤ S) :
    (∀ v, ∑ u, recordMajorant (fun i => π i / w i ^ 2) F v u ≤ S) ∧
      (∀ u, ∑ v, recordMajorant (fun i => π i / w i ^ 2) F v u ≤ S) := by
  simp_rw [recordMajorant_effective_mass F π w hπ hw]
  exact ⟨hrow, hcol⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Moving torus averages act measurably on strongly measurable L2 fields. -/

open AVRegularity.Analysis.Convolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem moving_torus_average_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    (H : T → Vec 2 →L[ℝ] Vec 2) (hH : Measurable H) (r : ℝ)
    (κ : Vec 2 → ℝ) (hκ : Measurable κ) (hκint : Integrable κ)
    (f : T → L2 E torusMeasure) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun t => torusAveragingOperator r (H t) κ hκint (f t)) := by
  have heval : Continuous (fun p : (Vec 2 →L[ℝ] Vec 2) × Vec 2 => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hδ : Measurable (fun p : T × Vec 2 => torusQuotient (r • H p.1 p.2)) :=
    continuous_torusQuotient.measurable.comp
      ((heval.measurable.comp ((hH.comp measurable_fst).prodMk measurable_snd)).const_smul r)
  let action : (UnitAddTorus (Fin 2)) × L2 E torusMeasure → L2 E torusMeasure :=
    fun p => translation p.1 p.2
  have haction : Continuous action :=
    continuous_prod_of_continuous_lipschitzWith' action 1
      (fun x => (translation x).isometry.lipschitzWith) continuous_translation
  have hδs : StronglyMeasurable (fun p : T × Vec 2 =>
      torusQuotient (r • H p.1 p.2)) := hδ.stronglyMeasurable
  have hfs : StronglyMeasurable (fun p : T × Vec 2 => f p.1) :=
    hf.comp_measurable measurable_fst
  have hp : StronglyMeasurable (fun p : T × Vec 2 =>
      (torusQuotient (r • H p.1 p.2), f p.1)) := hδs.prodMk hfs
  have htr : StronglyMeasurable (fun p : T × Vec 2 =>
      action (torusQuotient (r • H p.1 p.2), f p.1)) :=
    haction.comp_stronglyMeasurable hp
  have hi : StronglyMeasurable (fun p : T × Vec 2 =>
      κ p.2 • translation (torusQuotient (r • H p.1 p.2)) (f p.1)) :=
    (hκ.comp measurable_snd).stronglyMeasurable.smul htr
  change StronglyMeasurable (fun t => ∫ z : Vec 2,
    κ z • translation (torusQuotient (r • H t z)) (f t))
  exact hi.integral_prod_right' 

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Evaluate the physical pulse sum with time-frozen charts and input. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem pulsePhysicalLift_static_expansion (c ρ e εc : ℝ) (N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (Φ Ψ : Vec 2 → Vec 2)
    (f : Vec 2 → ∀ i, h i) (τ : ℝ) (x : Vec 2) (v : ι) :
    pulsePhysicalLift c ρ e εc N H Cc (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ x v =
      ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1),
        εc ^ n • liftApply n (Cc hh n) (fun _ Y => f (Φ (ρ • Y)))
          (c⁻¹ * τ) (ρ⁻¹ • Ψ x) (e⁻¹ • Ψ x) v := by
  simp only [pulsePhysicalLift, diagSample, Finset.sum_apply, Pi.smul_apply]

/-- At a fixed physical time, only the pulled-back input at the corresponding cell time is used. -/
theorem pulsePhysicalLift_freeze_time (c ρ e εc : ℝ) (N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (chart label : ℝ → Vec 2 → Vec 2)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) :
    pulsePhysicalLift c ρ e εc N H Cc chart label a t =
      pulsePhysicalLift c ρ e εc N H Cc
        (fun _ => chart (c * (c⁻¹ * t))) (fun _ => label t)
        (fun _ => a (c * (c⁻¹ * t))) t := by
  rfl

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! An ambient jet reserve supplies every smaller effective source reserve with the same prices. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem scaledEnvelope_order_mono {π : ι → ℝ} {edge : ConstituentEdges D h}
    {I : Set ℝ} {lam : ℝ} {Cj : ℕ → ℕ → ℝ} {qs qf rs rf : ℕ}
    {price : ι → ι → ℝ} {Θ : ℝ} (hs : rs ≤ qs) (hf : rf ≤ qf)
    (he : IsScaledJetEnvelope π edge I lam Cj qs qf price Θ) :
    IsScaledJetEnvelope π edge I lam Cj rs rf price Θ := by
  exact ⟨he.nonneg, he.row_sum, he.col_sum,
    fun v u r hr q hq => he.jets v u r (hr.trans hs) q (hq.trans hf)⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Physical lift synthesis respects coefficient equality at its actual cell time. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem pulsePhysicalLift_coeff_congr (c ρ e εc : ℝ) (N H : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hc : ∀ hh ≤ H, ∀ n ≤ N, ∀ m (α : DerivativeWord2 m), ∀ X z v u,
      Cc hh n m α (c⁻¹ * t) X z v u = Dc hh n m α (c⁻¹ * t) X z v u)
    (x : Vec 2) :
    pulsePhysicalLift c ρ e εc N H Cc chart label a t x =
      pulsePhysicalLift c ρ e εc N H Dc chart label a t x := by
  unfold pulsePhysicalLift
  apply Finset.sum_congr rfl
  intro hh hhh
  dsimp only [diagSample]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  funext v
  unfold liftApply
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro u _
  rw [hc hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh))
    n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) m α]

theorem gluedLift_coeff_congr (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (c ρ e εc : ℝ) (N H : ℕ) (Cc Dc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hc : ∀ j ∈ kset, ϖ j t ≠ 0 → ∀ hh ≤ H, ∀ n ≤ N,
      ∀ m (α : DerivativeWord2 m), ∀ X z v u,
        Cc j hh n m α (c⁻¹ * t) X z v u = Dc j hh n m α (c⁻¹ * t) X z v u)
    (x : Vec 2) :
    gluedLift kset ϖ c ρ e εc N H Cc chart label a t x =
      gluedLift kset ϖ c ρ e εc N H Dc chart label a t x := by
  classical
  unfold gluedLift
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hw : ϖ j t = 0
  · simp only [hw, zero_smul]
  · rw [pulsePhysicalLift_coeff_congr c ρ e εc N H (Cc j) (Dc j)
      (chart j) (label j) a t (hc j hj hw) x]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Scale-invariant chart composition preserves the original positive coefficient price. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem positive_chart_composition_jet_bound
    (f : Vec 2 → V) (Ψ : Vec 2 → Vec 2) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ∞) f) (hΨ : ContDiff ℝ (n : ℕ∞) Ψ)
    (C R ρ θ : ℝ) (hC : 1 ≤ C) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (B : ℕ → ℝ)
    (hjet : ChartTransport.JetBound Ψ n C R)
    (hbound : ∀ j, j ≤ n → ∀ y, ρ ^ j * ‖iteratedFDeriv ℝ j f y‖ ≤ B j * θ)
    (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (f ∘ Ψ) x‖ ≤
      ((n.factorial : ℝ) * C ^ n * ∑ j ∈ Finset.range (n + 1), B j) * θ := by
  have hh := ChartTransport.scaled_comp_bound hf hΨ hC hρ hρR x
    (fun p hp hpn => hjet p hp hpn x)
  apply hh.trans
  calc
    (n.factorial : ℝ) * C ^ n *
        (∑ j ∈ Finset.range (n + 1), ρ ^ j * ‖iteratedFDeriv ℝ j f (Ψ x)‖) ≤
      (n.factorial : ℝ) * C ^ n * (∑ j ∈ Finset.range (n + 1), B j * θ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun j hj => hbound j (by have := Finset.mem_range.mp hj; omega) _))
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hC) _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Truncation retains the value, which determines every Sobolev jet of the same field. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem torus_truncation_injective {K L : ℕ} (hKL : K ≤ L) :
    Function.Injective (truncateTorusHk hKL : TorusHk L E → TorusHk K E) := by
  intro W V he
  apply TorusHk.ext_value
  have hi : truncateJetIndex hKL (valueIndex2 K) = valueIndex2 L := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  have hval := congrArg (fun U : TorusHk K E => U.val (valueIndex2 K)) he
  change W.val (truncateJetIndex hKL (valueIndex2 K)) =
    V.val (truncateJetIndex hKL (valueIndex2 K)) at hval
  simpa only [hi] using hval

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Every fiber coefficient is the literal field of one identity at that order. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem fiber_coefficient_identity (F : ChartedFamily ι h D P Ctx) (p : P) (c : Ctx p)
    (v u : ι) (d : Finset.Icc 2 D) (γ : Constituent d.1 (h u) (h v))
    (hγ : γ ∈ F.fiber p c v u d) :
    ∃ δ : F.Γ v u, d.1 ≤ (F.identity v u δ).maxOrder ∧
      γ.coeff = F.flux p c v u δ d.1 := by
  classical
  obtain ⟨δ, _hδ, he⟩ := List.mem_filterMap.mp hγ
  split_ifs at he with hd
  · cases he
    exact ⟨δ, hd, rfl⟩

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
open Homogenization MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! Time measurability and exact transverse invariance survive the lift reparametrization. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftEdges_transverse (c lam : ℝ) (edge : ConstituentEdges D h)
    (par : Fin 2) (S T : Set ℝ) (hclock : ∀ t ∈ S, c * t ∈ T)
    (ht : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsTransverseOn par T (γ.coeff α)) :
    ∀ v u d, ∀ γ ∈ liftEdges c lam edge v u d, ∀ α,
      IsTransverseOn par S (γ.coeff α) := by
  intro v u d γ hγ α t htS X z r
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
  exact ht v u d δ hδ α (c * t) (hclock t htS) (lam • X) z r

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! The composition estimate preserves the positive input derivative needed for dissipation. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_sub_const_of_ne (j : ℕ) (hj : j ≠ 0)
    (f : Vec 2 → E) (hf : ContDiff ℝ (j : ℕ∞) f) (c : E) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => f y - c) x‖ = ‖iteratedFDeriv ℝ j f x‖ := by
  change ‖iteratedFDeriv ℝ j (f - fun _ => c) x‖ = _
  rw [iteratedFDeriv_sub_apply hf.contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne hj]
  simp only [Pi.zero_apply, sub_zero]

theorem positive_chart_input_jet_sum_bound {n : ℕ}
    (f : Vec 2 → E) (hf : ContDiff ℝ (n : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ (n : ℕ∞) Φ)
    {C ρ : ℝ} (hC : 1 ≤ C) (hρ : 0 < ρ) (hJ : ChartTransport.JetBound Φ n C ρ)
    (X x : Vec 2) (hΦX : Φ X = x) :
    (∑ j ∈ Finset.range (n + 1),
      if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (f ∘ Φ) X‖) ≤
      ChartTransport.compConst C n * ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
  let f₀ : Vec 2 → E := fun y => f y - f x
  have hf₀ : ContDiff ℝ (n : ℕ∞) f₀ := hf.sub contDiff_const
  have hb := ChartTransport.comp_sum_bound hf₀ hΦ hC hρ le_rfl hJ X
  rw [hΦX] at hb
  have hl (j : ℕ) (hj : j ≤ n) :
      ρ ^ j * ‖iteratedFDeriv ℝ j (f₀ ∘ Φ) X‖ =
        if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (f ∘ Φ) X‖ := by
    by_cases hj0 : j = 0
    · subst j
      rw [ite_eq_left rfl, pow_zero, one_mul, norm_iteratedFDeriv_zero]
      change ‖f (Φ X) - f x‖ = 0
      rw [hΦX, sub_self, norm_zero]
    · rw [ite_eq_right hj0]
      change ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => (f ∘ Φ) y - f x) X‖ = _
      rw [norm_iteratedFDeriv_sub_const_of_ne j hj0 (f ∘ Φ)
        ((hf.comp hΦ).of_le (by exact_mod_cast hj))]
  have hr (j : ℕ) (hj : j ≤ n) :
      ρ ^ j * ‖iteratedFDeriv ℝ j f₀ x‖ =
        if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
    by_cases hj0 : j = 0
    · subst j
      rw [ite_eq_left rfl, pow_zero, one_mul, norm_iteratedFDeriv_zero]
      change ‖f x - f x‖ = 0
      rw [sub_self, norm_zero]
    · rw [ite_eq_right hj0]
      change ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => f y - f x) x‖ = _
      rw [norm_iteratedFDeriv_sub_const_of_ne j hj0 f (hf.of_le (by exact_mod_cast hj))]
  have hls : (∑ j ∈ Finset.range (n + 1), ρ ^ j * ‖iteratedFDeriv ℝ j (f₀ ∘ Φ) X‖) =
      ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (f ∘ Φ) X‖ :=
    Finset.sum_congr rfl (fun j hj => hl j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  have hrs : (∑ j ∈ Finset.range (n + 1), ρ ^ j * ‖iteratedFDeriv ℝ j f₀ x‖) =
      ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ :=
    Finset.sum_congr rfl (fun j hj => hr j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  rw [hls, hrs] at hb
  exact hb

end AVRegularity.Construction.Preservation.FullLift
end
end
