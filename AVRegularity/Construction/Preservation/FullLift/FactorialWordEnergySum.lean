-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.Construction.Preservation.Buffer.ShiftedEnergyEndpoint
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.Statements.Intermediate.CycleOutput.LiftEdges
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyP
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyQ
public import AVRegularity.Statements.Intermediate.KernelEnergy.SchurBound
public import AVRegularity.EntryWeak.WeakCarrierAppend
public import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleComparison.Residual.Jets.Lift
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Higher coefficient seminorms approach their order-zero budget at least linearly in radius. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientSeminorm_order_zero_slope {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 < R)
    (hρR : ρ ≤ R) (K : ℕ) (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F) :
    coefficientSeminorm ρ K a b A ≤ coefficientSeminorm ρ 0 a b A +
      ENNReal.ofReal (ρ / R) * coefficientSeminorm R K a b A := by
  classical
  let M (n : ℕ) : ℝ≥0∞ :=
    ⨆ t ∈ Set.Icc a b, ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) n x‖₊ : ℝ≥0∞)
  have hz : coefficientSeminorm ρ 0 a b A = M 0 := by
    unfold coefficientSeminorm
    rw [Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, Nat.factorial_zero, Nat.cast_one, pow_zero,
      div_one, ENNReal.ofReal_one, one_mul, zero_add]
    rfl
  have hs : ∀ n ∈ Finset.range (K + 1),
      ENNReal.ofReal (ρ ^ n / (n.factorial : ℝ)) * M n ≤
        (if n = 0 then M 0 else 0) + ENNReal.ofReal (ρ / R) *
          (ENNReal.ofReal (R ^ n / (n.factorial : ℝ)) * M n) := by
    intro n _
    by_cases hn : n = 0
    · subst n
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        ENNReal.ofReal_one, one_mul, ↓reduceIte]
      exact le_self_add
    · simp only [hn, ↓reduceIte, zero_add]
      have hp := div_le_div_of_nonneg_right (radius_power_linear_bound hρ hR hρR n (by omega))
        (show (0 : ℝ) ≤ (n.factorial : ℝ) by positivity)
      have hw : ENNReal.ofReal (ρ ^ n / (n.factorial : ℝ)) ≤
          ENNReal.ofReal (ρ / R) * ENNReal.ofReal (R ^ n / (n.factorial : ℝ)) := by
        rw [← ENNReal.ofReal_mul (div_nonneg hρ hR.le)]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_div_assoc] using hp
      exact (mul_le_mul_of_nonneg_right hw zero_le).trans_eq (mul_assoc _ _ _)
  have hsum : (∑ n ∈ Finset.range (K + 1), if n = 0 then M 0 else 0) = M 0 := by
    rw [Finset.sum_eq_single 0]
    · simp only [↓reduceIte]
    · intro n _ hn
      simp only [hn, ↓reduceIte]
    · intro hn
      exact (hn (Finset.mem_range.mpr (Nat.succ_pos K))).elim
  unfold coefficientSeminorm
  change (∑ n ∈ Finset.range (K + 1), ENNReal.ofReal (ρ ^ n / (n.factorial : ℝ)) * M n) ≤ _
  calc
    _ ≤ ∑ n ∈ Finset.range (K + 1), ((if n = 0 then M 0 else 0) +
        ENNReal.ofReal (ρ / R) * (ENNReal.ofReal (R ^ n / (n.factorial : ℝ)) * M n)) :=
      Finset.sum_le_sum hs
    _ = M 0 + ENNReal.ofReal (ρ / R) *
        ∑ n ∈ Finset.range (K + 1), ENNReal.ofReal (R ^ n / (n.factorial : ℝ)) * M n := by
      rw [Finset.sum_add_distrib, hsum, ← Finset.mul_sum]
    _ = _ := by rw [← hz]; rfl

end AVRegularity.Construction.Preservation.FullLift
end

section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The inflated birth-price matrix at effective mass is exactly its marked conjugate. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pricedRecordMajorant_effective_mass (F : ChartedFamily ι h D P Ctx)
    (π w : ι → ℝ) (hπ : ∀ i, 0 < π i) (hw : ∀ i, 0 < w i) (v u : ι) :
    pricedRecordMajorant (fun i => π i / w i ^ 2) (fun _ => 1) F v u =
      pricedRecordMajorant π w F v u := by
  unfold pricedRecordMajorant
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul]
  rw [sqrt_effective_mass_ratio (hπ u).le (hπ v) (hw u) (hw v)]

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Positive derivative composition at any weight below the chart radius. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positive_chart_input_jet_sum_bound_of_le {n : ℕ}
    (f : Vec 2 → E) (hf : ContDiff ℝ (n : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ (n : ℕ∞) Φ)
    {C ρ s : ℝ} (hC : 1 ≤ C) (hs : 0 < s) (hsρ : s ≤ ρ) (hJ : ChartTransport.JetBound Φ n C ρ)
    (X x : Vec 2) (hΦX : Φ X = x) :
    (∑ j ∈ Finset.range (n + 1),
      if j = 0 then 0 else s ^ j * ‖iteratedFDeriv ℝ j (f ∘ Φ) X‖) ≤
      ChartTransport.compConst C n * ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else s ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
  let f₀ : Vec 2 → E := fun y => f y - f x
  have hf₀ : ContDiff ℝ (n : ℕ∞) f₀ := hf.sub contDiff_const
  have hb := ChartTransport.comp_sum_bound hf₀ hΦ hC hs hsρ hJ X
  rw [hΦX] at hb
  have hl (j : ℕ) (hj : j ≤ n) :
      s ^ j * ‖iteratedFDeriv ℝ j (f₀ ∘ Φ) X‖ =
        if j = 0 then 0 else s ^ j * ‖iteratedFDeriv ℝ j (f ∘ Φ) X‖ := by
    by_cases hj0 : j = 0
    · subst j
      rw [ite_eq_left rfl, pow_zero, one_mul, norm_iteratedFDeriv_zero]
      change ‖f (Φ X) - f x‖ = 0
      rw [hΦX, sub_self, norm_zero]
    · rw [ite_eq_right hj0]
      change s ^ j * ‖iteratedFDeriv ℝ j (fun y => (f ∘ Φ) y - f x) X‖ = _
      rw [norm_iteratedFDeriv_sub_const_of_ne j hj0 (f ∘ Φ)
        ((hf.comp hΦ).of_le (by exact_mod_cast hj))]
  have hr (j : ℕ) (hj : j ≤ n) :
      s ^ j * ‖iteratedFDeriv ℝ j f₀ x‖ =
        if j = 0 then 0 else s ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
    by_cases hj0 : j = 0
    · subst j
      rw [ite_eq_left rfl, pow_zero, one_mul, norm_iteratedFDeriv_zero]
      change ‖f x - f x‖ = 0
      rw [sub_self, norm_zero]
    · rw [ite_eq_right hj0]
      change s ^ j * ‖iteratedFDeriv ℝ j (fun y => f y - f x) x‖ = _
      rw [norm_iteratedFDeriv_sub_const_of_ne j hj0 f (hf.of_le (by exact_mod_cast hj))]
  have hls : (∑ j ∈ Finset.range (n + 1), s ^ j * ‖iteratedFDeriv ℝ j (f₀ ∘ Φ) X‖) =
      ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else s ^ j * ‖iteratedFDeriv ℝ j (f ∘ Φ) X‖ :=
    Finset.sum_congr rfl (fun j hj => hl j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  have hrs : (∑ j ∈ Finset.range (n + 1), s ^ j * ‖iteratedFDeriv ℝ j f₀ x‖) =
      ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else s ^ j * ‖iteratedFDeriv ℝ j f x‖ :=
    Finset.sum_congr rfl (fun j hj => hr j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  rw [hls, hrs] at hb
  exact hb

/-- Composition preserves one unweighted derivative without introducing the zero input jet. -/
theorem positive_chart_input_gradient_sum_bound {n : ℕ}
    (f : Vec 2 → E) (hf : ContDiff ℝ (n : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ (n : ℕ∞) Φ)
    {C ρ s : ℝ} (hC : 1 ≤ C) (hs : 0 < s) (hsρ : s ≤ ρ)
    (hJ : ChartTransport.JetBound Φ n C ρ) (X x : Vec 2) (hΦX : Φ X = x) :
    (∑ j ∈ Finset.range (n + 1),
      if j = 0 then 0 else s ^ (j - 1) * ‖iteratedFDeriv ℝ j (f ∘ Φ) X‖) ≤
      ChartTransport.compConst C n * ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else s ^ (j - 1) * ‖iteratedFDeriv ℝ j f x‖ := by
  have hb := positive_chart_input_jet_sum_bound_of_le f hf Φ hΦ hC hs hsρ hJ X x hΦX
  have hfactor (F : Vec 2 → E) (y : Vec 2) :
      s * (∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else s ^ (j - 1) * ‖iteratedFDeriv ℝ j F y‖) =
      ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else s ^ j * ‖iteratedFDeriv ℝ j F y‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = 0
    · simp only [ite_eq_left hj, mul_zero]
    · simp only [ite_eq_right hj]
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj)]
  apply (mul_le_mul_iff_right₀ hs).mp
  rw [hfactor, mul_left_comm s, hfactor]
  exact hb

end AVRegularity.Construction.Preservation.FullLift
end

section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual chart fiber inherits the identity graph's path depth. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem chartedFiber_empty_of_identity_empty (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (he : IsEmpty (F.Γ v u))
    (d : Finset.Icc 2 D) : F.fiber p c v u d = [] := by
  let := he
  simp [ChartedFamily.fiber]

theorem chartedFiber_depth (F : ChartedFamily ι h D P Ctx) (p : P) (c : Ctx p)
    {H : ℕ} (hd : F.HasDepthAtMost H) : HasDepthAtMost (F.fiber p c) H := by
  intro path
  obtain ⟨k, hk⟩ := hd path
  exact ⟨k, fun d => chartedFiber_empty_of_identity_empty F p c _ _ hk d⟩

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! A covariance power consumes exactly twice its degree from the classical reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covOperator_iterate_contDiff (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (r n : ℕ) (u : Vec 2 → E) (hu : ContDiff ℝ ((n + 2 * r : ℕ) : ℕ∞) u) :
    ContDiff ℝ (n : ℕ∞) ((covOperator Hc)^[r] u) := by
  induction r generalizing n with
  | zero => simpa only [Function.iterate_zero_apply, mul_zero, add_zero] using hu
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    apply covOperator_contDiff Hc n
    apply ih
    simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hu

theorem covOperator_iterate_periodic (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (r : ℕ) (u : Vec 2 → E) (hu : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) u)
    (hp : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic ((covOperator Hc)^[r] u) := by
  induction r with
  | zero => simpa only [Function.iterate_zero_apply] using hp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have hmid : ContDiff ℝ 2 ((covOperator Hc)^[r] u) := by
      apply covOperator_iterate_contDiff Hc r 2
      simpa only [Nat.mul_succ, Nat.add_comm] using hu
    have hulow : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) u :=
      hu.of_le (by exact_mod_cast (by omega : 2 * r ≤ 2 * (r + 1)))
    exact covOperator_periodic Hc _ hmid (ih hulow)

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual stored L2 jet norm square equals its lower integral. -/

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ofReal_L2_norm_sq_eq_lintegral (u : Lp E 2 μ) :
    ENNReal.ofReal (‖u‖ ^ 2) = ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ := by
  have heq : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [heq, ofReal_integral_eq_lintegral_ofReal (Lp.memLp u).norm.integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! Copy-adapt the bounded contour argument to simultaneous slow and fast parameters. -/

open AVRegularity.Construction.Preservation.Buffer

theorem localized_joint_cauchy_regular {d : ℕ}
    (R : ℝ) (hR : 0 < R) (χ : Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hb : ∀ x, ‖χ x‖ ≤ R / 2)
    (hzero : χ 0 = 0) (hout : ∀ x, R / 2 ≤ ‖x‖ → χ x = 0)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (n : ℕ) (L : Vec d →L[ℝ] Vec 2)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∀ (f : (ℝ × ℝ) → Vec d → ℂ),
        (∀ x, Measurable (fun p => f p x)) →
        (∀ p, ContDiff ℝ (n : ℕ∞) (f p)) → ∀ M : ℝ, 0 ≤ M →
        (∀ j ≤ n, ∀ p x, ‖iteratedFDeriv ℝ j (f p) x‖ ≤ A j * M) →
        ContDiff ℝ (n : ℕ∞) (fun x => ∫ p, f p x * localizedCauchyKernel R χ (p, L x) ∂μ) := by
  choose C hC hCb using fun j =>
    localized_cauchy_kernel_exists_global_jet_bound R hR χ hχ hb hzero hout j
  let Q : ℕ → ℝ := fun j => ∑ l ∈ Finset.range (j + 1),
    (j.choose l : ℝ) * A l * (C (j - l) * ‖L‖ ^ (j - l))
  intro f hm hs M hM hf
  let g : (ℝ × ℝ) → Vec d → ℂ := fun p x => f p x * localizedCauchyKernel R χ (p, L x)
  have hk := localized_cauchy_kernel_contDiff R hR χ hχ hb
  have hks (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞)
      (fun x : Vec d => localizedCauchyKernel R χ (p, L x)) :=
    ((hk.comp (contDiff_const.prodMk contDiff_id)).comp L.contDiff).of_le (by simp)
  have hkernel (j : ℕ) (p : ℝ × ℝ) (x : Vec d) :
      ‖iteratedFDeriv ℝ j (fun y : Vec d => localizedCauchyKernel R χ (p, L y)) x‖ ≤
        C j * ‖L‖ ^ j := by
    have hs : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => localizedCauchyKernel R χ (p, y)) :=
      hk.comp (contDiff_const.prodMk contDiff_id)
    change ‖iteratedFDeriv ℝ j ((fun y => localizedCauchyKernel R χ (p, y)) ∘ L) x‖ ≤ _
    rw [L.iteratedFDeriv_comp_right hs x (by simp)]
    have hh : ‖(iteratedFDeriv ℝ j (fun y : Vec 2 => localizedCauchyKernel R χ (p, y))
        (L x)).compContinuousLinearMap (fun _ => L)‖ ≤
        ‖iteratedFDeriv ℝ j (fun y : Vec 2 => localizedCauchyKernel R χ (p, y)) (L x)‖ * ‖L‖ ^ j := by
      simpa using (iteratedFDeriv ℝ j (fun y : Vec 2 => localizedCauchyKernel R χ (p, y))
        (L x)).norm_compContinuousLinearMap_le (fun _ => L)
    exact hh.trans (mul_le_mul_of_nonneg_right (hCb j p.1 p.2 (L x)) (by positivity))
  have hgs (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞) (g p) := (hs p).mul (hks p)
  have hgm (x : Vec d) : Measurable (fun p => g p x) :=
    (hm x).mul ((hk.continuous.comp (continuous_id.prodMk continuous_const)).measurable)
  have hgb : ∀ j ≤ n, ∀ p x, ‖iteratedFDeriv ℝ j (g p) x‖ ≤ Q j * M := by
    intro j hj p x
    apply (norm_iteratedFDeriv_mul_le (hs p) (hks p) x (by exact_mod_cast hj)).trans
    calc
      _ ≤ ∑ l ∈ Finset.range (j + 1),
          (j.choose l : ℝ) * (A l * M) * (C (j - l) * ‖L‖ ^ (j - l)) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' : l ≤ n := le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hl)) hj
        have hAl := hA l
        apply mul_le_mul
          (mul_le_mul_of_nonneg_left (hf l hl' p x) (by positivity))
          (hkernel (j - l) p x) (norm_nonneg _) (by positivity)
      _ = Q j * M := by
        dsimp only [Q]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ring
  exact finite_parameter_integral_contDiff μ n ℂ g hgm hgs
    (fun j => Q j * M) hgb

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! A positive physical jet density controls any spatial word with one unweighted derivative. -/

open ChartTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem physical_positive_jet_density_word_le {U r : ℕ} (hr0 : 1 ≤ r) (hrU : r ≤ U)
    (f : Vec 2 → E) (hf : ContDiff ℝ (U : ℕ∞) f)
    {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) (β : DerivativeWord2 r) (x : Vec 2) :
    s ^ (r - 1) * ‖orderedDerivative β f x‖ ≤
      ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        ρ ^ (j - 1) * ‖iteratedFDeriv ℝ j f x‖ := by
  have hword := norm_orderedDerivative_le (hf.of_le (by exact_mod_cast hrU)) β x
  have hp := pow_le_pow_left₀ hs.le hsρ (r - 1)
  have hsingle := Finset.single_le_sum
    (f := fun j => if j = 0 then 0 else ρ ^ (j - 1) * ‖iteratedFDeriv ℝ j f x‖)
    (fun j _ => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (pow_nonneg (hs.trans_le hsρ).le _) (norm_nonneg _))
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hrU))
  have hb : ρ ^ (r - 1) * ‖iteratedFDeriv ℝ r f x‖ ≤
      ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        ρ ^ (j - 1) * ‖iteratedFDeriv ℝ j f x‖ := by
    simpa only [ite_eq_right (show r ≠ 0 by omega)] using hsingle
  exact ((mul_le_mul_of_nonneg_left hword (pow_nonneg hs.le _)).trans
    (mul_le_mul_of_nonneg_right hp (norm_nonneg _))).trans hb

theorem physical_positive_jet_density_dissipation_le {U r : ℕ}
    (hr0 : 1 ≤ r) (hrU : r ≤ U) (f : Vec 2 → E) (hf : ContDiff ℝ (U : ℕ∞) f)
    {s ρ ν B : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) (hνB : ν ≤ B)
    (β : DerivativeWord2 r) (x : Vec 2) :
    Real.sqrt ν * (s ^ (r - 1) * ‖orderedDerivative β f x‖) ≤
      Real.sqrt B * (∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
        ρ ^ (j - 1) * ‖iteratedFDeriv ℝ j f x‖) := by
  have hb := physical_positive_jet_density_word_le hr0 hrU f hf hs hsρ β x
  have hd : 0 ≤ ∑ j ∈ Finset.range (U + 1), if j = 0 then 0 else
      ρ ^ (j - 1) * ‖iteratedFDeriv ℝ j f x‖ :=
    Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (pow_nonneg (hs.trans_le hsρ).le _) (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg ν)).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hνB) hd)

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Rescaling the pulled-back input exactly restores its physical weighted jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_chart_dilated_input_jet (j : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (j : ℕ∞) f) (Φ : Vec 2 → Vec 2)
    (hΦ : ContDiff ℝ (j : ℕ∞) Φ) {ρ : ℝ} (hρ : 0 < ρ) (y : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖ =
      ρ ^ j * ‖iteratedFDeriv ℝ j (f ∘ Φ) y‖ := by
  have hh := CycleComparison.Lift.norm_iteratedFDeriv_dilation_smul
    j ρ 1 (f ∘ Φ) (hf.comp hΦ) (ρ⁻¹ • y)
  simpa only [one_smul, abs_one, one_mul, abs_of_pos hρ, smul_smul,
    mul_inv_cancel₀ hρ.ne', Function.comp_def] using hh

theorem chart_dilated_input_jet_sum_bound {n : ℕ}
    (f : Vec 2 → E) (hf : ContDiff ℝ (n : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ (n : ℕ∞) Φ)
    {C ρ : ℝ} (hC : 1 ≤ C) (hρ : 0 < ρ) (hJ : ChartTransport.JetBound Φ n C ρ)
    (y x : Vec 2) (hΦy : Φ y = x) :
    (∑ j ∈ Finset.range (n + 1),
      ‖iteratedFDeriv ℝ j (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖) ≤
      ChartTransport.compConst C n * ∑ j ∈ Finset.range (n + 1),
        ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
  have he : (∑ j ∈ Finset.range (n + 1),
      ‖iteratedFDeriv ℝ j (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖) =
      ∑ j ∈ Finset.range (n + 1), ρ ^ j * ‖iteratedFDeriv ℝ j (f ∘ Φ) y‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact norm_chart_dilated_input_jet j f (hf.of_le (by exact_mod_cast hjn))
      Φ (hΦ.of_le (by exact_mod_cast hjn)) hρ y
  rw [he]
  have hb := ChartTransport.comp_sum_bound hf hΦ hC hρ le_rfl hJ y
  simpa only [hΦy] using hb

theorem positive_chart_dilated_input_jet_sum_bound {n : ℕ}
    (f : Vec 2 → E) (hf : ContDiff ℝ (n : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ (n : ℕ∞) Φ)
    {C ρ : ℝ} (hC : 1 ≤ C) (hρ : 0 < ρ) (hJ : ChartTransport.JetBound Φ n C ρ)
    (y x : Vec 2) (hΦy : Φ y = x) :
    (∑ j ∈ Finset.range (n + 1), if j = 0 then 0 else
      ‖iteratedFDeriv ℝ j (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖) ≤
      ChartTransport.compConst C n * ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
  have he : (∑ j ∈ Finset.range (n + 1), if j = 0 then 0 else
      ‖iteratedFDeriv ℝ j (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖) =
      ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j (f ∘ Φ) y‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hd := norm_chart_dilated_input_jet j f (hf.of_le (by exact_mod_cast hjn))
      Φ (hΦ.of_le (by exact_mod_cast hjn)) hρ y
    rw [hd]
  rw [he]
  exact positive_chart_input_jet_sum_bound f hf Φ hΦ hC hρ hJ y x hΦy

theorem chart_dilated_input_finite_density_bound {n : ℕ}
    (f : Vec 2 → E) (hf : ContDiff ℝ (n : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ (n : ℕ∞) Φ)
    {C ρ : ℝ} (hC : 1 ≤ C) (hρ : 0 < ρ) (hJ : ChartTransport.JetBound Φ n C ρ)
    (y x : Vec 2) (hΦy : Φ y = x) (m : ℕ) (hm : m ≤ n) :
    (∑ j : Fin (m + 1),
      ‖iteratedFDeriv ℝ j.1 (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖) ≤
      ChartTransport.compConst C n * ∑ j ∈ Finset.range (n + 1),
        ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => ‖iteratedFDeriv ℝ j (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖) (m + 1)]
  apply (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.succ_le_succ hm)) (fun _ _ _ => norm_nonneg _)).trans
  exact chart_dilated_input_jet_sum_bound f hf Φ hΦ hC hρ hJ y x hΦy

theorem positive_chart_dilated_input_finite_density_bound {n : ℕ}
    (f : Vec 2 → E) (hf : ContDiff ℝ (n : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ (n : ℕ∞) Φ)
    {C ρ : ℝ} (hC : 1 ≤ C) (hρ : 0 < ρ) (hJ : ChartTransport.JetBound Φ n C ρ)
    (y x : Vec 2) (hΦy : Φ y = x) (m : ℕ) (hm : m ≤ n) :
    (∑ j : Fin (m + 1), if j.1 = 0 then 0 else
      ‖iteratedFDeriv ℝ j.1 (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖) ≤
      ChartTransport.compConst C n * ∑ j ∈ Finset.range (n + 1),
        if j = 0 then 0 else ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if j = 0 then 0 else
      ‖iteratedFDeriv ℝ j (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖) (m + 1)]
  have hnonneg (j : ℕ) : 0 ≤ (if j = 0 then 0 else
      ‖iteratedFDeriv ℝ j (fun Y => f (Φ (ρ • Y))) (ρ⁻¹ • y)‖) := by
    split_ifs <;> first | exact le_rfl | exact norm_nonneg _
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.succ_le_succ hm))
    (fun j _ _ => hnonneg j)).trans
    (positive_chart_dilated_input_jet_sum_bound f hf Φ hΦ hC hρ hJ y x hΦy)

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! The radius-slope estimate in the real-valued prices consumed by the kernel Schur matrix. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientSeminorm_real_slope {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 < R)
    (hρR : ρ ≤ R) (K : ℕ) (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : coefficientSeminorm R K a b A ≠ ⊤) :
    (coefficientSeminorm ρ K a b A).toReal ≤ (coefficientSeminorm ρ 0 a b A).toReal +
      (ρ / R) * (coefficientSeminorm R K a b A).toReal := by
  have hzero : coefficientSeminorm ρ 0 a b A ≠ ⊤ :=
    ne_top_of_le_ne_top hA ((coefficientSeminorm_order_zero_radius ρ R a b A).le.trans
      (coefficientSeminorm_order_mono R (Nat.zero_le K) a b A))
  have hm : ENNReal.ofReal (ρ / R) * coefficientSeminorm R K a b A ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  have hb := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hzero, hm⟩)
    (coefficientSeminorm_order_zero_slope hρ hR hρR K a b A)
  rw [ENNReal.toReal_add hzero hm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg hρ hR.le)] at hb
  exact hb

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Price only actual constituents against their original record, independent of the component count. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem liftedFiber_record_jet_price_le (F : ChartedFamily ι h D P Ctx)
    (p : P) (ctx : Ctx p) (v u : ι) (d : Finset.Icc 2 D)
    (S : Set ℝ) (clock lam K : ℝ) (hK : 0 ≤ K) (r q : ℕ)
    (θ : F.Γ v u → DerivativeWord2 (d.1 - 1) → Fin 2 → ℝ)
    (hθ : ∀ δ I c, 0 ≤ θ δ I c)
    (hrecord : ∀ δ, d.1 ≤ (F.identity v u δ).maxOrder →
      ∑ I, ∑ c, θ δ I c ≤ (F.identity v u δ).record.size)
    (hjet : ∀ δ, d.1 ≤ (F.identity v u δ).maxOrder → ∀ I,
      jetSup S r q (fun t X z => F.flux p ctx v u δ d.1 I (clock * t) (lam • X) z) ≤
        ENNReal.ofReal (K * ∑ c, θ δ I c)) :
    (((liftEdges clock lam (F.fiber p ctx)) v u d).map fun γ =>
      ENNReal.ofReal ‖γ.map‖ * ∑ I, jetSup S r q (γ.coeff I)).sum ≤
      ENNReal.ofReal (K * ∑ δ, ‖(F.identity v u δ).map‖ * (F.identity v u δ).record.size) := by
  classical
  let price (δ : F.Γ v u) := ENNReal.ofReal
    (K * (‖(F.identity v u δ).map‖ * (F.identity v u δ).record.size))
  have hs : ((Finset.univ.toList : List (F.Γ v u)).map price).sum =
      ENNReal.ofReal (K * ∑ δ, ‖(F.identity v u δ).map‖ * (F.identity v u δ).record.size) := by
    rw [Finset.sum_map_toList]
    dsimp only [price]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun δ _ => mul_nonneg hK
      (mul_nonneg (norm_nonneg _) (F.identity v u δ).record.size_nonneg)), ← Finset.mul_sum]
  apply le_trans _ (le_of_eq hs)
  unfold liftEdges ChartedFamily.fiber
  rw [List.map_map]
  apply filteredList_positive_sum_le
  intro δ γ hγ
  split_ifs at hγ with hd
  · cases hγ
    dsimp only [Function.comp_def, price]
    calc
      _ ≤ ENNReal.ofReal ‖(F.identity v u δ).map‖ *
          ∑ I, ENNReal.ofReal (K * ∑ c, θ δ I c) :=
        mul_le_mul_right (Finset.sum_le_sum (fun I _ => hjet δ hd I)) _
      _ = ENNReal.ofReal (K * (‖(F.identity v u δ).map‖ * ∑ I, ∑ c, θ δ I c)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun I _ => mul_nonneg hK
          (Finset.sum_nonneg (fun c _ => hθ δ I c))),
          ← ENNReal.ofReal_mul (norm_nonneg _), ← Finset.mul_sum]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hrecord δ hd) (norm_nonneg _)) hK)

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! Uniform quantitative joint jets of the same bounded contour integral. -/

open AVRegularity.Construction.Preservation.Buffer

theorem localized_joint_cauchy_exists_jet_bounds {d : ℕ}
    (R : ℝ) (hR : 0 < R) (χ : Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hb : ∀ x, ‖χ x‖ ≤ R / 2)
    (hzero : χ 0 = 0) (hout : ∀ x, R / 2 ≤ ‖x‖ → χ x = 0)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (n : ℕ) (L : Vec d →L[ℝ] Vec 2)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ Q : ℕ → ℝ, (∀ j, 0 ≤ Q j) ∧
      ∀ (f : (ℝ × ℝ) → Vec d → ℂ),
        (∀ x, Measurable (fun p => f p x)) →
        (∀ p, ContDiff ℝ (n : ℕ∞) (f p)) → ∀ M : ℝ, 0 ≤ M →
        (∀ j ≤ n, ∀ p x, ‖iteratedFDeriv ℝ j (f p) x‖ ≤ A j * M) →
        ContDiff ℝ (n : ℕ∞) (fun x => ∫ p, f p x * localizedCauchyKernel R χ (p, L x) ∂μ) ∧
        ∀ j ≤ n, ∀ x,
          ‖iteratedFDeriv ℝ j (fun x => ∫ p, f p x * localizedCauchyKernel R χ (p, L x) ∂μ) x‖ ≤
            (Q j * M) * μ.real Set.univ := by
  choose C hC hCb using fun j =>
    localized_cauchy_kernel_exists_global_jet_bound R hR χ hχ hb hzero hout j
  let Q : ℕ → ℝ := fun j => ∑ l ∈ Finset.range (j + 1),
    (j.choose l : ℝ) * A l * (C (j - l) * ‖L‖ ^ (j - l))
  have hQ (j : ℕ) : 0 ≤ Q j := by
    apply Finset.sum_nonneg
    intro l _
    have hl := hA l
    have hc := hC (j - l)
    positivity
  refine ⟨Q, hQ, ?_⟩
  intro f hm hs M hM hf
  let g : (ℝ × ℝ) → Vec d → ℂ := fun p x => f p x * localizedCauchyKernel R χ (p, L x)
  have hk := localized_cauchy_kernel_contDiff R hR χ hχ hb
  have hks (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞)
      (fun x : Vec d => localizedCauchyKernel R χ (p, L x)) :=
    ((hk.comp (contDiff_const.prodMk contDiff_id)).comp L.contDiff).of_le (by simp)
  have hkernel (j : ℕ) (p : ℝ × ℝ) (x : Vec d) :
      ‖iteratedFDeriv ℝ j (fun y : Vec d => localizedCauchyKernel R χ (p, L y)) x‖ ≤
        C j * ‖L‖ ^ j := by
    have hs : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => localizedCauchyKernel R χ (p, y)) :=
      hk.comp (contDiff_const.prodMk contDiff_id)
    change ‖iteratedFDeriv ℝ j ((fun y => localizedCauchyKernel R χ (p, y)) ∘ L) x‖ ≤ _
    rw [L.iteratedFDeriv_comp_right hs x (by simp)]
    have hh : ‖(iteratedFDeriv ℝ j (fun y : Vec 2 => localizedCauchyKernel R χ (p, y))
        (L x)).compContinuousLinearMap (fun _ => L)‖ ≤
        ‖iteratedFDeriv ℝ j (fun y : Vec 2 => localizedCauchyKernel R χ (p, y)) (L x)‖ * ‖L‖ ^ j := by
      simpa using (iteratedFDeriv ℝ j (fun y : Vec 2 => localizedCauchyKernel R χ (p, y))
        (L x)).norm_compContinuousLinearMap_le (fun _ => L)
    exact hh.trans (mul_le_mul_of_nonneg_right (hCb j p.1 p.2 (L x)) (by positivity))
  have hgs (p : ℝ × ℝ) : ContDiff ℝ (n : ℕ∞) (g p) := (hs p).mul (hks p)
  have hgm (x : Vec d) : Measurable (fun p => g p x) :=
    (hm x).mul ((hk.continuous.comp (continuous_id.prodMk continuous_const)).measurable)
  have hgb : ∀ j ≤ n, ∀ p x, ‖iteratedFDeriv ℝ j (g p) x‖ ≤ Q j * M := by
    intro j hj p x
    apply (norm_iteratedFDeriv_mul_le (hs p) (hks p) x (by exact_mod_cast hj)).trans
    calc
      _ ≤ ∑ l ∈ Finset.range (j + 1),
          (j.choose l : ℝ) * (A l * M) * (C (j - l) * ‖L‖ ^ (j - l)) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' : l ≤ n := le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hl)) hj
        have hAl := hA l
        apply mul_le_mul
          (mul_le_mul_of_nonneg_left (hf l hl' p x) (by positivity))
          (hkernel (j - l) p x) (norm_nonneg _) (by positivity)
      _ = Q j * M := by
        dsimp only [Q]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ring
  refine ⟨finite_parameter_integral_contDiff μ n ℂ g hgm hgs
    (fun j => Q j * M) hgb, ?_⟩
  intro j hj x
  exact finite_parameter_integral_jet_norm_le μ j ℂ g hgm
    (fun p => (hgs p).of_le (by exact_mod_cast hj)) (fun l => Q l * M)
    (fun l hl p y => hgb l (hl.trans hj) p y) x

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Inverse chart transport of a derivative word retains a positive input derivative. -/

open ChartTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positive_chart_word_gradient_bound {r : ℕ} (hr : 1 ≤ r)
    (f : Vec 2 → E) (hf : ContDiff ℝ (r : ℕ∞) f)
    (Φ : Vec 2 → Vec 2) (hΦ : ContDiff ℝ (r : ℕ∞) Φ)
    {C ρ s : ℝ} (hC : 1 ≤ C) (hs : 0 < s) (hsρ : s ≤ ρ)
    (hJ : JetBound Φ r C ρ) (β : DerivativeWord2 r) (X : Vec 2) :
    s ^ (r - 1) * ‖orderedDerivative β (f ∘ Φ) X‖ ≤
      compConst C r * ∑ j ∈ Finset.range (r + 1),
        if j = 0 then 0 else ∑ w : DerivativeWord2 j,
          s ^ (j - 1) * ‖orderedDerivative w f (Φ X)‖ := by
  have hb := positive_chart_input_gradient_sum_bound f hf Φ hΦ hC hs hsρ hJ X (Φ X) rfl
  have hword := norm_orderedDerivative_le (hf.comp hΦ) β X
  have hsingle : s ^ (r - 1) * ‖iteratedFDeriv ℝ r (f ∘ Φ) X‖ ≤
      ∑ j ∈ Finset.range (r + 1),
        if j = 0 then 0 else s ^ (j - 1) * ‖iteratedFDeriv ℝ j (f ∘ Φ) X‖ := by
    have h := Finset.single_le_sum
      (f := fun j => if j = 0 then 0 else
        s ^ (j - 1) * ‖iteratedFDeriv ℝ j (f ∘ Φ) X‖)
      (fun j _ => by split_ifs <;> positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_self r))
    simpa only [ite_eq_right (show r ≠ 0 by omega)] using h
  have hsum : (∑ j ∈ Finset.range (r + 1),
      if j = 0 then 0 else s ^ (j - 1) * ‖iteratedFDeriv ℝ j f (Φ X)‖) ≤
      ∑ j ∈ Finset.range (r + 1),
        if j = 0 then 0 else ∑ w : DerivativeWord2 j,
          s ^ (j - 1) * ‖orderedDerivative w f (Φ X)‖ := by
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hj0 : j = 0
    · simp only [ite_eq_left hj0, le_refl]
    · simp only [ite_eq_right hj0]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_le_sum_words
          (hf.of_le (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) _)
        (by positivity)
  exact ((mul_le_mul_of_nonneg_left hword (by positivity)).trans hsingle).trans
    (hb.trans (mul_le_mul_of_nonneg_left hsum (compConst_nonneg hC r)))

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Convert actual real Schur budgets to the fixed matrices used by component time energies. -/

open CycleComparison.Lift
variable {ι : Type*} [Fintype ι]

theorem real_schur_ofReal_col_sum_le {M : ι → ι → ℝ} {C : ℝ}
    (hM : HasRealSchurBudget M C) (K : ℝ≥0∞) (u : ι) :
    (∑ v, K * ENNReal.ofReal (M v u)) ≤ K * ENNReal.ofReal C := by
  rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun v _ => hM.nonneg v u)]
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hM.col_sum u))

variable {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem classicalStrongEnergy_le_of_real_schur_bounds (rs ν ρ B : ℝ) (π : ι → ℝ)
    (I : Set ℝ) (P Q : ℕ) (a b : ℝ → Homogenization.Vec 2 → ∀ i, h i)
    (M₀ M₁ : ι → ι → ℝ) (C₀ C₁ : ℝ) (K₀ K₁ : ℝ≥0∞)
    (hM₀ : HasRealSchurBudget M₀ C₀) (hM₁ : HasRealSchurBudget M₁ C₁)
    (hmeas : ∀ j, AEMeasurable (fun t => ENNReal.ofReal B *
      (ENNReal.ofReal (π j)⁻¹ * classicalGradFactorialSq ρ Q (fun x => b t x j)))
        (volume.restrict I))
    (hvalue : ∀ i, ∀ t ∈ I,
      ENNReal.ofReal (π i)⁻¹ * classicalFactorialSq rs P (fun x => a t x i) ≤
        ∑ j, (K₀ * ENNReal.ofReal (M₀ i j)) * (ENNReal.ofReal (π j)⁻¹ *
          classicalFactorialSq ρ Q (fun x => b t x j)))
    (hgradient : ∀ i, ∀ᵐ t ∂volume.restrict I,
      ENNReal.ofReal ν * (ENNReal.ofReal (π i)⁻¹ *
        classicalGradFactorialSq rs P (fun x => a t x i)) ≤
        ∑ j, (K₁ * ENNReal.ofReal (M₁ i j)) * (ENNReal.ofReal B *
          (ENNReal.ofReal (π j)⁻¹ * classicalGradFactorialSq ρ Q (fun x => b t x j)))) :
    classicalStrongEnergy rs ν π I P a ≤
      (K₀ * ENNReal.ofReal C₀ + K₁ * ENNReal.ofReal C₁) ^ (1 / 2 : ℝ) *
        classicalStrongEnergy ρ B π I Q b := by
  exact classicalStrongEnergy_le_of_matrix_bounds rs ν ρ B π I P Q a b
    (fun i j => K₀ * ENNReal.ofReal (M₀ i j))
    (fun i j => K₁ * ENNReal.ofReal (M₁ i j)) _ _
    (real_schur_ofReal_col_sum_le hM₀ K₀) (real_schur_ofReal_col_sum_le hM₁ K₁)
    hmeas hvalue hgradient

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! The order-zero graph has no weak-derivative constraints, for every Hilbert component. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def torusZeroCarrier (z : Lp E 2 (volume.restrict AVenhance.unitCube)) : TorusHk 0 E := by
  refine ⟨WithLp.toLp 2 (fun _ => z), ?_⟩
  simp only [torusHkGraph, ClosedSubmodule.mem_iInf]
  intro j
  exact Fin.elim0 j

theorem torusZeroCarrier_value (z : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    (torusZeroCarrier z).val (valueIndex2 0) = z := rfl

theorem factorialNormSq_order_zero (ρ : ℝ) (z : TorusHk 0 E) :
    factorialNormSq ρ z.val = ‖z.val (valueIndex2 0)‖ ^ 2 := by
  rw [Buffer.factorialNormSq_zero_eq_derivative]
  unfold derivativeNormSq
  change (∑ w : Fin 0 → Fin 2, ‖z.val ⟨(0 : Fin 1), w⟩‖ ^ 2) = _
  simp only [Fintype.sum_unique]
  rfl

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Reserved regularity of the literal finite covariance polynomials. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def covariancePolynomial (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (a : ℕ → ℝ)
    (u : Vec 2 → E) : Vec 2 → E :=
  fun x => ∑ l ∈ Finset.range (p + 1), a l • ((covOperator Hc)^[l] u) x

theorem covariancePolynomial_contDiff (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p n : ℕ)
    (a : ℕ → ℝ) (u : Vec 2 → E) (hu : ContDiff ℝ ((n + 2 * p : ℕ) : ℕ∞) u) :
    ContDiff ℝ (n : ℕ∞) (covariancePolynomial Hc p a u) := by
  apply ContDiff.sum
  intro l hl
  have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  apply contDiff_const.smul
  apply covOperator_iterate_contDiff Hc l n
  exact hu.of_le (by exact_mod_cast (by omega : n + 2 * l ≤ n + 2 * p))

theorem covariancePolynomial_periodic (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (a : ℕ → ℝ) (u : Vec 2 → E) (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u)
    (hp : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (covariancePolynomial Hc p a u) := by
  intro k x
  apply Finset.sum_congr rfl
  intro l hl
  have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hper := covOperator_iterate_periodic Hc l u
    (hu.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * p))) hp
  exact congrArg (fun z => a l • z) (hper k x)

theorem covariancePolynomial_eq_P (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (u : Vec 2 → E) :
    covariancePolynomial Hc p (fun l => (l.factorial : ℝ)⁻¹) u = covPolyP Hc p u := by
  funext x
  unfold covariancePolynomial covPolyP
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem covariancePolynomial_eq_Q (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (u : Vec 2 → E) :
    covariancePolynomial Hc p (fun l => (-1 : ℝ) ^ l / (l.factorial : ℝ)) u = covPolyQ Hc p u := by
  funext x
  unfold covariancePolynomial covPolyQ
  simp only [Finset.sum_apply, Pi.smul_apply]

end AVRegularity.Construction.Preservation.FullLift
end

section
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Move finite row prices to a fixed matrix and the diffusivity to the source dissipation. -/

variable {ι : Type*} [Fintype ι]

theorem factored_matrix_energy_eq (M : ι → ℝ) (hM : ∀ u, 0 ≤ M u)
    (π : ι → ℝ) (B K C : ℝ≥0∞) (E : ι → ℝ≥0∞) :
    (B * K) * (∑ u, ENNReal.ofReal (M u * (π u)⁻¹) * (C * E u)) =
      ∑ u, (K * C * ENNReal.ofReal (M u)) * (B * (ENNReal.ofReal (π u)⁻¹ * E u)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [ENNReal.ofReal_mul (hM u)]
  ac_rfl

theorem finite_order_price_factor (s : Finset ℕ) (w : ℕ → ℝ≥0∞)
    {B : ℝ} (hB : 0 ≤ B) (D : ℝ) :
    (∑ j ∈ s, w j * ENNReal.ofReal (B * D)) =
      ENNReal.ofReal B * ∑ j ∈ s, w j * ENNReal.ofReal D := by
  simp only [ENNReal.ofReal_mul hB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ac_rfl

end AVRegularity.Construction.Preservation.FullLift
end

section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The single inflated ledger supplies both ordinary and marked effective-mass Schur sums. -/

theorem fullLedger_schur_bound {ι : Type*} [Fintype ι] (b : ι → ι → ℝ) :
    SchurBound (fullLedger b) b := by
  constructor
  · intro v
    exact (le_ciSup (Set.finite_range (fun v => ∑ u, b v u)).bddAbove v).trans (le_max_left _ _)
  · intro u
    exact (le_ciSup (Set.finite_range (fun u => ∑ v, b v u)).bddAbove u).trans (le_max_right _ _)

theorem priced_record_ledger_schur {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (π w : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (hw : ∀ i, 0 < w i) (S : ℝ)
    (hledger : markedLedger π w F ≤ S) :
    SchurBound S (pricedRecordMajorant π (fun _ => 1) F) ∧
      SchurBound S (pricedRecordMajorant (fun i => π i / w i ^ 2) (fun _ => 1) F) := by
  have hmono (b : ι → ι → ℝ) (hb : fullLedger b ≤ S) : SchurBound S b := by
    have hh := fullLedger_schur_bound b
    exact ⟨fun v => (hh.1 v).trans hb, fun u => (hh.2 u).trans hb⟩
  constructor
  · exact hmono _ ((le_max_left _ _).trans hledger)
  · have he : pricedRecordMajorant (fun i => π i / w i ^ 2) (fun _ => 1) F =
        pricedRecordMajorant π w F := by
      funext v u
      exact pricedRecordMajorant_effective_mass F π w hπ hw v u
    rw [he]
    exact hmono _ ((le_max_right _ _).trans hledger)

end AVRegularity.Construction.Preservation.FullLift
end

section
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Finite factorial word prices give a real strong-energy constant before the fields are chosen. -/

theorem finite_factorial_order_price_ne_top (r offset : ℕ) (cost : ℕ → ℝ) :
    (∑ j ∈ Finset.range (r + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
      (2 : ℝ≥0∞) ^ (j + offset) * ENNReal.ofReal (cost j)) ≠ ∞ := by
  apply ENNReal.sum_ne_top.mpr
  intro j _
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr
        (sq_pos_of_pos (by exact_mod_cast Nat.factorial_pos j))))
    · exact ENNReal.pow_ne_top (by norm_num)
  · exact ENNReal.ofReal_ne_top

theorem finite_factorial_strong_price_ne_top (r : ℕ) (valueCost gradCost : ℕ → ℝ)
    (inputValue inputGrad columnValue columnGrad : ℝ) :
    (((∑ j ∈ Finset.range (r + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
      (2 : ℝ≥0∞) ^ j * ENNReal.ofReal (valueCost j)) * ENNReal.ofReal inputValue) *
        ENNReal.ofReal columnValue +
      ((∑ j ∈ Finset.range (r + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
        (2 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (gradCost j)) * ENNReal.ofReal inputGrad) *
          ENNReal.ofReal columnGrad) ≠ ∞ := by
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
    apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
    simpa only [Nat.add_zero] using finite_factorial_order_price_ne_top r 0 valueCost
  · apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top (finite_factorial_order_price_ne_top r 1 gradCost) ENNReal.ofReal_ne_top

theorem finite_energy_price_real_bound (P : ℝ≥0∞) (hP : P ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ P ^ (1 / 2 : ℝ) = ENNReal.ofReal C := by
  refine ⟨Real.sqrt P.toReal, Real.sqrt_nonneg _, ?_⟩
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal hP]

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Place the mass and radius factors inside each classical spatial word integral. -/

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

theorem weighted_scaled_square_lintegral (μ : Measure Ω) {π : ℝ} (hπ : 0 < π)
    (s : ℝ) (m : ℕ) (f : Ω → E) :
    (∫⁻ x, ENNReal.ofReal (π⁻¹ * (s ^ m * ‖f x‖) ^ 2) ∂μ) =
      ENNReal.ofReal π⁻¹ * ENNReal.ofReal (s ^ (2 * m)) * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have hs : 0 ≤ s ^ (2 * m) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg s) m
  have he (x : Ω) : (s ^ m * ‖f x‖) ^ 2 = s ^ (2 * m) * ‖f x‖ ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm m 2]
  simp_rw [he, ENNReal.ofReal_mul (inv_nonneg.mpr hπ.le), ENNReal.ofReal_mul hs,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]

theorem weighted_dissipation_square_lintegral (μ : Measure Ω) {π ν : ℝ}
    (hπ : 0 < π) (hν : 0 ≤ ν) (s : ℝ) (m : ℕ) (f : Ω → E) :
    (∫⁻ x, ENNReal.ofReal (π⁻¹ * (Real.sqrt ν * (s ^ m * ‖f x‖)) ^ 2) ∂μ) =
      ENNReal.ofReal ν * (ENNReal.ofReal π⁻¹ * ENNReal.ofReal (s ^ (2 * m)) *
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) := by
  have he (x : Ω) : π⁻¹ * (Real.sqrt ν * (s ^ m * ‖f x‖)) ^ 2 =
      ν * (π⁻¹ * (s ^ m * ‖f x‖) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hν]
    ring
  simp_rw [he, ENNReal.ofReal_mul hν]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    weighted_scaled_square_lintegral μ hπ s m f]

variable [NormedSpace ℝ E]

theorem weighted_classical_factorial_energy_eq {π : ℝ} (hπ : 0 < π)
    (s : ℝ) (K : ℕ) (f : Vec 2 → E) :
    ENNReal.ofReal π⁻¹ * classicalFactorialSq s K f =
      ∑ j ∈ Finset.range (K + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
        ∑ w : DerivativeWord2 j, ∫⁻ x in AVenhance.unitCube,
          ENNReal.ofReal (π⁻¹ * (s ^ j * ‖orderedDerivative w f x‖) ^ 2) := by
  simp only [classicalFactorialSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos (by exact_mod_cast Nat.factorial_pos j))]
  simp only [div_eq_mul_inv,
    weighted_scaled_square_lintegral (volume.restrict AVenhance.unitCube) hπ]
  refine Finset.sum_congr rfl fun w _ => ?_
  ac_rfl

theorem weighted_classical_gradient_energy_eq {π ν : ℝ} (hπ : 0 < π) (hν : 0 ≤ ν)
    (s : ℝ) (K : ℕ) (f : Vec 2 → E) :
    ENNReal.ofReal ν * (ENNReal.ofReal π⁻¹ * classicalGradFactorialSq s K f) =
      ∑ j ∈ Finset.range (K + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
        ∑ w : DerivativeWord2 (j + 1), ∫⁻ x in AVenhance.unitCube,
          ENNReal.ofReal (π⁻¹ * (Real.sqrt ν * (s ^ j * ‖orderedDerivative w f x‖)) ^ 2) := by
  simp only [classicalGradFactorialSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos (by exact_mod_cast Nat.factorial_pos j))]
  simp only [div_eq_mul_inv,
    weighted_dissipation_square_lintegral (volume.restrict AVenhance.unitCube) hπ hν]
  refine Finset.sum_congr rfl fun w _ => ?_
  ac_rfl

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Original record Schur prices bound native source jets without counting components. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem scaledEnvelope_of_original_records (F : ChartedFamily ι h D P Ctx)
    (p : P) (ctx : Ctx p) (π : ι → ℝ) (S : Set ℝ) (e clock lam : ℝ) (hlam : 0 ≤ lam)
    (Cj : ℕ → ℕ → ℝ) (hCj : ∀ r q, 0 ≤ Cj r q) (qs qf : ℕ)
    (θ : ∀ v u, F.Γ v u → (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ)
    (hθ : ∀ v u δ d I c, 0 ≤ θ v u δ d I c)
    (hrecord : ∀ v u δ d, 2 ≤ d → d ≤ (F.identity v u δ).maxOrder →
      (e / (F.identity v u δ).record.length) ^ (d - 2) *
        ∑ I, ∑ c, θ v u δ d I c ≤ (F.identity v u δ).record.size)
    (hlength : ∀ v u δ, 1 ≤ (F.identity v u δ).record.birthExcess →
      (F.identity v u δ).record.length ≤ e)
    (Θ : ℝ) (hrow : ∀ v, ∑ u, recordMajorant π F v u ≤ Θ)
    (hcol : ∀ u, ∑ v, recordMajorant π F v u ≤ Θ)
    (hjet : ∀ v u δ d, d ≤ (F.identity v u δ).maxOrder → ∀ I,
      ∀ r ≤ qs, ∀ q ≤ qf,
        jetSup S r q (fun t X z => F.flux p ctx v u δ d I (clock * t) (lam • X) z) ≤
          ENNReal.ofReal (Cj r q * lam ^ r * ∑ c, θ v u δ d I c)) :
    IsScaledJetEnvelope π (liftEdges clock lam (F.fiber p ctx)) S lam
      (fun r q => (Fintype.card (Finset.Icc 2 D) : ℝ) * Cj r q)
      qs qf (recordMajorant π F) Θ := by
  refine ⟨?_, hrow, hcol, ?_⟩
  · intro v u
    exact mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun δ _ =>
      mul_nonneg (norm_nonneg _) (F.identity v u δ).record.size_nonneg))
  · intro v u r hr q hq
    have hK : 0 ≤ Cj r q * lam ^ r := mul_nonneg (hCj r q) (pow_nonneg hlam r)
    have hdprice (d : Finset.Icc 2 D) := liftedFiber_record_jet_price_le F p ctx v u d
      S clock lam (Cj r q * lam ^ r) hK r q (fun δ I c => θ v u δ d.1 I c)
      (fun δ I c => hθ v u δ d.1 I c)
      (fun δ hd => context_record_weight_bound_or_quadratic d.1
        (F.identity v u δ).record.length_pos
        (fun h3 => hlength v u δ (by have hb := (F.identity v u δ).le_birth; omega))
        (Finset.sum_nonneg (fun I _ => Finset.sum_nonneg (fun c _ => hθ v u δ d.1 I c)))
        (hrecord v u δ d.1 (Finset.mem_Icc.mp d.2).1 hd))
      (fun δ hd I => hjet v u δ d.1 hd I r hr q hq)
    have hsum := Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset (Finset.Icc 2 D))) => hdprice d)
    apply (mul_le_mul_right hsum _).trans_eq
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg hK
      (Finset.sum_nonneg (fun δ _ => mul_nonneg (norm_nonneg _)
        (F.identity v u δ).record.size_nonneg))),
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, recordMajorant]
    congr 1
    ring

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Removing empty high degrees preserves the graph depth and the exact positive source envelope. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

omit [Fintype ι] in
theorem restrictSource_depth (K : ℕ) (hKD : K ≤ D) (edge : ConstituentEdges D h) {H : ℕ}
    (hdepth : HasDepthAtMost edge H) :
    HasDepthAtMost (EntryWeakProofs.restrictConstituentEdges K hKD edge) H := by
  intro path
  obtain ⟨j, hj⟩ := hdepth path
  exact ⟨j, fun d => hj ⟨d.1, Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp d.2).1, (Finset.mem_Icc.mp d.2).2.trans hKD⟩⟩⟩

theorem restrictSource_scaled_envelope (K : ℕ) (hKD : K ≤ D)
    (edge : ConstituentEdges D h) (hz : ∀ v u d, K < d.1 → edge v u d = [])
    (π : ι → ℝ) (S : Set ℝ) (lam : ℝ) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (price : ι → ι → ℝ) (Θ : ℝ)
    (he : IsScaledJetEnvelope π edge S lam Cj qs qf price Θ) :
    IsScaledJetEnvelope π (EntryWeakProofs.restrictConstituentEdges K hKD edge)
      S lam Cj qs qf price Θ := by
  refine ⟨he.nonneg, he.row_sum, he.col_sum, ?_⟩
  intro v u r hr q hq
  let cost (d : Finset.Icc 2 D) := ((edge v u d).map fun γ =>
    ENNReal.ofReal ‖γ.map‖ * ∑ I, jetSup S r q (γ.coeff I)).sum
  have hs : (∑ d : Finset.Icc 2 D, cost d) = ∑ d : Finset.Icc 2 K,
      cost (EntryWeakProofs.degreeRangeInclusion K D hKD d) :=
    EntryWeakProofs.sum_degreeRange_restrict hKD cost (fun d hd => by
      simp only [cost, hz v u d hd, List.map_nil, List.sum_nil])
  change ENNReal.ofReal (Real.sqrt (π u / π v)) *
    (∑ d : Finset.Icc 2 K, cost (EntryWeakProofs.degreeRangeInclusion K D hKD d)) ≤ _
  rw [← hs]
  exact he.jets v u r hr q hq

end AVRegularity.Construction.Preservation.FullLift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Summing spatial word energies costs the finite two-dimensional word count. -/

theorem factorial_word_energy_sum_le (K : ℕ) (E : (j : ℕ) → DerivativeWord2 j → ℝ≥0∞)
    (C : ℕ → ℝ≥0∞) (Z : ℝ≥0∞)
    (hb : ∀ j ≤ K, ∀ w, E j w ≤ C j * Z) :
    (∑ j ∈ Finset.range (K + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ * ∑ w, E j w) ≤
      (∑ j ∈ Finset.range (K + 1),
        (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ * (2 : ℝ≥0∞) ^ j * C j) * Z := by
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
        ∑ _w : DerivativeWord2 j, C j * Z := by
      refine Finset.sum_le_sum fun j hj => mul_le_mul' le_rfl ?_
      exact Finset.sum_le_sum fun w _ => hb j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) w
    _ = _ := by
      simp only [Finset.sum_const, ChartTransport.card_derivativeWord2, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, ← mul_assoc, ← Finset.sum_mul]

theorem gradient_factorial_word_energy_sum_le (K : ℕ) (E : (j : ℕ) → DerivativeWord2 (j + 1) → ℝ≥0∞)
    (C : ℕ → ℝ≥0∞) (Z : ℝ≥0∞)
    (hb : ∀ j ≤ K, ∀ w, E j w ≤ C j * Z) :
    (∑ j ∈ Finset.range (K + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ * ∑ w, E j w) ≤
      (∑ j ∈ Finset.range (K + 1),
        (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ * (2 : ℝ≥0∞) ^ (j + 1) * C j) * Z := by
  calc
    _ ≤ ∑ j ∈ Finset.range (K + 1), (ENNReal.ofReal ((j.factorial : ℝ) ^ 2))⁻¹ *
        ∑ _w : DerivativeWord2 (j + 1), C j * Z := by
      refine Finset.sum_le_sum fun j hj => mul_le_mul' le_rfl ?_
      exact Finset.sum_le_sum fun w _ => hb j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) w
    _ = _ := by
      simp only [Finset.sum_const, ChartTransport.card_derivativeWord2, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, ← mul_assoc, ← Finset.sum_mul]

end AVRegularity.Construction.Preservation.FullLift
end
