-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Variational.DriftCarrierBudget
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledWeakIdentity
public import AVRegularity.Sobolev.Carrier
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
namespace AVRegularity.KernelEnergy

/-! Finite real component bounds imply finite extended-real time suprema. -/

section
variable {ι T : Type*} [Fintype ι]

theorem componentSup_le_budget (I : Set T) (w S : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hS : ∀ i, 0 ≤ S i) (E : ι → T → ℝ) (hE : ∀ i, ∀ t ∈ I, E i t ≤ S i) :
    (∑ i, ENNReal.ofReal (w i) * ⨆ t ∈ I, ENNReal.ofReal (E i t)) ≤
      ENNReal.ofReal (∑ i, w i * S i) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (hS i))]
  apply Finset.sum_le_sum
  intro i _
  rw [ENNReal.ofReal_mul (hw i)]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  exact iSup_le (fun t => iSup_le (fun ht => ENNReal.ofReal_le_ofReal (hE i t ht)))

theorem componentSupDissipation_le_budget (I : Set T) (w S R : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hS : ∀ i, 0 ≤ S i) (hR : ∀ i, 0 ≤ R i)
    (E : ι → T → ℝ) (hE : ∀ i, ∀ t ∈ I, E i t ≤ S i) :
    (∑ i, ENNReal.ofReal (w i) *
      ((⨆ t ∈ I, ENNReal.ofReal (E i t)) + ENNReal.ofReal (R i))) ≤
      ENNReal.ofReal (∑ i, w i * (S i + R i)) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (add_nonneg (hS i) (hR i)))]
  apply Finset.sum_le_sum
  intro i _
  rw [ENNReal.ofReal_mul (hw i), ENNReal.ofReal_add (hS i) (hR i)]
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  apply add_le_add _ le_rfl
  exact iSup_le (fun t => iSup_le (fun ht => ENNReal.ofReal_le_ofReal (hE i t ht)))
end

/-! Remove an arbitrary positive loss from a finite real dissipation integral. -/

theorem energy_of_all_positive_losses (E S c R : ℝ) (hR : 0 ≤ R)
    (h : ∀ ε : ℝ, 0 < ε → E + (c - ε) * R ≤ S) : E + c * R ≤ S := by
  by_contra hn
  have hgap : 0 < E + c * R - S := by linarith
  let ε := (E + c * R - S) / (R + 1)
  have hε : 0 < ε := div_pos hgap (by linarith)
  have he : ε * (R + 1) = E + c * R - S :=
    div_mul_cancel₀ _ (by linarith : R + 1 ≠ 0)
  have hh := h ε hε
  nlinarith

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.KernelEnergy

/-! A finite scalar budget simultaneously bounds all regularizer gains. -/

def regularizerGainBudget (c : ℕ → ℝ) (r : ℝ) (D : ℕ) : ℝ :=
  (c 0) ^ 2 + 2 * ∑ m : Fin (D - 1), (c m / r ^ (m : ℕ)) ^ 2

theorem regularizerGainBudget_nonneg (c : ℕ → ℝ) (r : ℝ) (D : ℕ) :
    0 ≤ regularizerGainBudget c r D :=
  add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun m _ => sq_nonneg _)))

theorem regularizer_gain_le_budget (c : ℕ → ℝ) (r : ℝ) (D m : ℕ) (hD : 2 ≤ D)
    (hm : m ≤ D - 2 + 1) :
    (if m = 0 then (c 0) ^ 2 else 2 * (c (m - 1) / r ^ (m - 1)) ^ 2) ≤
      regularizerGainBudget c r D := by
  unfold regularizerGainBudget
  cases m with
  | zero =>
    change (c 0) ^ 2 ≤ _
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun m _ => sq_nonneg _)))
  | succ m =>
    simp only [ite_eq_right (Nat.succ_ne_zero m), Nat.succ_sub_one]
    let j : Fin (D - 1) := ⟨m, by omega⟩
    have hs : (c m / r ^ m) ^ 2 ≤ ∑ q : Fin (D - 1), (c q / r ^ (q : ℕ)) ^ 2 :=
      Finset.single_le_sum (f := fun q : Fin (D - 1) => (c q / r ^ (q : ℕ)) ^ 2)
        (fun q _ => sq_nonneg _) (Finset.mem_univ j)
    exact (mul_le_mul_of_nonneg_left hs (by norm_num)).trans (le_add_of_nonneg_left (sq_nonneg _))

end AVRegularity.KernelEnergy
end
end

section
@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Absolute bilinear pairings converge under contracting strong projections. -/

theorem timeBilinear_projection_abs_integral_tendsto
    {T H E : Type*} [MeasurableSpace T] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure T) (Q : ℕ → H →L[ℝ] H) (hq : ∀ n x, ‖Q n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => Q n x) atTop (𝓝 x))
    (L : T → H →L[ℝ] E) (R : H →L[ℝ] E) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ t x, ‖L t x‖ ≤ B * ‖x‖)
    (u : T → H) (hu : MemLp u 2 μ)
    (hmes : ∀ n, AEStronglyMeasurable
      (fun t => |inner ℝ (L t (Q n (u t))) (R (Q n (u t)))|) μ) :
    Tendsto (fun n => ∫ t, |inner ℝ (L t (Q n (u t))) (R (Q n (u t)))| ∂μ)
      atTop (𝓝 (∫ t, |inner ℝ (L t (u t)) (R (u t))| ∂μ)) := by
  have hi : Integrable (fun t => (B * ‖R‖) * ‖u t‖ ^ 2) μ := hu.norm.integrable_sq.const_mul _
  apply tendsto_integral_of_dominated_convergence (fun t => (B * ‖R‖) * ‖u t‖ ^ 2) hmes hi
  · intro n
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_abs]
    have hl := (hL t (Q n (u t))).trans (mul_le_mul_of_nonneg_left (hq n (u t)) hB)
    have hr := (R.le_opNorm (Q n (u t))).trans
      (mul_le_mul_of_nonneg_left (hq n (u t)) (norm_nonneg R))
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul hl hr (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).trans_eq (by ring))
  · filter_upwards [] with t
    exact ((((L t).continuous.tendsto (u t)).comp (hlim (u t))).inner
      ((R.continuous.tendsto (u t)).comp (hlim (u t)))).abs

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
namespace AVRegularity.KernelEnergy

/-! Strong operator measurability acts on measurable time-dependent inputs.
Only continuity of each operator is used; no time derivative is required. -/

variable {T E F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem timeOperator_simple_aestronglyMeasurable (μ : Measure T)
    (A : T → E →L[ℝ] F) (hA : ∀ z, AEStronglyMeasurable (fun t => A t z) μ)
    (f : SimpleFunc T E) : AEStronglyMeasurable (fun t => A t (f t)) μ := by
  classical
  have hs : AEStronglyMeasurable (fun t => ∑ z ∈ f.range,
      (f ⁻¹' {z}).indicator (fun t => A t z) t) μ :=
    f.range.aestronglyMeasurable_fun_sum (fun z _ => (hA z).indicator (f.measurableSet_fiber z))
  apply hs.congr
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [Finset.sum_eq_single (f t)]
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.indicator_of_mem]
  · intro z _ hz
    apply Set.indicator_of_notMem
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using Ne.symm hz
  · exact fun hz => (hz (f.mem_range_self t)).elim

theorem timeOperator_aestronglyMeasurable (μ : Measure T)
    (A : T → E →L[ℝ] F) (hA : ∀ z, AEStronglyMeasurable (fun t => A t z) μ)
    (f : T → E) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun t => A t (f t)) μ := by
  have hm (n : ℕ) := timeOperator_simple_aestronglyMeasurable μ A hA (hf.stronglyMeasurable_mk.approx n)
  apply aestronglyMeasurable_of_tendsto_ae atTop hm
  filter_upwards [hf.ae_eq_mk] with t ht
  rw [ht]
  exact ((A t).continuous.tendsto (hf.mk f t)).comp (hf.stronglyMeasurable_mk.tendsto_approx t)

theorem timeOperator_simple_stronglyMeasurable
    (A : T → E →L[ℝ] F) (hA : ∀ z, StronglyMeasurable (fun t => A t z))
    (f : SimpleFunc T E) : StronglyMeasurable (fun t => A t (f t)) := by
  classical
  have hs : StronglyMeasurable (fun t => ∑ z ∈ f.range,
      (f ⁻¹' {z}).indicator (fun t => A t z) t) :=
    f.range.stronglyMeasurable_fun_sum (fun z _ => (hA z).indicator (f.measurableSet_fiber z))
  have he : (fun t => ∑ z ∈ f.range, (f ⁻¹' {z}).indicator (fun t => A t z) t) =
      (fun t => A t (f t)) := by
    funext t
    rw [Finset.sum_eq_single (f t)]
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.indicator_of_mem]
    · intro z _ hz
      apply Set.indicator_of_notMem
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using Ne.symm hz
    · exact fun hz => (hz (f.mem_range_self t)).elim
  rwa [he] at hs

theorem timeOperator_stronglyMeasurable (A : T → E →L[ℝ] F)
    (hA : ∀ z, StronglyMeasurable (fun t => A t z))
    (f : T → E) (hf : StronglyMeasurable f) : StronglyMeasurable (fun t => A t (f t)) := by
  have hm (n : ℕ) := timeOperator_simple_stronglyMeasurable A hA (hf.approx n)
  exact stronglyMeasurable_of_tendsto atTop hm (tendsto_pi_nhds.mpr (fun t =>
    ((A t).continuous.tendsto (f t)).comp (hf.tendsto_approx t)))

end AVRegularity.KernelEnergy
end
end

section
@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Two vanishing time L² residuals have a vanishing sum. -/

theorem timeL2_residual_add_square_tendsto {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] (μ : Measure T) (r s : ℕ → T → E)
    (hr : ∀ n, MemLp (r n) 2 μ) (hs : ∀ n, MemLp (s n) 2 μ)
    (hlr : Tendsto (fun n => ∫ t, ‖r n t‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hls : Tendsto (fun n => ∫ t, ‖s n t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, ‖r n t + s n t‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hl := (hlr.add hls).const_mul 2
  simp only [add_zero, mul_zero] at hl
  apply squeeze_zero (fun n => integral_nonneg (fun t => sq_nonneg _)) _ hl
  intro n
  have hi (u : T → E) (hu : MemLp u 2 μ) : Integrable (fun t => ‖u t‖ ^ 2) μ := by
    simpa only [pow_two, Pi.mul_apply] using! hu.norm.integrable_mul hu.norm
  have hadd : MemLp (fun t => r n t + s n t) 2 μ :=
    AVRegularity.CoupledEnergy.Variational.timeMemLp_pointwise_add μ 2 _ _ (hr n) (hs n)
  rw [← integral_add (hi _ (hr n)) (hi _ (hs n)), ← integral_const_mul]
  apply integral_mono (hi _ hadd) (((hi _ (hr n)).add (hi _ (hs n))).const_mul 2)
  intro t
  change ‖r n t + s n t‖ ^ 2 ≤ 2 * (‖r n t‖ ^ 2 + ‖s n t‖ ^ 2)
  have hn := norm_add_le (r n t) (s n t)
  have hsq := mul_self_le_mul_self (norm_nonneg _) hn
  nlinarith [sq_nonneg (‖r n t‖ - ‖s n t‖)]

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! A uniformly bounded strongly measurable action gives one fixed Bochner
operator. Scalar testing of this operator is therefore preserved by weak limits. -/

variable {T H G : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (μ : Measure T) (L : T → H →L[ℝ] G)
  (hL : ∀ x, StronglyMeasurable (fun t => L t x))
  (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t, ‖L t‖ ≤ M)

include hL hM hb in
theorem memLp_operator_action {u : T → H} (hu : MemLp u 2 μ) :
    MemLp (fun t => L t (u t)) 2 μ := by
  apply (hu.const_smul M).of_le
  · exact timeOperator_aestronglyMeasurable μ L
      (fun x => (hL x).aestronglyMeasurable) u hu.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    calc
      ‖L t (u t)‖ ≤ ‖L t‖ * ‖u t‖ := (L t).le_opNorm _
      _ ≤ M * ‖u t‖ := mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _)
      _ = ‖M • u t‖ := by rw [norm_smul, Real.norm_of_nonneg hM]

/-- The actual time-dependent action on equivalence classes. -/
def timeOperatorValue (u : Lp H 2 μ) : Lp G 2 μ :=
  (memLp_operator_action μ L hL M hM hb (Lp.memLp u)).toLp (fun t => L t (u t))

theorem timeOperatorValue_ae (u : Lp H 2 μ) :
    timeOperatorValue μ L hL M hM hb u =ᵐ[μ] fun t => L t (u t) :=
  (memLp_operator_action μ L hL M hM hb (Lp.memLp u)).coeFn_toLp

/-- Linearity of the coefficient action survives the Bochner quotient. -/
def timeOperatorLinearMap : Lp H 2 μ →ₗ[ℝ] Lp G 2 μ where
  toFun := timeOperatorValue μ L hL M hM hb
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [timeOperatorValue_ae μ L hL M hM hb (u + v),
      timeOperatorValue_ae μ L hL M hM hb u,
      timeOperatorValue_ae μ L hL M hM hb v, Lp.coeFn_add u v,
      Lp.coeFn_add (timeOperatorValue μ L hL M hM hb u)
        (timeOperatorValue μ L hL M hM hb v)] with t huv hu hv hi ho
    rw [huv, ho, hi]
    simp only [Pi.add_apply]
    rw [hu, hv]
    exact (L t).map_add _ _
  map_smul' := by
    intro c u
    apply Lp.ext
    filter_upwards [timeOperatorValue_ae μ L hL M hM hb (c • u),
      timeOperatorValue_ae μ L hL M hM hb u, Lp.coeFn_smul c u,
      Lp.coeFn_smul c (timeOperatorValue μ L hL M hM hb u)] with t hcu hu hi ho
    change timeOperatorValue μ L hL M hM hb (c • u) t =
      (c • timeOperatorValue μ L hL M hM hb u) t
    rw [hcu, ho, hi]
    simp only [Pi.smul_apply]
    rw [hu]
    exact (L t).map_smul c _

theorem timeOperatorValue_norm_le (u : Lp H 2 μ) :
    ‖timeOperatorValue μ L hL M hM hb u‖ ≤ M * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [timeOperatorValue_ae μ L hL M hM hb u] with t ht
  rw [ht]
  exact ((L t).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _))

/-- One fixed bounded linear operator for the entire variable-coefficient time action. -/
def timeOperatorCLM : Lp H 2 μ →L[ℝ] Lp G 2 μ :=
  (timeOperatorLinearMap μ L hL M hM hb).mkContinuous M
    (timeOperatorValue_norm_le μ L hL M hM hb)

end AVRegularity.KernelEnergy
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.KernelEnergy

/-! Integrate the sharp homogeneous differential energy on any closed subinterval. -/

theorem homogeneousTimeEnergy {a b s t c : ℝ} {E R : ℝ → ℝ}
    (hab : a ≤ b) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hE : AbsolutelyContinuousOnInterval E a b) (hR : IntervalIntegrable R volume a b)
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b), deriv E r + c * R r ≤ 0) :
    E t + c * (∫ r in Ioc s t, R r) ≤ E s := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hu : uIcc s t ⊆ uIcc a b := by simpa only [uIcc_of_le hst, uIcc_of_le hab] using hsub
  have hac := hE.mono hu
  have hr := hR.mono_set hu
  have hmono := intervalIntegral.integral_mono_ae_restrict hst
    (hac.intervalIntegrable_deriv.add (hr.const_mul c)) (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (0 : ℝ)) volume s t)
    (ae_restrict_of_ae_restrict_of_subset hsub hd)
  rw [intervalIntegral.integral_add hac.intervalIntegrable_deriv (hr.const_mul c),
    hac.integral_deriv_eq_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_zero, intervalIntegral.integral_of_le hst] at hmono
  linarith

end AVRegularity.KernelEnergy
end
end

section
@[expose] public section
open MeasureTheory Homogenization
namespace AVRegularity.KernelEnergy

/-! Transfer a literal weak identity when total flux representatives agree spatially. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem weakIdentity_flux_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (Q₁ F₁ Q₂ F₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (hflux : ∀ r ∈ Set.Ioc a t, ∀ᵐ x ∂μ, Q₁ r x + F₁ r x = Q₂ r x + F₂ r x)
    (h : CoupledWeakIdentity μ ν a t v u f φ dφ du Q₁ F₁ g) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du Q₂ F₂ g := by
  let R (Q F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (r : ℝ) (x : Vec 2) : ℝ :=
    -(∑ q : Fin 2, v r x q * inner ℝ (du r q x) (φ x)) -
      ν * ∑ q : Fin 2, inner ℝ (du r q x) (dφ q x) -
      ∑ q : Fin 2, inner ℝ (Q r x q + F r x q) (dφ q x) + inner ℝ (g r x) (φ x)
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ r ∈ Set.Ioc a t, Integrable (R Q₁ F₁ r) μ) ∧
    IntegrableOn (fun r => ∫ x, R Q₁ F₁ r x ∂μ) (Set.Ioc a t) ∧ _ at h
  have he (r : ℝ) (hr : r ∈ Set.Ioc a t) : R Q₁ F₁ r =ᵐ[μ] R Q₂ F₂ r := by
    filter_upwards [hflux r hr] with x hx
    change _ - (∑ q : Fin 2, inner ℝ ((Q₁ r x + F₁ r x) q) (dφ q x)) + _ =
      _ - (∑ q : Fin 2, inner ℝ ((Q₂ r x + F₂ r x) q) (dφ q x)) + _
    rw [hx]
  have hi (r : ℝ) (hr : r ∈ Set.Ioc a t) :
      (∫ x, R Q₁ F₁ r x ∂μ) = ∫ x, R Q₂ F₂ r x ∂μ := integral_congr_ae (he r hr)
  have ht : (fun r => ∫ x, R Q₁ F₁ r x ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun r => ∫ x, R Q₂ F₂ r x ∂μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hi r hr
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1.congr ht, ?_⟩
  · intro r hr
    exact (h.2.2.1 r hr).congr (he r hr)
  · exact h.2.2.2.2.trans (integral_congr_ae ht)
end

/-! Transfer a literal weak identity when total flux representatives agree spatially. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem weakIdentity_flux_congr_time (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (Q₁ F₁ Q₂ F₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (hflux : ∀ᵐ r ∂volume.restrict (Set.Ioc a t), ∀ᵐ x ∂μ,
      Q₁ r x + F₁ r x = Q₂ r x + F₂ r x)
    (hpoint : ∀ r ∈ Set.Ioc a t, Integrable (fun x =>
      -(∑ q : Fin 2, v r x q * inner ℝ (du r q x) (φ x)) -
        ν * ∑ q : Fin 2, inner ℝ (du r q x) (dφ q x) -
        ∑ q : Fin 2, inner ℝ (Q₂ r x q + F₂ r x q) (dφ q x) + inner ℝ (g r x) (φ x)) μ)
    (h : CoupledWeakIdentity μ ν a t v u f φ dφ du Q₁ F₁ g) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du Q₂ F₂ g := by
  let R (Q F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (r : ℝ) (x : Vec 2) : ℝ :=
    -(∑ q : Fin 2, v r x q * inner ℝ (du r q x) (φ x)) -
      ν * ∑ q : Fin 2, inner ℝ (du r q x) (dφ q x) -
      ∑ q : Fin 2, inner ℝ (Q r x q + F r x q) (dφ q x) + inner ℝ (g r x) (φ x)
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ r ∈ Set.Ioc a t, Integrable (R Q₁ F₁ r) μ) ∧
    IntegrableOn (fun r => ∫ x, R Q₁ F₁ r x ∂μ) (Set.Ioc a t) ∧ _ at h
  have ht : (fun r => ∫ x, R Q₁ F₁ r x ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun r => ∫ x, R Q₂ F₂ r x ∂μ) := by
    filter_upwards [hflux] with r hr
    apply integral_congr_ae
    filter_upwards [hr] with x hx
    change _ - (∑ q : Fin 2, inner ℝ ((Q₁ r x + F₁ r x) q) (dφ q x)) + _ =
      _ - (∑ q : Fin 2, inner ℝ ((Q₂ r x + F₂ r x) q) (dφ q x)) + _
    rw [hx]
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1.congr ht, ?_⟩
  · intro r hr
    exact hpoint r hr
  · exact h.2.2.2.2.trans (integral_congr_ae ht)
end

/-! Restart an integrated weak identity by subtracting its value at the new initial time. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem weakIdentity_restart (μ : Measure (Vec 2)) (ν a s t : ℝ) (has : a ≤ s) (hst : s ≤ t)
    (v : ℝ → Vec 2 → Vec 2) (u us f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (Q F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (ht : CoupledWeakIdentity μ ν a t v u f φ dφ du Q F g)
    (hs : CoupledWeakIdentity μ ν a s v us f φ dφ du Q F g) :
    CoupledWeakIdentity μ ν s t v u us φ dφ du Q F g := by
  let R (r : ℝ) (x : Vec 2) : ℝ :=
    -(∑ q : Fin 2, v r x q * inner ℝ (du r q x) (φ x)) -
      ν * ∑ q : Fin 2, inner ℝ (du r q x) (dφ q x) -
      ∑ q : Fin 2, inner ℝ (Q r x q + F r x q) (dφ q x) + inner ℝ (g r x) (φ x)
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ r ∈ Set.Ioc a t, Integrable (R r) μ) ∧
    IntegrableOn (fun r => ∫ x, R r x ∂μ) (Set.Ioc a t) ∧ _ at ht
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ r ∈ Set.Ioc a s, Integrable (R r) μ) ∧
    IntegrableOn (fun r => ∫ x, R r x ∂μ) (Set.Ioc a s) ∧ _ at hs
  have hsub : Set.Ioc s t ⊆ Set.Ioc a t := fun r hr => ⟨has.trans_lt hr.1, hr.2⟩
  have hi := ht.2.2.2.1.mono_set hsub
  have he : (∫ r in Set.Ioc a t, ∫ x, R r x ∂μ) =
      (∫ r in Set.Ioc a s, ∫ x, R r x ∂μ) +
        ∫ r in Set.Ioc s t, ∫ x, R r x ∂μ := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc has hst]
    exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hs.2.2.2.1 hi
  refine ⟨ht.1, hs.1, (fun r hr => ht.2.2.1 r (hsub hr)), hi, ?_⟩
  linarith [ht.2.2.2.2, hs.2.2.2.2]
end

end AVRegularity.KernelEnergy
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.KernelEnergy

/-! Integrate a differential energy estimate with an integrable error. -/

theorem perturbedTimeEnergy {a b s t c : ℝ} {E R H : ℝ → ℝ}
    (hab : a ≤ b) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hE : AbsolutelyContinuousOnInterval E a b) (hR : IntervalIntegrable R volume a b)
    (hH : IntervalIntegrable H volume a b)
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b), deriv E r + c * R r ≤ H r) :
    E t + c * (∫ r in Ioc s t, R r) ≤ E s + ∫ r in Ioc s t, H r := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hu : uIcc s t ⊆ uIcc a b := by simpa only [uIcc_of_le hst, uIcc_of_le hab] using hsub
  have hac := hE.mono hu
  have hr := hR.mono_set hu
  have hh := hH.mono_set hu
  have hmono := intervalIntegral.integral_mono_ae_restrict hst
    (hac.intervalIntegrable_deriv.add (hr.const_mul c)) hh
    (ae_restrict_of_ae_restrict_of_subset hsub hd)
  rw [intervalIntegral.integral_add hac.intervalIntegrable_deriv (hr.const_mul c),
    hac.integral_deriv_eq_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst] at hmono
  linarith

 theorem perturbedTimeEnergyGlobal {a b s t c : ℝ} {E R H : ℝ → ℝ}
    (hab : a ≤ b) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hE : AbsolutelyContinuousOnInterval E a b) (hR : IntervalIntegrable R volume a b)
    (hH : Integrable H (volume.restrict (Icc a b)))
    (hpos : ∀ r, 0 ≤ H r)
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b), deriv E r + c * R r ≤ H r) :
    E t + c * (∫ r in Ioc s t, R r) ≤ E s + ∫ r in Icc a b, H r := by
  have he := perturbedTimeEnergy hab hs ht hst hE hR
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hH) hd
  have hsub : Ioc s t ⊆ Icc a b := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  have hm := setIntegral_mono_set hH (Filter.Eventually.of_forall hpos)
    (Filter.Eventually.of_forall hsub)
  linarith

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! A bounded extension from ambient jets, used only after coefficient synthesis
when passing the actual kernel operator through the spacetime weak limit. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def torusGraphProjection (K : ℕ) : JetL2 (volume.restrict AVenhance.unitCube) K E →L[ℝ]
    TorusHk K E :=
  (torusHkGraph (E := E) K).toSubmodule.orthogonalProjectionOnto

@[simp] theorem torusGraphProjection_carrier (K : ℕ) (u : TorusHk K E) :
    torusGraphProjection K u.val = u :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self u

end AVRegularity.KernelEnergy
end
end
