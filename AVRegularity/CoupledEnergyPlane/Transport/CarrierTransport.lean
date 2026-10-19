-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergyPlane.Fourier.CarrierPairing
public import AVRegularity.Sobolev.Carrier
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Transport

/-! Smooth compact cutoffs exhausting the plane, with vanishing gradient.
These are test functions for the weak transport identity. -/

theorem exists_expanding_smooth_cutoffs :
    ∃ (χ : ℕ → Vec 2 → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n) ∧ HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1)) ∧
      (∀ n x, ‖fderiv ℝ (χ n) x‖ ≤ ((n : ℝ) + 1)⁻¹ * C) := by
  let φ : ContDiffBump (0 : Vec 2) := default
  let ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let χ : ℕ → Vec 2 → ℝ := fun n x => φ (ε n • x)
  have hφd : ContDiff ℝ (⊤ : ℕ∞) (φ : Vec 2 → ℝ) := φ.contDiff
  have hφc : Continuous (fderiv ℝ (φ : Vec 2 → ℝ)) :=
    hφd.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support
    (φ.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0 : Vec 2))
  have hε (n : ℕ) : 0 < ε n := inv_pos.mpr (by positivity)
  refine ⟨χ, C, hC0, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨hφd.comp (ε n • ContinuousLinearMap.id ℝ (Vec 2)).contDiff,
      φ.hasCompactSupport.comp_smul (hε n).ne'⟩
  · intro n x
    exact ⟨φ.nonneg, φ.le_one⟩
  · intro x
    have he : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hs : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Vec 2)) := by
      simpa only [zero_smul] using he.smul_const x
    have ht := φ.continuous.continuousAt.tendsto.comp hs
    have hzero : φ (0 : Vec 2) = 1 :=
      φ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall, dist_self] using φ.rIn_pos.le)
    simpa only [χ, Function.comp_def, hzero] using ht
  · intro n x
    let L : Vec 2 →L[ℝ] Vec 2 := ε n • ContinuousLinearMap.id ℝ (Vec 2)
    have hd := (hφd.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
      L.hasFDerivAt
    have he : fderiv ℝ (χ n) x = (fderiv ℝ (φ : Vec 2 → ℝ) (ε n • x)).comp L :=
      hd.fderiv
    rw [he]
    calc
      _ ≤ ‖fderiv ℝ (φ : Vec 2 → ℝ) (ε n • x)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ‖L‖ := mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
      _ = ((n : ℝ) + 1)⁻¹ * C := by
        simp only [L, norm_smul, Real.norm_eq_abs, abs_of_pos (hε n),
          ContinuousLinearMap.norm_id, one_mul, ε, mul_comm]

end AVRegularity.CoupledEnergyPlane.Transport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Transport

/-! Compact-coefficient transport identities for actual plane weak derivatives.
No global bound on a derivative of the eventual physical drift is required. -/

theorem integral_mul_eq_neg_integral_mul_of_weakPartial (i : Fin 2)
    {f g h k : Vec 2 → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hh : MemLp h 2 volume) (hk : MemLp k 2 volume)
    (hfg : HasWeakPartialDerivOn Set.univ i f g)
    (hhk : HasWeakPartialDerivOn Set.univ i h k) :
    (∫ x, g x * h x) = -(∫ x, f x * k x) := by
  have hfg' : HasWeakPartialDerivOn Set.univ i (hf.toLp f) (hg.toLp g) := by
    apply hasWeakPartialDerivOn_congr_ae _ _ hfg
    · simpa only [Measure.restrict_univ] using hf.coeFn_toLp.symm
    · simpa only [Measure.restrict_univ] using hg.coeFn_toLp.symm
  have hhk' : HasWeakPartialDerivOn Set.univ i (hh.toLp h) (hk.toLp k) := by
    apply hasWeakPartialDerivOn_congr_ae _ _ hhk
    · simpa only [Measure.restrict_univ] using hh.coeFn_toLp.symm
    · simpa only [Measure.restrict_univ] using hk.coeFn_toLp.symm
  have he := Fourier.weakPartial_inner i (hf.toLp f) (hg.toLp g)
    (hh.toLp h) (hk.toLp k) hfg' hhk'
  simp only [L2.inner_def, Real.inner_apply] at he
  have hl : (∫ x, (hg.toLp g) x * (hh.toLp h) x) = ∫ x, g x * h x := by
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp, hg.coeFn_toLp] with x hx gx
    rw [hx, gx]
  have hr : (∫ x, (hf.toLp f) x * (hk.toLp k) x) = ∫ x, f x * k x := by
    apply integral_congr_ae
    filter_upwards [hk.coeFn_toLp, hf.coeFn_toLp] with x hx fx
    rw [hx, fx]
  rwa [hl, hr] at he

theorem weakPartial_mul_self_compact (i : Fin 2) {u g c : Vec 2 → ℝ}
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hw : HasWeakPartialDerivOn Set.univ i u g)
    (hc : ContDiff ℝ 1 c) (hcc : HasCompactSupport c) :
    2 * (∫ x, c x * g x * u x) =
      -(∫ x, fderiv ℝ c x (basisVec i) * u x ^ 2) := by
  let dc := fun x => fderiv ℝ c x (basisVec i)
  have hdc : Continuous dc :=
    (hc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcd : MemLp c ⊤ volume := hc.continuous.memLp_top_of_hasCompactSupport hcc volume
  have hdcd : MemLp dc ⊤ volume :=
    hdc.memLp_top_of_hasCompactSupport (hcc.fderiv_apply (𝕜 := ℝ) (basisVec i)) volume
  have hcu : MemLp (fun x => c x * u x) 2 volume := hcd.fun_mul hu
  have hcg : MemLp (fun x => c x * g x) 2 volume := hcd.fun_mul hg
  have hdcu : MemLp (fun x => dc x * u x) 2 volume := hdcd.fun_mul hu
  have hp := hasWeakPartialDerivOn_mul_contDiff_one hw
    (hu.locallyIntegrable (by norm_num)) (hg.locallyIntegrable (by norm_num)) hc
  have he := integral_mul_eq_neg_integral_mul_of_weakPartial i hu hg hcu
    (hcg.add hdcu) hw hp
  have hA : Integrable (fun x => u x * (c x * g x)) volume :=
    memLp_one_iff_integrable.mp
      (hu.fun_mul hcg : MemLp (fun x => u x * (c x * g x)) 1 volume)
  have hB : Integrable (fun x => u x * (dc x * u x)) volume :=
    memLp_one_iff_integrable.mp
      (hu.fun_mul hdcu : MemLp (fun x => u x * (dc x * u x)) 1 volume)
  have hleft : (fun x => g x * (c x * u x)) = (fun x => c x * g x * u x) := by
    funext x
    ring
  have hright : (fun x => u x * (c x * g x + dc x * u x)) =
      (fun x => u x * (c x * g x) + u x * (dc x * u x)) := by
    funext x
    ring
  change (∫ x, g x * (c x * u x)) = -(∫ x, u x * (c x * g x + dc x * u x)) at he
  rw [hleft, hright, integral_add hA hB] at he
  have hAeq : (fun x => u x * (c x * g x)) = (fun x => c x * g x * u x) := by
    funext x
    ring
  have hBeq : (fun x => u x * (dc x * u x)) =
      (fun x => fderiv ℝ c x (basisVec i) * u x ^ 2) := by
    funext x
    dsimp only [dc]
    ring
  rw [hAeq, hBeq] at he
  linarith only [he]

theorem weak_gradient_mul_compact {u : Vec 2 → ℝ} {g c : Fin 2 → Vec 2 → ℝ}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hw : ∀ i, HasWeakPartialDerivOn Set.univ i u (g i))
    (hc : ∀ i, ContDiff ℝ 1 (c i)) (hcc : ∀ i, HasCompactSupport (c i)) :
    2 * (∫ x, (∑ i : Fin 2, c i x * g i x) * u x) =
      -(∫ x, (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) * u x ^ 2) := by
  have hA (i : Fin 2) : Integrable (fun x => c i x * g i x * u x) volume := by
    have hcg : MemLp (fun x => c i x * g i x) 2 volume :=
      ((hc i).continuous.memLp_top_of_hasCompactSupport (hcc i) volume).fun_mul (hg i)
    exact memLp_one_iff_integrable.mp (hcg.fun_mul hu)
  have hB (i : Fin 2) : Integrable
      (fun x => fderiv ℝ (c i) x (basisVec i) * u x ^ 2) volume := by
    have hd : Continuous (fun x => fderiv ℝ (c i) x (basisVec i)) :=
      ((hc i).continuous_fderiv (by simp)).clm_apply continuous_const
    have hdc : MemLp (fun x => fderiv ℝ (c i) x (basisVec i) * u x) 2 volume :=
      (hd.memLp_top_of_hasCompactSupport ((hcc i).fderiv_apply (𝕜 := ℝ) (basisVec i)) volume).fun_mul hu
    have h := memLp_one_iff_integrable.mp
      (hdc.fun_mul hu : MemLp (fun x => (fderiv ℝ (c i) x (basisVec i) * u x) * u x) 1 volume)
    simpa only [pow_two, mul_assoc] using h
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hA i),
    integral_finsetSum _ (fun i _ => hB i), Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => weakPartial_mul_self_compact i hu (hg i) (hw i) (hc i) (hcc i))

/-! The divergence-free weak transport identity with a compact cutoff.
Only local classical differentiability of the drift is used. -/

theorem weak_transport_cutoff_identity {u : Vec 2 → ℝ} {g : Fin 2 → Vec 2 → ℝ}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hw : ∀ i, HasWeakPartialDerivOn Set.univ i u (g i))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ (fun y => v y i) x (basisVec i) = 0)
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    2 * (∫ x, χ x * (∑ i : Fin 2, v x i * g i x) * u x) =
      -(∫ x, (∑ i : Fin 2, fderiv ℝ χ x (basisVec i) * v x i) * u x ^ 2) := by
  have hvi (i : Fin 2) : ContDiff ℝ 1 (fun x => v x i) := contDiff_pi.mp hv i
  let c : Fin 2 → Vec 2 → ℝ := fun i x => χ x * v x i
  have hc (i : Fin 2) : ContDiff ℝ 1 (c i) := hχ.mul (hvi i)
  have hcc (i : Fin 2) : HasCompactSupport (c i) := hχc.mul_right
  have he := weak_gradient_mul_compact hu hg hw hc hcc
  have hcder (x : Vec 2) (i : Fin 2) :
      fderiv ℝ (c i) x (basisVec i) =
        χ x * fderiv ℝ (fun y => v y i) x (basisVec i) +
          fderiv ℝ χ x (basisVec i) * v x i := by
    rw [show c i = (fun y => χ y * v y i) from rfl,
      fderiv_fun_mul (hχ.differentiable (by simp)).differentiableAt
        ((hvi i).differentiable (by simp)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hsum (x : Vec 2) : (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) =
      ∑ i : Fin 2, fderiv ℝ χ x (basisVec i) * v x i := by
    simp_rw [hcder]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdiv x, mul_zero, zero_add]
  have hleft (x : Vec 2) : (∑ i : Fin 2, c i x * g i x) =
      χ x * ∑ i : Fin 2, v x i * g i x := by
    simp only [c, Finset.mul_sum, mul_assoc]
  simpa only [hsum, hleft] using he

end AVRegularity.CoupledEnergyPlane.Transport
end

section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Transport

/-! Bounded divergence-free transport cancels against actual plane H¹ data.
The compact cutoffs remove every need for a global derivative bound on v. -/

theorem weak_transport_integral_zero {u : Vec 2 → ℝ} {g : Fin 2 → Vec 2 → ℝ}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hw : ∀ i, HasWeakPartialDerivOn Set.univ i u (g i))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hb : ∃ M : ℝ, ∀ x, ‖v x‖ ≤ M)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ (fun y => v y i) x (basisVec i) = 0) :
    (∫ x, (∑ i : Fin 2, v x i * g i x) * u x) = 0 := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0 : Vec 2))
  obtain ⟨χ, C, hC, hχ, hχrange, hχlim, hDχ⟩ := exists_expanding_smooth_cutoffs
  let a : Vec 2 → ℝ := fun x => ∑ i : Fin 2, v x i * g i x
  have hvi (i : Fin 2) : MemLp (fun x => v x i) ⊤ volume :=
    memLp_top_of_bound ((continuous_apply i).comp hv.continuous).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => (norm_le_pi_norm (v x) i).trans (hM x))
  have ha : MemLp a 2 volume :=
    memLp_finsetSum Finset.univ (fun i _ => (hvi i).fun_mul (hg i))
  have hf : Integrable (fun x => a x * u x) volume :=
    memLp_one_iff_integrable.mp (ha.fun_mul hu)
  have hu2 : Integrable (fun x => u x ^ 2) volume := by
    simpa only [pow_two] using
      (memLp_one_iff_integrable.mp (hu.fun_mul hu : MemLp (fun x => u x * u x) 1 volume))
  have hχnorm (n : ℕ) (x : Vec 2) : ‖χ n x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hχrange n x).1]
    exact (hχrange n x).2
  have hleft : Tendsto (fun n => ∫ x, χ n x * (a x * u x)) atTop
      (𝓝 (∫ x, a x * u x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖a x * u x‖)
    · intro n
      exact (hχ n).1.continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
    · exact hf.norm
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hχnorm n x) (norm_nonneg _)).trans_eq (one_mul _)
    · exact Filter.Eventually.of_forall fun x => by
        simpa only [one_mul] using (hχlim x).mul_const (a x * u x)
  let b : ℕ → Vec 2 → ℝ := fun n x =>
    (∑ i : Fin 2, fderiv ℝ (χ n) x (basisVec i) * v x i) * u x ^ 2
  have hbnorm (n : ℕ) (x : Vec 2) :
      ‖b n x‖ ≤ ((n : ℝ) + 1)⁻¹ * (2 * C * M * u x ^ 2) := by
    have he (i : Fin 2) : ‖basisVec i‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro j
      simp only [basisVec_apply]
      split_ifs <;> norm_num
    have hcoord (i : Fin 2) : ‖fderiv ℝ (χ n) x (basisVec i) * v x i‖ ≤
        (((n : ℝ) + 1)⁻¹ * C) * M := by
      rw [norm_mul]
      apply mul_le_mul _ ((norm_le_pi_norm (v x) i).trans (hM x)) (norm_nonneg _) (by positivity)
      exact ((fderiv ℝ (χ n) x).le_opNorm _).trans
        ((mul_le_mul (hDχ n x) (he i) (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
    calc
      ‖b n x‖ = ‖∑ i : Fin 2, fderiv ℝ (χ n) x (basisVec i) * v x i‖ * u x ^ 2 := by
        dsimp only [b]
        rw [norm_mul, show ‖u x ^ 2‖ = u x ^ 2 by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]]
      _ ≤ (∑ _i : Fin 2, (((n : ℝ) + 1)⁻¹ * C) * M) * u x ^ 2 :=
        mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hcoord i)) (sq_nonneg _)
      _ = _ := by simp only [Fin.sum_univ_two]; ring
  have hright : Tendsto (fun n => ∫ x, b n x) atTop (𝓝 0) := by
    have heps : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hi := tendsto_integral_of_dominated_convergence
      (fun x => 2 * C * M * u x ^ 2) (μ := (volume : Measure (Vec 2)))
      (F := b) (f := fun _ => (0 : ℝ))
    apply (by simpa only [integral_zero] using hi) <;> clear hi
    · intro n
      have hc : Continuous (fun x => ∑ i : Fin 2, fderiv ℝ (χ n) x (basisVec i) * v x i) := by
        apply continuous_finsetSum
        intro i _
        exact (((hχ n).1.continuous_fderiv (by simp)).clm_apply continuous_const).mul
          ((continuous_apply i).comp hv.continuous)
      exact hc.aestronglyMeasurable.mul (hu.aestronglyMeasurable.pow 2)
    · exact hu2.const_mul _
    · intro n
      exact Filter.Eventually.of_forall fun x =>
        (hbnorm n x).trans (by
          have hn : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 2*C*M*u x^2))
    · exact Filter.Eventually.of_forall fun x =>
        squeeze_zero_norm (fun n => hbnorm n x) (by
          simpa only [zero_mul] using heps.mul_const (2*C*M*u x^2))
  have hid (n : ℕ) : 2 * (∫ x, χ n x * (a x * u x)) = -(∫ x, b n x) := by
    simpa only [a, b, mul_assoc] using
      weak_transport_cutoff_identity hu hg hw v hv hdiv (χ n)
        ((hχ n).1.of_le (by simp)) (hχ n).2
  have hzero : 2 * (∫ x, a x * u x) = 0 :=
    tendsto_nhds_unique (hleft.const_mul 2)
      (by simpa only [neg_zero] using hright.neg.congr' (Filter.Eventually.of_forall fun n => (hid n).symm))
  change (∫ x, a x * u x) = 0
  linarith only [hzero]

end AVRegularity.CoupledEnergyPlane.Transport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Transport

/-! Transport cancellation with the literal vector divergence used by the coupled energy estimate
on the plane (`coupled_energy_plane`). -/

theorem weak_transport_integral_zero_of_vector_divergence
    {u : Vec 2 → ℝ} {g : Fin 2 → Vec 2 → ℝ}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hw : ∀ i, HasWeakPartialDerivOn Set.univ i u (g i))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hb : ∃ M : ℝ, ∀ x, ‖v x‖ ≤ M)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ v x (basisVec i) i = 0) :
    (∫ x, (∑ i : Fin 2, v x i * g i x) * u x) = 0 := by
  apply weak_transport_integral_zero hu hg hw v hv hb
  intro x
  have hd := (hv.differentiable (by simp)).differentiableAt (x := x)
  simpa only [fderiv_apply hd, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using hdiv x

/-! Weak transport cancellation in the arbitrary finite-dimensional Hilbert fibres of
`coupled_energy_plane`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem weak_hilbert_transport_integral_zero {u : Vec 2 → E}
    {g : Fin 2 → Vec 2 → E} (hu : MemLp u 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (hw : ∀ i e, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (u x)) (fun x => inner ℝ e (g i x)))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hb : ∃ M : ℝ, ∀ x, ‖v x‖ ≤ M)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ v x (basisVec i) i = 0) :
    (∫ x, inner ℝ (∑ i : Fin 2, v x i • g i x) (u x)) = 0 := by
  let b := stdOrthonormalBasis ℝ E
  let U := fun (k : Fin (Module.finrank ℝ E)) x => inner ℝ (b k) (u x)
  let G := fun (k : Fin (Module.finrank ℝ E)) i x => inner ℝ (b k) (g i x)
  have hU (k) : MemLp (U k) 2 volume :=
    (InnerProductSpace.toDual ℝ E (b k)).comp_memLp' hu
  have hG (k) (i) : MemLp (G k i) 2 volume :=
    (InnerProductSpace.toDual ℝ E (b k)).comp_memLp' (hg i)
  obtain ⟨M, hM⟩ := hb
  have hVM (i : Fin 2) : MemLp (fun x => v x i) ⊤ volume := by
    apply memLp_top_of_bound ((contDiff_pi.mp hv i).continuous.stronglyMeasurable.aestronglyMeasurable) M
    exact Filter.Eventually.of_forall (fun x => (norm_le_pi_norm (v x) i).trans (hM x))
  have hI (k) : Integrable
      (fun x => (∑ i : Fin 2, v x i * G k i x) * U k x) volume := by
    have hm : MemLp (fun x => ∑ i : Fin 2, v x i * G k i x) 2 volume := by
      exact memLp_finsetSum Finset.univ (fun i _ => (hVM i).fun_mul (hG k i))
    exact memLp_one_iff_integrable.mp (hm.fun_mul (hU k))
  have he (x) : inner ℝ (∑ i : Fin 2, v x i • g i x) (u x) =
      ∑ k : Fin (Module.finrank ℝ E), (∑ i : Fin 2, v x i * G k i x) * U k x := by
    rw [← b.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_comm (b k) (∑ i : Fin 2, v x i • g i x)]
    simp only [inner_sum, real_inner_smul_right, U, G]
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ => hI k)]
  apply Finset.sum_eq_zero
  intro k _
  exact weak_transport_integral_zero_of_vector_divergence (hU k) (hG k)
    (fun i => hw i (b k)) v hv ⟨M, hM⟩ hdiv
end

/-! Every actual plane Sobolev derivative has a vanishing principal transport pairing. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_principal_transport_zero {K : ℕ} (p : PlaneHk Set.univ (K + 1) E)
    (j : Fin (K + 1)) (w : DerivativeWord2 j.val)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hb : ∃ M : ℝ, ∀ x, ‖v x‖ ≤ M)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ v x (basisVec i) i = 0) :
    (∫ x, inner ℝ (∑ i : Fin 2, v x i • p.val (nextIndex2 j w i) x)
      (p.val (lowerIndex2 j w) x)) = 0 := by
  have hu : MemLp (fun x => p.val (lowerIndex2 j w) x) 2 volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp (p.val (lowerIndex2 j w))
  have hg (i : Fin 2) : MemLp (fun x => p.val (nextIndex2 j w i) x) 2 volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp (p.val (nextIndex2 j w i))
  apply weak_hilbert_transport_integral_zero hu hg _ v hv hb hdiv
  intro i e
  exact p.toFunction.hasWeakJet j w i e
end

end AVRegularity.CoupledEnergyPlane.Transport
end
