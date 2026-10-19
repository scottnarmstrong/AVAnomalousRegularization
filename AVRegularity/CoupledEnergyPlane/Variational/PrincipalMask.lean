-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Variational.PullbackForm
import AVRegularity.CoupledEnergyPlane.Variational.FiniteFamilyPrimitive
public import AVRegularity.CoupledEnergyPlane.ActionODE
public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

section
@[expose] public section
open Filter Function Set
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Sequential weak compactness in Hilbert spaces, and its continuous-linear-map companion. -/

/-- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence whose inner products converge against every test vector. -/
theorem exists_strictMono_tendsto_inner_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ z : H,
        Tendsto (fun n => inner ℝ (u (φ n)) z) atTop
          (𝓝 (inner ℝ v z)) := by
  let f : ℕ → WeakDual ℝ H := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
  have hf : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ H) R := by
    intro n
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    change ‖InnerProductSpace.toDual ℝ H (u n) - 0‖ ≤ R
    simpa using hu n
  obtain ⟨ℓ, hℓ, φ, hφ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) R) hf
  let v : H :=
    (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ℓ)
  refine ⟨v, φ, hφ, fun z => ?_⟩
  simpa [f, v, Function.comp_def] using
    ((WeakDual.eval_continuous z).tendsto ℓ).comp hlim

/-- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence converging against every continuous linear functional. -/
theorem exists_strictMono_tendsto_clm_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : H →L[ℝ] ℝ,
        Tendsto (fun n => ell (u (φ n))) atTop (𝓝 (ell v)) := by
  obtain ⟨v, φ, hφ, hinner⟩ := exists_strictMono_tendsto_inner_of_norm_le u R hu
  refine ⟨v, φ, hφ, fun ell => ?_⟩
  let z := (InnerProductSpace.toDual ℝ H).symm ell
  simp_rw [← InnerProductSpace.toDual_symm_apply]
  simpa only [z, real_inner_comm] using hinner z

/-- A uniform Hilbert norm bound survives convergence of all scalar pairings. -/
theorem norm_le_of_tendsto_inner {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {u : ℕ → H} {v : H} {R : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ R)
    (hlim : ∀ z : H, Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z))) :
    ‖v‖ ≤ R := by
  have hR : 0 ≤ R := (norm_nonneg (u 0)).trans (hu 0)
  have hp : inner ℝ v v ≤ R * ‖v‖ :=
    le_of_tendsto (hlim v) (Eventually.of_forall (fun n =>
      (real_inner_le_norm (u n) v).trans (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg v))))
  rw [real_inner_self_eq_norm_sq] at hp
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · simpa only [← hv] using hR
  · nlinarith

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Bounded linear scalar observations of Bochner L² classes are integrable on finite time measures. -/

variable {T H : Type*} [MeasurableSpace T] [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem timeL2_observable_integrable (μ : Measure T) [IsFiniteMeasure μ]
    (U : Lp H 2 μ) (ell : H →L[ℝ] ℝ) : Integrable (fun t => ell (U t)) μ := by
  exact (ell.comp_memLp' (Lp.memLp U)).integrable (by norm_num)

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Genuine L² functions have integrable raw inner products on arbitrary measures. -/

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rawInner_integrable_of_memLp_two (μ : Measure X) (f g : X → E)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public section
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! A simultaneous finite-family replacement in the actual residual coupling sum. -/

variable {ι : Type*} [Fintype ι] {δ : ι → Type*} [∀ i, Fintype (δ i)]
  {E : ι → Type*} [∀ i, AddGroup (E i)] {G : Type*} [AddCommGroup G]

theorem residualFluxFields_congr (P : ∀ i, E i → E i) (C : ∀ i, δ i → E i → G)
    (u u' : ∀ i, E i) (f f' : G) (hu : ∀ i, u i = u' i) (hf : f = f') :
    (∑ i, ∑ d : δ i, C i d (u i - P i (u i))) + f =
      (∑ i, ∑ d : δ i, C i d (u' i - P i (u' i))) + f' := by
  exact congrArg₂ (fun (q : ∀ i, E i) z => (∑ i, ∑ d : δ i, C i d (q i - P i (q i))) + z)
    (funext hu) hf

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Set-integral observables of the actual weak Hilbert spacetime class. -/

variable {T H : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def scalarSetIntegralCLM (μ : Measure T) [IsFiniteMeasure μ]
    (ell : H →L[ℝ] ℝ) (s : Set T) (hs : MeasurableSet s) : Lp H 2 μ →L[ℝ] ℝ :=
  innerSL ℝ (((memLp_const (μ := μ) (p := 2) ((InnerProductSpace.toDual ℝ H).symm ell)).indicator hs).toLp
    (s.indicator (fun _ : T => (InnerProductSpace.toDual ℝ H).symm ell)))

theorem scalarSetIntegralCLM_apply (μ : Measure T) [IsFiniteMeasure μ]
    (ell : H →L[ℝ] ℝ) (s : Set T) (hs : MeasurableSet s) (U : Lp H 2 μ) :
    scalarSetIntegralCLM μ ell s hs U = ∫ t in s, ell (U t) ∂μ := by
  let z := (InnerProductSpace.toDual ℝ H).symm ell
  unfold scalarSetIntegralCLM
  rw [innerSL_apply_apply, L2.inner_def]
  have he : (fun t => inner ℝ
      (((memLp_const (μ := μ) (p := 2) z).indicator hs).toLp (s.indicator (fun _ : T => z)) t) (U t)) =ᵐ[μ]
      s.indicator (fun t => ell (U t)) := by
    filter_upwards [((memLp_const (μ := μ) (p := 2) z).indicator hs).coeFn_toLp] with t ht
    rw [ht]
    by_cases hts : t ∈ s
    · simp only [Set.indicator_of_mem hts]
      exact InnerProductSpace.toDual_symm_apply
    · simp only [Set.indicator_of_notMem hts, inner_zero_left]
  rw [integral_congr_ae he, integral_indicator hs]

theorem scalarSetIntegral_weak_limit (μ : Measure T) [IsFiniteMeasure μ]
    (U : ℕ → Lp H 2 μ) (W : Lp H 2 μ)
    (hw : ∀ L : Lp H 2 μ →L[ℝ] ℝ, Tendsto (fun n => L (U n)) atTop (𝓝 (L W)))
    (ell : H →L[ℝ] ℝ) (s : Set T) (hs : MeasurableSet s) :
    Tendsto (fun n => ∫ t in s, ell (U n t) ∂μ) atTop (𝓝 (∫ t in s, ell (W t) ∂μ)) := by
  simpa only [scalarSetIntegralCLM_apply] using hw (scalarSetIntegralCLM μ ell s hs)

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Expansion of the tested PDE integral with all summands genuinely integrable. -/

theorem testedIntegral_expansion {ι : Type*} [Fintype ι] {δ : ι → Type*}
    [∀ i, Fintype (δ i)] {a b ν : ℝ}
    (d r f g : ℝ → ℝ) (e : ∀ i, δ i → ℝ → ℝ)
    (hd : IntervalIntegrable d volume a b)
    (hr : IntervalIntegrable r volume a b)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (he : ∀ i j, IntervalIntegrable (e i j) volume a b) :
    (∫ s in a..b, -d s - ν * r s - (∑ i, ∑ j, e i j s) - f s + g s) =
      -(∫ s in a..b, d s) - ν * (∫ s in a..b, r s) -
        (∑ i, ∑ j, ∫ s in a..b, e i j s) - (∫ s in a..b, f s) + ∫ s in a..b, g s := by
  have hi (i : ι) : IntervalIntegrable (fun s => ∑ j, e i j s) volume a b := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => he i j) using 1
    ext s
    simp
  have hsum : IntervalIntegrable (fun s => ∑ i, ∑ j, e i j s) volume a b := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hi i) using 1
    ext s
    simp
  have hdn : IntervalIntegrable (fun s => -d s) volume a b := hd.neg
  rw [intervalIntegral.integral_add (((hdn.sub (hr.const_mul ν)).sub hsum).sub hf) hg,
    intervalIntegral.integral_sub ((hdn.sub (hr.const_mul ν)).sub hsum) hf,
    intervalIntegral.integral_sub (hdn.sub (hr.const_mul ν)) hsum,
    intervalIntegral.integral_sub hdn (hr.const_mul ν),
    intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => he _ j)]

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Contractive strongly convergent Hilbert operators converge strongly on Bochner L². -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem contractiveApproximation_time_tendsto {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (L : ℕ → H →L[ℝ] H)
    (hL : ∀ N x, ‖L N x‖ ≤ ‖x‖)
    (hstrong : ∀ x, Tendsto (fun N => L N x) atTop (𝓝 x))
    (U : Lp H 2 μ) :
    Tendsto (fun N => (L N).compLpL 2 μ U) atTop (𝓝 U) := by
  let q : ℕ → T → ℝ := fun N t => ‖L N (U t) - U t‖ ^ 2
  have hq (N : ℕ) : AEStronglyMeasurable (q N) μ := by
    exact (((L N).continuous.comp_aestronglyMeasurable
      (Lp.memLp U).aestronglyMeasurable).sub
        (Lp.memLp U).aestronglyMeasurable).norm.pow 2
  have hd : Integrable (fun t => 4 * ‖U t‖ ^ 2) μ :=
    ((Lp.memLp U).norm.integrable_sq).const_mul 4
  have hb (N : ℕ) : ∀ᵐ t ∂μ, ‖q N t‖ ≤ 4 * ‖U t‖ ^ 2 := by
    filter_upwards with t
    have hp := hL N (U t)
    have hsub := norm_sub_le (L N (U t)) (U t)
    dsimp only [q]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (L N (U t) - U t), norm_nonneg (U t)]
  have hpoint : ∀ᵐ t ∂μ, Tendsto (fun N => q N t) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with t
    have hp := ((hstrong (U t)).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => U t) atTop (𝓝 (U t)))).norm.pow 2
    simpa only [q, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hp
  have hint := tendsto_integral_of_dominated_convergence
    (fun t => 4 * ‖U t‖ ^ 2) hq hd hb hpoint
  have he (N : ℕ) : ‖(L N).compLpL 2 μ U - U‖ ^ 2 = ∫ t, q N t ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((L N).compLpL 2 μ U) U,
      ContinuousLinearMap.coeFn_compLpL (L N) U] with t ht hp
    rw [ht, Pi.sub_apply, hp, real_inner_self_eq_norm_sq]
  simp only [integral_zero] at hint
  simp_rw [← he] at hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := (Real.continuous_sqrt.tendsto 0).comp hint
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Linear assembly of diffusion, finitely many edge fluxes, and external forcing in time L². -/

variable {T J I : Type*} [MeasurableSpace T] [Fintype I]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

def assembleTimeFlux (μ : Measure T) {D : I → Type*} [∀ i, Fintype (D i)]
    (ν : ℝ) (G : Lp J 2 μ) (C : ∀ i, D i → Lp J 2 μ) (F : Lp J 2 μ) : Lp J 2 μ :=
  ν • G + (∑ i, ∑ d, C i d) + F

theorem assembleTimeFlux_apply_of_fields {L : Type*}
    [NormedAddCommGroup L] [NormedSpace ℝ L]
    (μ : Measure T) {D : I → Type*} [∀ i, Fintype (D i)]
    (P : Lp J 2 μ →L[ℝ] Lp L 2 μ) (ν : ℝ) (G : Lp J 2 μ)
    (C : ∀ i, D i → Lp J 2 μ) (F : Lp J 2 μ)
    (g : Lp L 2 μ) (c : ∀ i, D i → Lp L 2 μ)
    (hg : P G = g) (hc : ∀ i d, P (C i d) = c i d) :
    P (assembleTimeFlux μ ν G C F) = ν • g + ((∑ i, ∑ d, c i d) + P F) := by
  simp only [assembleTimeFlux, map_add, map_smul, map_sum, hg, hc]
  abel

omit [Fintype I] in
theorem timeFlux_value_ae {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    (μ : Measure T) (P : J →L[ℝ] L) (ν : ℝ) (S : Lp J 2 μ)
    (G F : Lp L 2 μ) (g : T → L)
    (hclass : P.compLpL 2 μ S = ν • G + F) (hg : G =ᵐ[μ] g) :
    (fun t => P (S t)) =ᵐ[μ] fun t => ν • g t + F t := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL P S,
    Lp.coeFn_add (ν • G) F, Lp.coeFn_smul ν G, hg] with t hp ha hs hg
  have he := congrArg (fun z : Lp L 2 μ => z t) hclass
  rw [hp, ha, Pi.add_apply, hs, Pi.smul_apply, hg] at he
  exact he

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Contractive strong approximations converge in the time integral of the norm. -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem contractiveApproximation_timeL1_integral_tendsto {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (L : ℕ → H →L[ℝ] H)
    (hL : ∀ N x, ‖L N x‖ ≤ ‖x‖)
    (hstrong : ∀ x, Tendsto (fun N => L N x) atTop (𝓝 x))
    (U : Lp H 1 μ) :
    Tendsto (fun N => ∫ t, ‖L N (U t) - U t‖ ∂μ) atTop (𝓝 0) := by
  have hq (N : ℕ) : AEStronglyMeasurable (fun t => ‖L N (U t) - U t‖) μ :=
    (((L N).continuous.comp_aestronglyMeasurable (Lp.memLp U).aestronglyMeasurable).sub
      (Lp.memLp U).aestronglyMeasurable).norm
  have hd : Integrable (fun t => 2 * ‖U t‖) μ :=
    ((memLp_one_iff_integrable.mp (Lp.memLp U)).norm).const_mul 2
  have hb (N : ℕ) : ∀ᵐ t ∂μ, ‖‖L N (U t) - U t‖‖ ≤ 2 * ‖U t‖ := by
    filter_upwards with t
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc
      ‖L N (U t) - U t‖ ≤ ‖L N (U t)‖ + ‖U t‖ := norm_sub_le _ _
      _ ≤ 2 * ‖U t‖ := by linarith [hL N (U t)]
  have hp : ∀ᵐ t ∂μ, Tendsto (fun N => ‖L N (U t) - U t‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with t
    simpa only [sub_self, norm_zero] using
      ((hstrong (U t)).sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => U t) atTop (𝓝 (U t)))).norm
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun t => 2 * ‖U t‖) hq hd hb hp

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Almost-everywhere identities for composing fixed fiber maps with time-class readouts. -/

variable {T H J X : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem timeReadout_compLp_ae (μ : Measure T) (L : H →L[ℝ] J)
    (M : X →L[ℝ] Lp H 2 μ) (W : X) (f : T → H) (hf : M W =ᵐ[μ] f) :
    ((L.compLpL 2 μ).comp M) W =ᵐ[μ] fun t => L (f t) := by
  exact (ContinuousLinearMap.coeFn_compLpL L (M W)).trans (hf.mono (fun _ h => congrArg L h))

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Strong time L² convergence makes residual time L¹ norms vanish on finite intervals. -/

section
variable {T H : Type*} [MeasurableSpace T] [NormedAddCommGroup H]

theorem timeLp_integral_norm_le (μ : Measure T) [IsFiniteMeasure μ] (U : Lp H 2 μ) :
    (∫ t, ‖U t‖ ∂μ) ≤ ‖U‖ * (μ Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))).toReal := by
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num) (Lp.aestronglyMeasurable U)
  have ht : eLpNorm U 2 μ * μ Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (Lp.eLpNorm_ne_top U)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ))
  have hreal := ENNReal.toReal_mono ht hb
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable U),
    ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable U),
    ENNReal.toReal_mul, ← Lp.norm_def] at hreal
  exact hreal

theorem timeLp_integral_norm_tendsto_zero (μ : Measure T) [IsFiniteMeasure μ]
    (U : ℕ → Lp H 2 μ) (hU : Tendsto U atTop (𝓝 0)) :
    Tendsto (fun N => ∫ t, ‖U N t‖ ∂μ) atTop (𝓝 0) := by
  have hbound := hU.norm.mul_const
    (μ Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))).toReal
  simp only [norm_zero, zero_mul] at hbound
  exact squeeze_zero (fun N => integral_nonneg (fun t => norm_nonneg (U N t)))
    (fun N => timeLp_integral_norm_le μ (U N)) hbound
end

/-! Strong time L² convergence preserves each actual bounded jet readout energy. -/

section
variable {T H J : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J]

theorem timeLp_readout_integral_norm_square (μ : Measure T) (L : H →L[ℝ] J) (U : Lp H 2 μ) :
    (∫ t, ‖L (U t)‖ ^ 2 ∂μ) = ‖L.compLpL 2 μ U‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL L U] with t ht
  rw [ht, real_inner_self_eq_norm_sq]

theorem timeLp_readout_integral_norm_square_tendsto (μ : Measure T) (L : H →L[ℝ] J)
    (U : ℕ → Lp H 2 μ) (V : Lp H 2 μ) (hU : Tendsto U atTop (𝓝 V)) :
    Tendsto (fun N => ∫ t, ‖L (U N t)‖ ^ 2 ∂μ) atTop (𝓝 (∫ t, ‖L (V t)‖ ^ 2 ∂μ)) := by
  simpa only [timeLp_readout_integral_norm_square, Function.comp_def] using
    (((L.compLpL 2 μ).continuous.tendsto V).comp hU).norm.pow 2
end

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Literal fixed-test integrals of time L² classes made from genuine carrier curves. -/

section
variable {H J : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J]

theorem timeLpReadout_toLp_test_integral {a b t : ℝ} (ht : t ∈ Set.Icc a b)
    (L : H →L[ℝ] J) (q : ℝ → H) (hq : MemLp q 2 (volume.restrict (Set.Icc a b)))
    (z : J) :
    (∫ s in a..t, inner ℝ ((L.compLpL 2 (volume.restrict (Set.Icc a b)) (hq.toLp q)) s) z) =
      ∫ s in a..t, inner ℝ (L (q s)) z := by
  apply intervalIntegral.integral_congr_ae_restrict
  have hs : Set.uIoc a t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le ht.1]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs
      (ContinuousLinearMap.coeFn_compLpL L (hq.toLp q)),
    ae_restrict_of_ae_restrict_of_subset hs hq.coeFn_toLp] with s hL hq
  rw [hL, hq]
end

/-! A time L² transport field and a time L¹ value source give a genuine integrable RHS. -/

section
variable {H : Type*} [NormedAddCommGroup H]

def timeValueSource {a b : ℝ} (T : Lp H 2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → H) (t : ℝ) : H := -T t + g t

theorem timeValueSource_integrable {a b : ℝ}
    (T : Lp H 2 (volume.restrict (Set.Icc a b))) (g : ℝ → H)
    (hg : Integrable g (volume.restrict (Set.Icc a b))) :
    Integrable (timeValueSource T g) (volume.restrict (Set.Icc a b)) := by
  exact ((Lp.memLp T).integrable (by norm_num)).neg.add hg

theorem timeValueSource_ae_sub_of_field {a b : ℝ}
    (T : Lp H 2 (volume.restrict (Set.Icc a b))) (g q : ℝ → H)
    (hT : T =ᵐ[volume.restrict (Set.Icc a b)] q) :
    timeValueSource T g =ᵐ[volume.restrict (Set.Icc a b)] fun t => g t - q t := by
  filter_upwards [hT] with t ht
  change -T t + g t = g t - q t
  rw [ht, sub_eq_add_neg, add_comm]
end

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Closed linear constraints survive weak limits through explicit continuous readouts. -/

variable {H : Type*} [NormedAddCommGroup H]

/-- Every continuous Hilbert-valued constraint vanishing on a weak sequence vanishes on its limit. -/
theorem map_eq_zero_of_weak_limit [NormedSpace ℝ H] {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (L : H →L[ℝ] G) {u : ℕ → H} {v : H}
    (hlim : ∀ ell : H →L[ℝ] ℝ, Tendsto (fun n => ell (u n)) atTop (𝓝 (ell v)))
    (hzero : ∀ n, L (u n) = 0) : L v = 0 := by
  let ell : H →L[ℝ] ℝ := (InnerProductSpace.toDualMap ℝ G (L v)).comp L
  have heq : ∀ n, ell (u n) = 0 := by
    intro n
    simp only [ell, ContinuousLinearMap.comp_apply, hzero, map_zero]
  have h0 : Tendsto (fun n => ell (u n)) atTop (𝓝 0) := by
    simp only [heq]
    exact tendsto_const_nhds
  have hv : ell v = 0 := tendsto_nhds_unique (hlim ell) h0
  change inner ℝ (L v) (L v) = 0 at hv
  exact inner_self_eq_zero.mp hv

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A closed Hilbert subspace retains membership under scalar-observable weak convergence. -/
theorem mem_closedSubmodule_of_weak_limit (S : ClosedSubmodule ℝ H) {u : ℕ → H} {v : H}
    (hlim : ∀ ell : H →L[ℝ] ℝ, Tendsto (fun n => ell (u n)) atTop (𝓝 (ell v)))
    (hu : ∀ n, u n ∈ S) : v ∈ S := by
  let L : H →L[ℝ] H := ContinuousLinearMap.id ℝ H - S.toSubmodule.starProjection
  have hn : ∀ n, L (u n) = 0 := by
    intro n
    change u n - S.toSubmodule.starProjection (u n) = 0
    rw [Submodule.starProjection_eq_self_iff.mpr (hu n), sub_self]
  have hz := map_eq_zero_of_weak_limit L hlim hn
  change v - S.toSubmodule.starProjection v = 0 at hz
  have hp : S.toSubmodule.starProjection v = v := (sub_eq_zero.mp hz).symm
  exact Submodule.starProjection_eq_self_iff.mp hp

/-- A generic fixed readout into a closed Hilbert subspace. -/
def closedSubmoduleReadout (S : ClosedSubmodule ℝ H) : H →L[ℝ] S :=
  S.toSubmodule.starProjection.codRestrict S.toSubmodule (Submodule.starProjection_apply_mem _)

/-- Closed-subspace readout preserves Bochner integrability without unfolding the graph constraints. -/
theorem closedSubmoduleReadout_memLp (S : ClosedSubmodule ℝ H)
    {X : Type*} [MeasurableSpace X] {m : MeasureTheory.Measure X} {p : ENNReal}
    {f : X → H} (hf : MeasureTheory.MemLp f p m) :
    MeasureTheory.MemLp (fun t => closedSubmoduleReadout S (f t)) p m :=
  (closedSubmoduleReadout S).comp_memLp' hf

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The finite L² flux sum has the literal sum representative almost everywhere. -/

variable {T J I : Type*} [MeasurableSpace T] [Fintype I]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

theorem assembleTimeFlux_coeFn_ae (μ : Measure T) {D : I → Type*} [∀ i, Fintype (D i)]
    (ν : ℝ) (G : Lp J 2 μ) (C : ∀ i, D i → Lp J 2 μ) (F : Lp J 2 μ) :
    assembleTimeFlux μ ν G C F =ᵐ[μ] fun t =>
      ν • G t + (∑ i, ∑ d, C i d t) + F t := by
  have hC := Lp.coeFn_finsetSum Finset.univ (fun i => ∑ d, C i d)
  have hCi := ae_all_iff.mpr (fun i => Lp.coeFn_finsetSum Finset.univ (C i))
  filter_upwards [Lp.coeFn_add (ν • G + ∑ i, ∑ d, C i d) F,
    Lp.coeFn_add (ν • G) (∑ i, ∑ d, C i d), Lp.coeFn_smul ν G, hC, hCi] with t h1 h2 hs hc hci
  change (ν • G + (∑ i, ∑ d, C i d) + F) t = _
  rw [h1, Pi.add_apply, h2, Pi.add_apply, hs, Pi.smul_apply, hc, Finset.sum_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Finset.sum_apply] using hci i

theorem doubleSum_add_coeFn_ae (μ : Measure T) {D : I → Type*} [∀ i, Fintype (D i)]
    (C : ∀ i, D i → Lp J 2 μ) (F : Lp J 2 μ) :
    ((∑ i, ∑ d, C i d) + F) =ᵐ[μ] fun t => (∑ i, ∑ d, C i d t) + F t := by
  simpa only [assembleTimeFlux, zero_smul, zero_add] using
    assembleTimeFlux_coeFn_ae μ 0 (0 : Lp J 2 μ) C F

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Identify bounded pointwise Galerkin observables with their common weak spacetime class. -/

variable {T H : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem scalarTrace_eq_of_weakLp_and_boundedConvergence (μ : Measure T) [IsFiniteMeasure μ]
    (U : ℕ → Lp H 2 μ) (W : Lp H 2 μ)
    (hw : ∀ L : Lp H 2 μ →L[ℝ] ℝ, Tendsto (fun n => L (U n)) atTop (𝓝 (L W)))
    (ell : H →L[ℝ] ℝ) (z : ℕ → T → ℝ) (g : T → ℝ) (B : ℝ)
    (hz : ∀ n, z n =ᵐ[μ] fun t => ell (U n t))
    (hg : AEStronglyMeasurable g μ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖z n t‖ ≤ B)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun n => z n t) atTop (𝓝 (g t))) :
    g =ᵐ[μ] fun t => ell (W t) := by
  have hzm (n : ℕ) : AEStronglyMeasurable (z n) μ :=
    (ell.continuous.comp_aestronglyMeasurable (Lp.memLp (U n)).aestronglyMeasurable).congr (hz n).symm
  have hgb : ∀ᵐ t ∂μ, ‖g t‖ ≤ B := by
    filter_upwards [hlim, ae_all_iff.mpr hb] with t ht hbt
    exact le_of_tendsto ht.norm (Eventually.of_forall hbt)
  have hgi : Integrable g μ := Integrable.of_bound hg B hgb
  have hwi : Integrable (fun t => ell (W t)) μ := by
    simpa only [Function.comp_def] using (ell.comp_memLp' (Lp.memLp W)).integrable (by norm_num)
  apply hgi.ae_eq_of_forall_setIntegral_eq g (fun t => ell (W t)) hwi
  intro s hs _
  have hc : Tendsto (fun n => ∫ t in s, z n t ∂μ) atTop (𝓝 (∫ t in s, g t ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => (hzm n).restrict) (integrable_const B)
      (fun n => ae_restrict_of_ae (hb n)) (ae_restrict_of_ae hlim)
  have he (n : ℕ) : (∫ t in s, z n t ∂μ) = ∫ t in s, ell (U n t) ∂μ :=
    integral_congr_ae (ae_restrict_of_ae (hz n))
  simp_rw [he] at hc
  exact tendsto_nhds_unique hc (scalarSetIntegral_weak_limit μ U W hw ell s hs)

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Finite sums of actual time L² classes preserve the tested subinterval pairings. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem timeClassPairing_doubleSum_add {ι : Type*} [Fintype ι] {δ : ι → Type*}
    [∀ i, Fintype (δ i)] {a b t : ℝ} (ht : t ∈ Set.Icc a b)
    (U : ∀ i, δ i → Lp H 2 (volume.restrict (Set.Icc a b)))
    (F : Lp H 2 (volume.restrict (Set.Icc a b))) (z : H) :
    (∫ s in a..t, inner ℝ (((∑ i, ∑ j, U i j) + F :
      Lp H 2 (volume.restrict (Set.Icc a b))) s) z) =
      (∑ i, ∑ j, ∫ s in a..t, inner ℝ (U i j s) z) + ∫ s in a..t, inner ℝ (F s) z := by
  let ell := timeTestIntegralCLM a b a t (fun _ => z) (memLp_const z)
  have he (V : Lp H 2 (volume.restrict (Set.Icc a b))) :
      ell V = ∫ s in a..t, inner ℝ (V s) z :=
    timeTestIntegralCLM_apply_class ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1 V
      (fun _ => z) (memLp_const z)
  rw [← he, map_add, map_sum]
  simp_rw [map_sum, he]
end

/-! Fixed-test subinterval integrals are linear in the genuine time L² readout class. -/

section
variable {H J : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J]

theorem timeClassReadoutPairing_sub {a b t : ℝ} (ht : t ∈ Set.Icc a b)
    (L : H →L[ℝ] J) (U V : Lp H 2 (volume.restrict (Set.Icc a b))) (z : J) :
    (∫ s in a..t, inner ℝ (L ((U - V) s)) z) =
      (∫ s in a..t, inner ℝ (L (U s)) z) - ∫ s in a..t, inner ℝ (L (V s)) z := by
  let ell := timeTestIntegralCLM a b a t (fun _ => z) (memLp_const z)
  have he (W : Lp H 2 (volume.restrict (Set.Icc a b))) :
      ell (L.compLpL 2 (volume.restrict (Set.Icc a b)) W) =
        ∫ s in a..t, inner ℝ (L (W s)) z := by
    rw [timeTestIntegralCLM_apply_class ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
      (L.compLpL 2 (volume.restrict (Set.Icc a b)) W) (fun _ => z) (memLp_const z)]
    apply intervalIntegral.integral_congr_ae_restrict
    have hs : Set.uIoc a t ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le ht.1]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs
      (ContinuousLinearMap.coeFn_compLpL L W)] with s hL
    rw [hL]
  have hs : (L.compLpL 2 (volume.restrict (Set.Icc a b))) (U - V) =
      (L.compLpL 2 (volume.restrict (Set.Icc a b))) U - (L.compLpL 2 (volume.restrict (Set.Icc a b))) V :=
    (L.compLpL 2 (volume.restrict (Set.Icc a b))).toLinearMap.map_sub U V
  have hl : ell ((L.compLpL 2 (volume.restrict (Set.Icc a b))) U -
      (L.compLpL 2 (volume.restrict (Set.Icc a b))) V) =
      ell ((L.compLpL 2 (volume.restrict (Set.Icc a b))) U) -
        ell ((L.compLpL 2 (volume.restrict (Set.Icc a b))) V) :=
    ell.toLinearMap.map_sub _ _
  rw [← he, hs, hl, he, he]
end

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Vanishing edge residuals leave precisely the external time flux. -/

variable {T J I : Type*} [MeasurableSpace T] [Fintype I]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

theorem assembleTimeFlux_zero_tendsto (μ : Measure T) {D : I → Type*} [∀ i, Fintype (D i)]
    (C : ℕ → ∀ i, D i → Lp J 2 μ) (F : Lp J 2 μ)
    (hC : ∀ i d, Tendsto (fun N => C N i d) atTop (𝓝 0)) :
    Tendsto (fun N => assembleTimeFlux μ 0 0 (C N) F) atTop (𝓝 F) := by
  have hs : Tendsto (fun N => ∑ i, ∑ d, C N i d) atTop (𝓝 (0 : Lp J 2 μ)) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
      (fun i _ => tendsto_finsetSum Finset.univ (fun d _ => hC i d))
  simpa only [assembleTimeFlux, zero_smul, zero_add] using
    hs.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => F) atTop (𝓝 F))

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public section
open Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Uniform Hilbert bounds for a bounded readout survive weak scalar convergence of its input. -/

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J] [CompleteSpace J]

theorem norm_clm_le_of_tendsto_inner (P : H →L[ℝ] J) {u : ℕ → H} {v : H} {R : ℝ}
    (hu : ∀ n, ‖P (u n)‖ ≤ R)
    (hlim : ∀ z : H, Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z))) :
    ‖P v‖ ≤ R := by
  apply norm_le_of_tendsto_inner hu
  intro z
  simpa only [ContinuousLinearMap.adjoint_inner_right] using hlim (P.adjoint z)

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! A vanishing uniform tail budget for an L¹ value source and L² divergence source. -/

variable {X H J Z : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup J] [NormedSpace ℝ J] [NormedAddCommGroup Z]

def bandSourceTailMajorant (P : H →L[ℝ] H) (Q : J →L[ℝ] J)
    (R : ℝ) (u : X → H) (F : X → J) (w : X → Z) (t : X) : ℝ :=
  4 * R * ‖P (u t) - u t‖ + 4 * (‖Q (F t) - F t‖ * ‖w t‖)

def bandSourceTailBudget (μ : Measure X) (P : H →L[ℝ] H) (Q : J →L[ℝ] J)
    (R : ℝ) (f : H) (u : X → H) (F : X → J) (w : X → Z) : ℝ :=
  2 * ‖P f - f‖ ^ 2 + ∫ t, bandSourceTailMajorant P Q R u F w t ∂μ

omit [MeasurableSpace X] in
theorem bandSourceTailMajorant_add (P Q : H →L[ℝ] H) (S T : J →L[ℝ] J)
    (R : ℝ) (u : X → H) (F : X → J) (w : X → Z) (t : X) :
    bandSourceTailMajorant P S R u F w t + bandSourceTailMajorant Q T R u F w t =
      4 * R * (‖P (u t) - u t‖ + ‖Q (u t) - u t‖) +
        4 * (‖S (F t) - F t‖ + ‖T (F t) - F t‖) * ‖w t‖ := by
  unfold bandSourceTailMajorant
  ring

theorem bandSourceTailMajorant_integrable (μ : Measure X)
    (P : H →L[ℝ] H) (Q : J →L[ℝ] J) (R : ℝ)
    (u : X → H) (hu : Integrable u μ) (F : X → J) (hF : MemLp F 2 μ)
    (w : X → Z) (hw : MemLp w 2 μ) :
    Integrable (bandSourceTailMajorant P Q R u F w) μ :=
  (((P.integrable_comp hu).sub hu).norm.const_mul (4 * R)).add
    ((AVRegularity.CoupledEnergy.Variational.contractingProjection_tail_product_integrable
      μ Q F hF w hw).const_mul 4)

theorem tendsto_bandSourceTailBudget (μ : Measure X)
    (P : ℕ → H →L[ℝ] H) (Q : ℕ → J →L[ℝ] J)
    (hP : ∀ n x, ‖P n x‖ ≤ ‖x‖) (hQ : ∀ n x, ‖Q n x‖ ≤ ‖x‖)
    (hPlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (hQlim : ∀ x, Tendsto (fun n => Q n x) atTop (𝓝 x))
    (R : ℝ) (f : H) (u : Lp H 1 μ) (F : X → J) (hF : MemLp F 2 μ)
    (w : X → Z) (hw : MemLp w 2 μ) :
    Tendsto (fun n => bandSourceTailBudget μ (P n) (Q n) R f u F w) atTop (𝓝 0) := by
  have hu := memLp_one_iff_integrable.mp (Lp.memLp u)
  have hi := ((((hPlim f).sub (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => f) atTop (𝓝 f))).norm).pow 2).const_mul 2
  have hv := (contractiveApproximation_timeL1_integral_tendsto μ P hP hPlim u).const_mul (4 * R)
  have hf := (AVRegularity.CoupledEnergy.Variational.contractingProjection_integral_tail_product_tendsto
    μ Q hQ hQlim F hF w hw).const_mul 4
  have he (n : ℕ) : bandSourceTailBudget μ (P n) (Q n) R f u F w =
      2 * ‖P n f - f‖ ^ 2 +
        ((4 * R) * ∫ t, ‖P n (u t) - u t‖ ∂μ) +
          4 * ∫ t, ‖Q n (F t) - F t‖ * ‖w t‖ ∂μ := by
    have h1 : Integrable (fun t => (4 * R) * ‖P n (u t) - u t‖) μ := by
      simpa only [Pi.sub_apply] using
        ((((P n).integrable_comp hu).sub hu).norm.const_mul (4 * R))
    have h2 := (AVRegularity.CoupledEnergy.Variational.contractingProjection_tail_product_integrable
      μ (Q n) F hF w hw).const_mul 4
    unfold bandSourceTailBudget bandSourceTailMajorant
    rw [integral_add h1 h2, integral_const_mul, integral_const_mul]
    ring
  simp only [he]
  simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add] using (hi.add hv).add hf

theorem tendsto_bandSourceTailBudget_of_integrable (μ : Measure X)
    (P : ℕ → H →L[ℝ] H) (Q : ℕ → J →L[ℝ] J)
    (hP : ∀ n x, ‖P n x‖ ≤ ‖x‖) (hQ : ∀ n x, ‖Q n x‖ ≤ ‖x‖)
    (hPlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (hQlim : ∀ x, Tendsto (fun n => Q n x) atTop (𝓝 x))
    (R : ℝ) (f : H) (u : X → H) (hu : Integrable u μ)
    (F : X → J) (hF : MemLp F 2 μ) (w : X → Z) (hw : MemLp w 2 μ) :
    Tendsto (fun n => bandSourceTailBudget μ (P n) (Q n) R f u F w) atTop (𝓝 0) := by
  have hU := memLp_one_iff_integrable.mpr hu
  let U : Lp H 1 μ := hU.toLp u
  have he (n : ℕ) : bandSourceTailBudget μ (P n) (Q n) R f u F w =
      bandSourceTailBudget μ (P n) (Q n) R f U F w := by
    unfold bandSourceTailBudget
    congr 1
    apply integral_congr_ae
    filter_upwards [hU.coeFn_toLp] with t ht
    change bandSourceTailMajorant (P n) (Q n) R u F w t =
      bandSourceTailMajorant (P n) (Q n) R (hU.toLp u) F w t
    unfold bandSourceTailMajorant
    rw [ht]
  simp only [he]
  exact tendsto_bandSourceTailBudget μ P Q hP hQ hPlim hQlim R f U F hF w hw

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Genuine field representatives survive finite time-flux assembly. -/

variable {T J I : Type*} [MeasurableSpace T] [Fintype I]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

theorem assembleTimeFlux_ae_of_fields (μ : Measure T) {D : I → Type*} [∀ i, Fintype (D i)]
    (ν : ℝ) (G : Lp J 2 μ) (C : ∀ i, D i → Lp J 2 μ) (F : Lp J 2 μ)
    (g f : T → J) (c : ∀ i, D i → T → J)
    (hg : G =ᵐ[μ] g) (hf : F =ᵐ[μ] f) (hc : ∀ i d, C i d =ᵐ[μ] c i d) :
    assembleTimeFlux μ ν G C F =ᵐ[μ] fun t => ν • g t + (∑ i, ∑ d, c i d t) + f t := by
  have hcc := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hc i))
  filter_upwards [assembleTimeFlux_coeFn_ae μ ν G C F, hg, hf, hcc] with t ht hg' hf' hc'
  rw [ht, hg', hf']
  have hs : (∑ i, ∑ d, C i d t) = ∑ i, ∑ d, c i d t := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro d _
    exact hc' i d
  rw [hs]

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! All coefficient jets required by the finite Sobolev orders of the statement are jointly
measurable. -/

variable {T E F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem orderedCoefficientDerivative_measurable (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (K j : ℕ)
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (C t)) (hj : j ≤ K) (w : DerivativeWord2 j) :
    Measurable (fun p : T × Vec 2 => orderedCoefficientDerivative (C p.1) j w p.2) := by
  induction j with
  | zero =>
    convert hC using 1
    ext p
    rfl
  | succ j ih =>
    have hprev := ih (Nat.le_trans (Nat.le_succ j) hj) (Fin.init w)
    have hs (t : T) : ContDiff ℝ (j + 1 : ℕ) (C t) :=
      (hc t).of_le (by exact_mod_cast hj)
    have hd (t : T) : Differentiable ℝ (orderedCoefficientDerivative (C t) j (Fin.init w)) :=
      (orderedCoefficientDerivative_contDiff (C t) j 1 (hs t) (Fin.init w)).differentiable
        (by norm_num)
    exact measurable_directionalDerivative
      (fun t => orderedCoefficientDerivative (C t) j (Fin.init w)) hprev hd
      (basisVec (w (Fin.last j)))

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Spatial torus separability. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
omit [BorelSpace E] [CompleteSpace E] in
/-- Spatial cell L² has a countable topology for finite-dimensional fibers. -/
theorem planeL2SecondCountableTopology :
    SecondCountableTopology (ComponentL2 (volume.restrict Set.univ) E) := by
  let : TopologicalSpace.SeparableSpace E := inferInstance
  let : SFinite (volume.restrict Set.univ : Measure (Vec 2)) := inferInstance
  let : MeasurableSpace.CountablyGenerated (Vec 2) := inferInstance
  let : IsSeparable (volume.restrict Set.univ : Measure (Vec 2)) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

omit [BorelSpace E] [CompleteSpace E] in
/-- The ambient finite Hilbert jet array is separable on the periodic cell. -/
theorem planeJetSeparableSpace (K : ℕ) : TopologicalSpace.SeparableSpace (JetL2 (volume.restrict Set.univ) K E) := by
  let : TopologicalSpace.SeparableSpace E := inferInstance
  let : SFinite (volume.restrict Set.univ : Measure (Vec 2)) := inferInstance
  let : MeasurableSpace.CountablyGenerated (Vec 2) := inferInstance
  let : IsSeparable (volume.restrict Set.univ : Measure (Vec 2)) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (ComponentL2 (volume.restrict Set.univ) E) := Lp.SecondCountableTopology
  let : SecondCountableTopology (JetL2 (volume.restrict Set.univ) K E) := PiLp.secondCountableTopology 2 _
  exact TopologicalSpace.SecondCountableTopology.to_separableSpace

/-- The periodic Sobolev graph is separable by its finite ambient Hilbert jets. -/
theorem planeHkSeparableSpace (K : ℕ) : TopologicalSpace.SeparableSpace (PlaneHk Set.univ K E) := by
  let : TopologicalSpace.SeparableSpace E := inferInstance
  let : SFinite (volume.restrict Set.univ : Measure (Vec 2)) := inferInstance
  let : MeasurableSpace.CountablyGenerated (Vec 2) := inferInstance
  let : IsSeparable (volume.restrict Set.univ : Measure (Vec 2)) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (ComponentL2 (volume.restrict Set.univ) E) := Lp.SecondCountableTopology
  let : SecondCountableTopology (JetL2 (volume.restrict Set.univ) K E) := PiLp.secondCountableTopology 2 _
  let : SecondCountableTopology (PlaneHk Set.univ K E) := inferInstance
  exact TopologicalSpace.SecondCountableTopology.to_separableSpace

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Uniform spectral tails identify a continuous representative of a Bochner class. -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem ae_norm_le_of_continuous_cutoff_bounds {a b : ℝ} (hab : a ≤ b)
    (u : ℝ → H) (P : ℕ → H →L[ℝ] H)
    (hP : ∀ x, Tendsto (fun N => P N x) atTop (𝓝 x))
    (q : ℕ → C(Set.Icc a b, H))
    (hae : ∀ N, extendCurve hab (q N) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => P N (u t))
    (R : ℝ) (hq : ∀ N t, ‖q N t‖ ≤ R) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖u t‖ ≤ R := by
  filter_upwards [ae_all_iff.mpr hae, ae_restrict_mem measurableSet_Icc] with t ht htm
  apply le_of_tendsto (hP (u t)).norm
  apply Filter.Eventually.of_forall
  intro N
  rw [← ht N, extendCurve_eq_of_mem hab (q N) htm]
  exact hq N ⟨t, htm⟩

theorem exists_continuous_timeRepresentative_of_spectral_tails {a b : ℝ} (hab : a ≤ b)
    (u : ℝ → H) (P : ℕ → H →L[ℝ] H)
    (hP : ∀ x, Tendsto (fun N => P N x) atTop (𝓝 x))
    (q : ℕ → C(Set.Icc a b, H)) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ n m t, ‖q n t - q m t‖ ^ 2 ≤ e n + e m)
    (hae : ∀ N, extendCurve hab (q N) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => P N (u t)) :
    ∃ U : C(Set.Icc a b, H), Tendsto q atTop (𝓝 U) ∧
      extendCurve hab U =ᵐ[volume.restrict (Set.Icc a b)] u := by
  obtain ⟨U, hU⟩ := cauchySeq_tendsto_of_complete
    (AVRegularity.CoupledEnergy.Variational.cauchySeq_continuousCurves_of_sqNorm_tail
      a b q e he hq)
  refine ⟨U, hU, ?_⟩
  filter_upwards [ae_all_iff.mpr hae, ae_restrict_mem measurableSet_Icc] with t ht htm
  have hc := (((continuous_eval_const (⟨t, htm⟩ : Set.Icc a b)).tendsto U).comp hU)
  change Tendsto (fun N => q N ⟨t, htm⟩) atTop (𝓝 (U ⟨t, htm⟩)) at hc
  have hp := hP (u t)
  have hh : (fun N => q N ⟨t, htm⟩) = fun N => P N (u t) := by
    funext N
    rw [← ht N, extendCurve_eq_of_mem hab (q N) htm]
  rw [hh] at hc
  rw [extendCurve_eq_of_mem hab U htm]
  exact tendsto_nhds_unique hc hp

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Every literal spatial weak jet of a plane Sobolev carrier belongs to L². -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeRawJet_memLp {K : ℕ} (q : PlaneHk Set.univ K E) (α : JetIndex2 K) :
    MemLp (q.toFunction.jet α) 2 volume := by
  simpa only [Measure.restrict_univ] using q.toFunction.memL2 α

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The principal drift mask is exactly the true transport of a raw finite weak jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem driftMaskTerm_principal {K j : ℕ} (hj : j ≤ K)
    (D : RawJet2 (K + 1) E) (v : Vec 2 → Vec 2)
    (m : PositionMask j) (hm : maskLeftLength j m = 0) (w : DerivativeWord2 j) (x : Vec 2) :
    driftMaskTerm hj v D m w x =
      ∑ k : Fin 2, v x k • D ⟨⟨j + 1, by omega⟩, Fin.snoc w k⟩ x := by
  change (∑ k : Fin 2, orderedCoefficientDerivative (driftCoefficient v)
    (maskLeftLength j m) (maskWordEquiv 2 j m w).1 x (PiLp.single 2 k 1) •
    D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩,
      Fin.snoc (maskWordEquiv 2 j m w).2 k⟩ x) = _
  have hc (r : ℕ) (hr : r = 0) (a : DerivativeWord2 r) :
      orderedCoefficientDerivative (driftCoefficient v) r a = driftCoefficient v := by
    subst r
    rfl
  rw [hc _ hm]
  apply Finset.sum_congr rfl
  intro k _
  have hw := zero_left_mask_word
    (fun r a => if hr : r ≤ K then D ⟨⟨r + 1, by omega⟩, Fin.snoc a k⟩ x else 0)
    j m hm w
  simp only [dite_eq_left ((maskRightLength_le j m).trans hj), dite_eq_left hj] at hw
  rw [hw]
  congr 1
  fin_cases k <;> simp [driftCoefficient]

theorem driftMaskTerm_principal_sum {K j : ℕ} (hj : j ≤ K)
    (D : RawJet2 (K + 1) E) (v : Vec 2 → Vec 2) (w : DerivativeWord2 j) (x : Vec 2) :
    (∑ m : PositionMask j, if maskLeftLength j m = 0 then driftMaskTerm hj v D m w x else 0) =
      ∑ k : Fin 2, v x k • D ⟨⟨j + 1, by omega⟩, Fin.snoc w k⟩ x := by
  have he (m : PositionMask j) :
      (if maskLeftLength j m = 0 then driftMaskTerm hj v D m w x else 0) =
      if maskLeftLength j m = 0 then
        ∑ k : Fin 2, v x k • D ⟨⟨j + 1, by omega⟩, Fin.snoc w k⟩ x else 0 := by
    split_ifs with hm
    · exact driftMaskTerm_principal hj D v m hm w x
    · rfl
  simp_rw [he]
  exact sum_zero_left_masks j _

end AVRegularity.CoupledEnergyPlane.Variational
end
end
