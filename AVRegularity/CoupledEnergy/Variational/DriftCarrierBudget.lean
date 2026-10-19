-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVenhance.Infra.Classical.PeriodicCalculus
import AVRegularity.CoupledEnergy.Variational.PullbackForm
public import AVRegularity.Sobolev.Multiply.OperatorProduct
import AVRegularity.CoupledEnergy.Variational.ConstantTimeTest
public import AVRegularity.Sobolev.Carrier
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Scalar observables of a weak Bochner subsequence can be tested on every
measurable time set. This is the fixed-test Galerkin limit mechanism. -/

variable {T H : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The set integral of a scalar continuous linear observable is a time L² dual map. -/
def scalarSetIntegralCLM (μ : Measure T) [IsFiniteMeasure μ]
    (s : Set T) (hs : MeasurableSet s) (ell : H →L[ℝ] ℝ) : Lp H 2 μ →L[ℝ] ℝ :=
  (innerSL ℝ (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ))).comp (ell.compLpL 2 μ)

theorem scalarSetIntegralCLM_apply (μ : Measure T) [IsFiniteMeasure μ]
    (s : Set T) (hs : MeasurableSet s) (ell : H →L[ℝ] ℝ) (U : Lp H 2 μ) :
    scalarSetIntegralCLM μ s hs ell U = ∫ t in s, ell (U t) ∂μ := by
  unfold scalarSetIntegralCLM
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  have he : (∫ t, inner ℝ (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ) t)
      (ell.compLpL 2 μ U t) ∂μ) = ∫ t, s.indicator (fun t => ell (U t)) t ∂μ := by
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs)
      (hμs := measure_ne_top μ s) (c := (1 : ℝ)), ell.coeFn_compLpL U] with t ht he
    rw [ht, he]
    by_cases hts : t ∈ s
    · simp only [Set.indicator_of_mem hts]
      simp
    · simp only [Set.indicator_of_notMem hts, inner_zero_left]
  rw [he, integral_indicator hs]

/-- Weak Bochner convergence gives convergence of all scalar set integrals. -/
theorem scalarSetIntegral_weak_limit (μ : Measure T) [IsFiniteMeasure μ]
    (U : ℕ → Lp H 2 μ) (V : Lp H 2 μ)
    (hw : ∀ L : Lp H 2 μ →L[ℝ] ℝ, Tendsto (fun n => L (U n)) atTop (𝓝 (L V)))
    (ell : H →L[ℝ] ℝ) (s : Set T) (hs : MeasurableSet s) :
    Tendsto (fun n => ∫ t in s, ell (U n t) ∂μ) atTop (𝓝 (∫ t in s, ell (V t) ∂μ)) := by
  simpa only [scalarSetIntegralCLM_apply] using hw (scalarSetIntegralCLM μ s hs ell)

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CoupledEnergy.Variational

/-! Scalar coefficient arrays act on finite Hilbert fibers with the same norm bound.
The proof decomposes the fiber in its orthonormal basis, applies the scalar
operator bound to each coordinate, and recombines by Parseval. -/

variable {J L E : Type*} [Fintype J] [DecidableEq J] [Fintype L]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The scalar coordinates of a finite Hilbert-valued array. -/
def fiberArrayCoordinate (U : PiLp 2 (fun _ : J => E))
    (e : Fin (Module.finrank ℝ E)) : PiLp 2 (fun _ : J => ℝ) :=
  WithLp.toLp 2 fun j => inner ℝ ((stdOrthonormalBasis ℝ E) e) (U j)

omit [DecidableEq J] [Fintype L] in
/-- Parseval commutes with the finite array sum. -/
theorem fiberArray_normSq_eq_sum_coordinate (U : PiLp 2 (fun _ : J => E)) :
    ‖U‖ ^ 2 = ∑ e : Fin (Module.finrank ℝ E), ‖fiberArrayCoordinate U e‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact ((stdOrthonormalBasis ℝ E).sum_sq_norm_inner_right (U j)).symm

/-- Lift a scalar finite-array operator by applying its matrix to each Hilbert fiber. -/
def scalarArrayAct (T : PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : L => ℝ))
    (U : PiLp 2 (fun _ : J => E)) : PiLp 2 (fun _ : L => E) :=
  WithLp.toLp 2 fun l => ∑ j, (T (PiLp.single 2 j 1) l) • U j

omit [Fintype L] in
/-- Fiber coordinates of the lifted array are exactly the original scalar operator action. -/
theorem scalarArrayAct_coordinate
    (T : PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : L => ℝ))
    (U : PiLp 2 (fun _ : J => E)) (e : Fin (Module.finrank ℝ E)) :
    fiberArrayCoordinate (scalarArrayAct T U) e = T (fiberArrayCoordinate U e) := by
  have heq : fiberArrayCoordinate U e =
      ∑ j : J, inner ℝ ((stdOrthonormalBasis ℝ E) e) (U j) • PiLp.single 2 j 1 := by
    apply PiLp.ext
    intro j
    simp [fiberArrayCoordinate, Pi.single_apply]
  rw [heq, map_sum]
  apply PiLp.ext
  intro l
  simp [fiberArrayCoordinate, scalarArrayAct, inner_sum, real_inner_smul_right, mul_comm]

/-- Lifting to a finite-dimensional Hilbert fiber introduces no dimension factor. -/
theorem scalarArrayAct_normSq_le
    (T : PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : L => ℝ))
    (U : PiLp 2 (fun _ : J => E)) :
    ‖scalarArrayAct T U‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖U‖ ^ 2 := by
  classical
  rw [fiberArray_normSq_eq_sum_coordinate]
  simp_rw [scalarArrayAct_coordinate]
  calc
    (∑ e : Fin (Module.finrank ℝ E), ‖T (fiberArrayCoordinate U e)‖ ^ 2) ≤
        ∑ e : Fin (Module.finrank ℝ E), ‖T‖ ^ 2 * ‖fiberArrayCoordinate U e‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg T) (norm_nonneg (fiberArrayCoordinate U e)))).mpr
          (T.le_opNorm (fiberArrayCoordinate U e))
    _ = ‖T‖ ^ 2 * ‖U‖ ^ 2 := by
      rw [← Finset.mul_sum, ← fiberArray_normSq_eq_sum_coordinate]

/-- The same operator bound in unsquared form. -/
theorem scalarArrayAct_norm_le
    (T : PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : L => ℝ))
    (U : PiLp 2 (fun _ : J => E)) : ‖scalarArrayAct T U‖ ≤ ‖T‖ * ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg U))).mp
  simpa only [mul_pow] using scalarArrayAct_normSq_le T U

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! The spectral-tail form of the Hilbert representative construction.
The uniform Cauchy argument, complete continuous-map limits and pointwise identification;
analytic tail estimates are discharged separately. -/

variable {H : Type*} [NormedAddCommGroup H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Uniform squared-norm tail estimates make continuous spectral curves Cauchy. -/
theorem cauchySeq_continuousCurves_of_sqNorm_tail (a b : ℝ)
    (q : ℕ → C(Icc a b, H)) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ n m t, ‖q n t - q m t‖ ^ 2 ≤ e n + e m) : CauchySeq q := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, e n < ε ^ 2 / 2 :=
    he.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < ε ^ 2 / 2))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, ?_⟩
  intro n hn m hm
  rw [ContinuousMap.dist_lt_iff hε]
  intro t
  rw [dist_eq_norm]
  have hsq := hq n m t
  have hn' := hN n hn
  have hm' := hN m hm
  nlinarith [norm_nonneg (q n t - q m t)]

/-- A trajectory identified pointwise by continuous spectral curves with
vanishing uniform tails has a unique continuous closed-time representative. -/
theorem existsUnique_hilbertRepresentative_of_spectral_tails (a b : ℝ) (u : ℝ → H)
    (q : ℕ → C(Icc a b, H)) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ n m t, ‖q n t - q m t‖ ^ 2 ≤ e n + e m)
    (hpoint : ∀ t : Icc a b, Tendsto (fun n => q n t) atTop (𝓝 (u t))) :
    ∃! U : C(Icc a b, H), ∀ t, U t = u t := by
  obtain ⟨U, hU⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_continuousCurves_of_sqNorm_tail a b q e he hq)
  have hident (t : Icc a b) : U t = u t :=
    tendsto_nhds_unique (((continuous_eval_const t).tendsto U).comp hU) (hpoint t)
  refine ⟨U, hident, ?_⟩
  intro V hV
  apply ContinuousMap.ext
  intro t
  exact (hV t).trans (hident t).symm

/-- The same spectral-tail construction proves strong continuity of the original trajectory. -/
theorem continuousOn_of_spectral_tails (a b : ℝ) (u : ℝ → H)
    (q : ℕ → C(Icc a b, H)) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hq : ∀ n m t, ‖q n t - q m t‖ ^ 2 ≤ e n + e m)
    (hpoint : ∀ t : Icc a b, Tendsto (fun n => q n t) atTop (𝓝 (u t))) :
    ContinuousOn u (Icc a b) := by
  obtain ⟨U, hU, _⟩ := existsUnique_hilbertRepresentative_of_spectral_tails a b u q e he hq hpoint
  rw [continuousOn_iff_continuous_domRestrict]
  have hu : (Icc a b).domRestrict u = U := by
    funext t
    exact (hU t).symm
  rw [hu]
  exact U.continuous

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CoupledEnergy.Variational

/-! Measurable evaluation of a strongly measurable operator action. Operator
norm measurability is unnecessary: continuity in the vector and measurability
on each fixed vector suffice. -/

variable {T H G : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Strong operator measurability permits evaluation along a measurable vector field. -/
theorem stronglyMeasurable_operator_action (L : T → H →L[ℝ] G)
    (hL : ∀ x, StronglyMeasurable (fun t => L t x))
    {u : T → H} (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun t => L t (u t)) := by
  have hm := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun t => (L t).continuous) hL
  exact hm.comp_measurable (hu.measurable.prodMk measurable_id)

/-- The evaluation statement also respects almost-everywhere representatives. -/
theorem aestronglyMeasurable_operator_action (L : T → H →L[ℝ] G)
    (hL : ∀ x, StronglyMeasurable (fun t => L t x))
    {μ : Measure T} {u : T → H} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun t => L t (u t)) μ := by
  have hm : AEStronglyMeasurable (fun t => L t (hu.mk u t)) μ :=
    (stronglyMeasurable_operator_action L hL hu.stronglyMeasurable_mk).aestronglyMeasurable
  apply hm.congr
  filter_upwards [hu.ae_eq_mk] with t ht
  rw [ht]

/-- Uniformly bounded strongly measurable operator actions preserve time L². -/
theorem memLp_operator_action (L : T → H →L[ℝ] G)
    (hL : ∀ x, StronglyMeasurable (fun t => L t x))
    {μ : Measure T} {u : T → H} (hu : MemLp u 2 μ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t, ‖L t‖ ≤ M) :
    MemLp (fun t => L t (u t)) 2 μ := by
  apply (hu.const_smul M).of_le
  · exact aestronglyMeasurable_operator_action L hL hu.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    calc
      ‖L t (u t)‖ ≤ ‖L t‖ * ‖u t‖ := (L t).le_opNorm _
      _ ≤ M * ‖u t‖ := mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _)
      _ = ‖M • u t‖ := by rw [norm_smul, Real.norm_of_nonneg hM]

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CoupledEnergy.Variational

/-! Pointwise time arithmetic with a fixed codomain instance. This keeps
finite carrier-family applications from reopening dependent norm searches. -/

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E]

theorem timeMemLp_zero (μ : Measure T) (p : ℝ≥0∞) :
    MemLp (fun _ : T => (0 : E)) p μ := MemLp.zero'

theorem timeIntegrable_zero (μ : Measure T) :
    Integrable (fun _ : T => (0 : E)) μ := integrable_zero _ _ _

theorem timeMemLp_pointwise_add (μ : Measure T) (p : ℝ≥0∞) (f g : T → E)
    (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (fun t => f t + g t) p μ := by
  simpa only [Pi.add_apply] using! hf.add hg

theorem timeMemLp_pointwise_sub (μ : Measure T) (p : ℝ≥0∞) (f g : T → E)
    (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (fun t => f t - g t) p μ := by
  simpa only [Pi.sub_apply] using! hf.sub hg

theorem timeIntegrable_pointwise_sub (μ : Measure T) (f g : T → E)
    (hf : Integrable f μ) (hg : Integrable g μ) : Integrable (fun t => f t - g t) μ := by
  simpa only [Pi.sub_apply] using! hf.sub hg

theorem timeContinuousOn_pointwise_sub {T : Type*} [TopologicalSpace T]
    (f g : T → E) (s : Set T) (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun t => f t - g t) s := hf.sub hg

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Componentwise time L¹ convergence controls the norm of the finite family. -/

section
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]

theorem timeL1_family_integrable (μ : Measure T) (f : ∀ i, T → E i)
    (hf : ∀ i, Integrable (f i) μ) : Integrable (fun t i => f i t) μ := by
  exact memLp_one_iff_integrable.mp (memLp_pi_iff.mpr
    (fun i => memLp_one_iff_integrable.mpr (hf i)))

theorem timeL1_family_integral_norm_tendsto (μ : Measure T)
    (r : ℕ → ∀ i, T → E i) (hr : ∀ n i, Integrable (r n i) μ)
    (hlim : ∀ i, Tendsto (fun n => ∫ t, ‖r n i t‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, ‖fun i => r n i t‖ ∂μ) atTop (𝓝 0) := by
  have hl : Tendsto (fun n => ∑ i, ∫ t, ‖r n i t‖ ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  apply squeeze_zero (fun n => integral_nonneg (fun t => norm_nonneg _)) _ hl
  intro n
  rw [← integral_finsetSum Finset.univ (fun i _ => (hr n i).norm)]
  apply integral_mono (timeL1_family_integrable μ (r n) (hr n)).norm
    (integrable_finsetSum Finset.univ (fun i _ => (hr n i).norm))
  intro t
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg (r n i t)))).mpr
  intro i
  exact Finset.single_le_sum (fun j _ => norm_nonneg (r n j t)) (Finset.mem_univ i)
end

/-! Vanishing time L¹ residuals preserve the integral of the value-source
norm, including when the original source is only time L¹. -/

section
variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E]

theorem timeL1_perturbed_integral_norm_tendsto (μ : Measure T)
    (f : T → E) (hf : Integrable f μ) (r : ℕ → T → E) (hr : ∀ n, Integrable (r n) μ)
    (hlim : Tendsto (fun n => ∫ t, ‖r n t‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, ‖f t + r n t‖ ∂μ) atTop (𝓝 (∫ t, ‖f t‖ ∂μ)) := by
  have hb (n : ℕ) : ‖(∫ t, ‖f t + r n t‖ ∂μ) - ∫ t, ‖f t‖ ∂μ‖ ≤ ∫ t, ‖r n t‖ ∂μ := by
    have ha : Integrable (fun t => ‖f t + r n t‖) μ := by
      simpa only [Pi.add_apply] using! (hf.add (hr n)).norm
    rw [← integral_sub ha hf.norm]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono (ha.sub hf.norm).norm (hr n).norm
    intro t
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, Pi.sub_apply] using! abs_norm_sub_norm_le (f t + r n t) (f t)
  have hz : Tendsto (fun n => ‖(∫ t, ‖f t + r n t‖ ∂μ) - ∫ t, ‖f t‖ ∂μ‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hb hlim
  have hh := tendsto_zero_iff_norm_tendsto_zero.mpr hz
  simpa only [sub_add_cancel, zero_add] using hh.add_const (∫ t, ‖f t‖ ∂μ)


theorem timeL1_integral_clm_norm_tendsto [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure T) (L : E →L[ℝ] F) (r : ℕ → T → E)
    (hr : ∀ n, Integrable (r n) μ)
    (hlim : Tendsto (fun n => ∫ t, ‖r n t‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, ‖L (r n t)‖ ∂μ) atTop (𝓝 0) := by
  have hl := hlim.const_mul ‖L‖
  simp only [mul_zero] at hl
  apply squeeze_zero (fun n => integral_nonneg (fun t => norm_nonneg _)) _ hl
  intro n
  rw [← integral_const_mul]
  have hi : Integrable (fun t => L (r n t)) μ := by
    simpa only [Function.comp_def] using!
      memLp_one_iff_integrable.mp (L.comp_memLp' (memLp_one_iff_integrable.mpr (hr n)))
  exact integral_mono hi.norm ((hr n).norm.const_mul ‖L‖) (fun t => L.le_opNorm (r n t))
end

/-! Convert actual temporal norm-square integrals to norms in the compiled
Bochner L² space, so finite sums and bounded linear maps preserve convergence. -/

section
variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem timeL2_toLp_norm_square (μ : Measure T) (u : T → E) (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ t, ‖u t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with t ht
  rw [ht, real_inner_self_eq_norm_sq]

theorem timeL2_norm_tendsto_zero_of_integral_square (μ : Measure T)
    (u : ℕ → T → E) (hu : ∀ n, MemLp (u n) 2 μ)
    (hs : Tendsto (fun n => ∫ t, ‖u n t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ‖(hu n).toLp (u n)‖) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ‖(hu n).toLp (u n)‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [timeL2_toLp_norm_square] using hs
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hh.sqrt

theorem timeL2_toLp_tendsto_zero_of_integral_square (μ : Measure T)
    (u : ℕ → T → E) (hu : ∀ n, MemLp (u n) 2 μ)
    (hs : Tendsto (fun n => ∫ t, ‖u n t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (timeL2_norm_tendsto_zero_of_integral_square μ u hu hs)
end

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Fixed temporal test functionals for Galerkin weak limits. The pairing
mechanism is that of a fixed-test Galerkin limit, expressed on an
abstract Hilbert carrier so it applies to each coupled Sobolev jet readout. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A fixed L² test supported on a subinterval defines a temporal dual vector. -/
def timeTestIntegralCLM (a b s t : ℝ) (w : ℝ → H)
    (hw : MemLp w 2 (volume.restrict (Icc a b))) :
    Lp H 2 (volume.restrict (Icc a b)) →L[ℝ] ℝ :=
  innerSL ℝ ((hw.indicator measurableSet_Ioc).toLp ((Ioc s t).indicator w))

/-- The dual vector evaluates to the literal time integral on the subinterval. -/
theorem timeTestIntegralCLM_apply {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (u w : ℝ → H) (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hw : MemLp w 2 (volume.restrict (Icc a b))) :
    timeTestIntegralCLM a b s t w hw (hu.toLp u) =
      ∫ r in s..t, inner ℝ (u r) (w r) := by
  unfold timeTestIntegralCLM
  rw [innerSL_apply_apply, L2.inner_def]
  have he : (∫ r in Icc a b,
      inner ℝ (((hw.indicator measurableSet_Ioc).toLp ((Ioc s t).indicator w)) r)
        ((hu.toLp u) r)) =
      ∫ r in Icc a b, (Ioc s t).indicator (fun r => inner ℝ (u r) (w r)) r := by
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, (hw.indicator measurableSet_Ioc).coeFn_toLp] with r hur hwr
    rw [hur, hwr]
    by_cases hr : r ∈ Ioc s t
    · simp only [indicator_of_mem hr, real_inner_comm]
    · simp only [indicator_of_notMem hr, inner_zero_left]
  rw [he, integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have hsub : Ioc s t ⊆ Icc a b :=
    Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)
  rw [inter_eq_left.mpr hsub, intervalIntegral.integral_of_le hst]

/-- The same formula uses the canonical representative of a Bochner class. -/
theorem timeTestIntegralCLM_apply_class {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (U : Lp H 2 (volume.restrict (Icc a b))) (w : ℝ → H)
    (hw : MemLp w 2 (volume.restrict (Icc a b))) :
    timeTestIntegralCLM a b s t w hw U = ∫ r in s..t, inner ℝ (U r) (w r) := by
  simpa only [Lp.toLp_coeFn] using timeTestIntegralCLM_apply hs ht hst U w (Lp.memLp U) hw

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus AVenhance.Infra.Classical
namespace AVRegularity.CoupledEnergy.Variational

/-! Divergence-free transport cancellation for arbitrary Hilbert-valued smooth periodic jets.
The integration-by-parts argument is copy-adapted from upstream `PeriodicCalculus`. -/

/-- The integral of divergence-free periodic transport of a scalar test is zero. -/
theorem periodic_transport_integral_zero (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hp : AVenhance.IsZ2Periodic v)
    (hd : ∀ x, ∑ k : Fin 2, fderiv ℝ v x (basisVec k) k = 0)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ 1 q) (hqp : AVenhance.IsZ2Periodic q) :
    (∫ x in AVenhance.unitCube, ∑ k : Fin 2,
      v x k * fderiv ℝ q x (basisVec k)) = 0 := by
  have hvk (k : Fin 2) : ContDiff ℝ 1 (fun x => v x k) := contDiff_pi.mp hv k
  have hqgrad (k : Fin 2) : Continuous (fun x => fderiv ℝ q x (basisVec k)) :=
    (hq.continuous_fderiv (by simp)).clm_apply continuous_const
  have hvgrad (k : Fin 2) : Continuous (fun x => fderiv ℝ (fun y => v y k) x (basisVec k)) :=
    ((hvk k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hgrad (k : Fin 2) (x : Vec 2) :
      fderiv ℝ (fun y => v y k) x (basisVec k) = fderiv ℝ v x (basisVec k) k := by
    have heq := ((ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ).hasFDerivAt.comp x
      (hv.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec k)) heq
  rw [← integral_unitCell_eq_unitCube]
  rw [integral_finsetSum Finset.univ
    (f := fun k x => v x k * fderiv ℝ q x (basisVec k)) (fun k _ =>
    PeriodicCalculus.continuous_integrableOn_unitCell ((hvk k).continuous.mul (hqgrad k)))]
  have hibp (k : Fin 2) :
      (∫ x in unitCell 2, v x k * fderiv ℝ q x (basisVec k)) =
        -∫ x in unitCell 2, fderiv ℝ (fun y => v y k) x (basisVec k) * q x := by
    exact integral_unitCell_coord_ibp_real k (hvk k) hq
      (fun n x => congrFun (hp n x) k) hqp
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ
    (f := fun k x => fderiv ℝ (fun y => v y k) x (basisVec k) * q x) (fun k _ =>
    PeriodicCalculus.continuous_integrableOn_unitCell ((hvgrad k).mul hq.continuous))]
  have hz : (fun x => ∑ k : Fin 2,
      fderiv ℝ (fun y => v y k) x (basisVec k) * q x) = fun _ => (0 : ℝ) := by
    funext x
    simp_rw [hgrad]
    rw [← Finset.sum_mul, hd, zero_mul]
  rw [hz, integral_zero, neg_zero]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The leading transport term cancels exactly, before estimating commutators. -/
theorem periodic_hilbert_transport_energy_zero (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hp : AVenhance.IsZ2Periodic v)
    (hd : ∀ x, ∑ k : Fin 2, fderiv ℝ v x (basisVec k) k = 0)
    (u : Vec 2 → E) (hu : ContDiff ℝ 1 u) (hup : AVenhance.IsZ2Periodic u) :
    (∫ x in AVenhance.unitCube, ∑ k : Fin 2,
      v x k * inner ℝ (fderiv ℝ u x (basisVec k)) (u x)) = 0 := by
  let q := fun x => inner ℝ (u x) (u x)
  have hq : ContDiff ℝ 1 q := hu.inner ℝ hu
  have hqp : AVenhance.IsZ2Periodic q := fun n x => by dsimp [q]; rw [hup n x]
  have hder (x : Vec 2) (k : Fin 2) :
      fderiv ℝ q x (basisVec k) = 2 * inner ℝ (fderiv ℝ u x (basisVec k)) (u x) := by
    rw [fderiv_inner_apply ℝ (hu.differentiable (by simp) x) (hu.differentiable (by simp) x),
      real_inner_comm (u x)]
    ring
  have hzero := periodic_transport_integral_zero v hv hp hd q hq hqp
  have hfun : (fun x => ∑ k : Fin 2, v x k * fderiv ℝ q x (basisVec k)) =
      fun x => 2 * ∑ k : Fin 2, v x k * inner ℝ (fderiv ℝ u x (basisVec k)) (u x) := by
    funext x
    simp_rw [hder, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfun] at hzero
  rw [integral_const_mul] at hzero
  linarith

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

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

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public section
open Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Pass strongly converging projected tests through a bounded weak Galerkin
sequence, as in the reused arbitrary-test variational limit argument. -/

variable {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Bounded weak trial convergence and strong test convergence pass through a fixed bilinear form. -/
theorem bilinear_weak_limit_moving_test (B : W →L[ℝ] H →L[ℝ] ℝ)
    (u : ℕ → H) (v : H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R)
    (hw : ∀ ell : H →L[ℝ] ℝ, Tendsto (fun n => ell (u n)) atTop (𝓝 (ell v)))
    (z : ℕ → W) (w : W) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => B (z n) (u n)) atTop (𝓝 (B w v)) := by
  have hb (n : ℕ) : ‖B (z n - w) (u n)‖ ≤ ‖B‖ * ‖z n - w‖ * R := by
    calc
      ‖B (z n - w) (u n)‖ ≤ ‖B (z n - w)‖ * ‖u n‖ := (B (z n - w)).le_opNorm _
      _ ≤ (‖B‖ * ‖z n - w‖) * ‖u n‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖B‖ * ‖z n - w‖ * R :=
        mul_le_mul_of_nonneg_left (hu n) (mul_nonneg (norm_nonneg B) (norm_nonneg (z n - w)))
  have hδ : Tendsto (fun n => z n - w) atTop (𝓝 0) := by
    simpa using hz.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => w) atTop (𝓝 w))
  have ht : Tendsto (fun n => ‖B‖ * ‖z n - w‖ * R) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖B‖) atTop (𝓝 ‖B‖)).mul hδ.norm).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => R) atTop (𝓝 R))
  have he : Tendsto (fun n => B (z n - w) (u n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hb ht)
  have h := he.add (hw (B w))
  simpa only [map_sub, sub_apply, sub_add_cancel, zero_add] using h

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CoupledEnergy.Variational

/-! Zero tests are zero almost everywhere; literal integrals must use that
fact rather than assume the chosen Lp representative vanishes pointwise. -/

variable {α H : Type*} [MeasurableSpace α] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem integral_inner_zeroLp (μ : Measure α) (u : α → H) :
    (∫ x, inner ℝ (u x) ((0 : Lp H 2 μ) x) ∂μ) = 0 := by
  calc
    _ = ∫ _, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero (E := H) (p := 2) (μ := μ)] with x hx
      simp only [hx, Pi.zero_apply, inner_zero_right]
    _ = 0 := integral_zero _ _

theorem integral_mul_inner_zeroLp (μ : Measure α) (c : α → ℝ) (u : α → H) :
    (∫ x, c x * inner ℝ (u x) ((0 : Lp H 2 μ) x) ∂μ) = 0 := by
  calc
    _ = ∫ _, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero (E := H) (p := 2) (μ := μ)] with x hx
      simp only [hx, Pi.zero_apply, inner_zero_right, mul_zero]
    _ = 0 := integral_zero _ _

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Strong time L² convergence of uniformly contracting projections. -/

section
variable {T H : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem contractingProjection_tail_square_integrable (μ : Measure T)
    (P : H →L[ℝ] H) (u : T → H) (hu : MemLp u 2 μ) :
    Integrable (fun t => ‖P (u t) - u t‖ ^ 2) μ := by
  have he := ((P.lipschitzWith.comp_memLp (map_zero P) hu).sub hu).norm
  simpa only [pow_two, Pi.mul_apply, Pi.sub_apply, Function.comp_def] using! he.integrable_mul he

theorem contractingProjection_integral_tail_square_tendsto (μ : Measure T)
    (P : ℕ → H →L[ℝ] H) (hp : ∀ n x, ‖P n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (u : T → H) (hu : MemLp u 2 μ) :
    Tendsto (fun n => ∫ t, ‖P n (u t) - u t‖ ^ 2 ∂μ) atTop (𝓝 0) :=
  contractingProjection_integral_normSq_sub_tendsto μ P hp hlim u hu
end

/-! Strong time L² residual convergence preserves squared forcing energies.
Bounded linear readouts preserve the same convergence. -/

section
variable {T E F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem timeL2_perturbed_integral_square_tendsto (μ : Measure T)
    (f : T → E) (hf : MemLp f 2 μ) (r : ℕ → T → E) (hr : ∀ n, MemLp (r n) 2 μ)
    (hlim : Tendsto (fun n => ∫ t, ‖r n t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, ‖f t + r n t‖ ^ 2 ∂μ) atTop (𝓝 (∫ t, ‖f t‖ ^ 2 ∂μ)) := by
  have hl := timeL2_toLp_tendsto_zero_of_integral_square μ r hr hlim
  have ha : Tendsto (fun n => hf.toLp f + (hr n).toLp (r n)) atTop (𝓝 (hf.toLp f)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hl
  have hh := ha.norm.pow 2
  have he (n : ℕ) : hf.toLp f + (hr n).toLp (r n) = (hf.add (hr n)).toLp (f + r n) :=
    (MemLp.toLp_add hf (hr n)).symm
  simpa only [he, timeL2_toLp_norm_square, Pi.add_apply] using! hh

theorem timeL2_toLp_clm (μ : Measure T) (L : E →L[ℝ] F) (u : T → E) (hu : MemLp u 2 μ) :
    (L.comp_memLp' hu).toLp (L ∘ u) = L.compLpL 2 μ (hu.toLp u) := by
  apply Lp.ext
  filter_upwards [(L.comp_memLp' hu).coeFn_toLp,
    ContinuousLinearMap.coeFn_compLpL L (hu.toLp u), hu.coeFn_toLp] with t ht hL hu'
  rw [ht, hL, hu']
  rfl

theorem timeL2_integral_square_clm_tendsto (μ : Measure T) (L : E →L[ℝ] F)
    (r : ℕ → T → E) (hr : ∀ n, MemLp (r n) 2 μ)
    (hlim : Tendsto (fun n => ∫ t, ‖r n t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, ‖L (r n t)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hl := timeL2_toLp_tendsto_zero_of_integral_square μ r hr hlim
  have hh := ((L.compLpL 2 μ).continuous.tendsto 0 |>.comp hl).norm.pow 2
  simp only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hh
  have he (n : ℕ) : ‖L.compLpL 2 μ ((hr n).toLp (r n))‖ ^ 2 = ∫ t, ‖L (r n t)‖ ^ 2 ∂μ := by
    rw [← timeL2_toLp_clm μ L (r n) (hr n), timeL2_toLp_norm_square]
    rfl
  simpa only [Function.comp_def, he] using hh
end

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! A uniformly bounded strongly measurable action gives one fixed Bochner
operator. Scalar testing of this operator is therefore preserved by weak limits. -/

variable {T H G : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (μ : Measure T) (L : T → H →L[ℝ] G)
  (hL : ∀ x, StronglyMeasurable (fun t => L t x))
  (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t, ‖L t‖ ≤ M)

/-- The actual time-dependent action on equivalence classes. -/
def timeOperatorValue (u : Lp H 2 μ) : Lp G 2 μ :=
  (memLp_operator_action L hL (Lp.memLp u) hM hb).toLp (fun t => L t (u t))

theorem timeOperatorValue_ae (u : Lp H 2 μ) :
    timeOperatorValue μ L hL M hM hb u =ᵐ[μ] fun t => L t (u t) :=
  (memLp_operator_action L hL (Lp.memLp u) hM hb).coeFn_toLp

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

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Residuals controlled by contracting projection tails vanish in time L²
and, on a finite time interval, in time L¹. -/

variable {T H Z : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Z]

theorem boundedResidual_integral_square_tendsto (μ : Measure T)
    (P : ℕ → H →L[ℝ] H) (hp : ∀ n x, ‖P n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (u : T → H) (hu : MemLp u 2 μ) (R : ℕ → T → Z)
    (hR : ∀ n, MemLp (R n) 2 μ) (B : ℝ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖R n t‖ ≤ B * ‖P n (u t) - u t‖) :
    Tendsto (fun n => ∫ t, ‖R n t‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hl := (contractingProjection_integral_tail_square_tendsto μ P hp hlim u hu).const_mul (B ^ 2)
  simp only [mul_zero] at hl
  apply squeeze_zero (fun n => integral_nonneg (fun t => sq_nonneg _)) _ hl
  intro n
  rw [← integral_const_mul]
  have hi : Integrable (fun t => ‖R n t‖ ^ 2) μ := by
    simpa only [pow_two, Pi.mul_apply] using! (hR n).norm.integrable_mul (hR n).norm
  apply integral_mono_ae hi ((contractingProjection_tail_square_integrable μ (P n) u hu).const_mul (B ^ 2))
  filter_upwards [hb n] with t ht
  have hh := mul_self_le_mul_self (norm_nonneg _) ht
  nlinarith [norm_nonneg (P n (u t) - u t)]


theorem boundedResidual_integral_norm_tendsto (μ : Measure T) [IsFiniteMeasure μ]
    (P : ℕ → H →L[ℝ] H) (hp : ∀ n x, ‖P n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (u : T → H) (hu : MemLp u 2 μ) (R : ℕ → T → Z)
    (hR : ∀ n, MemLp (R n) 2 μ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖R n t‖ ≤ B * ‖P n (u t) - u t‖) :
    Tendsto (fun n => ∫ t, ‖R n t‖ ∂μ) atTop (𝓝 0) := by
  have hi : Integrable (fun t => (2 * B) * ‖u t‖) μ :=
    (hu.integrable (by norm_num)).norm.const_mul (2 * B)
  have hd (n : ℕ) : ∀ᵐ t ∂μ, ‖‖R n t‖‖ ≤ (2 * B) * ‖u t‖ := by
    filter_upwards [hb n] with t ht
    rw [norm_norm]
    have hn : ‖P n (u t) - u t‖ ≤ 2 * ‖u t‖ :=
      (norm_sub_le _ _).trans (by linarith [hp n (u t)])
    exact ht.trans (by nlinarith)
  have ht : ∀ᵐ t ∂μ, Tendsto (fun n => ‖R n t‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_all_iff.mpr hb] with t ht
    have hl := (((hlim (u t)).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => u t) atTop (𝓝 (u t)))).norm).const_mul B
    simp only [sub_self, norm_zero, mul_zero] at hl
    exact squeeze_zero (fun n => norm_nonneg _) ht hl
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun t => (2 * B) * ‖u t‖) (fun n => (hR n).aestronglyMeasurable.norm) hi hd ht

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Ordered spatial coefficient differentiation commutes with constant continuous linear maps. -/

section
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Fixed operator-valued linear maps commute with all ordered coefficient derivatives. -/
theorem orderedCoefficientDerivative_linearMap
    (L : (E →L[ℝ] F) →L[ℝ] (G →L[ℝ] H))
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (↑(⊤ : ℕ∞)) C)
    (j : ℕ) (w : DerivativeWord2 j) (x : Vec 2) :
    orderedCoefficientDerivative (fun y => L (C y)) j w x =
      L (orderedCoefficientDerivative C j w x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    simp only [orderedCoefficientDerivative]
    have heq : orderedCoefficientDerivative (fun z => L (C z)) j (Fin.init w) =
        fun y => L (orderedCoefficientDerivative C j (Fin.init w) y) := by
      funext y
      exact ih (Fin.init w) y
    rw [heq]
    have hc : ContDiff ℝ 1 (orderedCoefficientDerivative C j (Fin.init w)) :=
      orderedCoefficientDerivative_contDiff C j 1 (hC.of_le (by simp)) (Fin.init w)
    have hd := (L.hasFDerivAt.comp x (hc.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun T : Vec 2 →L[ℝ] (G →L[ℝ] H) => T (basisVec (w (Fin.last j)))) hd
end

/-! The zeroth coefficient derivative array preserves the operator norm.
This discharges the value-order part of the literal velocity budget. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientDerivativeArray_zero_norm (C : Vec 2 → E →L[ℝ] F) (x : Vec 2) :
    ‖coefficientDerivativeArray C 0 x‖ = ‖C x‖ := by
  have hn (z : E) : ‖coefficientDerivativeArray C 0 x z‖ = ‖C x z‖ := by
    have hs := coefficientDerivativeArray_normSq C 0 x z
    simp only [orderedCoefficientDerivative_zero] at hs
    simp at hs
    nlinarith [norm_nonneg (coefficientDerivativeArray C 0 x z), norm_nonneg (C x z)]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    rw [hn]
    exact (C x).le_opNorm z
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    rw [← hn]
    exact (coefficientDerivativeArray C 0 x).le_opNorm z
end

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The unique positional mask with no coefficient derivatives preserves the entire word. -/

/-- There is exactly one positional mask with no selected positions. -/
theorem sum_zero_left_masks {E : Type*} [AddCommMonoid E] (j : ℕ) (z : E) :
    (∑ m : PositionMask j, if maskLeftLength j m = 0 then z else 0) = z := by
  induction j with
  | zero => simp [PositionMask, maskLeftLength]
  | succ j ih =>
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, maskLeftLength, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ite_false, zero_add]
    exact ih

/-- A zero-selection mask retains the full ordered word in any dependent derivative family. -/
theorem zero_left_mask_word {E : Type*} (H : (r : ℕ) → DerivativeWord2 r → E)
    (j : ℕ) (m : PositionMask j) (hm : maskLeftLength j m = 0) (w : DerivativeWord2 j) :
    H (maskRightLength j m) (maskWordEquiv 2 j m w).2 = H j w := by
  induction j generalizing H with
  | zero => exact congrArg (H 0) (Subsingleton.elim _ _)
  | succ j ih =>
    obtain ⟨m, b⟩ := m
    cases b with
    | true => simp [maskLeftLength] at hm
    | false =>
      have hw : w = Fin.snoc (Fin.init w) (w (Fin.last j)) :=
        (Fin.snoc_init_self w).symm
      rw [hw, maskWordEquiv_snoc_false]
      exact ih (fun r a => H (r + 1) (Fin.snoc a (w (Fin.last j)))) m hm (Fin.init w)

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Match pointwise scalar Galerkin traces to the canonical spacetime class.
Actual continuous finite trajectories may differ from the Lp representative
on null sets; the identification explicitly keeps that distinction. -/

variable {T H : Type*} [MeasurableSpace T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A bounded pointwise observable limit is the observable of the weak L² limit almost everywhere. -/
theorem weakLp_scalar_trace_eq_ae (μ : Measure T) [IsFiniteMeasure μ]
    (U : ℕ → Lp H 2 μ) (V : Lp H 2 μ)
    (hw : ∀ L : Lp H 2 μ →L[ℝ] ℝ, Tendsto (fun n => L (U n)) atTop (𝓝 (L V)))
    (ell : H →L[ℝ] ℝ) (z : ℕ → T → ℝ) (u : T → ℝ) (B : ℝ)
    (hz : ∀ n, z n =ᵐ[μ] fun t => ell (U n t))
    (hu : AEStronglyMeasurable u μ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖z n t‖ ≤ B)
    (ht : ∀ᵐ t ∂μ, Tendsto (fun n => z n t) atTop (𝓝 (u t))) :
    u =ᵐ[μ] fun t => ell (V t) := by
  have hm (n : ℕ) : AEStronglyMeasurable (z n) μ :=
    (ell.continuous.comp_aestronglyMeasurable (Lp.memLp (U n)).aestronglyMeasurable).congr
      (hz n).symm
  have hv : Integrable (fun t => ell (V t)) μ :=
    (ell.comp_memLp V).integrable (by norm_num)
  apply boundedScalarTrace_eq_ae μ z u (fun t => ell (V t)) B hm hu hv hb ht
  intro s hs
  apply (scalarSetIntegral_weak_limit μ U V hw ell s hs).congr'
  filter_upwards [] with n
  exact (integral_congr_ae (ae_restrict_of_ae (hz n))).symm

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoupledEnergy.Variational

/-! Spatial torus separability. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
omit [BorelSpace E] [CompleteSpace E] in
/-- Spatial cell L² has a countable topology for finite-dimensional fibers. -/
theorem cellL2SecondCountableTopology :
    SecondCountableTopology (ComponentL2 (volume.restrict AVenhance.unitCube) E) := by
  let : TopologicalSpace.SeparableSpace E := inferInstance
  let : SFinite (volume.restrict AVenhance.unitCube : Measure (Vec 2)) := inferInstance
  let : MeasurableSpace.CountablyGenerated (Vec 2) := inferInstance
  let : IsSeparable (volume.restrict AVenhance.unitCube : Measure (Vec 2)) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

omit [BorelSpace E] [CompleteSpace E] in
/-- The ambient finite Hilbert jet array is separable on the periodic cell. -/
theorem torusJetSeparableSpace (K : ℕ) : TopologicalSpace.SeparableSpace (JetL2 (volume.restrict AVenhance.unitCube) K E) := by
  let : TopologicalSpace.SeparableSpace E := inferInstance
  let : SFinite (volume.restrict AVenhance.unitCube : Measure (Vec 2)) := inferInstance
  let : MeasurableSpace.CountablyGenerated (Vec 2) := inferInstance
  let : IsSeparable (volume.restrict AVenhance.unitCube : Measure (Vec 2)) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (ComponentL2 (volume.restrict AVenhance.unitCube) E) := Lp.SecondCountableTopology
  let : SecondCountableTopology (JetL2 (volume.restrict AVenhance.unitCube) K E) := PiLp.secondCountableTopology 2 _
  exact TopologicalSpace.SecondCountableTopology.to_separableSpace

/-- The periodic Sobolev graph is separable by its finite ambient Hilbert jets. -/
theorem torusHkSeparableSpace (K : ℕ) : TopologicalSpace.SeparableSpace (TorusHk K E) := by
  let : TopologicalSpace.SeparableSpace E := inferInstance
  let : SFinite (volume.restrict AVenhance.unitCube : Measure (Vec 2)) := inferInstance
  let : MeasurableSpace.CountablyGenerated (Vec 2) := inferInstance
  let : IsSeparable (volume.restrict AVenhance.unitCube : Measure (Vec 2)) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (ComponentL2 (volume.restrict AVenhance.unitCube) E) := Lp.SecondCountableTopology
  let : SecondCountableTopology (JetL2 (volume.restrict AVenhance.unitCube) K E) := PiLp.secondCountableTopology 2 _
  let : SecondCountableTopology (TorusHk K E) := inferInstance
  exact TopologicalSpace.SecondCountableTopology.to_separableSpace

end AVRegularity.CoupledEnergy.Variational
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The original bounded velocity and derivative envelope supply every
order of the finite multiplication budget for the weak transport carrier. -/

theorem driftCoefficient_norm_le (v : Vec 2 → Vec 2) (V : ℝ) (hV : 0 ≤ V)
    (hb : ∀ x, ‖v x‖ ≤ V) (x : Vec 2) : ‖driftCoefficient v x‖ ≤ 2 * V := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hV)
  intro z
  change ‖∑ k : Fin 2, v x k * z k‖ ≤ _
  calc
    _ ≤ ∑ k : Fin 2, ‖v x k * z k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 2, V * ‖z‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (v x) k).trans (hb x))
        (PiLp.norm_apply_le z k) (norm_nonneg _) hV
    _ = (2 * V) * ‖z‖ := by simp; ring

/-- A finite budget includes bounded velocity at order zero and the prescribed positive-order jets. -/
def driftCarrierBudget (K : ℕ) (V α B lam : ℝ) (l : Fin (K + 1)) : ℝ :=
  if l.val = 0 then 2 * V else α * B ^ l.val * (l.val.factorial : ℝ) * lam ^ ((1 : ℤ) - l.val)

theorem driftCarrierBudget_bounds (K : ℕ) (v : Vec 2 → Vec 2)
    (V α B lam : ℝ) (hV : 0 ≤ V) (hv : ∀ x, ‖v x‖ ≤ V)
    (hjets : ∀ l, 1 ≤ l → l ≤ K → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    ∀ l x, ‖coefficientDerivativeArray (driftCoefficient v) l.val x‖ ≤
      driftCarrierBudget K V α B lam l := by
  intro l x
  by_cases hl : l.val = 0
  · simp only [driftCarrierBudget, hl, ite_true]
    change ‖coefficientDerivativeArray (driftCoefficient v) l.val x‖ ≤ 2 * V
    rw [hl, coefficientDerivativeArray_zero_norm]
    exact driftCoefficient_norm_le v V hV hv x
  · simp only [driftCarrierBudget, hl, ite_false]
    exact hjets l.val (by omega) (Nat.le_of_lt_succ l.isLt) x

end AVRegularity.CoupledEnergy.Variational
end
end
