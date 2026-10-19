-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
public import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.Construction.Preservation.FullLift.KernelStrongEnergy
import AVRegularity.CycleComparison.Coarse.Meas.Pairing
public import AVRegularity.EntryWeak.SourceParameterPeriodicity
import AVRegularity.CycleComparison.Coarse.Defect.CovCommute
public import AVRegularity.Construction.Residual.Presentation.ProofMeanFluxSplit
public import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

section
section
/-! # The radius comparison without time measurability

`strongEnergy_mul_radius_le'`: `𝓔_{Aρ} ≤ A^K 𝓔_ρ` for `A ≥ 1` at the orders `K, K + 1`. The
cascade version `strongEnergy_mul_radius_le` needs `AEMeasurable` of the gradient norm of `w`; here
the constant is pulled out of the lower integral with `lintegral_const_mul'`, which needs none.

Degenerate case: `A = 1`: `𝓔_ρ ≤ 𝓔_ρ`. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem strongEnergy_mul_radius_le' {K : ℕ} {A : ℝ} (hA : 1 ≤ A) (ρ ν a b : ℝ)
    (π : ι → ℝ) (u : ∀ i, ℝ → TorusHk K (h i)) (w : ∀ i, ℝ → TorusHk (K + 1) (h i)) :
    strongEnergy (A * ρ) ν π a b u w ≤ ENNReal.ofReal (A ^ K) * strongEnergy ρ ν π a b u w := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  set c : ℝ≥0∞ := ENNReal.ofReal (A ^ (2 * K)) with hc
  have hroot : c ^ (1 / 2 : ℝ) = ENNReal.ofReal (A ^ K) := by
    rw [hc, ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hA0 _) (by norm_num), ← Real.sqrt_eq_rpow,
      pow_mul', Real.sqrt_sq (pow_nonneg hA0 _)]
  unfold strongEnergy
  rw [← hroot, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_left_comm]
  refine mul_le_mul_right ?_ _
  have h1 : (⨆ t ∈ Set.Icc a b, ENNReal.ofReal (factorialNormSq (A * ρ) (u i t).val)) ≤
      c * ⨆ t ∈ Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (u i t).val) := by
    refine iSup₂_le fun t ht => ?_
    refine (ENNReal.ofReal_le_ofReal (factorialNormSq_mul_radius_le hA ρ (u i t).val)).trans ?_
    rw [ENNReal.ofReal_mul (pow_nonneg hA0 _)]
    exact mul_le_mul_right (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc a b) =>
      ENNReal.ofReal (factorialNormSq ρ (u i t).val)) t ht) _
  have h2 : ∫⁻ s in Set.Icc a b, ENNReal.ofReal (gradFactorialNormSq (A * ρ) (w i s).val) ≤
      c * ∫⁻ s in Set.Icc a b, ENNReal.ofReal (gradFactorialNormSq ρ (w i s).val) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun s => ?_
    refine (ENNReal.ofReal_le_ofReal (gradFactorialNormSq_mul_radius_le hA ρ (w i s).val)).trans ?_
    rw [ENNReal.ofReal_mul (pow_nonneg hA0 _)]
  calc _ ≤ c * (⨆ t ∈ Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (u i t).val)) +
        ENNReal.ofReal ν * (c * ∫⁻ s in Set.Icc a b,
          ENNReal.ofReal (gradFactorialNormSq ρ (w i s).val)) := add_le_add h1
          (mul_le_mul_right h2 _)
    _ = _ := by rw [mul_left_comm (ENNReal.ofReal ν), mul_add]

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! **A periodic average of small width moves a fixed class little.** For a mass-one
integrable kernel `κ`, a fixed matrix `H` and a fixed `f ∈ L²(cell)`, `‖A_{r,H} f - f‖ → 0` as
`r → 0`. The paired kernel is the composition of two such averages, each of norm at most one for
a moment kernel of a nonnegative mass-one template.

Degenerate cases:
- `r = 0`: the average is the identity (`periodicComponentAverage_zero`).
- `f = 0`: both sides vanish. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Analysis.Convolution Filter Topology

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-- The periodic average `A_{r,H}` of a mass-one kernel converges strongly to the identity as the
width tends to `0`. -/
theorem ckerShift_tendsto {κ : Vec 2 → ℝ} (hκ : Integrable κ) (hmass : ∫ z, κ z = 1)
    (H : Vec 2 →L[ℝ] Vec 2) (f : Lp ℝ 2 (volume.restrict AVenhance.unitCube)) :
    Tendsto (fun r : ℝ => ‖periodicComponentAverage (E := ℝ) (displacement r H)
      (continuous_displacement r H) κ hκ f - f‖) (𝓝 0) (𝓝 0) := by
  set g := (cellToTorus (E := ℝ)) f with hg
  have hnorm : ∀ r : ℝ, ‖periodicComponentAverage (E := ℝ) (displacement r H)
      (continuous_displacement r H) κ hκ f - f‖ =
      ‖averagingOperator (torusQuotient.comp (displacement r H))
        (continuous_torusQuotient.comp (continuous_displacement r H)) κ hκ g - g‖ := by
    intro r
    have h1 : periodicComponentAverage (E := ℝ) (displacement r H)
        (continuous_displacement r H) κ hκ f - f =
        torusToCell (averagingOperator (torusQuotient.comp (displacement r H))
          (continuous_torusQuotient.comp (continuous_displacement r H)) κ hκ g - g) := by
      rw [map_sub, hg, torusToCell_cellToTorus]
      rfl
    rw [h1, LinearIsometry.norm_map]
  simp_rw [hnorm]
  have hdiff : ∀ r : ℝ, averagingOperator (torusQuotient.comp (displacement r H))
        (continuous_torusQuotient.comp (continuous_displacement r H)) κ hκ g - g =
      ∫ z : Vec 2, κ z • (translation (torusQuotient (r • H z)) g - g) := by
    intro r
    have hc := continuous_torusQuotient.comp (continuous_displacement r H)
    have e1 := integrable_average_integrand (torusQuotient.comp (displacement r H)) hc hκ g
    have e2 : Integrable (fun z : Vec 2 => κ z • g) := hκ.smul_const g
    have hg' : (∫ z : Vec 2, κ z • g) = g := by
      rw [integral_smul_const, hmass, one_smul]
    rw [averagingOperator_apply]
    calc (∫ z : Vec 2, κ z • translation ((torusQuotient.comp (displacement r H)) z) g) - g
        = (∫ z : Vec 2, κ z • translation ((torusQuotient.comp (displacement r H)) z) g) -
          ∫ z : Vec 2, κ z • g := by rw [hg']
      _ = ∫ z : Vec 2, (κ z • translation ((torusQuotient.comp (displacement r H)) z) g -
          κ z • g) := (integral_sub e1 e2).symm
      _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [smul_sub]
        rfl
  have hle : ∀ r : ℝ, ‖averagingOperator (torusQuotient.comp (displacement r H))
        (continuous_torusQuotient.comp (continuous_displacement r H)) κ hκ g - g‖ ≤
      ∫ z : Vec 2, ‖κ z‖ * ‖translation (torusQuotient (r • H z)) g - g‖ := by
    intro r
    rw [hdiff r]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [norm_smul]
  have hlim : Tendsto (fun r : ℝ => ∫ z : Vec 2, ‖κ z‖ *
      ‖translation (torusQuotient (r • H z)) g - g‖) (𝓝 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (Vec 2))) (l := 𝓝 (0 : ℝ))
      (F := fun (r : ℝ) (z : Vec 2) => ‖κ z‖ * ‖translation (torusQuotient (r • H z)) g - g‖)
      (f := fun _ => (0 : ℝ)) (fun z => 2 * ‖g‖ * ‖κ z‖) ?_ ?_ ?_ ?_
    · simpa using this
    · refine Eventually.of_forall fun r => ?_
      have hc : Continuous fun z : Vec 2 => translation (torusQuotient (r • H z)) g :=
        (continuous_translation g).comp
          (continuous_torusQuotient.comp (by fun_prop : Continuous fun z : Vec 2 => r • H z))
      exact hκ.norm.aestronglyMeasurable.mul (hc.sub continuous_const).norm.aestronglyMeasurable
    · refine Eventually.of_forall fun r => Eventually.of_forall fun z => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      have : ‖translation (torusQuotient (r • H z)) g - g‖ ≤ 2 * ‖g‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [translation_norm]; linarith
      calc ‖κ z‖ * ‖translation (torusQuotient (r • H z)) g - g‖ ≤ ‖κ z‖ * (2 * ‖g‖) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = 2 * ‖g‖ * ‖κ z‖ := by ring
    · exact (hκ.norm.const_mul (2 * ‖g‖))
    · refine Eventually.of_forall fun z => ?_
      have hT : Tendsto (fun r : ℝ => translation (torusQuotient (r • H z)) g) (𝓝 0)
          (𝓝 (translation (torusQuotient ((0 : ℝ) • H z)) g)) :=
        (((continuous_translation g).comp
          (continuous_torusQuotient.comp (continuous_id.smul continuous_const))).tendsto 0)
      have h0 : translation (torusQuotient ((0 : ℝ) • H z)) g = g := by
        simp
      rw [h0] at hT
      have := ((hT.sub_const g).norm).const_mul ‖κ z‖
      simpa using this
  exact squeeze_zero (fun r => norm_nonneg _) hle hlim

/-- **The isotropic paired kernel of small width moves a fixed class little**: for a nonnegative
mass-one template, `‖S_{r} f - f‖ → 0` as `r → 0`, for every time `t`. -/
theorem ckerShift_iso_tendsto {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (hnn : ∀ z, 0 ≤ φ₀ z)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) (t : ℝ) (f : Lp ℝ 2 (volume.restrict AVenhance.unitCube)) :
    Tendsto (fun r : ℝ => ‖(isoPairedKernel r n).op φ₀ hφ₀ (E := ℝ) t f - f‖) (𝓝 0) (𝓝 0) := by
  have hk := integral_momentKernel hφ₀ hmass n
  have h1 := ckerShift_tendsto (integrable_momentKernel hφ₀ n) hk
    ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)) f
  have h2 := h1.const_mul 2
  rw [mul_zero] at h2
  refine squeeze_zero (fun r => norm_nonneg _) (fun r => ?_) h2
  set P := periodicComponentAverage (E := ℝ)
    (displacement r ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)))
    (continuous_displacement r _) (momentKernel φ₀ n) (integrable_momentKernel hφ₀ n) with hP
  have hop : (isoPairedKernel r n).op φ₀ hφ₀ (E := ℝ) t f - f = P (P f - f) + (P f - f) := by
    simp only [KernelSpec.op, isoPairedKernel, ContinuousLinearMap.coe_comp, Function.comp_apply,
      map_sub]
    abel
  rw [hop]
  have hc : ‖P (P f - f)‖ ≤ ‖P f - f‖ :=
    periodicComponentAverage_momentKernel_norm _ _ hφ₀ hnn hmass n _
  calc _ ≤ ‖P (P f - f)‖ + ‖P f - f‖ := norm_add_le _ _
    _ ≤ 2 * ‖P f - f‖ := by linarith

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! # Generic measurability tools

The time-measurability of the lifted field of the terminal context is strict (Borel) joint
measurability in `(t, x)`. The tools, none of which mentions the construction:

* `measurable_joint`: a function measurable in `t` at each point and continuous in the point
  at each `t` is jointly measurable (Mathlib's Carathéodory lemma, in the order used here).
* `measurable_eval_of_l2`: a family `F t` of continuous periodic functions which is
  continuous in `t` into `L²` of the cell is measurable in `t` at EVERY point: the value at a point
  is the limit of the averages over small boxes, and each average is continuous in `t`.
* `measurable_of_separating`: a function into a finite-dimensional space whose pairings with
  a separating family of functionals are measurable has all its pairings measurable.
* `measurable_orderedDerivative`: word derivatives of a jointly measurable family of `C^m`
  functions are jointly measurable (limits of difference quotients).

Degenerate cases: `m = 0` (no derivative); an empty family of functionals separates only `U = ⊥`;
`I = ∅` (the time type is empty). -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-- **Carathéodory**: measurable in the first variable at each point, continuous in the second
variable at each parameter, gives joint measurability. -/
theorem measurable_joint {T : Type*} [MeasurableSpace T] {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [SecondCountableTopology Y]
    [OpensMeasurableSpace Y] {β : Type*} [MeasurableSpace β] [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β] (f : T → Y → β)
    (hc : ∀ t, Continuous (f t)) (hm : ∀ y, Measurable fun t => f t y) :
    Measurable fun p : T × Y => f p.1 p.2 :=
  (measurable_uncurry_of_continuous_of_measurable (u := fun y t => f t y) hc hm).comp
    measurable_swap

/-- A function which is measurable on a measurable set, cut off outside it, is measurable. -/
theorem measurable_indicator {T : Type*} [MeasurableSpace T] {β : Type*} [MeasurableSpace β]
    [Zero β] {s : Set T} (hs : MeasurableSet s) (f : T → β)
    (hf : Measurable fun z : s => f z.1) : Measurable (s.indicator f) := by
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · have he : s.domRestrict (s.indicator f) = fun z : s => f z.1 := by
      funext z
      exact Set.indicator_of_mem z.2 f
    rw [he]
    exact hf
  · have he : sᶜ.domRestrict (s.indicator f) = fun _ => 0 := by
      funext z
      exact Set.indicator_of_notMem z.2 f
    rw [he]
    exact measurable_const

/-- **Separation.** If the functionals `φ j` separate the points of a subspace `U` of a
finite-dimensional space and `c` takes values in `U`, measurability of every `φ j ∘ c` gives
measurability of every `lam ∘ c`. -/
theorem measurable_of_separating {S : Type*} [MeasurableSpace S] {W : Type*}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] {J : Type*} (U : Submodule ℝ W)
    (φ : J → W →ₗ[ℝ] ℝ) (hsep : ∀ w ∈ U, (∀ j, φ j w = 0) → w = 0) (c : S → W)
    (hc : ∀ s, c s ∈ U) (hmeas : ∀ j, Measurable fun s => φ j (c s)) (lam : W →ₗ[ℝ] ℝ) :
    Measurable fun s => lam (c s) := by
  classical
  let Ψ : Submodule ℝ (Module.Dual ℝ U) :=
    Submodule.span ℝ (Set.range fun j => (φ j).domRestrict U)
  have hco : Ψ.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have h0 : (w : W) = 0 := hsep w w.2 fun j => hw _ (Submodule.subset_span ⟨j, rfl⟩)
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext h0)
  have hΨ : Ψ = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Ψ)
    rw [hco, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  have hall : ∀ ψ ∈ Ψ, Measurable fun s => ψ ⟨c s, hc s⟩ := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨j, rfl⟩ := h
      exact hmeas j
    | zero => exact measurable_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul r a _ ha => exact ha.const_smul r
  exact hall (lam.domRestrict U) (hΨ ▸ Submodule.mem_top)

/-- A function into a finite-dimensional space all of whose pairings are measurable is
measurable. -/
theorem measurable_of_dual {S : Type*} [MeasurableSpace S] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (f : S → F) (h : ∀ ℓ : F →ₗ[ℝ] ℝ, Measurable fun s => ℓ (f s)) :
    Measurable f := by
  classical
  let b := Module.finBasis ℝ F
  have hrep : f = fun s => ∑ i, (b.coord i (f s)) • b i := by
    funext s
    exact (b.sum_repr (f s)).symm
  rw [hrep]
  exact Finset.measurable_sum _ fun i _ => (h (b.coord i)).smul_const (b i)

/-- The open box of side `r` with lower corner `x`. -/
def openBox (x : Vec 2) (r : ℝ) : Set (Vec 2) :=
  Set.pi Set.univ fun i => Set.Ioo (x i) (x i + r)

theorem Box_volume (x : Vec 2) {r : ℝ} (hr : 0 ≤ r) :
    volume (openBox x r) = ENNReal.ofReal (r ^ 2) := by
  unfold openBox
  rw [Real.volume_pi_Ioo (a := x) (b := fun i => x i + r)]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hr]

theorem Box_dist (x : Vec 2) {r : ℝ} {y : Vec 2} (hy : y ∈ openBox x r) : dist y x ≤ r := by
  have hr : 0 ≤ r := by
    have h := hy 0 (Set.mem_univ 0)
    linarith [h.1, h.2]
  rw [dist_pi_le_iff hr]
  intro i
  have h := hy i (Set.mem_univ i)
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- **The averages over small boxes at a point converge to the value.** -/
theorem box_average_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : Vec 2 → E} (hg : Continuous g) (x : Vec 2) {r : ℕ → ℝ}
    (hr0 : ∀ n, 0 < r n) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => (r n ^ 2)⁻¹ • ∫ y in openBox x (r n), g y) atTop (𝓝 (g x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuous_iff.1 hg x (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hr) δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hrn : r n < δ := by
    have h := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_pos (hr0 n)] at h
  have hvol : volume (openBox x (r n)) = ENNReal.ofReal (r n ^ 2) := Box_volume x (hr0 n).le
  have hvolr : (volume : Measure (Vec 2)).real (openBox x (r n)) = r n ^ 2 := by
    rw [Measure.real, hvol, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hfin : volume (openBox x (r n)) < ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_lt_top
  have hint : IntegrableOn g (openBox x (r n)) := by
    refine (hg.continuousOn.integrableOn_compact
      (isCompact_Icc (a := x) (b := fun i => x i + r n))).mono_set ?_
    intro y hy
    exact ⟨fun i => (hy i (Set.mem_univ i)).1.le, fun i => (hy i (Set.mem_univ i)).2.le⟩
  have hsub : ((r n ^ 2)⁻¹ • ∫ y in openBox x (r n), g y) - g x =
      (r n ^ 2)⁻¹ • ∫ y in openBox x (r n), (g y - g x) := by
    rw [integral_sub hint (integrableOn_const hfin.ne), setIntegral_const, hvolr, smul_sub,
      smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (hr0 n).ne'), one_smul]
  have hb : ‖∫ y in openBox x (r n), (g y - g x)‖ ≤ ε / 2 * r n ^ 2 := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := openBox x (r n))
      (f := fun y => g y - g x) (C := ε / 2) hfin (fun y hy => by
        rw [← dist_eq_norm]
        exact (hδg y (lt_of_le_of_lt (Box_dist x hy) hrn)).le)
    rwa [hvolr] at h
  have hpos : 0 < r n ^ 2 := pow_pos (hr0 n) 2
  rw [dist_eq_norm, hsub, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le]
  calc (r n ^ 2)⁻¹ * ‖∫ y in openBox x (r n), (g y - g x)‖
      ≤ (r n ^ 2)⁻¹ * (ε / 2 * r n ^ 2) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hpos.le)
    _ = ε / 2 := by
        rw [mul_comm (ε / 2) (r n ^ 2), ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    _ < ε := half_lt_self hε

theorem volume_unitCube'' : volume (AVenhance.unitCube : Set (Vec 2)) = 1 := by
  unfold AVenhance.unitCube
  rw [Real.volume_pi_Ioo (a := fun _ => (0 : ℝ)) (b := fun _ => (1 : ℝ))]
  simp

/-- A continuous function is integrable on a subset of the cell. -/
theorem integrableOn_of_subset_cube {E : Type*} [NormedAddCommGroup E] {g : Vec 2 → E}
    (hg : Continuous g) {B : Set (Vec 2)} (hB : B ⊆ AVenhance.unitCube) : IntegrableOn g B := by
  refine (hg.continuousOn.integrableOn_compact
    (isCompact_Icc (a := fun _ : Fin 2 => (0 : ℝ)) (b := fun _ => (1 : ℝ)))).mono_set ?_
  intro y hy
  have h := hB hy
  exact ⟨fun i => (h i (Set.mem_univ i)).1.le, fun i => (h i (Set.mem_univ i)).2.le⟩

/-- **Continuity in `L²` of the cell gives continuity of the integrals over subsets.** -/
theorem setIntegral_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} (F : ℝ → Vec 2 → E) (hcont : ∀ t ∈ I, Continuous (F t))
    (hL2 : ∀ t₀ ∈ I, Tendsto (fun t => ∫⁻ x in AVenhance.unitCube, ‖F t x - F t₀ x‖ₑ ^ 2)
      (𝓝[I] t₀) (𝓝 0))
    {B : Set (Vec 2)} (hB : B ⊆ AVenhance.unitCube) :
    ContinuousOn (fun t => ∫ y in B, F t y) I := by
  intro t₀ ht₀
  show Tendsto (fun t => ∫ y in B, F t y) (𝓝[I] t₀) (𝓝 (∫ y in B, F t₀ y))
  rw [tendsto_iff_edist_tendsto_0]
  have hup : Tendsto (fun t => (∫⁻ x in AVenhance.unitCube, ‖F t x - F t₀ x‖ₑ ^ 2) ^ (1 / 2 : ℝ))
      (𝓝[I] t₀) (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp (hL2 t₀ ht₀)
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hm : AEStronglyMeasurable (fun x => F t x - F t₀ x)
      (volume.restrict AVenhance.unitCube) :=
    ((hcont t ht).sub (hcont t₀ ht₀)).aestronglyMeasurable
  have h1 : edist (∫ y in B, F t y) (∫ y in B, F t₀ y) ≤
      ∫⁻ x in AVenhance.unitCube, ‖F t x - F t₀ x‖ₑ := by
    rw [edist_eq_enorm_sub, ← integral_sub (integrableOn_of_subset_cube (hcont t ht) hB)
      (integrableOn_of_subset_cube (hcont t₀ ht₀) hB)]
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_set hB)
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict AVenhance.unitCube)
    (p := 1) (q := 2) (by norm_num) hm
  rw [eLpNorm_one_eq_lintegral_enorm hm, Measure.restrict_apply_univ, volume_unitCube'',
    ENNReal.one_rpow, mul_one,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm] at h2
  refine h1.trans (h2.trans (le_of_eq ?_))
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- **Measurability in time at every point from continuity in `L²`.** A family of continuous
periodic functions, continuous in `t ∈ I` into `L²` of the cell, is measurable in `t` at every
point. -/
theorem measurable_eval_of_l2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {I : Set ℝ} (F : ℝ → Vec 2 → E) (hcont : ∀ t ∈ I, Continuous (F t))
    (hper : ∀ t ∈ I, AVenhance.IsZ2Periodic (F t))
    (hL2 : ∀ t₀ ∈ I, Tendsto (fun t => ∫⁻ x in AVenhance.unitCube, ‖F t x - F t₀ x‖ₑ ^ 2)
      (𝓝[I] t₀) (𝓝 0))
    (x : Vec 2) : Measurable (fun t : I => F t.1 x) := by
  let n₀ : Fin 2 → ℤ := fun i => ⌊x i⌋
  let x₀ : Vec 2 := fun i => Int.fract (x i)
  have hx : x = x₀ + AVenhance.latticeShift n₀ := by
    funext i
    simp only [Pi.add_apply, AVenhance.latticeShift, x₀, n₀]
    exact (Int.fract_add_floor (x i)).symm
  have hval : ∀ t : I, F t.1 x = F t.1 x₀ := fun t => by
    rw [hx]
    exact hper t.1 t.2 n₀ x₀
  have hx0 : ∀ i, 0 ≤ x₀ i := fun i => Int.fract_nonneg _
  have hx1 : ∀ i, x₀ i < 1 := fun i => Int.fract_lt_one _
  let δ : ℝ := min (1 - x₀ 0) (1 - x₀ 1)
  have hδ : 0 < δ := lt_min (by linarith [hx1 0]) (by linarith [hx1 1])
  have hδi : ∀ i, x₀ i + δ ≤ 1 := by
    intro i
    fin_cases i
    · have := min_le_left (1 - x₀ 0) (1 - x₀ 1)
      show x₀ 0 + δ ≤ 1
      linarith
    · have := min_le_right (1 - x₀ 0) (1 - x₀ 1)
      show x₀ 1 + δ ≤ 1
      linarith
  let r : ℕ → ℝ := fun n => δ / ((n + 2 : ℕ) : ℝ)
  have hr0 : ∀ n, 0 < r n := fun n => div_pos hδ (by positivity)
  have hrδ : ∀ n, r n ≤ δ := fun n => by
    have h2 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      norm_cast
      omega
    exact div_le_self hδ.le h2
  have hr : Tendsto r atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat δ).comp (tendsto_add_atTop_nat 2)
  have hsub : ∀ n, openBox x₀ (r n) ⊆ AVenhance.unitCube := by
    intro n y hy i _
    have h := hy i (Set.mem_univ i)
    exact ⟨lt_of_le_of_lt (hx0 i) h.1, lt_of_lt_of_le h.2 (by linarith [hrδ n, hδi i])⟩
  have hmeas : ∀ n, Measurable
      (fun t : I => (r n ^ 2)⁻¹ • ∫ y in openBox x₀ (r n), F t.1 y) := by
    intro n
    have hc := setIntegral_continuousOn F hcont hL2 (hsub n)
    exact (continuousOn_iff_continuous_domRestrict.1 hc).measurable.const_smul _
  have hfun : (fun t : I => F t.1 x) = fun t : I => F t.1 x₀ := funext hval
  rw [hfun]
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun t => ?_)
  exact box_average_tendsto (hcont t.1 t.2) x₀ hr0 hr

private theorem orderedDerivative_succ' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (α : DerivativeWord2 (m + 1)) (g : Vec 2 → E) :
    orderedDerivative α g =
      orderedDerivative (fun i : Fin m => α i.succ) (fun x => fderiv ℝ g x (basisVec (α 0))) := by
  simp [orderedDerivative, List.ofFn_succ]

/-- **Word derivatives of a jointly measurable family of `C^m` functions are jointly
measurable.** -/
theorem measurable_orderedDerivative {T : Type*} [MeasurableSpace T] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] :
    ∀ (m : ℕ) (α : DerivativeWord2 m) (g : T → Vec 2 → E), (∀ t, ContDiff ℝ m (g t)) →
      Measurable (fun p : T × Vec 2 => g p.1 p.2) →
      Measurable (fun p : T × Vec 2 => orderedDerivative α (g p.1) p.2) := by
  intro m
  induction m with
  | zero =>
    intro α g _ hg
    simpa [orderedDerivative] using hg
  | succ m ih =>
    intro α g hsm hg
    have hfun : (fun p : T × Vec 2 => orderedDerivative α (g p.1) p.2) =
        fun p : T × Vec 2 => orderedDerivative (fun i : Fin m => α i.succ)
          (fun x => fderiv ℝ (g p.1) x (basisVec (α 0))) p.2 := by
      funext p
      rw [orderedDerivative_succ']
    rw [hfun]
    refine ih (fun i : Fin m => α i.succ) (fun t x => fderiv ℝ (g t) x (basisVec (α 0)))
      (fun t => ?_) ?_
    · have h1 : ContDiff ℝ ((m : ℕ∞) + 1) (g t) := by exact_mod_cast hsm t
      exact (h1.fderiv_right le_rfl).clm_apply contDiff_const
    · have hq : ∀ n : ℕ, Measurable (fun p : T × Vec 2 =>
          ((n : ℝ) + 1) • (g p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • basisVec (α 0)) - g p.1 p.2)) := by
        intro n
        have hsh : Measurable (fun p : T × Vec 2 =>
            (p.1, p.2 + ((n : ℝ) + 1)⁻¹ • basisVec (α 0))) :=
          measurable_fst.prodMk (measurable_snd.add_const _)
        exact ((hg.comp hsh).sub hg).const_smul _
      refine measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.2 fun p => ?_)
      have hd : DifferentiableAt ℝ (g p.1) p.2 :=
        ((hsm p.1).differentiable (by exact_mod_cast Nat.succ_ne_zero m)).differentiableAt
      refine hd.hasFDerivAt.lim (basisVec (α 0)) (c := fun n : ℕ => (n : ℝ) + 1) ?_
      have hn : ∀ n : ℕ, ‖(n : ℝ) + 1‖ = (n : ℝ) + 1 := fun n =>
        Real.norm_of_nonneg (by positivity)
      simp only [hn]
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end

section
section
/-! # The coefficients of a lift sequence are jointly measurable in `(t, X, z)`

From `IsLiftSequence Q sX sZ t₀ t₁ N H Cc` alone, on the window `[t₀, t₁]` of the sequence:

* `liftApply_test_measurable`: for a smooth test field `a₀`, a point `(X, z)` and a
  functional `ℓ`, `t ↦ ℓ (liftApply n (Cc hh n) a₀ t X z)` is measurable. For `n ≥ 1` this is
  clause 7: the cell value of the field inverse is continuous in `t` into `L²` of the cell,
  periodic and continuous in `z`, so it is measurable in `t` at EVERY `z`
  (`measurable_eval_of_l2`). For `n = 0` the action is constant in `t` (clauses 1 and 2).
* `coeff_measurable_time`: each coefficient is measurable in `t` at every `(X, z)`: the test
  functionals separate the symmetric coefficient arrays
  (`symmetric_lift_coefficient_eq_of_operator_eq`, clause 5), and the arrays form a
  finite-dimensional space (`measurable_of_separating`).
* `coeff_measurable`: with the continuity in `(X, z)` of clause 6, joint measurability on
  `[t₀, t₁] × (ℝ² × ℝ²)`; the coefficients vanish for `n > N` and for `m > n` (clauses 3, 4).

Degenerate cases: `N = 0` (only `n = 0`: the coefficients are constant in `t`); `ι` empty (the array
space is a point); `t₀ > t₁` (the time type is empty). -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

private theorem cellValue_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (c : ℝ → Vec 2 → E) (t : ℝ) (x : Vec 2) :
    cellValue (cellJetOfField ℓ c) t x = ((ℓ (c t x) : ℝ) : ℂ) := by
  simp [cellValue, cellJetOfField, valueIndex2, valueIndex]

omit [DecidableEq ι] in
/-- **The action of a lift coefficient on a smooth test field is measurable in time**, at every
point and against every functional. -/
theorem liftApply_test_measurable {D : ℕ} {Q : LiftOperatorData ι h D} {sX sZ : ℕ}
    {t₀ t₁ : ℝ} {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh n : ℕ} (hhH : hh ≤ H) (hn : n ≤ N)
    (a₀ : Vec 2 → ∀ i, h i) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀) (X z : Vec 2)
    (ℓ : (∀ i, h i) →L[ℝ] ℝ) :
    Measurable (fun s : Set.Icc t₀ t₁ => ℓ (liftApply n (Cc hh n) (fun _ => a₀) s.1 X z)) := by
  obtain ⟨h1, h2, -, -, -, -, h7⟩ := hseq
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rcases Nat.eq_zero_or_pos hh with rfl | hh1
    · have he : (fun s : Set.Icc t₀ t₁ => ℓ (liftApply 0 (Cc 0 0) (fun _ => a₀) s.1 X z)) =
          fun _ => ℓ (a₀ X) := by
        funext s
        rw [h1 a₀ ha₀ s.1 s.2 X z]
      rw [he]
      exact measurable_const
    · have he : (fun s : Set.Icc t₀ t₁ => ℓ (liftApply 0 (Cc hh 0) (fun _ => a₀) s.1 X z)) =
          fun _ => ℓ 0 := by
        funext s
        congr 1
        funext v
        simp only [liftApply, h2 hh hh1 hhH, zero_apply,
          Finset.sum_const_zero, Pi.zero_apply]
      rw [he]
      exact measurable_const
  · obtain ⟨hcd, hℓ⟩ := h7 hh hhH n hn1 hn a₀ ha₀ X
    obtain ⟨hsol, -, -, -⟩ := hℓ ℓ
    obtain ⟨-, -, hval, -, hL2, -, -⟩ := hsol
    have hm := measurable_eval_of_l2 (E := ℂ) (I := Set.Icc t₀ t₁)
      (fun t => cellValue (cellJetOfField ℓ
        (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z)) t)
      (fun t ht => by
        have he : cellValue (cellJetOfField ℓ
            (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z)) t =
            fun x => ((ℓ (liftApply n (Cc hh n) (fun _ => a₀) t X x) : ℝ) : ℂ) :=
          funext fun x => cellValue_field ℓ _ t x
        rw [he]
        exact Complex.continuous_ofReal.comp (ℓ.continuous.comp (hcd t ht).continuous))
      (fun t ht => (hval t ht).2) hL2 z
    have hre := Complex.measurable_re.comp hm
    have he : (fun s : Set.Icc t₀ t₁ => ℓ (liftApply n (Cc hh n) (fun _ => a₀) s.1 X z)) =
        Complex.re ∘ fun s : Set.Icc t₀ t₁ => cellValue (cellJetOfField ℓ
          (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z)) s.1 z := by
      funext s
      simp only [Function.comp_apply, cellValue_field, Complex.ofReal_re]
    rw [he]
    exact hre

/-- The coefficient arrays of degree `n`: one map `h u → h v` per row `v`, order `m ≤ n`, word
and column `u`. -/
abbrev CoeffArray (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (n : ℕ) : Type _ :=
  ∀ v : ι, ∀ q : LiftActionIndex ι n, (h q.2.2 →L[ℝ] h v)

/-- The array of a coefficient at a point. -/
def coeffArrayAt (C : LiftCoeff ι h) (n : ℕ) (t : ℝ) (X z : Vec 2) : CoeffArray ι h n :=
  fun v q => C q.1.val q.2.1 t X z v q.2.2

/-- The test functional of a field `a₀` and a functional `ℓ` at the slow point `X`. -/
def Test (n : ℕ) (X : Vec 2) (a₀ : Vec 2 → ∀ i, h i) (ℓ : (∀ i, h i) →L[ℝ] ℝ) :
    CoeffArray ι h n →ₗ[ℝ] ℝ where
  toFun w := ℓ (fun v => ∑ q : LiftActionIndex ι n, w v q (orderedDerivative q.2.1 a₀ X q.2.2))
  map_add' w w' := by
    rw [← map_add]
    congr 1
    funext v
    simp only [Pi.add_apply, add_apply, Finset.sum_add_distrib]
  map_smul' r w := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    funext v
    simp only [Pi.smul_apply, smul_apply, Finset.smul_sum]

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem Test_arr (C : LiftCoeff ι h) (n : ℕ) (t : ℝ) (X z : Vec 2)
    (a₀ : Vec 2 → ∀ i, h i) (ℓ : (∀ i, h i) →L[ℝ] ℝ) :
    Test n X a₀ ℓ (coeffArrayAt C n t X z) = ℓ (liftApply n C (fun _ => a₀) t X z) := by
  show ℓ (fun v => ∑ q : LiftActionIndex ι n,
    C q.1.val q.2.1 t X z v q.2.2 (orderedDerivative q.2.1 a₀ X q.2.2)) = _
  congr 1
  funext v
  exact liftApply_finite_vector_synthesis n C a₀ t X z v

/-- The symmetric arrays: invariant under the permutations of the letters of each word. -/
def symmetricCoeffArrays (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (n : ℕ) : Submodule ℝ (CoeffArray ι h n) where
  carrier := {w | ∀ (v : ι) (m : Fin (n + 1)) (β : DerivativeWord2 m.val)
    (σ : Equiv.Perm (Fin m.val)) (u : ι),
    w v (⟨m, β ∘ σ, u⟩ : LiftActionIndex ι n) = w v (⟨m, β, u⟩ : LiftActionIndex ι n)}
  add_mem' := by
    intro a b ha hb v m β σ u
    exact congrArg₂ (· + ·) (ha v m β σ u) (hb v m β σ u)
  zero_mem' := by
    intro v m β σ u
    rfl
  smul_mem' := by
    intro r a ha v m β σ u
    exact congrArg (r • ·) (ha v m β σ u)

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The test functionals separate the symmetric arrays.** -/
theorem sym_separated (n : ℕ) (X : Vec 2) (w : CoeffArray ι h n) (hw : w ∈ symmetricCoeffArrays ι h n)
    (h0 : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
      ∀ ℓ : (∀ i, h i) →L[ℝ] ℝ, Test n X a₀ ℓ w = 0) : w = 0 := by
  classical
  let C : LiftCoeff ι h := fun m α _ _ _ v u =>
    if hm : m < n + 1 then w v (⟨⟨m, hm⟩, α, u⟩ : LiftActionIndex ι n) else 0
  have hvec : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
      (fun v => ∑ q : LiftActionIndex ι n, w v q (orderedDerivative q.2.1 a₀ X q.2.2)) = 0 :=
    fun a₀ ha₀ => SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) (h0 a₀ ha₀)
  have hw' : ∀ (v : ι) (m : Fin (n + 1)) (β : DerivativeWord2 m.val)
      (σ : Equiv.Perm (Fin m.val)) (u : ι),
      w v (⟨m, β ∘ σ, u⟩ : LiftActionIndex ι n) = w v (⟨m, β, u⟩ : LiftActionIndex ι n) := hw
  funext v q
  obtain ⟨m, α, u⟩ := q
  have hm : m.val ≤ n := Nat.lt_succ_iff.mp m.2
  have hC : ∀ (β : DerivativeWord2 m.val) (σ : Equiv.Perm (Fin m.val)),
      C m.val (β ∘ σ) = C m.val β := by
    intro β σ
    funext t X' z' v' u'
    simp only [C, m.2, dite_true]
    exact hw' v' m β σ u'
  have h0C : ∀ (β : DerivativeWord2 m.val) (σ : Equiv.Perm (Fin m.val)),
      (0 : LiftCoeff ι h) m.val (β ∘ σ) = (0 : LiftCoeff ι h) m.val β := fun _ _ => rfl
  have key := symmetric_lift_coefficient_eq_of_operator_eq n m.val hm C 0 hC h0C 0 X 0 v u
    (fun a₀ ha₀ => by
      rw [← liftApply_finite_vector_synthesis n C a₀ 0 X 0 v,
        ← liftApply_finite_vector_synthesis n (0 : LiftCoeff ι h) a₀ 0 X 0 v]
      have hl : (∑ p : LiftActionIndex ι n,
          C p.1.val p.2.1 0 X 0 v p.2.2 (orderedDerivative p.2.1 a₀ X p.2.2)) =
          ∑ q : LiftActionIndex ι n, w v q (orderedDerivative q.2.1 a₀ X q.2.2) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [C, p.1.2, dite_true]
        rfl
      rw [hl, congrFun (hvec a₀ ha₀) v]
      simp only [Pi.zero_apply, zero_apply, Finset.sum_const_zero]) α
  have hk : C m.val α 0 X 0 v u = w v (⟨m, α, u⟩ : LiftActionIndex ι n) := by
    simp only [C, m.2, dite_true]
  rw [hk] at key
  exact key

/-- **Each coefficient of a lift sequence is measurable in time** at every point `(X, z)`. -/
theorem coeff_measurable_time {D : ℕ} {Q : LiftOperatorData ι h D} {sX sZ : ℕ}
    {t₀ t₁ : ℝ} {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh n : ℕ} (hhH : hh ≤ H) (hn : n ≤ N)
    (X z : Vec 2) (v : ι) (q : LiftActionIndex ι n) :
    Measurable (fun s : Set.Icc t₀ t₁ => Cc hh n q.1.val q.2.1 s.1 X z v q.2.2) := by
  classical
  have h5 := hseq.2.2.2.2.1
  have hmem : ∀ s : Set.Icc t₀ t₁, coeffArrayAt (Cc hh n) n s.1 X z ∈ symmetricCoeffArrays ι h n := by
    intro s v' m β σ u
    show Cc hh n m.val (β ∘ σ) s.1 X z v' u = Cc hh n m.val β s.1 X z v' u
    rw [h5 hh hhH n m.val β σ]
  refine measurable_of_dual _ fun ℓ' => ?_
  have hmain := measurable_of_separating (S := Set.Icc t₀ t₁) (U := symmetricCoeffArrays ι h n)
    (φ := fun j : {a₀ : Vec 2 → ∀ i, h i // ContDiff ℝ (⊤ : ℕ∞) a₀} × ((∀ i, h i) →L[ℝ] ℝ) =>
      Test n X j.1.1 j.2)
    (fun w hw hall => sym_separated n X w hw fun a₀ ha₀ ℓ => hall (⟨a₀, ha₀⟩, ℓ))
    (fun s : Set.Icc t₀ t₁ => coeffArrayAt (Cc hh n) n s.1 X z) hmem
    (fun j => by
      have he : (fun s : Set.Icc t₀ t₁ =>
          Test n X j.1.1 j.2 (coeffArrayAt (Cc hh n) n s.1 X z)) =
          fun s : Set.Icc t₀ t₁ => j.2 (liftApply n (Cc hh n) (fun _ => j.1.1) s.1 X z) :=
        funext fun s => Test_arr (Cc hh n) n s.1 X z j.1.1 j.2
      rw [he]
      exact liftApply_test_measurable hseq hhH hn j.1.1 j.1.2 X z j.2)
    (ℓ' ∘ₗ (LinearMap.proj q : (∀ q : LiftActionIndex ι n, (h q.2.2 →L[ℝ] h v)) →ₗ[ℝ] _) ∘ₗ
      (LinearMap.proj v : CoeffArray ι h n →ₗ[ℝ] _))
  exact hmain

/-- **The coefficients of a lift sequence are jointly measurable** on the window of the sequence
times the two space variables. -/
theorem coeff_measurable {D : ℕ} {Q : LiftOperatorData ι h D} {sX sZ : ℕ}
    {t₀ t₁ : ℝ} {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ} (hhH : hh ≤ H) (n m : ℕ)
    (α : DerivativeWord2 m) (v u : ι) :
    Measurable (fun p : Set.Icc t₀ t₁ × (Vec 2 × Vec 2) =>
      Cc hh n m α p.1.1 p.2.1 p.2.2 v u) := by
  have h3 := hseq.2.2.1
  have h4 := hseq.2.2.2.1
  have h6 := hseq.2.2.2.2.2.1
  by_cases hnN : N < n
  · have he : (fun p : Set.Icc t₀ t₁ × (Vec 2 × Vec 2) => Cc hh n m α p.1.1 p.2.1 p.2.2 v u) =
        fun _ => 0 := funext fun p => h3 hh hhH n hnN m α _ _ _ v u
    rw [he]
    exact measurable_const
  by_cases hmn : n < m
  · have he : (fun p : Set.Icc t₀ t₁ × (Vec 2 × Vec 2) => Cc hh n m α p.1.1 p.2.1 p.2.2 v u) =
        fun _ => 0 := funext fun p => h4 hh hhH n m hmn α _ _ _ v u
    rw [he]
    exact measurable_const
  have hn : n ≤ N := Nat.le_of_not_lt hnN
  have hm : m < n + 1 := Nat.lt_succ_of_le (Nat.le_of_not_lt hmn)
  refine measurable_joint (T := Set.Icc t₀ t₁) (Y := Vec 2 × Vec 2)
    (fun s Y => Cc hh n m α s.1 Y.1 Y.2 v u) (fun s => ?_) (fun Y => ?_)
  · exact boxSmooth_continuous (h6 hh hhH n m α v u s.1 s.2).1
  · exact coeff_measurable_time hseq hhH hn Y.1 Y.2 v
      (⟨⟨m, hm⟩, α, u⟩ : LiftActionIndex ι n)

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! **The covariance operator is self-adjoint without a symmetry hypothesis**.

On `C²` fields the mixed second derivatives agree, so `covOperator H = covOperator (symmPart H)`
on `C²` fields; the classical adjoint lemmas (stated for symmetric matrices) then give

* `cellInner (𝖯_p u) q = cellInner u (𝖯_p q)` and the same for `𝖰_p`;
* the duality `cellInner g (φ - 𝖰_p 𝖯_p φ) = cellInner (g - 𝖯_p 𝖰_p g) φ`;
* the commutation of `𝖯_p`, `𝖰_p` with a constant continuous linear map.

Degenerate cases:
- `H` symmetric: `symmPart H = H`.
- `p = 0`: `𝖯_0 = 𝖰_0 = id`, the duality reads `cellInner g (φ - φ) = cellInner (g - g) φ`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift

namespace AVRegularity.EntryTerminal.CovOp

/-- The symmetric part of a matrix. -/
def symmPart (H : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (H i j + H j i) / 2

theorem symmPart_symm (H : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    symmPart H i j = symmPart H j i := by
  unfold symmPart; ring

section Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem covOp_secondDeriv_swap {f : Vec 2 → E} (hf : ContDiff ℝ 2 f) (x : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x (basisVec i) =
      fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x (basisVec j) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  simp only [fderiv_clm_apply hd (differentiableAt_const _), fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add]
  exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num) _ _

/-- On `C²` fields the covariance operator only sees the symmetric part of the matrix. -/
theorem covOp_eq_symmPart (H : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → E} (hf : ContDiff ℝ 2 f) :
    covOperator H f = covOperator (symmPart H) f := by
  funext x
  have hs := covOp_secondDeriv_swap hf x 0 1
  unfold covOperator
  simp only [Fin.sum_univ_two, symmPart]
  rw [hs]
  module

theorem covOp_iterate_eq_symmPart (H : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ (n : ℕ) {f : Vec 2 → E}, ContDiff ℝ ((2 * n : ℕ) : ℕ∞) f →
      (covOperator H)^[n] f = (covOperator (symmPart H))^[n] f
  | 0, _, _ => rfl
  | n + 1, f, hf => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hmid : ContDiff ℝ 2 ((covOperator H)^[n] f) :=
      covOperator_iterate_contDiff H n 2 f (by
        simpa only [Nat.mul_succ, Nat.add_comm] using hf)
    rw [covOp_eq_symmPart H hmid, covOp_iterate_eq_symmPart H n
      (hf.of_le (by exact_mod_cast (by omega : 2 * n ≤ 2 * (n + 1))))]

theorem covOp_polynomial_eq_symmPart (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (a : ℕ → ℝ)
    {f : Vec 2 → E} (hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f) :
    covariancePolynomial H p a f = covariancePolynomial (symmPart H) p a f := by
  funext x
  unfold covariancePolynomial
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [covOp_iterate_eq_symmPart H l (hf.of_le (by exact_mod_cast Nat.mul_le_mul_left 2 hlp))]

/-- `𝖯_p`-type polynomials are self-adjoint on `C^{2p}` periodic fields, for every matrix. -/
theorem covOp_polynomial_adjoint (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (a : ℕ → ℝ)
    (u q : Vec 2 → E) (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u)
    (hq : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) q) (hpu : AVenhance.IsZ2Periodic u)
    (hpq : AVenhance.IsZ2Periodic q) :
    cellInner (covariancePolynomial H p a u) q = cellInner u (covariancePolynomial H p a q) := by
  rw [covOp_polynomial_eq_symmPart H p a hu, covOp_polynomial_eq_symmPart H p a hq]
  exact covariancePolynomial_cellInner_adjoint (symmPart H) (symmPart_symm H) p a u q hu hq hpu hpq

theorem covOp_P_adjoint (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (u q : Vec 2 → E) (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u)
    (hq : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) q) (hpu : AVenhance.IsZ2Periodic u)
    (hpq : AVenhance.IsZ2Periodic q) :
    cellInner (covPolyP H p u) q = cellInner u (covPolyP H p q) := by
  rw [← covariancePolynomial_eq_P, ← covariancePolynomial_eq_P]
  exact covOp_polynomial_adjoint H p _ u q hu hq hpu hpq

theorem covOp_Q_adjoint (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (u q : Vec 2 → E) (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u)
    (hq : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) q) (hpu : AVenhance.IsZ2Periodic u)
    (hpq : AVenhance.IsZ2Periodic q) :
    cellInner (covPolyQ H p u) q = cellInner u (covPolyQ H p q) := by
  rw [← covariancePolynomial_eq_Q, ← covariancePolynomial_eq_Q]
  exact covOp_polynomial_adjoint H p _ u q hu hq hpu hpq

theorem covOp_contDiff_P (H : Matrix (Fin 2) (Fin 2) ℝ) (p n : ℕ) {u : Vec 2 → E}
    (hu : ContDiff ℝ ((n + 2 * p : ℕ) : ℕ∞) u) : ContDiff ℝ (n : ℕ∞) (covPolyP H p u) := by
  rw [← covariancePolynomial_eq_P]; exact covariancePolynomial_contDiff H p n _ u hu

theorem covOp_contDiff_Q (H : Matrix (Fin 2) (Fin 2) ℝ) (p n : ℕ) {u : Vec 2 → E}
    (hu : ContDiff ℝ ((n + 2 * p : ℕ) : ℕ∞) u) : ContDiff ℝ (n : ℕ∞) (covPolyQ H p u) := by
  rw [← covariancePolynomial_eq_Q]; exact covariancePolynomial_contDiff H p n _ u hu

theorem covOp_periodic_P (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {u : Vec 2 → E}
    (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) (hp : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (covPolyP H p u) := by
  rw [← covariancePolynomial_eq_P]; exact covariancePolynomial_periodic H p _ u hu hp

theorem covOp_periodic_Q (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {u : Vec 2 → E}
    (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) (hp : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (covPolyQ H p u) := by
  rw [← covariancePolynomial_eq_Q]; exact covariancePolynomial_periodic H p _ u hu hp

/-- **The duality of the truncation**: for `g ∈ C^{4p}` periodic and `φ` smooth periodic,
`⟨g, φ - 𝖰_p 𝖯_p φ⟩ = ⟨g - 𝖯_p 𝖰_p g, φ⟩`. -/
theorem covOp_truncation_duality (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {g φ : Vec 2 → E}
    (hg : ContDiff ℝ ((4 * p : ℕ) : ℕ∞) g) (hpg : AVenhance.IsZ2Periodic g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hpφ : AVenhance.IsZ2Periodic φ) :
    cellInner g (φ - covPolyQ H p (covPolyP H p φ)) =
      cellInner (g - covPolyP H p (covPolyQ H p g)) φ := by
  have hφ' : ∀ m : ℕ, ContDiff ℝ (m : ℕ∞) φ := fun m => hφ.of_le (by exact_mod_cast le_top)
  have hPφ : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (covPolyP H p φ) :=
    covOp_contDiff_P H p (2 * p) (by simpa [two_mul, add_comm] using hφ' (2 * p + 2 * p))
  have hPφp : AVenhance.IsZ2Periodic (covPolyP H p φ) := covOp_periodic_P H p (hφ' _) hpφ
  have hQg : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) (covPolyQ H p g) :=
    covOp_contDiff_Q H p (2 * p) (by rw [show 2 * p + 2 * p = 4 * p by omega]; exact hg)
  have hg2 : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) g := hg.of_le (by exact_mod_cast (by omega : 2 * p ≤ 4 * p))
  have hQgp : AVenhance.IsZ2Periodic (covPolyQ H p g) := covOp_periodic_Q H p hg2 hpg
  have hQPφ : Continuous (covPolyQ H p (covPolyP H p φ)) :=
    (covOp_contDiff_Q H p 0 (by simpa using hPφ)).continuous
  have hPQg : Continuous (covPolyP H p (covPolyQ H p g)) :=
    (covOp_contDiff_P H p 0 (by simpa using hQg)).continuous
  have h1 : cellInner g (covPolyQ H p (covPolyP H p φ)) =
      cellInner (covPolyP H p (covPolyQ H p g)) φ := by
    rw [← covOp_Q_adjoint H p g (covPolyP H p φ) hg2 hPφ hpg hPφp]
    exact (covOp_P_adjoint H p (covPolyQ H p g) φ hQg (hφ' _) hQgp hpφ).symm
  have hint1 := AVRegularity.CycleComparison.Coarse.integrable_inner_continuous
    (AVRegularity.CycleComparison.Coarse.memLp_two_cell_of_continuous hg2.continuous)
    hφ.continuous
  have hint2 := AVRegularity.CycleComparison.Coarse.integrable_inner_continuous
    (AVRegularity.CycleComparison.Coarse.memLp_two_cell_of_continuous hg2.continuous) hQPφ
  have hint3 := AVRegularity.CycleComparison.Coarse.integrable_inner_continuous
    (AVRegularity.CycleComparison.Coarse.memLp_two_cell_of_continuous hPQg) hφ.continuous
  unfold cellInner at h1 ⊢
  have e1 : (∫ x in AVenhance.unitCube, inner ℝ (g x) ((φ - covPolyQ H p (covPolyP H p φ)) x)) =
      (∫ x in AVenhance.unitCube, inner ℝ (g x) (φ x)) -
        ∫ x in AVenhance.unitCube, inner ℝ (g x) (covPolyQ H p (covPolyP H p φ) x) := by
    rw [← integral_sub hint1 hint2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, inner_sub_right])
  have e2 : (∫ x in AVenhance.unitCube, inner ℝ ((g - covPolyP H p (covPolyQ H p g)) x) (φ x)) =
      (∫ x in AVenhance.unitCube, inner ℝ (g x) (φ x)) -
        ∫ x in AVenhance.unitCube, inner ℝ (covPolyP H p (covPolyQ H p g) x) (φ x) := by
    rw [← integral_sub hint1 hint3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, inner_sub_left])
  rw [e1, e2, h1]

end Classical

end AVRegularity.EntryTerminal.CovOp
end
end

section
/-! **Positivity of a regularizer constant from closeness to the identity.**
Let `S(t)` satisfy clause (4) of `IsSpatialRegularizerTorus` at the order `0` with `ρ = 1`. If
`‖S(t) f - f‖ < ‖f‖` for the mode `f = cos(2π x₁)`, then `c_j > 0` for every `j + 2 ≤ D`.
If `c_j = 0`, the `j`-th jets of the regularized field `Y` vanish. Periodic integration by parts
against `ψ = cos(2π x₁ - jπ/2)` (`∂₁^j ψ = (2π)^j f`) gives `⟨S f, f⟩ = 0`, so
`‖f‖² = ⟨f - S f, f⟩ < ‖f‖²`.

Degenerate cases:
- `j = 0`: `c_0 = 0` forces `S f = 0`, so `⟨S f, f⟩ = 0`.
- `S = id`: `‖S f - f‖ = 0 < ‖f‖` as soon as `f ≠ 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.EntryWeakProofs
  AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-- The plane wave `x ↦ cos(2π x₁ + θ)`. -/
def ckerPhase (θ : ℝ) : Vec 2 → ℝ := fun x => Real.cos (2 * Real.pi * x 0 + θ)

theorem ckerPhase_contDiff (θ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (ckerPhase θ) := by
  unfold ckerPhase
  fun_prop

theorem ckerPhase_differentiableAt (θ : ℝ) (x : Vec 2) : DifferentiableAt ℝ (ckerPhase θ) x := by
  unfold ckerPhase
  fun_prop

theorem ckerPhase_periodic (θ : ℝ) : IsZ2Periodic (ckerPhase θ) := by
  intro n x
  unfold ckerPhase
  have : 2 * Real.pi * (x + latticeShift n) 0 + θ =
      (2 * Real.pi * x 0 + θ) + (n 0 : ℤ) * (2 * Real.pi) := by
    simp only [Pi.add_apply, latticeShift]
    ring
  rw [this, Real.cos_add_int_mul_two_pi]

theorem ckerPhase_fderiv (θ : ℝ) (x : Vec 2) :
    fderiv ℝ (ckerPhase θ) x (basisVec 0) = 2 * Real.pi * ckerPhase (θ + Real.pi / 2) x := by
  have h0 := ((hasDerivAt_id (x 0)).const_mul (2 * Real.pi)).add_const θ
  have h1 : HasDerivAt (fun s : ℝ => Real.cos (2 * Real.pi * s + θ))
      (-Real.sin (2 * Real.pi * x 0 + θ) * (2 * Real.pi * 1)) (x 0) :=
    h0.cos
  have h2 : HasFDerivAt (fun y : Vec 2 => y 0) (ContinuousLinearMap.proj 0) x :=
    hasFDerivAt_apply (𝕜 := ℝ) 0 x
  have h3 := h1.comp_hasFDerivAt x h2
  have h4 : fderiv ℝ (ckerPhase θ) x = _ := h3.fderiv
  rw [h4]
  unfold ckerPhase
  rw [← add_assoc, Real.cos_add_pi_div_two]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, basisVec, Pi.single_eq_same, smul_eq_mul]
  ring

theorem ckerPhase_rev (m : ℕ) (θ : ℝ) :
    orderedDerivativeRev (fun _ : Fin m => (0 : Fin 2)) (ckerPhase θ) =
      fun x => (2 * Real.pi) ^ m * ckerPhase (θ + m * (Real.pi / 2)) x := by
  induction m generalizing θ with
  | zero => funext x; simp [orderedDerivativeRev]
  | succ m ih =>
    have e : orderedDerivativeRev (fun _ : Fin (m + 1) => (0 : Fin 2)) (ckerPhase θ) =
        fun x => fderiv ℝ (orderedDerivativeRev (fun _ : Fin m => (0 : Fin 2)) (ckerPhase θ)) x
          (basisVec 0) := by
      unfold orderedDerivativeRev
      rw [List.ofFn_succ]
      rfl
    rw [e, ih]
    funext x
    rw [fderiv_const_mul (ckerPhase_differentiableAt _ x), smul_apply,
      ckerPhase_fderiv, smul_eq_mul]
    have : θ + (m : ℝ) * (Real.pi / 2) + Real.pi / 2 = θ + ((m + 1 : ℕ) : ℝ) * (Real.pi / 2) := by
      push_cast; ring
    rw [this]
    ring

theorem ckerPhase_memLp (θ : ℝ) (K : ℕ) (a : JetIndex2 K) :
    MemLp (orderedDerivative a.2 (ckerPhase θ)) 2 (volume.restrict unitCube) := by
  have h : ContDiff ℝ ((1 : ℕ) : ℕ∞) (orderedDerivative a.2 (ckerPhase θ)) :=
    AVRegularity.ChartTransport.contDiff_orderedDerivative a.2
      ((ckerPhase_contDiff θ).of_le (by simp))
  exact AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On h.continuous

/-- The torus field `x ↦ cos(2π x₁)` at the order `0`. -/
def ckerZ : TorusHk 0 ℝ :=
  smoothPeriodicHk 0 (ckerPhase 0) (ckerPhase_contDiff 0) (ckerPhase_periodic 0)
    (ckerPhase_memLp 0 0)

/-- Its value class in `L²(cell)`. -/
def ckerMode : Lp ℝ 2 (volume.restrict unitCube) := ckerZ.val (valueIndex2 0)

theorem ckerMode_ae : (ckerMode : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] ckerPhase 0 := by
  have := smoothPeriodicHk_jet_ae 0 (ckerPhase 0) (ckerPhase_contDiff 0) (ckerPhase_periodic 0)
    (ckerPhase_memLp 0 0) (valueIndex2 0)
  simpa [orderedDerivative, ckerMode, ckerZ] using this

/-- **Positivity of the regularizer constants from closeness to the identity.** -/
theorem ckerPos_of_close {D : ℕ} {t₀ t₁ : ℝ} {c : ℕ → ℝ} {r : ℝ}
    {S : ℝ → (Lp ℝ 2 (volume.restrict unitCube)) →L[ℝ] (Lp ℝ 2 (volume.restrict unitCube))}
    (hreg : IsSpatialRegularizerTorus (G := ℝ) 1 0 D t₀ t₁ c r S) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) (hclose : ‖S t ckerMode - ckerMode‖ < ‖ckerMode‖) {j : ℕ}
    (hj : j + 2 ≤ D) : 0 < c j := by
  rcases (hreg.2.2.1 j hj).lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨Y, hYv, hYb⟩ := hreg.2.2.2 t ht j hj ckerZ
  rw [← h, zero_div, sq, zero_mul, zero_mul] at hYb
  -- the `j`-th jets of `Y` vanish
  have hzero : ∀ w : DerivativeWord2 (0 + j), Y.val ⟨⟨0 + j, Nat.lt_succ_self _⟩, w⟩ = 0 := by
    intro w
    have hnn : ∀ i : Fin (0 + 1), 0 ≤ factorialWeight 1 i.val *
        ∑ w : DerivativeWord2 (i.val + j), ‖Y.val ⟨⟨i.val + j, by omega⟩, w⟩‖ ^ 2 := by
      intro i
      exact mul_nonneg (by unfold factorialWeight; positivity)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h1 := (Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ (0 : Fin (0 + 1)))).trans
      hYb
    have h2 : ∑ w : DerivativeWord2 (0 + j), ‖Y.val ⟨⟨0 + j, Nat.lt_succ_self _⟩, w⟩‖ ^ 2 ≤ 0 := by
      have e : factorialWeight 1 ((0 : Fin (0 + 1)) : ℕ) = 1 := by simp [factorialWeight]
      rw [e, one_mul] at h1
      exact h1
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1
      (le_antisymm h2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)) w (Finset.mem_univ w)
    exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 h3)
  set θ : ℝ := -(((0 + j : ℕ) : ℝ) * (Real.pi / 2)) with hθ
  have hibp := cellInner_jet_eq Y (m := 0 + j) le_rfl (fun _ : Fin (0 + j) => (0 : Fin 2))
    (χ := ckerPhase θ) ((ckerPhase_contDiff θ).of_le (by simp)) (ckerPhase_periodic θ)
  have hL : cellInner (Y.toFunction.jet ⟨⟨0 + j, Nat.lt_succ_of_le le_rfl⟩,
      fun _ : Fin (0 + j) => 0⟩) (ckerPhase θ) = 0 := by
    unfold cellInner
    refine integral_eq_zero_of_ae ?_
    have hz := hzero (fun _ : Fin (0 + j) => 0)
    filter_upwards [periodicJetRepresentative_ae Y.val
      ⟨⟨0 + j, Nat.lt_succ_of_le le_rfl⟩, fun _ : Fin (0 + j) => 0⟩,
      Lp.coeFn_zero ℝ 2 (volume.restrict unitCube)] with x hx hx0
    change inner ℝ (periodicJetRepresentative Y.val _ x) _ = _
    rw [hz] at hx
    rw [hx, hx0]
    simp
  -- the value class
  have hV : cellInner (tval Y) (ckerPhase 0) = inner ℝ (S t ckerMode) ckerMode := by
    rw [L2.inner_def]
    unfold cellInner
    refine integral_congr_ae ?_
    filter_upwards [tvalL2_ae Y, ckerMode_ae] with x h1 h2
    rw [h1, h2]
    have : tvalL2 Y = S t ckerMode := hYv
    rw [this]
  have hrev := ckerPhase_rev (0 + j) θ
  have hθ0 : θ + ((0 + j : ℕ) : ℝ) * (Real.pi / 2) = 0 := by rw [hθ]; ring
  rw [hθ0] at hrev
  rw [hL, hrev] at hibp
  have hmul : cellInner (tval Y) (fun x => ((2 * Real.pi) ^ (0 + j)) • ckerPhase 0 x) =
      (2 * Real.pi) ^ (0 + j) * cellInner (tval Y) (ckerPhase 0) :=
    cellInner_smul_right _ _ _
  have hpi : (2 * Real.pi) ^ (0 + j) ≠ 0 := by positivity
  simp only [smul_eq_mul] at hmul
  rw [hmul, hV] at hibp
  have hin : inner ℝ (S t ckerMode) ckerMode = 0 := by
    have := hibp.symm
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by positivity)
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hpi
      · exact h
  have hpos : 0 < ‖ckerMode‖ := lt_of_le_of_lt (norm_nonneg _) hclose
  have hsq : ‖ckerMode‖ ^ 2 = inner ℝ (ckerMode - S t ckerMode) ckerMode := by
    rw [inner_sub_left, hin, sub_zero, real_inner_self_eq_norm_sq]
  have hle : inner ℝ (ckerMode - S t ckerMode) ckerMode ≤ ‖ckerMode - S t ckerMode‖ * ‖ckerMode‖ :=
    real_inner_le_norm _ _
  rw [norm_sub_rev] at hle
  nlinarith

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! **Two basic facts about realized flux bounds**, generic in the stages. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.Construction.Residual.Presentation

/-- A realized flux bound can be weakened. -/
theorem hasFluxBound_mono_Y {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {k : ℕ} {I : Set ℝ} {ν ρ : ℝ} {π : ι → ℝ}
    {F : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} {Y Y' : ℝ}
    (hF : HasFluxBound k I ν ρ π F Y) (hY : Y ≤ Y') : HasFluxBound k I ν ρ π F Y' := by
  obtain ⟨Fk, hr, hm⟩ := hF
  exact ⟨Fk, hr, hm.1, hm.2.trans hY⟩

end AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

open AVRegularity.Construction.Residual.Presentation

/-- A flux that vanishes on the window has every nonnegative flux bound (realized by `0`). -/
theorem hasFluxBound_of_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (k : ℕ) (I : Set ℝ) (ν ρ : ℝ) (π : ι → ℝ)
    (F : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (hF : ∀ v, ∀ t ∈ I, F v t = 0)
    {Y : ℝ} (hY : 0 ≤ Y) : HasFluxBound k I ν ρ π F Y := by
  refine ⟨fun _ _ => 0, fun v t ht => ?_, fun v => ?_, ?_⟩
  · rw [hF v t ht]
    exact torusHk_zero_jet_ae _
  · exact CoupledEnergy.Variational.timeMemLp_zero _ 2
  · simp [massNormSq, factorialNormSq, derivativeNormSq, hY]

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end
