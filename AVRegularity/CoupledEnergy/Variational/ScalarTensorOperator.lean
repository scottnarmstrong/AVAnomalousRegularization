-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
import AVRegularity.CoupledEnergy.Variational.PullbackForm
public import AVRegularity.CoupledEnergy.Variational.DriftCarrierBudget
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurCondition
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurMatrix
import AVRegularity.Analysis.Schur.Finite
public import AVRegularity.CoupledEnergy.Galerkin.PlainSynthesis
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Pointwise weak compactness in the lower-order ambient Hilbert jets. This
is used for closed-time traces after the common spacetime subsequence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The fixed lower-order Hilbert space controlling the time traces. -/
abbrev CoupledLowHilbert (K : ι → ℕ) :=
  PiLp 2 (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i) (h i))

omit [∀ i, BorelSpace (h i)] in
/-- A bounded sequence of lower jets has one pointwise weak subsequence. -/
theorem exists_strictMono_tendsto_lowHilbert_clm (K : ι → ℕ) (R : ℝ)
    (u : ℕ → CoupledLowHilbert (h := h) K) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (U : CoupledLowHilbert (h := h) K) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
        Tendsto (fun n => ell (u (φ n))) atTop (𝓝 (ell U)) := by
  let : ∀ i, InnerProductSpace ℝ (JetL2 (volume.restrict AVenhance.unitCube) (K i) (h i)) := fun i => inferInstance
  let : InnerProductSpace ℝ (CoupledLowHilbert (h := h) K) :=
    PiLp.innerProductSpace (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i) (h i))
  let : ∀ i, TopologicalSpace.SeparableSpace (JetL2 (volume.restrict AVenhance.unitCube) (K i) (h i)) :=
    fun i => torusJetSeparableSpace (K i)
  let : SecondCountableTopology (CoupledLowHilbert (h := h) K) :=
    PiLp.secondCountableTopology 2 (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i) (h i))
  let : TopologicalSpace.SeparableSpace (CoupledLowHilbert (h := h) K) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  exact exists_strictMono_tendsto_clm_of_norm_le u R hu

omit [∀ i, BorelSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- The lower-order Hilbert bound is inherited by any scalar-observable weak trace limit. -/
theorem coupledLowHilbert_norm_le_of_weak_limit (K : ι → ℕ)
    (u : ℕ → CoupledLowHilbert (h := h) K) (V : CoupledLowHilbert (h := h) K)
    (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R)
    (hw : ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
      Tendsto (fun n => ell (u n)) atTop (𝓝 (ell V))) : ‖V‖ ≤ R := by
  let : ∀ i, InnerProductSpace ℝ (JetL2 (volume.restrict AVenhance.unitCube) (K i) (h i)) :=
    fun i => inferInstance
  let : InnerProductSpace ℝ (CoupledLowHilbert (h := h) K) :=
    PiLp.innerProductSpace (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i) (h i))
  exact norm_le_of_tendsto_clm hu hw

omit [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The mass energy controls the entire lower-order ambient Hilbert norm. -/
theorem coupledLowHilbert_normSq_le_mass (K : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (U : CoupledLowHilbert (h := h) K) :
    ‖U‖ ^ 2 ≤ (∑ i, π i / factorialWeightMin ρ (K i)) * massNormSq ρ π (fun i => U i) := by
  have hi (i : ι) : ‖U i‖ ^ 2 ≤
      (π i / factorialWeightMin ρ (K i)) * massNormSq ρ π (fun i => U i) := by
    have hmin := factorialWeightMin_pos ρ hρ (K := K i)
    have he := (factorialNormSq_lower ρ (U i)).trans
      (componentFactorial_le_mass ρ π hπ (fun i => U i) i)
    calc
      ‖U i‖ ^ 2 ≤ (π i * massNormSq ρ π (fun i => U i)) / factorialWeightMin ρ (K i) := by
        rw [le_div_iff₀ hmin, mul_comm]
        exact he
      _ = _ := by ring
  rw [PiLp.norm_sq_eq_of_L2]
  simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun i _ => hi i)

end AVRegularity.CoupledEnergy.Variational
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The literal multiplier-reserve budget is exactly the Schur budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- Sum of the exact spatial multiplier and derivative-reserve costs. -/
def couplingReserveBudget (ρ : ℝ) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) (i i' : ι) : ℝ :=
  ∑ d : admissibleOrders K D i i',
    (coefficientSeminorm ρ (K i) a b (A i i' d)).toReal *
      derivativeReserveFactor ρ (K i) (d.1 - 2)

omit [Fintype ι] in
/-- Reserve shifts match the factorial ratio and radius power of the Schur matrix exactly. -/
theorem couplingReserveBudget_schurMatrix (ν ρ : ℝ) (π : ι → ℝ) (K : ι → ℕ)
    (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) (i i' : ι) :
    Real.sqrt (π i' / π i) * (couplingReserveBudget ρ K D a b A i i' / ν) =
      schurMatrix ν ρ π K D a b A i i' := by
  unfold couplingReserveBudget schurMatrix
  rw [Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  have hd : 2 ≤ d.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp d.2).1).1
  rw [show K i + d.1 - 2 = K i + (d.1 - 2) by omega]
  simp only [derivativeReserveFactor, div_eq_mul_inv, mul_inv_rev]
  ring

omit [Fintype ι] in
/-- Positivity of the reserve budget used in the weighted Schur test. -/
theorem couplingReserveBudget_nonneg (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) (i i' : ι) :
    0 ≤ couplingReserveBudget ρ K D a b A i i' := by
  apply Finset.sum_nonneg
  intro d _
  apply mul_nonneg ENNReal.toReal_nonneg
  unfold derivativeReserveFactor
  positivity

/-- The exact actual reserve budget is absorbed in the mass-weighted dissipation. -/
theorem couplingReserveBudget_quadratic_le (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A)) (y : ι → ℝ) :
    (∑ i, ∑ i', (π i)⁻¹ * couplingReserveBudget ρ K D a b A i i' * y i * y i') ≤
      (ν / 8) * ∑ i, (π i)⁻¹ * y i ^ 2 := by
  have hs := Analysis.Schur.massSchurBilinear Finset.univ π
    (fun i i' => couplingReserveBudget ρ K D a b A i i' / ν) y y (1 / 8 : ℝ)
    (fun i _ => hπ i)
    (fun i _ i' _ => div_nonneg (couplingReserveBudget_nonneg ρ hρ K D a b A i i') hν.le)
    (by norm_num)
    (by intro i _; simpa only [couplingReserveBudget_schurMatrix] using hschur.1 i)
    (by intro i' _; simpa only [couplingReserveBudget_schurMatrix] using hschur.2 i')
  have hsq : 0 ≤ ∑ i, (π i)⁻¹ * y i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr (hπ i).le) (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hs hν.le
  have hl : ν * (∑ i, ∑ i', (π i)⁻¹ * (couplingReserveBudget ρ K D a b A i i' / ν) * y i * y i') =
      ∑ i, ∑ i', (π i)⁻¹ * couplingReserveBudget ρ K D a b A i i' * y i * y i' := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro i' _
    field_simp
  rw [hl] at hmul
  have hr : ν * ((1 / 8 : ℝ) * Real.sqrt (∑ i, (π i)⁻¹ * y i ^ 2) *
      Real.sqrt (∑ i, (π i)⁻¹ * y i ^ 2)) = (ν / 8) * ∑ i, (π i)⁻¹ * y i ^ 2 := by
    rw [mul_assoc (1 / 8 : ℝ), Real.mul_self_sqrt hsq]
    ring
  rwa [hr] at hmul

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Exact mass forcing energies are continuous under componentwise strong
time L² residuals in the genuine Sobolev carriers. -/

variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem torusMassNormSq_integral_split (μ : Measure T) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (f : ∀ i, T → TorusHk (K i) (E i)) (hf : ∀ i, MemLp (f i) 2 μ) :
    (∫ t, massNormSq ρ π (fun i => (f i t).val) ∂μ) =
      ∑ i, (π i)⁻¹ * ∫ t, factorialNormSq ρ (f i t).val ∂μ := by
  change (∫ t, ∑ i, (π i)⁻¹ * factorialNormSq ρ (f i t).val ∂μ) = _
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (factorialNormSq_integrable ρ (K i) (torusJet_memLp (K i) (hf i))).const_mul ((π i)⁻¹))]
  simp_rw [integral_const_mul]

theorem torusMassNormSq_perturbed_integral_tendsto (μ : Measure T) (K : ι → ℕ)
    (ρ : ℝ) (π : ι → ℝ)
    (f : ∀ i, T → TorusHk (K i) (E i)) (hf : ∀ i, MemLp (f i) 2 μ)
    (r : ℕ → ∀ i, T → TorusHk (K i) (E i)) (hr : ∀ n i, MemLp (r n i) 2 μ)
    (hlim : ∀ i, Tendsto (fun n => ∫ t, ‖r n i t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, massNormSq ρ π (fun i => (f i t + r n i t).val) ∂μ)
      atTop (𝓝 (∫ t, massNormSq ρ π (fun i => (f i t).val) ∂μ)) := by
  let L (i : ι) : TorusHk (K i) (E i) →L[ℝ] JetL2 (volume.restrict AVenhance.unitCube) (K i) (E i) :=
    (factorialWeightedJetCLM (E := E i) (μ := volume.restrict AVenhance.unitCube) ρ (K i)).comp
      (torusHkGraph (E := E i) (K i)).toSubmodule.subtypeL
  have hLn (i : ι) : Tendsto (fun n => ∫ t, ‖L i (r n i t)‖ ^ 2 ∂μ) atTop (𝓝 0) :=
    timeL2_integral_square_clm_tendsto μ (L i) (fun n => r n i) (fun n => hr n i) (hlim i)
  have hLi (i : ι) : Tendsto (fun n => ∫ t, factorialNormSq ρ (f i t + r n i t).val ∂μ)
      atTop (𝓝 (∫ t, factorialNormSq ρ (f i t).val ∂μ)) := by
    have hfL : MemLp (fun t => L i (f i t)) 2 μ := by
      simpa only [Function.comp_def] using! (L i).comp_memLp' (hf i)
    have hrL (n : ℕ) : MemLp (fun t => L i (r n i t)) 2 μ := by
      simpa only [Function.comp_def] using! (L i).comp_memLp' (hr n i)
    have hh := timeL2_perturbed_integral_square_tendsto μ _ hfL _ hrL (hLn i)
    have he (x : TorusHk (K i) (E i)) : ‖L i x‖ ^ 2 = factorialNormSq ρ x.val :=
      factorialWeightedJet_normSq ρ x.val
    simpa only [← map_add, he] using hh
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => (hLi i).const_mul ((π i)⁻¹))
  have hp (n : ℕ) : ∀ i, MemLp (fun t => f i t + r n i t) 2 μ := by
    intro i
    exact timeMemLp_pointwise_add μ 2 (f i) (r n i) (hf i) (hr n i)
  simpa only [← torusMassNormSq_integral_split μ K ρ π _ (hp _),
    ← torusMassNormSq_integral_split μ K ρ π f hf] using hsum

end AVRegularity.CoupledEnergy.Variational
end

section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Periodic weak derivative constraints survive pointwise lower-order weak
compactness, component by component in the fixed ambient Hilbert product. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- Every component of a pointwise weak lower-jet limit is a genuine periodic Sobolev jet. -/
theorem lowHilbert_graph_of_weak_limit (K : ι → ℕ)
    {u : ℕ → CoupledLowHilbert (h := h) K} {V : CoupledLowHilbert (h := h) K}
    (hw : ∀ ell : CoupledLowHilbert (h := h) K →L[ℝ] ℝ,
      Tendsto (fun n => ell (u n)) atTop (𝓝 (ell V)))
    (hu : ∀ n i, u n i ∈ torusHkGraph (E := h i) (K i)) :
    ∀ i, V i ∈ torusHkGraph (E := h i) (K i) := by
  intro i
  apply mem_closedSubmodule_of_weak_limit (torusHkGraph (E := h i) (K i))
  · intro ell
    exact hw (ell.comp (PiLp.proj (𝕜 := ℝ) 2
      (fun j => JetL2 (volume.restrict AVenhance.unitCube) (K j) (h j)) i))
  · intro n
    exact hu n i

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! The exact time integral of the mass value-source norm is preserved
under componentwise time L¹ residuals in the Sobolev carriers. -/

variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem torusMassNorm_perturbed_integral_tendsto (μ : Measure T) (K : ι → ℕ)
    (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (f : ∀ i, T → TorusHk (K i) (E i)) (hf : ∀ i, Integrable (f i) μ)
    (r : ℕ → ∀ i, T → TorusHk (K i) (E i)) (hr : ∀ n i, Integrable (r n i) μ)
    (hlim : ∀ i, Tendsto (fun n => ∫ t, ‖r n i t‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, Real.sqrt (massNormSq ρ π (fun i => (f i t + r n i t).val)) ∂μ)
      atTop (𝓝 (∫ t, Real.sqrt (massNormSq ρ π (fun i => (f i t).val)) ∂μ)) := by
  let L := massWeightedCarrierCLM (E := E) K ρ π
  let f0 : T → (∀ i, TorusHk (K i) (E i)) := fun t i => f i t
  let r0 : ℕ → T → (∀ i, TorusHk (K i) (E i)) := fun n t i => r n i t
  have hf0 : Integrable f0 μ := timeL1_family_integrable μ f hf
  have hr0 (n : ℕ) : Integrable (r0 n) μ := timeL1_family_integrable μ (r n) (hr n)
  have hlf : Integrable (fun t => L (f0 t)) μ := by
    simpa only [Function.comp_def] using!
      memLp_one_iff_integrable.mp (L.comp_memLp' (memLp_one_iff_integrable.mpr hf0))
  have hlr (n : ℕ) : Integrable (fun t => L (r0 n t)) μ := by
    simpa only [Function.comp_def] using!
      memLp_one_iff_integrable.mp (L.comp_memLp' (memLp_one_iff_integrable.mpr (hr0 n)))
  have hl := timeL1_integral_clm_norm_tendsto μ L r0 hr0
    (timeL1_family_integral_norm_tendsto μ r hr hlim)
  have hh := timeL1_perturbed_integral_norm_tendsto μ _ hlf _ hlr hl
  have hn (w : ∀ i, TorusHk (K i) (E i)) : ‖L w‖ = Real.sqrt (massNormSq ρ π (fun i => (w i).val)) :=
    massWeightedCarrierCLM_norm K ρ π hπ w
  simpa only [← map_add, hn, f0, r0, Pi.add_apply] using hh


theorem torusMassNorm_sub_integral_tendsto (μ : Measure T) (K : ι → ℕ)
    (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (f : ∀ i, T → TorusHk (K i) (E i)) (hf : ∀ i, Integrable (f i) μ)
    (r : ℕ → ∀ i, T → TorusHk (K i) (E i)) (hr : ∀ n i, Integrable (r n i) μ)
    (hlim : ∀ i, Tendsto (fun n => ∫ t, ‖r n i t‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, Real.sqrt (massNormSq ρ π (fun i => (f i t - r n i t).val)) ∂μ)
      atTop (𝓝 (∫ t, Real.sqrt (massNormSq ρ π (fun i => (f i t).val)) ∂μ)) := by
  have hneg (n : ℕ) (i : ι) : Integrable (fun t => -r n i t) μ := by
    simpa only [Pi.neg_apply] using! (hr n i).neg
  have hnegLim (i : ι) : Tendsto (fun n => ∫ t, ‖-r n i t‖ ∂μ) atTop (𝓝 0) := by
    simpa only [norm_neg] using hlim i
  have hh := torusMassNorm_perturbed_integral_tendsto μ K ρ π hπ f hf
    (fun n i t => -r n i t) hneg hnegLim
  simpa only [sub_eq_add_neg] using hh

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Zero mass and strict component coercivity for genuine torus carriers. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusMassNormSq_zero (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    massNormSq ρ π (fun i => (0 : TorusHk (K i) (h i)).val) = 0 := by
  have hh := massWeightedCarrierCLM_normSq K ρ π hπ (0 : ∀ i, TorusHk (K i) (h i))
  rw [(massWeightedCarrierCLM (E := h) K ρ π).map_zero] at hh
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply] using! hh.symm

theorem torusCarrier_eq_zero_of_mass_le_zero (K : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (w : ∀ i, TorusHk (K i) (h i))
    (hm : massNormSq ρ π (fun i => (w i).val) ≤ 0) (i : ι) : w i = 0 := by
  have hf := (componentFactorial_le_mass ρ π hπ (fun i => (w i).val) i).trans
    (mul_nonpos_of_nonneg_of_nonpos (hπ i).le hm)
  have he : factorialNormSq ρ (w i).val = 0 := le_antisymm hf (factorialNormSq_nonneg ρ _)
  have hn := jetNorm_le_factorialRoot ρ hρ (w i).val
  rw [he, Real.sqrt_zero, zero_div] at hn
  apply Subtype.ext
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Fixed bounded readouts of periodic H¹ weak tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Read the physical two-coordinate gradient of a periodic H¹ test. -/
def torusH1GradientL2CLM : TorusHk 1 E →L[ℝ]
    ComponentL2 (volume.restrict AVenhance.unitCube) (PiLp 2 (fun _ : Fin 2 => E)) :=
  ∑ k : Fin 2, ((Galerkin.tensorEntryCLM (E := E) k).compLpL 2
    (volume.restrict AVenhance.unitCube)).comp
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 1 =>
        ComponentL2 (volume.restrict AVenhance.unitCube) E)
          ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩).comp
            (torusHkGraph (E := E) 1).toSubmodule.subtypeL)

/-- The test gradient readout represents its actual first-order jets. -/
theorem torusH1GradientL2CLM_ae (φ : TorusHk 1 E) :
    torusH1GradientL2CLM (E := E) φ =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => WithLp.toLp 2 (fun k : Fin 2 =>
        φ.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) := by
  change (∑ k : Fin 2, (Galerkin.tensorEntryCLM (E := E) k).compLpL 2
    (volume.restrict AVenhance.unitCube) (φ.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)) =ᵐ[_] _
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun k : Fin 2 =>
    (Galerkin.tensorEntryCLM (E := E) k).compLpL 2 (volume.restrict AVenhance.unitCube)
      (φ.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩))
  have hterms : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      ((Galerkin.tensorEntryCLM (E := E) k).compLpL 2 (volume.restrict AVenhance.unitCube)
        (φ.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)) x =
      Galerkin.tensorEntryCLM k (φ.val ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) := by
    rw [ae_all_iff]
    intro k
    exact ContinuousLinearMap.coeFn_compLpL _ _
  filter_upwards [hsum, hterms] with x hx hxt
  rw [hx]
  simp only [Finset.sum_apply]
  simp_rw [hxt]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [Galerkin.tensorEntryCLM, Galerkin.tensorEntryLinearMap]

variable [FiniteDimensional ℝ E]
/-- Fourier projection converges strongly in the actual weak-test gradient readout. -/
theorem torusH1Gradient_projected_tendsto (φ : TorusHk 1 E) :
    Tendsto (fun N => torusH1GradientL2CLM (E := E) (Galerkin.galerkinProj N φ)) atTop
      (𝓝 (torusH1GradientL2CLM (E := E) φ)) :=
  (torusH1GradientL2CLM (E := E)).continuous.continuousAt.tendsto.comp (Galerkin.galerkinProj_tendsto φ)

end AVRegularity.CoupledEnergy.Variational
end

section
namespace AVRegularity.CoupledEnergy.Variational

/-! Continuous operator-valued scalar tensor extension, for differentiating the drift lift. -/

variable {J L E : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Extend a scalar matrix to a Hilbert fiber as a literal finite sum of coordinate maps. -/
def scalarTensorOperator
    (T : PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : L => ℝ)) :
    PiLp 2 (fun _ : J => E) →L[ℝ] PiLp 2 (fun _ : L => E) :=
  ∑ l, ∑ j, T (PiLp.single 2 j 1) l •
    (Galerkin.tensorEntryCLM (E := E) l).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : J => E) j)

omit [FiniteDimensional ℝ E] in
/-- The operator extension applies exactly the scalar-array action already estimated by Parseval. -/
theorem scalarTensorOperator_apply
    (T : PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : L => ℝ))
    (U : PiLp 2 (fun _ : J => E)) : scalarTensorOperator T U = scalarArrayAct T U := by
  apply PiLp.ext
  intro l
  simp [scalarTensorOperator, scalarArrayAct, Galerkin.tensorEntryCLM,
    Galerkin.tensorEntryLinearMap, WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.single_apply]

/-- Scalar tensor extension never increases the operator norm. -/
theorem scalarTensorOperator_norm_le
    (T : PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : L => ℝ)) :
    ‖scalarTensorOperator (E := E) T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro U
  rw [scalarTensorOperator_apply]
  exact scalarArrayAct_norm_le T U

/-- The extension depends continuously and linearly on the original scalar matrix. -/
def scalarTensorOperatorMap :
    (PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : L => ℝ)) →L[ℝ]
      (PiLp 2 (fun _ : J => E) →L[ℝ] PiLp 2 (fun _ : L => E)) :=
  ∑ l, ∑ j,
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : L => ℝ) l).comp
      (ContinuousLinearMap.apply ℝ (PiLp 2 (fun _ : L => ℝ)) (PiLp.single 2 j 1))).smulRight
        ((Galerkin.tensorEntryCLM (E := E) l).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : J => E) j))

omit [FiniteDimensional ℝ E] in
/-- Operator-valued extension is exactly the explicit matrix lift. -/
@[simp] theorem scalarTensorOperatorMap_apply
    (T : PiLp 2 (fun _ : J => ℝ) →L[ℝ] PiLp 2 (fun _ : L => ℝ)) :
    scalarTensorOperatorMap (E := E) T = scalarTensorOperator T := by
  simp [scalarTensorOperatorMap, scalarTensorOperator]

end AVRegularity.CoupledEnergy.Variational
end
