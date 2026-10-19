-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.LowerReadout
import AVRegularity.CoupledEnergyPlane.Variational.PrincipalMask
public import AVRegularity.CoupledEnergyPlane.Variational.GradientTensorOperator
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
public import AVRegularity.CoupledEnergy.Variational.WeightedJetMap
import AVRegularity.CoupledEnergyPlane.Fourier.LaplacianProjection
import AVRegularity.CoupledEnergy.Variational.PullbackForm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.CoupledEnergy.Variational.TorusCoupledFluxValue
import AVenhance.Infra.ODE.Linear.Energy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane

/-! Reindex the literal coefficient fields, including constant continuation from a closed interval. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]

/-- A measurable physical coefficient field, with no operator-norm time premise. -/
structure ProjectedCoefficients.IsMeasurable {T : Type*} [MeasurableSpace T]
    {K : ι → ℕ} {D : ℕ} (C : ProjectedCoefficients (h := h) T K D) : Prop where
  drift : ∀ i, Measurable (Function.uncurry (C.drift i))
  coupling : ∀ i j d, Measurable (Function.uncurry (C.coupling i j d))

/-- Composition of every original coefficient field with a common time map. -/
def ProjectedCoefficients.reindex {T S : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (φ : S → T) :
    ProjectedCoefficients (h := h) S K D where
  drift := fun i s => C.drift i (φ s)
  drift_continuous := fun i s => C.drift_continuous i (φ s)
  drift_bound := C.drift_bound
  drift_bound_nonneg := C.drift_bound_nonneg
  drift_le := fun i s => C.drift_le i (φ s)
  coupling := fun i j d s => C.coupling i j d (φ s)
  coupling_continuous := fun i j d s => C.coupling_continuous i j d (φ s)
  coupling_bound := C.coupling_bound
  coupling_bound_nonneg := C.coupling_bound_nonneg
  coupling_le := fun i j d s => C.coupling_le i j d (φ s)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] in
theorem ProjectedCoefficients.IsMeasurable.reindex {T S : Type*}
    [MeasurableSpace T] [MeasurableSpace S] {K : ι → ℕ} {D : ℕ}
    {C : ProjectedCoefficients (h := h) T K D} (hc : C.IsMeasurable)
    (φ : S → T) (hφ : Measurable φ) : (C.reindex φ).IsMeasurable := by
  have hp : Measurable (fun p : S × Vec 2 => (φ p.1, p.2)) :=
    (hφ.comp measurable_fst).prodMk measurable_snd
  exact ⟨fun i => (hc.drift i).comp hp, fun i j d => (hc.coupling i j d).comp hp⟩

omit [Fintype ι] [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] in
theorem continuous_clampPoint (a b : ℝ) (hab : a ≤ b) : Continuous (clampPoint a b hab) := by
  have h : Continuous (fun t : ℝ => max a (min b t)) := by fun_prop
  exact h.subtype_mk (fun t => (clampPoint a b hab t).property)

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! The original flux and value forcing supply the projected Bochner source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Literal projected initial data. -/
def projectedInitial {K : ι → ℕ} (N : ℕ) (f : ∀ i, PlaneHk Set.univ (K i) (h i)) :
    ProjectedFamily h :=
  WithLp.toLp 2 fun i => hilbertProjection N (planeHkValueOperator (K i) (f i))

/-- Literal divergence of the projected flux, plus the projected scalar source. -/
def projectedSource {K : ι → ℕ} (N : ℕ)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (t : ℝ) : ProjectedFamily h :=
  WithLp.toLp 2 fun i =>
    bandDivergenceOperator (E := h i) N (planeHkValueOperator (K i) (F i t)) +
      hilbertProjection N (planeHkValueOperator (K i) (g i t))

omit [Fintype ι] in
theorem projectedInitial_range {K : ι → ℕ} (N : ℕ)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i)) :
    familyProjection N (projectedInitial N f) = projectedInitial N f := by
  apply PiLp.ext
  intro i
  simp only [familyProjection_component, projectedInitial, WithLp.ofLp_toLp,
    hilbertProjection_idempotent]

omit [Fintype ι] in
theorem projectedSource_range {K : ι → ℕ} (N : ℕ)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (t : ℝ) :
    familyProjection N (projectedSource N F g t) = projectedSource N F g t := by
  apply PiLp.ext
  intro i
  simp only [familyProjection_component, projectedSource, WithLp.ofLp_toLp, map_add,
    hilbertProjection_divergence, hilbertProjection_idempotent]

theorem projectedSource_intervalIntegrable {K : ι → ℕ} {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    IntervalIntegrable (projectedSource N F g) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply integrable_piLp_iff.mpr
  intro i
  exact ((bandDivergenceOperator (E := h i) N).integrable_comp
    ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).integrable_comp
      ((hF i).integrable (by norm_num)))).add
    ((hilbertProjection (E := h i) N).integrable_comp
      ((planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i)))
end

/-! Genuine time integrability of the plane forcing paired with fixed spatial tests. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem planeHkTest_intervalIntegrable {K : ℕ} {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → PlaneHk Set.univ K E)
    (hg : Integrable g (volume.restrict (Set.Icc a b)))
    (z : Lp E 2 (volume : Measure (Vec 2))) :
    IntervalIntegrable (fun s => inner ℝ (planeHkValueOperator K (g s)) z) volume a b := by
  let L := (innerSL ℝ z).comp (planeHkValueOperator (E := E) K)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  simpa only [IntegrableOn, L, Function.comp_def, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, real_inner_comm] using L.integrable_comp hg

theorem planeFluxTest_intervalIntegrable {K : ℕ} {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b)))
    (z : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) :
    IntervalIntegrable (fun s => inner ℝ (planeHkValueOperator K (F s)) z) volume a b :=
  planeHkTest_intervalIntegrable (E := PiLp 2 (fun _ : Fin 2 => E)) hab F (hF.integrable (by norm_num)) z
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! The true projected initial data converge in every fixed spatial observable. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedInitial_test_tendsto {K : ι → ℕ}
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (i : ι)
    (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => inner ℝ (projectedInitial (φ n) f i) z) atTop
      (𝓝 (inner ℝ (planeHkValueOperator (K i) (f i)) z)) := by
  have ht := (tendsto_hilbertProjection (planeHkValueOperator (K i) (f i))).comp
    hφ.tendsto_atTop
  simpa only [projectedInitial, WithLp.ofLp_toLp, Function.comp_def] using ht.inner tendsto_const_nhds

end AVRegularity.CoupledEnergyPlane
end

section
open Homogenization
namespace AVRegularity.CoupledEnergyPlane

/-! Reindexing the original coefficients reindexes their actual projected operator. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedOperator_reindex_apply {T S : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (φ : S → T) (N : ℕ) (ν : ℝ)
    (s : S) (u : ProjectedFamily h) :
    projectedOperator (C.reindex φ) N ν s u = projectedOperator C N ν (φ s) u := rfl

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! Literal component formula for the actual projected external source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
theorem projectedSource_component (K : ι → ℕ) (N : ℕ)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (t : ℝ) (i : ι) :
    projectedSource N F g t i =
      bandDivergenceOperator (E := h i) N
        (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) (F i t)) +
      hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i) (g i t)) := rfl

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Actual simultaneous plane Fourier evolutions from physical bounded measurable coefficients. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The bounded projected operator and its original source, as genuine Banach ODE data. -/
def projectedODEData {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) ℝ K D)
    (hCd : ∀ i, Measurable (Function.uncurry (C.drift i)))
    (hCa : ∀ i j d, Measurable (Function.uncurry (C.coupling i j d)))
    (N : ℕ) (ν : ℝ) (a b : ℝ) (hab : a ≤ b)
    (source : ℝ → ProjectedFamily h) (hs : IntervalIntegrable source volume a b)
    (z₀ : ProjectedFamily h) : ActionODEData (E := ProjectedFamily h) a b hab where
  A := projectedOperator C N ν
  f := source
  y₀ := z₀
  operatorBound := projectedOperatorBound C N ν
  operatorBound_nonneg := projectedOperatorBound_nonneg C N ν
  operator_stronglyMeasurable := projectedOperator_stronglyMeasurable C hCd hCa N ν
  operator_norm_le := projectedOperator_norm_le C N ν
  forcing_intervalIntegrable := hs

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! The actual projected initial data preserve the initial mass energy budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedInitial_massNormSq_le (N : ℕ) (K : ι → ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i)) :
    massNormSq ρ π (fun i => (hilbertBandHk N (K i) (projectedInitial N f i)).val) ≤
      massNormSq ρ π (fun i => (f i).val) := by
  unfold massNormSq
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hπ i).le)
  simp only [projectedInitial, WithLp.ofLp_toLp, hilbertBandHk_projection,
    planeHkValueOperator_apply]
  exact hilbertBandHk_factorialNormSq_le N (K i) ρ (f i)

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Linearity of the exact genuine H¹ native diffusion test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem nativeGradientTest_sub {a b t : ℝ} (ht : t ∈ Set.Icc a b)
    (Q Q' : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (ψ : PlaneHk Set.univ 1 E) :
    (∫ s in a..t, inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0
      (planeGradientTensor (E := E) ((Q - Q') s)))
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) =
    (∫ s in a..t, inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0
      (planeGradientTensor (E := E) (Q s)))
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) -
    ∫ s in a..t, inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0
      (planeGradientTensor (E := E) (Q' s)))
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ)) := by
  let G : PlaneHk Set.univ 1 E →L[ℝ]
      Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)) :=
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0).comp
      (planeGradientTensorOperator (E := E) 0)
  have he := timeClassReadoutPairing_sub ht G Q Q'
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))
  simpa only [G, ContinuousLinearMap.comp_apply, planeGradientTensorOperator_apply] using he

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! A fixed Hilbert readout realizes exactly the mass energy of all true Galerkin jets. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Exact mass and factorial weighting of every actual simultaneous cutoff jet. -/
def massBandJetOperator (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) :
    ProjectedFamily h →L[ℝ] PiLp 2
      (fun i => JetL2 (volume.restrict Set.univ) (K i) (h i)) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun i => JetL2 (volume.restrict Set.univ) (K i) (h i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => Real.sqrt ((π i)⁻¹) •
      (factorialWeightedJetCLM ρ (K i)).comp ((bandJetOperator N (K i)).comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i))))

omit [Fintype ι] in
theorem massBandJetOperator_component (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (u : ProjectedFamily h) (i : ι) :
    massBandJetOperator N K ρ π u i =
      Real.sqrt ((π i)⁻¹) • factorialWeightedJet ρ (hilbertBandHk N (K i) (u i)).val := rfl

theorem massBandJetOperator_normSq (N : ℕ) (K : ι → ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (u : ProjectedFamily h) :
    ‖massBandJetOperator N K ρ π u‖ ^ 2 =
      massNormSq ρ π (fun i => (hilbertBandHk N (K i) (u i)).val) := by
  change ‖massWeightedJet ρ π (fun i => (hilbertBandHk N (K i) (u i)).val)‖ ^ 2 = _
  exact massWeightedJet_normSq ρ π hπ _

theorem massBandJetOperator_inner (N : ℕ) (K : ι → ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (u q : ProjectedFamily h) :
    inner ℝ (massBandJetOperator N K ρ π u) (massBandJetOperator N K ρ π q) =
      ∑ i, (π i)⁻¹ * factorialPairing ρ (hilbertBandHk N (K i) (u i)).val
        (hilbertBandHk N (K i) (q i)).val := by
  rw [PiLp.inner_apply]
  simp only [massBandJetOperator_component, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [← factorialPairing_eq_weighted_inner]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (inv_nonneg.mpr (hπ i).le)]

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Genuine simultaneous plane Galerkin curves, with their frequency-range invariance. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Clamped original coefficient fields and the actual initial/forcing data for a fixed cutoff. -/
def intervalProjectedODEData {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Icc a b) K D) (hc : C.IsMeasurable)
    (N : ℕ) (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Icc a b))) :
    ActionODEData (E := ProjectedFamily h) a b hab :=
  let hcm := hc.reindex (clampPoint a b hab) (continuous_clampPoint a b hab).measurable
  projectedODEData (C.reindex (clampPoint a b hab)) hcm.drift hcm.coupling
    N ν a b hab (projectedSource N F g)
      (projectedSource_intervalIntegrable hab N F hF g hg) (projectedInitial N f)

/-- The actual projected system is solvable in its true bounded-frequency Hilbert range. -/
theorem exists_projectedPlaneEvolution_with_timeRegularity {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Icc a b) K D) (hc : C.IsMeasurable)
    (N : ℕ) (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Icc a b))) :
    ∃ u : C(Icc a b, ProjectedFamily h),
      (∀ t : Icc a b, u t = projectedInitial N f + ∫ s in a..t.1,
        projectedOperator (C.reindex (clampPoint a b hab)) N ν s (extendCurve hab u s) +
          projectedSource N F g s) ∧
        (∀ t : Icc a b, familyProjection N (u t) = u t) ∧
        AbsolutelyContinuousOnInterval (extendCurve hab u) a b ∧
        (∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt (extendCurve hab u)
          (projectedOperator (C.reindex (clampPoint a b hab)) N ν t
            (extendCurve hab u t) + projectedSource N F g t) t) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : ∀ i, SecondCountableTopology (Lp (h i) 2 (volume : Measure (Vec 2))) :=
    fun _ => Lp.SecondCountableTopology
  let : SecondCountableTopology (ProjectedFamily h) := PiLp.secondCountableTopology 2 _
  borelize (ProjectedFamily h)
  let data := intervalProjectedODEData hab C hc N ν f F hF g hg
  obtain ⟨u, hu, _⟩ := data.existsUnique_solution
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · intro t
    have he := congrArg (fun v : C(Icc a b, ProjectedFamily h) => v t) hu
    rw [data.volterra_apply] at he
    exact he.symm
  · intro t
    exact hu.invariantProjection data u (familyProjection N) (projectedInitial_range N f)
      (fun s x => familyProjection_operator (C.reindex (clampPoint a b hab)) N ν s x)
      (projectedSource_range N F g) t
  · exact hu.absolutelyContinuousOnInterval data
  · exact hu.ae_hasDerivAt data

end AVRegularity.CoupledEnergyPlane
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! Exact separation of diffusion, drift and every admissible edge in the actual projected PDE. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedOperator_row_energy {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν ρ : ℝ) (t : T)
    (u : ProjectedFamily h) (i : ι) :
    factorialPairing ρ (hilbertBandHk N (K i) (projectedOperator C N ν t u i)).val
      (hilbertBandHk N (K i) (u i)).val =
    -factorialPairing ρ
      (hilbertBandHk N (K i) (hilbertProjection N
        (planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
          (C.drift_bound_nonneg i) (C.drift_le i t)
          (bandGradientOperator (E := h i) N (u i))))).val
      (hilbertBandHk N (K i) (u i)).val -
    ν * gradFactorialNormSq ρ (hilbertBandHk N (K i + 1) (u i)).val +
    ∑ j : ι, ∑ d : admissibleOrders K D i j, factorialPairing ρ
      (hilbertBandHk N (K i) (bandDivergenceOperator (E := h i) N
        (planeCoefficientOperator (C.coupling i j d t) (C.coupling_continuous i j d t)
          (C.coupling_bound_nonneg i j d) (C.coupling_le i j d t)
          (bandTensorOperator (E := h j) N (d.1 - 1) (u j))))).val
      (hilbertBandHk N (K i) (u i)).val := by
  rw [projectedOperator_component]
  simp only [bandPairing_add, bandPairing_neg, bandPairing_smul,
    bandLaplacian_factorialPairing, bandPairing_sum]
  ring

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane

/-! Literal spatial testing of the actual Galerkin integral equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem intervalProjectedRhs_intervalIntegrable {K : ι → ℕ} {D : ℕ} {a b : ℝ}
    (hab : a ≤ b) (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D)
    (hc : C.IsMeasurable) (N : ℕ) (ν : ℝ)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : C(Set.Icc a b, ProjectedFamily h)) :
    IntervalIntegrable (fun t => projectedOperator (C.reindex (clampPoint a b hab))
      N ν t (extendCurve hab u t) + projectedSource N F g t) volume a b := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : ∀ i, SecondCountableTopology (Lp (h i) 2 (volume : Measure (Vec 2))) :=
    fun _ => Lp.SecondCountableTopology
  let : SecondCountableTopology (ProjectedFamily h) := PiLp.secondCountableTopology 2 _
  borelize (ProjectedFamily h)
  let f : ∀ i, PlaneHk Set.univ (K i) (h i) := fun _ => 0
  exact (intervalProjectedODEData hab C hc N ν f F hF g hg).rhs_intervalIntegrable u

theorem projectedCurve_test_identity_of_integralEquation {K : ι → ℕ} {D : ℕ} {a b : ℝ}
    (hab : a ≤ b) (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D)
    (hc : C.IsMeasurable) (N : ℕ) (ν : ℝ)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : C(Set.Icc a b, ProjectedFamily h))
    (hu : ∀ t : Set.Icc a b, u t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator (C.reindex (clampPoint a b hab)) N ν s (extendCurve hab u s) +
        projectedSource N F g s)
    (i : ι) (t : Set.Icc a b) (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    inner ℝ (u t i) z = inner ℝ (projectedInitial N f i) z + ∫ s in a..t.1,
      inner ℝ ((projectedOperator (C.reindex (clampPoint a b hab)) N ν s
        (extendCurve hab u s) + projectedSource N F g s) i) z := by
  let L : ProjectedFamily h →L[ℝ] ℝ := (innerSL ℝ z).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i)
  have hint := intervalProjectedRhs_intervalIntegrable hab C hc N ν F hF g hg u
  have hsub : Set.uIcc a t.1 ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le t.property.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl t.property.2
  have he := congrArg L (hu t)
  rw [map_add, ← L.intervalIntegral_comp_comm (hint.mono_set hsub)] at he
  simpa only [L, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    innerSL_apply_apply, real_inner_comm] using he

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! The exact time derivative of the mass energy, with the PDE on the tested side. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem hasDerivAt_massBandEnergy (N : ℕ) (K : ι → ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    {u : ℝ → ProjectedFamily h} {q : ProjectedFamily h} {t : ℝ}
    (hu : HasDerivAt u q t) :
    HasDerivAt (fun s => massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u s i)).val))
      (2 * ∑ i, (π i)⁻¹ * factorialPairing ρ
        (hilbertBandHk N (K i) (q i)).val (hilbertBandHk N (K i) (u t i)).val) t := by
  have he := ((massBandJetOperator (h := h) N K ρ π).hasFDerivAt.comp_hasDerivAt t hu).norm_sq
  simp only [Function.comp_def, massBandJetOperator_normSq N K ρ π hπ,
    massBandJetOperator_inner N K ρ π hπ] at he
  simpa only [factorialPairing_comm] using he
end

/-! Exact native spatial row tested in plane L², retaining the projected drift and flux tests. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedOperator_row_inner {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) (t : T)
    (u : ProjectedFamily h) (i : ι) (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    inner ℝ (projectedOperator C N ν t u i) z =
      -inner ℝ (planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
        (C.drift_bound_nonneg i) (C.drift_le i t) (bandGradientOperator (E := h i) N (u i)))
        (hilbertProjection N z) -
      ν * inner ℝ (bandGradientOperator (E := h i) N (u i))
        (bandGradientOperator (E := h i) N z) -
      ∑ j : ι, ∑ d : admissibleOrders K D i j, inner ℝ
        (planeCoefficientOperator (C.coupling i j d t) (C.coupling_continuous i j d t)
          (C.coupling_bound_nonneg i j d) (C.coupling_le i j d t)
          (bandTensorOperator (E := h j) N (d.1 - 1) (u j)))
        (bandGradientOperator (E := h i) N z) := by
  rw [projectedOperator_component]
  simp only [inner_add_left, inner_neg_left, real_inner_smul_left, sum_inner,
    hilbertProjection_inner, bandLaplacian_gradient_inner, bandDivergence_gradient_inner,
    Finset.sum_neg_distrib]
  ring

omit [Fintype ι] in
theorem projectedSource_inner {K : ι → ℕ} (N : ℕ)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (t : ℝ) (i : ι)
    (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    inner ℝ (projectedSource N F g t i) z =
      -inner ℝ (planeHkValueOperator (K i) (F i t)) (bandGradientOperator (E := h i) N z) +
        inner ℝ (planeHkValueOperator (K i) (g i t)) (hilbertProjection N z) := by
  simp only [projectedSource, WithLp.ofLp_toLp, inner_add_left,
    bandDivergence_gradient_inner, hilbertProjection_inner]
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergyPlane.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! The original L² flux and L¹ value forcing pass to projected spatial tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem valueForcing_projected_test_tendsto {K : ℕ} {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (g : ℝ → PlaneHk Set.univ K E)
    (hg : Integrable g (volume.restrict (Set.Icc a b)))
    (z : Lp E 2 (volume : Measure (Vec 2))) :
    Tendsto (fun N => ∫ s in a..t,
      inner ℝ (hilbertProjection N (planeHkValueOperator K (g s))) z) atTop
      (𝓝 (∫ s in a..t, inner ℝ (planeHkValueOperator K (g s)) z)) := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    ((planeHkValueOperator (E := E) K).integrable_comp hg)
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl ht.2
  simp_rw [hilbertProjection_inner]
  exact l1TimeTest_integral_tendsto (fun s => planeHkValueOperator K (g s))
    (hi.mono_set hsub) _ z (tendsto_hilbertProjection z)

theorem fluxForcing_projected_test_tendsto {K : ℕ} {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b)))
    (φ : PlaneHk Set.univ 1 E) :
    Tendsto (fun N => ∫ s in a..t, inner ℝ
      (planeHkValueOperator K (F s)) (bandGradientOperator (E := E) N (planeHkValueOperator 1 φ))) atTop
      (𝓝 (∫ s in a..t, inner ℝ (planeHkValueOperator K (F s))
        (planeHkValueOperator 0 (planeGradientTensor φ)))) := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K).integrable_comp
      (hF.integrable (by norm_num)))
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl ht.2
  exact l1TimeTest_integral_tendsto (fun s => planeHkValueOperator K (F s))
    (hi.mono_set hsub) _ _ (tendsto_bandGradient_planeH1_value φ)

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! Time regularity of the actual cutoff mass energy and dissipation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem massBandEnergy_absolutelyContinuous (N : ℕ) (K : ι → ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {a b : ℝ}
    {u : ℝ → ProjectedFamily h} (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t => massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u t i)).val)) a b := by
  have he := ((massBandJetOperator (h := h) N K ρ π).lipschitzWith.comp_absolutelyContinuousOnInterval hu).norm_sq
  simpa only [Function.comp_def, massBandJetOperator_normSq N K ρ π hπ] using he

theorem continuous_massBandGradient (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) :
    Continuous (fun u : ProjectedFamily h => massGradNormSq ρ π
      (fun i => (hilbertBandHk N (K i + 1) (u i)).val)) := by
  unfold massGradNormSq gradFactorialNormSq
  apply continuous_finsetSum
  intro i _
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro j _
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro w _
  have hc := ((PiLp.proj (𝕜 := ℝ) 2
    (fun _ : JetIndex2 (K i + 1) => ComponentL2 (volume.restrict Set.univ) (h i))
    ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩).comp
      ((bandJetOperator (E := h i) N (K i + 1)).comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun k => Lp (h k) 2 (volume : Measure (Vec 2))) i))).continuous
  exact hc.norm.pow 2

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The actual fixed-frequency right-hand side has the native weak gradient pairing. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance rhsNativeCarrierAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance rhsNativeCarrierTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

theorem fixedBandRhs_native_test_ae {a b : ℝ} (N : ℕ) (ν : ℝ)
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (z : Lp E 2 (volume : Measure (Vec 2))) :
    (fun s => inner ℝ (fixedBandRhs N ν
      ((planeHkValueOperator (E := E) 1).compLpL 2 (volume.restrict (Set.Icc a b)) Q)
      D F g s) z) =ᵐ[volume.restrict (Set.Icc a b)] fun s =>
      -inner ℝ (D s) (hilbertProjection N z) -
        ν * inner ℝ (planeHkValueOperator 0 (planeGradientTensor (Q s)))
          (bandGradientOperator (E := E) N z) -
        inner ℝ (F s) (bandGradientOperator (E := E) N z) +
        inner ℝ (g s) (hilbertProjection N z) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (planeHkValueOperator (E := E) 1) Q]
    with s hq
  simp only [fixedBandRhs, inner_add_left, inner_neg_left, real_inner_smul_left, hq,
    hilbertProjection_inner, bandLaplacian_planeH1_pairing, bandDivergence_gradient_inner]
  ring
end

/-! Literal native integral formula for every fixed-band continuous primitive. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance primitiveNativeCarrierAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance primitiveNativeCarrierTopAdd (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k E) := inferInstance

theorem fixedBandPrimitive_native_test {a b : ℝ} (hab : a ≤ b) (N : ℕ) (ν : ℝ)
    (f : Lp E 2 (volume : Measure (Vec 2)))
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (t : Set.Icc a b)
    (z : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (fixedBandPrimitive hab N ν f
      ((planeHkValueOperator (E := E) 1).compLpL 2 (volume.restrict (Set.Icc a b)) Q)
      D F g hg t) z = inner ℝ f (hilbertProjection N z) +
      ∫ s in a..t.1,
        -inner ℝ (D s) (hilbertProjection N z) -
          ν * inner ℝ (planeHkValueOperator 0 (planeGradientTensor (Q s)))
            (bandGradientOperator (E := E) N z) -
          inner ℝ (F s) (bandGradientOperator (E := E) N z) +
          inner ℝ (g s) (hilbertProjection N z) := by
  have hp := fixedBandPrimitive_test hab N ν f
    ((planeHkValueOperator (E := E) 1).compLpL 2 (volume.restrict (Set.Icc a b)) Q)
    D F g hg t ((innerSL ℝ).flip z)
  simp only [ContinuousLinearMap.flip_apply, innerSL_apply_apply] at hp
  rw [hp, hilbertProjection_inner]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub : Set.uIoc a t.1 ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le t.property.1]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl t.property.2)
  exact ae_restrict_of_ae_restrict_of_subset hsub (fixedBandRhs_native_test_ae N ν Q D F g z)
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The data of the statement themselves supply every bounded coefficient used in the plane
approximation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem driftFiberCoefficient_norm_le (v : Vec 2 → Vec 2) (x : Vec 2) :
    ‖driftFiberCoefficient (E := E) v x‖ ≤ 2 * ‖v x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg _))
  intro U
  rw [driftFiberCoefficient_apply]
  calc
    ‖∑ k : Fin 2, v x k • U k‖ ≤ ∑ k : Fin 2, ‖v x k • U k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 2, ‖v x‖ * ‖U‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm (v x) k) (PiLp.norm_apply_le U k)
        (norm_nonneg _) (norm_nonneg _)
    _ = 2 * ‖v x‖ * ‖U‖ := by simp [mul_assoc]

theorem driftFiberCoefficient_measurable {T : Type*} [MeasurableSpace T]
    (v : T → Vec 2 → Vec 2) (hv : Measurable (Function.uncurry v)) :
    Measurable (fun p : T × Vec 2 => driftFiberCoefficient (E := E) (v p.1) p.2) := by
  have he : (fun p : T × Vec 2 => driftFiberCoefficient (E := E) (v p.1) p.2) =
      fun p => ∑ k : Fin 2, (v p.1 p.2 k) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k := by
    funext p
    apply ContinuousLinearMap.ext
    intro U
    simp only [driftFiberCoefficient_apply, sum_apply, smul_apply, PiLp.proj_apply]
  rw [he]
  apply Finset.measurable_sum
  intro k _
  exact ((measurable_pi_apply k).comp hv).smul measurable_const

omit [FiniteDimensional ℝ E] in
/-- The zeroth seminorm summand bounds the coefficient itself on the whole plane. -/
theorem sourceCoefficient_norm_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : AVRegularity.coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (x : Vec 2) :
    ‖A t x‖ ≤ (AVRegularity.coefficientSeminorm ρ K a b A).toReal := by
  have hz : ‖A t x‖ ≤ ‖coefficientDerivativeArray (A t) 0 x‖ := by
    simpa only [orderedCoefficientDerivative_zero] using
      orderedCoefficientDerivative_norm_le_array (A t) 0 Fin.elim0 x
  have hb := coefficientSeminorm_derivative_bound ρ hρ K a b A hA
    ⟨0, Nat.succ_pos K⟩ t ht x
  exact hz.trans (by simpa using hb)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]

/-- The original drift and couplings on the literal time interval, with bounds derived from data. -/
def sourceProjectedCoefficients (a b ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤) :
    ProjectedCoefficients (h := h) (Set.Icc a b) K D where
  drift := fun _ t => driftFiberCoefficient (v t)
  drift_continuous := fun _ t => (driftFiberCoefficient_contDiff (v t) (hv t t.property)).continuous
  drift_bound := fun _ => 2 * V
  drift_bound_nonneg := fun _ => mul_nonneg (by norm_num) hV
  drift_le := fun _ t x => (driftFiberCoefficient_norm_le (v t) x).trans
    (mul_le_mul_of_nonneg_left (hbv t t.property x) (by norm_num))
  coupling := fun i j d t => A i j d t
  coupling_continuous := fun i j d t => (hAc i j d t t.property).continuous
  coupling_bound := fun i j d => (AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d)).toReal
  coupling_bound_nonneg := fun _ _ _ => ENNReal.toReal_nonneg
  coupling_le := fun i j d t x => sourceCoefficient_norm_le ρ hρ (K i) a b
    (A i j d) (hAf i j d) t t.property x

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] in
/-- The measurability premises of `coupled_energy_plane` apply to the constructed physical
fields. -/
theorem sourceProjectedCoefficients_isMeasurable (a b ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)) :
    (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).IsMeasurable := by
  exact ⟨fun i => driftFiberCoefficient_measurable (E := h i)
    (fun t : Set.Icc a b => v t) hvm, hAm⟩

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! A native tested time equation for genuine H¹ carriers and integrable raw fields. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance nativeRawCarrierAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance nativeRawCarrierTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

def nativeRawTestValue {a b : ℝ} (ν : ℝ)
    (f : Lp E 2 (volume : Measure (Vec 2)))
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (t : ℝ) (ψ : PlaneHk Set.univ 1 E) : ℝ :=
  inner ℝ f (planeHkValueOperator 1 ψ) + ∫ s in a..t,
    -inner ℝ (D s) (planeHkValueOperator 1 ψ) -
      ν * inner ℝ (planeHkValueOperator 0 (planeGradientTensor (Q s)))
        (planeHkValueOperator 0 (planeGradientTensor ψ)) -
      inner ℝ (F s) (planeHkValueOperator 0 (planeGradientTensor ψ)) +
      inner ℝ (g s) (planeHkValueOperator 1 ψ)

theorem fixedBandPrimitive_eq_nativeRawTestValue {a b : ℝ} (hab : a ≤ b) (N : ℕ) (ν : ℝ)
    (f : Lp E 2 (volume : Measure (Vec 2)))
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (t : Set.Icc a b)
    (z : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (fixedBandPrimitive hab N ν f
      ((planeHkValueOperator (E := E) 1).compLpL 2 (volume.restrict (Set.Icc a b)) Q)
      D F g hg t) z = nativeRawTestValue ν f Q D F g t (hilbertBandHk N 1 z) := by
  rw [fixedBandPrimitive_native_test]
  have hv : planeHkValueOperator 1 (hilbertBandHk N 1 z) = hilbertProjection N z :=
    planeHkValueOperator_hilbertBand N 1 z
  simp only [nativeRawTestValue, hv, planeGradientTensor_band_value]

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! Actual higher-order Bochner jets of the plane Galerkin curves. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

abbrev PlaneHighHilbert (K : ι → ℕ) :=
  PiLp 2 (fun i => JetL2 (volume.restrict Set.univ) (K i + 1) (h i))

abbrev PlaneHighTime (K : ι → ℕ) (a b : ℝ) :=
  Lp (PlaneHighHilbert (h := h) K) 2 (volume.restrict (Set.Icc a b))

def higherBandJetOperator (N : ℕ) (K : ι → ℕ) :
    ProjectedFamily h →L[ℝ] PlaneHighHilbert (h := h) K :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun i => JetL2 (volume.restrict Set.univ) (K i + 1) (h i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (bandJetOperator N (K i + 1)).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i)))

omit [Fintype ι] in
@[simp] theorem higherBandJetOperator_component (N : ℕ) (K : ι → ℕ)
    (u : ProjectedFamily h) (i : ι) :
    higherBandJetOperator N K u i = (hilbertBandHk N (K i + 1) (u i)).val := rfl

theorem higherBandJet_memLp (N : ℕ) (K : ι → ℕ) (a b : ℝ)
    {u : ℝ → ProjectedFamily h} (hu : Continuous u) :
    MemLp (fun t => higherBandJetOperator N K (u t)) 2 (volume.restrict (Set.Icc a b)) := by
  let : SecondCountableTopologyEither ℝ (PlaneHighHilbert (h := h) K) :=
    secondCountableTopologyEither_of_left ℝ _
  have hc := (higherBandJetOperator (h := h) N K).continuous.comp hu
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable.restrict).mpr
    ((hc.norm.pow 2).integrableOn_Icc)

theorem higherBandJet_normSq_le (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (u : ProjectedFamily h) :
    ‖higherBandJetOperator N K u‖ ^ 2 ≤
      (∑ i, π i) * massNormSq ρ π (fun i => (hilbertBandHk N (K i) (u i)).val) +
      (∑ i, π i / factorialWeightMin ρ (K i)) * massGradNormSq ρ π
        (fun i => (hilbertBandHk N (K i + 1) (u i)).val) := by
  have he : (fun i => truncateJet (Nat.le_succ (K i))
      (hilbertBandHk N (K i + 1) (u i)).val) =
      (fun i => (hilbertBandHk N (K i) (u i)).val) := by
    funext i
    exact (congrArg Subtype.val (hilbertBandHk_truncate N (K i) (K i + 1)
      (Nat.le_succ (K i)) (u i)))
  rw [PiLp.norm_sq_eq_of_L2]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    componentJetNormSq_le_mass ρ hρ π hπ
      (fun j => (hilbertBandHk N (K j + 1) (u j)).val) i)
  rw [he] at hs
  simpa only [higherBandJetOperator_component, Finset.sum_add_distrib, ← Finset.sum_mul] using hs

def higherBandBochner (N : ℕ) (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (u : C(Set.Icc a b, ProjectedFamily h)) : PlaneHighTime (h := h) K a b :=
  (higherBandJet_memLp N K a b (continuous_extendCurve hab u)).toLp
    (fun t => higherBandJetOperator N K (extendCurve hab u t))

theorem higherBandBochner_normSq (N : ℕ) (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (u : C(Set.Icc a b, ProjectedFamily h)) :
    ‖higherBandBochner N K a b hab u‖ ^ 2 =
      ∫ t in Set.Icc a b, ‖higherBandJetOperator N K (extendCurve hab u t)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(higherBandJet_memLp N K a b (continuous_extendCurve hab u)).coeFn_toLp] with t ht
  change inner ℝ
    ((higherBandJet_memLp N K a b (continuous_extendCurve hab u)).toLp
      (fun s => higherBandJetOperator N K (extendCurve hab u s)) t)
    ((higherBandJet_memLp N K a b (continuous_extendCurve hab u)).toLp
      (fun s => higherBandJetOperator N K (extendCurve hab u s)) t) = _
  rw [ht, real_inner_self_eq_norm_sq]

theorem higherBandBochner_graph_ae (N : ℕ) (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (u : C(Set.Icc a b, ProjectedFamily h)) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      higherBandBochner N K a b hab u t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1) := by
  filter_upwards [(higherBandJet_memLp N K a b (continuous_extendCurve hab u)).coeFn_toLp] with t ht
  intro i
  change (higherBandJet_memLp N K a b (continuous_extendCurve hab u)).toLp
    (fun s => higherBandJetOperator N K (extendCurve hab u s)) t i ∈ _
  rw [ht, higherBandJetOperator_component]
  exact (hilbertBandHk N (K i + 1) (extendCurve hab u t i)).property

end AVRegularity.CoupledEnergyPlane
end
end
end
