-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.HigherReadout
import AVRegularity.CoupledEnergyPlane.Variational.PrincipalMask
public import AVRegularity.CoupledEnergyPlane.Variational.FiniteFamilyPrimitive

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! The individual native drift and coupling integrals in the tested Galerkin row are integrable. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem driftTest_intervalIntegrable {K : ι → ℕ} {D : ℕ} {a b : ℝ}
    (hab : a ≤ b) (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D)
    (hc : C.IsMeasurable) (N : ℕ) (u : C(Set.Icc a b, ProjectedFamily h))
    (i : ι) (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    IntervalIntegrable (fun s => inner ℝ
      (planeCoefficientOperator
        ((C.reindex (clampPoint a b hab)).drift i s)
        ((C.reindex (clampPoint a b hab)).drift_continuous i s)
        (C.drift_bound_nonneg i) ((C.reindex (clampPoint a b hab)).drift_le i s)
        (bandGradientOperator (E := h i) N (extendCurve hab u s i)))
      (hilbertProjection N z)) volume a b := by
  have hm := hc.reindex (clampPoint a b hab) (continuous_clampPoint a b hab).measurable
  have hu := ((bandGradientOperator (E := h i) N).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i)).continuous.comp
    (continuous_extendCurve hab u)
  exact planeCoefficientAction_inner_intervalIntegrable hab
    ((C.reindex (clampPoint a b hab)).drift i)
    ((C.reindex (clampPoint a b hab)).drift_continuous i) (hm.drift i)
    (C.drift_bound_nonneg i) ((C.reindex (clampPoint a b hab)).drift_le i)
    (fun s => bandGradientOperator (E := h i) N (extendCurve hab u s i)) hu (hilbertProjection N z)

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem edgeTest_intervalIntegrable {K : ι → ℕ} {D : ℕ} {a b : ℝ}
    (hab : a ≤ b) (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D)
    (hc : C.IsMeasurable) (N : ℕ) (u : C(Set.Icc a b, ProjectedFamily h))
    (i j : ι) (d : admissibleOrders K D i j) (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    IntervalIntegrable (fun s => inner ℝ
      (planeCoefficientOperator
        ((C.reindex (clampPoint a b hab)).coupling i j d s)
        ((C.reindex (clampPoint a b hab)).coupling_continuous i j d s)
        (C.coupling_bound_nonneg i j d) ((C.reindex (clampPoint a b hab)).coupling_le i j d s)
        (bandTensorOperator (E := h j) N (d.1 - 1) (extendCurve hab u s j)))
      (bandGradientOperator (E := h i) N z)) volume a b := by
  have hm := hc.reindex (clampPoint a b hab) (continuous_clampPoint a b hab).measurable
  have hu := ((bandTensorOperator (E := h j) N (d.1 - 1)).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun k => Lp (h k) 2 (volume : Measure (Vec 2))) j)).continuous.comp
    (continuous_extendCurve hab u)
  exact planeCoefficientAction_inner_intervalIntegrable hab
    ((C.reindex (clampPoint a b hab)).coupling i j d)
    ((C.reindex (clampPoint a b hab)).coupling_continuous i j d) (hm.coupling i j d)
    (C.coupling_bound_nonneg i j d) ((C.reindex (clampPoint a b hab)).coupling_le i j d)
    (fun s => bandTensorOperator (E := h j) N (d.1 - 1) (extendCurve hab u s j)) hu
    (bandGradientOperator (E := h i) N z)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem diffusionTest_intervalIntegrable {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (u : C(Set.Icc a b, ProjectedFamily h)) (i : ι)
    (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    IntervalIntegrable (fun s => inner ℝ
      (bandGradientOperator (E := h i) N (extendCurve hab u s i))
      (bandGradientOperator (E := h i) N z)) volume a b := by
  have hu := ((bandGradientOperator (E := h i) N).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i)).continuous.comp
    (continuous_extendCurve hab u)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    ((hu.inner continuous_const).integrableOn_Icc)

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Conditional conversion of a native tested equation into the actual continuous fixed-band trace. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance allTimeIdentificationCarrierAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) :=
  inferInstance
local instance allTimeIdentificationCarrierTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

theorem fixedBandPrimitive_eq_cutoff_of_allTime_native_equation {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (ν : ℝ) (f : Lp E 2 (volume : Measure (Vec 2)))
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b)))
    (u : Set.Icc a b → Lp E 2 (volume : Measure (Vec 2)))
    (hweak : ∀ t : Set.Icc a b, ∀ ψ : PlaneHk Set.univ 1 E,
      inner ℝ (u t) (planeHkValueOperator 1 ψ) = nativeRawTestValue ν f Q D F g t ψ)
    (t : Set.Icc a b) :
    fixedBandPrimitive hab N ν f
      ((planeHkValueOperator (E := E) 1).compLpL 2 (volume.restrict (Set.Icc a b)) Q)
      D F g hg t = hilbertProjection N (u t) := by
  apply ext_inner_right (𝕜 := ℝ)
  intro z
  rw [fixedBandPrimitive_eq_nativeRawTestValue, ← hweak t (hilbertBandHk N 1 z)]
  simp only [planeHkValueOperator_apply, hilbertBandHk_value,
    AVRegularity.Analysis.Convolution.univToPlane_planeToUniv]
  exact (hilbertProjection_inner N (u t) z).symm
end

/-! Conditional conversion of a native tested equation into the actual continuous fixed-band trace. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance identificationCarrierAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) :=
  inferInstance
local instance identificationCarrierTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

theorem fixedBandPrimitive_ae_eq_cutoff_of_native_equation {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (ν : ℝ) (f : Lp E 2 (volume : Measure (Vec 2)))
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b)))
    (hweak : ∀ ψ : PlaneHk Set.univ 1 E,
      (fun t => inner ℝ (planeHkValueOperator 1 (Q t)) (planeHkValueOperator 1 ψ))
        =ᵐ[volume.restrict (Set.Icc a b)] fun t => nativeRawTestValue ν f Q D F g t ψ) :
    extendCurve hab (fixedBandPrimitive hab N ν f
      ((planeHkValueOperator (E := E) 1).compLpL 2 (volume.restrict (Set.Icc a b)) Q)
      D F g hg) =ᵐ[volume.restrict (Set.Icc a b)]
        fun t => hilbertProjection N (planeHkValueOperator 1 (Q t)) := by
  apply planeL2_ae_eq_of_H1_tests
  intro ψ
  let z := planeHkValueOperator 1 ψ
  filter_upwards [hweak (hilbertBandHk N 1 z), ae_restrict_mem measurableSet_Icc]
    with t ht htm
  rw [extendCurve_eq_of_mem hab _ htm,
    fixedBandPrimitive_eq_nativeRawTestValue, ← ht]
  simp only [planeHkValueOperator_apply, hilbertBandHk_value,
    AVRegularity.Analysis.Convolution.univToPlane_planeToUniv]
  exact (hilbertProjection_inner N _ z).symm
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Fixed spatial and temporal differential readouts from the common weak Hilbert class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def highJetReadout (K : ι → ℕ) (i : ι) (α : JetIndex2 (K i + 1)) :
    PlaneHighHilbert (h := h) K →L[ℝ] Lp (h i) 2 (volume : Measure (Vec 2)) :=
  univToPlane.toContinuousLinearMap.comp
    ((PiLp.proj (𝕜 := ℝ) 2
      (fun _ : JetIndex2 (K i + 1) => ComponentL2 (volume.restrict Set.univ) (h i)) α).comp
        (PiLp.proj (𝕜 := ℝ) 2
          (fun j => JetL2 (volume.restrict Set.univ) (K j + 1) (h j)) i))

def highTensorReadout (K : ι → ℕ) (i : ι) (r : ℕ) (hr : r ≤ K i + 1) :
    PlaneHighHilbert (h := h) K →L[ℝ]
      Lp (PiLp 2 (fun _ : DerivativeWord2 r => h i)) 2 (volume : Measure (Vec 2)) :=
  ∑ w : DerivativeWord2 r,
    ((tensorEntryCLM (E := h i) w).compLpL 2 volume).comp
      (highJetReadout (h := h) K i ⟨⟨r, by omega⟩, w⟩)

omit [Fintype ι] in
theorem highTensorReadout_band (N : ℕ) (K : ι → ℕ) (i : ι)
    (r : ℕ) (hr : r ≤ K i + 1) (u : ProjectedFamily h) :
    highTensorReadout (h := h) K i r hr (higherBandJetOperator (h := h) N K u) =
      bandTensorOperator (E := h i) N r (u i) := by
  simp only [highTensorReadout, bandTensorOperator, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  change univToPlane ((hilbertBandHk N (K i + 1) (u i)).val ⟨⟨r, by omega⟩, w⟩) = _
  rw [hilbertBandHk_component, univToPlane_planeToUniv]
  rfl

theorem highTensorReadout_band_time_ae (N : ℕ) (K : ι → ℕ) (a b : ℝ)
    (hab : a ≤ b) (u : C(Set.Icc a b, ProjectedFamily h)) (i : ι)
    (r : ℕ) (hr : r ≤ K i + 1) :
    (highTensorReadout (h := h) K i r hr).compLpL 2 (volume.restrict (Set.Icc a b))
      (higherBandBochner N K a b hab u) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => bandTensorOperator (E := h i) N r (extendCurve hab u t i) := by
  have hcoe : higherBandBochner N K a b hab u =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => higherBandJetOperator (h := h) N K (extendCurve hab u t) :=
    (higherBandJet_memLp N K a b (continuous_extendCurve hab u)).coeFn_toLp
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (highTensorReadout (h := h) K i r hr) (higherBandBochner N K a b hab u), hcoe]
    with t ht hc
  rw [ht, hc, highTensorReadout_band]

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane

/-! Fixed two-direction gradient readout from the common higher-order spacetime carrier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def highGradientReadout (K : ι → ℕ) (i : ι) :
    PlaneHighHilbert (h := h) K →L[ℝ]
      Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)) :=
  ∑ k : Fin 2, ((tensorEntryCLM (E := h i) k).compLpL 2 volume).comp
    (highJetReadout (h := h) K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)

omit [Fintype ι] in
theorem highGradientReadout_band (N : ℕ) (K : ι → ℕ) (i : ι) (u : ProjectedFamily h) :
    highGradientReadout (h := h) K i (higherBandJetOperator (h := h) N K u) =
      bandGradientOperator (E := h i) N (u i) := by
  simp only [highGradientReadout, bandGradientOperator, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  change univToPlane ((hilbertBandHk N (K i + 1) (u i)).val
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩) = _
  rw [hilbertBandHk_component, univToPlane_planeToUniv]
  rfl

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Every term of the native time-tested equation is genuinely integrable. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance rawIntegralCarrierAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance rawIntegralCarrierTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

theorem nativeRawTest_terms_integrable {a b : ℝ}
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (ψ : PlaneHk Set.univ 1 E) :
    Integrable (fun s => inner ℝ (D s) (planeHkValueOperator 1 ψ))
        (volume.restrict (Set.Icc a b)) ∧
      Integrable (fun s => inner ℝ (planeHkValueOperator 0 (planeGradientTensor (Q s)))
        (planeHkValueOperator 0 (planeGradientTensor ψ))) (volume.restrict (Set.Icc a b)) ∧
      Integrable (fun s => inner ℝ (F s) (planeHkValueOperator 0 (planeGradientTensor ψ)))
        (volume.restrict (Set.Icc a b)) ∧
      Integrable (fun s => inner ℝ (g s) (planeHkValueOperator 1 ψ))
        (volume.restrict (Set.Icc a b)) := by
  let μ := volume.restrict (Set.Icc a b)
  let z := planeHkValueOperator 1 ψ
  let p := planeHkValueOperator 0 (planeGradientTensor ψ)
  have hd := timeL2_observable_integrable μ D ((innerSL ℝ).flip z)
  have hf := timeL2_observable_integrable μ F ((innerSL ℝ).flip p)
  let L : PlaneHk Set.univ 1 E →L[ℝ] ℝ := ((innerSL ℝ).flip p).comp
    ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0).comp
      (planeGradientTensorOperator (E := E) 0))
  have hr := timeL2_observable_integrable μ Q L
  have hgg := ((innerSL ℝ).flip z).integrable_comp hg
  simp only [L, μ, z, p, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, innerSL_apply_apply, planeGradientTensorOperator_apply]
      at hd hf hr hgg
  exact ⟨hd, hr, hf, hgg⟩

theorem nativeRawTest_rhs_integrable {a b : ℝ} (ν : ℝ)
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (ψ : PlaneHk Set.univ 1 E) :
    Integrable (fun s =>
      -inner ℝ (D s) (planeHkValueOperator 1 ψ) -
        ν * inner ℝ (planeHkValueOperator 0 (planeGradientTensor (Q s)))
          (planeHkValueOperator 0 (planeGradientTensor ψ)) -
        inner ℝ (F s) (planeHkValueOperator 0 (planeGradientTensor ψ)) +
        inner ℝ (g s) (planeHkValueOperator 1 ψ)) (volume.restrict (Set.Icc a b)) := by
  obtain ⟨hd, hr, hf, hgg⟩ := nativeRawTest_terms_integrable Q D F g hg ψ
  exact (((hd.neg.sub (hr.const_mul ν)).sub hf).add hgg).congr
    (by filter_upwards with s; rfl)

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! Native drift, diffusion, coupling and forcing form of the tested Galerkin equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedCurve_native_test_identity {K : ι → ℕ} {D : ℕ} {a b : ℝ}
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
    inner ℝ (u t i) z - inner ℝ (projectedInitial N f i) z = ∫ s in a..t.1,
      -inner ℝ (planeCoefficientOperator
        ((C.reindex (clampPoint a b hab)).drift i s)
        ((C.reindex (clampPoint a b hab)).drift_continuous i s)
        (C.drift_bound_nonneg i) ((C.reindex (clampPoint a b hab)).drift_le i s)
        (bandGradientOperator (E := h i) N (extendCurve hab u s i)))
        (hilbertProjection N z) -
      ν * inner ℝ (bandGradientOperator (E := h i) N (extendCurve hab u s i))
        (bandGradientOperator (E := h i) N z) -
      (∑ j : ι, ∑ d : admissibleOrders K D i j, inner ℝ
        (planeCoefficientOperator
          ((C.reindex (clampPoint a b hab)).coupling i j d s)
          ((C.reindex (clampPoint a b hab)).coupling_continuous i j d s)
          (C.coupling_bound_nonneg i j d)
          ((C.reindex (clampPoint a b hab)).coupling_le i j d s)
          (bandTensorOperator (E := h j) N (d.1 - 1) (extendCurve hab u s j)))
        (bandGradientOperator (E := h i) N z)) -
      inner ℝ (planeHkValueOperator (K i) (F i s))
        (bandGradientOperator (E := h i) N z) +
      inner ℝ (planeHkValueOperator (K i) (g i s)) (hilbertProjection N z) := by
  have he := projectedCurve_test_identity_of_integralEquation hab C hc N ν f F hF g hg u hu i t z
  rw [he, add_sub_cancel_left]
  apply intervalIntegral.integral_congr
  intro s _
  change inner ℝ (projectedOperator (C.reindex (clampPoint a b hab)) N ν s
    (extendCurve hab u s) i + projectedSource N F g s i) z = _
  rw [inner_add_left, projectedOperator_row_inner, projectedSource_inner]
  simp only [ProjectedCoefficients.reindex]
  ring

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Every term of the native time-tested equation is genuinely integrable. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance rawContinuousCarrierAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance rawContinuousCarrierTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

theorem nativeRawTestValue_continuousOn {a b : ℝ} (hab : a ≤ b) (ν : ℝ)
    (f : Lp E 2 (volume : Measure (Vec 2)))
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (ψ : PlaneHk Set.univ 1 E) :
    ContinuousOn (fun t => nativeRawTestValue ν f Q D F g t ψ) (Set.Icc a b) := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (nativeRawTest_rhs_integrable ν Q D F g hg ψ)
  have hc := AVenhance.Infra.ODE.continuousOn_intervalPrimitive hi
  rw [Set.uIcc_of_le hab] at hc
  exact continuousOn_const.add hc
end

/-! Expansion of the genuine native tested equation into its separately integrable terms. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance expansionCarrierAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance expansionCarrierTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

theorem nativeRawTestValue_expansion {a b t : ℝ} (ht : t ∈ Set.Icc a b) (ν : ℝ)
    (f : Lp E 2 (volume : Measure (Vec 2)))
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (ψ : PlaneHk Set.univ 1 E) :
    nativeRawTestValue ν f Q D F g t ψ = inner ℝ f (planeHkValueOperator 1 ψ) -
      (∫ s in a..t, inner ℝ (D s) (planeHkValueOperator 1 ψ)) -
      ν * (∫ s in a..t, inner ℝ (planeHkValueOperator 0 (planeGradientTensor (Q s)))
        (planeHkValueOperator 0 (planeGradientTensor ψ))) -
      (∫ s in a..t, inner ℝ (F s) (planeHkValueOperator 0 (planeGradientTensor ψ))) +
      (∫ s in a..t, inner ℝ (g s) (planeHkValueOperator 1 ψ)) := by
  obtain ⟨hd, hr, hf, hgg⟩ := nativeRawTest_terms_integrable Q D F g hg ψ
  have hs : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl ht.2
  have hi {q : ℝ → ℝ} (hq : Integrable q (volume.restrict (Set.Icc a b))) :
      IntervalIntegrable q volume a t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr (hq.mono_measure (Measure.restrict_mono hs le_rfl))
  have he := testedIntegral_expansion (ι := Empty) (δ := fun _ => Empty) (ν := ν)
    (fun s => inner ℝ (D s) (planeHkValueOperator 1 ψ))
    (fun s => inner ℝ (planeHkValueOperator 0 (planeGradientTensor (Q s)))
      (planeHkValueOperator 0 (planeGradientTensor ψ)))
    (fun s => inner ℝ (F s) (planeHkValueOperator 0 (planeGradientTensor ψ)))
    (fun s => inner ℝ (g s) (planeHkValueOperator 1 ψ))
    (fun i => nomatch i) (hi hd) (hi hr) (hi hf) (hi hgg) (fun i => nomatch i)
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at he
  rw [nativeRawTestValue, he]
  ring
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! Native drift, diffusion, coupling and forcing form of the tested Galerkin equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedCurve_expanded_test_identity {K : ι → ℕ} {D : ℕ} {a b : ℝ}
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
    inner ℝ (u t i) z - inner ℝ (projectedInitial N f i) z =
      -(∫ s in a..t.1, inner ℝ (planeCoefficientOperator
        ((C.reindex (clampPoint a b hab)).drift i s)
        ((C.reindex (clampPoint a b hab)).drift_continuous i s)
        (C.drift_bound_nonneg i) ((C.reindex (clampPoint a b hab)).drift_le i s)
        (bandGradientOperator (E := h i) N (extendCurve hab u s i)))
        (hilbertProjection N z)) -
      ν * (∫ s in a..t.1, inner ℝ (bandGradientOperator (E := h i) N (extendCurve hab u s i))
        (bandGradientOperator (E := h i) N z)) -
      (∑ j : ι, ∑ d : admissibleOrders K D i j, ∫ s in a..t.1, inner ℝ
        (planeCoefficientOperator
          ((C.reindex (clampPoint a b hab)).coupling i j d s)
          ((C.reindex (clampPoint a b hab)).coupling_continuous i j d s)
          (C.coupling_bound_nonneg i j d)
          ((C.reindex (clampPoint a b hab)).coupling_le i j d s)
          (bandTensorOperator (E := h j) N (d.1 - 1) (extendCurve hab u s j)))
        (bandGradientOperator (E := h i) N z)) -
      (∫ s in a..t.1, inner ℝ (planeHkValueOperator (K i) (F i s))
        (bandGradientOperator (E := h i) N z)) +
      ∫ s in a..t.1, inner ℝ (planeHkValueOperator (K i) (g i s)) (hilbertProjection N z) := by
  rw [projectedCurve_native_test_identity hab C hc N ν f F hF g hg u hu i t z]
  apply AVRegularity.CoupledEnergyPlane.Variational.testedIntegral_expansion
  · exact (driftTest_intervalIntegrable hab C hc N u i z).mono_set (by
      rw [Set.uIcc_of_le t.property.1, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc le_rfl t.property.2)
  · exact (diffusionTest_intervalIntegrable hab N u i z).mono_set (by
      rw [Set.uIcc_of_le t.property.1, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc le_rfl t.property.2)
  · exact (planeFluxTest_intervalIntegrable hab (F i) (hF i)
      (bandGradientOperator (E := h i) N z)).mono_set (by
      rw [Set.uIcc_of_le t.property.1, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc le_rfl t.property.2)
  · exact (planeHkTest_intervalIntegrable hab (g i) (hg i)
      (hilbertProjection N z)).mono_set (by
      rw [Set.uIcc_of_le t.property.1, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc le_rfl t.property.2)
  · intro j d
    exact (edgeTest_intervalIntegrable hab C hc N u i j d z).mono_set (by
      rw [Set.uIcc_of_le t.property.1, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc le_rfl t.property.2)

end AVRegularity.CoupledEnergyPlane
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Every term of the native time-tested equation is genuinely integrable. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance rawAllTimeCarrierAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance rawAllTimeCarrierTopAdd (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k E) :=
  inferInstance

theorem nativeRawTestValue_eq_continuousCarrier_of_ae {a b : ℝ} (hab : a ≤ b) (K : ℕ) (ν : ℝ)
    (f : PlaneHk Set.univ K E) (U : C(Set.Icc a b, PlaneHk Set.univ K E))
    (hinit : U ⟨a, le_rfl, hab⟩ = f)
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b)))
    (hvalue : (fun t => planeHkValueOperator (E := E) K (extendCurve hab U t))
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => planeHkValueOperator (E := E) 1 (Q t))
    (ψ : PlaneHk Set.univ 1 E)
    (heq : (fun t => inner ℝ (planeHkValueOperator (E := E) 1 (Q t))
      (planeHkValueOperator (E := E) 1 ψ)) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => nativeRawTestValue ν (planeHkValueOperator (E := E) K f) Q D F g t ψ)
    (t : Set.Icc a b) :
    inner ℝ (planeHkValueOperator (E := E) K (U t)) (planeHkValueOperator (E := E) 1 ψ) =
      nativeRawTestValue ν (planeHkValueOperator (E := E) K f) Q D F g t ψ := by
  let L : PlaneHk Set.univ K E →L[ℝ] ℝ :=
    ((innerSL ℝ).flip (planeHkValueOperator (E := E) 1 ψ)).comp (planeHkValueOperator (E := E) K)
  have hleft : ContinuousOn (fun s => L (extendCurve hab U s)) (Set.Icc a b) :=
    (L.continuous.comp (continuous_extendCurve hab U)).continuousOn
  have hae : (fun s => L (extendCurve hab U s)) =ᵐ[volume.restrict (Set.Icc a b)]
      fun s => nativeRawTestValue ν (planeHkValueOperator (E := E) K f) Q D F g s ψ := by
    filter_upwards [hvalue, heq] with s hv he
    change inner ℝ (planeHkValueOperator (E := E) K (extendCurve hab U s))
      (planeHkValueOperator (E := E) 1 ψ) = _
    exact (congrArg (fun z => inner ℝ z (planeHkValueOperator (E := E) 1 ψ)) hv).trans he
  have ha : L (extendCurve hab U a) =
      nativeRawTestValue ν (planeHkValueOperator (E := E) K f) Q D F g a ψ := by
    rw [extendCurve_eq_of_mem hab U (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩), hinit]
    change inner ℝ (planeHkValueOperator (E := E) K f) (planeHkValueOperator (E := E) 1 ψ) = _
    simp only [nativeRawTestValue, intervalIntegral.integral_same, add_zero]
  have hh := eqOn_Icc_of_ae_eq_and_initial hab _ _ hleft
    (nativeRawTestValue_continuousOn hab ν (planeHkValueOperator (E := E) K f) Q D F g hg ψ) hae ha
  have ht := hh t.property
  change L (extendCurve hab U t) = nativeRawTestValue ν (planeHkValueOperator (E := E) K f) Q D F g t ψ at ht
  rw [extendCurve_eq_of_mem hab U t.property] at ht
  exact ht

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! Genuine bounded-frequency native primitives for the entire coupled family. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {a b : ℝ} (hab : a ≤ b) (N : ℕ) (ν : ℝ)
  (f : ∀ i, Lp (h i) 2 (volume : Measure (Vec 2)))
  (Q : ∀ i, Lp (PlaneHk Set.univ 1 (h i)) 2 (volume.restrict (Set.Icc a b)))
  (D : ∀ i, Lp (Lp (h i) 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
  (F : ∀ i, Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
    2 (volume.restrict (Set.Icc a b)))
  (g : ∀ i, ℝ → Lp (h i) 2 (volume : Measure (Vec 2)))
  (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))

def nativeFamilyPrimitive : C(Set.Icc a b, ProjectedFamily h) :=
  finiteFamilyCurve (fun i => fixedBandPrimitive hab N ν (f i)
    ((planeHkValueOperator (E := h i) 1).compLpL 2 (volume.restrict (Set.Icc a b)) (Q i))
    (D i) (F i) (g i) (hg i))

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
def nativeFamilyRhs (t : ℝ) : ProjectedFamily h :=
  WithLp.toLp 2 (fun i => fixedBandRhs (E := h i) N ν
    ((planeHkValueOperator (E := h i) 1).compLpL 2 (volume.restrict (Set.Icc a b)) (Q i))
    (D i) (F i) (g i) t)

include hab hg in
theorem nativeFamilyRhs_intervalIntegrable :
    IntervalIntegrable (nativeFamilyRhs N ν Q D F g) volume a b := by
  exact finiteFamilyRhs_intervalIntegrable hab _ (fun i =>
    fixedBandRhs_intervalIntegrable (E := h i) hab N ν _ (D i) (F i) (g i) (hg i))

theorem nativeFamilyPrimitive_eq_integral (t : Set.Icc a b) :
    nativeFamilyPrimitive hab N ν f Q D F g hg t =
      WithLp.toLp 2 (fun i => hilbertProjection N (f i)) +
        ∫ s in a..t.val, nativeFamilyRhs N ν Q D F g s := by
  exact finiteFamilyCurve_eq_primitive_of_components hab _ _ _
    (fun i => fixedBandRhs_intervalIntegrable (E := h i) hab N ν _ (D i) (F i) (g i) (hg i))
    (fun _ _ => rfl) t

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The exact native tested equation is linear in its actual carriers and forcing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem nativeRawTestValue_sub_same_source {a b t : ℝ} (ht : t ∈ Set.Icc a b) (ν : ℝ)
    (f f' : Lp E 2 (volume : Measure (Vec 2)))
    (Q Q' : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D D' : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F F' : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (ψ : PlaneHk Set.univ 1 E) :
    nativeRawTestValue (E := E) (a := a) (b := b) ν (f - f') (Q - Q') (D - D') (F - F') (fun _ => 0) t ψ =
      nativeRawTestValue (E := E) (a := a) (b := b) ν f Q D F g t ψ - nativeRawTestValue (E := E) (a := a) (b := b) ν f' Q' D' F' g t ψ := by
  have hq := nativeGradientTest_sub (E := E) ht Q Q' ψ
  have hd := timeClassReadoutPairing_sub ht
    (ContinuousLinearMap.id ℝ (Lp E 2 (volume : Measure (Vec 2)))) D D'
    (planeHkValueOperator (E := E) 1 ψ)
  have hf := timeClassReadoutPairing_sub ht
    (ContinuousLinearMap.id ℝ (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))) F F'
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))
  simp only [ContinuousLinearMap.id_apply] at hd hf
  have hg0 : Integrable (fun _ : ℝ => (0 : Lp E 2 (volume : Measure (Vec 2))))
      (volume.restrict (Set.Icc a b)) := by simp
  have h0 := nativeRawTestValue_expansion (E := E) ht ν (f - f') (Q - Q') (D - D') (F - F') (fun _ => 0) hg0 ψ
  have h1 := nativeRawTestValue_expansion (E := E) ht ν f Q D F g hg ψ
  have h2 := nativeRawTestValue_expansion (E := E) ht ν f' Q' D' F' g hg ψ
  simp only [inner_zero_left, intervalIntegral.integral_zero, add_zero] at h0
  have hi : inner ℝ (f - f') (planeHkValueOperator (E := E) 1 ψ) =
      inner ℝ f (planeHkValueOperator (E := E) 1 ψ) - inner ℝ f' (planeHkValueOperator (E := E) 1 ψ) :=
    inner_sub_left _ _ _
  have hs := congrArg₂ (fun x y : ℝ => x - y)
    (congrArg₂ (fun x y : ℝ => x - ν * y) (congrArg₂ (fun x y : ℝ => x - y) hi hd) hq) hf
  have hr :
      (inner ℝ f (planeHkValueOperator (E := E) 1 ψ) - inner ℝ f' (planeHkValueOperator (E := E) 1 ψ)) -
        ((∫ s in a..t, inner ℝ (D s) (planeHkValueOperator (E := E) 1 ψ)) -
          ∫ s in a..t, inner ℝ (D' s) (planeHkValueOperator (E := E) 1 ψ)) -
        ν * ((∫ s in a..t, inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) (Q s)))
          (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) -
          ∫ s in a..t, inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) (Q' s)))
          (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) -
        ((∫ s in a..t, inner ℝ (F s) (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) -
          ∫ s in a..t, inner ℝ (F' s) (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) =
      (inner ℝ f (planeHkValueOperator (E := E) 1 ψ) -
        (∫ s in a..t, inner ℝ (D s) (planeHkValueOperator (E := E) 1 ψ)) -
        ν * (∫ s in a..t, inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) (Q s)))
          (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) -
        (∫ s in a..t, inner ℝ (F s) (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) +
        (∫ s in a..t, inner ℝ (g s) (planeHkValueOperator (E := E) 1 ψ))) -
      (inner ℝ f' (planeHkValueOperator (E := E) 1 ψ) -
        (∫ s in a..t, inner ℝ (D' s) (planeHkValueOperator (E := E) 1 ψ)) -
        ν * (∫ s in a..t, inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) (Q' s)))
          (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) -
        (∫ s in a..t, inner ℝ (F' s) (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))) +
        (∫ s in a..t, inner ℝ (g s) (planeHkValueOperator (E := E) 1 ψ))) := by ring
  exact h0.trans (hs.trans (hr.trans (congrArg₂ (fun x y : ℝ => x - y) h1.symm h2.symm)))

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.ODE
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! Genuine bounded-frequency native primitives for the entire coupled family. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {a b : ℝ} (hab : a ≤ b) (N : ℕ) (ν : ℝ)
  (f : ∀ i, Lp (h i) 2 (volume : Measure (Vec 2)))
  (Q : ∀ i, Lp (PlaneHk Set.univ 1 (h i)) 2 (volume.restrict (Set.Icc a b)))
  (D : ∀ i, Lp (Lp (h i) 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
  (F : ∀ i, Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
    2 (volume.restrict (Set.Icc a b)))
  (g : ∀ i, ℝ → Lp (h i) 2 (volume : Measure (Vec 2)))
  (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))

theorem nativeFamilyPrimitive_timeRegularity_of_rhs_ae
    (A : ℝ → ProjectedFamily h →L[ℝ] ProjectedFamily h) (S : ℝ → ProjectedFamily h)
    (hae : nativeFamilyRhs N ν Q D F g =ᵐ[volume.restrict (Set.Icc a b)]
      fun s => A s (extendCurve hab (nativeFamilyPrimitive hab N ν f Q D F g hg) s) + S s) :
    AbsolutelyContinuousOnInterval (extendCurve hab (nativeFamilyPrimitive hab N ν f Q D F g hg)) a b ∧
      (∀ᵐ t ∂volume, t ∈ Set.Icc a b → HasDerivAt
        (extendCurve hab (nativeFamilyPrimitive hab N ν f Q D F g hg))
        (A t (extendCurve hab (nativeFamilyPrimitive hab N ν f Q D F g hg) t) + S t) t) := by
  let q := nativeFamilyPrimitive hab N ν f Q D F g hg
  have hi := nativeFamilyRhs_intervalIntegrable (hab := hab) (N := N) (ν := ν)
    (Q := Q) (D := D) (F := F) (g := g) (hg := hg)
  have hint : IntervalIntegrable (linearRhs A S (extendCurve hab q)) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi).congr hae
  have hq : IsLinearIntegralSolution A S (WithLp.toLp 2 (fun i => hilbertProjection N (f i)))
      a b (extendCurve hab q) := by
    intro t ht
    rw [extendCurve_eq_of_mem hab q ht]
    change nativeFamilyPrimitive hab N ν f Q D F g hg ⟨t, ht⟩ = _
    rw [nativeFamilyPrimitive_eq_integral]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    have hs : Set.uIoc a t ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le ht.1]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)
    exact ae_restrict_of_ae_restrict_of_subset hs hae
  refine ⟨IsLinearIntegralSolution.absolutelyContinuousOnInterval hab hq hint, ?_⟩
  simpa only [linearRhs] using IsLinearIntegralSolution.ae_hasDerivAt hab hq hint

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The exact native tested equation is linear in its actual carriers and forcing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem nativeRawTestDifference_identity_of_same_source {a b t : ℝ} (ht : t ∈ Set.Icc a b) (ν : ℝ)
    (f : Lp E 2 (volume : Measure (Vec 2)))
    (Q Q' : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (D D' : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F F' : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (ψ : PlaneHk Set.univ 1 E)
    (u u' : Lp E 2 (volume : Measure (Vec 2)))
    (hu : inner ℝ u (planeHkValueOperator (E := E) 1 ψ) =
      nativeRawTestValue (E := E) ν f Q D F g t ψ)
    (hu' : inner ℝ u' (planeHkValueOperator (E := E) 1 ψ) =
      nativeRawTestValue (E := E) ν f Q' D' F' g t ψ) :
    inner ℝ (u - u') (planeHkValueOperator (E := E) 1 ψ) =
      nativeRawTestValue (E := E) ν 0 (Q - Q') (D - D') (F - F') (fun _ => 0) t ψ := by
  have hs := nativeRawTestValue_sub_same_source (E := E) ht ν f f Q Q' D D' F F' g hg ψ
  have hi : inner ℝ (u - u') (planeHkValueOperator (E := E) 1 ψ) =
      inner ℝ u (planeHkValueOperator (E := E) 1 ψ) - inner ℝ u' (planeHkValueOperator (E := E) 1 ψ) :=
    inner_sub_left _ _ _
  have he := congrArg₂ (fun x y : ℝ => x - y) hu hu'
  have h0 : nativeRawTestValue (E := E) ν 0 (Q - Q') (D - D') (F - F') (fun _ => 0) t ψ =
      nativeRawTestValue (E := E) ν f Q D F g t ψ - nativeRawTestValue (E := E) ν f Q' D' F' g t ψ := by
    simpa only [sub_self] using hs
  exact hi.trans (he.trans h0.symm)

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Actual projected derivative tensors pass through variable-coefficient weak spacetime limits. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G]

theorem fixedReadout_coefficient_integral_weak_limit {a b s t : ℝ}
    (hab : a ≤ b) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (K : ι → ℕ)
    (LH : PlaneHighHilbert (h := h) K →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (C : ℝ → Vec 2 → E →L[ℝ] G)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ q ∈ Set.Icc a b, Continuous (C q))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q ∈ Set.Icc a b, ∀ x, ‖C q x‖ ≤ M)
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h)) (φ : ℕ → ℕ)
    (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (z : ℕ → Lp G 2 (volume : Measure (Vec 2)))
    (w : Lp G 2 (volume : Measure (Vec 2))) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => ∫ q in s..t, ∫ x,
      inner ℝ (C q x (LH (higherBandJetOperator (h := h) (φ n) K (extendCurve hab (u (φ n)) q)) x)) (z n x)) atTop
      (𝓝 (∫ q in s..t, ∫ x, inner ℝ
        (C q x ((LH.compLpL 2
          (volume.restrict (Set.Icc a b)) W) q x)) (w x))) := by
  let L := LH.compLpL 2 (volume.restrict (Set.Icc a b))
  let U := fun n => higherBandBochner (φ n) K a b hab (u (φ n))
  have hbound (n : ℕ) : ‖L (U n)‖ ≤ ‖L‖ * R :=
    (L.le_opNorm (U n)).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg L))
  have hweak : ∀ ell : Lp (Lp (E) 2
      (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)) →L[ℝ] ℝ, Tendsto (fun n => ell (L (U n))) atTop (𝓝 (ell (L W))) :=
    fun ell => hw (ell.comp L)
  have he (n : ℕ) : (∫ q in s..t, ∫ x, inner ℝ (C q x (L (U n) q x)) (z n x)) =
      ∫ q in s..t, ∫ x, inner ℝ (C q x
        (LH (higherBandJetOperator (h := h) (φ n) K (extendCurve hab (u (φ n)) q)) x)) (z n x) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : Set.uIoc s t ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le hst]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)
    have hcoe : U n =ᵐ[volume.restrict (Set.Icc a b)]
        fun q => higherBandJetOperator (h := h) (φ n) K (extendCurve hab (u (φ n)) q) :=
      (higherBandJet_memLp (φ n) K a b (continuous_extendCurve hab (u (φ n)))).coeFn_toLp
    have hm : L (U n) =ᵐ[volume.restrict (Set.Icc a b)]
        fun q => LH (higherBandJetOperator (h := h) (φ n) K (extendCurve hab (u (φ n)) q)) := by
      filter_upwards [ContinuousLinearMap.coeFn_compLpL LH (U n), hcoe] with q hq huq
      exact hq.trans (congrArg LH huq)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hm] with q hq
    rw [hq]
  simpa only [he, L] using intervalCoefficient_integral_weak_limit_moving_test hs ht hst C
    hC hc M hM hb (fun n => L (U n)) (L W) (‖L‖ * R) hbound hweak z w hz

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The native plane fields recover the literal spatial weak identity through their L² representatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def nativeRawSpatialRhs (ν : ℝ) (D : Lp E 2 (volume : Measure (Vec 2)))
    (G F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
    (g : Lp E 2 (volume : Measure (Vec 2))) (ψ : PlaneHk Set.univ 1 E) (x : Vec 2) : ℝ :=
  -inner ℝ (D x) (planeHkValueOperator (E := E) 1 ψ x) -
    ν * inner ℝ (G x)
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ) x) -
    inner ℝ (F x)
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ) x) +
    inner ℝ (g x) (planeHkValueOperator (E := E) 1 ψ x)

theorem nativeRawSpatialRhs_integrable_and_integral (ν : ℝ)
    (D : Lp E 2 (volume : Measure (Vec 2)))
    (G F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
    (g : Lp E 2 (volume : Measure (Vec 2))) (ψ : PlaneHk Set.univ 1 E) :
    Integrable (nativeRawSpatialRhs ν D G F g ψ) volume ∧
      (∫ x, nativeRawSpatialRhs ν D G F g ψ x) =
        -inner ℝ D (planeHkValueOperator (E := E) 1 ψ) -
          ν * inner ℝ G
            (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ)) -
          inner ℝ F
            (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ)) +
          inner ℝ g (planeHkValueOperator (E := E) 1 ψ) := by
  have hd := L2.integrable_inner (𝕜 := ℝ) D (planeHkValueOperator (E := E) 1 ψ)
  have hr := L2.integrable_inner (𝕜 := ℝ) G
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))
  have hf := L2.integrable_inner (𝕜 := ℝ) F
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) 0 (planeGradientTensor (E := E) ψ))
  have hg := L2.integrable_inner (𝕜 := ℝ) g (planeHkValueOperator (E := E) 1 ψ)
  refine ⟨((hd.neg.sub (hr.const_mul ν)).sub hf).add hg, ?_⟩
  have ha := integral_add ((hd.neg.sub (hr.const_mul ν)).sub hf) hg
  have hs := integral_sub (hd.neg.sub (hr.const_mul ν)) hf
  have hdif := integral_sub hd.neg (hr.const_mul ν)
  simp only [Pi.sub_apply, Pi.neg_apply] at ha hs hdif
  unfold nativeRawSpatialRhs
  rw [ha, hs, hdif, integral_neg, integral_const_mul]
  simp only [L2.inner_def]

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Actual projected derivative tensors pass through variable-coefficient weak spacetime limits. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G]

theorem bandTensor_coefficient_integral_weak_limit {a b s t : ℝ}
    (hab : a ≤ b) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (K : ι → ℕ) (i : ι) (r : ℕ) (hr : r ≤ K i + 1)
    (C : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => h i) →L[ℝ] G)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ q ∈ Set.Icc a b, Continuous (C q))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q ∈ Set.Icc a b, ∀ x, ‖C q x‖ ≤ M)
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h)) (φ : ℕ → ℕ)
    (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (z : ℕ → Lp G 2 (volume : Measure (Vec 2)))
    (w : Lp G 2 (volume : Measure (Vec 2))) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => ∫ q in s..t, ∫ x,
      inner ℝ (C q x (bandTensorOperator (E := h i) (φ n) r
        (extendCurve hab (u (φ n)) q i) x)) (z n x)) atTop
      (𝓝 (∫ q in s..t, ∫ x, inner ℝ
        (C q x (((highTensorReadout (h := h) K i r hr).compLpL 2
          (volume.restrict (Set.Icc a b)) W) q x)) (w x))) := by
  let L := (highTensorReadout (h := h) K i r hr).compLpL 2 (volume.restrict (Set.Icc a b))
  let U := fun n => higherBandBochner (φ n) K a b hab (u (φ n))
  have hbound (n : ℕ) : ‖L (U n)‖ ≤ ‖L‖ * R :=
    (L.le_opNorm (U n)).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg L))
  have hweak : ∀ ell : Lp (Lp (PiLp 2 (fun _ : DerivativeWord2 r => h i)) 2
      (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)) →L[ℝ] ℝ, Tendsto (fun n => ell (L (U n))) atTop (𝓝 (ell (L W))) :=
    fun ell => hw (ell.comp L)
  have he (n : ℕ) : (∫ q in s..t, ∫ x, inner ℝ (C q x (L (U n) q x)) (z n x)) =
      ∫ q in s..t, ∫ x, inner ℝ (C q x
        (bandTensorOperator (E := h i) (φ n) r (extendCurve hab (u (φ n)) q i) x)) (z n x) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : Set.uIoc s t ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le hst]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (highTensorReadout_band_time_ae (φ n) K a b hab (u (φ n)) i r hr)] with q hq
    rw [show L (U n) q = bandTensorOperator (E := h i) (φ n) r
      (extendCurve hab (u (φ n)) q i) from hq]
  simpa only [he, L] using intervalCoefficient_integral_weak_limit_moving_test hs ht hst C
    hC hc M hM hb (fun n => L (U n)) (L W) (‖L‖ * R) hbound hweak z w hz

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Genuine L² native drift and coupling flux fields of the common weak jet class. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def limitDriftField {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (i : ι) : PlaneHighTime (h := h) K a b →L[ℝ]
      Lp (Lp (h i) 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)) :=
  (coefficientTimeCLM (volume.restrict (Set.Icc a b))
    ((C.reindex (clampPoint a b hab)).drift i)
    ((hc.reindex (clampPoint a b hab) (continuous_clampPoint a b hab).measurable).drift i)
    ((C.reindex (clampPoint a b hab)).drift_continuous i)
    (C.drift_bound i) (C.drift_bound_nonneg i)
    ((C.reindex (clampPoint a b hab)).drift_le i)).comp
    ((highGradientReadout (h := h) K i).compLpL 2 (volume.restrict (Set.Icc a b)))

def limitEdgeField {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (i j : ι) (d : admissibleOrders K D i j) : PlaneHighTime (h := h) K a b →L[ℝ]
      Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
        2 (volume.restrict (Set.Icc a b)) :=
  (coefficientTimeCLM (volume.restrict (Set.Icc a b))
    ((C.reindex (clampPoint a b hab)).coupling i j d)
    ((hc.reindex (clampPoint a b hab) (continuous_clampPoint a b hab).measurable).coupling i j d)
    ((C.reindex (clampPoint a b hab)).coupling_continuous i j d)
    (C.coupling_bound i j d) (C.coupling_bound_nonneg i j d)
    ((C.reindex (clampPoint a b hab)).coupling_le i j d)).comp
    ((highTensorReadout (h := h) K j (d.1 - 1)
      (by have hh := admissibleOrders_reserve K D i j d; omega)).compLpL 2
        (volume.restrict (Set.Icc a b)))
end

/-! The constructed limiting drift and edge classes retain their literal coefficient pairings. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem limitDriftField_test_integral {K : ι → ℕ} {D : ℕ} {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W : PlaneHighTime (h := h) K a b) (i : ι)
    (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    (∫ s in a..t, inner ℝ (limitDriftField hab C hc i W s) z) =
      ∫ s in a..t, ∫ x, inner ℝ
        (C.drift i (clampPoint a b hab s) x
          (((highGradientReadout (h := h) K i).compLpL 2
            (volume.restrict (Set.Icc a b)) W) s x)) (z x) := by
  exact coefficientTimeCLM_fixed_test_integral ht
    ((C.reindex (clampPoint a b hab)).drift i)
    ((hc.reindex (clampPoint a b hab) (continuous_clampPoint a b hab).measurable).drift i)
    ((C.reindex (clampPoint a b hab)).drift_continuous i)
    (C.drift_bound i) (C.drift_bound_nonneg i)
    ((C.reindex (clampPoint a b hab)).drift_le i)
    ((highGradientReadout (h := h) K i).compLpL 2 (volume.restrict (Set.Icc a b)) W) z

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem limitEdgeField_test_integral {K : ι → ℕ} {D : ℕ} {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W : PlaneHighTime (h := h) K a b) (i j : ι) (d : admissibleOrders K D i j)
    (z : Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2))) :
    (∫ s in a..t, inner ℝ (limitEdgeField hab C hc i j d W s) z) =
      ∫ s in a..t, ∫ x, inner ℝ
        (C.coupling i j d (clampPoint a b hab s) x
          (((highTensorReadout (h := h) K j (d.1 - 1)
            (by have hh := admissibleOrders_reserve K D i j d; omega)).compLpL 2
              (volume.restrict (Set.Icc a b)) W) s x)) (z x) := by
  exact coefficientTimeCLM_fixed_test_integral ht
    ((C.reindex (clampPoint a b hab)).coupling i j d)
    ((hc.reindex (clampPoint a b hab) (continuous_clampPoint a b hab).measurable).coupling i j d)
    ((C.reindex (clampPoint a b hab)).coupling_continuous i j d)
    (C.coupling_bound i j d) (C.coupling_bound_nonneg i j d)
    ((C.reindex (clampPoint a b hab)).coupling_le i j d)
    ((highTensorReadout (h := h) K j (d.1 - 1)
      (by have hh := admissibleOrders_reserve K D i j d; omega)).compLpL 2
        (volume.restrict (Set.Icc a b)) W) z
end

end AVRegularity.CoupledEnergyPlane
end
end
end
