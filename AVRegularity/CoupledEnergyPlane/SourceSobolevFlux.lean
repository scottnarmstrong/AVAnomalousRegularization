-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergyPlane.Fourier.LaplacianProjection
public import AVRegularity.CoupledEnergyPlane.Variational.UniformEvolution

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Values of the native drift and flux time classes are literal spatial multipliers. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem limitDriftField_ae {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W : PlaneHighTime (h := h) K a b) (i : ι) :
    limitDriftField hab C hc i W =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      planeCoefficientOperator (C.drift i (clampPoint a b hab t))
        (C.drift_continuous i _) (C.drift_bound_nonneg i) (C.drift_le i _)
        (highGradientReadout (h := h) K i (W t)) := by
  have hp := coefficientTimeCLM_ae (volume.restrict (Set.Icc a b))
    ((C.reindex (clampPoint a b hab)).drift i)
    ((hc.reindex (clampPoint a b hab) (continuous_clampPoint a b hab).measurable).drift i)
    ((C.reindex (clampPoint a b hab)).drift_continuous i)
    (C.drift_bound i) (C.drift_bound_nonneg i)
    ((C.reindex (clampPoint a b hab)).drift_le i)
    ((highGradientReadout (h := h) K i).compLpL 2 (volume.restrict (Set.Icc a b)) W)
  refine hp.trans ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (highGradientReadout (h := h) K i) W]
    with t ht
  rw [ht]
  rfl

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem limitEdgeField_ae {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W : PlaneHighTime (h := h) K a b) (i j : ι) (d : admissibleOrders K D i j) :
    limitEdgeField hab C hc i j d W =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      planeCoefficientOperator (C.coupling i j d (clampPoint a b hab t))
        (C.coupling_continuous i j d _) (C.coupling_bound_nonneg i j d)
        (C.coupling_le i j d _)
        (highTensorReadout (h := h) K j (d.1 - 1)
          (by have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d; omega) (W t)) := by
  let T := highTensorReadout (h := h) K j (d.1 - 1)
    (show d.1 - 1 ≤ K j + 1 by have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d; omega)
  have hp := coefficientTimeCLM_ae (volume.restrict (Set.Icc a b))
    ((C.reindex (clampPoint a b hab)).coupling i j d)
    ((hc.reindex (clampPoint a b hab) (continuous_clampPoint a b hab).measurable).coupling i j d)
    ((C.reindex (clampPoint a b hab)).coupling_continuous i j d)
    (C.coupling_bound i j d) (C.coupling_bound_nonneg i j d)
    ((C.reindex (clampPoint a b hab)).coupling_le i j d)
    (T.compLpL 2 (volume.restrict (Set.Icc a b)) W)
  refine hp.trans ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL T W] with t ht
  rw [ht]
  rfl
end

/-! Literal gradient test integrals of the reconstructed weak H¹ time carrier. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakGradientPairAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakGradientPairTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem weakH1Carrier_gradient_test_integral {K : ι → ℕ} {a b t : ℝ}
    (ht : t ∈ Set.Icc a b) (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) (i : ι)
    (z : Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2))) :
    (∫ s in a..t, inner ℝ (planeHkValueOperator 0
      (planeGradientTensor (weakH1CarrierTimeCLM K a b i W s))) z) =
      ∫ s in a..t, ∫ x, inner ℝ
        (((highGradientReadout (h := h) K i).compLpL 2
          (volume.restrict (Set.Icc a b)) W) s x) (z x) := by
  apply intervalIntegral.integral_congr_ae_restrict
  have hs : Set.uIoc a t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le ht.1]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs
      (weakH1CarrierTimeCLM_gradient_ae K a b i W hW),
    ae_restrict_of_ae_restrict_of_subset hs
      (ContinuousLinearMap.coeFn_compLpL (highGradientReadout (h := h) K i) W)] with s hq hp
  rw [hq, ← hp]
  exact L2.inner_def _ _
end

/-! Assemble the actual finite coupling flux and external forcing as one time L² field. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def limitFluxField {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W : PlaneHighTime (h := h) K a b) (i : ι)
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b))) :
    Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)) :=
  (∑ j, ∑ d : admissibleOrders K D i j, limitEdgeField hab C hc i j d W) + F

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem limitFluxField_test_integral {K : ι → ℕ} {D : ℕ} {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W : PlaneHighTime (h := h) K a b) (i : ι)
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (z : Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2))) :
    (∫ s in a..t, inner ℝ (limitFluxField hab C hc W i F s) z) =
      (∑ j, ∑ d : admissibleOrders K D i j, ∫ s in a..t, ∫ x, inner ℝ
        (C.coupling i j d (clampPoint a b hab s) x
          (((highTensorReadout (h := h) K j (d.1 - 1)
            (by have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d; omega)).compLpL 2
              (volume.restrict (Set.Icc a b)) W) s x)) (z x)) +
      ∫ s in a..t, inner ℝ (F s) z := by
  rw [limitFluxField, timeClassPairing_doubleSum_add ht]
  simp_rw [limitEdgeField_test_integral hab ht C hc W]
end

/-! The full Sobolev gradient class has exactly the native weak L² value readout. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem weakGradientTime_value_ae (K : ι → ℕ) (a b : ℝ)
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) (i : ι) :
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
      (volume.restrict (Set.Icc a b)) (weakGradientTimeCLM K a b i W)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => highGradientReadout (h := h) K i (W t) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i))
      (weakGradientTimeCLM K a b i W),
    weakGradientTimeCLM_ae K a b i W, weakHighCarrier_jet_ae K a b W hW i] with t hv hg hj
  rw [hv, hg, planeGradientTensor_value_formula, hj]
  rfl
end

/-! Assemble the actual finite coupling flux and external forcing as one time L² field. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem limitFluxField_sub_same_forcing {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W W' : PlaneHighTime (h := h) K a b) (i : ι)
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b))) :
    limitFluxField hab C hc (W - W') i 0 =
      limitFluxField hab C hc W i F - limitFluxField hab C hc W' i F := by
  have hs (j : ι) (d : admissibleOrders K D i j) :
      limitEdgeField hab C hc i j d (W - W') =
        limitEdgeField hab C hc i j d W - limitEdgeField hab C hc i j d W' :=
    (limitEdgeField hab C hc i j d).toLinearMap.map_sub W W'
  simp only [limitFluxField, hs, Finset.sum_sub_distrib, add_zero]
  abel
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! The actual plane diffusion gradient pairing passes through the common weak subsequence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem diffusion_projected_test_weak_limit {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (K : ι → ℕ) (i : ι)
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W))) (ψ : PlaneHk Set.univ 1 (h i)) :
    Tendsto (fun n => ∫ q in a..t, ∫ x, inner ℝ
      (bandGradientOperator (E := h i) (φ n) (extendCurve hab (u (φ n)) q i) x)
      (bandGradientOperator (E := h i) (φ n) (planeHkValueOperator 1 ψ) x)) atTop
      (𝓝 (∫ q in a..t, ∫ x, inner ℝ
        (((highGradientReadout (h := h) K i).compLpL 2
          (volume.restrict (Set.Icc a b)) W) q x)
        (planeHkValueOperator 0 (planeGradientTensor ψ) x))) := by
  let C := fun (_q : ℝ) (_x : Vec 2) =>
    ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin 2 => h i))
  have hz := (tendsto_bandGradient_planeH1_value ψ).comp hφ.tendsto_atTop
  have he := fixedReadout_coefficient_integral_weak_limit hab
    (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩) ht ht.1 K (highGradientReadout (h := h) K i)
    C measurable_const (fun _ _ => continuous_const) 1 (by norm_num)
    (fun _ _ _ => ContinuousLinearMap.norm_id_le)
    u φ W R hu hw
    (fun n => bandGradientOperator (E := h i) (φ n) (planeHkValueOperator 1 ψ))
    (planeHkValueOperator 0 (planeGradientTensor ψ)) hz
  simpa only [C, ContinuousLinearMap.id_apply, highGradientReadout_band] using he

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! All three actual native limiting fields are linear in the common higher carrier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem nativeDifferenceFields {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W W' : PlaneHighTime (h := h) K a b) (i : ι)
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b))) :
    weakH1CarrierTimeCLM (h := h) K a b i (W - W') =
      weakH1CarrierTimeCLM (h := h) K a b i W - weakH1CarrierTimeCLM (h := h) K a b i W' ∧
    limitDriftField (h := h) hab C hc i (W - W') =
      limitDriftField (h := h) hab C hc i W - limitDriftField (h := h) hab C hc i W' ∧
    limitFluxField (h := h) hab C hc (W - W') i 0 =
      limitFluxField (h := h) hab C hc W i F - limitFluxField (h := h) hab C hc W' i F := by
  refine ⟨?_, ?_, ?_⟩
  · exact (weakH1CarrierTimeCLM (h := h) K a b i).toLinearMap.map_sub W W'
  · exact (limitDriftField (h := h) hab C hc i).toLinearMap.map_sub W W'
  · exact limitFluxField_sub_same_forcing (h := h) hab C hc W W' i F

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! The actual plane transport integral passes through the common Galerkin weak subsequence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem drift_projected_test_weak_limit {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (K : ι → ℕ) (i : ι) (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ q ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v q))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ q ∈ Set.Icc a b, ∀ x, ‖v q x‖ ≤ V)
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => ∫ q in a..t, ∫ x, inner ℝ
      (driftFiberCoefficient (E := h i) (v q) x
        (bandGradientOperator (E := h i) (φ n) (extendCurve hab (u (φ n)) q i) x))
      (hilbertProjection (φ n) z x)) atTop
      (𝓝 (∫ q in a..t, ∫ x, inner ℝ
        (driftFiberCoefficient (E := h i) (v q) x
          (((highGradientReadout (h := h) K i).compLpL 2
            (volume.restrict (Set.Icc a b)) W) q x)) (z x))) := by
  have hc : Measurable (fun p : Set.Icc a b × Vec 2 =>
      driftFiberCoefficient (E := h i) (v p.1) p.2) :=
    driftFiberCoefficient_measurable (E := h i) (fun q : Set.Icc a b => v q) hvm
  have hz := (tendsto_hilbertProjection z).comp hφ.tendsto_atTop
  have he := fixedReadout_coefficient_integral_weak_limit hab
    (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩) ht ht.1 K (highGradientReadout (h := h) K i)
    (fun q => driftFiberCoefficient (E := h i) (v q)) hc
    (fun q hq => (driftFiberCoefficient_contDiff (E := h i) (v q) (hv q hq)).continuous)
    (2 * V) (mul_nonneg (by norm_num) hV)
    (fun q hq x => (driftFiberCoefficient_norm_le (E := h i) (v q) x).trans
      (mul_le_mul_of_nonneg_left (hbv q hq x) (by norm_num)))
    u φ W R hu hw (fun n => hilbertProjection (φ n) z) z hz
  simpa only [highGradientReadout_band] using he
end

/-! The actual plane transport integral passes through the common Galerkin weak subsequence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem drift_clampedOperator_test_weak_limit {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (K : ι → ℕ) (i : ι) (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ q ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v q))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ q ∈ Set.Icc a b, ∀ x, ‖v q x‖ ≤ V)
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (z : Lp (h i) 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => ∫ q in a..t, inner ℝ
      (planeCoefficientOperator
        (driftFiberCoefficient (E := h i) (v (clampPoint a b hab q)))
        ((driftFiberCoefficient_contDiff (E := h i)
          (v (clampPoint a b hab q)) (hv _ (clampPoint a b hab q).property)).continuous)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hV)
        (fun x => (driftFiberCoefficient_norm_le (E := h i)
          (v (clampPoint a b hab q)) x).trans
          (mul_le_mul_of_nonneg_left (hbv _ (clampPoint a b hab q).property x)
            (by norm_num)))
        (bandGradientOperator (E := h i) (φ n) (extendCurve hab (u (φ n)) q i)))
      (hilbertProjection (φ n) z)) atTop
      (𝓝 (∫ q in a..t, ∫ x, inner ℝ
        (driftFiberCoefficient (E := h i) (v q) x
          (((highGradientReadout (h := h) K i).compLpL 2
            (volume.restrict (Set.Icc a b)) W) q x)) (z x))) := by
  have he := drift_projected_test_weak_limit hab ht K i v hv hvm V hV hbv u φ hφ W R hu hw z
  have hi (n : ℕ) := coefficient_clamped_intervalPairing hab ht
    (fun q => driftFiberCoefficient (E := h i) (v q))
    (fun q hq => (driftFiberCoefficient_contDiff (E := h i) (v q) (hv q hq)).continuous)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hV)
    (fun q hq x => (driftFiberCoefficient_norm_le (E := h i) (v q) x).trans
      (mul_le_mul_of_nonneg_left (hbv q hq x) (by norm_num)))
    (fun q => bandGradientOperator (E := h i) (φ n) (extendCurve hab (u (φ n)) q i))
    (hilbertProjection (φ n) z)
  simp_rw [hi]
  exact he
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! A verified Sobolev source identity lifts a native raw primitive to the Sobolev source primitive. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance sourceLiftAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance sourceLiftTopAdd (K : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ K E) := inferInstance

theorem fixedBandSobolevPrimitive_eq_sourcePrimitive_of_rhs {a b : ℝ} (hab : a ≤ b)
    (N K : ℕ) (ν : ℝ) (f : PlaneHk Set.univ K E)
    (V D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b)))
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (H : ℝ → PlaneHk Set.univ K E)
    (hH : Integrable H (volume.restrict (Set.Icc a b)))
    (hrhs : (fun s => hilbertBandHkOperator N K (fixedBandRhs N ν V D F g s))
      =ᵐ[volume.restrict (Set.Icc a b)] planeBandSobolevRhs N K S H)
    (t : Set.Icc a b) :
    hilbertBandHkOperator N K
      (fixedBandPrimitive hab N ν (planeHkValueOperator K f) V D F g hg t) =
      planeBandSobolevPrimitive hab N K f S hS H hH t := by
  let P := hilbertBandHkOperator (E := E) N K
  have hs : Set.uIcc a t.1 ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le t.property.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl t.property.2
  have hi := (fixedBandRhs_intervalIntegrable hab N ν V D F g hg).mono_set hs
  change P (hilbertProjection N (planeHkValueOperator K f) +
    ∫ s in a..t.1, fixedBandRhs N ν V D F g s) =
      planeHkCutoff N K f + ∫ s in a..t.1, planeBandSobolevRhs N K S H s
  rw [map_add, ← P.intervalIntegral_comp_comm hi]
  have hf : P (hilbertProjection N (planeHkValueOperator K f)) = planeHkCutoff N K f :=
    hilbertBandHk_projection N K (planeHkValueOperator K f)
  rw [hf]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  have hs' : Set.uIoc a t.1 ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le t.property.1]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl t.property.2)
  exact ae_restrict_of_ae_restrict_of_subset hs' hrhs

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Every literal admissible plane coupling flux passes through the Galerkin weak subsequence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem coupling_projected_test_weak_limit {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (i j : ι)
    (d : admissibleOrders K D i j)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hAc : ∀ q ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A q))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W))) (ψ : PlaneHk Set.univ 1 (h i)) :
    Tendsto (fun n => ∫ q in a..t, ∫ x, inner ℝ
      (A q x (bandTensorOperator (E := h j) (φ n) (d.1 - 1)
        (extendCurve hab (u (φ n)) q j) x))
      (bandGradientOperator (E := h i) (φ n) (planeHkValueOperator 1 ψ) x)) atTop
      (𝓝 (∫ q in a..t, ∫ x, inner ℝ
        (A q x (((highTensorReadout (h := h) K j (d.1 - 1)
          (by have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d; omega)).compLpL 2
            (volume.restrict (Set.Icc a b)) W) q x))
        (planeHkValueOperator 0 (planeGradientTensor ψ) x))) := by
  have hr : d.1 - 1 ≤ K j + 1 := by
    have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d
    omega
  have hz := (tendsto_bandGradient_planeH1_value ψ).comp hφ.tendsto_atTop
  exact bandTensor_coefficient_integral_weak_limit hab
    (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩) ht ht.1 K j (d.1 - 1) hr A hAm
    (fun q hq => (hAc q hq).continuous) (coefficientSeminorm ρ (K i) a b A).toReal
    ENNReal.toReal_nonneg (fun q hq x => sourceCoefficient_norm_le ρ hρ (K i) a b A hA q hq x)
    u φ W R hu hw (fun n => bandGradientOperator (E := h i) (φ n) (planeHkValueOperator 1 ψ))
    (planeHkValueOperator 0 (planeGradientTensor ψ)) hz

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Native drift, diffusion, and flux fields give the literal Sobolev value/divergence source. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance rhsSourceIdentityAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance rhsSourceIdentityTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K E) := inferInstance

theorem nativeBandRhs_eq_sobolevSources (N K : ℕ) (ν : ℝ)
    (q : PlaneHk Set.univ 1 E) (T g : PlaneHk Set.univ K E)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
    (hS : planeHkValueOperator K S =
      ν • planeHkValueOperator 0 (planeGradientTensor q) + F) :
    -hilbertProjection N (planeHkValueOperator K T) +
      ν • bandLaplacianOperator N (planeHkValueOperator 1 q) +
      bandDivergenceOperator (E := E) N F + hilbertProjection N (planeHkValueOperator K g) =
      bandDivergenceOperator (E := E) N (planeHkValueOperator K S) +
        hilbertProjection N (planeHkValueOperator K (-T + g)) := by
  rw [hS, map_add, map_smul, ← bandLaplacian_planeH1_eq_divergence]
  rw [map_add, map_neg, map_add, map_neg]
  abel

theorem nativeBandRhs_lift_eq_sobolevSources (N K : ℕ) (ν : ℝ)
    (q : PlaneHk Set.univ 1 E) (T g : PlaneHk Set.univ K E)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
    (hS : planeHkValueOperator K S =
      ν • planeHkValueOperator 0 (planeGradientTensor q) + F) :
    hilbertBandHkOperator N K
      (-hilbertProjection N (planeHkValueOperator K T) +
        ν • bandLaplacianOperator N (planeHkValueOperator 1 q) +
        bandDivergenceOperator (E := E) N F + hilbertProjection N (planeHkValueOperator K g)) =
      planeBandDivergenceCLM N K S + planeHkCutoff N K (-T + g) := by
  rw [nativeBandRhs_eq_sobolevSources N K ν q T g S F hS, map_add]
  have hp : hilbertBandHkOperator N K
      (hilbertProjection N (planeHkValueOperator K (-T + g))) =
      planeHkCutoff N K (-T + g) := hilbertBandHk_projection N K _
  rw [hp]
  rfl

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Every literal admissible plane coupling flux passes through the Galerkin weak subsequence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem coupling_clampedOperator_test_weak_limit {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (i j : ι)
    (d : admissibleOrders K D i j)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hAc : ∀ q ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A q))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W))) (ψ : PlaneHk Set.univ 1 (h i)) :
    Tendsto (fun n => ∫ q in a..t, inner ℝ
      (planeCoefficientOperator (A (clampPoint a b hab q))
        ((hAc _ (clampPoint a b hab q).property).continuous)
        (ENNReal.toReal_nonneg : 0 ≤ (coefficientSeminorm ρ (K i) a b A).toReal)
        (fun x => sourceCoefficient_norm_le ρ hρ (K i) a b A hA
          _ (clampPoint a b hab q).property x)
        (bandTensorOperator (E := h j) (φ n) (d.1 - 1)
          (extendCurve hab (u (φ n)) q j)))
      (bandGradientOperator (E := h i) (φ n) (planeHkValueOperator 1 ψ))) atTop
      (𝓝 (∫ q in a..t, ∫ x, inner ℝ
        (A q x (((highTensorReadout (h := h) K j (d.1 - 1)
          (by have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d; omega)).compLpL 2
            (volume.restrict (Set.Icc a b)) W) q x))
        (planeHkValueOperator 0 (planeGradientTensor ψ) x))) := by
  have he := coupling_projected_test_weak_limit hab ht ρ hρ K D i j d A hA hAm hAc
    u φ hφ W R hu hw ψ
  have hi (n : ℕ) := coefficient_clamped_intervalPairing hab ht A
    (fun q hq => (hAc q hq).continuous)
    (ENNReal.toReal_nonneg : 0 ≤ (coefficientSeminorm ρ (K i) a b A).toReal)
    (fun q hq x => sourceCoefficient_norm_le ρ hρ (K i) a b A hA q hq x)
    (fun q => bandTensorOperator (E := h j) (φ n) (d.1 - 1)
      (extendCurve hab (u (φ n)) q j))
    (bandGradientOperator (E := h i) (φ n) (planeHkValueOperator 1 ψ))
  simp_rw [hi]
  exact he

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The verified native spacetime field identities lift the frequency RHS almost everywhere. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance timeRhsSourceAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance timeRhsSourceTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K E) := inferInstance

theorem fixedBandSobolevRhs_ae_eq_sourceRhs_of_flux_value {a b : ℝ}
    (N K : ℕ) (ν : ℝ)
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (T : Lp (PlaneHk Set.univ K E) 2 (volume.restrict (Set.Icc a b)))
    (S : Lp (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) 2
      (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) 2
      (volume.restrict (Set.Icc a b)))
    (g : ℝ → PlaneHk Set.univ K E)
    (hS : ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeHkValueOperator K (S t) =
      ν • planeHkValueOperator 0 (planeGradientTensor (Q t)) + F t) :
    (fun t => hilbertBandHkOperator N K
      (fixedBandRhs N ν ((planeHkValueOperator (E := E) 1).compLpL 2
        (volume.restrict (Set.Icc a b)) Q)
        ((planeHkValueOperator (E := E) K).compLpL 2 (volume.restrict (Set.Icc a b)) T)
        F (fun s => planeHkValueOperator K (g s)) t))
      =ᵐ[volume.restrict (Set.Icc a b)]
        planeBandSobolevRhs N K S (timeValueSource T g) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (planeHkValueOperator (E := E) 1) Q,
    ContinuousLinearMap.coeFn_compLpL (planeHkValueOperator (E := E) K) T, hS] with t hq ht hs
  change hilbertBandHkOperator N K
    (-hilbertProjection N (((planeHkValueOperator (E := E) K).compLpL 2
        (volume.restrict (Set.Icc a b)) T) t) +
      ν • bandLaplacianOperator N (((planeHkValueOperator (E := E) 1).compLpL 2
        (volume.restrict (Set.Icc a b)) Q) t) +
      bandDivergenceOperator (E := E) N (F t) + hilbertProjection N (planeHkValueOperator K (g t))) =
      planeBandDivergenceCLM N K (S t) + planeHkCutoff N K (-T t + g t)
  rw [hq, ht]
  exact nativeBandRhs_lift_eq_sobolevSources N K ν (Q t) (T t) (g t) (S t) (F t) hs

theorem fixedBandSobolevRhs_ae_eq_sourceRhs_of_field_values {a b : ℝ}
    (N K : ℕ) (ν : ℝ)
    (Q : Lp (PlaneHk Set.univ 1 E) 2 (volume.restrict (Set.Icc a b)))
    (T : Lp (PlaneHk Set.univ K E) 2 (volume.restrict (Set.Icc a b)))
    (S : Lp (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) 2
      (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) 2
      (volume.restrict (Set.Icc a b)))
    (D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (hD : D = (planeHkValueOperator (E := E) K).compLpL 2 (volume.restrict (Set.Icc a b)) T)
    (g : ℝ → PlaneHk Set.univ K E)
    (hS : ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeHkValueOperator K (S t) =
      ν • planeHkValueOperator 0 (planeGradientTensor (Q t)) + F t) :
    (fun t => hilbertBandHkOperator N K
      (fixedBandRhs N ν ((planeHkValueOperator (E := E) 1).compLpL 2
        (volume.restrict (Set.Icc a b)) Q)
        D F (fun s => planeHkValueOperator K (g s)) t))
      =ᵐ[volume.restrict (Set.Icc a b)]
        planeBandSobolevRhs N K S (timeValueSource T g) := by
  subst D
  exact fixedBandSobolevRhs_ae_eq_sourceRhs_of_flux_value N K ν Q T S F g hS
end

/-! Literal tested weak equation of the actual limiting coefficient fields. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance coefficientWeakAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance coefficientWeakTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

def coefficientWeakTestValue {K : ι → ℕ} {D : ℕ} {a b : ℝ} (hab : a ≤ b)
    (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D)
    (W : PlaneHighTime (h := h) K a b) (i : ι) (ν : ℝ)
    (f : Lp (h i) 2 (volume : Measure (Vec 2)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp (h i) 2 (volume : Measure (Vec 2)))
    (t : ℝ) (ψ : PlaneHk Set.univ 1 (h i)) : ℝ :=
  inner ℝ f (planeHkValueOperator 1 ψ) -
    (∫ s in a..t, ∫ x, inner ℝ (C.drift i (clampPoint a b hab s) x
      (((highGradientReadout (h := h) K i).compLpL 2 (volume.restrict (Set.Icc a b)) W) s x))
      (planeHkValueOperator 1 ψ x)) -
    ν * (∫ s in a..t, ∫ x, inner ℝ
      (((highGradientReadout (h := h) K i).compLpL 2 (volume.restrict (Set.Icc a b)) W) s x)
      (planeHkValueOperator 0 (planeGradientTensor ψ) x)) -
    (∑ j, ∑ d : admissibleOrders K D i j, ∫ s in a..t, ∫ x, inner ℝ
      (C.coupling i j d (clampPoint a b hab s) x
        (((highTensorReadout (h := h) K j (d.1 - 1)
          (by have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d; omega)).compLpL 2
            (volume.restrict (Set.Icc a b)) W) s x))
      (planeHkValueOperator 0 (planeGradientTensor ψ) x)) -
    (∫ s in a..t, inner ℝ (F s) (planeHkValueOperator 0 (planeGradientTensor ψ))) +
    ∫ s in a..t, inner ℝ (g s) (planeHkValueOperator 1 ψ)

theorem nativeRawTestValue_eq_coefficientWeakTestValue {K : ι → ℕ} {D : ℕ} {a b : ℝ}
    (hab : a ≤ b) (C : ProjectedCoefficients (h := h) (Set.Icc a b) K D) (hc : C.IsMeasurable)
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) (i : ι) (ν : ℝ)
    (f : Lp (h i) 2 (volume : Measure (Vec 2)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp (h i) 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b)))
    (t : Set.Icc a b) (ψ : PlaneHk Set.univ 1 (h i)) :
    nativeRawTestValue ν f (weakH1CarrierTimeCLM K a b i W) (limitDriftField hab C hc i W)
      (limitFluxField hab C hc W i F) g t ψ =
      coefficientWeakTestValue hab C W i ν f F g t ψ := by
  have hd := limitDriftField_test_integral hab t.property C hc W i (planeHkValueOperator 1 ψ)
  have hr := weakH1Carrier_gradient_test_integral t.property W hW i
    (planeHkValueOperator 0 (planeGradientTensor ψ))
  have hf := limitFluxField_test_integral hab t.property C hc W i F
    (planeHkValueOperator 0 (planeGradientTensor ψ))
  rw [nativeRawTestValue_expansion t.property ν _ _ _ _ _ hg ψ, hd, hr, hf]
  unfold coefficientWeakTestValue
  ring
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The actual transport residual preserves the paper's original value-source budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceValueBudgetCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (h i)) := inferInstance
local instance sourceValueBudgetTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (h i)) 2 (volume.restrict (Set.Icc a b))) := inferInstance

theorem sourceResidualValue_budget_tendsto {a b : ℝ} (hab : a ≤ b)
    (K : ι → ℕ) (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (U : ∀ i, Lp (PlaneHk Set.univ (K i + 1) (h i)) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    Tendsto (fun N => ∫ t in Set.Icc a b, Real.sqrt (massNormSq ρ π
      (fun i => (planeResidualValueSource hab (hK i) v hvm hv V strain B lam
        hV hstrain hB hlam hbv hjets (U i) (g i) N t).val))) atTop
      (𝓝 (∫ t in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i t).val)))) := by
  let R := fun N i => intervalTransportTimeCLM hab (hK i) v hvm hv V strain B lam
    hV hstrain hB hlam hbv hjets (planeSobolevTimeResidual (volume.restrict (Set.Icc a b)) N (K i + 1) (U i))
  have hr (i : ι) : Tendsto (fun N => R N i) atTop (𝓝 0) :=
    tendsto_intervalTransportTimeCLM_residual hab (hK i) v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets (U i)
  have he := planeMassNorm_timeLp_residual_tendsto (volume.restrict (Set.Icc a b)) K ρ π hπ g hg R hr
  have heq (N : ℕ) (i : ι) : planeResidualValueSource hab (hK i) v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets (U i) (g i) N = fun t => g i t - R N i t := by
    funext t
    change -(R N i t) + g i t = g i t - R N i t
    abel
  simpa only [heq] using he

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Pointwise convergence of every native weak test along the actual common Galerkin subsequence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def sourceWeakTestValue (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (W : PlaneHighTime (h := h) K a b) (i : ι) (t : ℝ)
    (ψ : PlaneHk Set.univ 1 (h i)) : ℝ :=
  inner ℝ (planeHkValueOperator (K i) (f i)) (planeHkValueOperator 1 ψ) -
    (∫ q in a..t, ∫ x, inner ℝ
      (driftFiberCoefficient (E := h i) (v q) x
        (((highGradientReadout (h := h) K i).compLpL 2
          (volume.restrict (Set.Icc a b)) W) q x)) (planeHkValueOperator 1 ψ x)) -
    ν * (∫ q in a..t, ∫ x, inner ℝ
      (((highGradientReadout (h := h) K i).compLpL 2
        (volume.restrict (Set.Icc a b)) W) q x)
      (planeHkValueOperator 0 (planeGradientTensor ψ) x)) -
    (∑ j, ∑ d : admissibleOrders K D i j, ∫ q in a..t, ∫ x, inner ℝ
      (A i j d q x (((highTensorReadout (h := h) K j (d.1 - 1)
        (by have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d; omega)).compLpL 2
          (volume.restrict (Set.Icc a b)) W) q x))
      (planeHkValueOperator 0 (planeGradientTensor ψ) x)) -
    (∫ q in a..t, inner ℝ (planeHkValueOperator (K i) (F i q))
      (planeHkValueOperator 0 (planeGradientTensor ψ))) +
    (∫ q in a..t, inner ℝ (planeHkValueOperator (K i) (g i q))
      (planeHkValueOperator 1 ψ))

theorem sourceProjectedCurve_test_tendsto {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (i : ι) (t : Set.Icc a b) (ψ : PlaneHk Set.univ 1 (h i)) :
    Tendsto (fun n => inner ℝ (u (φ n) t i) (planeHkValueOperator 1 ψ))
      atTop (𝓝 (sourceWeakTestValue K D a b v A ν f F g W i t ψ)) := by
  have hd := drift_clampedOperator_test_weak_limit hab t.property K i v hv hvm V hV hbv
    u φ hφ W R hu hw (planeHkValueOperator 1 ψ)
  have hr := diffusion_projected_test_weak_limit hab t.property K i u φ hφ W R hu hw ψ
  simp_rw [← L2.inner_def] at hr
  have hc (j : ι) (d : admissibleOrders K D i j) :=
    coupling_clampedOperator_test_weak_limit hab t.property ρ hρ K D i j d (A i j d)
      (hAf i j d) (hAm i j d) (hAc i j d) u φ hφ W R hu hw ψ
  have hsum := tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_finsetSum Finset.univ (fun d _ => hc j d))
  have hf := (fluxForcing_projected_test_tendsto hab t.property (F i) (hF i) ψ).comp
    hφ.tendsto_atTop
  have hg' := (valueForcing_projected_test_tendsto hab t.property (g i) (hg i)
    (planeHkValueOperator 1 ψ)).comp hφ.tendsto_atTop
  simp_rw [Function.comp_def, hilbertProjection_inner] at hg'
  simp only [Function.comp_def] at hf
  have hinit := projectedInitial_test_tendsto f φ hφ i (planeHkValueOperator 1 ψ)
  have hlim := (((hinit.add hd.neg).sub ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ν) atTop (𝓝 ν)).mul hr)).sub hsum).sub hf |>.add hg'
  refine hlim.congr' (Eventually.of_forall ?_)
  intro n
  have htest := projectedCurve_expanded_test_identity hab
    (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
    (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
    (φ n) ν f F hF g hg (u (φ n)) (heq (φ n)) i t (planeHkValueOperator 1 ψ)
  dsimp only [ProjectedCoefficients.reindex, sourceProjectedCoefficients] at htest
  dsimp only
  linarith only [htest]

theorem sourceProjectedCurve_test_converges {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (i : ι) (t : Set.Icc a b) (ψ : PlaneHk Set.univ 1 (h i)) :
    ∃ L : ℝ, Tendsto (fun n => inner ℝ (u (φ n) t i) (planeHkValueOperator 1 ψ))
      atTop (𝓝 L) := by
  exact ⟨_, sourceProjectedCurve_test_tendsto hab ρ hρ v hv V hV hbv K D A hAc hAf
    hvm hAm ν f F hF g hg u heq φ hφ W R hu hw i t ψ⟩
end

/-! Pointwise convergence of every native weak test along the actual common Galerkin subsequence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceProjectedCurve_scalarTrace {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hrange : ∀ N t, familyProjection N (u N t) = u N t)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C : ℝ)
    (hmass : ∀ N t, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤ C)
    (i : ι) (ψ : PlaneHk Set.univ 1 (h i)) :

    ∃ q : ℝ → ℝ,
      (∀ t : Set.Icc a b, Tendsto (fun n => inner ℝ (u (φ n) t i)
        (planeHkValueOperator 1 ψ)) atTop (𝓝 (q t))) ∧
      q =ᵐ[volume.restrict (Set.Icc a b)] fun t => inner ℝ
        (highJetReadout (h := h) K i (valueIndex2 (K i + 1)) (W t))
        (planeHkValueOperator 1 ψ) := by
  classical
  have hex (t : Set.Icc a b) := sourceProjectedCurve_test_converges hab ρ hρ
    v hv V hV hbv K D A hAc hAf hvm hAm ν f F hF g hg u heq φ hφ W R hu hw i t ψ
  choose q hq using hex
  let Q : ℝ → ℝ := fun t => q (clampPoint a b hab t)
  have hQ (t : Set.Icc a b) : Q t = q t := by
    dsimp only [Q]
    congr 1
    apply Subtype.ext
    simp only [clampPoint, max_eq_right t.property.1, min_eq_right t.property.2]
  have hlim (t : Set.Icc a b) : Tendsto (fun n => inner ℝ (u (φ n) t i)
      (planeHkValueOperator 1 ψ)) atTop (𝓝 (Q t)) := by
    rw [hQ]
    exact hq t
  refine ⟨Q, hlim, ?_⟩
  apply nativeScalarTrace_eq_weakClass hab K u φ W hw
    (fun n t => hrange (φ n) t) i (planeHkValueOperator 1 ψ)
    (Real.sqrt ((∑ i, π i / factorialWeightMin ρ (K i)) * C)) _ Q hlim
  intro n t
  exact (PiLp.norm_apply_le _ i).trans
    (projectedFamily_norm_le_of_massBound (φ n) K ρ hρ π hπ
      (u (φ n) t) (hrange (φ n) t) C (hmass (φ n) t))
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The true diffusion, all admissible couplings, and external flux form a Sobolev time L² class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceFluxCarrierAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance sourceFluxCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance sourceFluxCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance sourceFluxTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := inferInstance
local instance sourceFluxTimeModule (i : ι) (k : ℕ) (a b : ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := (sourceFluxTimeSpace i k a b).toModule

def sourceSobolevFlux {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (ν : ℝ) (W : PlaneHighTime (h := h) K a b) (i : ι)
    (F : ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b))) :
    Lp (PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b)) :=
  assembleTimeFlux (volume.restrict (Set.Icc a b)) ν (weakGradientTimeCLM K a b i W)
    (fun j d => weakCoupledFluxTimeCLM hab ρ hρ K D i j d (A i j d) (hAf i j d)
      (hAc i j d) (hAm i j d) W) (hF.toLp F)

end AVRegularity.CoupledEnergyPlane
end
