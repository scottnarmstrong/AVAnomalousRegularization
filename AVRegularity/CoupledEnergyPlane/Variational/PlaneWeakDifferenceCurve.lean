-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Variational.DerivativeTensorOperator
public import AVRegularity.CoupledEnergyPlane.Variational.SourcePrimitiveInitial
import AVRegularity.CoupledEnergyPlane.Fourier.LaplacianProjection
import AVRegularity.CoupledEnergy.CouplingBounds
public import AVRegularity.CoupledEnergyPlane.LimitFieldPairing
import Mathlib.MeasureTheory.SpecificCodomains.Pi

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Literal admissible coupling fluxes, with the exact coefficient budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def planeCoupledFluxCarrierOperator (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
 :
    PlaneHk Set.univ (K i' + 1) (h i') →L[ℝ]
      PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  (productPlaneHkOperator (A t) hC
    (fun l x => AVRegularity.CoupledEnergy.Galerkin.coefficientOrderSup_derivative_bound
      ρ hρ (K i) a b A hA l.val (Nat.le_of_lt_succ l.isLt) t ht x)).comp
    (planePositiveDerivativeTensorOperator (E := h i') (d.1 - 1)
      (admissibleOrders_reserve K D i i' d).1 (admissibleOrders_reserve K D i i' d).2)

omit [Fintype ι] in
theorem planeCoupledFluxCarrierOperator_apply (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (u : PlaneHk Set.univ (K i' + 1) (h i')) :
    planeCoupledFluxCarrierOperator ρ hρ K D a b i i' d A hA t ht hC u =
      planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC u := by
  simp only [planeCoupledFluxCarrierOperator, ContinuousLinearMap.comp_apply,
    planePositiveDerivativeTensorOperator_apply, productPlaneHkOperator_apply,
    planeCoupledFluxTerm, planeMultiplyIntervalCoefficient]

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual projected forcing has the exact constant-one mass pairing bounds. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedSource_massPairing_abs_le (N : ℕ) (K : ι → ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (g : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, Lp (h i) 2 (volume : Measure (Vec 2))) :
    |∑ i, (π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N (K i) (hilbertProjection N (planeHkValueOperator (K i) (g i)))).val
      (hilbertBandHk N (K i) (u i)).val| ≤
    Real.sqrt (massNormSq ρ π (fun i => (g i).val)) *
      Real.sqrt (massNormSq ρ π (fun i => (hilbertBandHk N (K i) (u i)).val)) := by
  simp_rw [hilbertBandHk_projection, hilbertBandHk_carrier_factorialPairing,
    factorialPairing_eq_weighted_inner]
  exact massFactorialPairing_abs_le ρ π hπ _ _

theorem projectedFlux_massPairing_abs_le (N : ℕ) (K : ι → ℕ) (ρ : ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (F : ∀ i, PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (u : ∀ i, Lp (h i) 2 (volume : Measure (Vec 2))) :
    |∑ i, (π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N (K i)
        (bandDivergenceOperator (E := h i) N (planeHkValueOperator (K i) (F i)))).val
      (hilbertBandHk N (K i) (u i)).val| ≤
    Real.sqrt (massNormSq ρ π (fun i => (F i).val)) *
      Real.sqrt (massGradNormSq ρ π (fun i => (hilbertBandHk N (K i + 1) (u i)).val)) := by
  simp_rw [bandDivergence_factorialPairing, mul_neg, Finset.sum_neg_distrib, abs_neg,
    factorialPairing_eq_weighted_inner]
  have hc := massFactorialPairing_abs_le ρ π hπ (fun i => (F i).val)
    (fun i => (planeGradientTensor (hilbertBandHk N (K i + 1) (u i))).val)
  simpa only [massNormSq, planeGradientTensor_factorialNormSq, massGradNormSq] using hc

theorem projectedFlux_massPairing_young_le (N : ℕ) (K : ι → ℕ) (ρ ν : ℝ)
    (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (F : ∀ i, PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (u : ∀ i, Lp (h i) 2 (volume : Measure (Vec 2))) :
    |∑ i, (π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N (K i)
        (bandDivergenceOperator (E := h i) N (planeHkValueOperator (K i) (F i)))).val
      (hilbertBandHk N (K i) (u i)).val| ≤
    (ν / 8) * massGradNormSq ρ π (fun i => (hilbertBandHk N (K i + 1) (u i)).val) +
      (2 / ν) * massNormSq ρ π (fun i => (F i).val) := by
  refine (projectedFlux_massPairing_abs_le N K ρ π hπ F u).trans ?_
  have hy := coupledFluxYoung hν
    (Real.sqrt (massNormSq ρ π (fun i => (F i).val)))
    (Real.sqrt (massGradNormSq ρ π (fun i => (hilbertBandHk N (K i + 1) (u i)).val)))
  simpa only [Real.sq_sqrt (massNormSq_nonneg ρ π hπ _),
    Real.sq_sqrt (massGradNormSq_nonneg ρ π hπ _)] using hy

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Every drift mask's plane integrability follows from the original velocity data of
`coupled_energy_plane`. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem coefficientDerivativeArray_zero_norm_le (C : Vec 2 → E →L[ℝ] F) (x : Vec 2) :
    ‖coefficientDerivativeArray C 0 x‖ ≤ ‖C x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  have he : ‖coefficientDerivativeArray C 0 x z‖ = ‖C x z‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [coefficientDerivativeArray_normSq, orderedCoefficientDerivative_zero]
  rw [he]
  exact (C x).le_opNorm z

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem driftCoefficient_norm_le (v : Vec 2 → Vec 2) (x : Vec 2) :
    ‖driftCoefficient v x‖ ≤ 2 * ‖v x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖∑ k : Fin 2, v x k * z k‖ ≤ _
  calc
    _ ≤ ∑ k : Fin 2, ‖v x k * z k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 2, ‖v x‖ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm (v x) k) (PiLp.norm_apply_le z k)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

variable {K Kmax j : ℕ}

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem driftMaskTerm_memLp_of_velocityJets (hj : j ≤ K) (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On Set.univ D)
    (m : PositionMask j) (w : DerivativeWord2 j) :
    MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict Set.univ) := by
  let l := maskLeftLength j m
  by_cases hl : l = 0
  · apply driftMaskTerm_memLp_of_coefficientBound hj v hv D hD m w (2 * V)
    intro x
    rw [show maskLeftLength j m = 0 from hl]
    apply (coefficientDerivativeArray_zero_norm_le _ x).trans
    exact (driftCoefficient_norm_le v x).trans (mul_le_mul_of_nonneg_left (hbv x) (by norm_num))
  · apply driftMaskTerm_memLp_of_coefficientBound hj v hv D hD m w
      (a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    exact hjets l (by omega) ((maskLeftLength_le j m).trans (hj.trans hK))

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The literal interval multiplier agrees with the value of its Sobolev product. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [FiniteDimensional ℝ F] in
theorem planeMultiplyIntervalCoefficient_value (ρ : ℝ) (hρ : 0 < ρ)
    (K : ℕ) (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K : ℕ) (A t))
    (q : PlaneHk Set.univ K E) :
    planeCoefficientOperator (A t) hC.continuous ENNReal.toReal_nonneg
      (sourceCoefficient_norm_le ρ hρ K a b A hA t ht)
      (planeHkValueOperator K q) =
      planeHkValueOperator K (planeMultiplyIntervalCoefficient ρ hρ K a b A hA t ht hC q) := by
  exact planeCoefficientOperator_eq_productValue q (A t) hC
    (fun l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t ht x)
    ENNReal.toReal_nonneg (sourceCoefficient_norm_le ρ hρ K a b A hA t ht)

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Spacetime weak compactness with an explicit, short Hilbert instance chain. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] in
/-- Uniform higher-order spacetime norms yield one subsequence for every linear observable. -/
theorem exists_strictMono_tendsto_highTime_clm (K : ι → ℕ) (a b R : ℝ)
    (u : ℕ → PlaneHighTime (h := h) K a b) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (U : PlaneHighTime (h := h) K a b) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
        Tendsto (fun n => ell (u (φ n))) atTop (𝓝 (ell U)) := by
  let : ∀ i, InnerProductSpace ℝ (JetL2 (volume.restrict Set.univ) (K i + 1) (h i)) := fun i => inferInstance
  let : InnerProductSpace ℝ (PlaneHighHilbert (h := h) K) :=
    PiLp.innerProductSpace (fun i => JetL2 (volume.restrict Set.univ) (K i + 1) (h i))
  let : InnerProductSpace ℝ (PlaneHighTime (h := h) K a b) := L2.innerProductSpace
  let : ∀ i, TopologicalSpace.SeparableSpace (JetL2 (volume.restrict Set.univ) (K i + 1) (h i)) :=
    fun i => planeJetSeparableSpace (K i + 1)
  let : SecondCountableTopology (PlaneHighHilbert (h := h) K) :=
    PiLp.secondCountableTopology 2 (fun i => JetL2 (volume.restrict Set.univ) (K i + 1) (h i))
  let : TopologicalSpace.SeparableSpace (PlaneHighHilbert (h := h) K) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  let : SFinite (volume.restrict (Set.Icc a b) : Measure ℝ) := inferInstance
  let : MeasurableSpace.CountablyGenerated ℝ := inferInstance
  let : IsSeparable (volume.restrict (Set.Icc a b) : Measure ℝ) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (PlaneHighTime (h := h) K a b) := Lp.SecondCountableTopology
  let : TopologicalSpace.SeparableSpace (PlaneHighTime (h := h) K a b) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  exact exists_strictMono_tendsto_clm_of_norm_le u R hu

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Weak spacetime limits of the actual Galerkin jets retain the plane Sobolev graph. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem weakHighTime_graph_ae (K : ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h)) (φ : ℕ → ℕ)
    (W : PlaneHighTime (h := h) K a b)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W))) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      W t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1) := by
  have hi (i : ι) : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      W t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1) := by
    let S := planeHkGraph (E := h i) Set.univ (K i + 1)
    let L : PlaneHighHilbert (h := h) K →L[ℝ]
        JetL2 (volume.restrict Set.univ) (K i + 1) (h i) :=
      (ContinuousLinearMap.id ℝ _ - S.toSubmodule.starProjection).comp
        (PiLp.proj (𝕜 := ℝ) 2
          (fun j => JetL2 (volume.restrict Set.univ) (K j + 1) (h j)) i)
    let LT := L.compLpL 2 (volume.restrict (Set.Icc a b))
    have hn (n : ℕ) : LT (higherBandBochner (φ n) K a b hab (u (φ n))) = 0 := by
      apply Lp.ext
      filter_upwards [ContinuousLinearMap.coeFn_compLpL L
          (higherBandBochner (φ n) K a b hab (u (φ n))),
        higherBandBochner_graph_ae (φ n) K a b hab (u (φ n)), Lp.coeFn_zero
          (E := JetL2 (volume.restrict Set.univ) (K i + 1) (h i))
          (p := 2) (μ := volume.restrict (Set.Icc a b))] with t ht hg hz
      change (L.compLpL 2 (volume.restrict (Set.Icc a b))
        (higherBandBochner (φ n) K a b hab (u (φ n)))) t = _
      rw [ht, hz]
      change (higherBandBochner (φ n) K a b hab (u (φ n)) t i) -
        S.toSubmodule.starProjection (higherBandBochner (φ n) K a b hab (u (φ n)) t i) = 0
      rw [Submodule.starProjection_eq_self_iff.mpr (hg i), sub_self]
    have hzero := map_eq_zero_of_weak_limit LT hw hn
    have hae := ContinuousLinearMap.coeFn_compLpL L W
    rw [hzero] at hae
    filter_upwards [hae, Lp.coeFn_zero
      (E := JetL2 (volume.restrict Set.univ) (K i + 1) (h i))
      (p := 2) (μ := volume.restrict (Set.Icc a b))] with t ht hz
    rw [hz] at ht
    change 0 = W t i - S.toSubmodule.starProjection (W t i) at ht
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp ht.symm).symm
  exact ae_all_iff.mpr hi

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Genuine higher-order plane Sobolev carriers reconstructed from the weak spacetime class. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def weakHighCarrier (K : ι → ℕ) (a b : ℝ)
    (W : PlaneHighTime (h := h) K a b) (i : ι) (t : ℝ) :
    PlaneHk Set.univ (K i + 1) (h i) :=
  closedSubmoduleReadout (planeHkGraph (E := h i) Set.univ (K i + 1)) (W t i)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem weakHighCarrier_memLp (K : ι → ℕ) (a b : ℝ)
    (W : PlaneHighTime (h := h) K a b) (i : ι) :
    MemLp (weakHighCarrier K a b W i) 2 (volume.restrict (Set.Icc a b)) := by
  exact ((closedSubmoduleReadout (planeHkGraph (E := h i) Set.univ (K i + 1))).comp
    (PiLp.proj (𝕜 := ℝ) 2
      (fun j => JetL2 (volume.restrict Set.univ) (K j + 1) (h j)) i)).comp_memLp' (Lp.memLp W)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem weakHighCarrier_jet_ae (K : ι → ℕ) (a b : ℝ)
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      W t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1)) (i : ι) :
    (fun t => (weakHighCarrier K a b W i t).val) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => W t i := by
  filter_upwards [hW] with t ht
  exact Submodule.starProjection_eq_self_iff.mpr (ht i)
end

/-! Bundle arbitrary higher plane Sobolev trajectories in the native time space. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def planeCarrierHighJets (K : ι → ℕ)
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) : PlaneHighHilbert (h := h) K :=
  WithLp.toLp 2 (fun i => (w i).val)

theorem planeCarrierHighJets_memLp (K : ι → ℕ) (a b : ℝ)
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => planeCarrierHighJets K (fun i => w i t)) 2
      (volume.restrict (Set.Icc a b)) := by
  have hi (i : ι) := (planeHkGraph (E := h i) Set.univ (K i + 1)).toSubmodule.subtypeL.comp_memLp' (hw i)
  have hp : MemLp (fun t i => (w i t).val) 2 (volume.restrict (Set.Icc a b)) :=
    memLp_pi_iff.mpr hi
  simpa only [Function.comp_def, planeCarrierHighJets] using!
    (PiLp.continuousLinearEquiv 2 ℝ (fun i =>
      JetL2 (volume.restrict Set.univ) (K i + 1) (h i))).symm.toContinuousLinearMap.comp_memLp' hp

def planeCarrierHighTime (K : ι → ℕ) (a b : ℝ)
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) : PlaneHighTime (h := h) K a b :=
  (planeCarrierHighJets_memLp K a b w hw).toLp (fun t => planeCarrierHighJets K (fun i => w i t))

theorem planeCarrierHighTime_ae (K : ι → ℕ) (a b : ℝ)
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      (w i t).val = planeCarrierHighTime K a b w hw t i := by
  filter_upwards [(planeCarrierHighJets_memLp K a b w hw).coeFn_toLp] with t ht
  intro i
  exact (congrArg (fun U : PlaneHighHilbert (h := h) K => U i) ht).symm

theorem planeCarrierHighTime_graph_ae (K : ι → ℕ) (a b : ℝ)
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      planeCarrierHighTime K a b w hw t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1) := by
  filter_upwards [planeCarrierHighTime_ae K a b w hw] with t ht
  intro i
  rw [← ht i]
  exact (w i t).property

theorem planeCarrierHighTime_readout_ae (K : ι → ℕ) (a b : ℝ)
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    weakHighCarrier K a b (planeCarrierHighTime K a b w hw) i
      =ᵐ[volume.restrict (Set.Icc a b)] w i := by
  have hjet := weakHighCarrier_jet_ae K a b (planeCarrierHighTime K a b w hw)
    (planeCarrierHighTime_graph_ae K a b w hw) i
  filter_upwards [hjet, planeCarrierHighTime_ae K a b w hw] with t ht he
  apply Subtype.ext
  exact ht.trans (he i).symm
end

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Actual plane transport products belong to the full finite weak Sobolev graph. -/

/-- Construction-only uniform velocity derivative bound, including the value level. -/
def driftEnvelope (V a B lam : ℝ) (l : ℕ) : ℝ :=
  if l = 0 then 2 * V else a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)

theorem driftCoefficient_array_envelope {Kmax : ℕ}
    (v : Vec 2 → Vec 2) (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (l : ℕ) (hl : l ≤ Kmax) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤ driftEnvelope V a B lam l := by
  by_cases hz : l = 0
  · subst l
    simp only [driftEnvelope, ite_true]
    exact (coefficientDerivativeArray_zero_norm_le _ x).trans
      ((driftCoefficient_norm_le v x).trans
        (mul_le_mul_of_nonneg_left (hbv x) (by norm_num)))
  · simp only [driftEnvelope, hz, ite_false]
    exact hjets l (by omega) hl x

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The true velocity-gradient contraction, constructed with every ordered product-rule derivative. -/
def planeTransportCarrier {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (p : PlaneHk Set.univ (K + 1) E) : PlaneHk Set.univ K E :=
  (planeGradientTensor p).mulCoefficient (driftFiberCoefficient v)
    ((driftFiberCoefficient_contDiff v hv).of_le (by simp))
    (A := fun l => driftEnvelope V a B lam l.val)
    (fun l x => (driftFiberCoefficient_array_norm_le v hv l.val x).trans
      (driftCoefficient_array_envelope v V hbv a B lam hjets l.val
        ((Nat.le_of_lt_succ l.isLt).trans hK) x))

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! A pointwise limit of bounded native Galerkin observables equals the actual weak spacetime value. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem nativeScalarTrace_eq_weakClass {a b : ℝ} (hab : a ≤ b) (K : ι → ℕ)
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h)) (φ : ℕ → ℕ)
    (W : PlaneHighTime (h := h) K a b)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hrange : ∀ n t, familyProjection (φ n) (u (φ n) t) = u (φ n) t)
    (i : ι) (z : Lp (h i) 2 (volume : Measure (Vec 2))) (B : ℝ)
    (hb : ∀ n t, ‖u (φ n) t i‖ ≤ B)
    (g : ℝ → ℝ)
    (hlim : ∀ t : Set.Icc a b, Tendsto (fun n => inner ℝ (u (φ n) t i) z)
      atTop (𝓝 (g t))) :
    g =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      inner ℝ (highJetReadout (h := h) K i (valueIndex2 (K i + 1)) (W t)) z := by
  let μ := volume.restrict (Set.Icc a b)
  let L : PlaneHighHilbert (h := h) K →L[ℝ] ℝ :=
    (innerSL ℝ z).comp (highJetReadout (h := h) K i (valueIndex2 (K i + 1)))
  let q : ℕ → ℝ → ℝ := fun n t => inner ℝ (extendCurve hab (u (φ n)) t i) z
  have hq (n : ℕ) : AEStronglyMeasurable (q n) μ := by
    exact (((PiLp.proj (𝕜 := ℝ) 2
      (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i)).continuous.comp
      (continuous_extendCurve hab (u (φ n)))).inner continuous_const
      |>.aestronglyMeasurable.restrict
  have hpoint : ∀ᵐ t ∂μ, Tendsto (fun n => q n t) atTop (𝓝 (g t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [q, extendCurve_eq_of_mem hab _ ht] using hlim ⟨t, ht⟩
  have hg := aestronglyMeasurable_of_tendsto_ae atTop hq hpoint
  have hqb (n : ℕ) : ∀ᵐ t ∂μ, ‖q n t‖ ≤ B * ‖z‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp only [q]
    rw [extendCurve_eq_of_mem hab _ ht]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hb n ⟨t, ht⟩) (norm_nonneg z))
  have halign (n : ℕ) : q n =ᵐ[μ] fun t =>
      L (higherBandBochner (φ n) K a b hab (u (φ n)) t) := by
    have hcoe := (higherBandJet_memLp (φ n) K a b
      (continuous_extendCurve hab (u (φ n)))).coeFn_toLp
    filter_upwards [hcoe, ae_restrict_mem measurableSet_Icc] with t ht hm
    dsimp only [q, L, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    change _ = inner ℝ z (univToPlane
      ((higherBandBochner (φ n) K a b hab (u (φ n)) t i) (valueIndex2 (K i + 1))))
    change higherBandBochner (φ n) K a b hab (u (φ n)) t =
      higherBandJetOperator (h := h) (φ n) K (extendCurve hab (u (φ n)) t) at ht
    rw [ht]
    change _ = inner ℝ z (univToPlane
      ((hilbertBandHk (φ n) (K i + 1) (extendCurve hab (u (φ n)) t i)).val
        (valueIndex2 (K i + 1))))
    rw [hilbertBandHk_value, univToPlane_planeToUniv,
      extendCurve_eq_of_mem hab _ hm]
    have hp := congrArg (fun U : ProjectedFamily h => U i) (hrange n ⟨t, hm⟩)
    simp only [familyProjection_component] at hp
    rw [hp, real_inner_comm]
  have he := scalarTrace_eq_of_weakLp_and_boundedConvergence μ
    (fun n => higherBandBochner (φ n) K a b hab (u (φ n))) W hw L q g
    (B * ‖z‖) halign hg hqb hpoint
  simpa only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm] using he

end AVRegularity.CoupledEnergyPlane.Variational
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The literal raw drift multiplier is the value of the true Sobolev transport product. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeTransportCarrier_value {K Kmax : ℕ} (hK : K ≤ Kmax)
    (q : PlaneHk Set.univ (K + 1) E)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    planeCoefficientOperator (driftFiberCoefficient (E := E) v)
      (driftFiberCoefficient_contDiff (E := E) v hv).continuous (mul_nonneg (by norm_num) hV)
      (fun x => (driftFiberCoefficient_norm_le (E := E) v x).trans
        (mul_le_mul_of_nonneg_left (hbv x) (by norm_num)))
      (planeHkValueOperator K (planeGradientTensor q)) =
      planeHkValueOperator K (planeTransportCarrier hK v hv V hbv a B lam hjets q) := by
  exact planeCoefficientOperator_eq_productValue (planeGradientTensor q)
    (driftFiberCoefficient (E := E) v)
    ((driftFiberCoefficient_contDiff (E := E) v hv).of_le (by simp))
    (A := fun l => driftEnvelope V a B lam l.val)
    (fun l x => (driftFiberCoefficient_array_norm_le (E := E) v hv l.val x).trans
      (driftCoefficient_array_envelope v V hbv a B lam hjets l.val
        ((Nat.le_of_lt_succ l.isLt).trans hK) x))
    (mul_nonneg (by norm_num) hV)
    (fun x => (driftFiberCoefficient_norm_le (E := E) v x).trans
      (mul_le_mul_of_nonneg_left (hbv x) (by norm_num)))

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The genuine weak Sobolev carrier is a bounded linear readout of the spacetime class. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakCarrierNormed (i : ι) (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance weakCarrierAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

local instance weakCarrierTopAdd (i : ι) (k : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance

def weakHighCarrierTimeCLM (K : ι → ℕ) (a b : ℝ) (i : ι) :
    PlaneHighTime (h := h) K a b →L[ℝ]
      Lp (PlaneHk Set.univ (K i + 1) (h i)) 2 (volume.restrict (Set.Icc a b)) :=
  (((closedSubmoduleReadout (planeHkGraph (E := h i) Set.univ (K i + 1))).comp
    (PiLp.proj (𝕜 := ℝ) 2
      (fun j => JetL2 (volume.restrict Set.univ) (K j + 1) (h j)) i)).compLpL 2
        (volume.restrict (Set.Icc a b)))

theorem weakHighCarrierTimeCLM_ae (K : ι → ℕ) (a b : ℝ) (i : ι)
    (W : PlaneHighTime (h := h) K a b) :
    weakHighCarrierTimeCLM K a b i W =ᵐ[volume.restrict (Set.Icc a b)]
      weakHighCarrier K a b W i := by
  exact ContinuousLinearMap.coeFn_compLpL _ W
end

/-! Differences of actual higher time carriers retain the graph and the true Sobolev readout. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] in
theorem planeHighTime_sub_graph_ae (K : ι → ℕ) (a b : ℝ)
    (W W' : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      W t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1))
    (hW' : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      W' t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1)) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      (W - W') t i ∈ planeHkGraph (E := h i) Set.univ (K i + 1) := by
  filter_upwards [Lp.coeFn_sub W W', hW, hW'] with t hs ht ht'
  intro i
  rw [hs]
  change W t i - W' t i ∈ _
  exact (planeHkGraph (E := h i) Set.univ (K i + 1)).toSubmodule.sub_mem (ht i) (ht' i)

theorem weakHighCarrier_sub_ae (K : ι → ℕ) (a b : ℝ)
    (W W' : PlaneHighTime (h := h) K a b) (i : ι) :
    weakHighCarrier (h := h) K a b (W - W') i =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => weakHighCarrier (h := h) K a b W i t - weakHighCarrier (h := h) K a b W' i t := by
  have hs : weakHighCarrierTimeCLM (h := h) K a b i (W - W') =
      weakHighCarrierTimeCLM (h := h) K a b i W - weakHighCarrierTimeCLM (h := h) K a b i W' :=
    (weakHighCarrierTimeCLM (h := h) K a b i).toLinearMap.map_sub W W'
  have hd := weakHighCarrierTimeCLM_ae (h := h) K a b i (W - W')
  rw [hs] at hd
  have hc := Lp.coeFn_sub (weakHighCarrierTimeCLM (h := h) K a b i W)
    (weakHighCarrierTimeCLM (h := h) K a b i W')
  filter_upwards [hd, hc, weakHighCarrierTimeCLM_ae (h := h) K a b i W,
    weakHighCarrierTimeCLM_ae (h := h) K a b i W'] with t ht hc hu hu'
  exact ht.symm.trans (hc.trans (congrArg₂ (fun x y => x - y) hu hu'))
end

/-! The actual continuous difference trajectory and its higher-order Sobolev lift. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def planeWeakDifferenceCurve (K : ι → ℕ) (a b : ℝ)
    (u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hu : ∀ i, ContinuousOn (u i) (Set.Icc a b))
    (hu' : ∀ i, ContinuousOn (u' i) (Set.Icc a b)) (i : ι) :
    C(Set.Icc a b, PlaneHk Set.univ (K i) (h i)) :=
  ⟨fun t => u i t - u' i t, (continuousOn_iff_continuous_domRestrict.mp (hu i)).sub
    (continuousOn_iff_continuous_domRestrict.mp (hu' i))⟩

omit [Fintype ι] in
@[simp] theorem planeWeakDifferenceCurve_apply (K : ι → ℕ) (a b : ℝ)
    (u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hu : ∀ i, ContinuousOn (u i) (Set.Icc a b))
    (hu' : ∀ i, ContinuousOn (u' i) (Set.Icc a b)) (i : ι) (t : Set.Icc a b) :
    planeWeakDifferenceCurve (h := h) K a b u u' hu hu' i t = u i t - u' i t := rfl

omit [Fintype ι] in
theorem planeWeakDifferenceCurve_initial_zero (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hu : ∀ i, ContinuousOn (u i) (Set.Icc a b))
    (hu' : ∀ i, ContinuousOn (u' i) (Set.Icc a b))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i)) (hi : ∀ i, u i a = f i) (hi' : ∀ i, u' i a = f i) (i : ι) :
    planeWeakDifferenceCurve (h := h) K a b u u' hu hu' i ⟨a, le_rfl, hab⟩ = 0 := by
  rw [planeWeakDifferenceCurve_apply, hi i, hi' i, sub_self]

theorem planeWeakDifferenceCurve_carrier_alignment_ae (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hu : ∀ i, ContinuousOn (u i) (Set.Icc a b))
    (hu' : ∀ i, ContinuousOn (u' i) (Set.Icc a b))
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (hw' : ∀ i, MemLp (w' i) 2 (volume.restrict (Set.Icc a b)))
    (ht : ∀ i, (fun s => truncatePlaneHk (E := h i) (Nat.le_succ (K i)) (w i s)) =ᵐ[volume.restrict (Set.Icc a b)] u i)
    (ht' : ∀ i, (fun s => truncatePlaneHk (E := h i) (Nat.le_succ (K i)) (w' i s)) =ᵐ[volume.restrict (Set.Icc a b)] u' i)
    (i : ι) :
    extendCurve hab (planeWeakDifferenceCurve (h := h) K a b u u' hu hu' i)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => truncatePlaneHk (E := h i) (Nat.le_succ (K i))
        (weakHighCarrier (h := h) K a b
          (planeCarrierHighTime (h := h) K a b w hw - planeCarrierHighTime (h := h) K a b w' hw') i t) := by
  have hs := weakHighCarrier_sub_ae (h := h) K a b
    (planeCarrierHighTime (h := h) K a b w hw) (planeCarrierHighTime (h := h) K a b w' hw') i
  have hc := planeCarrierHighTime_readout_ae (h := h) K a b w hw i
  have hc' := planeCarrierHighTime_readout_ae (h := h) K a b w' hw' i
  filter_upwards [hs, hc, hc', ht i, ht' i, ae_restrict_mem measurableSet_Icc]
    with t hs hc hc' ht ht' htm
  rw [extendCurve_eq_of_mem hab _ htm, planeWeakDifferenceCurve_apply]
  have hz := hs.trans (congrArg₂ (fun x y => x - y) hc hc')
  have hl : truncatePlaneHk (E := h i) (Nat.le_succ (K i)) (w i t - w' i t) = u i t - u' i t :=
    ((truncatePlaneHk (E := h i) (Nat.le_succ (K i))).toLinearMap.map_sub (w i t) (w' i t)).trans
      (congrArg₂ (fun x y => x - y) ht ht')
  exact hl.symm.trans (congrArg (truncatePlaneHk (E := h i) (Nat.le_succ (K i))) hz.symm)
end

end AVRegularity.CoupledEnergyPlane.Variational
end
end
