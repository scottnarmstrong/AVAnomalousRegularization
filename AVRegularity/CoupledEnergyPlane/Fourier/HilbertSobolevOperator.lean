-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Fourier.BandSobolev
public import AVRegularity.CoupledEnergyPlane.CarrierMapOperator

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Genuine plane Fourier cutoff weak jets for arbitrary finite Hilbert fibers. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Every cutoff derivative is constructed from proved scalar weak derivatives. -/
def hilbertBandHk (N K : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    PlaneHk Set.univ K E :=
  ∑ k : Fin (Module.finrank ℝ E), mapPlaneHk
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (stdOrthonormalBasis ℝ E k))
    (bandProjectionHk N K (fiberCoordinate k u))

theorem hilbertBandHk_component (N K : ℕ) (u : Lp E 2 (volume : Measure (Vec 2)))
    (a : JetIndex2 K) :
    (hilbertBandHk N K u).val a =
      planeToUniv (hilbertLift (bandWordRealOperator N a.2) u) := by
  classical
  simp only [hilbertBandHk, hilbertLift, sum_apply, ContinuousLinearMap.comp_apply,
    map_sum, planeHk_sum_component]
  change (∑ k : Fin (Module.finrank ℝ E), (mapPlaneHk
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (stdOrthonormalBasis ℝ E k))
    (bandProjectionHk N K (fiberCoordinate k u))).val a) = _
  simp only [mapPlaneHk_component, bandProjectionHk_component, ← bandWordRealOperator_apply]
  apply Finset.sum_congr rfl
  intro k _
  apply Lp.ext
  have hs := ContinuousLinearMap.coeFn_compLpL
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (stdOrthonormalBasis ℝ E k))
    (planeToUniv (bandWordRealOperator N a.2 (fiberCoordinate k u)))
  have hi := fiberInjection_ae k (bandWordRealOperator N a.2 (fiberCoordinate k u))
  simp only [Measure.restrict_univ] at hs ⊢
  filter_upwards [hs, planeToUniv_ae (bandWordRealOperator N a.2 (fiberCoordinate k u)),
    planeToUniv_ae (fiberInjection k (bandWordRealOperator N a.2 (fiberCoordinate k u))), hi]
    with x hx hv hp he
  simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, hv,
    hp, he] using hx

theorem hilbertBandHk_value (N K : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    (hilbertBandHk N K u).val (valueIndex2 K) = planeToUniv (hilbertProjection N u) := by
  rw [hilbertBandHk_component]
  have h : bandWordRealOperator N (Fin.elim0 : Fin 0 → Fin 2) =
      realSpectralProjection (frequencyBall N) (frequencyBall_measurableSet N)
        (frequencyBall_neg N) := by
    apply ContinuousLinearMap.ext
    intro f
    exact bandWordReal_zero N Fin.elim0 f
  exact congrArg (fun T => planeToUniv (hilbertLift T u)) h
end

/-! Bounded linear promotion of the literal plane Fourier cutoff and its weak jets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The actual frequency cutoff as a bounded map into the closed plane Sobolev graph. -/
def hilbertBandHkOperator (N K : ℕ) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] PlaneHk Set.univ K E where
  toFun := hilbertBandHk N K
  map_add' u v := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    simp only [planeHk_add_component, hilbertBandHk_component, map_add]
  map_smul' c u := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    simp only [RingHom.id_apply, planeHk_smul_component, hilbertBandHk_component, map_smul]
  cont := by
    apply Continuous.subtype_mk
    change Continuous (fun u : Lp E 2 (volume : Measure (Vec 2)) => (hilbertBandHk N K u).val)
    have hc : Continuous (fun u : Lp E 2 (volume : Measure (Vec 2)) =>
        fun a : JetIndex2 K => (hilbertBandHk N K u).val a) := by
      apply continuous_pi
      intro a
      simp only [hilbertBandHk_component]
      exact planeToUniv.continuous.comp (hilbertLift (bandWordRealOperator N a.2)).continuous
    have h := (PiLp.continuous_toLp 2
      (fun _ : JetIndex2 K => ComponentL2 (volume.restrict Set.univ) E)).comp hc
    simpa only [Function.comp_def, WithLp.toLp_ofLp] using h

@[simp] theorem hilbertBandHkOperator_apply (N K : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertBandHkOperator N K u = hilbertBandHk N K u := rfl

/-- The literal zeroth-order value in ambient spatial L². -/
def planeHkValueOperator (K : ℕ) : PlaneHk Set.univ K E →L[ℝ]
    Lp E 2 (volume : Measure (Vec 2)) :=
  univToPlane.toContinuousLinearMap.comp
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K => ComponentL2 (volume.restrict Set.univ) E)
      (valueIndex2 K)).comp (planeHkGraph (E := E) Set.univ K).toSubmodule.subtypeL)

omit [FiniteDimensional ℝ E] in
@[simp] theorem planeHkValueOperator_apply (K : ℕ) (u : PlaneHk Set.univ K E) :
    planeHkValueOperator K u = univToPlane (u.val (valueIndex2 K)) := rfl

@[simp] theorem planeHkValueOperator_hilbertBand (N K : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    planeHkValueOperator K (hilbertBandHkOperator N K u) = hilbertProjection N u := by
  simp only [planeHkValueOperator_apply, hilbertBandHkOperator_apply, hilbertBandHk_value,
    univToPlane_planeToUniv]
end

end AVRegularity.CoupledEnergyPlane.Fourier
end
