-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergyPlane.PlaneKernelResidualDecomposition
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Time regularity of the native forced solution. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneForcedCutoffData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneForcedCutoffData Q)

theorem nativeForcedTimeRegularity (N : ℕ) :
    AbsolutelyContinuousOnInterval (extendCurve P.htime (T.curve N)) a b ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ ht : t ∈ Set.Icc a b,
        HasDerivAt (extendCurve P.htime (T.curve N))
          (projectedOperator Q.baseCoefficients N ν ⟨t, ht⟩
            (extendCurve P.htime (T.curve N) t) +
          projectedSource N (fun i => T.residualFlux N i) (T.residualValue N) t) t) := by
  have hr := T.timeRegularity N
  refine ⟨hr.1, ?_⟩
  have hd := hr.2.filter_mono (ae_mono (Measure.restrict_le_self (s := Set.Icc a b)))
  filter_upwards [hd] with t ht
  intro htm
  have hcl : clampPoint a b P.htime t = ⟨t, htm⟩ := by
    apply Subtype.ext
    simp only [clampPoint, max_eq_right htm.1, min_eq_right htm.2]
  have he := ht htm
  rw [projectedOperator_reindex_apply, hcl] at he
  exact he


end PlaneForcedCutoffData
end

/-! Time regularity of the native kernel solution. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelSolutionData Q)

theorem nativeKernelTimeRegularity (N : ℕ) :
    AbsolutelyContinuousOnInterval (extendCurve P.htime (T.forced.curve N)) a b ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ ht : t ∈ Set.Icc a b,
        HasDerivAt (extendCurve P.htime (T.forced.curve N))
          (projectedOperator Q.baseCoefficients N ν ⟨t, ht⟩
            (extendCurve P.htime (T.forced.curve N) t) +
          projectedSource N (fun i s => T.residualFlux N i s + P.flux t ht
            (fun j => hilbertBandHk N (k + 1)
              (extendCurve P.htime (T.forced.curve N) t j)) i) (T.forced.residualValue N) t) t) := by
  have hr := T.forced.timeRegularity N
  refine ⟨hr.1, ?_⟩
  have hd := hr.2.filter_mono (ae_mono (Measure.restrict_le_self (s := Set.Icc a b)))
  have hs := ae_all_iff.mpr (T.residualFlux_source_decomposition_ae N)
  filter_upwards [hd, hs] with t ht hsrc
  intro htm
  have hcl : clampPoint a b P.htime t = ⟨t, htm⟩ := by
    apply Subtype.ext
    simp only [clampPoint, max_eq_right htm.1, min_eq_right htm.2]
  have hp : projectedOperator (Q.baseCoefficients.reindex (clampPoint a b P.htime))
      N ν t (extendCurve P.htime (T.forced.curve N) t) =
      projectedOperator Q.baseCoefficients N ν ⟨t, htm⟩
        (extendCurve P.htime (T.forced.curve N) t) := by
    rw [projectedOperator_reindex_apply, hcl]
  have hsource : projectedSource N (fun i => T.forced.residualFlux N i)
      (T.forced.residualValue N) t =
      projectedSource N (fun i s => T.residualFlux N i s + P.flux t htm
        (fun j => hilbertBandHk N (k + 1)
          (extendCurve P.htime (T.forced.curve N) t j)) i) (T.forced.residualValue N) t := by
    apply PiLp.ext
    intro i
    have hi := hsrc i
    rw [P.carrierFlux_of_mem _ i t htm] at hi
    simp only [projectedSource, WithLp.ofLp_toLp, hi]
  have he := ht htm
  rw [hp, hsource] at he
  exact he

end PlaneKernelSolutionData
end

/-! Pointwise-in-time energy of the native kernel solution. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelSolutionData Q)

theorem nativePointEnergy (N : ℕ) (t : Set.Icc a b) :
    massNormSq ρ P.π (fun i => (hilbertBandHk N k (T.forced.curve N t i)).val) +
      (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq ρ P.π
        (fun i => (hilbertBandHk N (k + 1)
          (extendCurve P.htime (T.forced.curve N) s i)).val)) ≤
    2 * massNormSq ρ P.π (fun i => (hilbertBandHk N k
      (T.forced.curve N ⟨a, le_rfl, P.htime⟩ i)).val) +
      (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π
        (fun i => (T.residualFlux N i s).val)) +
      10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π
        (fun i => (T.forced.residualValue N i s).val))) ^ 2 := by
  have ht := T.nativeKernelTimeRegularity N
  have hg (i : ι) : Integrable (T.forced.residualValue N i) (volume.restrict (Set.Icc a b)) :=
    planeResidualValueSource_integrable P.htime (show k ≤ k from le_rfl) Q.v Q.measurable Q.smooth
      Q.V Q.strain Q.B Q.lam Q.V_nonneg Q.strain_nonneg
      (le_trans zero_le_one Q.B_ge_one) Q.lam_pos Q.bounded Q.jets
      (T.forced.highComponent i) (T.g i) N (T.hg i)
  obtain ⟨S, _hS, hpoint, he⟩ := Q.kernelProjectedEnergy_uniform_of_timeRegularity N (T.forced.curve N)
    (fun i => T.residualFlux N i) (T.forced.residualValue N)
    (fun i => Lp.memLp (T.residualFlux N i)) hg ht.1 ht.2
  simp only [intervalIntegral.integral_of_le P.htime, ← integral_Icc_eq_integral_Ioc] at he
  have hp := hpoint t
  linarith


end PlaneKernelSolutionData
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Gradient and flux-difference bounds for kernel solutions with the same data. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T S : PlaneKernelSolutionData Q)

theorem sameData_forcedSolution (hf : S.f = T.f) (hF : S.F = T.F) (hg : S.g = T.g) :
    IsCoupledWeakSolutionPlane ν a b Q.v 0 (fun _ => k) noLocalCoefficient T.f
      (fun i t => T.F i t + P.carrierFlux S.w i t) T.g S.u S.w := by
  simpa only [forced, hf, hF, hg] using S.forced.solution

theorem sameData_fluxDifference_massEq :
    (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i =>
      (T.F i s + P.carrierFlux T.w i s - (T.F i s + P.carrierFlux S.w i s)).val)) =
      ∫ s in Set.Icc a b, massNormSq ρ P.π
        (fun i => (P.carrierFlux (fun j t => T.w j t - S.w j t) i s).val) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => congrArg (massNormSq ρ P.π)
    (funext (fun i => congrArg Subtype.val (by
      rw [add_sub_add_left_eq_sub]
      exact P.carrierFlux_sub T.w S.w i s))))

theorem sameData_gradient_zero [Nonempty ι]
    (hf : S.f = T.f) (hF : S.F = T.F) (hg : S.g = T.g) :
    (∫ s in Set.Icc a b, massGradNormSq ρ P.π
      (fun i => (T.w i s - S.w i s).val)) = 0 := by
  have hw (i : ι) : MemLp (fun s => T.w i s - S.w i s) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_sub _ 2 (T.w i) (S.w i) (T.solution.2.1 i) (S.solution.2.1 i)
  have hS := T.sameData_forcedSolution S hf hF hg
  have hgrad := Q.forcedFluxDifference_gradient_bound T.f T.forced.F
    (fun i t => T.F i t + P.carrierFlux S.w i t) T.totalFlux_memLp
    (fun i => timeMemLp_pointwise_add _ 2 (T.F i) (P.carrierFlux S.w i)
      (T.hF i) (P.carrierFlux_memLp S.w S.solution.2.1 i)) T.g T.hg T.u S.u T.w S.w
    T.forced.solution hS
  change (∫ s in Set.Icc a b, massGradNormSq ρ P.π
      (fun i => (T.w i s - S.w i s).val)) ≤
    (16 / ν ^ 2) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i =>
      (T.F i s + P.carrierFlux T.w i s - (T.F i s + P.carrierFlux S.w i s)).val)) at hgrad
  rw [T.sameData_fluxDifference_massEq S] at hgrad
  have hflux := P.carrierFlux_mass_integral_le (fun i s => T.w i s - S.w i s) hw
  exact kernelFeedback_gradient_eq_zero ν P.θ _ _ P.diffusivity_pos
    (P.theta_nonneg_of_component (Classical.arbitrary ι)) P.hθ
    (integral_nonneg (fun s => massGradNormSq_nonneg ρ P.π P.hπ _)) hgrad hflux

end PlaneKernelSolutionData
end

/-! Uniqueness of the kernel solution for the same data. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T S : PlaneKernelSolutionData Q)

theorem sameData_kernelFlux_mass_zero [Nonempty ι]
    (hf : S.f = T.f) (hF : S.F = T.F) (hg : S.g = T.g) :
    (∫ s in Set.Icc a b, massNormSq ρ P.π
      (fun i => (P.carrierFlux (fun j t => T.w j t - S.w j t) i s).val)) = 0 := by
  have hw (i : ι) : MemLp (fun s => T.w i s - S.w i s) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_sub _ 2 (T.w i) (S.w i) (T.solution.2.1 i) (S.solution.2.1 i)
  have hb := P.carrierFlux_mass_integral_le (fun i s => T.w i s - S.w i s) hw
  rw [T.sameData_gradient_zero S hf hF hg, mul_zero] at hb
  exact le_antisymm hb (integral_nonneg (fun s => massNormSq_nonneg ρ P.π P.hπ _))

theorem sameData_unique [Nonempty ι]
    (hf : S.f = T.f) (hF : S.F = T.F) (hg : S.g = T.g) :
    ∀ i, ∀ t ∈ Set.Icc a b, T.u i t = S.u i t := by
  have hS := T.sameData_forcedSolution S hf hF hg
  have hF' (i : ι) := timeMemLp_pointwise_add (volume.restrict (Set.Icc a b)) 2
    (T.F i) (P.carrierFlux S.w i) (T.hF i) (P.carrierFlux_memLp S.w S.solution.2.1 i)
  intro i t ht
  have hm := Q.forcedFluxDifference_mass_bound T.f T.forced.F
    (fun i t => T.F i t + P.carrierFlux S.w i t) T.totalFlux_memLp hF'
    T.g T.hg T.u S.u T.w S.w T.forced.solution hS t ht
  change massNormSq ρ P.π (fun i => (T.u i t - S.u i t).val) ≤
    (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i =>
      (T.F i s + P.carrierFlux T.w i s - (T.F i s + P.carrierFlux S.w i s)).val)) at hm
  rw [T.sameData_fluxDifference_massEq S, T.sameData_kernelFlux_mass_zero S hf hF hg,
    mul_zero] at hm
  exact sub_eq_zero.mp (planeCarrier_eq_zero_of_mass_le_zero (fun _ => k) ρ P.radius_pos
    P.π P.hπ (fun i => T.u i t - S.u i t) hm i)

end PlaneKernelSolutionData
end

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Energy budgets of the kernel solution, from the residual flux and value budgets. -/

variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelSolutionData Q)

theorem residualFlux_budget_tendsto :
    Tendsto (fun N => ∫ s in Set.Icc a b, massNormSq ρ P.π
      (fun i => (T.residualFlux N i s).val)) atTop
      (𝓝 (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (T.F i s).val))) := by
  have ht := planeMassNormSq_timeLp_tendsto
    (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
    (volume.restrict (Set.Icc a b)) (fun _ => k) ρ P.π T.residualFlux
    (fun i => (T.hF i).toLp (T.F i)) (T.residualFlux_tendsto : _)
  have he : (∫ s in Set.Icc a b, massNormSq ρ P.π
      (fun i => ((T.hF i).toLp (T.F i) s).val)) =
      ∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (T.F i s).val) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i => (T.hF i).coeFn_toLp)] with s hs
    simp only [hs]
  rw [he] at ht
  exact ht

theorem residualValue_budget_tendsto :
    Tendsto (fun N => ∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π
      (fun i => (T.forced.residualValue N i s).val))) atTop
      (𝓝 (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (T.g i s).val)))) :=
  sourceResidualValue_budget_tendsto P.htime (fun _ => k) k (fun _ => le_rfl)
    Q.v Q.measurable Q.smooth Q.V Q.strain Q.B Q.lam Q.V_nonneg Q.strain_nonneg
    (le_trans zero_le_one Q.B_ge_one) Q.lam_pos Q.bounded Q.jets
    T.forced.highComponent T.g T.hg ρ P.π P.hπ

theorem curve_mass_tendsto (t : Set.Icc a b) :
    Tendsto (fun N => massNormSq ρ P.π
      (fun i => (hilbertBandHk N k (T.forced.curve N t i)).val)) atTop
      (𝓝 (massNormSq ρ P.π (fun i => (T.u i t).val))) := by
  have ht := planeMassNormSq_cutoff_tendsto (fun _ : ι => k) ρ P.π P.hπ (fun i => T.u i t)
  have he (N : ℕ) : (fun i => (hilbertBandHk N k (T.forced.curve N t i)).val) =
      fun i => (planeHkCutoff N k (T.u i t)).val := by
    funext i
    rw [T.forced.curve_component, hilbertBandHk_projection]
    rfl
  simp_rw [he]
  exact ht

theorem curve_gradient_tendsto :
    Tendsto (fun N => ∫ s in Set.Icc a b, massGradNormSq ρ P.π
      (fun i => (hilbertBandHk N (k + 1)
        (extendCurve P.htime (T.forced.curve N) s i)).val)) atTop
      (𝓝 (∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (T.w i s).val))) := by
  have hw (i : ι) : T.forced.highComponent i =ᵐ[volume.restrict (Set.Icc a b)] T.w i :=
    (weakHighCarrierTimeCLM_ae (h := h) (fun _ => k) a b i T.forced.highTime).trans
      (planeCarrierHighTime_readout_ae (h := h) (fun _ => k) a b T.w T.solution.2.1 i)
  have hq (N : ℕ) (i : ι) : (fun t => extendCurve P.htime (T.forced.curve N) t i)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        hilbertProjection N (planeHkValueOperator (k + 1) (T.forced.highComponent i t)) := by
    filter_upwards [T.forced.curve_alignment_ae N i, hw i] with t ht hw
    rw [ht, hw]
    rfl
  have ht := bandCurve_gradient_integral_tendsto_of_alignment (E := h)
    (volume.restrict (Set.Icc a b)) (fun _ => k) ρ P.π
    T.forced.highComponent (fun N => extendCurve P.htime (T.forced.curve N)) hq
  have he : (∫ s in Set.Icc a b, massGradNormSq ρ P.π
      (fun i => (T.forced.highComponent i s).val)) =
      ∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (T.w i s).val) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hw] with s hs
    simp only [hs]
  rw [he] at ht
  exact ht

theorem energy (t : Set.Icc a b) :
    massNormSq ρ P.π (fun i => (T.u i t).val) +
      (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (T.w i s).val)) ≤
    2 * massNormSq ρ P.π (fun i => (T.f i).val) +
      (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (T.F i s).val)) +
      10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (T.g i s).val))) ^ 2 := by
  have hi := T.curve_mass_tendsto ⟨a, le_rfl, P.htime⟩
  simp only [T.solution.2.2.2.1] at hi
  exact le_of_tendsto_of_tendsto'
    ((T.curve_mass_tendsto t).add (T.curve_gradient_tendsto.const_mul (ν / 2)))
    (((hi.const_mul 2).add (T.residualFlux_budget_tendsto.const_mul (8 / ν))).add
      ((T.residualValue_budget_tendsto.pow 2).const_mul 10)) (fun N => T.nativePointEnergy N t)

end PlaneKernelSolutionData

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Existence of a fixed point of the kernel feedback map, hence of the kernel weak solution. -/

variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelFeedbackData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelFeedbackData Q)

theorem exists_feedbackFixedPoint [Nonempty ι] :
    ∃ Z : Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b)), T.feedback Z = Z := by
  let M := planeMassCoercivityBudget (fun _ : ι => k) ρ P.π
  exact exists_weightedFeedback_fixedPoint
    (E := Lp (∀ i, PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b)))
    (weightedTimeReadout (h := h) (a := a) (b := b) (k := k) (P := P)) M
    (planeMassCoercivityBudget_nonneg (fun _ => k) ρ P.π)
    ((fun Z => planeFluxTime_lower_bound (h := h)
      (volume.restrict (Set.Icc a b)) k ρ P.radius_pos P.π P.hπ Z) : _)
    T.feedback T.feedback_weighted_contraction

theorem exists_kernelWeakSolution_of_nonempty [Nonempty ι] :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ k (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (k + 1) (h i))
      (y : ∀ i j (α : Γ i j), ℝ → PlaneHk Set.univ (k + D - 1) (G i j α)),
      IsKernelWeakSolutionPlane ν a b Q.v k D P.B P.C P.S T.f T.F T.g u w y := by
  obtain ⟨Z, hZ⟩ := T.exists_feedbackFixedPoint
  let A := T.forcedCarrier Z
  have he : ∀ i, T.inputFlux Z i =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => T.F i t + P.carrierFlux A.w i t := by
    intro i
    have hz := T.feedback_ae Z
    rw [hZ] at hz
    filter_upwards [hz] with t ht
    exact congrArg (fun q => T.F i t + q i) ht
  exact ⟨A.u, A.w, P.higherInput A.w,
    P.forcedWeakSolution_kernelWeakSolution Q.v Q.smooth Q.V Q.bounded T.f T.F
      (T.inputFlux Z) T.g A.u A.w he A.solution⟩

end PlaneKernelFeedbackData

end AVRegularity.KernelEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
open AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.KernelEnergyPlane

/-! Interval energy bound for homogeneous kernel solutions. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelSolutionData Q)

theorem curve_mass_le (N : ℕ) (t : Set.Icc a b) :
    massNormSq ρ P.π (fun i => (hilbertBandHk N k (T.forced.curve N t i)).val) ≤
      massNormSq ρ P.π (fun i => (T.u i t).val) := by
  unfold massNormSq
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (P.hπ i).le)
  change factorialNormSq ρ (hilbertBandHk N k (T.forced.curve N t i)).val ≤
    factorialNormSq ρ (T.u i t).val
  rw [T.forced.curve_component, hilbertBandHk_projection]
  exact hilbertBandHk_factorialNormSq_le N k ρ (T.u i t)

theorem homogeneous_interval (hF : T.F = 0) (hg : T.g = 0)
    (s t : Set.Icc a b) (hst : (s : ℝ) ≤ t) :
    massNormSq ρ P.π (fun i => (T.u i t).val) +
      (5 * ν / 4) * (∫ r in Set.Ioc (s : ℝ) t, massGradNormSq ρ P.π
        (fun i => (T.w i r).val)) ≤ massNormSq ρ P.π (fun i => (T.u i s).val) := by
  let M := Real.sqrt (2 * massNormSq ρ P.π (fun i => (T.f i).val))
  have henergy (t : Set.Icc a b) := T.energy t
  simp only [hF, hg, Pi.zero_apply,
    planeMassNormSq_zero (fun _ => k) ρ P.π P.hπ, Real.sqrt_zero,
    integral_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at henergy
  have hM (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
      Real.sqrt (massNormSq ρ P.π (fun i =>
        (hilbertBandHk N k (extendCurve P.htime (T.forced.curve N) t i)).val)) ≤ M := by
    apply Real.sqrt_le_sqrt
    rw [extendCurve_eq_of_mem P.htime (T.forced.curve N) ht]
    have hb := T.curve_mass_le N ⟨t, ht⟩
    have hn : 0 ≤ (ν / 2) * (∫ r in Set.Icc a b,
        massGradNormSq ρ P.π (fun i => (T.w i r).val)) :=
      mul_nonneg (div_nonneg P.diffusivity_pos.le (by norm_num))
        (integral_nonneg (fun r => massGradNormSq_nonneg ρ P.π P.hπ _))
    linarith [henergy ⟨t, ht⟩]
  have hf := T.residualFlux_budget_tendsto
  have hv := T.residualValue_budget_tendsto
  simp only [hF, Pi.zero_apply, planeMassNormSq_zero (fun _ => k) ρ P.π P.hπ, integral_zero] at hf
  simp only [hg, Pi.zero_apply, planeMassNormSq_zero (fun _ => k) ρ P.π P.hπ,
    Real.sqrt_zero, integral_zero] at hv
  have hsub : Set.Ioc (s : ℝ) t ⊆ Set.Icc a b :=
    fun r hr => ⟨s.property.1.trans hr.1.le, hr.2.trans t.property.2⟩
  have hw (i : ι) : MemLp (T.w i) 2 (volume.restrict (Set.Ioc (s : ℝ) t)) :=
    (T.solution.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgrad := bandCurve_gradient_tendsto_of_fields (E := h)
    (volume.restrict (Set.Ioc (s : ℝ) t)) (fun _ => k) ρ P.π T.w hw
    (fun N => extendCurve P.htime (T.forced.curve N))
    (fun N i => ae_restrict_of_ae_restrict_of_subset hsub (T.forced.curve_alignment_ae N i))
  apply energy_of_all_positive_losses _ _ _ _
    (integral_nonneg (fun r => massGradNormSq_nonneg ρ P.π P.hπ _))
  intro ε hε
  have hl := (T.curve_mass_tendsto t).add (hgrad.const_mul (5 * ν / 4 - ε))
  have hr := ((T.curve_mass_tendsto s).add (hv.const_mul (2 * M))).add (hf.const_mul (1 / ε))
  simp only [mul_zero, add_zero] at hr
  apply le_of_tendsto_of_tendsto' hl hr
  intro N
  have ht := T.nativeKernelTimeRegularity N
  have hgN (i : ι) : Integrable (T.forced.residualValue N i) (volume.restrict (Set.Icc a b)) :=
    planeResidualValueSource_integrable P.htime (show k ≤ k from le_rfl) Q.v Q.measurable Q.smooth
      Q.V Q.strain Q.B Q.lam Q.V_nonneg Q.strain_nonneg
      (le_trans zero_le_one Q.B_ge_one) Q.lam_pos Q.bounded Q.jets
      (T.forced.highComponent i) (T.g i) N (T.hg i)
  exact Q.kernelProjectedEnergy_perturbed_interval N (T.forced.curve N)
    (fun i => T.residualFlux N i) (T.forced.residualValue N)
    (fun i => Lp.memLp (T.residualFlux N i)) hgN ht.1 ht.2 M ε hε (hM N)
    s s.property t t.property hst

end PlaneKernelSolutionData
end

/-! Componentwise energy budgets for homogeneous kernel solutions. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelSolutionData Q)

theorem curve_component_mass_tendsto (i : ι) (t : Set.Icc a b) :
    Tendsto (fun N => factorialNormSq ρ (hilbertBandHk N k (T.forced.curve N t i)).val)
      atTop (𝓝 (factorialNormSq ρ (T.u i t).val)) := by
  have he (N : ℕ) : hilbertBandHk N k (T.forced.curve N t i) = planeHkCutoff N k (T.u i t) := by
    rw [T.forced.curve_component, hilbertBandHk_projection]
    rfl
  simp_rw [he]
  exact planeFactorial_cutoff_tendsto k ρ (T.u i t)

theorem residualValue_component_budget_zero (hg : T.g = 0) (i : ι) :
    Tendsto (fun N => ∫ r in Set.Icc a b,
      Real.sqrt (factorialNormSq ρ (T.forced.residualValue N i r).val)) atTop (𝓝 0) := by
  have ht := T.residualValue_budget_tendsto
  simp only [hg, Pi.zero_apply, planeMassNormSq_zero (fun _ => k) ρ P.π P.hπ,
    Real.sqrt_zero, integral_zero] at ht
  have hc (N : ℕ) : (∫ r in Set.Icc a b,
      Real.sqrt (factorialNormSq ρ (T.forced.residualValue N i r).val)) ≤
      Real.sqrt (P.π i) * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π
        (fun j => (T.forced.residualValue N j r).val))) := by
    have hint (j : ι) : Integrable (T.forced.residualValue N j) (volume.restrict (Set.Icc a b)) :=
      planeResidualValueSource_integrable P.htime (show k ≤ k from le_rfl) Q.v Q.measurable Q.smooth
        Q.V Q.strain Q.B Q.lam Q.V_nonneg Q.strain_nonneg
        (le_trans zero_le_one Q.B_ge_one) Q.lam_pos Q.bounded Q.jets
        (T.forced.highComponent j) (T.g j) N (T.hg j)
    rw [← integral_const_mul]
    apply integral_mono (planeFactorialRoot_integrable _ k ρ _ (hint i))
      ((planeMassNorm_integrable ρ P.π P.hπ (fun _ => k)
        (T.forced.residualValue N) hint).const_mul _)
    intro r
    have hb := Real.sqrt_le_sqrt (componentFactorial_le_mass ρ P.π P.hπ
      (fun j => (T.forced.residualValue N j r).val) i)
    rwa [Real.sqrt_mul (P.hπ i).le] at hb
  apply squeeze_zero
    (fun N => integral_nonneg (fun r => Real.sqrt_nonneg _)) hc
  simpa only [mul_zero] using ht.const_mul (Real.sqrt (P.π i))

theorem homogeneous_component_interval (hF : T.F = 0) (hg : T.g = 0)
    (i : ι) (s t : Set.Icc a b) (hst : (s : ℝ) ≤ t) :
    factorialNormSq ρ (T.u i t).val +
      (5 * ν / 4) * (∫ r in Set.Ioc (s : ℝ) t, gradFactorialNormSq ρ (T.w i r).val) ≤
    factorialNormSq ρ (T.u i s).val +
      (4 / ν) * (∫ r in Set.Icc a b, factorialNormSq ρ (P.carrierFlux T.w i r).val) := by
  let M := Real.sqrt (P.π i * (2 * massNormSq ρ P.π (fun j => (T.f j).val)))
  have henergy (t : Set.Icc a b) := T.energy t
  simp only [hF, hg, Pi.zero_apply, planeMassNormSq_zero (fun _ => k) ρ P.π P.hπ,
    Real.sqrt_zero, integral_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at henergy
  have hM (N : ℕ) (r : ℝ) (hr : r ∈ Set.Icc a b) :
      Real.sqrt (factorialNormSq ρ (hilbertBandHk N k
        (extendCurve P.htime (T.forced.curve N) r i)).val) ≤ M := by
    apply Real.sqrt_le_sqrt
    rw [extendCurve_eq_of_mem P.htime (T.forced.curve N) hr]
    have hc := componentFactorial_le_mass ρ P.π P.hπ
      (fun j => (hilbertBandHk N k (T.forced.curve N ⟨r, hr⟩ j)).val) i
    have hm := T.curve_mass_le N ⟨r, hr⟩
    have hn : 0 ≤ (ν / 2) * (∫ r in Set.Icc a b,
        massGradNormSq ρ P.π (fun i => (T.w i r).val)) :=
      mul_nonneg (div_nonneg P.diffusivity_pos.le (by norm_num))
        (integral_nonneg (fun r => massGradNormSq_nonneg ρ P.π P.hπ _))
    exact hc.trans (mul_le_mul_of_nonneg_left (hm.trans (by linarith [henergy ⟨r, hr⟩])) (P.hπ i).le)
  have hsub : Set.Ioc (s : ℝ) t ⊆ Set.Icc a b :=
    fun r hr => ⟨s.property.1.trans hr.1.le, hr.2.trans t.property.2⟩
  have hw : MemLp (T.w i) 2 (volume.restrict (Set.Ioc (s : ℝ) t)) :=
    (T.solution.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgrad := planeComponentBand_gradient_tendsto (volume.restrict (Set.Ioc (s : ℝ) t)) k ρ
    (T.w i) hw (fun N r => extendCurve P.htime (T.forced.curve N) r i)
    (fun N => ae_restrict_of_ae_restrict_of_subset hsub (T.forced.curve_alignment_ae N i))
  have hv := T.residualValue_component_budget_zero hg i
  have hl := (T.curve_component_mass_tendsto i t).add (hgrad.const_mul (5 * ν / 4))
  have hr := ((T.curve_component_mass_tendsto i s).add (hv.const_mul (2 * M))).add
    (tendsto_const_nhds (x := (4 / ν) * (∫ r in Set.Icc a b,
      factorialNormSq ρ (P.carrierFlux T.w i r).val)))
  simp only [mul_zero, add_zero] at hr
  apply le_of_tendsto_of_tendsto' hl hr
  intro N
  have ht := T.forced.nativeForcedTimeRegularity N
  have hgN (j : ι) : Integrable (T.forced.residualValue N j) (volume.restrict (Set.Icc a b)) :=
    planeResidualValueSource_integrable P.htime (show k ≤ k from le_rfl) Q.v Q.measurable Q.smooth
      Q.V Q.strain Q.B Q.lam Q.V_nonneg Q.strain_nonneg
      (le_trans zero_le_one Q.B_ge_one) Q.lam_pos Q.bounded Q.jets
      (T.forced.highComponent j) (T.g j) N (T.hg j)
  have he := Q.forcedProjected_row_interval N (T.forced.curve N)
    (fun j => T.forced.residualFlux N j) (T.forced.residualValue N)
    (fun j => Lp.memLp (T.forced.residualFlux N j)) hgN ht.1 ht.2 i M (hM N) s t hst
  have hfN : (∫ r in Set.Icc a b, factorialNormSq ρ (T.forced.residualFlux N i r).val) =
      ∫ r in Set.Icc a b, factorialNormSq ρ (P.carrierFlux T.w i r).val := by
    apply integral_congr_ae
    filter_upwards [T.forced.residualFlux_ae N i] with r hr
    rw [hr]
    change factorialNormSq ρ (T.F i r + P.carrierFlux T.w i r).val = _
    simp only [hF, Pi.zero_apply, zero_add]
  rw [hfN] at he
  exact he

end PlaneKernelSolutionData
end

/-! Componentwise sup bounds for homogeneous kernel solutions. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace PlaneKernelSolutionData
variable {P : PlaneKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D}
  {Q : PlaneKernelDriftData P} (T : PlaneKernelSolutionData Q)

theorem homogeneous_component_sups [Nonempty ι] (hF : T.F = 0) (hg : T.g = 0) :
    (∑ i, ENNReal.ofReal (P.π i)⁻¹ *
      ⨆ t ∈ Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (T.u i t).val)) ≤
      ENNReal.ofReal (massNormSq ρ P.π (fun i => (T.f i).val) +
        2 * ν * P.θ * ∫ r in Set.Icc a b, massGradNormSq ρ P.π (fun i => (T.w i r).val)) ∧
    (∑ i, ENNReal.ofReal (P.π i)⁻¹ *
      ((⨆ t ∈ Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (T.u i t).val)) +
        ENNReal.ofReal (ν * ∫ r in Set.Icc a b, gradFactorialNormSq ρ (T.w i r).val))) ≤
      ENNReal.ofReal (2 * massNormSq ρ P.π (fun i => (T.f i).val)) := by
  classical
  have hν : 0 < ν := P.diffusivity_pos
  let ω := fun i => (P.π i)⁻¹
  let E0 := massNormSq ρ P.π (fun i => (T.f i).val)
  let e0 := fun i => factorialNormSq ρ (T.f i).val
  let C := fun i => (4 / ν) * (∫ r in Set.Icc a b, factorialNormSq ρ (P.carrierFlux T.w i r).val)
  let R := fun i => ∫ r in Set.Icc a b, gradFactorialNormSq ρ (T.w i r).val
  let Rall := ∫ r in Set.Icc a b, massGradNormSq ρ P.π (fun i => (T.w i r).val)
  have hE0 : 0 ≤ E0 := massNormSq_nonneg ρ P.π P.hπ _
  have hω (i : ι) : 0 ≤ ω i := inv_nonneg.mpr (P.hπ i).le
  have he0 (i : ι) : 0 ≤ e0 i := factorialNormSq_nonneg ρ _
  have hC (i : ι) : 0 ≤ C i := mul_nonneg (div_nonneg (by norm_num) P.diffusivity_pos.le)
    (integral_nonneg (fun r => factorialNormSq_nonneg ρ _))
  have hR (i : ι) : 0 ≤ R i := integral_nonneg (fun r => planeGradient_factorial_nonneg k ρ _)
  have hRall : 0 ≤ Rall := integral_nonneg (fun r => massGradNormSq_nonneg ρ P.π P.hπ _)
  have hSup (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
      factorialNormSq ρ (T.u i t).val ≤ e0 i + C i := by
    have he := T.homogeneous_component_interval hF hg i ⟨a, le_rfl, P.htime⟩ ⟨t, ht⟩ ht.1
    simp only [T.solution.2.2.2.1] at he
    have hn : 0 ≤ (5 * ν / 4) * ∫ r in Set.Ioc a t, gradFactorialNormSq ρ (T.w i r).val :=
      mul_nonneg (by have := P.diffusivity_pos; positivity)
        (integral_nonneg (fun r => planeGradient_factorial_nonneg k ρ _))
    linarith
  have hDiss (i : ι) : ν * R i ≤ (4 / 5 : ℝ) * (e0 i + C i) := by
    have he := T.homogeneous_component_interval hF hg i ⟨a, le_rfl, P.htime⟩ ⟨b, P.htime, le_rfl⟩ P.htime
    simp only [T.solution.2.2.2.1, ← integral_Icc_eq_integral_Ioc] at he
    have hn := factorialNormSq_nonneg ρ (T.u i b).val
    linarith
  have hflux := P.carrierFlux_mass_integral_le T.w T.solution.2.1
  have hsplit := planeMassNormSq_integral_split
    (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
    (volume.restrict (Set.Icc a b)) (fun _ => k) ρ P.π (P.carrierFlux T.w)
    (P.carrierFlux_memLp T.w T.solution.2.1)
  have hCE : (∑ i, ω i * C i) = (4 / ν) *
      (∫ r in Set.Icc a b, massNormSq ρ P.π (fun i => (P.carrierFlux T.w i r).val)) := by
    rw [hsplit, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [ω, C]
    ring
  have hCB : (∑ i, ω i * C i) ≤ (4 * ν * P.θ ^ 2) * Rall := by
    rw [hCE]
    have he := mul_le_mul_of_nonneg_left hflux
      (show 0 ≤ (4 / ν : ℝ) from div_nonneg (by norm_num) P.diffusivity_pos.le)
    convert he using 1
    dsimp only [Rall]
    field_simp
  have hsharp := T.homogeneous_interval hF hg ⟨a, le_rfl, P.htime⟩ ⟨b, P.htime, le_rfl⟩ P.htime
  simp only [T.solution.2.2.2.1, ← integral_Icc_eq_integral_Ioc] at hsharp
  have hgrad : ν * Rall ≤ (4 / 5 : ℝ) * E0 := by
    have hn := massNormSq_nonneg ρ P.π P.hπ (fun i => (T.u i b).val)
    linarith
  have hθ0 := P.theta_nonneg_of_component (Classical.arbitrary ι)
  have hθsq : P.θ ^ 2 ≤ (1 / 64 : ℝ) := by nlinarith [P.hθ]
  have hCsmall : (∑ i, ω i * C i) ≤ E0 / 20 := by
    have hb := mul_le_mul_of_nonneg_right hθsq (show 0 ≤ ν * Rall from mul_nonneg P.diffusivity_pos.le hRall)
    nlinarith
  have hCtheta : (∑ i, ω i * C i) ≤ 2 * ν * P.θ * Rall := by
    have hsq : 4 * P.θ ^ 2 ≤ 2 * P.θ := by nlinarith [P.hθ]
    have hb := mul_le_mul_of_nonneg_right hsq (show 0 ≤ ν * Rall from mul_nonneg P.diffusivity_pos.le hRall)
    nlinarith
  let S := fun i => e0 i + C i
  have hS (i : ι) : 0 ≤ S i := add_nonneg (he0 i) (hC i)
  have hsumb : (∑ i, ω i * S i) ≤ E0 + 2 * ν * P.θ * Rall := by
    simp only [S, mul_add, Finset.sum_add_distrib]
    change E0 + (∑ i, ω i * C i) ≤ E0 + 2 * ν * P.θ * Rall
    linarith only [hCtheta]
  have hsumD : (∑ i, ω i * (S i + ν * R i)) ≤ 2 * E0 := by
    have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      mul_le_mul_of_nonneg_left (add_le_add (le_refl (S i)) (hDiss i)) (hω i))
    have he (i : ι) : ω i * (S i + (4 / 5 : ℝ) * (e0 i + C i)) =
        (9 / 5 : ℝ) * (ω i * e0 i) + (9 / 5 : ℝ) * (ω i * C i) := by dsimp only [S]; ring
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum] at hb
    change _ ≤ (9 / 5 : ℝ) * E0 + (9 / 5 : ℝ) * (∑ i, ω i * C i) at hb
    linarith
  refine ⟨?_, ?_⟩
  · exact (componentSup_le_budget (Set.Icc a b) ω S hω hS
      (fun i t => factorialNormSq ρ (T.u i t).val) hSup).trans (ENNReal.ofReal_le_ofReal hsumb)
  · exact (componentSupDissipation_le_budget (Set.Icc a b) ω S (fun i => ν * R i) hω hS
      (fun i => mul_nonneg P.diffusivity_pos.le (hR i))
      (fun i t => factorialNormSq ρ (T.u i t).val) hSup).trans (ENNReal.ofReal_le_ofReal hsumD)

end PlaneKernelSolutionData
end

end AVRegularity.KernelEnergyPlane
end
