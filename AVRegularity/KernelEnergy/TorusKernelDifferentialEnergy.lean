-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Variational.TorusSpatialFluxTimeLp
public import AVRegularity.KernelEnergy.TorusTimeFlux
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
public import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePrimitiveContinuity
import AVRegularity.CoupledEnergy.Variational.ConstantTimeTest
import AVRegularity.CoupledEnergy.Galerkin.PlainClosedTraceIdentity
import AVRegularity.CoupledEnergy.CouplingBounds
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import AVRegularity.CoupledEnergy.Variational.PullbackForm

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! The native homogeneous equation of the difference of two weak
solutions with the same original forcing and initial data. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusWeakSolution_flux_difference_nativeEquation (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F F' : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hF' : ∀ i, MemLp (F' i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))

    (w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (u u' : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hsol' : IsCoupledWeakSolutionTorus ν a b v D K A f F' g u' w')
    (hd : ∀ i, MemLp (fun t => w i t - w' i t) 2 (volume.restrict (Set.Icc a b))) :
    let U := coupledCarrierHighTime K a b (fun i t => w i t - w' i t) hd
    ∀ i, ∀ t ∈ Set.Icc a b, ∀ φ : TorusHk 1 (h i),
      inner ℝ (Galerkin.torusHkValueCLM (u i t - u' i t)) (Galerkin.torusHkValueCLM φ) -
        inner ℝ (Galerkin.torusHkValueCLM (0 : TorusHk (K i) (h i))) (Galerkin.torusHkValueCLM φ) =
          coupledIntegratedRhs K D ν a t v A (fun i r => F i r - F' i r) (fun _ _ => 0) U i φ := by
  dsimp only
  have hnative := torusRawWeakSolution_nativeEquation K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc
    F g hF hg w u f hsol
  have hnative' := torusRawWeakSolution_nativeEquation K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc
    F' g hF' hg w' u' f hsol'
  intro i t ht φ
  rw [coupledCarrierHighTime_sub K a b w w' hsol.2.1 hsol'.2.1 hd]
  rw [coupledIntegratedRhs_sub_flux_forcing K D ν ρ hρ hab ht v hv hvc B hvb A hA hAm hAc
    F F' g hF hF' (coupledCarrierHighTime K a b w hsol.2.1) (coupledCarrierHighTime K a b w' hsol'.2.1) i φ]
  simp only [map_sub, map_zero, inner_sub_left, inner_zero_left, sub_zero]
  linarith [hnative i t ht φ, hnative' i t ht φ]
end

/-! The native homogeneous equation of the difference of two weak
solutions with the same original forcing and initial data. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusWeakSolution_flux_difference (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F F' : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hF' : ∀ i, MemLp (F' i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))

    (w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (u u' : ∀ i, ℝ → TorusHk (K i) (h i)) (f : ∀ i, TorusHk (K i) (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hsol' : IsCoupledWeakSolutionTorus ν a b v D K A f F' g u' w')
 :
    IsCoupledWeakSolutionTorus ν a b v D K A (fun _ => 0) (fun i r => F i r - F' i r) (fun _ _ => 0)
      (fun i t => u i t - u' i t) (fun i t => w i t - w' i t) := by
  have hd : ∀ i, MemLp (fun t => w i t - w' i t) 2 (volume.restrict (Set.Icc a b)) :=
    fun i => timeMemLp_pointwise_sub (volume.restrict (Set.Icc a b)) 2 (w i) (w' i)
      (hsol.2.1 i) (hsol'.2.1 i)
  have hid := torusWeakSolution_flux_difference_nativeEquation K D ν ρ hρ hab v hv hvc B hvb
    A hA hAm hAc F F' g hF hF' hg w w' u u' f hsol hsol' hd
  have hFd : ∀ i, MemLp (fun t => F i t - F' i t) 2 (volume.restrict (Set.Icc a b)) :=
    fun i => timeMemLp_pointwise_sub _ 2 _ _ (hF i) (hF' i)
  have hg0 : ∀ i, Integrable (fun _ : ℝ => (0 : TorusHk (K i) (h i)))
      (volume.restrict (Set.Icc a b)) := fun i => timeIntegrable_zero (E := TorusHk (K i) (h i)) (volume.restrict (Set.Icc a b))
  have hcont : ∀ i, ContinuousOn (fun t => u i t - u' i t) (Set.Icc a b) :=
    fun i => timeContinuousOn_pointwise_sub (u i) (u' i) (Set.Icc a b) (hsol.1 i) (hsol'.1 i)
  apply torusNativeEquation_pack_weakSolution (h := h) K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc
    (fun i t => F i t - F' i t) (fun _ _ => 0) hFd hg0
    (fun i t => w i t - w' i t) (fun i t => u i t - u' i t) (fun _ => 0)
    hcont hd
  · intro i
    filter_upwards [hsol.2.2.1 i, hsol'.2.2.1 i] with t ht ht'
    rw [(truncateTorusHk (E := h i) (Nat.le_succ (K i))).map_sub, ht, ht']
  · intro i
    rw [hsol.2.2.2.1 i, hsol'.2.2.2.1 i, sub_self]
  · exact hid
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Actual finite kernel fluxes are time-L2 and agree with their fixed Bochner operator. -/

variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def finiteFlux (N : ℕ) (y : ℝ → CoupledPlainCoefficients (h := h) N) (i : ι) (t : ℝ) :
    TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  P.clampedAmbientFluxCLM i t (plainHigherSynthesisCLM N (fun _ => k) (y t))

theorem finiteFlux_of_mem (N : ℕ) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    P.finiteFlux N y i t = P.flux t ht (coefficientSynthesis (h := h) (k := k) N (y t)) i := by
  unfold finiteFlux clampedAmbientFluxCLM
  rw [Set.projIcc_of_mem P.htime ht]
  change P.flux t ht (ambientCarrierCLM (h := h) (k := k)
    (plainHigherSynthesisCLM N (fun _ => k) (y t))) i = _
  rw [ambientCarrierCLM_plainSynthesis]

theorem finiteFlux_memLp (N : ℕ) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (hy : Continuous y) (i : ι) :
    MemLp (P.finiteFlux N y i) 2 (volume.restrict (Set.Icc a b)) :=
  AVRegularity.KernelEnergy.memLp_operator_action (volume.restrict (Set.Icc a b))
    (P.clampedAmbientFluxCLM i) (P.clampedAmbientFluxCLM_stronglyMeasurable i)
    P.ambientFluxBudget P.ambientFluxBudget_nonneg (P.clampedAmbientFluxCLM_norm_le i)
    (plainHigherSynthesis_memLp N (fun _ => k) a b hy)

omit [DecidableEq ι] in
theorem kernelTimeFluxCLM_ae (i : ι) (U : CoupledHighTime (h := h) (fun _ => k) a b) :
    P.kernelTimeFluxCLM i U =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => P.clampedAmbientFluxCLM i t (U t) :=
  AVRegularity.KernelEnergy.timeOperatorValue_ae (volume.restrict (Set.Icc a b))
    (P.clampedAmbientFluxCLM i) (P.clampedAmbientFluxCLM_stronglyMeasurable i)
    P.ambientFluxBudget P.ambientFluxBudget_nonneg (P.clampedAmbientFluxCLM_norm_le i) U

theorem kernelTimeFluxCLM_finite_ae (N : ℕ)
    (y : C(Set.Icc a b, CoupledPlainCoefficients (h := h) N)) (i : ι) :
    P.kernelTimeFluxCLM i (plainHigherBochner N (fun _ => k) a b P.htime y) =ᵐ[
      volume.restrict (Set.Icc a b)] P.finiteFlux N (AVenhance.Infra.ODE.extendCurve P.htime y) i := by
  filter_upwards [P.kernelTimeFluxCLM_ae i (plainHigherBochner N (fun _ => k) a b P.htime y),
    plainHigherBochner_readout_ae N (fun _ => k) a b P.htime y] with t ht hr
  rw [ht, hr]
  rfl

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! The zero-local-coupling weak equation with the actual kernel flux. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelODE_as_forced_diffusionDrift (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y) :
    AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (plainFourierMatrix N 0 ν (fun _ => k) v noLocalCoefficient t))
      (fun t => plainSourceCoefficients N (fun _ => k)
        (fun i => F i t + P.finiteFlux N y i t) (fun i => g i t)) initial a b y := by
  intro t ht
  rw [hy t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hmem : s ∈ Set.Icc a b := by
    have hs' : s ∈ Set.Icc a t := by simpa only [Set.uIcc_of_le ht.1] using hs
    exact ⟨hs'.1, hs'.2.trans ht.2⟩
  simp only [AVenhance.Infra.ODE.linearRhs, P.finiteFlux_of_mem N y _ s hmem]
  exact P.projectedMatrix_rhs N v s hmem (y s) (fun i => F i s) (fun i => g i s)

end TorusKernelOperator
end

/-! The zero-local-coupling weak equation with the actual kernel flux. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelLinearRhs_sub_flux_eq (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i)) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    AVenhance.Infra.ODE.linearRhs (fun r => plainMatrixCLM (P.projectedMatrix N v r))
      (fun r => plainSourceCoefficients N (fun _ => k)
        (fun i => F i r - P.finiteFlux N y i r) (fun i => g i r)) y t =
    AVenhance.Infra.ODE.linearRhs
      (fun r => plainMatrixCLM (plainFourierMatrix N 0 ν (fun _ => k) v noLocalCoefficient r))
      (fun r => plainSourceCoefficients N (fun _ => k) (fun i => F i r) (fun i => g i r)) y t := by
  simp only [AVenhance.Infra.ODE.linearRhs, P.finiteFlux_of_mem N y _ t ht]
  have he := P.projectedMatrix_rhs N v t ht (y t)
    (fun i => F i t - P.flux t ht (coefficientSynthesis (h := h) (k := k) N (y t)) i)
    (fun i => g i t)
  simpa only [sub_add_cancel] using he

theorem kernelODE_from_forced_diffusionDrift (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (plainFourierMatrix N 0 ν (fun _ => k) v noLocalCoefficient t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y) :
    AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k)
        (fun i => F i t - P.finiteFlux N y i t) (fun i => g i t)) initial a b y := by
  intro t ht
  rw [hy t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hmem : s ∈ Set.Icc a b := by
    have hs' : s ∈ Set.Icc a t := by simpa only [Set.uIcc_of_le ht.1] using hs
    exact ⟨hs'.1, hs'.2.trans ht.2⟩
  exact (P.kernelLinearRhs_sub_flux_eq N v F g y s hmem).symm

theorem kernelLinearRhs_sub_flux_intervalIntegrable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i)) (y : ℝ → CoupledPlainCoefficients (h := h) N)
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun r => plainMatrixCLM (plainFourierMatrix N 0 ν (fun _ => k) v noLocalCoefficient r))
      (fun r => plainSourceCoefficients N (fun _ => k) (fun i => F i r) (fun i => g i r)) y) volume a b) :
    IntervalIntegrable (AVenhance.Infra.ODE.linearRhs (fun r => plainMatrixCLM (P.projectedMatrix N v r))
      (fun r => plainSourceCoefficients N (fun _ => k)
        (fun i => F i r - P.finiteFlux N y i r) (fun i => g i r)) y) volume a b := by
  apply hint.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have htI : t ∈ Set.Icc a b := by
    rw [Set.uIoc_of_le P.htime] at ht
    exact ⟨ht.1.le, ht.2⟩
  exact (P.kernelLinearRhs_sub_flux_eq N v F g y t htI).symm

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Kernel fluxes pass through the common weak limit against strongly converging tests. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [DecidableEq ι] in
theorem kernelFlux_integral_weak_limit_moving_test {s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (U : ℕ → CoupledHighTime (h := h) (fun _ => k) a b)
    (V : CoupledHighTime (h := h) (fun _ => k) a b) (R : ℝ) (hu : ∀ n, ‖U n‖ ≤ R)
    (hw : ∀ ell : CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V))) (i : ι)
    (z : ℕ → Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume.restrict AVenhance.unitCube))
    (w : Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume.restrict AVenhance.unitCube))
    (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => ∫ r in s..t, ∫ x in AVenhance.unitCube,
      inner ℝ (torusHkValueCLM (P.clampedAmbientFluxCLM i r (U n r)) x) (z n x)) atTop
      (𝓝 (∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (torusHkValueCLM (P.clampedAmbientFluxCLM i r (V r)) x) (w x))) := by
  let μ := volume.restrict (Set.Icc a b)
  let L := ((torusHkValueCLM (E := PiLp 2 (fun _ : Fin 2 => h i)) (K := k)).compLpL 2 μ).comp
    (P.kernelTimeFluxCLM i)
  let B := pullbackInnerCLM
    (constantTimeTestCLM (G := Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2
      (volume.restrict AVenhance.unitCube)) μ (Set.Ioc s t) measurableSet_Ioc (measure_ne_top μ _)) L
  have happly (U : CoupledHighTime (h := h) (fun _ => k) a b)
      (q : Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2 (volume.restrict AVenhance.unitCube)) :
      B q U = ∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (torusHkValueCLM (P.clampedAmbientFluxCLM i r (U r)) x) (q x) := by
    change timeTestIntegralCLM a b s t (fun _ => q) (memLp_const q) (L U) = _
    rw [timeTestIntegralCLM_apply_class hs ht hst]
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : Set.uIoc s t ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le hst]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (ContinuousLinearMap.coeFn_compLpL
        (torusHkValueCLM (E := PiLp 2 (fun _ : Fin 2 => h i)) (K := k)) (P.kernelTimeFluxCLM i U)),
      ae_restrict_of_ae_restrict_of_subset hsub (P.kernelTimeFluxCLM_ae i U)] with r hv hf
    change inner ℝ
      (((torusHkValueCLM (E := PiLp 2 (fun _ : Fin 2 => h i)) (K := k)).compLpL 2 μ
        (P.kernelTimeFluxCLM i U)) r) q = _
    rw [hv, hf, L2.inner_def]
  simpa only [happly] using bilinear_weak_limit_moving_test B U V R hu hw z w hz

end TorusKernelOperator
end

/-! The integrated kernel RHS combines the reused diffusion/drift/forcing
terms with the actual kernel flux, all passing through the common weak limit. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def kernelIntegratedRhs (t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (U : ℝ → CoupledHighHilbert (h := h) (fun _ => k)) (i : ι) (φ : TorusHk 1 (h i)) : ℝ :=
  coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient F g U i φ -
    (∫ r in a..t, ∫ x in AVenhance.unitCube,
      inner ℝ (torusHkValueCLM (P.clampedAmbientFluxCLM i r (U r)) x)
        (torusH1GradientL2CLM (E := h i) φ x))

omit [DecidableEq ι] in
theorem kernelIntegratedRhs_projected_weak_limit (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ B : ℝ, ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : ℕ → CoupledHighTime (h := h) (fun _ => k) a b)
    (V : CoupledHighTime (h := h) (fun _ => k) a b) (Q : ℝ) (hu : ∀ n, ‖U n‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (N : ℕ → ℕ) (hN : StrictMono N) (i : ι) (φ : TorusHk 1 (h i)) :
    Tendsto (fun n => P.kernelIntegratedRhs t v F g (U n) i (galerkinProj (N n) φ)) atTop
      (𝓝 (P.kernelIntegratedRhs t v F g V i φ)) := by
  obtain ⟨B, hb⟩ := hv_bdd
  have hbase := coupledIntegratedRhs_projected_weak_limit (fun _ => k) 0 ν ρ P.radius_pos
    P.htime ht v hv_meas hv B hb noLocalCoefficient
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    (fun r hr i j d => (noLocalOrders (k := k) i j d).elim)
    F g hF hg U V Q hu hw N hN i φ
  have hflux := P.kernelFlux_integral_weak_limit_moving_test ⟨le_rfl, P.htime⟩ ht ht.1
    U V Q hu hw i (fun n => torusH1GradientL2CLM (E := h i) (galerkinProj (N n) φ))
    (torusH1GradientL2CLM (E := h i) φ) ((torusH1Gradient_projected_tendsto φ).comp hN.tendsto_atTop)
  exact hbase.sub hflux

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Continuous closed-time primitives of the actual limit kernel flux. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [DecidableEq ι] in
theorem limitFlux_memLp (U : CoupledHighTime (h := h) (fun _ => k) a b) (i : ι) :
    MemLp (fun r => P.clampedAmbientFluxCLM i r (U r)) 2
      (volume.restrict (Set.Icc a b)) := by
  have hm : MemLp (fun r => P.kernelTimeFluxCLM i U r) 2
      (volume.restrict (Set.Icc a b)) := Lp.memLp _
  exact (memLp_congr_ae (P.kernelTimeFluxCLM_ae i U)).mp hm

omit [DecidableEq ι] in
theorem kernelIntegratedRhs_continuousOn (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) (fun _ => k) a b) (i : ι) (φ : TorusHk 1 (h i)) :
    ContinuousOn (fun t => P.kernelIntegratedRhs t v F g U i φ) (Set.Icc a b) := by
  have hc := coupledIntegratedRhs_continuousOn (fun _ => k) 0 ν ρ P.radius_pos
    P.htime v hv hvc B hvb noLocalCoefficient
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    (fun r hr i j d => (noLocalOrders (k := k) i j d).elim)
    F g hF hg U i φ
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
    (torusFluxSource_test_integrable k a b
      (fun r => P.clampedAmbientFluxCLM i r (U r)) (P.limitFlux_memLp U i) φ)
  have hq : ContinuousOn (fun t => ∫ r in a..t, ∫ x in AVenhance.unitCube,
      inner ℝ (torusHkValueCLM (P.clampedAmbientFluxCLM i r (U r)) x)
        (torusH1GradientL2CLM (E := h i) φ x)) (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le P.htime] using
      intervalIntegral.continuousOn_primitive_interval' hi Set.left_mem_uIcc
  exact hc.sub hq

end TorusKernelOperator
end

/-! The exact Fourier energy identity for the actual kernel right-hand side. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, MeasurableSpace (h i)] in
theorem noLocalFinite (i j : ι) (d : admissibleOrders (fun _ : ι => k) 0 i j) :
    coefficientSeminorm ρ k a b (noLocalCoefficient (h := h) (k := k) i j d) ≠ ⊤ :=
  (noLocalOrders (k := k) i j d).elim

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, MeasurableSpace (h i)] in
theorem noLocalSmooth (t : ℝ) (i j : ι) (d : admissibleOrders (fun _ : ι => k) 0 i j) :
    ContDiff ℝ (k : ℕ) (noLocalCoefficient (h := h) (k := k) i j d t) :=
  (noLocalOrders (k := k) i j d).elim

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, MeasurableSpace (h i)] in
theorem noLocalPeriodic (t : ℝ) (i j : ι) (d : admissibleOrders (fun _ : ι => k) 0 i j) :
    AVenhance.IsZ2Periodic (noLocalCoefficient (h := h) (k := k) i j d t) :=
  (noLocalOrders (k := k) i j d).elim

theorem noLocalFlux_zero (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (x : CoupledPlainCoefficients (h := h) N) (i : ι) :
    plainCouplingFlux N 0 ρ P.radius_pos (fun _ => k) a b noLocalCoefficient
      noLocalFinite t ht (noLocalSmooth t) (noLocalPeriodic t) x i = 0 := by
  let (j : ι) : IsEmpty (admissibleOrders (fun _ : ι => k) 0 i j) :=
    ⟨fun d => noLocalOrders (k := k) i j d⟩
  simp only [plainCouplingFlux, Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero]

theorem kernelRhs_factorial_energy_identity (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
    (x : CoupledPlainCoefficients (h := h) N)
    (F : ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk k (h i)) (i : ι) :
    inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (coupledPlainSynthesis N i k
        (plainMatrixCLM (P.projectedMatrix N v t) x + plainSourceCoefficients N (fun _ => k) F g)).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainSynthesis N i k x).val) =
    inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (g i).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainSynthesis N i k x).val) -
    inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N x i k (v t) hv hvp).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainSynthesis N i k x).val) -
    ν * gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) x).val -
    inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht (coefficientSynthesis (h := h) (k := k) N x) i).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N x i k).val) -
    inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (F i).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N x i k).val) := by
  rw [P.projectedMatrix_rhs N v t ht x F g]
  rw [plainFourierRhs_factorial_energy_identity N 0 ν ρ P.radius_pos (fun _ => k) a b v
    noLocalCoefficient noLocalFinite t ht hv hvp (noLocalSmooth t) (noLocalPeriodic t) x
    (fun i => F i + P.flux t ht (coefficientSynthesis (h := h) (k := k) N x) i) g i]
  rw [P.noLocalFlux_zero N t ht x i]
  have hvzero : (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))).val = 0 := rfl
  have hvadd : (F i + P.flux t ht (coefficientSynthesis (h := h) (k := k) N x) i).val =
      (F i).val + (P.flux t ht (coefficientSynthesis (h := h) (k := k) N x) i).val := rfl
  rw [hvzero, hvadd]
  have hz : AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (0 : JetL2 (volume.restrict AVenhance.unitCube) k (PiLp 2 (fun _ : Fin 2 => h i))) = 0 := by
    apply PiLp.ext
    intro a
    simp [AVRegularity.CoupledEnergy.Variational.factorialWeightedJet]
  simp only [hz, inner_zero_left, sub_zero,
    factorialWeightedJet_add, inner_add_left]
  ring

end TorusKernelOperator
end

/-! Energy absorption with the actual kernel flux bound. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelRhs_mass_energy_le (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
    (c : CoupledPlainCoefficients (h := h) N)
    (F : ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk k (h i)) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    (∑ i, (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (coupledPlainSynthesis N i k
        (plainMatrixCLM (P.projectedMatrix N v t) c + plainSourceCoefficients N (fun _ => k) F g)).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainSynthesis N i k c).val)) +
      (ν / 2) * massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) c).val) ≤
    Real.sqrt (massNormSq ρ P.π (fun i => (g i).val)) *
      Real.sqrt (massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k c).val)) +
      (2 / ν) * massNormSq ρ P.π (fun i => (F i).val) := by
  let U := fun i => (coupledPlainSynthesis N i (k) c).val
  let W := fun i => (coupledPlainSynthesis N i (k + 1) c).val
  let R := massGradNormSq ρ P.π W
  let Gp := ∑ i, (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (g i).val) (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i))
  let Vp := ∑ i, (P.π i)⁻¹ * inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i (k) (v t) hv hvp).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i))
  let Cp := ∑ i, (P.π i)⁻¹ * inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht (coefficientSynthesis (h := h) (k := k) N c) i).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val)
  let Fp := ∑ i, (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (F i).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val)
  have hG : |Gp| ≤ Real.sqrt (massNormSq ρ P.π (fun i => (g i).val)) * Real.sqrt (massNormSq ρ P.π U) :=
    massFactorialPairing_abs_le ρ P.π P.hπ _ _
  have hV : |Vp| ≤ (ν / 4) * R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    change (∑ i, |(P.π i)⁻¹ * inner ℝ
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i (k) (v t) hv hvp).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i))|) ≤ _
    simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (P.hπ _).le)]
    change _ ≤ (ν / 4) * ∑ i, (P.π i)⁻¹ * gradFactorialNormSq ρ (W i)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb := coupledPlainDriftHk_energy_abs_le (le_refl k) N c i ρ αv B lam ν P.radius_pos hα hB hlam P.diffusivity_pos
      hsmall hstrain (v t) hv hvp hd hjets
    rw [← factorialWeightedJet_inner] at hb
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (P.hπ i).le)).trans_eq (by ring)
  have hCoup : |Cp| ≤ (ν / 8) * R :=
    by
    simpa only [Cp, R, W, coefficientSynthesis, ContinuousLinearMap.pi_apply,
      coupledPlainGradientHk_eq_gradientTensor,
      AVRegularity.KernelEnergy.factorialWeightedJet,
      AVRegularity.CoupledEnergy.Variational.factorialWeightedJet] using!
      P.flux_massPairing_abs_le t ht (fun i => coupledPlainSynthesis N i (k + 1) c)
  have hgrad : massNormSq ρ P.π (fun i => (coupledPlainGradientHk N c i (k)).val) = R := by
    unfold massNormSq R massGradNormSq
    apply Finset.sum_congr rfl
    intro i _
    rw [coupledPlainGradientHk_factorialNormSq]
  have hF := massFactorialPairing_abs_le ρ P.π P.hπ (fun i => (F i).val)
    (fun i => (coupledPlainGradientHk N c i (k)).val)
  rw [hgrad] at hF
  have hy := coupledFluxYoung P.diffusivity_pos (Real.sqrt (massNormSq ρ P.π (fun i => (F i).val))) (Real.sqrt R)
  rw [Real.sq_sqrt (massNormSq_nonneg ρ P.π P.hπ _), Real.sq_sqrt (massGradNormSq_nonneg ρ P.π P.hπ W)] at hy
  have hid := fun i => P.kernelRhs_factorial_energy_identity N v t ht hv hvp c F g i
  have he (i : ι) : (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (coupledPlainSynthesis N i (k)
        (plainMatrixCLM (P.projectedMatrix N v t) c + plainSourceCoefficients N (fun _ => k) F g)).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)) =
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (g i).val) (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)) -
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i (k) (v t) hv hvp).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)) - ν * ((P.π i)⁻¹ * gradFactorialNormSq ρ (W i)) -
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht (coefficientSynthesis (h := h) (k := k) N c) i).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val) -
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (F i).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val) := by
    dsimp only [U, W]
    rw [hid i]
    ring
  have hs := congrArg (fun z : ι → ℝ => ∑ i, z i) (funext he)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  change _ = Gp - Vp - ν * R - Cp - Fp at hs
  change _ + (ν / 2) * R ≤ _
  rw [hs]
  have hnegV := neg_le_abs Vp
  have hnegC := neg_le_abs Cp
  have hnegF := neg_le_abs Fp
  have hposG := le_abs_self Gp
  change |Fp| ≤ _ at hF
  change _ ≤ (ν / 8) * R + (2 / ν) * massNormSq ρ P.π (fun i => (F i).val) at hy
  dsimp only [U] at hG
  linarith

end TorusKernelOperator
end

/-! Energy absorption with the actual kernel flux bound. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelRhs_mass_unabsorbed_le (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
    (c : CoupledPlainCoefficients (h := h) N)
    (F : ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk k (h i)) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    (∑ i, (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (coupledPlainSynthesis N i k
        (plainMatrixCLM (P.projectedMatrix N v t) c + plainSourceCoefficients N (fun _ => k) F g)).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainSynthesis N i k c).val)) +
      (5 * ν / 8) * massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) c).val) ≤
    Real.sqrt (massNormSq ρ P.π (fun i => (g i).val)) *
      Real.sqrt (massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k c).val)) +
      Real.sqrt (massNormSq ρ P.π (fun i => (F i).val)) *
        Real.sqrt (massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) c).val)) := by
  let U := fun i => (coupledPlainSynthesis N i (k) c).val
  let W := fun i => (coupledPlainSynthesis N i (k + 1) c).val
  let R := massGradNormSq ρ P.π W
  let Gp := ∑ i, (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (g i).val) (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i))
  let Vp := ∑ i, (P.π i)⁻¹ * inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i (k) (v t) hv hvp).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i))
  let Cp := ∑ i, (P.π i)⁻¹ * inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht (coefficientSynthesis (h := h) (k := k) N c) i).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val)
  let Fp := ∑ i, (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (F i).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val)
  have hG : |Gp| ≤ Real.sqrt (massNormSq ρ P.π (fun i => (g i).val)) * Real.sqrt (massNormSq ρ P.π U) :=
    massFactorialPairing_abs_le ρ P.π P.hπ _ _
  have hV : |Vp| ≤ (ν / 4) * R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    change (∑ i, |(P.π i)⁻¹ * inner ℝ
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i (k) (v t) hv hvp).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i))|) ≤ _
    simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (P.hπ _).le)]
    change _ ≤ (ν / 4) * ∑ i, (P.π i)⁻¹ * gradFactorialNormSq ρ (W i)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb := coupledPlainDriftHk_energy_abs_le (le_refl k) N c i ρ αv B lam ν P.radius_pos hα hB hlam P.diffusivity_pos
      hsmall hstrain (v t) hv hvp hd hjets
    rw [← factorialWeightedJet_inner] at hb
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (P.hπ i).le)).trans_eq (by ring)
  have hCoup : |Cp| ≤ (ν / 8) * R :=
    by
    simpa only [Cp, R, W, coefficientSynthesis, ContinuousLinearMap.pi_apply,
      coupledPlainGradientHk_eq_gradientTensor,
      AVRegularity.KernelEnergy.factorialWeightedJet,
      AVRegularity.CoupledEnergy.Variational.factorialWeightedJet] using!
      P.flux_massPairing_abs_le t ht (fun i => coupledPlainSynthesis N i (k + 1) c)
  have hgrad : massNormSq ρ P.π (fun i => (coupledPlainGradientHk N c i (k)).val) = R := by
    unfold massNormSq R massGradNormSq
    apply Finset.sum_congr rfl
    intro i _
    rw [coupledPlainGradientHk_factorialNormSq]
  have hF := massFactorialPairing_abs_le ρ P.π P.hπ (fun i => (F i).val)
    (fun i => (coupledPlainGradientHk N c i (k)).val)
  rw [hgrad] at hF
  have hid := fun i => P.kernelRhs_factorial_energy_identity N v t ht hv hvp c F g i
  have he (i : ι) : (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (coupledPlainSynthesis N i (k)
        (plainMatrixCLM (P.projectedMatrix N v t) c + plainSourceCoefficients N (fun _ => k) F g)).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)) =
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (g i).val) (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)) -
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i (k) (v t) hv hvp).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)) - ν * ((P.π i)⁻¹ * gradFactorialNormSq ρ (W i)) -
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht (coefficientSynthesis (h := h) (k := k) N c) i).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val) -
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (F i).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val) := by
    dsimp only [U, W]
    rw [hid i]
    ring
  have hs := congrArg (fun z : ι → ℝ => ∑ i, z i) (funext he)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  change _ = Gp - Vp - ν * R - Cp - Fp at hs
  change _ + (5 * ν / 8) * R ≤
    Real.sqrt (massNormSq ρ P.π (fun i => (g i).val)) * Real.sqrt (massNormSq ρ P.π U) +
      Real.sqrt (massNormSq ρ P.π (fun i => (F i).val)) * Real.sqrt R
  rw [hs]
  have hnegV := neg_le_abs Vp
  have hnegC := neg_le_abs Cp
  have hnegF := neg_le_abs Fp
  have hposG := le_abs_self Gp
  change |Fp| ≤ _ at hF
  linarith

end TorusKernelOperator
end

/-! Energy absorption with the actual kernel flux bound. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelRhs_mass_homogeneous_le (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
    (c : CoupledPlainCoefficients (h := h) N)
    (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    (∑ i, (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (coupledPlainSynthesis N i k
        (plainMatrixCLM (P.projectedMatrix N v t) c + plainSourceCoefficients N (fun _ => k) (fun _ => 0) (fun _ => 0))).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainSynthesis N i k c).val)) +
      (5 * ν / 8) * massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) c).val) ≤ 0 := by
  let U := fun i => (coupledPlainSynthesis N i (k) c).val
  let W := fun i => (coupledPlainSynthesis N i (k + 1) c).val
  let R := massGradNormSq ρ P.π W
  let Vp := ∑ i, (P.π i)⁻¹ * inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i (k) (v t) hv hvp).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i))
  let Cp := ∑ i, (P.π i)⁻¹ * inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht (coefficientSynthesis (h := h) (k := k) N c) i).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val)
  have hV : |Vp| ≤ (ν / 4) * R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    change (∑ i, |(P.π i)⁻¹ * inner ℝ
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i (k) (v t) hv hvp).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i))|) ≤ _
    simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr (P.hπ _).le)]
    change _ ≤ (ν / 4) * ∑ i, (P.π i)⁻¹ * gradFactorialNormSq ρ (W i)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb := coupledPlainDriftHk_energy_abs_le (le_refl k) N c i ρ αv B lam ν P.radius_pos hα hB hlam P.diffusivity_pos
      hsmall hstrain (v t) hv hvp hd hjets
    rw [← factorialWeightedJet_inner] at hb
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (P.hπ i).le)).trans_eq (by ring)
  have hCoup : |Cp| ≤ (ν / 8) * R :=
    by
    simpa only [Cp, R, W, coefficientSynthesis, ContinuousLinearMap.pi_apply,
      coupledPlainGradientHk_eq_gradientTensor,
      AVRegularity.KernelEnergy.factorialWeightedJet,
      AVRegularity.CoupledEnergy.Variational.factorialWeightedJet] using!
      P.flux_massPairing_abs_le t ht (fun i => coupledPlainSynthesis N i (k + 1) c)
  have hid := fun i => P.kernelRhs_factorial_energy_identity N v t ht hv hvp c (fun _ => 0) (fun _ => 0) i
  have he (i : ι) : (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (coupledPlainSynthesis N i (k)
        (plainMatrixCLM (P.projectedMatrix N v t) c + plainSourceCoefficients N (fun _ => k) (fun _ => 0) (fun _ => 0))).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)) =
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (0 : TorusHk k (h i)).val) (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)) -
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i (k) (v t) hv hvp).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)) - ν * ((P.π i)⁻¹ * gradFactorialNormSq ρ (W i)) -
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (P.flux t ht (coefficientSynthesis (h := h) (k := k) N c) i).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val) -
      (P.π i)⁻¹ * inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i (k)).val) := by
    dsimp only [U, W]
    rw [hid i]
    ring
  have hs := congrArg (fun z : ι → ℝ => ∑ i, z i) (funext he)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  simp only [ZeroMemClass.coe_zero, ← factorialWeightedJetCLM_apply, map_zero, inner_zero_left, mul_zero,
    Finset.sum_const_zero, zero_sub, sub_zero] at hs
  change _ = -Vp - ν * R - Cp at hs
  simp only [factorialWeightedJetCLM_apply] at hs
  change _ + (5 * ν / 8) * R ≤ 0
  rw [hs]
  have hnegV := neg_le_abs Vp
  have hnegC := neg_le_abs Cp
  linarith

end TorusKernelOperator
end

/-! Continuous closed-time primitives of the actual limit kernel flux. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def higherInput (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (i j : ι) (α : Γ i j) (t : ℝ) : TorusHk (k + D - 1) (G i j α) :=
  clampedRegularizedInputCLM ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) P.radius_pos P.htime t (w j t)

omit [DecidableEq ι] in
theorem higherInput_of_mem (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (i j : ι) (α : Γ i j) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    P.higherInput w i j α t = P.lift t ht (fun j => w j t) i j α := by
  apply TorusHk.ext_value
  change (torusRegularizedInput ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) (Set.projIcc a b P.htime t)
    (Set.projIcc a b P.htime t).property (w j t)).val (valueIndex2 (k + D - 1)) = _
  rw [torusRegularizedInput_value, P.lift_value]
  simp only [Set.projIcc_of_mem P.htime ht]

omit [DecidableEq ι] in
theorem higherInput_memLp (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i j : ι) (α : Γ i j) :
    MemLp (P.higherInput w i j α) 2 (volume.restrict (Set.Icc a b)) :=
  clampedRegularizedInput_memLp ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) P.radius_pos P.htime (w j) (hw j)

omit [DecidableEq ι] in
theorem higherInput_value_ae (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (i j : ι) (α : Γ i j) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (P.higherInput w i j α t).val (valueIndex2 (k + D - 1)) =
      P.S i j α t ((P.C i j α).compLp ((w j t).val (valueIndex2 (k + 1)))) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [P.higherInput_of_mem w i j α t ht]
  exact P.lift_value t ht (fun j => w j t) i j α

end TorusKernelOperator
end

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_mass_deriv_energy_le
    (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y)
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv (fun s => massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y s)).val)) t +
        ν * massGradNormSq ρ P.π (fun i => (coupledPlainSynthesis N i (k + 1) (y t)).val) ≤
      2 * Real.sqrt (massNormSq ρ P.π (fun i => (g i t).val)) *
        Real.sqrt (massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y t)).val)) +
        (4 / ν) * massNormSq ρ P.π (fun i => (F i t).val) := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [plainODE_mass_ae_deriv N (fun _ => k) ρ P.π P.htime
    (P.projectedMatrix N v)
    (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t))
    y initial hy hint] with t ht
  intro hmem
  rw [(ht hmem).deriv]
  have hpoint := P.kernelRhs_mass_energy_le N v t hmem (hv t hmem) (hvp t hmem)
    (y t) (fun i => F i t) (fun i => g i t) αv B lam hα hB hlam
    hsmall hstrain (hd t hmem) (hjets t hmem)
  convert mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end
