-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence
import AVRegularity.CoupledEnergy.Galerkin.PlainWeakSolutionExistence
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
public import AVRegularity.Statements.Intermediate.KernelEnergy.KernelWeakSolutionTorus
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

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
theorem kernelForcedWeakSolution_residualComponentEnergy
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (M ε : ℝ) (hM0 : 0 ≤ M) (hε : 0 < ε)
    (hM : ∀ t ∈ Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (u i t).val)) ≤ M)
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f F g u w) :
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + P.diffusionResidual z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
    ∃ y : ℝ → CoupledPlainCoefficients (h := h) N,
      Continuous y ∧ (∀ t ∈ Set.Icc a b, y t = plainInitialCoefficients N (fun _ => k) (fun i => u i t)) ∧
      ∀ i, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
        factorialNormSq ρ (galerkinProj N (u i t)).val +
          (3 * ν / 2 - ε) * (∫ r in Set.Ioc s t, gradFactorialNormSq ρ (galerkinProj N (w i r)).val) ≤
        factorialNormSq ρ (galerkinProj N (u i s)).val +
          2 * (∫ r in Set.Icc a b, |P.carrierPair (fun j τ => coupledPlainSynthesis N j (k + 1) (y τ)) i r|) +
          2 * P.π i * M * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (Rg i r).val))) +
          (P.π i / ε) * (∫ r in Set.Icc a b, massNormSq ρ P.π
            (fun i => (RF i r - P.finiteFlux N y i r).val)) := by
  dsimp only
  let z := fun i t => w i t - galerkinProj N (w i t)
  let RF := fun i t => F i t + P.diffusionResidual z i t
  let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
  obtain ⟨y, hycont, hy, hRFnew, hRg, hkODE, hkint⟩ :=
    P.kernelForcedWeakSolution_residualODE N v hv hvp F g hv_meas V hV hvb T hT w u f hF hg hsol
  have hMy (t : ℝ) (ht : t ∈ Set.Icc a b) :
      Real.sqrt (massNormSq ρ P.π (fun i => (coupledPlainSynthesis N i k (y t)).val)) ≤ M := by
    rw [hy t ht]
    exact (Real.sqrt_le_sqrt (plainInitialCoefficients_mass_le N (fun _ => k) ρ P.π P.hπ
      (fun i => u i t))).trans (hM t ht)
  have he (i : ι) := P.kernelODE_component_perturbed_interval_le N v hv hvp
    (fun i t => RF i t - P.finiteFlux N y i t) Rg αv B lam hα hB hlam hsmall hstrain
    hd hjets i y (plainInitialCoefficients N (fun _ => k) f) hkODE hycont M ε hM0 hε hMy hRFnew hRg hkint
  have hlower (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ι) :
      coupledPlainSynthesis N i (k) (y t) = galerkinProj N (u i t) := by
    rw [hy t ht]
    exact plainInitialCoefficients_synthesis N (fun _ => k) (fun j => u j t) i
  have hhigher : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ i,
      coupledPlainSynthesis N i (k + 1) (y s) = galerkinProj N (w i s) := by
    filter_upwards [ae_all_iff.mpr hsol.2.2.1, ae_restrict_mem measurableSet_Icc] with s hs hsI
    intro i
    rw [hy s hsI]
    have he : (fun j => u j s) = (fun j => truncateTorusHk (Nat.le_succ (k)) (w j s)) :=
      funext (fun j => (hs j).symm)
    rw [he]
    exact plainInitialCoefficients_higher_synthesis N (fun _ => k) (fun j => w j s) i
  refine ⟨y, hycont, hy, ?_⟩
  intro i s hs t ht hst
  have hsub : Set.Ioc s t ⊆ Set.Icc a b := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  have hintEq : (∫ r in Set.Ioc s t, gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) (y r)).val) =
      ∫ r in Set.Ioc s t, gradFactorialNormSq ρ (galerkinProj N (w i r)).val := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hhigher] with r hr
    simp only [hr]
  have he := he i s hs t ht hst
  simp only [hlower t ht, hlower s hs, hintEq] at he
  exact he

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
theorem kernelForcedWeakSolution_projectedComponentEnergy
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (M ε : ℝ) (hM0 : 0 ≤ M) (hε : 0 < ε)
    (hM : ∀ t ∈ Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (u i t).val)) ≤ M)
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f (fun i t => F i t + P.carrierFlux w i t) g u w) :
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + P.carrierFlux z i t + P.diffusionResidual z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
    ∀ i, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      factorialNormSq ρ (galerkinProj N (u i t)).val +
        (3 * ν / 2 - ε) * (∫ r in Set.Ioc s t, gradFactorialNormSq ρ (galerkinProj N (w i r)).val) ≤
      factorialNormSq ρ (galerkinProj N (u i s)).val +
        2 * (∫ r in Set.Icc a b, |P.carrierPair (fun j τ => galerkinProj N (w j τ)) i r|) +
        2 * P.π i * M * (∫ r in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (Rg i r).val))) +
        (P.π i / ε) * (∫ r in Set.Icc a b, massNormSq ρ P.π (fun i => (RF i r).val)) := by
  dsimp only
  let z := fun i t => w i t - galerkinProj N (w i t)
  let Ftotal := fun i t => F i t + P.carrierFlux w i t
  have hFt (i : ι) : MemLp (Ftotal i) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add _ 2 (F i) (P.carrierFlux w i) (hF i)
      (P.carrierFlux_memLp_of_family w hsol.2.1 i)
  obtain ⟨y, _, hy, he⟩ := P.kernelForcedWeakSolution_residualComponentEnergy N v hv hvp Ftotal g
    αv B lam hα hB hlam hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hFt hg M ε hM0 hε hM hsol
  have hflux (i : ι) := P.finiteFlux_eq_projectedCarrierFlux_ae N y u w hy hsol.2.2.1 i
  have hintEq :
      (∫ s in Set.Icc a b, massNormSq ρ P.π
        (fun i => ((F i s + P.carrierFlux w i s) +
          P.diffusionResidual z i s - P.finiteFlux N y i s).val)) =
      (∫ s in Set.Icc a b, massNormSq ρ P.π
        (fun i => (F i s + P.carrierFlux z i s +
          P.diffusionResidual z i s).val)) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hflux] with s hs
    apply congrArg (massNormSq ρ P.π)
    funext i
    rw [hs i, P.carrierFlux_sub w (fun j t => galerkinProj N (w j t)) i s]
    congr 1
    abel
  intro i r hr t ht hrt
  have hp : (∫ s in Set.Icc a b, |P.carrierPair (fun j τ => coupledPlainSynthesis N j (k + 1) (y τ)) i s|) =
      ∫ s in Set.Icc a b, |P.carrierPair (fun j τ => galerkinProj N (w j τ)) i s| := by
    apply integral_congr_ae
    filter_upwards [P.carrierPair_synthesis_projected_ae N y u w hy hsol.2.2.1 i] with s hs
    rw [hs]
  have h := he i r hr t ht hrt
  dsimp only [Ftotal] at h
  rw [hintEq, hp] at h
  exact h

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

variable (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))



include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_homogeneous_interval
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) + P.carrierFlux w i t)
      (fun _ _ => 0) u w) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      massNormSq ρ P.π (fun i => (u i t).val) +
        (5 * ν / 4) * (∫ r in Set.Ioc s t, massGradNormSq ρ P.π (fun i => (w i r).val)) ≤
      massNormSq ρ P.π (fun i => (u i s).val) := by
  let F0 := fun i (_t : ℝ) => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  let g0 := fun i (_t : ℝ) => (0 : TorusHk k (h i))
  have hF0 (i : ι) : MemLp (F0 i) 2 (volume.restrict (Set.Icc a b)) := timeMemLp_zero _ 2
  have hg0 (i : ι) : Integrable (g0 i) (volume.restrict (Set.Icc a b)) := timeIntegrable_zero _
  have henergy := P.kernelForcedWeakSolution_energy v hv hvp F0 g0 αv B lam hα hB hlam
    hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hF0 hg0 hsol
  simp only [F0, g0, torusMassNormSq_zero (fun _ => k) ρ P.π P.hπ,
    Real.sqrt_zero, integral_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at henergy
  let M := Real.sqrt (2 * massNormSq ρ P.π (fun i => (f i).val))
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hM (t : ℝ) (ht : t ∈ Set.Icc a b) :
      Real.sqrt (massNormSq ρ P.π (fun i => (u i t).val)) ≤ M := by
    apply Real.sqrt_le_sqrt
    have hr : 0 ≤ (ν / 2) * (∫ r in Set.Icc a b,
        massGradNormSq ρ P.π (fun i => (w i r).val)) :=
      mul_nonneg (div_nonneg P.diffusivity_pos.le (by norm_num)) (integral_nonneg (fun r => massGradNormSq_nonneg ρ P.π P.hπ _))
    linarith [henergy t ht]
  have hflux := P.kernelResidualFlux_mass_limit F0 hF0 w hsol.2.1
  have hvalue := plainResidualValue_mass_limit (fun _ => k) ρ P.radius_pos a b P.htime
    v hv_meas hv hvp V hV hvb T hT g0 w hsol.2.1 hg0 P.π P.hπ
  simp only [F0, torusMassNormSq_zero (fun _ => k) ρ P.π P.hπ, integral_zero] at hflux
  simp only [g0, torusMassNormSq_zero (fun _ => k) ρ P.π P.hπ, Real.sqrt_zero, integral_zero] at hvalue
  intro s hs t ht hst
  have hsub : Set.Icc s t ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 ht.2
  have hwst (i : ι) : MemLp (w i) 2 (volume.restrict (Set.Icc s t)) :=
    (hsol.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgrad := galerkinProj_massGradNormSq_integral_tendsto (fun _ => k) s t ρ P.π w hwst
  simp only [integral_Icc_eq_integral_Ioc] at hgrad
  have htime := galerkinProj_massNormSq_tendsto (fun _ => k) ρ P.π P.hπ (fun i => u i t)
  have hstart := galerkinProj_massNormSq_tendsto (fun _ => k) ρ P.π P.hπ (fun i => u i s)
  apply energy_of_all_positive_losses _ _ _ _
    (integral_nonneg (fun r => massGradNormSq_nonneg ρ P.π P.hπ _))
  intro ε hε
  have hleft := htime.add (hgrad.const_mul (5 * ν / 4 - ε))
  have hright := (hstart.add (hvalue.const_mul (2 * M))).add (hflux.const_mul (1 / ε))
  simp only [mul_zero, add_zero] at hright
  exact le_of_tendsto_of_tendsto' hleft hright (fun N =>
    P.kernelForcedWeakSolution_projectedPerturbedEnergy N v hv hvp F0 g0 αv B lam hα hB hlam
      hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hF0 hg0 M ε hM0 hε hM hsol s hs t ht hst)

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



omit [DecidableEq ι] in
theorem kernelForcedWeakSolution_difference
    (v : ℝ → Vec 2 → Vec 2)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (V : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (f : ∀ i, TorusHk k (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u u' : ∀ i, ℝ → TorusHk k (h i))
    (w w' : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w)
    (hsol' : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w' i t) g u' w') :
    IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient (fun _ => 0)
      (fun i t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) +
        P.carrierFlux (fun j s => w j s - w' j s) i t) (fun _ _ => 0)
      (fun i t => u i t - u' i t) (fun i t => w i t - w' i t) := by
  have hFt (i : ι) : MemLp (fun t => F i t + P.carrierFlux w i t) 2
      (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add _ 2 _ _ (hF i) (P.carrierFlux_memLp_of_family w hsol.2.1 i)
  have hFt' (i : ι) : MemLp (fun t => F i t + P.carrierFlux w' i t) 2
      (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add _ 2 _ _ (hF i) (P.carrierFlux_memLp_of_family w' hsol'.2.1 i)
  have hd := torusWeakSolution_flux_difference (fun _ => k) 0 ν ρ P.radius_pos P.htime v hv_meas
    (fun t ht => (hv t ht).continuous) V hvb noLocalCoefficient noLocalSeminorm noLocalMeasurable
    (fun t ht i j d => noLocalSmoothOnInterval t ht i j d)
    (fun i t => F i t + P.carrierFlux w i t) (fun i t => F i t + P.carrierFlux w' i t)
    g hFt hFt' hg w w' u u' f hsol hsol'
  have he : (fun i t => F i t + P.carrierFlux w i t - (F i t + P.carrierFlux w' i t)) =
      (fun i t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) +
        P.carrierFlux (fun j s => w j s - w' j s) i t) := by
    funext i t
    rw [zero_add, P.carrierFlux_sub]
    abel
  rw [he] at hd
  exact hd

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Hilbert weak compactness and closed Sobolev graph readout. -/

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

variable (v : ℝ → Vec 2 → Vec 2)
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
theorem kernelFourier_exists_forcedWeakSolution
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i)),
      IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
        (fun i r => F i r + P.carrierFlux w i r) g u w ∧
      (∀ i, MemLp (P.carrierFlux w i) 2 (volume.restrict (Set.Icc a b))) := by
  obtain ⟨U, u, hmem, hgraph, hinit, _, hid, _, _, huw, hstrong⟩ :=
    P.kernelFourier_exists_strongTrace v hv hvp F g αv B lam hα hB hlam hsmall hstrain hd hjets
      hv_bdd hv_meas f hF hg
  let w := fun i t => coupledHighGraphReadout (fun _ => k) i (U t)
  have hQ (i : ι) : MemLp (P.carrierFlux w i) 2 (volume.restrict (Set.Icc a b)) :=
    P.carrierFlux_memLp U w hgraph i
  have hforce (i : ι) : MemLp (fun r => F i r + P.carrierFlux w i r) 2
      (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add (volume.restrict (Set.Icc a b)) 2 (F i) (P.carrierFlux w i) (hF i) (hQ i)
  have heq (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (φ : TorusHk 1 (h i)) :
      inner ℝ (torusHkValueCLM (u i t)) (torusHkValueCLM φ) -
        inner ℝ (torusHkValueCLM (f i)) (torusHkValueCLM φ) =
      coupledIntegratedRhs (fun _ => k) 0 ν a t v noLocalCoefficient
        (fun i r => F i r + P.carrierFlux w i r) g U i φ := by
    rw [P.kernelIntegratedRhs_eq_forcedRhs t ht v F g hF U w hgraph i φ]
    exact hid i t ht φ
  obtain ⟨V, hV⟩ := hv_bdd
  have hidentity := torusNativeEquation_implies_rawWeakIdentity (fun _ => k) 0 ν ρ P.radius_pos
    P.htime v hv_meas (fun t ht => (hv t ht).continuous) V hV noLocalCoefficient
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
    (fun t ht i j d => (noLocalOrders (k := k) i j d).elim)
    (fun i r => F i r + P.carrierFlux w i r) g hforce hg U w hgraph u f heq
  refine ⟨u, w, ⟨hstrong, hmem, ?_, hinit, ?_⟩, hQ⟩
  · intro i
    exact huw.mono (fun t ht => (ht i).symm)
  · intro i t ht φ
    simpa only [torusRawCouplingFlux] using! hidentity i t ht φ

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

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

variable (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))



include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_component_interval
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) + P.carrierFlux w i t)
      (fun _ _ => 0) u w) :
    ∀ i, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      factorialNormSq ρ (u i t).val +
        (3 * ν / 2) * (∫ r in Set.Ioc s t, gradFactorialNormSq ρ (w i r).val) ≤
      factorialNormSq ρ (u i s).val + 2 * ∫ r in Set.Icc a b, |P.carrierPair w i r| := by
  let F0 := fun i (_t : ℝ) => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  let g0 := fun i (_t : ℝ) => (0 : TorusHk k (h i))
  have hF0 (i : ι) : MemLp (F0 i) 2 (volume.restrict (Set.Icc a b)) := timeMemLp_zero _ 2
  have hg0 (i : ι) : Integrable (g0 i) (volume.restrict (Set.Icc a b)) := timeIntegrable_zero _
  have henergy := P.kernelForcedWeakSolution_energy v hv hvp F0 g0 αv B lam hα hB hlam
    hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hF0 hg0 hsol
  simp only [F0, g0, torusMassNormSq_zero (fun _ => k) ρ P.π P.hπ,
    Real.sqrt_zero, integral_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at henergy
  let M := Real.sqrt (2 * massNormSq ρ P.π (fun i => (f i).val))
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hM (t : ℝ) (ht : t ∈ Set.Icc a b) :
      Real.sqrt (massNormSq ρ P.π (fun i => (u i t).val)) ≤ M := by
    apply Real.sqrt_le_sqrt
    have hr : 0 ≤ (ν / 2) * (∫ r in Set.Icc a b,
        massGradNormSq ρ P.π (fun i => (w i r).val)) :=
      mul_nonneg (div_nonneg P.diffusivity_pos.le (by norm_num)) (integral_nonneg (fun r => massGradNormSq_nonneg ρ P.π P.hπ _))
    linarith [henergy t ht]
  have hflux := P.kernelResidualFlux_mass_limit F0 hF0 w hsol.2.1
  have hvalue := plainResidualValue_mass_limit (fun _ => k) ρ P.radius_pos a b P.htime
    v hv_meas hv hvp V hV hvb T hT g0 w hsol.2.1 hg0 P.π P.hπ
  simp only [F0, torusMassNormSq_zero (fun _ => k) ρ P.π P.hπ, integral_zero] at hflux
  simp only [g0, torusMassNormSq_zero (fun _ => k) ρ P.π P.hπ, Real.sqrt_zero, integral_zero] at hvalue
  intro i s hs t ht hst
  have hsub : Set.Icc s t ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 ht.2
  have hwst (i : ι) : MemLp (w i) 2 (volume.restrict (Set.Icc s t)) :=
    (hsol.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgrad := galerkinProj_gradFactorial_integral_tendsto k s t ρ (w i) (hwst i)
  simp only [integral_Icc_eq_integral_Ioc] at hgrad
  have htime := galerkinProj_factorialNormSq_tendsto k ρ (u i t)
  have hstart := galerkinProj_factorialNormSq_tendsto k ρ (u i s)
  have hpair := P.carrierPair_projected_abs_integral_tendsto w hsol.2.1 i
  apply energy_of_all_positive_losses _ _ _ _
    (integral_nonneg (fun r => by
      rw [← torusGradientTensor_factorialNormSq]
      exact factorialNormSq_nonneg ρ _))
  intro ε hε
  have hleft := htime.add (hgrad.const_mul (3 * ν / 2 - ε))
  have hright := ((hstart.add (hpair.const_mul 2)).add (hvalue.const_mul (2 * P.π i * M))).add (hflux.const_mul (P.π i / ε))
  simp only [mul_zero, add_zero] at hright
  exact le_of_tendsto_of_tendsto' hleft hright (fun N =>
    P.kernelForcedWeakSolution_projectedComponentEnergy N v hv hvp F0 g0 αv B lam hα hB hlam
      hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hF0 hg0 M ε hM0 hε hM hsol i s hs t ht hst)

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

variable (v : ℝ → Vec 2 → Vec 2)
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
theorem kernelForcedWeakSolution_unique
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w w' : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u u' : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w)
    (hsol' : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w' i t) g u' w') :
    ∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t := by
  have hdiff := P.kernelForcedWeakSolution_difference v hv_meas hv V hvb f F g hF hg
    u u' w w' hsol hsol'
  have he := P.kernelForcedWeakSolution_energy v hv hvp (fun _ _ => 0) (fun _ _ => 0)
    αv B lam hα hB hlam hsmall hstrain hd hjets hv_meas V hV hvb T hT
    (fun i t => w i t - w' i t) (fun i t => u i t - u' i t) (fun _ => 0)
    (fun i => timeMemLp_zero (E := TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) _ 2)
    (fun i => timeIntegrable_zero (E := TorusHk k (h i)) _) hdiff
  intro i t ht
  have hh := he t ht
  simp only [torusMassNormSq_zero (fun _ => k) ρ P.π P.hπ,
    Real.sqrt_zero, integral_zero, mul_zero, zero_add, zero_pow (by decide : 2 ≠ 0)] at hh
  have hg0 : 0 ≤ (ν / 2) * (∫ s in Set.Icc a b,
      massGradNormSq ρ P.π (fun i => (w i s - w' i s).val)) :=
    mul_nonneg (div_nonneg P.diffusivity_pos.le (by norm_num))
      (integral_nonneg (fun s => massGradNormSq_nonneg ρ P.π P.hπ _))
  have hm : massNormSq ρ P.π (fun i => (u i t - u' i t).val) ≤ 0 := by linarith
  exact sub_eq_zero.mp (torusCarrier_eq_zero_of_mass_le_zero (fun _ => k) ρ P.radius_pos P.π P.hπ
    (fun i => u i t - u' i t) hm i)

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Hilbert weak compactness and closed Sobolev graph readout. -/

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

variable (v : ℝ → Vec 2 → Vec 2)
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
theorem kernelFourier_exists_weakSolution
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    ∃ (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
      (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)),
      IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f F g u w y := by
  obtain ⟨u, w, hsol, _⟩ := P.kernelFourier_exists_forcedWeakSolution v hv hvp F g αv B lam
    hα hB hlam hsmall hstrain hd hjets hv_bdd hv_meas f hF hg
  refine ⟨u, w, P.higherInput w, hsol.1, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1,
    P.higherInput_memLp w hsol.2.1, P.higherInput_value_ae w, ?_⟩
  intro i t ht φ
  have hf : ∀ r ∈ Set.Ioc a t, ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      torusRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun i => w i r) i x +
        (F i r + P.carrierFlux w i r).toFunction.jet (valueIndex2 k) x =
      P.kernelRawFlux w i r x + (F i r).toFunction.jet (valueIndex2 k) x := by
    intro r hr
    exact P.totalCarrierFlux_raw_ae w F i r ⟨hr.1.le, hr.2.trans ht.2⟩
  have hw := weakIdentity_flux_congr (volume.restrict AVenhance.unitCube) ν a t v
    ((u i t).toFunction.jet (valueIndex2 k)) ((f i).toFunction.jet (valueIndex2 k))
    (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (fun r => torusRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun i => w i r) i)
    (fun r => (F i r + P.carrierFlux w i r).toFunction.jet (valueIndex2 k))
    (P.kernelRawFlux w i) (fun r => (F i r).toFunction.jet (valueIndex2 k))
    (fun r => (g i r).toFunction.jet (valueIndex2 k)) hf (hsol.2.2.2.2 i t ht φ)
  simpa only [kernelRawFlux] using! hw

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! The solved kernel coefficient ODE has the native differential mass estimate. -/

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

variable (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))



include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_component_sups
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) + P.carrierFlux w i t)
      (fun _ _ => 0) u w) :
    (∑ i, ENNReal.ofReal (P.π i)⁻¹ *
      ⨆ t ∈ Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (u i t).val)) ≤
      ENNReal.ofReal (massNormSq ρ P.π (fun i => (f i).val) +
        2 * ν * P.θ * ∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i s).val)) ∧
    (∑ i, ENNReal.ofReal (P.π i)⁻¹ *
      ((⨆ t ∈ Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (u i t).val)) +
        ENNReal.ofReal (ν * ∫ s in Set.Icc a b, gradFactorialNormSq ρ (w i s).val))) ≤
      ENNReal.ofReal (2 * massNormSq ρ P.π (fun i => (f i).val)) := by
  let ω := fun i => (P.π i)⁻¹
  let E0 := massNormSq ρ P.π (fun i => (f i).val)
  let e0 := fun i => factorialNormSq ρ (f i).val
  let C := fun i => ∫ s in Set.Icc a b, |P.carrierPair w i s|
  let R := fun i => ∫ s in Set.Icc a b, gradFactorialNormSq ρ (w i s).val
  let Rall := ∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i s).val)
  have hω (i : ι) : 0 ≤ ω i := inv_nonneg.mpr (P.hπ i).le
  have he0 (i : ι) : 0 ≤ e0 i := factorialNormSq_nonneg ρ _
  have hC (i : ι) : 0 ≤ C i := integral_nonneg (fun _ => abs_nonneg _)
  have hR (i : ι) : 0 ≤ R i := integral_nonneg (fun s => torusCarrierGradFactorial_nonneg ρ k (w i s))
  have hRall : 0 ≤ Rall := integral_nonneg (fun s => massGradNormSq_nonneg ρ P.π P.hπ _)
  have hrow := P.kernelForcedWeakSolution_component_interval v hv hvp αv B lam hα hB hlam
    hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hsol
  have hSup (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) : factorialNormSq ρ (u i t).val ≤ e0 i + 2 * C i := by
    have he := hrow i a ⟨le_rfl, P.htime⟩ t ht ht.1
    rw [hsol.2.2.2.1 i] at he
    have hn : 0 ≤ (3 * ν / 2) * ∫ s in Set.Ioc a t, gradFactorialNormSq ρ (w i s).val :=
      mul_nonneg (by have := P.diffusivity_pos; positivity)
        (integral_nonneg (fun s => torusCarrierGradFactorial_nonneg ρ k (w i s)))
    linarith
  have hDiss (i : ι) : ν * R i ≤ (2 / 3 : ℝ) * e0 i + (4 / 3 : ℝ) * C i := by
    have he := hrow i a ⟨le_rfl, P.htime⟩ b ⟨P.htime, le_rfl⟩ P.htime
    rw [hsol.2.2.2.1 i, ← integral_Icc_eq_integral_Ioc] at he
    have hn := factorialNormSq_nonneg ρ (u i b).val
    linarith
  have hCB : (∑ i, ω i * C i) ≤ (ν * P.θ) * Rall := P.carrierPair_sum_integral_bound w hsol.2.1
  have hsharp := P.kernelForcedWeakSolution_homogeneous_interval v hv hvp αv B lam hα hB hlam
    hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hsol a ⟨le_rfl, P.htime⟩ b ⟨P.htime, le_rfl⟩ P.htime
  simp only [hsol.2.2.2.1, ← integral_Icc_eq_integral_Ioc] at hsharp
  have hgrad : ν * Rall ≤ (4 / 5 : ℝ) * E0 := by
    have hn := massNormSq_nonneg ρ P.π P.hπ (fun i => (u i b).val)
    linarith
  have htheta : (ν * P.θ) * Rall ≤ E0 / 10 := by
    have hh := mul_le_mul_of_nonneg_right P.hθ (mul_nonneg P.diffusivity_pos.le hRall)
    nlinarith
  let S := fun i => e0 i + 2 * C i
  have hS (i : ι) : 0 ≤ S i := add_nonneg (he0 i) (mul_nonneg (by norm_num) (hC i))
  have hsumb : (∑ i, ω i * S i) ≤ E0 + 2 * ν * P.θ * Rall := by
    have he (i : ι) : ω i * S i = ω i * e0 i + 2 * (ω i * C i) := by dsimp only [S]; ring
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
    change E0 + 2 * (∑ i, ω i * C i) ≤ _
    nlinarith
  have hsumD : (∑ i, ω i * (S i + ν * R i)) ≤ 2 * E0 := by
    have hbound := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      mul_le_mul_of_nonneg_left (add_le_add (le_refl (S i)) (hDiss i)) (hω i))
    have he (i : ι) : ω i * (S i + ((2 / 3 : ℝ) * e0 i + (4 / 3 : ℝ) * C i)) =
        (5 / 3 : ℝ) * (ω i * e0 i) + (10 / 3 : ℝ) * (ω i * C i) := by dsimp only [S]; ring
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum] at hbound
    change _ ≤ (5 / 3 : ℝ) * E0 + (10 / 3 : ℝ) * (∑ i, ω i * C i) at hbound
    linarith
  refine ⟨?_, ?_⟩
  · exact (componentSup_le_budget (Set.Icc a b) ω S hω hS (fun i t => factorialNormSq ρ (u i t).val) hSup).trans
      (ENNReal.ofReal_le_ofReal hsumb)
  · exact (componentSupDissipation_le_budget (Set.Icc a b) ω S (fun i => ν * R i) hω hS
      (fun i => mul_nonneg P.diffusivity_pos.le (hR i)) (fun i t => factorialNormSq ρ (u i t).val) hSup).trans
      (ENNReal.ofReal_le_ofReal hsumD)

end TorusKernelOperator

end AVRegularity.KernelEnergy
end
