-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.SourceSobolevFlux

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Pointwise convergence of every native weak test along the actual common Galerkin subsequence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceWeakTestValue_eq_weakClass {a b : ℝ} (hab : a ≤ b)
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

    (fun t => sourceWeakTestValue K D a b v A ν f F g W i t ψ)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => inner ℝ
        (highJetReadout (h := h) K i (valueIndex2 (K i + 1)) (W t))
        (planeHkValueOperator 1 ψ) := by
  obtain ⟨q, hq, hqa⟩ := sourceProjectedCurve_scalarTrace hab ρ hρ v hv V hV hbv
    K D A hAc hAf hvm hAm ν f F hF g hg u heq φ hφ W R hu hw hrange π hπ C hmass i ψ
  have hid (t : Set.Icc a b) : q t = sourceWeakTestValue K D a b v A ν f F g W i t ψ :=
    tendsto_nhds_unique (hq t)
      (sourceProjectedCurve_test_tendsto hab ρ hρ v hv V hV hbv K D A hAc hAf
        hvm hAm ν f F hF g hg u heq φ hφ W R hu hw i t ψ)
  filter_upwards [hqa, ae_restrict_mem measurableSet_Icc] with t ht htm
  rw [← hid ⟨t, htm⟩]
  exact ht

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The true diffusion, all admissible couplings, and external flux form a Sobolev time L² class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance residualFluxCarrierAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := inferInstance
local instance residualFluxTimeModule (i : ι) (k : ℕ) (a b : ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := (residualFluxTimeSpace i k a b).toModule

local instance residualHighCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (h i)) := inferInstance
local instance residualHighTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (h i)) 2 (volume.restrict (Set.Icc a b))) := inferInstance

def planeResidualFluxTime {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (U : ∀ j, Lp (PlaneHk Set.univ (K j + 1) (h j)) 2 (volume.restrict (Set.Icc a b)))
    (F : ∀ j, Lp (PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j))) 2
      (volume.restrict (Set.Icc a b))) (N : ℕ) (i : ι) :
    Lp (PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b)) :=
  assemblePlaneResidualFlux (h := h) (volume.restrict (Set.Icc a b)) (fun j => K j + 1)
    (fun j d => planeCoupledFluxTimeCLM hab ρ hρ K D i j d (A i j d) (hAf i j d)
      (hAc i j d) (hAm i j d)) U (F i) N


theorem tendsto_planeResidualFluxTime {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (U : ∀ j, Lp (PlaneHk Set.univ (K j + 1) (h j)) 2 (volume.restrict (Set.Icc a b)))
    (F : ∀ j, Lp (PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j))) 2
      (volume.restrict (Set.Icc a b))) (i : ι) :
    Tendsto (fun N => planeResidualFluxTime hab ρ hρ K D A hAc hAf hAm U F N i)
      atTop (𝓝 (F i)) := by
  exact tendsto_assemblePlaneResidualFlux (h := h) (volume.restrict (Set.Icc a b)) (fun j => K j + 1)
    (fun j d => planeCoupledFluxTimeCLM hab ρ hρ K D i j d (A i j d) (hAf i j d)
      (hAc i j d) (hAm i j d)) U (F i)

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

local instance carrierFluxValueCarrierAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance carrierFluxValueCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance carrierFluxValueCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance carrierFluxValueTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := inferInstance
local instance carrierFluxValueTimeModule (i : ι) (k : ℕ) (a b : ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := (carrierFluxValueTimeSpace i k a b).toModule

theorem sourceSobolevFlux_carrier_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
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
    sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i F hF
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        ν • planeGradientTensor (weakHighCarrier K a b W i t) +
          (∑ j, ∑ d : admissibleOrders K D i j,
            planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
              (clampPoint a b hab t) (clampPoint a b hab t).property
              (hAc i j d _ (clampPoint a b hab t).property) (weakHighCarrier K a b W j t)) + F t := by
  exact assembleTimeFlux_ae_of_fields
    (J := PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (I := ι) (D := fun j => admissibleOrders K D i j) (volume.restrict (Set.Icc a b)) ν
    (weakGradientTimeCLM K a b i W)
    (fun j d => weakCoupledFluxTimeCLM hab ρ hρ K D i j d (A i j d) (hAf i j d)
      (hAc i j d) (hAm i j d) W) (hF.toLp F)
    (fun t => planeGradientTensor (weakHighCarrier K a b W i t)) F
    (fun j d t => planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
      (clampPoint a b hab t) (clampPoint a b hab t).property
      (hAc i j d _ (clampPoint a b hab t).property) (weakHighCarrier K a b W j t))
    (weakGradientTimeCLM_ae K a b i W) hF.coeFn_toLp
    (fun j d => weakCoupledFluxTimeCLM_ae hab ρ hρ K D i j d (A i j d) (hAf i j d)
      (hAc i j d) (hAm i j d) W)

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The true diffusion, all admissible couplings, and external flux form a Sobolev time L² class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance residualFluxValueCarrierAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxValueCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxValueCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxValueCarrierModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  (residualFluxValueCarrierSpace i k).toModule
local instance residualFluxValueCarrierSmulZero (i : ι) (k : ℕ) :
    SMulWithZero ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxValueTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := inferInstance
local instance residualFluxValueTimeModule (i : ι) (k : ℕ) (a b : ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := (residualFluxValueTimeSpace i k a b).toModule

local instance residualValueHighCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (h i)) := inferInstance
local instance residualValueHighTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (h i)) 2 (volume.restrict (Set.Icc a b))) := inferInstance

theorem planeResidualFluxAssembly_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (U : ∀ j, Lp (PlaneHk Set.univ (K j + 1) (h j)) 2 (volume.restrict (Set.Icc a b)))
    (F : ∀ j, Lp (PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j))) 2
      (volume.restrict (Set.Icc a b))) (N : ℕ) (i : ι) :
    assembleTimeFlux (volume.restrict (Set.Icc a b)) 0 0
      (fun j d => planeCoupledFluxTimeCLM hab ρ hρ K D i j d (A i j d) (hAf i j d)
        (hAc i j d) (hAm i j d)
        (planeSobolevTimeResidual (volume.restrict (Set.Icc a b)) N (K j + 1) (U j))) (F i)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        (∑ j, ∑ d : admissibleOrders K D i j,
          planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
            (clampPoint a b hab t) (clampPoint a b hab t).property
            (hAc i j d _ (clampPoint a b hab t).property)
            (U j t - AVRegularity.CoupledEnergyPlane.Fourier.planeHkCutoff N (K j + 1) (U j t))) + F i t := by
  let Cn : ∀ j, admissibleOrders K D i j →
      Lp (PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))) 2
        (volume.restrict (Set.Icc a b)) := fun j d =>
    planeCoupledFluxTimeCLM hab ρ hρ K D i j d (A i j d) (hAf i j d)
      (hAc i j d) (hAm i j d)
      (planeSobolevTimeResidual (volume.restrict (Set.Icc a b)) N (K j + 1) (U j))
  have he := assembleTimeFlux_ae_of_fields (volume.restrict (Set.Icc a b)) 0
    (0 : Lp (PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) Cn (F i)
    (fun _ => (0 : PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))) (F i)
    (fun j d t => planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
      (clampPoint a b hab t) (clampPoint a b hab t).property
      (hAc i j d _ (clampPoint a b hab t).property)
      (U j t - AVRegularity.CoupledEnergyPlane.Fourier.planeHkCutoff N (K j + 1) (U j t)))
    (Lp.coeFn_zero (E := PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (p := 2) (μ := volume.restrict (Set.Icc a b))) Filter.EventuallyEq.rfl
    (fun j d => planeCoupledFluxTimeCLM_residual_ae hab ρ hρ K D i j d (A i j d) (hAf i j d)
      (hAc i j d) (hAm i j d) (U j) N)
  simpa only [Cn, zero_smul, zero_add] using he

end AVRegularity.CoupledEnergyPlane
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The true diffusion, all admissible couplings, and external flux form a Sobolev time L² class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance residualFluxWrapperCarrierAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxWrapperCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxWrapperCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxWrapperCarrierModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  (residualFluxWrapperCarrierSpace i k).toModule
local instance residualFluxWrapperCarrierSmulZero (i : ι) (k : ℕ) :
    SMulWithZero ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance residualFluxWrapperTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := inferInstance
local instance residualFluxWrapperTimeModule (i : ι) (k : ℕ) (a b : ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) 2
      (volume.restrict (Set.Icc a b))) := (residualFluxWrapperTimeSpace i k a b).toModule

local instance residualWrapperHighCarrierSpace (i : ι) (k : ℕ) :
    NormedSpace ℝ (PlaneHk Set.univ k (h i)) := inferInstance
local instance residualWrapperHighTimeSpace (i : ι) (k : ℕ) (a b : ℝ) :
    NormedSpace ℝ (Lp (PlaneHk Set.univ k (h i)) 2 (volume.restrict (Set.Icc a b))) := inferInstance

theorem planeResidualFluxTime_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : admissibleOrders K D i j, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (U : ∀ j, Lp (PlaneHk Set.univ (K j + 1) (h j)) 2 (volume.restrict (Set.Icc a b)))
    (F : ∀ j, Lp (PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j))) 2
      (volume.restrict (Set.Icc a b))) (N : ℕ) (i : ι) :
    planeResidualFluxTime hab ρ hρ K D A hAc hAf hAm U F N i
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        (∑ j, ∑ d : admissibleOrders K D i j,
          planeCoupledFluxTerm ρ hρ K D a b i j d (A i j d) (hAf i j d)
            (clampPoint a b hab t) (clampPoint a b hab t).property
            (hAc i j d _ (clampPoint a b hab t).property)
            (U j t - AVRegularity.CoupledEnergyPlane.Fourier.planeHkCutoff N (K j + 1) (U j t))) + F i t := by
  unfold planeResidualFluxTime assemblePlaneResidualFlux
  exact planeResidualFluxAssembly_ae hab ρ hρ K D A hAc hAf hAm U F N i

end AVRegularity.CoupledEnergyPlane
end
end
