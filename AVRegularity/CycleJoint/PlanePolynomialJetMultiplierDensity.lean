-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PreparationWindowReferenceCellReturnMass
import AVRegularity.Construction.StrainPhysical.Context
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVRegularity.CoupledEnergyPlane.Variational.SourceWeakSolutionExistence
import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
import AVRegularity.CycleWords.CellEnergyJointH1Trace
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Actual coupled solutions supply continuous material traces, integrable higher states, and their native truncation agreement. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem coupledPlane_chart_trace_data {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {D : ℕ} {K : ι → ℕ}
    {A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)}
    {f : ∀ i, PlaneHk univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {u : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ) (i : ι)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K i + 1 → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K i + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j) :
    ContinuousOn (fun t => planeHkWindowChartPull a b hφ s B
      (fun j hj hjK => hB j hj (by omega))
      (fun t ht j hj hjK => hb t ht j hj (by omega)) t (u i t)) (Icc a b) ∧
    MemLp (fun t => planeHkWindowChartPull a b hφ s B hB hb t (w i t))
      2 (volume.restrict (Icc a b)) ∧
    (∀ᵐ t ∂volume.restrict (Icc a b),
      truncatePlaneHk (show K i ≤ K i + 1 by omega)
        (planeHkWindowChartPull a b hφ s B hB hb t (w i t)) =
      planeHkWindowChartPull a b hφ s B
        (fun j hj hjK => hB j hj (by omega))
        (fun t ht j hj hjK => hb t ht j hj (by omega)) t (u i t)) := by
  refine ⟨?_, coupledPlane_chart_energy_state hs hφ s i B hB hb, ?_⟩
  · exact planeHkWindowChartPull_trace_continuousOn a b hφ s B _ _ (u i) (hs.1 i)
  · filter_upwards [ae_restrict_mem measurableSet_Icc, hs.2.2.1 i] with t ht htu
    rw [planeHkWindowChartPull_truncate (show K i ≤ K i + 1 by omega)
      a b hφ s B hB hb t ht (w i t), htu]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Literal spatial value readouts of the actual reference-cell native curves. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

theorem preparationWindowReferenceHkWindowPull_value_ae
    (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk univ J E) :
    planeValue (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t U) =ᵐ[volume]
      fun z => planeValue U (streamFlow φ hφ t z σ) := by
  unfold preparationWindowReferenceHkWindowPull planeHkWindowChartPull
  rw [dite_eq_left ht]
  exact planeHkSmoothPullback_value_ae _ _ _ _ _ _ U

theorem preparationWindowReferenceCellNativeCurve_value_ae_at_physical_time
    (ν : ℝ) (hν : ν ≠ 0) (e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : ℝ → PlaneHk univ J E) (t : ℝ) (ht : t ∈ Icc a b) :
    planeValue (preparationWindowReferenceCellNativeCurve hc hcover σ hσ ha J hJ
      ν e he yc U ((e⁻¹) ^ 2 * (ν * t))) =ᵐ[volume]
      fun z => planeValue (U t) (streamFlow φ hφ t (yc + e • z) σ) := by
  rw [preparationWindowReferenceCellNativeCurve_at_physical_time hc hcover σ hσ ha J hJ
    ν hν e he yc U t]
  have hh := (plane_affine_quasiMeasurePreserving e he yc).ae_eq_comp
    (preparationWindowReferenceHkWindowPull_value_ae hc hcover σ hσ ha J hJ t ht (U t))
  exact (planeCarrierAffine_value_ae e he yc _).trans hh
end

/-! The exact native initial datum at any covered seam is a linear map of the physical trace. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)

/-- Pull a physical time trace into its actual reference cell. -/
def preparationWindowReferenceCellTraceLinearMap
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i))) :
    X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)) :=
  LinearMap.pi (fun i =>
    (planeCarrierAffineOperator (K i) e he yc).toLinearMap.comp
      ((preparationWindowReferenceHkWindowPullOperator hc hcover σ hσ ha
        (K i) (hK i) t ht).toLinearMap.comp ((LinearMap.proj i).comp T)))

omit [Fintype ι] in
theorem preparationWindowReferenceCellTraceLinearMap_apply
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i))) (ξ : X) (i : ι) :
    preparationWindowReferenceCellTraceLinearMap hc hcover σ hσ ha K hK e he yc t ht T ξ i =
      planeCarrierAffine e he yc
        (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha (K i) (hK i) t (T ξ i)) := by
  change planeCarrierAffine e he yc
    (preparationWindowReferenceHkWindowPullOperator hc hcover σ hσ ha (K i) (hK i) t ht
      (T ξ i)) = _
  rw [preparationWindowReferenceHkWindowPullOperator_apply]
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! The actual full source map obeys the original inverse-mass gradient Schur estimate. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceTaylorMassBudgetNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance sourceTaylorMassBudgetModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

local instance sourceTaylorMassBudgetFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance sourceTaylorMassBudgetFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance sourceTaylorMassBudgetFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance sourceTaylorMassBudgetFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem planeActual_sourceTaylor_mass_budget
    {a b : ℝ} (hab : a ≤ b) (ϖ ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (T : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hT : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun W t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (E := h j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W j) t) i) (T i))
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (θ : ℝ)
    (hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (R : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (W : ∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) (n : ℕ) :
    planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Set.Icc a b)) π
      (fun i => (T i - R i) W) ≤
      2 * (ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * θ) ^ 2) *
        planeAllMomentFamilyGradientEnergy K n ϖ ρ (volume.restrict (Set.Icc a b)) π W +
        planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Set.Icc a b)) π
          (fun i => R i W)) := by
  have hs := planeAllMomentFamilyEnergy_sub_le (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) K n ϖ ρ
    (volume.restrict (Set.Icc a b)) π (fun i => T i W) (fun i => R i W)
  have hf := planeRaw_allMoment_coupling_mass_budget hab ϖ ρ hρ K D A hA hC T hT
    π hπ θ hrow hcol W n
  have he : (fun i => (T i - R i) W) = (fun i => T i W) - (fun i => R i W) := by
    funext i
    exact LinearMap.sub_apply (T i) (R i) W
  rw [he]
  apply le_trans hs
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact add_le_add hf le_rfl

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.Weighted AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleJointProofs

/-! Reference-chart source transfer retains the original Hilbert constituent map inside the physical row, with no dimension factor. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem planePeriodicNativeRow_reference_fiber_transfer {K : ℕ}
    (P X : Vec 2 ≃ₜ Vec 2)
    (hP : ContDiff ℝ (⊤ : ℕ∞) ⇑P) (hYP : ContDiff ℝ (⊤ : ℕ∞) ⇑P.symm)
    (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X) (hYX : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm)
    (hμ : MeasurePreserving ⇑X volume volume) (hμY : MeasurePreserving ⇑X.symm volume volume)
    (D : ℕ) (hD : D ≤ K + 1)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2) (k : Fin 2)
    (hcS : ∀ z : JetIndex2 K,
      Continuous (transportedNativeScalarJetCoefficient (P.trans X.symm) D B k z))
    (hpS : ∀ z : JetIndex2 K,
      IsZ2Periodic (transportedNativeScalarJetCoefficient (P.trans X.symm) D B k z))
    (hcP : ∀ i (z : JetIndex2 K), Continuous (transportedNativeScalarJetCoefficient P D B i z))
    (hpP : ∀ i (z : JetIndex2 K), IsZ2Periodic (transportedNativeScalarJetCoefficient P D B i z))
    (hcJ : ∀ i, Continuous (fun y => (chartJacobian ⇑X y)⁻¹ k i))
    (MJ : Fin 2 → ℝ) (hMJ : ∀ i, 0 ≤ MJ i)
    (hbJ : ∀ i y, |(chartJacobian ⇑X y)⁻¹ k i| ≤ MJ i)
    (BF : ℕ → ℝ) (hBF : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ BF j)
    (hbF : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j ⇑X.symm x‖ ≤ BF j)
    (L : E →L[ℝ] F) (U : PlaneHk univ K E) :
    periodicScalarRowOperator (transportedNativeScalarJetCoefficient (P.trans X.symm) D B k)
      hcS hpS (mapPlaneHk L U) =
      ∑ i : Fin 2,
        planeScalarMultiplier (fun y => (chartJacobian ⇑X y)⁻¹ k i) (hcJ i) (hMJ i) (hbJ i)
          (Lp.compMeasurePreservingₗᵢ ℝ ⇑X hμ
            (periodicScalarRowOperator (transportedNativeScalarJetCoefficient P D B i)
              (hcP i) (hpP i)
              (mapPlaneHk L (planeHkSmoothPullback X.symm hYX hμY BF hBF hbF U)))) := by
  have he := congrArg (fun T => T (mapPlaneHk L U))
    (planePeriodicNativeRow_reference_transfer (E := F) P X hP hYP hX hYX hμ hμY D hD B k
      hcS hpS hcP hpP hcJ MJ hMJ hbJ BF hBF hbF)
  rw [he]
  simp only [planeJetRowPiolaOperator, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [planeHkSmoothPullback_fiberMap X.symm hYX hμY BF hBF hbF L U]
  rfl

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Literal matrix-gradient fluxes superpose on the actual native weak jets. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [AddCommGroup X] [Module ℝ X] {K : ℕ}

def planeMatrixGradientFlux (C : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (U : PlaneHk Set.univ (K + 1) E) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => E) :=
  ∑ kl : Fin 2 × Fin 2, C z kl.1 kl.2 •
    Weighted.fluxCoordinateInjection kl.1 (ContinuousLinearMap.id ℝ E)
      (planeJetOrder U 1 (fun _ => kl.2) z)

theorem planeMatrixGradientFlux_add_ae
    (C : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (U V : PlaneHk Set.univ (K + 1) E) :
    planeMatrixGradientFlux C (U + V) =ᵐ[volume]
      fun z => planeMatrixGradientFlux C U z + planeMatrixGradientFlux C V z := by
  have hh (kl : Fin 2 × Fin 2) := planeJetOrder_add_ae (K := K + 1)
    (Nat.succ_le_succ (Nat.zero_le K)) U V (fun _ => kl.2)
  filter_upwards [ae_all_iff.mpr hh] with z hz
  unfold planeMatrixGradientFlux
  simp only [hz, map_add, smul_add, Finset.sum_add_distrib]

theorem planeMatrixGradientFlux_smul_ae
    (C : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) (U : PlaneHk Set.univ (K + 1) E) :
    planeMatrixGradientFlux C (c • U) =ᵐ[volume]
      fun z => c • planeMatrixGradientFlux C U z := by
  have hj : 1 ≤ K + 1 := Nat.succ_le_succ (Nat.zero_le K)
  have hh (kl : Fin 2 × Fin 2) : planeJetOrder (c • U) 1 (fun _ => kl.2) =ᵐ[volume]
      fun z => c • planeJetOrder U 1 (fun _ => kl.2) z := by
    simp only [planeJetOrder_eq_stored hj]
    exact planeCarrier_jet_smul_ae c U _
  filter_upwards [ae_all_iff.mpr hh] with z hz
  unfold planeMatrixGradientFlux
  simp only [hz, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro kl _
  exact smul_comm (C z kl.1 kl.2) c _

theorem planeMatrixGradientFlux_curve_superposition
    (μ : Measure ℝ) (C : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (U : X → ℝ → PlaneHk Set.univ (K + 1) E)
    (hadd : ∀ x y, U (x + y) =ᵐ[μ] fun t => U x t + U y t)
    (hsmul : ∀ (c : ℝ) x, U (c • x) =ᵐ[μ] fun t => c • U x t) :
    (∀ x y, ∀ᵐ t ∂μ,
      planeMatrixGradientFlux (C t) (U (x + y) t) =ᵐ[volume]
        fun z => planeMatrixGradientFlux (C t) (U x t) z +
          planeMatrixGradientFlux (C t) (U y t) z) ∧
    (∀ (c : ℝ) x, ∀ᵐ t ∂μ,
      planeMatrixGradientFlux (C t) (U (c • x) t) =ᵐ[volume]
        fun z => c • planeMatrixGradientFlux (C t) (U x t) z) := by
  constructor
  · intro x y
    filter_upwards [hadd x y] with t ht
    rw [ht]
    exact planeMatrixGradientFlux_add_ae (C t) (U x t) (U y t)
  · intro c x
    filter_upwards [hsmul c x] with t ht
    rw [ht]
    exact planeMatrixGradientFlux_smul_ae (C t) c (U x t)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
open AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The original preparation reference curve transfers to a covered following reference without requiring the original anchor to lie in the preparation window. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

theorem preparationReferenceCellNativeCurve_transition_value_ae
    (σ' : ℝ) (hσ' : σ' ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (e : ℝ) (he : e ≠ 0) (yc yc' : Vec 2)
    (U : ℝ → PlaneHk univ J E) (t : ℝ) (ht : t ∈ Icc a b) :
    let X := cellRescaledHomeomorph (streamFlowHomeomorph hφ ((l₀ : ℝ) * ocTauPP α q Λ m) σ') e he yc yc'
    planeValue (preparationWindowReferenceCellNativeCurve hc hcover σ' hσ' ha J hJ
      ν e he yc' U ((e⁻¹) ^ 2 * (ν * t))) =ᵐ[volume]
      fun z => planeValue (preparationReferenceCellNativeCurve hc hcover hTau ha J hJ
        ν e he yc U ((e⁻¹) ^ 2 * (ν * t))) (X z) := by
  intro X
  have hm : MeasurePreserving X volume volume :=
    cell_rescaled_measurePreserving _ (streamFlow_measurePreserving hφ ((l₀ : ℝ) * ocTauPP α q Λ m) σ') e he yc yc'
  have ho := hm.quasiMeasurePreserving.ae_eq_comp
    (preparationReferenceCellNativeCurve_value_ae_at_physical_time hc hcover hTau ha
      J hJ ν hν e he yc U t ht)
  have hn := preparationWindowReferenceCellNativeCurve_value_ae_at_physical_time hc hcover
    σ' hσ' ha J hJ ν hν e he yc' U t ht
  filter_upwards [hn, ho] with z hnew hold
  have hx : yc + e • X z = streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) (yc' + e • z) σ' := by
    change yc + e • (e⁻¹ • (streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) (yc' + e • z) σ' - yc)) = _
    rw [smul_smul, mul_inv_cancel₀ he, one_smul, add_sub_cancel]
  simp only [Function.comp_def] at hold
  rw [hx] at hold
  have hg : streamFlow φ hφ t (streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) (yc' + e • z) σ') ((l₀ : ℝ) * ocTauPP α q Λ m) =
      streamFlow φ hφ t (yc' + e • z) σ' :=
    Infra.Flow.flow_group_law _ hφ.vel_lipschitz (StrainPhysical.isFlow_stream hφ)
      (yc' + e • z) σ' ((l₀ : ℝ) * ocTauPP α q Λ m) t
  exact hnew.trans ((congrArg (planeValue (U t)) hg).symm.trans hold.symm)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual physical return of the cell model is a continuous linear inverse
with a uniform factorial price, retaining the exact plane dilation factor. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

/-- Pull a returned first-cell endpoint into a covered reference chart.
The first anchor itself need not belong to the preparation window. -/
def preparationReferenceCellTransitionOperator
    (σ : ℝ) (hσ : σ ∈ Icc a b)
    (e : ℝ) (he : e ≠ 0) (yc yc' : Vec 2) (t : ℝ) (ht : t ∈ Icc a b) :
    PlaneHk univ J E →L[ℝ] PlaneHk univ J E :=
  (planeCarrierAffineOperator J e he yc').comp
    ((preparationWindowReferenceHkWindowPullOperator hc hcover σ hσ ha J hJ t ht).comp
      (preparationReferenceCellReturnOperator hc hcover hTau ha J hJ e he yc t ht))

theorem preparationReferenceCellTransitionOperator_apply
    (σ : ℝ) (hσ : σ ∈ Icc a b)
    (e : ℝ) (he : e ≠ 0) (yc yc' : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    (U : PlaneHk univ J E) :
    preparationReferenceCellTransitionOperator hc hcover hTau ha J hJ σ hσ e he yc yc' t ht U =
      planeCarrierAffine e he yc' (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t
        (preparationReferenceCellReturnOperator hc hcover hTau ha J hJ e he yc t ht U)) := by
  change planeCarrierAffine e he yc'
    (preparationWindowReferenceHkWindowPullOperator hc hcover σ hσ ha J hJ t ht
      (preparationReferenceCellReturnOperator hc hcover hTau ha J hJ e he yc t ht U)) = _
  rw [preparationWindowReferenceHkWindowPullOperator_apply]

theorem preparationReferenceCellTransitionOperator_native_curve
    (σ : ℝ) (hσ : σ ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (e : ℝ) (he : e ≠ 0)
    (yc yc' : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    (U : ℝ → PlaneHk univ J E) :
    preparationReferenceCellTransitionOperator hc hcover hTau ha J hJ σ hσ e he yc yc' t ht
      (preparationReferenceCellNativeCurve hc hcover hTau ha J hJ ν e he yc U
        ((e⁻¹) ^ 2 * (ν * t))) =
      preparationWindowReferenceCellNativeCurve hc hcover σ hσ ha J hJ ν e he yc' U
        ((e⁻¹) ^ 2 * (ν * t)) := by
  rw [preparationReferenceCellTransitionOperator_apply,
    preparationReferenceCellNativeCurve_return hc hcover hTau ha J hJ ν hν e he yc U t ht,
    preparationWindowReferenceCellNativeCurve_at_physical_time hc hcover σ hσ ha J hJ
      ν hν e he yc' U t]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The assembled native remainder maps read out exactly the original finite
identity, derivative-order and weighted piece sums. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem naturalFamilyRemainder_raw_map_sum
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (S : Finset P) (ctx : ∀ p : S, Ctx p.val) (anchor : S → ℝ)
    (timeScale a b σ e E ϖ ρ : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (yc : Vec 2) (μ : Measure ℝ)
    (T : ∀ v u, F.Γ v u → Fin D → S →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 μ →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ ρ 0 μ)
    (hT : ∀ v u γ j p, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 μ
      (fun x τ z => naturalFamilyRemainderNativeArray Ks F p.val (ctx p) v u γ
        timeScale a b hφ (anchor p) σ e E yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ x τ) (j.val + 1) I z)))
      (T v u γ j p)) (v u : ι) :
    IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 μ
      (fun x τ z => ∑ γ, ∑ j : Fin D, ∑ p : S,
        naturalFamilyRemainderNativeArray Ks F p.val (ctx p) v u γ
          timeScale a b hφ (anchor p) σ e E yc (j.val + 1) τ z
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ x τ) (j.val + 1) I z)))
      (∑ γ, ∑ j, ∑ p, T v u γ j p) := by
  apply planeRaw_allMoment_linearMap_sum
  intro γ
  apply planeRaw_allMoment_linearMap_sum
  intro j
  exact planeRaw_allMoment_linearMap_sum (K v) ϖ ρ 0 μ _ _ (hT v u γ j)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Coordinate injection reads the actual native matrix-gradient flux component. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMatrixGradientFlux_component {K : ℕ}
    (C : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (U : PlaneHk Set.univ (K + 1) E)
    (z : Vec 2) (k : Fin 2) :
    planeMatrixGradientFlux C U z k =
      ∑ l : Fin 2, C z k l • planeJetOrder U 1 (fun _ => l) z := by
  classical
  simp only [planeMatrixGradientFlux, Fintype.sum_prod_type, WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.smul_apply, Weighted.fluxCoordinateInjection_apply,
    ContinuousLinearMap.id_apply]
  simp_rw [smul_ite, smul_zero, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  change (∑ a : Fin 2, if k = a then
    (∑ l : Fin 2, C z a l • planeJetOrder U 1 (fun _ => l) z) else 0) = _
  rw [Finset.sum_eq_single k]
  · simp only [ite_true]
  · intro a _ ha
    exact ite_eq_right (Ne.symm ha)
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual physical return of the cell model is a continuous linear inverse
with a uniform factorial price, retaining the exact plane dilation factor. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

/-- The following native initial trace of a returned retained datum is its actual mixed chart transition. -/
theorem preparationWindowReferenceCellNativeCurve_returned_initial
    (σ : ℝ) (hσ : σ ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (e : ℝ) (he : e ≠ 0)
    (yc yc' : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    (U : PlaneHk univ J E) (V : ℝ → PlaneHk univ J E)
    (hV : V t = preparationReferenceCellReturnOperator hc hcover hTau ha J hJ e he yc t ht U) :
    preparationWindowReferenceCellNativeCurve hc hcover σ hσ ha J hJ ν e he yc' V
      ((e⁻¹) ^ 2 * (ν * t)) =
    preparationReferenceCellTransitionOperator hc hcover hTau ha J hJ σ hσ e he yc yc' t ht U := by
  rw [preparationWindowReferenceCellNativeCurve_at_physical_time hc hcover σ hσ ha J hJ
    ν hν e he yc' V t, hV, preparationReferenceCellTransitionOperator_apply]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The literal native metric flux splits into its central metric, positive Taylor part and remainder. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMatrixGradientFlux_taylor_split {K : ℕ} (Ks : ℕ)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (U : PlaneHk Set.univ (K + 1) E) (z : Vec 2) :
    planeMatrixGradientFlux (fun y => G y - 1) U z =
      planeMatrixGradientFlux (fun _ => G 0 - 1) U z +
      planeMatrixGradientFlux (fun y k l => taylorSlow 1 Ks (fun x => G x k l) 0 y) U z +
      planeMatrixGradientFlux (fun y k l => G y k l - taylorSlow 0 Ks (fun x => G x k l) 0 y) U z := by
  unfold planeMatrixGradientFlux
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro kl _
  rw [← add_smul, ← add_smul]
  congr 1
  have ht := AVRegularity.CycleWords.taylorSlow_zero_eq_constant_add_positive Ks
    (fun x => G x kl.1 kl.2) 0 z
  simp only [Matrix.sub_apply]
  linarith only [ht]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual first-to-following reference change is precisely the cycle renewal map on native values. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

theorem preparationReferenceCellNativeCurve_renewal_value_ae
    (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ν : ℝ) (hν : ν ≠ 0) (he : ocEpsilon q Λ m ≠ 0) (yc yc' : Vec 2)
    (U : ℝ → PlaneHk univ J E) (t : ℝ) (ht : t ∈ Icc a b) :
    planeValue (preparationWindowReferenceCellNativeCurve hc hcover
      (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext ha J hJ
      ν (ocEpsilon q Λ m) he yc' U (((ocEpsilon q Λ m)⁻¹) ^ 2 * (ν * t))) =ᵐ[volume]
      fun z => planeValue (preparationReferenceCellNativeCurve hc hcover hTau ha J hJ
        ν (ocEpsilon q Λ m) he yc U (((ocEpsilon q Λ m)⁻¹) ^ 2 * (ν * t)))
        (ocCellTransition α q Λ m φ hφ l₀ yc yc' z) := by
  exact preparationReferenceCellNativeCurve_transition_value_ae hc hcover hTau ha J hJ
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext
    ν hν (ocEpsilon q Λ m) he yc yc' U t ht

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The diagonal order-two coupling array reads exactly the literal native matrix-gradient forcing. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawCouplingFlux_diagonal_matrix_flux (K : ι → ℕ) (D : ℕ) (hD : 2 ≤ D)
    (G : ∀ _v : ι, ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) (t : ℝ) (x : Vec 2) :
    planeRawCouplingFlux K D t (planeDiagonalGradientCoefficient K D G) w i x =
      planeMatrixGradientFlux (G i t) (w i) x := by
  apply PiLp.ext
  intro k
  rw [planeRawCouplingFlux_diagonal_gradient K D hD G w i t x k,
    planeMatrixGradientFlux_component]
  apply Finset.sum_congr rfl
  intro l _
  simp only [planeJetOrder, dite_eq_left (Nat.succ_le_succ (Nat.zero_le (K i)))]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The constructed retained homogeneous error has its literal forcing represented in the native all-moment carrier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance retainedNativeErrorScalarNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance retainedNativeErrorScalarNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance retainedNativeErrorScalarCarrierAdd (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance retainedNativeErrorScalarCarrierModule (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance

variable (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
  (K : ι → ℕ) (a b ϖ ρ : ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
  (Lmetric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (f : ∀ i, PlaneHk Set.univ (K i) (h i))
  (u₀ : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
  (w₀ : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
  (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)))

variable {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem planeComponentAllMomentResponse_retained_native_error_solution
    (hab : a ≤ b) (hρ : 0 < ρ) (hD : 2 ≤ D)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) i j d) ≠ ⊤)
    (hA' : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ)
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) i j d t))
    (hC' : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (family : ChartedFamily ι h D P Ctx)
    (H J : ℕ) (hdepth : family.HasDepthAtMost H)
    (hS : HasSourceDegreeOn family 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (hbase : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u₀ i) (fun _ i => w₀ i))
    (hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Z i) (w₀ i))
    (Lfull Ldiag : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hfull : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun X t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (E := h j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (X j) t) i) (Lfull i))
    (hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun X t => planeRawCouplingFlux K D t
        (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1))
        (fun j => planeTimeAllMomentCarrierToLp (E := h j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (X j) t) i) (Ldiag i))
    (uH : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wH : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hH : IsCoupledWeakSolutionPlane 1 a b v D K A f
      (fun _ _ => 0) (fun _ _ => 0) uH wH) :
    let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
      (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
    let W := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
    let T := ∑ n ∈ Finset.range (H + 1), U J n
    let Q := fun i => Lmetric i (W i) + nativeFamilyEdgeForcingMap Ledge i W - Lmetric i (T i)
    ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane 1 a b v D K A (fun _ => 0)
        (fun i t => -(F i t - planeCouplingFluxRow hab ρ hρ K D A hA' hC' w i t +
          planeCouplingFluxRow hab ρ hρ K D
            (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1))
            hA hC w i t)) (fun _ _ => 0)
        (fun i t => uH i t - u i t) (fun i t => wH i t - w i t) ∧
      (∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (Q i) (F i) ∧
        PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (W i) (w i)) ∧
      ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (-(Q i - Lfull i W + Ldiag i W))
        (fun t => -(F i t - planeCouplingFluxRow hab ρ hρ K D A hA' hC' w i t +
          planeCouplingFluxRow hab ρ hρ K D
            (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1))
            hA hC w i t)) := by
  dsimp only
  let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
    (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
  let W := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
  obtain ⟨F, u, w, hs, hr⟩ :=
    planeComponentAllMomentResponse_retained_homogeneous_error_solution M v K a b ϖ ρ R
      Lmetric Ledge f u₀ w₀ Z hab hρ hD A hA hA' hC hC'
      family H J hdepth hS hR hbase hZ uH wH hH
  refine ⟨F, u, w, hs, hr, ?_⟩
  have hf := planeRaw_allMoment_couplingRow_represents hab ϖ ρ hρ K D A hA' hC'
    Lfull hfull W w (fun i => (hr i).2)
  have hd := planeRaw_allMoment_couplingRow_represents hab ϖ ρ hρ K D
    (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1))
    hA hC Ldiag hdiag W w (fun i => (hr i).2)
  intro i
  apply planeTimeAllMomentRepresents_neg (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
  exact planeTimeAllMomentRepresents_add (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
    _ _ _ _ (planeTimeAllMomentRepresents_sub (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      _ _ _ _ (hr i).1 (hf i)) (hd i)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Whole-plane existence for finite strictly triangular systems without a coupling smallness premise. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_triangularPlaneWeakSolution (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (r : ι → ℕ) (hr : ∀ i i', ¬ r i' < r i → ∀ d, A i i' d = 0)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)) :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν a b v D K A f F g u w := by
  obtain ⟨π, hπ, hschur⟩ := exists_triangularCoefficientSchur ν ρ K D a b A hν hρ hA r hr
  exact exists_sourcePlaneWeakSolution K Kmax hK ρ strain B lam ν hρ hstrain0 hB
    hlam hν hsmall hstrain π hπ a b hab v hv V hV hbv hdiv hjets D A hA hC hschur
    F g hF hg f hvm hAm

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Polynomially growing scalar coefficients define native all-moment maps on reserved source jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

local instance polynomialJetMultiplierMomentNormed (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k E) := allMomentTimeNativeNormed k
local instance polynomialJetMultiplierMomentModule (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k E) := allMomentTimeNativeModule k

theorem exists_planePolynomialJetMultiplier_allMoment_map
    {K L r : ℕ} (hKL : K + r ≤ L + 1) (hr : 1 ≤ r) (I : DerivativeWord2 r)
    (p : ℕ) (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (c : ℝ → Vec 2 → ℝ) (hm : ∀ z, Measurable (fun t => c t z))
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (c t)) (A : E →L[ℝ] F)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c t) z‖ ≤ B * polynomialMomentRoot ϖ z ^ p) :
    ∃ T : PlaneTimeAllMomentCarrier (E := E) (L + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := F) K ϖ ρ 0 μ,
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
        (fun x t z => c t z • A (planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z)) T := by
  let U := fun x t => planeTimeAllMomentCarrierToLp (E := E) (L + 1) ϖ ρ 0 μ x t
  obtain ⟨hadd, hsmul⟩ := planeJetMultiplier_curve_superposition μ c A r I U
    (planeTimeAllMomentCarrier_add (L + 1) ϖ ρ 0 μ)
    (planeTimeAllMomentCarrier_smul (L + 1) ϖ ρ 0 μ)
  apply exists_planeRaw_allMoment_linearMap K ϖ ρ 0 μ
    (fun x t z => c t z • A (planeJetOrder (U x t) r I z)) hadd hsmul
  intro x n
  have he := integrated_weightedGradFactorialNormSq_ne_top_of_lift (n + p) ϖ 0 ρ hρ μ (U x)
    (planeTimeAllMomentCarrier_moment (L + 1) ϖ ρ 0 μ x (n + p))
  have hR : 0 < derivativeReserveFactor ρ K (r - 1) := by
    unfold derivativeReserveFactor
    positivity
  have hb' : ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c t) z‖ ≤
        (B * derivativeReserveFactor ρ K (r - 1)) /
          derivativeReserveFactor ρ K (r - 1) * polynomialMomentRoot ϖ z ^ p := by
    simpa only [mul_div_cancel_right₀ B hR.ne'] using hb
  obtain ⟨V, hV, hVe, hv, _⟩ := reserved_scalar_native_flux_exists hKL hr I n p ϖ ρ hϖ hρ
    c hm hc A (B * derivativeReserveFactor ρ K (r - 1)) (mul_nonneg hB hR.le) μ hb'
    (U x) (planeTimeAllMomentCarrier_memLp (L + 1) ϖ ρ 0 μ x) he
  exact ⟨V, hV, hVe, hv⟩

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The assembled native remainder maps read out exactly the original finite
identity, derivative-order and weighted piece sums. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem naturalFamilyRemainder_family_raw_map
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (S : Finset P) (ctx : ∀ p : S, Ctx p.val) (anchor : S → ℝ)
    (timeScale a b σ e E ϖ ρ : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (yc : Vec 2) (μ : Measure ℝ)
    (T : ∀ v u, F.Γ v u → Fin D → S →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 μ →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ ρ 0 μ)
    (hT : ∀ v u γ j p, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 μ
      (fun x τ z => naturalFamilyRemainderNativeArray Ks F p.val (ctx p) v u γ
        timeScale a b hφ (anchor p) σ e E yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ x τ) (j.val + 1) I z)))
      (T v u γ j p)) (v : ι) :
    IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 μ
      (fun x τ z => ∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p : S,
        naturalFamilyRemainderNativeArray Ks F p.val (ctx p) v u γ
          timeScale a b hφ (anchor p) σ e E yc (j.val + 1) τ z
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ (x u) τ) (j.val + 1) I z)))
      (nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p) v) := by
  unfold nativeFamilyEdgeForcingMap
  apply planeRaw_allMoment_linearMap_sum
  intro u
  have hh := naturalFamilyRemainder_raw_map_sum Ks F K S ctx anchor timeScale a b σ e E ϖ ρ hφ yc μ T hT v u
  intro x
  exact hh (x u)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Polynomially growing scalar coefficients define native all-moment maps on reserved source jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem planePolynomialJetMultiplier_allMoment_density
    {K L r : ℕ} (hKL : K + r ≤ L + 1) (hr : 1 ≤ r) (I : DerivativeWord2 r)
    (p : ℕ) (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (c : ℝ → Vec 2 → ℝ) (hm : ∀ z, Measurable (fun t => c t z))
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (c t)) (A : E →L[ℝ] F)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c t) z‖ ≤ B * polynomialMomentRoot ϖ z ^ p)
    (T : PlaneTimeAllMomentCarrier (E := E) (L + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := F) K ϖ ρ 0 μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
      (fun x t z => c t z • A (planeJetOrder
        (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z)) T) (x : PlaneTimeAllMomentCarrier (E := E) (L + 1) ϖ ρ 0 μ) :
    ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (planeTimeAllMomentCarrierToLp K ϖ ρ 0 μ (T x) t) z ≤
        multiplicationDensityBudget K *
          (B * derivativeReserveFactor ρ K (r - 1) * ‖A‖) ^ 2 *
            (polynomialMomentRoot ϖ z ^ p) ^ 2 *
              planeGradFactorialDensity ρ (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) z := by
  let U := fun t => planeTimeAllMomentCarrierToLp (E := E) (L + 1) ϖ ρ 0 μ x t
  have he := integrated_weightedGradFactorialNormSq_ne_top_of_lift p ϖ 0 ρ hρ μ U
    (planeTimeAllMomentCarrier_moment (L + 1) ϖ ρ 0 μ x p)
  have hR : 0 < derivativeReserveFactor ρ K (r - 1) := by
    unfold derivativeReserveFactor
    positivity
  have hb' : ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c t) z‖ ≤
        (B * derivativeReserveFactor ρ K (r - 1)) /
          derivativeReserveFactor ρ K (r - 1) * polynomialMomentRoot ϖ z ^ p := by
    simpa only [mul_div_cancel_right₀ B hR.ne'] using hb
  obtain ⟨V, _, _, hv, hdens⟩ := reserved_scalar_native_flux_exists hKL hr I 0 p ϖ ρ hϖ hρ
    c hm hc A (B * derivativeReserveFactor ρ K (r - 1)) (mul_nonneg hB hR.le) μ hb'
    U (planeTimeAllMomentCarrier_memLp (L + 1) ϖ ρ 0 μ x) (by simpa using he)
  have hrep := planeRaw_allMoment_map_represents K ϖ ρ 0 μ _ T hT x V hv
  filter_upwards [hrep, hdens] with t ht hdensity
  rw [ht]
  exact hdensity

end AVRegularity.CycleJointProofs
end
