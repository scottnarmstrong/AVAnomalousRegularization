-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.WindowCoverConstructedRetainedActualTaylorLinearEndpointAllMomentsBound
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
import AVRegularity.CycleJoint.ActualPreparationHomogeneousPlaneExistence
import AVRegularity.CycleJoint.PreparationReferenceCellInitialHomogeneousResponsePair
public import AVRegularity.CycleJoint.PointwiseNativeTransportIdentityPrice
import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction

section
/-! The actual first reference chart constructs the original-edge source maps,
metric Taylor maps and genuine component responses before the datum is selected. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

theorem windowCover_window_reference_feedback_maps (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (_hζ : IsFastProfile ζfast) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (CG : ℕ → ℝ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (_ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ ∈ Set.Icc tS tZ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (ic : Fin (P + 2)) (a b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        ∀ (Ks : ℕ), F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        Ks + 1 + Kmax ≤ qJ → b - a ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
      ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀
      ic
    ∃ Rs : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    ∃ Ledge : ∀ v u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    ∃ diag positive Rm : ∀ v, PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc a b)),
    ∃ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc a b)),
    ((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ σ ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (nativeFamilyEdgeForcingMap Ledge v + Rs v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
        (fun x t z => ∑ u, ∑ γ, naturalFamilyTaylorRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
          (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ (fun p => (F.piece p).anchor)
          σ (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc ϖ (ρ / (ocEpsilon q Λ m))
          (volume.restrict (Set.Icc a b)) v u γ (x u) t z)
        (nativeFamilyEdgeForcingMap Ledge v)) ∧
      (∀ v u, ¬ Nonempty (F.Γ v u) → Ledge v u = 0) ∧
      (∀ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
        HasSourceDegreeOn F 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))) ∧
    ((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
          (planeTimeAllMomentCarrierToLp (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) X t)) (diag v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) X t)) (positive v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux
          (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) X t)) (Rm v))) ∧
    (∀ v, IsPlaneComponentAllMomentResponse (E := h v) (fun t => G t 0)
      (ocCellDrift α q Λ ζfast m ν yc) (K v) a b ϖ (ρ / ocEpsilon q Λ m) (R v)) ∧
    (let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CR := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
      (volume.restrict (Set.Icc a b))) (n : ℕ),
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / (ocEpsilon q Λ m)) (K v)
      (planeTimeAllMomentCarrierToLp (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
        (Rs v Z) τ)
      ∂volume.restrict (Set.Icc a b)) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) *
        (pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CR) Cm * θ)) ^ 2) *
      ∫⁻ τ, ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + (Ks + 1))
        ϖ 0 (ρ / (ocEpsilon q Λ m)) (K u)
        (planeTimeAllMomentCarrierToLp (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
          (volume.restrict (Set.Icc a b)) (Z u) τ) ∂volume.restrict (Set.Icc a b)) ∧
    (∀ W n, planeAllMomentFamilyEnergy K n ϖ (ρ / (ocEpsilon q Λ m)) (volume.restrict (Set.Icc a b)) π
      (fun v => (nativeFamilyEdgeForcingMap Ledge v + Rs v) W) ≤ ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K n ϖ (ρ / (ocEpsilon q Λ m)) (volume.restrict (Set.Icc a b)) π W) ∧
    (∀ v, ∑ u, schurMatrix 1 (ρ / (ocEpsilon q Λ m)) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) ∧
    (∀ u, ∑ v, schurMatrix 1 (ρ / (ocEpsilon q Λ m)) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) := by
  have hpkg := windowCover_window_reference_constructed_edge_package
    D Kmax Jchart Jm hchart hmol Cm Cchart
  obtain ⟨Cprep, hCprep, hmaps⟩ := hpkg
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc hcover σ hσ henv ic a b hab hwindow θ hrow hcol Ks hdesc hKs hθ hqJ hlength
  classical
  dsimp only
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
  let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
  let A := preparationReferenceCellSourceCoefficient F hφ σ
    ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc
  have hmapsA := hmaps
    α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha F hmeas hwmeas π hπ K hK actual B hB hc hcover σ hσ henv
    yc ic a b hab.le hwindow θ hrow hcol Ks hdesc hKs hθ
  obtain ⟨Rs, Ledge, hsource, hrem, hmass, hrows, hcols⟩ := hmapsA
  have hmet := windowCover_exists_metric_source_originalEdge_allMoment_maps (h := h)
      hΛ hφ cov Ks hqJ K hK ic a b hwindow ϖ rfl D hD A Ledge Rs hsource.1
  obtain ⟨diag, positive, Rm, hmetric, _hfull⟩ := hmet
  have hresp := windowCover_frozen_family_component_all_moment_response (h := h)
    hΛ hζ hφ cov K hK ic a b hab hwindow hgsmall hg0 hlength ϖ rfl
  obtain ⟨R, hR⟩ := hresp
  exact ⟨Rs, Ledge, diag, positive, Rm, R, hsource, hmetric, hR, hrem, hmass, hrows, hcols⟩
end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual preparation inputs construct a physical solution and its native
first-block homogeneous response pair with the same localized initial datum. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

variable {Bcover g g0 strain B₀ lam Cb : ℝ} {qJ : ℕ} {CG : ℕ → ℝ} {y₀ : Vec 2}

theorem exists_preparation_reference_cell_initial_homogeneous_response_pair
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (H : ℕ) (hdepth : F.HasDepthAtMost H)
    {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (Kmax Jm : ℕ) (hKmax : ∀ j, K j ≤ Kmax)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ j, 0 < π j)
    (B : ι → ι → ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (ν e : ℝ) (hν : 0 < ν) (heScale : e = ocEpsilon q Λ m) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1))
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
    {N : ℕ} (he : e⁻¹ = N)
    (hζ : IsFastProfile ζ)
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν Bcover a b ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ Pcover y₀)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (ϖ : ℝ) (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m))
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (f : ∀ i, TorusHk (K i) (h i))
    (d : ℝ) (hcd : (e⁻¹) ^ 2 * (ν * a) < d)
    (hwindow : Icc ((e⁻¹) ^ 2 * (ν * a)) d ⊆
      windowCoverChartWindow α q Λ m ν a b l₀ Pcover (windowCoverReferenceChartIndex Pcover))
    (hlength : d - (e⁻¹) ^ 2 * (ν * a) ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * b))
    (hblock : ∀ t ∈ Icc ((e⁻¹) ^ 2 * (ν * a)) d,
      ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    :
    ∃ (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i)),
    IsCoupledWeakSolutionPlane ν a b (streamVel (Φ m)) D K
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K)
      (fun j => spatialPatchLocalization hζ Npatch hNpatch patch (K j) (f j))
      (fun _ _ => 0) (fun _ _ => 0) u w ∧
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀ (windowCoverReferenceChartIndex Pcover)
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hKmax j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
        (Nat.add_le_add_right (show K j ≤ Jchart by have hh := hKmax j; omega) 1) t (w j t)
    IsCoupledWeakSolutionPlane 1 ((e⁻¹) ^ 2 * (ν * a)) d
      (ocCellDrift α q Λ ζ m ν yc) D K
      (planeMetricSourceCoefficient K D
        (ocCellMetric α q Λ m (Φ (m - 1)) hφ l₀ ν yc)
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
          ν e (ocEpsilon q Λ (m - 1)) actual K yc))
      (fun j => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hKmax j; omega) a (spatialPatchLocalization hζ Npatch hNpatch patch (K j) (f j))))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (W j (ν⁻¹ * (e ^ 2 * t)))) ∧
    ∃ (Z : ∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ (ρ / e) 0
        (volume.restrict (Icc ((e⁻¹) ^ 2 * (ν * a)) d)))
      (u0 : ∀ j, ℝ → PlaneHk univ (K j) (h j))
      (w0 : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ l₀ ν yc t 0))
        (fun _ j => K j) ((e⁻¹) ^ 2 * (ν * a)) d (ocCellDrift α q Λ ζ m ν yc)
        (fun _ j => planeCarrierAffine e (hρ.trans_le hρe).ne' yc
          (preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
            (by have hh := hKmax j; omega) a
            (spatialPatchLocalization hζ Npatch hNpatch patch (K j) (f j))))
        (fun _ _ _ => 0) (fun _ j => u0 j) (fun _ j => w0 j) ∧
      ∀ j, PlaneTimeAllMomentRepresents (K j + 1) ϖ (ρ / e) 0
        (volume.restrict (Icc ((e⁻¹) ^ 2 * (ν * a)) d)) (Z j) (w0 j) := by
  have hT0 := exists_actualPreparation_planeEndpoint_linearMap K Kmax hKmax
    ρ ν hρ hν a b hab D F H hdepth α q Λ m Φ ζ hseq (Φ (m - 1)) hφ
    Cpad Cage Npad Jchart Cchart l₀ Pcover hprep e (ocEpsilon q Λ (m - 1)) actual
    hmeas hwmeas rfl hρe heE Jm hchart hmol Cm π hπ B hB henv
  obtain ⟨_T, hTsol⟩ := hT0
  have hTs := hTsol (fun j => spatialPatchLocalization hζ Npatch hNpatch patch (K j) (f j))
  obtain ⟨u, w, hs, _⟩ := hTs
  refine ⟨u, w, hs, ?_⟩
  exact preparation_reference_cell_initial_homogeneous_response_pair F hab ρ hρ K hdesc hD
    hprep hcover hTau ha Kmax Jm hKmax hchart hmol Cm π hπ B hB hmeas hwmeas
    hΛ hm hseq ν e hν heScale hρe heE henv actual hT he hζ cov hgsmall hg0 ϖ hϖ
    Npatch hNpatch patch f u w d hcd hwindow hlength hdb hblock hs
end

/-! The physical solution is chosen for every datum, and its exact native
first-block transfer uses the common linear localized initial family map. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

variable {Bcover g g0 strain B₀ lam Cb : ℝ} {qJ : ℕ} {CG : ℕ → ℝ} {y₀ : Vec 2}

theorem exists_preparation_reference_cell_coupled_solution_family
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (H : ℕ) (hdepth : F.HasDepthAtMost H)
    {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (Kmax Jm : ℕ) (hKmax : ∀ j, K j ≤ Kmax)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ j, 0 < π j)
    (B : ι → ι → ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (ν e : ℝ) (hν : 0 < ν) (heScale : e = ocEpsilon q Λ m) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1))
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
    {N : ℕ} (he : e⁻¹ = N)
    (hζ : IsFastProfile ζ)
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν Bcover a b ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ Pcover y₀)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (ϖ : ℝ) (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m))
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (d : ℝ) (hcd : (e⁻¹) ^ 2 * (ν * a) < d)
    (hwindow : Icc ((e⁻¹) ^ 2 * (ν * a)) d ⊆
      windowCoverChartWindow α q Λ m ν a b l₀ Pcover (windowCoverReferenceChartIndex Pcover))
    (hlength : d - (e⁻¹) ^ 2 * (ν * a) ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * b))
    (hblock : ∀ t ∈ Icc ((e⁻¹) ^ 2 * (ν * a)) d,
      ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    :
    ∃ (u : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk univ (K i) (h i))
      (w : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk univ (K i + 1) (h i)),
    ∀ f,
    IsCoupledWeakSolutionPlane ν a b (streamVel (Φ m)) D K
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K)
      (fun j => spatialPatchLocalization hζ Npatch hNpatch patch (K j) (f j))
      (fun _ _ => 0) (fun _ _ => 0) (u f) (w f) ∧
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀ (windowCoverReferenceChartIndex Pcover)
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hKmax j; omega) t (u f j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
        (Nat.add_le_add_right (show K j ≤ Jchart by have hh := hKmax j; omega) 1) t (w f j t)
    IsCoupledWeakSolutionPlane 1 ((e⁻¹) ^ 2 * (ν * a)) d
      (ocCellDrift α q Λ ζ m ν yc) D K
      (planeMetricSourceCoefficient K D
        (ocCellMetric α q Λ m (Φ (m - 1)) hφ l₀ ν yc)
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
          ν e (ocEpsilon q Λ (m - 1)) actual K yc))
      (preparationReferenceCellLocalizedInitialFamilyLinearMap hprep hcover hTau ha K
        (fun j => by have hh := hKmax j; omega) hab hζ Npatch hNpatch patch e
        (hρ.trans_le hρe).ne' yc f)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (W j (ν⁻¹ * (e ^ 2 * t)))) := by
  classical
  have hall := fun f : ∀ i, TorusHk (K i) (h i) =>
    exists_preparation_reference_cell_initial_homogeneous_response_pair F H hdepth hab
      ρ hρ K hdesc hD hprep hcover hTau ha Kmax Jm hKmax hchart hmol Cm π hπ B hB
      hmeas hwmeas hΛ hm hseq ν e hν heScale hρe heE henv actual hT he hζ cov
      hgsmall hg0 ϖ hϖ Npatch hNpatch patch f d hcd hwindow hlength hdb hblock
  choose u w hphysical hnative using hall
  refine ⟨u, w, ?_⟩
  intro f
  refine ⟨hphysical f, ?_⟩
  have hinit : preparationReferenceCellLocalizedInitialFamilyLinearMap hprep hcover hTau ha K
      (fun j => by have hh := hKmax j; omega) hab hζ Npatch hNpatch patch e
      (hρ.trans_le hρe).ne'
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀
        (windowCoverReferenceChartIndex Pcover)) f =
      (fun j => planeCarrierAffine e (hρ.trans_le hρe).ne'
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀
          (windowCoverReferenceChartIndex Pcover))
        (preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
          (by have hh := hKmax j; omega) a
          (spatialPatchLocalization hζ Npatch hNpatch patch (K j) (f j)))) := by
    funext j
    exact preparationReferenceCellLocalizedInitialFamilyLinearMap_apply hprep hcover hTau ha
      K (fun j => by have hh := hKmax j; omega) hab hζ Npatch hNpatch patch e
      (hρ.trans_le hρe).ne' _ f j
  dsimp only
  rw [hinit]
  exact (hnative f).1
end

end AVRegularity.CycleJointProofs
end
end

section
/-! Actual preparation inputs construct the feedback maps and homogeneous base,
then give a linear retained endpoint and a genuine coupled error representation. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

universe u v w x y


variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]


local instance coverReferenceRetainedEndpointNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance coverReferenceRetainedEndpointNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance coverReferenceRetainedEndpointFluxNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance coverReferenceRetainedEndpointFluxNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance coverReferenceRetainedEndpointScalarCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverReferenceRetainedEndpointScalarCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverReferenceRetainedEndpointFluxCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance coverReferenceRetainedEndpointFluxCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem windowCover_reference_retained_linear_endpoint_all_moments_bound (D Ks Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart CG : ℕ → ℝ) :
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CRemainder := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    let Cgraph := pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CRemainder) Cm
    ∃ Cprep CT CR Cterminal : ℝ, 1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (_hζ : IsFastProfile ζfast) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (_ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (a b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P (windowCoverReferenceChartIndex P) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        Ks + 1 + Kmax ≤ qJ → b - a ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
      (windowCoverReferenceChartIndex P)
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀
      (windowCoverReferenceChartIndex P)
    let v := ocCellDrift α q Λ ζfast m ν yc
    let A := preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc
    ∀ {X : Type y} [AddCommGroup X] [Module ℝ X],
    ∀ (n H N J : ℕ) (_hdepth : F.HasDepthAtMost H) (Cw : ℕ → ℝ)
      (_W : ChartWeights G v a (b - a) ϖ 0 N Cw)
      (_WM : ChartWeights (fun t _ => G t 0) v a (b - a) ϖ 0 N Cw)
      (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (_hf : ∀ ξ r i, weightedFactorialNormSq r ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i) ≠ ⊤)
      (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (_hH : ∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K
        (planeMetricSourceCoefficient K D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0) (uH ξ) (wH ξ))
      (L : ℝ) (_hL : 1 ≤ L)
      (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
      (_hgain : ENNReal.ofReal (CT * g * ζ) ≤ 1)
      (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
      (τ : ℝ) (_hτ : τ ∈ Set.Icc a b),
    ∃ Rs : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    ∃ Ledge : ∀ v u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    ∃ diag positive Rm : ∀ v, PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc a b)),
    ∃ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc a b)),
    (((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (nativeFamilyEdgeForcingMap Ledge v + Rs v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
        (fun x t z => ∑ u, ∑ γ, naturalFamilyTaylorRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
          (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ (fun p => (F.piece p).anchor)
          ((l₀ : ℝ) * ocTauPP α q Λ m) (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc ϖ (ρ / (ocEpsilon q Λ m))
          (volume.restrict (Set.Icc a b)) v u γ (x u) t z)
        (nativeFamilyEdgeForcingMap Ledge v)) ∧
      (∀ v u, ¬ Nonempty (F.Γ v u) → Ledge v u = 0) ∧
      (∀ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
        HasSourceDegreeOn F 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))) ∧
    ((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
          (planeTimeAllMomentCarrierToLp (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) X t)) (diag v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) X t)) (positive v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux
          (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) X t)) (Rm v))) ∧
    (∀ v, IsPlaneComponentAllMomentResponse (E := h v) (fun t => G t 0)
      (ocCellDrift α q Λ ζfast m ν yc) (K v) a b ϖ (ρ / ocEpsilon q Λ m) (R v))) ∧
        ∃ u0 : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i),
        ∃ w0 : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i),
        ∃ Z : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ (ρ / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc a b))),
        (∀ ξ, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => (fun t => G t 0) t)) (fun _ i => K i) a b v
      (fun _ i => V₀ ξ i) (fun _ _ _ => 0) (fun _ i => u0 ξ i) (fun _ i => w0 ξ i)) ∧
        (∀ ξ i, PlaneTimeAllMomentRepresents (E := h i) (K i + 1) ϖ (ρ / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b))
      (Z ξ i) (w0 ξ i)) ∧
        let Lfull := nativeMetricSourceFiveTermForcingMap diag positive Ledge Rm Rs
        let Ldiag := nativeDiagonalForcingMap diag
        let C := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
        let cm := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2)
        let cs := ENNReal.ofReal ((Cgraph * θ) ^ 2)
        let ct := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)
        let θcap := ENNReal.ofReal θ
        let ζcap := ENNReal.ofReal ζ
        let η := ENNReal.ofReal (Cterminal * g * ζ)
        let G0 := fun ξ => ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} N Kmax Cw) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i)
        let U := fun ξ => finiteResponse 1 (nativeDiagonalResponseOperator R positive)
          (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) (Z ξ)
        let Wret := fun ξ => ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U ξ j k
        let Tret := fun ξ => ∑ k ∈ Finset.range (H + 1), U ξ J k
        let Q := fun ξ i => positive i (Wret ξ i) + nativeFamilyEdgeForcingMap Ledge i (Wret ξ) - positive i (Tret ξ i)
        ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
        (∀ ξ r i, weightedFactorialNormSq r ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (T ξ i) ≠ ⊤) ∧
        ∀ ξ, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
          (ferr : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))),
          IsCoupledWeakSolutionPlane 1 a b v D K
            (planeMetricSourceCoefficient K D G A) (fun _ => 0) ferr (fun _ _ => 0)
            (fun i t => uH ξ i t - u i t) (fun i t => wH ξ i t - w i t) ∧
          (∀ i, PlaneTimeAllMomentRepresents (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b))
            (-(Q ξ i - Lfull i (Wret ξ) + Ldiag i (Wret ξ))) (ferr i)) ∧
          (∀ i, PlaneTimeAllMomentRepresents (E := h i) (K i + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) (Wret ξ i) (w i)) ∧
          (∀ i, T ξ i = u i τ) ∧
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (uH ξ i τ - T ξ i)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζcap ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0 ξ)) := by
  intro Cjet Cflow Cpiola CRemainder Cgraph
  have hm := windowCover_reference_feedback_maps.{u, v, w, x}
    D Kmax Jchart Jm hchart hmol Cm Cchart
  let Cprep := hm.choose
  have hCprep := hm.choose_spec.1
  have hmaps := hm.choose_spec.2
  have he := windowCover_constructed_homogeneous_retained_linear_endpoint_all_moments_bound.{u, v, w, x, y}
    Ks Kmax CG
  let CT := he.choose
  let CR := he.choose_spec.choose
  let Cterminal := he.choose_spec.choose_spec.choose
  have hs := he.choose_spec.choose_spec.choose_spec
  have hCT := hs.1
  have hCR := hs.2.1
  have hCterminal := hs.2.2.1
  refine ⟨Cprep, CT, CR, Cterminal, hCprep, hCT, hCR, hCterminal, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ y₀ cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc henv a b hab hwindow θ hrow hcol hdesc hKs hθ hqJ hlength
    ϖ ζ yc G v A X _ _ n H N J hdepth Cw W WM V₀ hf uH wH hH L hL hreserve hgain hN τ hτ
  classical
  let ic := windowCoverReferenceChartIndex P
  have hd := hmaps
    α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha hgsmall hg0 hD F hmeas hwmeas π hπ K hK actual B hB
    hc henv a b hab hwindow θ hrow hcol Ks hdesc hKs hθ hqJ hlength
  let Rs := hd.choose
  let Ledge := hd.choose_spec.choose
  let diag := hd.choose_spec.choose_spec.choose
  let positive := hd.choose_spec.choose_spec.choose_spec.choose
  let Rm := hd.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let R := hd.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hcert := hd.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hsource := hcert.1
  have hmetric := hcert.2.1
  have hR := hcert.2.2.1
  have hrem := hcert.2.2.2.1
  have hrows := hcert.2.2.2.2.2.1
  have hcols := hcert.2.2.2.2.2.2
  refine ⟨Rs, Ledge, diag, positive, Rm, R,
    ⟨hsource, hmetric, hR⟩, ?_⟩
  have hsc := windowCover_native_subwindow_scales hΛ hφ cov ic a b hwindow
  have hsub := hsc.1
  have hϖ := hsc.2.2.1
  have hscale := hsc.2.2.2.1
  have hζslow := hsc.2.2.2.2.1
  have hζslow1 := hsc.2.2.2.2.2.1
  have hδ := hsc.2.2.2.2.2.2
  have hdata := preparationReferenceCellSource_pointwise_subwindow_data
    F hc ν (ocEpsilon q Λ m) ρ cov.pos.1 cov.pos.2.2 cov.rho_e heE K Kmax Jm
    hK hchart hmol Cm hmeas hwmeas actual yc π hπ B hB henv a b
    (ρ / ocEpsilon q Λ m) hsub
  have hA := hdata.1
  have hAsmooth := hdata.2.1
  have hAm := hdata.2.2.1
  exact hs.2.2.2 (ι := ι) (h := h)
    α q Λ m ζfast hζ Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ l₀ P y₀ cov
    hΛ heE ic a b hab hwindow hqJ hgsmall hg0 hlength
    (ρ / ocEpsilon q Λ m) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) v G rfl rfl rfl rfl
    n D H N Cw Cprep Cgraph θ hθ π hπ K hK ϖ rfl W hD A hA hAsmooth hAm hrows hcols
    (sourceDepthRank F H) (sourceDepthRank_le F H)
    (fun i j hr d => preparationReferenceCellSourceCoefficient_zero_of_rank F hφ H hdepth
      ((l₀ : ℝ) * ocTauPP α q Λ m) ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
      actual K yc i j d hr)
    V₀ hf uH wH hH (fun t => G t 0) R positive Ledge F J hdepth
    (naturalFamilyTaylorRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
      (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ (fun p => (F.piece p).anchor)
      ((l₀ : ℝ) * ocTauPP α q Λ m) (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc
      ϖ (ρ / ocEpsilon q Λ m) (volume.restrict (Set.Icc a b)))
    (naturalFamilyTaylorRawConstituent_zero Ks F (F.locally_finite tS tZ).toFinset actual K
      (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ (fun p => (F.piece p).anchor)
      ((l₀ : ℝ) * ocTauPP α q Λ m) (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc
      ϖ (ρ / ocEpsilon q Λ m) (volume.restrict (Set.Icc a b)))
    hsource.2.1 hR Rs diag Rm rfl hsource.1 hmetric.1 hmetric.2.1 hmetric.2.2 WM
    L (Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) hL
    hζslow hζslow1 hϖ hscale hδ hreserve hrem hgain hN τ hτ

end AVRegularity.CycleJointProofs
end
end

section
/-! Actual preparation inputs construct the feedback maps and homogeneous base,
then give a linear retained endpoint and a genuine coupled error representation. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

universe u v w x y


variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]


local instance coverWindowReferenceRetainedEndpointNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance coverWindowReferenceRetainedEndpointNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance coverWindowReferenceRetainedEndpointFluxNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance coverWindowReferenceRetainedEndpointFluxNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance coverWindowReferenceRetainedEndpointScalarCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverWindowReferenceRetainedEndpointScalarCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverWindowReferenceRetainedEndpointFluxCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance coverWindowReferenceRetainedEndpointFluxCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem windowCover_window_reference_retained_linear_endpoint_all_moments_bound (D Ks Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart CG : ℕ → ℝ) :
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CRemainder := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    let Cgraph := pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CRemainder) Cm
    ∃ Cprep CT CR Cterminal : ℝ, 1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (_hζ : IsFastProfile ζfast) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (_ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ ∈ Set.Icc tS tZ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (ic : Fin (P + 2)) (a b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        Ks + 1 + Kmax ≤ qJ → b - a ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
      ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀
      ic
    let v := ocCellDrift α q Λ ζfast m ν yc
    let A := preparationReferenceCellSourceCoefficient F hφ σ
      ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc
    ∀ {X : Type y} [AddCommGroup X] [Module ℝ X],
    ∀ (n H N J : ℕ) (_hdepth : F.HasDepthAtMost H) (Cw : ℕ → ℝ)
      (_W : ChartWeights G v a (b - a) ϖ 0 N Cw)
      (_WM : ChartWeights (fun t _ => G t 0) v a (b - a) ϖ 0 N Cw)
      (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (_hf : ∀ ξ r i, weightedFactorialNormSq r ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i) ≠ ⊤)
      (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (_hH : ∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K
        (planeMetricSourceCoefficient K D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0) (uH ξ) (wH ξ))
      (L : ℝ) (_hL : 1 ≤ L)
      (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
      (_hgain : ENNReal.ofReal (CT * g * ζ) ≤ 1)
      (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
      (τ : ℝ) (_hτ : τ ∈ Set.Icc a b),
    ∃ Rs : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    ∃ Ledge : ∀ v u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    ∃ diag positive Rm : ∀ v, PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc a b)),
    ∃ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc a b)),
    (((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ σ ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (nativeFamilyEdgeForcingMap Ledge v + Rs v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
        (fun x t z => ∑ u, ∑ γ, naturalFamilyTaylorRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
          (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ (fun p => (F.piece p).anchor)
          σ (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc ϖ (ρ / (ocEpsilon q Λ m))
          (volume.restrict (Set.Icc a b)) v u γ (x u) t z)
        (nativeFamilyEdgeForcingMap Ledge v)) ∧
      (∀ v u, ¬ Nonempty (F.Γ v u) → Ledge v u = 0) ∧
      (∀ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
        HasSourceDegreeOn F 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))) ∧
    ((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
          (planeTimeAllMomentCarrierToLp (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) X t)) (diag v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) X t)) (positive v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc a b))
        (fun X t => planeMatrixGradientFlux
          (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (E := h v) (K v + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) X t)) (Rm v))) ∧
    (∀ v, IsPlaneComponentAllMomentResponse (E := h v) (fun t => G t 0)
      (ocCellDrift α q Λ ζfast m ν yc) (K v) a b ϖ (ρ / ocEpsilon q Λ m) (R v))) ∧
        ∃ u0 : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i),
        ∃ w0 : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i),
        ∃ Z : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ (ρ / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc a b))),
        (∀ ξ, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => (fun t => G t 0) t)) (fun _ i => K i) a b v
      (fun _ i => V₀ ξ i) (fun _ _ _ => 0) (fun _ i => u0 ξ i) (fun _ i => w0 ξ i)) ∧
        (∀ ξ i, PlaneTimeAllMomentRepresents (E := h i) (K i + 1) ϖ (ρ / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b))
      (Z ξ i) (w0 ξ i)) ∧
        let Lfull := nativeMetricSourceFiveTermForcingMap diag positive Ledge Rm Rs
        let Ldiag := nativeDiagonalForcingMap diag
        let C := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
        let cm := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2)
        let cs := ENNReal.ofReal ((Cgraph * θ) ^ 2)
        let ct := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)
        let θcap := ENNReal.ofReal θ
        let ζcap := ENNReal.ofReal ζ
        let η := ENNReal.ofReal (Cterminal * g * ζ)
        let G0 := fun ξ => ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} N Kmax Cw) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i)
        let U := fun ξ => finiteResponse 1 (nativeDiagonalResponseOperator R positive)
          (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) (Z ξ)
        let Wret := fun ξ => ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U ξ j k
        let Tret := fun ξ => ∑ k ∈ Finset.range (H + 1), U ξ J k
        let Q := fun ξ i => positive i (Wret ξ i) + nativeFamilyEdgeForcingMap Ledge i (Wret ξ) - positive i (Tret ξ i)
        ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
        (∀ ξ r i, weightedFactorialNormSq r ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (T ξ i) ≠ ⊤) ∧
        ∀ ξ, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
          (ferr : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))),
          IsCoupledWeakSolutionPlane 1 a b v D K
            (planeMetricSourceCoefficient K D G A) (fun _ => 0) ferr (fun _ _ => 0)
            (fun i t => uH ξ i t - u i t) (fun i t => wH ξ i t - w i t) ∧
          (∀ i, PlaneTimeAllMomentRepresents (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b))
            (-(Q ξ i - Lfull i (Wret ξ) + Ldiag i (Wret ξ))) (ferr i)) ∧
          (∀ i, PlaneTimeAllMomentRepresents (E := h i) (K i + 1) ϖ (ρ / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) (Wret ξ i) (w i)) ∧
          (∀ i, T ξ i = u i τ) ∧
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (uH ξ i τ - T ξ i)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζcap ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0 ξ)) := by
  intro Cjet Cflow Cpiola CRemainder Cgraph
  have hm := windowCover_window_reference_feedback_maps.{u, v, w, x}
    D Kmax Jchart Jm hchart hmol Cm Cchart
  let Cprep := hm.choose
  have hCprep := hm.choose_spec.1
  have hmaps := hm.choose_spec.2
  have he := windowCover_constructed_homogeneous_retained_linear_endpoint_all_moments_bound.{u, v, w, x, y}
    Ks Kmax CG
  let CT := he.choose
  let CR := he.choose_spec.choose
  let Cterminal := he.choose_spec.choose_spec.choose
  have hs := he.choose_spec.choose_spec.choose_spec
  have hCT := hs.1
  have hCR := hs.2.1
  have hCterminal := hs.2.2.1
  refine ⟨Cprep, CT, CR, Cterminal, hCprep, hCT, hCR, hCterminal, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ y₀ cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc hcover σ hσ henv ic a b hab hwindow θ hrow hcol hdesc hKs hθ hqJ hlength
    ϖ ζ yc G v A X _ _ n H N J hdepth Cw W WM V₀ hf uH wH hH L hL hreserve hgain hN τ hτ
  classical
  have hd := hmaps
    α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha hgsmall hg0 hD F hmeas hwmeas π hπ K hK actual B hB
    hc hcover σ hσ henv ic a b hab hwindow θ hrow hcol Ks hdesc hKs hθ hqJ hlength
  let Rs := hd.choose
  let Ledge := hd.choose_spec.choose
  let diag := hd.choose_spec.choose_spec.choose
  let positive := hd.choose_spec.choose_spec.choose_spec.choose
  let Rm := hd.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let R := hd.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hcert := hd.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hsource := hcert.1
  have hmetric := hcert.2.1
  have hR := hcert.2.2.1
  have hrem := hcert.2.2.2.1
  have hrows := hcert.2.2.2.2.2.1
  have hcols := hcert.2.2.2.2.2.2
  refine ⟨Rs, Ledge, diag, positive, Rm, R,
    ⟨hsource, hmetric, hR⟩, ?_⟩
  have hsc := windowCover_native_subwindow_scales hΛ hφ cov ic a b hwindow
  have hsub := hsc.1
  have hϖ := hsc.2.2.1
  have hscale := hsc.2.2.2.1
  have hζslow := hsc.2.2.2.2.1
  have hζslow1 := hsc.2.2.2.2.2.1
  have hδ := hsc.2.2.2.2.2.2
  have hdata := preparationWindowReferenceCellSource_pointwise_subwindow_data
    F hc hcover σ hσ ν (ocEpsilon q Λ m) ρ cov.pos.1 cov.pos.2.2 cov.rho_e heE K Kmax Jm
    hK hchart hmol Cm hmeas hwmeas actual yc π hπ B hB henv a b
    (ρ / ocEpsilon q Λ m) hsub
  have hA := hdata.1
  have hAsmooth := hdata.2.1
  have hAm := hdata.2.2.1
  exact hs.2.2.2 (ι := ι) (h := h)
    α q Λ m ζfast hζ Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ l₀ P y₀ cov
    hΛ heE ic a b hab hwindow hqJ hgsmall hg0 hlength
    (ρ / ocEpsilon q Λ m) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) v G rfl rfl rfl rfl
    n D H N Cw Cprep Cgraph θ hθ π hπ K hK ϖ rfl W hD A hA hAsmooth hAm hrows hcols
    (sourceDepthRank F H) (sourceDepthRank_le F H)
    (fun i j hr d => preparationReferenceCellSourceCoefficient_zero_of_rank F hφ H hdepth
      σ ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
      actual K yc i j d hr)
    V₀ hf uH wH hH (fun t => G t 0) R positive Ledge F J hdepth
    (naturalFamilyTaylorRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
      (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ (fun p => (F.piece p).anchor)
      σ (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc
      ϖ (ρ / ocEpsilon q Λ m) (volume.restrict (Set.Icc a b)))
    (naturalFamilyTaylorRawConstituent_zero Ks F (F.locally_finite tS tZ).toFinset actual K
      (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ (fun p => (F.piece p).anchor)
      σ (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc
      ϖ (ρ / ocEpsilon q Λ m) (volume.restrict (Set.Icc a b)))
    hsource.2.1 hR Rs diag Rm rfl hsource.1 hmetric.1 hmetric.2.1 hmetric.2.2 WM
    L (Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) hL
    hζslow hζslow1 hϖ hscale hδ hreserve hrem hgain hN τ hτ

end AVRegularity.CycleJointProofs
end
end

section
/-! Focused endpoint and genuine coupled-error readout of the complete actual
 Taylor response producer. The producer retains the detailed source maps. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

universe u v w x y

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]


local instance coverWindowReferenceEndpointSummaryNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance coverWindowReferenceEndpointSummaryNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance coverWindowReferenceEndpointSummaryFluxNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance coverWindowReferenceEndpointSummaryFluxNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance coverWindowReferenceEndpointSummaryScalarCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverWindowReferenceEndpointSummaryScalarCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverWindowReferenceEndpointSummaryFluxCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance coverWindowReferenceEndpointSummaryFluxCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem windowCover_window_reference_retained_endpoint_summary (D Ks Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart CG : ℕ → ℝ) :
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CRemainder := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    let Cgraph := pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CRemainder) Cm
    ∃ Cprep CT CR Cterminal : ℝ, 1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (_hζ : IsFastProfile ζfast) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (_ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ ∈ Set.Icc tS tZ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (ic : Fin (P + 2)) (a b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        Ks + 1 + Kmax ≤ qJ → b - a ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
      ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀
      ic
    let v := ocCellDrift α q Λ ζfast m ν yc
    let A := preparationReferenceCellSourceCoefficient F hφ σ
      ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc
    ∀ {X : Type y} [AddCommGroup X] [Module ℝ X],
    ∀ (n H N J : ℕ) (_hdepth : F.HasDepthAtMost H) (Cw : ℕ → ℝ)
      (_W : ChartWeights G v a (b - a) ϖ 0 N Cw)
      (_WM : ChartWeights (fun t _ => G t 0) v a (b - a) ϖ 0 N Cw)
      (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (_hf : ∀ ξ r i, weightedFactorialNormSq r ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i) ≠ ⊤)
      (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (_hH : ∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K
        (planeMetricSourceCoefficient K D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0) (uH ξ) (wH ξ))
      (L : ℝ) (_hL : 1 ≤ L)
      (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
      (_hgain : ENNReal.ofReal (CT * g * ζ) ≤ 1)
      (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
      (τ : ℝ) (_hτ : τ ∈ Set.Icc a b),
        let C := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
        let cm := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2)
        let cs := ENNReal.ofReal ((Cgraph * θ) ^ 2)
        let ct := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)
        let θcap := ENNReal.ofReal θ
        let ζcap := ENNReal.ofReal ζ
        let η := ENNReal.ofReal (Cterminal * g * ζ)
        let G0 := fun ξ => ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} N Kmax Cw) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i)
        ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
        (∀ ξ r i, weightedFactorialNormSq r ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (T ξ i) ≠ ⊤) ∧
        ∀ ξ, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
          (ferr : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))),
          IsCoupledWeakSolutionPlane 1 a b v D K
            (planeMetricSourceCoefficient K D G A) (fun _ => 0) ferr (fun _ _ => 0)
            (fun i t => uH ξ i t - u i t) (fun i t => wH ξ i t - w i t) ∧
          (∀ i, T ξ i = u i τ) ∧
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (uH ξ i τ - T ξ i)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζcap ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0 ξ)) := by
  intro Cjet Cflow Cpiola CRemainder Cgraph
  have hr := windowCover_window_reference_retained_linear_endpoint_all_moments_bound.{u, v, w, x, y}
    D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG
  let Cprep := hr.choose
  let CT := hr.choose_spec.choose
  let CR := hr.choose_spec.choose_spec.choose
  let Cterminal := hr.choose_spec.choose_spec.choose_spec.choose
  have hs := hr.choose_spec.choose_spec.choose_spec.choose_spec
  refine ⟨Cprep, CT, CR, Cterminal, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ y₀ cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc hcover σ hσ henv ic a b hab hwindow θ hrow hcol hdesc hKs hθ hqJ hlength
    ϖ ζ yc G v A X _ _ n H N J hdepth Cw W WM V₀ hf uH wH hH L hL hreserve hgain hN τ hτ
  have hp := hs.2.2.2.2 (X := X) α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ
    g g0 strain B₀ lam Cb qJ y₀ cov hΛ heE ha hgsmall hg0 hD F hmeas hwmeas
    π hπ K hK actual B hB hc hcover σ hσ henv ic a b hab hwindow
    θ hrow hcol hdesc hKs hθ hqJ hlength n H N J hdepth Cw W WM V₀ hf uH wH hH
    L hL hreserve hgain hN τ hτ
  refine hp.elim fun _ h1 => h1.elim fun _ h2 => h2.elim fun _ h3 => h3.elim fun _ h4 =>
    h4.elim fun _ h5 => h5.elim fun _ h6 => h6.2.elim fun _ h7 => h7.elim fun _ h8 =>
    h8.elim fun _ h9 => h9.2.2.elim fun T hT => ?_
  refine ⟨T, hT.1, fun ξ => ?_⟩
  exact (hT.2 ξ).elim fun u h1 => h1.elim fun w h2 => h2.elim fun ferr hh =>
    ⟨u, w, ferr, hh.1, hh.2.2.2.1, hh.2.2.2.2⟩

end AVRegularity.CycleJointProofs
end
end
