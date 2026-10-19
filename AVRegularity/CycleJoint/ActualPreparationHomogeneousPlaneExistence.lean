-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.WindowCoverFrozenHomogeneousFamilyLinearMap
import AVRegularity.CycleJoint.OriginalFamilyNaturalRemainderDescendingIdentity
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction
import AVRegularity.CycleJoint.ActualPreparationHomogeneousFamilyNativeTraceLinearMap
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
public import AVRegularity.CycleJoint.PointwiseNativeTransportIdentityPrice
import AVenhance.Infra.Classical.Drift

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! One chart-window construction supplies the entire family's scalar response
maps before any finite Taylor response is assembled. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

variable (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))

include hΛ hζ cov hK hu hwindow hgsmall hg0 hlength hϖ in
theorem windowCover_frozen_family_component_all_moment_response :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v))
      (K v) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρs / ocEpsilon q Λ m) 0
        (volume.restrict (Set.Icc u0 u1)),
      ∀ v, IsPlaneComponentAllMomentResponse (E := h v)
        (fun t => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0)
        (ocCellDrift α q Λ ζ m ν yc) (K v) u0 u1 ϖ (ρs / ocEpsilon q Λ m) (R v) := by
  classical
  have hRi (v : ι) := windowCover_frozen_component_all_moment_response (E := h v)
    hΛ hζ hφ cov (K v) (hK v) i u0 u1 hu hwindow hgsmall hg0 hlength ϖ hϖ
  choose R hR using hRi
  exact ⟨R, hR⟩

end AVRegularity.CycleJointProofs
end
end

section
/-! The actual cover supplies the preparation-domain and slow-scale inputs of
its original-edge source decomposition on every certified native subwindow. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

theorem windowCover_reference_constructed_edge_package (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (CG : ℕ → ℝ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (_ha : 0 ≤ ocA α q Λ (m - 1)),
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (ic : Fin (P + 2)) (a b : ℝ) (_hab : a ≤ b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        ∀ (Ks : ℕ), F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    ∃ Rs : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    ∃ Ledge : ∀ v u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    ((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
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
    (let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CR := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
      (volume.restrict (Set.Icc a b))) (n : ℕ),
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / (ocEpsilon q Λ m)) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
        (Rs v Z) τ)
      ∂volume.restrict (Set.Icc a b)) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) *
        (pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CR) Cm * θ)) ^ 2) *
      ∫⁻ τ, ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + (Ks + 1))
        ϖ 0 (ρ / (ocEpsilon q Λ m)) (K u)
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
          (volume.restrict (Set.Icc a b)) (Z u) τ) ∂volume.restrict (Set.Icc a b)) ∧
    (∀ W n, planeAllMomentFamilyEnergy K n ϖ (ρ / (ocEpsilon q Λ m)) (volume.restrict (Set.Icc a b)) π
      (fun v => (nativeFamilyEdgeForcingMap Ledge v + Rs v) W) ≤ ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K n ϖ (ρ / (ocEpsilon q Λ m)) (volume.restrict (Set.Icc a b)) π W) ∧
    (∀ v, ∑ u, schurMatrix 1 (ρ / (ocEpsilon q Λ m)) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) ∧
    (∀ u, ∑ v, schurMatrix 1 (ρ / (ocEpsilon q Λ m)) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) := by
  obtain ⟨Cprep, hCprep, hmaps⟩ := preparation_reference_cell_constructed_edge_package
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc henv yc ic a b hab hwindow θ hrow hcol Ks hdesc hKs hθ
  dsimp only
  obtain ⟨hsub, htime, hϖ, hscale, hζ, _hζ1, hδ⟩ :=
    windowCover_native_subwindow_scales hΛ hφ cov ic a b hwindow
  exact hmaps α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad l₀ P
    ν (ocEpsilon q Λ m) ρ cov.pos.1 cov.pos.2.2 cov.rho_e heE
    F hmeas hwmeas π hπ K hK actual B hB hc henv yc a b
    (ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)) hab hsub θ hrow hcol
    Ks hdesc hKs hθ (Construction.Stream.ocTauPP_pos hΛ).le ha
    (Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))
    hϖ hscale hζ hδ htime

end AVRegularity.CycleJointProofs
end
end

section
/-! The same actual preparation source carries both its Schur estimate and its
original natural Taylor remainder estimate. The Schur constant precedes all
family data and even the chosen Taylor order. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

theorem preparation_window_reference_cell_source_maps_with_schur_and_remainder (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ ∈ Set.Icc tS tZ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (a b ϖ : ℝ) (_hab : a ≤ b),
          Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        ∀ (Ks : ℕ), F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        0 ≤ ocA α q Λ (m - 1) →
        ∀ ζ : ℝ, 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ →
        e / ocEpsilon q Λ (m - 1) = ζ * ϖ →
        (∀ τ ∈ Set.Icc a b, ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ) →
    ∃ T : ∀ v u, F.Γ v u → Fin D → (F.locally_finite tS tZ).toFinset →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    ∃ Lfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    (((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ σ ν e (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (Lfull v)) ∧
    let Rs := nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p)
    ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
      (fun x τ z => ∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p : (F.locally_finite tS tZ).toFinset,
        naturalFamilyTaylorNativeArray Ks F p.val (actual p.val) v u γ (ν⁻¹ * e ^ 2) hφ
          (F.piece p.val).anchor σ e (ocEpsilon q Λ (m - 1)) yc (j.val + 1) τ z
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
              (volume.restrict (Set.Icc a b)) (x u) τ) (j.val + 1) I z)))
      (Lfull v - Rs v) ∧ Lfull v = (Lfull v - Rs v) + Rs v) ∧
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CR := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))) (n : ℕ),
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
        (nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p) v Z) τ)
      ∂volume.restrict (Set.Icc a b)) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) *
        (pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CR) Cm * θ)) ^ 2) *
      ∫⁻ τ, ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + (Ks + 1))
        ϖ 0 (ρ / e) (K u)
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
          (volume.restrict (Set.Icc a b)) (Z u) τ) ∂volume.restrict (Set.Icc a b)) ∧
    (∀ W n, planeAllMomentFamilyEnergy K n ϖ (ρ / e) (volume.restrict (Set.Icc a b)) π
      (fun v => Lfull v W) ≤ ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K n ϖ (ρ / e) (volume.restrict (Set.Icc a b)) π W) ∧
    (∀ v, ∑ u, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) ∧
    (∀ u, ∑ v, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) := by
  obtain ⟨Cprep, hCprep, hschur⟩ := preparation_window_reference_cell_source_subwindow_schur_budget
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB hc hcover σ hσ henv
    yc a b ϖ hab hsub θ hrow hcol Ks hdesc hKs hθ ha ζ hϖ hscale hζ hδ htime
  obtain ⟨T, Lfull, hsplit, hrem⟩ := exists_preparationWindowReferenceCellSourceMaps_with_remainder_budget
    F hc hcover σ hσ ν e ρ hν hρ hρe heE actual K hdesc Ks yc a b ϖ hab Kmax Jm hK hchart _hmol
    Cm hmeas hwmeas π hπ B hB henv hsub hKs θ hθ hrow hcol ha ζ hϖ hscale hζ hδ htime
  have he : 0 < e := hρ.trans_le hρe
  have hr : 0 < ρ / e := div_pos hρ he
  obtain ⟨hA, hC, _, _⟩ := preparationWindowReferenceCellSource_pointwise_subwindow_data F hc hcover σ hσ ν e ρ
    hν hρ hρe heE K Kmax Jm hK hchart _hmol Cm hmeas hwmeas actual yc π hπ B hB henv
    a b (ρ / e) hsub
  have hentry := hschur α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hc hcover σ hσ henv yc a b hsub
  have hrow' v : ∑ u, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ := by
    calc
      _ ≤ ∑ u, Cprep * B v u := Finset.sum_le_sum (fun u _ => hentry v u)
      _ = Cprep * ∑ u, B v u := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow v) (zero_le_one.trans hCprep)
  have hcol' u : ∑ v, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ := by
    calc
      _ ≤ ∑ v, Cprep * B v u := Finset.sum_le_sum (fun v _ => hentry v u)
      _ = Cprep * ∑ v, B v u := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcol u) (zero_le_one.trans hCprep)
  refine ⟨T, Lfull, ⟨hsplit, hrem⟩, ?_, hrow', hcol'⟩
  intro W n
  exact planeRaw_allMoment_coupling_mass_budget hab ϖ (ρ / e) hr K D _ hA hC Lfull hsplit.1
    π hπ (Cprep * θ) hrow' hcol' W n

end AVRegularity.CycleJointProofs
end
end

section
/-! The same actual preparation source carries both its Schur estimate and its
original natural Taylor remainder estimate. The Schur constant precedes all
family data and even the chosen Taylor order. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

theorem preparation_window_reference_cell_constructed_edge_package (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ ∈ Set.Icc tS tZ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (a b ϖ : ℝ) (_hab : a ≤ b),
          Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        ∀ (Ks : ℕ), F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        0 ≤ ocA α q Λ (m - 1) →
        ∀ ζ : ℝ, 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ →
        e / ocEpsilon q Λ (m - 1) = ζ * ϖ →
        (∀ τ ∈ Set.Icc a b, ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ) →
    ∃ Rs : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b)),
    ∃ Ledge : ∀ v u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b)),
    ((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ σ ν e (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (nativeFamilyEdgeForcingMap Ledge v + Rs v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
        (fun x t z => ∑ u, ∑ γ, naturalFamilyTaylorRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
          (ν⁻¹ * e ^ 2) hφ (fun p => (F.piece p).anchor)
          σ e (ocEpsilon q Λ (m - 1)) yc ϖ (ρ / e)
          (volume.restrict (Set.Icc a b)) v u γ (x u) t z)
        (nativeFamilyEdgeForcingMap Ledge v)) ∧
      (∀ v u, ¬ Nonempty (F.Γ v u) → Ledge v u = 0) ∧
      (∀ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b)),
        HasSourceDegreeOn F 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))) ∧
    (let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CR := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))) (n : ℕ),
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
        (Rs v Z) τ)
      ∂volume.restrict (Set.Icc a b)) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) *
        (pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CR) Cm * θ)) ^ 2) *
      ∫⁻ τ, ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + (Ks + 1))
        ϖ 0 (ρ / e) (K u)
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
          (volume.restrict (Set.Icc a b)) (Z u) τ) ∂volume.restrict (Set.Icc a b)) ∧
    (∀ W n, planeAllMomentFamilyEnergy K n ϖ (ρ / e) (volume.restrict (Set.Icc a b)) π
      (fun v => (nativeFamilyEdgeForcingMap Ledge v + Rs v) W) ≤ ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K n ϖ (ρ / e) (volume.restrict (Set.Icc a b)) π W) ∧
    (∀ v, ∑ u, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) ∧
    (∀ u, ∑ v, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) := by
  obtain ⟨Cprep, hCprep, hmaps⟩ := preparation_window_reference_cell_source_maps_with_schur_and_remainder
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB hc hcover σ hσ henv
    yc a b ϖ hab hsub θ hrow hcol Ks hdesc hKs hθ ha ζ hϖ hscale hζ hδ htime
  classical
  obtain ⟨T, Lfull, ⟨hsplit, hrem⟩, hmass, hrows, hcols⟩ := hmaps
    α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F hmeas hwmeas π hπ K hK actual B hB hc hcover σ hσ henv yc a b ϖ hab hsub θ hrow hcol
    Ks hdesc hKs hθ ha ζ hϖ hscale hζ hδ htime
  let Rs := nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p)
  obtain ⟨Ledge, hsource, htaylor, hzero, hdegree⟩ := naturalFamilyTaylor_constructed_split_edges
    Ks F (F.locally_finite tS tZ).toFinset actual K (ν⁻¹ * e ^ 2) hφ
    (fun p => (F.piece p).anchor) σ e (ocEpsilon q Λ (m - 1))
    yc ϖ (ρ / e) (volume.restrict (Set.Icc a b)) Lfull Rs (fun v => (hsplit.2 v).1) _ hsplit.1
  have he v : nativeFamilyEdgeForcingMap Ledge v + Rs v = Lfull v := by
    apply planeRaw_allMoment_map_unique (K v) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b)) _ _ _ _ (hsource v) (hsplit.1 v)
    intro X
    exact Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl))
  refine ⟨Rs, Ledge, ⟨hsource, htaylor, hzero, hdegree⟩, hrem, ?_, hrows, hcols⟩
  intro W n
  have heW : (fun v => (nativeFamilyEdgeForcingMap Ledge v + Rs v) W) =
      (fun v => Lfull v W) := funext (fun v => congrArg (fun L => L W) (he v))
  rw [heW]
  exact hmass W n

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual cover supplies all native drift and metric inputs of the retained
coupled error estimate, on precisely the chart's certified time window. -/

universe u v w x

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance coverRetainedEndpointNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance coverRetainedEndpointNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance coverRetainedEndpointFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance coverRetainedEndpointFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance coverRetainedEndpointScalarCarrierAdd (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverRetainedEndpointScalarCarrierModule (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverRetainedEndpointFluxCarrierAdd (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance coverRetainedEndpointFluxCarrierModule (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem windowCover_retained_actualTaylor_initial_data_endpoint_bound
    (Ks Kmax : ℕ) (CG : ℕ → ℝ) :
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
    ∃ CT CR Cterminal : ℝ, 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)],
    ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (_hζ : IsFastProfile ζfast)
      (Φ : ℕ → ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream (Φ (m - 1)))
      (ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ)
      (l₀ : ℤ) (Pcover : ℕ) (y₀ : Vec 2)
      (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ Pcover y₀)
      (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
      (ic : Fin (Pcover + 2)) (ta tb : ℝ) (_ht : ta ≤ tb)
      (_hwindow : Set.Icc ta tb ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ Pcover ic)
      (_hqJ : Ks + 1 + Kmax ≤ qJ) (_hg4 : g ≤ 1 / 4),
    ∀ (rstar δ : ℝ) (v : ℝ → Vec 2 → Vec 2)
      (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (_hrstarCover : rstar = ρs / ocEpsilon q Λ m)
      (_hδCover : δ = ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
      (_hvCell : v = ocCellDrift α q Λ ζfast m ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀ ic))
      (_hGCell : G = windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ Pcover ν y₀ ic),
    ∀ (n D H N : ℕ) (Cw : ℕ → ℝ) (Cprep Cgraph θsrc : ℝ), 0 ≤ θsrc →
      ∀ (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ϖ : ℝ)
        (_W : ChartWeights G v ta (tb - ta) ϖ (0 : Vec 2) N Cw)
        (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ (Cprep * θsrc))
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ (Cprep * θsrc))
        (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
        (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
        (V₀ : ∀ i, PlaneHk Set.univ (Kslot i) (h i))
        (_hf : ∀ i, weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (V₀ i) ≠ ⊤)
        (uH : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (wH : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
        (_hH : IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
          (planeMetricSourceCoefficient Kslot D G A) V₀ (fun _ _ => 0) (fun _ _ => 0) uH wH)
        (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
    (volume.restrict (Set.Icc ta tb)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0 (volume.restrict (Set.Icc ta tb)))
  (Lmetric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
    (volume.restrict (Set.Icc ta tb)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb)))
  (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
    (volume.restrict (Set.Icc ta tb)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb)))
        (u0 : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (w0 : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
        (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)))
    (_hdiagA : ∀ i j d, coefficientSeminorm rstar (Kslot i) ta tb
      (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1) i j d) ≠ ⊤)
    (_hfullA : ∀ i j d, coefficientSeminorm rstar (Kslot i) ta tb (planeMetricSourceCoefficient Kslot D G A i j d) ≠ ⊤)
    (_hdiagC : ∀ i j d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ)
      (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1) i j d t))
    (_hfullC : ∀ i j d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (planeMetricSourceCoefficient Kslot D G A i j d t))
    {P : Type w} {Ctx : P → Type x}
    (family : ChartedFamily ι h D P Ctx)
    (J : ℕ) (_hdepth : family.HasDepthAtMost H)
    (Hraw : ∀ v u, family.Γ v u →
      PlaneTimeAllMomentCarrier (E := h u) (Kslot u + 1) ϖ rstar 0
        (volume.restrict (Set.Icc ta tb)) → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (_hHzero : ∀ v u γ, ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), Hraw v u γ 0 t =ᵐ[volume] (fun _ => 0))
    (_hTaylorRaw : ∀ v, IsPlaneTimeAllMomentRawLinearMap (Kslot v) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t z => ∑ u, ∑ γ, Hraw v u γ (X u) t z) (nativeFamilyEdgeForcingMap Ledge v))
    (_hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (Kslot i) ta tb ϖ rstar (R i))
    (_hbase : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => Kslot i) ta tb v
      (fun _ i => V₀ i) (fun _ _ _ => 0) (fun _ i => u0 i) (fun _ i => w0 i))
    (_hZ : ∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0 (volume.restrict (Set.Icc ta tb))
      (Z i) (w0 i))
    (Lfull Ldiag : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
        (volume.restrict (Set.Icc ta tb)))
    (_hfull : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t => planeRawCouplingFlux Kslot D t (planeMetricSourceCoefficient Kslot D G A)
        (fun j => planeTimeAllMomentReadout (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) (X j) t) i) (Lfull i))
    (_hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t => planeRawCouplingFlux Kslot D t
        (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1))
        (fun j => planeTimeAllMomentReadout (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) (X j) t) i) (Ldiag i))
        (Rs : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)))
        (diag Rmetric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)))
        (_hMcenter : M = fun t => G t 0)
        (_hSourceRaw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeRawCouplingFlux Kslot D t A
            (fun j => planeTimeAllMomentReadout (Kslot j + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) (X j) t) i)
          (nativeFamilyEdgeForcingMap Ledge i + Rs i))
        (_hDiagComponent : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun _ => M t - 1)
            (planeTimeAllMomentReadout (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (diag i))
        (_hPositive : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentReadout (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Lmetric i))
        (_hMetricRemainder : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux
            (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentReadout (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Rmetric i))
        (_WM : ChartWeights (fun t _ => M t) v ta (tb - ta) ϖ 0 N Cw)
        (L ζslow : ℝ) (_hL : 1 ≤ L) (_hζslow : 0 ≤ ζslow) (_hζslow1 : ζslow ≤ 1)
        (_hϖ : 0 < ϖ) (_hscale : rstar * ϖ ≤ 1) (_hδslow : δ = ζslow * ϖ)
        (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
        (_hrem : ∀ X k, planeAllMomentFamilyEnergy Kslot k ϖ rstar
          (volume.restrict (Set.Icc ta tb)) π (fun i => Rs i X) ≤
          ENNReal.ofReal ((ζslow ^ (Ks + 1) * (Cgraph * θsrc)) ^ 2) *
          planeAllMomentFamilyGradientEnergy Kslot (k + (Ks + 1)) ϖ rstar
            (volume.restrict (Set.Icc ta tb)) π X)
        (_hgain : ENNReal.ofReal (CT * g * ζslow) ≤ 1)
        (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N),
        let C := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
        let cm := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2)
        let cs := ENNReal.ofReal ((Cgraph * θsrc) ^ 2)
        let ct := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)
        let θcap := ENNReal.ofReal θsrc
        let ζ := ENNReal.ofReal ζslow
        let η := ENNReal.ofReal (Cterminal * g * ζslow)
        let G0 := ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} N Kmax Cw) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 rstar (Kslot i) (V₀ i)
        let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
          (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
        let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U j k
        let Tret := ∑ k ∈ Finset.range (H + 1), U J k
        let Q := fun i => Lmetric i (Wret i) + nativeFamilyEdgeForcingMap Ledge i Wret - Lmetric i (Tret i)
        ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
          (ferr : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i))),
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A) (fun _ => 0) ferr (fun _ _ => 0)
            (fun i t => uH i t - u i t) (fun i t => wH i t - w i t) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb))
            (-(Q i - Lfull i Wret + Ldiag i Wret)) (ferr i)) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Wret i) (w i)) ∧
          ∀ tp, tp ∈ Set.Icc ta tb →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (uH i tp - u i tp)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θsrc)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζ ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0)) := by
  dsimp only
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hendpoint⟩ :=
    planeRetained_actualTaylor_window_initial_data_endpoint_bound.{u, v, w, x}
      Ks Kmax (fun r => max (CG r) 0) (fun r => le_max_right (CG r) 0)
  refine ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, ?_⟩
  intro ι _ h _ _ _ _ _ _ α q Λ m ζfast hζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb
    qJ l₀ Pcover y₀ cov hΛ heE ic ta tb ht hwindow hqJ hg4
    rstar δ v G hrstarCover hδCover hvCell hGCell
    n D H N Cw Cprep Cgraph θsrc hθsrc π hπ Kslot hKslot
    ϖ W hD A hA hc hAm hrow hcol rank hrank hzero V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC
    P Ctx family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM
    L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve hrem hgain hN
  have he := Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hE := Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hrstar : 0 < rstar := by rw [hrstarCover]; exact div_pos cov.pos.2.2 he
  have hδ : 0 ≤ δ := by rw [hδCover]; exact div_nonneg he.le hE.le
  have hr1 : rstar ≤ 1 := by rw [hrstarCover]; exact (div_le_one he).mpr cov.rho_e
  have hrδ : rstar * δ ≤ 1 := by
    rw [hrstarCover, hδCover]
    rw [div_mul_div_cancel₀ he.ne']
    exact (div_le_one hE).mpr (cov.rho_e.trans heE)
  have hd := windowCover_native_drift_data hΛ hζ hφ cov ic ta tb hwindow
  dsimp only at hd
  rw [← hvCell] at hd
  obtain ⟨hv_bdd, hv_meas, hv_smooth, hv_div, hjets⟩ := hd
  have hm := windowCover_native_metric_data hΛ hφ cov ic ta tb hwindow
  dsimp only at hm
  rw [← hGCell] at hm
  obtain ⟨hG_near, hG_meas, hGm, hG_symm, hG_smooth, hG_jets⟩ := hm
  have hB : B₀ * rstar / lam ≤ 1 / 2 := by
    rw [hrstarCover]
    exact cov.drift_scale
  have hab : strain * B₀ * rstar ^ 2 ≤ 1 / 8 := by
    rw [hrstarCover]
    exact cov.drift_small
  have hMm : Measurable M := by
    rw [hMcenter]
    apply Measurable.of_eval_matrix
    intro r c
    exact hGm 0 r c
  have hGhigh t (htt : t ∈ Set.Icc ta tb) r c :
      ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z r c) :=
    (hG_smooth t htt r c).of_le (by exact_mod_cast hqJ)
  have hGlowjet : ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ max (CG r) 0 * g * δ ^ r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htt
    intro r hr hrKs k l
    rw [hδCover]
    exact hG_jets t htt 0 r hr (by omega) k l
  have hGhighjet : ∀ᵐ t ∂volume.restrict (Set.Icc ta tb), ∀ r, Ks + 1 ≤ r →
      r ≤ Ks + 1 + Kmax → ∀ y k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ max (CG r) 0 * g * (ζslow * ϖ) ^ r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htt
    intro r hr hrq y k l
    rw [← hδslow, hδCover]
    exact hG_jets t htt y r (by omega) (hrq.trans hqJ) k l
  exact hendpoint (ι := ι) (h := h) n D H N Cw Cprep Cgraph θsrc hθsrc
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam
    cov.drift_pos.1 cov.drift_pos.2.1 cov.drift_pos.2.2 hjets hB hab
    G g cov.g_range.1 hg4 hG_meas (fun t _ z => hG_symm t z) hG_near
    (fun t htt r c => (hG_smooth t htt r c).of_le (by exact_mod_cast (show max Kmax 1 ≤ qJ by omega)))
    (fun t htt z j hj hjK r c => by
      rw [hδCover]
      exact hG_jets t htt z j hj (by omega) r c)
    ϖ W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC
    family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM
    L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve
    hMm hGm hGhigh hGlowjet hGhighjet hrem hgain hN

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The genuine physical preparation equation transfers to the full homogeneous coupled weak solution class in reference cell coordinates. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_cell_natural_block_coupled_solution_of_pointwise
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
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
    (yc : Vec 2)
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (c d : ℝ) (hac : (e⁻¹) ^ 2 * (ν * a) ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * b))
    (hblock : ∀ t ∈ Icc c d,
      ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hs : IsCoupledWeakSolutionPlane ν a b (streamVel (Φ m)) D K (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hKmax j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
        (Nat.add_le_add_right (show K j ≤ Jchart by have hh := hKmax j; omega) 1) t (w j t)
    IsCoupledWeakSolutionPlane 1 c d
      (ocCellDrift α q Λ ζ m ν yc) D K
      (planeMetricSourceCoefficient K D
        (ocCellMetric α q Λ m (Φ (m - 1)) hφ l₀ ν yc)
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
          ν e (ocEpsilon q Λ (m - 1)) actual K yc))
      (fun j => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (U j (ν⁻¹ * (e ^ 2 * c))))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (W j (ν⁻¹ * (e ^ 2 * t)))) := by
  have hcell : e ≠ 0 := (hρ.trans_le hρe).ne'
  have hK (j : ι) : K j ≤ Jchart := by have hh := hKmax j; omega
  obtain ⟨hsmooth, hA, hc, hAm⟩ := preparation_physical_coefficient_pointwise_data F hprep
    ν e ρ hν hρ hρe heE K Kmax Jm hKmax hchart hmol Cm hmeas hwmeas
    actual π hπ B hB henv
  have hΨ := streamSeq_current_admissible hseq m
  have hvfull := Infra.Classical.streamVel_smoothPeriodic (Φ m) hΨ
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => streamVel (Φ m) p.1 p.2) := hvfull.smooth
  have hp : ∀ t, IsZ2Periodic (streamVel (Φ m) t) := by
    intro t k x
    simpa using hvfull.periodic 0 k t x
  have hvc : ∀ t ∈ Icc a b, Continuous (streamVel (Φ m) t) := by
    intro t _
    exact (hv.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hvm : Measurable (fun p : Icc a b × Vec 2 => streamVel (Φ m) p.1 p.2) :=
    hv.continuous.measurable.comp (measurable_subtype_coe.prodMap measurable_id)
  obtain ⟨M, _, hMb⟩ := admissible_stream_spatial_jet_bound (Φ m) hΨ 0
  have hvb : ∀ t ∈ Icc a b, ∀ x, ‖streamVel (Φ m) t x‖ ≤ M := by
    intro t _ x
    simpa only [norm_iteratedFDeriv_zero] using hMb t x
  exact preparation_reference_cell_natural_block_coupled_solution F hab ρ hρ K hdesc hD hprep hcover hTau ha hK
    hΛ hm hseq hΨ ν e (ocEpsilon q Λ (m - 1)) hν heScale K hsmooth actual hT he
    hA hc hv hp hvc hvm M hvb hAm hcell yc f u w c d hac hcd hdb hblock hs
end

/-! The genuine physical preparation equation transfers to the full homogeneous coupled weak solution class in reference cell coordinates. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_cell_initial_natural_block_coupled_solution_of_pointwise
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
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
    (yc : Vec 2)
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (d : ℝ) (hcd : (e⁻¹) ^ 2 * (ν * a) ≤ d)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * b))
    (hblock : ∀ t ∈ Icc ((e⁻¹) ^ 2 * (ν * a)) d,
      ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hs : IsCoupledWeakSolutionPlane ν a b (streamVel (Φ m)) D K (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) :
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
        (by have hh := hKmax j; omega) a (f j)))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e (hρ.trans_le hρe).ne' yc (W j (ν⁻¹ * (e ^ 2 * t)))) := by
  have hcell : e ≠ 0 := (hρ.trans_le hρe).ne'
  have ht0 : ν⁻¹ * (e ^ 2 * ((e⁻¹) ^ 2 * (ν * a))) = a := by
    calc
      _ = (ν⁻¹ * ν) * (e * e⁻¹) ^ 2 * a := by ring
      _ = a := by rw [inv_mul_cancel₀ hν.ne', mul_inv_cancel₀ hcell]; ring
  have hr := preparation_reference_cell_natural_block_coupled_solution_of_pointwise
    F hab ρ hρ K hdesc hD hprep hcover hTau ha Kmax Jm hKmax hchart hmol Cm π hπ B hB
    hmeas hwmeas hΛ hm hseq ν e hν heScale hρe heE henv actual hT he yc f u w
    ((e⁻¹) ^ 2 * (ν * a)) d (le_refl _) hcd hdb hblock hs
  dsimp only at hr ⊢
  have hi : (fun j => planeCarrierAffine e (hρ.trans_le hρe).ne' yc
      (preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hKmax j; omega) (ν⁻¹ * (e ^ 2 * ((e⁻¹) ^ 2 * (ν * a))))
          (u j (ν⁻¹ * (e ^ 2 * ((e⁻¹) ^ 2 * (ν * a))))))) =
      (fun j => planeCarrierAffine e (hρ.trans_le hρe).ne' yc
        (preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
          (by have hh := hKmax j; omega) a (f j))) := by
    funext j
    rw [ht0, hs.2.2.2.1 j]
  rw [hi] at hr
  exact hr
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Existence for the actual stream drift: the auxiliary energy radius is chosen internally. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The actual preparation preserves finite initial polynomial moments in genuine geometry energy. -/
theorem actualPreparation_geometry_energy_lt_top (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν)
    (a b : ℝ) (hab : a ≤ b)
    (D : ℕ) {P' : Type*} {Ctx : P' → Type*}
    (family : ChartedFamily ι h D P' Ctx) (H : ℕ) (hdepth : family.HasDepthAtMost H)
    (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (ζ : ℝ → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P : ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P family)
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hmeas : family.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (family.weight p))
    (hE : E = ocEpsilon q Λ (m - 1)) (hρe : ρ ≤ e) (heE : e ≤ E)
    (Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hpointwise : IsPointwiseMolecularEnvelope family π K
      (ChartedFamily.Domain.onWindow family (Set.Icc a b)) ν e E ρ Cm Jm A)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) f (fun _ _ => 0) (fun _ _ => 0) u w)
    (n : ℕ) (ϖ : ℝ) (z : Vec 2)
    (hf : ∀ i, weightedFactorialNormSq n ϖ z ρ (K i) (f i) ≠ ⊤) :
    geometryEnergyNorm π K n ϖ z ρ a b u w < ⊤ := by
  obtain ⟨Cprep, _, hsample⟩ := preparation_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hfwd : IsSampledEnvelope family π K actual a b ν e E ρ Cprep A := by
    subst E
    exact hsample α q Λ m φ hφ a b Cpad Cage Npad l₀ P ν e ρ
      hν hρ hρe heE family π hπ K hK actual A hA hprep hpointwise
  have hs : family.IsSmoothOn (ChartedFamily.Domain.onWindow family (Set.Icc a b)) E K := by
    intro p ctx v u γ d I tY htY z
    exact (hpointwise.1 p ctx v u γ d I tY htY z).of_le
      (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hcur := streamSeq_current_admissible hΦ m
  have hvfull := Infra.Classical.streamVel_smoothPeriodic (Φ m) hcur
  obtain ⟨V, hV, hVbound⟩ := admissible_stream_spatial_jet_bound (Φ m) hcur 0
  have hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖AVenhance.streamVel (Φ m) t x‖ ≤ V := by
    intro t _ x
    simpa only [norm_iteratedFDeriv_zero] using hVbound t x
  have hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel (Φ m) t) := by
    intro t _
    exact hvfull.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hvm : Measurable (fun p : Set.Icc a b × Vec 2 => AVenhance.streamVel (Φ m) p.1 p.2) :=
    hvfull.smooth.continuous.measurable.comp (measurable_subtype_coe.prodMap measurable_id)
  have hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2,
      fderiv ℝ (AVenhance.streamVel (Φ m) t) x (basisVec k) k = 0 := by
    intro t _ x
    have he := Infra.Classical.streamVel_vecDiv_eq_zero (Φ m) hcur t x
    unfold AVenhance.vecDiv AVenhance.spaceGrad at he
    have hd : DifferentiableAt ℝ (AVenhance.streamVel (Φ m) t) x :=
      ((hvfull.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) x
    simp only [fderiv_apply hd, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.comp_apply] at he
    exact he
  obtain ⟨M, hM, hMbound⟩ := admissible_stream_coefficient_array_budget (Φ m) hcur Kmax
  have hfinite i j d := sampledEnvelope_edge_seminorm_ne_top family π hπ K actual
    a b ν e E ρ Cprep hν hρ A hfwd i j d
  have hc : ∀ i j d t, t ∈ Set.Icc a b →
      ContDiff ℝ (K i : ℕ) (edgeCoefficient family ν e E actual K i j d t) := by
    intro i j d t ht
    exact edgeCoefficient_spatial_smooth family hprep ν e E K hs actual K i j d t ht
  have hAm i j d := edgeCoefficient_joint_measurable family hprep ν e E K hs hmeas hwmeas actual K i j d
  have hzero : ∀ i j, ¬ sourceDepthRank family H j < sourceDepthRank family H i →
      ∀ d t x, edgeCoefficient family ν e E actual K i j d t x = 0 := by
    intro i j hnot d t x
    exact congrFun (congrFun (physicalCoefficient_zero_of_rank family H hdepth ν e E actual
      i j d.val hnot) t) x
  have hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (AVenhance.streamVel (Φ m) t)) l x‖ ≤
        M * (l.factorial : ℝ) := by
    intro t _ l _ hl x
    have hfac : (1 : ℝ) ≤ (l.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos l)
    exact (hMbound l hl t x).trans (le_mul_of_one_le_right hM hfac)
  exact physical_triangular_geometry_energy_lt_top a b ν hab hν K D Kmax hK
    (AVenhance.streamVel (Φ m)) hvm hv V M hV hM
    (fun t x => by simpa only [norm_iteratedFDeriv_zero] using hVbound t x)
    hjets ϖ z n ρ hρ hdiv (edgeCoefficient family ν e E actual K) hfinite hc hAm
    f u w hsol (sourceDepthRank family H) hzero hf π hπ
end

/-! Existence for the actual stream drift: the auxiliary energy radius is chosen internally. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Homogeneous preparation existence includes its finite genuine polynomial energy. -/
theorem exists_actualPreparation_homogeneous_plane_with_energy (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν)
    (a b : ℝ) (hab : a ≤ b)
    (D : ℕ) {P' : Type*} {Ctx : P' → Type*}
    (family : ChartedFamily ι h D P' Ctx) (H : ℕ) (hdepth : family.HasDepthAtMost H)
    (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (ζ : ℝ → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P : ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P family)
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hmeas : family.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (family.weight p))
    (hE : E = ocEpsilon q Λ (m - 1)) (hρe : ρ ≤ e) (heE : e ≤ E)
    (Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hpointwise : IsPointwiseMolecularEnvelope family π K
      (ChartedFamily.Domain.onWindow family (Set.Icc a b)) ν e E ρ Cm Jm A)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (n : ℕ) (ϖ : ℝ) (z : Vec 2)
    (hf : ∀ i, weightedFactorialNormSq n ϖ z ρ (K i) (f i) ≠ ⊤) :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν a b (streamVel (Φ m)) D K
        (edgeCoefficient family ν e E actual K) f (fun _ _ => 0) (fun _ _ => 0) u w ∧
      geometryEnergyNorm π K n ϖ z ρ a b u w < ⊤ := by
  have hFzero (i : ι) : MemLp
      (fun _ : ℝ => (0 : PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))))
      2 (volume.restrict (Set.Icc a b)) :=
    Weighted.planeHk_zero_time_memLp (K i) _
  have hgzero (i : ι) : Integrable (fun _ : ℝ => (0 : PlaneHk Set.univ (K i) (h i)))
      (volume.restrict (Set.Icc a b)) := by
    simpa only [Pi.zero_def] using integrable_zero ℝ (PlaneHk Set.univ (K i) (h i))
      (volume.restrict (Set.Icc a b))
  obtain ⟨u, w, hs⟩ := exists_actualPreparation_planeWeakSolution K Kmax hK ρ ν hρ hν a b hab
    D family H hdepth α q Λ m Φ ζ hΦ φ hφ Cpad Cage Npad Jchart Cchart l₀ P hprep
    e E actual hmeas hwmeas hE hρe heE Jm hchart hmol Cm π hπ A hA hpointwise
    (fun _ _ => 0) (fun _ _ => 0) hFzero hgzero f
  exact ⟨u, w, hs, actualPreparation_geometry_energy_lt_top K Kmax hK ρ ν hρ hν a b hab
    D family H hdepth α q Λ m Φ ζ hΦ φ hφ Cpad Cage Npad Jchart Cchart l₀ P hprep
    e E actual hmeas hwmeas hE hρe heE Jm hchart hmol Cm π hπ A hA hpointwise
    f u w hs n ϖ z hf⟩
end

end AVRegularity.CycleJointProofs
end
end
