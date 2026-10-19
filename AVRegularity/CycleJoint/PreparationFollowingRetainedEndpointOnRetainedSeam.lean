-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.WindowCoverWindowReferenceRetainedEndpointSummary
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
import AVRegularity.CycleJoint.ActualPreparationHomogeneousFamilyNativeTraceLinearMap
import AVRegularity.CycleJoint.WindowCoverConstructedRetainedActualTaylorLinearEndpointAllMomentsBound
import AVRegularity.CycleJoint.PreparationReferenceCellInitialHomogeneousResponsePair
public import AVRegularity.CycleJoint.PointwiseNativeTransportIdentityPrice

section
/-! The actual first-block construction supplies both the homogeneous native
family and its retained endpoint, hiding the internal response-map witnesses. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

universe u v w x


variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]


local instance preparationReferenceRetainedSummaryNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance preparationReferenceRetainedSummaryNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance preparationReferenceRetainedSummaryFluxNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance preparationReferenceRetainedSummaryFluxNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance preparationReferenceRetainedSummaryScalarCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance preparationReferenceRetainedSummaryScalarCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance preparationReferenceRetainedSummaryFluxCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance preparationReferenceRetainedSummaryFluxCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem preparationReferenceCell_retained_endpoint_summary (D Ks Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart CG : ℕ → ℝ) :
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CRemainder := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    let Cgraph := pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CRemainder) Cm
    ∃ Cprep CT CR Cterminal : ℝ, 1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (hζ : IsFastProfile ζfast) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        ∀ (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
        (_henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
        (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) (htSZ : tS ≤ tZ)
        (_hm : 1 ≤ m) (_hseq : IsOCStreamSeq α q Λ ζfast Φ)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (Nperiod : ℕ) (_hperiod : (ocEpsilon q Λ m)⁻¹ = (Nperiod : ℝ))
        (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ),
        let a := (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tS)
        ∀ (b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P (windowCoverReferenceChartIndex P) →
        (∀ t ∈ Set.Icc a b,
          ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
          ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
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
    ∀ (n H N J : ℕ) (_hdepth : F.HasDepthAtMost H) (Cw : ℕ → ℝ)
      (_W : ChartWeights G v a (b - a) ϖ 0 N Cw)
      (_WM : ChartWeights (fun t _ => G t 0) v a (b - a) ϖ 0 N Cw)
      (L : ℝ) (_hL : 1 ≤ L)
      (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
      (_hgain : ENNReal.ofReal (CT * g * ζ) ≤ 1)
      (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
      (τ : ℝ) (_hτ : τ ∈ Set.Icc a b),
    let X := ∀ i, TorusHk (K i) (h i)
    let V₀ := preparationReferenceCellLocalizedInitialFamilyLinearMap hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ).le ha K
      (fun i => by have hh := _hK i; omega) htSZ hζ Npatch hNpatch patch
      (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' yc
    ∃ (uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    (∀ f, IsCoupledWeakSolutionPlane ν tS tZ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (fun i => spatialPatchLocalization hζ Npatch hNpatch patch (K i) (f i))
      (fun _ _ => 0) (fun _ _ => 0) (uphys f) (wphys f)) ∧
    let uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i) := fun f i =>
      preparationReferenceCellNativeCurve hprep hcover (Construction.Stream.ocTauPP_pos hΛ).le ha
        (K i) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc (uphys f i)
    let wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i) := fun f i =>
      preparationReferenceCellNativeCurve hprep hcover (Construction.Stream.ocTauPP_pos hΛ).le ha
        (K i + 1) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc (wphys f i)
    (∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K
      (planeMetricSourceCoefficient K D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0)
      (uH ξ) (wH ξ)) ∧
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
  have he := windowCover_reference_retained_linear_endpoint_all_moments_bound.{u, v, w, x, max u v}
    D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG
  let Cprep := he.choose
  let CT := he.choose_spec.choose
  let CR := he.choose_spec.choose_spec.choose
  let Cterminal := he.choose_spec.choose_spec.choose_spec.choose
  have hs := he.choose_spec.choose_spec.choose_spec.choose_spec
  refine ⟨Cprep, CT, CR, Cterminal, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ y₀ cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hprep henv hcover htSZ hm hseq htorus Nperiod hperiod Npatch hNpatch patch
    a b hab hwindow hblock θ hrow hcol hdesc hKs hθ hqJ hlength
    ϖ ζ yc G v A n H N J hdepth Cw W WM L hL hreserve hgain hN τ hτ X V₀
  classical
  have hsc := windowCover_native_subwindow_scales hΛ hφ cov
    (windowCoverReferenceChartIndex P) a b hwindow
  have hdb := (hsc.1 (show b ∈ Set.Icc a b from ⟨hab.le, le_refl b⟩)).2
  have hp := exists_preparation_reference_cell_coupled_solution_family
    F H hdepth htSZ ρ cov.pos.2.2 K hdesc hD hprep hcover
    (Construction.Stream.ocTauPP_pos hΛ).le ha Kmax Jm hK hchart hmol Cm π hπ B hB
    hmeas hwmeas hΛ hm hseq ν (ocEpsilon q Λ m) cov.pos.1 rfl cov.rho_e heE
    henv actual htorus hperiod hζ cov hgsmall hg0 ϖ rfl Npatch hNpatch patch
    b hab hwindow hlength hdb hblock
  let uphys := hp.choose
  let wphys := hp.choose_spec.choose
  have hsol := hp.choose_spec.choose_spec
  refine ⟨uphys, wphys, (fun f => (hsol f).1), ?_⟩
  intro uH wH
  have hH : ∀ f, IsCoupledWeakSolutionPlane 1 a b v D K
      (planeMetricSourceCoefficient K D G A) (V₀ f) (fun _ _ => 0) (fun _ _ => 0)
      (uH f) (wH f) := by
    intro f
    dsimp only [a, V₀, yc, G, v, A, uH, wH, preparationReferenceCellNativeCurve,
      windowCoverCellMetric]
    rw [windowCoverReferenceChartIndex_label]
    exact (hsol f).2
  have hp := hs.2.2.2.2 α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ
    g g0 strain B₀ lam Cb qJ y₀ cov hΛ heE ha hgsmall hg0 hD F hmeas hwmeas
    π hπ K hK actual B hB hprep henv a b hab hwindow θ hrow hcol hdesc hKs hθ hqJ hlength
    n H N J hdepth Cw W WM V₀
    (fun f r i => preparationReferenceCellLocalizedInitialFamilyLinearMap_all_moments hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ).le ha K (fun i => by have hh := hK i; omega)
      htSZ hζ Npatch hNpatch patch (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne'
      yc f r ϖ ρ i)
    uH wH hH
    L hL hreserve hgain hN τ hτ

  refine hp.elim fun _ h1 => h1.elim fun _ h2 => h2.elim fun _ h3 => h3.elim fun _ h4 =>
    h4.elim fun _ h5 => h5.elim fun _ h6 => h6.2.elim fun _ h7 => h7.elim fun _ h8 =>
    h8.elim fun _ h9 => h9.2.2.elim fun T hT => ?_
  refine ⟨hH, T, hT.1, fun ξ => ?_⟩
  exact (hT.2 ξ).elim fun u h1 => h1.elim fun w h2 => h2.elim fun ferr hh =>
    ⟨u, w, ferr, hh.1, hh.2.2.2.1, hh.2.2.2.2⟩

end AVRegularity.CycleJointProofs
end
end

section
/-! The actual first-block construction supplies both the homogeneous native
family and its retained endpoint, hiding the internal response-map witnesses. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

universe u v w x


variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]


local instance preparationReferenceRetainedLinearTraceSummaryNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance preparationReferenceRetainedLinearTraceSummaryNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance preparationReferenceRetainedLinearTraceSummaryFluxNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance preparationReferenceRetainedLinearTraceSummaryFluxNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance preparationReferenceRetainedLinearTraceSummaryScalarCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance preparationReferenceRetainedLinearTraceSummaryScalarCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance preparationReferenceRetainedLinearTraceSummaryFluxCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance preparationReferenceRetainedLinearTraceSummaryFluxCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem preparationReferenceCell_retained_endpoint_summary_with_linear_trace (D Ks Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart CG : ℕ → ℝ) :
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CRemainder := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    let Cgraph := pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CRemainder) Cm
    ∃ Cprep CT CR Cterminal : ℝ, 1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (hζ : IsFastProfile ζfast) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        ∀ (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
        (_henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
        (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) (htSZ : tS ≤ tZ)
        (_hm : 1 ≤ m) (_hseq : IsOCStreamSeq α q Λ ζfast Φ)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (Nperiod : ℕ) (_hperiod : (ocEpsilon q Λ m)⁻¹ = (Nperiod : ℝ))
        (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ),
        let a := (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tS)
        ∀ (b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P (windowCoverReferenceChartIndex P) →
        (∀ t ∈ Set.Icc a b,
          ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
          ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
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
    ∀ (n H N J : ℕ) (_hdepth : F.HasDepthAtMost H) (Cw : ℕ → ℝ)
      (_W : ChartWeights G v a (b - a) ϖ 0 N Cw)
      (_WM : ChartWeights (fun t _ => G t 0) v a (b - a) ϖ 0 N Cw)
      (L : ℝ) (_hL : 1 ≤ L)
      (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
      (_hgain : ENNReal.ofReal (CT * g * ζ) ≤ 1)
      (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
      (τ : ℝ) (_hτ : τ ∈ Set.Icc a b),
    let X := ∀ i, TorusHk (K i) (h i)
    let V₀ := preparationReferenceCellLocalizedInitialFamilyLinearMap hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ).le ha K
      (fun i => by have hh := _hK i; omega) htSZ hζ Npatch hNpatch patch
      (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' yc
    ∃ (uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    (∀ f, IsCoupledWeakSolutionPlane ν tS tZ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (fun i => spatialPatchLocalization hζ Npatch hNpatch patch (K i) (f i))
      (fun _ _ => 0) (fun _ _ => 0) (uphys f) (wphys f)) ∧
    let uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i) := fun f i =>
      preparationReferenceCellNativeCurve hprep hcover (Construction.Stream.ocTauPP_pos hΛ).le ha
        (K i) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc (uphys f i)
    let wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i) := fun f i =>
      preparationReferenceCellNativeCurve hprep hcover (Construction.Stream.ocTauPP_pos hΛ).le ha
        (K i + 1) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc (wphys f i)
    (∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K
      (planeMetricSourceCoefficient K D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0)
      (uH ξ) (wH ξ)) ∧
    ∃ Upre : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
    (∀ ξ i, Upre ξ i = uH ξ i τ) ∧
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
  have hr := preparationReferenceCell_retained_endpoint_summary.{u, v, w, x}
    D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG
  let Cprep := hr.choose
  let CT := hr.choose_spec.choose
  let CR := hr.choose_spec.choose_spec.choose
  let Cterminal := hr.choose_spec.choose_spec.choose_spec.choose
  have hs := hr.choose_spec.choose_spec.choose_spec.choose_spec
  refine ⟨Cprep, CT, CR, Cterminal, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ y₀ cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hprep henv hcover htSZ hm hseq htorus Nperiod hperiod Npatch hNpatch patch
    a b hab hwindow hblock θ hrow hcol hdesc hKs hθ hqJ hlength
    ϖ ζ yc G v A n H N J hdepth Cw W WM L hL hreserve hgain hN τ hτ X V₀
  have hp := hs.2.2.2.2 α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ
    g g0 strain B₀ lam Cb qJ y₀ cov hΛ heE ha hgsmall hg0 hD F hmeas hwmeas
    π hπ K hK actual B hB hprep henv hcover htSZ hm hseq htorus Nperiod hperiod
    Npatch hNpatch patch b hab hwindow hblock θ hrow hcol hdesc hKs hθ hqJ hlength
    n H N J hdepth Cw W WM L hL hreserve hgain hN τ hτ
  obtain ⟨uphys, wphys, hphysical, hH, T, hT, hrest⟩ := hp
  refine ⟨uphys, wphys, hphysical, ?_⟩
  intro uH wH
  let tp := ν⁻¹ * (ocEpsilon q Λ m ^ 2 * τ)
  have hsc := windowCover_native_subwindow_scales hΛ hφ cov
    (windowCoverReferenceChartIndex P) a b hwindow
  have htp : tp ∈ Set.Icc tS tZ := hsc.2.1 τ hτ
  let lf : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)) :=
    LinearMap.pi (fun i => (spatialPatchLocalization hζ Npatch hNpatch patch (K i)).comp
      (LinearMap.proj i))
  obtain ⟨Upre, hUpre⟩ := actualPreparation_homogeneous_family_native_trace_linearMap
    K Kmax hK ρ ν cov.pos.2.2 cov.pos.1 tS tZ htSZ D F H hdepth
    α q Λ m Φ ζfast hseq (Φ (m - 1)) hφ Cpad Cage Npad Jchart Cchart l₀ P
    hprep (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual hmeas hwmeas rfl
    cov.rho_e heE Jm hchart hmol Cm π hπ B hB henv
    lf uphys wphys hphysical tp htp hcover
    (Construction.Stream.ocTauPP_pos hΛ).le ha (Construction.Stream.ocEpsilon_pos hΛ).ne' yc
  have htime : (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tp) = τ := by
    dsimp only [tp]
    field_simp [cov.pos.1.ne', (Construction.Stream.ocEpsilon_pos hΛ).ne']
  rw [htime] at hUpre
  exact ⟨hH, Upre, hUpre, T, hT, hrest⟩

end AVRegularity.CycleJointProofs
end
end

section
/-! The actual first-block construction supplies both the homogeneous native
family and its retained endpoint, hiding the internal response-map witnesses. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

universe u v w x


variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]


local instance preparationReferenceRetainedEnergySummaryNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance preparationReferenceRetainedEnergySummaryNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance preparationReferenceRetainedEnergySummaryFluxNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance preparationReferenceRetainedEnergySummaryFluxNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance preparationReferenceRetainedEnergySummaryScalarCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance preparationReferenceRetainedEnergySummaryScalarCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance preparationReferenceRetainedEnergySummaryFluxCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance preparationReferenceRetainedEnergySummaryFluxCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem preparationReferenceCell_retained_endpoint_summary_with_energy (D Ks Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart CG : ℕ → ℝ) :
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CRemainder := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    let Cgraph := pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CRemainder) Cm
    ∃ Cenergy Cprep CT CR Cterminal : ℝ, 1 ≤ Cenergy ∧ 1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (hζ : IsFastProfile ζfast) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        ∀ (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
        (_henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
        (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) (htSZ : tS ≤ tZ)
        (_hm : 1 ≤ m) (_hseq : IsOCStreamSeq α q Λ ζfast Φ)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (Nperiod : ℕ) (_hperiod : (ocEpsilon q Λ m)⁻¹ = (Nperiod : ℝ))
        (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ),
        let a := (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tS)
        ∀ (b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P (windowCoverReferenceChartIndex P) →
        (∀ t ∈ Set.Icc a b,
          ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
          ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
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
    ∀ (n H N J : ℕ) (_hdepth : F.HasDepthAtMost H) (Cw : ℕ → ℝ)
      (_W : ChartWeights G v a (b - a) ϖ 0 N Cw)
      (_WM : ChartWeights (fun t _ => G t 0) v a (b - a) ϖ 0 N Cw)
      (L : ℝ) (_hL : 1 ≤ L)
      (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
      (_hgain : ENNReal.ofReal (CT * g * ζ) ≤ 1)
      (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
      (τ : ℝ) (_hτ : τ ∈ Set.Icc a b),
    let X := ∀ i, TorusHk (K i) (h i)
    let V₀ := preparationReferenceCellLocalizedInitialFamilyLinearMap hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ).le ha K
      (fun i => by have hh := _hK i; omega) htSZ hζ Npatch hNpatch patch
      (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' yc
    ∃ (uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    (∀ f, IsCoupledWeakSolutionPlane ν tS tZ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (fun i => spatialPatchLocalization hζ Npatch hNpatch patch (K i) (f i))
      (fun _ _ => 0) (fun _ _ => 0) (uphys f) (wphys f)) ∧
    let uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i) := fun f i =>
      preparationReferenceCellNativeCurve hprep hcover (Construction.Stream.ocTauPP_pos hΛ).le ha
        (K i) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc (uphys f i)
    let wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i) := fun f i =>
      preparationReferenceCellNativeCurve hprep hcover (Construction.Stream.ocTauPP_pos hΛ).le ha
        (K i + 1) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc (wphys f i)
    (∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K
      (planeMetricSourceCoefficient K D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0)
      (uH ξ) (wH ξ)) ∧
    ∃ Upre : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
    (∀ ξ i, Upre ξ i = uH ξ i τ) ∧
    (∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq N ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (Upre ξ i)) ≤
      ENNReal.ofReal ((planeSourceRankScale.{u, v} N Kmax Cjet Cw D (Cenergy * θ)) ^ (2 * H)) *
        (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} N Kmax Cjet Cw)) *
        (∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq N ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i))) ∧
    (∀ ξ k, k ≤ N → ∀ i, weightedFactorialNormSq k ϖ 0 (ρ / ocEpsilon q Λ m)
      (K i) (Upre ξ i) ≠ ⊤) ∧
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
  obtain ⟨Cenergy, hCenergy, henergy⟩ := preparation_reference_homogeneous_endpoint_energy
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hr := preparationReferenceCell_retained_endpoint_summary_with_linear_trace.{u, v, w, x}
    D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG
  let Cprep := hr.choose
  let CT := hr.choose_spec.choose
  let CR := hr.choose_spec.choose_spec.choose
  let Cterminal := hr.choose_spec.choose_spec.choose_spec.choose
  have hs := hr.choose_spec.choose_spec.choose_spec.choose_spec
  refine ⟨Cenergy, Cprep, CT, CR, Cterminal, hCenergy, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ y₀ cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hprep henv hcover htSZ hm hseq htorus Nperiod hperiod Npatch hNpatch patch
    a b hab hwindow hblock θ hrow hcol hdesc hKs hθ hqJ hlength
    ϖ ζ yc G v A n H N J hdepth Cw W WM L hL hreserve hgain hN τ hτ X V₀
  have hp := hs.2.2.2.2 α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ
    g g0 strain B₀ lam Cb qJ y₀ cov hΛ heE ha hgsmall hg0 hD F hmeas hwmeas
    π hπ K hK actual B hB hprep henv hcover htSZ hm hseq htorus Nperiod hperiod
    Npatch hNpatch patch b hab hwindow hblock θ hrow hcol hdesc hKs hθ hqJ hlength
    n H N J hdepth Cw W WM L hL hreserve hgain hN τ hτ
  obtain ⟨uphys, wphys, hphysical, hH, Upre, hUpre, T, hT, hrest⟩ := hp
  refine ⟨uphys, wphys, hphysical, ?_⟩
  intro uH wH
  have hsc := windowCover_native_subwindow_scales hΛ hφ cov
    (windowCoverReferenceChartIndex P) a b hwindow
  have hactual (ξ : X) := henergy α q Λ m Φ hφ tS tZ Cpad Cage Npad l₀ P
    ν (ocEpsilon q Λ m) ρ cov.pos.1 cov.pos.2.2 cov.rho_e heE
    F π hπ K hK actual B hB hprep hmeas hwmeas henv a b θ hsc.1 hrow hcol H hdepth
    ζfast Bcover g g0 strain B₀ lam Cb qJ CG y₀ cov hΛ hζ hab.le hwindow
    (by omega) (by linarith only [hgsmall]) hD rfl N Cw ϖ W (V₀ ξ)
    (fun i => preparationReferenceCellLocalizedInitialFamilyLinearMap_all_moments hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ).le ha K (fun i => by have hh := hK i; omega)
      htSZ hζ Npatch hNpatch patch (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne'
      yc ξ N ϖ ρ i)
    (uH ξ) (wH ξ) (hH ξ) τ hτ
  have hinit (ξ : X) (i : ι) : weightedFactorialNormSq N ϖ 0
      (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i) ≠ ⊤ :=
    preparationReferenceCellLocalizedInitialFamilyLinearMap_all_moments hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ).le ha K (fun i => by have hh := hK i; omega)
      htSZ hζ Npatch hNpatch patch (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne'
      yc ξ N ϖ ρ i
  have hfinite (ξ : X) (k : ℕ) (hk : k ≤ N) (i : ι) :
      weightedFactorialNormSq k ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (Upre ξ i) ≠ ⊤ := by
    have hi : (∑ j, ENNReal.ofReal ((π j)⁻¹) * weightedFactorialNormSq N ϖ 0
        (ρ / ocEpsilon q Λ m) (K j) (V₀ ξ j)) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hinit ξ j))
    have hb := hactual ξ
    have hs := ne_top_of_le_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ENNReal.ofReal_ne_top)) hi) hb
    have hj := AVRegularity.Weighted.finite_weighted_sum_component (fun j => (π j)⁻¹)
      (fun j => inv_pos.mpr (hπ j)) _ hs i
    have heq : Upre ξ i = uH ξ i τ := hUpre ξ i
    rw [← heq] at hj
    exact ne_top_of_le_ne_top hj (weightedFactorialNormSq_moment_mono hk ϖ 0
      (ρ / ocEpsilon q Λ m) (K i) (Upre ξ i))
  refine ⟨hH, Upre, hUpre, ?_, hfinite, T, hT, hrest⟩
  intro ξ
  simpa only [hUpre, mul_assoc] using hactual ξ

end AVRegularity.CycleJointProofs
end
end

section
/-! The first-block endpoint energy and retained error, without auxiliary
error-equation witnesses. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

universe u v w x

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]


local instance preparationReferenceRetainedEnergyErrorSummaryNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance preparationReferenceRetainedEnergyErrorSummaryNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance preparationReferenceRetainedEnergyErrorSummaryFluxNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance preparationReferenceRetainedEnergyErrorSummaryFluxNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem preparationReferenceCell_retained_endpoint_energy_error_summary (D Ks Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart CG : ℕ → ℝ) :
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CRemainder := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    let Cgraph := pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CRemainder) Cm
    ∃ Cenergy Cprep CT CR Cterminal : ℝ, 1 ≤ Cenergy ∧ 1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (hζ : IsFastProfile ζfast) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        ∀ (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
        (_henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
        (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) (htSZ : tS ≤ tZ)
        (_hm : 1 ≤ m) (_hseq : IsOCStreamSeq α q Λ ζfast Φ)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (Nperiod : ℕ) (_hperiod : (ocEpsilon q Λ m)⁻¹ = (Nperiod : ℝ))
        (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ),
        let a := (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tS)
        ∀ (b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P (windowCoverReferenceChartIndex P) →
        (∀ t ∈ Set.Icc a b,
          ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
          ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
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
    ∀ (n H N J : ℕ) (_hdepth : F.HasDepthAtMost H) (Cw : ℕ → ℝ)
      (_W : ChartWeights G v a (b - a) ϖ 0 N Cw)
      (_WM : ChartWeights (fun t _ => G t 0) v a (b - a) ϖ 0 N Cw)
      (L : ℝ) (_hL : 1 ≤ L)
      (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
      (_hgain : ENNReal.ofReal (CT * g * ζ) ≤ 1)
      (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
      (τ : ℝ) (_hτ : τ ∈ Set.Icc a b),
    let X := ∀ i, TorusHk (K i) (h i)
    let V₀ := preparationReferenceCellLocalizedInitialFamilyLinearMap hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ).le ha K
      (fun i => by have hh := _hK i; omega) htSZ hζ Npatch hNpatch patch
      (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' yc
    ∃ (uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    (∀ f, IsCoupledWeakSolutionPlane ν tS tZ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (fun i => spatialPatchLocalization hζ Npatch hNpatch patch (K i) (f i))
      (fun _ _ => 0) (fun _ _ => 0) (uphys f) (wphys f)) ∧
    let uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i) := fun f i =>
      preparationReferenceCellNativeCurve hprep hcover (Construction.Stream.ocTauPP_pos hΛ).le ha
        (K i) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc (uphys f i)
    let wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i) := fun f i =>
      preparationReferenceCellNativeCurve hprep hcover (Construction.Stream.ocTauPP_pos hΛ).le ha
        (K i + 1) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc (wphys f i)
    (∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K
      (planeMetricSourceCoefficient K D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0)
      (uH ξ) (wH ξ)) ∧
    ∃ Upre : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
    (∀ ξ i, Upre ξ i = uH ξ i τ) ∧
    (∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq N ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (Upre ξ i)) ≤
      ENNReal.ofReal ((planeSourceRankScale.{u, v} N Kmax Cjet Cw D (Cenergy * θ)) ^ (2 * H)) *
        (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} N Kmax Cjet Cw)) *
        (∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq N ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i))) ∧
    (∀ ξ k, k ≤ N → ∀ i, weightedFactorialNormSq k ϖ 0 (ρ / ocEpsilon q Λ m)
      (K i) (Upre ξ i) ≠ ⊤) ∧
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
        ∀ ξ,
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (Upre ξ i - T ξ i)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζcap ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0 ξ)) := by
  intro Cjet Cflow Cpiola CRemainder Cgraph
  have hr := preparationReferenceCell_retained_endpoint_summary_with_energy.{u, v, w, x}
    D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG
  obtain ⟨Cenergy, Cprep, CT, CR, Cterminal, hCenergy, hCprep, hCT, hCR, hCterminal, hs⟩ := hr
  refine ⟨Cenergy, Cprep, CT, CR, Cterminal, hCenergy, hCprep, hCT, hCR, hCterminal, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ y₀ cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hprep henv hcover htSZ hm hseq htorus Nperiod hperiod Npatch hNpatch patch
    a b hab hwindow hblock θ hrow hcol hdesc hKs hθ hqJ hlength
    ϖ ζ yc G v A n H N J hdepth Cw W WM L hL hreserve hgain hN τ hτ X V₀
  have hp := hs α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ
    g g0 strain B₀ lam Cb qJ y₀ cov hΛ heE ha hgsmall hg0 hD F hmeas hwmeas
    π hπ K hK actual B hB hprep henv hcover htSZ hm hseq htorus Nperiod hperiod
    Npatch hNpatch patch b hab hwindow hblock θ hrow hcol hdesc hKs hθ hqJ hlength
    n H N J hdepth Cw W WM L hL hreserve hgain hN τ hτ
  obtain ⟨uphys, wphys, hphysical, hH, Upre, hUpre, henergy, hfinite, T, hT, hrest⟩ := hp
  refine ⟨uphys, wphys, hphysical, ?_⟩
  intro uH wH
  refine ⟨hH, Upre, hUpre, henergy, hfinite, T, hT, ?_⟩
  intro ξ
  obtain ⟨u, w, ferr, herror, htrace, hbnd⟩ := hrest ξ
  simp only [← hUpre] at hbnd
  exact hbnd

end AVRegularity.CycleJointProofs
end
end

section
/-! Actual following-block Taylor response construction, starting from the
 actual restart from a retained first-cell seam datum. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

universe u v w x y

theorem preparation_following_retained_endpoint_on_retained_seam (D Ks Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart CG : ℕ → ℝ)
    {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3)
    (hs0 : 0 < s) (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    {ζfast : ℝ → ℝ} (hζ : IsFastProfile ζfast) :
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CRemainder := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    let Cgraph := pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CRemainder) Cm
    ∃ Cprep CT CR Cterminal : ℝ, 1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧
      ∀ (Λ m : ℕ) (hΛ128 : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        ∀ (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
        (_henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
        (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output)
        (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Set.Icc tS tZ)
        (_hm : 1 ≤ m) (_hseq : IsOCStreamSeq α q Λ ζfast Φ)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (Nperiod : ℕ) (_hperiod : (ocEpsilon q Λ m)⁻¹ = (Nperiod : ℝ)),
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        Ks + 1 + Kmax ≤ qJ →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    let yc' := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
      (windowCoverFollowingChartIndex P _cov.P_pos)
    ∀ (H : ℕ) (_hdepth : F.HasDepthAtMost H)
      (τ : ℝ)
      (d : ℝ) (_hτd : τ < d) (_hdb : d ≤ (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tZ))
      (_hblockNext : ∀ t ∈ Set.Icc τ d,
        (((l₀ + 1 : ℤ) : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
        ocEll q Λ m ν ^ 2 * t ≤ (((l₀ + 1 : ℤ) : ℝ) + 1 / 2) * ocTauPP α q Λ m),
    ∀ (_hwindowNext : Set.Icc τ d ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P
      (windowCoverFollowingChartIndex P _cov.P_pos)),
    d - τ ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀
      (windowCoverFollowingChartIndex P _cov.P_pos)
    let v := ocCellDrift α q Λ ζfast m ν yc'
    let A := preparationReferenceCellSourceCoefficient F hφ
      (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m)
      ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc'
    ∀ (n N J : ℕ) (Cw : ℕ → ℝ)
      (_W : ChartWeights G v τ (d - τ) ϖ 0 N Cw)
      (_WM : ChartWeights (fun t _ => G t 0) v τ (d - τ) ϖ 0 N Cw)
      (L : ℝ) (_hL : 1 ≤ L)
      (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
      (_hgainEndpoint : ENNReal.ofReal (CT * g * ζ) ≤ 1)
      (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
      (τend : ℝ) (_hτend : τend ∈ Set.Icc τ d),
    ∀ {X : Type y} [AddCommGroup X] [Module ℝ X]
      (Tpre : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (_hTpre : ∀ ξ n i, weightedFactorialNormSq n ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (Tpre ξ i) ≠ ⊤),
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc0 := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let tp := ν⁻¹ * (ocEpsilon q Λ m ^ 2 * τ)
    let htp : tp ∈ Set.Icc tS tZ :=
      (windowCover_native_subwindow_scales hΛ hφ _cov
        (windowCoverFollowingChartIndex P _cov.P_pos) τ d _hwindowNext).2.1 τ ⟨le_rfl, _hτd.le⟩
    let lf := preparationReferenceRetainedEndpointLinearMap hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ).le ha K (fun i => by have hh := _hK i; omega)
      (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' yc0 tp htp Tpre
    ∃ (uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    (∀ f, IsCoupledWeakSolutionPlane ν tp tZ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (lf f)
      (fun _ _ => 0) (fun _ _ => 0) (uphys f) (wphys f)) ∧
    let uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i) := fun f i =>
      preparationWindowReferenceCellNativeCurve hprep hcover
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext ha
        (K i) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc' (uphys f i)
    let wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i) := fun f i =>
      preparationWindowReferenceCellNativeCurve hprep hcover
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext ha
        (K i + 1) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc' (wphys f i)
    ∃ V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
      (∀ ξ, IsCoupledWeakSolutionPlane 1 τ d (ocCellDrift α q Λ ζfast m ν yc') D K
        (planeMetricSourceCoefficient K D
          (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + 1) ν yc')
          (preparationReferenceCellSourceCoefficient F hφ (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m)
            ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc'))
        (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0) (uH ξ) (wH ξ)) ∧
      (∀ ξ n i, weightedFactorialNormSq n ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i) ≠ ⊤) ∧
      (∀ ξ i, V₀ ξ i = preparationReferenceCellTransitionOperator hprep hcover
        (Construction.Stream.ocTauPP_pos hΛ).le ha (K i) (by have hh := _hK i; omega)
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext (ocEpsilon q Λ m)
        (Construction.Stream.ocEpsilon_pos hΛ).ne' yc0 yc' tp htp (Tpre ξ i)) ∧
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
          (ENNReal.ofReal (cellTransitionMomentBudget Kmax N) *
            ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (Tpre ξ i))
        ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
        (∀ ξ r i, weightedFactorialNormSq r ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (T ξ i) ≠ ⊤) ∧
        ∀ ξ, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
          (ferr : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))),
          IsCoupledWeakSolutionPlane 1 τ d v D K
            (planeMetricSourceCoefficient K D G A) (fun _ => 0) ferr (fun _ _ => 0)
            (fun i t => uH ξ i t - u i t) (fun i t => wH ξ i t - w i t) ∧
          (∀ i, T ξ i = u i τend) ∧
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (uH ξ i τend - T ξ i)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζcap ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0 ξ)) := by
  intro Cjet Cflow Cpiola CRemainder Cgraph
  have hend := windowCover_window_reference_retained_endpoint_summary.{u, v, w, x, y}
    D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG
  let Cprep := hend.choose
  let CT := hend.choose_spec.choose
  let CR := hend.choose_spec.choose_spec.choose
  let Cterminal := hend.choose_spec.choose_spec.choose_spec.choose
  have hs := hend.choose_spec.choose_spec.choose_spec.choose_spec
  have he := hs.2.2.2.2
  refine ⟨Cprep, CT, CR, Cterminal, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro Λ m hΛ128 Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0
    strain B₀ lam Cb qJ y₀ cov hΛ heE ha hgsmall hg0 hD
    ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hprep henv hcover hnext hm hseq htorus Nperiod hperiod
    θ hrow hcol hdesc hKs hθ hqJ ϖ ζ yc' H hdepth τ d hτd hdb hblockNext hwindowNext
    hlengthNext G v A n N J Cw W WM L hL hreserve hgainEndpoint hN τend hτend
    X _ _ Tpre hTpre seed yc0 tp htp lf
  have htime : (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tp) = τ := by
    dsimp only [tp]
    field_simp [cov.pos.1.ne', (Construction.Stream.ocEpsilon_pos hΛ).ne']
  have hp := exists_preparation_retained_restart_all_moment_coupled_family
    F H hdepth htp.2 (show Set.Icc tp tZ ⊆ Set.Icc tS tZ from
      fun _ ht => ⟨htp.1.trans ht.1, ht.2⟩)
    ρ cov.pos.2.2 K hdesc hD hprep hcover hnext
    (Construction.Stream.ocTauPP_pos hΛ).le ha Kmax Jm hK hchart hmol
    Cm π hπ B hB hmeas hwmeas hΛ128 s hα0 hα1 hs0 hs1 hq hζ hm hseq
    ν (ocEpsilon q Λ m) cov.pos.1 rfl cov.rho_e heE henv actual htorus hperiod y₀
    Tpre ϖ hTpre d (by rw [htime]; exact hτd.le) hdb
    (by rw [htime]; exact hblockNext)
  dsimp only at hp
  rw [htime] at hp
  obtain ⟨uphys, wphys, hphysical, V₀, hcoupled, hV₀, hident, hprice⟩ := hp
  refine ⟨uphys, wphys, hphysical, ?_⟩
  intro uH wH
  refine ⟨V₀, hcoupled, hV₀, hident, ?_⟩
  have hH : ∀ ξ, IsCoupledWeakSolutionPlane 1 τ d v D K
      (planeMetricSourceCoefficient K D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0) (uH ξ) (wH ξ) := by
    intro ξ
    dsimp only [G, windowCoverCellMetric]
    rw [windowCoverFollowingChartIndex_label]
    exact hcoupled ξ
  have hr := he (X := X) α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ
    g g0 strain B₀ lam Cb qJ y₀ cov hΛ heE ha hgsmall hg0 hD F hmeas hwmeas
    π hπ K hK actual B hB hprep hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext henv
    (windowCoverFollowingChartIndex P cov.P_pos) τ d hτd hwindowNext θ hrow hcol hdesc hKs hθ hqJ hlengthNext
    n H N J hdepth Cw W WM V₀ hV₀ uH wH hH L hL hreserve hgainEndpoint hN τend hτend
  obtain ⟨T, hTall, herr⟩ := hr
  refine ⟨T, hTall, ?_⟩
  intro ξ
  obtain ⟨u, w, ferr, herror, htrace, hbnd⟩ := herr ξ
  refine ⟨u, w, ferr, herror, htrace, hbnd.trans ?_⟩
  dsimp only
  gcongr
  exact hprice ξ N

end AVRegularity.CycleJointProofs
end
end
