-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PreparationFollowingRetainedEndpointOnRetainedSeam
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
public import AVRegularity.CycleJoint.PointwiseNativeTransportIdentityPrice

/-! Actual following-block Taylor response construction, starting from the
 actual restart from a retained first-cell seam datum. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

universe u v w x y

private theorem endpointResidualPrice_reassociate {x a b c d e f : ℝ≥0∞}
    (hx : x ≤ a * (b * (c * (d * (e * f))))) :
    x ≤ (a * (b * c) * d * e) * f := by
  simpa only [mul_assoc] using hx

theorem preparation_following_retained_endpoint_error_summary (D Ks Kmax Jchart Jm : ℕ)
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
    let _A := preparationReferenceCellSourceCoefficient F hφ
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
        ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
        (∀ ξ r i, weightedFactorialNormSq r ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (T ξ i) ≠ ⊤) ∧
        ∀ ξ,
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (uH ξ i τend - T ξ i)) ≤
          (ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζcap ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))))) *
            ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} N Kmax Cw) *
            ENNReal.ofReal (cellTransitionMomentBudget Kmax N)) *
            (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0
              (ρ / ocEpsilon q Λ m) (K i) (Tpre ξ i)) := by
  intro Cjet Cflow Cpiola CRemainder Cgraph
  have hr := preparation_following_retained_endpoint_on_retained_seam.{u, v, w, x, y}
    D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG hα0 hα1 hs0 hs1 hq hζ
  let Cprep := hr.choose
  let CT := hr.choose_spec.choose
  let CR := hr.choose_spec.choose_spec.choose
  let Cterminal := hr.choose_spec.choose_spec.choose_spec.choose
  have hs := hr.choose_spec.choose_spec.choose_spec.choose_spec
  refine ⟨Cprep, CT, CR, Cterminal, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro Λ m hΛ128 Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb qJ y₀
    cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hprep henv hcover hnext hm hseq htorus Nperiod hperiod θ hrow hcol hdesc hKs hθ hqJ
    ϖ ζ yc' H hdepth τ d hτd hdb hblock hwindow hlength G v A
    n N J Cw W WM L hL hreserve hgain hN τend hτend X _ _ Tpre hTpre seed yc0 tp htp lf
  have hp := hs.2.2.2.2 Λ m hΛ128 Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ y₀ cov hΛ heE ha hgsmall hg0 hD F hmeas hwmeas π hπ K hK actual B hB
    hprep henv hcover hnext hm hseq htorus Nperiod hperiod θ hrow hcol hdesc hKs hθ hqJ
    H hdepth τ d hτd hdb hblock hwindow hlength n N J Cw W WM L hL hreserve hgain
    hN τend hτend Tpre hTpre
  refine hp.elim fun uphys h1 => h1.elim fun wphys h2 => ?_
  refine ⟨uphys, wphys, h2.1, ?_⟩
  intro uH wH
  refine h2.2.elim fun V₀ h3 => ?_
  refine ⟨V₀, h3.1, h3.2.1, h3.2.2.1, ?_⟩
  refine h3.2.2.2.elim fun T h4 => ?_
  refine ⟨T, h4.1, fun ξ => ?_⟩
  exact (h4.2 ξ).elim fun _ h5 => h5.elim fun _ h6 => h6.elim fun _ hh =>
    endpointResidualPrice_reassociate hh.2.2

end AVRegularity.CycleJointProofs
