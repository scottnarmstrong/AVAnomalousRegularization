-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.ActualPreparationHomogeneousFamilyNativeTraceLinearMap
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
import AVRegularity.CycleJoint.PlaneRetainedActualTaylorInitialDataEndpointPrice
import AVRegularity.CycleJoint.PreparationReferenceNormalizedHilbertCurve
import AVRegularity.CycleJoint.PlaneMetricActualTaylorRetainedGradientGain

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Every actual cover chart supplies the drift and windowed metric data for
 the quantitative homogeneous native endpoint estimate. -/

section
universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρ g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_homogeneous_difference_endpoint_energy
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (ic : Fin (P + 2)) (a b : ℝ) (hab : a ≤ b)
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P ic)
    (hqJ : max Kmax 1 ≤ qJ) (hg4 : g ≤ 1 / 4)
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Kmax) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D H n : ℕ) (hD : 2 ≤ D) (Cw : ℕ → ℝ) (ϖ : ℝ) :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let v := ocCellDrift α q Λ ζ m ν yc
    let r := ρ / ocEpsilon q Λ m
    let Cjet := fun j => max (CG j) 0
    ∀ (_W : ChartWeights G v a (b - a) ϖ 0 n Cw)
      (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => h i))
      (_hA : ∀ i j d, coefficientSeminorm r (K i) a b (A i j d) ≠ ⊤)
      (_hc : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
      (_hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
      (Bsrc : ℝ)
      (_hrow : ∀ i, ∑ j, schurMatrix 1 r π K D a b A i j ≤ Bsrc)
      (_hcol : ∀ j, ∑ i, schurMatrix 1 r π K D a b A i j ≤ Bsrc)
      (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
      (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
      (U₀ : ∀ i, PlaneHk Set.univ (K i) (h i))
      (_hUinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (U₀ i) ≠ ⊤)
      (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Uw : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (V₀ : ∀ i, PlaneHk Set.univ (K i) (h i))
      (_hinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (V₀ i) ≠ ⊤)
      (V : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Vw : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      U₀ (fun _ _ => 0) (fun _ _ => 0) U Uw →
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      V₀ (fun _ _ => 0) (fun _ _ => 0) V Vw →
    ∀ t ∈ Set.Icc a b,
      (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U i t - V i t)) ≤
        ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D Bsrc) ^ (2 * H)) *
          (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) *
            ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U₀ i - V₀ i)) := by
  intro yc G v r Cjet W A hA hc hAm Bsrc hrow hcol rank hrank hzero
    U₀ hUinit U Uw V₀ hinit V Vw hU hV t ht
  have hdiff := planeWeakSolution_sub K D 1 a b v
    (planeMetricSourceCoefficient K D G A) U₀ V₀
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) U V Uw Vw hU hV
  simp only [sub_self] at hdiff
  have hfinite (i : ι) : weightedFactorialNormSq n ϖ 0 r (K i) (U₀ i - V₀ i) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (weightedFactorialNormSq_sub_le n ϖ 0 r (U₀ i) (V₀ i))
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨hUinit i, hinit i⟩)
  exact windowCover_homogeneous_endpoint_energy hΛ hζ hφ cov heE ic a b hab hwindow hqJ hg4
    K hK π hπ D H n hD Cw ϖ W A hA hc hAm Bsrc hrow hcol rank hrank hzero
    (fun i => U₀ i - V₀ i) hfinite (fun i t => U i t - V i t)
    (fun i t => Uw i t - Vw i t) hdiff t ht
end

/-! Every actual cover chart supplies the drift and windowed metric data for
 the quantitative homogeneous native endpoint estimate. -/

section
universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρ g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_restart_retained_endpoint_error
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
    (ic : Fin (P + 2)) (a b : ℝ) (hab : a ≤ b)
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P ic)
    (hqJ : max Kmax 1 ≤ qJ) (hg4 : g ≤ 1 / 4)
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Kmax) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D H n : ℕ) (hD : 2 ≤ D) (Cw : ℕ → ℝ) (ϖ : ℝ) :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let v := ocCellDrift α q Λ ζ m ν yc
    let r := ρ / ocEpsilon q Λ m
    let Cjet := fun j => max (CG j) 0
    ∀ (_W : ChartWeights G v a (b - a) ϖ 0 n Cw)
      (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => h i))
      (_hA : ∀ i j d, coefficientSeminorm r (K i) a b (A i j d) ≠ ⊤)
      (_hc : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
      (_hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
      (Bsrc : ℝ)
      (_hrow : ∀ i, ∑ j, schurMatrix 1 r π K D a b A i j ≤ Bsrc)
      (_hcol : ∀ j, ∑ i, schurMatrix 1 r π K D a b A i j ≤ Bsrc)
      (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
      (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
      (U₀ : ∀ i, PlaneHk Set.univ (K i) (h i))
      (_hUinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (U₀ i) ≠ ⊤)
      (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Uw : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (V₀ : ∀ i, PlaneHk Set.univ (K i) (h i))
      (_hinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (V₀ i) ≠ ⊤)
      (V : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Vw : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      U₀ (fun _ _ => 0) (fun _ _ => 0) U Uw →
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      V₀ (fun _ _ => 0) (fun _ _ => 0) V Vw →
    ∀ t ∈ Set.Icc a b,
    let EinDiff := ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U₀ i - V₀ i)
    let Cactual := ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D Bsrc) ^ (2 * H)) *
      (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw))
    ∀ (Tret : ∀ i, PlaneHk Set.univ (K i) (h i)) (Aerr : ℝ≥0∞),
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (V i t - Tret i)) ≤ Aerr →
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U i t - Tret i)) ≤
      2 * (Cactual * EinDiff + Aerr) := by
  intro yc G v r Cjet W A hA hc hAm Bsrc hrow hcol rank hrank hzero
    U₀ hUinit U Uw V₀ hinit V Vw hU hV t ht EinDiff Cactual Tret Aerr herr
  have hprop : (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U i t - V i t)) ≤
      Cactual * EinDiff := by
    simpa only [Cactual, EinDiff, mul_assoc] using
      windowCover_homogeneous_difference_endpoint_energy hΛ hζ hφ cov heE ic a b hab hwindow hqJ hg4
        K hK π hπ D H n hD Cw ϖ W A hA hc hAm Bsrc hrow hcol rank hrank hzero
        U₀ hUinit U Uw V₀ hinit V Vw hU hV t ht
  have hsum (i : ι) : (U i t - V i t) + (V i t - Tret i) = U i t - Tret i := by abel
  have hquad := planeFamily_polynomial_energy_add_le K π n ϖ 0 r
    (fun i => U i t - V i t) (fun i => V i t - Tret i)
  simp only [hsum] at hquad
  exact hquad.trans (mul_le_mul_right (add_le_add hprop herr) 2)
end

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

theorem preparation_reference_cell_constructed_edge_package (D Kmax Jchart Jm : ℕ)
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
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (a b ϖ : ℝ) (_hab : a ≤ b),
          Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        ∀ (Ks : ℕ), F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        0 ≤ ocTauPP α q Λ m → 0 ≤ ocA α q Λ (m - 1) →
        ∀ ζ : ℝ, 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ →
        e / ocEpsilon q Λ (m - 1) = ζ * ϖ →
        (∀ τ ∈ Set.Icc a b, ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ) →
    ∃ Rs : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b)),
    ∃ Ledge : ∀ v u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b)),
    ((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (nativeFamilyEdgeForcingMap Ledge v + Rs v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
        (fun x t z => ∑ u, ∑ γ, naturalFamilyTaylorRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
          (ν⁻¹ * e ^ 2) hφ (fun p => (F.piece p).anchor)
          ((l₀ : ℝ) * ocTauPP α q Λ m) e (ocEpsilon q Λ (m - 1)) yc ϖ (ρ / e)
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
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) ∧
    (∀ u, ∑ v, schurMatrix 1 (ρ / e) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) := by
  obtain ⟨Cprep, hCprep, hmaps⟩ := preparation_reference_cell_source_maps_with_schur_and_remainder
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB hc henv
    yc a b ϖ hab hsub θ hrow hcol Ks hdesc hKs hθ hTau ha ζ hϖ hscale hζ hδ htime
  classical
  obtain ⟨T, Lfull, ⟨hsplit, hrem⟩, hmass, hrows, hcols⟩ := hmaps
    α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F hmeas hwmeas π hπ K hK actual B hB hc henv yc a b ϖ hab hsub θ hrow hcol
    Ks hdesc hKs hθ hTau ha ζ hϖ hscale hζ hδ htime
  let Rs := nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p)
  obtain ⟨Ledge, hsource, htaylor, hzero, hdegree⟩ := naturalFamilyTaylor_constructed_split_edges
    Ks F (F.locally_finite tS tZ).toFinset actual K (ν⁻¹ * e ^ 2) hφ
    (fun p => (F.piece p).anchor) ((l₀ : ℝ) * ocTauPP α q Λ m) e (ocEpsilon q Λ (m - 1))
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
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The genuine physical preparation equation transfers to the full homogeneous coupled weak solution class in reference cell coordinates. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_cell_metric_source_coupled_solution_subwindow
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (ν e E : ℝ) (hν : 0 < ν) (n : ι → ℕ)
    (hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ i i' o, coefficientSeminorm ρ (K i) c d (edgeCoefficient F ν e E actual K i i' o) ≠ ⊤)
    (hc : ∀ i i' o t, t ∈ Icc c d → ContDiff ℝ (K i : ℕ) (edgeCoefficient F ν e E actual K i i' o t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t))
    (hvc : ∀ t ∈ Icc c d, Continuous (v t))
    (hvm : Measurable (fun p : Icc c d × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc c d, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' o, Measurable (fun p : Icc c d × Vec 2 => edgeCoefficient F ν e E actual K i i' o p.1 p.2))
    (hcell : e ≠ 0) (yc : Vec 2)
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν c d v D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    IsCoupledWeakSolutionPlane 1 ((e⁻¹) ^ 2 * (ν * c)) ((e⁻¹) ^ 2 * (ν * d))
      (fun t z => e • normalizedMaterialVelocity hφ σ ν v
        (e ^ 2 * t) (yc + e • z)) D K
      (planeMetricSourceCoefficient K D
        (fun t z => CycleReference.chartMetric hφ σ
          (ν⁻¹ * (e ^ 2 * t)) (yc + e • z))
        (preparationReferenceCellSourceCoefficient F hφ σ
          ν e E actual K yc))
      (fun j => planeCarrierAffine e hcell yc (preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
        (by have hh := hK j; omega) c (f j)))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e hcell yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e hcell yc (W j (ν⁻¹ * (e ^ 2 * t)))) := by
  dsimp only
  have hh := preparation_window_reference_cell_coupled_solution_subwindow F hcd hsub ρ hρ K hdesc hD
    hprep hcover σ hσ ha hK ν e E hν n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm
    hcell yc f u w hs
  have hcoeff : (fun i i' d t z => (e * (e ^ (d.1 - 1))⁻¹) •
        preparationReferenceNormalizedCoefficient F hφ σ ν e E actual K
          i i' d (e ^ 2 * t) (yc + e • z)) = (planeMetricSourceCoefficient K D
        (fun t z => CycleReference.chartMetric hφ σ
          (ν⁻¹ * (e ^ 2 * t)) (yc + e • z))
        (preparationReferenceCellSourceCoefficient F hφ σ
          ν e E actual K yc)) := by
    exact preparationReferenceCellCoefficient_eq_metricSource F hφ σ
      ν e E actual K yc hcell
  rw [hcoeff] at hh
  exact hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Finite mixed endpoint operators on an actual covered chart retain every polynomial moment at the chosen endpoint. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance mixedEndpointMomentScalarNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance mixedEndpointMomentScalarNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance mixedEndpointMomentScalarCarrierAdd (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance mixedEndpointMomentScalarCarrierModule (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

variable (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
  (K : ι → ℕ) (a b ϖ ρ : ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
  (Lmetric Lsource : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (lf : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
  (u₀ : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
  (w₀ : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
  (Z : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b))))

variable {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem windowCover_finite_mixed_endpoint_all_moments
    (family : ChartedFamily ι h D P Ctx) (H J : ℕ) (hdepth : family.HasDepthAtMost H)
    (hM : HasSourceDegreeOn family 0 (nativeComponentResponseOperator R Lmetric))
    (hS : HasSourceDegreeOn family 1 (nativeComponentResponseOperator R Lsource))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (hbase : ∀ x, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t))
      (fun _ i => K i) a b v (fun _ i => lf x i) (fun _ _ _ => 0)
      (fun _ i => u₀ x i) (fun _ i => w₀ x i))
    (hZ : ∀ x i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (Z x i) (w₀ x i))
    (hab : a < b) (τ : ℝ) (hτ : τ ∈ Set.Icc a b)
    (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ) (qJ Kmax : ℕ) (CG : ℕ → ℝ)
    (l₀ : ℤ) (Pcover : ℕ) (y₀ : Vec 2)
    (cov : IsWindowCover α q Λ m ζfast Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ Pcover y₀)
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζfast) (hK : ∀ i, K i ≤ Kmax)
    (ic : Fin (Pcover + 2))
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ Pcover ic)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (hlength : b - a ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (hρ : ρ = ρs / ocEpsilon q Λ m)
    (hmetric : M = fun t => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + ic) ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀ ic) t 0)
    (hdrift : v = ocCellDrift α q Λ ζfast m ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀ ic))
    (hf : ∀ ξ n i, weightedFactorialNormSq n ϖ 0 ρ (K i) (lf ξ i) ≠ ⊤) :
    let W : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1)
      ϖ ρ 0 (volume.restrict (Set.Icc a b))) :=
      (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1),
        finiteResponseOperator 1 (nativeComponentResponseOperator R Lmetric)
          (nativeComponentResponseOperator R Lsource) j n).comp Z
    ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
      ∀ x, ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
        (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
        (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
        IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
          (fun _ i => lf x i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) ∧
        (∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W x i) (w i)) ∧
        (∀ i, ∃ Q : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
          (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)),
          PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)) Q (F i)) ∧
        (∀ i, T x i = u i τ) ∧
        ∀ n i, weightedFactorialNormSq n ϖ 0 ρ (K i) (T x i) ≠ ⊤ := by
  classical
  subst ρ
  obtain ⟨T, hT⟩ := planeComponentAllMomentResponse_finite_mixed_endpoint_with_forcing_linearMap
    M v K a b ϖ (ρs / ocEpsilon q Λ m) R Lmetric Lsource lf u₀ w₀ Z
    family H J hdepth hM hS hR hbase hZ hab τ hτ
  refine ⟨T, ?_⟩
  intro ξ
  obtain ⟨F, u, w, hs, hw, hF, htrace⟩ := hT ξ
  have hFcopy := hF
  choose Q hQ using hFcopy
  have hchain : let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀ ic
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + ic) ν yc t 0))
        (fun _ i => K i) a b (ocCellDrift α q Λ ζfast m ν yc)
        (fun _ i => lf ξ i) (fun _ i => F i) (fun _ i => u i) (fun _ i => w i) := by
    dsimp only
    have hs' := hs
    rw [hmetric, hdrift] at hs'
    exact hs'
  have hfinite := windowCover_frozen_response_endpoint_all_moments hΛ hζ hφ cov K hK ic
    a b hab hwindow hgsmall hg0 hlength ϖ hϖ F Q hQ (lf ξ) (hf ξ) u w hchain
  refine ⟨F, u, w, hs, hw, hF, htrace, ?_⟩
  intro n i
  rw [htrace i]
  exact hfinite n i τ hτ

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

theorem preparation_reference_cell_natural_block_coupled_solution
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hΨ : IsAdmissibleStream (Φ m))
    (ν e E : ℝ) (hν : 0 < ν) (heScale : e = ocEpsilon q Λ m) (n : ι → ℕ)
    (hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (edgeCoefficient F ν e E actual K i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Icc a b → ContDiff ℝ (K i : ℕ) (edgeCoefficient F ν e E actual K i i' d t))
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (streamVel (Φ m)) p.1 p.2))
    (hp : ∀ t, IsZ2Periodic ((streamVel (Φ m)) t))
    (hvc : ∀ t ∈ Icc a b, Continuous ((streamVel (Φ m)) t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => (streamVel (Φ m)) p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖(streamVel (Φ m)) t x‖ ≤ M)
    (hAm : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => edgeCoefficient F ν e E actual K i i' d p.1 p.2))
    (hcell : e ≠ 0) (yc : Vec 2)
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (c d : ℝ) (hac : (e⁻¹) ^ 2 * (ν * a) ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * b))
    (hblock : ∀ t ∈ Icc c d,
      ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hs : IsCoupledWeakSolutionPlane ν a b (streamVel (Φ m)) D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    IsCoupledWeakSolutionPlane 1 c d
      (ocCellDrift α q Λ ζ m ν yc) D K
      (planeMetricSourceCoefficient K D
        (ocCellMetric α q Λ m (Φ (m - 1)) hφ l₀ ν yc)
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
          ν e E actual K yc))
      (fun j => planeCarrierAffine e hcell yc (U j (ν⁻¹ * (e ^ 2 * c))))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e hcell yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e hcell yc (W j (ν⁻¹ * (e ^ 2 * t)))) := by
  dsimp only
  have hh := preparation_reference_cell_metric_source_coupled_solution F hab ρ hρ K hdesc hD
    hprep hcover hTau ha hK ν e E hν n hsmooth actual hT he hA hc
    (streamVel (Φ m)) hv hp hvc hvm M hvb hAm hcell yc f u w hs
  have hr := planeWeakSolution_restart_subwindow K D 1 _ _ c d hac hcd hdb
    _ _ _ _ _ _ _ hh
  subst e
  rw [preparationReferenceCellMetric_eq_ocCellMetric α q Λ m hφ l₀ ν hν yc] at hr
  exact planeWeakSolution_naturalBlock_cell_drift hΛ hseq hm hφ hΨ hν l₀ yc
    K _ c d hblock _ _ _ _ _ hr
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

theorem preparation_window_reference_cell_natural_block_coupled_solution_subwindow
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b u0 u1 : ℝ} (h01 : u0 ≤ u1) (hsub : Icc u0 u1 ⊆ Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (l : ℤ) (hσ : (l : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hΨ : IsAdmissibleStream (Φ m))
    (ν e E : ℝ) (hν : 0 < ν) (heScale : e = ocEpsilon q Λ m) (n : ι → ℕ)
    (hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) u0 u1 (edgeCoefficient F ν e E actual K i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Icc u0 u1 → ContDiff ℝ (K i : ℕ) (edgeCoefficient F ν e E actual K i i' d t))
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (streamVel (Φ m)) p.1 p.2))
    (hp : ∀ t, IsZ2Periodic ((streamVel (Φ m)) t))
    (hvc : ∀ t ∈ Icc u0 u1, Continuous ((streamVel (Φ m)) t))
    (hvm : Measurable (fun p : Icc u0 u1 × Vec 2 => (streamVel (Φ m)) p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc u0 u1, ∀ x, ‖(streamVel (Φ m)) t x‖ ≤ M)
    (hAm : ∀ i i' d, Measurable (fun p : Icc u0 u1 × Vec 2 => edgeCoefficient F ν e E actual K i i' d p.1 p.2))
    (hcell : e ≠ 0) (yc : Vec 2)
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (c d : ℝ) (hac : (e⁻¹) ^ 2 * (ν * u0) ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * u1))
    (hblock : ∀ t ∈ Icc c d,
      ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hs : IsCoupledWeakSolutionPlane ν u0 u1 (streamVel (Φ m)) D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    IsCoupledWeakSolutionPlane 1 c d
      (ocCellDrift α q Λ ζ m ν yc) D K
      (planeMetricSourceCoefficient K D
        (ocCellMetric α q Λ m (Φ (m - 1)) hφ l ν yc)
        (preparationReferenceCellSourceCoefficient F hφ ((l : ℝ) * ocTauPP α q Λ m)
          ν e E actual K yc))
      (fun j => planeCarrierAffine e hcell yc (U j (ν⁻¹ * (e ^ 2 * c))))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun j t => planeCarrierAffine e hcell yc (U j (ν⁻¹ * (e ^ 2 * t))))
      (fun j t => planeCarrierAffine e hcell yc (W j (ν⁻¹ * (e ^ 2 * t)))) := by
  dsimp only
  have hh := preparation_window_reference_cell_metric_source_coupled_solution_subwindow F h01 hsub ρ hρ K hdesc hD
    hprep hcover ((l : ℝ) * ocTauPP α q Λ m) hσ ha hK ν e E hν n hsmooth actual hT he hA hc
    (streamVel (Φ m)) hv hp hvc hvm M hvb hAm hcell yc f u w hs
  have hr := planeWeakSolution_restart_subwindow K D 1 _ _ c d hac hcd hdb
    _ _ _ _ _ _ _ hh
  subst e
  rw [preparationReferenceCellMetric_eq_ocCellMetric α q Λ m hφ l ν hν yc] at hr
  exact planeWeakSolution_naturalBlock_cell_drift hΛ hseq hm hφ hΨ hν l yc
    K _ c d hblock _ _ _ _ _ hr
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords AVRegularity.ChartTransport
open scoped ENNReal
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Subtracting the constructed original remainder from the actual native
source map gives precisely the natural Taylor source, with an exact map split. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem exists_preparationWindowReferenceCellSourceMaps_with_remainder_budget
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc tS tZ)
    (ν e ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1)) (actual : ∀ p, Ctx p)
    (K : ι → ℕ) (hdesc : F.IsDescending K) (Ks : ℕ)
    (yc : Vec 2) (a b ϖ : ℝ) (hab : a ≤ b)
    (Kmax Jm : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm) (Cm : ℕ → ℝ)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (B : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    (hsub : Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)))
    (hKs : Ks + 1 ≤ Jm) (θ : ℝ) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, B v u ≤ θ) (hcol : ∀ u, ∑ v, B v u ≤ θ)
    (ha : 0 ≤ ocA α q Λ (m - 1))
    (ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1) (hζ : 0 ≤ ζ)
    (hδ : e / ocEpsilon q Λ (m - 1) = ζ * ϖ)
    (htime : ∀ τ ∈ Set.Icc a b, ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ) :
    ∃ T : ∀ v u, F.Γ v u → Fin D → (F.locally_finite tS tZ).toFinset →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    ∃ Lfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    ((∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
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
          (volume.restrict (Set.Icc a b)) (Z u) τ) ∂volume.restrict (Set.Icc a b) := by
  have he : 0 < e := hρ.trans_le hρe
  have hE : 0 < ocEpsilon q Λ (m - 1) := he.trans_le heE
  have hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e :=
    div_le_div_of_nonneg_right (hρe.trans heE) he.le
  have hN : Kmax + D ≤ Jchart := by omega
  obtain ⟨T, hT, hmass⟩ := exists_preparationWindowNaturalRemainder_maps_mass_budget Ks F hwmeas hmeas
    π hπ K Kmax hK hdesc ν e (ocEpsilon q Λ (m - 1)) ρ hν he hE hρ Cm Jm B henv
    hKs hB θ hθ hrow hcol actual hc hcover σ hσ ha hsE ϖ ζ hϖ hscale hζ hδ
    (ν⁻¹ * e ^ 2) a b (fun τ ht => by simpa only [mul_assoc] using htime τ ht)
    hN hE yc (volume.restrict (Set.Icc a b))
  obtain ⟨Lfull, hfull, htaylor⟩ := exists_preparationWindowReferenceCellSourceMap_natural_split F hc hcover σ hσ ν e ρ
    hν hρ hρe heE actual K hdesc Ks yc a b ϖ hab Kmax Jm hK hchart hmol Cm hmeas hwmeas
    π hπ B hB henv hsub htime T hT
  exact ⟨T, Lfull, ⟨hfull, htaylor⟩, hmass⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The same actual native frozen response operator preserves every polynomial moment, allowing finite insertions to compose on one carrier. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

local instance coverAllDomainResponseNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := inferInstance
local instance coverAllDomainResponseLpAdd (i : ι) (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance coverAllDomainResponseLpModule (i : ι) (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance coverAllDomainResponseNativeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance coverAllDomainResponseNativeModule (i : ι) (k : ℕ) : Module ℝ (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance coverAllDomainResponseFluxAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance coverAllDomainResponseFluxModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

theorem windowCover_frozen_response_all_moment_linearMap (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8)
    (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (lf : X →ₗ[ℝ] (∀ x, PlaneHk Set.univ (K x) (h x)))
    (lF : X → ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hadd : ∀ a b x, lF (a + b) x =ᵐ[volume.restrict (Set.Icc u0 u1)]
      fun t => lF a x t + lF b x t)
    (hsmul : ∀ (c : ℝ) a x, lF (c • a) x =ᵐ[volume.restrict (Set.Icc u0 u1)]
      fun t => c • lF a x t)
    (hF : ∀ a x, MemLp (lF a x) 2 (volume.restrict (Set.Icc u0 u1)))
    (hf : ∀ a n x, weightedFactorialNormSq n ϖ 0
      (ρs / ocEpsilon q Λ m) (K x) (lf a x) ≠ ⊤)
    (hFe : ∀ a n x, (∫⁻ t in Set.Icc u0 u1,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (lF a x t)) ≠ ⊤) :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ T : ∀ x, X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := h x)
      (K x + 1) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)),
      ∀ a, ∃ (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
        (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
        IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
          ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
          (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
          (fun _ x => lf a x) (fun _ x => lF a x) (fun _ x => u x) (fun _ x => w x) ∧
          (∀ x, PlaneTimeAllMomentRepresents (K x + 1) ϖ (ρs / ocEpsilon q Λ m) 0
              (volume.restrict (Set.Icc u0 u1)) (T x a) (w x)) ∧
            ∀ n x,
              ((⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
                (ρs / ocEpsilon q Λ m) (K x) (u x t)) +
                ∫⁻ t in Set.Icc u0 u1, weightedGradFactorialNormSq n ϖ 0
                  (ρs / ocEpsilon q Λ m) (K x) (w x t)) ≠ ⊤ ∧
              (∫⁻ t in Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
                (ρs / ocEpsilon q Λ m) (K x + 1) (w x t)) ≠ ⊤ := by
  classical
  obtain ⟨T, hT⟩ := windowCover_frozen_response_ae_liftLinearMap hΛ hζ hφ cov K hK i
    u0 u1 hu.le hwindow hgsmall lf lF hadd hsmul hF
  choose u w hs hw heq using hT
  have hmoment (a : X) (n : ℕ) := windowCover_frozen_response_moment_propagation
    hΛ hζ hφ cov K hK i u0 u1 hu hwindow hgsmall hg0 hlength n ϖ hϖ (lF a) (hF a) (lf a)
    (fun k _ x => hf a k x) (fun k _ x => hFe a k x) (u a) (w a) (hs a)
  let T' := fun x => planeTimeAllMomentCarrierLinearMap (K x + 1) ϖ (ρs / ocEpsilon q Λ m) 0
    (volume.restrict (Set.Icc u0 u1)) (T x) (fun a => w a x) (fun a => hw a x)
    (fun a => congrFun (heq a) x) (fun a n => (hmoment a n n (le_refl n) x).2)
  refine ⟨T', ?_⟩
  intro a
  exact ⟨u a, w a, hs a,
    fun x => planeTimeAllMomentCarrierLinearMap_represents (K x + 1) ϖ
      (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)) (T x)
      (fun a => w a x) (fun a => hw a x) (fun a => congrFun (heq a) x)
      (fun a n => (hmoment a n n (le_refl n) x).2) a,
    fun n x => hmoment a n n (le_refl n) x⟩
end

/-! Homogeneous native chart responses are linear in compact initial data before any datum is selected. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

local instance coverHomogeneousLinearNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := inferInstance
local instance coverHomogeneousLinearLpAdd (i : ι) (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance coverHomogeneousLinearLpModule (i : ι) (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance coverHomogeneousLinearNativeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance coverHomogeneousLinearNativeModule (i : ι) (k : ℕ) : Module ℝ (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance coverHomogeneousLinearFluxAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance coverHomogeneousLinearFluxModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

theorem windowCover_frozen_homogeneous_all_moment_linearMap (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8)
    (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (lf : X →ₗ[ℝ] (∀ x, PlaneHk Set.univ (K x) (h x)))
    (hf : ∀ a n x, weightedFactorialNormSq n ϖ 0
      (ρs / ocEpsilon q Λ m) (K x) (lf a x) ≠ ⊤)
 :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ T : ∀ x, X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := h x)
      (K x + 1) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)),
      ∀ a, ∃ (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
        (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
        IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
          ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
          (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
          (fun _ x => lf a x) (fun _ _ _ => 0) (fun _ x => u x) (fun _ x => w x) ∧
          (∀ x, PlaneTimeAllMomentRepresents (K x + 1) ϖ (ρs / ocEpsilon q Λ m) 0
              (volume.restrict (Set.Icc u0 u1)) (T x a) (w x)) ∧
            ∀ n x,
              ((⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
                (ρs / ocEpsilon q Λ m) (K x) (u x t)) +
                ∫⁻ t in Set.Icc u0 u1, weightedGradFactorialNormSq n ϖ 0
                  (ρs / ocEpsilon q Λ m) (K x) (w x t)) ≠ ⊤ ∧
              (∫⁻ t in Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
                (ρs / ocEpsilon q Λ m) (K x + 1) (w x t)) ≠ ⊤ := by
  apply windowCover_frozen_response_all_moment_linearMap hΛ hζ hφ cov K hK i
    u0 u1 hu hwindow hgsmall hg0 hlength ϖ hϖ lf (fun _ _ _ => 0)
  · intro x y v
    exact Filter.Eventually.of_forall (fun t => by simp only [add_zero])
  · intro c x v
    exact Filter.Eventually.of_forall (fun t => by simp only [smul_zero])
  · intro x v
    exact planeHk_zero_time_memLp (K v) (volume.restrict (Set.Icc u0 u1))
  · exact hf
  · intro x n v
    simp only [weightedFactorialNormSq_zero_carrier, lintegral_zero]
    exact ENNReal.zero_ne_top
end

/-! Component frozen responses act on the actual all-moment forcing domain, with zero initial data. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

local instance componentAllMomentFluxNormed :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E)) := componentCertificateFluxNormed
local instance componentAllMomentFluxInner :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E)) := componentCertificateFluxInner
local instance componentAllMomentFluxFinite :
    FiniteDimensional ℝ (PiLp 2 (fun _ : Fin 2 => E)) := inferInstance
local instance componentAllMomentFluxMeasurable :
    MeasurableSpace (PiLp 2 (fun _ : Fin 2 => E)) := inferInstance
local instance componentAllMomentFluxBorel :
    BorelSpace (PiLp 2 (fun _ : Fin 2 => E)) := inferInstance
local instance componentAllMomentFluxComplete :
    CompleteSpace (PiLp 2 (fun _ : Fin 2 => E)) := inferInstance
local instance componentAllMomentResponseNativeNormed (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k E) := allMomentTimeNativeNormed k
local instance componentAllMomentResponseLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpAdd k μ
local instance componentAllMomentResponseLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpModule k μ
local instance componentAllMomentResponseNativeAdd (k : ℕ) : AddCommGroup (PlaneHk Set.univ k E) :=
  inferInstance
local instance componentAllMomentResponseNativeModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  inferInstance
local instance componentAllMomentResponseFluxAdd (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance
local instance componentAllMomentResponseFluxModule (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E))) := allMomentTimeNativeModule k

local instance componentAllMomentDomainAdd (k : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) k ϖ ρ zc μ) :=
  inferInstance
local instance componentAllMomentDomainModule (k : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) k ϖ ρ zc μ) :=
  inferInstance

variable (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ℕ) (hK : K ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8)
    (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))

include hΛ hζ cov hK hu hwindow hgsmall hg0 hlength hϖ in
theorem windowCover_frozen_component_all_moment_response :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    let X := PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E))
      K ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1))
    ∃ T : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E)
      (K + 1) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)),
      IsPlaneComponentAllMomentResponse (E := E)
        (fun t => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0)
        (ocCellDrift α q Λ ζ m ν yc) K u0 u1 ϖ (ρs / ocEpsilon q Λ m) T := by
  classical
  let μ := volume.restrict (Set.Icc u0 u1)
  let X := PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E))
    K ϖ (ρs / ocEpsilon q Λ m) 0 μ
  let lf : X →ₗ[ℝ] (Unit → PlaneHk Set.univ K E) := 0
  let lF : X → Unit → ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) :=
    fun f _ t => planeTimeAllMomentCarrierToLp K ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1)) f t
  obtain ⟨T, hT⟩ := windowCover_frozen_response_all_moment_linearMap
    (h := fun _ : Unit => E) hΛ hζ hφ cov (fun _ => K) (fun _ => hK) i
    u0 u1 hu hwindow hgsmall hg0 hlength ϖ hϖ lf lF
    (fun f g _ => planeTimeAllMomentCarrier_add K ϖ _ 0 μ f g)
    (fun c f _ => planeTimeAllMomentCarrier_smul K ϖ _ 0 μ c f)
    (fun f _ => planeTimeAllMomentCarrier_memLp K ϖ _ 0 μ f)
    (fun _ _ _ => by
      change weightedFactorialNormSq _ _ _ _ K (0 : PlaneHk Set.univ K E) ≠ ⊤
      rw [weightedFactorialNormSq_zero_carrier]
      exact ENNReal.zero_ne_top)
    (fun f n _ => planeTimeAllMomentCarrier_moment K ϖ _ 0 μ f n)
  let T' : X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ
    (ρs / ocEpsilon q Λ m) 0 μ := T Unit.unit
  refine ⟨T', ?_⟩
  intro f
  obtain ⟨u, w, hs, heq, _⟩ := hT f
  refine ⟨lF f Unit.unit, u, w, hs, Filter.EventuallyEq.rfl, ?_⟩
  exact heq Unit.unit
end

/-! The homogeneous family carrier is a single linear map, with representing curves chosen for every datum. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

local instance coverHomogeneousFamilyLinearNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := inferInstance
local instance coverHomogeneousFamilyLinearLpAdd (i : ι) (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance coverHomogeneousFamilyLinearLpModule (i : ι) (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance coverHomogeneousFamilyLinearNativeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance coverHomogeneousFamilyLinearNativeModule (i : ι) (k : ℕ) : Module ℝ (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance coverHomogeneousFamilyLinearFluxAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance coverHomogeneousFamilyLinearFluxModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

theorem windowCover_frozen_homogeneous_family_linearMap (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 < u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8)
    (hg0 : g0 ≤ 1 / 4)
    (hlength : u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (ϖ : ℝ)
    (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (lf : X →ₗ[ℝ] (∀ x, PlaneHk Set.univ (K x) (h x)))
    (hf : ∀ a n x, weightedFactorialNormSq n ϖ 0
      (ρs / ocEpsilon q Λ m) (K x) (lf a x) ≠ ⊤)
 :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ Z : X →ₗ[ℝ] (∀ x, PlaneTimeAllMomentCarrier (E := h x)
      (K x + 1) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc u0 u1))),
      ∃ (u : X → ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
        (w : X → ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)), ∀ a,
        IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
          ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
          (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
          (fun _ x => lf a x) (fun _ _ _ => 0) (fun _ x => u a x) (fun _ x => w a x) ∧
          (∀ x, PlaneTimeAllMomentRepresents (K x + 1) ϖ (ρs / ocEpsilon q Λ m) 0
              (volume.restrict (Set.Icc u0 u1)) (Z a x) (w a x)) ∧
            ∀ n x,
              ((⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
                (ρs / ocEpsilon q Λ m) (K x) (u a x t)) +
                ∫⁻ t in Set.Icc u0 u1, weightedGradFactorialNormSq n ϖ 0
                  (ρs / ocEpsilon q Λ m) (K x) (w a x t)) ≠ ⊤ ∧
              (∫⁻ t in Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
                (ρs / ocEpsilon q Λ m) (K x + 1) (w a x t)) ≠ ⊤ := by
  classical
  obtain ⟨T, hT⟩ := windowCover_frozen_homogeneous_all_moment_linearMap
    hΛ hζ hφ cov K hK i u0 u1 hu hwindow hgsmall hg0 hlength ϖ hϖ lf hf
  choose u w hchain hrep henergy using hT
  exact ⟨LinearMap.pi T, u, w, fun a => ⟨hchain a, hrep a, henergy a⟩⟩
end

end AVRegularity.CycleJointProofs
end
end
