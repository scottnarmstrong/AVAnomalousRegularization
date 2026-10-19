-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneMetricActualTaylorRetainedMetricRemainderBudget
import AVRegularity.CycleJoint.PlaneMetricActualTaylorRetainedGradientGain
import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction
public import AVRegularity.CycleJoint.PlaneForcedZeroInitialEndpointEnergy
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
public import AVRegularity.Statements.Intermediate.CycleJoint.OcQuietTimes

section
@[expose] public noncomputable section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Genuine metric and original edge insertions assemble into the finite native response mass-gradient estimate. -/

theorem planeComponentAllMomentResponse_actualTaylor_three_residual_budgets_uniform
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r) :
    ∃ CT CR Cterminal : ℝ, 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧ ∀ {ι : Type*} [Fintype ι] {E : ι → Type*}
      [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
      [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
      [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)], ∀
    (a b : ℝ) (_hab : a ≤ b) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (_hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (_hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (_hV : 0 ≤ V) (_ha : 0 ≤ strain) (_hB : 1 ≤ B) (_hlam : 0 < lam)
    (_hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (_hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (_hMm : Measurable M)
    (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
    (_hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (_hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (t₀ S ϖ : ℝ) (N : ℕ) (Cw : ℕ → ℝ)
    (_C : ChartWeights (fun t _ => M t) v t₀ S ϖ 0 N Cw)
    (ρ L : ℝ) (_hρ : 0 < ρ) (_hL : 1 ≤ L)
    (_hsmall : B * ρ / lam ≤ 1 / 2)
    (_hstrainSmall : strain * B * ρ ^ 2 ≤ 1 / 8)
    (_hreserve : ∀ n ≤ N, Real.exp (18 * Cw n) / L ^ 2 ≤ 1 / 16)
    (_hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (_hwa : t₀ ≤ a) (_hwb : b ≤ t₀ + S)
    (π : ι → ℝ) (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)))
    (_hR : ∀ i, IsPlaneComponentAllMomentResponse (E := E i) M v (K i) a b ϖ ρ (R i))
    (_hπ : ∀ i, 0 < π i)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (δ ζ gm : ℝ)
    (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
    (_hGs : ∀ t ∈ Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l))
    (_hϖ : 0 < ϖ) (_hscale : ρ * ϖ ≤ 1) (_hζ : 0 ≤ ζ) (_hζ1 : ζ ≤ 1)
    (_hgm : 0 ≤ gm) (_hδ : δ = ζ * ϖ)
    (_hGjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ Cjet r * gm * δ ^ r)
    (T : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Icc a b)))
    (_hT : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Icc a b))
      (fun x t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0
          (volume.restrict (Icc a b)) x t)) (T i))
    (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => E j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E i))
    (_hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (_hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (Tsource : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (_hTsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun W t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (E := E j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W j) t) i) (Tsource i))
    (Cprep Cgraph θ : ℝ)
    (_hθ : 0 ≤ θ)
    (_hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ Cprep * θ)
    (_hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ Cprep * θ)
    (Remainder : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (_hrem : ∀ W k, planeAllMomentFamilyEnergy K k ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => Remainder i W) ≤ ENNReal.ofReal ((ζ ^ (Ks + 1) * (Cgraph * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K (k + (Ks + 1)) ϖ ρ (volume.restrict (Icc a b)) π W)
    (_hGhigh : ∀ t ∈ Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
    (_hGhighjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ r, Ks + 1 ≤ r → r ≤ Ks + 1 + Kmax → ∀ y k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ Cjet r * gm * (ζ * ϖ) ^ r)
    (Rm : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Icc a b)))
    (_hRm : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Icc a b))
      (fun x t => planeMatrixGradientFlux
        (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)) x t)) (Rm i))
    (_hgain : ENNReal.ofReal (CT * gm * ζ) ≤ 1)
    (Z : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b))) (n J H : ℕ) (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N),
    let Cg := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
    let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
      finiteResponse 1 (nativeDiagonalResponseOperator R T)
        (nativeComponentResponseOperator R (fun i => Tsource i - Remainder i)) Z j k
    (planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π (fun i => Rm i (Wret i)) ≤
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * gm * ζ ^ (Ks + 1)) ^ 2) *
        retainedResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
      planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z) ∧
    (planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π (fun i => Remainder i Wret) ≤
      (ENNReal.ofReal ((ζ ^ (Ks + 1) * (Cgraph * θ)) ^ 2) *
        retainedResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
      planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z) ∧
    (planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => T i ((∑ k ∈ Finset.range (H + 1), finiteResponse 1
        (nativeDiagonalResponseOperator R T)
        (nativeComponentResponseOperator R (fun v => Tsource v - Remainder v)) Z J k) i)) ≤
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax) *
        terminalResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
        (ENNReal.ofReal (Cterminal * gm * ζ)) ^ (2 * (J + 1)) *
        planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z) := by
  obtain ⟨CTm, CR, hCTm, hCR, hm⟩ :=
    planeComponentAllMomentResponse_metric_actualTaylor_retained_metric_remainder_budget_uniform
      Ks Kmax Cjet hCjet
  obtain ⟨CTs, hCTs, hs⟩ :=
    planeComponentAllMomentResponse_metric_actualTaylor_retained_source_remainder_budget_uniform
      Ks Kmax Cjet hCjet
  obtain ⟨CTt, hCTt, ht⟩ :=
    planeComponentAllMomentResponse_metric_actualTaylor_terminal_forcing_gain_uniform
      Ks Kmax Cjet hCjet
  refine ⟨max CTm CTs, CR, CTt, hCTm.trans (le_max_left _ _), hCR, hCTt, ?_⟩
  intro ι _ E _ _ _ _ _ _ a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem
    hGhigh hGhighjet Rm hRm hgain Z n J H hN
  have hgmζ : 0 ≤ gm * ζ := mul_nonneg hgm hζ
  have hgmul (c : ℝ) (hc : c ≤ max CTm CTs) :
      ENNReal.ofReal (c * gm * ζ) ≤ 1 := by
    apply le_trans _ hgain
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hgmζ
  refine ⟨?_, ?_, ?_⟩
  · exact hm (E := E) a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
      M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
      hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
      T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem
      hGhigh hGhighjet Rm hRm (hgmul CTm (le_max_left _ _)) Z n J H hN
  · exact hs (E := E) a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
      M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
      hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
      T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem
      (hgmul CTs (le_max_right _ _)) Z n J H hN
  · exact ht (E := E) a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
      M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
      hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
      T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem Z n J H hN

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual coupled native map has the central, positive metric, original source, and two remainder decomposition consumed by the constructed error. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance coverMetricSourceConstructionNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance coverMetricSourceConstructionModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

local instance coverMetricSourceConstructionFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance coverMetricSourceConstructionFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance coverMetricSourceConstructionFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance coverMetricSourceConstructionFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

def windowCoverCellMetric (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (l₀ : ℤ) (P : ℕ) (ν : ℝ) (y₀ : Vec 2)
    (i : Fin (P + 2)) : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ocCellMetric α q Λ m φ hφ (l₀ - 1 + i) ν
    (windowCoverChartCentre α q Λ m φ hφ l₀ P y₀ i)

theorem windowCover_exists_metric_source_originalEdge_allMoment_maps
    {α q : ℝ} {Λ m : ℕ} {ζfast : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (hΛ : 1 ≤ Λ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζfast Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (Ks : ℕ) (hqJ : Ks + 1 + Kmax ≤ qJ) (K : ι → ℕ) (hK : ∀ j, K j ≤ Kmax)
    (ic : Fin (P + 2)) (a b : ℝ)
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P ic)
    (ϖ : ℝ) (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (D : ℕ) (hD : 2 ≤ D)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b)))
    (Rs : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b)))
    (hsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ (ρs / ocEpsilon q Λ m) 0
          (volume.restrict (Set.Icc a b)) (X j) t) i) (nativeFamilyEdgeForcingMap Ledge i + Rs i)) :
    ∃ diag positive Rm : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b)),
    ((∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux (fun _ => (windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic) t 0 - 1)
          (planeTimeAllMomentCarrierToLp (K i + 1) ϖ (ρs / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) x t)) (diag i)) ∧
      (∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => (windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic) t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K i + 1) ϖ (ρs / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) x t)) (positive i)) ∧
      (∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => (windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic) t z k l - taylorSlow 0 Ks (fun y => (windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic) t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K i + 1) ϖ (ρs / ocEpsilon q Λ m) 0
            (volume.restrict (Set.Icc a b)) x t)) (Rm i))) ∧
    ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeRawCouplingFlux K D t (planeMetricSourceCoefficient K D (windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic) A)
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ (ρs / ocEpsilon q Λ m) 0 (volume.restrict (Set.Icc a b)) (X j) t) i)
      ((diag i).comp (LinearMap.proj i) + (positive i).comp (LinearMap.proj i) +
        nativeFamilyEdgeForcingMap Ledge i +
        (Rm i).comp (LinearMap.proj i) + Rs i) := by
  let e := ocEpsilon q Λ m
  let E := ocEpsilon q Λ (m - 1)
  let R := Real.sqrt (B * ocTauPP α q Λ m)
  let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
  have he : 0 < e := Construction.Stream.ocEpsilon_pos hΛ
  have hE : 0 < E := Construction.Stream.ocEpsilon_pos hΛ
  have hT : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos hΛ
  have hR : 0 < R := Real.sqrt_pos.mpr (mul_pos cov.pos.2.1 hT)
  have hϖpos : 0 < ϖ := by rw [hϖ]; exact div_pos he hR
  have hscale : (ρs / e) * ϖ ≤ 1 := by
    rw [hϖ, div_mul_div_cancel₀ he.ne']
    exact (div_le_one hR).mpr cov.rho_R
  have hδ : e / E = (R / E) * ϖ := by
    rw [hϖ, div_mul_div_cancel₀' hR.ne']
  have hjets (t : ℝ) (ht : t ∈ Set.Icc a b) (r : ℕ) (hr : 1 ≤ r) (hrq : r ≤ qJ)
      (x : Vec 2) (k l : Fin 2) :
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) x‖ ≤ max (CG r) 0 * g * ((R / E) * ϖ) ^ r := by
    rw [← hδ]
    exact (cov.metric_jets ic t (hwindow ht) x r hr hrq k l).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left (CG r) 0) cov.g_range.1)
        (pow_nonneg (div_nonneg he.le hE.le) r))
  apply exists_planeMetricSource_originalEdge_allMoment_maps Ks Kmax (fun r => max (CG r) 0)
    (fun r => le_max_right (CG r) 0) K hK G a b ϖ (ρs / e) (R / E) g
    (fun X k l => cellMetric_time_slice_measurable α q Λ m hφ (l₀ - 1 + ic) ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic) X k l)
    (fun t ht k l => (cov.metric_smooth ic t (hwindow ht) k l).of_le (by exact_mod_cast hqJ))
    hϖpos (div_pos cov.pos.2.2 he) hscale (div_nonneg hR.le hE.le)
    ((div_le_one hE).mpr cov.RE) cov.g_range.1
    (fun t _ => ocCellMetric_symmetric α q Λ m hφ (l₀ - 1 + ic) ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic) t 0)
    (fun t ht ξ => cov.metric_near ic t (hwindow ht) 0 ξ) _ _ D hD A Ledge Rs hsource
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro r hr hrKs k l
    exact hjets t ht r hr (by omega) 0 k l
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro r hr hrmax x k l
    exact hjets t ht r (by omega) (hrmax.trans hqJ) x k l

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! The initial partial block and following full block use actual covered charts
one and two, with all metric premises confined to their certified windows. -/

def windowCoverFollowingChartIndex (P : ℕ) (hP : 1 ≤ P) : Fin (P + 2) := ⟨2, by omega⟩

theorem windowCoverFollowingChartIndex_label (l₀ : ℤ) (P : ℕ) (hP : 1 ≤ P) :
    l₀ - 1 + (windowCoverFollowingChartIndex P hP : ℤ) = l₀ + 1 := by
  simp only [windowCoverFollowingChartIndex, Fin.val_mk, Nat.cast_ofNat]
  ring

theorem windowCover_two_block_geometry
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {ν B tS ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (hΛ : 1 ≤ Λ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + 2 * ocTauPP α q Λ m)
      ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀) :
    let T := ocTauPP α q Λ m
    let scale := ocEll q Λ m ν ^ 2
    let seam := ((l₀ : ℝ) + 1 / 2) * T
    let tp := ((l₀ : ℝ) + 3 / 2) * T
    tp ∈ Set.Ioc tS (tS + 2 * T) ∧ tp ∈ ocQuietTimes α q Λ ζ m ∧
    ((l₀ : ℝ) + 1) * T ∈ Set.Icc tS (tS + 2 * T) ∧
    tS < seam ∧ seam < tp ∧
    Set.Icc (tS / scale) (seam / scale) ⊆
      windowCoverChartWindow α q Λ m ν tS (tS + 2 * T) l₀ P (windowCoverReferenceChartIndex P) ∧
    Set.Icc (seam / scale) (tp / scale) ⊆
      windowCoverChartWindow α q Λ m ν tS (tS + 2 * T) l₀ P
        (windowCoverFollowingChartIndex P cov.P_pos) := by
  dsimp only
  let T := ocTauPP α q Λ m
  let scale := ocEll q Λ m ν ^ 2
  have hT : 0 < T := Construction.Stream.ocTauPP_pos hΛ
  have he : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hscale : 0 < scale := by
    rw [show scale = ocEpsilon q Λ m ^ 2 / ν from CycleReference.ocEll_sq_eq cov.pos.1]
    exact div_pos (sq_pos_of_pos he) cov.pos.1
  obtain ⟨hseam, hseamT, htpT, htp, hσ, hfirst, hsecond⟩ :=
    preparation_two_block_time_geometry tS (l₀ : ℝ) T hT cov.window.1 cov.window.2.1
  have hq := renewal_boundary_quiet_margin (α := α) (q := q) (m := m) hΛ ζ (l₀ + 1)
  have hq' : ((l₀ : ℝ) + 3 / 2) * T ∈ ocQuietTimes α q Λ ζ m := by
    apply hq
    have hpad : 0 ≤ ocTauP α q Λ m := by
      unfold ocTauP
      exact div_nonneg hT.le (Nat.cast_nonneg _)
    push_cast
    constructor <;> linarith only [hpad]
  refine ⟨⟨by linarith only [htpT, hT], htp⟩, hq', hσ, hseam,
    by linarith only [hT], ?_, ?_⟩
  · have hh := positive_time_scaled_interval_inclusion _ _ _ _ scale hscale hfirst
    simpa only [windowCoverChartWindow, windowCoverReferenceChartIndex_label] using hh
  · have hh := positive_time_scaled_interval_inclusion _ _ _ _ scale hscale hsecond
    simpa only [windowCoverChartWindow, windowCoverFollowingChartIndex_label,
      Int.cast_add, Int.cast_one, add_sub_cancel_right, add_assoc, one_add_one_eq_two] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Genuine metric and original edge insertions assemble into the finite native response mass-gradient estimate. -/

theorem planeComponentAllMomentResponse_actualTaylor_normalized_three_residual_budgets_uniform
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r) :
    ∃ CT CR Cterminal : ℝ, 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧ ∀ {ι : Type*} [Fintype ι] {E : ι → Type*}
      [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
      [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
      [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)], ∀
    (a b : ℝ) (_hab : a ≤ b) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (_hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (_hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (_hV : 0 ≤ V) (_ha : 0 ≤ strain) (_hB : 1 ≤ B) (_hlam : 0 < lam)
    (_hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (_hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (_hMm : Measurable M)
    (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
    (_hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (_hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (t₀ S ϖ : ℝ) (N : ℕ) (Cw : ℕ → ℝ)
    (_C : ChartWeights (fun t _ => M t) v t₀ S ϖ 0 N Cw)
    (ρ L : ℝ) (_hρ : 0 < ρ) (_hL : 1 ≤ L)
    (_hsmall : B * ρ / lam ≤ 1 / 2)
    (_hstrainSmall : strain * B * ρ ^ 2 ≤ 1 / 8)
    (_hreserve : ∀ n ≤ N, Real.exp (18 * Cw n) / L ^ 2 ≤ 1 / 16)
    (_hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (_hwa : t₀ ≤ a) (_hwb : b ≤ t₀ + S)
    (π : ι → ℝ) (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)))
    (_hR : ∀ i, IsPlaneComponentAllMomentResponse (E := E i) M v (K i) a b ϖ ρ (R i))
    (_hπ : ∀ i, 0 < π i)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (δ ζ gm : ℝ)
    (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
    (_hGs : ∀ t ∈ Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l))
    (_hϖ : 0 < ϖ) (_hscale : ρ * ϖ ≤ 1) (_hζ : 0 ≤ ζ) (_hζ1 : ζ ≤ 1)
    (_hgm : 0 ≤ gm) (_hδ : δ = ζ * ϖ)
    (_hGjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ Cjet r * gm * δ ^ r)
    (T : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Icc a b)))
    (_hT : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Icc a b))
      (fun x t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0
          (volume.restrict (Icc a b)) x t)) (T i))
    (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => E j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E i))
    (_hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (_hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (Tsource : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (_hTsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun W t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (E := E j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W j) t) i) (Tsource i))
    (Cprep Cgraph θ : ℝ)
    (_hθ : 0 ≤ θ)
    (_hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ Cprep * θ)
    (_hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ Cprep * θ)
    (Remainder : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (_hrem : ∀ W k, planeAllMomentFamilyEnergy K k ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => Remainder i W) ≤ ENNReal.ofReal ((ζ ^ (Ks + 1) * (Cgraph * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K (k + (Ks + 1)) ϖ ρ (volume.restrict (Icc a b)) π W)
    (_hGhigh : ∀ t ∈ Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
    (_hGhighjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ r, Ks + 1 ≤ r → r ≤ Ks + 1 + Kmax → ∀ y k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ Cjet r * gm * (ζ * ϖ) ^ r)
    (Rm : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Icc a b)))
    (_hRm : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Icc a b))
      (fun x t => planeMatrixGradientFlux
        (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)) x t)) (Rm i))
    (_hgain : ENNReal.ofReal (CT * gm * ζ) ≤ 1)
    (Z : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b))) (n J H : ℕ) (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N),
    let Cg := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
    let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
      finiteResponse 1 (nativeDiagonalResponseOperator R T)
        (nativeComponentResponseOperator R (fun i => Tsource i - Remainder i)) Z j k
    (planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π (fun i => Rm i (Wret i)) ≤
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * gm) ^ 2) *
        ENNReal.ofReal ζ ^ (2 * (Ks + 1)) *
        retainedResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
      planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z) ∧
    (planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π (fun i => Remainder i Wret) ≤
      (ENNReal.ofReal ((Cgraph * θ) ^ 2) * ENNReal.ofReal ζ ^ (2 * (Ks + 1)) *
        retainedResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
      planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z) ∧
    (planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => T i ((∑ k ∈ Finset.range (H + 1), finiteResponse 1
        (nativeDiagonalResponseOperator R T)
        (nativeComponentResponseOperator R (fun v => Tsource v - Remainder v)) Z J k) i)) ≤
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax) *
        terminalResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
        (ENNReal.ofReal (Cterminal * gm * ζ)) ^ (2 * (J + 1)) *
        planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z) := by
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hbound⟩ :=
    planeComponentAllMomentResponse_actualTaylor_three_residual_budgets_uniform
      Ks Kmax Cjet hCjet
  refine ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, ?_⟩
  intro ι _ E _ _ _ _ _ _ a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem
    hGhigh hGhighjet Rm hRm hgain Z n J H hN
  obtain ⟨hm, hs, ht⟩ := hbound (E := E) a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem
    hGhigh hGhighjet Rm hRm hgain Z n J H hN
  rw [residual_squared_power_factorization _ _ _
    (metricTaylorUniformDensityPrice_nonneg Kmax) hζ (Ks + 1)] at hm
  rw [source_remainder_squared_power_factorization _ _ hζ (Ks + 1)] at hs
  exact ⟨hm, hs, ht⟩

/-! Genuine metric and original edge insertions assemble into the finite native response mass-gradient estimate. -/

theorem planeComponentAllMomentResponse_actualTaylor_originalEdge_three_residual_budgets_uniform
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r) :
    ∃ CT CR Cterminal : ℝ, 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧ ∀ {ι : Type*} [Fintype ι] {E : ι → Type*}
      [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
      [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
      [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)], ∀
    (a b : ℝ) (_hab : a ≤ b) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (_hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (_hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (_hV : 0 ≤ V) (_ha : 0 ≤ strain) (_hB : 1 ≤ B) (_hlam : 0 < lam)
    (_hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (_hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (_hMm : Measurable M)
    (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
    (_hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (_hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (t₀ S ϖ : ℝ) (N : ℕ) (Cw : ℕ → ℝ)
    (_C : ChartWeights (fun t _ => M t) v t₀ S ϖ 0 N Cw)
    (ρ L : ℝ) (_hρ : 0 < ρ) (_hL : 1 ≤ L)
    (_hsmall : B * ρ / lam ≤ 1 / 2)
    (_hstrainSmall : strain * B * ρ ^ 2 ≤ 1 / 8)
    (_hreserve : ∀ n ≤ N, Real.exp (18 * Cw n) / L ^ 2 ≤ 1 / 16)
    (_hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (_hwa : t₀ ≤ a) (_hwb : b ≤ t₀ + S)
    (π : ι → ℝ) (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)))
    (_hR : ∀ i, IsPlaneComponentAllMomentResponse (E := E i) M v (K i) a b ϖ ρ (R i))
    (_hπ : ∀ i, 0 < π i)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (δ ζ gm : ℝ)
    (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
    (_hGs : ∀ t ∈ Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l))
    (_hϖ : 0 < ϖ) (_hscale : ρ * ϖ ≤ 1) (_hζ : 0 ≤ ζ) (_hζ1 : ζ ≤ 1)
    (_hgm : 0 ≤ gm) (_hδ : δ = ζ * ϖ)
    (_hGjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ Cjet r * gm * δ ^ r)
    (T : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Icc a b)))
    (_hT : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Icc a b))
      (fun x t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0
          (volume.restrict (Icc a b)) x t)) (T i))
    (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => E j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E i))
    (_hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (_hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (Cprep Cgraph θ : ℝ)
    (_hθ : 0 ≤ θ)
    (_hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ Cprep * θ)
    (_hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ Cprep * θ)
    (Remainder : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (_hrem : ∀ W k, planeAllMomentFamilyEnergy K k ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => Remainder i W) ≤ ENNReal.ofReal ((ζ ^ (Ks + 1) * (Cgraph * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K (k + (Ks + 1)) ϖ ρ (volume.restrict (Icc a b)) π W)
    (_hsourceRaw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun W t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (E := E j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W j) t) i)
      (nativeFamilyEdgeForcingMap Ledge i + Remainder i))
    (_hGhigh : ∀ t ∈ Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
    (_hGhighjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ r, Ks + 1 ≤ r → r ≤ Ks + 1 + Kmax → ∀ y k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ Cjet r * gm * (ζ * ϖ) ^ r)
    (Rm : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Icc a b)))
    (_hRm : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Icc a b))
      (fun x t => planeMatrixGradientFlux
        (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)) x t)) (Rm i))
    (_hgain : ENNReal.ofReal (CT * gm * ζ) ≤ 1)
    (Z : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b))) (n J H : ℕ) (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N),
    let Cg := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
    let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
      finiteResponse 1 (nativeDiagonalResponseOperator R T)
        (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z j k
    (planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π (fun i => Rm i (Wret i)) ≤
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * gm) ^ 2) *
        ENNReal.ofReal ζ ^ (2 * (Ks + 1)) *
        retainedResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
      planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z) ∧
    (planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π (fun i => Remainder i Wret) ≤
      (ENNReal.ofReal ((Cgraph * θ) ^ 2) * ENNReal.ofReal ζ ^ (2 * (Ks + 1)) *
        retainedResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
      planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z) ∧
    (planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => T i ((∑ k ∈ Finset.range (H + 1), finiteResponse 1
        (nativeDiagonalResponseOperator R T)
        (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z J k) i)) ≤
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax) *
        terminalResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
        (ENNReal.ofReal (Cterminal * gm * ζ)) ^ (2 * (J + 1)) *
        planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z) := by
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hbound⟩ :=
    planeComponentAllMomentResponse_actualTaylor_normalized_three_residual_budgets_uniform
      Ks Kmax Cjet hCjet
  refine ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, ?_⟩
  intro ι _ E _ _ _ _ _ _ a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Ledge Cprep Cgraph θ hθ hrow hcol Remainder hrem
    hsourceRaw hGhigh hGhighjet Rm hRm hgain Z n J H hN
  simpa only [add_sub_cancel_right] using hbound (E := E)
    a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC (fun i => nativeFamilyEdgeForcingMap Ledge i + Remainder i) hsourceRaw
    Cprep Cgraph θ hθ hrow hcol Remainder hrem
    hGhigh hGhighjet Rm hRm hgain Z n J H hN

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Actual native metrics supply joint measurability and all reserved jets on
their certified windows, with a nonnegative reserve constant. -/

theorem windowCover_native_metric_data
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (hΛ : 1 ≤ Λ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (ic : Fin (P + 2)) (a b : ℝ)
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P ic) :
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    IsMetricNearIdentityOn (Set.Icc a b) G g ∧
    Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2) ∧
    (∀ z r c, Measurable (fun t => G t z r c)) ∧
    (∀ t z, (G t z).IsSymm) ∧
    (∀ t ∈ Set.Icc a b, ∀ r c, ContDiff ℝ (qJ : ℕ) (fun z => G t z r c)) ∧
    (∀ t ∈ Set.Icc a b, ∀ z j, 1 ≤ j → j ≤ qJ → ∀ r c,
      ‖iteratedFDeriv ℝ j (fun x => G t x r c) z‖ ≤
        max (CG j) 0 * g * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ j) := by
  dsimp only
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
  have he := Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hE := Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  refine ⟨fun t ht z ξ => cov.metric_near ic t (hwindow ht) z ξ, ?_,
    cellMetric_time_slice_measurable α q Λ m hφ (l₀ - 1 + ic) ν yc,
    fun t z => ocCellMetric_symmetric α q Λ m hφ (l₀ - 1 + ic) ν yc t z,
    fun t ht r c => cov.metric_smooth ic t (hwindow ht) r c, ?_⟩
  · exact matrixTimeWindow_measurable
      (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + ic) ν yc)
      (cellMetric_joint_measurable α q Λ m hφ (l₀ - 1 + ic) ν yc) a b
  · intro t ht z j hj hjq r c
    exact (cov.metric_jets ic t (hwindow ht) z j hj hjq r c).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left (CG j) 0) cov.g_range.1)
        (pow_nonneg (div_nonneg he.le hE.le) j))

end AVRegularity.CycleJointProofs
end
end

section
/-! Subtracting the constructed original remainder from the actual native
source map gives precisely the natural Taylor source, with an exact map split. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CoupledEnergyPlane.Variational

namespace AVRegularity.CycleJointProofs

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem exists_preparationWindowReferenceCellSourceMap_natural_split
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
    (htime : ∀ τ ∈ Set.Icc a b, ν⁻¹ * (e ^ 2 * τ) ∈ Set.Icc tS tZ)
    (T : ∀ v u, F.Γ v u → Fin D → (F.locally_finite tS tZ).toFinset →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)))
    (hT : ∀ v u γ j p, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))
      (fun x τ z => naturalFamilyRemainderNativeArray Ks F p.val (actual p.val) v u γ
        (ν⁻¹ * e ^ 2) a b hφ (F.piece p.val).anchor σ e (ocEpsilon q Λ (m - 1)) yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
            (volume.restrict (Set.Icc a b)) x τ) (j.val + 1) I z))) (T v u γ j p)) :
    ∃ Lfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
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
      (Lfull v - Rs v) ∧ Lfull v = (Lfull v - Rs v) + Rs v := by
  have he : 0 < e := hρ.trans_le hρe
  have hr : 0 < ρ / e := div_pos hρ he
  obtain ⟨Lfull, hfull⟩ := preparationWindowReferenceCellSource_allMoment_map_of_pointwise F hc hcover σ hσ ν e ρ
    hν hρ hρe heE K Kmax Jm hK hchart hmol Cm hmeas hwmeas actual yc π hπ B hB henv
    a b ϖ (ρ / e) hab hr hsub
  refine ⟨Lfull, hfull, ?_⟩
  exact preparationReferenceCellSourceMap_natural_split F hc ν e (ocEpsilon q Λ (m - 1))
    hν.ne' he actual K hdesc Ks σ yc a b ϖ (ρ / e)
    htime Lfull hfull T hT

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The actual chart centre supplies the frozen diagonal coefficient reserves
on the certified window, at every admissible edge order. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem windowCover_frozen_metric_order_data
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (ic : Fin (P + 2)) (a b : ℝ)
    (hwindow : Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P ic)
    (K : ι → ℕ) (D : ℕ) (rstar : ℝ) :
    let M := fun t => windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic t 0
    (∀ i j d, coefficientSeminorm rstar (K i) a b
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) i j d) ≠ ⊤) ∧
    (∀ i j d t, ContDiff ℝ (K i : ℕ)
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) i j d t)) := by
  dsimp only
  let M := fun t => windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic t 0
  have hsym (t : ℝ) (_ht : t ∈ Set.Icc a b) : (M t).IsSymm :=
    ocCellMetric_symmetric α q Λ m hφ (l₀ - 1 + ic) ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic) t 0
  refine ⟨?_, fun i j d t => frozenMetric_order_coefficient_contDiff K D M i j d t⟩
  intro i j d
  exact frozenMetric_order_coefficients_finite K D M rstar a b g cov.g_range.1 hsym
    (fun t ht ξ => cov.metric_near ic t (hwindow ht) 0 ξ) i j d

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The constructed finite response approximates the genuine homogeneous coupled preparation with the three original-mass residual budgets. -/

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance literalEndpointNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance literalEndpointNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance literalEndpointFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance literalEndpointFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem planeRetained_literal_constructed_error_endpoint_energy
    (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D H Ks : ℕ) (Bsrc : ℝ) :
      ∀ (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ (0 : Vec 2) n Cw)
        (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
        (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
        (_hr1 : rstar ≤ 1)
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
    {P : Type*} {Ctx : P → Type*}
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
        (fun j => planeTimeAllMomentCarrierToLp (E := h j) (Kslot j + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) (X j) t) i) (Lfull i))
    (_hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t => planeRawCouplingFlux Kslot D t
        (planeDiagonalGradientCoefficient (h := h) Kslot D (fun _ t _ => M t - 1))
        (fun j => planeTimeAllMomentCarrierToLp (E := h j) (Kslot j + 1) ϖ rstar 0
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
            (fun j => planeTimeAllMomentCarrierToLp (Kslot j + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) (X j) t) i)
          (nativeFamilyEdgeForcingMap Ledge i + Rs i))
        (_hDiagComponent : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun _ => M t - 1)
            (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (diag i))
        (_hPositive : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Lmetric i))
        (_hMetricRemainder : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux
            (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Rmetric i)),
        let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
          (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
        let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U j k
        let Tret := ∑ k ∈ Finset.range (H + 1), U J k
        let Q := fun i => Lmetric i (Wret i) + nativeFamilyEdgeForcingMap Ledge i Wret - Lmetric i (Tret i)
        ∀ Bm Bs Bt : ℝ≥0∞,
        planeAllMomentFamilyEnergy Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π (fun i => Rmetric i (Wret i)) ≤ Bm →
        planeAllMomentFamilyEnergy Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π (fun i => Rs i Wret) ≤ Bs →
        planeAllMomentFamilyEnergy Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π (fun i => Lmetric i (Tret i)) ≤ Bt →
        ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i)))
          (u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i)),
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A) (fun _ => 0)
            (fun i t => -(F i t - planeCouplingFluxRow _ht rstar _hrstar Kslot D
              (planeMetricSourceCoefficient Kslot D G A) _hfullA _hfullC w i t +
              planeCouplingFluxRow _ht rstar _hrstar Kslot D
                (planeDiagonalGradientCoefficient Kslot D (fun _ t _ => M t - 1)) _hdiagA _hdiagC w i t))
            (fun _ _ => 0) (fun i t => uH i t - u i t) (fun i t => wH i t - w i t) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Q i) (F i)) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Wret i) (w i)) ∧
          ∀ tp, tp ∈ Set.Icc ta tb →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (uH i tp - u i tp)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax CG Cw D Bsrc) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) * (Bm + Bs + Bt)) := by
  intro π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ htw htb W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC
    P Ctx family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder
  classical
  have hS := nativeRawOriginalFamilyMap_response_sourceDegree family Kslot ϖ rstar 0
    (volume.restrict (Set.Icc ta tb)) Hraw hHzero (nativeFamilyEdgeForcingMap Ledge) hTaylorRaw R
  have hDiagG i : IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))
      (fun X t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
        (planeTimeAllMomentCarrierToLp (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) X t)) (diag i) := by
    simpa only [hMcenter] using hDiagComponent i
  have hLdiagG := hdiag
  rw [hMcenter] at hLdiagG
  have hspl := planeMetricSource_fiveTerm_allMoment_map_identification Kslot Ks D hD ϖ rstar
    (volume.restrict (Set.Icc ta tb)) G A
    (fun i => nativeFamilyEdgeForcingMap Ledge i + Rs i) Rs diag Lmetric Rmetric
    hSourceRaw hDiagG hPositive hMetricRemainder Lfull Ldiag hfull hLdiagG
  let Rm : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (Kslot j + 1) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
        (volume.restrict (Set.Icc ta tb)) := fun i => (Rmetric i).comp (LinearMap.proj i)
  have hsplit i : Lfull i = Ldiag i + (Lmetric i).comp (LinearMap.proj i) +
      nativeFamilyEdgeForcingMap Ledge i + Rm i + Rs i := by
    have hh := hspl i
    rw [nativeFamilyMapEdge_add_sub_assembly] at hh
    exact hh
  exact planeRetained_constructed_error_endpoint_energy n Kmax CG Cw D H Bsrc
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ htw htb W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC family J hdepth hS hR hbase hZ
    Lfull Ldiag hfull hdiag Rm Rs hsplit

end AVRegularity.CycleJointProofs
end
end
