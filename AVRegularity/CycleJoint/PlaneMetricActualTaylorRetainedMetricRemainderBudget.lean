-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneMetricActualTaylorRetainedGradientGain
import AVRegularity.CycleJoint.OriginalFamilyNaturalRemainderDescendingIdentity
import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction
public import AVRegularity.CycleJoint.PlanePolynomialJetMultiplierDensity
import AVenhance.Infra.Classical.Drift

section
@[expose] public noncomputable section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Genuine metric and original edge insertions assemble into the finite native response mass-gradient estimate. -/

theorem planeComponentAllMomentResponse_metric_actualTaylor_retained_source_remainder_budget_uniform
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ {ι : Type*} [Fintype ι] {E : ι → Type*}
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
    (_hgain : ENNReal.ofReal (CT * gm * ζ) ≤ 1)
    (Z : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b))) (n J H : ℕ) (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N),
    let Cg := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
    let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
      finiteResponse 1 (nativeDiagonalResponseOperator R T)
        (nativeComponentResponseOperator R (fun i => Tsource i - Remainder i)) Z j k
    planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π (fun i => Remainder i Wret) ≤
      (ENNReal.ofReal ((ζ ^ (Ks + 1) * (Cgraph * θ)) ^ 2) *
        retainedResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
      planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z := by
  obtain ⟨CT, hCT, hgainRet⟩ := planeComponentAllMomentResponse_metric_actualTaylor_retained_gradient_gain_uniform
    Ks Kmax Cjet hCjet
  refine ⟨CT, hCT, ?_⟩
  intro ι _ E _ _ _ _ _ _ a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem hgain Z n J H hN
  dsimp only
  let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
    finiteResponse 1 (nativeDiagonalResponseOperator R T)
      (nativeComponentResponseOperator R (fun i => Tsource i - Remainder i)) Z j k
  have he := hrem Wret n
  have hgret := hgainRet (E := E) a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem hgain Z
    (n + (Ks + 1)) J H hN
  simpa only [Wret, mul_assoc] using he.trans (mul_le_mul_of_nonneg_left hgret zero_le)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual coupled native map has the central, positive metric, original source, and two remainder decomposition consumed by the constructed error. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance fullMetricSourceConstructionNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance fullMetricSourceConstructionModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

local instance fullMetricSourceConstructionFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance fullMetricSourceConstructionFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance fullMetricSourceConstructionFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance fullMetricSourceConstructionFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem exists_planeMetricSource_originalEdge_allMoment_maps
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r)
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Kmax)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ ζ g : ℝ)
    (hm : ∀ X k l, Measurable (fun t => G t X k l))
    (hf : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
    (hϖ : 0 < ϖ) (hρ : 0 < ρ) (hscale : ρ * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hg : 0 ≤ g)
    (hsym : ∀ t ∈ Set.Icc a b, (G t 0).IsSymm)
    (hnear : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (G t 0 - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2)
    (hlow : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ Cjet r * g * (ζ * ϖ) ^ r)
    (hhigh : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, Ks + 1 ≤ r →
      r ≤ Ks + 1 + Kmax → ∀ y k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ Cjet r * g * (ζ * ϖ) ^ r)
    (D : ℕ) (hD : 2 ≤ D)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (Rs : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (hsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (X j) t) i) (nativeFamilyEdgeForcingMap Ledge i + Rs i)) :
    ∃ diag positive Rm : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)),
    ((∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
          (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) (diag i)) ∧
      (∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) (positive i)) ∧
      (∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) (Rm i))) ∧
    ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => planeRawCouplingFlux K D t (planeMetricSourceCoefficient K D G A)
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (X j) t) i)
      ((diag i).comp (LinearMap.proj i) + (positive i).comp (LinearMap.proj i) +
        nativeFamilyEdgeForcingMap Ledge i +
        (Rm i).comp (LinearMap.proj i) + Rs i) := by
  classical
  have hmapi (i : ι) := exists_metricTaylor_remainder_allMoment_maps (E := h i)
    Ks Kmax Cjet hCjet (K i) (hK i) G a b ϖ ρ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hsym hnear hlow hhigh
  choose diag positive Rm hdiag hpositive hRm using hmapi
  refine ⟨diag, positive, Rm, ⟨hdiag, hpositive, hRm⟩, ?_⟩
  exact planeMetricSource_originalEdge_allMoment_map_construction K Ks D hD ϖ ρ
    (volume.restrict (Set.Icc a b)) G A Ledge Rs diag positive Rm hsource hdiag hpositive hRm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Uniqueness of the actual preparation family, with an internally chosen auxiliary radius. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem actualPreparation_planeWeakSolution_unique (K : ι → ℕ) (Kmax : ℕ)
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
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) f F g u w)
    (hsol' : IsCoupledWeakSolutionPlane ν a b (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) f F g u' w') :
    ∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t := by
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
  obtain ⟨r, hr, hrρ, hrhalf, hrsmall⟩ := exists_auxiliary_absorption_radius ρ ν M hρ hν hM
  have hfinite i j d := coefficientSeminorm_radius_ne_top r ρ hr.le hrρ (K i) a b _
    (sampledEnvelope_edge_seminorm_ne_top family π hπ K actual a b ν e E ρ Cprep hν hρ A hfwd i j d)
  have hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (AVenhance.streamVel (Φ m) t)) l x‖ ≤
        M * (1 : ℝ) ^ l * (l.factorial : ℝ) * (1 : ℝ) ^ ((1 : ℤ) - l) := by
    intro t _ l _ hl x
    simp only [one_pow, one_zpow, mul_one]
    have hfac : (1 : ℝ) ≤ (l.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos l)
    exact (hMbound l hl t x).trans (le_mul_of_one_le_right hM hfac)
  have hC i j d t ht := edgeCoefficient_spatial_smooth family hprep ν e E K hs actual K i j d t ht
  have hAm i j d := edgeCoefficient_joint_measurable family hprep ν e E K hs hmeas hwmeas actual K i j d
  have hrank i j (hij : ¬ sourceDepthRank family H j < sourceDepthRank family H i) d :
      edgeCoefficient family ν e E actual K i j d = 0 :=
    physicalCoefficient_zero_of_rank family H hdepth ν e E actual i j d.val hij
  exact triangularPlaneWeakSolution_unique K Kmax hK r M 1 1 ν
    hr hM (le_refl 1) zero_lt_one hν (by simpa using hrhalf) (by simpa using hrsmall)
    a b hab (AVenhance.streamVel (Φ m)) hv hvm V hV hbv hdiv hjets D
    (edgeCoefficient family ν e E actual K) hfinite hC hAm
    (sourceDepthRank family H) hrank F g hF hg f u w hsol u' w' hsol'

end AVRegularity.CycleJointProofs
end
end

section
/-! The actual preparation inputs construct the complete native source map at
any reference time in the covered preparation window. -/

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
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparationWindowReferenceCellSource_allMoment_map_of_pointwise
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b)
    (ν e ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1)) (K : ι → ℕ) (Kmax Jm : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm : ℕ → ℝ)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (yc : Vec 2)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (B : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    (u0 u1 ϖ r : ℝ) (hu : u0 ≤ u1) (hr : 0 < r)
    (hsub : Set.Icc u0 u1 ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))) :
    ∃ T : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ r 0
      (volume.restrict (Set.Icc u0 u1))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ r 0
        (volume.restrict (Set.Icc u0 u1)),
      ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ r 0 (volume.restrict (Set.Icc u0 u1))
        (fun W t => planeRawCouplingFlux K D t
          (preparationReferenceCellSourceCoefficient F hφ σ
            ν e (ocEpsilon q Λ (m - 1)) actual K yc)
          (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ r 0
            (volume.restrict (Set.Icc u0 u1)) (W j) t) i) (T i) := by
  obtain ⟨Cprep, _, hsamp⟩ := preparation_window_reference_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hsample := hsamp α q Λ m φ hφ a b Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hc hcover σ hσ henv
  have hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      (ocEpsilon q Λ (m - 1)) K := by
    intro p c v u γ d I tY htY z
    exact (henv.1 p c v u γ d I tY htY z).of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have he : 0 < e := hρ.trans_le hρe
  have hE : 0 < ocEpsilon q Λ (m - 1) := he.trans_le heE
  exact preparationReferenceCellSource_allMoment_map F hc ν e (ocEpsilon q Λ (m - 1)) hν
    he.ne' hE.ne' K hs hmeas hwmeas actual σ yc
    π hπ ρ r Cprep hρ hr B hsample u0 u1 ϖ hu hsub

end AVRegularity.CycleJointProofs
end
end

section
/-! The actual preparation inputs construct the complete native source map at
any reference time in the covered preparation window. -/

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
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem preparationWindowReferenceCellSource_pointwise_subwindow_data
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b)
    (ν e ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1)) (K : ι → ℕ) (Kmax Jm : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm : ℕ → ℝ)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (actual : ∀ p, Ctx p) (yc : Vec 2)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (B : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ B v u)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    (u0 u1 r : ℝ)
    (hsub : Set.Icc u0 u1 ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))) :
    let A := preparationReferenceCellSourceCoefficient F hφ σ
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    (∀ v u d, coefficientSeminorm r (K v) u0 u1 (A v u d) ≠ ⊤) ∧
    (∀ v u d t, t ∈ Set.Icc u0 u1 → ContDiff ℝ (K v : ℕ) (A v u d t)) ∧
    (∀ v u d, Measurable (fun p : Set.Icc u0 u1 × Vec 2 => A v u d p.1 p.2)) ∧
    (∀ v u, ¬ Nonempty (F.Γ v u) → ∀ d t z, t ∈ Set.Icc u0 u1 → A v u d t z = 0) := by
  obtain ⟨Cprep, _, hsamp⟩ := preparation_window_reference_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hsample := hsamp α q Λ m φ hφ a b Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hc hcover σ hσ henv
  have hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      (ocEpsilon q Λ (m - 1)) K := by
    intro p c v u γ d I tY htY z
    exact (henv.1 p c v u γ d I tY htY z).of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have he : 0 < e := hρ.trans_le hρe
  exact preparationReferenceCellSourceCoefficient_subwindow_data F hc ν e (ocEpsilon q Λ (m - 1))
    hν he.ne' (he.trans_le heE).ne' K hs hmeas hwmeas actual
    σ yc π hπ ρ r Cprep hρ B hsample u0 u1 hsub

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The true preparation plane equation is unique on every chronological subwindow, using the original preparation certificate. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem actualPreparation_planeWeakSolution_arbitrary_subwindow_unique (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν)
    (a b : ℝ)
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
    (c tZ : ℝ) (hac : a ≤ c) (hcd : c ≤ tZ) (hdb : tZ ≤ b)
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc c tZ)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc c tZ)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν c tZ (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) f F g u w)
    (hsol' : IsCoupledWeakSolutionPlane ν c tZ (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) f F g u' w') :
    ∀ i, ∀ t ∈ Set.Icc c tZ, u i t = u' i t := by
  have hsub : Set.Icc c tZ ⊆ Set.Icc a b := by
    intro t ht
    exact ⟨hac.trans ht.1, ht.2.trans hdb⟩
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
  obtain ⟨r, hr, hrρ, hrhalf, hrsmall⟩ := exists_auxiliary_absorption_radius ρ ν M hρ hν hM
  have hfiniteFull i j d := coefficientSeminorm_radius_ne_top r ρ hr.le hrρ (K i) a b _
    (sampledEnvelope_edge_seminorm_ne_top family π hπ K actual a b ν e E ρ Cprep hν hρ A hfwd i j d)
  have hfinite i j d := ne_top_of_le_ne_top (hfiniteFull i j d)
    (coefficientSeminorm_time_mono r (K i) c tZ a b hsub
      (edgeCoefficient family ν e E actual K i j d))
  have hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (AVenhance.streamVel (Φ m) t)) l x‖ ≤
        M * (1 : ℝ) ^ l * (l.factorial : ℝ) * (1 : ℝ) ^ ((1 : ℤ) - l) := by
    intro t _ l _ hl x
    simp only [one_pow, one_zpow, mul_one]
    have hfac : (1 : ℝ) ≤ (l.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos l)
    exact (hMbound l hl t x).trans (le_mul_of_one_le_right hM hfac)
  have hC i j d t ht := edgeCoefficient_spatial_smooth family hprep ν e E K hs actual K i j d t ht
  have hAm i j d := jointMeasurable_subwindow c tZ a b hsub
    (edgeCoefficient family ν e E actual K i j d)
    (edgeCoefficient_joint_measurable family hprep ν e E K hs hmeas hwmeas actual K i j d)
  have hvmSmall := jointMeasurable_subwindow c tZ a b hsub (streamVel (Φ m)) hvm
  have hrank i j (hij : ¬ sourceDepthRank family H j < sourceDepthRank family H i) d :
      edgeCoefficient family ν e E actual K i j d = 0 :=
    physicalCoefficient_zero_of_rank family H hdepth ν e E actual i j d.val hij
  exact triangularPlaneWeakSolution_unique K Kmax hK r M 1 1 ν
    hr hM (le_refl 1) zero_lt_one hν (by simpa using hrhalf) (by simpa using hrsmall)
    c tZ hcd (AVenhance.streamVel (Φ m)) (fun t ht => hv t (hsub ht)) hvmSmall
    V hV (fun t ht => hbv t (hsub ht)) (fun t ht => hdiv t (hsub ht))
    (fun t ht => hjets t (hsub ht)) D
    (edgeCoefficient family ν e E actual K) hfinite (fun i j d t ht => hC i j d t (hsub ht)) hAm
    (sourceDepthRank family H) hrank F g hF hg f u w hsol u' w' hsol'

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Actual preparation data supply the quantitative source inputs for native
homogeneous stability, uniformly over the covered reference time. -/

universe u v w x

theorem preparation_window_reference_source_energy_data
    (D Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
    ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
      (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)]
      {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
      (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hB : ∀ i j, 0 ≤ B i j),
      IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
      (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
      F.IsTimeMeasurable → (∀ p, Measurable (F.weight p)) →
      IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
        ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    ∀ σ ∈ Set.Icc tS tZ, ∀ (yc : Vec 2) (a b θ : ℝ),
      Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
      (∀ i, ∑ j, B i j ≤ θ) → (∀ j, ∑ i, B i j ≤ θ) →
    ∀ H : ℕ, F.HasDepthAtMost H →
    let A := preparationReferenceCellSourceCoefficient F hφ σ
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    (∀ i j d, coefficientSeminorm (ρ / e) (K i) a b (A i j d) ≠ ⊤) ∧
    (∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t)) ∧
    (∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)) ∧
    (∀ i, ∑ j, schurMatrix 1 (ρ / e) π K D a b A i j ≤ Cprep * θ) ∧
    (∀ j, ∑ i, schurMatrix 1 (ρ / e) π K D a b A i j ≤ Cprep * θ) ∧
    (∀ i, sourceDepthRank F H i ≤ H) ∧
    (∀ i j, ¬ sourceDepthRank F H j < sourceDepthRank F H i → ∀ d, A i j d = 0) := by
  obtain ⟨Cprep, hCprep, hschur⟩ := preparation_window_reference_cell_source_subwindow_schur_budget
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ P' Ctx F π hπ K hK actual B hB hprep hcover hmeas hwmeas henv
    σ hσ yc a b θ hsub hrow hcol H hdepth A
  obtain ⟨hfinite, hsmooth, hmeasA, _⟩ := preparationWindowReferenceCellSource_pointwise_subwindow_data
    F hprep hcover σ hσ ν e ρ hν hρ hρe heE K Kmax Jm hK hchart hmol Cm
    hmeas hwmeas actual yc π hπ B hB henv a b (ρ / e) hsub
  have hentry := hschur α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ
    hν hρ hρe heE F π hπ K hK actual B hB hprep hcover σ hσ henv yc a b hsub
  refine ⟨hfinite, hsmooth, hmeasA, ?_, ?_, ?_, ?_⟩
  · intro i
    calc
      _ ≤ ∑ j, Cprep * B i j := Finset.sum_le_sum (fun j _ => hentry i j)
      _ = Cprep * ∑ j, B i j := (Finset.mul_sum _ _ _).symm
      _ ≤ Cprep * θ := mul_le_mul_of_nonneg_left (hrow i) (le_trans zero_le_one hCprep)
  · intro j
    calc
      _ ≤ ∑ i, Cprep * B i j := Finset.sum_le_sum (fun i _ => hentry i j)
      _ = Cprep * ∑ i, B i j := (Finset.mul_sum _ _ _).symm
      _ ≤ Cprep * θ := mul_le_mul_of_nonneg_left (hcol j) (le_trans zero_le_one hCprep)
  · exact sourceDepthRank_le F H
  · intro i j hij d
    exact preparationReferenceCellSourceCoefficient_zero_of_rank F hφ H hdepth
      σ ν e (ocEpsilon q Λ (m - 1)) actual K yc i j d hij

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The actual reference chart of the preparation cover supplies all coefficient
regularity for the full metric-plus-source feedback equation. -/

def windowCoverReferenceChartIndex (P : ℕ) : Fin (P + 2) := ⟨1, by omega⟩

theorem windowCoverReferenceChartIndex_label (l₀ : ℤ) (P : ℕ) :
    l₀ - 1 + (windowCoverReferenceChartIndex P : ℤ) = l₀ := by
  simp only [windowCoverReferenceChartIndex, Fin.val_mk, Nat.cast_one, sub_add_cancel]

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The padded cover's reference chart has exactly the prescribed central
particle label, so recentering the cover chooses the desired localization center. -/

theorem windowCover_reference_centre_eq (α q : ℝ) (Λ m : ℕ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2) :
    windowCoverChartCentre α q Λ m φ hφ l₀ P y₀ (windowCoverReferenceChartIndex P) = y₀ := by
  unfold windowCoverChartCentre windowCoverReferenceChartIndex
  change ocCellCentre α q Λ m φ hφ (l₀ - 1)
    (ocTransition α q Λ m φ hφ (l₀ - 1) l₀ y₀) (0 + 1) = y₀
  rw [ocCellCentre, ocCellCentre]
  have hl : l₀ - 1 + (0 : ℕ) + 1 = l₀ := by omega
  rw [hl]
  simp only [Nat.cast_zero, add_zero]
  exact (streamFlowHomeomorph hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
    (((l₀ - 1 : ℤ) : ℝ) * ocTauPP α q Λ m)).apply_symm_apply y₀

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! Every covered time trace of the actual homogeneous preparation family is linear. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem actualPreparation_homogeneous_family_trace_linearMap (K : ι → ℕ) (Kmax : ℕ)
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
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (lf : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (u : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : ∀ x, IsCoupledWeakSolutionPlane ν a b (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) (lf x)
      (fun _ _ => 0) (fun _ _ => 0) (u x) (w x))
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
      ∀ x i, T x i = u x i t := by
  have huniq f u₁ w₁ u₂ w₂ h₁ h₂ :=
    actualPreparation_planeWeakSolution_unique K Kmax hK ρ ν hρ hν a b hab D family H hdepth
      α q Λ m Φ ζ hΦ φ hφ Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual
      hmeas hwmeas hE hρe heE Jm hchart hmol Cm π hπ A hA hpointwise
      (fun _ _ => 0) (fun _ _ => 0)
      (fun _ => timeMemLp_zero _ _) (fun _ => timeIntegrable_zero _) f u₁ u₂ w₁ w₂ h₁ h₂
  let T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)) :=
    { toFun := fun x i => u x i t
      map_add' := by
        intro x y
        have hs := planeWeakSolution_add K D ν a b (AVenhance.streamVel (Φ m)) _
          (lf x) (lf y) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
          (u x) (u y) (w x) (w y) (hsol x) (hsol y)
        simp only [add_zero] at hs
        rw [← Pi.add_def, ← map_add] at hs
        funext i
        exact huniq (lf (x + y)) _ _ _ _ (hsol (x + y)) hs i t ht
      map_smul' := by
        intro c x
        have hs := planeWeakSolution_smul K D c ν a b (AVenhance.streamVel (Φ m)) _
          (lf x) (fun _ _ => 0) (fun _ _ => 0) (u x) (w x) (hsol x)
        simp only [smul_zero] at hs
        rw [← Pi.smul_def, ← map_smul] at hs
        funext i
        exact huniq (lf (c • x)) _ _ _ _ (hsol (c • x)) hs i t ht }
  exact ⟨T, fun _ _ => rfl⟩
end

/-! The actual preparation endpoint is linear on prepared data, with no auxiliary drift premises. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_actualPreparation_planeEndpoint_linearMap (K : ι → ℕ) (Kmax : ℕ)
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
    :
    ∃ T : (∀ i, PlaneHk Set.univ (K i) (h i)) →ₗ[ℝ]
      (∀ i, PlaneHk Set.univ (K i) (h i)),
      ∀ f, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
        (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
        IsCoupledWeakSolutionPlane ν a b (AVenhance.streamVel (Φ m)) D K
          (edgeCoefficient family ν e E actual K) f (fun _ _ => 0) (fun _ _ => 0) u w ∧
        (fun i => u i b) = T f := by
  classical
  have hex (f : ∀ i, PlaneHk Set.univ (K i) (h i)) :=
    exists_actualPreparation_planeWeakSolution K Kmax hK ρ ν hρ hν a b hab D family H hdepth
      α q Λ m Φ ζ hΦ φ hφ Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual
      hmeas hwmeas hE hρe heE Jm hchart hmol Cm π hπ A hA hpointwise
      (fun _ _ => 0) (fun _ _ => 0) (fun _ => timeMemLp_zero _ _)
      (fun _ => timeIntegrable_zero _) f
  let u := fun f => Classical.choose (hex f)
  let w := fun f => Classical.choose (Classical.choose_spec (hex f))
  have hsol f : IsCoupledWeakSolutionPlane ν a b (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) f (fun _ _ => 0) (fun _ _ => 0) (u f) (w f) :=
    Classical.choose_spec (Classical.choose_spec (hex f))
  have huniq f u₁ u₂ w₁ w₂ h₁ h₂ :=
    actualPreparation_planeWeakSolution_unique K Kmax hK ρ ν hρ hν a b hab D family H hdepth
      α q Λ m Φ ζ hΦ φ hφ Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual
      hmeas hwmeas hE hρe heE Jm hchart hmol Cm π hπ A hA hpointwise
      (fun _ _ => 0) (fun _ _ => 0) (fun _ => timeMemLp_zero _ _)
      (fun _ => timeIntegrable_zero _) f u₁ u₂ w₁ w₂ h₁ h₂
  let T : (∀ i, PlaneHk Set.univ (K i) (h i)) →ₗ[ℝ]
      (∀ i, PlaneHk Set.univ (K i) (h i)) :=
    { toFun := fun f i => u f i b
      map_add' := by
        intro f g
        have hadd := planeWeakSolution_add K D ν a b (AVenhance.streamVel (Φ m)) _ f g
          (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
          (u f) (u g) (w f) (w g) (hsol f) (hsol g)
        simp only [add_zero] at hadd
        funext i
        exact huniq (f + g) _ _ _ _ (hsol (f + g)) hadd i b ⟨hab, le_refl b⟩
      map_smul' := by
        intro c f
        have hsmul := planeWeakSolution_smul K D c ν a b (AVenhance.streamVel (Φ m)) _ f
          (fun _ _ => 0) (fun _ _ => 0) (u f) (w f) (hsol f)
        simp only [smul_zero] at hsmul
        funext i
        exact huniq (fun j => c • f j) _ _ _ _
          (hsol (fun j => c • f j)) hsmul i b ⟨hab, le_refl b⟩ }
  exact ⟨T, fun f => ⟨u f, w f, hsol f, rfl⟩⟩
end

/-! Every covered time trace of the actual homogeneous preparation family is linear. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem actualPreparation_homogeneous_subwindow_family_trace_linearMap (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν)
    (a b : ℝ)
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
    (c tZ : ℝ) (hac : a ≤ c) (hcd : c ≤ tZ) (hdb : tZ ≤ b)
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (lf : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (u : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : ∀ x, IsCoupledWeakSolutionPlane ν c tZ (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) (lf x)
      (fun _ _ => 0) (fun _ _ => 0) (u x) (w x))
    (t : ℝ) (ht : t ∈ Set.Icc c tZ) :
    ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
      ∀ x i, T x i = u x i t := by
  have huniq f u₁ w₁ u₂ w₂ h₁ h₂ :=
    actualPreparation_planeWeakSolution_arbitrary_subwindow_unique K Kmax hK ρ ν hρ hν a b D family H hdepth
      α q Λ m Φ ζ hΦ φ hφ Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual
      hmeas hwmeas hE hρe heE Jm hchart hmol Cm π hπ A hA hpointwise c tZ hac hcd hdb
      (fun _ _ => 0) (fun _ _ => 0)
      (fun _ => timeMemLp_zero _ _) (fun _ => timeIntegrable_zero _) f u₁ u₂ w₁ w₂ h₁ h₂
  let T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)) :=
    { toFun := fun x i => u x i t
      map_add' := by
        intro x y
        have hs := planeWeakSolution_add K D ν c tZ (AVenhance.streamVel (Φ m)) _
          (lf x) (lf y) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
          (u x) (u y) (w x) (w y) (hsol x) (hsol y)
        simp only [add_zero] at hs
        rw [← Pi.add_def, ← map_add] at hs
        funext i
        exact huniq (lf (x + y)) _ _ _ _ (hsol (x + y)) hs i t ht
      map_smul' := by
        intro r x
        have hs := planeWeakSolution_smul K D r ν c tZ (AVenhance.streamVel (Φ m)) _
          (lf x) (fun _ _ => 0) (fun _ _ => 0) (u x) (w x) (hsol x)
        simp only [smul_zero] at hs
        rw [← Pi.smul_def, ← map_smul] at hs
        funext i
        exact huniq (lf (r • x)) _ _ _ _ (hsol (r • x)) hs i t ht }
  exact ⟨T, fun _ _ => rfl⟩
end

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

theorem planeComponentAllMomentResponse_metric_actualTaylor_retained_metric_remainder_budget_uniform
    (Ks Kmax : ℕ) (Cjet : ℕ → ℝ) (hCjet : ∀ r, 0 ≤ Cjet r) :
    ∃ CT CR : ℝ, 0 ≤ CT ∧ 0 ≤ CR ∧ ∀ {ι : Type*} [Fintype ι] {E : ι → Type*}
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
    planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π (fun i => Rm i (Wret i)) ≤
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * gm * ζ ^ (Ks + 1)) ^ 2) *
        retainedResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
      planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z := by
  obtain ⟨CT, hCT, hgainRet⟩ := planeComponentAllMomentResponse_metric_actualTaylor_retained_gradient_gain_uniform
    Ks Kmax Cjet hCjet
  obtain ⟨CR, hCR, hmetric⟩ := metricRemainder_family_map_mass_moment_budget_uniform Ks Kmax Cjet
  refine ⟨CT, CR, hCT, hCR, ?_⟩
  intro ι _ E _ _ _ _ _ _ a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem
    hGhigh hGhighjet Rm hRm hgain Z n J H hN
  dsimp only
  let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
    finiteResponse 1 (nativeDiagonalResponseOperator R T)
      (nativeComponentResponseOperator R (fun i => Tsource i - Remainder i)) Z j k
  have he := hmetric (E := E) K hK G a b ϖ ρ ζ gm hGm hGhigh hϖ hρ hscale hζ hζ1 hgm
    hGhighjet π Rm hRm Wret n
  have hgret := hgainRet (E := E) a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem hgain Z
    (n + (Ks + 1)) J H hN
  simpa only [Wret, mul_assoc] using he.trans (mul_le_mul_of_nonneg_left hgret zero_le)

end AVRegularity.CycleJointProofs
end
end
