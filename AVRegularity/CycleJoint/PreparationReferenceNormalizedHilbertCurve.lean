-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction
import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
import AVRegularity.CycleJoint.PlaneMetricActualTaylorRetainedGradientGain
public import AVRegularity.CycleJoint.PlaneHomogeneousMaterialWeakCurve
import AVRegularity.Families.TorusCompatible.WeakStage
import AVenhance.Infra.Classical.Drift

section
/-! Constructing all original weighted natural remainder maps and assembling
 their mass moment estimate, with constants fixed before the family and scales. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.ChartTransport
  AVRegularity.CycleWords AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem exists_preparationWindowNaturalRemainder_maps_mass_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hdesc : F.IsDescending K)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) ν e E ρ C J b₀)
    (hKs : Ks + 1 ≤ J) (hb : ∀ v u, 0 ≤ b₀ v u)
    (θ : ℝ) (hθ : 0 ≤ θ) (hrow : ∀ v, ∑ u, b₀ v u ≤ θ)
    (hcol : ∀ u, ∑ v, b₀ v u ≤ θ)
    (actual : ∀ p, Ctx p)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc tS tZ)
    (ha : 0 ≤ ocA α q Λ (m - 1))
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ Set.Icc tS tZ)
    (hN : Kmax + D ≤ Jchart)
    (hcellE : 0 < ocEpsilon q Λ (m - 1)) (yc : Vec 2) (μ : Measure ℝ) :
    let S := (F.locally_finite tS tZ).toFinset
    ∃ T : ∀ v u, F.Γ v u → Fin D → S →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ,
    (∀ v u γ j p, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
      (fun x τ z => naturalFamilyRemainderNativeArray Ks F p.val (actual p.val) v u γ
        timeScale a b hφ (F.piece p.val).anchor σ e E yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) (j.val + 1) I z)))
      (T v u γ j p)) ∧
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpiola := compConst Cflow (Kmax + D) * Cflow
    let CR := nativeArrayUniformTransportPrice (Kmax + D) D Kmax Cpiola *
      naturalRemainderChartPrice Ks Kmax Jchart Cchart
    ∀ (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ) (n : ℕ),
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ
        (nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p) v Z) τ) ∂μ) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) *
        (pointwiseOriginalRemainderGraphConstant Ks Kmax ((D : ℝ) * CR) C * θ)) ^ 2) *
      ∫⁻ τ, ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + (Ks + 1))
        ϖ 0 (ρ / e) (K u) (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ (Z u) τ) ∂μ := by
  classical
  let S := (F.locally_finite tS tZ).toFinset
  have hg (p : S) := preparation_piece_anchor_mem_geometry hprep p.val
    ((F.locally_finite tS tZ).mem_toFinset.mp p.property)
  have hpad (p : S) := hprep.schedule.geometry_padded p.val
    ((F.locally_finite tS tZ).mem_toFinset.mp p.property) (hg p)
  have hage (p : S) := preparation_piece_to_window_reference_age hprep hcover p.val
    ((F.locally_finite tS tZ).mem_toFinset.mp p.property) _ (hg p) σ hσ
  exact exists_naturalFamilyRemainder_maps_mass_budget Ks F hw hm π hπ K Kmax hK hdesc
    (Set.Icc tS tZ) ν e E ρ hν he hE hρ C J b₀ henv hKs hb θ hθ hrow hcol
    S (fun p => actual p.val) hprep.flow ha (fun p => (F.piece p.val).anchor)
    σ hpad (preparation_reference_time_padded hprep hcover σ hσ)
    hage hsE ϖ ζ hϖ hscale hζ hδ
    (fun v => by have hv := hK v; omega)
    timeScale a b htime (Kmax + D) hN
    (fun v u γ => Nat.add_le_add (hK v) (F.identity v u γ).le_D) hcellE yc μ

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

local instance literalPriceEndpointNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance literalPriceEndpointNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance literalPriceEndpointFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance literalPriceEndpointFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem planeRetained_literal_constructed_error_endpoint_price
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
        ∀ C cm cs ct θ θcap ζ η G0 : ℝ≥0∞, θ ≤ θcap →
        planeAllMomentFamilyEnergy Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π (fun i => Rmetric i (Wret i)) ≤ (cm * ζ ^ (2 * (Ks + 1)) * retainedResponseEnergyPrice C θ J H) * G0 →
        planeAllMomentFamilyEnergy Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π (fun i => Rs i Wret) ≤ (cs * ζ ^ (2 * (Ks + 1)) * retainedResponseEnergyPrice C θ J H) * G0 →
        planeAllMomentFamilyEnergy Kslot n ϖ rstar (volume.restrict (Set.Icc ta tb)) π (fun i => Lmetric i (Tret i)) ≤ (ct * terminalResponseEnergyPrice C θ J H * η ^ (2 * (J + 1))) * G0 →
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
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζ ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0)) := by
  intro π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ htw htb W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC
    P Ctx family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder
  classical
  have hout := planeRetained_literal_constructed_error_endpoint_energy
    n Kmax CG Cw D H Ks Bsrc π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets tw S ϖ htw htb W hD A hA hc hAm hrow hcol rank hrank hzero hr1 V₀ hf uH wH hH M R Lmetric Ledge u0 w0 Z hdiagA hfullA hdiagC hfullC family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder
  dsimp only at hout ⊢
  intro C cm cs ct θ θcap ζ η G0 hθ hm hs ht
  obtain ⟨Fout, uout, wout, hsol, hF, hW, hbound⟩ := hout
    ((cm * ζ ^ (2 * (Ks + 1)) * retainedResponseEnergyPrice C θ J H) * G0)
    ((cs * ζ ^ (2 * (Ks + 1)) * retainedResponseEnergyPrice C θ J H) * G0)
    ((ct * terminalResponseEnergyPrice C θ J H * η ^ (2 * (J + 1))) * G0) hm hs ht
  refine ⟨Fout, uout, wout, hsol, hF, hW, ?_⟩
  intro tp htp
  exact (hbound tp htp).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (coupledRetainedResidualPrice_source_scale_budget C cm cs ct θ θcap ζ η G0 hθ (Ks + 1) J H)
      zero_le) zero_le)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The genuine reference-chart homogeneous curve retains its physical viscous diffusion and the actual native source, before diffusion-time normalization. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_homogeneous_material_diffusion_curve
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (ν e E : ℝ) (n : ι → ℕ)
    (hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (edgeCoefficient F ν e E actual K i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Icc a b → ContDiff ℝ (K i : ℕ) (edgeCoefficient F ν e E actual K i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t))
    (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => edgeCoefficient F ν e E actual K i i' d p.1 p.2))
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    let Q : ℝ → PlaneFluxL2 (h i) := fun t => if ht : t ∈ Icc a b then
      preparationReferenceNativeFluxOperator F K hprep hcover hTau ha hK ν e E n hsmooth
        actual hT he t ht i (fun j => W j t) else 0
    PlaneWeakHilbertCurve a b (fun t => planeHkValueOperator (K i) (U i t))
      (fun t => truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i t))
      (fun t => planeWeakDualRepresentative
        (planeMaterialTransport a b hab hφ ((l₀ : ℝ) * ocTauPP α q Λ m) v hv hp t)
        (planeMaterialDiffusion (E := h i) a b hab hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν t)
        (truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i t)) (Q t)) := by
  dsimp only
  have hcurve := planeHomogeneous_higher_material_weak_curve hab ρ hρ K D
    (edgeCoefficient F ν e E actual K) hA hc ν v hv hp hvc hvm M hvb hAm f u w hφ
    ((l₀ : ℝ) * ocTauPP α q Λ m) hs i
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun t ht j hj hjK x => preparation_reference_flow_jets hprep hcover hTau ha t ht j hj
      (hjK.trans (Nat.add_le_add_right (hK i) 1)) x)
  apply planeWeakHilbertCurve_dual_congr_on hcurve
  intro t ht
  rw [dite_eq_left ht, preparationReferenceNativeFluxOperator_windowPull,
    preparationPhysicalNativeFlux_eq_couplingRow F K hdesc ν e E a b hab ρ hρ n hsmooth
      actual hT he hA hc w t ht i]
  rfl
end

/-! The genuine reference-chart homogeneous curve retains its physical viscous diffusion and the actual native source, before diffusion-time normalization. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_homogeneous_material_diffusion_curve_subwindow
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (ν e E : ℝ) (n : ι → ℕ)
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
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν c d v D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    let Q : ℝ → PlaneFluxL2 (h i) := fun t => if ht : t ∈ Icc a b then
      preparationWindowReferenceNativeFluxOperator F K hprep hcover σ hσ ha hK ν e E n hsmooth
        actual hT he t ht i (fun j => W j t) else 0
    PlaneWeakHilbertCurve c d (fun t => planeHkValueOperator (K i) (U i t))
      (fun t => truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i t))
      (fun t => planeWeakDualRepresentative
        (planeMaterialTransport c d hcd hφ σ v hv hp t)
        (planeMaterialDiffusion (E := h i) c d hcd hφ σ ν t)
        (truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i t)) (Q t)) := by
  dsimp only
  have hcurve := planeHomogeneous_higher_material_weak_curve hcd ρ hρ K D
    (edgeCoefficient F ν e E actual K) hA hc ν v hv hp hvc hvm M hvb hAm f u w hφ
    σ hs i
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun t ht j hj hjK x => preparation_window_reference_time_flow_jets hprep hcover σ hσ ha t (hsub ht) j hj
      (hjK.trans (Nat.add_le_add_right (hK i) 1)) x)
  have heq (k : ℕ) (hk : k ≤ Jchart + 1) (t : ℝ) (ht : t ∈ Icc c d)
      (V : PlaneHk univ k (h i)) :
      planeHkWindowChartPull c d hφ σ
        (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
        (fun _ _ _ => abs_nonneg _)
        (fun r hr j hj hjk x => preparation_window_reference_time_flow_jets hprep hcover σ hσ ha
          r (hsub hr) j hj (hjk.trans hk) x) t V =
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha k hk t V := by
    unfold preparationWindowReferenceHkWindowPull planeHkWindowChartPull
    rw [dite_eq_left ht, dite_eq_left (hsub ht)]
  apply planeWeakHilbertCurve_congr_on hcurve
  · intro t ht
    rw [heq _ _ t ht _]
  · intro t ht
    rw [heq _ _ t ht _]
  · intro t ht
    rw [heq _ _ t ht _, dite_eq_left (hsub ht),
      preparationWindowReferenceNativeFluxOperator_windowPull,
      preparationPhysicalNativeFlux_eq_subwindow_couplingRow F K hdesc ν e E a b
        ρ hρ n hsmooth actual hT he c d hcd hsub hA hc w t ht i]
end

/-! The actual homogeneous preparation equation in diffusion time has unit diffusion, the computed chart metric deviation, and its original finite native source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_normalized_homogeneous_weak_curve
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (ν e E : ℝ) (hν : 0 < ν) (n : ι → ℕ)
    (hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (edgeCoefficient F ν e E actual K i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Icc a b → ContDiff ℝ (K i : ℕ) (edgeCoefficient F ν e E actual K i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t))
    (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => edgeCoefficient F ν e E actual K i i' d p.1 p.2))
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    let Q : ℝ → PlaneFluxL2 (h i) := fun t => if ht : t ∈ Icc a b then
      preparationReferenceNativeFluxOperator F K hprep hcover hTau ha hK ν e E n hsmooth
        actual hT he t ht i (fun j => W j t) else 0
    PlaneWeakHilbertCurve (ν * a) (ν * b)
      (fun t => planeHkValueOperator (K i) (U i (ν⁻¹ * t)))
      (fun t => truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))
      (fun t => planeWeakDualRepresentative
        (ν⁻¹ • planeMaterialTransport a b hab hφ ((l₀ : ℝ) * ocTauPP α q Λ m) v hv hp (ν⁻¹ * t))
        (ContinuousLinearMap.id ℝ (PlaneFluxL2 (h i)))
        (truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))
        ((planeMaterialDiffusion (E := h i) a b hab hφ ((l₀ : ℝ) * ocTauPP α q Λ m) 1 (ν⁻¹ * t) -
          ContinuousLinearMap.id ℝ (PlaneFluxL2 (h i)))
            (planeH1GradientOperator (truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))) +
          ν⁻¹ • Q (ν⁻¹ * t))) := by
  dsimp only
  have hcurve := preparation_reference_homogeneous_material_diffusion_curve F hab ρ hρ K hdesc
    hprep hcover hTau ha hK ν e E n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm f u w hs i
  exact planeMaterialWeakCurve_normalized_unit_diffusion hab hν hφ
    ((l₀ : ℝ) * ocTauPP α q Λ m)
    (planeMaterialTransport a b hab hφ ((l₀ : ℝ) * ocTauPP α q Λ m) v hv hp) _ _ _ hcurve
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Uniqueness of the actual preparation family, with an internally chosen auxiliary radius. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem actualPreparation_torusWeakSolution_subwindow_unique (K : ι → ℕ) (Kmax : ℕ)
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
    (he : e = ocEpsilon q Λ m) (htorus : IsTorusCompatible family actual E)
    (hmeas : family.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (family.weight p))
    (hE : E = ocEpsilon q Λ (m - 1)) (hρe : ρ ≤ e) (heE : e ≤ E)
    (Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hpointwise : IsPointwiseMolecularEnvelope family π K
      (ChartedFamily.Domain.onWindow family (Set.Icc a b)) ν e E ρ Cm Jm A)
    (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a c)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a c)))
    (f : ∀ i, TorusHk (K i) (h i))
    (u u' : ∀ i, ℝ → TorusHk (K i) (h i))
    (w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionTorus ν a c (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) f F g u w)
    (hsol' : IsCoupledWeakSolutionTorus ν a c (AVenhance.streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) f F g u' w') :
    ∀ i, ∀ t ∈ Set.Icc a c, u i t = u' i t := by
  have hsub : Set.Icc a c ⊆ Set.Icc a b := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hcb⟩
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
    (coefficientSeminorm_time_mono r (K i) a c a b hsub
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
  have hAm i j d := jointMeasurable_subwindow a c a b hsub
    (edgeCoefficient family ν e E actual K i j d)
    (edgeCoefficient_joint_measurable family hprep ν e E K hs hmeas hwmeas actual K i j d)
  have hvmSmall := jointMeasurable_subwindow a c a b hsub (streamVel (Φ m)) hvm
  have hrank i j (hij : ¬ sourceDepthRank family H j < sourceDepthRank family H i) d :
      edgeCoefficient family ν e E actual K i j d = 0 :=
    physicalCoefficient_zero_of_rank family H hdepth ν e E actual i j d.val hij
  have hvp : ∀ t ∈ Set.Icc a b, IsZ2Periodic (streamVel (Φ m) t) := by
    intro t _ k x
    simpa using hvfull.periodic 0 k t x
  have hpA : ∀ t ∈ Set.Icc a b, ∀ i j d,
      IsZ2Periodic (edgeCoefficient family ν e E actual K i j d t) := by
    intro t _ i j d
    subst e
    subst E
    exact htorus.edgeCoefficient_periodic_ocEpsilon ν K i j d t
  exact triangularWeakSolution_unique K D ν r hr a c hac (streamVel (Φ m))
    hvmSmall (fun t ht => hv t (hsub ht))
    (fun t ht => hvp t (hsub ht)) V hV (fun t ht => hbv t (hsub ht)) (fun _ _ => M)
    (fun t _ i l x => hMbound l.val (Nat.le_trans (Nat.le_of_lt_succ l.isLt) (hK i)) t x)
    (edgeCoefficient family ν e E actual K) hfinite hAm
    (fun t ht i j d => hC i j d t (hsub ht))
    (fun t ht => hpA t (hsub ht)) F g w u f hF hg hsol hν Kmax hK M 1 1
    hM (le_refl 1) zero_lt_one (by simpa using hrhalf) (by simpa using hrsmall)
    (fun t ht => hdiv t (hsub ht)) (fun t ht => hjets t (hsub ht))
    (sourceDepthRank family H) hrank u' w' hsol'

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual homogeneous preparation equation in diffusion time has unit diffusion, the computed chart metric deviation, and its original finite native source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_normalized_homogeneous_weak_curve_subwindow
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K)
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
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν c d v D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    let Q : ℝ → PlaneFluxL2 (h i) := fun t => if ht : t ∈ Icc a b then
      preparationWindowReferenceNativeFluxOperator F K hprep hcover σ hσ ha hK ν e E n hsmooth
        actual hT he t ht i (fun j => W j t) else 0
    PlaneWeakHilbertCurve (ν * c) (ν * d)
      (fun t => planeHkValueOperator (K i) (U i (ν⁻¹ * t)))
      (fun t => truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))
      (fun t => planeWeakDualRepresentative
        (ν⁻¹ • planeMaterialTransport c d hcd hφ σ v hv hp (ν⁻¹ * t))
        (ContinuousLinearMap.id ℝ (PlaneFluxL2 (h i)))
        (truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))
        ((planeMaterialDiffusion (E := h i) c d hcd hφ σ 1 (ν⁻¹ * t) -
          ContinuousLinearMap.id ℝ (PlaneFluxL2 (h i)))
            (planeH1GradientOperator (truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))) +
          ν⁻¹ • Q (ν⁻¹ * t))) := by
  dsimp only
  have hcurve := preparation_window_reference_homogeneous_material_diffusion_curve_subwindow F hcd hsub ρ hρ K hdesc
    hprep hcover σ hσ ha hK ν e E n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm f u w hs i
  exact planeMaterialWeakCurve_normalized_unit_diffusion hcd hν hφ
    σ
    (planeMaterialTransport c d hcd hφ σ v hv hp) _ _ _ hcurve

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Genuine frozen scalar responses on the certified native windows, with their complete finite moment reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_frozen_response_exists (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 ≤ u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8)
    (N : ℕ) (ϖ : ℝ) (Cw : ℕ → ℝ)
    (C : ChartWeights
      (fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i) t 0)
      (ocCellDrift α q Λ ζ m ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i))
      u0 (u1 - u0) ϖ 0 N Cw)
    (L : ℕ → ℝ) (hL : ∀ n ≤ N, 1 ≤ L n)
    (hreserve : ∀ n ≤ N, Real.exp (18 * Cw n) / (L n) ^ 2 ≤ 1 / 16)
    (F : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc u0 u1)))
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (hf : ∀ n ≤ N, ∀ x,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (f x) ≠ ⊤)
    (hFe : ∀ n ≤ N, ∀ x, (∫⁻ t in Set.Icc u0 u1,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (F x t)) ≠ ⊤) :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
      (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
        (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
        (fun _ x => f x) (fun _ x => F x) (fun _ x => u x) (fun _ x => w x) ∧
      ∀ n ≤ N, ∀ x,
        ((⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x) (u x t)) +
          ∫⁻ t in Set.Icc u0 u1, weightedGradFactorialNormSq n ϖ 0
            (ρs / ocEpsilon q Λ m) (K x) (w x t)) ≠ ⊤ ∧
        (∫⁻ t in Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x + 1) (w x t)) ≠ ⊤ := by
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
  have he : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hell : 0 < ocEll q Λ m ν ^ 2 := by
    rw [CycleReference.ocEll_sq_eq cov.pos.1]
    exact div_pos (sq_pos_of_pos he) cov.pos.1
  have hfull : Set.Icc u0 u1 ⊆ Set.Icc (tA / ocEll q Λ m ν ^ 2)
      (tZ / ocEll q Λ m ν ^ 2) :=
    hwindow.trans (clipped_scaled_time_window_subset _ _ _ _ _ hell)
  obtain ⟨V, hbv⟩ := cellDrift_norm_bound (α := α) (q := q) (m := m) hΛ hζ ν yc
  have hV : 0 ≤ V := (norm_nonneg _).trans (hbv 0 0)
  have hvm : Measurable (fun p : Set.Icc u0 u1 × Vec 2 =>
      ocCellDrift α q Λ ζ m ν yc p.1 p.2) :=
    cellDrift_window_measurable (α := α) (q := q) (m := m) hΛ hζ ν yc u0 u1
  exact exists_frozenMetricScalarChain_on_window_with_polynomial_reserve
    K Kmax hK (ρs / ocEpsilon q Λ m) strain B₀ lam (div_pos cov.pos.2.2 he)
    cov.drift_pos.1 cov.drift_pos.2.1 cov.drift_pos.2.2 cov.drift_scale cov.drift_small
    u0 u1 hu (ocCellDrift α q Λ ζ m ν yc)
    (fun t _ => cellDrift_spatial_contDiff (α := α) (q := q) (m := m) hΛ hζ ν t yc)
    V hV (fun t _ z => hbv t z)
    (fun t _ z => cellDrift_divergence_zero (α := α) (q := q) (m := m) hΛ hζ ν t yc z)
    (fun t ht r hr hrmax z => cov.drift_jets i r hr hrmax t (hfull ht) z)
    (fun t => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0)
    (frozenCellMetric_measurable α q Λ m hφ (l₀ - 1 + i) ν yc)
    g cov.g_range.1 hgsmall
    (fun t _ => ocCellMetric_symmetric α q Λ m hφ (l₀ - 1 + i) ν yc t 0)
    (fun t ht ξ => cov.metric_near i t (hwindow ht) 0 ξ)
    F hF f hvm ϖ 0 N Cw C L hL ((div_le_one he).mpr cov.rho_e) hreserve hf hFe
end

/-! Every actual frozen scalar response on a certified native window retains the supplied finite moment reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_frozen_response_reserve_propagation (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 ≤ u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8)
    (N : ℕ) (ϖ : ℝ) (Cw : ℕ → ℝ)
    (C : ChartWeights
      (fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i) t 0)
      (ocCellDrift α q Λ ζ m ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i))
      u0 (u1 - u0) ϖ 0 N Cw)
    (L : ℕ → ℝ) (hL : ∀ n ≤ N, 1 ≤ L n)
    (hreserve : ∀ n ≤ N, Real.exp (18 * Cw n) / (L n) ^ 2 ≤ 1 / 16)
    (F : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc u0 u1)))
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (hf : ∀ n ≤ N, ∀ x,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (f x) ≠ ⊤)
    (hFe : ∀ n ≤ N, ∀ x, (∫⁻ t in Set.Icc u0 u1,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (F x t)) ≠ ⊤)
    (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
    (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (hs : let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
        (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
        (fun _ x => f x) (fun _ x => F x) (fun _ x => u x) (fun _ x => w x)) :
      ∀ n ≤ N, ∀ x,
        ((⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x) (u x t)) +
          ∫⁻ t in Set.Icc u0 u1, weightedGradFactorialNormSq n ϖ 0
            (ρs / ocEpsilon q Λ m) (K x) (w x t)) ≠ ⊤ ∧
        (∫⁻ t in Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x + 1) (w x t)) ≠ ⊤ := by
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
  have he : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hell : 0 < ocEll q Λ m ν ^ 2 := by
    rw [CycleReference.ocEll_sq_eq cov.pos.1]
    exact div_pos (sq_pos_of_pos he) cov.pos.1
  have hfull : Set.Icc u0 u1 ⊆ Set.Icc (tA / ocEll q Λ m ν ^ 2)
      (tZ / ocEll q Λ m ν ^ 2) :=
    hwindow.trans (clipped_scaled_time_window_subset _ _ _ _ _ hell)
  obtain ⟨V, hbv⟩ := cellDrift_norm_bound (α := α) (q := q) (m := m) hΛ hζ ν yc
  have hV : 0 ≤ V := (norm_nonneg _).trans (hbv 0 0)
  have hvm : Measurable (fun p : Set.Icc u0 u1 × Vec 2 =>
      ocCellDrift α q Λ ζ m ν yc p.1 p.2) :=
    cellDrift_window_measurable (α := α) (q := q) (m := m) hΛ hζ ν yc u0 u1
  exact frozenMetricScalarChain_on_window_polynomial_reserve
    K Kmax hK (ρs / ocEpsilon q Λ m) strain B₀ lam (div_pos cov.pos.2.2 he)
    cov.drift_pos.1 cov.drift_pos.2.1 cov.drift_pos.2.2 cov.drift_scale cov.drift_small
    u0 u1 hu (ocCellDrift α q Λ ζ m ν yc)
    (fun t _ => cellDrift_spatial_contDiff (α := α) (q := q) (m := m) hΛ hζ ν t yc)
    V hV (fun t _ z => hbv t z)
    (fun t _ z => cellDrift_divergence_zero (α := α) (q := q) (m := m) hΛ hζ ν t yc z)
    (fun t ht r hr hrmax z => cov.drift_jets i r hr hrmax t (hfull ht) z)
    (fun t => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0)
    (frozenCellMetric_measurable α q Λ m hφ (l₀ - 1 + i) ν yc)
    g cov.g_range.1 hgsmall
    (fun t _ => ocCellMetric_symmetric α q Λ m hφ (l₀ - 1 + i) ν yc t 0)
    (fun t ht ξ => cov.metric_near i t (hwindow ht) 0 ξ)
    F hF f hvm ϖ 0 N Cw C L hL ((div_le_one he).mpr cov.rho_e) hreserve hf hFe u w hs
end

/-! Native frozen responses retain every supplied finite polynomial moment without a reserve-size premise. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

theorem windowCover_frozen_response_finite_moments (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 ≤ u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8)
    (N : ℕ) (ϖ : ℝ) (Cw : ℕ → ℝ)
    (C : ChartWeights
      (fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i) t 0)
      (ocCellDrift α q Λ ζ m ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i))
      u0 (u1 - u0) ϖ 0 N Cw)
    (F : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hF : ∀ x, MemLp (F x) 2 (volume.restrict (Set.Icc u0 u1)))
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (hf : ∀ n ≤ N, ∀ x,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (f x) ≠ ⊤)
    (hFe : ∀ n ≤ N, ∀ x, (∫⁻ t in Set.Icc u0 u1,
      weightedFactorialNormSq n ϖ 0 (ρs / ocEpsilon q Λ m) (K x) (F x t)) ≠ ⊤) :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
      (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
        ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
        (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
        (fun _ x => f x) (fun _ x => F x) (fun _ x => u x) (fun _ x => w x) ∧
      ∀ n ≤ N, ∀ x,
        ((⨆ t ∈ Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x) (u x t)) +
          ∫⁻ t in Set.Icc u0 u1, weightedGradFactorialNormSq n ϖ 0
            (ρs / ocEpsilon q Λ m) (K x) (w x t)) ≠ ⊤ ∧
        (∫⁻ t in Set.Icc u0 u1, weightedFactorialNormSq n ϖ 0
          (ρs / ocEpsilon q Λ m) (K x + 1) (w x t)) ≠ ⊤ := by
  classical
  have hres (n : ℕ) := exists_scalar_square_reserve (Real.exp (18 * Cw n))
    (Real.exp_pos _).le
  let L : ℕ → ℝ := fun n => Classical.choose (hres n)
  have hL : ∀ n ≤ N, 1 ≤ L n := fun n _ => (Classical.choose_spec (hres n)).1
  have hreserve : ∀ n ≤ N, Real.exp (18 * Cw n) / (L n) ^ 2 ≤ 1 / 16 :=
    fun n _ => (Classical.choose_spec (hres n)).2
  exact windowCover_frozen_response_exists hΛ hζ hφ cov K hK i u0 u1 hu hwindow hgsmall
    N ϖ Cw C L hL hreserve F hF f hf hFe
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The normalized homogeneous material curve uses the true computed velocity and the exact coupled-array L2 flux, with no operator identification premise. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_normalized_hilbert_curve
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart)
    (ν e E : ℝ) (hν : 0 < ν) (n : ι → ℕ)
    (hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (edgeCoefficient F ν e E actual K i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Icc a b → ContDiff ℝ (K i : ℕ) (edgeCoefficient F ν e E actual K i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t))
    (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => edgeCoefficient F ν e E actual K i i' d p.1 p.2))
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K (edgeCoefficient F ν e E actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j)
        (by have hh := hK j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K j + 1)
        (Nat.add_le_add_right (hK j) 1) t (w j t)
    PlaneWeakHilbertCurve (ν * a) (ν * b)
      (fun t => planeHkValueOperator (K i) (U i (ν⁻¹ * t)))
      (fun t => truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))
      (fun t => planeWeakDualRepresentative
        (planeIntervalTransport (ν * a) (ν * b) (mul_le_mul_of_nonneg_left hab hν.le)
          (normalizedMaterialVelocity hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν v)
          (fun r _ => normalizedMaterialVelocity_continuous hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν v hv r)
          (normalizedMaterialVelocityBudget hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν a b v hv hp)
          (normalizedMaterialVelocity_norm_le hφ ((l₀ : ℝ) * ocTauPP α q Λ m) hν a b v hv hp) t)
        (ContinuousLinearMap.id ℝ (PlaneFluxL2 (h i)))
        (truncatePlaneHk (show 1 ≤ K i + 1 by omega) (W i (ν⁻¹ * t)))
        (preparationReferenceNormalizedFlux F K hab hprep hcover hTau ha hK ν e E n hsmooth
          actual hT he W i t)) := by
  dsimp only
  have hcurve := preparation_reference_normalized_homogeneous_weak_curve F hab ρ hρ K hdesc
    hprep hcover hTau ha hK ν e E hν n hsmooth actual hT he hA hc v hv hp hvc hvm M hvb hAm f u w hs i
  apply planeWeakHilbertCurve_dual_congr_on hcurve
  intro t ht
  rw [planeMaterialTransport_diffusion_time_normalization hab hν hφ
    ((l₀ : ℝ) * ocTauPP α q Λ m) v hv hp t ht]
  rfl

end AVRegularity.CycleJointProofs
end
end
