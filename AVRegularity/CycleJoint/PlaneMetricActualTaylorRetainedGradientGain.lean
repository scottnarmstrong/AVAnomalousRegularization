-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
import AVRegularity.CycleJoint.PlaneHomogeneousMaterialWeakCurve
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.CycleJoint.OriginalFamilyNaturalRemainderDescendingIdentity
public import AVRegularity.CycleJoint.PlaneComponentAllMomentGradientBudget
import AVenhance.Infra.Classical.Drift

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The actual native-window response lift is linear for forcing which superposes almost everywhere. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {ν B tA tZ ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
  {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}

local instance coverAeLiftResponseNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := inferInstance
local instance coverAeLiftResponseLpAdd (i : ι) (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance coverAeLiftResponseLpModule (i : ι) (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k (h i)) 2 μ) := inferInstance
local instance coverAeLiftResponseNativeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance coverAeLiftResponseNativeModule (i : ι) (k : ℕ) : Module ℝ (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance coverAeLiftResponseFluxAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance coverAeLiftResponseFluxModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

theorem windowCover_frozen_response_ae_liftLinearMap (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
    (K : ι → ℕ) (hK : ∀ x, K x ≤ Kmax) (i : Fin (P + 2))
    (u0 u1 : ℝ) (hu : u0 ≤ u1)
    (hwindow : Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i)
    (hgsmall : 4 * g ≤ 1 / 8)
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (lf : X →ₗ[ℝ] (∀ x, PlaneHk Set.univ (K x) (h x)))
    (lF : X → ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hadd : ∀ a b x, lF (a + b) x =ᵐ[volume.restrict (Set.Icc u0 u1)]
      fun t => lF a x t + lF b x t)
    (hsmul : ∀ (c : ℝ) a x, lF (c • a) x =ᵐ[volume.restrict (Set.Icc u0 u1)]
      fun t => c • lF a x t)
    (hF : ∀ a x, MemLp (lF a x) 2 (volume.restrict (Set.Icc u0 u1)))
    :
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i
    ∃ T : ∀ x, X →ₗ[ℝ] Lp (PlaneHk Set.univ (K x + 1) (h x)) 2
      (volume.restrict (Set.Icc u0 u1)),
      ∀ a, ∃ (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
        (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
        IsPlaneChainFrom (geometryScalarData 2 (fun t _ =>
          ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0))
          (fun _ x => K x) u0 u1 (ocCellDrift α q Λ ζ m ν yc)
          (fun _ x => lf a x) (fun _ x => lF a x) (fun _ x => u x) (fun _ x => w x) ∧
          ∃ hw : ∀ x, MemLp (w x) 2 (volume.restrict (Set.Icc u0 u1)),
            (fun x => (hw x).toLp (w x)) = (fun x => T x a) := by
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
  obtain ⟨T, hT⟩ := exists_frozenMetricPlaneResponse_ae_liftLinearMap
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
    lf lF hadd hsmul (0 : X →ₗ[ℝ] (∀ x, ℝ → PlaneHk Set.univ (K x) (h x))) hF
    (fun _ x => integrable_zero ℝ (PlaneHk Set.univ (K x) (h x)) _) hvm
  refine ⟨T, ?_⟩
  intro a
  obtain ⟨u, w, hs, heq⟩ := hT a
  refine ⟨u, w, ?_, heq⟩
  exact planeDiagonalMetric_scalar_solution K u0 u1 (ocCellDrift α q Λ ζ m ν yc)
    (fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν yc t 0)
    (lf a) (lF a) u w hs

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

theorem exists_preparationReferenceCellSourceMap_natural_split
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
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
        (ν⁻¹ * e ^ 2) a b hφ (F.piece p.val).anchor ((l₀ : ℝ) * ocTauPP α q Λ m) e (ocEpsilon q Λ (m - 1)) yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
            (volume.restrict (Set.Icc a b)) x τ) (j.val + 1) I z))) (T v u γ j p)) :
    ∃ Lfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0
        (volume.restrict (Set.Icc a b)),
    (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (Lfull v)) ∧
    let Rs := nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p)
    ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 (volume.restrict (Set.Icc a b))
      (fun x τ z => ∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p : (F.locally_finite tS tZ).toFinset,
        naturalFamilyTaylorNativeArray Ks F p.val (actual p.val) v u γ (ν⁻¹ * e ^ 2) hφ
          (F.piece p.val).anchor ((l₀ : ℝ) * ocTauPP α q Λ m) e (ocEpsilon q Λ (m - 1)) yc (j.val + 1) τ z
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0
              (volume.restrict (Set.Icc a b)) (x u) τ) (j.val + 1) I z)))
      (Lfull v - Rs v) ∧ Lfull v = (Lfull v - Rs v) + Rs v := by
  have he : 0 < e := hρ.trans_le hρe
  have hr : 0 < ρ / e := div_pos hρ he
  obtain ⟨Lfull, hfull⟩ := preparationReferenceCellSource_allMoment_map_of_pointwise F hc ν e ρ
    hν hρ hρe heE K Kmax Jm hK hchart hmol Cm hmeas hwmeas actual yc π hπ B hB henv
    a b ϖ (ρ / e) hab hr hsub
  refine ⟨Lfull, hfull, ?_⟩
  exact preparationReferenceCellSourceMap_natural_split F hc ν e (ocEpsilon q Λ (m - 1))
    hν.ne' he actual K hdesc Ks ((l₀ : ℝ) * ocTauPP α q Λ m) yc a b ϖ (ρ / e)
    htime Lfull hfull T hT

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual coupled native map has the central, positive metric, original source, and two remainder decomposition consumed by the constructed error. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance fiveTermMapConstructionNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance fiveTermMapConstructionModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

local instance fiveTermMapConstructionFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance fiveTermMapConstructionFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance fiveTermMapConstructionFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance fiveTermMapConstructionFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem planeMetricSource_fiveTerm_allMoment_map_construction
    (K : ι → ℕ) (Ks D : ℕ) (hD : 2 ≤ D) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (sourceFull Rs : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (diag positive Rm : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (hsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i) (sourceFull i))
    (hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (diag i))
    (hpositive : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (positive i))
    (hremainder : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux
        (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (Rm i)) :
    ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t (planeMetricSourceCoefficient K D G A)
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i)
      ((diag i).comp (LinearMap.proj i) + (positive i).comp (LinearMap.proj i) +
        nativeFamilyEdgeForcingMap (nativeFamilyMapEdge (fun v => sourceFull v - Rs v)) i +
        (Rm i).comp (LinearMap.proj i) + Rs i) := by
  let metric := fun i => diag i + positive i + Rm i
  have hm i := metric_allMoment_map_taylor_construction (K i) Ks ϖ ρ μ G
    (diag i) (positive i) (Rm i) (hdiag i) (hpositive i) (hremainder i)
  have hc := planeMetricSource_allMoment_map_construction K D hD ϖ ρ μ G A sourceFull metric hsource hm
  intro i
  have he : (diag i).comp (LinearMap.proj i) + (positive i).comp (LinearMap.proj i) +
      nativeFamilyEdgeForcingMap (nativeFamilyMapEdge (fun v => sourceFull v - Rs v)) i +
      (Rm i).comp (LinearMap.proj i) + Rs i = (metric i).comp (LinearMap.proj i) + sourceFull i := by
    rw [nativeFamilyMapEdge_assembly]
    dsimp only [metric]
    rw [LinearMap.add_comp, LinearMap.add_comp]
    abel
  rw [he]
  exact hc i
end

/-! The actual coupled native map has the central, positive metric, original source, and two remainder decomposition consumed by the constructed error. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance fiveTermMapIdentificationNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance fiveTermMapIdentificationModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

local instance fiveTermMapIdentificationFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance fiveTermMapIdentificationFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance fiveTermMapIdentificationFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance fiveTermMapIdentificationFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem planeMetricSource_fiveTerm_allMoment_map_identification
    (K : ι → ℕ) (Ks D : ℕ) (hD : 2 ≤ D) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (sourceFull Rs : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (diag positive Rm : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (hsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i) (sourceFull i))
    (hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (diag i))
    (hpositive : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (positive i))
    (hremainder : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux
        (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (Rm i))
    (full Ldiag : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (hfull : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t (planeMetricSourceCoefficient K D G A)
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i) (full i))
    (hLdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t
        (planeDiagonalGradientCoefficient K D (fun _ t _ => G t 0 - 1))
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i) (Ldiag i)) :
    ∀ i, full i = Ldiag i + (positive i).comp (LinearMap.proj i) +
      nativeFamilyEdgeForcingMap (nativeFamilyMapEdge (fun v => sourceFull v - Rs v)) i +
      (Rm i).comp (LinearMap.proj i) + Rs i := by
  have hc := planeMetricSource_fiveTerm_allMoment_map_construction K Ks D hD ϖ ρ μ G A
    sourceFull Rs diag positive Rm hsource hdiag hpositive hremainder
  have hd := planeCentralMetric_family_map_identification K D hD ϖ ρ μ (fun t => G t 0)
    Ldiag diag hLdiag hdiag
  intro i
  rw [hd i]
  apply planeRaw_allMoment_map_unique (K i) ϖ ρ 0 μ _ _ _ _ (hfull i) (hc i)
  intro X
  exact Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl))
end

/-! The actual coupled native map has the central, positive metric, original source, and two remainder decomposition consumed by the constructed error. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance originalEdgeMapConstructionNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance originalEdgeMapConstructionModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

local instance originalEdgeMapConstructionFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance originalEdgeMapConstructionFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => h i)) := inferInstance
local instance originalEdgeMapConstructionFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance originalEdgeMapConstructionFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem planeMetricSource_originalEdge_allMoment_map_construction
    (K : ι → ℕ) (Ks D : ℕ) (hD : 2 ≤ D) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (Rs : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (diag positive Rm : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (hsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i) (nativeFamilyEdgeForcingMap Ledge i + Rs i))
    (hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (diag i))
    (hpositive : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (positive i))
    (hremainder : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux
        (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (Rm i)) :
    ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeRawCouplingFlux K D t (planeMetricSourceCoefficient K D G A)
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i)
      ((diag i).comp (LinearMap.proj i) + (positive i).comp (LinearMap.proj i) +
        nativeFamilyEdgeForcingMap Ledge i +
        (Rm i).comp (LinearMap.proj i) + Rs i) := by
  have hc := planeMetricSource_fiveTerm_allMoment_map_construction K Ks D hD ϖ ρ μ G A
    (fun i => nativeFamilyEdgeForcingMap Ledge i + Rs i) Rs diag positive Rm
    hsource hdiag hpositive hremainder
  intro i
  have hi := hc i
  rw [nativeFamilyMapEdge_add_sub_assembly] at hi
  exact hi
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

/-! The higher native material carriers satisfy the homogeneous coupled weak equation in every row. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeHomogeneous_higher_material_weak_curve {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t))
    (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K i + 1 → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K i + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j) :
    PlaneWeakHilbertCurve a b
      (fun t => planeHkValueOperator (K i) (planeHkWindowChartPull a b hφ s B
        (fun j hj hjK => hB j hj (by omega))
        (fun t ht j hj hjK => hb t ht j hj (by omega)) t (u i t)))
      (fun t => truncatePlaneHk (show 1 ≤ K i + 1 by omega)
        (planeHkWindowChartPull a b hφ s B hB hb t (w i t)))
      (fun t => planeWeakDualRepresentative (planeMaterialTransport a b hab hφ s v hv hp t)
        (planeMaterialDiffusion a b hab hφ s ν t)
        (truncatePlaneHk (show 1 ≤ K i + 1 by omega)
          (planeHkWindowChartPull a b hφ s B hB hb t (w i t)))
        (planeFluxChartPull hφ t s (planeFluxValueOperator (E := h i) (K i)
          (planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)))) := by
  have h := planeHomogeneous_material_weak_curve hab ρ hρ K D A hA hc ν v hv hp
    hvc hvm M hvb hAm f u w hφ s hs i
  have he : (fun t => truncatePlaneHk (show 1 ≤ K i + 1 by omega)
      (planeHkWindowChartPull a b hφ s B hB hb t (w i t)))
      =ᵐ[volume.restrict (Icc a b)]
        (fun t => planeH1ChartPull hφ t s (coupledPlaneH1Slice w i t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact planeHkWindowChartPull_h1 (by omega) a b hφ s B hB hb t ht (w i t)
  apply planeWeakCurve_congr h
  · intro t ht
    exact planeHkWindowChartPull_value_eq a b hφ s B _ _ t ht (u i t)
  · exact he
  · filter_upwards [he] with t ht
    rw [ht]

end AVRegularity.CycleJointProofs
end
end

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

theorem exists_preparationNaturalRemainder_maps_mass_budget
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
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hsE : ρ / e ≤ ocEpsilon q Λ (m - 1) / e)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hδ : e / E = ζ * ϖ)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ Set.Icc tS tZ)
    (hN : Kmax + D ≤ Jchart)
    (hcellE : 0 < ocEpsilon q Λ (m - 1)) (yc : Vec 2) (μ : Measure ℝ) :
    let S := (F.locally_finite tS tZ).toFinset
    let σ := (l₀ : ℝ) * ocTauPP α q Λ m
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
  have hend (p : S) := preparation_reference_anchor_endpoints hprep p.val
    ((F.locally_finite tS tZ).mem_toFinset.mp p.property) hTau
  exact exists_naturalFamilyRemainder_maps_mass_budget Ks F hw hm π hπ K Kmax hK hdesc
    (Set.Icc tS tZ) ν e E ρ hν he hE hρ C J b₀ henv hKs hb θ hθ hrow hcol
    S (fun p => actual p.val) hprep.flow ha (fun p => (F.piece p.val).anchor)
    ((l₀ : ℝ) * ocTauPP α q Λ m) (fun p => (hend p).1) hprep.schedule.reference_mem
    (fun p => (hend p).2.2) hsE ϖ ζ hϖ hscale hζ hδ
    (fun v => by have hv := hK v; omega)
    timeScale a b htime (Kmax + D) hN
    (fun v u γ => Nat.add_le_add (hK v) (F.identity v u γ).le_D) hcellE yc μ

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual preparation coefficients satisfy the homogeneous periodization transfer requirements. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_actualPreparation_periodizedHomogeneous_solution (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν)
    (a b : ℝ) (hab : a ≤ b)
    (D : ℕ) {P' : Type*} {Ctx : P' → Type*}
    (family : ChartedFamily ι h D P' Ctx)
    (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P : ℕ)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P family)
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hmeas : family.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (family.weight p))
    (hE : E = ocEpsilon q Λ (m - 1)) (hρe : ρ ≤ e) (heE : e ≤ E)
    (Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (he : e = ocEpsilon q Λ m) (htorus : IsTorusCompatible family actual E)
    (hpointwise : IsPointwiseMolecularEnvelope family π K
      (ChartedFamily.Domain.onWindow family (Set.Icc a b)) ν e E ρ Cm Jm
      (fun v u => Real.sqrt (π u / π v) * A v u))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b (streamVel (Φ m)) D K
      (edgeCoefficient family ν e E actual K) f (fun _ _ => 0) (fun _ _ => 0) u w)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2)
    (henergy : geometryEnergyNorm π K 4 ϖ z ρ a b u w < ⊤) :
    ∃ (U : ∀ i, ℝ → TorusHk (K i) (h i)) (W : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsPeriodizedFamilyPair K a b u w U W ∧
      IsCoupledWeakSolutionTorus ν a b (streamVel (Φ m)) D K
        (edgeCoefficient family ν e E actual K) (fun i => U i a)
        (fun _ _ => 0) (fun _ _ => 0) U W := by
  obtain ⟨Cprep, hCprep, hsample⟩ := preparation_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hfwd : IsSampledEnvelope family π K actual a b ν e E ρ Cprep
      (fun v u => Real.sqrt (π u / π v) * A v u) := by
    subst E
    exact hsample α q Λ m φ hφ a b Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
      family π hπ K hK actual _
      (fun v u => mul_nonneg (Real.sqrt_nonneg _) (hA v u)) hprep hpointwise
  have hsm : family.IsSmoothOn (ChartedFamily.Domain.onWindow family (Set.Icc a b)) E K := by
    intro p ctx v u γ d I tY htY z
    exact (hpointwise.1 p ctx v u γ d I tY htY z).of_le
      (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hcur := streamSeq_current_admissible hΦ m
  have hvfull := Infra.Classical.streamVel_smoothPeriodic (Φ m) hcur
  obtain ⟨V, hV, hbV⟩ := admissible_stream_spatial_jet_bound (Φ m) hcur 0
  let MC := fun v u (d : admissibleOrders K D v u) =>
    Cprep * (ν * ρ ^ (d.val - 2)) *
      ((K v).factorial : ℝ) / ((K v + d.val - 2).factorial : ℝ) * A v u
  apply exists_periodizedHomogeneous_torus_solution K D π hπ ν a b hab
    (streamVel (Φ m)) _ _ hvfull.smooth.continuous.measurable V hV _
    (edgeCoefficient family ν e E actual K) _ f u w hs ϖ hϖ z ρ hρ henergy
    _ _ MC _ _ hζ
  · intro t n x
    simpa using hvfull.periodic 0 n t x
  · intro t _
    exact (hvfull.smooth.comp (contDiff_const.prodMk contDiff_id)).continuous
  · intro t _ x
    simpa only [norm_iteratedFDeriv_zero] using hbV t x
  · intro v u d t
    subst e
    subst E
    exact htorus.edgeCoefficient_periodic_ocEpsilon ν K v u d t
  · intro v u d t ht
    exact (edgeCoefficient_spatial_smooth family hprep ν e E K hsm actual K v u d t ht).continuous
  · intro v u d
    exact edgeCoefficient_joint_measurable family hprep ν e E K hsm hmeas hwmeas actual K v u d
  · intro v u d
    dsimp only [MC]
    have hCp : 0 ≤ Cprep := zero_le_one.trans hCprep
    have hAvu := hA v u
    positivity
  · intro v u d t ht x
    exact sampledEnvelope_edgeCoefficient_bound family π hπ K actual a b ν e E ρ Cprep
      hν hρ (zero_le_one.trans hCprep) A hA hfwd v u d t ht x

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

theorem planeComponentAllMomentResponse_metric_actualTaylor_insertion_budgets_uniform
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
    , ∀ k : ℕ, k + (Ks + 1) ≤ N → ∀ W,
    (planeAllMomentFamilyGradientEnergy K k ϖ ρ (volume.restrict (Icc a b)) π
      (nativeDiagonalResponseOperator R T W) ≤
      (scalarResponseGradientPrice Kmax L Cw k *
        ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CT * gm * ζ) ^ 2)) *
      planeAllMomentFamilyGradientEnergy K (k + (Ks + 1)) ϖ ρ (volume.restrict (Icc a b)) π W) ∧
    (planeAllMomentFamilyGradientEnergy K k ϖ ρ (volume.restrict (Icc a b)) π
      (nativeComponentResponseOperator R (fun i => Tsource i - Remainder i) W) ≤
      ((scalarResponseGradientReservePrice Kmax L Cw N *
        ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph)) * (ENNReal.ofReal θ) ^ 2) *
      planeAllMomentFamilyGradientEnergy K (k + (Ks + 1)) ϖ ρ (volume.restrict (Icc a b)) π W) := by
  obtain ⟨CT, hCT, hmetric⟩ :=
    planeComponentAllMomentResponse_metric_insertion_gradient_budget_uniform Ks Kmax Cjet hCjet
  refine ⟨CT, hCT, ?_⟩
  intro ι _ E _ _ _ _ _ _ a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem k hk W
  constructor
  ·
    have hkN : k ≤ N := (Nat.le_add_right k (Ks + 1)).trans hk
    have he := hmetric (E := E) a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
      M hMm g hg hg4 hnear hsym t₀ S ϖ N k Cw C hkN ρ L hρ hL hsmall hstrainSmall
      (hreserve k hkN) hdiv hwa hwb π R hR G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet T hT W
    have hm := planeAllMomentFamilyGradientEnergy_moment_mono K
      (show k + Ks ≤ k + (Ks + 1) by omega) ϖ ρ (volume.restrict (Icc a b)) π W
    have hh := he.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm zero_le) zero_le) zero_le)
    simpa only [scalarResponseGradientPrice, planeAllMomentFamilyGradientEnergy, mul_assoc] using hh
  · have hkN : k ≤ N := (Nat.le_add_right k (Ks + 1)).trans hk
    have he := planeComponentAllMomentResponse_actualTaylor_uniform_gradient_budget
      a b hab K Kmax hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
      M hMm g hg hg4 hnear hsym t₀ S ϖ N k Cw C hkN ρ L hρ hL hsmall hstrainSmall
      (hreserve k hkN) hdiv hwa hwb π R hR D A hA hC Tsource hTsource hπ Cprep Cgraph θ ζ
      hθ hζ hζ1 hrow hcol Remainder W (Ks + 1) (hrem W k)
    exact he

/-! Genuine metric and original edge insertions assemble into the finite native response mass-gradient estimate. -/

theorem planeComponentAllMomentResponse_metric_actualTaylor_terminal_forcing_gain_uniform
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
    (Z : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b))) (n J H : ℕ) (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N),
    let Cg := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
    planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => T i ((∑ k ∈ Finset.range (H + 1), finiteResponse 1
        (nativeDiagonalResponseOperator R T)
        (nativeComponentResponseOperator R (fun v => Tsource v - Remainder v)) Z J k) i)) ≤
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax) *
        terminalResponseEnergyPrice Cg (ENNReal.ofReal θ) J H) *
        (ENNReal.ofReal (CT * gm * ζ)) ^ (2 * (J + 1)) *
        planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z := by
  obtain ⟨CT, hCT, hmetric⟩ := metricTaylor_family_map_mass_moment_budget_uniform Ks Kmax Cjet hCjet
  refine ⟨CT, hCT, ?_⟩
  intro ι _ E _ _ _ _ _ _ a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem Z n J H hN
  dsimp only
  have ht (X : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
      (volume.restrict (Icc a b))) (k : ℕ) := hmetric (E := E) K hK G a b ϖ ρ δ ζ gm
    hGm hGs hϖ hρ hscale hζ hζ1 hgm hδ hGjet π T hT X k
  have htshift X k := (ht X k).trans (mul_le_mul_of_nonneg_left
    (planeAllMomentFamilyGradientEnergy_moment_mono K
      (show k + Ks ≤ k + (Ks + 1) by omega) ϖ ρ (volume.restrict (Icc a b)) π X) zero_le)
  refine planeAllMoment_terminal_forcing_energy_gain K ϖ ρ (volume.restrict (Icc a b)) π
    (nativeDiagonalResponseOperator R T)
    (nativeComponentResponseOperator R (fun i => Tsource i - Remainder i))
    (fun X i => T i (X i))
    (fun k => scalarResponseGradientPrice Kmax L Cw k *
      ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CT * gm * ζ) ^ 2))
    (fun _ => (scalarResponseGradientReservePrice Kmax L Cw N *
      ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph)) * (ENNReal.ofReal θ) ^ 2)
    (scalarResponseTwoInsertionCommonPrice Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph)))
    (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)) (ENNReal.ofReal (CT * gm * ζ))
    (ENNReal.ofReal θ) (Ks + 1) N ?_ ?_ ?_ ?_ Z n J H hN ?_
  · intro k hk X
    have hkN : k ≤ N := (Nat.le_add_right k (Ks + 1)).trans hk
    have he := planeComponentAllMomentResponse_family_gradient_budget a b hab K Kmax hK
      v hvm hv V strain B lam hV ha hB hlam hbv hjets M hMm g hg hg4 hnear hsym
      t₀ S ϖ N k Cw C hkN ρ L hρ hL hsmall hstrainSmall (hreserve k hkN)
      hdiv hwa hwb π R hR (fun i => T i (X i))
    have hbnd := he.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (htshift X k) zero_le) zero_le)
    simpa only [scalarResponseGradientPrice, planeAllMomentFamilyGradientEnergy, mul_assoc,
      nativeDiagonalResponseOperator, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply] using hbnd
  · intro k hk X
    have hkN : k ≤ N := (Nat.le_add_right k (Ks + 1)).trans hk
    exact planeComponentAllMomentResponse_actualTaylor_uniform_gradient_budget
      a b hab K Kmax hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
      M hMm g hg hg4 hnear hsym t₀ S ϖ N k Cw C hkN ρ L hρ hL hsmall hstrainSmall
      (hreserve k hkN) hdiv hwa hwb π R hR D A hA hC Tsource hTsource hπ Cprep Cgraph θ ζ
      hθ hζ hζ1 hrow hcol Remainder X (Ks + 1) (hrem X k)
  · intro k hk
    rw [ENNReal.ofReal_mul (metricTaylorUniformDensityPrice_nonneg Kmax),
      ENNReal.ofReal_pow (mul_nonneg (mul_nonneg hCT hgm) hζ), ← mul_assoc]
    exact scalarResponseTwoInsertionCommonPrice_metric Kmax L Cw N k hk _ _ _
  · intro k _
    exact scalarResponseTwoInsertionCommonPrice_source Kmax L Cw N _ _ _
  · intro X
    have he := htshift X n
    rw [ENNReal.ofReal_mul (metricTaylorUniformDensityPrice_nonneg Kmax),
      ENNReal.ofReal_pow (mul_nonneg (mul_nonneg hCT hgm) hζ)] at he
    exact he

/-! Genuine metric and original edge insertions assemble into the finite native response mass-gradient estimate. -/

theorem planeComponentAllMomentResponse_metric_actualTaylor_retained_gradient_gain_uniform
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
      (volume.restrict (Icc a b))) (n J H : ℕ) (_hN : n + (J + H) * (Ks + 1) ≤ N),
    let Cg := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
    planeAllMomentFamilyGradientEnergy K n ϖ ρ (volume.restrict (Icc a b)) π
      (∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
        finiteResponse 1 (nativeDiagonalResponseOperator R T)
          (nativeComponentResponseOperator R (fun i => Tsource i - Remainder i)) Z j k) ≤
      retainedResponseEnergyPrice Cg (ENNReal.ofReal θ) J H *
        planeAllMomentFamilyGradientEnergy K N ϖ ρ (volume.restrict (Icc a b)) π Z := by
  obtain ⟨CT, hCT, hone⟩ := planeComponentAllMomentResponse_metric_actualTaylor_insertion_budgets_uniform
    Ks Kmax Cjet hCjet
  refine ⟨CT, hCT, ?_⟩
  intro ι _ E _ _ _ _ _ _ a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem hgain Z n J H hN
  dsimp only
  have hinsert := hone (E := E) a b hab K hK v hvm hv V strain B lam hV ha hB hlam hbv hjets
    M hMm g hg hg4 hnear hsym t₀ S ϖ N Cw C ρ L hρ hL hsmall hstrainSmall
    hreserve hdiv hwa hwb π R hR hπ G δ ζ gm hGm hGs hϖ hscale hζ hζ1 hgm hδ hGjet
    T hT D A hA hC Tsource hTsource Cprep Cgraph θ hθ hrow hcol Remainder hrem
  apply planeAllMoment_retained_gradient_energy_gain K ϖ ρ (volume.restrict (Icc a b)) π
    (nativeDiagonalResponseOperator R T)
    (nativeComponentResponseOperator R (fun i => Tsource i - Remainder i))
    (fun k => scalarResponseGradientPrice Kmax L Cw k *
      ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CT * gm * ζ) ^ 2))
    (fun _ => (scalarResponseGradientReservePrice Kmax L Cw N *
      ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph)) * (ENNReal.ofReal θ) ^ 2)
    _ (ENNReal.ofReal (CT * gm * ζ)) (ENNReal.ofReal θ) (Ks + 1) N
    (fun k hk W => (hinsert k hk W).1) (fun k hk W => (hinsert k hk W).2) _ _ hgain Z n J H hN
  · intro k hk
    have he := scalarResponseTwoInsertionCommonPrice_metric Kmax L Cw N k hk
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
      (ENNReal.ofReal (CT * gm * ζ))
    rw [ENNReal.ofReal_mul (metricTaylorUniformDensityPrice_nonneg Kmax),
      ENNReal.ofReal_pow (mul_nonneg (mul_nonneg hCT hgm) hζ) 2]
    simpa only [mul_assoc] using he
  · intro k _
    exact scalarResponseTwoInsertionCommonPrice_source Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph)) (ENNReal.ofReal θ)

end AVRegularity.CycleJointProofs
end
end
