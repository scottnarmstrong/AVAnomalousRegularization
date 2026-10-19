-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.ActualPreparationHomogeneousPlaneExistence
import AVRegularity.CycleJoint.WindowCoverFrozenHomogeneousFamilyLinearMap
import AVRegularity.CycleJoint.PlaneMetricActualTaylorRetainedGradientGain
public import AVRegularity.CycleJoint.PreparationTransportedWeightedPolynomialAllMomentMap
import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction
import AVRegularity.CycleJoint.ActualPreparationHomogeneousFamilyNativeTraceLinearMap
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
import AVRegularity.CycleJoint.MetricTaylorFamilyMapMassBudget
import AVenhance.Infra.Classical.Drift

section
/-! The actual cover supplies the preparation-domain and slow-scale inputs of
its original-edge source decomposition on every certified native subwindow. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

theorem windowCover_window_reference_constructed_edge_package (D Kmax Jchart Jm : ℕ)
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
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ ∈ Set.Icc tS tZ,
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
        (preparationReferenceCellSourceCoefficient F hφ σ ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
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
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) ∧
    (∀ u, ∑ v, schurMatrix 1 (ρ / (ocEpsilon q Λ m)) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) := by
  obtain ⟨Cprep, hCprep, hmaps⟩ := preparation_window_reference_cell_constructed_edge_package
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc hcover σ hσ henv yc ic a b hab hwindow θ hrow hcol Ks hdesc hKs hθ
  dsimp only
  obtain ⟨hsub, htime, hϖ, hscale, hζ, _hζ1, hδ⟩ :=
    windowCover_native_subwindow_scales hΛ hφ cov ic a b hwindow
  exact hmaps α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad l₀ P
    ν (ocEpsilon q Λ m) ρ cov.pos.1 cov.pos.2.2 cov.rho_e heE
    F hmeas hwmeas π hπ K hK actual B hB hc hcover σ hσ henv yc a b
    (ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)) hab hsub θ hrow hcol
    Ks hdesc hKs hθ ha
    (Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))
    hϖ hscale hζ hδ htime

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

theorem preparation_window_reference_cell_natural_block_coupled_solution_of_pointwise_subwindow
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b u0 u1 : ℝ} (h01 : u0 ≤ u1) (hsub : Icc u0 u1 ⊆ Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (l : ℤ) (hσ : (l : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ha : 0 ≤ ocA α q Λ (m - 1))
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
    (c d : ℝ) (hac : (e⁻¹) ^ 2 * (ν * u0) ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * u1))
    (hblock : ∀ t ∈ Icc c d,
      ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hs : IsCoupledWeakSolutionPlane ν u0 u1 (streamVel (Φ m)) D K (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w) :
    let U : ∀ j, ℝ → PlaneHk univ (K j) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j)
        (by have hh := hKmax j; omega) t (u j t)
    let W : ∀ j, ℝ → PlaneHk univ (K j + 1) (h j) := fun j t =>
      preparationWindowReferenceHkWindowPull hprep hcover ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j + 1)
        (Nat.add_le_add_right (show K j ≤ Jchart by have hh := hKmax j; omega) 1) t (w j t)
    IsCoupledWeakSolutionPlane 1 c d
      (ocCellDrift α q Λ ζ m ν yc) D K
      (planeMetricSourceCoefficient K D
        (ocCellMetric α q Λ m (Φ (m - 1)) hφ l ν yc)
        (preparationReferenceCellSourceCoefficient F hφ ((l : ℝ) * ocTauPP α q Λ m)
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
  have hAsub i i' d := ne_top_of_le_ne_top (hA i i' d)
    (coefficientSeminorm_time_mono ρ (K i) u0 u1 a b hsub
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K i i' d))
  have hAmsub i i' d := jointMeasurable_subwindow u0 u1 a b hsub
    (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K i i' d) (hAm i i' d)
  exact preparation_window_reference_cell_natural_block_coupled_solution_subwindow F h01 hsub ρ hρ K hdesc hD hprep hcover l hσ ha hK
    hΛ hm hseq hΨ ν e (ocEpsilon q Λ (m - 1)) hν heScale K hsmooth actual hT he
    hAsub (fun i i' d t ht => hc i i' d t (hsub ht)) hv hp
    (fun t ht => hvc t (hsub ht))
    (jointMeasurable_subwindow u0 u1 a b hsub (streamVel (Φ m)) hvm)
    M (fun t ht => hvb t (hsub ht)) hAmsub hcell yc f u w c d hac hcd hdb hblock hs
end

/-! The actual physical preparation solution transfers with initial datum given by the mixed transition of its original reference native trace. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_cell_coupled_solution_on_actual_mixed_seam
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    {a b u0 u1 : ℝ} (h01 : u0 ≤ u1) (hsub : Icc u0 u1 ⊆ Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (l : ℤ) (hσ : (l : ℝ) * ocTauPP α q Λ m ∈ Icc a b)
    (ha : 0 ≤ ocA α q Λ (m - 1))
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
    (c d : ℝ) (hac : (e⁻¹) ^ 2 * (ν * u0) ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * u1))
    (hblock : ∀ t ∈ Icc c d,
      ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hs : IsCoupledWeakSolutionPlane ν u0 u1 (streamVel (Φ m)) D K (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) f (fun _ _ => 0)
      (fun _ _ => 0) u w)
    (hTau : 0 ≤ ocTauPP α q Λ m) (yc0 : Vec 2) (tp : ℝ) (htp : tp ∈ Icc a b)
    (htime : c = (e⁻¹) ^ 2 * (ν * tp)) :
    let hK := fun j => (show K j ≤ Jchart + 1 by have hh := hKmax j; omega)
    let he0 : e ≠ 0 := (hρ.trans_le hρe).ne'
    let U := fun j => preparationWindowReferenceCellNativeCurve hprep hcover
      ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j) (hK j) ν e he0 yc (u j)
    let W := fun j => preparationWindowReferenceCellNativeCurve hprep hcover
      ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j + 1)
      (by have hh := hKmax j; omega) ν e he0 yc (w j)
    let Upre := fun j => preparationReferenceCellNativeCurve hprep hcover hTau ha
      (K j) (hK j) ν e he0 yc0 (u j) c
    let S := preparationReferenceCellTransitionFamilyLinearMap hprep hcover hTau ha K hK
      ((l : ℝ) * ocTauPP α q Λ m) hσ e he0 yc0 yc tp htp
    IsCoupledWeakSolutionPlane 1 c d (ocCellDrift α q Λ ζ m ν yc) D K
      (planeMetricSourceCoefficient K D
        (ocCellMetric α q Λ m (Φ (m - 1)) hφ l ν yc)
        (preparationReferenceCellSourceCoefficient F hφ ((l : ℝ) * ocTauPP α q Λ m)
          ν e (ocEpsilon q Λ (m - 1)) actual K yc))
      (S Upre) (fun _ _ => 0) (fun _ _ => 0) U W := by
  intro hK he0 U W Upre S
  have hb := preparation_window_reference_cell_natural_block_coupled_solution_of_pointwise_subwindow
    F h01 hsub ρ hρ K hdesc hD hprep hcover l hσ ha Kmax Jm hKmax hchart hmol
    Cm π hπ B hB hmeas hwmeas hΛ hm hseq ν e hν heScale hρe heE henv actual hT he
    yc f u w c d hac hcd hdb hblock hs
  have hid : S Upre = fun j => U j c := by
    funext j
    change preparationReferenceCellTransitionOperator hprep hcover hTau ha (K j) (hK j)
      ((l : ℝ) * ocTauPP α q Λ m) hσ e he0 yc0 yc tp htp
      (preparationReferenceCellNativeCurve hprep hcover hTau ha (K j) (hK j)
        ν e he0 yc0 (u j) c) = U j c
    rw [htime]
    exact preparationReferenceCellTransitionOperator_native_curve hprep hcover hTau ha
      (K j) (hK j) ((l : ℝ) * ocTauPP α q Λ m) hσ ν hν.ne' e he0 yc0 yc tp htp (u j)
  rw [hid]
  exact hb
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.Weighted AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual preparation data supply the quantitative source inputs for native
homogeneous stability, uniformly over the covered reference time. -/

section
universe u v w x

theorem preparation_window_reference_restart_retained_error
    (D Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
    ∀ (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
      [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
      (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hB : ∀ i j, 0 ≤ B i j),
      IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
      (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
      F.IsTimeMeasurable → (∀ p, Measurable (F.weight p)) →
      IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
        ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    ∀ σ ∈ Set.Icc tS tZ, ∀ (a b θ : ℝ),
      Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
      (∀ i, ∑ j, B i j ≤ θ) → (∀ j, ∑ i, B i j ≤ θ) →
    ∀ H : ℕ, F.HasDepthAtMost H →
    ∀ (ζ : ℝ → ℝ) (Bcover g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ)
      (CG : ℕ → ℝ) (y₀ : Vec 2)
      (_cov : IsWindowCover α q Λ m ζ Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀),
      1 ≤ Λ → IsFastProfile ζ → a ≤ b →
    ∀ (ic : Fin (P + 2)),
      Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
      max Kmax 1 ≤ qJ → g ≤ 1 / 4 → 2 ≤ D →
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let v := ocCellDrift α q Λ ζ m ν yc
    let r := ρ / ocEpsilon q Λ m
    let A := preparationReferenceCellSourceCoefficient F hφ σ
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    e = ocEpsilon q Λ m →
    ∀ (n : ℕ) (Cw : ℕ → ℝ) (ϖ : ℝ) (_W : ChartWeights G v a (b - a) ϖ 0 n Cw)
      (U₀ V₀ : ∀ i, PlaneHk Set.univ (K i) (h i))
      (_hUinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (U₀ i) ≠ ⊤)
      (_hVinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (V₀ i) ≠ ⊤)
      (U V : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Uw Vw : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      U₀ (fun _ _ => 0) (fun _ _ => 0) U Uw →
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      V₀ (fun _ _ => 0) (fun _ _ => 0) V Vw →
    ∀ t ∈ Set.Icc a b,
    let EinDiff := ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U₀ i - V₀ i)
    let Cjet := fun j => max (CG j) 0
    let Cactual := ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
      (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw))
    ∀ (Tret : ∀ i, PlaneHk Set.univ (K i) (h i)) (Aerr : ℝ≥0∞),
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (V i t - Tret i)) ≤ Aerr →
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U i t - Tret i)) ≤
      2 * (Cactual * EinDiff + Aerr) := by
  obtain ⟨Cprep, hCprep, hdata⟩ := preparation_window_reference_source_energy_data
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m Φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ _ _ _ P' Ctx F π hπ K hK actual B hB hprep hcover hmeas hwmeas henv
    σ hσ a b θ hsub hrow hcol H hdepth ζ Bcover g g0 strain B₀ lam Cb qJ CG y₀ cov
    hΛ hζ hab ic hwindow hqJ hg4 hD yc G v r A he
    n Cw ϖ W U₀ V₀ hUinit hVinit U V Uw Vw hU hV t ht EinDiff Cjet Cactual Tret Aerr herr
  obtain ⟨hfinite, hsmooth, hAm, hrowA, hcolA, hrank, hzero⟩ :=
    hdata α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
      F π hπ K hK actual B hB hprep hcover hmeas hwmeas henv
      σ hσ yc a b θ hsub hrow hcol H hdepth
  have heE' : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) := he ▸ heE
  have hr : ρ / e = r := by rw [he]
  rw [hr] at hfinite hrowA hcolA
  exact windowCover_restart_retained_endpoint_error hΛ hζ hφ cov heE' ic a b hab hwindow hqJ hg4
    K hK π hπ D H n hD Cw ϖ W A hfinite hsmooth hAm (Cprep * θ) hrowA hcolA
    (sourceDepthRank F H) hrank hzero U₀ hUinit U Uw V₀ hVinit V Vw hU hV t ht Tret Aerr herr
end

/-! Actual preparation data supply the quantitative source inputs for native
homogeneous stability, uniformly over the covered reference time. -/

section
universe u v w x

theorem preparation_reference_homogeneous_endpoint_energy
    (D Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
    ∀ (α q : ℝ) (Λ m : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
      [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (K : ι → ℕ) (_hK : ∀ i, K i ≤ Kmax)
      (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hB : ∀ i j, 0 ≤ B i j),
      IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
      F.IsTimeMeasurable → (∀ p, Measurable (F.weight p)) →
      IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
        ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    ∀ (a b θ : ℝ),
      Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
      (∀ i, ∑ j, B i j ≤ θ) → (∀ j, ∑ i, B i j ≤ θ) →
    ∀ H : ℕ, F.HasDepthAtMost H →
    ∀ (ζ : ℝ → ℝ) (Bcover g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ)
      (CG : ℕ → ℝ) (y₀ : Vec 2)
      (_cov : IsWindowCover α q Λ m ζ Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀),
      1 ≤ Λ → IsFastProfile ζ → a ≤ b →
    let ic := windowCoverReferenceChartIndex P
    Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
      max Kmax 1 ≤ qJ → g ≤ 1 / 4 → 2 ≤ D →
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let v := ocCellDrift α q Λ ζ m ν yc
    let r := ρ / ocEpsilon q Λ m
    let A := preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    e = ocEpsilon q Λ m →
    ∀ (n : ℕ) (Cw : ℕ → ℝ) (ϖ : ℝ) (_W : ChartWeights G v a (b - a) ϖ 0 n Cw)
      (U₀ : ∀ i, PlaneHk Set.univ (K i) (h i))
      (_hUinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (U₀ i) ≠ ⊤)
      (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Uw : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      U₀ (fun _ _ => 0) (fun _ _ => 0) U Uw →
    ∀ t ∈ Set.Icc a b,
    let Ein := ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U₀ i)
    let Cjet := fun j => max (CG j) 0
    let Cactual := ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
      (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw))
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U i t)) ≤
      Cactual * Ein := by
  obtain ⟨Cprep, hCprep, hdata⟩ := preparation_reference_source_energy_data
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m Φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ _ _ _ P' Ctx F π hπ K hK actual B hB hprep hmeas hwmeas henv
    a b θ hsub hrow hcol H hdepth ζ Bcover g g0 strain B₀ lam Cb qJ CG y₀ cov
    hΛ hζ hab ic hwindow hqJ hg4 hD yc G v r A he
    n Cw ϖ W U₀ hUinit U Uw hU t ht Ein Cjet Cactual
  obtain ⟨hfinite, hsmooth, hAm, hrowA, hcolA, hrank, hzero⟩ :=
    hdata α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
      F π hπ K hK actual B hB hprep hmeas hwmeas henv
      yc a b θ hsub hrow hcol H hdepth
  have heE' : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) := he ▸ heE
  have hr : ρ / e = r := by rw [he]
  rw [hr] at hfinite hrowA hcolA
  simpa only [Cactual, Ein, mul_assoc] using
    windowCover_homogeneous_endpoint_energy hΛ hζ hφ cov heE' ic a b hab hwindow hqJ hg4
    K hK π hπ D H n hD Cw ϖ W A hfinite hsmooth hAm (Cprep * θ) hrowA hcolA
    (sourceDepthRank F H) hrank hzero U₀ hUinit U Uw hU t ht
end

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

/-- Finite prepared polynomial data yield the genuine physical and periodized homogeneous solutions. -/
theorem exists_actualPreparation_homogeneous_plane_and_torus (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ ν : ℝ) (hρ : 0 < ρ) (hν : 0 < ν)
    (a b : ℝ) (hab : a ≤ b)
    (D : ℕ) {P' : Type*} {Ctx : P' → Type*}
    (family : ChartedFamily ι h D P' Ctx) (H : ℕ) (hdepth : family.HasDepthAtMost H)
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
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2)
    (hf : ∀ i, weightedFactorialNormSq 4 ϖ z ρ (K i) (f i) ≠ ⊤) :
    ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (U : ∀ i, ℝ → TorusHk (K i) (h i)) (W : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν a b (streamVel (Φ m)) D K
        (edgeCoefficient family ν e E actual K) f (fun _ _ => 0) (fun _ _ => 0) u w ∧
      geometryEnergyNorm π K 4 ϖ z ρ a b u w < ⊤ ∧
      IsPeriodizedFamilyPair K a b u w U W ∧
      IsCoupledWeakSolutionTorus ν a b (streamVel (Φ m)) D K
        (edgeCoefficient family ν e E actual K) (fun i => U i a)
        (fun _ _ => 0) (fun _ _ => 0) U W := by
  let B := fun v u => Real.sqrt (π u / π v) * A v u
  have hB (v u : ι) : 0 ≤ B v u := mul_nonneg (Real.sqrt_nonneg _) (hA v u)
  obtain ⟨u, w, hs, henergy⟩ := exists_actualPreparation_homogeneous_plane_with_energy
    K Kmax hK ρ ν hρ hν a b hab D family H hdepth α q Λ m Φ ζ hΦ φ hφ
    Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual hmeas hwmeas hE hρe heE
    Jm hchart hmol Cm π hπ B hB hpointwise f 4 ϖ z hf
  obtain ⟨U, W, hpair, hcell⟩ := exists_actualPreparation_periodizedHomogeneous_solution
    K Kmax hK ρ ν hρ hν a b hab D family α q Λ m Φ ζ hζ hΦ φ hφ
    Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual hmeas hwmeas hE hρe heE
    Jm hchart hmol Cm π hπ A hA he htorus hpointwise f u w hs ϖ hϖ z henergy
  exact ⟨u, w, U, W, hs, henergy, hpair, hcell⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual-cover coupled error estimate has a retained endpoint linear in
the initial datum. Its scalar response construction and the coupled error
construction agree through their common all-moment carrier and continuous traces. -/

section
universe u v w x y

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance coverRetainedAllMomentsEndpointNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance coverRetainedAllMomentsEndpointNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance coverRetainedAllMomentsEndpointFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance coverRetainedAllMomentsEndpointFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance coverRetainedAllMomentsEndpointScalarCarrierAdd (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverRetainedAllMomentsEndpointScalarCarrierModule (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverRetainedAllMomentsEndpointFluxCarrierAdd (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance coverRetainedAllMomentsEndpointFluxCarrierModule (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem windowCover_retained_actualTaylor_linear_endpoint_all_moments_bound
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
      (ic : Fin (Pcover + 2)) (ta tb : ℝ) (_ht : ta < tb)
      (_hwindow : Set.Icc ta tb ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ Pcover ic)
      (_hqJ : Ks + 1 + Kmax ≤ qJ) (_hg4 : g ≤ 1 / 4)
      (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4)
      (_hlength : tb - ta ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2),
    ∀ (rstar δ : ℝ) (v : ℝ → Vec 2 → Vec 2)
      (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (_hrstarCover : rstar = ρs / ocEpsilon q Λ m)
      (_hδCover : δ = ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
      (_hvCell : v = ocCellDrift α q Λ ζfast m ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀ ic))
      (_hGCell : G = windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ Pcover ν y₀ ic),
    ∀ {X : Type y} [AddCommGroup X] [Module ℝ X],
    ∀ (n D H N : ℕ) (Cw : ℕ → ℝ) (Cprep Cgraph θsrc : ℝ), 0 ≤ θsrc →
      ∀ (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ϖ : ℝ)
        (_hϖCover : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
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
        (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (Kslot i) (h i)))
        (_hf : ∀ ξ r i, weightedFactorialNormSq r ϖ 0 rstar (Kslot i) (V₀ ξ i) ≠ ⊤)
        (uH : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (wH : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
        (_hH : ∀ ξ, IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
          (planeMetricSourceCoefficient Kslot D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0) (uH ξ) (wH ξ))
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
        (u0 : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (w0 : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
        (Z : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))))
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
    (_hbase : ∀ ξ, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => Kslot i) ta tb v
      (fun _ i => V₀ ξ i) (fun _ _ _ => 0) (fun _ i => u0 ξ i) (fun _ i => w0 ξ i))
    (_hZ : ∀ ξ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0 (volume.restrict (Set.Icc ta tb))
      (Z ξ i) (w0 ξ i))
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
        (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
        (τ : ℝ) (_hτ : τ ∈ Set.Icc ta tb),
        let C := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
        let cm := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2)
        let cs := ENNReal.ofReal ((Cgraph * θsrc) ^ 2)
        let ct := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)
        let θcap := ENNReal.ofReal θsrc
        let ζ := ENNReal.ofReal ζslow
        let η := ENNReal.ofReal (Cterminal * g * ζslow)
        let G0 := fun ξ => ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} N Kmax Cw) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 rstar (Kslot i) (V₀ ξ i)
        let U := fun ξ => finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
          (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) (Z ξ)
        let Wret := fun ξ => ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U ξ j k
        let Tret := fun ξ => ∑ k ∈ Finset.range (H + 1), U ξ J k
        let Q := fun ξ i => Lmetric i (Wret ξ i) + nativeFamilyEdgeForcingMap Ledge i (Wret ξ) - Lmetric i (Tret ξ i)
        ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (Kslot i) (h i)),
        (∀ ξ r i, weightedFactorialNormSq r ϖ 0 rstar (Kslot i) (T ξ i) ≠ ⊤) ∧
        ∀ ξ, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
          (ferr : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i))),
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A) (fun _ => 0) ferr (fun _ _ => 0)
            (fun i t => uH ξ i t - u i t) (fun i t => wH ξ i t - w i t) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb))
            (-(Q ξ i - Lfull i (Wret ξ) + Ldiag i (Wret ξ))) (ferr i)) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Wret ξ i) (w i)) ∧
          (∀ i, T ξ i = u i τ) ∧
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (uH ξ i τ - T ξ i)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θsrc)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζ ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0 ξ)) := by
  dsimp only
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hendpoint⟩ :=
    windowCover_retained_actualTaylor_initial_data_endpoint_bound.{u, v, w, x} Ks Kmax CG
  refine ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, ?_⟩
  intro ι _ h _ _ _ _ _ _ α q Λ m ζfast hζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb
    qJ l₀ Pcover y₀ cov hΛ heE ic ta tb ht hwindow hqJ hg4 hgsmall hg0 hlength
    rstar δ v G hrstarCover hδCover hvCell hGCell X _ _
    n D H N Cw Cprep Cgraph θsrc hθsrc π hπ Kslot hKslot
    ϖ hϖCover W hD A hA hc hAm hrow hcol rank hrank hzero V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z
    P Ctx family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ Lfull Ldiag hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM
    L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve hrem hgain hN τ hτ
  classical
  have hMcover : M = fun t =>
      windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ Pcover ν y₀ ic t 0 := by
    rw [hMcenter, hGCell]
  obtain ⟨hdiagA, hdiagCall⟩ := windowCover_frozen_metric_order_data
    (h := h) hφ cov ic ta tb hwindow Kslot D rstar
  dsimp only at hdiagA hdiagCall
  have hMfield : (fun (_ : ι) t (_ : Vec 2) => M t - 1) =
      (fun (_ : ι) t (_ : Vec 2) =>
        windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ Pcover ν y₀ ic t 0 - 1) := by
    rw [hMcover]
  rw [← hMfield] at hdiagA hdiagCall
  have hdiagC := fun i j d t (_ht : t ∈ Set.Icc ta tb) => hdiagCall i j d t
  obtain ⟨hnear, _, _, hsym, hsmooth, hjets⟩ :=
    windowCover_native_metric_data hΛ hφ cov ic ta tb hwindow
  rw [← hGCell] at hnear hsym hsmooth hjets
  have hqmetric : max Kmax 1 ≤ qJ := by omega
  have hδnonneg : 0 ≤ ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) :=
    div_nonneg (Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).le
      (Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ).le
  obtain ⟨hfullA, hfullC⟩ := planeMetricSource_coefficient_data_of_window_metric_envelope
    Kslot Kmax D hKslot rstar ta tb ht.le G A hA hc (fun r => max (CG r) 0)
    g (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) cov.g_range.1 hδnonneg hg4 hnear
    (fun t _ht z => hsym t z)
    (fun t ht k l => (hsmooth t ht k l).of_le (by exact_mod_cast hqmetric))
    (fun t ht z j hj hjmax k l => hjets t ht z j hj (hjmax.trans (by omega)) k l)
  have hMdegree := nativeDiagonalResponseOperator_sourceDegree family R Lmetric
  have hSdegree := nativeRawOriginalFamilyMap_response_sourceDegree family Kslot ϖ rstar 0
    (volume.restrict (Set.Icc ta tb)) Hraw hHzero (nativeFamilyEdgeForcingMap Ledge) hTaylorRaw R
  obtain ⟨T, hT⟩ := windowCover_finite_mixed_endpoint_all_moments
    M v Kslot ta tb ϖ rstar R (fun i => (Lmetric i).comp (LinearMap.proj i))
    (nativeFamilyEdgeForcingMap Ledge) V₀ u0 w0 Z family H J hdepth hMdegree hSdegree
    hR hbase hZ ht τ hτ
    α q Λ m ζfast Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ Pcover y₀
    cov hΛ hζ hKslot ic hwindow hgsmall hg0 hlength hϖCover hrstarCover
    (by simpa only [windowCoverCellMetric] using hMcover) hvCell hf
  refine ⟨T, ?_, ?_⟩
  · intro ξ
    obtain ⟨_, _, _, _, _, _, _, hfinite⟩ := hT ξ
    exact hfinite
  intro ξ
  obtain ⟨FT, uT, wT, hTs, hTW, _hFT, hTV, _hfinite⟩ := hT ξ
  obtain ⟨ur, wr, ferr, herr, hferr, hwr, hbound⟩ := hendpoint (ι := ι) (h := h)
    α q Λ m ζfast hζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ l₀ Pcover y₀ cov
    hΛ heE ic ta tb ht.le hwindow hqJ hg4 rstar δ v G hrstarCover hδCover hvCell hGCell
    n D H N Cw Cprep Cgraph θsrc hθsrc π hπ Kslot hKslot
    ϖ W hD A hA hc hAm hrow hcol rank hrank hzero (V₀ ξ) (hf ξ n) (uH ξ) (wH ξ) (hH ξ)
    M R Lmetric Ledge (u0 ξ) (w0 ξ) (Z ξ) hdiagA hfullA hdiagC hfullC
    family J hdepth Hraw hHzero hTaylorRaw hR (hbase ξ) (hZ ξ) Lfull Ldiag hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM
    L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve hrem hgain hN
  let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
    (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) (Z ξ)
  let Wret := ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U j k
  have hwT : ∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0
      (volume.restrict (Set.Icc ta tb)) (Wret i) (wT i) := by
    have hmetric : nativeComponentResponseOperator R
        (fun i => (Lmetric i).comp (LinearMap.proj i)) =
        nativeDiagonalResponseOperator R Lmetric := by
      ext f i
      rfl
    rw [hmetric] at hTW
    simpa only [Wret, U, LinearMap.comp_apply, LinearMap.sum_apply,
      finiteResponseOperator_apply] using hTW
  have htrace := planeRetained_endpoint_trace_identification 1 ta tb ϖ rstar ht v D Kslot
    (planeMetricSourceCoefficient Kslot D G A) (V₀ ξ) ferr FT (uH ξ) ur uT (wH ξ) wr wT
    M Wret (hH ξ) herr hTs hwr hwT
  have hTx (i : ι) : T ξ i = ur i τ := (hTV i).trans (htrace i hτ)
  refine ⟨ur, wr, ferr, herr, hferr, hwr, hTx, ?_⟩
  simpa only [hTx] using hbound τ hτ
end

/-! The primitive central, Taylor, original-edge and remainder maps construct
the full native feedback and its genuine coupled error estimate. -/

section
universe u v w x y

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance coverConstructedRetainedEndpointNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance coverConstructedRetainedEndpointNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance coverConstructedRetainedEndpointFluxNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance coverConstructedRetainedEndpointFluxNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance coverConstructedRetainedEndpointScalarCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverConstructedRetainedEndpointScalarCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverConstructedRetainedEndpointFluxCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance coverConstructedRetainedEndpointFluxCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem windowCover_constructed_retained_actualTaylor_linear_endpoint_all_moments_bound
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
      (ic : Fin (Pcover + 2)) (ta tb : ℝ) (_ht : ta < tb)
      (_hwindow : Set.Icc ta tb ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ Pcover ic)
      (_hqJ : Ks + 1 + Kmax ≤ qJ) (_hg4 : g ≤ 1 / 4)
      (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4)
      (_hlength : tb - ta ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2),
    ∀ (rstar δ : ℝ) (v : ℝ → Vec 2 → Vec 2)
      (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (_hrstarCover : rstar = ρs / ocEpsilon q Λ m)
      (_hδCover : δ = ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
      (_hvCell : v = ocCellDrift α q Λ ζfast m ν
        (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀ ic))
      (_hGCell : G = windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ Pcover ν y₀ ic),
    ∀ {X : Type y} [AddCommGroup X] [Module ℝ X],
    ∀ (n D H N : ℕ) (Cw : ℕ → ℝ) (Cprep Cgraph θsrc : ℝ), 0 ≤ θsrc →
      ∀ (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ϖ : ℝ)
        (_hϖCover : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
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
        (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (Kslot i) (h i)))
        (_hf : ∀ ξ r i, weightedFactorialNormSq r ϖ 0 rstar (Kslot i) (V₀ ξ i) ≠ ⊤)
        (uH : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (wH : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
        (_hH : ∀ ξ, IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
          (planeMetricSourceCoefficient Kslot D G A) (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0) (uH ξ) (wH ξ))
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
        (u0 : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (w0 : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
        (Z : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))))
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
    (_hbase : ∀ ξ, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => Kslot i) ta tb v
      (fun _ i => V₀ ξ i) (fun _ _ _ => 0) (fun _ i => u0 ξ i) (fun _ i => w0 ξ i))
    (_hZ : ∀ ξ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0 (volume.restrict (Set.Icc ta tb))
      (Z ξ i) (w0 ξ i))
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
        (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
        (τ : ℝ) (_hτ : τ ∈ Set.Icc ta tb),
        let Lfull := nativeMetricSourceFiveTermForcingMap diag Lmetric Ledge Rmetric Rs
        let Ldiag := nativeDiagonalForcingMap diag
        let C := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph))
        let cm := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2)
        let cs := ENNReal.ofReal ((Cgraph * θsrc) ^ 2)
        let ct := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)
        let θcap := ENNReal.ofReal θsrc
        let ζ := ENNReal.ofReal ζslow
        let η := ENNReal.ofReal (Cterminal * g * ζslow)
        let G0 := fun ξ => ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} N Kmax Cw) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 rstar (Kslot i) (V₀ ξ i)
        let U := fun ξ => finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
          (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) (Z ξ)
        let Wret := fun ξ => ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), U ξ j k
        let Tret := fun ξ => ∑ k ∈ Finset.range (H + 1), U ξ J k
        let Q := fun ξ i => Lmetric i (Wret ξ i) + nativeFamilyEdgeForcingMap Ledge i (Wret ξ) - Lmetric i (Tret ξ i)
        ∃ T : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (Kslot i) (h i)),
        (∀ ξ r i, weightedFactorialNormSq r ϖ 0 rstar (Kslot i) (T ξ i) ≠ ⊤) ∧
        ∀ ξ, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
          (w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
          (ferr : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i))),
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A) (fun _ => 0) ferr (fun _ _ => 0)
            (fun i t => uH ξ i t - u i t) (fun i t => wH ξ i t - w i t) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb))
            (-(Q ξ i - Lfull i (Wret ξ) + Ldiag i (Wret ξ))) (ferr i)) ∧
          (∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Wret ξ i) (w i)) ∧
          (∀ i, T ξ i = u i τ) ∧
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (uH ξ i τ - T ξ i)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θsrc)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζ ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0 ξ)) := by
  dsimp only
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hendpoint⟩ :=
    windowCover_retained_actualTaylor_linear_endpoint_all_moments_bound.{u, v, w, x, y} Ks Kmax CG
  refine ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, ?_⟩
  intro ι _ h _ _ _ _ _ _ α q Λ m ζfast hζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb
    qJ l₀ Pcover y₀ cov hΛ heE ic ta tb ht hwindow hqJ hg4 hgsmall hg0 hlength
    rstar δ v G hrstarCover hδCover hvCell hGCell X _ _
    n D H N Cw Cprep Cgraph θsrc hθsrc π hπ Kslot hKslot
    ϖ hϖCover W hD A hA hc hAm hrow hcol rank hrank hzero V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z P Ctx family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM
    L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve hrem hgain hN τ hτ
  classical
  have hDiagG := hDiagComponent
  rw [hMcenter] at hDiagG
  have hfull := planeMetricSource_originalEdge_allMoment_map_construction
    Kslot Ks D hD ϖ rstar (volume.restrict (Set.Icc ta tb)) G A Ledge Rs
    diag Lmetric Rmetric hSourceRaw hDiagG hPositive hMetricRemainder
  have hdiag := planeDiagonal_allMoment_family_map Kslot D hD ϖ rstar
    (volume.restrict (Set.Icc ta tb)) M diag hDiagComponent
  exact hendpoint (ι := ι) (h := h)
    α q Λ m ζfast hζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ l₀ Pcover y₀ cov
    hΛ heE ic ta tb ht hwindow hqJ hg4 hgsmall hg0 hlength rstar δ v G hrstarCover hδCover hvCell hGCell
    n D H N Cw Cprep Cgraph θsrc hθsrc π hπ Kslot hKslot
    ϖ hϖCover W hD A hA hc hAm hrow hcol rank hrank hzero V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z family J hdepth Hraw hHzero hTaylorRaw hR hbase hZ
    (nativeMetricSourceFiveTermForcingMap diag Lmetric Ledge Rmetric Rs)
    (nativeDiagonalForcingMap diag) hfull hdiag
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM
    L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve hrem hgain hN τ hτ
end

end AVRegularity.CycleJointProofs
end
end
