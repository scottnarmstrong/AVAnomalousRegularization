-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.WindowCoverConstructedRetainedActualTaylorLinearEndpointAllMomentsBound
import AVRegularity.CycleJoint.ActualPreparationHomogeneousPlaneExistence
public import AVRegularity.CycleJoint.PreparationTransportedWeightedPolynomialAllMomentMap
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
import AVRegularity.CycleJoint.WindowCoverFrozenHomogeneousFamilyLinearMap
import AVRegularity.CycleJoint.PlaneMetricSourceAllMomentMapConstruction
import AVRegularity.CycleJoint.ActualPreparationHomogeneousFamilyNativeTraceLinearMap
import Mathlib.Algebra.Order.Star.Real

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

/-- Arbitrary torus data admit the actual homogeneous preparation solution via the unit-patch transfer. -/
theorem exists_actualPreparation_torus_solution (K : ι → ℕ) (Kmax : ℕ)
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
    (f : ∀ i, TorusHk (K i) (h i))
    (ϖ : ℝ) (hϖ : 0 < ϖ) :
    ∃ (U : ∀ i, ℝ → TorusHk (K i) (h i)) (W : ∀ i, ℝ → TorusHk (K i + 1) (h i)),
      IsCoupledWeakSolutionTorus ν a b (streamVel (Φ m)) D K
        (edgeCoefficient family ν e E actual K) f (fun _ _ => 0) (fun _ _ => 0) U W := by
  let fP := fun i => spatialPatchLocalization hζ 1 (by decide) 0 (K i) (f i)
  have hfP (i : ι) : weightedFactorialNormSq 4 ϖ 0 ρ (K i) (fP i) ≠ ⊤ :=
    unitPatchLocalization_weightedFactorialNormSq_ne_top hζ (f i) ρ 4 ϖ hϖ.le
  obtain ⟨u, w, U, W, hs, _, hp, hcell⟩ := exists_actualPreparation_homogeneous_plane_and_torus
    K Kmax hK ρ ν hρ hν a b hab D family H hdepth α q Λ m Φ ζ hζ hΦ φ hφ
    Cpad Cage Npad Jchart Cchart l₀ P hprep e E actual hmeas hwmeas hE hρe heE
    Jm hchart hmol Cm π hπ A hA he htorus hpointwise fP ϖ hϖ 0 hfP
  have hinit : (fun i => U i a) = f := by
    funext i
    exact periodizedUnitPatch_initial_trace hζ K a b hab f u w U W hs.2.2.2.1 hp i
  rw [hinit] at hcell
  exact ⟨U, W, hcell⟩

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

universe u v w x

theorem preparation_following_mixed_seam_retained_error
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
    ∀ (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
      (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output),
      F.IsTimeMeasurable → (∀ p, Measurable (F.weight p)) →
      IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
        ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    ∀ (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Set.Icc tS tZ)
      (a b θ : ℝ),
      Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) →
      (∀ i, ∑ j, B i j ≤ θ) → (∀ j, ∑ i, B i j ≤ θ) →
    ∀ H : ℕ, F.HasDepthAtMost H →
    ∀ (ζ : ℝ → ℝ) (Bcover g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ)
      (CG : ℕ → ℝ) (y₀ : Vec 2)
      (cov : IsWindowCover α q Λ m ζ Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
      (hΛ : 128 ≤ Λ), IsFastProfile ζ → a ≤ b →
    let ic := windowCoverFollowingChartIndex P cov.P_pos
    Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
      max Kmax 1 ≤ qJ → g ≤ 1 / 4 → 2 ≤ D →
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let v := ocCellDrift α q Λ ζ m ν yc
    let r := ρ / ocEpsilon q Λ m
    let σ := ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m
    let A := preparationReferenceCellSourceCoefficient F hφ σ
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    e = ocEpsilon q Λ m →
    ∀ (s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      IsAdmissibleQ α s q → IsOCStreamSeq α q Λ ζ Φ → 1 ≤ m →
    ∀ (ha : 0 ≤ ocA α q Λ (m - 1)) (tp : ℝ) (htp : tp ∈ Set.Icc tS tZ),
    let hΛ1 : 1 ≤ Λ := (by omega)
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc0 := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let S := preparationReferenceCellTransitionFamilyLinearMap hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ1).le ha K (fun i => by have hh := _hK i; omega)
      σ hnext (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc0 yc tp htp
    ∀ (n : ℕ) (Cw : ℕ → ℝ) (ϖ : ℝ) (_W : ChartWeights G v a (b - a) ϖ 0 n Cw)
      (Upre Tpre : ∀ i, PlaneHk Set.univ (K i) (h i))
      (_hUinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (Upre i) ≠ ⊤)
      (_hTinit : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (Tpre i) ≠ ⊤)
      (U V : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Uw Vw : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      (S Upre) (fun _ _ => 0) (fun _ _ => 0) U Uw →
    IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      (S Tpre) (fun _ _ => 0) (fun _ _ => 0) V Vw →
    ∀ t ∈ Set.Icc a b,
    let EinPre := ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (Upre i - Tpre i)
    let Cjet := fun j => max (CG j) 0
    let Cactual := ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
      (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw))
    ∀ (Tret : ∀ i, PlaneHk Set.univ (K i) (h i)) (Aerr : ℝ≥0∞),
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (V i t - Tret i)) ≤ Aerr →
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (U i t - Tret i)) ≤
      2 * (Cactual * (ENNReal.ofReal (cellTransitionMomentBudget Kmax n) * EinPre) + Aerr) := by
  obtain ⟨Cprep, hCprep, hbase⟩ := preparation_window_reference_restart_retained_error
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m Φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ _ _ _ P' Ctx F π hπ K hK actual B hB hprep hcover hmeas hwmeas henv
    hnext a b θ hsub hrow hcol H hdepth ζ Bcover g g0 strain B₀ lam Cb qJ CG y₀ cov hΛ
    hζ hab ic hwindow hqJ hg4 hD yc G v r σ A he
    s hα0 hα1 hs0 hs1 hq hseq hm ha tp htp hΛ1 seed yc0 S
    n Cw ϖ W Upre Tpre hUinit hTinit U V Uw Vw hU hV t ht EinPre Cjet Cactual Tret Aerr herr
  have hKchart (i : ι) : K i ≤ Jchart + 1 := by have hh := hK i; omega
  have hr : 0 ≤ r := (div_pos hρ (Construction.Stream.ocEpsilon_pos hΛ1)).le
  have hr1 : r ≤ 1 := (div_le_one₀ (Construction.Stream.ocEpsilon_pos hΛ1)).mpr (he ▸ hρe)
  have hfinite (Z : ∀ i, PlaneHk Set.univ (K i) (h i))
      (hZ : ∀ i, weightedFactorialNormSq n ϖ 0 r (K i) (Z i) ≠ ⊤) (i : ι) :
      weightedFactorialNormSq n ϖ 0 r (K i) (S Z i) ≠ ⊤ := by
    exact preparationReferenceCellTransitionOperator_renewal_polynomial_energy_ne_top
      hprep hcover (Construction.Stream.ocTauPP_pos hΛ1).le ha (K i) (hKchart i)
      s hα0 hα1 hs0 hs1 hq hζ hΛ hseq hm hnext ν hν.ne'
      (Construction.Stream.ocEpsilon_pos hΛ1).ne' y₀ (Z i) tp htp n n Kmax le_rfl (hK i)
      ϖ r hr hr1 (hZ i)
  have hprice := preparationReferenceCellTransitionFamilyLinearMap_renewal_difference_energy_le
    hprep hcover (Construction.Stream.ocTauPP_pos hΛ1).le ha K hKchart
    s hα0 hα1 hs0 hs1 hq hζ hΛ hseq hm hnext ν hν.ne'
    (Construction.Stream.ocEpsilon_pos hΛ1).ne' y₀ Upre Tpre π tp htp n n Kmax le_rfl hK ϖ r hr hr1
  have hh := hbase α q Λ m Φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hprep hcover hmeas hwmeas henv σ hnext
    a b θ hsub hrow hcol H hdepth ζ Bcover g g0 strain B₀ lam Cb qJ CG y₀ cov
    hΛ1 hζ hab ic hwindow hqJ hg4 hD he n Cw ϖ W (S Upre) (S Tpre)
    (hfinite Upre hUinit) (hfinite Tpre hTinit) U V Uw Vw hU hV t ht Tret Aerr herr
  change (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i)
    (S Upre i - S Tpre i)) ≤ ENNReal.ofReal (cellTransitionMomentBudget Kmax n) * EinPre at hprice
  exact hh.trans (mul_le_mul_right
    (add_le_add (mul_le_mul_right hprice Cactual) (le_refl Aerr)) 2)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The linear homogeneous family response is constructed before the datum,
and supplies the base of the genuine retained coupled error estimate. -/

universe u v w x y

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance coverHomogeneousRetainedEndpointNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance coverHomogeneousRetainedEndpointNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance coverHomogeneousRetainedEndpointFluxNativeNormedAllMoments (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance coverHomogeneousRetainedEndpointFluxNativeModuleAllMoments (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

local instance coverHomogeneousRetainedEndpointScalarCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverHomogeneousRetainedEndpointScalarCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance coverHomogeneousRetainedEndpointFluxCarrierAddAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance
local instance coverHomogeneousRetainedEndpointFluxCarrierModuleAllMoments (i : ι) (k : ℕ)
    (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
      k ϖ ρ 0 μ) := inferInstance

theorem windowCover_constructed_homogeneous_retained_linear_endpoint_all_moments_bound
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
      (_hqJ : Ks + 1 + Kmax ≤ qJ) (_hgsmall : 4 * g ≤ 1 / 8)
      (_hg0 : g0 ≤ 1 / 4) (_hlength : tb - ta ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2),
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
        (ϖ : ℝ) (_hϖCover : ϖ = ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
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
            (fun j => planeTimeAllMomentReadout (E := h j) (Kslot j + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) (X j) t) i)
          (nativeFamilyEdgeForcingMap Ledge i + Rs i))
        (_hDiagComponent : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun _ => M t - 1)
            (planeTimeAllMomentReadout (E := h i) (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (diag i))
        (_hPositive : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentReadout (E := h i) (Kslot i + 1) ϖ rstar 0
              (volume.restrict (Set.Icc ta tb)) X t)) (Lmetric i))
        (_hMetricRemainder : ∀ i, IsPlaneTimeAllMomentRawLinearMap (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))
          (fun X t => planeMatrixGradientFlux
            (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
            (planeTimeAllMomentReadout (E := h i) (Kslot i + 1) ϖ rstar 0
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
        ∃ u0 : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i),
        ∃ w0 : X → ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i),
        ∃ Z : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb))),
        (∀ ξ, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => Kslot i) ta tb v
      (fun _ i => V₀ ξ i) (fun _ _ _ => 0) (fun _ i => u0 ξ i) (fun _ i => w0 ξ i)) ∧
        (∀ ξ i, PlaneTimeAllMomentRepresents (E := h i) (Kslot i + 1) ϖ rstar 0 (volume.restrict (Set.Icc ta tb))
      (Z ξ i) (w0 ξ i)) ∧
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
          (∀ i, PlaneTimeAllMomentRepresents (E := PiLp 2 (fun _ : Fin 2 => h i)) (Kslot i) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb))
            (-(Q ξ i - Lfull i (Wret ξ) + Ldiag i (Wret ξ))) (ferr i)) ∧
          (∀ i, PlaneTimeAllMomentRepresents (E := h i) (Kslot i + 1) ϖ rstar 0
            (volume.restrict (Set.Icc ta tb)) (Wret ξ i) (w i)) ∧
          (∀ i, T ξ i = u i τ) ∧
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (uH ξ i τ - T ξ i)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θsrc)) ^ (2 * H)) *
            (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) * (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
              (ζ ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0 ξ)) := by
  dsimp only
  obtain ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, hendpoint⟩ :=
    windowCover_constructed_retained_actualTaylor_linear_endpoint_all_moments_bound.{u, v, w, x, y} Ks Kmax CG
  refine ⟨CT, CR, Cterminal, hCT, hCR, hCterminal, ?_⟩
  intro ι _ h _ _ _ _ _ _ α q Λ m ζfast hζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb
    qJ l₀ Pcover y₀ cov hΛ heE ic ta tb ht hwindow hqJ hgsmall hg0 hlength
    rstar δ v G hrstarCover hδCover hvCell hGCell X _ _
    n D H N Cw Cprep Cgraph θsrc hθsrc π hπ Kslot hKslot
    ϖ hϖCover W hD A hA hc hAm hrow hcol rank hrank hzero V₀ hf uH wH hH
    M R Lmetric Ledge P Ctx family J hdepth Hraw hHzero hTaylorRaw hR
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM
    L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve hrem hgain hN τ hτ
  classical
  subst rstar
  obtain ⟨Z, u0, w0, hbase⟩ := windowCover_frozen_homogeneous_family_linearMap
    hΛ hζ hφ cov Kslot hKslot ic ta tb ht hwindow hgsmall hg0 hlength ϖ hϖCover V₀
    hf
  have hbase' : ∀ ξ, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t))
      (fun _ i => Kslot i) ta tb v (fun _ i => V₀ ξ i) (fun _ _ _ => 0)
      (fun _ i => u0 ξ i) (fun _ i => w0 ξ i) := by
    intro ξ
    simpa only [hMcenter, hGCell, hvCell, windowCoverCellMetric] using (hbase ξ).1
  have hZ : ∀ ξ i, PlaneTimeAllMomentRepresents (E := h i) (Kslot i + 1) ϖ (ρs / ocEpsilon q Λ m) 0
      (volume.restrict (Set.Icc ta tb)) (Z ξ i) (w0 ξ i) := by
    exact fun ξ => (hbase ξ).2.1
  refine ⟨u0, w0, Z, hbase', hZ, ?_⟩
  exact hendpoint (ι := ι) (h := h)
    α q Λ m ζfast hζ Φ hφ ν B tA tZ ρs g g0 strain B₀ lam Cb qJ l₀ Pcover y₀ cov
    hΛ heE ic ta tb ht hwindow hqJ (by linarith only [hgsmall]) hgsmall hg0 hlength
    (ρs / ocEpsilon q Λ m) δ v G rfl hδCover hvCell hGCell
    n D H N Cw Cprep Cgraph θsrc hθsrc π hπ Kslot hKslot
    ϖ hϖCover W hD A hA hc hAm hrow hcol rank hrank hzero V₀ hf uH wH hH
    M R Lmetric Ledge u0 w0 Z family J hdepth Hraw hHzero hTaylorRaw hR hbase' hZ
    Rs diag Rmetric hMcenter hSourceRaw hDiagComponent hPositive hMetricRemainder WM
    L ζslow hL hζslow hζslow1 hϖ hscale hδslow hreserve hrem hgain hN τ hτ

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! A true homogeneous solution family transfers to any natural block with its linear seam datum constructed by uniqueness. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_cell_natural_block_coupled_solution_family_subwindow
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (H : ℕ) (hdepth : F.HasDepthAtMost H)
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
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (lf : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)))
    (u : X → ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : X → ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (c d : ℝ) (hac : (e⁻¹) ^ 2 * (ν * u0) ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * u1))
    (hblock : ∀ t ∈ Icc c d,
      ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hs : ∀ x, IsCoupledWeakSolutionPlane ν u0 u1 (streamVel (Φ m)) D K
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) (lf x)
      (fun _ _ => 0) (fun _ _ => 0) (u x) (w x)) :
    ∃ V0 : X →ₗ[ℝ] (∀ j, PlaneHk univ (K j) (h j)), ∀ x,
      IsCoupledWeakSolutionPlane 1 c d (ocCellDrift α q Λ ζ m ν yc) D K
        (planeMetricSourceCoefficient K D
          (ocCellMetric α q Λ m (Φ (m - 1)) hφ l ν yc)
          (preparationReferenceCellSourceCoefficient F hφ ((l : ℝ) * ocTauPP α q Λ m)
            ν e (ocEpsilon q Λ (m - 1)) actual K yc))
        (V0 x) (fun _ _ => 0) (fun _ _ => 0)
        (fun j => preparationWindowReferenceCellNativeCurve hprep hcover
          ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j)
          (by have hh := hKmax j; omega) ν e (hρ.trans_le hρe).ne' yc (u x j))
        (fun j => preparationWindowReferenceCellNativeCurve hprep hcover
          ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j + 1)
          (by have hh := hKmax j; omega) ν e (hρ.trans_le hρe).ne' yc (w x j)) := by
  have hepos : 0 < e := hρ.trans_le hρe
  let scale := ν⁻¹ * e ^ 2
  have hscale : 0 ≤ scale := mul_nonneg (inv_nonneg.mpr hν.le) (sq_nonneg e)
  have htime (t : ℝ) : scale * ((e⁻¹) ^ 2 * (ν * t)) = t := by
    dsimp only [scale]
    field_simp
  have htcsub : scale * c ∈ Icc u0 u1 := by
    constructor
    · calc u0 = scale * ((e⁻¹) ^ 2 * (ν * u0)) := (htime u0).symm
           _ ≤ scale * c := mul_le_mul_of_nonneg_left hac hscale
    · calc scale * c ≤ scale * ((e⁻¹) ^ 2 * (ν * u1)) :=
             mul_le_mul_of_nonneg_left (hcd.trans hdb) hscale
           _ = u1 := htime u1
  have htc : scale * c ∈ Icc a b := hsub htcsub
  obtain ⟨T, htrace⟩ := actualPreparation_homogeneous_subwindow_family_trace_linearMap K Kmax hKmax
    ρ ν hρ hν a b D F H hdepth α q Λ m Φ ζ hseq (Φ (m - 1)) hφ
    Cpad Cage Npad Jchart Cchart l₀ Pcover hprep e (ocEpsilon q Λ (m - 1)) actual
    hmeas hwmeas rfl hρe heE Jm hchart hmol Cm π hπ B hB henv u0 u1 (hsub ⟨le_rfl, h01⟩).1 h01
    (hsub ⟨h01, le_rfl⟩).2 lf u w hs (scale * c) htcsub
  have hK (j : ι) : K j ≤ Jchart + 1 := by have hh := hKmax j; omega
  let V0 := preparationWindowReferenceCellTraceLinearMap hprep hcover
    ((l : ℝ) * ocTauPP α q Λ m) hσ ha K hK e hepos.ne' yc (scale * c) htc T
  refine ⟨V0, ?_⟩
  intro x
  have hn := preparation_window_reference_cell_natural_block_coupled_solution_of_pointwise_subwindow
    F h01 hsub ρ hρ K hdesc hD hprep hcover l hσ ha Kmax Jm hKmax hchart hmol Cm π hπ B hB
    hmeas hwmeas hΛ hm hseq ν e hν heScale hρe heE henv actual hT he yc
    (lf x) (u x) (w x) c d hac hcd hdb hblock (hs x)
  have hinit : V0 x = fun j => planeCarrierAffine e hepos.ne' yc
      (preparationWindowReferenceHkWindowPull hprep hcover ((l : ℝ) * ocTauPP α q Λ m)
        hσ ha (K j) (hK j) (ν⁻¹ * (e ^ 2 * c)) (u x j (ν⁻¹ * (e ^ 2 * c)))) := by
    funext j
    dsimp only [V0]
    rw [preparationWindowReferenceCellTraceLinearMap_apply, htrace]
    simp only [scale, mul_assoc]
  rw [hinit]
  exact hn

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
open AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual natural-block initial linear map inherits all polynomial
 moments from its true native initial trace. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_cell_natural_block_all_moment_initial_family_subwindow
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (H : ℕ) (hdepth : F.HasDepthAtMost H)
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
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (lf : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)))
    (u : X → ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : X → ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (c d : ℝ) (hac : (e⁻¹) ^ 2 * (ν * u0) ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * u1))
    (hblock : ∀ t ∈ Icc c d,
      ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hs : ∀ x, IsCoupledWeakSolutionPlane ν u0 u1 (streamVel (Φ m)) D K
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) (lf x)
      (fun _ _ => 0) (fun _ _ => 0) (u x) (w x))
    (ϖ : ℝ)
    (hf : ∀ x n j, weightedFactorialNormSq n ϖ 0 (ρ / e) (K j)
      (preparationWindowReferenceCellNativeCurve hprep hcover
        ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j)
        (by have hh := hKmax j; omega) ν e (hρ.trans_le hρe).ne' yc (u x j) c) ≠ ⊤) :
    ∃ V0 : X →ₗ[ℝ] (∀ j, PlaneHk univ (K j) (h j)), (∀ x,
      IsCoupledWeakSolutionPlane 1 c d (ocCellDrift α q Λ ζ m ν yc) D K
        (planeMetricSourceCoefficient K D
          (ocCellMetric α q Λ m (Φ (m - 1)) hφ l ν yc)
          (preparationReferenceCellSourceCoefficient F hφ ((l : ℝ) * ocTauPP α q Λ m)
            ν e (ocEpsilon q Λ (m - 1)) actual K yc))
        (V0 x) (fun _ _ => 0) (fun _ _ => 0)
        (fun j => preparationWindowReferenceCellNativeCurve hprep hcover
          ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j)
          (by have hh := hKmax j; omega) ν e (hρ.trans_le hρe).ne' yc (u x j))
        (fun j => preparationWindowReferenceCellNativeCurve hprep hcover
          ((l : ℝ) * ocTauPP α q Λ m) hσ ha (K j + 1)
          (by have hh := hKmax j; omega) ν e (hρ.trans_le hρe).ne' yc (w x j))) ∧ ∀ x n j, weightedFactorialNormSq n ϖ 0 (ρ / e) (K j) (V0 x j) ≠ ⊤ := by
  obtain ⟨V0, hsol⟩ := preparation_window_reference_cell_natural_block_coupled_solution_family_subwindow
    F H hdepth h01 hsub ρ hρ K hdesc hD hprep hcover l hσ ha Kmax Jm hKmax hchart hmol
    Cm π hπ B hB hmeas hwmeas hΛ hm hseq ν e hν heScale hρe heE henv actual hT he yc
    lf u w c d hac hcd hdb hblock hs
  refine ⟨V0, hsol, ?_⟩
  intro x n j
  rw [← (hsol x).2.2.2.1 j]
  exact hf x n j

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
open AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A retained first-cell datum generates an actual physical restart and a
 following native coupled family. Its initial moments follow from the true
 mixed chart transition estimate, without using the true first-cell endpoint. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem exists_preparation_retained_restart_all_moment_coupled_family
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (H : ℕ) (hdepth : F.HasDepthAtMost H)
    {a b u0 u1 : ℝ} (h01 : u0 ≤ u1) (hsub : Icc u0 u1 ⊆ Icc a b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (hdesc : F.IsDescending K) (hD : 2 ≤ D)
    (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hσ : (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) ∈ Icc a b)
    (hTau : 0 ≤ ocTauPP α q Λ m)
    (ha : 0 ≤ ocA α q Λ (m - 1))
    (Kmax Jm : ℕ) (hKmax : ∀ j, K j ≤ Kmax)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (Cm : ℕ → ℝ) (π : ι → ℝ) (hπ : ∀ j, 0 < π j)
    (B : ι → ι → ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (hΛ : 128 ≤ Λ)
    (s : ℝ) (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ) (hm : 1 ≤ m) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (ν e : ℝ) (hν : 0 < ν) (heScale : e = ocEpsilon q Λ m) (hρe : ρ ≤ e)
    (heE : e ≤ ocEpsilon q Λ (m - 1))
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
    {N : ℕ} (he : e⁻¹ = N)
    (y0 : Vec 2)
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)))
    (ϖ : ℝ) (hTfinite : ∀ x n j, weightedFactorialNormSq n ϖ 0 (ρ / e) (K j) (T x j) ≠ ⊤) :
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y0
    let yc0 := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 2
    let c := (e⁻¹) ^ 2 * (ν * u0)
    ∀ (d : ℝ) (hcd : c ≤ d)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * u1))
    (_hblock : ∀ t ∈ Icc c d,
      ((((l₀ + 1 : ℤ) : ℝ)) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((((l₀ + 1 : ℤ) : ℝ)) + 1 / 2) * ocTauPP α q Λ m),
    let hKchart : ∀ j, K j ≤ Jchart + 1 := fun j => by have hh := hKmax j; omega
    let ht0 : u0 ∈ Icc a b := hsub ⟨le_rfl, h01⟩
    let lf := preparationReferenceRetainedEndpointLinearMap hprep hcover hTau ha K hKchart
      e (hρ.trans_le hρe).ne' yc0 u0 ht0 T
    ∃ (u : X → ∀ i, ℝ → PlaneHk univ (K i) (h i))
      (w : X → ∀ i, ℝ → PlaneHk univ (K i + 1) (h i)),
    (∀ x, IsCoupledWeakSolutionPlane ν u0 u1 (streamVel (Φ m)) D K
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) (lf x)
      (fun _ _ => 0) (fun _ _ => 0) (u x) (w x)) ∧
    ∃ V0 : X →ₗ[ℝ] (∀ j, PlaneHk univ (K j) (h j)), (∀ x,
      IsCoupledWeakSolutionPlane 1 c d (ocCellDrift α q Λ ζ m ν yc) D K
        (planeMetricSourceCoefficient K D
          (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + 1) ν yc)
          (preparationReferenceCellSourceCoefficient F hφ (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m)
            ν e (ocEpsilon q Λ (m - 1)) actual K yc))
        (V0 x) (fun _ _ => 0) (fun _ _ => 0)
        (fun j => preparationWindowReferenceCellNativeCurve hprep hcover
          (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hσ ha (K j)
          (by have hh := hKmax j; omega) ν e (hρ.trans_le hρe).ne' yc (u x j))
        (fun j => preparationWindowReferenceCellNativeCurve hprep hcover
          (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hσ ha (K j + 1)
          (by have hh := hKmax j; omega) ν e (hρ.trans_le hρe).ne' yc (w x j))) ∧ (∀ x n j, weightedFactorialNormSq n ϖ 0 (ρ / e) (K j) (V0 x j) ≠ ⊤) ∧
      (∀ x j, V0 x j = preparationReferenceCellTransitionOperator hprep hcover hTau ha
        (K j) (hKchart j) (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hσ
        e (hρ.trans_le hρe).ne' yc0 yc u0 ht0 (T x j)) ∧
      ∀ x n, (∑ j, ENNReal.ofReal ((π j)⁻¹) *
        weightedFactorialNormSq n ϖ 0 (ρ / e) (K j) (V0 x j)) ≤
        ENNReal.ofReal (cellTransitionMomentBudget Kmax n) *
          ∑ j, ENNReal.ofReal ((π j)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K j) (T x j) := by
  intro seed yc0 yc c d hcd hdb hblock hKchart ht0 lf
  have hepos : 0 < e := hρ.trans_le hρe
  obtain ⟨u, w, hs⟩ := exists_actualPreparation_planeWeakSolution_arbitrary_subwindow_family
    K Kmax hKmax ρ ν hρ hν a b D F H hdepth α q Λ m Φ ζ hseq (Φ (m - 1)) hφ
    Cpad Cage Npad Jchart Cchart l₀ Pcover hprep e (ocEpsilon q Λ (m - 1)) actual
    hmeas hwmeas rfl hρe heE Jm hchart hmol Cm π hπ B hB henv
    u0 u1 ht0.1 h01 (hsub ⟨h01, le_rfl⟩).2
    (fun _ _ => 0) (fun _ _ => 0)
    (fun _ => timeMemLp_zero _ _) (fun _ => timeIntegrable_zero _) lf
  refine ⟨u, w, hs, ?_⟩
  have hinit (x : X) (j : ι) :
      preparationWindowReferenceCellNativeCurve hprep hcover
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hσ ha (K j) (hKchart j)
        ν e hepos.ne' yc (u x j) c =
      preparationReferenceCellTransitionOperator hprep hcover hTau ha (K j) (hKchart j)
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hσ e hepos.ne' yc0 yc u0 ht0 (T x j) := by
    apply preparationWindowReferenceCellNativeCurve_returned_initial
      hprep hcover hTau ha (K j) (hKchart j)
      (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hσ ν hν.ne' e hepos.ne' yc0 yc u0 ht0
    exact (hs x).2.2.2.1 j
  have hf (x : X) (n : ℕ) (j : ι) :
      weightedFactorialNormSq n ϖ 0 (ρ / e) (K j)
        (preparationWindowReferenceCellNativeCurve hprep hcover
          (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hσ ha (K j) (hKchart j)
          ν e hepos.ne' yc (u x j) c) ≠ ⊤ := by
    rw [hinit]
    subst e
    exact preparationReferenceCellTransitionOperator_renewal_polynomial_energy_ne_top
      hprep hcover hTau ha (K j) (hKchart j) s hα0 hα1 hs0 hs1 hq hζ hΛ hseq hm
      hσ ν hν.ne' hepos.ne' y0 (T x j) u0 ht0 n n (K j) le_rfl le_rfl
      ϖ (ρ / ocEpsilon q Λ m) (div_nonneg hρ.le hepos.le)
      ((div_le_one₀ hepos).mpr hρe) (hTfinite x n j)
  obtain ⟨V0, hsol, hfinite⟩ := preparation_window_reference_cell_natural_block_all_moment_initial_family_subwindow
    F H hdepth h01 hsub ρ hρ K hdesc hD hprep hcover (l₀ + 1) hσ ha Kmax Jm hKmax
    hchart hmol Cm π hπ B hB hmeas hwmeas (by omega) hm hseq ν e hν heScale hρe heE
    henv actual hT he yc lf u w c d (le_refl _) hcd hdb hblock hs ϖ hf
  have hident (x : X) (j : ι) : V0 x j =
      preparationReferenceCellTransitionOperator hprep hcover hTau ha (K j) (hKchart j)
        (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hσ e hepos.ne' yc0 yc u0 ht0 (T x j) := by
    rw [← (hsol x).2.2.2.1 j]
    exact hinit x j
  refine ⟨V0, hsol, hfinite, hident, ?_⟩
  intro x n
  simp_rw [hident]
  subst e
  exact preparationReferenceCellTransitionOperator_renewal_family_energy_le
    hprep hcover hTau ha K hKchart s hα0 hα1 hs0 hs1 hq hζ hΛ hseq hm
    hσ ν hν.ne' hepos.ne' y0 (T x) π u0 ht0 n n Kmax le_rfl hKmax
    ϖ (ρ / ocEpsilon q Λ m) (div_nonneg hρ.le hepos.le)
    ((div_le_one₀ hepos).mpr hρe)

end AVRegularity.CycleJointProofs
end
end

section
/-! The actual first reference chart constructs the original-edge source maps,
metric Taylor maps and genuine component responses before the datum is selected. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

namespace AVRegularity.CycleJointProofs

theorem windowCover_reference_feedback_maps (D Kmax Jchart Jm : ℕ)
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
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (a b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P (windowCoverReferenceChartIndex P) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        ∀ (Ks : ℕ), F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        Ks + 1 + Kmax ≤ qJ → b - a ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
      (windowCoverReferenceChartIndex P)
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀
      (windowCoverReferenceChartIndex P)
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
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) ∧
    (∀ u, ∑ v, schurMatrix 1 (ρ / (ocEpsilon q Λ m)) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) := by
  obtain ⟨Cprep, hCprep, hmaps⟩ := windowCover_reference_constructed_edge_package
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m ζfast hζ Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha hgsmall hg0 hD ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc henv a b hab hwindow θ hrow hcol Ks hdesc hKs hθ hqJ hlength
  classical
  dsimp only
  let ic := windowCoverReferenceChartIndex P
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
  let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
  let A := preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
    ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc
  obtain ⟨Rs, Ledge, hsource, hrem, hmass, hrows, hcols⟩ := hmaps
    α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha F hmeas hwmeas π hπ K hK actual B hB hc henv
    yc ic a b hab.le hwindow θ hrow hcol Ks hdesc hKs hθ
  obtain ⟨diag, positive, Rm, hmetric, _hfull⟩ :=
    windowCover_exists_metric_source_originalEdge_allMoment_maps (h := h)
      hΛ hφ cov Ks hqJ K hK ic a b hwindow ϖ rfl D hD A Ledge Rs hsource.1
  obtain ⟨R, hR⟩ := windowCover_frozen_family_component_all_moment_response (h := h)
    hΛ hζ hφ cov K hK ic a b hab hwindow hgsmall hg0 hlength ϖ rfl
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

/-! The actual physical solution and its homogeneous zeroth response
share the same transformed localized initial datum on a certified first block. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

variable {Bcover g g0 strain B₀ lam Cb : ℝ} {qJ : ℕ} {CG : ℕ → ℝ} {y₀ : Vec 2}

theorem preparation_reference_cell_initial_homogeneous_response_pair
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
    (hζ : IsFastProfile ζ)
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν Bcover a b ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ Pcover y₀)
    (hgsmall : 4 * g ≤ 1 / 8) (hg0 : g0 ≤ 1 / 4)
    (ϖ : ℝ) (hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m))
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (f : ∀ i, TorusHk (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    (d : ℝ) (hcd : (e⁻¹) ^ 2 * (ν * a) < d)
    (hwindow : Icc ((e⁻¹) ^ 2 * (ν * a)) d ⊆
      windowCoverChartWindow α q Λ m ν a b l₀ Pcover (windowCoverReferenceChartIndex Pcover))
    (hlength : d - (e⁻¹) ^ 2 * (ν * a) ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2)
    (hdb : d ≤ (e⁻¹) ^ 2 * (ν * b))
    (hblock : ∀ t ∈ Icc ((e⁻¹) ^ 2 * (ν * a)) d,
      ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hs : IsCoupledWeakSolutionPlane ν a b (streamVel (Φ m)) D K (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) (fun j => spatialPatchLocalization hζ Npatch hNpatch patch (K j) (f j)) (fun _ _ => 0)
      (fun _ _ => 0) u w) :
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
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ Pcover y₀
    (windowCoverReferenceChartIndex Pcover)
  have hphysical := preparation_reference_cell_initial_natural_block_coupled_solution_of_pointwise
    F hab ρ hρ K hdesc hD hprep hcover hTau ha Kmax Jm hKmax hchart hmol Cm π hπ B hB
    hmeas hwmeas hΛ hm hseq ν e hν heScale hρe heE henv actual hT he yc
    (fun j => spatialPatchLocalization hζ Npatch hNpatch patch (K j) (f j)) u w d hcd.le hdb hblock hs
  dsimp only at hphysical ⊢
  refine ⟨hphysical, ?_⟩
  have hmom (n : ℕ) (j : ι) := preparationReferenceCell_localized_initial_moments
    hprep hcover hTau ha (K j) (by have hh := hKmax j; omega) hab
    hζ Npatch hNpatch patch (f j) e (hρ.trans_le hρe).ne' yc n ϖ ρ
  subst e
  have hr := windowCover_frozen_homogeneous_all_moment_response hΛ hζ hφ cov K hKmax
    (windowCoverReferenceChartIndex Pcover) _ _ hcd hwindow hgsmall hg0 hlength
    ϖ hϖ _ hmom
  simpa only [windowCoverReferenceChartIndex_label] using hr

end AVRegularity.CycleJointProofs
end
end
