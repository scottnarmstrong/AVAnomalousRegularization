-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.ActualPreparationHomogeneousFamilyNativeTraceLinearMap
public import AVRegularity.CycleJoint.PreparationTransportedWeightedPolynomialAllMomentMap
public import AVRegularity.CycleJoint.Assembly.PatchBridges
import AVRegularity.CycleJoint.WindowCoverConstructedRetainedActualTaylorLinearEndpointAllMomentsBound
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
import AVRegularity.CycleJoint.ActualPreparationHomogeneousPlaneExistence

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.Weighted AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CycleJointProofs
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The moments of the actual solution at the end of the following block**.

The following-chart curve of the actual physical solution solves the cell problem started from the
transition of its old-block curve at the seam
(`preparation_window_reference_cell_coupled_solution_on_actual_mixed_seam`); the homogeneous
endpoint energy (`windowCover_homogeneous_endpoint_energy`, with the source data of
`preparation_window_reference_source_energy_data`) and the transition's renewal energy bound its
weighted energy at every cell time of the block by `Cactual · budget · ` the weighted energy of
the old-block curve at the seam, without any small factor. -/

universe u v w x y

/-- **The moments at the end of the following block, cell part.** -/
theorem following_actual_endpoint_energy
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
    ∀ H : ℕ, F.HasDepthAtMost H → F.IsDescending K →
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
    let _A := preparationReferenceCellSourceCoefficient F hφ σ
      ν e (ocEpsilon q Λ (m - 1)) actual K yc
    e = ocEpsilon q Λ m →
    IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)) →
    ∀ Nperiod : ℕ, (ocEpsilon q Λ m)⁻¹ = (Nperiod : ℝ) →
    ∀ (s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      IsAdmissibleQ α s q → IsOCStreamSeq α q Λ ζ Φ → 1 ≤ m →
    ∀ (ha : 0 ≤ ocA α q Λ (m - 1)) (tp : ℝ) (htp : tp ∈ Set.Icc tS tZ),
    a = (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * tp) →
    (∀ t ∈ Set.Icc a b,
      (((l₀ + 1 : ℤ) : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ (((l₀ + 1 : ℤ) : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
    let hΛ1 : 1 ≤ Λ := (by omega)
    let seed := ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀
    let yc0 := ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1) seed 1
    let _S := preparationReferenceCellTransitionFamilyLinearMap hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ1).le ha K (fun i => by have hh := _hK i; omega)
      σ hnext (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc0 yc tp htp
    ∀ (n : ℕ) (Cw : ℕ → ℝ) (ϖ : ℝ) (_W : ChartWeights G v a (b - a) ϖ 0 n Cw),
    ∀ {X : Type y} [AddCommGroup X] [Module ℝ X]
      (Upre : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (_hUinit : ∀ ξ i, weightedFactorialNormSq n ϖ 0 r (K i) (Upre ξ i) ≠ ⊤)
      (Uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (Uwphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
    (∀ ξ, ∃ f : ∀ i, PlaneHk Set.univ (K i) (h i),
      IsCoupledWeakSolutionPlane ν tS tZ (streamVel (Φ m)) D K
        (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K)
        f (fun _ _ => 0) (fun _ _ => 0) (Uphys ξ) (Uwphys ξ)) →
    (∀ ξ i, Upre ξ i = preparationReferenceCellNativeCurve hprep hcover
      (Construction.Stream.ocTauPP_pos hΛ1).le ha (K i) (by have hh := _hK i; omega)
      ν (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc0 (Uphys ξ i) a) →
    let Cjet := fun j => max (CG j) 0
    let Cactual := ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
      (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw))
    ∀ ξ, ∀ t ∈ Set.Icc a b,
      (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i)
        (preparationWindowReferenceCellNativeCurve hprep hcover σ hnext ha
          (K i) (by have hh := _hK i; omega) ν (ocEpsilon q Λ m)
          (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc (Uphys ξ i) t)) ≤
        Cactual * (ENNReal.ofReal (cellTransitionMomentBudget Kmax n) *
          ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (Upre ξ i)) := by
  obtain ⟨Cprep, hCprep, hdata⟩ := preparation_window_reference_source_energy_data
    D Kmax Jchart Jm hchart hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m Φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ _ _ _ _ P' Ctx F π hπ K hK actual B hB hprep hcover hmeas hwmeas henv
    hnext a b θ hsub hrow hcol H hdepth hdesc ζ Bcover g g0 strain B₀ lam Cb qJ CG y₀ cov hΛ
    hζ hab ic hwindow hqJ hg4 hD yc G v r σ A he htorus Nperiod hperiod
    s hα0 hα1 hs0 hs1 hq hseq hm ha tp htp htime hblock hΛ1 seed yc0 S
    n Cw ϖ W X _ _ Upre hUinit Uphys Uwphys hphysical htrace Cjet Cactual ξ t ht
  let U := fun i => preparationWindowReferenceCellNativeCurve hprep hcover σ hnext ha
    (K i) (by have hh := hK i; omega) ν (ocEpsilon q Λ m)
    (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc (Uphys ξ i)
  let Uw := fun i => preparationWindowReferenceCellNativeCurve hprep hcover σ hnext ha
    (K i + 1) (by have hh := hK i; omega) ν (ocEpsilon q Λ m)
    (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc (Uwphys ξ i)
  have hρe' : ρ ≤ ocEpsilon q Λ m := he ▸ hρe
  have heE' : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) := he ▸ heE
  have henv' := henv
  rw [he] at henv'
  have hsub' := hsub
  rw [he] at hsub'
  have hU : IsCoupledWeakSolutionPlane 1 a b v D K
      (planeMetricSourceCoefficient K D G A) (S (Upre ξ))
      (fun _ _ => 0) (fun _ _ => 0) U Uw := by
    obtain ⟨f, hs⟩ := hphysical ξ
    rw [he] at hs
    have hb := preparation_window_reference_cell_coupled_solution_on_actual_mixed_seam
      F (htp.1.trans htp.2) (fun _ ht => ht) ρ hρ K hdesc hD hprep hcover
      (l₀ + 1) hnext ha Kmax Jm hK hchart hmol Cm π hπ B hB hmeas hwmeas
      hΛ1 hm hseq ν (ocEpsilon q Λ m) hν rfl hρe' heE' henv' actual htorus hperiod
      yc f (Uphys ξ) (Uwphys ξ) a b (hsub' ⟨le_rfl, hab⟩).1 hab
      (hsub' ⟨hab, le_rfl⟩).2 hblock hs
      (Construction.Stream.ocTauPP_pos hΛ1).le yc0 tp htp htime
    dsimp only at hb
    have hid : (fun i => preparationReferenceCellNativeCurve hprep hcover
        (Construction.Stream.ocTauPP_pos hΛ1).le ha (K i) (by have hh := hK i; omega)
        ν (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ1).ne' yc0 (Uphys ξ i) a) =
        Upre ξ :=
      funext (fun i => (htrace ξ i).symm)
    rw [hid] at hb
    dsimp only [G, windowCoverCellMetric]
    rw [windowCoverFollowingChartIndex_label]
    simpa only [A, he, σ, S, U, Uw, v] using hb
  have hKchart (i : ι) : K i ≤ Jchart + 1 := by have hh := hK i; omega
  have hr : 0 ≤ r := (div_pos hρ (Construction.Stream.ocEpsilon_pos hΛ1)).le
  have hr1 : r ≤ 1 := (div_le_one₀ (Construction.Stream.ocEpsilon_pos hΛ1)).mpr hρe'
  have hfinS (i : ι) : weightedFactorialNormSq n ϖ 0 r (K i) (S (Upre ξ) i) ≠ ⊤ :=
    preparationReferenceCellTransitionOperator_renewal_polynomial_energy_ne_top
      hprep hcover (Construction.Stream.ocTauPP_pos hΛ1).le ha (K i) (hKchart i)
      s hα0 hα1 hs0 hs1 hq hζ hΛ hseq hm hnext ν hν.ne'
      (Construction.Stream.ocEpsilon_pos hΛ1).ne' y₀ (Upre ξ i) tp htp n n Kmax le_rfl (hK i)
      ϖ r hr hr1 (hUinit ξ i)
  obtain ⟨hfinite, hsmooth, hAm, hrowA, hcolA, hrank, hzero⟩ :=
    hdata α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
      F π hπ K hK actual B hB hprep hcover hmeas hwmeas henv
      σ hnext yc a b θ hsub hrow hcol H hdepth
  have hre : ρ / e = r := by rw [he]
  rw [hre] at hfinite hrowA hcolA
  have hE := windowCover_homogeneous_endpoint_energy hΛ1 hζ hφ cov heE' ic a b hab hwindow hqJ hg4
    K hK π hπ D H n hD Cw ϖ W A hfinite hsmooth hAm (Cprep * θ) hrowA hcolA
    (sourceDepthRank F H) hrank hzero (S (Upre ξ)) hfinS U Uw hU t ht
  have hT := preparationReferenceCellTransitionFamilyLinearMap_renewal_energy_le
    hprep hcover (Construction.Stream.ocTauPP_pos hΛ1).le ha K hKchart
    s hα0 hα1 hs0 hs1 hq hζ hΛ hseq hm hnext ν hν.ne'
    (Construction.Stream.ocEpsilon_pos hΛ1).ne' y₀ (Upre ξ) π tp htp n n Kmax le_rfl hK ϖ r hr hr1
  have hT' : (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i)
      (S (Upre ξ) i)) ≤ ENNReal.ofReal (cellTransitionMomentBudget Kmax n) *
        ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 r (K i) (Upre ξ i) := hT
  refine hE.trans (le_of_le_of_eq (mul_le_mul_right (mul_le_mul_right hT' _) _) ?_)
  simp only [Cactual]
  ring

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Level C, geometry side: statements**.

`BlockEdgePackageStatement`: the edge package
(`windowCover_window_reference_constructed_edge_package`) with the source insertion read through the
block letters (`blockLetterRawConstituent`) instead of each piece's native Taylor array, on a
window inside one renewal block `l` with reference time `σ = l τ''` and the chart reserve
`Ks + D + 2 ≤ Jchart` (the transported fields of pieces of another label are Taylor-expanded to order
`Ks` in the block chart, which uses the flow certificate's jets through order `Ks + D + 2`), where
either `l = l₀` (the
first block, `windowCover_reference_constructed_edge_package`) or `σ ∈ [tS, tZ]` (the
following block, `windowCover_window_reference_constructed_edge_package`). For the pieces of label `l`
(anchor `σ`) the two readouts coincide; the other pieces are active in the block only at quiet
times, where they are fast independent and their transported slow field is
Taylor-expanded in the block chart. The remainder constant `Crem` replaces
`pointwiseOriginalRemainderGraphConstant`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x y

namespace AVRegularity.CycleJointProofs.Assembly

/-- A slot bounded by `Kmax` is within the chart order `Jchart + 1` when `Kmax + D + 2 ≤ Jchart`
(used in the statements in place of an `omega` call, which would scan the whole statement
context). -/
theorem slot_le_chart {ι : Type*} {K : ι → ℕ} {Kmax D Jchart : ℕ} (hK : ∀ i, K i ≤ Kmax)
    (hchart : Kmax + D + 2 ≤ Jchart) (i : ι) : K i ≤ Jchart + 1 := by
  have := hK i
  omega

/-- `slot_le_chart` one order higher. -/
theorem slot_succ_le_chart {ι : Type*} {K : ι → ℕ} {Kmax D Jchart : ℕ} (hK : ∀ i, K i ≤ Kmax)
    (hchart : Kmax + D + 2 ≤ Jchart) (i : ι) : K i + 1 ≤ Jchart + 1 := by
  have := hK i
  omega

/-- **The edge package of the block letters.** -/
def BlockEdgePackageStatement : Prop :=
  ∀ (D Kmax Jchart Jm : ℕ) (_hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) (Ks : ℕ) (_hKsJ : Ks + D + 2 ≤ Jchart),
    ∃ Cprep Crem : ℝ, 1 ≤ Cprep ∧ 0 ≤ Crem ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (CG : ℕ → ℝ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (_ha : 0 ≤ ocA α q Λ (m - 1)),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ : ℝ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (ic : Fin (P + 2)) (a b : ℝ) (_hab : a ≤ b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
        ∀ l : ℤ, σ = (l : ℝ) * ocTauPP α q Λ m → (l = l₀ ∨ σ ∈ Set.Icc tS tZ) →
        (∀ t ∈ Set.Icc a b, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
          ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
        ∀ S : Set ℝ, IsCoreOutside α q Λ m F tS tZ S → F.IsFastIndependentOn (S ∩ Set.Icc tS tZ) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
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
        (fun x t z => ∑ u, ∑ γ, blockLetterRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
          (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ l
          σ (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc ϖ (ρ / (ocEpsilon q Λ m))
          (volume.restrict (Set.Icc a b)) v u γ (x u) t z)
        (nativeFamilyEdgeForcingMap Ledge v)) ∧
      (∀ v u, ¬ Nonempty (F.Γ v u) → Ledge v u = 0) ∧
      (∀ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
        HasSourceDegreeOn F 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))) ∧
    (∀ (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
      (volume.restrict (Set.Icc a b))) (n : ℕ),
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / (ocEpsilon q Λ m)) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
        (Rs v Z) τ)
      ∂volume.restrict (Set.Icc a b)) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) * (Crem * θ)) ^ 2) *
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
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ)

/-- **Cell solutions from a linear datum** (a named proposition, shared by the statements and
their proofs): for every `ξ`, `(uH ξ, wH ξ)` solves the cell equation on `[a, b]` with drift `v`,
metric `G` and source coefficient `A` from the datum `V₀ ξ`. -/
def BlockCellSolutions {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {X : Type*} [AddCommGroup X] [Module ℝ X] (D : ℕ) (K : ι → ℕ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)) : Prop :=
  ∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A) (V₀ ξ)
    (fun _ _ => 0) (fun _ _ => 0) (uH ξ) (wH ξ)

/-- **Physical solutions from localized data** (a named proposition, shared by the statements and
their proofs): for every datum `f`, `(uphys f, wphys f)` solves the physical equation on
`[t₀, t₁]` with velocity `vel` and coefficient `Aphys` from the localized datum `loc f`. -/
def PhysicalSolutions {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ} {X : Type*} (K : ι → ℕ)
    (ν t₀ t₁ : ℝ) (vel : ℝ → Vec 2 → Vec 2)
    (Aphys : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (loc : X → ∀ i, PlaneHk Set.univ (K i) (h i))
    (uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)) : Prop :=
  ∀ f, IsCoupledWeakSolutionPlane ν t₀ t₁ vel D K Aphys (loc f) (fun _ _ => 0) (fun _ _ => 0)
    (uphys f) (wphys f)

/-- **The conclusion of the block word geometry** for given letters `M`, `S`, datum `V₀`, solution `uH` and bound
`Bd`: word chains of the block (`wordChainData Gfr` with the frozen metric `Gfr` and the letters of the word, slots `K`) from
`V₀`, linear in the datum, with finite moments at the end of the window `[a, b]` and with fields of
finite time-integrated moments at every level, whose sum over
the words with at most `J` metric and `H` source insertions approximates `uH` at `τ` up to `Bd`.
It is a named proposition so that the statement and its proofs share one elaborated form. -/
def BlockWordConclusion {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}
    {X : Type*} [AddCommGroup X] [Module ℝ X] (K : ι → ℕ) (J H : ℕ)
    (Gfr : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (M S : CycleLetter ι h D) (X₀ : Vec 2) (δ a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i))) (ϖ rs : ℝ)
    (n : ℕ) (π : ι → ℝ) (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (τ : ℝ)
    (Bd : X → ℝ≥0∞) : Prop :=
  ∃ (uW : ∀ w : List Bool, X → ∀ (_ : Fin (w.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (K x) (h x))
    (wW : ∀ w : List Bool, X → ∀ (_ : Fin (w.length + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (K x + 1) (h x)),
    (∀ w ∈ blockWords J H, ∀ ξ, IsPlaneChain (wordChainData Gfr (blockWordLetters M S w) X₀ δ)
      (fun _ x => K x) a b v (V₀ ξ) (fun _ _ _ => 0) (uW w ξ) (wW w ξ)) ∧
    (∀ w ∈ blockWords J H, ∀ (c : ℝ) (ξ ξ' : X) j x, ∀ t ∈ Set.Icc a b,
      uW w (c • ξ + ξ') j x t = c • uW w ξ j x t + uW w ξ' j x t) ∧
    (∀ w ∈ blockWords J H, ∀ ξ r x, ∀ t ∈ Set.Icc a b,
      weightedFactorialNormSq r ϖ 0 rs (K x) (uW w ξ (Fin.last _) x t) ≠ ⊤) ∧
    (∀ w ∈ blockWords J H, ∀ ξ j x r,
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq r ϖ 0 rs (K x + 1) (wW w ξ j x t)) ≠ ⊤) ∧
    ∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ 0 rs (K i)
          (uH ξ i τ - ∑ w ∈ blockWords J H, uW w ξ (Fin.last _) i τ)) ≤ Bd ξ

/-- **The body of the block word geometry: geometry of one renewal block in word form** (given the constants). The
retained-endpoint layer
(`windowCover_window_reference_retained_linear_endpoint_all_moments_bound`) on a window inside the
block `l` with reference time `σ = l τ''`, with the source insertion read through the block letters:
for every linear datum `V₀` with finite moments there are word chains (`wordChainData` with the
block's metric letter `M` and source letter `S`, slots `K`), linear in the datum and with finite
moments at the end of the window, whose sum over the words with at most `J` metric and `H` source
insertions approximates the actual block solution `uH` at every `τ` with the retained price (the
remainder constant `Crem` of the block letters in place of `Cgraph`). -/
def BlockWordBody (D Ks Kmax Jchart Jm : ℕ) (Cm Cchart CG : ℕ → ℝ)
    (Cprep CT CR Cterminal Crem : ℝ) : Prop :=
    let Cjet : ℕ → ℝ := fun r => max (CG r) 0
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (_hζ : IsFastProfile ζfast) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (_ha : 0 ≤ ocA α q Λ (m - 1))
        (_hgsmall : 4 * g ≤ 1 / 8) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ : ℝ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (ic : Fin (P + 2)) (a b : ℝ) (_hab : a < b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
        ∀ l : ℤ, σ = (l : ℝ) * ocTauPP α q Λ m →
          (l = l₀ ∧ ic = windowCoverReferenceChartIndex P ∨ σ ∈ Set.Icc tS tZ) →
        (∀ t ∈ Set.Icc a b, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
          ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
        ∀ S : Set ℝ, IsCoreOutside α q Λ m F tS tZ S → F.IsFastIndependentOn (S ∩ Set.Icc tS tZ) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
        Ks + 1 + Kmax ≤ qJ → b - a ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
      ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀
      ic
    let v := ocCellDrift α q Λ ζfast m ν yc
    let A := preparationReferenceCellSourceCoefficient F hφ σ
      ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc
    ∀ {X : Type y} [AddCommGroup X] [Module ℝ X],
    ∀ (n H N J : ℕ) (_hdepth : F.HasDepthAtMost H) (Cw : ℕ → ℝ)
      (_W : ChartWeights G v a (b - a) ϖ 0 N Cw)
      (_WM : ChartWeights (fun t _ => G t 0) v a (b - a) ϖ 0 N Cw)
      (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (_hf : ∀ ξ r i, weightedFactorialNormSq r ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i) ≠ ⊤)
      (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
      (_hH : BlockCellSolutions D K a b v G A V₀ uH wH)
      (L : ℝ) (_hL : 1 ≤ L)
      (_hreserve : ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16)
      (_hgain : ENNReal.ofReal (CT * g * ζ) ≤ 1)
      (_hN : n + (Ks + 1) + (J + H) * (Ks + 1) ≤ N)
      (τ : ℝ) (_hτ : τ ∈ Set.Icc a b),
    ∀ (θM θS : ℝ) (bM bS : ι → ι → ℝ),
    let X₀ := (ocEpsilon q Λ (m - 1))⁻¹ • yc
    let δ := ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)
    let M := blockMetricLetter (D := D) (h := h) G X₀ δ Ks θM bM
    let S := blockSourceLetter F (F.locally_finite tS tZ).toFinset actual hφ (Set.Icc tS tZ) l σ yc
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) Ks θS bS
    let C := scalarResponseTwoInsertionCommonPrice Kmax L Cw N
      (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
      (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Crem))
    let cm := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2)
    let cs := ENNReal.ofReal ((Crem * θ) ^ 2)
    let ct := ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)
    let θcap := ENNReal.ofReal θ
    let ζcap := ENNReal.ofReal ζ
    let η := ENNReal.ofReal (Cterminal * g * ζ)
    let G0 := fun ξ => ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} N Kmax Cw) *
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 (ρ / ocEpsilon q Λ m) (K i) (V₀ ξ i)
    BlockWordConclusion K J H (fun t => G t 0) M S X₀ δ a b v V₀ ϖ (ρ / ocEpsilon q Λ m) n π uH τ
      (fun ξ => ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax Cjet Cw D (Cprep * θ)) ^ (2 * H)) *
        (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax Cjet Cw) *
          (coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
            (ζcap ^ (2 * (Ks + 1)) + η ^ (2 * (J + 1))) * G0 ξ)))

/-- **Geometry of one renewal block in word form** (see `BlockWordBody`): the constants
depend only on the orders and the supplied jet bounds. -/
def BlockWordGeometryStatement : Prop :=
  ∀ (D Ks Kmax Jchart Jm : ℕ) (_hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (_hKsJ : Ks + D + 2 ≤ Jchart) (Cm Cchart CG : ℕ → ℝ),
    ∃ Cprep CT CR Cterminal Crem : ℝ, 1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧ 0 ≤ Crem ∧
      BlockWordBody.{u, v, w, x, y} D Ks Kmax Jchart Jm Cm Cchart CG Cprep CT CR Cterminal Crem

/-- **The conclusion of the two-block theorem** (a named proposition, shared by the statement and its proof): a
physical solution for every datum (`loc f` its localized initial value, coefficient `Aphys` of the
equation with velocity `vel` on `[t₀, t₁]`), old word chains of the letters `Mpre`, `Spre` on
`[a, b]` from `V₀`, future word chains of `Mpost`, `Spost` on `[b, dpost]` started from the
transition of each old endpoint, all linear in the datum, the old endpoints with finite moments,
the fields of the old chains with finite time-integrated moments at every level,
and the physical solution at `tfinal` approximated by the return of the allocation sum at `τend` up
to `Bd`. -/
def TwoBlockWordConclusion {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}
    {X : Type*} [AddCommGroup X] [Module ℝ X] (K : ι → ℕ) (ν t₀ t₁ : ℝ)
    (vel : ℝ → Vec 2 → Vec 2)
    (Aphys : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (loc : X → ∀ i, PlaneHk Set.univ (K i) (h i)) (Jpre Jpost H : ℕ)
    (Gfpre Gfpost : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (Mpre Spre Mpost Spost : CycleLetter ι h D)
    (X₀pre X₀post : Vec 2) (δ a b dpost : ℝ) (vpre vpost : ℝ → Vec 2 → Vec 2)
    (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (transit ret : ∀ i, PlaneHk Set.univ (K i) (h i) →L[ℝ] PlaneHk Set.univ (K i) (h i))
    (ϖ rs ρ : ℝ) (π : ι → ℝ) (tfinal τend : ℝ) (Bd : X → ℝ≥0∞) : Prop :=
  ∃ (uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
  (∀ f, IsCoupledWeakSolutionPlane ν t₀ t₁ vel D K Aphys (loc f) (fun _ _ => 0) (fun _ _ => 0)
    (uphys f) (wphys f)) ∧
  ∃ (uO : ∀ w : List Bool, X → ∀ (_ : Fin (w.length + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (K x) (h x))
    (wO : ∀ w : List Bool, X → ∀ (_ : Fin (w.length + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (K x + 1) (h x))
    (uF : List Bool → ∀ w : List Bool, X → ∀ (_ : Fin (w.length + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (K x) (h x))
    (wF : List Bool → ∀ w : List Bool, X → ∀ (_ : Fin (w.length + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (K x + 1) (h x)),
    (∀ wo ∈ blockWords Jpre H, ∀ ξ, IsPlaneChain (wordChainData Gfpre
      (blockWordLetters Mpre Spre wo) X₀pre δ) (fun _ x => K x) a b vpre (V₀ ξ)
      (fun _ _ _ => 0) (uO wo ξ) (wO wo ξ)) ∧
    (∀ wo ∈ blockWords Jpre H, ∀ wf ∈ blockWords Jpost H, ∀ ξ,
      IsPlaneChain (wordChainData Gfpost (blockWordLetters Mpost Spost wf) X₀post δ)
        (fun _ x => K x) b dpost vpost (fun x => transit x (uO wo ξ (Fin.last _) x b))
        (fun _ _ _ => 0) (uF wo wf ξ) (wF wo wf ξ)) ∧
    (∀ wo ∈ blockWords Jpre H, ∀ (c : ℝ) (ξ ξ' : X) j x, ∀ t ∈ Set.Icc a b,
      uO wo (c • ξ + ξ') j x t = c • uO wo ξ j x t + uO wo ξ' j x t) ∧
    (∀ wo ∈ blockWords Jpre H, ∀ wf ∈ blockWords Jpost H, ∀ (c : ℝ) (ξ ξ' : X) j x,
      ∀ t ∈ Set.Icc b dpost,
      uF wo wf (c • ξ + ξ') j x t = c • uF wo wf ξ j x t + uF wo wf ξ' j x t) ∧
    (∀ wo ∈ blockWords Jpre H, ∀ ξ r x,
      weightedFactorialNormSq r ϖ 0 rs (K x) (uO wo ξ (Fin.last _) x b) ≠ ⊤) ∧
    (∀ wo ∈ blockWords Jpre H, ∀ ξ j x r,
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq r ϖ 0 rs (K x + 1) (wO wo ξ j x t)) ≠ ⊤) ∧
    ∀ ξ, ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq ρ
      (uphys ξ i tfinal - ret i (∑ wo ∈ blockWords Jpre H, ∑ wf ∈ blockWords Jpost H,
        uF wo wf ξ (Fin.last _) i τend)).val) ≤ Bd ξ

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! The two existing reference-time packages supply one full-source energy and
Schur constant before any family is chosen. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

def BlockNativeFullStatement : Prop :=
  ∀ (D Kmax Jchart Jm : ℕ) (_hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) (Ks : ℕ) (_hKsJ : Ks + D + 2 ≤ Jchart),
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (CG : ℕ → ℝ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (_ha : 0 ≤ ocA α q Λ (m - 1)),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ : ℝ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (ic : Fin (P + 2)) (a b : ℝ) (_hab : a ≤ b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
        ∀ l : ℤ, σ = (l : ℝ) * ocTauPP α q Λ m → (l = l₀ ∨ σ ∈ Set.Icc tS tZ) →
        (∀ t ∈ Set.Icc a b, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
          ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
        ∀ S : Set ℝ, IsCoreOutside α q Λ m F tS tZ S →
        F.IsFastIndependentOn (S ∩ Set.Icc tS tZ) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let _ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    ∃ Tfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ σ ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (Tfull v)) ∧
    (∀ W n, planeAllMomentFamilyEnergy K n ϖ (ρ / (ocEpsilon q Λ m)) (volume.restrict (Set.Icc a b)) π
      (fun v => (Tfull v) W) ≤ ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K n ϖ (ρ / (ocEpsilon q Λ m)) (volume.restrict (Set.Icc a b)) π W) ∧
    (∀ v, ∑ u, schurMatrix 1 (ρ / (ocEpsilon q Λ m)) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ) ∧
    (∀ u, ∑ v, schurMatrix 1 (ρ / (ocEpsilon q Λ m)) π K D a b
      (preparationReferenceCellSourceCoefficient F hφ σ
        ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * θ)

/-- The native packages give a common full-source bound for both reference paths. -/
theorem blockNativeFull : BlockNativeFullStatement.{u, v, w, x} := by
  intro D Kmax Jchart Jm hchart hmol Cm Cchart Ks _hKsJ
  obtain ⟨C₀, hC₀, hn₀⟩ := windowCover_reference_constructed_edge_package
    D Kmax Jchart Jm hchart hmol Cm Cchart
  obtain ⟨C₁, hC₁, hn₁⟩ := windowCover_window_reference_constructed_edge_package
    D Kmax Jchart Jm hchart hmol Cm Cchart
  let Cprep := max C₀ C₁
  refine ⟨Cprep, hC₀.trans (le_max_left _ _), ?_⟩
  intro α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc hcover σ henv yc ic a b hab hwindow l hσ hpath _hblock _S _hcoreS _hquiet θ hrow hcol hdesc hKs hθ
  dsimp only
  have hmass_const (C : ℝ) (hC : 0 ≤ C) (hCC : C ≤ Cprep) :
      ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (C * θ)) ^ 2) ≤
        ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (Cprep * θ)) ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hC hθ))
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCC hθ) (Real.sqrt_nonneg _)
  rcases hpath with hl | ht
  · have hσ₀ : σ = (l₀ : ℝ) * ocTauPP α q Λ m := by simpa only [hl] using hσ
    rw [hσ₀]
    obtain ⟨R, Ledge, hraw, _hrem, hmass, hrow', hcol'⟩ :=
      hn₀ α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
        qJ CG y₀ cov hΛ heE ha F hmeas hwmeas π hπ K hK actual B hB hc henv yc ic a b
        hab hwindow θ hrow hcol Ks hdesc hKs hθ
    refine ⟨fun v => nativeFamilyEdgeForcingMap Ledge v + R v, hraw.1, ?_, ?_, ?_⟩
    · intro W n
      exact (hmass W n).trans (mul_le_mul_left
        (hmass_const C₀ (zero_le_one.trans hC₀) (le_max_left _ _)) _)
    · intro v
      exact (hrow' v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hθ)
    · intro u
      exact (hcol' u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hθ)
  · obtain ⟨R, Ledge, hraw, _hrem, hmass, hrow', hcol'⟩ :=
      hn₁ α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
        qJ CG y₀ cov hΛ heE ha F hmeas hwmeas π hπ K hK actual B hB hc hcover σ ht henv
        yc ic a b hab hwindow θ hrow hcol Ks hdesc hKs hθ
    refine ⟨fun v => nativeFamilyEdgeForcingMap Ledge v + R v, hraw.1, ?_, ?_, ?_⟩
    · intro W n
      exact (hmass W n).trans (mul_le_mul_left
        (hmass_const C₁ (zero_le_one.trans hC₁) (le_max_right _ _)) _)
    · intro v
      exact (hrow' v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hθ)
    · intro u
      exact (hcol' u).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hθ)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The two-block theorem, the common finish**.

`twoBlockWordGeometry_finish`: the block word geometry on the old block (datum `V₀`, words with at most `Jpre` metric
and `H` source insertions) and on the future block over the extended datum space
`List Bool → X` (one datum per old word; the datum `V₀' η` is the transition of the sum of the
old endpoints `uO wo (η wo)`) give the conclusion `TwoBlockWordConclusion` of the two-block theorem: the future chain of
the pair `(wo, wf)` is the future chain of `wf` at the single datum `Pi.single wo ξ`, whose datum
is the transition of the endpoint of `wo` alone; by linearity, the allocation sum is the future
sum at the diagonal datum `wordDiag ξ`, which is where the physical bound `hbound` is stated. Both
conclusions of the block word geometry enter as the named proposition `BlockWordConclusion`, so no chain clause is
re-elaborated. -/

local instance blockRawPlanePiAddGroup {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    AddCommGroup (∀ i, PlaneHk Set.univ (K i) (h i)) := inferInstance
local instance blockRawPlanePiAddMonoid {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    AddCommMonoid (∀ i, PlaneHk Set.univ (K i) (h i)) := inferInstance
local instance blockRawPlanePiModule {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    Module ℝ (∀ i, PlaneHk Set.univ (K i) (h i)) := inferInstance

/-- **The two-block theorem, the common finish.** -/
theorem twoBlockWordGeometry_finish {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}
    {X : Type*} [AddCommGroup X] [Module ℝ X] (K : ι → ℕ) (ν t₀ t₁ : ℝ)
    (vel : ℝ → Vec 2 → Vec 2)
    (Aphys : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (loc : X → ∀ i, PlaneHk Set.univ (K i) (h i)) (Jpre Jpost H : ℕ)
    (Gfpre Gfpost : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (Mpre Spre Mpost Spost : CycleLetter ι h D)
    (X₀pre X₀post : Vec 2) (δ a b dpost : ℝ) (hab : a ≤ b) (vpre vpost : ℝ → Vec 2 → Vec 2)
    (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (transit ret : ∀ i, PlaneHk Set.univ (K i) (h i) →L[ℝ] PlaneHk Set.univ (K i) (h i))
    (ϖ rs ρ : ℝ) (π : ι → ℝ) (tfinal τend : ℝ) (hτend : τend ∈ Set.Icc b dpost)
    (Bd : X → ℝ≥0∞) (npre npost : ℕ) (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (Bdpre : X → ℝ≥0∞)
    (hpre : BlockWordConclusion K Jpre H Gfpre Mpre Spre X₀pre δ a b vpre V₀ ϖ rs npre π uH b
      Bdpre)
    (V₀' : (List Bool → X) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (uH' : (List Bool → X) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (Bdpost : (List Bool → X) → ℝ≥0∞)
    (hpost : BlockWordConclusion K Jpost H Gfpost Mpost Spost X₀post δ b dpost vpost V₀' ϖ rs
      npost π uH' τend Bdpost)
    (hV₀' : ∀ η x, V₀' η x = transit x (∑ wo ∈ blockWords Jpre H,
      Classical.choose hpre wo (η wo) (Fin.last _) x b))
    (uphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hphysical : PhysicalSolutions K ν t₀ t₁ vel Aphys loc uphys wphys)
    (hbound : ∀ ξ, ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq ρ
      (uphys ξ i tfinal - ret i (∑ wf ∈ blockWords Jpost H,
        Classical.choose hpost wf (wordDiag (blockWords Jpre H) ξ) (Fin.last _) i τend)).val) ≤
      Bd ξ) :
    TwoBlockWordConclusion K ν t₀ t₁ vel Aphys loc Jpre Jpost H Gfpre Gfpost Mpre Spre Mpost
      Spost X₀pre X₀post δ a b dpost vpre vpost V₀ transit ret ϖ rs ρ π tfinal τend Bd := by
  classical
  obtain ⟨wO, hcO, hlO, hfO, hEO, -⟩ := Classical.choose_spec hpre
  obtain ⟨wW, hcW, hlW, -, -⟩ := Classical.choose_spec hpost
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hO0 : ∀ wo ∈ blockWords Jpre H, ∀ x,
      Classical.choose hpre wo 0 (Fin.last _) x b = 0 := fun wo hwo x =>
    wordMap_zero (blockWords Jpre H)
      (fun w ξ => Classical.choose hpre w ξ (Fin.last _) x b)
      (fun w hw c ξ ξ' => hlO w hw c ξ ξ' (Fin.last _) x b hb) hwo
  have hsingle : ∀ wo ∈ blockWords Jpre H, ∀ (ξ : X),
      V₀' (Pi.single wo ξ) = fun x => transit x (Classical.choose hpre wo ξ (Fin.last _) x b) := by
    intro wo hwo ξ
    funext x
    rw [hV₀' (Pi.single wo ξ) x, Finset.sum_eq_single wo]
    · rw [Pi.single_eq_same (M := fun _ : List Bool => X)]
    · intro wo' hwo' hne
      rw [Pi.single_eq_of_ne (M := fun _ : List Bool => X) hne, hO0 wo' hwo' x]
    · exact fun h => absurd hwo h
  unfold TwoBlockWordConclusion
  refine ⟨uphys, wphys, hphysical, Classical.choose hpre, wO,
    fun wo wf ξ => Classical.choose hpost wf (Pi.single wo ξ),
    fun wo wf ξ => wW wf (Pi.single wo ξ), hcO, ?_, hlO, ?_,
    fun wo hwo ξ r x => hfO wo hwo ξ r x b hb, hEO, ?_⟩
  · intro wo hwo wf hwf ξ
    have hc := hcW wf hwf (Pi.single wo ξ)
    rw [hsingle wo hwo ξ] at hc
    exact hc
  · intro wo _ wf hwf c ξ ξ' j x t ht
    have hs : Pi.single (M := fun _ : List Bool => X) wo (c • ξ + ξ') =
        c • Pi.single (M := fun _ : List Bool => X) wo ξ +
          Pi.single (M := fun _ : List Bool => X) wo ξ' := by
      funext w'
      by_cases hw : w' = wo
      · subst hw
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hw, smul_zero, add_zero]
    have hl := hlW wf hwf c (Pi.single (M := fun _ : List Bool => X) wo ξ)
      (Pi.single (M := fun _ : List Bool => X) wo ξ') j x t ht
    exact (congrArg (fun η => Classical.choose hpost wf η j x t) hs).trans hl
  · intro ξ
    refine (le_of_eq (congrArg ENNReal.ofReal (Finset.sum_congr rfl fun i _ => ?_))).trans
      (hbound ξ)
    have hsum := planeWordSum_single_comm (blockWords Jpre H) (blockWords Jpost H)
      (fun w η => Classical.choose hpost w η (Fin.last _) i τend)
      (fun w hw c η η' => hlW w hw c η η' (Fin.last _) i τend hτend) ξ
    exact congrArg (fun T => (π i)⁻¹ * factorialNormSq ρ (uphys ξ i tfinal - ret i T).val) hsum

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! **The two-block theorem, small pieces**.

* `planeWordSumPi`, `planeWordSum`: the word sums `wordSumPi`, `wordSum` for families of `PlaneHk`
  values, with the linearity hypothesis stated componentwise on `PlaneHk` (the form of the
  linearity clause of `BlockWordConclusion`), and their evaluation lemmas.
* `coupled_following_windowCover`: the following-block cell solutions, stated with the cell metric
  of block `l₀ + 1`, read with the cover's following chart metric.
* `gain_of_max`: a gain condition for `max a b` gives both.
* `pricePre_reassoc`, `pricePost_le`: the reassociations from the bound of the block word geometry to the prices `εpre`,
  `εpost`. -/

section
section PlaneMaps

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

/-- `wordSumPi` for families of `PlaneHk` values. -/
def planeWordSumPi (K : ι → ℕ) (s : Finset (List Bool))
    (f : List Bool → Y → ∀ i, PlaneHk Set.univ (K i) (h i))
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (η η' : Y) i, f w (c • η + η') i = c • f w η i + f w η' i) :
    (List Bool → Y) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)) :=
  wordSumPi s f (fun w hw c η η' => funext fun i => hf w hw c η η' i)

theorem planeWordSumPi_apply (K : ι → ℕ) (s : Finset (List Bool))
    (f : List Bool → Y → ∀ i, PlaneHk Set.univ (K i) (h i))
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (η η' : Y) i, f w (c • η + η') i = c • f w η i + f w η' i)
    (η : List Bool → Y) (i : ι) :
    planeWordSumPi K s f hf η i = ∑ w ∈ s, f w (η w) i := by
  rw [planeWordSumPi, wordSumPi_apply, Finset.sum_apply]

theorem planeWordSumPi_diag (K : ι → ℕ) (s : Finset (List Bool))
    (f : List Bool → Y → ∀ i, PlaneHk Set.univ (K i) (h i))
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (η η' : Y) i, f w (c • η + η') i = c • f w η i + f w η' i)
    (ξ : Y) (i : ι) :
    planeWordSumPi K s f hf (wordDiag s ξ) i = ∑ w ∈ s, f w ξ i := by
  rw [planeWordSumPi, wordSumPi_diag, Finset.sum_apply]

/-- `wordSum` for families of `PlaneHk` values. -/
def planeWordSum (K : ι → ℕ) (s : Finset (List Bool))
    (f : List Bool → Y → ∀ i, PlaneHk Set.univ (K i) (h i))
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (η η' : Y) i, f w (c • η + η') i = c • f w η i + f w η' i) :
    Y →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)) :=
  wordSum s f (fun w hw c η η' => funext fun i => hf w hw c η η' i)

theorem planeWordSum_apply (K : ι → ℕ) (s : Finset (List Bool))
    (f : List Bool → Y → ∀ i, PlaneHk Set.univ (K i) (h i))
    (hf : ∀ w ∈ s, ∀ (c : ℝ) (η η' : Y) i, f w (c • η + η') i = c • f w η i + f w η' i)
    (ξ : Y) (i : ι) :
    planeWordSum K s f hf ξ i = ∑ w ∈ s, f w ξ i := by
  rw [planeWordSum, wordSum_apply, Finset.sum_apply]

end PlaneMaps

section Following

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The following-block cell solutions read with the cover's following chart metric. -/
theorem coupled_following_windowCover {Y : Type*} (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (l₀ : ℤ) (P : ℕ) (hP : 1 ≤ P) (ν : ℝ)
    (y₀ : Vec 2) (D : ℕ) (K : ι → ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (V : Y → ∀ i, PlaneHk Set.univ (K i) (h i)) (uH : Y → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wH : Y → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : ∀ η, IsCoupledWeakSolutionPlane 1 a b
      (ocCellDrift α q Λ ζfast m ν
        (windowCoverChartCentre α q Λ m φ hφ l₀ P y₀ (windowCoverFollowingChartIndex P hP))) D K
      (planeMetricSourceCoefficient K D (ocCellMetric α q Λ m φ hφ (l₀ + 1) ν
        (windowCoverChartCentre α q Λ m φ hφ l₀ P y₀ (windowCoverFollowingChartIndex P hP))) A)
      (V η) (fun _ _ => 0) (fun _ _ => 0) (uH η) (wH η)) :
    ∀ η, IsCoupledWeakSolutionPlane 1 a b
      (ocCellDrift α q Λ ζfast m ν
        (windowCoverChartCentre α q Λ m φ hφ l₀ P y₀ (windowCoverFollowingChartIndex P hP))) D K
      (planeMetricSourceCoefficient K D
        (windowCoverCellMetric α q Λ m φ hφ l₀ P ν y₀ (windowCoverFollowingChartIndex P hP)) A)
      (V η) (fun _ _ => 0) (fun _ _ => 0) (uH η) (wH η) := by
  intro η
  unfold windowCoverCellMetric
  rw [windowCoverFollowingChartIndex_label]
  exact hs η

/-- Cell solutions as the named proposition. -/
theorem blockCellSolutions_of {X : Type*} [AddCommGroup X] [Module ℝ X] (D : ℕ) (K : ι → ℕ)
    (a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i)))
    (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wH : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : ∀ ξ, IsCoupledWeakSolutionPlane 1 a b v D K (planeMetricSourceCoefficient K D G A)
      (V₀ ξ) (fun _ _ => 0) (fun _ _ => 0) (uH ξ) (wH ξ)) :
    BlockCellSolutions D K a b v G A V₀ uH wH := hs

/-- A cell solution from equal data. -/
theorem coupled_datum_congr {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h i))}
    {f f' : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {Fo : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)} {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f Fo g u w) (hf : f = f') :
    IsCoupledWeakSolutionPlane ν a b v D K A f' Fo g u w := hf ▸ hs

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The physical bound with equal retained endpoints. -/
theorem physicalBound_congr {X : Type*} {K : ι → ℕ} (π : ι → ℝ) (ρ t : ℝ)
    (U : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (R : ∀ i, PlaneHk Set.univ (K i) (h i) →L[ℝ] PlaneHk Set.univ (K i) (h i))
    (T T' : X → ∀ i, PlaneHk Set.univ (K i) (h i)) (Bd : X → ℝ≥0∞)
    (hb : ∀ ξ, ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq ρ (U ξ i t - R i (T ξ i)).val) ≤
      Bd ξ)
    (hT : ∀ ξ i, T ξ i = T' ξ i) :
    ∀ ξ, ENNReal.ofReal (∑ i, (π i)⁻¹ * factorialNormSq ρ (U ξ i t - R i (T' ξ i)).val) ≤
      Bd ξ := by
  intro ξ
  have h := hb ξ
  simp only [hT] at h
  exact h

end Following

/-- A gain condition for `max a b` gives the gain conditions for `a` and `b`. -/
theorem gain_of_max {a b g ζ : ℝ} (hg : 0 ≤ g) (hζ : 0 ≤ ζ)
    (h : ENNReal.ofReal (max a b * g * ζ) ≤ 1) :
    ENNReal.ofReal (a * g * ζ) ≤ 1 ∧ ENNReal.ofReal (b * g * ζ) ≤ 1 :=
  ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left a b) hg) hζ)).trans h,
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right a b) hg) hζ)).trans h⟩

/-- The retained bound of the block word geometry in the factor order of `εpre * Ein`. -/
theorem pricePre_reassoc (A B P Q f E : ℝ≥0∞) :
    A * (B * (P * Q * (f * E))) = A * (B * (P * Q)) * f * E := by
  ring

/-- The retained bound of the block word geometry on a transported datum, bounded by `εpost` times the energy of the
datum before the transition. -/
theorem pricePost_le {A B P Q f g E E' : ℝ≥0∞} (hE : E' ≤ g * E) :
    A * (B * (P * Q * (f * E'))) ≤ A * (B * (P * Q)) * f * g * E := by
  rw [pricePre_reassoc]
  calc A * (B * (P * Q)) * f * E' ≤ A * (B * (P * Q)) * f * (g * E) := mul_le_mul_right hE _
    _ = A * (B * (P * Q)) * f * g * E := by ring
end

/-! **The two-block theorem, the word data of the two blocks**.

From the conclusion of the block word geometry on a block (`BlockWordConclusion`), in an abstract context:

* `pre_word_maps`: the old retained endpoint `Tpre = Σ_wo uO wo · (last) b` as a linear map, its
  version `Tpre'` on the datum space `List Bool → X` (one datum per word; `Tpre'` at the diagonal is
  `Tpre`), finite moments of both, and the retained bound for `Tpre` of the block word geometry;
* `post_word_maps`: the future retained endpoint at the diagonal datum, `Tret`, and the retained
  bound of the block word geometry for it;
* `datum_diag_eq`, `datumEnergy_le`: the future datum at the diagonal is the transition of `Tpre`,
  and its energy is bounded through that of `Tpre`.

The main proof of the two-block theorem only instantiates these lemmas, so no word-chain clause is re-elaborated in
its context. -/

section
attribute [local instance] blockRawPlanePiAddGroup blockRawPlanePiAddMonoid blockRawPlanePiModule

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}
  {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- **The old word data.** -/
theorem pre_word_maps (K : ι → ℕ) (J H : ℕ) (Gfr : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (M S : CycleLetter ι h D) (X₀ : Vec 2) (δ a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i))) (ϖ rs : ℝ) (n : ℕ) (π : ι → ℝ)
    (uH : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (Bd : X → ℝ≥0∞)
    (hpre : BlockWordConclusion K J H Gfr M S X₀ δ a b v V₀ ϖ rs n π uH b Bd) :
    ∃ (Tpre' : (List Bool → X) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
      (Tpre : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i))),
      (∀ η i, Tpre' η i = ∑ wo ∈ blockWords J H, Classical.choose hpre wo (η wo) (Fin.last _) i b) ∧
      (∀ ξ, Tpre' (wordDiag (blockWords J H) ξ) = Tpre ξ) ∧
      (∀ η r i, weightedFactorialNormSq r ϖ 0 rs (K i) (Tpre' η i) ≠ ⊤) ∧
      (∀ ξ r i, weightedFactorialNormSq r ϖ 0 rs (K i) (Tpre ξ i) ≠ ⊤) ∧
      ∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ 0 rs (K i) (uH ξ i b - Tpre ξ i)) ≤ Bd ξ := by
  obtain ⟨-, hlin, hfin, -, hbd⟩ := Classical.choose_spec (Classical.choose_spec hpre)
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hlinO := fun (wo : List Bool) (hwo : wo ∈ blockWords J H) (c : ℝ) (ξ ξ' : X) (i : ι) =>
    hlin wo hwo c ξ ξ' (Fin.last _) i b hb
  let fO : List Bool → X → ∀ i, PlaneHk Set.univ (K i) (h i) := fun wo ξ i =>
    Classical.choose hpre wo ξ (Fin.last _) i b
  refine ⟨planeWordSumPi K (blockWords J H) fO hlinO, planeWordSum K (blockWords J H) fO hlinO,
    planeWordSumPi_apply K _ fO hlinO, fun ξ => funext fun i => ?_, fun η r i => ?_,
    fun ξ r i => ?_, fun ξ => ?_⟩
  · rw [planeWordSumPi_diag, planeWordSum_apply]
  · rw [planeWordSumPi_apply]
    exact weightedFactorialNormSq_finset_sum_ne_top r ϖ 0 _ _ _
      fun wo hwo => hfin wo hwo (η wo) r i b hb
  · rw [planeWordSum_apply]
    exact weightedFactorialNormSq_finset_sum_ne_top r ϖ 0 _ _ _
      fun wo hwo => hfin wo hwo ξ r i b hb
  · refine (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)).trans (hbd ξ)
    rw [planeWordSum_apply]

/-- **The future word data**, at the diagonal datum of the word set `s`. -/
theorem post_word_maps (K : ι → ℕ) (J H : ℕ) (Gfr : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (M S : CycleLetter ι h D) (X₀ : Vec 2) (δ a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (V₀' : (List Bool → X) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i))) (ϖ rs : ℝ) (n : ℕ)
    (π : ι → ℝ) (uH' : (List Bool → X) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (τ : ℝ)
    (hτ : τ ∈ Set.Icc a b) (Bd' : (List Bool → X) → ℝ≥0∞) (s : Finset (List Bool))
    (hpost : BlockWordConclusion K J H Gfr M S X₀ δ a b v V₀' ϖ rs n π uH' τ Bd') :
    ∃ Tret : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)),
      (∀ ξ i, Tret ξ i = ∑ wf ∈ blockWords J H,
        Classical.choose hpost wf (wordDiag s ξ) (Fin.last _) i τ) ∧
      ∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ 0 rs (K i) (uH' (wordDiag s ξ) i τ - Tret ξ i)) ≤
        Bd' (wordDiag s ξ) := by
  obtain ⟨-, hlin, -, -, hbd⟩ := Classical.choose_spec (Classical.choose_spec hpost)
  have hlinW := fun (wf : List Bool) (hwf : wf ∈ blockWords J H) (c : ℝ)
      (η η' : List Bool → X) (i : ι) => hlin wf hwf c η η' (Fin.last _) i τ hτ
  let fW : List Bool → (List Bool → X) → ∀ i, PlaneHk Set.univ (K i) (h i) := fun wf η i =>
    Classical.choose hpost wf η (Fin.last _) i τ
  refine ⟨(planeWordSum K (blockWords J H) fW hlinW).comp (wordDiag s), fun ξ i => ?_,
    fun ξ => ?_⟩
  · rw [LinearMap.comp_apply, planeWordSum_apply]
  · refine (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)).trans (hbd (wordDiag s ξ))
    rw [LinearMap.comp_apply, planeWordSum_apply]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The future datum at the diagonal is the transition of the old endpoint. -/
theorem datum_diag_eq {K : ι → ℕ}
    (V₀' : (List Bool → X) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tpre' : (List Bool → X) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tpre : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tr : ∀ i, PlaneHk Set.univ (K i) (h i) →L[ℝ] PlaneHk Set.univ (K i) (h i))
    (s : Finset (List Bool)) (hident : ∀ η i, V₀' η i = Tr i (Tpre' η i))
    (hdiag : ∀ ξ, Tpre' (wordDiag s ξ) = Tpre ξ) (ξ : X) :
    V₀' (wordDiag s ξ) = fun i => Tr i (Tpre ξ i) := by
  funext i
  rw [hident, hdiag]

omit [∀ i, FiniteDimensional ℝ (h i)] [AddCommGroup X] [Module ℝ X] in
/-- The energy of a datum through the energy of the transition of the old endpoint. -/
theorem datumEnergy_le {K : ι → ℕ} (π : ι → ℝ) (N : ℕ) (ϖ rs : ℝ) (g : ℝ≥0∞)
    (Vd T : X → ∀ i, PlaneHk Set.univ (K i) (h i))
    (Tr : ∀ i, PlaneHk Set.univ (K i) (h i) →L[ℝ] PlaneHk Set.univ (K i) (h i))
    (hdat : ∀ ξ, Vd ξ = fun i => Tr i (T ξ i))
    (hE : ∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq N ϖ 0 rs (K i) (Tr i (T ξ i))) ≤
      g * ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 rs (K i) (T ξ i))
    (ξ : X) :
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 rs (K i) (Vd ξ i)) ≤
      g * ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq N ϖ 0 rs (K i) (T ξ i) := by
  rw [hdat ξ]
  exact hE ξ

omit [∀ i, FiniteDimensional ℝ (h i)] [AddCommGroup X] [Module ℝ X] in
/-- Energies of differences with equal first terms. -/
theorem energySub_congr {K : ι → ℕ} (π : ι → ℝ) (n : ℕ) (ϖ rs : ℝ)
    (U U' T : X → ∀ i, PlaneHk Set.univ (K i) (h i)) (hU : ∀ ξ i, U ξ i = U' ξ i) (ξ : X) :
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 rs (K i) (U ξ i - T ξ i)) =
      ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 rs (K i) (U' ξ i - T ξ i) := by
  simp only [hU]
end

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! The remaining closed ingredient is the Taylor remainder of the full source,
read in the block chart. Constants precede all family and scale data. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

def BlockRawRemainderStatement : Prop :=
  ∀ (D Kmax Jchart Jm : ℕ) (_hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) (Ks : ℕ) (_hKsJ : Ks + D + 2 ≤ Jchart),
    ∃ Crem : ℝ, 0 ≤ Crem ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (CG : ℕ → ℝ) (y₀ : Vec 2)
        (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀)
        (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
        (_ha : 0 ≤ ocA α q Λ (m - 1)),
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
        [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
        (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ : ℝ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (ic : Fin (P + 2)) (a b : ℝ) (_hab : a ≤ b),
        Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
        ∀ l : ℤ, σ = (l : ℝ) * ocTauPP α q Λ m → (l = l₀ ∨ σ ∈ Set.Icc tS tZ) →
        (∀ t ∈ Set.Icc a b, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
          ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
        ∀ S : Set ℝ, IsCoreOutside α q Λ m F tS tZ S →
        F.IsFastIndependentOn (S ∩ Set.Icc tS tZ) →
        ∀ θ : ℝ, (∀ v, ∑ u, B v u ≤ θ) → (∀ u, ∑ v, B v u ≤ θ) →
        F.IsDescending K → Ks + 1 ≤ Jm → 0 ≤ θ →
    let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
    let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)
    ∀ (Tfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))),
    (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
      (fun x τ => planeRawCouplingFlux K D τ
        (preparationReferenceCellSourceCoefficient F hφ σ ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K yc)
        (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
          (volume.restrict (Set.Icc a b)) (x u) τ) v) (Tfull v)) →
    ∃ Rs : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))) →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b)),
    (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
        (fun x t z => ∑ u, ∑ γ, blockLetterRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
          (ν⁻¹ * (ocEpsilon q Λ m) ^ 2) hφ l
          σ (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) yc ϖ (ρ / (ocEpsilon q Λ m))
          (volume.restrict (Set.Icc a b)) v u γ (x u) t z)
        (Tfull v - Rs v)) ∧
    (∀ (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
      (volume.restrict (Set.Icc a b))) (n : ℕ),
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / (ocEpsilon q Λ m)) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / (ocEpsilon q Λ m)) 0 (volume.restrict (Set.Icc a b))
        (Rs v Z) τ)
      ∂volume.restrict (Set.Icc a b)) ≤
      ENNReal.ofReal ((ζ ^ (Ks + 1) * (Crem * θ)) ^ 2) *
      ∫⁻ τ, ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + (Ks + 1))
        ϖ 0 (ρ / (ocEpsilon q Λ m)) (K u)
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / (ocEpsilon q Λ m)) 0
          (volume.restrict (Set.Icc a b)) (Z u) τ) ∂volume.restrict (Set.Icc a b))

end AVRegularity.CycleJointProofs.Assembly
end
end
