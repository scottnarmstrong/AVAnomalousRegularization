-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.BlockRawRemainder
import AVRegularity.CycleJoint.Assembly.BlockTransitionJets
import AVRegularity.CycleJoint.PreparationFollowingRetainedEndpointOnRetainedSeam

section
/-! The closed original-family block remainder, including its literal readout
and all-moment mass bound on the supplied renewal window. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The block-chart Taylor remainder is constructed from the original family,
with its constant fixed before any family or physical scale is chosen. -/
theorem blockRawRemainder : BlockRawRemainderStatement.{u, v, w, x} := by
  classical
  intro D Kmax Jchart Jm hchart _hmol Cm Cchart Ks hKsJ
  let M := max Kmax (Ks + 1)
  let Cjet := blockCommonChartPrice Ks Kmax D M Jchart Cchart
  let Crem := (D : ℝ) * blockRemainderGraphConstant Ks Kmax Cjet Cm
  have hCj : 0 ≤ Cjet := blockCommonChartPrice_nonneg Ks Kmax D M Jchart Cchart
  refine ⟨Crem, mul_nonneg (Nat.cast_nonneg _) (blockRemainderGraphConstant_nonneg _ _ _ _), ?_⟩
  intro α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc hcover σ henv yc ic a b _hab hwindow l hσ hpath hblock S hcoreS hquiet θ hrow hcol hdesc hKs hθ
  dsimp only
  intro Tfull hfull
  let e := ocEpsilon q Λ m
  let E := ocEpsilon q Λ (m - 1)
  let ϖ := e / Real.sqrt (Bcover * ocTauPP α q Λ m)
  let ζ := Real.sqrt (Bcover * ocTauPP α q Λ m) / E
  let μ := volume.restrict (Set.Icc a b)
  let pieces := (F.locally_finite tS tZ).toFinset
  have he : 0 < e := Construction.Stream.ocEpsilon_pos hΛ
  have hE : 0 < E := Construction.Stream.ocEpsilon_pos hΛ
  let data : BlockMolecularInputs F π K Kmax (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
      ν e E ρ Cm Jm B := ⟨hπ, hK, cov.pos.1, he, hE, cov.pos.2.2, henv⟩
  obtain ⟨_hsub, htime, hϖ, hfit, _hζ, hζ1, hδ⟩ :=
    windowCover_native_subwindow_scales hΛ hφ cov ic a b hwindow
  have hζpos : 0 < ζ := div_pos (Real.sqrt_pos.mpr
    (mul_pos cov.pos.2.1 (Construction.Stream.ocTauPP_pos hΛ))) hE
  have hρE : ρ ≤ E := cov.rho_e.trans heE
  have hMchart : M + D ≤ Jchart := by dsimp only [M]; omega
  have htimem (τ : ℝ) (hτ : τ ∈ Set.Icc a b) : (ν⁻¹ * e ^ 2) * τ ∈ Set.Icc tS tZ := by
    simpa only [mul_assoc] using htime τ hτ
  have hcharts (p : pieces) : BlockSourceChartInputs α q Λ m (Φ (m - 1)) hφ
      tS tZ Cpad Cage Jchart Cchart (F.piece p.val).anchor σ := by
    have hp := (F.locally_finite tS tZ).mem_toFinset.mp p.property
    have hg := preparation_piece_anchor_mem_geometry hc p.val hp
    rcases hpath with hl₀ | hσwin
    · have hσ₀ : σ = (l₀ : ℝ) * ocTauPP α q Λ m := by simpa only [hl₀] using hσ
      rw [hσ₀]
      have hh := preparation_reference_anchor_endpoints hc p.val hp (Construction.Stream.ocTauPP_pos hΛ).le
      exact ⟨hc.flow, ha, hh.1, hh.2.1, hh.2.2⟩
    · exact ⟨hc.flow, ha, hc.schedule.geometry_padded p.val hp hg,
        preparation_reference_time_padded hc hcover σ hσwin,
        preparation_piece_to_window_reference_age hc hcover p.val hp _ hg σ hσwin⟩
  obtain ⟨T, hT, hden⟩ := exists_blockPieceRemainder_maps data hwmeas hmeas hdesc Ks M hKs
    (le_max_left _ _) (le_max_right _ _) hMchart pieces actual l σ hcharts (ν⁻¹ * e ^ 2) a b htimem
    yc hρE ζ ϖ hζpos hζ1 hϖ hδ hfit μ
  let Rs := nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p)
  refine ⟨Rs, ?_, ?_⟩
  · intro v
    have hr : IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
        (fun x τ z => ∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p : pieces,
          blockPieceRemainderNativeArray Ks F p.val (actual p.val) v u γ hφ l σ e E (ν⁻¹ * e ^ 2)
            a b yc (j.val + 1) τ z (WithLp.toLp 2 (fun I => planeJetOrder
              (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ (x u) τ) (j.val + 1) I z))) (Rs v) := by
      unfold Rs nativeFamilyEdgeForcingMap
      apply planeRaw_allMoment_linearMap_sum
      intro u
      have hh : IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
          (fun x τ z => ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p : pieces,
            blockPieceRemainderNativeArray Ks F p.val (actual p.val) v u γ hφ l σ e E (ν⁻¹ * e ^ 2)
              a b yc (j.val + 1) τ z (WithLp.toLp 2 (fun I => planeJetOrder
                (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) (j.val + 1) I z)))
          (∑ γ, ∑ j, ∑ p, T v u γ j p) := by
        apply planeRaw_allMoment_linearMap_sum
        intro γ
        apply planeRaw_allMoment_linearMap_sum
        intro j
        exact planeRaw_allMoment_linearMap_sum (K v) ϖ (ρ / e) 0 μ _ _ (hT v u γ j)
      intro x
      exact hh (x u)
    have hs := planeRaw_allMoment_linearMap_sub (K v) ϖ (ρ / e) 0 μ _ _ _ _ (hfull v) hr
    intro x
    filter_upwards [hs x, ae_restrict_mem measurableSet_Icc] with τ hτ hm
    filter_upwards [hτ] with z hz
    have hEll : ocEll q Λ m ν ^ 2 = ν⁻¹ * e ^ 2 := by
      rw [CycleReference.ocEll_sq_eq cov.pos.1, div_eq_mul_inv, mul_comm]
    have hflux := blockReferenceCellSourceFlux_split data hc hΛ actual hdesc Ks hKs l σ hσ S hcoreS hquiet
      yc z a b τ hm (htimem τ hm) (by simpa only [hEll] using hblock τ hm)
      (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ (x u) τ) v
    have hsort (u : ι) (γ : F.Γ v u) (j : Fin D) := pieces.sum_coe_sort
      (fun p => blockPieceRemainderNativeArray Ks F p (actual p) v u γ hφ l σ e E (ν⁻¹ * e ^ 2)
        a b yc (j.val + 1) τ z (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ (x u) τ) (j.val + 1) I z)))
    dsimp only [E, pieces] at hsort
    simp_rw [← hsort] at hflux
    apply hz.trans
    simp only [blockLetterRawConstituent]
    exact sub_eq_iff_eq_add.mpr hflux
  · intro Z n
    exact blockRemainder_piece_order_mass_budget data Ks hKs Cjet ζ ϖ hCj hζpos.le μ pieces
      (ν⁻¹ * e ^ 2) θ hθ hB hrow hcol T hden Z n

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! The exact block edge package follows from the closed raw Taylor remainder.
The existing native packages discharge the full-source energy and Schur bounds. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- Assembly at the fixed statement, with only the new block-chart remainder open. -/
theorem blockEdgePackage_of_raw_remainder (hrem : BlockRawRemainderStatement.{u, v, w, x}) :
    BlockEdgePackageStatement.{u, v, w, x} := by
  classical
  intro D Kmax Jchart Jm hchart hmol Cm Cchart Ks hKsJ
  obtain ⟨Cprep, hCprep, hnative⟩ := blockNativeFull D Kmax Jchart Jm hchart hmol Cm Cchart Ks hKsJ
  obtain ⟨Crem, hCrem, hrem⟩ := hrem D Kmax Jchart Jm hchart hmol Cm Cchart Ks hKsJ
  refine ⟨Cprep, Crem, hCprep, hCrem, ?_⟩
  intro α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
    qJ CG y₀ cov hΛ heE ha ι _ h _ _ _ _ _ _ P' Ctx F hmeas hwmeas π hπ K hK actual B hB
    hc hcover σ henv yc ic a b hab hwindow l hσ hpath hblock S hcoreS hquiet θ hrow hcol hdesc hKs hθ
  dsimp only
  let ϖ := ocEpsilon q Λ m / Real.sqrt (Bcover * ocTauPP α q Λ m)
  let rc := ρ / ocEpsilon q Λ m
  let μ := volume.restrict (Set.Icc a b)
  obtain ⟨Tfull, hfull, hmass, hrow', hcol'⟩ :=
    hnative α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
      qJ CG y₀ cov hΛ heE ha F hmeas hwmeas π hπ K hK actual B hB hc hcover σ henv yc ic a b
      hab hwindow l hσ hpath hblock S hcoreS hquiet θ hrow hcol hdesc hKs hθ
  obtain ⟨Rs, hTaylor, hbudget⟩ :=
    hrem α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb
      qJ CG y₀ cov hΛ heE ha F hmeas hwmeas π hπ K hK actual B hB hc hcover σ henv yc ic a b
      hab hwindow l hσ hpath hblock S hcoreS hquiet θ hrow hcol hdesc hKs hθ Tfull hfull
  obtain ⟨Ledge, hraw, hread, hgraph, hdegree⟩ :=
    nativeRawOriginalFamilyMap_taylor_split_edges F K ϖ rc 0 μ
      (fun v u γ => blockLetterRawConstituent Ks F (F.locally_finite tS tZ).toFinset actual K
        (ν⁻¹ * ocEpsilon q Λ m ^ 2) hφ l σ (ocEpsilon q Λ m)
        (ocEpsilon q Λ (m - 1)) yc ϖ rc μ v u γ)
      (fun v u γ => blockLetterRawConstituent_zero Ks F (F.locally_finite tS tZ).toFinset actual K
        (ν⁻¹ * ocEpsilon q Λ m ^ 2) hφ l σ (ocEpsilon q Λ m)
        (ocEpsilon q Λ (m - 1)) yc ϖ rc μ v u γ)
      Tfull Rs hTaylor _ hfull
  have he v : nativeFamilyEdgeForcingMap Ledge v + Rs v = Tfull v :=
    planeRaw_allMoment_map_unique (K v) ϖ rc 0 μ _ _ _ _ (hraw v) (hfull v)
      (fun _ => Filter.Eventually.of_forall (fun _ => Filter.Eventually.of_forall (fun _ => rfl)))
  refine ⟨Rs, Ledge, ⟨hraw, hread, hgraph, hdegree⟩, hbudget, ?_, hrow', hcol'⟩
  intro W n
  have hvalues : (fun v => (nativeFamilyEdgeForcingMap Ledge v + Rs v) W) =
      (fun v => Tfull v W) := funext (fun v => congrArg (fun L => L W) (he v))
  rw [hvalues]
  exact hmass W n

/-- The exact block edge package, with the constructed block remainder discharged. -/
theorem blockEdgePackage : BlockEdgePackageStatement.{u, v, w, x} :=
  blockEdgePackage_of_raw_remainder blockRawRemainder

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The two-block theorem on its window: statement**.

The two-block theorem (`TwoBlockWordConclusion`: the retained endpoints read as word sums
of the block letters) stated over the joint premises `JointPremisesGen` (abstract radius `r`) and on
the two-block window: the old block from `tS` to the seam `(l₀ + 1/2) τ''` (the first renewal after `tS`),
the future block from the seam to `t_p = (l₀ + 3/2) τ''`, the physical endpoint at `t_p`
(`cellTime` is the cell time `ε_m⁻² ν t = t / ℓ_m²`).

* `TwoBlockWindows`: the window facts, from the cover (`twoBlockWindows_of`);
* `twoV₀`, `twoTransit`, `twoReturn`: the cell datum of the patch, the chart transition at the
  seam and the return at `t_p`, as functions of the premises;
* `TwoBlockJointConclusion`: the conclusion of the two-block theorem for one family, one patch and one allocation of the
  letters (`θM₁ θS₁ bM₁ bS₁` for the old block, `θM₂ θS₂ bM₂ bS₂` for the future block);
* `TwoBlockJointStatement`: the two-block theorem. The weights `Cw` and the threshold `Λ₀` are universal; the
  constants depend only on the orders and the supplied jet bounds; the moment normalizations
  `Lpre`, `Lpost` on the moment orders. The gain `C_T g R/E ≤ 1` is a hypothesis (a starting
  level discharges it).

The premises bundled in `JointPremisesGen` are elaborated once, so the statements of the stages of
the proof (`TwoBlockJoint*`) are cheap. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The cell time `ε_m⁻² ν t` of a physical time `t`. -/
def cellTime (q : ℝ) (Λ m : ℕ) (ν t : ℝ) : ℝ := (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * t)

/-- The seam of the two-block window: the first renewal `(l₀ + 1/2) τ''` after `tS`. -/
def twoSeam (α q : ℝ) (Λ m : ℕ) (l₀ : ℤ) : ℝ := ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m

/-- The endpoint `t_p = (l₀ + 3/2) τ''` of the two-block window. -/
def twoTp (α q : ℝ) (Λ m : ℕ) (l₀ : ℤ) : ℝ := ((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m

/-- `ocA` is nonnegative. -/
theorem ocA_nonneg_of {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) : 0 ≤ ocA α q Λ m := by
  unfold ocA
  exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _

/-- The window `[tS, tS + 2 τ'']` is nonempty. -/
theorem twoWindow_le {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) (tS : ℝ) :
    tS ≤ tS + 2 * ocTauPP α q Λ m := by
  have := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  linarith

/-- **The window facts of the two blocks** (cell times). -/
structure TwoBlockWindows (α q : ℝ) (Λ m : ℕ) (ν tS : ℝ) (l₀ : ℤ) (P : ℕ) (hP : 1 ≤ P) :
    Prop where
  ab : cellTime q Λ m ν tS < cellTime q Λ m ν (twoSeam α q Λ m l₀)
  bd : cellTime q Λ m ν (twoSeam α q Λ m l₀) < cellTime q Λ m ν (twoTp α q Λ m l₀)
  windowPre : Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) ⊆
    windowCoverChartWindow α q Λ m ν tS (tS + 2 * ocTauPP α q Λ m) l₀ P
      (windowCoverReferenceChartIndex P)
  blockPre : ∀ t ∈ Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)),
    ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m
  lengthPre : cellTime q Λ m ν (twoSeam α q Λ m l₀) - cellTime q Λ m ν tS ≤
    ocTauPP α q Λ m / ocEll q Λ m ν ^ 2
  next : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)
  dZ : cellTime q Λ m ν (twoTp α q Λ m l₀) ≤
    (ocEpsilon q Λ m)⁻¹ ^ 2 * (ν * (tS + 2 * ocTauPP α q Λ m))
  blockPost : ∀ t ∈ Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)),
    (((l₀ + 1 : ℤ) : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ (((l₀ + 1 : ℤ) : ℝ) + 1 / 2) * ocTauPP α q Λ m
  windowPost : Set.Icc (cellTime q Λ m ν (twoSeam α q Λ m l₀))
      (cellTime q Λ m ν (twoTp α q Λ m l₀)) ⊆
    windowCoverChartWindow α q Λ m ν tS (tS + 2 * ocTauPP α q Λ m) l₀ P
      (windowCoverFollowingChartIndex P hP)
  lengthPost : cellTime q Λ m ν (twoTp α q Λ m l₀) - cellTime q Λ m ν (twoSeam α q Λ m l₀) ≤
    ocTauPP α q Λ m / ocEll q Λ m ν ^ 2
  seamMem : ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀)) ∈
    Set.Icc tS (tS + 2 * ocTauPP α q Λ m)
  tpMem : twoTp α q Λ m l₀ ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)
  seamTime : (ocEpsilon q Λ m)⁻¹ ^ 2 *
      (ν * (ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀)))) =
    cellTime q Λ m ν (twoSeam α q Λ m l₀)

/-- **The window facts** from the cover of `[tS, tS + 2 τ'']`. -/
theorem twoBlockWindows_of {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {ν B tS ρs g g0 strain B₀ lam Cb : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (hΛ : 1 ≤ Λ) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (cov : IsWindowCover α q Λ m ζ Φ hφ ν B tS (tS + 2 * ocTauPP α q Λ m)
      ρs g g0 strain B₀ lam Cb qJ Kmax CG l₀ P y₀) :
    TwoBlockWindows α q Λ m ν tS l₀ P cov.P_pos := by
  have hgeo := windowCover_two_block_geometry hΛ hφ cov
  dsimp only at hgeo
  obtain ⟨htpI, -, hnext, hSs, hst, hwpre, hwpost⟩ := hgeo
  have hν : 0 < ν := cov.pos.1
  have he : 0 < ocEpsilon q Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hT : 0 < ocTauPP α q Λ m := Construction.Stream.ocTauPP_pos hΛ
  have hwin := cov.window.1
  have hell : ocEll q Λ m ν ^ 2 = ν⁻¹ * ocEpsilon q Λ m ^ 2 := by
    unfold ocEll
    rw [div_pow, Real.sq_sqrt hν.le]
    ring
  have hell0 : 0 < ocEll q Λ m ν ^ 2 := by
    rw [hell]
    positivity
  have hcell : ∀ t, cellTime q Λ m ν t = t / ocEll q Λ m ν ^ 2 := by
    intro t
    unfold cellTime
    rw [hell]
    field_simp
  have hmul : ∀ t, ocEll q Λ m ν ^ 2 * cellTime q Λ m ν t = t := by
    intro t
    rw [hcell, mul_div_cancel₀ _ hell0.ne']
  have hback : ∀ t, ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν t) = t := by
    intro t
    calc ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν t) =
        ocEll q Λ m ν ^ 2 * cellTime q Λ m ν t := by rw [hell]; ring
      _ = t := hmul t
  have hlt : ∀ t t', t < t' → cellTime q Λ m ν t < cellTime q Λ m ν t' := by
    intro t t' htt
    rw [hcell, hcell]
    exact div_lt_div_of_pos_right htt hell0
  have hle : ∀ t t', t ≤ t' → cellTime q Λ m ν t ≤ cellTime q Λ m ν t' := by
    intro t t' htt
    rw [hcell, hcell]
    exact div_le_div_of_nonneg_right htt hell0.le
  have hsub : ∀ t t', cellTime q Λ m ν t' - cellTime q Λ m ν t =
      (t' - t) / ocEll q Λ m ν ^ 2 := by
    intro t t'
    rw [hcell, hcell, sub_div]
  have hseam : twoSeam α q Λ m l₀ = ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m := rfl
  have htp : twoTp α q Λ m l₀ = ((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m := rfl
  have hcast : ((l₀ + 1 : ℤ) : ℝ) = (l₀ : ℝ) + 1 := by push_cast; ring
  have hmem : ∀ t t' s, s ∈ Set.Icc (cellTime q Λ m ν t) (cellTime q Λ m ν t') →
      t ≤ ocEll q Λ m ν ^ 2 * s ∧ ocEll q Λ m ν ^ 2 * s ≤ t' := by
    intro t t' s hs
    rw [hcell, hcell] at hs
    constructor
    · have := mul_le_mul_of_nonneg_left hs.1 hell0.le
      rwa [mul_div_cancel₀ _ hell0.ne'] at this
    · have := mul_le_mul_of_nonneg_left hs.2 hell0.le
      rwa [mul_div_cancel₀ _ hell0.ne'] at this
  refine
    { ab := hlt _ _ hSs
      bd := hlt _ _ hst
      windowPre := ?_
      blockPre := ?_
      lengthPre := ?_
      next := ?_
      dZ := hle _ _ htpI.2
      blockPost := ?_
      windowPost := ?_
      lengthPost := ?_
      seamMem := ?_
      tpMem := ⟨htpI.1.le, htpI.2⟩
      seamTime := ?_ }
  · rw [hcell, hcell]
    exact hwpre
  · intro t ht
    obtain ⟨h1, h2⟩ := hmem _ _ t ht
    exact ⟨hwin.trans h1, h2⟩
  · rw [hsub]
    refine div_le_div_of_nonneg_right ?_ hell0.le
    rw [hseam]
    linarith
  · rw [hcast]
    exact hnext
  · intro t ht
    obtain ⟨h1, h2⟩ := hmem _ _ t ht
    rw [hcast]
    rw [hseam] at h1
    rw [htp] at h2
    constructor <;> linarith
  · rw [hcell, hcell]
    exact hwpost
  · rw [hsub, htp, hseam]
    refine le_of_eq ?_
    congr 1
    ring
  · rw [hback]
    exact ⟨hSs.le, (hst.trans_le htpI.2).le⟩
  · rw [hback]
    rfl

section Objects

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The window facts of the premises. -/
theorem JointPremisesGen.windows
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) :
    TwoBlockWindows α q Λ m ν tS l₀ P hp.cov.P_pos :=
  twoBlockWindows_of hΛ hφ hp.cov

/-- The chart centre of the old block (reference chart, label `l₀`). -/
def twoYc (_hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) : Vec 2 :=
  windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ (windowCoverReferenceChartIndex P)

/-- The chart centre of the future block (following chart, label `l₀ + 1`). -/
def twoYcPost (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) : Vec 2 :=
  windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
    (windowCoverFollowingChartIndex P hp.cov.P_pos)

/-- The cell metric of the old block. -/
def twoGpre (_hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ (windowCoverReferenceChartIndex P)

/-- The cell metric of the future block. -/
def twoGpost (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀
    (windowCoverFollowingChartIndex P hp.cov.P_pos)

/-- The metric letter of the old block. -/
def twoMpre (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (θM : ℝ) (bM : ι → ι → ℝ) : CycleLetter ι h D :=
  blockMetricLetter (D := D) (h := h) (twoGpre hp) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp)
    (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) Ks θM bM

/-- The source letter of the old block. -/
def twoSpre (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (θS : ℝ) (bS : ι → ι → ℝ) : CycleLetter ι h D :=
  blockSourceLetter F (F.locally_finite tS (tS + 2 * ocTauPP α q Λ m)).toFinset actual hφ
    (Set.Icc tS (tS + 2 * ocTauPP α q Λ m)) l₀ ((l₀ : ℝ) * ocTauPP α q Λ m) (twoYc hp)
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ν⁻¹ * ocEpsilon q Λ m ^ 2) Ks θS bS

/-- The metric letter of the future block. -/
def twoMpost (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (θM : ℝ) (bM : ι → ι → ℝ) : CycleLetter ι h D :=
  blockMetricLetter (D := D) (h := h) (twoGpost hp) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp)
    (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) Ks θM bM

/-- The source letter of the future block. -/
def twoSpost (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (θS : ℝ) (bS : ι → ι → ℝ) : CycleLetter ι h D :=
  blockSourceLetter F (F.locally_finite tS (tS + 2 * ocTauPP α q Λ m)).toFinset actual hφ
    (Set.Icc tS (tS + 2 * ocTauPP α q Λ m)) (l₀ + 1) (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m)
    (twoYcPost hp) (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ν⁻¹ * ocEpsilon q Λ m ^ 2) Ks θS bS

/-- **The cell datum of the patch** `patch` of mesh `Npatch` (old block, reference chart). -/
def twoV₀ (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) :
    (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)) :=
  preparationReferenceCellLocalizedInitialFamilyLinearMap hp.hprep hp.hcover
    (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1)) K
    (slot_le_chart hp.hK hchart) (twoWindow_le hΛ tS) hζ Npatch hNpatch patch
    (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYc hp)

/-- **The cell curves of the old block** of physical curves `U`. -/
def twoUH (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) {Y : Type*}
    (U : Y → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) :
    Y → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i) := fun f i =>
  preparationReferenceCellNativeCurve hp.hprep hp.hcover (Construction.Stream.ocTauPP_pos hΛ).le
    (ocA_nonneg_of hΛ (m - 1)) (K i) (slot_le_chart hp.hK hchart i) ν (ocEpsilon q Λ m)
    (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYc hp) (U f i)

/-- **The cell curves of the future block** of physical curves `U`. -/
def twoUHpost (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) {Y : Type*}
    (U : Y → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) :
    Y → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i) := fun f i =>
  preparationWindowReferenceCellNativeCurve hp.hprep hp.hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next (ocA_nonneg_of hΛ (m - 1)) (K i)
    (slot_le_chart hp.hK hchart i) ν (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne'
    (twoYcPost hp) (U f i)

/-- **The cell flux curves of the future block** of physical flux curves `W`. -/
def twoWHpost (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) {Y : Type*}
    (W : Y → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)) :
    Y → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i) := fun f i =>
  preparationWindowReferenceCellNativeCurve hp.hprep hp.hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next (ocA_nonneg_of hΛ (m - 1))
    (K i + 1) (slot_succ_le_chart hp.hK hchart i) ν (ocEpsilon q Λ m)
    (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYcPost hp) (W f i)

/-- **The chart transition at the seam** (reference chart to following chart). -/
def twoTransit (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (i : ι) :
    PlaneHk Set.univ (K i) (h i) →L[ℝ] PlaneHk Set.univ (K i) (h i) :=
  preparationReferenceCellTransitionOperator hp.hprep hp.hcover
    (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1)) (K i)
    (slot_le_chart hp.hK hchart i) (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next
    (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYc hp) (twoYcPost hp)
    (ν⁻¹ * (ocEpsilon q Λ m ^ 2 * cellTime q Λ m ν (twoSeam α q Λ m l₀))) (hp.windows hΛ).seamMem

/-- **The return to physical variables at `t_p`** (following chart). -/
def twoReturn (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (i : ι) :
    PlaneHk Set.univ (K i) (h i) →L[ℝ] PlaneHk Set.univ (K i) (h i) :=
  preparationWindowReferenceCellReturnOperator hp.hprep hp.hcover
    (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) (hp.windows hΛ).next (ocA_nonneg_of hΛ (m - 1)) (K i)
    (slot_le_chart hp.hK hchart i) (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne'
    (twoYcPost hp) (twoTp α q Λ m l₀) (hp.windows hΛ).tpMem

/-- The physical data of the patch. -/
def twoLoc (_hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hζ : IsFastProfile ζ) (Npatch : ℕ) (hNpatch : 0 < Npatch)
    (patch : Fin 2 → ℤ) (f : ∀ i, TorusHk (K i) (h i)) : ∀ i, PlaneHk Set.univ (K i) (h i) :=
  fun i => spatialPatchLocalization hζ Npatch hNpatch patch (K i) (f i)

/-- The physical solutions from the patch data on `[tS, tS + 2 τ'']`. -/
def twoPhysical (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hζ : IsFastProfile ζ) (Npatch : ℕ) (hNpatch : 0 < Npatch)
    (patch : Fin 2 → ℤ)
    (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)) : Prop :=
  PhysicalSolutions K ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
    (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
    (twoLoc hp hζ Npatch hNpatch patch) uphys wphys

/-- The energy of the cell datum at moment order `N`. -/
def twoEin (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) (N : ℕ)
    (ξ : ∀ i, TorusHk (K i) (h i)) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal ((π i)⁻¹) *
    weightedFactorialNormSq N (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
      (r / ocEpsilon q Λ m) (K i) (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch ξ i)

/-- The energy price of the first block (the first summary). -/
def twoCfirst (_hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Cw : ℕ → ℝ) (Cenergy : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((planeSourceRankScale.{u, v} N Kmax (fun j => max (CG j) 0) Cw D
      (Cenergy * (max Cth 0 * Θ))) ^ (2 * H)) *
    (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} N Kmax (fun j => max (CG j) 0) Cw))

/-- The retained price of a block (from the block word geometry), without the energy factor: moment order `n` of the
bound, moment order `N` and normalization `L` of the weights, `J` metric insertions. -/
def twoRetained (_hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Cw : ℕ → ℝ) (Cprep CR Cterminal Crem : ℝ) (n N L J : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax (fun j => max (CG j) 0) Cw D
      (Cprep * (max Cth 0 * Θ))) ^ (2 * H)) *
    (256 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax (fun j => max (CG j) 0) Cw) *
      (coupledRetainedResidualPrice
        (scalarResponseTwoInsertionCommonPrice Kmax (L : ℝ) Cw N
          (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax))
          (ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Crem)) *
          (1 + ENNReal.ofReal (max Cth 0 * Θ) ^ 2))
        (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (CR * g) ^ 2))
        (ENNReal.ofReal ((Crem * (max Cth 0 * Θ)) ^ 2))
        (ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax)) J H *
        (ENNReal.ofReal (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1)) ^ (2 * (Ks + 1)) +
          ENNReal.ofReal (Cterminal * g *
            (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))) ^ (2 * (J + 1)))))

/-- The price of the old block's retained endpoint, `εpre`. -/
def twoEpsPre (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Cw : ℕ → ℝ) (Cprep CR Cterminal Crem : ℝ) (Npre Npost Lpre Jpre : ℕ) : ℝ≥0∞ :=
  twoRetained hp Cw Cprep CR Cterminal Crem Npost Npre Lpre Jpre *
    ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npre Kmax Cw)

/-- The price of the future block's retained endpoint, `εpost`. -/
def twoEpsPost (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Cw : ℕ → ℝ) (Cprep CR Cterminal Crem : ℝ) (Npost Lpost Jpost : ℕ) :
    ℝ≥0∞ :=
  twoRetained hp Cw Cprep CR Cterminal Crem 0 Npost Lpost Jpost *
    ENNReal.ofReal (frozenWindowHomogeneousGradientConstant.{u, v} Npost Kmax Cw) *
    ENNReal.ofReal (cellTransitionMomentBudget Kmax Npost)

/-- The energy price of the following block (explicit endpoint). -/
def twoCactual (_hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (Cw : ℕ → ℝ) (Cenergy : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((planeSourceRankScale.{u, v} 0 Kmax (fun j => max (CG j) 0) Cw D
      (Cenergy * (max Cth 0 * Θ))) ^ (2 * H)) *
    (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} 0 Kmax (fun j => max (CG j) 0) Cw))

/-- **The conclusion of the two-block theorem** for one family, one patch and one choice of the letters
(`θM₁ θS₁ bM₁ bS₁` old block, `θM₂ θS₂ bM₂ bS₂` future block): `TwoBlockWordConclusion` with the
old block `[a, b]` (from `tS` to the seam), the future block `[b, d]` (from the seam to `t_p`),
the physical endpoint `t_p` and the cell endpoint `d`, the radius `r` and `θ = max Cth 0 · Θ`. -/
def TwoBlockJointConclusion
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hζ : IsFastProfile ζ) (Cw : ℕ → ℝ) (Cenergy1 Cenergy2 Cprep CR Cterminal Crem : ℝ)
    (Npre Npost Lpre Lpost : ℕ) (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ)
    (Jpre Jpost : ℕ) (θM₁ θS₁ θM₂ θS₂ : ℝ) (bM₁ bS₁ bM₂ bS₂ : ι → ι → ℝ) : Prop :=
  TwoBlockWordConclusion K ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
    (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
    (twoLoc hp hζ Npatch hNpatch patch) Jpre Jpost H
    (fun t => twoGpre hp t 0) (fun t => twoGpost hp t 0) (twoMpre hp θM₁ bM₁)
    (twoSpre hp θS₁ bS₁) (twoMpost hp θM₂ bM₂) (twoSpost hp θS₂ bS₂)
    ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYcPost hp)
    (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
    (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    (cellTime q Λ m ν (twoTp α q Λ m l₀))
    (ocCellDrift α q Λ ζ m ν (twoYc hp)) (ocCellDrift α q Λ ζ m ν (twoYcPost hp))
    (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch)
    (twoTransit hp hΛ hchart) (twoReturn hp hΛ hchart)
    (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) r π
    (twoTp α q Λ m l₀) (cellTime q Λ m ν (twoTp α q Λ m l₀))
    (fun ξ => twoBlockOriginalEnergyPrice
      (ENNReal.ofReal ((compositionFactorialNormBound (preparationFlowJetConstant Cchart)
        (Jchart + 1) * |ocEpsilon q Λ m|) ^ 2)) (twoCactual hp Cw Cenergy2)
      (ENNReal.ofReal (cellTransitionMomentBudget Kmax 0)) (twoCfirst hp Cw Cenergy1 Npre)
      (twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre)
      (twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre)
      (twoEpsPost hp Cw Cprep CR Cterminal Crem Npost Lpost Jpost) *
      twoEin hp hΛ hchart hζ Npatch hNpatch patch Npre ξ)

end Objects

/-- **The body of the two-block theorem** for given weights `Cw`, threshold `Λ₀`, orders, constants
and moment orders: for every level `Λ ≥ Λ₀`, the joint premises at an abstract radius
(`JointPremisesGen`), a quiet set `S` with the core property and fast independence on it, a patch,
word lengths `Jpre`, `Jpost` within the moment orders, the gain `C_T g R/E ≤ 1` and the letter
parameters, the conclusion of the two-block theorem holds. -/
def TwoBlockJointBody (α q : ℝ) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Cw : ℕ → ℝ) (Λ₀ : ℕ)
    (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (Cm Cchart CG : ℕ → ℝ)
    (Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem : ℝ) (Npre Npost Lpre Lpost : ℕ) : Prop :=
  ∀ (Λ : ℕ) (_hΛ₀ : Λ₀ ≤ Λ) (hΛ : 1 ≤ Λ) (g₀ : ℝ) (_hg₀ : g₀ ≤ 1 / 32) (H Ls qJ : ℕ)
    (_hD : 2 ≤ D) (_hKs : Ks + 1 ≤ Jm) (_hqJ : Ks + 1 + Kmax ≤ qJ)
    (Ca Cth Cb COld Crat Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (S : Set ℝ) (_hcoreS : IsCoreOutside α q Λ m F tS (tS + 2 * ocTauPP α q Λ m) S)
    (_hquiet : F.IsFastIndependentOn (S ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) (Jpre Jpost : ℕ)
    (_hNpre : Npost + (Ks + 1) + (Jpre + H) * (Ks + 1) ≤ Npre)
    (_hNpost : (Ks + 1) + (Jpost + H) * (Ks + 1) ≤ Npost)
    (_hgain : ENNReal.ofReal (CT * g * (Real.sqrt (B * ocTauPP α q Λ m) /
      ocEpsilon q Λ (m - 1))) ≤ 1)
    (θM₁ θS₁ θM₂ θS₂ : ℝ) (bM₁ bS₁ bM₂ bS₂ : ι → ι → ℝ),
    TwoBlockJointConclusion hp hΛ hchart hζ Cw Cenergy1 Cenergy2 Cprep CR Cterminal Crem Npre
      Npost Lpre Lpost Npatch hNpatch patch Jpre Jpost θM₁ θS₁ θM₂ θS₂ bM₁ bS₁ bM₂ bS₂

/-- **The two-block theorem: the two blocks in word form** (the two-block theorem with the retained
endpoints read as word sums of the block letters, on the joint premises at an abstract radius). The
weights `Cw` and the threshold `Λ₀` are universal; the constants depend only on the orders and the
supplied jet bounds; the moment normalizations on the moment orders. -/
def TwoBlockJointStatement : Prop :=
  ∀ {α s q : ℝ} (_hα0 : 0 < α) (_hα1 : α < 1 / 3) (_hs0 : 0 < s) (_hs1 : s < (1 - α) / 2)
    (_hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ),
  ∃ (Cw : ℕ → ℝ) (Λ₀ : ℕ), 128 ≤ Λ₀ ∧
  ∀ (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (_hKsJ : Ks + D + 2 ≤ Jchart) (Cm Cchart CG : ℕ → ℝ),
  ∃ Cenergy1 Cenergy2 Cprep CT CR Cterminal Crem : ℝ, 1 ≤ Cenergy1 ∧ 1 ≤ Cenergy2 ∧
    1 ≤ Cprep ∧ 0 ≤ CT ∧ 0 ≤ CR ∧ 0 ≤ Cterminal ∧ 0 ≤ Crem ∧
  ∀ Npre Npost : ℕ, ∃ Lpre Lpost : ℕ, 1 ≤ Lpre ∧ 1 ≤ Lpost ∧
    TwoBlockJointBody.{u, v, w, x} α q hζ Cw Λ₀ D Ks Kmax Jchart Jm hchart Cm Cchart CG Cenergy1
      Cenergy2 Cprep CT CR Cterminal Crem Npre Npost Lpre Lpost

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The two-block theorem on its window, the old block**.

`twoBlockJoint_old`: on the old block `[tS, seam]` (cell times), the first-block summary gives
the physical solutions from the patch data and the cell solutions `uH` from the cell datum, with
the energy of `Upre = uH(seam)`; `BlockWordBody` gives the old word chains with its retained
bound; `pre_word_maps` gives the old endpoint `Tpre` (the word sum) and its version `Tpre'` on the
datum space `List Bool → X`. The output is the named proposition `TwoBlockOldFacts`, so that the
later stages do not re-elaborate the clauses.

* `twoPhysical_of`: the physical solutions as `twoPhysical` (its own declaration: the solution
  clause is elaborated in the two-block statement and in `PhysicalSolutions` separately).
* `JointPremisesGen.scales`: the scale facts used by the two-block theorem (`ε_m ≤ ε_{m-1}`, `ε_m⁻¹ ∈ ℕ`, …). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

local instance twoBlockOldTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance twoBlockOldTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance twoBlockOldTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance
local instance twoBlockOldTorusPiAdd {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    AddCommMonoid (∀ i, TorusHk (K i) (h i)) := inferInstance
local instance twoBlockOldTorusPiModule {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] (K : ι → ℕ) :
    Module ℝ (∀ i, TorusHk (K i) (h i)) := inferInstance

section Old

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- The physical solutions from the patch data, as `twoPhysical`. -/
theorem twoPhysical_of
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hζ : IsFastProfile ζ) (Npatch : ℕ) (hNpatch : 0 < Npatch)
    (patch : Fin 2 → ℤ)
    (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : ∀ f, IsCoupledWeakSolutionPlane ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      (fun i => spatialPatchLocalization hζ Npatch hNpatch patch (K i) (f i))
      (fun _ _ => 0) (fun _ _ => 0) (uphys f) (wphys f)) :
    twoPhysical hp hζ Npatch hNpatch patch uphys wphys := hs

/-- **The facts of the old block** for the physical solutions `uphys, wphys`, the cell endpoint
`Upre`, the conclusion `hpre` of the block word geometry on the old block (bound `Bdpre`) and the old word endpoints
`Tpre'` (one datum per word) and `Tpre` (diagonal). -/
def TwoBlockOldFacts
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (Cw : ℕ → ℝ) (Cenergy1 Cprep CR Cterminal Crem : ℝ) (Npre Npost Lpre : ℕ)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) (Jpre : ℕ)
    (θM₁ θS₁ : ℝ) (bM₁ bS₁ : ι → ι → ℝ)
    (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (Upre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Bdpre : (∀ i, TorusHk (K i) (h i)) → ℝ≥0∞)
    (hpre : BlockWordConclusion K Jpre H (fun t => twoGpre hp t 0) (twoMpre hp θM₁ bM₁)
      (twoSpre hp θS₁ bS₁) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp)
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) (cellTime q Λ m ν tS)
      (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch)
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) Npost π
      (twoUH hp hΛ hchart uphys) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) Bdpre)
    (Tpre' : (List Bool → ∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tpre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i))) : Prop :=
  twoPhysical hp hζ Npatch hNpatch patch uphys wphys ∧
  (∀ ξ i, Upre ξ i = twoUH hp hΛ hchart uphys ξ i (cellTime q Λ m ν (twoSeam α q Λ m l₀))) ∧
  (∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq Npre (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
        (r / ocEpsilon q Λ m) (K i) (Upre ξ i)) ≤
    twoCfirst hp Cw Cenergy1 Npre * twoEin hp hΛ hchart hζ Npatch hNpatch patch Npre ξ) ∧
  (∀ ξ k, k ≤ Npre → ∀ i,
    weightedFactorialNormSq k (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
      (r / ocEpsilon q Λ m) (K i) (Upre ξ i) ≠ ⊤) ∧
  (∀ η i, Tpre' η i = ∑ wo ∈ blockWords Jpre H,
    Classical.choose hpre wo (η wo) (Fin.last _) i (cellTime q Λ m ν (twoSeam α q Λ m l₀))) ∧
  (∀ ξ, Tpre' (wordDiag (blockWords Jpre H) ξ) = Tpre ξ) ∧
  (∀ η k i, weightedFactorialNormSq k (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
      (r / ocEpsilon q Λ m) (K i) (Tpre' η i) ≠ ⊤) ∧
  (∀ ξ k i, weightedFactorialNormSq k (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
      (r / ocEpsilon q Λ m) (K i) (Tpre ξ i) ≠ ⊤) ∧
  ∀ ξ, (∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq Npost (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0
        (r / ocEpsilon q Λ m) (K i) (Upre ξ i - Tpre ξ i)) ≤
    twoEpsPre hp Cw Cprep CR Cterminal Crem Npre Npost Lpre Jpre *
      twoEin hp hΛ hchart hζ Npatch hNpatch patch Npre ξ

/-- **The output of the old block**: physical solutions, the cell endpoint, the conclusion of the block word geometry on the
old block and the old word endpoints, with `TwoBlockOldFacts`. -/
def TwoBlockOldOut
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) (hΛ : 1 ≤ Λ) (hchart : Kmax + D + 2 ≤ Jchart) (hζ : IsFastProfile ζ)
    (Cw : ℕ → ℝ) (Cenergy1 Cprep CR Cterminal Crem : ℝ) (Npre Npost Lpre : ℕ)
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) (Jpre : ℕ)
    (θM₁ θS₁ : ℝ) (bM₁ bS₁ : ι → ι → ℝ) : Prop :=
  ∃ (uphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wphys : (∀ i, TorusHk (K i) (h i)) → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (Upre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Bdpre : (∀ i, TorusHk (K i) (h i)) → ℝ≥0∞)
    (hpre : BlockWordConclusion K Jpre H (fun t => twoGpre hp t 0) (twoMpre hp θM₁ bM₁)
      (twoSpre hp θS₁ bS₁) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp)
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) (cellTime q Λ m ν tS)
      (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch)
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) Npost π
      (twoUH hp hΛ hchart uphys) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) Bdpre)
    (Tpre' : (List Bool → ∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (Tpre : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i))),
    TwoBlockOldFacts hp hΛ hchart hζ Cw Cenergy1 Cprep CR Cterminal Crem Npre Npost Lpre Npatch
      hNpatch patch Jpre θM₁ θS₁ bM₁ bS₁ uphys wphys Upre Bdpre hpre Tpre' Tpre

/-- The envelope matrix of the premises is nonnegative with row and column sums at most
`max Cth 0 · Θ`. -/
theorem JointPremisesGen.sums
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) :
    (∀ v u, 0 ≤ Real.sqrt (π u / π v) * A v u) ∧
    (∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ max Cth 0 * Θ) ∧
    (∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ max Cth 0 * Θ) ∧ 0 ≤ max Cth 0 * Θ :=
  ⟨hp.henv.nonneg,
    fun v => (hp.henv.row_sum v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.hΘ₀),
    fun u => (hp.henv.col_sum u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.hΘ₀),
    mul_nonneg (le_max_right _ _) hp.hΘ₀⟩

/-- The scale facts of the premises used by the two-block theorem:`ε_m ≤ ε_{m-1}`, `ε_m⁻¹ ∈ ℕ`, `4 g ≤ 1/8`,
`g₀ ≤ 1/4`, `1 ≤ m`. -/
theorem JointPremisesGen.scales {s : ℝ} (hq : IsAdmissibleQ α s q) (hΛ128 : 128 ≤ Λ)
    (hg₀ : g₀ ≤ 1 / 32)
        (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold) :
    ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) ∧ (∃ N : ℕ, (ocEpsilon q Λ m)⁻¹ = (N : ℝ)) ∧
      4 * g ≤ 1 / 8 ∧ g₀ ≤ 1 / 4 ∧ 1 ≤ m := by
  have hm : 1 ≤ m := le_trans (by norm_num) hp.hm2
  have hsc := Scales.admissible_space_scale_facts hq hΛ128 hm
  have hE : 0 < ocEpsilon q Λ (m - 1) :=
    Construction.Stream.ocEpsilon_pos (le_trans (by norm_num) hΛ128)
  have hg : g ≤ g₀ := hp.cov.g_range.2
  refine ⟨hsc.2.2.1.trans (div_le_self hE.le (by norm_num)), hsc.1.2.2, ?_, ?_, hm⟩ <;> linarith

end Old

/-- **The body of the old block** for the constants of the block word geometry and the first-block constants `Cenergy1`,
`CTa`: for every family with the joint premises, every patch and the weights of the old window, the old
block's output `TwoBlockOldOut` holds. -/
def TwoBlockOldBody (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (Cm Cchart CG : ℕ → ℝ) (Cprep CT CR Cterminal Crem : ℝ) (Cenergy1 CTa : ℝ) : Prop :=
    ∀ {α s q : ℝ} (_hq : IsAdmissibleQ α s q) (Λ : ℕ) (_hΛ128 : 128 ≤ Λ) (hΛ : 1 ≤ Λ)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (g₀ : ℝ) (_hg₀ : g₀ ≤ 1 / 32) (H Ls qJ : ℕ)
    (_hD : 2 ≤ D) (_hKs : Ks + 1 ≤ Jm) (_hqJ : Ks + 1 + Kmax ≤ qJ)
    (Ca Cth Cb COld Crat Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (r ρold : ℝ)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (S : Set ℝ) (_hcoreS : IsCoreOutside α q Λ m F tS (tS + 2 * ocTauPP α q Λ m) S)
    (_hquiet : F.IsFastIndependentOn (S ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
    (Npatch : ℕ) (hNpatch : 0 < Npatch) (patch : Fin 2 → ℤ) (Jpre Npre Npost : ℕ)
    (_hNpre : Npost + (Ks + 1) + (Jpre + H) * (Ks + 1) ≤ Npre) (Cw : ℕ → ℝ)
    (_W : ChartWeights (twoGpre hp) (ocCellDrift α q Λ ζ m ν (twoYc hp)) (cellTime q Λ m ν tS)
      (cellTime q Λ m ν (twoSeam α q Λ m l₀) - cellTime q Λ m ν tS)
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0 Npre Cw)
    (_WM : ChartWeights (fun t _ => twoGpre hp t 0) (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀) - cellTime q Λ m ν tS)
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) 0 Npre Cw)
    (Lpre : ℕ) (_hL : 1 ≤ Lpre)
    (_hreserve : ∀ k ≤ Npre, Real.exp (18 * Cw k) / (Lpre : ℝ) ^ 2 ≤ 1 / 16)
    (_hgain : ENNReal.ofReal (max CTa CT * g *
      (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))) ≤ 1)
    (θM₁ θS₁ : ℝ) (bM₁ bS₁ : ι → ι → ℝ),
    TwoBlockOldOut hp hΛ hchart hζ Cw Cenergy1 Cprep CR Cterminal Crem Npre Npost Lpre Npatch
      hNpatch patch Jpre θM₁ θS₁ bM₁ bS₁

/-- **The two-block theorem on its window, the old block.** For the constants of the block word geometry (`hC`), the first-block
constants `Cenergy1`, `CTa` are chosen with `TwoBlockOldBody`. -/
theorem twoBlockJoint_old (D Ks Kmax Jchart Jm : ℕ) (hchart : Kmax + D + 2 ≤ Jchart)
    (hmol : Kmax + D + 2 ≤ Jm) (Cm Cchart CG : ℕ → ℝ) (Cprep CT CR Cterminal Crem : ℝ)
    (hC : BlockWordBody.{u, v, w, x, max u v} D Ks Kmax Jchart Jm Cm Cchart CG Cprep CT CR
      Cterminal Crem) :
    ∃ Cenergy1 CTa : ℝ, 1 ≤ Cenergy1 ∧ 0 ≤ CTa ∧
      TwoBlockOldBody.{u, v, w, x} D Ks Kmax Jchart Jm hchart Cm Cchart CG Cprep CT CR Cterminal
        Crem Cenergy1 CTa := by
  obtain ⟨Cenergy1, CprepA, CTa, CRA, CterminalA, he1, -, hCTa, -, -, hfirstS⟩ :=
    preparationReferenceCell_retained_endpoint_energy_error_summary.{u, v, w, x}
      D Ks Kmax Jchart Jm hchart hmol Cm Cchart CG
  refine ⟨Cenergy1, CTa, he1, hCTa, ?_⟩
  intro α s q hq Λ hΛ128 hΛ ζ hζ g₀ hg₀ H Ls qJ hD hKs hqJ Ca Cth Cb COld Crat Cpad Cage Npad
    mStar ι _ _ h _ _ _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual A Θ T r
    ρold hp S hcoreS hquiet Npatch hNpatch patch Jpre Npre Npost hNpre Cw W WM Lpre hL hreserve
    hgain θM₁ θS₁ bM₁ bS₁
  obtain ⟨heE, hper, hgsmall, hg0, hm⟩ := hp.scales hq hΛ128 hg₀
  obtain ⟨hBnn, hrow, hcol, hθ⟩ := hp.sums
  have hwin := hp.windows hΛ
  have hE : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have hζc : 0 ≤ Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1) :=
    div_nonneg (Real.sqrt_nonneg _) hE.le
  have hgain2 := gain_of_max hp.cov.g_range.1 hζc hgain
  have hb : cellTime q Λ m ν (twoSeam α q Λ m l₀) ∈
      Set.Icc (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) :=
    ⟨hwin.ab.le, le_rfl⟩
  have hL' : (1 : ℝ) ≤ (Lpre : ℝ) := Nat.one_le_cast.mpr hL
  have hfirst := hfirstS α q Λ m ζ hζ Φ hφ tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad l₀ P ν B
    r g g₀ a B₀ lam Cb qJ y₀ hp.cov hΛ heE (ocA_nonneg_of hΛ (m - 1)) hgsmall hg0 hD F hp.hmeas
    hp.hwmeas π hp.hπ K hp.hK actual (fun v u => Real.sqrt (π u / π v) * A v u) hBnn hp.hprep
    hp.hpointwise hp.hcover (twoWindow_le hΛ tS) hm hp.hΦ hp.htorus (Classical.choose hper)
    (Classical.choose_spec hper) Npatch hNpatch patch (cellTime q Λ m ν (twoSeam α q Λ m l₀))
    hwin.ab hwin.windowPre hwin.blockPre (max Cth 0 * Θ) hrow hcol hp.hdesc hKs hθ hqJ
    hwin.lengthPre Npost H Npre Jpre hp.hdepth Cw W WM (Lpre : ℝ) hL' hreserve hgain2.1 hNpre _ hb
  have hp1 := Classical.choose_spec (Classical.choose_spec hfirst)
  have hp3 := hp1.2.2
  have hp4 := Classical.choose_spec hp3
  have hH := blockCellSolutions_of D K (cellTime q Λ m ν tS)
    (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYc hp)) (twoGpre hp)
    (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K (twoYc hp))
    (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch) (twoUH hp hΛ hchart (Classical.choose hfirst))
    (fun f i => preparationReferenceCellNativeCurve hp.hprep hp.hcover
      (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1)) (K i + 1)
      (slot_succ_le_chart hp.hK hchart i) ν (ocEpsilon q Λ m)
      (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYc hp)
      (Classical.choose (Classical.choose_spec hfirst) f i)) hp1.2.1
  have hpre0 := hC α q Λ m ζ hζ Φ hφ tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad l₀ P ν B r g
    g₀ a B₀ lam Cb qJ y₀ hp.cov hΛ heE (ocA_nonneg_of hΛ (m - 1)) hgsmall hg0 hD F hp.hmeas
    hp.hwmeas π hp.hπ K hp.hK actual (fun v u => Real.sqrt (π u / π v) * A v u) hBnn hp.hprep
    hp.hcover ((l₀ : ℝ) * ocTauPP α q Λ m) hp.hpointwise (windowCoverReferenceChartIndex P)
    (cellTime q Λ m ν tS) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) hwin.ab hwin.windowPre l₀ rfl
    (Or.inl ⟨rfl, rfl⟩) hwin.blockPre S hcoreS hquiet (max Cth 0 * Θ) hrow hcol hp.hdesc hKs hθ
    hqJ hwin.lengthPre (X := ∀ i, TorusHk (K i) (h i)) Npost H Npre Jpre hp.hdepth Cw W WM
    (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch)
    (fun ξ k i => preparationReferenceCellLocalizedInitialFamilyLinearMap_all_moments hp.hprep
      hp.hcover (Construction.Stream.ocTauPP_pos hΛ).le (ocA_nonneg_of hΛ (m - 1)) K
      (slot_le_chart hp.hK hchart) (twoWindow_le hΛ tS) hζ Npatch hNpatch patch
      (ocEpsilon q Λ m) (Construction.Stream.ocEpsilon_pos hΛ).ne' (twoYc hp) ξ k
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) r i)
    (twoUH hp hΛ hchart (Classical.choose hfirst)) _ hH (Lpre : ℝ) hL' hreserve hgain2.2 hNpre _ hb
    θM₁ θS₁ bM₁ bS₁
  have hpre : BlockWordConclusion K Jpre H (fun t => twoGpre hp t 0) (twoMpre hp θM₁ bM₁)
      (twoSpre hp θS₁ bS₁) ((ocEpsilon q Λ (m - 1))⁻¹ • twoYc hp)
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) (cellTime q Λ m ν tS)
      (cellTime q Λ m ν (twoSeam α q Λ m l₀)) (ocCellDrift α q Λ ζ m ν (twoYc hp))
      (twoV₀ hp hΛ hchart hζ Npatch hNpatch patch)
      (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (r / ocEpsilon q Λ m) Npost π
      (twoUH hp hΛ hchart (Classical.choose hfirst)) (cellTime q Λ m ν (twoSeam α q Λ m l₀)) _ :=
    hpre0
  have hmO := pre_word_maps K Jpre H _ _ _ _ _ _ _ hwin.ab.le _ _ _ _ Npost π _ _ hpre
  have hmO' := Classical.choose_spec (Classical.choose_spec hmO)
  refine ⟨Classical.choose hfirst, Classical.choose (Classical.choose_spec hfirst),
    Classical.choose hp3, _, hpre, Classical.choose hmO,
    Classical.choose (Classical.choose_spec hmO),
    twoPhysical_of hp hζ Npatch hNpatch patch _ _ hp1.1, hp4.1, hp4.2.1, hp4.2.2.1, hmO'.1,
    hmO'.2.1, hmO'.2.2.1, hmO'.2.2.2.1, fun ξ => ?_⟩
  exact (le_of_eq (energySub_congr π Npost (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m))
    (r / ocEpsilon q Λ m) (⇑(Classical.choose hp3))
    (fun ξ i => twoUH hp hΛ hchart (Classical.choose hfirst) ξ i
      (cellTime q Λ m ν (twoSeam α q Λ m l₀)))
    (⇑(Classical.choose (Classical.choose_spec hmO))) hp4.1 ξ)).trans
    ((hmO'.2.2.2.2 ξ).trans (le_of_eq (pricePre_reassoc _ _ _ _ _ _)))

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The plane solutions of the one-patch statement are the physical solutions of the two-block theorem at `t_p`**.

The error clause of the one-patch statement quantifies over the plane solutions `U` on `[tS, t_p]` from the localized datum,
while the physical solution `u` of the two-block theorem lives on the longer window `[tS, tS + 2 τ'']`. Restricted to
`[tS, t_p]`, `u` solves the same problem, and the uniqueness of the actual preparation problem on
a subwindow of the certificate's window (`actualPreparation_planeWeakSolution_arbitrary_subwindow_unique`)
identifies the two at `t_p`.

For an empty index type both sides are functions on the empty type. The case `t_p = tS` cannot
occur (`t_p - tS ≥ τ''`), and the restriction lemma allows any `c ≤ b`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
  AVRegularity.CycleWords AVRegularity.ChartTransport AVRegularity.CycleJointProofs
open AVRegularity.CoupledEnergy.Variational
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

section Restrict

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- A plane solution on `[a, b]` solves the same problem on `[a, c]`, `c ≤ b`. -/
theorem isCoupledWeakSolutionPlane_restrict_right {K : ι → ℕ} {D : ℕ} {ν a b c : ℝ}
    (hcb : c ≤ b) {v : ℝ → Vec 2 → Vec 2}
    {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν a c v D K A f F g u w := by
  have hsub : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hcb
  exact ⟨fun i => (hs.1 i).mono hsub,
    fun i => (hs.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl),
    fun i => ae_restrict_of_ae_restrict_of_subset hsub (hs.2.2.1 i), hs.2.2.2.1,
    fun i t ht φ => hs.2.2.2.2 i t (hsub ht) φ⟩

end Restrict

section Unique

variable {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {g₀ : ℝ} {H D Kmax Ks Ls Jm qJ Jchart : ℕ}
  {Ca Cth Cb COld Crat : ℝ} {Cm CG Cchart : ℕ → ℝ} {Cpad Cage : ℝ} {Npad mStar : ℕ}
  {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {K : ι → ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {M' : ℕ} {κ : ℕ → ℝ} {m : ℕ} {ν B : ℝ}
  {hφ : IsAdmissibleStream (Φ (m - 1))} {tS g a B₀ lam : ℝ} {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
  {P' : Type w} {Ctx : P' → Type x} {F : ChartedFamily ι h D P' Ctx} {actual : ∀ p, Ctx p}
  {A : Matrix ι ι ℝ} {Θ : ℝ} {T : F.Atlas} {r ρold : ℝ}

/-- **Uniqueness of the plane solution.** A plane solution on `[tS, t_p]` from the datum `f` agrees at `t_p` with every plane
solution on `[tS, tS + 2 τ'']` from the same datum. -/
theorem JointPremisesGen.plane_eq_at_tp {s : ℝ} (hq : IsAdmissibleQ α s q)
    (hΛ128 : 128 ≤ Λ) (hg₀ : g₀ ≤ 1 / 32)
    (hp : JointPremisesGen α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb COld Crat
      Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual
      A Θ T r ρold)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hu : IsCoupledWeakSolutionPlane ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) u w)
    (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (W : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hU : IsCoupledWeakSolutionPlane ν tS (twoTp α q Λ m l₀) (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) U W) :
    ∀ i, U i (twoTp α q Λ m l₀) = u i (twoTp α q Λ m l₀) := by
  have hΛ : 1 ≤ Λ := le_trans (by norm_num) hΛ128
  have htp := (hp.windows hΛ).tpMem
  obtain ⟨heE, -⟩ := hp.scales hq hΛ128 hg₀
  obtain ⟨hBnn, -⟩ := hp.sums
  intro i
  exact actualPreparation_planeWeakSolution_arbitrary_subwindow_unique K Kmax hp.hK r ν
    hp.cov.pos.2.2 hp.cov.pos.1 tS (tS + 2 * ocTauPP α q Λ m) D F H hp.hdepth α q Λ m Φ ζ hp.hΦ
    (Φ (m - 1)) hφ Cpad Cage Npad Jchart Cchart l₀ P hp.hprep (ocEpsilon q Λ m)
    (ocEpsilon q Λ (m - 1)) actual hp.hmeas hp.hwmeas rfl hp.cov.rho_e heE Jm hchart hmol Cm π
    hp.hπ (fun v u => Real.sqrt (π u / π v) * A v u) hBnn hp.hpointwise tS
    (twoTp α q Λ m l₀) le_rfl htp.1 htp.2 (fun _ _ => 0) (fun _ _ => 0)
    (fun _ => timeMemLp_zero _ _) (fun _ => timeIntegrable_zero _) f U u W w hU
    (isCoupledWeakSolutionPlane_restrict_right htp.2 hu) i (twoTp α q Λ m l₀)
    ⟨htp.1, le_rfl⟩

end Unique

end AVRegularity.CycleJointProofs.Assembly
end
end
