-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.EntryTerminal.Ingredients.Recon.Times.Times
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleReference.TorusStreamFluxEquation
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.CycleComparison.Assembly.OfPhysicalLift
import AVRegularity.EntryTerminal.Ingredients.Recon.Family.Main
import AVRegularity.CycleComparison.Assembly.OcDiagonal
import AVRegularity.CycleComparison.Diagonal.Main
import AVRegularity.EntryTerminal.Ingredients.Recon.Setting.Main
import AVRegularity.EntryTerminal.Ingredients.Recon.Seq.Main
public import AVRegularity.CycleComparison.Assembly.CoarseLetters
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.TerminalLift.Assembly
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.EntryTerminal.Ingredients.QuietEntrance.ZeroAssembly

section
section
/-! Assembly ingredients for the letters: window geometry, and the actual Eulerian mean letters
with their coefficient bounds and masked graph. All constants have the scope of ReconPrefix;
these are conditional helper propositions. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Letters

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The geometry and reference flux of the coarse window, independent of its mean letters. -/
structure ReconWindowGeometry
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) where
  a : ℝ
  B₀ : ℝ
  lam : ℝ
  window : c.tp ≤ c.tp + rTobs c
  rho_pos : 0 < rRho c
  B_pos : 0 < c.D.κ (M - 1)
  D_ge : 2 ≤ A.NT + A.Dt
  mass_pos : ∀ v, 0 < c.Gw.mass c.lawW v
  drift_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ x,
    ‖streamVel (c.D.Φ (M - 1)) t x‖ ≤ C
  drift_meas : Measurable fun q : Set.Icc c.tp (c.tp + rTobs c) × Vec 2 =>
    streamVel (c.D.Φ (M - 1)) q.1 q.2
  drift_smooth : ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c),
    ContDiff ℝ (⊤ : ℕ∞) (streamVel (c.D.Φ (M - 1)) t)
  drift_div : ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ x,
    ∑ k : Fin 2, fderiv ℝ (streamVel (c.D.Φ (M - 1)) t) x (basisVec k) k = 0
  drift_per : ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), IsZ2Periodic (streamVel (c.D.Φ (M - 1)) t)
  a_nonneg : 0 ≤ a
  B₀_ge : 1 ≤ B₀
  lam_pos : 0 < lam
  drift_jets : ∀ l : ℕ, 1 ≤ l → l ≤ rNc A kc → ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (streamVel (c.D.Φ (M - 1)) t)) l x‖ ≤
      a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)
  drift_scale : B₀ * rRho c / lam ≤ 1 / 2
  drift_small : a * B₀ * rRho c ^ 2 ≤ c.D.κ (M - 1) / 8
  J_symm : ∀ t i j,
    ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) t i j =
      ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) t j i
  J_meas : ∀ i j, Measurable fun t => ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) t i j
  J_bdd : matrixSupNorm (fun t =>
    ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) t -
      c.D.κ (M - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) c.tp (c.tp + rTobs c) ≠ ⊤
  cov_small : matrixSupNorm
    (covarianceMatrix (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) (c.D.κ (M - 1)) c.tp)
      c.tp (c.tp + rTobs c) ≤ ENNReal.ofReal (rRho c ^ 2)

/-- Eulerian letters presenting the actual glued means, including all coefficient and graph
clauses of `IsCoarseSetting`; produced from the entrywise and actual-mean budgets
(`ReconMeanBudget`). -/
structure ReconMeanLetters
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) where
  AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)
  CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
  Aedge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ
  Cstar : ℝ
  Θ : ℝ
  AD_meas : ∀ d, Measurable fun q : Set.Icc c.tp (c.tp + rTobs c) × Vec 2 => AD d q.1 q.2
  AD_smooth : ∀ d, ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ContDiff ℝ ((rNc A kc) : ℕ) (AD d t)
  AD_per : ∀ d, ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), AVenhance.IsZ2Periodic (AD d t)
  AD_fin : ∀ d, coefficientSeminorm (rRho c) (rNc A kc) c.tp (c.tp + rTobs c) (AD d) ≠ ⊤
  CE_meas : ∀ r ∈ Finset.Icc 1 A.dW, ∀ v u d, Measurable fun q : Set.Icc c.tp (c.tp + rTobs c) × Vec 2 => CE r v u d q.1 q.2
  CE_smooth : ∀ r ∈ Finset.Icc 1 A.dW, ∀ v u d, ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), ContDiff ℝ ((rNc A kc) : ℕ) (CE r v u d t)
  CE_per : ∀ r ∈ Finset.Icc 1 A.dW, ∀ v u d, ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c), AVenhance.IsZ2Periodic (CE r v u d t)
  CE_fin : ∀ r ∈ Finset.Icc 1 A.dW, ∀ v u d, coefficientSeminorm (rRho c) (rNc A kc) c.tp (c.tp + rTobs c) (CE r v u d) ≠ ⊤
  edge_nonneg : ∀ v u, 0 ≤ Aedge v u
  edge_row : ∀ v, ∑ u, Aedge v u ≤ Θ
  edge_col : ∀ u, ∑ v, Aedge v u ≤ Θ
  edge_acyclic : Aedge ^ (A.dW + 1) = 0
  edge_mean : ∀ r ∈ Finset.Icc 1 A.dW, ∀ v u,
    ENNReal.ofReal (Real.sqrt ((c.Gw.mass c.lawW) u / (c.Gw.mass c.lawW) v)) *
      ∑ d : Finset.Icc 2 (A.NT + A.Dt), coefficientSeminorm (rRho c) (rNc A kc) c.tp (c.tp + rTobs c) (CE r v u d) *
        (ENNReal.ofReal ((c.D.κ (M - 1)) * (rRho c) ^ (d.1 - 2)))⁻¹
      ≤ ENNReal.ofReal (Cstar ^ r * (Aedge ^ r) v u)

  presentation :
  ∀ r ∈ Finset.range (A.dW + 1),
    IsMeanPresentation (Set.Icc c.tp (c.tp + rTobs c)) (A.NT + A.Dt) r AD CE
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M))
      (gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
        (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
        (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) A.NT r
        (fun k => rLiftData c k) c.CcT
        (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
        (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k)))

/-- Geometry input with the exact reconstruction prefix. -/
def ReconWindowGeometryStatement : Prop :=
  ReconPrefix (κ := Unit) fun c _ kc _ _ => Nonempty (ReconWindowGeometry c kc)

/-- Actual-mean letter input with the exact reconstruction prefix. -/
def ReconMeanLettersStatement : Prop :=
  ReconPrefix (κ := Unit) fun c _ kc _ _ => Nonempty (ReconMeanLetters c kc)

end AVRegularity.EntryTerminal.Ingredients.Recon.Letters
end
end

section
/-! Geometry for the letters: the existing coarse-drift lemma supplies all drift orders at the renewal
radius. The all-anchor band covariance estimate becomes at most rho squared past a level floor.
The existing reconstruction deadline supplies the nonempty window. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Letters

private theorem reference_bounds (D : OCData) (M : ℕ) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hν : 0 < D.κ M) (B tp tf : ℝ) (hB : 0 ≤ B) :
    (∀ t i j, ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t i j =
      ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t j i) ∧
    (∀ i j, Measurable fun t => ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t i j) ∧
    matrixSupNorm (fun t => ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t -
      B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) tp tf ≠ ⊤ := by
  refine ⟨fun t i j => Construction.Preservation.FullLift.refFlux_entry_symm hΛ hζ (D.κ M) t i j,
    fun i j => CycleReference.refFlux_entry_measurable hΛ hζ hν i j, ?_⟩
  have hId : ∀ i j : Fin 2, |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ B := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [abs_of_nonneg hB, hB]
  have hb : matrixSupNorm (fun t => ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t -
      B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) tp tf ≤
      ENNReal.ofReal (D.κ M + ocHStar D.α D.q D.Λ M (D.κ M) + B) := by
    refine iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j => ?_
    apply ENNReal.ofReal_le_ofReal
    change |ocRefFlux D.α D.q D.Λ D.ζ M (D.κ M) t i j -
      B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ _
    exact (abs_sub _ _).trans (add_le_add
      (by simpa only [Real.norm_eq_abs] using CycleReference.refFlux_entry_norm_le hΛ hζ hν i j)
      (hId i j))
  exact ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top)

private theorem geometry_before_deadline :
    ReconPrefix (κ := Unit) fun c _ kc _ _ =>
      c.tp < c.tp + rTobs c → Nonempty (ReconWindowGeometry c kc) := by
  intro ℓ X
  obtain ⟨ΛD, B₀, C₁, hΛD, hB₀, _, hdr⟩ := CycleComparison.Assembly.coarse_drift_small
    X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  obtain ⟨C, hC, ΛH, hΛH, hcov⟩ := CycleReference.bandChain_covariance_estimates
    X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  have hδ : 0 < ocDelta X.α X.q :=
    (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  obtain ⟨η, hη, hsmall⟩ := Applications.exists_small_pow (K := C) (zero_le_one.trans hC)
    hδ (zero_lt_one : (0 : ℝ) < 1)
  refine ⟨max ΛD ΛH, hΛD.trans (le_max_left _ _), fun A hΛ _ => ?_⟩
  have h128 : 128 ≤ A.Λ := hΛD.trans ((le_max_left _ _).trans hΛ)
  obtain ⟨N, hN⟩ := Applications.eps_eventually_le X.hq.1 h128 hη
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _
  refine ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨N + 3, fun M hM c _ hdl => ?_⟩⟩
  obtain ⟨hα, hq, hΛD', hζ, hseq, hband, -⟩ := c.data
  have hM2 : 2 ≤ M := by omega
  have hΛ1 : 1 ≤ A.Λ := by omega
  have hΛc : 1 ≤ c.D.Λ := hΛD' ▸ hΛ1
  have hζc : IsFastProfile c.D.ζ := hζ ▸ X.hζ
  have hν : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 X.hζ hband le_rfl
  have hB : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (by omega)
  have hr : rRho c = Real.sqrt (c.D.κ (M - 1) * ocTauPP X.α X.q A.Λ M) := by
    simp only [rRho, hα, hq, hΛD']
  have hrpos : 0 < rRho c := by
    rw [hr]
    exact Real.sqrt_pos.mpr (mul_pos hB (Construction.Stream.ocTauPP_pos hΛ1))
  obtain ⟨a, lam, ha, hlam, hscale, hstrain, _, hjets, hsmooth, hdiv, hper, hbdd, hmeas⟩ :=
    hdr A.Λ ((le_max_left _ _).trans hΛ) c.D.Φ hseq M c.D.κ hband M hM2 le_rfl
      (c.D.κ M) (c.D.κ (M - 1)) rfl rfl
  obtain ⟨hJs, hJm, hJb⟩ := reference_bounds c.D M hΛc hζc hν (c.D.κ (M - 1))
    c.tp (c.tp + rTobs c) hB.le
  have hCsmall : C * ocEpsilon X.q A.Λ (M - 1) ^ ocDelta X.α X.q ≤ 1 :=
    hsmall _ (Applications.eps_pos X.hq.1 h128).le (hN (M - 1) (by omega))
  have hCov : matrixSupNorm
      (covarianceMatrix (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) (c.D.κ (M - 1)) c.tp)
        c.tp (c.tp + rTobs c) ≤ ENNReal.ofReal (rRho c ^ 2) := by
    refine iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j => ?_
    apply ENNReal.ofReal_le_ofReal
    change |ocCovariance c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) (c.D.κ (M - 1)) c.tp t i j| ≤ _
    have hh := (hcov A.Λ ((le_max_right _ _).trans hΛ) M (by omega) c.D.κ hband M hM2 le_rfl
      c.tp t i j).2.2.2
    have hR : ocRh X.α X.q A.Λ M (c.D.κ (M - 1)) = rRho c := hr.symm
    rw [hR] at hh
    rw [hα, hq, hΛD', hζ]
    exact (div_le_one (sq_pos_of_pos hrpos)).mp (hh.trans hCsmall)
  have hDm : 2 ≤ A.NT + A.Dt := by
    have := le_max_left 2 (max A.DW ((termAlphabet A.NT A.pT A.DW A.dW).sup (letterOrder A.NT A.pT)))
    change 2 ≤ A.Dt at this
    omega
  exact ⟨{
    a := a, B₀ := B₀, lam := lam
    window := hdl.le, rho_pos := hrpos, B_pos := hB, D_ge := hDm
    mass_pos := fun v => Construction.Preservation.Buffer.birth_compMass_pos
      (hq ▸ X.hq.1) (hΛD' ▸ h128) c.lawW v.1
    drift_bdd := hbdd c.tp (c.tp + rTobs c)
    drift_meas := hmeas c.tp (c.tp + rTobs c)
    drift_smooth := fun t _ => hsmooth t
    drift_div := fun t _ x => hdiv t x
    drift_per := fun t _ => hper t
    a_nonneg := ha, B₀_ge := hB₀, lam_pos := hlam
    drift_jets := fun l hl _ t _ x => hjets l hl t x
    drift_scale := by rw [hr]; exact hscale
    drift_small := by rw [hr]; exact hstrain
    J_symm := hJs, J_meas := hJm, J_bdd := hJb, cov_small := hCov }⟩

/-- Window geometry for the letters with the exact prefix, using the already proved reconstruction deadline. -/
theorem termReconWindowGeometry : ReconWindowGeometryStatement := by
  apply (geometry_before_deadline.and termReconTimes.toReconPrefix).mono (fun _ => ())
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker
    j₀ M c x kc ℓ k h
  apply h.1
  have hend : c.tp + rTobs c = c.a + A.T₀ := by unfold rTobs; ring
  rw [hend]
  exact h.2.2

end AVRegularity.EntryTerminal.Ingredients.Recon.Letters
end
end

section
/-! Mean-budget assembly for the letters. The actual-mean budget `ReconMeanBudget` supplies
presentation and regularity.
Its normalized diagonal and positive-grade budgets imply finite seminorms; conjugating the
masked physical majorant gives the coarse edge matrix, nilpotent by the weak family's depth.
The statement asks only for existence of the row/column price, so the finite total matrix mass
is a valid price, without a further smallness assumption. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly
open AVRegularity.CycleComparison.ActualMeans
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Letters

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Actual Eulerian mean letters and their normalized budgets. The edge budget is expressed
in the physical masked majorant, as in the existing cycle-comparison means stage. -/
structure ReconMeanBudget
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) where
  AD : ∀ d : Finset.Icc 2 (A.NT + A.Dt), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)
  CE : ℕ → ∀ (v u : CompIn c.Gw.comps) (d : Finset.Icc 2 (A.NT + A.Dt)), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
  Lb : ℤ → ℕ → ℕ → MeanCoeff (CompIn c.Gw.comps) (fun v => ScalarH v.1.root)
  transferCost : ℝ
  physicalEdge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ
  physical_nonneg : ∀ v u, 0 ≤ physicalEdge v u
  diagonalCost : ℝ
  edgeCost : ℝ
  actual : IsActualMeans A.NT A.Dt A.dW (rNc A kc) transferCost
    (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (fun k => c.Gw.actualFamily.weight (oddSlotOf k)) c.tp (c.tp + rTobs c)
    (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
    (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) (ocEpsilon c.D.q c.D.Λ (M - 1))
    (rLiftData c) c.CcT
    (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (rSeqStart c) (rSeqEnd c) Lb
    (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) AD CE
  diagonal_bound :
    ∑ d : Finset.Icc 2 (A.NT + A.Dt),
      coefficientSeminorm (rRho c) (rNc A kc) c.tp (c.tp + rTobs c) (AD d) *
        (ENNReal.ofReal (c.D.κ (M - 1) * rRho c ^ (d.1 - 2)))⁻¹ ≤
      ENNReal.ofReal diagonalCost
  edge_bound : ∀ r ∈ Finset.Icc 1 A.dW, ∀ v u,
    ENNReal.ofReal (Real.sqrt ((c.Gw.mass c.lawW) u / (c.Gw.mass c.lawW) v)) *
      ((∑ d : Finset.Icc 2 (A.NT + A.Dt),
        coefficientSeminorm (ocEpsilon c.D.q c.D.Λ (M - 1)) (rNc A kc)
          c.tp (c.tp + rTobs c) (CE r v u d) *
          (ENNReal.ofReal (c.D.κ (M - 1) * ocEpsilon c.D.q c.D.Λ (M - 1) ^ (d.1 - 2)))⁻¹) +
      ∑ d : Finset.Icc 2 (A.NT + A.Dt),
        coefficientSeminorm (rRho c) (rNc A kc) c.tp (c.tp + rTobs c) (CE r v u d) *
          (ENNReal.ofReal (c.D.κ (M - 1) * rRho c ^ (d.1 - 2)))⁻¹) ≤
      ENNReal.ofReal (edgeCost *
        (Real.sqrt ((c.Gw.mass c.lawW) u / (c.Gw.mass c.lawW) v) *
          (CycleComparison.Coarse.maskedEdgeMatrix (familyAdj c.Gw.actualFamily) physicalEdge ^ r) v u))

/-- Budget input with the literal reconstruction prefix. -/
def ReconMeanBudgetStatement : Prop :=
  ReconPrefix (κ := Unit) fun c _ kc _ _ => Nonempty (ReconMeanBudget c kc)

/-- The budgets and regularity of `ReconMeanBudget` give all the coarse letter fields. -/
theorem reconMeanLetters_of_budget
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) (hπ : ∀ v, 0 < c.Gw.mass c.lawW v) (b : ReconMeanBudget c kc) :
    Nonempty (ReconMeanLetters c kc) := by
  classical
  let π := c.Gw.mass c.lawW
  let Ae : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ :=
    Matrix.of (familyMask c.Gw.actualFamily (fun v u => Real.sqrt (π u / π v) * b.physicalEdge v u))
  have hAe : ∀ v u, 0 ≤ Ae v u :=
    familyMask_nonneg _ (fun v u => mul_nonneg (Real.sqrt_nonneg _) (b.physical_nonneg v u))
  have hrow : ∀ v, ∑ u, Ae v u ≤ ∑ v, ∑ u, Ae v u := fun v =>
    Finset.single_le_sum (fun w _ => Finset.sum_nonneg fun u _ => hAe w u) (Finset.mem_univ v)
  have hcol : ∀ u, ∑ v, Ae v u ≤ ∑ v, ∑ u, Ae v u := by
    intro u
    exact Finset.sum_le_sum fun v _ =>
      Finset.single_le_sum (fun w _ => hAe v w) (Finset.mem_univ u)
  have hconj : (Matrix.of fun v u => Real.sqrt (π u / π v) *
      CycleComparison.Coarse.maskedEdgeMatrix (familyAdj c.Gw.actualFamily) b.physicalEdge v u) = Ae := by
    ext v u
    exact (familyMask_eq_conj c.Gw.actualFamily π b.physicalEdge v u).symm
  refine ⟨{
    AD := b.AD, CE := b.CE, Aedge := Ae, Cstar := max 1 b.edgeCost, Θ := ∑ v, ∑ u, Ae v u
    AD_meas := b.actual.2.2.2.1
    AD_smooth := b.actual.2.2.1
    AD_per := b.actual.2.2.2.2.1
    AD_fin := fun d => ne_top_of_sum_inv_le _ _ b.diagonal_bound d
    CE_meas := b.actual.2.2.2.2.2.2.1
    CE_smooth := b.actual.2.2.2.2.2.1
    CE_per := b.actual.2.2.2.2.2.2.2.1
    CE_fin := ?_
    edge_nonneg := hAe, edge_row := hrow, edge_col := hcol
    edge_acyclic := familyMask_pow_eq_zero _ (c.Gw.hasDepthAtMost_actualFamily c.weak.2.2.2.1) _
    edge_mean := ?_
    presentation := fun r hr => b.actual.1 r (by have := Finset.mem_range.mp hr; omega) }⟩
  · intro r hr v u d
    have h := b.edge_bound r hr v u
    exact ne_top_of_sum_inv_ne_top _ _ (ne_top_of_mul_add_le
      (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v)))).ne' h) d
  · intro r hr v u
    have h := edge_mean_of_bound hπ
      (CycleComparison.Coarse.maskedEdgeMatrix_nonneg _ _ b.physical_nonneg)
      (le_rfl : max 1 b.edgeCost ≤ max 1 b.edgeCost) (Finset.mem_Icc.mp hr).1
      (b.edge_bound r hr v u)
    rw [hconj] at h
    exact h

/-- The budget producer gives the remaining mean ingredient of the letters; masses come from the geometry. -/
theorem termReconMeanLetters_of_budget (hbudget : ReconMeanBudgetStatement) : ReconMeanLettersStatement := by
  apply (hbudget.and termReconWindowGeometry).mono (fun _ => ())
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker
    j₀ M c x kc ℓ k h
  obtain ⟨b⟩ := h.1
  obtain ⟨g⟩ := h.2
  exact reconMeanLetters_of_budget c kc g.mass_pos b

end AVRegularity.EntryTerminal.Ingredients.Recon.Letters
end
end
end

section
section
/-! Pulse model for the letters: the letter construction is applied to the supplied sequence c.CcT, and the mean transport transports its
letters through the actual observation charts. No newly chosen lift sequence is substituted. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly
open AVRegularity.CycleComparison.ActualMeans
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Letters

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M ℓfamily : ℕ}

/-- The high-order pulse setting and the GIVEN lifted sequence on the clipped window.
The analytic constants and orders may depend on kc; they precede the level in the prefix producer. -/
structure ReconPulseInput
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) where
  K : ℕ
  L : ℕ
  order : rNc A kc ≤ K + 1
  CG : ℕ → ℝ
  Cw : ℕ → ℝ
  Cj : ℕ → ℕ → ℝ
  qs : ℕ
  qf : ℕ
  par : ℤ → Fin 2
  V : ℤ → ℝ → ℝ → ℝ
  price : ℝ
  settings : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
    IsLiftSetting (rLiftData c k) (c.Gw.mass c.lawW) (rSeqStart c k) (rSeqEnd c k)
      (ocEpsilon c.D.q c.D.Λ M) (c.D.κ M) (c.D.κ (M - 1)) (rRho c)
      (ocEpsilon c.D.q c.D.Λ (M - 1)) (ocEll c.D.q c.D.Λ M (c.D.κ M))
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)))
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
      (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) (par k) (V k) A.dW A.NT K L L
      qs qf CG Cw Cj (recordMajorant (c.Gw.mass c.lawW) c.Gw.fam) price
  sequences : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
    IsLiftSequence (rLiftData c k) (K + A.Dt + 2) (max (L + 1) (L + 2))
      (rSeqStart c k) (rSeqEnd c k) A.NT A.dW (c.CcT k)

section Model

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
  cker j₀ M)

/-- Renewal chart and inverse of an observed pulse. -/
abbrev reconChart (k : ℤ) :=
  ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
    (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k)

abbrev reconLabel (k : ℤ) :=
  ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
    (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k)

/-- The explicit diagonal letter of the reconstruction window. -/
abbrev reconAD (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ) :=
  adLetter (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
    (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) (A.NT + A.Dt)
    (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (rSeqStart c) (rSeqEnd c) Lsc (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M))

/-- The explicit positive-grade letter of the reconstruction window. -/
abbrev reconCE (Lb : ℤ → ℕ → ℕ → MeanCoeff (CompIn c.Gw.comps) (fun v => ScalarH v.1.root)) :=
  ceLetter (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
    (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) (A.NT + A.Dt)
    (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (rSeqStart c) (rSeqEnd c) Lb

/-- Letters, their scalar reading, and the actual means, at the requested coarse order. -/
structure ReconPulseModel (kc : ℕ) (p : ReconPulseInput c kc) where
  C₂ : ℝ
  C₂_nonneg : 0 ≤ C₂
  C₁ : ℝ
  Lb : ℤ → ℕ → ℕ → MeanCoeff (CompIn c.Gw.comps) (fun v => ScalarH v.1.root)
  Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ
  pulse : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
    IsPulseLetters (rLiftData c k) (c.CcT k) (c.Gw.mass c.lawW)
      (recordMajorant (c.Gw.mass c.lawW) c.Gw.fam) (rSeqStart c k) (rSeqEnd c k)
      (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) C₂ A.NT A.dW p.K (Lb k)
  scalar_smooth : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
    ∀ n, 2 ≤ n → n ≤ A.NT + A.Dt → ∀ d, 2 ≤ d → d ≤ n →
    ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (rSeqStart c k) (rSeqEnd c k),
      ContDiff ℝ ((rNc A kc) : ℕ∞) (Lsc k n d α l s)
  reading : IsScalarReading (fun k n => Lb k 0 n) Lsc
    (refFallback (c.D.κ (M - 1)) (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)))
  actual : IsActualMeans A.NT A.Dt A.dW (rNc A kc) C₁
    (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (fun k => c.Gw.actualFamily.weight (oddSlotOf k)) c.tp (c.tp + rTobs c)
    (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
    (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) (ocEpsilon c.D.q c.D.Λ (M - 1))
    (rLiftData c) c.CcT
    (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (rSeqStart c) (rSeqEnd c) Lb
    (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) (reconAD c Lsc) (reconCE c Lb)

end Model

/-- The exact remaining pulse-setting input, within the reconstruction prefix. -/
def ReconPulseInputStatement : Prop :=
  ReconPrefix (κ := Unit) fun c _ kc _ _ => Nonempty (ReconPulseInput c kc)

/-- The remaining letter budgets from high-order pulse data, with the exact prefix. -/
def ReconPulseBudgetStatement : Prop :=
  ReconPrefix (κ := Unit) fun c _ kc _ _ =>
    ∀ _p : ReconPulseInput c kc, Nonempty (ReconMeanBudget c kc)

/-- The letter construction at the supplied sequence, followed by the mean transport at the actual charts and partition. -/
theorem reconPulseModel_of_input
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) (p : ReconPulseInput c kc) (g : ReconWindowGeometry c kc)
    (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M) (hfamily : ReconFamilyAt c ℓfamily) :
    Nonempty (ReconPulseModel c kc p) := by
  classical
  obtain ⟨hα, hq, hΛD, hζ, hseq, hband, -⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ (by omega : 1 ≤ A.Λ)
  have hν : 0 < c.D.κ M := CycleReference.bandChain_pos (by omega) X.hζ hband le_rfl
  have hℓ : 0 < ocEll c.D.q c.D.Λ M (c.D.κ M) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  have hE : 0 < ocEpsilon c.D.q c.D.Λ (M - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hd : 0 ≤ ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) := by
    unfold ocDStar
    exact mul_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le (Real.sqrt_nonneg _)
  have hDt : 2 ≤ A.Dt := le_max_left _ _
  have hnc : 1 ≤ rNc A kc := by
    have hp : 0 < (0 + A.dW + 3) * ((A.NT + A.Dt) + 8 * 1 + 4) :=
      Nat.mul_pos (by omega) (by omega)
    simp only [rNc]
    omega
  obtain ⟨C₂, hC₂, hletters⟩ := exists_pulseLetters A.NT p.K p.L p.L A.Dt A.dW p.CG p.Cw p.Cj
  choose! Lb hLb using fun k (hk : k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c)) =>
    hletters (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root)
      (rLiftData c k) (c.Gw.mass c.lawW) (rSeqStart c k) (rSeqEnd c k)
      (ocEpsilon c.D.q c.D.Λ M) (c.D.κ M) (c.D.κ (M - 1)) (rRho c)
      (ocEpsilon c.D.q c.D.Λ (M - 1)) (ocEll c.D.q c.D.Λ M (c.D.κ M))
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)))
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
      (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) (p.par k) (p.V k) p.qs p.qf
      (recordMajorant (c.Gw.mass c.lawW) c.Gw.fam) p.price (p.settings k hk)
      (c.CcT k) (p.sequences k hk)
  choose! Ls hLs using fun k (hk : k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (n : ℕ) (hn : 2 ≤ n) (hnN : n ≤ A.NT + A.Dt) => (hLb k hk).diag n hn hnN
  obtain ⟨T, hf⟩ := hfamily
  have htorus := hf.2.1
  have hpart := hf.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hwmeas, -, hsupp⟩ := partition_stage_facts hpart
  obtain ⟨C₁, -, hmeans⟩ := actual_means_explicit A.NT A.Dt A.dW (rNc A kc) hDt
    (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)))
  have hreg : (((rNc A kc : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((p.K + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast p.order
  obtain ⟨Lsc, -, hscC, hread, hAM⟩ := hmeans (ι := CompIn c.Gw.comps)
    (h := fun v => ScalarH v.1.root)
    (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (fun k => c.Gw.actualFamily.weight (oddSlotOf k)) c.tp (c.tp + rTobs c)
    (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c)
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
    (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) (ocEpsilon c.D.q c.D.Λ (M - 1))
    (rLiftData c) c.CcT
    (fun k => ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (fun k => ocChartInv c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k))
    (rSeqStart c) (rSeqEnd c) Lb Ls
    (refFallback (c.D.κ (M - 1)) (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)
      (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)))
    (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) hnc (pow_pos hℓ 2) g.rho_pos
    (div_nonneg hd g.rho_pos.le) hE rfl g.J_meas hwmeas
    (fun k hk t ht hn => cellTime_mem_liftWindow (pow_pos hℓ 2) (hsupp k hk t hn) ht)
    (fun k _ t y => CycleComparison.Charts.ocChartInv_ocChart _ _ _ _ _ _ _ t y)
    (fun k _ t y => CycleComparison.Charts.ocChart_ocChartInv _ _ _ _ _ _ _ t y)
    (fun k _ t z y => CycleComparison.Charts.ocChart_latticeShift _ _ _ _ _ _ t z y)
    (fun k _ t y => CycleComparison.Charts.ocChart_det _ _ _ _ _ _ t y)
    (fun k _ => CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _)
    (fun k _ => CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _)
    (fun k _ t _ hwin j hj _ y => by
      have ha := abs_sub_anchor_le c.D.α c.D.q hΛ1 M hℓ c.tp (c.tp + rTobs c) k hwin
      rw [hα, hq, hΛD]
      exact CycleComparison.Charts.ocChart_window_jets X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq
        X.ζ X.hζ A.Λ hΛ c.D.Φ hseq M hM (c.D.hΦ (M - 1)) _ t
        (by simpa only [hα, hq, hΛD] using ha) j hj y)
    (fun k hk r hr n hn hnN => (hLb k hk).pres r hr n hn hnN)
    (fun k hk r hr n hn hnN d _ _ α l v u s hs =>
      ((hLb k hk).smooth r hr n hn hnN d α l v u s hs).of_le hreg)
    (fun k hk r hr n hn hnN d _ _ α l v u Y => (hLb k hk).meas r hr n hn hnN d α l v u Y)
    (fun k hk r hr n hn hnN d _ _ α l v u s hs z Y =>
      (hLb k hk).shift ((rRho c)⁻¹ • latticeShift z)
        (fun t Y i j => pulseLiftData_G_shift c.D.α c.D.q c.D.Λ M c.D.ζ (c.D.hΦ (M - 1))
          (c.D.κ M) (c.D.κ (M - 1)) g.rho_pos.ne' _ k _ z t Y i j)
        (fun v u d γ hγ α t Y Z => liftEdges_fiber_coeff_shift g.rho_pos.ne' htorus
          (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (oddSlotOf k) z hγ α t Y Z)
        r hr n hn hnN d α l v u s hs Y)
    (fun k hk n hn hnN d hd hdn α l s hs Y => hLs k hk n hn hnN d hd hdn α l s hs Y)
    (fun k _ n _ _ d _ _ α l s _ => contDiff_refFallback _ _ _ k n d α l s _)
    (fun k _ n _ _ d _ _ α l Y => measurable_refFallback _ _ g.J_meas k n d α l Y _ _)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
  exact ⟨{
    C₂ := C₂
    C₂_nonneg := hC₂
    C₁ := C₁
    Lb := Lb
    Lsc := Lsc
    pulse := hLb
    scalar_smooth := hscC
    reading := hread
    actual := hAM }⟩

end AVRegularity.EntryTerminal.Ingredients.Recon.Letters
end
end

section
/-! Normalized coefficient budgets for the actual pulse means of the letters. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly
open AVRegularity.CycleComparison.ActualMeans
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Letters

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M ℓfamily : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The physical record matrix (before conjugation by the masses). -/
abbrev reconPhysicalEdge : Matrix (CompIn c.Gw.comps) (CompIn c.Gw.comps) ℝ :=
  Matrix.of fun v u => recordMajorant (c.Gw.mass c.lawW) c.Gw.fam v u /
    Real.sqrt ((c.Gw.mass c.lawW) u / (c.Gw.mass c.lawW) v)

private theorem physical_mask :
    CycleComparison.Coarse.maskedEdgeMatrix (familyAdj c.Gw.actualFamily) (reconPhysicalEdge c) =
      reconPhysicalEdge c := by
  classical
  ext v u
  rw [CycleComparison.Coarse.maskedEdgeMatrix_apply]
  split_ifs with h
  · rfl
  · have he : IsEmpty (c.Gw.fam.Γ v u) := not_nonempty_iff.mp h
    simp only [reconPhysicalEdge, Matrix.of_apply, recordMajorant, Fintype.sum_empty, mul_zero, zero_div]

private theorem physical_nonneg : ∀ v u, 0 ≤ reconPhysicalEdge c v u := by
  intro v u
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun γ _ =>
    mul_nonneg (norm_nonneg _) (c.Gw.fam.identity v u γ).record.size_nonneg)) (Real.sqrt_nonneg _)

/-- Every-order chart bounds on the clipped pulse window, from the renewal-chart theorem. -/
theorem recon_chart_jets (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M) (K : ℕ) :
    ∀ k : ℤ, ∀ t ∈ Set.Icc c.tp (c.tp + rTobs c),
      (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)⁻¹ * t ∈ Set.Icc (rSeqStart c k) (rSeqEnd c k) →
      ∀ j, 1 ≤ j → j ≤ K → ∀ y,
      ‖iteratedFDeriv ℝ j (reconChart c k t) y‖ ≤
        CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) j *
          (ocEpsilon c.D.q c.D.Λ (M - 1))⁻¹ ^ (j - 1) ∧
      ‖iteratedFDeriv ℝ j (reconLabel c k t) y‖ ≤
        CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)) j *
          (ocEpsilon c.D.q c.D.Λ (M - 1))⁻¹ ^ (j - 1) := by
  obtain ⟨hα, hq, hΛD, hζ, hseq, hband, -⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ (by omega : 1 ≤ A.Λ)
  have hν : 0 < c.D.κ M := CycleReference.bandChain_pos (by omega) X.hζ hband le_rfl
  have hℓ : 0 < ocEll c.D.q c.D.Λ M (c.D.κ M) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  intro k t _ hwin j hj _ y
  have ha := abs_sub_anchor_le c.D.α c.D.q hΛ1 M hℓ c.tp (c.tp + rTobs c) k hwin
  simp only [reconChart, reconLabel, hα, hq, hΛD]
  exact CycleComparison.Charts.ocChart_window_jets X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq
    X.ζ X.hζ A.Λ hΛ c.D.Φ hseq M hM (c.D.hΦ (M - 1)) _ t
    (by simpa only [hα, hq, hΛD] using ha) j hj y

private theorem setting_scales (kc : ℕ) (p : ReconPulseInput c kc) (g : ReconWindowGeometry c kc)
    (hfamily : ReconFamilyAt c ℓfamily) :
    ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) ≤ rRho c ∧
      rRho c ≤ ocEpsilon c.D.q c.D.Λ (M - 1) := by
  classical
  obtain ⟨T, hf⟩ := hfamily
  have hs := hf.2.2.2.2.2.2.2.2.1.2.2.1 c.tp ⟨le_rfl, g.window⟩
  obtain ⟨k, hk, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hs]; exact one_ne_zero)
  have hset := p.settings k hk
  exact ⟨(div_le_one hset.ρ_pos).mp hset.εc_le, (div_le_one hset.E_pos).mp hset.lam_le⟩

/-- The normalized positive-grade budget, at both the parent and observation radii. -/
theorem recon_positive_mean_budget (kc : ℕ) (p : ReconPulseInput c kc)
    (m : ReconPulseModel c kc p) (g : ReconWindowGeometry c kc) (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M)
    (hfamily : ReconFamilyAt c ℓfamily) :
    ∃ C : ℝ, ∀ r ∈ Finset.Icc 1 A.dW, ∀ v u,
    ENNReal.ofReal (Real.sqrt ((c.Gw.mass c.lawW) u / (c.Gw.mass c.lawW) v)) *
      ((∑ d : Finset.Icc 2 (A.NT + A.Dt),
        coefficientSeminorm (ocEpsilon c.D.q c.D.Λ (M - 1)) (rNc A kc)
          c.tp (c.tp + rTobs c) ((reconCE c m.Lb r v u d)) *
          (ENNReal.ofReal (c.D.κ (M - 1) * ocEpsilon c.D.q c.D.Λ (M - 1) ^ (d.1 - 2)))⁻¹) +
      ∑ d : Finset.Icc 2 (A.NT + A.Dt),
        coefficientSeminorm (rRho c) (rNc A kc) c.tp (c.tp + rTobs c) ((reconCE c m.Lb r v u d)) *
          (ENNReal.ofReal (c.D.κ (M - 1) * rRho c ^ (d.1 - 2)))⁻¹) ≤
      ENNReal.ofReal (C *
        (Real.sqrt ((c.Gw.mass c.lawW) u / (c.Gw.mass c.lawW) v) *
          (CycleComparison.Coarse.maskedEdgeMatrix (familyAdj c.Gw.actualFamily) (reconPhysicalEdge c) ^ r) v u)) := by
  classical
  obtain ⟨hα, hq, hΛD, hζ, hseq, hband, -⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ (by omega : 1 ≤ A.Λ)
  have hν : 0 < c.D.κ M := CycleReference.bandChain_pos (by omega) X.hζ hband le_rfl
  have hℓ : 0 < ocEll c.D.q c.D.Λ M (c.D.κ M) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  obtain ⟨hdρ, hρE⟩ := setting_scales c kc p g hfamily
  obtain ⟨T, hf⟩ := hfamily
  obtain ⟨hϖ0, -, hϖ1, -⟩ := partition_stage_facts hf.2.2.2.2.2.2.2.2.1
  obtain ⟨Ct, hCt, hbound⟩ := ceLetter_means_bound A.NT A.Dt (rNc A kc)
    (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)))
  refine ⟨2 * ((A.NT + A.Dt : ℕ) : ℝ) ^ 2 * ((rNc A kc : ℝ) + 1) * (Ct * m.C₂), ?_⟩
  intro r hr v u
  have hM0 : 0 ≤ m.C₂ * (reconPhysicalEdge c ^ r) v u :=
    mul_nonneg m.C₂_nonneg (matrix_pow_apply_nonneg (physical_nonneg c) r v u)
  have hreg : (((rNc A kc : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((p.K + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast p.order
  have h3 := hbound
    (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
    (ocEll c.D.q c.D.Λ M (c.D.κ M)) (c.D.κ (M - 1))
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1))) (rRho c)
    (ocEpsilon c.D.q c.D.Λ (M - 1)) c.tp (c.tp + rTobs c)
    (reconChart c) (reconLabel c) (rSeqStart c) (rSeqEnd c) m.Lb r v u
    (m.C₂ * (reconPhysicalEdge c ^ r) v u) hℓ g.B_pos g.rho_pos
    (CycleComparison.LiftSetting.dstar_eq _ _ _ hν.le _) hdρ hρE hM0 hϖ0 hϖ1
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t ht hwin j hj hjK y => recon_chart_jets c hΛ hM _ k t ht hwin j hj hjK y)
    (fun k hk n hn hnN d _ _ α l s hs =>
      ((m.pulse k hk).smooth r (Finset.mem_Icc.mp hr).2 n hn hnN d α l v u s hs).of_le hreg)
    (fun k hk n hn hnN d hd hdn α l i hi s hs Y =>
      (m.pulse k hk).bound r (Finset.mem_Icc.mp hr).2 n hn hnN d hd hdn α l v u i
        (hi.trans p.order) s hs Y) (rNc A kc) le_rfl
  rw [physical_mask c] 
  refine (mul_le_mul' le_rfl h3).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  ring

/-- The diagonal letter has a finite normalized budget. Only boundedness is needed here:
the order-two letter may be bounded by the raw mean plus the reference flux. -/
theorem recon_diagonal_mean_budget (kc : ℕ) (p : ReconPulseInput c kc)
    (m : ReconPulseModel c kc p) (g : ReconWindowGeometry c kc) (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M)
    (hfamily : ReconFamilyAt c ℓfamily) :
    ∃ C : ℝ, ∑ d : Finset.Icc 2 (A.NT + A.Dt),
      coefficientSeminorm (rRho c) (rNc A kc) c.tp (c.tp + rTobs c) (reconAD c m.Lsc d) *
        (ENNReal.ofReal (c.D.κ (M - 1) * rRho c ^ (d.1 - 2)))⁻¹ ≤ ENNReal.ofReal C := by
  classical
  obtain ⟨hα, hq, hΛD, hζ, hseq, hband, -⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ (by omega : 1 ≤ A.Λ)
  have hν : 0 < c.D.κ M := CycleReference.bandChain_pos (by omega) X.hζ hband le_rfl
  have hℓ : 0 < ocEll c.D.q c.D.Λ M (c.D.κ M) :=
    div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.mpr hν)
  have hE : 0 < ocEpsilon c.D.q c.D.Λ (M - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  obtain ⟨hdρ, hρE⟩ := setting_scales c kc p g hfamily
  obtain ⟨T, hf⟩ := hfamily
  obtain ⟨hϖ0, -, hϖ1, hsupp⟩ := partition_stage_facts hf.2.2.2.2.2.2.2.2.1
  set B := c.D.κ (M - 1)
  set CJ := c.D.κ M + ocHStar c.D.α c.D.q c.D.Λ M (c.D.κ M)
  set gm := ocA c.D.α c.D.q c.D.Λ (M - 1) * ocTauPP c.D.α c.D.q c.D.Λ M
  have hCJ : 0 ≤ CJ := add_nonneg hν.le (CycleReference.ocHStar_pos hΛ1 hν).le
  have hgm : 0 ≤ gm := mul_nonneg (Real.rpow_nonneg hE.le _)
    (Construction.Stream.ocTauPP_pos hΛ1).le
  have hJ : ∀ t, ∀ a b, |ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M) t a b| ≤ CJ :=
    fun t a b => refFlux_entry_abs_le hΛ1 (hζ ▸ X.hζ) hν t a b
  have hlam : 0 ≤ rRho c / ocEpsilon c.D.q c.D.Λ (M - 1) := div_nonneg g.rho_pos.le hE.le
  have hθ : 0 ≤ B * m.C₂ + CJ := add_nonneg (mul_nonneg g.B_pos.le m.C₂_nonneg) hCJ
  have hreg : ∀ i : ℕ, i ≤ rNc A kc →
      (((i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((p.K + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
    intro i hi
    exact_mod_cast hi.trans p.order
  have hhigh : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
      ∀ n, 3 ≤ n → n ≤ A.NT + A.Dt → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ i, i ≤ rNc A kc →
      ∀ s ∈ Set.Icc (rSeqStart c k) (rSeqEnd c k), ∀ Y,
        ‖iteratedFDeriv ℝ i (m.Lsc k n d α l s) Y‖ ≤
          m.C₂ * (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) ^ (n - d + i) := by
    intro k hk n hn hnN d hd hdn α l i hi s hs Y
    apply scalarReading_jet_le m.reading k n d α l s i Y
    · intro v
      exact ((m.pulse k hk).smooth 0 (Nat.zero_le _) n (by omega) hnN d α l v v s hs).of_le (hreg i hi)
    · intro v
      have hb := (m.pulse k hk).bound 0 (Nat.zero_le _) n (by omega) hnN d hd hdn α l v v i
        (hi.trans p.order) s hs Y
      rw [pow_zero, Matrix.one_apply_eq, mul_one] at hb
      exact hb
    · rw [refFallback_jet_of_ne _ _ _ k (by omega) d α l s i Y]
      exact mul_nonneg m.C₂_nonneg (pow_nonneg hlam _)
  have hpair : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c),
      ∀ (α : DerivativeWord2 1) (l : Fin 2), ∀ i, i ≤ rNc A kc →
      ∀ s ∈ Set.Icc (rSeqStart c k) (rSeqEnd c k), ∀ Y,
        ‖iteratedFDeriv ℝ i (fun Y' => B * m.Lsc k 2 2 α l s Y' +
          ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)
            (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 * s) l (α 0)) Y‖ ≤
          (B * m.C₂ + CJ) * (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) ^ i := by
    intro k hk α l i hi s hs Y
    apply scalarReading_pair_jet_le m.reading k 2 2 α l s i Y B _
    · intro v
      exact ((m.pulse k hk).smooth 0 (Nat.zero_le _) 2 le_rfl g.D_ge 2 α l v v s hs).of_le (hreg i hi)
    · intro v
      have hb := (m.pulse k hk).bound 0 (Nat.zero_le _) 2 le_rfl g.D_ge 2 le_rfl le_rfl α l v v i
        (hi.trans p.order) s hs Y
      simp only [pow_zero, Matrix.one_apply_eq, mul_one, Nat.sub_self, zero_add] at hb
      have hraw := CycleComparison.Diagonal.norm_iteratedFDeriv_smul_add_const_le i
        (fun Y' => m.Lb k 0 2 2 α s Y' l v v) (ContinuousLinearMap.id ℝ (ScalarH v.1.root)) B 0
        (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)
          (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 * s) l (α 0)) g.B_pos.le
        (((m.pulse k hk).smooth 0 (Nat.zero_le _) 2 le_rfl g.D_ge 2 α l v v s hs).of_le (hreg i hi)) Y
      simp only [zero_smul, sub_zero, mul_zero, zero_add] at hraw
      refine hraw.trans ?_
      by_cases hi0 : i = 0
      · subst hi0
        simp only [ite_true, pow_zero, mul_one] at hb ⊢
        refine add_le_add (mul_le_mul_of_nonneg_left hb g.B_pos.le) ?_
        exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)).trans
          (by simpa only [mul_one] using hJ _ l (α 0))
      · rw [ite_eq_right hi0, add_zero, add_mul]
        exact (mul_le_mul_of_nonneg_left hb g.B_pos.le).trans
          (by simpa only [B, mul_assoc] using
            (le_add_of_nonneg_right (a := B * m.C₂ * (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1)) ^ i)
              (mul_nonneg hCJ (pow_nonneg hlam i))))
    · rw [refFallback_pair_jet B _ g.B_pos.ne' _ k α l s i Y]
      exact mul_nonneg hθ (pow_nonneg hlam _)
  obtain ⟨Cad, -, had⟩ := adLetter_means_bound A.NT A.Dt (rNc A kc)
    (CycleComparison.Charts.chartJetConst (2 ^ 25) (2 ^ (-25 : ℤ)))
  refine ⟨_, had
    (ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c))
    (fun k => c.Gw.actualFamily.weight (oddSlotOf k))
    (ocEll c.D.q c.D.Λ M (c.D.κ M)) B
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1))) (rRho c)
    (ocEpsilon c.D.q c.D.Λ (M - 1)) c.tp (c.tp + rTobs c)
    (reconChart c) (reconLabel c) (rSeqStart c) (rSeqEnd c) m.Lsc
    (ocRefFlux c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.κ M)) m.C₂ (B * m.C₂ + CJ)
    (CycleComparison.Charts.chartDevConst (rNc A kc) * gm) CJ g.D_ge hℓ g.B_pos g.rho_pos
    (CycleComparison.LiftSetting.dstar_eq _ _ _ hν.le _) hdρ hρE m.C₂_nonneg hθ
    (mul_nonneg (CycleComparison.Charts.chartDevConst_nonneg _) hgm) hCJ hϖ0 hϖ1
    (fun k hk t ht hn => cellTime_mem_liftWindow (pow_pos hℓ 2) (hsupp k hk t hn) ht)
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChart_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t => (CycleComparison.Charts.contDiff_ocChartInv_joint _ _ _ _ _ _).comp
      ((contDiff_const (c := t)).prodMk contDiff_id))
    (fun k _ t ht hwin j hj hjK y => recon_chart_jets c hΛ hM _ k t ht hwin j hj hjK y)
    (fun k _ t _ hwin a b => by
      have ha := abs_sub_anchor_le c.D.α c.D.q hΛ1 M hℓ c.tp (c.tp + rTobs c) k hwin
      dsimp only [reconChart]
      simpa only [gm, hα, hq, hΛD] using CycleComparison.Charts.ocChart_jac_deviation
        X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ A.Λ hΛ c.D.Φ hseq M hM
        (c.D.hΦ (M - 1)) (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k) t
        (by simpa only [hα, hq, hΛD] using ha) (rNc A kc) a b)
    (fun t _ a b => hJ t a b) m.scalar_smooth hhigh hpair (rNc A kc) le_rfl⟩

/-- The explicit mean model supplies the normalized budget input of the letters. -/
theorem reconMeanBudget_of_model (kc : ℕ) (p : ReconPulseInput c kc) (m : ReconPulseModel c kc p)
    (g : ReconWindowGeometry c kc) (hΛ : 128 ≤ A.Λ) (hM : 2 ≤ M)
    (hfamily : ReconFamilyAt c ℓfamily) : Nonempty (ReconMeanBudget c kc) := by
  obtain ⟨Ca, hCa⟩ := recon_diagonal_mean_budget c kc p m g hΛ hM hfamily
  obtain ⟨Ce, hCe⟩ := recon_positive_mean_budget c kc p m g hΛ hM hfamily
  exact ⟨{
    AD := reconAD c m.Lsc
    CE := reconCE c m.Lb
    Lb := m.Lb
    transferCost := m.C₁
    physicalEdge := reconPhysicalEdge c
    physical_nonneg := physical_nonneg c
    diagonalCost := Ca
    edgeCost := Ce
    actual := m.actual
    diagonal_bound := hCa
    edge_bound := hCe }⟩

private theorem pulse_domain :
    ReconPrefix (κ := Unit) fun c _ _ _ _ => 128 ≤ c.D.Λ ∧ 2 ≤ c.Gw.level := by
  intro ℓ X
  refine ⟨128, le_rfl, fun A hΛ _ => ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ =>
    ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
      cP CP cHP Cw Ce cker _ => ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ =>
        ⟨2, fun M hM c _ => ?_⟩⟩⟩⟩⟩⟩
  exact ⟨c.data.2.2.1 ▸ hΛ, c.weak.2.2.1.symm ▸ hM⟩

/-- The complete budget transfer for the letters, through the exact prefix. The only remaining input
of the letters assembly is production of the high-order pulse setting and sequence. -/
theorem termReconPulseBudget : ReconPulseBudgetStatement := by
  apply (((termReconWindowGeometry.and termReconTimes.toReconPrefix).and termReconFamily).and pulse_domain).mono
    (fun _ => ())
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker
    j₀ M c x kc ℓ k h p
  obtain ⟨g⟩ := h.1.1.1
  have hf := h.1.2 h.1.1.2.2
  have hΛ : 128 ≤ A.Λ := c.data.2.2.1 ▸ h.2.1
  have hM : 2 ≤ M := c.weak.2.2.1 ▸ h.2.2
  obtain ⟨m⟩ := reconPulseModel_of_input c kc p g hΛ hM hf
  exact reconMeanBudget_of_model c kc p m g hΛ hM hf

end AVRegularity.EntryTerminal.Ingredients.Recon.Letters
end
end

section
/-! The letters from the window geometry and the Eulerian mean-letter ingredient, through the
literal reconstruction prefix. The geometric input is discharged by its proved producer; the mean-letter input is a hypothesis. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Letters

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The geometry and letters give every field of the coarse setting, and exactly the actual
mean presentations requested by the letters statement. -/
theorem reconLettersAt_of_inputs
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (kc : ℕ) (g : ReconWindowGeometry c kc) (m : ReconMeanLetters c kc) :
    ReconLettersAt c kc := by
  refine ⟨g.a, g.B₀, g.lam, m.AD, m.CE, m.Aedge, m.Cstar, m.Θ, ?_, m.presentation⟩
  exact {
    window := g.window
    rho_pos := g.rho_pos
    B_pos := g.B_pos
    D_ge := g.D_ge
    p_pos := le_rfl
    L_eq := rfl
    N_eq := rfl
    mass_pos := g.mass_pos
    drift_bdd := g.drift_bdd
    drift_meas := g.drift_meas
    drift_smooth := g.drift_smooth
    drift_div := g.drift_div
    drift_per := g.drift_per
    a_nonneg := g.a_nonneg
    B₀_ge := g.B₀_ge
    lam_pos := g.lam_pos
    drift_jets := g.drift_jets
    drift_scale := g.drift_scale
    drift_small := g.drift_small
    J_symm := g.J_symm
    J_meas := g.J_meas
    J_bdd := g.J_bdd
    cov_small := g.cov_small
    AD_meas := m.AD_meas
    AD_smooth := m.AD_smooth
    AD_per := m.AD_per
    AD_fin := m.AD_fin
    CE_meas := m.CE_meas
    CE_smooth := m.CE_smooth
    CE_per := m.CE_per
    CE_fin := m.CE_fin
    edge_nonneg := m.edge_nonneg
    edge_row := m.edge_row
    edge_col := m.edge_col
    edge_acyclic := m.edge_acyclic
    edge_mean := m.edge_mean }

/-- Exact letters prefix statement from its two named ingredients. -/
theorem termReconLetters_of_ingredients (hmean : ReconMeanLettersStatement) : TermReconLettersStatement := by
  apply (termReconWindowGeometry.and hmean).mono (fun _ => ())
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker
    j₀ M c x kc ℓ k h
  obtain ⟨g⟩ := h.1
  obtain ⟨m⟩ := h.2
  exact reconLettersAt_of_inputs c kc g m

/-- Exact letters statement from the normalized actual-mean budget; geometry and graph packing are proved. -/
theorem termReconLetters_of_budget (hbudget : ReconMeanBudgetStatement) : TermReconLettersStatement :=
  termReconLetters_of_ingredients (termReconMeanLetters_of_budget hbudget)

/-- The two remaining substeps of the letters: the high-order pulse input and its mean budgets. -/
theorem termReconLetters_of_pulse_ingredients
    (hpulse : ReconPulseInputStatement) (hbudget : ReconPulseBudgetStatement) :
    TermReconLettersStatement := by
  apply termReconLetters_of_budget
  apply (hpulse.and hbudget).mono (fun _ => ())
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker
    j₀ M c x kc ℓ k h
  obtain ⟨p⟩ := h.1
  exact h.2 p

/-- The letters from the high-order pulse producer; the letter construction, the mean transport and both normalized budgets are discharged. -/
theorem termReconLetters_of_pulse_input (hpulse : ReconPulseInputStatement) :
    TermReconLettersStatement :=
  termReconLetters_of_pulse_ingredients hpulse termReconPulseBudget

end AVRegularity.EntryTerminal.Ingredients.Recon.Letters
end
end

section
/-! High-order pulse input for the letters. Orders are chosen after A,kc, while the threshold in Lambda
comes from the order-independent band scale lemma. The shared terminal lift and native source
envelope are assembled at those orders, then the lift setting is transferred and the lift sequence `CcT` restarted. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryTerminal.QuietEntrance
open AVRegularity.EntryTerminal.Ingredients.Recon.Setting

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Letters

private theorem pulseInput_before_entrance :
    ReconPrefix (κ := Unit) fun c _ kc _ _ =>
      c.aM + ocTauP c.D.α c.D.q c.D.Λ c.Gw.level ≤ c.tp → Nonempty (ReconPulseInput c kc) := by
  intro ℓ X
  obtain ⟨Λa, hΛa, hsc⟩ := band_enhanced_lift_scale_bounds X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨max Λa 128, le_max_right _ _, fun A hΛ hV => ?_⟩
  have hΛA : Λa ≤ A.Λ := (le_max_left _ _).trans hΛ
  have hΛ128 : 128 ≤ A.Λ := (le_max_right _ _).trans hΛ
  have hN : 1 ≤ A.NT := qe_one_le_NT A hV
  have hDt : 2 ≤ A.Dt := le_max_left _ _
  have hbw : 0 < A.bw := hV.2.2.1.1
  obtain ⟨Mell, -, hell⟩ := uniform_native_lift_ellipticity_all_carriers X.α X.s X.q
    X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ hΛ128 X.ζ X.hζ
  refine ⟨0, fun kc _ => ?_⟩
  let ell' := rNc A kc
  let K := rKlift A ell'
  let L := rLlift A ell'
  let qs := K + 4 * (A.dW + 1) * (A.NT + A.Dt) ^ 2
  let qf := max L (L + 2) + A.dW * A.Dt + 2 * A.NT + 2 * A.Dt
  obtain ⟨CG, Cw, m₀, -, -, -, hmain⟩ := Construction.TerminalLift.terminal_level_lift
    X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq A.Λ hΛ128 X.ζ X.hζ A.dW A.NT K L L A.Dt hN hDt
  obtain ⟨B, hB, hsrc⟩ := stage_native_lift_source_exists_envelope A.bw hbw qs qf
  let Cj := fun r q => (Fintype.card (Finset.Icc 2 A.Dt) : ℝ) * B (r + q)
  let Ca : ℝ := ∑ r ∈ Finset.range (qs + 1), ∑ q ∈ Finset.range (qf + 1), Cj r q
  have hCj : ∀ r q, 0 ≤ Cj r q := fun r q => mul_nonneg (Nat.cast_nonneg _) (hB _)
  have hCa : ∀ r, r ≤ qs → ∀ q, q ≤ qf → Cj r q ≤ Ca := by
    intro r hr q hq
    refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ q ∈ Finset.range (qf + 1), Cj r q)
      (fun r _ => Finset.sum_nonneg fun q _ => hCj r q) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr)))
    exact Finset.single_le_sum (f := fun q => Cj r q) (fun q _ => hCj r q)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
  refine ⟨K + A.Dt + 2, max (L + 1) (L + 2), 0, fun sXT sZT hX hZ Kout _ => ⟨0, ?_⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ hcr hcr1 hone _ _ _ _ _ _
    cK CK CL Cχ Cread Cid kW hcK hkc _ cP CP cHP Cw' Ce cker _
  obtain ⟨m₁, -, hscale⟩ := hsc A.Λ hΛA cr hcr
  obtain ⟨M₂, -, hratio⟩ := qe_eps_ratio (q := X.q) (Λ := A.Λ) X.hq.1 hΛ128 CL
  refine ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ =>
    ⟨max (max (max m₀ m₁) (max j₀ M₂)) (Mell + 1), fun M hM c x hentry => ?_⟩⟩
  have hn : ∀ (k : ℤ) (hk : Odd k), NativeSlotSetting c.D M c.Gw c.lawW cr
      (Cχ * c.D.eps M ^ A.χw) A.NT A.dW K L L CG Cw Cj k hk := by
    intro k hk
    let D := c.D
    let Gw := c.Gw
    let lawW := c.lawW
    let PW := c.PW
    let a := c.a
    let aM := c.aM
    have hD : IsTermData X A.Λ M D := c.data
    have hW : IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW
        a A.T₀ A.σw CL Cχ A.χw Gw aM := c.weak
    have hG0 := x.reserve
    obtain ⟨hDα, hDq, hDΛ, hDζ, hseq, hband, hterm⟩ := hD
    obtain ⟨-, -, hlev, hdepth, hroot, -, hid, -, -, hinv⟩ := hW
    have hm₀M : m₀ ≤ M := (by omega : m₀ ≤ M)
    have hm₁M : m₁ ≤ M := (by omega : m₁ ≤ M)
    have hjM : j₀ ≤ M := (by omega : j₀ ≤ M)
    have hM₂M : M₂ ≤ M := (by omega : M₂ ≤ M)
    have hΛD : 128 ≤ D.Λ := hDΛ ▸ hΛ128
    have hqD : 1 < D.q := hDq ▸ X.hq.1
    have hbandD : IsOCBandChain X.α X.q A.Λ X.ζ D.term D.κ := hterm ▸ hband
    have hscl := hscale D.term D.κ hbandD M hm₁M (le_of_eq hterm.symm)
    have hprev : M - 1 ≤ D.term := le_trans (Nat.sub_le M 1) (le_of_eq hterm.symm)
    have key : 0 < cr * liftLength D M ∧
        ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1)) / (cr * liftLength D M) ≤ 1 ∧
        (cr * liftLength D M) / D.eps (M - 1) ≤ 1 := by
      simpa only [liftLength, OCData.kap, Nat.min_eq_left (le_of_eq hterm.symm),
        Nat.min_eq_left hprev, OCData.eps, hDα, hDq, hDΛ, hDζ] using hscl.2
    rw [← hlev] at key
    obtain ⟨hρ, hcell, hlam⟩ := key
    have hres : ∀ v : CompIn Gw.comps, 0 ≤ compReserve kW v.1 :=
      fun v => (qe_compReserve_bounds kW hG0 v.1 (hroot v)).1
    have hres2 : ∀ v : CompIn Gw.comps, compReserve kW v.1 ≤ 2 :=
      fun v => (qe_compReserve_bounds kW hG0 v.1 (hroot v)).2
    have hlen : ∀ v u γ, 1 ≤ (Gw.fam.identity v u γ).record.birthExcess →
        (Gw.fam.identity v u γ).record.length ≤ D.eps Gw.level := by
      intro v u γ _
      have hE : D.eps Gw.level = D.eps M := congrArg D.eps hlev
      rw [hE]
      have h1 := (hid v u γ).2.2.1
      have h2 := hratio M hM₂M
      have h3 : D.eps (M + 1) = ocEpsilon X.q A.Λ (M + 1) := by
        simp only [OCData.eps, hDq, hDΛ]
      have h4 : D.eps M = ocEpsilon X.q A.Λ M := by simp only [OCData.eps, hDq, hDΛ]
      rw [h3] at h1
      rw [h4]
      exact h1.trans h2
    have hinv0 := hinv
    obtain ⟨hnat, -, -, -, hpar, hcert, -, -⟩ := hinv
    have hπ : ∀ v : CompIn Gw.comps, 0 < Gw.mass lawW v :=
      fun v => Construction.Preservation.Buffer.birth_compMass_pos hqD hΛD lawW v.1
    have hεpos : 0 ≤ D.eps (Gw.level - 1) :=
      le_of_lt (Construction.Stream.ocEpsilon_pos (q := D.q) (Λ := D.Λ) (by omega))
    have hsrc' := hsrc ScalarH D A.Dt j₀ Gw lawW PW _ _ A.φ₀ A.hφ₀ (M + A.Jw) kW aM (a + A.T₀) _ _
      hinv0 (by omega) (by omega) (Construction.Stream.ocEpsilon_pos (by omega)) hqD hΛD
      (hDζ ▸ X.hζ) (by rw [hDα, hDq, hDΛ, hDζ]; exact hbandD) hres hres2 hlen ⟨k, hk⟩
      ((cr * liftLength D Gw.level) / D.eps (Gw.level - 1)) (div_nonneg hρ.le hεpos)
      (fun _ => 1) (Or.inl rfl)
    simp only [one_pow, div_one] at hsrc'
    have hz : ∀ v u (d : Finset.Icc 2 A.Dt), A.Dt < d.1 →
        (familyLiftData D Gw.level k (nativeChain Gw.level k) (cr * liftLength D Gw.level)
          (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩))).edge v u d = [] := by
      intro v u d hd
      exact False.elim (Nat.not_lt_of_ge (Finset.mem_Icc.mp d.2).2 hd)
    have hset := hmain ScalarH D hDα hDq hDΛ hDζ hseq
      (by rw [hDα, hDq, hDΛ, hDζ]; exact hbandD) A.Dt j₀ (M + A.Jw) A.bw Gw kW hbw hcert hpar hnat
      (by omega) (by omega) (by omega) hdepth hres hres2 ⟨k, hk⟩ (cr * liftLength D Gw.level) hρ
      hcell hlam (Gw.mass lawW) hπ le_rfl
      (fun r q => (Fintype.card (Finset.Icc 2 A.Dt) : ℝ) * B (r + q))
      (recordMajorant (Gw.mass lawW) Gw.fam) (Cχ * D.eps M ^ A.χw) hz hsrc'
    obtain ⟨hsetting, -, -, -⟩ := hset
    change NativeSlotSetting D M Gw lawW cr (Cχ * D.eps M ^ A.χw) A.NT A.dW K L L CG Cw Cj k hk
    rw [← hlev]
    exact ⟨Cχ * D.eps M ^ A.χw, by rw [hlev], hsetting⟩
  have hM1 : 1 ≤ M := by omega
  have hΛ1 : 1 ≤ A.Λ := by omega
  rw [c.weak.2.2.1] at hentry
  have hseq := reconSeqStep_of_ctx c x ell' hΛ1 hM1 (seqEll_of_uniform c hell (by omega)) hX hZ hentry
  refine ⟨{
    K := K
    L := L
    order := ?_
    CG := CG
    Cw := Cw
    Cj := fun _ _ => Ca
    qs := qs
    qf := qf
    par := pulseParallel
    V := fun k => pulseShearProfile c.D.α c.D.q c.D.Λ M c.D.ζ (c.D.κ M) k
    price := Cχ * c.D.eps M ^ A.χw
    settings := fun k hk => setting_of_native c hone hΛ1 hM1 ell' hCa le_rfl hk
      (hn k (CycleComparison.LiftSetting.obsPulse_odd hk))
    sequences := hseq }⟩
  simp only [K, ell', rKlift, rKmax]
  omega

/-- The high-order pulse input, with its order choices after A,kc and its level floor before c. -/
theorem termReconPulseInput : ReconPulseInputStatement := by
  apply (pulseInput_before_entrance.and termReconTimes.toReconPrefix).mono (fun _ => ())
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker
    j₀ M c x kc ℓ k h
  apply h.1
  simpa only [c.weak.2.2.1] using h.2.1

end AVRegularity.EntryTerminal.Ingredients.Recon.Letters

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- **The letters of the reconstruction window**: the actual reconstruction window has mean letters and its complete coarse
setting at p_c = 1, J_c = 0, with the literal reconstruction prefix and no open inputs. -/
theorem termReconLetters : TermReconLettersStatement :=
  Letters.termReconLetters_of_pulse_input Letters.termReconPulseInput

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
