-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftField
import AVRegularity.Finite.TerminalLift.PositiveTransfer
import AVRegularity.Finite.TerminalLift.PositiveGeometry
import AVRegularity.EntryTerminal.Ingredients.QuietEntrance.ZeroAssembly
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.TerminalLift.Assembly

section
@[expose] public section
open AVRegularity.Finite.TerminalLift
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The lifted field from the terminal lift sequences alone.** The difference bounds
`TerminalDifferenceBoundsGeneralStatement` hold: they follow from the shared physical
transfer `terminal_shared_physical_transfer`, through the raw jet coupling and the profile jet
packing. So `LiftFieldStatement` depends only on `TerminalLiftSeqStatement`. -/

/-- **The lifted field, depending only on the terminal lift sequences.** -/
theorem liftField_of_seq (hseq : TerminalLiftSeqStatement) :
    AVRegularity.EntryTerminal.Route.LiftFieldStatement :=
  liftField_of hseq (terminal_difference_bounds_of_jets
    (terminal_difference_jets_of_physical_transfer terminal_shared_physical_transfer))

end AVRegularity.EntryTerminal.Ingredients
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.EntryWeakProofs
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.EntryTerminal.Ingredients

/-! **The lift sequences at the terminal level**. `TerminalLiftSeqStatement` is proved from
`terminal_level_lift` (the orders are `Ksrc = D̄₀`, `K = s_XT - D̄₀ - 2`, `k + 1 = L + 2 = s_ZT`).
Its premise `kW.G0 ≤ kW.Hprod + 1` is needed for the reserves of the root components
(`0 ≤ compReserve ≤ 2`, a hypothesis of `terminal_level_lift`), and `LiftFieldStatement` carries
it. -/

/-- **The lift sequences at the terminal level** from `terminal_level_lift`. -/
theorem terminalLiftSeq : TerminalLiftSeqStatement := by
  intro X
  obtain ⟨Λa, hΛa, hsc⟩ := band_enhanced_lift_scale_bounds X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨max Λa 128, le_max_right _ _, fun A hΛ hV => ?_⟩
  have hΛA : Λa ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hΛ128 : 128 ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hN : 1 ≤ A.NT := QuietEntrance.qe_one_le_NT A hV
  have hDt : 2 ≤ A.Dt := le_max_left _ _
  have hbw : 0 < A.bw := hV.2.2.1.1
  refine ⟨A.Dt + 2, 2, fun sXT sZT hX hZ nW cr hcr hcr1 kW CL Cχ hG0 j₀ => ?_⟩
  obtain ⟨CG, Cw, m₀, hCG, hCw, hm₀, hmain⟩ := Construction.TerminalLift.terminal_level_lift
    X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq A.Λ hΛ128 X.ζ X.hζ A.dW A.NT (sXT - A.Dt - 2)
    (sZT - 1) (sZT - 2) A.Dt hN hDt
  obtain ⟨B, hB, hsrc⟩ := stage_native_lift_source_exists_envelope A.bw hbw
    ((sXT - A.Dt - 2) + 4 * (A.dW + 1) * (A.NT + A.Dt) ^ 2)
    (max (sZT - 1) (sZT - 2 + 2) + A.dW * A.Dt + 2 * A.NT + 2 * A.Dt)
  obtain ⟨m₁, hm₁, hscale⟩ := hsc A.Λ hΛA cr hcr
  obtain ⟨M₂, hM₂, hratio⟩ := QuietEntrance.qe_eps_ratio (q := X.q) (Λ := A.Λ) X.hq.1 hΛ128 CL
  refine ⟨max (max m₀ m₁) (max j₀ M₂), fun M hM D hD a lawW PW Gw aM hW => ?_⟩
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseq, hband, hterm⟩ := hD
  obtain ⟨-, -, hlev, hdepth, hroot, -, hid, -, -, hinv⟩ := hW
  have hm₀M : m₀ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hm₁M : m₁ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hjM : j₀ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hM₂M : M₂ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
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
    fun v => (QuietEntrance.qe_compReserve_bounds kW hG0 v.1 (hroot v)).1
  have hres2 : ∀ v : CompIn Gw.comps, compReserve kW v.1 ≤ 2 :=
    fun v => (QuietEntrance.qe_compReserve_bounds kW hG0 v.1 (hroot v)).2
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
  have hex : ∀ (k : ℤ) (hk : Odd k), ∃ Cc : ℕ → ℕ → LiftCoeff (CompIn Gw.comps)
      (fun v => ScalarH v.1.root),
      IsLiftSequence (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
          (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)))
        sXT sZT (D.slotStart M k / D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) A.NT A.dW Cc := by
    intro k hk
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
      (by rw [hDα, hDq, hDΛ, hDζ]; exact hbandD) A.Dt j₀ (M + A.Jw) A.bw Gw kW hbw hcert hpar
      hnat (by omega) (by omega) (by omega) hdepth hres hres2 ⟨k, hk⟩ (cr * liftLength D Gw.level)
      hρ hcell hlam (Gw.mass lawW) hπ le_rfl
      (fun r q => (Fintype.card (Finset.Icc 2 A.Dt) : ℝ) * B (r + q))
      (recordMajorant (Gw.mass lawW) Gw.fam) (Cχ * D.eps M ^ A.χw) hz hsrc'
    obtain ⟨-, Cc, -, hamb⟩ := hset
    have e1 : sXT - A.Dt - 2 + A.Dt + 2 = sXT := by omega
    have e2 : max (sZT - 1 + 1) (sZT - 2 + 2) = sZT := by omega
    rw [e1, e2] at hamb
    rw [← hlev]
    exact ⟨Cc, hamb⟩
  have hdef : ∃ C0 : ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root), True := by
    obtain ⟨C, -⟩ := hex 1 odd_one
    exact ⟨C, trivial⟩
  classical
  refine ⟨fun k => if hk : Odd k then (hex k hk).choose else hdef.choose, fun k hk => ?_⟩
  simp only [hk, ↓reduceDIte]
  exact (hex k hk).choose_spec

/-- **The lifted field**: `LiftFieldStatement`. -/
theorem liftField : LiftFieldStatement := liftField_of_seq terminalLiftSeq

end AVRegularity.EntryTerminal.Ingredients
end
end
