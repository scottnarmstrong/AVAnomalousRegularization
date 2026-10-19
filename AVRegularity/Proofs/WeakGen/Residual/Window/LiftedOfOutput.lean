-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.Window.Scale
import AVRegularity.Proofs.WeakGen.Comparison.RowCoefficients
public import AVRegularity.EntryTerminal.Ingredients.Recon.Seq.Main
import AVRegularity.EntryTerminal.Ingredients.Recon.R2Core.Quiet
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.EntryTerminal.Ingredients.Recon.Family.Main
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.EntryTerminal.Ingredients.Recon.Conv.Conv
import AVRegularity.CycleComparison.Coarse.Fact.FBoundOps
import AVRegularity.CycleReference.ChartTestTransport

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Providers.WeakGen.Window

/-! **The lift sequences: the split and the compiled assembly**. `WeakSeqStep` from three named parts, each
for one odd slot `k`:

* `WeakSeqCap`: the lift sequence `h.lifts i` of the ambient data, restricted
  to the cap `D_w` (`isLiftSequence_restrict`; `EdgesBelow` of the fibre).
* `WeakSeqAgree`: on the pulse window the restricted data agree with `wLiftData`
  (`SeqAgreeAt`; `native_familyLiftData_metric`, `seq_sourceFlux_actual_eq`; `ν = B = κ_M`).
* `WeakSeqQuietZero`: the positive lifts vanish at the cell time of `t_i` when
  `t_i` lies in the slot window (`t_i` is the midpoint of a quiet margin: `weakSlotNativeQuiet`).

The assembly follows `reconSeqStep_of_ctx`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The ambient lift data of the odd slot `k` of the stage `i`, restricted to the cap `D_w`. -/
abbrev weakCapData (c : WeakPassageInstance plan R) (i : ℕ) (k : ℤ) (hk : Odd k) :
    LiftOperatorData (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root) (weakDw A) :=
  Providers.WeakGen.restrictData (by exact c.order_ge)
    (familyLiftData c.D i k (nativeChain i k) (c.D.eps (i - 1))
      ((c.stage i).fam.fiber ⟨k, hk⟩ ((c.stage i).actual ⟨k, hk⟩)))

/-- **Part 1**: the lift sequence on the whole slot window, at the cap
`D_w`. -/
def WeakSeqCap (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (h : WeakComparisonInput r i) : Prop :=
  ∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (weakCapData c i k hk) R.sX R.sZ (c.D.slotStart i k / c.D.cellScaleSq i)
      ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i) / c.D.cellScaleSq i) A.Nw (weakH A)
      (h.CcR i k)

/-- **Part 2 (open, moderate)**: on the pulse window the restricted data and `wLiftData` agree. -/
def WeakSeqAgree (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) :
    Prop :=
  ∀ (k : ℤ) (hk : Odd k),
    (weakCapData c i k hk).η = (wLiftData c i hi hit k).η ∧
      ∀ t, c.D.cellScaleSq i * t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ i k →
        EntryTerminal.Ingredients.Recon.Seq.SeqAgreeAt (weakCapData c i k hk)
          (wLiftData c i hi hit k) t

/-- **Part 3 (open, moderate-hard)**: the positive lifts vanish at the cell time of `t_i` when
`t_i` lies in the slot window of `k`. -/
def WeakSeqQuietZero (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (h : WeakComparisonInput r i) : Prop :=
  ∀ (k : ℤ) (hk : Odd k), r.tq i < r.a + A.T₀ → c.D.slotStart i k ≤ r.tq i →
    r.tq i ≤ ((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i →
    IsLiftSequence (weakCapData c i k hk) R.sX R.sZ (c.D.slotStart i k / c.D.cellScaleSq i)
      ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i) / c.D.cellScaleSq i) A.Nw (weakH A)
      (h.CcR i k) →
    ∀ hh ≤ weakH A, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u,
      h.CcR i k hh n m α (r.tq i / c.D.cellScaleSq i) X z v u = 0

/-- **The lift sequences from the three parts** (the assembly of `reconSeqStep_of_ctx`). -/
theorem weakSeqStep_of_parts (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (k₀ : ℕ)
    (hcap : WeakSeqCap c r i h) (hag : WeakSeqAgree c i hi hit)
    (hz : WeakSeqQuietZero c r i h) : WeakSeqStep c r i hi hit h k₀ := by
  classical
  intro hdl hX hZ k hkobs
  obtain ⟨hΛ, -, hζ, hband⟩ := Comparison.weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hζp := hζ
  have hκM : 0 < c.D.κ c.M := by
    have h0 := weakData_kap_pos c.D hΛ1 hζp hband i
    rwa [weakData_kap_terminal c.D i (by rw [c.terminal]; exact hi.le), c.terminal] at h0
  have hkap : c.D.kap i = c.D.κ c.M := by
    rw [weakData_kap_terminal c.D i (by rw [c.terminal]; exact hi.le), c.terminal]
  have hcs : 0 < c.D.cellScaleSq i := by
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hκM
  have hc : ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2 = c.D.cellScaleSq i := by
    rw [CycleReference.ocEll_sq_eq hκM]; unfold OCData.cellScaleSq OCData.eps; rw [hkap]
  obtain ⟨-, hk, y, ⟨hy1, hy2⟩, hy3, hy4⟩ := Finset.mem_filter.1 hkobs
  set τ := ocTau c.D.α c.D.q c.D.Λ i with hτdef
  have hlo : wSeqStart c r i k = max (((k : ℝ) - 61 / 48) * τ) (r.tq i) / c.D.cellScaleSq i := by
    unfold wSeqStart; rw [hc]
  have hhi : wSeqEnd c r i k =
      min (((k : ℝ) + 61 / 48) * τ) (r.tq i + wTobs c r i) / c.D.cellScaleSq i := by
    unfold wSeqEnd; rw [hc]
  have hseq0 := hcap k hk
  have hmem : ∀ t ∈ Set.Icc (wSeqStart c r i k) (wSeqEnd c r i k),
      c.D.cellScaleSq i * t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ i k := by
    intro t ht
    rw [hlo] at ht; rw [hhi] at ht
    have h1 := (div_le_iff₀ hcs).1 ht.1
    have h2 := (le_div_iff₀ hcs).1 ht.2
    have e : t * c.D.cellScaleSq i = c.D.cellScaleSq i * t := mul_comm _ _
    exact ⟨(((le_max_left _ _).trans h1).trans_eq e), (e.symm.le.trans h2).trans (min_le_left _ _)⟩
  have hhi_le : wSeqEnd c r i k ≤ (((k : ℝ) + 61 / 48) * τ) / c.D.cellScaleSq i := by
    rw [hhi]; exact div_le_div_of_nonneg_right (min_le_left _ _) hcs.le
  have hseq1 : IsLiftSequence (weakCapData c i k hk) R.sX R.sZ (wSeqStart c r i k)
      (wSeqEnd c r i k) A.Nw (weakH A) (h.CcR i k) := by
    by_cases hcase : r.tq i ≤ ((k : ℝ) - 61 / 48) * τ
    · have hl : wSeqStart c r i k = c.D.slotStart i k / c.D.cellScaleSq i := by
        rw [hlo, max_eq_left hcase]; rfl
      rw [hl]
      exact EntryTerminal.Ingredients.Recon.R2Core.r2c_liftSequence_restrict_right hseq0 hhi_le
    · have hcase' : c.D.slotStart i k ≤ r.tq i := (not_le.1 hcase).le
      have hl : wSeqStart c r i k = r.tq i / c.D.cellScaleSq i := by
        rw [hlo, max_eq_right (not_le.1 hcase).le]
      have hwin : r.tq i ≤ ((k : ℝ) + 61 / 48) * τ := hy3.trans hy2
      have hzero := hz k hk hdl hcase' hwin hseq0
      rw [hl]
      exact EntryTerminal.Ingredients.Recon.R2Core.r2c_liftSequence_restart hseq0
        (div_le_div_of_nonneg_right hcase' hcs.le) hhi_le hzero
  obtain ⟨hη, hag'⟩ := hag k hk
  exact isLiftSequence_mono (EntryTerminal.Ingredients.Recon.Seq.seq_isLiftSequence_congr _ _ hη
    (fun t ht => hag' t (hmem t ht)) hseq1) (by omega) (by omega)
end

/-! **Lift sequences, part 1: the lift sequence at the cap `D_w`**. The fibre of a passage
stage vanishes above `1 + J_wN_w` (`weakStage_maxOrder_le`), so the lift sequences
`h.lifts i` of the ambient data restrict to the cap `D_w` (`isLiftSequence_restrict`). -/

section
open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The fibre of a passage stage vanishes above `D_w`.** -/
theorem weakStage_fiber_edgesBelow (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (p : OddSlot) :
    EdgesBelow (weakDw A) ((c.stage i).fam.fiber p ((c.stage i).actual p)) := by
  intro v u d hd
  unfold ChartedFamily.fiber
  rw [List.filterMap_eq_nil_iff]
  intro γ _
  have hmax := weakStage_maxOrder_le c i hi hit v u γ
  rw [dite_eq_right_iff]
  intro h'
  exact absurd h' (not_le.2 (lt_of_le_of_lt hmax hd))

/-- **Part 1 proved**: the lift sequence on the slot window, at the cap `D_w`. -/
theorem weakSeqCap_of (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) :
    WeakSeqCap c r i h := by
  intro k hk
  have hJ : 1 ≤ A.Jw :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.add_zero] at hit; exact absurd hit (not_le.2 hi)
  have hNl : A.Nw ≤ weakDw A :=
    le_trans (Nat.le_mul_of_pos_left _ hJ) (Nat.le_add_left _ _)
  have hE : EdgesBelow (weakDw A)
      (familyLiftData c.D i k (nativeChain i k) (c.D.eps (i - 1))
        ((c.stage i).fam.fiber ⟨k, hk⟩ ((c.stage i).actual ⟨k, hk⟩))).edge :=
    edgesBelow_liftEdges (weakStage_fiber_edgesBelow c i hi hit ⟨k, hk⟩) _ _
  exact isLiftSequence_restrict c.order_ge hE (h.CcR i k) hNl (h.lifts i hi hit k hk)
end

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.Providers.WeakGen.Window

/-! **The part of the family side that needs no atlas**: descent, torus
compatibility, pieces, injectivity and the lift partition of the window family of a weak passage
(`WeakFamilyBody` minus the atlas fields `hTcons, hTcov, hTq, hTact` and `hquiet`). -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.EntryWeakProofs
  AVRegularity.Providers.WeakGen.Comparison

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The passage stages are natural at the top level `M + J_w`. -/
theorem weakStage_isNatural (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) : (c.stage i).IsNatural (c.M + A.Jw) := by
  by_cases hiJ : i = c.M + A.Jw
  · subst hiJ
    have h := c.construction.2.1.2.2.2
    exact h
  · exact weakConstruction_output_natural c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le
      (lt_of_le_of_ne hit hiJ)

/-- The passage stages satisfy the torus law. -/
theorem weakStage_isShiftInvariant (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) : (c.stage i).IsShiftInvariant := by
  obtain ⟨hΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  exact weakConstruction_shiftInvariant c.P _ c.M A.Jw 0 _ c.stage c.construction hζ
    (fun _ => Construction.Stream.ocTau_pos hΛ1) (fun _ => Construction.Stream.ocEpsilon_pos hΛ1)
    (fun m _ _ => (weakData_cellScaleSq_pos c.D hΛ1 hζ hband m).le) i hi.le hit

/-- **Torus compatibility of the window family.** -/
theorem weakWindowFamily_isTorusCompatible (c : WeakPassageInstance plan R) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) :
    IsTorusCompatible (weakWindowFamily c i hi hit) (fun _ => ())
      (ocEpsilon c.D.q c.D.Λ (i - 1)) := by
  have hlev : (c.stage i).level = i :=
    weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le hit
  have h := GenStage.isTorusCompatible_of_shiftInvariant
    (recap_isNatural (N := 1 + A.Jw * A.Nw) (hN := weakStage_maxOrder_le c i hi hit)
      (𝒮 := (c.stage i).exports) (weakStage_isNatural c i hi hit))
    (recap_isShiftInvariant (N := 1 + A.Jw * A.Nw) (hN := weakStage_maxOrder_le c i hi hit)
      (𝒮 := (c.stage i).exports) (weakStage_isShiftInvariant c i hi hit))
  have e : c.D.eps ((weakWindowStage c i hi hit).level - 1) = ocEpsilon c.D.q c.D.Λ (i - 1) := by
    simp [weakWindowStage, GenStage.recap, hlev, OCData.eps]
  rw [← e]
  exact GenStage.isTorusCompatible_actualFamily (weakWindowStage c i hi hit) h

/-- **The pulses' pieces, injectivity and the lift partition of the window family.** -/
theorem weakWindowFamily_pieces (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) :
    (∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
      ((weakWindowFamily c i hi hit).piece (oddSlotOf k)).label =
          ocPulseChartIndex c.D.α c.D.q c.D.Λ i k ∧
        (∀ t, ⇑(((weakWindowFamily c i hi hit).piece (oddSlotOf k)).material t) =
          ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) t) ∧
        ocPulseWindow c.D.α c.D.q c.D.Λ i k ∩ Set.Icc (r.tq i) (r.tq i + wTobs c r i) ⊆
          ((weakWindowFamily c i hi hit).piece (oddSlotOf k)).output) ∧
    Set.InjOn oddSlotOf ↑(ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i)) ∧
    IsLiftPartition (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i))
      (fun k => (weakWindowFamily c i hi hit).weight (oddSlotOf k))
      (ocPulseWindow c.D.α c.D.q c.D.Λ i) (ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i)
      (Set.Icc (r.tq i) (r.tq i + wTobs c r i)) (ocTau c.D.α c.D.q c.D.Λ i) weakCpart := by
  obtain ⟨hΛ, -, hζ, -⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hlev : (c.stage i).level = i :=
    weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le hit
  have hnat := weakStage_isNatural c i hi hit
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ i := Construction.Stream.ocTauPP_pos hΛ1
  have hobsodd : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i), Odd k :=
    fun k hk => by
      classical
      unfold ocObsPulses at hk
      exact (Finset.mem_filter.1 hk).2.1
  have hw : ∀ p : OddSlot, (weakWindowFamily c i hi hit).weight p =
      ocCutoff c.D.α c.D.q c.D.Λ i p.1 := by
    intro p
    funext t
    have := hnat.2.1 p t
    simp only [hlev] at this
    exact this
  have hpart := EntryTerminal.Ingredients.Recon.Family.reconFamily_liftPartition
    (α := c.D.α) (q := c.D.q) (m := i) (ζ := c.D.ζ) hΛ1 hζ (r.tq i) (r.tq i + wTobs c r i)
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · have hk' := hobsodd k hk
    obtain ⟨hl, ho, -, -, hm⟩ := hnat.1 (oddSlotOf k)
    rw [oddSlotOf_of_odd hk'] at hl ho hm
    simp only [hlev] at hl ho hm
    rw [oddSlotOf_of_odd hk']
    refine ⟨hl.trans (ocLabel_eq_ocPulseChartIndex _ _ _ _ k hτ''), fun t => ?_, ?_⟩
    · show _ = ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
        (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) t
      refine (hm t).trans ?_
      funext y
      unfold ocChart OCData.flowOf OCData.slotAnchor
      rw [ocLabel_eq_ocPulseChartIndex _ _ _ _ k hτ'']
    · show _ ⊆ ((c.stage i).fam.piece _).output
      rw [ho]
      exact Set.inter_subset_left
  · exact oddSlotOf_injOn.mono fun k hk => hobsodd k hk
  · refine EntryTerminal.Ingredients.Recon.Family.reconFamily_isLiftPartition_congr
      (fun k hk => ?_) hpart
    rw [hw, oddSlotOf_of_odd (hobsodd k hk)]

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Providers.WeakGen.Window

/-! **Lift sequences, part 2: the restricted ambient lift data of the slot agree with `wLiftData`**.
Model: the same step at terminal entry (`EntryTerminal.Ingredients.Recon.Seq.seq_agree`). -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The output window of a piece of a passage stage is the pulse window. -/
theorem weakStage_output_eq (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (p : OddSlot) :
    ((c.stage i).fam.piece p).output = ocPulseWindow c.D.α c.D.q c.D.Λ i p.1 := by
  have hlev : (c.stage i).level = i :=
    weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le hit
  have := ((weakStage_isNatural c i hi hit).1 p).2.1
  simp only [hlev] at this
  exact this

/-- **Part 2 proved.** -/
theorem weakSeqAgree_of (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) : WeakSeqAgree c i hi hit := by
  intro k hk
  obtain ⟨hΛ, -, hζ, hband⟩ := Comparison.weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hζp := hζ
  have hκM : 0 < c.D.κ c.M := by
    have h0 := weakData_kap_pos c.D hΛ1 hζp hband i
    rwa [weakData_kap_terminal c.D i (by rw [c.terminal]; exact hi.le), c.terminal] at h0
  have hkap : c.D.kap i = c.D.κ c.M := by
    rw [weakData_kap_terminal c.D i (by rw [c.terminal]; exact hi.le), c.terminal]
  have hkap1 : c.D.kap (i - 1) = c.D.κ c.M := by
    rw [weakData_kap_terminal c.D (i - 1) (by rw [c.terminal]; omega), c.terminal]
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ i := Construction.Stream.ocTauPP_pos hΛ1
  have hc : ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2 = c.D.cellScaleSq i := by
    rw [CycleReference.ocEll_sq_eq hκM]; unfold OCData.cellScaleSq OCData.eps; rw [hkap]
  have hM1 : 1 ≤ i := by omega
  refine ⟨?_, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · show c.D.kap i / c.D.kap (i - 1) = c.D.κ c.M / c.D.κ c.M
    rw [hkap, hkap1]
  · funext X' a b
    have hG : (weakCapData c i k hk).G t X' a b = (familyLiftData (Dm := c.Dm) c.D i k
        (nativeChain i k) (c.D.eps (i - 1))
        ((c.stage i).fam.fiber ⟨k, hk⟩ ((c.stage i).actual ⟨k, hk⟩))).G t X' a b := rfl
    rw [hG, native_familyLiftData_metric c.D i hM1 k _ _ t X']
    show _ = ocMaterialMetric c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2 * t)
      (ocEpsilon c.D.q c.D.Λ (i - 1) • X') a b
    unfold ocMaterialMetric ocChart OCData.flowOf OCData.slotAnchor
    rw [hc, ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ i k hτ'']
    rfl
  · funext z
    show ocPulseCellDrift c.D.α c.D.q c.D.Λ c.D.ζ i (c.D.kap i) k t z = _
    rw [hkap]
    rfl
  · intro ε Φ j
    have hout : c.D.cellScaleSq i * t ∈ ((c.stage i).fam.piece ⟨k, hk⟩).output := by
      rw [weakStage_output_eq c i hi hit]; exact ht
    show sourceFlux (restrictEdges c.order_ge (liftEdges (c.D.cellScaleSq i)
        (c.D.eps (i - 1) / c.D.eps (i - 1)) ((c.stage i).fam.fiber ⟨k, hk⟩
          ((c.stage i).actual ⟨k, hk⟩)))) _ ε t Φ j =
      sourceFlux (liftEdges (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) _
        ((weakWindowFamily c i hi hit).fiber (oddSlotOf k) ())) _ ε t Φ j
    rw [oddSlotOf_of_odd hk, hc]
    funext X' z v
    unfold sourceFlux
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [restrictEdges, capOrder, liftEdges, ChartedFamily.fiber, List.map_map]
    refine EntryTerminal.Ingredients.Recon.Seq.seq_listSum_filterMap_congr _ _ _ _ _ fun γ _ => ?_
    by_cases hd : d.1 ≤ ((c.stage i).fam.identity v u γ).maxOrder
    · simp [weakWindowFamily, weakWindowStage, GenStage.recap, GenStage.actualFamily, CoefficientIdentity.recap, OCData.eps, hd, hout]
    · simp [weakWindowFamily, weakWindowStage, GenStage.recap, GenStage.actualFamily, CoefficientIdentity.recap, OCData.eps, hd]

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Window

/-! **The lifted comparison of a weak passage from the output of the physical lift**
(the conversion).

At a passage `M < i ≤ M + J_w`, the physical lift of the weak window
(`ReconPhysicalLiftStatement` at the data of `WeakWindow`) returns a family `û` at the slots
`weakWindowSlots c i k₀` whose value is the glued lift of the window, a solution of the coupled
system of the window's family with the residual `(R_res, q_res)`, and the two mass bounds of the
residual at a radius `r_s` with a bound `X_b`. The four lemmas turn these into the conjuncts of
`WeakLiftedComparisonStatement` at the instance, for

* `uΛ`, `wΛ`, `YΛ`: the truncations of `û`, `ŵ` to the orders `0`, `1`, `J_wN_w`;
* `F = weakLiftedF` and `g = weakLiftedG`: `−R_res`, `−q_res` truncated to the plan's forcing
  order (`k₀` above it).

* `weakLifted_value`: the value of `uΛ` is the glued weak lift of the readout
  (`weakWindow_gluedLift_eq`).
* `weakLifted_errSol`: `WeakErrSol` with the initial value `U(t_i)` and the forcing `−(F, g)`
  (`weakErrSol_of_coupled_eq`), given that `û(t_i)` truncates to the incoming value.
* `weakLifted_cost`: `F`, `g` are measurable in time and their forcing cost is at most
  `2 L^{K_max} X_b`, for `L ≥ 1` with `plan.radius R · ε_i ≤ L r_s` (truncation and change of
  radius: `convMass_flux`, `convMass_scalar`; then `weakComparisonForcingCost_le_of_mass`).
* The lift relation `trunc wΛ = uΛ` is the third clause of `WeakErrSol`.

The statements are on the window `[t_i, a + T₀]`; the window's `t_p + T_obs` is rewritten once at
the use. The lemmas are separate to keep each elaboration small: no proposition about these
Sobolev families is rewritten here, and `weakErrSol_of_coupled_eq` substitutes before the system
is specialized.

The application of `ReconPhysicalLiftStatement` to the window with
the inputs of the coarse side, the initial value `û(t_i)`, and the price
`2 L^{K_max} X_b ≤ forceC · ε_M^{P} · Φ` are handled separately.

The degenerate cases are included: `R_res = 0`, `q_res = 0`, `X_b = 0` give `F = g = 0` and the
homogeneous system; `L = 1` is `plan.radius R · ε_i ≤ r_s`; at the root the stage has no identity
and `YΛ` is vacuous. -/

open WeakEntryProofs WeakEntryProofs.Assembly Residual

section Neg

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The factorial norm is even. -/
theorem factorialNormSq_torus_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (ρ : ℝ) (U : TorusHk K E) :
    factorialNormSq ρ (-U).val = factorialNormSq ρ U.val := by
  have h := CycleComparison.Coarse.sqrt_fNSq_torus_neg ρ U
  rw [← Real.sq_sqrt (factorialNormSq_nonneg ρ (-U).val),
    ← Real.sq_sqrt (factorialNormSq_nonneg ρ U.val), h]

/-- The flux mass bound of the negated family. -/
theorem fluxMassLe_neg {K : ι → ℕ} {ν ρ : ℝ} {π : ι → ℝ} {I : Set ℝ}
    {F : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v))} {Y : ℝ}
    (hF : FluxMassLe (ι := ι) (h := h) (K := K) ν ρ π I F Y) :
    FluxMassLe (ι := ι) (h := h) (K := K) ν ρ π I (fun v t => -F v t) Y := by
  refine ⟨fun v => (hF.1 v).neg, ?_⟩
  have e : ∀ s, massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) ρ π
      (fun v => (-F v s).val) =
      massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) ρ π
        (fun v => (F v s).val) := fun s => by
    unfold massNormSq
    exact Finset.sum_congr rfl fun v _ => by rw [factorialNormSq_torus_neg]
  simp only [e]
  exact hF.2

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The scalar mass bound of the negated family. -/
theorem scalarMassLe_neg {K : ι → ℕ} {ρ : ℝ} {π : ι → ℝ} {I : Set ℝ}
    {q : ∀ v, ℝ → TorusHk (K v) (h v)} {Y : ℝ}
    (hq : ScalarMassLe (ι := ι) (h := h) (K := K) ρ π I q Y) :
    ScalarMassLe (ι := ι) (h := h) (K := K) ρ π I (fun v t => -q v t) Y := by
  refine ⟨fun v => (hq.1 v).neg, ?_⟩
  have e : ∀ s, massNormSq (E := h) (K := K) ρ π (fun v => (-q v s).val) =
      massNormSq (E := h) (K := K) ρ π (fun v => (q v s).val) := fun s => by
    unfold massNormSq
    exact Finset.sum_congr rfl fun v _ => by rw [factorialNormSq_torus_neg]
  simp only [e]
  exact hq.2

end Neg

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The forcing order of the plan is below every slot, for `k₀` above it. -/
theorem weakWindow_forcing_le (c : WeakPassageInstance plan R) (i k₀ : ℕ)
    (hk₀f : plan.forcingOrder R ≤ k₀) (v : CompIn (c.stage i).comps) :
    plan.forcingOrder R ≤ weakWindowSlots c i k₀ v :=
  hk₀f.trans (weakWindowSlots_ge c i k₀ v)

/-- **The flux forcing**: minus the residual flux, truncated to the forcing order. -/
def weakLiftedF (c : WeakPassageInstance plan R) (i k₀ : ℕ) (hk₀f : plan.forcingOrder R ≤ k₀)
    (Rres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) :=
  fun v t => -truncateTorusHk (weakWindow_forcing_le c i k₀ hk₀f v) (Rres v t)

/-- **The scalar forcing**: minus the residual scalar, truncated to the forcing order. -/
def weakLiftedG (c : WeakPassageInstance plan R) (i k₀ : ℕ) (hk₀f : plan.forcingOrder R ≤ k₀)
    (qres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root)) :
    ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root) :=
  fun v t => -truncateTorusHk (weakWindow_forcing_le c i k₀ hk₀f v) (qres v t)

theorem weakNegTruncF_weakLiftedF (c : WeakPassageInstance plan R) (i k₀ : ℕ)
    (hk₀f : plan.forcingOrder R ≤ k₀)
    (Rres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (v : CompIn (c.stage i).comps) (t : ℝ) :
    truncateTorusHk (Nat.zero_le _) (Rres v t) =
      weakNegTruncF c i (weakLiftedF c i k₀ hk₀f Rres) v t := by
  have h1 : truncateTorusHk (Nat.zero_le (plan.forcingOrder R))
      (-truncateTorusHk (weakWindow_forcing_le c i k₀ hk₀f v) (Rres v t)) =
      -truncateTorusHk (Nat.zero_le (plan.forcingOrder R))
        (truncateTorusHk (weakWindow_forcing_le c i k₀ hk₀f v) (Rres v t)) :=
    ContinuousLinearMap.map_neg _ _
  show _ = -truncateTorusHk (Nat.zero_le (plan.forcingOrder R))
    (-truncateTorusHk (weakWindow_forcing_le c i k₀ hk₀f v) (Rres v t))
  rw [h1, neg_neg]
  rfl

theorem weakNegTruncG_weakLiftedG (c : WeakPassageInstance plan R) (i k₀ : ℕ)
    (hk₀f : plan.forcingOrder R ≤ k₀)
    (qres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root))
    (v : CompIn (c.stage i).comps) (t : ℝ) :
    truncateTorusHk (Nat.zero_le _) (qres v t) =
      weakNegTruncG c i (weakLiftedG c i k₀ hk₀f qres) v t := by
  have h1 : truncateTorusHk (Nat.zero_le (plan.forcingOrder R))
      (-truncateTorusHk (weakWindow_forcing_le c i k₀ hk₀f v) (qres v t)) =
      -truncateTorusHk (Nat.zero_le (plan.forcingOrder R))
        (truncateTorusHk (weakWindow_forcing_le c i k₀ hk₀f v) (qres v t)) :=
    ContinuousLinearMap.map_neg _ _
  show _ = -truncateTorusHk (Nat.zero_le (plan.forcingOrder R))
    (-truncateTorusHk (weakWindow_forcing_le c i k₀ hk₀f v) (qres v t))
  rw [h1, neg_neg]
  rfl

/-- **The value**: the truncation of the window's family is the glued weak lift of the
readout. -/
theorem weakLifted_value (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (k₀ : ℕ)
    (hΛ : 1 ≤ c.D.Λ) (hκ : 0 < c.D.κ c.M)
    (hw : ∀ (p : OddSlot) (s : ℝ),
      (c.stage i).fam.weight p s = ocCutoff c.D.α c.D.q c.D.Λ i p.1 s)
    (û : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root))
    (hval : ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v,
      (û v t).toFunction.jet (valueIndex2 (weakWindowSlots c i k₀ v))
        =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => gluedLift (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀))
          (fun k => (weakWindowFamily c i hi hit).weight (oddSlotOf k))
          (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) (ocEpsilon c.D.q c.D.Λ (i - 1))
          (ocEpsilon c.D.q c.D.Λ i)
          (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
          A.Nw (A.Jw * A.Rw) (h.CcR i)
          (fun k => ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
          (fun k => ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
          (fun s y w' => weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU s) w' y)
          t x v)
    (v : CompIn (c.stage i).comps) (t : ℝ) (ht : t ∈ Set.Icc (r.tq i) (r.a + A.T₀)) :
    (truncateTorusHk (Nat.zero_le (weakWindowSlots c i k₀ v)) (û v t)).toFunction.jet
        (valueIndex2 0) =ᵐ[volume.restrict unitCube]
      fun x => weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) (h.CcR i) t
        (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t)) v x := by
  filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae
    (Nat.zero_le (weakWindowSlots c i k₀ v)) (û v t) (valueIndex2 0), hval t ht v] with x h1 h2
  rw [h1]
  refine h2.trans ?_
  exact weakWindow_gluedLift_eq c i hi hit (h.CcR i)
    (fun s => weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU s)) x hΛ hκ hw ht v

/-- **The cost**: the forcing cost of the truncated residual, after truncation and a change of
radius. -/
theorem weakLifted_cost (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i k₀ : ℕ)
    (hk₀f : plan.forcingOrder R ≤ k₀) (hΛ : 1 ≤ c.D.Λ) (hκ : 0 < c.D.κ c.M)
    (hπ : ∀ v : CompIn (c.stage i).comps, 0 < weakMass c.D A.Nw A.Jw A.η₀ v.1)
    {rs L Xb : ℝ} (hL : 1 ≤ L) (hrad : plan.radius R * c.D.eps i ≤ L * rs) (hXb : 0 ≤ Xb)
    {Kmax : ℕ} (hKmax : ∀ v, weakWindowSlots c i k₀ v ≤ Kmax)
    (Rres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (qres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root))
    (hRm : ∀ v, MemLp (Rres v) 2 (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))))
    (hqi : ∀ v, Integrable (qres v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))))
    (hRb : (c.D.κ c.M)⁻¹ * ∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
        massNormSq (E := fun v : CompIn (c.stage i).comps =>
            PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
          (K := weakWindowSlots c i k₀) rs (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Rres v s).val) ≤ Xb ^ 2)
    (hqb : ∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
        Real.sqrt (massNormSq (E := fun v : CompIn (c.stage i).comps => ScalarH v.1.root)
          (K := weakWindowSlots c i k₀) rs (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (qres v s).val)) ≤ Xb) :
    (∀ v, AEStronglyMeasurable (weakLiftedF c i k₀ hk₀f Rres v)
      (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
    (∀ v, AEStronglyMeasurable (weakLiftedG c i k₀ hk₀f qres v)
      (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
    weakComparisonForcingCost r i (weakLiftedF c i k₀ hk₀f Rres) (weakLiftedG c i k₀ hk₀f qres) ≤
      ENNReal.ofReal (L ^ Kmax * Xb + L ^ Kmax * Xb) := by
  have hε : 0 ≤ plan.radius R * c.D.eps i :=
    mul_nonneg (plan.radius_pos R).le (Construction.Stream.ocEpsilon_pos hΛ).le
  have hF := fluxMassLe_neg (EntryTerminal.Ingredients.Recon.convMass_flux
    (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root) (c.D.κ c.M)
    (plan.radius R * c.D.eps i) rs L hκ hε hL hrad (weakWindowSlots c i k₀)
    (plan.forcingOrder R) Kmax (weakWindow_forcing_le c i k₀ hk₀f) hKmax
    (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) hπ (r.tq i) (r.a + A.T₀) Rres Xb hXb hRm hRb)
  have hg := scalarMassLe_neg (EntryTerminal.Ingredients.Recon.convMass_scalar
    (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
    (plan.radius R * c.D.eps i) rs L hε hL hrad (weakWindowSlots c i k₀)
    (plan.forcingOrder R) Kmax (weakWindow_forcing_le c i k₀ hk₀f) hKmax
    (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) hπ (r.tq i) (r.a + A.T₀) qres Xb hqi hqb)
  have hF1 := hF.1
  have hg1 := hg.1
  beta_reduce at hF1 hg1
  exact ⟨fun v => (hF1 v).aestronglyMeasurable, fun v => (hg1 v).aestronglyMeasurable,
    weakComparisonForcingCost_le_of_mass r i hκ hπ _ _ hF hg⟩

/-- **The system**: the truncations solve the system of the comparison error with the initial
value `U(t_i)` and the forcing `−(F, g)`. -/
theorem weakLifted_errSol (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (k₀ : ℕ)
    (hk₀J : A.Jw * A.Nw ≤ k₀ + 1) (hk₀f : plan.forcingOrder R ≤ k₀)
    {û : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root)}
    {ŵ : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v + 1) (ScalarH v.1.root)}
    {Rres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {qres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root)}
    (hsol : IsCoupledWeakSolutionTorus (c.D.κ c.M) (r.tq i) (r.a + A.T₀)
      (streamVel (c.D.Φ i)) (1 + A.Jw * A.Nw) (weakWindowSlots c i k₀)
      (edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i)
        (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ()) (weakWindowSlots c i k₀))
      (fun v => û v (r.tq i)) Rres qres û ŵ)
    (hinit : ∀ v, truncateTorusHk (Nat.zero_le _) (û v (r.tq i)) = weakIncomingInit r i v) :
    WeakErrSol c r i (weakIncomingInit r i) (weakNegTruncF c i (weakLiftedF c i k₀ hk₀f Rres))
      (weakNegTruncG c i (weakLiftedG c i k₀ hk₀f qres))
      (fun v t => truncateTorusHk (Nat.zero_le _) (û v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (ŵ v t))
      (fun _ u' _ t => truncateTorusHk (weakWindow_lift_le c i k₀ hk₀J u') (ŵ u' t)) :=
  weakErrSol_of_coupled_eq c r i hi hit k₀ hk₀J hsol hinit
    (weakNegTruncF_weakLiftedF c i k₀ hk₀f Rres) (weakNegTruncG_weakLiftedG c i k₀ hk₀f qres)

end AVRegularity.Providers.WeakGen.Window
end
