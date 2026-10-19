-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.WeakStageSampledReferenceField
import AVRegularity.CycleJoint.PlaneImageJetMomentNorm

section
section
/-! Equal stored geometries give equal moving zero-child references across actual charts. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw : ℝ} {j₀ level minBase cap : ℕ}

theorem weakStageZeroChildReference_geometry_congr (hΛ : 1 ≤ D.Λ)
    (c c' : WeakStageProductionContext D bw j₀ level minBase cap)
    (hslot : c.slot = c'.slot)
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (slot : ℤ) (t : ℝ) (z X : Vec 2) :
    (actualIndependentCoarseParameterChain D (weakZeroChildAnchor c.chain.1 slot)
      (weakZeroChildParameterPacking c.chain.1 slot
        (independentFreshCoarseAppendPacking c.chain.1.children.length D level c.slot.1 slot
          (D.eps level / D.eps (level - 1)) t
          (z, independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P)))).geom D =
    (actualIndependentCoarseParameterChain D (weakZeroChildAnchor c'.chain.1 slot)
      (weakZeroChildParameterPacking c'.chain.1 slot
        (independentFreshCoarseAppendPacking c'.chain.1.children.length D level c'.slot.1 slot
          (D.eps level / D.eps (level - 1)) t
          (z, independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q)))).geom D := by
  rw [actualZeroChildParameterChain_eq_reference D c.chain.1 c.chain.2.2.2.1,
    actualZeroChildParameterChain_eq_reference D c'.chain.1 c'.chain.2.2.2.1]
  have hctx : c.chain.1.ctxLevel = level := c.chain.2.1
  have hctx' : c'.chain.1.ctxLevel = level := c'.chain.2.1
  have hs : c.chain.1.slot = c.slot.1 := c.chain.2.2.2.2.1
  have hs' : c'.chain.1.slot = c'.slot.1 := c'.chain.2.2.2.2.1
  have hg := weakZeroChildReferenceFamily_append_geometry D c.chain.1 c.chain.2.2.2.1 slot
    (D.eps (level - 1)) (Construction.Stream.ocEpsilon_pos hΛ).ne' (by rw [hctx]) t z
    (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P)
  have hg' := weakZeroChildReferenceFamily_append_geometry D c'.chain.1 c'.chain.2.2.2.1 slot
    (D.eps (level - 1)) (Construction.Stream.ocEpsilon_pos hΛ).ne' (by rw [hctx']) t z
    (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q)
  simp only [hctx, hs, independentIntrinsicParameterPacking_stored,
    independentIntrinsicParameterPacking_slow] at hg
  simp only [hctx', hs', independentIntrinsicParameterPacking_stored,
    independentIntrinsicParameterPacking_slow] at hg'
  rw [hg, hg']
  apply weak_appendChild_recenter_reference_geometry_congr D _ _
    (actualIndependentCoarseParameterChain_wellSlotted D c.chain.1 c.chain.2.2.2.1 P)
    (actualIndependentCoarseParameterChain_wellSlotted D c'.chain.1 c'.chain.2.2.2.1 Q) _ _ hgeom
    (D.eps (level - 1)) (Construction.Stream.ocEpsilon_pos hΛ).ne' slot t z X X rfl
  · rw [actualIndependentCoarseParameterChain_ctxLevel, actualIndependentCoarseParameterChain_ctxLevel,
      hctx, hctx']
  · rw [actualIndependentCoarseParameterChain_slot, actualIndependentCoarseParameterChain_slot,
      hs, hs', hslot]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual produced arrays read their native source at every admissible moving child reference. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.sampled_reference_native
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) (hd : 2 ≤ d) (hdn : d ≤ n)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (t : ℝ) (z : Vec 2)
    (hA : IsAdmissibleChain D bw j₀ (level + 1) slot.1 (weakStageAppendedNativeChain c Y slot.1 t z))
    (hell : |D.eps level / D.eps (level - 1)| ≤ 1)
    (hc : ∀ j, ‖independentFreshChildProjection j false
      (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)‖ ≤ 3 / 16)
    (hY : ‖independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y‖ ≤ 1 / 8)
    (hδ : ‖D.relDisp level c.slot.1 (D.slotAnchor (level + 1) slot.1) t z‖ ≤ 1 / 16)
    (tt : ℝ) (ht : (D.cellScaleSq fine)⁻¹ * tt ∈ weakStageMeanClockWindow D fine slot.1)
    (zz : Vec 2) :
    let cf := c.zeroChild (by omega : 1 ≤ D.Λ) hbw slot hs
    let cn := c.appendNative Y slot t z hA
    M.field (cf.relevel he) d word tt zz (independentIntrinsicParameterPacking (4 * cf.chain.1.children.length) 0
      (weakZeroChildParameterPacking c.chain.1 slot.1
        (independentFreshCoarseAppendPacking c.chain.1.children.length D level c.slot.1 slot.1
          (D.eps level / D.eps (level - 1)) t (z, Y)))) =
      native slot (cn.relevel he).chain d word tt := by
  have hg := weakStageSampled_reference_field hq hΛ hbw hbw₁
    (fun cc => M.field (cc.relevel he) d word) (by
      intro ca cb hslot hdepth P Q hP hQ hgeom t z
      exact M.geometry (ca.relevel he) (cb.relevel he) hslot hdepth d word P Q hP hQ hgeom
        0 (by simp only [norm_zero]; norm_num) t z)
    c slot hs Y t z hA hell hc hY hδ tt zz
  exact hg.trans (M.native_copy ((c.appendNative Y slot t z hA).relevel he) d word hd hdn tt ht zz)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual produced arrays read their native source at every admissible moving child reference. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

def IndependentWeakMeanArrayProduction.referenceField
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hbw : 0 < bw)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (d : ℕ) (word : DerivativeWord2 (d - 1))
    (t : ℝ) (z : Vec 2) (W : Vec (2 + 4 * (c.chain.1.children.length + 1))) : Vec 2 :=
  let cf := (c.zeroChild hΛ hbw slot hs).relevel he
  M.field cf d word t z
    (Eq.rec (motive := fun r _ => Vec (2 + 4 * r)) W
      (show c.chain.1.children.length + 1 = cf.chain.1.children.length by
        simp only [cf, WeakStageProductionContext.relevel, WeakStageProductionContext.zeroChild,
          weakZeroChildAnchor, List.length_append, List.length_singleton]))

theorem IndependentWeakMeanArrayProduction.referenceField_native
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) (hd : 2 ≤ d) (hdn : d ≤ n)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (Y : Vec (2 + 4 * c.chain.1.children.length)) (t : ℝ) (z : Vec 2)
    (hA : IsAdmissibleChain D bw j₀ (level + 1) slot.1 (weakStageAppendedNativeChain c Y slot.1 t z))
    (hell : |D.eps level / D.eps (level - 1)| ≤ 1)
    (hc : ∀ j, ‖independentFreshChildProjection j false
      (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)‖ ≤ 3 / 16)
    (hY : ‖independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y‖ ≤ 1 / 8)
    (hδ : ‖D.relDisp level c.slot.1 (D.slotAnchor (level + 1) slot.1) t z‖ ≤ 1 / 16)
    (tt : ℝ) (ht : (D.cellScaleSq fine)⁻¹ * tt ∈ weakStageMeanClockWindow D fine slot.1)
    (zz : Vec 2) :
    let cn := c.appendNative Y slot t z hA
    M.referenceField he (by omega) hbw c slot hs d word tt zz
      (independentIntrinsicParameterPacking (4 * (c.chain.1.children.length + 1)) 0
        (independentFreshCoarseAppendPacking c.chain.1.children.length D level c.slot.1 slot.1
          (D.eps level / D.eps (level - 1)) t (z, Y))) =
      native slot (cn.relevel he).chain d word tt := by
  dsimp only [IndependentWeakMeanArrayProduction.referenceField]
  rw [independentIntrinsicParameterPacking_cast]
  exact M.sampled_reference_native he hq hΛ hbw hbw₁ d word hd hdn c slot hs Y t z hA hell hc hY hδ tt ht zz

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual zero-child input retains phase symmetry after the literal coordinate transport. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.referenceField_phase
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hbw : 0 < bw)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ∀ δ ∈ independentFreshPhaseTranslations (c.chain.1.children.length + 1),
      IndependentSourceTranslationInvariant δ (M.referenceField he hΛ hbw c slot hs d word) := by
  let cf := (c.zeroChild hΛ hbw slot hs).relevel he
  have hlen : cf.chain.1.children.length = c.chain.1.children.length + 1 := by
    simp only [cf, WeakStageProductionContext.relevel, WeakStageProductionContext.zeroChild,
      weakZeroChildAnchor, List.length_append, List.length_singleton]
  exact independentSource_phase_dimension_cast hlen (M.field cf d word) (M.phase cf d word)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual sampled mean input respects whole-ball reference geometry across parent charts. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.referenceField_geometry
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hbw : 0 < bw)
    (c c' : WeakStageProductionContext D bw j₀ level minBase cap)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (hs' : IsScheduledIn D level slot.1 c'.slot.1)
    (d : ℕ) (word : DerivativeWord2 (d - 1))
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8)
    (hell : |D.eps level / D.eps (level - 1)| ≤ 1)
    (t : ℝ) (z : Vec 2)
    (hδ : ‖D.relDisp level c.slot.1 (D.slotAnchor (level + 1) slot.1) t z‖ ≤ 1 / 16)
    (tt : ℝ) (zz : Vec 2) :
    M.referenceField he hΛ hbw c slot hs d word tt zz
      (independentIntrinsicParameterPacking (4 * (c.chain.1.children.length + 1)) 0
        (independentFreshCoarseAppendPacking c.chain.1.children.length D level c.slot.1 slot.1
          (D.eps level / D.eps (level - 1)) t
          (z, independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P))) =
    M.referenceField he hΛ hbw c' slot hs' d word tt zz
      (independentIntrinsicParameterPacking (4 * (c'.chain.1.children.length + 1)) 0
        (independentFreshCoarseAppendPacking c'.chain.1.children.length D level c'.slot.1 slot.1
          (D.eps level / D.eps (level - 1)) t
          (z, independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q))) := by
  dsimp only [IndependentWeakMeanArrayProduction.referenceField]
  rw [independentIntrinsicParameterPacking_cast, independentIntrinsicParameterPacking_cast]
  let cf := (c.zeroChild hΛ hbw slot hs).relevel he
  let cg := (c'.zeroChild hΛ hbw slot hs').relevel he
  refine M.geometry cf cg rfl ?_ d word _ _ ?_ ?_ ?_ 0 (by simp only [norm_zero]; norm_num) tt zz
  · change (weakZeroChildAnchor c.chain.1 slot.1).children.length =
      (weakZeroChildAnchor c'.chain.1 slot.1).children.length
    simp only [weakZeroChildAnchor, List.length_append, List.length_singleton, hdepth]
  · exact weakStageSampled_reference_center_bound c slot.1 _ hell _ t z
      (by simpa only [independentIntrinsicParameterPacking_stored] using hP)
      (by simpa only [independentIntrinsicParameterPacking_slow] using hX.le) hδ
  · apply weakStageSampled_reference_center_bound c' slot.1 _ hell _ t z
      (by simpa only [independentIntrinsicParameterPacking_stored] using hQ)
      (by simpa only [independentIntrinsicParameterPacking_slow] using hX.le)
    simpa only [hslot] using hδ
  · exact weakStageZeroChildReference_geometry_congr hΛ c c' hslot P Q hgeom slot.1 t z X

end AVRegularity.EntryWeakProofs
end
end

section
/-! One matrix jet price covers every stored-history depth in the weak menu. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

def weakStageTransferDepthPrice (N r : ℕ) : ℝ :=
  N.factorial * independentMovingTransferJetCost N
    (nativeMixedChartBudget (N + 2) r (1 / 2 + (0 + 2 * Real.pi))) 0 *
      independentFreshGeometryClampJetCost r N ^ N

def weakStageTransferJetMenu (J N : ℕ) : ℝ :=
  independentFiniteStepBudget (fun r : Fin (J + 1) => |weakStageTransferDepthPrice N r.val|)

theorem weakStageTransferJetMenu_one_le (J N : ℕ) : 1 ≤ weakStageTransferJetMenu J N :=
  independentFiniteStepBudget_one_le _ (fun _ => abs_nonneg _)

theorem weakStageTransferDepthPrice_le (J N r : ℕ) (hr : r ≤ J) :
    weakStageTransferDepthPrice N r ≤ weakStageTransferJetMenu J N :=
  (le_abs_self _).trans (independentFiniteStepBudget_entry_le
    (fun j : Fin (J + 1) => |weakStageTransferDepthPrice N j.val|)
    (fun _ => abs_nonneg _) ⟨r, Nat.lt_succ_of_le hr⟩)

theorem uniform_weak_stage_transfer_jet_menu (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J N : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.children.length ≤ J →
      ∀ bw j₀, 0 < bw → IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A →
      ∀ slot, Odd slot → IsScheduledIn D A.ctxLevel slot A.slot → ∀ t,
      ocCutoff D.α D.q D.Λ (A.ctxLevel + 1) slot t ≠ 0 →
      ∀ X : Vec 2 × Vec (2 + 4 * A.children.length), ∀ n ≤ N, ∀ a b : Fin 2,
      ‖iteratedFDeriv ℝ n (fun Z : (Vec 2 × Vec (2 + 4 * A.children.length)) × Vec 2 =>
        independentFreshClampedTransferMatrix A.children.length D
          (actualIndependentCoarseParameterChain D A) A.ctxLevel
          (D.eps (A.baseLevel + A.children.length)) slot t Z.1 (D.eps A.ctxLevel • Z.2) a b) (X, 0)‖ ≤
        weakStageTransferJetMenu J N := by
  obtain ⟨M, hM, hprod⟩ := uniform_actual_coarse_clamped_transfer_jets
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq A hbase hdepth bw j₀ hbw hA slot hslot hs t hcut X n hn a b
  exact (hprod D hDα hDq hDΛ hDζ hseq A hbase hdepth bw j₀ hbw hA slot hslot hs
    N t hcut X n hn a b).trans (weakStageTransferDepthPrice_le J N _ hdepth)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual produced source reserves bound every physical operator piece with one finite price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {Dm : ℕ} {bw B : ℝ} {j₀ minBase cap H : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem IndependentWeakStageFluxProduction.physical_piece_jet_le
    (S : IndependentWeakStageFluxProduction G' minBase cap H B)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : bw ≤ 1 / 10000) (hB : 0 ≤ B)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (Mtop : ℕ) (hG : G'.IsNatural Mtop) (hbase : minBase ≤ G'.level - 1)
    (K : ℕ) (hK : G'.maxOrderBound K) (Ks : ℕ) (hKs : Ks ≤ H)
    (C : ℝ) (hC : 1 ≤ C)
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (d : ℕ) (hd : 2 ≤ d)
    (hdn : d ≤ (G'.fam.identity v u γ).maxOrder) (t : ℝ) (p : OddSlot)
    (hFj : ∀ j, 1 ≤ j → j ≤ Ks + K + 1 → ∀ y,
      ‖iteratedFDeriv ℝ j (rescaledChart (D.eps G'.level) ⇑((G'.fam.piece p).material t)) y‖ ≤ C)
    (hGj : ∀ j, 1 ≤ j → j ≤ Ks + K + 1 → ∀ y,
      ‖iteratedFDeriv ℝ j (rescaledChart (D.eps G'.level) ⇑((G'.fam.piece p).material t).symm) y‖ ≤ C)
    (k : ℕ) (hk : k ≤ Ks) (x : Vec 2) :
    D.eps G'.level ^ k * ‖iteratedFDeriv ℝ k
      (weakPhysicalPieceCoefficient G'.fam (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
        G'.actual v u γ d t p) x‖ ≤
      (G'.fam.identity v u γ).record.size *
        (D.κ D.term * D.eps (G'.level + 1) ^ ((G'.fam.identity v u γ).maxOrder - 2) *
          D.eps G'.level ^ ((d : ℝ) - ((G'.fam.identity v u γ).maxOrder : ℝ))) *
      weakPhysicalPiolaMenuPrice Ks K (Ks + K) (positiveJetCompositionBudget (Ks + K) C)
        (Ks.factorial * B * C ^ Ks) := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hε : ∀ j, 0 < D.eps j := fun _ => Construction.Stream.ocEpsilon_pos hΛ₁
  have hκ : 0 ≤ D.κ D.term := by
    rw [← weakData_kap_terminal D D.term le_rfl]
    exact (weakData_kap_pos D hΛ₁ hζ hband D.term).le
  let Cmat := positiveJetCompositionBudget (Ks + K) C
  have hCmat : 1 ≤ Cmat := positiveJetCompositionBudget_ge_one _ _ hC
  let Bsource := Ks.factorial * B * C ^ Ks
  have hBs : 0 ≤ Bsource := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (pow_nonneg (zero_le_one.trans hC) _)
  have hdim : 0 ≤ (G'.fam.identity v u γ).record.size *
      (D.κ D.term * D.eps (G'.level + 1) ^ ((G'.fam.identity v u γ).maxOrder - 2) *
        D.eps G'.level ^ ((d : ℝ) - ((G'.fam.identity v u γ).maxOrder : ℝ))) :=
    mul_nonneg (G'.fam.identity v u γ).record.size_nonneg
      (mul_nonneg (mul_nonneg hκ (pow_nonneg (hε _).le _)) (Real.rpow_pos_of_pos (hε _) _).le)
  rw [weakStagePhysicalPiece_eq_array G' v u γ d hd t p]
  refine (weak_physical_piola_jet_bound _
    (CycleJointProofs.chartInvJacobian_homeomorph_smooth ((G'.fam.piece p).material t)
      ((G'.fam.piece p).material_smooth t) ((G'.fam.piece p).material_symm_smooth t))
    Ks K (Ks + K) (G'.fam.identity v u γ).maxOrder d k (hK v u γ) hd hdn hk le_rfl
    Cmat Bsource (G'.fam.identity v u γ).record.size (D.κ D.term) (D.eps (G'.level + 1)) (D.eps G'.level)
    hCmat hBs (G'.fam.identity v u γ).record.size_nonneg hκ (hε _).le (hε _) ?_
    (weakStagePhysicalSourceArray G' v u γ t p) ?_ ?_ (G'.fam.identity v u γ).map
    (weakPassage_identity_map_norm_le_one P Mn rW Din G G' hp v u γ) x).trans ?_
  · intro a b j hj y
    exact physical_chart_inverse_jacobian_scaled_jets ((G'.fam.piece p).material t)
      ((G'.fam.piece p).material_smooth t) ((G'.fam.piece p).material_symm_smooth t)
      (D.eps G'.level) (hε _) (Ks + K) C hC hFj
      (fun j hj hjN => hGj j hj (by omega)) a b j hj y
  · intro a I i
    exact contDiff_pi.mp ((S.physical_source_array_contDiff hq hΛ hζ hband hbw hB P Mn rW Din hp ht
      Mtop hG hbase v u γ t p a I).of_le (by exact_mod_cast hk.trans hKs)) i
  · intro a ha I i j hj y
    exact S.physical_source_array_jet_le hq hΛ hζ hband hbw hB P Mn rW Din hp ht Mtop hG hbase
      v u γ t p Ks hKs C hC (fun j hj hjK => hGj j hj (by omega)) a
      (Finset.mem_Icc.mpr ⟨hd.trans (Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp ha).2⟩)
      I j (hj.trans hk) i y
  · exact mul_le_mul_of_nonneg_left (weakPhysicalPiolaPrice_le_menu Ks K (Ks + K) _ d Cmat Bsource
      (zero_le_one.trans hCmat) hBs (hK v u γ) (hdn.trans (hK v u γ))) hdim

end AVRegularity.EntryWeakProofs
end
end

section
/-! On active cutoffs, produced sampled fields read the original native child source. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.sampledField_native
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hbw : 0 < bw) (hbw₁ : bw ≤ 1 / 10000)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (Y : Vec (2 + 4 * c.chain.1.children.length))
    (hY : Y ∈ actualIndependentCoarseProductionCarrier D c.chain.1 bw (D.eps (level - 1))
      j₀ level c.slot.1)
    (t : ℝ) (ht : t ∈ weakStageCutoffWindow D fine slot.1) (z : Vec 2)
    (hA : IsAdmissibleChain D bw j₀ (level + 1) slot.1 (weakStageAppendedNativeChain c Y slot.1 t z))
    (hell : |D.eps level / D.eps (level - 1)| ≤ 1)
    (hδ : ‖D.relDisp level c.slot.1 (D.slotAnchor (level + 1) slot.1) t z‖ ≤ 1 / 16)
    (d : ℕ) (hd : 2 ≤ d) (word : DerivativeWord2 (d - 1)) :
    actualWeakSampledPiolaField D c.chain.1 (D.eps (level - 1)) (D.eps level / D.eps (level - 1))
      slot.1 (weakStageCutoffWindow D fine slot.1) n
      (M.referenceField he (by omega) hbw c slot hs) d word t z Y =
    transportedCoeff
      (fun w => (childTransition D slot.1 t
        (((actualIndependentCoarseParameterChain D c.chain.1
          (independentStoredParameterProjection (4 * c.chain.1.children.length) Y)).recenter D
          (D.eps (level - 1) • independentIntrinsicSlowProjection (4 * c.chain.1.children.length) Y)).recenter D w)
        (z + (D.eps level)⁻¹ • w))⁻¹) n
      (fun e β => native slot ((c.appendNative Y slot t z hA).relevel he).chain e β t) (d - 1) word 0 := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hctx : c.chain.1.ctxLevel = level := c.chain.2.1
  have hslot : c.chain.1.slot = c.slot.1 := c.chain.2.2.2.2.1
  apply actualWeakSampledPiolaField_native_copy D c.chain.1 _ _ slot.1 _ n
    (M.referenceField he hΛ₁ hbw c slot hs) d word t ht z Y
  · funext w
    have hm := independentFreshClampedTransferMatrix_native c.chain.1.children.length D hΛ₁
      (actualIndependentCoarseParameterChain D c.chain.1) c.chain.1.ctxLevel
      (D.eps (level - 1)) slot.1 t (z, Y) hY.1.1.2 w
    simpa only [hctx] using hm
  · intro e he' β
    have he₁ : 2 ≤ e := by have := (Finset.mem_Icc.mp he').1; omega
    have he₂ : e ≤ n := (Finset.mem_Icc.mp he').2
    have hc j := (actualIndependentCoarseStoredCarrier_center_bound D hq hΛ c.chain.1 bw hbw₁
      _ hY.1.1.1 j).trans (by norm_num : (1 / 8 : ℝ) ≤ 3 / 16)
    have hm := M.referenceField_native he hq hΛ hbw hbw₁ e β he₁ he₂ c slot hs Y t z hA hell
      hc hY.2.le hδ t (weakStageCutoffWindow_clock D hΛ₁ hζ hband fine slot.1 t ht) 0
    funext a
    unfold actualWeakSampledPiolaArray independentTimeWindowSource independentFreshCoarseAppendedSource
    dsimp only
    rw [ite_eq_left ht, hctx, hslot]
    exact congrFun hm a

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual sampled mean input respects whole-ball reference geometry across parent charts. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.sampledField_geometry
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hbw : 0 < bw)
    (c c' : WeakStageProductionContext D bw j₀ level minBase cap)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (hs' : IsScheduledIn D level slot.1 c'.slot.1)
    (d : ℕ) (word : DerivativeWord2 (d - 1))
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8)
    (hell : |D.eps level / D.eps (level - 1)| ≤ 1)
    (I : Set ℝ) (t : ℝ) (z : Vec 2)
    (hδ : t ∈ I → ‖D.relDisp level c.slot.1 (D.slotAnchor (level + 1) slot.1) t z‖ ≤ 1 / 16) :
    actualWeakSampledPiolaField D c.chain.1 (D.eps (level - 1)) (D.eps level / D.eps (level - 1))
      slot.1 I n (M.referenceField he hΛ hbw c slot hs) d word t z
      (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
    actualWeakSampledPiolaField D c'.chain.1 (D.eps (level - 1)) (D.eps level / D.eps (level - 1))
      slot.1 I n (M.referenceField he hΛ hbw c' slot hs') d word t z
      (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q) := by
  classical
  let Y := independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P
  let Z := independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q
  have hcctx : c.chain.1.ctxLevel = level := c.chain.2.1
  have hdctx : c'.chain.1.ctxLevel = level := c'.chain.2.1
  have hcslot : c.chain.1.slot = c.slot.1 := c.chain.2.2.2.2.1
  have hdslot : c'.chain.1.slot = c'.slot.1 := c'.chain.2.2.2.2.1
  by_cases ht : t ∈ I
  · have hB e β :
        actualWeakSampledPiolaArray D c.chain.1 (D.eps level / D.eps (level - 1)) slot.1 I
          (M.referenceField he hΛ hbw c slot hs) e β t z Y =
        actualWeakSampledPiolaArray D c'.chain.1 (D.eps level / D.eps (level - 1)) slot.1 I
          (M.referenceField he hΛ hbw c' slot hs') e β t z Z := by
      have hm := M.referenceField_geometry he hΛ hbw c c' hslot hdepth slot hs hs' e β
        P Q hP hQ hgeom X hX hell t z (hδ ht) t 0
      funext a
      unfold actualWeakSampledPiolaArray independentTimeWindowSource independentFreshCoarseAppendedSource
      dsimp only
      rw [ite_eq_left ht, ite_eq_left ht, hcctx, hdctx, hcslot, hdslot]
      exact congrFun hm a
    have hK :
        (fun w => independentFreshClampedTransferMatrix c.chain.1.children.length D
          (actualIndependentCoarseParameterChain D c.chain.1) c.chain.1.ctxLevel
          (D.eps (level - 1)) slot.1 t (z, Y) w) =
        (fun w => independentFreshClampedTransferMatrix c'.chain.1.children.length D
          (actualIndependentCoarseParameterChain D c'.chain.1) c'.chain.1.ctxLevel
          (D.eps (level - 1)) slot.1 t (z, Z) w) := by
      funext w
      exact actualWeakClampedTransfer_reference_geometry hΛ hζ c c' hslot hdepth _
        P Q hP hQ hgeom X hX slot.1 t z w
    have heB :
        (fun e β => actualWeakSampledPiolaArray D c.chain.1 (D.eps level / D.eps (level - 1))
          slot.1 I (M.referenceField he hΛ hbw c slot hs) e β t z Y) =
        (fun e β => actualWeakSampledPiolaArray D c'.chain.1 (D.eps level / D.eps (level - 1))
          slot.1 I (M.referenceField he hΛ hbw c' slot hs') e β t z Z) :=
      funext fun e => funext fun β => hB e β
    funext a
    change (if t ∈ I then _ else 0) = (if t ∈ I then _ else 0)
    rw [ite_eq_left ht, ite_eq_left ht]
    dsimp only
    rw [hK, heB]
  · funext a
    change (if t ∈ I then _ else 0) = (if t ∈ I then _ else 0)
    rw [ite_eq_right ht, ite_eq_right ht]

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Actual coherent inherited families supply scheduled Piola data at every parent chart. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory Set AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H N n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.sampled_field_production
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hbw : 0 < bw)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (slot : OddSlot) (hs : IsScheduledIn D level slot.1 c.slot.1)
    (ρ ell : ℝ) (hell : |ell| ≤ 1) (hscale : D.eps c.chain.1.ctxLevel = ρ * ell)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hsmall : ∀ t ∈ I, |D.slotAnchor (c.chain.1.ctxLevel + 1) slot.1 - t| *
      ocA D.α D.q D.Λ c.chain.1.ctxLevel ≤ 1)
    (C : ℝ) (hKC : ∀ t ∈ I, ∀ X : Vec 2 × Vec (2 + 4 * c.chain.1.children.length),
      ∀ a b j, j ≤ N → ‖iteratedFDeriv ℝ j
        (fun Z : (Vec 2 × Vec (2 + 4 * c.chain.1.children.length)) × Vec 2 =>
          independentFreshClampedTransferMatrix c.chain.1.children.length D
            (actualIndependentCoarseParameterChain D c.chain.1) c.chain.1.ctxLevel ρ slot.1 t Z.1
            (D.eps c.chain.1.ctxLevel • Z.2) a b) (X, 0)‖ ≤ C)
    (hκ : 0 ≤ D.κ D.term) (hC : 0 ≤ C) (hHN : H + n ≤ N)
    (d : ℕ) (hd : 1 ≤ d) (word : DerivativeWord2 (d - 1)) :
    ∃ Q : IndependentParameterSourceReserve H
      (actualWeakSampledPiolaField D c.chain.1 ρ ell slot.1 I n
        (M.referenceField he hΛ hbw c slot hs) d word),
      ∀ k ≤ H, Q.budget k ≤ θ *
        (D.κ D.term * D.eps fine ^ (n - 2) * D.eps level ^ ((d : ℝ) - (n : ℝ))) *
        (2 * ∑ j : Fin (H + 1), independentPiolaDimensionlessPrice N n j.val C
          (H.factorial * B * (1 + (2 * Real.pi) ^ (H + 1)) ^ H) (d - 1)) := by
  obtain ⟨T, hw, hTm, hTa⟩ := M.sampled_piola hθ hB he hΛ hζ hbw c slot hs
    ρ ell hell hscale I hI hsmall C hKC hκ
  have hctx : c.chain.1.ctxLevel = level := c.chain.2.1
  have hslot : c.chain.1.slot = c.slot.1 := c.chain.2.2.2.2.1
  have hTm' : T.matrix = fun t z Y w => independentFreshClampedTransferMatrix c.chain.1.children.length D
      (actualIndependentCoarseParameterChain D c.chain.1) c.chain.1.ctxLevel ρ slot.1 t (z, Y) w := by
    simpa only [hctx] using hTm
  have hTa' : T.array = actualWeakSampledPiolaArray D c.chain.1 ell slot.1 I
      (M.referenceField he hΛ hbw c slot hs) := by
    rw [hTa]
    funext d word t z Y a
    unfold actualWeakSampledPiolaArray IndependentWeakMeanArrayProduction.referenceField
    rw [hctx, hslot]
  have hfield := T.source_eq_actualWeakSampledPiolaField D c.chain.1 ρ ell slot.1 I
    (M.referenceField he hΛ hbw c slot hs) hw hTm' hTa' d word
  have hp := T.production hHN (Construction.Stream.ocEpsilon_pos hΛ) hC hθ hκ
    (Construction.Stream.ocEpsilon_pos hΛ).le
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (pow_nonneg (by positivity) _)) (d - 1) word
  rw [hfield] at hp
  rw [Nat.sub_add_cancel hd] at hp
  exact hp

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual successor field is the literal scheduled cutoff sum of produced sampled means. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

def IndependentWeakMeanArrayProduction.stepField
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hbw : 0 < bw)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (ρ ell : ℝ) (I : ℤ → Set ℝ) (d : ℕ) (word : DerivativeWord2 (d - 1)) :
    ℝ → Vec 2 → Vec (2 + 4 * c.chain.1.children.length) → Vec 2 :=
  independentWeakCutoffPartition D fine (fun slot t z Y =>
    ∑ᶠ hs : Odd slot ∧ IsScheduledIn D level slot c.slot.1,
      actualWeakSampledPiolaField D c.chain.1 ρ ell slot (I slot) n
        (M.referenceField he hΛ hbw c ⟨slot, hs.1⟩ hs.2) d word t z Y)

theorem IndependentWeakMeanArrayProduction.stepField_phase
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hbw : 0 < bw)
    (c : WeakStageProductionContext D bw j₀ level minBase cap)
    (ρ ell : ℝ) (I : ℤ → Set ℝ) (d : ℕ) (word : DerivativeWord2 (d - 1))
    (δ : Vec (2 + 4 * c.chain.1.children.length))
    (hδ : δ ∈ independentFreshPhaseTranslations c.chain.1.children.length) :
    IndependentSourceTranslationInvariant δ (M.stepField he hΛ hbw c ρ ell I d word) := by
  apply independentWeakConditionalPartition_translation
  intro slot hs
  exact actualWeakSampledPiolaField_phase D hΛ hζ c.chain.1 c.chain.2 ρ ell slot (I slot) n
    (M.referenceField he hΛ hbw c ⟨slot, hs.1⟩ hs.2)
    (M.referenceField_phase he hΛ hbw c ⟨slot, hs.1⟩ hs.2) δ hδ d word

end AVRegularity.EntryWeakProofs
end
end

section
/-! Reconstructed mean coefficient arrays equal the original native arrays on the true open carrier. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d T base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteNativeMeanCoefficient_copy
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (Y : Vec (2 + d)) (hY : Y ∈ S.U)
    (hh n : ℕ) (hhh : hh ≤ R) (hn : 1 ≤ n) (hhpos : hh ≠ 0)
    (k : Fin 2) (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Icc S.a S.b) (z : Vec 2) (v u : ι) :
    let Q : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
        S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
          (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
    positiveMeanFluxCoefficient Q (independentFiniteNativeCoefficients S P Y) hh n k m α t
      (independentIntrinsicSlowProjection d Y) z v u =
    positiveMeanFluxCoefficient Q (S.Cc (independentStoredParameterProjection d Y)) hh n k m α t
      (independentIntrinsicSlowProjection d Y) z v u := by
  dsimp only
  exact positiveMeanFluxCoefficient_slow_local_congr
    (independentIntrinsicSliceCarrier_isOpen d S.U S.open_carrier Y) _
    (independentFiniteNativeCoefficients S P Y) (S.Cc (independentStoredParameterProjection d Y))
    hh n hn hhpos t
    (fun p q hpq m hm α X hX z v u => independentFiniteNativeCoefficients_copy S P Y p q m
      (by rcases hpq with hp | ⟨hp, _⟩ <;> omega) hm α t ht X z hX v u)
    k m hm α (independentIntrinsicSlowProjection d Y)
    (independentIntrinsicSliceCarrier_base d S.U Y hY) z v u

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual sampled mean input respects whole-ball reference geometry across parent charts. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {D : OCData} {bw θ B : ℝ} {j₀ minBase cap H n level fine : ℕ}
  {native : ∀ p : OddSlot, StageCtx D bw j₀ fine p → ∀ d,
    DerivativeWord2 (d - 1) → ℝ → Vec 2}

theorem IndependentWeakMeanArrayProduction.stepField_geometry
    (M : IndependentWeakMeanArrayProduction D bw j₀ fine minBase (cap + 1) H n θ B native)
    (he : level + 1 = fine) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hbw : 0 < bw)
    (c c' : WeakStageProductionContext D bw j₀ level minBase cap)
    (hslot : c.slot = c'.slot) (hdepth : c.chain.1.children.length = c'.chain.1.children.length)
    (d : ℕ) (word : DerivativeWord2 (d - 1))
    (P : Vec (4 * c.chain.1.children.length)) (Q : Vec (4 * c'.chain.1.children.length))
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ 3 / 16)
    (hQ : ∀ j, ‖independentFreshChildProjection j false Q‖ ≤ 3 / 16)
    (hgeom : (actualIndependentCoarseParameterChain D c.chain.1 P).geom D =
      (actualIndependentCoarseParameterChain D c'.chain.1 Q).geom D)
    (X : Vec 2) (hX : ‖X‖ < 1 / 8)
    (hell : |D.eps level / D.eps (level - 1)| ≤ 1)
    (I : ℤ → Set ℝ)
    (hδ : ∀ slot, Odd slot ∧ IsScheduledIn D level slot c.slot.1 → ∀ t ∈ I slot, ∀ z,
      ‖D.relDisp level c.slot.1 (D.slotAnchor (level + 1) slot) t z‖ ≤ 1 / 16)
    (t : ℝ) (z : Vec 2) :
    M.stepField he hΛ hbw c (D.eps (level - 1)) (D.eps level / D.eps (level - 1)) I d word t z
      (independentIntrinsicParameterPacking (4 * c.chain.1.children.length) X P) =
    M.stepField he hΛ hbw c' (D.eps (level - 1)) (D.eps level / D.eps (level - 1)) I d word t z
      (independentIntrinsicParameterPacking (4 * c'.chain.1.children.length) X Q) := by
  classical
  unfold IndependentWeakMeanArrayProduction.stepField independentWeakCutoffPartition
  apply finsum_congr
  intro slot
  apply congrArg (fun w : Vec 2 => ocCutoff D.α D.q D.Λ fine slot t • w)
  dsimp only
  by_cases hs : Odd slot ∧ IsScheduledIn D level slot c.slot.1
  · have hs' : Odd slot ∧ IsScheduledIn D level slot c'.slot.1 := by simpa only [hslot] using hs
    rw [finsum_eq_single _ hs (fun h hh => False.elim (hh (Subsingleton.elim h hs))),
      finsum_eq_single _ hs' (fun h hh => False.elim (hh (Subsingleton.elim h hs')))]
    exact M.sampledField_geometry he hΛ hζ hbw c c' hslot hdepth ⟨slot, hs.1⟩ hs.2 hs'.2
      d word P Q hP hQ hgeom X hX hell (I slot) t z (fun ht => hδ slot hs t ht z)
  · have hs' : ¬ (Odd slot ∧ IsScheduledIn D level slot c'.slot.1) := by simpa only [hslot] using hs
    let : IsEmpty (Odd slot ∧ IsScheduledIn D level slot c.slot.1) := ⟨hs⟩
    let : IsEmpty (Odd slot ∧ IsScheduledIn D level slot c'.slot.1) := ⟨hs'⟩
    exact (finsum_of_isEmpty _).trans (finsum_of_isEmpty _).symm

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual empty-edge histories supply the positive primitive inputs of the coherent Eddy producer. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set Filter Topology AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem uniform_actual_independent_coarse_positive_datum_production (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (J H N sZ : ℕ) :
    ∃ (χ : ∀ r, Vec (2 + 4 * r) → ℝ) (BG BV : ℝ),
      (∀ r, ContDiff ℝ (⊤ : ℕ∞) (χ r) ∧ (∀ Y, χ r Y ∈ Icc 0 1) ∧
        (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ r =ᶠ[𝓝 Y] fun _ => 1) ∧
        (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z →
          χ r Y = χ r Z)) ∧
      1 ≤ BG ∧ 0 ≤ BV ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      M ≤ D.term → D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.children.length ≤ J → D.term < A.ctxLevel →
      ∀ bw j₀, IsAdmissibleChain D bw j₀ A.ctxLevel A.slot A →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.eps A.lastLevel → ∀ Dm sX,
      ∀ Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ),
      (∀ B, IsAdmissibleChain D bw j₀ A.ctxLevel A.slot B →
        IsLiftSequence (familyLiftData (Dm := Dm) D A.ctxLevel A.slot B ρ (fun _ _ _ => [])) sX sZ
          (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
          ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)
          N 0 (Cc B)) →
      ∃ x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * A.children.length)
          H N N 0 0 sZ BG BV 0,
        x.response = D.weakPe A.ctxLevel ∧
        x.data.primitive.a = D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel ∧
        x.data.primitive.b =
          (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel ∧
        x.data.primitive.U = actualIndependentCoarseNativeCarrier D A bw ∧
        x.data.primitive.G = actualIndependentCoarseScaledExtendedMetric D A ρ (χ A.children.length)
          x.data.primitive.a x.data.primitive.b ∧
        x.data.primitive.v = ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot ∧
        x.data.primitive.edge = (fun _ _ _ => []) ∧
        x.data.primitive.M = (fun _ _ => 0) ∧
        x.data.primitive.Cc = independentCarrierCoefficientExtension
          (actualIndependentCoarseStoredCarrier D A bw)
          (fun P => Cc (actualIndependentCoarseParameterChain D A P)) ∧
        x.data.translations = independentFreshPhaseTranslations A.children.length := by
  let O := independentPositivePrimitiveTopOrder H N N 0
  obtain ⟨χ, BG, BV, hχ, hBG, hBV, M, hM, hmol⟩ :=
    uniform_actual_independent_coarse_molecular_production
      α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J (O + N) (O + N + 1)
  refine ⟨χ, BG, BV, hχ, hBG, hBV, M, hM, ?_⟩
  intro D hterm hDα hDq hDΛ hDζ hseq hband A hbase hdepth hweak bw j₀ hA
    ρ hρ hρle Dm sX Cc hc
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζ' : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  obtain ⟨QM, Qv, Mdata, hQM, hQv, hPeQv, hPe1, hMG, hMv, hMC, hV⟩ :=
    hmol D hterm hDα hDq hDΛ hDζ hseq hband A hbase hdepth hweak bw j₀ hA ρ hρ hρle
  let c := fun P => Cc (actualIndependentCoarseParameterChain D A P)
  have hc' P (hP : P ∈ actualIndependentCoarseStoredCarrier D A bw) :
      IsLiftSequence (familyLiftData (Dm := N) D A.ctxLevel A.slot
        (actualIndependentCoarseParameterChain D A P) ρ (fun _ _ _ => [])) sX sZ
        (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)
        N 0 (c P) := by
    have hB := (actualIndependentCoarseParameterChain_admissible_iff
      D A bw j₀ A.ctxLevel A.slot hA P).mpr hP
    exact scalar_family_lift_zero_grade_degree_congr D A.ctxLevel A.slot
      (actualIndependentCoarseParameterChain D A P) ρ Dm N sX sZ N _ _ (c P) (hc _ hB)
  let S := actualIndependentCoarseEmptyPrimitiveData (ι := Fin 1) O N N BG BV
    D hΛ₁ hζ' hband A bw j₀ hA hweak ρ (χ A.children.length) (hχ _).2.2.1
    sX sZ c hc' QM hQM Qv hQv Mdata hMG hMv hMC
    (fun Y K hK => (hV Y K (by omega)).some)
  have hPe0 : 0 ≤ D.weakPe A.ctxLevel :=
    div_nonneg (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ₁).le _)
      (weakData_kap_pos D hΛ₁ hζ' hband _).le
  let x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * A.children.length)
      H N N 0 0 sZ BG BV 0 :=
    { data :=
        { primitive := S
          fastOrder := rfl
          translations := independentFreshPhaseTranslations A.children.length
          metric_translation := fun δ hδ t Y =>
            actualIndependentCoarseScaledExtendedMetric_phase_translation D hΛ₁ A bw j₀
              A.ctxLevel A.slot hA ρ _ _ t (χ A.children.length) (hχ _).2.2.2 δ hδ Y
          edge_translation := by
            intro δ _hδ v u e γ hγ
            exact (List.not_mem_nil hγ).elim }
      response := D.weakPe A.ctxLevel
      response_nonneg := hPe0
      response_small := hPe1
      drift_response := fun i r _hr => hPeQv i r }
  exact ⟨x, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal native inherited means from the internally produced finite coefficient fields. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d T base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteNativeMeanFlux_literal_apply
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (hD : 1 ≤ D) (hbase : D ≤ base) (Y : Vec (2 + d)) (hh n : ℕ)
    (hn : 2 ≤ n) (hhpos : hh ≠ 0) (A : Vec 2 →L[ℝ] ℝ) (u : ι)
    (k : Fin 2) (t : ℝ) (X z : Vec 2) (v : ι) :
    let Q : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
        S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
          (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
    liftApply (n - 1) (positiveMeanFluxCoefficient Q (independentFiniteNativeCoefficients S P Y) hh n k)
      (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) t X z v =
      fieldCellMean (fun z => liftFluxX Q (independentFiniteNativeCoefficients S P Y)
        (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) hh n t X z k) v := by
  dsimp only
  let Q : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
      S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
        (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
  have hbase1 : 1 ≤ base := hD.trans hbase
  refine positiveMeanFluxCoefficient_literal_apply Q hD (independentFiniteNativeCoefficients S P Y)
    hh n hn hhpos _ ((Real.contDiff_exp.comp A.contDiff).smul contDiff_const)
    k t X z v ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j
    exact ((((S.metric_entries i j).affineSlice (independentIntrinsicSlowEmbedding d)
      (independentIntrinsicSlowEmbedding_norm_le d) (independentIntrinsicSliceOffset d Y)).goodField t).1.comp
        (contDiff_id.prodMk (contDiff_const (c := (0 : Vec 2))))).of_le (by simp)
  · apply continuous_pi
    intro i
    exact (((S.drift_entries i).regular t).comp₂ contDiff_id
      (contDiff_const (c := (0 : Vec (2 + d))))).continuous
  · exact (independentFiniteNativeTest_goodField S P hB Y hh (n - 1) A u t).mono hbase1
  · exact (independentFiniteNativeTest_positive_grade_centField S P hB Y hh (n - 2) hhpos A u t).mono hbase1
  · intro m hm α w
    exact (scalarCoefficient_goodField base m _ α v w
      (independentFiniteNativeCoefficients_reserve S P hB Y hh (n - 1) m α v w) t).continuous_slice X
  · intro j hj m hm α w w'
    exact scalarCoefficient_boxSmooth base j ((D - 1) - j) m (by omega) _ α w w'
      (independentFiniteNativeCoefficients_reserve S P hB Y (hh - 1) (n - 1 - j) m α w w') t
  · intro q
    exact (independentFiniteNativeTest_goodField S P hB Y (hh - 1) q A u t).mono hbase
  · intro w w' e γ hγ α
    exact ((independent_edge_slice_source_reserve S.edge S.edgeField S.edges
      (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d)
      (independentIntrinsicSliceOffset d Y) w w' e γ hγ α).goodField t).mono (by omega)

theorem independentFiniteNativeMeanFlux_normalized_apply
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (hD : 1 ≤ D) (hbase : D ≤ base) (Y : Vec (2 + d)) (hh n : ℕ)
    (hn : 2 ≤ n) (hhpos : hh ≠ 0) (A : Vec 2 →L[ℝ] ℝ) (u : ι)
    (k : Fin 2) (t : ℝ) (X z : Vec 2) (v : ι) :
    let Q : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
        S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
          (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
    normalizedLiftTestField
      (positiveMeanFluxCoefficient Q (independentFiniteNativeCoefficients S P Y) hh n k)
      (n - 1) A u v 1 t X z =
      (Real.exp (A X))⁻¹ • fieldCellMean (fun z => liftFluxX Q
        (independentFiniteNativeCoefficients S P Y)
        (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) hh n t X z k) v := by
  dsimp only
  unfold normalizedLiftTestField
  rw [independentFiniteNativeMeanFlux_literal_apply S P hB hD hbase Y hh n hn hhpos A u k t X z v]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Reuse the smooth-test action for full independent native fields, including the monomials of physical extraction. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d T base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteNativeSmooth_goodField
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (Y : Vec (2 + d)) (hh n : ℕ)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    GoodField base (liftApply n (independentFiniteNativeCoefficients S P Y hh n) (fun _ => f) t) :=
  scalarLiftSmoothTest_goodField base n _ f hf
    (fun m α v w => independentFiniteNativeCoefficients_reserve S P hB Y hh n m.val α v w) t

theorem independentFiniteNativeSmooth_positive_grade_centField
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (Y : Vec (2 + d)) (hh n : ℕ) (hhpos : hh ≠ 0)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    CoefField True base (liftApply n (independentFiniteNativeCoefficients S P Y hh n) (fun _ => f) t) :=
  scalarLiftSmoothTest_centField base n _ f hf
    (fun m α v w => independentFiniteNativeCoefficients_reserve S P hB Y hh n m.val α v w)
    (fun m _ α t X v w ξ => independentFiniteNativeCoefficients_positive_grade_mean_zero
      S P Y hh n hhpos m α t X v w ξ) t

theorem independentFiniteNativeMeanFlux_smooth_apply
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (hD : 1 ≤ D) (hbase : D ≤ base) (Y : Vec (2 + d)) (hh n : ℕ)
    (hn : 2 ≤ n) (hhpos : hh ≠ 0)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : Fin 2) (t : ℝ) (X z : Vec 2) (v : ι) :
    let Q : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
        S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
          (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
    liftApply (n - 1) (positiveMeanFluxCoefficient Q (independentFiniteNativeCoefficients S P Y) hh n k)
      (fun _ => f) t X z v =
      fieldCellMean (fun z => liftFluxX Q (independentFiniteNativeCoefficients S P Y)
        (fun _ => f) hh n t X z k) v := by
  dsimp only
  let Q : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
      S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
        (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
  have hbase1 : 1 ≤ base := hD.trans hbase
  refine positiveMeanFluxCoefficient_literal_apply Q hD (independentFiniteNativeCoefficients S P Y)
    hh n hn hhpos f hf
    k t X z v ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j
    exact ((((S.metric_entries i j).affineSlice (independentIntrinsicSlowEmbedding d)
      (independentIntrinsicSlowEmbedding_norm_le d) (independentIntrinsicSliceOffset d Y)).goodField t).1.comp
        (contDiff_id.prodMk (contDiff_const (c := (0 : Vec 2))))).of_le (by simp)
  · apply continuous_pi
    intro i
    exact (((S.drift_entries i).regular t).comp₂ contDiff_id
      (contDiff_const (c := (0 : Vec (2 + d))))).continuous
  · exact (independentFiniteNativeSmooth_goodField S P hB Y hh (n - 1) f hf t).mono hbase1
  · exact (independentFiniteNativeSmooth_positive_grade_centField S P hB Y hh (n - 2) hhpos f hf t).mono hbase1
  · intro m hm α w
    exact (scalarCoefficient_goodField base m _ α v w
      (independentFiniteNativeCoefficients_reserve S P hB Y hh (n - 1) m α v w) t).continuous_slice X
  · intro j hj m hm α w w'
    exact scalarCoefficient_boxSmooth base j ((D - 1) - j) m (by omega) _ α w w'
      (independentFiniteNativeCoefficients_reserve S P hB Y (hh - 1) (n - 1 - j) m α w w') t
  · intro q
    exact (independentFiniteNativeSmooth_goodField S P hB Y (hh - 1) q f hf t).mono hbase
  · intro w w' e γ hγ α
    exact ((independent_edge_slice_source_reserve S.edge S.edgeField S.edges
      (independentIntrinsicSlowEmbedding d) (independentIntrinsicSlowEmbedding_norm_le d)
      (independentIntrinsicSliceOffset d Y) w w' e γ hγ α).goodField t).mono (by omega)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Local native coefficient copies suffice for the literal physical mean action on the original family. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {d T base D N R count : ℕ} {BG BV BE B : ℝ}

theorem independentFiniteOriginalMeanFlux_smooth_apply
    (S : IndependentLiftPrimitiveData ι d T D N R count BG BV BE)
    (P : IndependentLiftMenuProductions S base B) (hB : 1 ≤ B)
    (hD : 1 ≤ D) (hbase : D ≤ base) (Y : Vec (2 + d)) (hY : Y ∈ S.U)
    (hh n : ℕ) (hhh : hh ≤ R) (hn : 2 ≤ n) (hhpos : hh ≠ 0)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : Fin 2) (t : ℝ) (ht : t ∈ Icc S.a S.b) (z : Vec 2) (v : ι) :
    let Q : LiftOperatorData ι (fun _ => ℝ) D :=
      ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
        S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
          (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
    liftApply (n - 1) (positiveMeanFluxCoefficient Q
      (S.Cc (independentStoredParameterProjection d Y)) hh n k) (fun _ => f)
      t (independentIntrinsicSlowProjection d Y) z v =
      fieldCellMean (fun w => liftFluxX Q (S.Cc (independentStoredParameterProjection d Y))
        (fun _ => f) hh n t (independentIntrinsicSlowProjection d Y) w k) v := by
  dsimp only
  let Q : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨1, fun t X => S.G t (independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y),
      S.v, independentConstituentEdgeSlice S.edge S.edgeField S.edges
        (independentIntrinsicSlowEmbedding d) (independentIntrinsicSliceOffset d Y)⟩
  let C := independentFiniteNativeCoefficients S P Y
  have haction := independentFiniteNativeMeanFlux_smooth_apply S P hB hD hbase Y
    hh n hn hhpos f hf k t (independentIntrinsicSlowProjection d Y) z v
  have hcoeff : liftApply (n - 1) (positiveMeanFluxCoefficient Q C hh n k) (fun _ => f)
      t (independentIntrinsicSlowProjection d Y) z v =
      liftApply (n - 1) (positiveMeanFluxCoefficient Q
        (S.Cc (independentStoredParameterProjection d Y)) hh n k) (fun _ => f)
        t (independentIntrinsicSlowProjection d Y) z v := by
    unfold liftApply
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro u _
    rw [independentFiniteNativeMeanCoefficient_copy S P Y hY hh n hhh (by omega) hhpos
      k m (by have := Finset.mem_range.mp hm; omega) α t ht z v u]
  have hflux (w : Vec 2) : liftFluxX Q C (fun _ => f) hh n t
      (independentIntrinsicSlowProjection d Y) w k =
      liftFluxX Q (S.Cc (independentStoredParameterProjection d Y)) (fun _ => f) hh n t
        (independentIntrinsicSlowProjection d Y) w k := by
    apply liftFluxX_slow_open_congr_predecessors
      (independentIntrinsicSliceCarrier_isOpen d S.U S.open_carrier Y) Q C _
      (fun _ => f) hh n hn t _ _ (independentIntrinsicSliceCarrier_base d S.U Y hY) w k
    intro p q hpq m hm α X hX z v u
    exact independentFiniteNativeCoefficients_copy S P Y p q m
      (by rcases hpq with hp | ⟨rfl, _⟩ <;> omega) hm α t ht X z hX v u
  exact hcoeff.symm.trans (haction.trans (congrArg (fun F : Vec 2 → ι → ℝ => fieldCellMean F v)
    (funext hflux)))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Reading a coherently chosen Eddy field on its actual native carrier preserves the response square. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

theorem independent_actual_coarse_eddy_copy (J H N sZ : ℕ) (BG BV : ℝ)
    (E : IndependentPositiveEddyDepthProducer (Fin 1) J H N N 0 0 sZ BG BV 0)
    (D : OCData) (A : RealChain) (bw : ℝ) (hdepth : A.children.length ≤ J)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (x : IndependentPositiveNaturalPrimitiveDatum (Fin 1) (4 * A.children.length)
      H N N 0 0 sZ BG BV 0)
    (hresponse : x.response = D.weakPe A.ctxLevel)
    (ha : x.data.primitive.a = D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
    (hb : x.data.primitive.b =
      (((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel)
    (hU : x.data.primitive.U = actualIndependentCoarseNativeCarrier D A bw)
    (hv : x.data.primitive.v =
      ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot)
    (hCc : x.data.primitive.Cc = independentCarrierCoefficientExtension
      (actualIndependentCoarseStoredCarrier D A bw)
      (fun P => Cc (actualIndependentCoarseParameterChain D A P)))
    (hphase : x.data.translations = independentFreshPhaseTranslations A.children.length)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (m : ℕ) (hm : m ≤ n) (β : DerivativeWord2 m) :
    ∃ Q : IndependentParameterSourceReserve H
        (E.field ⟨A.children.length, by omega⟩ x n hn hnN m hm β 0 0),
      (∀ j ≤ H, Q.budget j ≤ D.weakPe A.ctxLevel ^ 2 * E.budget) ∧
      (∀ t ∈ Icc (D.slotStart A.ctxLevel A.slot / D.cellScaleSq A.ctxLevel)
        ((((A.slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ A.ctxLevel) / D.cellScaleSq A.ctxLevel),
        ∀ Y ∈ actualIndependentCoarseNativeCarrier D A bw, ∀ z k,
          E.field ⟨A.children.length, by omega⟩ x n hn hnN m hm β 0 0 t z Y k =
          fieldCellMean (fun w =>
            ocPulseCellDrift D.α D.q D.Λ D.ζ A.ctxLevel (D.kap A.ctxLevel) A.slot t w k •
              Cc (actualIndependentCoarseParameterChain D A
                (independentStoredParameterProjection (4 * A.children.length) Y))
                0 n m β t (independentIntrinsicSlowProjection (4 * A.children.length) Y) w 0 0 1)) ∧
      (∀ δ ∈ independentFreshPhaseTranslations A.children.length,
        IndependentSourceTranslationInvariant δ
          (E.field ⟨A.children.length, by omega⟩ x n hn hnN m hm β 0 0)) := by
  obtain ⟨Q, hQ, hcopy, hperiod⟩ :=
    E.production ⟨A.children.length, by omega⟩ x n hn hnN m hm β 0 0
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro j hj
    simpa only [hresponse, finiteMatrixPower_zero, ite_true, mul_one] using hQ j hj
  · intro t ht Y hY z k
    have ht' : t ∈ Icc x.data.primitive.a x.data.primitive.b := by
      simpa only [ha, hb] using ht
    have hY' : Y ∈ x.data.primitive.U := by simpa only [hU] using hY
    have he := hcopy t ht' Y hY' z k
    simp only [Fin.val_mk] at he
    have hstored : independentStoredParameterProjection (4 * A.children.length) Y ∈
        actualIndependentCoarseStoredCarrier D A bw := hY.1
    rw [hv, hCc, independentCarrierCoefficientExtension,
      ite_eq_right (by omega : n ≠ 0), ite_eq_left hstored] at he
    exact he
  · simpa only [hphase] using hperiod

end AVRegularity.EntryWeakProofs
end
end
end
