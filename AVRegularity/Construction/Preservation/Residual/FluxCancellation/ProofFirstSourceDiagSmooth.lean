-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanFinal
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.Construction.StageSuccessor.StageOfFields
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Proofs.GenSem.Jet.Chart

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! The first-source-flux step, Lemma Piola-A: the smooth case and the conclusion.

`fsPiolaSmooth : FSPiolaSmooth`: on a smooth field the label operator at the recentred actual
context is the array operator `fsArr` (`firstSourceFlux_applyArr`; the strain coefficient is smooth
by `contDiff_contextStrain_recenter`, the lifts of the admissible children of nonzero cut-off are
regular by `liftRegular_of_isLiftSequence` applied to `SplitWitness.diag`, with the floors of
`SplitInput.range`), the arrays vanish above the order `N + 4p` (`first_source_array_support`),
and an array operator at the centre is the sum of its symmetric coefficients
(`arrOp_eq_sum_fluxCoeff`).

`fsPiolaOperator : FSPiolaOperator`, by `fsPiolaOperator_of_jet` and `fsLabelOpJet`. -/

section
open CovarianceTransport

/-- **Lemma Piola-A for a smooth field.** -/
theorem fsPiolaSmooth : FSPiolaSmooth := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x u hu
  classical
  have hi := hin.stage
  have hm : 1 ≤ G.level := by have := hi.level; omega
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hi.base
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hi.base hi.profile hi.band G.level
  have hκ : 0 < D.κ (G.level - 1) := by
    have hh := EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band (G.level - 1)
    simpa only [OCData.kap, min_eq_left ((Nat.sub_le _ _).trans hi.top)] using hh
  have hρ : Mn.lenFactor * liftLength D G.level ≠ 0 := by
    unfold liftLength
    exact (mul_pos hi.length_factor (Real.sqrt_pos.2 (mul_pos hκ
      (Construction.Stream.ocTauPP_pos hi.base)))).ne'
  have hch : (fsCtx G' p t x).WellSlotted := (fsAlg_ctx_adm hin p t x).2.2.1
  have hf := Providers.GenSem.scheduledSlots_finite D (G.level - 1) (fsCtx G' p t x).slot (by
    simpa only [Nat.sub_add_cancel hm] using hτ)
  have hS : ∀ k, k ∈ hf.toFinset ↔ Odd k ∧ IsScheduledIn D (G.level - 1) k (fsCtx G' p t x).slot :=
    fun k => hf.mem_toFinset
  have hstrain : ∀ a c, ContDiff ℝ ((4 * Mn.p : ℕ) : WithTop ℕ∞)
      (fun y => Providers.GenSem.strainAt D G.level t (fsCtx G' p t x)
        ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) y a c) := by
    intro a c
    exact ((Providers.GenSem.contDiff_contextStrain_recenter D hi.profile (G.level - 1)
      (fsCtx G' p t x).slot t (fsCtx G' p t x) hch _ a c).comp
      (Providers.GenSem.contDiff_famMapInv (fsCtx G' p t x) t)).of_le
        (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨Dord, nMax, hMax, npad, -, -, -, -, -, hfX, hfZ⟩ := hin.range
  have hR : 2 * Mn.p + Dm + 2 ≤ Mn.sX ∧ 2 * Mn.p + Dm + 2 ≤ Mn.sZ := by
    have := le_max_right (Mn.N + Dord) (2 * Mn.p)
    omega
  have he : ∀ (g : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → ∀ c,
      fsLabelOp Mn G G' W.Cc0 p t x g 0 c =
        Providers.GenSem.applyArr (Mn.N + 4 * Mn.p)
          (Providers.GenSem.fsArr D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N
            Mn.p Mn.anchor W.Cc0 hf.toFinset t (fsCtx G' p t x)
            ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) c) g 0 0 := by
    intro g hg c
    have h1 := Providers.GenSem.firstSourceFlux_applyArr (b := b) (j₀ := j₀) (Dm := Dm)
      (N := Mn.N) (p := Mn.p) (s₀ := Mn.anchor) (Cc0 := W.Cc0) hi.profile hρ hi.cutoff t
      (fsCtx G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x) hf.toFinset hS
      hstrain
      (fun n _ _ k hk hA hcut => Providers.GenSem.liftRegular_of_isLiftSequence D G.level k
        hA.2.2.1 _ (W.diag k _ ((hS k).mp hk).1 hA) hR.1 hR.2 0 le_rfl n _
        (CovFluxReg.clock_mem_window D G.level k t hτ hcc hcut) 0) hg 0 c
    unfold fsLabelOp
    rw [h1, Providers.GenSem.applyArr_eq_of_supp (by omega)
      (StageSuccessor.first_source_array_support hi.cutoff _ t _ _ c)]
  have key := Providers.QuietAtlas.arrOp_eq_sum_fluxCoeff (Mn.N + 4 * Mn.p) _
    (fsLabelOp Mn G G' W.Cc0 p t x) he hu
  have hn : Mn.N + 1 + 4 * Mn.p = Mn.N + 4 * Mn.p + 1 := by ring
  rw [Providers.QuietAtlas.sum_Icc_one_eq_sum_range, hn]
  exact key

/-- **Lemma Piola-A.** -/
theorem fsPiolaOperator : FSPiolaOperator := fsPiolaOperator_of_jet fsPiolaSmooth fsLabelOpJet
end

/-! The first-source-flux step (the physical flux of the first source), conclusion.

* `fsDiagSmooth : FSDiagSmooth`: for a smooth field frozen in time, the pushed grade-zero label
  flux of the appended child is the pushed label flux of the native chain of the finer slot by
  its natural chart, at the translated point (`fsd_child_push`: the recentred actual context of
  the piece is the native context at the coarser label of the point, `fsAlg_ctx_native`), and
  that is `ℓ` of the Hilbert pulse flux (`fsd_hilbert_pulse`);
* `fsDiagTerm : FSDiagTerm`, by `fsDiagTerm_of_steps` and the two jet localities;
* `firstSourceIdentity : FirstSourceIdentityStatement`, by `firstSourceIdentity_of_three` from
  `fsPiolaOperator`, `fsPiolaConstant`, `fsDiagTerm`;
* `firstSourcePhysicalFlux : FirstSourcePhysicalFluxStatement`: the three earlier pieces are not
  used as hypotheses (their content enters through the proved lemmas `firstSourceReadout`,
  `piecePiolaFiniteOrder`, `hilbertLiftGradeZero`). -/

section
open CovarianceTransport

/-- **The per-pulse identity for a smooth field frozen in time.** -/
theorem fsDiagSmooth : FSDiagSmooth := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x T hT v ℓ x' j n h2 hn k hk hc
  have hi := hin.stage
  obtain ⟨h1, hj0, hL'⟩ := fsAlg_level_pos hin
  have hL : G.level = G'.level + 1 := by have := hi.level; omega
  have hnat : G'.IsNatural Mn.M := hin.successor.2.2.2.1
  have hcp : ocCutoff D.α D.q D.Λ G'.level p.1 t ≠ 0 := by rw [← hnat.2.1 p t]; exact hp
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hi.base hi.profile hi.band G.level
  have hκ : 0 < D.κ (G.level - 1) := by
    have hh := EntryWeakProofs.weakData_kap_pos D hi.base hi.profile hi.band (G.level - 1)
    simpa only [OCData.kap, min_eq_left ((Nat.sub_le _ _).trans hi.top)] using hh
  have hρ : Mn.lenFactor * liftLength D G.level ≠ 0 := by
    unfold liftLength
    exact (mul_pos hi.length_factor (Real.sqrt_pos.2 (mul_pos hκ
      (Construction.Stream.ocTauPP_pos hi.base)))).ne'
  have hctx := fsAlg_ctx_native hin p t x
  have hsymm : ((G'.fam.piece p).material t).symm x =
      D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x t :=
    congrFun (tc_material_symm hnat p t) x
  have hxY : D.flowOf (G'.level - 1) t
      (D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x t) (D.slotAnchor G'.level p.1) = x :=
    flowOf_inv D _ t _ x
  have key := fsd_child_push hi.base hi.profile hin.stream hi.bandwidth hin.start hL h1 hj0 hcc
    W.diag hρ p.2 hk hcp hc (D.flowOf (G'.level - 1) (D.slotAnchor G'.level p.1) x t) n
    (fun y => ℓ (T y v)) x'
  rw [hxY] at key
  unfold fsDiagLhs
  rw [hctx, hsymm]
  simp only [key.1, ↓reduceIte]
  rw [key.2]
  exact (fsd_hilbert_pulse hin W t hk hc T hT n v ℓ (x + x') j).symm

/-- **The per-pulse identity** (sub-step Diagonal of the first-source-flux step). -/
theorem fsDiagTerm : FSDiagTerm := fsDiagTerm_of_steps fsDiagSmooth fsDiagJetL fsDiagJetR
end

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
