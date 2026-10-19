-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.StageSuccessor.StageOfFields
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.WeakGen.InhFacts

@[expose] public noncomputable section

section
open Homogenization Set AVRegularity.Sobolev
namespace AVRegularity.Construction.StageSuccessor

/-! First-source coefficient support for the shared canonical diagonal arrays.
All finite reserve orders are supplied by the one canonical empty-edge lift. -/

open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs AVRegularity.Providers.GenSem
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {P : ProvParams} {Mn : SuccMenu}
  {G : GenStage D hr Dm b j₀}

/-- The canonical diagonal array supplies any finite analytic reserve on its pulse. -/
theorem diagonal_lifts_regular (hi : Input P Mn G) (k : ℤ) (hk : Odd k) (A : RealChain)
    (hA : IsAdmissibleChain D b j₀ G.level k A) (n R : ℕ) (t : ℝ)
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k) :
    LiftRegular (diagQ D Dm G.level k A (Mn.lenFactor * liftLength D G.level))
      (diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
        (Mn.lenFactor * liftLength D G.level) Mn.N k A) (0 : Fin 1)
      ((D.cellScaleSq G.level)⁻¹ * t) 0 n R := by
  classical
  have hc := native_empty_full_lift_all_orders (ι := Fin 1) (Dm := Dm) D hi.profile hi.base G.level
    (weakData_kap_pos D hi.base hi.profile hi.band G.level) k hk A hA.2.2.1
    (Mn.lenFactor * liftLength D G.level) _ _
    (weakData_lift_window_strict D hi.base hi.profile hi.band G.level k) Mn.N hi.order R R
  have hseq : IsLiftSequence (diagQ D Dm G.level k A (Mn.lenFactor * liftLength D G.level)) R R
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N 0
      (diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
        (Mn.lenFactor * liftLength D G.level) Mn.N k A) := by
    simpa only [diagonalLiftFamily, dite_eq_left (show _ ∧ Odd k from ⟨hA, hk⟩)] using hc
  exact liftRegular_of_isLiftSequence D G.level k hA.2.2.1 _ hseq le_rfl le_rfl
    0 le_rfl n _ (Providers.WeakGen.physical_pulse_cell_time hi.base hi.profile hi.band _ _ t ht) 0

/-- The first-source operator has exactly the maximum order recorded on a diagonal letter. -/
theorem diagonal_coefficient_above_order (hi : Input P Mn G) (t : ℝ) (ch : RealChain)
    (hch : ch.WellSlotted) (ζ : Vec 2) (d : ℕ) (I : DerivativeWord2 (d - 1))
    (hd : Mn.N + 1 + 4 * Mn.p < d) :
    fluxCoeff (firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level)
      Mn.N Mn.p Mn.anchor (diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
        (Mn.lenFactor * liftLength D G.level) Mn.N) t ch ζ) d I 0 = 0 := by
  classical
  have hm : 1 ≤ G.level := by have := hi.level; omega
  have hκ : 0 < D.κ (G.level - 1) := by
    have hh := weakData_kap_pos D hi.base hi.profile hi.band (G.level - 1)
    simpa only [OCData.kap, min_eq_left ((Nat.sub_le _ _).trans hi.top)] using hh
  have hρ : Mn.lenFactor * liftLength D G.level ≠ 0 := by
    unfold liftLength
    exact (mul_pos hi.length_factor (Real.sqrt_pos.2 (mul_pos hκ
      (Construction.Stream.ocTauPP_pos hi.base)))).ne' 
  let hf := scheduledSlots_finite D (G.level - 1) ch.slot (by
    simpa only [Nat.sub_add_cancel hm] using
      (Construction.Stream.ocTau_pos hi.base : 0 < ocTau D.α D.q D.Λ G.level))
  let S := hf.toFinset
  have hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (G.level - 1) k ch.slot :=
    fun k => hf.mem_toFinset
  have hstrain : ∀ a c, ContDiff ℝ ((4 * Mn.p : ℕ) : WithTop ℕ∞)
      (fun x => strainAt D G.level t ch ζ x a c) := by
    intro a c
    exact ((contDiff_contextStrain_recenter D hi.profile (G.level - 1) ch.slot t ch hch ζ a c).comp
      (contDiff_famMapInv ch t)).of_le (WithTop.coe_le_coe.mpr le_top)
  have he : ∀ (u : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) u → ∀ y c,
      firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level)
        Mn.N Mn.p Mn.anchor (diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
          (Mn.lenFactor * liftLength D G.level) Mn.N) t ch ζ u y c =
      applyArr (2 * Mn.p + (Mn.N + 1 + 2 * Mn.p))
        (fsArr D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N Mn.p Mn.anchor
          (diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
            (Mn.lenFactor * liftLength D G.level) Mn.N) S t ch ζ c) u y 0 := by
    intro u hu y c
    apply firstSourceFlux_applyArr hi.profile hρ hi.cutoff t ch ζ S hS hstrain
    · intro n _ _ k hk hA hcut
      exact diagonal_lifts_regular hi k ((hS k).mp hk).1 _ hA n _ t
        (mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hi.base) hcut)
    · exact hu
  have hmono := he (mono 0 I) ((contDiff_mono 0 I).of_le le_top) 0
  have hh := extracted_array_above_support
    (K := 2 * Mn.p + (Mn.N + 1 + 2 * Mn.p))
    (fun c => first_source_array_support (D := D) (b := b) (j₀ := j₀) (Dm := Dm)
      (m := G.level) (ρ := Mn.lenFactor * liftLength D G.level) (p := Mn.p) (s₀ := Mn.anchor)
      (Cc0 := diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
        (Mn.lenFactor * liftLength D G.level) Mn.N) hi.cutoff S t ch ζ c) d I (by omega)
  unfold fluxCoeff at hh ⊢
  have hval : firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level)
      Mn.N Mn.p Mn.anchor (diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
        (Mn.lenFactor * liftLength D G.level) Mn.N) t ch ζ (mono 0 I) 0 =
      (fun c => applyArr (2 * Mn.p + (Mn.N + 1 + 2 * Mn.p))
        (fsArr D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N Mn.p Mn.anchor
          (diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
            (Mn.lenFactor * liftLength D G.level) Mn.N) S t ch ζ c) (mono 0 I) 0 0) :=
    funext hmono
  exact (congrArg (fun x : Vec 2 => ((d - 1).factorial : ℝ)⁻¹ • x) hval).trans hh

end AVRegularity.Construction.StageSuccessor
end

section
open Homogenization Set AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.StageSuccessor

/-! The shared qualitative producer: normalize path lifts, realize the literal
periodic supported coefficient fields, then use the finite source assembly. -/

open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs AVRegularity.Providers.WeakGen

/-- Every incoming certified stage has realized source fields at its own menu length
and anchor. No carrier-start inequality enters this qualitative construction. -/
theorem stage_transfer_fields : StageTransferFieldsStatement := by
  intro hr _ _ D Dm b j₀ P Mn G hi
  let Cc := sourceLiftFamilies (G := G) hi.base hi.profile hi.band (Mn.lenFactor * liftLength D G.level) Mn.N
  let C := phaseNormalizedSourceLifts Cc
  let C0 := diagonalLiftFamily D Dm b j₀ G.level hi.base hi.profile hi.band
    (Mn.lenFactor * liftLength D G.level) Mn.N
  refine ⟨C, C0, phase_normalized_source_lifts hi Cc (source_lift_families hi),
    diagonal_lift_family hi, ?_, ?_⟩
  · intro p c s _hs d I t X
    classical
    let A := c.1.recenter D (D.eps (G.level - 1 - 1) • X)
    by_cases hA : IsAdmissibleChain D b j₀ (G.level - 1) p.1 A
    all_goals dsimp only [A] at hA
    · have hslot : Odd A.slot := by rw [hA.2.2.2.1]; exact p.2
      by_cases hdg : s.IsDiag
      · intro n z
        simp only [sourceTransferredFlux, ite_eq_left hA, ite_eq_left hdg]
        exact congrArg (fun f => (s.lam G.level Mn.η0 *
          (D.κ (G.level - 1) * D.eps (G.level - 1) ^ (d - 2))⁻¹) • fluxCoeff f d I 0)
          (first_source_phase (D := D) (Dm := Dm) (b := b) (j₀ := j₀) (m := G.level)
            (ρ := Mn.lenFactor * liftLength D G.level) (N := Mn.N) (hΛ := hi.base) (hζ := hi.profile) (hband := hi.band)
            A hslot Mn.p Mn.anchor t n z)
      · have hctx : A.ctxLevel + 1 = G.level := by
          have hm := hi.level
          have hc := hA.1
          change A.ctxLevel = G.level - 1 at hc
          omega
        have hf : ∀ k t, t ∈ ocPulseWindow D.α D.q D.Λ (A.ctxLevel + 1) k →
            ∀ A B, WeakChainPhaseLatticeEquivalent A B →
            s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (C s) k t A =
              s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (C s) k t B := by
          rw [hctx]
          intro k t ht A B hp
          exact normalized_source_phase hi Cc s k A B hp t ht
        have he := transferAt_periodic_of_phase_window D hi.base hi.profile p.1
          (s.lam G.level Mn.η0) ((s.prov G.level).tags P).order
          (s.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor (C s)) A hf
          hA.2.2.1 hslot t d I
        rw [hctx] at he
        intro n z
        simpa only [sourceTransferredFlux, ite_eq_left hA, ite_eq_right hdg] using he n z
    · intro n z
      simp only [sourceTransferredFlux, ite_eq_right hA]
  · intro p c s _hs d I t X z hd
    classical
    let A := c.1.recenter D (D.eps (G.level - 1 - 1) • X)
    by_cases hA : IsAdmissibleChain D b j₀ (G.level - 1) p.1 A
    all_goals dsimp only [A] at hA
    · by_cases hdg : s.IsDiag
      · have hord : ((s.prov G.level).tags P).order = Mn.N + 1 + 4 * Mn.p := by
          cases s <;> simp only [SuccSource.IsDiag] at hdg
          simp only [SuccSource.prov, Prov.tags, letterOrder, hi.cutoff_eq, hi.covariance_eq]
        simp only [sourceTransferredFlux, ite_eq_left hA, ite_eq_left hdg]
        rw [diagonal_coefficient_above_order hi t A hA.2.2.1 z d I (hord ▸ hd), smul_zero]
      · simp only [sourceTransferredFlux, ite_eq_left hA, ite_eq_right hdg]
        exact transferAt_above_degree D G.level p.1 _ _ _ t A z d I hd
    · simp only [sourceTransferredFlux, ite_eq_right hA]

/-- One actual-successor producer for the cascade and terminal entry. -/
theorem stage_successor_exists : StageSuccessorExistsStatement := by
  intro hr _ _ D Dm b j₀ P Mn G hi
  obtain ⟨Cc, Cc0, hc⟩ := stage_transfer_fields P Mn G hi
  exact ⟨stageOfFields hi Cc Cc0 hc, stageOfFields_isActualSuccessor hi Cc Cc0 hc⟩

end AVRegularity.Construction.StageSuccessor
end
