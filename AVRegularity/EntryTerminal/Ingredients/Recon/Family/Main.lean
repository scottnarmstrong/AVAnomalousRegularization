-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Finite.WeakLift.IdentitySeparation
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Families.TorusCompatible.WeakStage
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.EntryTerminal.Ingredients.Recon.Family

/-! # The lift partition field

The cutoffs `ocCutoff` over the observed pulses form a lift partition of the window
(`IsLiftPartition`): nonnegative, `C¹`, sum one on the window, supported in the pulse windows, with
derivative bound `C/τ` and derivative supported in the quiet times. -/

/-- **The cutoffs of the observed pulses are a lift partition** of `[t_A, t_Z]`. -/
theorem reconFamily_liftPartition {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) (tA tZ : ℝ) :
    IsLiftPartition (ocObsPulses α q Λ m tA tZ) (fun k => ocCutoff α q Λ m k)
      (ocPulseWindow α q Λ m) (ocQuietTimes α q Λ ζ m) (Set.Icc tA tZ) (ocTau α q Λ m)
      reconCpart := by
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
  have hK := reconCpart_spec.2
  have hodd : ∀ k ∈ ocObsPulses α q Λ m tA tZ, Odd k := fun k hk => by
    classical
    unfold ocObsPulses at hk
    exact (Finset.mem_filter.1 hk).2.1
  refine ⟨fun k _ t => Providers.CascadeInvariants.ocCutoff_nonneg k t, fun k _ => ?_, ?_, ?_, ?_, ?_⟩
  · exact (CycleReference.ocCutoff_contDiff hΛ k).of_le (by exact_mod_cast le_top)
  · intro t ht
    refine Providers.CascadeInvariants.sum_ocCutoff_eq_one hτ _ hodd t fun k hk hne => ?_
    exact Construction.Residual.Presentation.obsPulses_time_subset α q Λ m hτ ht
      (Finite.WeakLift.active_cutoff_mem_obs hτ hk hne)
  · intro k _ t ht
    exact Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ ht
  · intro k _ t
    exact hK α q Λ m hΛ k t
  · intro k hk t hd
    have hkodd := hodd k hk
    have hh := CycleReference.cutoff_derivative_nonzero_distance hΛ k t hd
    rcases le_or_gt 0 (t - (k : ℝ) * ocTau α q Λ m) with hpos | hneg
    · rw [abs_of_nonneg hpos] at hh
      refine CycleComparison.Reconstruction.mem_ocQuietTimes_of_gap hΛ hζ hkodd ?_ ?_ <;>
        nlinarith [hh.1, hh.2]
    · rw [abs_of_neg hneg] at hh
      have hk2 : Odd (k - 2) := hkodd.sub_even even_two
      refine CycleComparison.Reconstruction.mem_ocQuietTimes_of_gap hΛ hζ hk2 ?_ ?_ <;>
        push_cast <;> nlinarith [hh.1, hh.2]

/-- A lift partition depends on the weights only through their values on the set. -/
theorem reconFamily_isLiftPartition_congr {kset : Finset ℤ} {ϖ ϖ' : ℤ → ℝ → ℝ}
    {win : ℤ → Set ℝ} {quiet I : Set ℝ} {τ Cpart : ℝ} (he : ∀ k ∈ kset, ϖ' k = ϖ k)
    (h : IsLiftPartition kset ϖ win quiet I τ Cpart) :
    IsLiftPartition kset ϖ' win quiet I τ Cpart := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun k hk t => ?_, fun k hk => ?_, fun t ht => ?_, fun k hk t => ?_, fun k hk t => ?_,
    fun k hk t => ?_⟩
  · rw [he k hk]; exact h1 k hk t
  · rw [he k hk]; exact h2 k hk
  · rw [Finset.sum_congr rfl fun k hk => by rw [he k hk]]; exact h3 t ht
  · rw [he k hk]; exact h4 k hk t
  · rw [he k hk]; exact h5 k hk t
  · rw [he k hk]; exact h6 k hk t

end AVRegularity.EntryTerminal.Ingredients.Recon.Family
end
end

section
section
/-! # The family side of the window at a context

The ten fields of `ReconFamilyBody` at the actual family of the weak stage, from the stage
invariant of `c.weak` (natural pieces, quiet atlas, fast independence), the torus compatibility of
the weak stage, the preparation (`a_M ≤ t_p`) and the cutoff partition. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Family

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)

/-- **The family side at a context**, for `Λ ≥ 1` and a positive preparation constant `c_P`. -/
theorem reconFamilyAt_of_ctx (hcP : 0 < cP) (hΛ : 1 ≤ A.Λ) (ℓ : ℕ) :
    c.tp < c.a + A.T₀ → ReconFamilyAt c ℓ := by
  intro _
  have hW := c.weak
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, -, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hDΛ ▸ hΛ
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTau_pos hΛ1
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTauPP_pos hΛ1
  have hlev : c.Gw.level = M := hW.2.2.1
  have hdepthW : c.Gw.fam.HasDepthAtMost A.dW := hW.2.2.2.1
  obtain ⟨hnat, -, -, -, -, -, -, -, -, -, ⟨T, hTc, hTv, hTq, hTs, -⟩, -, hfi, -⟩ :=
    hW.2.2.2.2.2.2.2.2.2
  simp only [hlev] at hTv hTq hfi
  have hkap : c.D.kap M = c.D.κ M := by
    unfold OCData.kap
    rw [hterm, min_self]
  rw [hkap] at hTq
  -- the window
  have haM : c.aM ≤ c.tp := by
    have h1 := c.prep.2.1
    have h2 : 0 < cP * c.D.termH M := mul_pos hcP hτ''
    linarith
  have hend : c.tp + rTobs c = c.a + A.T₀ := by unfold rTobs; ring
  have hsub : Set.Icc c.tp (c.tp + rTobs c) ⊆ Set.Icc c.aM (c.a + A.T₀) := by
    intro t ht
    exact ⟨haM.trans ht.1, hend ▸ ht.2⟩
  have hpart := reconFamily_liftPartition (α := c.D.α) (q := c.D.q) (m := M)
    (ζ := c.D.ζ) hΛ1 (hDζ ▸ X.hζ) c.tp (c.tp + rTobs c)
  have hw : ∀ p : OddSlot, c.Gw.actualFamily.weight p = ocCutoff c.D.α c.D.q c.D.Λ M p.1 := by
    intro p
    funext t
    have := hnat.2.1 p t
    simp only [hlev] at this
    exact this
  have hobsodd : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c), Odd k := fun k hk => by
    classical
    unfold ocObsPulses at hk
    exact (Finset.mem_filter.1 hk).2.1
  refine ⟨c.Gw.actualAtlas T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- descent of the slots
    have hmax : ∀ v u (γ : c.Gw.actualFamily.Γ v u),
        (c.Gw.actualFamily.identity v u γ).maxOrder ≤ A.Dt :=
      fun v u γ => (c.Gw.actualFamily.identity v u γ).le_D
    have hd := isDescending_descSlots c.Gw.actualFamily (c.Gw.hasDepthAtMost_actualFamily hdepthW)
      hmax
    intro v u γ
    have := hd v u γ
    show A.k₀ + ℓ + descSlots c.Gw.actualFamily A.dW A.Dt v + _ ≤
      A.k₀ + ℓ + descSlots c.Gw.actualFamily A.dW A.Dt u + 2
    omega
  · exact c.Gw.isTorusCompatible_actualFamily (IsWeakStage.isTorusCompatible hW)
  · exact c.Gw.actualAtlas_isConsecutiveClosed fun p q hpq hlab hne =>
      hTc p q hpq hlab (hne.mono (Set.inter_subset_inter_right _ hsub))
  · exact c.Gw.actualAtlas_coversQuiet fun p q hpq t ht Y =>
      hTv p q hpq t ⟨⟨⟨ht.1.1.1, hsub ht.1.1.2⟩, ht.1.2⟩, ht.2⟩ Y
  · exact c.Gw.actualAtlas_isQuiet hTq
  · intro p q hpq hne
    exact hTs p q hpq (hne.mono (Set.inter_subset_inter_right _ hsub))
  · intro k hk
    have hk' := hobsodd k hk
    obtain ⟨hl, ho, -, -, hm⟩ := hnat.1 (oddSlotOf k)
    rw [oddSlotOf_of_odd hk'] at hl ho hm
    simp only [hlev] at hl ho hm
    rw [oddSlotOf_of_odd hk']
    refine ⟨hl.trans (ocLabel_eq_ocPulseChartIndex _ _ _ _ k hτ''), fun t => ?_, ?_⟩
    · show _ = ocChart c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
        (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k) t
      refine (hm t).trans ?_
      funext y
      unfold ocChart OCData.flowOf OCData.slotAnchor
      rw [ocLabel_eq_ocPulseChartIndex _ _ _ _ k hτ'']
    · show _ ⊆ (c.Gw.fam.piece _).output
      rw [ho]
      exact Set.inter_subset_left
  · exact oddSlotOf_injOn.mono fun k hk => hobsodd k hk
  · refine reconFamily_isLiftPartition_congr (fun k hk => ?_) hpart
    rw [hw, oddSlotOf_of_odd (hobsodd k hk)]
  · exact c.Gw.isFastIndependentOn_actualFamily
      (CycleComparison.isFastIndependentOn_mono c.Gw.fam
        (Set.inter_subset_inter_right _ hsub) hfi)

end AVRegularity.EntryTerminal.Ingredients.Recon.Family
end
end

section
/-! # The family side of the reconstruction window

`termReconFamily` from `reconFamilyAt_of_ctx` through the prefix (a step with `κ = Unit` that holds
at every context with `Λ ≥ 128` and `0 < c_P`). -/

@[expose] public section

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- **The family side of the reconstruction window.** -/
theorem termReconFamily : TermReconFamilyStatement := by
  intro ℓ X
  refine ⟨128, le_rfl, fun A hΛ _ => ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ =>
    ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
      cP CP cHP Cw Ce cker hcP => ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨0, fun M _ c x =>
        fun hd => Family.reconFamilyAt_of_ctx c hcP (by omega) ℓ hd⟩⟩⟩⟩⟩⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
