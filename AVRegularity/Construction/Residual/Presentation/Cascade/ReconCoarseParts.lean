-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Cascade.SeqMain
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncPulsePeriodic
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.EntryTerminal.Ingredients.Recon.Family.Main
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.EntryTerminal.Ingredients.Recon.Setting.Main
import AVRegularity.CycleComparison.LiftSetting.Main
public import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.CycleComparison.Reconstruction.LiftSource

section
section
/-! **The periodic glue of the mean fluxes at a cascade frame** (cascade side of the bill
residual; the frame form of the terminal `covTruncLiftSlow_of_setting` and
`covTruncGluedPeriodic_of_slow`, `EntryTerminal/Ingredients/ResidualFlux/CovTruncGlued*.lean`).

* `frame_liftSlow`: on the window, at every time `t` and every observed pulse `k` with
  nonzero cutoff at `t`, the lift coefficients `CcT k` at the cell time of `t` are invariant under
  the slow lattice shifts `ρ⁻¹ℤ²` (`ρ = √(κ_{m−1}τ''_m)`), from the lift sequences and the lift
  settings of the window (`FrameReconSeqAt`, the first clause of `FrameReconSettingBody`) and the
  torus compatibility of the actual family (`setting_liftSequence_slowShift_invariant`).
* `frame_gluedPeriodic`: hence the glued mean flux of periodic fields is periodic at every
  time of the window, at every degree set and every bounded grade set
  (`CovTruncGluedPeriodicBounded`, the glue asked by the reconstruction defect).

A pulse with zero cutoff contributes a vanishing term, as does an even slot; an empty grade set
is allowed. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The slow periodicity of the lift coefficients of a frame at the observed pulses. -/
def FrameLiftSlow (F : Frame D hr Dm b j₀) : Prop :=
  ∀ t ∈ Set.Icc F.tp F.tf, ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m t t,
    ocCutoff D.α D.q D.Λ F.m k t ≠ 0 →
    ∀ (p : Fin 2 → ℤ) hh, hh ≤ F.depth → ∀ n m (α : DerivativeWord2 m) X z v u,
      F.CcT k hh n m α ((D.cellScaleSq F.m)⁻¹ * t) (X + (fRho F)⁻¹ • latticeShift p) z v u =
        F.CcT k hh n m α ((D.cellScaleSq F.m)⁻¹ * t) X z v u

/-- **The slow periodicity of the lift coefficients from the lift sequences and settings of the
window.** -/
theorem frame_liftSlow (F : Frame D hr Dm b j₀) (law : BirthLaw) {Acl ℓ : ℕ}
    {CGl Cwl : ℕ → ℝ} {Ca Sb Cg : ℝ} {qs qf : ℕ} {par : ℤ → Fin 2} {V : ℤ → ℝ → ℝ → ℝ}
    {bM : CompIn F.G.comps → CompIn F.G.comps → ℝ}
    (hΛ : 1 ≤ D.Λ) (hν : 0 < D.κ F.m) (hm : F.m ≤ D.term)
    (htorus : IsTorusCompatible F.G.actualFamily (fun _ => ()) (ocEpsilon D.q D.Λ (F.m - 1)))
    (hseq : FrameReconSeqAt F Acl ℓ)
    (hset : FrameReconSettingBody F law Acl ℓ CGl Cwl Ca Sb Cg qs qf par V bM) :
    FrameLiftSlow F := by
  classical
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos hΛ
  have hkap : D.kap F.m = D.κ F.m := by unfold OCData.kap; rw [min_eq_left hm]
  have hcs : ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 = D.cellScaleSq F.m := by
    rw [CycleReference.ocEll_sq_eq hν]
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
  have hcell : 0 < ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 := by
    rw [CycleReference.ocEll_sq_eq hν]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ) 2) hν
  intro t ht k hk hcut p hh hhH n m α Y z v u
  have ht' : t ∈ Set.Icc F.tp (F.tp + fTobs F) := by
    have hend : F.tp + fTobs F = F.tf := by unfold fTobs; ring
    rwa [hend]
  have hkobs := obsPulses_time_subset D.α D.q D.Λ F.m hτ ht' hk
  have hwin := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
  have htcell := CycleComparison.Assembly.cellTime_mem_liftWindow hcell hwin ht'
  have P := hset.1 k hkobs
  have hperiod := CycleComparison.LiftMeanEntrywise.setting_liftSequence_slowShift_invariant P
    (wKlift Dm F.depth F.N Acl ℓ + Dm + 2)
    (max (wLlift Dm F.depth F.N ℓ + 1) (wLlift Dm F.depth F.N ℓ + 2))
    (F.CcT k) (hseq k hkobs) ((fRho F)⁻¹ • latticeShift p)
    (fun s Y i j => CycleComparison.Assembly.pulseLiftData_G_shift D.α D.q D.Λ F.m D.ζ
      (D.hΦ (F.m - 1)) (D.κ F.m) (D.κ (F.m - 1)) P.ρ_pos.ne' _ k _ p s Y i j)
    (fun v u d γ hγ α s Y z => CycleComparison.Assembly.liftEdges_fiber_coeff_shift
      P.ρ_pos.ne' htorus (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (oddSlotOf k) p hγ α s Y z)
    hh hhH n m α _ htcell Y z v u
  rw [hcs] at hperiod
  exact hperiod

/-- **The glue at a frame**: the glued mean flux of periodic fields is periodic at every time of
the window, for every degree set and every grade set bounded by the depth. -/
theorem frame_gluedPeriodic (F : Frame D hr Dm b j₀) (hΛ : 1 ≤ D.Λ) (hν : 0 < D.κ F.m)
    (hm : F.m ≤ D.term) (hm1 : 1 ≤ F.m) (hlev : F.G.level = F.m) (hlen : F.Mn.lenFactor = 1)
    (hρ : fRho F ≠ 0)
    (htorus : IsTorusCompatible F.G.fam F.G.actual (D.eps (F.G.level - 1)))
    (hslow : FrameLiftSlow F) :
    ∀ t ∈ Set.Icc F.tp F.tf, ∀ v,
      CovTruncGluedPeriodicBounded F.Mn F.G F.m F.depth F.CcT t v := by
  classical
  have hkap : D.kap F.m = D.κ F.m := by unfold OCData.kap; rw [min_eq_left hm]
  have hcell : 0 < D.cellScaleSq F.m := by
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ) 2) hν
  have hρL : F.Mn.lenFactor * liftLength D F.m = fRho F := by
    rw [hlen, one_mul]
    rfl
  intro t ht v rs ns a hrs hpa p Y
  unfold menuGluedMeanFlux
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun r hr' =>
    Finset.sum_congr rfl fun n _ => ?_
  split_ifs with hodd
  · by_cases hcut : ocCutoff D.α D.q D.Λ F.m k t = 0
    · simp only [hcut, zero_smul]
    · apply congrArg (fun z => ocCutoff D.α D.q D.Λ F.m k t • z)
      rw [hρL]
      have hpulse := covTruncPulse_meanFluxEuler_periodic (D.cellScaleSq F.m) (fRho F)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) hρ hcell.ne'
        (familyLiftData D F.m k (nativeChain F.m k) (fRho F)
          (F.G.fam.fiber ⟨k, hodd⟩ (F.G.actual ⟨k, hodd⟩))) (F.CcT k) F.depth r n (hrs r hr')
        (fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m k))
        (fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m k) y s) a t
        (fun p y => CycleReference.streamFlow_lattice_equivariant (D.hΦ (F.m - 1))
          t (D.slotAnchor F.m k) y p)
        (fun p y => CycleReference.streamFlow_lattice_equivariant (D.hΦ (F.m - 1))
          (D.slotAnchor F.m k) t y p)
        (fun p X i j => congrFun (congrFun
          (Construction.Preservation.FullLift.native_familyLiftData_metric_shift D F.m hm1 k hρ
            (F.G.fam.fiber ⟨k, hodd⟩ (F.G.actual ⟨k, hodd⟩)) p _ X) i) j)
        (fun p v u d γ hγ α X z => by
          have hmem : γ ∈ (familyLiftData D F.G.level k (nativeChain F.G.level k) (fRho F)
              (F.G.fam.fiber ⟨k, hodd⟩ (F.G.actual ⟨k, hodd⟩))).edge v u d := by
            simpa only [hlev] using hγ
          simpa only [hlev] using
            Construction.Preservation.FullLift.native_familyLiftData_edge_coeff_shift F.G htorus
              ⟨k, hodd⟩ hρ p v u d γ hmem α _ X z)
        (fun p hh hhH n m α X z v u => hslow t ht k hk hcut p hh hhH n m α X z v u) hpa v
      exact hpulse p Y
  · rfl

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The family side: the family side of the window at a cascade frame** (cascade side of the bill
residual).

`frameReconFamilyBody`: at a frame whose incoming stage `F.G` carries the stage invariant
on a window `[t_A, t_B] ⊇ [t_p, t_f]`, at a level `F.m ≤ D.term`, the body `FrameReconFamilyBody`
holds at the actual atlas of the atlas of the invariant and the absolute partition constant
`reconCpart`, for every offset `ℓ`. It is the terminal `reconFamilyAt_of_ctx` at a frame:
descending slots from the depth bound, torus compatibility from the invariant, the atlas
clauses restricted to the window, the pieces of the observed pulses from `IsNatural`.

The case `ℓ = 0` is allowed; for a stage without identities `descSlots = 0`; for `t_p = t_f` the
window is a point and the clauses on it are those of the invariant. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.EntryTerminal.Ingredients.Recon.Family
open AVRegularity.EntryWeakProofs

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The family side.** -/
theorem frameReconFamilyBody (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (hφ₀ : Integrable F.φ₀) (Mnat : ℕ) (kI : InvConsts) (tA tB S θK : ℝ)
    (hinv : IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ Mnat kI tA tB S θK F.G)
    (hlev : F.G.level = F.m) (hmt : F.m ≤ D.term) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hdepth : F.G.fam.HasDepthAtMost F.depth) (htA : tA ≤ F.tp) (htB : F.tf ≤ tB) (ℓ : ℕ) :
    ∃ T : F.G.actualFamily.Atlas, FrameReconFamilyBody F ℓ T reconCpart := by
  have hτ'' : 0 < ocTauPP D.α D.q D.Λ F.m := Construction.Stream.ocTauPP_pos hΛ
  have hkap : D.kap F.m = D.κ F.m := by unfold OCData.kap; rw [min_eq_left hmt]
  have hsub : Set.Icc F.tp (F.tp + fTobs F) ⊆ Set.Icc tA tB := by
    intro t ht
    have htf : F.tp + fTobs F = F.tf := by simp only [fTobs]; ring
    exact ⟨htA.trans ht.1, (htf ▸ ht.2).trans htB⟩
  have hinv0 := hinv
  obtain ⟨hnat, -, -, -, -, -, -, -, -, -, ⟨T, hTc, hTv, hTq, hTs, -⟩, -, hfi, -⟩ := hinv
  simp only [hlev] at hTv hTq hfi
  rw [hkap] at hTq
  have hw : ∀ p : OddSlot, F.G.actualFamily.weight p = ocCutoff D.α D.q D.Λ F.m p.1 := by
    intro p
    funext t
    have := hnat.2.1 p t
    simp only [hlev] at this
    exact this
  have hobsodd : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F), Odd k := fun k hk => by
    classical
    unfold ocObsPulses at hk
    exact (Finset.mem_filter.1 hk).2.1
  have hpart := reconFamily_liftPartition (α := D.α) (q := D.q) (m := F.m)
    (ζ := D.ζ) hΛ hζ F.tp (F.tp + fTobs F)
  refine ⟨F.G.actualAtlas T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmax : ∀ v u (γ : F.G.actualFamily.Γ v u),
        (F.G.actualFamily.identity v u γ).maxOrder ≤ Dm :=
      fun v u γ => (F.G.actualFamily.identity v u γ).le_D
    have hd := isDescending_descSlots F.G.actualFamily (F.G.hasDepthAtMost_actualFamily hdepth)
      hmax
    intro v u γ
    have := hd v u γ
    show ℓ + descSlots F.G.actualFamily F.depth Dm v + _ ≤
      ℓ + descSlots F.G.actualFamily F.depth Dm u + 2
    omega
  · have ht := hinv0.isTorusCompatible
    simp only [hlev] at ht
    exact F.G.isTorusCompatible_actualFamily ht
  · exact F.G.actualAtlas_isConsecutiveClosed fun p q hpq hlab hne =>
      hTc p q hpq hlab (hne.mono (Set.inter_subset_inter_right _ hsub))
  · exact F.G.actualAtlas_coversQuiet fun p q hpq t ht Y =>
      hTv p q hpq t ⟨⟨⟨ht.1.1.1, hsub ht.1.1.2⟩, ht.1.2⟩, ht.2⟩ Y
  · exact F.G.actualAtlas_isQuiet hTq
  · intro p q hpq hne
    exact hTs p q hpq (hne.mono (Set.inter_subset_inter_right _ hsub))
  · intro k hk
    have hk' := hobsodd k hk
    obtain ⟨hl, ho, -, -, hm⟩ := hnat.1 (oddSlotOf k)
    rw [oddSlotOf_of_odd hk'] at hl ho hm
    simp only [hlev] at hl ho hm
    rw [oddSlotOf_of_odd hk']
    refine ⟨hl.trans (ocLabel_eq_ocPulseChartIndex _ _ _ _ k hτ''), fun t => ?_, ?_⟩
    · show _ = ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
        (ocPulseChartIndex D.α D.q D.Λ F.m k) t
      refine (hm t).trans ?_
      funext y
      unfold ocChart OCData.flowOf OCData.slotAnchor
      rw [ocLabel_eq_ocPulseChartIndex _ _ _ _ k hτ'']
    · show _ ⊆ (F.G.fam.piece _).output
      rw [ho]
      exact Set.inter_subset_left
  · exact oddSlotOf_injOn.mono fun k hk => hobsodd k hk
  · refine reconFamily_isLiftPartition_congr (fun k hk => ?_) hpart
    rw [hw, oddSlotOf_of_odd (hobsodd k hk)]
  · exact F.G.isFastIndependentOn_actualFamily
      (CycleComparison.isFastIndependentOn_mono F.G.fam
        (Set.inter_subset_inter_right _ hsub) hfi)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The lift setting of an observed pulse on the clipped window at a cascade frame** (cascade
side of the bill residual).

The native setting of the slot (`NativeStageSetting`) gives the setting
`IsLiftSetting (fLiftData F k)` on the clipped window `[fSeqStart, fSeqEnd]`: the data agree (cell
contrast, metric and drift at all times; edges on the output window, which is the pulse window of
the natural stage), the clipped window lies in the native one, and the jet constants and the
price bound are raised. It is the terminal `setting_of_native` at a frame.

If `t_p` lies before the slot start and the deadline after the slot end, the clipped window is
the native one; for `S = S_b` and `C_j ≤ C_a` there is no raise. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation AVRegularity.Construction.Preservation.FullLift
open AVRegularity.EntryWeakProofs AVRegularity.EntryTerminal.Ingredients.Recon.Setting

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The setting of the observed pulse `k` on the clipped window, from its native setting.** -/
theorem setting_of_native' (F : Frame D hr Dm b j₀) (law : BirthLaw)
    {kI : InvConsts} {Mnat : ℕ} (hnat : F.G.IsNatural Mnat) (hcert : F.G.IsContextCertified kI)
    (hlev : F.G.level = F.m) (hΛ : 1 ≤ D.Λ) (hm : 1 ≤ F.m) (hmt : F.m ≤ D.term)
    (hζ : IsFastProfile D.ζ) (hch : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {Ca S Sb : ℝ} {K kk L : ℕ}
    (hCa : ∀ r, r ≤ K + 4 * (F.depth + 1) * (F.N + Dm) ^ 2 → ∀ q,
      q ≤ max kk (L + 2) + F.depth * Dm + 2 * F.N + 2 * Dm → Cj r q ≤ Ca) (hSb : S ≤ Sb)
    {k : ℤ} (hkobs : k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (hset : NativeStageSetting F.G law F.m F.depth F.N K kk L CG Cw Cj S
      ⟨k, CycleComparison.LiftSetting.obsPulse_odd hkobs⟩) :
    IsLiftSetting (fLiftData F k) (F.G.mass law) (fSeqStart F k) (fSeqEnd F k)
      (ocEpsilon D.q D.Λ F.m) (D.κ F.m) (D.κ (F.m - 1)) (fRho F)
      (ocEpsilon D.q D.Λ (F.m - 1)) (ocEll D.q D.Λ F.m (D.κ F.m))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)))
      (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
      (fRho F / ocEpsilon D.q D.Λ (F.m - 1)) (pulseParallel k)
      (pulseShearProfile D.α D.q D.Λ F.m D.ζ (D.κ F.m) k) F.depth F.N K kk L
      (K + 4 * (F.depth + 1) * (F.N + Dm) ^ 2)
      (max kk (L + 2) + F.depth * Dm + 2 * F.N + 2 * Dm) CG Cw
      (fun _ _ => Ca) (recordMajorant (F.G.mass law) F.G.fam) Sb := by
  have hk : Odd k := CycleComparison.LiftSetting.obsPulse_odd hkobs
  have hκM : 0 < D.κ F.m := CycleReference.bandChain_pos hΛ hζ hch hmt
  have hτ'' : 0 < ocTauPP D.α D.q D.Λ F.m := Construction.Stream.ocTauPP_pos hΛ
  have hkap : D.kap F.m = D.κ F.m := by unfold OCData.kap; rw [min_eq_left hmt]
  have hkap1 : D.kap (F.m - 1) = D.κ (F.m - 1) := by
    unfold OCData.kap; rw [min_eq_left ((Nat.sub_le _ _).trans hmt)]
  have hρ : liftLength D F.m = fRho F := rfl
  have hc : ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 = D.cellScaleSq F.m := by
    rw [CycleReference.ocEll_sq_eq hκM]; unfold OCData.cellScaleSq OCData.eps; rw [hkap]
  have hcpos : 0 < D.cellScaleSq F.m := by
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ) 2) hκM
  have hout : ∀ p, (F.G.fam.piece p).output = ocPulseWindow D.α D.q D.Λ F.m p.1 := by
    intro p
    exact (hnat.1 p).2.1.trans (congrArg (ocPulseWindow D.α D.q D.Λ · p.1) hlev)
  have hmeasF : F.G.actualFamily.IsTimeMeasurable :=
    F.G.isTimeMeasurable_actualFamily_of_certified hcert fun p => by rw [hout p, hlev]
  have e2 : (fLiftData F k).edge = liftEdges (D.cellScaleSq F.m)
      (liftLength D F.m / D.eps (F.m - 1)) (F.G.actualFamily.fiber ⟨k, hk⟩ ()) := by
    show liftEdges (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F / ocEpsilon D.q D.Λ (F.m - 1))
      (F.G.actualFamily.fiber (oddSlotOf k) ()) = _
    rw [oddSlotOf_of_odd hk, hc, hρ]
    rfl
  have hset' := hset
  unfold NativeStageSetting at hset'
  have hη : (fLiftData F k).η = (familyLiftData D F.m k (nativeChain F.m k)
      (liftLength D F.m) (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))).η := by
    show D.κ F.m / D.κ (F.m - 1) = D.kap F.m / D.kap (F.m - 1)
    rw [hkap, hkap1]
  have hG : (fLiftData F k).G = (familyLiftData D F.m k (nativeChain F.m k)
      (liftLength D F.m) (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))).G := by
    funext t X' i j
    show _ = (familyLiftData D F.m k (nativeChain F.m k) (liftLength D F.m) _).G t X' i j
    rw [EntryWeakProofs.native_familyLiftData_metric D F.m hm k _ _ t X', hρ]
    show ocMaterialMetric D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k) (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 * t)
      (fRho F • X') i j = _
    unfold ocMaterialMetric ocChart OCData.flowOf OCData.slotAnchor
    rw [hc, ocLabel_eq_ocPulseChartIndex D.α D.q D.Λ F.m k hτ'']
  have hv : (fLiftData F k).v = (familyLiftData D F.m k (nativeChain F.m k)
      (liftLength D F.m) (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))).v := by
    funext t z
    show _ = ocPulseCellDrift D.α D.q D.Λ D.ζ F.m (D.kap F.m) k t z
    rw [hkap]
    rfl
  have hs₀ : D.slotStart F.m k / D.cellScaleSq F.m ≤ fSeqStart F k := by
    show _ ≤ max _ _ / ocEll D.q D.Λ F.m (D.κ F.m) ^ 2
    rw [hc]
    exact div_le_div_of_nonneg_right (le_max_left _ _) hcpos.le
  have hs₁ : fSeqEnd F k ≤ (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m := by
    show min _ _ / ocEll D.q D.Λ F.m (D.κ F.m) ^ 2 ≤ _
    rw [hc]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hcpos.le
  have ht : fSeqStart F k ≤ fSeqEnd F k := CycleComparison.LiftSetting.window (D.κ F.m) hkobs
  have hw : ∀ t ∈ Set.Icc (fSeqStart F k) (fSeqEnd F k),
      D.slotStart F.m k / D.cellScaleSq F.m ≤ t ∧
        t ≤ (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m ∧
        D.cellScaleSq F.m * t ∈ (F.G.fam.piece ⟨k, hk⟩).output := by
    intro t htt
    refine ⟨hs₀.trans htt.1, htt.2.trans hs₁, ?_⟩
    have := (CycleComparison.LiftSetting.mul_mem_pulseWindow_inter
      (by rw [hc]; exact hcpos : 0 < ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) htt).1
    rw [hc] at this
    rw [hout]; exact this
  have hE : EdgeAgree (restrictLiftData Dm le_rfl
        {familyLiftData D F.m k (nativeChain F.m k) (liftLength D F.m)
            (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩)) with
          edge := windowEdges (D.slotStart F.m k / D.cellScaleSq F.m)
            ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / D.cellScaleSq F.m)
            (familyLiftData D F.m k (nativeChain F.m k) (liftLength D F.m)
            (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))).edge}).edge
      (fLiftData F k).edge (fSeqStart F k) (fSeqEnd F k) := by
    rw [e2]
    exact edgeAgree_native_actual F.G ⟨k, hk⟩ (D.cellScaleSq F.m)
      (liftLength D F.m / D.eps (F.m - 1)) _ _ _ _ hw
  have hmeas : ∀ v u d, ∀ γ ∈ (fLiftData F k).edge v u d, ∀ α X z,
      Measurable fun t => γ.coeff α t X z := by
    rw [e2]
    exact actual_liftEdges_coeff_measurable F.G hmeasF ⟨k, hk⟩ (D.cellScaleSq F.m)
      (liftLength D F.m / D.eps (F.m - 1))
  have htr := isLiftSetting_transfer hset' hs₀ ht hs₁ (Q₂ := fLiftData F k) hη hG hv hE hmeas
  have hcg := isLiftSetting_congr_params (e' := ocEpsilon D.q D.Λ F.m)
    (E' := ocEpsilon D.q D.Λ (F.m - 1)) (ℓ' := ocEll D.q D.Λ F.m (D.κ F.m))
    (dstar' := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)))
    (εc' := ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F)
    (lam' := fRho F / ocEpsilon D.q D.Λ (F.m - 1)) htr rfl hkap hkap1 hρ rfl
    (by rw [hkap]; rfl) (by rw [hkap, hkap1]) (by rw [hkap, hkap1, hρ]) (by rw [hρ]; rfl)
  rw [hkap] at hcg
  exact isLiftSetting_mono_const hcg (fun r hr q hq => hCa r hr q hq) hSb

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The window theorem at a cascade frame** (cascade side of the bill residual).

`frameReconBound_of_window`: `ReconWindowAt.physical_lift` at the window `mkFrameReconWindow` of
a cascade frame, followed by the conversion of its output to the reconstruction clause
`ReconBound` at the order `ℓ` and the radius `ρ_s`. It is the terminal `reconBound_of_window` at a
frame; the remaining steps are hypotheses in the terminal forms, at a frame:

* `FrameReconEnergyAt` (E): continuity of `W = P_pZ` and its strong energy at the partition
  order, `≤ C_s·M`;
* `FrameReconCoeffAt`: the drift and the edge coefficients on the window;
* `FrameReconPartitionAt`: the partition terms, `X_p ≤ C_px·𝔅`;
* `FrameReconScaleBody`: the scales and the five dominations by the bill `𝔅`;
* `FrameReconFluxSumBody`: the coarse flux, `B^{-1/2}‖F_c‖ ≤ C_fl·M·𝔱`;
* `FrameReconConvAt` (Conv): from the output of the window theorem to `ReconBound`.

The size `M` (the cascade's `A_in`), the price sum `𝔱` and the bill `𝔅` are parameters: the
assembly of the bill takes `𝔱 = succCovPrice + succFilterPrice + succFrontPrice` and
`𝔅 = succReconBill`. The radius `ρ_s` is a parameter with `0 < ρ_s ≤ ε_m`, `ρ_s ≤ √(Bτ''_m)`
(the bill takes `ρ_s = rhoStar D c₀ m`).

For `M = 0` all bounds are `0`, and for a stage without identities `K ≡ ℓ + D_m·depth` and there
is no edge coefficient. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.CycleComparison.Lift AVRegularity.ChartTransport
open scoped ENNReal

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

omit [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The coarse order of the window is at least the maximal order `D_m` (the order condition
`D_m - 1 ≤ k_c + 2p + 1` of the frontier identification). -/
theorem le_wKcFloor (Dm depth N Acl ℓ : ℕ) : Dm ≤ wKcFloor Dm depth N Acl ℓ := by
  have h := le_max_right (wDens Dm depth N Acl ℓ + wKres Dm depth N Acl ℓ + N + 4)
    (3 * (N + Dm) + 2 * Acl + 16 + wKmax Dm depth ℓ)
  simp only [wKcFloor]
  omega

/-- **Continuity of `W` at a frame**: `W = P_pZ` is continuous on the window and its strong energy at the
slow length and the partition order is at most `C_s·M`. -/
def FrameReconEnergyAt (Acl kc ℓ : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (Cs M : ℝ) : Prop :=
  (∀ v, ContinuousOn (frameReconW F kc hW v) (Set.Icc F.tp (F.tp + fTobs F))) ∧
    strongEnergyUpTo (fRho F) (D.κ (F.m - 1)) (F.G.mass law) F.tp (F.tp + fTobs F)
      (wPord Dm F.depth F.N Acl ℓ) (frameReconW F kc hW) ≤ ENNReal.ofReal (Cs * M)

/-- **The coefficients at a frame**: the drift and the edge coefficients of the window are measurable
and bounded on the window. -/
def FrameReconCoeffAt (ℓ : ℕ) : Prop :=
  ∃ Vb CA : ℝ, 0 ≤ CA ∧
    (∀ s ∈ Set.Ioc F.tp (F.tp + fTobs F), ∀ k,
      AEStronglyMeasurable (fun y => streamVel (D.Φ F.m) s y k)
        (volume.restrict AVenhance.unitCube)) ∧
    (∀ s ∈ Set.Ioc F.tp (F.tp + fTobs F), ∀ y k, |streamVel (D.Φ F.m) s y k| ≤ Vb) ∧
    (∀ s ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ v u d y,
      ‖(edgeCoefficient F.G.actualFamily (D.κ F.m) (ocEpsilon D.q D.Λ F.m)
        (ocEpsilon D.q D.Λ (F.m - 1)) (fun _ => ()) (fK F ℓ)) v u d s y‖ ≤ CA) ∧
    ∀ s ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ v u d,
      AEStronglyMeasurable ((edgeCoefficient F.G.actualFamily (D.κ F.m)
        (ocEpsilon D.q D.Λ F.m) (ocEpsilon D.q D.Λ (F.m - 1)) (fun _ => ()) (fK F ℓ)) v u d s)
        (volume.restrict AVenhance.unitCube)

/-- **The partition terms at a frame**: the partition derivatives of the lifts of the
Galerkin approximants of `W` are bounded by `X_p` times their classical strong energy at the
partition order, with `X_p ≤ C_px·𝔅`. -/
def FrameReconPartitionAt (Acl kc ℓ : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (ρs Cpx bill : ℝ) : Prop :=
  ∃ Xp : ℝ, 0 ≤ Xp ∧ Xp ≤ Cpx * bill ∧
    ∀ n, ∫⁻ t in Set.Icc F.tp (F.tp + fTobs F),
        (∑ j ∈ Finset.range (wKmax Dm F.depth ℓ + 1),
        ∑ w' : DerivativeWord2 j, scalInt (F.G.mass law) (fun y => ρs ^ j •
          orderedDerivative w' (fun y' =>
            ∑ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
              deriv (F.G.actualFamily.weight (oddSlotOf k)) t •
                pulsePhysicalLift (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
                  (ocEpsilon D.q D.Λ F.m)
                  (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) F.N F.depth
                  (F.CcT k)
                  (ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
                    (ocPulseChartIndex D.α D.q D.Λ F.m k))
                  (ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
                    (ocPulseChartIndex D.α D.q D.Λ F.m k))
                  (coarseTraj n (frameReconW F kc hW)) t y') y)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal Xp * classicalStrongEnergy (fRho F) (D.κ (F.m - 1)) (F.G.mass law)
        (Set.Icc F.tp (F.tp + fTobs F)) (wPord Dm F.depth F.N Acl ℓ)
        (coarseTraj n (frameReconW F kc hW))

/-- **The scales at a frame**: the scales of the window and the dominations of the bill `𝔅`
over the five terms of the window's bill, at the price sum `𝔱`. -/
def FrameReconScaleBody (s : ℝ) (Acl : ℕ) (ρs tt bill : ℝ) : Prop :=
  0 < D.α ∧ D.α < 1 / 3 ∧ 0 < s ∧ s < (1 - D.α) / 2 ∧
  IsAdmissibleQ D.α s D.q ∧ IsFastProfile D.ζ ∧ 128 ≤ D.Λ ∧
  IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ ∧ 2 ≤ F.m ∧ 0 < D.κ F.m ∧ 0 < D.κ (F.m - 1) ∧
  0 < ρs ∧ ρs ≤ ocEpsilon D.q D.Λ F.m ∧ ρs ≤ fRho F ∧
  fRho F ≤ ocEpsilon D.q D.Λ (F.m - 1) ∧ 0 ≤ tt ∧
  (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) ^ F.N ≤ bill ∧
  Real.sqrt (D.κ (F.m - 1) / D.κ F.m) * tt ≤ bill ∧
  (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) ^ 2 * tt ≤ bill ∧
  (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) ^ F.N *
      (Real.sqrt (fTobs F) / ocEll D.q D.Λ F.m (D.κ F.m) *
        (ocEpsilon D.q D.Λ F.m / fRho F) ^ Acl) ≤ bill ∧
  (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) ^ 2 *
      (Real.sqrt (fTobs F) / ocEll D.q D.Λ F.m (D.κ F.m) *
        (ocEpsilon D.q D.Λ F.m / fRho F) ^ Acl) * tt ≤ bill

/-- **The coarse flux at a frame**: the coarse flux of the window is a.e. strongly measurable and
`B^{-1/2}‖F_c‖_{L²(I;H_{ρ,k_c;π})} ≤ C_fl·M·𝔱` at the slow length. -/
def FrameReconFluxSumBody (kc : ℕ) (Cfl M tt : ℝ)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) :
    Prop :=
  (∀ v, AEStronglyMeasurable (frameReconFc F F1 F2 F3 v)
    (volume.restrict (Set.Icc F.tp (F.tp + fTobs F)))) ∧
  ENNReal.ofReal (Real.sqrt (D.κ (F.m - 1)))⁻¹ * (∫⁻ s in Set.Icc F.tp (F.tp + fTobs F),
      ENNReal.ofReal (massNormSq (E := fun v : CompIn F.G.comps =>
        PiLp 2 (fun _ : Fin 2 => hr v.1.root)) (K := fun _ => kc) (fRho F)
        (F.G.mass law) (fun v => (frameReconFc F F1 F2 F3 v s).val))) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (Cfl * M * tt)

/-- **Conv at a frame**: from the output of the window theorem (the glued lift, the plain coupled
system at the slots with the edge coefficients of the actual family, the residual at the radius
`ρ_s`) to the reconstruction clause `ReconBound` at the order `ℓ`. -/
def FrameReconConvAt (ℓ : ℕ) (ρs : ℝ) : Prop :=
  F.G.actualFamily.IsDescending (fK F ℓ) →
  ∀ (Xb : ℝ), 0 ≤ Xb →
  ∀ (û : ∀ v : CompIn F.G.comps, ℝ → TorusHk (fK F ℓ v) (hr v.1.root))
    (ŵ : ∀ v : CompIn F.G.comps, ℝ → TorusHk (fK F ℓ v + 1) (hr v.1.root))
    (Rres : ∀ v : CompIn F.G.comps, ℝ →
      TorusHk (fK F ℓ v) (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (qres : ∀ v : CompIn F.G.comps, ℝ → TorusHk (fK F ℓ v) (hr v.1.root)),
    (∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ v,
      (û v t).toFunction.jet (valueIndex2 (fK F ℓ v)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun y => gluedLift (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
          (fun k => F.G.actualFamily.weight (oddSlotOf k))
          (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F) (ocEpsilon D.q D.Λ F.m)
          (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) F.N F.depth F.CcT
          (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
            (ocPulseChartIndex D.α D.q D.Λ F.m k))
          (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
            (ocPulseChartIndex D.α D.q D.Λ F.m k)) F.aRep t y v) →
    IsCoupledWeakSolutionTorus (D.κ F.m) F.tp (F.tp + fTobs F) (streamVel (D.Φ F.m)) Dm
      (fK F ℓ)
      (edgeCoefficient F.G.actualFamily (D.κ F.m) (ocEpsilon D.q D.Λ F.m)
        (ocEpsilon D.q D.Λ (F.m - 1)) (fun _ => ()) (fK F ℓ)) (fun v => û v F.tp) Rres qres û ŵ →
    (∀ v, MemLp (Rres v) 2 (volume.restrict (Set.Icc F.tp (F.tp + fTobs F)))) →
    (∀ v, Integrable (qres v) (volume.restrict (Set.Icc F.tp (F.tp + fTobs F)))) →
    (D.κ F.m)⁻¹ * ∫ s in Set.Icc F.tp (F.tp + fTobs F),
        massNormSq (E := fun v : CompIn F.G.comps => PiLp 2 (fun _ : Fin 2 => hr v.1.root))
          (K := fK F ℓ) ρs (F.G.mass law) (fun v => (Rres v s).val) ≤ Xb ^ 2 →
    ∫ s in Set.Icc F.tp (F.tp + fTobs F),
        Real.sqrt (massNormSq (E := fun v : CompIn F.G.comps => hr v.1.root) (K := fK F ℓ)
          ρs (F.G.mass law) (fun v => (qres v s).val)) ≤ Xb →
    ReconBound F.Mn F.G F.m F.N F.depth ℓ F.CcT F.aRep (F.G.mass law) F.tp F.tf ρs Xb

/-- **The window theorem at a frame** (`ReconWindow.physical_lift` and Conv): the reconstruction
of the lifted field at the order `ℓ` and the radius `ρ_s`, with the bound
`reconBillConst·𝔅·M`. -/
theorem frameReconBound_of_window {s : ℝ} (Acl kc ℓ : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (T : F.G.actualFamily.Atlas) (Cpart : ℝ) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn F.G.comps,
      TorusHk (kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4)) (hr v.1.root))
    (ρs Cfl Cs Cpx M tt bill : ℝ)
    (hfam : FrameReconFamilyBody F ℓ T Cpart) (hseq : FrameReconSeqAt F Acl ℓ)
    (hco : FrameReconCoarseBody F law kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0)
    (hTobs : 0 < fTobs F)
    (o : ReconOrders Dm F.N F.depth (wKlift Dm F.depth F.N Acl ℓ) (wLlift Dm F.depth F.N ℓ) kc Jc
      pc (wR0 Dm F.N kc) (wKmax Dm F.depth ℓ) Acl (wDens Dm F.depth F.N Acl ℓ)
      (wKres Dm F.depth F.N Acl ℓ) (wNchi Dm F.depth F.N Acl ℓ))
    (hSb : 0 ≤ Sb) (hCgr : 0 ≤ Cgr) (hCs : 0 ≤ Cs) (hCpx : 0 ≤ Cpx) (hM : 0 ≤ M)
    (hkc : wDens Dm F.depth F.N Acl ℓ + wKres Dm F.depth F.N Acl ℓ + F.N + 4 ≤ kc)
    (hkp : wPord Dm F.depth F.N Acl ℓ ≤ kc + (F.N + Dm))
    (hset : FrameReconSettingBody F law Acl ℓ CGl Cwl Ca Sb Cgr qs qf par V bM)
    (hR6a : FrameReconEnergyAt F law Acl kc ℓ hW Cs M) (hR6b : FrameReconCoeffAt F ℓ)
    (hR6c : FrameReconPartitionAt F law Acl kc ℓ hW ρs Cpx bill)
    (hsc : FrameReconScaleBody F s Acl ρs tt bill)
    (hfs : FrameReconFluxSumBody F law kc Cfl M tt F1 F2 F3)
    (hConv : FrameReconConvAt F law ℓ ρs) :
    ReconBound F.Mn F.G F.m F.N F.depth ℓ F.CcT F.aRep (F.G.mass law) F.tp F.tf ρs
      (reconBillConst F.depth F.N Dm Acl (wKmax Dm F.depth ℓ) (wDens Dm F.depth F.N Acl ℓ)
        (wKres Dm F.depth F.N Acl ℓ) (wNchi Dm F.depth F.N Acl ℓ) (wKlift Dm F.depth F.N Acl ℓ)
        (wLlift Dm F.depth F.N ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0) (Cpx * Cs) * bill * M) := by
  -- a strongly measurable version `Fc` of the coarse flux
  obtain ⟨hFcm, hY⟩ := hfs
  obtain ⟨Fc, hFc, hFcs⟩ := exists_fluxVersion hFcm
  obtain ⟨hα₀, hα₁, hs₀, hs₁, hq, hζ, hΛ, hΦ, hm, hν, hB, hrs, hrse, hrsρ, hRE, htt, hb1, hb2,
    hb3, hb4, hb5⟩ := hsc
  have w := mkFrameReconWindow F law Acl kc ℓ hW F1 F2 F3 T Cpart qs qf par V bM CGl Cwl Ca Sb
    Cgr aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0 ρs hfam hset hseq hco hα₀ hα₁ hs₀ hs₁ hq hζ hΛ
    hΦ hm hν hB hrs hrse hrsρ hRE hTobs (by omega) Fc hFc
  have hle : F.tp ≤ F.tp + fTobs F := by linarith
  have hFm : ∀ n r', Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc F.tp (F.tp + fTobs F) hle s)) r' :=
    fun n r' => measurable_coarseModeCoeff_comp hFcs
      (continuous_subtype_val.comp continuous_projIcc).measurable n r'
  obtain ⟨hWc, hEn⟩ := hR6a
  obtain ⟨Vb, CA, hCA, hbm, hVb, hAb, hAm⟩ := hR6b
  obtain ⟨Xp, hXp, hXpb, hPB⟩ := hR6c
  have hKmax : ∀ v, fK F ℓ v ≤ wKmax Dm F.depth ℓ := fun v => by
    have := descSlots_le F.G.actualFamily F.depth Dm v
    show ℓ + descSlots F.G.actualFamily F.depth Dm v ≤ ℓ + Dm * F.depth
    omega
  have hKM : ∀ v, fK F ℓ v ≤ kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4) := fun v => by
    have := hKmax v
    simp only [wDens, wKres, wKmax] at hkc this ⊢
    omega
  have hCfl : (0 : ℝ) ≤ max Cfl 0 := le_max_right _ _
  have hY' := (fluxBound_le_of_ae hFc hY).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left Cfl 0) hM) htt))
  obtain ⟨û, ŵ, Rres, qres, hval, hplain, -, -, hRm, hqi, hRb, hqb⟩ :=
    w.physical_lift o hKmax hSb hCgr hset.2 hrs hrse hrsρ hWc hFm
      (fun v => (hFcs v).aestronglyMeasurable) hbm hVb hCA hAb hAm
      (X := Cs * M) (Y := max Cfl 0 * M * tt) (M := M) (tt := tt)
      (bill := bill) (Cs := Cs) (Cy := max Cfl 0) (Cpx := Cpx)
      (mul_nonneg hCs hM) (mul_nonneg (mul_nonneg hCfl hM) htt) hM htt hCs hCfl hCpx
      (ord := wPord Dm F.depth F.N Acl ℓ) (by omega) hXp hPB hEn
      ((strongEnergyUpTo_mono_order (by simp only [wDens, wPord]; omega) _ _ _ _ _ _).trans hEn)
      hY' le_rfl
      le_rfl hXpb hb1 hb2 hb3 hb4 hb5
      (fun _ => kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4)) f0 (fun _ => le_rfl) hKM
      (fun _ => truncateTorusHk_le_refl _)
  have hXb : 0 ≤ reconBillConst F.depth F.N Dm Acl (wKmax Dm F.depth ℓ)
      (wDens Dm F.depth F.N Acl ℓ) (wKres Dm F.depth F.N Acl ℓ) (wNchi Dm F.depth F.N Acl ℓ)
      (wKlift Dm F.depth F.N Acl ℓ) (wLlift Dm F.depth F.N ℓ) CGl Cwl Ca Sb Cgr Cs (max Cfl 0)
      (Cpx * Cs) * bill * M :=
    le_trans (integral_nonneg fun _ => Real.sqrt_nonneg _) hqb
  exact hConv w.hdesc _ hXb û ŵ Rres qres hval hplain hRm hqi hRb hqb

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
section
/-! **`FrameReconAt` from the steps of the reconstruction** (cascade side of the bill residual).

`frameReconAt_of_steps` proves the reconstruction bound at a frame, `FrameReconAt` (from the
three flux bounds, a reconstruction of the lifted field at the order `0` and the radius
`ρ_⋆ = rhoStar D c₀ m` with the bound `C·𝔅_rec·A_in`), from the steps at the frame. It is the
terminal `termReconAt_of_steps` at a frame, at the offset `ℓ = 0`:

* the size is `M = A_in`, the price sum is
  `𝔱 = succCovPrice + succFilterPrice + succFrontPrice`, the bill is `𝔅 = succReconBill`, the
  radius of the window theorem is `ρ_s = rhoStar D c₀ m` (no change of radius at the end);
* `FrameReconCoarseAt` and `FrameReconFluxSumAt` are stated for EVERY triple of
  realizations of the three fluxes, because the realizations come out of the three flux bounds
  only as existentials; the flux bounds are at the radius `rhoEnh D c_r m`, the window's coarse
  flux at the slow length `fRho`: the change of radius (`c_r ≤ 1`) is inside `FrameReconFluxSumAt`;
* the partition step `FrameReconPartitionStepAt` is stated for every window data: its partition
  bound `partition_window_input` is applied to the window of the frame, which contains the coarse
  defect, and its constants are chosen before the frame because the partition constant is the
  absolute `reconCpart`;
* the orders are `frameReconOrders` at any coarse order `k_c ≥ wKcFloor D_m depth N A_cl 0`;
* the scales and the partition are bounded against `C₁·𝔅` with `C₁ > 0` the constant of the band
  chain in `√(κ_{m-1}/κ_m) ≤ C₁E^{-qγ}` (the domination does not hold with
  `C₁ = 1`); the window theorem is linear in its bill, and the factor goes into the final
  constant, `reconBillConst … * C₁ ≤ C`.

**Design note.** The realization and mass clauses of the three flux bounds are named once
(`FrameCovTruncReal`, `FrameFrontierReal`, `FrameFilterReal`) and passed around as these
definitions. Comparing a clause obtained by unfolding `CovTruncBound` with the same clause written
in another declaration is costly: definitions abstract their nested instance proofs into auxiliary
constants, and each such comparison unfolds the instances of `PiLp` many times. So each of
`frameCovTrunc_real`, `frameFrontier_real`, `frameFilter_real` does two such comparisons, and the
assembly does none on the clauses.

For `A_in = 0` the bound is `0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon
open AVRegularity.CycleComparison.Lift AVRegularity.ChartTransport
open scoped ENNReal

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The sum of the three flux prices of the cascade bill. -/
abbrev fTT (cr σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ : ℝ) : ℝ :=
  succCovPrice D F.m cr F.p F.tp F.tf + succFilterPrice D F.G F.m cr σ₀ Lc +
    succFrontPrice D F.m F.η₀ F.J F.H θ₁ θ₂

/-! ### The realizations of the three flux bounds -/

/-- The realization and mass clauses of `FrameCovTruncAt` for a given trajectory. -/
def FrameCovTruncReal (kc : ℕ) (cr Ain C : ℝ)
    (F1 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) :
    Prop :=
  IsFluxRealization (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) kc (Set.Icc F.tp F.tf)
      (fun v t y => toFluxL (menuCovTruncFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y))
      F1 ∧
    FluxMassLe (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) (K := fun _ => kc)
      (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law) (Set.Icc F.tp F.tf) F1
      (C * succCovPrice D F.m cr F.p F.tp F.tf * Ain)

/-- The realization and mass clauses of `FrameFrontierAt` for a given trajectory. -/
def FrameFrontierReal (kc : ℕ) (cr θ₁ θ₂ Ain C : ℝ)
    (F2 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) :
    Prop :=
  IsFluxRealization (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) kc (Set.Icc F.tp F.tf)
      (fun v t y => toFluxL (menuFrontierFlux F.Mn F.P F.seedK F.freshK F.φ₀ F.G F.G' F.Gr F.m
        F.p F.H F.J (D.eps (F.m - 1)) F.η₀ F.aY v t y)) F2 ∧
    FluxMassLe (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) (K := fun _ => kc)
      (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law) (Set.Icc F.tp F.tf) F2
      (C * succFrontPrice D F.m F.η₀ F.J F.H θ₁ θ₂ * Ain)

/-- The realization and mass clauses of `FrameFilterAt` for a given trajectory. -/
def FrameFilterReal (kc : ℕ) (cr σ₀ : ℝ) (Lc : ℕ) (Ain C : ℝ)
    (F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) :
    Prop :=
  IsFluxRealization (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) kc (Set.Icc F.tp F.tf)
      (fun v t y => toFluxL (menuFilterFlux F.Mn F.P F.seedK F.freshK F.φ₀ F.G F.G' F.m F.p
        (D.eps (F.m - 1)) F.η₀ F.aZ v t y)) F3 ∧
    FluxMassLe (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) (K := fun _ => kc)
      (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law) (Set.Icc F.tp F.tf) F3
      (C * succFilterPrice D F.G F.m cr σ₀ Lc * Ain)

/-- `FrameCovTruncAt` gives a realization with its mass clause. -/
theorem frameCovTrunc_real {kc : ℕ} {cr Ain C : ℝ} (h : FrameCovTruncAt F law kc cr Ain C) :
    ∃ F1, FrameCovTruncReal F law kc cr Ain C F1 := by
  obtain ⟨F1, h1, h2⟩ := h
  exact ⟨F1, h1, h2⟩

/-- `FrameFrontierAt` gives a realization with its mass clause. -/
theorem frameFrontier_real {kc : ℕ} {cr θ₁ θ₂ Ain C : ℝ}
    (h : FrameFrontierAt F law kc cr θ₁ θ₂ Ain C) :
    ∃ F2, FrameFrontierReal F law kc cr θ₁ θ₂ Ain C F2 := by
  obtain ⟨F2, h1, h2⟩ := h
  exact ⟨F2, h1, h2⟩

/-- `FrameFilterAt` gives a realization with its mass clause. -/
theorem frameFilter_real {kc : ℕ} {cr σ₀ : ℝ} {Lc : ℕ} {Ain C : ℝ}
    (h : FrameFilterAt F law kc cr σ₀ Lc Ain C) :
    ∃ F3, FrameFilterReal F law kc cr σ₀ Lc Ain C F3 := by
  obtain ⟨F3, h1, h2⟩ := h
  exact ⟨F3, h1, h2⟩

/-! ### The steps that take the realizations -/

/-- **The coarse side of the window at a frame**: for every triple of realizations of the three fluxes with
their mass clauses (the first conjunct of a mass clause is the square integrability in time),
with the continuity of `W`, the lift sequences and a lift setting of the window, the coarse side
of the window at some coarse data. -/
def FrameReconCoarseAt (Acl kc ℓ : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (cr σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ Ain Cfl : ℝ) (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) : Prop :=
  ∀ (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))),
    FrameCovTruncReal F law kc cr Ain Cfl F1 →
    FrameFrontierReal F law kc cr θ₁ θ₂ Ain Cfl F2 →
    FrameFilterReal F law kc cr σ₀ Lc Ain Cfl F3 →
    (∀ v, ContinuousOn (frameReconW F kc hW v) (Set.Icc F.tp (F.tp + fTobs F))) →
    FrameReconSeqAt F Acl ℓ →
    (∃ (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
      (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ),
      FrameReconSettingBody F law Acl ℓ CGl Cwl Ca Sb Cgr qs qf par V bM) →
    ∃ (aC B₀C lamC : ℝ) (pc Jc : ℕ)
      (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
      (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
        (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
          (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
      (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
      (f0 : ∀ v : CompIn F.G.comps,
        TorusHk (kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4)) (hr v.1.root)),
      FrameReconCoarseBody F law kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0

/-- **The coarse flux bound at a frame**: for every triple of realizations with the three mass
clauses at the radius `rhoEnh D c_r m` and the constant `C_fl`, the coarse flux of the window is
bounded at the slow length by `C_fs·A_in·𝔱` (Minkowski and the change of radius `c_r ≤ 1`). -/
def FrameReconFluxSumAt (kc : ℕ) (cr σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ Ain Cfl Cfs : ℝ) : Prop :=
  ∀ (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))),
    FrameCovTruncReal F law kc cr Ain Cfl F1 →
    FrameFrontierReal F law kc cr θ₁ θ₂ Ain Cfl F2 →
    FrameFilterReal F law kc cr σ₀ Lc Ain Cfl F3 →
    FrameReconFluxSumBody F law kc Cfs Ain (fTT F cr σ₀ Lc θ₁ θ₂) F1 F2 F3

/-- **The partition step at a frame**: the partition terms for every window data of the frame
(realizations of the fluxes, an atlas at the absolute partition constant `reconCpart`, a lift
setting, the lift sequences, a coarse body). The partition bound `partition_window_input` is
applied to the window of the frame, which contains the coarse defect, so the step comes after the
realizations. -/
def FrameReconPartitionStepAt (Acl kc : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (ρs Cpx : ℝ) (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr bill : ℝ) : Prop :=
  ∀ (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (T : F.G.actualFamily.Atlas) (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
    (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ) (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn F.G.comps,
      TorusHk (kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4)) (hr v.1.root)),
    FrameReconFamilyBody F 0 T reconCpart →
    FrameReconSettingBody F law Acl 0 CGl Cwl Ca Sb Cgr qs qf par V bM →
    FrameReconSeqAt F Acl 0 →
    FrameReconCoarseBody F law kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0 →
    FrameReconPartitionAt F law Acl kc 0 hW ρs Cpx bill

/-! ### The assembly -/

/-- The reconstruction bound from the coarse side and the flux sum at given realizations. -/
theorem frameReconBound_of_coarse {s : ℝ} (Acl kc : ℕ) (c₀ cr c σ₀ : ℝ) (Lc : ℕ)
    (θ₁ θ₂ Ain C C₁ : ℝ) (hC₁ : 0 < C₁) (hD2 : 2 ≤ Dm) (hN1 : 1 ≤ F.N) (hA1 : 1 ≤ Acl)
    (hkc : wKcFloor Dm F.depth F.N Acl 0 ≤ kc)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p) (hTobs : 0 < fTobs F) (hAin : 0 ≤ Ain)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr Cs Cpx Cfs : ℝ) (hSb : 0 ≤ Sb) (hCgr : 0 ≤ Cgr)
    (hCs : 0 ≤ Cs) (hCpx : 0 ≤ Cpx)
    (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (T : F.G.actualFamily.Atlas) (Cpart : ℝ) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ)
    (aC B₀C lamC : ℝ) (pc Jc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn F.G.comps,
      TorusHk (kc + (Jc + F.depth + 3) * ((F.N + Dm) + 8 * pc + 4)) (hr v.1.root))
    (hR2 : FrameReconSeqAt F Acl 0)
    (hset : FrameReconSettingBody F law Acl 0 CGl Cwl Ca Sb Cgr qs qf par V bM)
    (hfam : FrameReconFamilyBody F 0 T Cpart)
    (hco : FrameReconCoarseBody F law kc hW F1 F2 F3 aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0)
    (hR6a : FrameReconEnergyAt F law Acl kc 0 hW Cs Ain) (hR6b : FrameReconCoeffAt F 0)
    (hR6c : FrameReconPartitionAt F law Acl kc 0 hW (rhoStar D c₀ F.m) Cpx
      (C₁ * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂))
    (hR6d : FrameReconScaleBody F s Acl (rhoStar D c₀ F.m) (fTT F cr σ₀ Lc θ₁ θ₂)
      (C₁ * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂))
    (hfs : FrameReconFluxSumBody F law kc Cfs Ain (fTT F cr σ₀ Lc θ₁ θ₂) F1 F2 F3)
    (hConv : FrameReconConvAt F law 0 (rhoStar D c₀ F.m))
    (hC : reconBillConst F.depth F.N Dm Acl (wKmax Dm F.depth 0) (wDens Dm F.depth F.N Acl 0)
      (wKres Dm F.depth F.N Acl 0) (wNchi Dm F.depth F.N Acl 0) (wKlift Dm F.depth F.N Acl 0)
      (wLlift Dm F.depth F.N 0) CGl Cwl Ca Sb Cgr Cs (max Cfs 0) (Cpx * Cs) * C₁ ≤ C) :
    ReconBound F.Mn F.G F.m F.N F.depth 0 F.CcT F.aRep (F.G.mass law) F.tp F.tf
      (rhoStar D c₀ F.m)
      (C * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂ * Ain) := by
  obtain ⟨o, hkp⟩ := frameReconOrders (ℓ := 0) Jc pc hD2 hN1 hA1 hkc
  have hkc' : wDens Dm F.depth F.N Acl 0 + wKres Dm F.depth F.N Acl 0 + F.N + 4 ≤ kc :=
    le_trans (le_max_left _ _) hkc
  have hb := frameReconBound_of_window F law (s := s) Acl kc 0 hW F1 F2 F3 T Cpart qs qf par V bM
    CGl Cwl Ca Sb Cgr aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0 (rhoStar D c₀ F.m) Cfs Cs Cpx Ain
    (fTT F cr σ₀ Lc θ₁ θ₂)
    (C₁ * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂)
    hfam hR2 hco hTobs o hSb hCgr hCs hCpx hAin hkc' hkp hset hR6a hR6b hR6c hR6d hfs hConv
  have hbill₁ : 0 ≤ C₁ *
      succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂ :=
    le_trans (mul_nonneg (Real.sqrt_nonneg _) hR6d.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      hR6d.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbill : 0 ≤ succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂ :=
    nonneg_of_mul_nonneg_right hbill₁ hC₁
  refine reconBound_mono ?_ hb
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hbill) hAin

/-- **The reconstruction bound at a frame from the steps.** -/
theorem frameReconAt_of_steps {s : ℝ} (Acl kc : ℕ) (c₀ cr c σ₀ : ℝ) (Lc : ℕ)
    (θ₁ θ₂ Ain Cfl C C₁ : ℝ) (hC₁ : 0 < C₁) (hD2 : 2 ≤ Dm) (hN1 : 1 ≤ F.N) (hA1 : 1 ≤ Acl)
    (hkc : wKcFloor Dm F.depth F.N Acl 0 ≤ kc)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p) (hTobs : 0 < fTobs F) (hAin : 0 ≤ Ain)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr Cs Cpx Cfs : ℝ) (hSb : 0 ≤ Sb) (hCgr : 0 ≤ Cgr)
    (hCs : 0 ≤ Cs) (hCpx : 0 ≤ Cpx)
    (hR2 : FrameReconSeqAt F Acl 0)
    (hR3 : ∃ (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
      (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ),
      FrameReconSettingBody F law Acl 0 CGl Cwl Ca Sb Cgr qs qf par V bM)
    (hR4 : ∃ T : F.G.actualFamily.Atlas, FrameReconFamilyBody F 0 T reconCpart)
    (hR5 : FrameReconCoarseAt F law Acl kc 0 hW cr σ₀ Lc θ₁ θ₂ Ain Cfl CGl Cwl Ca Sb Cgr)
    (hR6a : FrameReconEnergyAt F law Acl kc 0 hW Cs Ain) (hR6b : FrameReconCoeffAt F 0)
    (hR6c : FrameReconPartitionStepAt F law Acl kc hW (rhoStar D c₀ F.m) Cpx CGl Cwl Ca Sb Cgr
      (C₁ * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂))
    (hR6d : FrameReconScaleBody F s Acl (rhoStar D c₀ F.m) (fTT F cr σ₀ Lc θ₁ θ₂)
      (C₁ * succReconBill D F.G F.m cr c σ₀ F.η₀ F.p F.N Lc Acl F.J F.H F.tp F.tf θ₁ θ₂))
    (hR6e : FrameReconFluxSumAt F law kc cr σ₀ Lc θ₁ θ₂ Ain Cfl Cfs)
    (hConv : FrameReconConvAt F law 0 (rhoStar D c₀ F.m))
    (hC : reconBillConst F.depth F.N Dm Acl (wKmax Dm F.depth 0) (wDens Dm F.depth F.N Acl 0)
      (wKres Dm F.depth F.N Acl 0) (wNchi Dm F.depth F.N Acl 0) (wKlift Dm F.depth F.N Acl 0)
      (wLlift Dm F.depth F.N 0) CGl Cwl Ca Sb Cgr Cs (max Cfs 0) (Cpx * Cs) * C₁ ≤ C) :
    FrameReconAt F law kc c₀ cr c σ₀ Lc Acl θ₁ θ₂ Ain Cfl C := by
  intro h2a h2b h3
  obtain ⟨F1, hF1⟩ := frameCovTrunc_real F law h2a
  obtain ⟨F2, hF2⟩ := frameFrontier_real F law h2b
  obtain ⟨F3, hF3⟩ := frameFilter_real F law h3
  obtain ⟨qs, qf, par, V, bM, hset⟩ := hR3
  obtain ⟨T, hfam⟩ := hR4
  obtain ⟨aC, B₀C, lamC, pc, Jc, AD, CE, Aedge, Cstar, Θc, f0, hco⟩ :=
    hR5 F1 F2 F3 hF1 hF2 hF3 hR6a.1 hR2 ⟨qs, qf, par, V, bM, hset⟩
  have hfs := hR6e F1 F2 F3 hF1 hF2 hF3
  exact frameReconBound_of_coarse F law (s := s) Acl kc c₀ cr c σ₀ Lc θ₁ θ₂ Ain C C₁ hC₁ hD2 hN1
    hA1 hkc
    hW hTobs hAin CGl Cwl Ca Sb Cgr Cs Cpx Cfs hSb hCgr hCs hCpx F1 F2 F3 T reconCpart qs qf par
    V bM aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0 hR2 hset hfam hco hR6a hR6b
    (hR6c F1 F2 F3 T qs qf par V bM aC B₀C lamC pc Jc AD CE Aedge Cstar Θc f0 hfam hset hR2 hco)
    hR6d hfs hConv hC

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end

section
/-! **The coarse side of the window at a frame, split in its parts** (cascade side of the bill
residual, the cascade form of the terminal coarse side of the module
`EntryTerminal.Ingredients.Recon.Coarse`).

`FrameReconCoarseAt` is the coarse side of the window. As at
the terminal level it has three parts:

* the coarse equation of `P_pZ`, i.e. `F.macroWeak` (the covariance leaf; a
  hypothesis here);
* the letters (`FrameReconLettersAt`): letters `(AD, CE)` presenting the glued means of the window
  (`IsMeanPresentation` for every grade `r ≤ depth`) with the coarse setting (`IsCoarseSetting`)
  at the degree `p_c = 1` and the word length `J_c = 0`; the cascade form of the terminal
  `termReconLetters`;
* the conversion to the coarse defect (`FrameReconDefectConvAt`): from `F.macroWeak`, the three flux realizations, the
  continuity of `W`, the lift sequences, a lift setting and letters, the coarse defect of the
  window with `f₀ = P_pZ(t_p)` truncated to `N_c = k_c + (depth + 3)(N + D_m + 12)`; the cascade
  form of the terminal `termReconDefectConv`.

`frameReconCoarse_of_parts`: `FrameReconCoarseAt` from the three parts, with the order `N_c + 2p ≤ N_aux`
(covered by the reconstruction order floor at `k_c = succKc`: `windowOrders_of_succReconFloor`).

For `p = 0` one has `P_p = I`; for a stage without identities `CE = 0`; for `depth = 0` there is
one grade and `r = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients

namespace AVRegularity.Construction.Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The initial order of the coarse defect at `p_c = 1`, `J_c = 0`. -/
abbrev fNc (kc : ℕ) : ℕ := kc + (0 + F.depth + 3) * ((F.N + Dm) + 8 * 1 + 4)

/-- **The letters of the window at given data** (the body of `FrameReconLettersAt`): the coarse setting at
`p_c = 1`, `J_c = 0` and the mean presentations of the window's glued means. -/
def FrameReconLettersBody (kc : ℕ) (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ) : Prop :=
  IsCoarseSetting F.tp (F.tp + fTobs F) (fRho F) (D.κ (F.m - 1)) aC B₀C lamC
    (streamVel (D.Φ (F.m - 1))) (F.N + Dm) F.depth 1 0 kc ((F.N + Dm) + 8 * 1 + 4) (fNc F kc)
    (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m)) AD CE (F.G.mass law) Aedge Cstar Θc ∧
  ∀ r ∈ Finset.range (F.depth + 1),
    IsMeanPresentation (Set.Icc F.tp (F.tp + fTobs F)) (F.N + Dm) r AD CE
      (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
      (gluedMean (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
        (fun k => F.G.actualFamily.weight (oddSlotOf k))
        (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) F.N r
        (fun k => fLiftData F k) F.CcT
        (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
          (ocPulseChartIndex D.α D.q D.Λ F.m k))
        (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
          (ocPulseChartIndex D.α D.q D.Λ F.m k)))

/-- **Letters for the window at a frame** (the cascade form of the terminal `ReconLettersAt`). -/
def FrameReconLettersAt (kc : ℕ) : Prop :=
  ∃ (aC B₀C lamC : ℝ)
    (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ),
    FrameReconLettersBody F law kc aC B₀C lamC AD CE Aedge Cstar Θc

/-- **The conversion to the coarse defect** (the cascade form of the terminal
`ReconDefectConvAt`). From the coarse equation of `P_pZ` (`F.macroWeak`), the three flux
realizations with their mass clauses, the continuity of `W`, the lift sequences, a lift setting
and letters presenting the glued means, the coarse defect of the window holds with
`f₀ = P_pZ(t_p)` truncated to the order `N_c`. -/
def FrameReconDefectConvAt (Acl kc ℓ : ℕ) (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hf : fNc F kc ≤ F.Naux - 2 * F.p) (cr σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ Ain Cfl : ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) : Prop :=
  F.macroWeak →
  ∀ (F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))),
    FrameCovTruncReal F law kc cr Ain Cfl F1 →
    FrameFrontierReal F law kc cr θ₁ θ₂ Ain Cfl F2 →
    FrameFilterReal F law kc cr σ₀ Lc Ain Cfl F3 →
    (∀ v, ContinuousOn (frameReconW F kc hW v) (Set.Icc F.tp (F.tp + fTobs F))) →
    FrameReconSeqAt F Acl ℓ →
    (∃ (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
      (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ),
      FrameReconSettingBody F law Acl ℓ CGl Cwl Ca Sb Cgr qs qf par V bM) →
    ∀ (aC B₀C lamC : ℝ)
      (AD : ∀ d : Finset.Icc 2 (F.N + Dm), ℝ → Vec 2 →
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
      (CE : ℕ → ∀ (v u : CompIn F.G.comps) (d : Finset.Icc 2 (F.N + Dm)), ℝ → Vec 2 →
        (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
          (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
      (Aedge : Matrix (CompIn F.G.comps) (CompIn F.G.comps) ℝ) (Cstar Θc : ℝ),
      FrameReconLettersBody F law kc aC B₀C lamC AD CE Aedge Cstar Θc →
      IsCoarseDefect F.tp (F.tp + fTobs F) (D.κ (F.m - 1)) (streamVel (D.Φ (F.m - 1)))
        (F.N + Dm) F.depth kc (fNc F kc) AD CE (ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m))
        (fun v => truncateTorusHk hf (F.PZ v F.tp)) (frameReconW F kc hW)
        (frameReconFc F F1 F2 F3)

/-- **The coarse side of the window at a frame, from its parts.** -/
theorem frameReconCoarse_of_parts {Acl kc ℓ : ℕ} {hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p}
    (hf : fNc F kc ≤ F.Naux - 2 * F.p) {cr σ₀ : ℝ} {Lc : ℕ} {θ₁ θ₂ Ain Cfl : ℝ}
    {CGl Cwl : ℕ → ℝ} {Ca Sb Cgr : ℝ} (hmacro : F.macroWeak)
    (hL : FrameReconLettersAt F law kc)
    (hD : FrameReconDefectConvAt F law Acl kc ℓ hW hf cr σ₀ Lc θ₁ θ₂ Ain Cfl CGl Cwl Ca Sb Cgr) :
    FrameReconCoarseAt F law Acl kc ℓ hW cr σ₀ Lc θ₁ θ₂ Ain Cfl CGl Cwl Ca Sb Cgr := by
  intro F1 F2 F3 h1 h2 h3 hc hseq hset
  obtain ⟨aC, B₀C, lamC, AD, CE, Aedge, Cstar, Θc, hlet⟩ := hL
  exact ⟨aC, B₀C, lamC, 1, 0, AD, CE, Aedge, Cstar, Θc,
    fun v => truncateTorusHk hf (F.PZ v F.tp), hlet.1,
    hD hmacro F1 F2 F3 h1 h2 h3 hc hseq hset aC B₀C lamC AD CE Aedge Cstar Θc hlet, hlet.2⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
