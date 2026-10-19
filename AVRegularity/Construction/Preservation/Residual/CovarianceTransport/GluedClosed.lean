-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.CascadeAdapterInput
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Proofs.CascadeInvariants.ReserveGrade
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble

section
section
/-! Cascade adapter: admissible kernels of the FULL actual successor `G'`, from the fresh
bounded axes and the inherited kernel key property (`successor_kernel_admissibility` exports only the retained part). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

/-- Every kernel of the outgoing family is admissible with the invariant constants. -/
def cascadeAdapterKernelClause : CascadeAdapterClause :=
  fun P _ seedK freshK kI _ G' =>
    ∀ v u (γ : G'.fam.Γ v u), (G'.kernelOf P seedK freshK v u γ).IsAdmissible kI.Γk kI.Lker

/-- Fresh bounded axes and the inherited kernel key property, for the full successor. -/
theorem cascadeAdapter_kernels (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    CascadeAdapterStatement α s q ζ cascadeAdapterKernelClause := by
  classical
  obtain ⟨Λ₀, hΛ₀, haxes⟩ := FullLift.uniform_fresh_axes_norm_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  have h128 := hΛ₀.trans hΛ
  obtain ⟨Γ, _hΓ, ma, hma, haxes⟩ := haxes Λ hΛ
  obtain ⟨mi, _hmi, hinv⟩ := FullLift.uniform_fresh_spanning_inverse_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ h128
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  let thr : InvConsts := { kS with Γk := max Γ 2 }
  refine ⟨thr, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hkI
  have hΓ : Γ ≤ kI.Γk := (le_max_left _ _).trans hkI.2.2.2.1
  have htwo : 2 ≤ kI.Γk := (le_max_right _ _).trans hkI.2.2.2.1
  have hnk : 1 ≤ nk := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn⟩ := hsched
    exact hn
  have horder : kI.Lker + 1 ≤ 2 * nk := hkI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart
  refine ⟨max ma mi, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    G G' hcascade hlevel hGex hactual
  obtain ⟨tA, htA, hG⟩ := hGex
  have hm2 : 2 ≤ m := by omega
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hspec := hfresh (m - 1) (by omega) (by omega)
  have hupper := haxes D hDα hDq hDΛ hDζ hseq hbandD (m - 1) (by omega) (by omega) (freshK (m - 1)) hspec.2.2
  have hinverse := hinv D hDα hDq hDΛ hDζ hseq hbandD (m - 1) (by omega) (by omega) (freshK (m - 1)) hspec.2.2
  have hmeas := FullLift.fresh_axes_measurable D (m - 1) (by rw [hDΛ]; omega)
    (freshK (m - 1)).H₁ (freshK (m - 1)).H₂ hspec.2.2
  have hnew : (freshK (m - 1)).IsAdmissible kI.Γk kI.Lker := by
    refine ⟨hmeas.1, hmeas.2, ?_, ?_⟩
    · intro t
      exact ⟨(hupper t).1.trans hΓ, (hupper t).2.trans hΓ,
        (hinverse t).1, (hinverse t).2.trans htwo⟩
    · rw [hspec.2.1]
      have hval : (nk.toPNat' : ℕ) = nk := by
        change nk - 1 + 1 = nk
        omega
      simpa only [hval] using horder
  let lookup : KernelKey → KernelSpec := fun key => match key with
    | .seed i => seedK i
    | .fresh i => freshK i
  have hall := FullLift.actual_successor_kernel_key_property _ _ G G' hactual
    (fun key => (lookup key).IsAdmissible kI.Γk kI.Lker)
    (fun v u γ => (hG.2.2.2.2.2.2.2.2.1 v u γ).1)
    (by simpa only [hlevel, lookup] using hnew)
  intro v u γ
  exact hall v u γ

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Cascade adapter: the qualitative native input of the literal cascade frame, in the
uniform choice order of the covariance-transport statement. No PDE estimate is proved: the
certificates come from the context and ledger results, the numeric reserves from the schedule. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

/-- Moment order zero is implied by any moment order. -/
theorem cascadeAdapter_admissible_zero {S : KernelSpec} {Γ : ℝ} {L : ℕ}
    (h : S.IsAdmissible Γ L) : S.IsAdmissible Γ 0 := by
  obtain ⟨a, b, c, d⟩ := h
  exact ⟨a, b, c, by omega⟩

/-- The schedule gives the second order at the previous level. -/
theorem cascadeAdapter_sched_two (D₀ N p H : ℕ) (hH : 1 ≤ H) : 2 ≤ succSchedD D₀ N p H := by
  obtain ⟨H', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : H ≠ 0)
  show 2 ≤ succSchedD D₀ N p H' + 2 * N + 4 * p + 4
  omega

/-- The three uniform clauses, with common thresholds. -/
theorem cascadeAdapter_clauses (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    CascadeAdapterStatement α s q ζ (fun P Mn seedK freshK kI G G' =>
      (cascadeAdapterInputClause P Mn seedK freshK kI G G' ∧
        cascadeAdapterContextClause P Mn seedK freshK kI G G') ∧
      cascadeAdapterKernelClause P Mn seedK freshK kI G G') :=
  cascadeAdapter_and
    (cascadeAdapter_and (cascadeAdapter_input (Construction.StageSuccessor.cascade_successor_inputs α s q ζ hζ))
      (cascadeAdapter_context α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ))
    (cascadeAdapter_kernels α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! Cascade adapter: the qualitative native inputs of the literal cascade frame. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

/-- **Cascade adapter.** Native inputs for every literal cascade frame, in the uniform choice
order of `CovarianceTransportProductionStatement`. -/
theorem cascadeNativeInputsProduction (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    CascadeNativeInputsProductionStatement α s q ζ := by
  classical
  obtain ⟨Λ₀, h128, hAD⟩ := cascadeAdapter_clauses α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, h128, fun Λ hΛ => ?_⟩
  obtain ⟨c, hc, hAD⟩ := hAD Λ hΛ
  refine ⟨c, hc, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hAD⟩ := hAD φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  have hΛ1 : 1 ≤ Λ := by omega
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos hΛ1) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos hΛ1).le
  refine ⟨thr, CH, max Υ 1, hCH, lt_of_lt_of_le hΥ (le_max_left _ _), fun kI hkI => ?_⟩
  obtain ⟨CIt, Cwt, hAD⟩ := hAD kI hkI
  refine ⟨CIt, Cwt, fun CI Cw j₀ hledger hstart => ?_⟩
  obtain ⟨mS, hAD⟩ := hAD CI Cw j₀ hledger (IsCarrierStart.mono hA hT le_rfl (le_max_left _ _)
    (zero_le_one.trans hCH) hΥ.le hstart)
  have hHprod : kI.Hprod = kI.G0 + H + 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hHprod, -⟩ := id hkI
    exact hHprod
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -, hH1, -⟩ := hsched
  have hd2 := cascadeAdapter_sched_two D₀ N p H hH1
  intro CQ Cpr
  refine ⟨mS, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hs1 hs2 hT0
    G G' hcas hlev hG hact tp Preg hprep f Ain hf Y0 Y Yw Yk htrace hsol
    CcT PZ aRep û hlift aZ aY hZ hY
  obtain ⟨⟨hin, hcert, hres⟩, hker⟩ := hAD D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law
    hlaw seedK freshK hfresh seed n tS tf hseed m hm hn hnM G G' hcas hlev ⟨tA, htA, hG⟩ hact
  have hgrade := Providers.CascadeInvariants.grade_le_of_cascade hseed.2.1 hcas
  have hdm : max (N + 2) (2 * p) ≤ max (N + succSchedD D₀ N p H) (2 * p) :=
    max_le_max (by omega) le_rfl
  have hlevD : G.level = m := hlev
  refine ⟨{
    stage := hin
    actual := hact
    retained := rfl
    level := hlev
    generated := hG.2.2.1
    shift := hG.2.2.2.1
    depth := Providers.CascadeInvariants.cascade_depth_of_generatedSeed hseed hcas
    incoming_context := ⟨kI, hG.2.2.2.2.2.1, fun v =>
      Providers.CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hHprod
        ((hgrade v).trans (Nat.le_succ _))⟩
    outgoing_context := ⟨kI, hcert, hres⟩
    menuN := rfl
    menup := rfl
    menuH := rfl
    menuJ := rfl
    menuEta := rfl
    menuSlow := rfl
    menuFast := rfl
    window := by
      have h1 := hprep.2.2.1
      rw [hDα, hDq, hDΛ, hlevD] at h1
      linarith
    carrier_start := fun k hk => by
      have h1 := hstart.1 k hk
      have hAk := hA k
      have hTk := hT (k + 1)
      have hAT : 0 ≤ ocA α q Λ k * ocTauPP α q Λ (k + 1) := mul_nonneg hAk hTk
      have hY : 1 ≤ max Υ 1 * CH := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hCH
      rw [hDα, hDq, hDΛ]
      calc 2 * ocA α q Λ k * ocTauPP α q Λ (k + 1)
          = 1 * (2 * (ocA α q Λ k * ocTauPP α q Λ (k + 1))) := by ring
        _ ≤ (max Υ 1 * CH) * (2 * (ocA α q Λ k * ocTauPP α q Λ (k + 1))) :=
            mul_le_mul_of_nonneg_right hY (by positivity)
        _ = 2 * max Υ 1 * CH * ocA α q Λ k * ocTauPP α q Λ (k + 1) := by ring
        _ ≤ _ := h1
    auxiliary := by have h := (le_max_left _ _).trans h15; dsimp only; omega
    slow := by have := hdm; dsimp only; omega
    fast := by have := hdm; dsimp only; omega
    integrable := hφ₀
    smooth := hφsmooth
    nonnegative := hφpos
    mass := hφint
    support := hφsupport
    kernels := ⟨kI.Γk, fun v u γ =>
      cascadeAdapter_admissible_zero (hG.2.2.2.2.2.2.2.2.1 v u γ).1⟩
    successorKernels := ⟨kI.Γk, fun v u γ => cascadeAdapter_admissible_zero (hker v u γ)⟩
    Y0 := Y0
    Yw := Yw
    Yk := Yk
    solution := hsol }⟩

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! The literal mean pullback expansion from finite native mean action.
The clock, chart inverse and finite Faà di Bruno expansion are discharged here.
The sole ingredient is the finite-regularity extension of the proved smooth action. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- The exact physical mean expansion from its one finite-action ingredient. -/
theorem native_mean_pullback_expansion_of_finite_action
    (hfinite : NativeFiniteMeanActionStatement) : NativeMeanPullbackExpansionStatement := by
  classical
  intro hr _ _ _ _ _ _ D Dm bw j₀ F hi p g n hg hn hnN a t _ht ha x k v
  dsimp only
  let clock := D.cellScaleSq F.m
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
    (F.G.fam.fiber p (F.G.actual p))
  let chart := fun s y => D.flowOf (F.m - 1) s y (D.slotAnchor F.m p.1)
  let label := fun s y => D.flowOf (F.m - 1) (D.slotAnchor F.m p.1) y s
  let Φ := fun Y => chart t (ρ • Y)
  let f := fun Y => a t (Φ Y)
  by_cases hz : ocCutoff D.α D.q D.Λ F.m p.1 t = 0
  · simp only [hz, zero_smul, Finset.sum_const_zero]
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
    (Construction.Stream.ocTau_pos hi.stage.base : 0 < ocTau D.α D.q D.Λ F.m) hz
  have hc : 0 < clock := EntryWeakProofs.weakData_cellScaleSq_pos
    D hi.stage.base hi.stage.profile hi.stage.band F.m
  have hclock : clock * (clock⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have htcell : clock⁻¹ * t ∈
      Icc (D.slotStart F.m p.1 / clock)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.m) / clock) := by
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩
  have htop : F.m - 1 ≤ D.term := by have := hi.stage.top; rw [hi.level] at this; omega
  have hρ : ρ ≠ 0 :=
    (mul_pos hi.stage.length_factor (Real.sqrt_pos.mpr
      (mul_pos (CycleReference.bandChain_pos hi.stage.base hi.stage.profile hi.stage.band htop)
        (Construction.Stream.ocTauPP_pos hi.stage.base)))).ne'
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ :=
    (CycleReference.streamFlow_spatial_smooth (D.hΦ (F.m - 1)) t (D.slotAnchor F.m p.1)).comp
      (contDiff_const_smul ρ)
  have hf : ContDiff ℝ ((F.N + Dm : ℕ) : ℕ∞) f :=
    (contDiff_pi.mpr ha).comp (hΦ.of_le (by simp))
  have hfreeze : liftFluxX Q (F.CcT p.1)
      (fun s Y => a (clock * s) (chart (clock * s) (ρ • Y))) g n (clock⁻¹ * t) =
      liftFluxX Q (F.CcT p.1) (fun _ => f) g n (clock⁻¹ * t) := by
    apply right_liftFluxX_time_congr
    funext Y
    rw [hclock]
  rw [hfreeze, hfinite hi p g n hg hn hnN f hf _ htcell]
  have hinv : Φ (ρ⁻¹ • label t x) = x := by
    dsimp only [Φ]
    rw [smul_inv_smul₀ hρ]
    exact (CycleReference.streamFlowHomeomorph (D.hΦ (F.m - 1)) t
      (D.slotAnchor F.m p.1)).right_inv x
  simp only [liftApply, show n - 1 + 1 = n by omega, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  have hmK : m ≤ F.N + Dm := by have := Finset.mem_range.mp hm; omega
  have hfm : ContDiff ℝ (m : ℕ∞) f := hf.of_le (Nat.cast_le.mpr hmK)
  simp_rw [ChartTransport.orderedDerivative_apply α hfm]
  have hfa (u : CompIn F.G.comps) := native_pullback_word_eq_faa α
    (fun y => a t y u) Φ ((ha u).of_le (Nat.cast_le.mpr hmK))
    (hΦ.of_le (by simp)) (ρ⁻¹ • label t x)
  simp only [hinv, Function.comp_def] at hfa
  dsimp only [ρ, label] at hfa
  dsimp only [f]
  simp_rw [hfa]
  simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end

section
/-! The actual finite native mean action and its physical pullback expansion.
The existing lift sequence supplies the finite coefficient reserve, the incoming
context supplies the edge reserve and the smooth mean identity is proved separately. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVenhance AVRegularity AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- The native path mean identity holds at the finite spatial reserve read by the flux. -/
theorem native_finite_mean_action : NativeFiniteMeanActionStatement := by
  intro hr _ _ _ _ _ _ D Dm bw j₀ F hi p g n hg hn hnN
  dsimp only
  intro f hf τ ht X k v
  let ρ := F.Mn.lenFactor * liftLength D F.m
  let Q := familyLiftData D F.m p.1 (nativeChain F.m p.1) ρ
    (F.G.fam.fiber p (F.G.actual p))
  have hX : Dm ≤ F.sX := by have := hi.slow; omega
  have hZ : Dm ≤ F.sZ := by have := hi.fast; omega
  have hb : ∀ q ≤ F.depth, ∀ n' m α v u,
      IsBoxSmooth Dm Dm (fun Y z => F.CcT p.1 q n' m α τ Y z v u) := by
    intro q hq n' m α v' u
    exact ((F.lift.1 p.1 p.2).2.2.2.2.2.1 q hq n' m α v' u τ ht).1.mono hX hZ
  have hmetric : ∀ j, ContDiff ℝ (0 : ℕ∞) (fun Y => Q.G τ Y k j) := by
    intro j
    exact (EntryWeakProofs.familyLiftData_metric_entry_smooth D F.m p.1
      (nativeChain F.m p.1) (by simp [nativeChain]) ρ _ τ k j).of_le (by simp)
  have hdrift : ContDiff ℝ (0 : ℕ∞) (fun z => Q.v τ z k) :=
    (CovFluxReg.ocPulseCellDrift_contDiff D.α D.q D.Λ D.ζ F.m (D.kap F.m)
      p.2 τ k).of_le (by simp)
  obtain ⟨ki, hctx, hres⟩ := hi.incoming_context
  have hedge := native_lift_fiber_boxSmooth hctx
    (native_context_slot_transverse hi.stage.base hi.stage.bandwidth hctx) hi.stage.natural
    (by have := hi.stage.level; omega) (by have := hi.stage.level; omega) hi.stage.bandwidth
    (Construction.Stream.ocEpsilon_pos hi.stage.base) hi.stage.base hi.stage.profile hi.stage.band
    hres (fun u => GenStage.compReserve_le_two ki u.1) p ρ 0 0
  simp only [hi.level] at hedge
  refine finite_mean_action_of_smooth Q (F.CcT p.1)
    (nativeStagePathMeanCoefficient hi.stage p g n k) F.N F.depth g n τ X k v
    hi.stage.order hg hnN ((F.lift.1 p.1 p.2).2.2.1) hb hmetric hdrift
    (fun v' u d γ hγ α => hedge v' u d γ hγ α τ ht) ?_ f hf
  intro f' hf'
  have hnM : n ≤ F.Mn.N + Dm := by rw [hi.menuN]; exact hnN
  have hA : (F.G.actual p).1 = nativeChain F.G.level p.1 := hi.stage.natural.2.2.1 p
  have htG : τ ∈ Icc (D.slotStart F.G.level p.1 / D.cellScaleSq F.G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ F.G.level) / D.cellScaleSq F.G.level) := by
    simpa only [hi.level] using ht
  have hm := nativeStagePathMeanAction hr D Dm bw j₀ F.P F.Mn F.G hi.stage
    F.depth p g n hg hn hnM f' hf' τ htG X k v
  have he : liftFluxX Q (F.CcT p.1) (fun _ => f') g n τ =
      liftFluxX Q (nativeStagePathCandidate hi.stage F.depth p) (fun _ => f') g n τ := by
    apply Uniqueness.liftFluxX_congr
    intro q hq n' m α
    have hc := native_input_coefficients_eq_paths hi p q (hq.trans hg) n'
    rw [hi.level] at hc
    exact hc τ ht m α
  rw [he]
  simpa only [hA, hi.level] using hm

/-- The literal cutoff-weighted mean is the finite physical pullback-jet expansion. -/
theorem native_mean_pullback_expansion : NativeMeanPullbackExpansionStatement :=
  native_mean_pullback_expansion_of_finite_action native_finite_mean_action

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! The native mean-flux jet and the native temporal representatives: the column aggregation
(`nativeGluedPulseJet_of_parts`) with the pullback expansion (`native_mean_pullback_expansion`) and
the word operators (`nativeMeanPhysicalWordOperator`). -/

/-- **The mean-flux jet production**, from the pullback expansion and the word operators. -/
theorem nativeMeanJetProduction_of_parts (hexp : NativeMeanPullbackExpansionStatement)
    (hword : NativeMeanPhysicalWordOperatorStatement) : NativeMeanJetProductionStatement :=
  fun F => nativeGluedPulseJet_of_parts hexp hword F

/-- The mean-flux jet production from the word operators. -/
theorem nativeMeanJetProduction_of_word (hword : NativeMeanPhysicalWordOperatorStatement) :
    NativeMeanJetProductionStatement :=
  nativeMeanJetProduction_of_parts native_mean_pullback_expansion hword

/-- The native temporal representatives from the word operators. -/
theorem nativeTemporalRepresentatives_of_word
    (hword : NativeMeanPhysicalWordOperatorStatement) : NativeTemporalRepresentativesStatement :=
  native_temporal_representatives_of_budget_ingredients
    (nativeMeanJetProduction_of_word hword)

/-- **The native temporal representatives**, closed. -/
theorem nativeTemporalRepresentatives : NativeTemporalRepresentativesStatement :=
  nativeTemporalRepresentatives_of_word nativeMeanPhysicalWordOperator

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
end
