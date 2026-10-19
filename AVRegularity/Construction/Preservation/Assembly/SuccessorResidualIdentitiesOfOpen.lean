-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Assembly.RetainedMarkedLedgerOfIngredients
public import AVRegularity.Construction.StageEnvelopes.SuccessorPreparation
public import AVRegularity.Proofs.Results.Construction.SuccessorExists
public import AVRegularity.Construction.Preservation.Residual.KernelReadout.ClassicalComponent
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanDirect
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofFirstSourceDiagSmooth
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.GluedClosed
public import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
public import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
public import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
public import AVRegularity.Construction.StageEnvelopes.Cauchy.RealMixedJetTransfer

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Filter
open scoped Topology Classical
open AVRegularity.Construction.StageEnvelopes
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.Construction.Preservation.Assembly

/-! The uniform retained pointwise input adapter, using the context certificate
and existing cascade length/reserve estimates. No analytic producer is repeated.

Root spaces may be trivial: only context certificates and record geometry are used, not the
kernel regularizer transfer that needs nontrivial roots, so empty components and edgeless
seeds are covered. -/

private theorem pointwise_floor_facts {mc mp mr j L m : ℕ}
    (hm : max mc (max 2 (max mp (max mr (max (j + 2) (L + 1))))) ≤ m) :
    mc ≤ m ∧ 2 ≤ m ∧ mp ≤ m ∧ mr ≤ m ∧ j ≤ m - 1 ∧ L ≤ m - 1 := by
  omega

private theorem pointwise_level_pos {m : ℕ} (hm : 2 ≤ m) : 1 ≤ m - 1 := by
  omega

/-- The one moderate input leaf of the fourth preservation assembly. -/
theorem retained_pointwise_context_inputs
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (estimates : ∀ p, ContextEnvelopeEstimate p) :
    RetainedPointwiseContextInputsStatement α s q ζ estimates := by
  obtain ⟨Λc, hΛc, hc⟩ := Providers.successor_context_certified α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Cu, _hCu, Λp, hΛp, hpass⟩ := Providers.CascadeInvariants.exists_passScales hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λl, hΛl, hlens⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λc (max Λp (max Λl Λr)), by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cc, hcc, hc⟩ := hc Λ (by omega)
  refine ⟨min cc 1, lt_min hcc zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨tc, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  let pe := successorEnvelopeParameters α s q Λ ζ hα₀ hα₁ hs₀ hs₁ hq h128 hζ bw hbw hbwupper kS
    (succSchedD D₀ N p (H + 1))
  let thr : InvConsts :=
    { tc with Ca := max tc.Ca (estimates pe).Ca
              Cm := fun j => max (tc.Cm j) ((estimates pe).Cm j) }
  obtain ⟨Υ', hcarrier, hstart_mono⟩ := Cauchy.common_carrier_constants h128 hCH hΥ
  refine ⟨thr, CH, Υ', hCH, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 100)
    ((le_max_left _ _).trans hcarrier.2), ?_⟩
  intro kI hkI
  have hkIc := invariant_admissible_of_threshold_bounds (a := tc) (b := thr)
    le_rfl le_rfl (le_max_left _ _) (fun _ => le_max_left _ _) (fun _ => le_rfl) hkI
  rcases id hkI with ⟨hcEq, _, _, _, _, _, _, _, _, _, _, hCa, hCm, _, _, _, _,
    _, hKs, _, hKan, _, hLan, _, hJm, _, _, hG0, hHprod, hprod, henvnonneg, _, henvlt⟩
  have hCaI : (estimates pe).Ca ≤ kI.Ca := (le_max_right _ _).trans hCa
  have hCmI (j : ℕ) : (estimates pe).Cm j ≤ kI.Cm j := (le_max_right _ _).trans (hCm j).2
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkIc
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hledger (hstart_mono j₀ hstart)
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hdecay := Buffer.preparation_parent_power_tendsto_zero hq.1 h128
    (mul_pos (by norm_num : (0 : ℝ) < 3) hδ)
  have hlim : Tendsto (fun m : ℕ => Cu * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q))
      atTop (𝓝 0) := by simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  obtain ⟨mp, hmp⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds zero_lt_one))
  have hcI : 0 < kI.c₀ := hcEq.symm ▸ hc₀
  obtain ⟨mr, hmr, hradius⟩ := hradius Λ (by omega) kI.c₀ 1 hcI zero_lt_one
  refine ⟨max mc (max 2 (max mp (max mr (max (j₀ + 2) ((estimates pe).levelFloor + 1))))), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    G G' hcascade hlevel hG hactual
  obtain ⟨hmc, hm2, hmpm, hmrm, hjm, hEm⟩ := pointwise_floor_facts hm
  have hmM : m ≤ M := hn.trans hnM.le
  have hmTerm : m ≤ D.term := hterm.symm ▸ hmM
  have hcertified := (hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmc hn hnM G G' hcascade hlevel hG hactual).2.2
  obtain ⟨tA, htA, hGInv⟩ := hG
  let Gr := G'.retained m H J
  have hGrlevel : Gr.level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hqD : 1 < D.q := hDq.symm ▸ hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ.symm ▸ h128
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hε (i : ℕ) : 0 < D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
  have hκ : 0 < D.κ Gr.level := CycleReference.bandChain_pos hΛ1 hζD hbandD
    (by rw [hGrlevel, hterm]; exact (Nat.sub_le m 1).trans hmM)
  have hcIupper : kI.c₀ ≤ 1 := hcEq.symm ▸ hc₀upper.trans (min_le_right _ _)
  have hrho : 0 < rhoStar D kI.c₀ Gr.level := mul_pos hcI
    (lt_min (hε _) (Real.sqrt_pos.mpr (div_pos hκ (Real.rpow_pos_of_pos (hε _) _))))
  have hrhoe : rhoStar D kI.c₀ Gr.level ≤ D.eps Gr.level :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hcI.le).trans
      (mul_le_of_le_one_left (hε _).le hcIupper)
  have hpass' := hpass D hDα hDq hDζ (by rw [hDΛ]; exact
    ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ)
    (by simpa only [hterm, hDΛ] using hband) m hm2 hmTerm
  have hsmall : Cu * D.eps (m - 1) ^ (3 * ocDelta D.α D.q) ≤ 1 := by
    simpa only [OCData.eps, hDα, hDq, hDΛ] using hmp m hmpm
  have hεlift : D.eps m ≤ liftLength D m := by
    have hd := hpass'.hDρ
    have hρ := hpass'.hρ0
    have hds : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / liftLength D m ≤ 1 :=
      hd.trans hsmall
    exact hpass'.hεd.trans ((div_le_one hρ).mp hds)
  have hlift : liftLength D m ≤ rhoStar D kI.c₀ (m - 1) := by
    have hh := hradius D hDα hDq hDΛ hDζ hbandD m hmrm hmTerm
    simpa only [rhoEnh, one_mul, liftLength] using hh
  obtain ⟨hseedlevel, _, _, _, _, hseedlength, _, hseedInv, _⟩ := hseed
  have hlengthG := hlens hr D hDα hDq hDζ (by rw [hDΛ]; exact
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hΛ) hbandD _ bw j₀ _ Cw kI.cr σ₀
    (succEta0 α q s) N p (hkI.2.1.symm ▸ hcrupper) seed G hseedInv.2.1
    (fun v u γ hbe => by simpa only [hseedlevel] using (hseedlength v u γ).2.2 hbe)
    (by rw [hseedlevel, hterm]; exact hnM.le) hcascade (hlevel.symm ▸ (Nat.le_trans (by norm_num : 1 ≤ 2) hm2))
  have hR : (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p).Rb (G.level - 1) ≤
      rhoStar D kI.c₀ (m - 1) := by
    change freshLength D kI.cr (G.level - 1) ≤ _
    rw [hlevel]
    have hcrI : kI.cr ≤ 1 := hkI.2.1.symm ▸ hcrupper
    have heq : freshLength D kI.cr (m - 1) = kI.cr * liftLength D m := by
      unfold freshLength liftLength
      rw [Nat.sub_add_cancel ((by norm_num : 1 ≤ 2).trans hm2)]
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hcrI hpass'.hρ0.le).trans
      (by simpa only [one_mul] using hlift)
  have hout := actual_successor_higher_lengths hGInv.2.1 hactual
    (fun v u γ hbe => (hlengthG v u γ hbe).trans (by rw [hlevel]; exact hεlift.trans hlift)) hR
  have hlength : ∀ v u (γ : Gr.fam.Γ v u), 3 ≤ (Gr.fam.identity v u γ).maxOrder →
      (Gr.fam.identity v u γ).record.length ≤ rhoStar D kI.c₀ Gr.level := by
    intro v u γ h3
    conv_rhs => rw [hGrlevel]
    exact hout ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩ γ h3

  have hnatural : ∃ M, Gr.IsNatural M := by
    have hnat := hactual.2.2.2.1
    refine ⟨Mnat, hnat.1, hnat.2.1, hnat.2.2.1, ?_⟩
    intro v u
    exact hnat.2.2.2 ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩
  refine ⟨pe, ?_, by rw [hGrlevel]; exact hEm, hCaI, hCmI⟩
  refine { bw_eq := rfl
           alpha_eq := hDα
           q_eq := hDq
           base_eq := hDΛ
           profile_eq := hDζ
           stream := hseq
           natural := hnatural
           certified := hcertified
           level_pos := by rw [hGrlevel]; exact pointwise_level_pos hm2
           carrier_start := by rw [hGrlevel]; exact hjm
           carrier_environment := ⟨CH, Υ', hcarrier, by
             simpa only [hDα, hDq, hDΛ] using hstart⟩
           q_pos := hqD
           large := hΛD
           kap_pos := by
             unfold OCData.kap
             exact CycleReference.bandChain_pos hΛ1 hζD hbandD (Nat.min_le_right _ _)
           radius_pos := hrho
           radius_le := hrhoe
           wavelength_le := Providers.CascadeInvariants.eps_le_of_le hqD hΛD (Nat.sub_le _ _)
           inner_nonneg := henvnonneg
           inner_le := ?_
           reserve_le := ?_
           reserve_upper := fun v => (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
           slot_order := hKs
           slow_order := hKan
           fast_order := hLan
           molecular_order := hJm
           source_order := fun v u γ => (Gr.fam.identity v u γ).le_D
           higher_length := hlength }
  · change kI.mEnv ≤ 1 / ((kS.Hprod : ℝ) + 1)
    rw [← hHprod]
    exact henvlt.le
  · intro v
    change 2 / ((kS.Hprod : ℝ) + 1) ≤ compReserve kI v.1
    rw [← hHprod]
    exact retained_compReserve_ge hprod (Finset.mem_filter.mp v.2).2.1

end AVRegularity.Construction.Preservation.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly

/-! **The residual identities of the successor, end to end from the statements taken as
hypotheses**.

The chain of `successor_residual_identities`:

* `successor_residual_identities_of_ingredients`: from the retained readout weak equation and the
  native lift covariance residual identity;
* `retained_readout_weak_equation_of_ingredients`: the first from the kernel equation (proved:
  `retained_readout_kernel_equation`) and the flux cancellation;
* `retained_readout_flux_cancellation_of_ingredients`: the flux cancellation from the reindexing
  (`retainedReadoutReindex`), the kernel split (`retainedReadoutKernelSplit`), the generic core, the
  cascade input (`cascadeSplitInput`, with the order bound of the cascade) and the continuity of
  the fluxes (`retainedReadoutFluxContinuity_of_input`);
* `successor_split_core_of_pieces`: the core from the eight pieces: 1 `rootSourceBookkeeping`,
  2 `piecePiolaFiniteOrder`, 3 `centeredCoefficientFiniteOrder`, 4 `transferChartCollapse`,
  5 `hilbertLiftPathSum`, 6 from its left and right steps (`sourceMeanLetterSum_of_left_right_steps`),
  7 from the diagonal term (`firstSourceIdentity_of_three`), 8 `covarianceFluxRegularity`.

The flux-cancellation half is proved unconditionally (`successorSplitCore`,
`retainedReadoutWeakEquation`, `successor_residual_identities_of_cov`), using the source-mean
steps `sourceMeanLeft` and `sourceMeanRight` and the diagonal term `fsDiagTerm`;
`successor_residual_identities_of_right` takes the right step as the only hypothesis of
this half. The other half,
`NativeLiftCovarianceResidualIdentityStatement`, is the covariance-transport leaf (not one of the
eight pieces); it enters `successor_residual_identities_of_open` as a hypothesis, and
`nativeLiftCovarianceResidualIdentity_of_open` reduces it to its own ingredients
(`native_lift_covariance_residual_identity_of_ingredients` with the three proved ones:
`covarianceMeanReduction`, `macroWeakFromStrong`, `kernelDefectRegularization`). -/

open AVRegularity.Construction.Preservation.Residual
  AVRegularity.Construction.Preservation.Residual.FluxCancellation
  AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- **The generic core from three statements taken as hypotheses**: the eight pieces assembled. -/
theorem successorSplitCore_of_open (hL : SourceMeanLeftStatement)
    (hR : SourceMeanRightStatement) (T : FSDiagTerm) : SuccessorSplitCoreStatement :=
  successor_split_core_of_pieces rootSourceBookkeeping piecePiolaFiniteOrder
    centeredCoefficientFiniteOrder transferChartCollapse hilbertLiftPathSum
    (sourceMeanLetterSum_of_left_right_steps hL hR)
    (fun _ _ _ => firstSourceIdentity_of_three fsPiolaOperator fsPiolaConstant T)
    covarianceFluxRegularity

/-- **The retained readout flux cancellation from three statements taken as hypotheses.** -/
theorem retainedReadoutFluxCancellation_of_open {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (hL : SourceMeanLeftStatement) (hR : SourceMeanRightStatement)
    (T : FSDiagTerm) : RetainedReadoutFluxCancellationStatement α s q ζ :=
  retained_readout_flux_cancellation_of_ingredients (retainedReadoutReindex α s q hζ)
    (retainedReadoutKernelSplit α s q ζ) (successorSplitCore_of_open hL hR T)
    (cascadeSplitInput α s q ζ hζ hα₀ hq.1)
    (retainedReadoutFluxContinuity_of_input hα₀ hα₁ hs₀ hs₁ hq hζ
      (cascadeSplitInput α s q ζ hζ hα₀ hq.1))

/-- **The retained readout weak equation from three statements taken as hypotheses.** -/
theorem retainedReadoutWeakEquation_of_open {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (hL : SourceMeanLeftStatement) (hR : SourceMeanRightStatement)
    (T : FSDiagTerm) : RetainedReadoutWeakEquationStatement α s q ζ :=
  retained_readout_weak_equation_of_ingredients
    (retained_readout_kernel_equation hα₀ hα₁ hs₀ hs₁ hq hζ)
    (retainedReadoutFluxCancellation_of_open hα₀ hα₁ hs₀ hs₁ hq hζ hL hR T)

/-- **The residual identities of the successor from statements taken as hypotheses**: the three
statements of the flux-cancellation half and the covariance-transport leaf. The conclusion is the
text of `successor_residual_identities`. -/
theorem successor_residual_identities_of_open (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hL : SourceMeanLeftStatement)
    (hR : SourceMeanRightStatement) (T : FSDiagTerm)
    (hcov : NativeLiftCovarianceResidualIdentityStatement α s q ζ) :
    type_of% (successor_residual_identities_of_ingredients α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      (retainedReadoutWeakEquation_of_open hα₀ hα₁ hs₀ hs₁ hq hζ hL hR T) hcov) :=
  successor_residual_identities_of_ingredients α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (retainedReadoutWeakEquation_of_open hα₀ hα₁ hs₀ hs₁ hq hζ hL hR T) hcov

/-- **The covariance-transport leaf from its remaining ingredients** (the mean reduction, the macro
weak equation and the kernel defect regularization are proved). -/
theorem nativeLiftCovarianceResidualIdentity_of_open {α s q : ℝ} {ζ : ℝ → ℝ}
    (hInputs : CascadeNativeInputsProductionStatement α s q ζ)
    (hNative : NativeTemporalRepresentativesStatement) (hRead : ReadoutStrongEquationStatement)
    (hTemporal : CovarianceTemporalProductStatement) (hLift : LiftResidualWeakStatement) :
    NativeLiftCovarianceResidualIdentityStatement α s q ζ :=
  native_lift_covariance_residual_identity_of_ingredients hInputs hNative hRead hTemporal
    covarianceMeanReduction macroWeakFromStrong hLift kernelDefectRegularization

/-! ### With the left source-mean step proved -/

/-- **The generic core from the right source-mean step**. -/
theorem successorSplitCore_of_right (hR : SourceMeanRightStatement) :
    SuccessorSplitCoreStatement :=
  successorSplitCore_of_open sourceMeanLeft hR fsDiagTerm

/-- **The retained readout weak equation from the right source-mean step.** -/
theorem retainedReadoutWeakEquation_of_right {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (hR : SourceMeanRightStatement) :
    RetainedReadoutWeakEquationStatement α s q ζ :=
  retainedReadoutWeakEquation_of_open hα₀ hα₁ hs₀ hs₁ hq hζ sourceMeanLeft hR fsDiagTerm

/-- **The residual identities of the successor from the right source-mean step and the
covariance-transport leaf.** -/
theorem successor_residual_identities_of_right (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hR : SourceMeanRightStatement)
    (hcov : NativeLiftCovarianceResidualIdentityStatement α s q ζ) :
    type_of% (successor_residual_identities_of_open α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      sourceMeanLeft hR fsDiagTerm hcov) :=
  successor_residual_identities_of_open α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ sourceMeanLeft hR
    fsDiagTerm hcov

/-! ### The flux-cancellation half (the right source-mean step is `sourceMeanRight`) -/

/-- **The generic core** (`SuccessorSplitCoreStatement`): the eight pieces, all proved. -/
theorem successorSplitCore : SuccessorSplitCoreStatement :=
  successorSplitCore_of_right sourceMeanRight

/-- **The retained readout weak equation.** -/
theorem retainedReadoutWeakEquation {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) : RetainedReadoutWeakEquationStatement α s q ζ :=
  retainedReadoutWeakEquation_of_right hα₀ hα₁ hs₀ hs₁ hq hζ sourceMeanRight

/-- **The residual identities of the successor from the covariance-transport leaf alone.** -/
theorem successor_residual_identities_of_cov (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hcov : NativeLiftCovarianceResidualIdentityStatement α s q ζ) :
    type_of% (successor_residual_identities_of_right α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      sourceMeanRight hcov) :=
  successor_residual_identities_of_right α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ sourceMeanRight hcov

/-- **The residual identities of the successor from the three statements of the covariance leaf
without a proof in the tree** (the cascade adapter is `cascadeNativeInputsProduction`, the strong
readout equation `readoutStrongEquation`). -/
theorem successor_residual_identities_of_cov_three (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hNative : NativeTemporalRepresentativesStatement)
    (hTemporal : CovarianceTemporalProductStatement) (hLift : LiftResidualWeakStatement) :
    type_of% (successor_residual_identities_of_cov α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      (nativeLiftCovarianceResidualIdentity_of_open
        (cascadeNativeInputsProduction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ) hNative
        readoutStrongEquation hTemporal hLift)) :=
  successor_residual_identities_of_cov α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (nativeLiftCovarianceResidualIdentity_of_open
      (cascadeNativeInputsProduction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ) hNative
      readoutStrongEquation hTemporal hLift)

end AVRegularity.Construction.Preservation.Assembly
end
