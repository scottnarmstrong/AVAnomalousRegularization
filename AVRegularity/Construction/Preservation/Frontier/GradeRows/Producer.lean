-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Frontier.GradeRows.ExtendedCertificates
public import AVRegularity.Construction.Preservation.Frontier.GradeSourceProduction
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.Construction.Preservation.RetainedEnergy.UniformInputs
public import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier

/-! Uniform fixed-data grade rows: the same native kernel operator is built once at Kres
and restricted to each requested order. The extended certificates and zero-extension
calculus discharge the remaining hypotheses of the flux bound. -/

open AVRegularity.Construction.Preservation.Assembly FullLift RetainedEnergy

def ExtendedCertificatesAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (mStar : ℕ) : Prop :=
  ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ tA : ℝ, tS ≤ tA →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      let Gr := G'
      Gr.IsNatural Mnat ∧ Gr.IsShiftInvariant ∧ Gr.IsSlotTransverse ∧
        Gr.IsContextCertified kI ∧
        markedLedger (Gr.mass law) (Gr.marker law) Gr.fam ≤
          CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe ∧
        (∀ v u (γ : Gr.fam.Γ v u),
          (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
            v u γ).width = (Gr.fam.identity v u γ).record.width ∧
          ∀ ρ : ℝ, 0 < ρ → IsSpatialRegularizerTorus ρ 0
            (succSchedD D₀ N p (H + 1)) (tA + 3 * ocTau α q Λ m) tf kI.cker
            (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              v u γ).width
            (Gr.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              φ₀ hφ₀ v u γ))


/-- Uniform grade rows at fixed allocation and before the stage data.
The degenerate cases are included: empty and singleton families, identity metric, k=0, J=0, zero
input and edgeless seed. -/
theorem grade_rows_at_data {α s q : ℝ}
    (hq : IsAdmissibleQ α s q)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Λl Λ : ℕ)
    (hlength : UniformRecordLengths α q ζ Λl) (hΛ : Λl ≤ Λ) (h128 : 128 ≤ Λ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ)
    (Q T₀ Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ)
    (σ₀ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr : ℝ) (hCI : 0 ≤ CI) (mc : ℕ)
    (hc : ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀ mc)
    (hprod : kI.Hprod = kI.G0 + H + 1) (hc0pos : 0 < kI.c₀) (hc0le : kI.c₀ ≤ 1)
    (_hcrpos : 0 < kI.cr) (hcrle : kI.cr ≤ 1) (mr : ℕ) (hmr : 2 ≤ mr)
    (hradius : EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr) (md : ℕ)
    (hdrift : EnhancedDriftAt α q ζ Λ kI.cr md)
    (Cu : ℝ) (hscale : ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → ∀ m, 2 ≤ m → m ≤ D.term →
        AVRegularity.Providers.CascadeInvariants.PassScales D m Cu)
    (A : ℝ) (hA : 0 ≤ A) (mo : ℕ)
    (hop : NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo)
    (ma : ℕ)
    (habs : ∀ m, ma ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8)
    : FrontierAnalyticProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ 1
      (max mc (max mr (max md (max (mo + 3) (max ma (j₀ + 3)))))) true
      (fun rows _readout _source => rows) := by
  classical
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow _hT G G' hcascade hlevel hG hactual tp Preg hprep
    _f _Ain _hf k hk Y0 _Y Yw _Yk _htrace hsol yom hyom
  have hmc : mc ≤ m := by omega
  have hmr' : mr ≤ m := by omega
  have hmd' : md ≤ m := by omega
  have hmo' : mo + 1 ≤ m - 1 := by omega
  have hma : ma ≤ m := by omega
  have hjGr' : j₀ ≤ m - 1 := by omega
  have hm2 : 2 ≤ m := by omega
  have hiGr' : 1 ≤ m - 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hmterm : m ≤ D.term := by rw [hterm]; exact hn.trans hnM.le
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact h128
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let Gr := G'
  have hGrlevel : Gr.level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hGrlevelterm : Gr.level ≤ D.term := by omega
  have hGrI := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmc hn hnM tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hnat, hshift, hslot, hctx, hled, hker⟩ := hGrI
  have hmGr v : 0 ≤ compReserve kI (v : CompIn Gr.comps).1 :=
    AVRegularity.Providers.CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hprod
      (AVRegularity.Providers.CascadeInvariants.grade_le_of_succ
        (AVRegularity.Providers.CascadeInvariants.grade_le_of_cascade hseed.2.1 hcascade) hactual v)
  have hm2Gr v : compReserve kI (v : CompIn Gr.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenG := hlength hr D hDα hDq hDζ (by rw [hDΛ]; omega) hbandD
    _ bw j₀ Mn Cw kI.cr σ₀ (succEta0 α q s) N p hcrle seed G hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcascade (hlevel.symm ▸ hm1)
  have hscl := hscale D hDα hDq hDΛ hDζ hbandD m hm2 hmterm
  have hlenGr := extended_successor_record_lengths P Mn G G' hactual hG.2.1 hlenG
    (EntryScales.epsilon_antitone hqD (by omega) (by rw [hactual.2.1]; omega))
    (by
      change freshLength D kI.cr (G.level - 1) ≤ D.eps G'.level
      rw [hactual.2.1, hlevel]
      simpa only [Nat.sub_add_cancel hm1] using
        AVRegularity.Providers.CascadeInvariants.freshLength_le_eps_of_passScales hcrle
          (show AVRegularity.Providers.CascadeInvariants.PassScales D ((m - 1) + 1) Cu from
            (Nat.sub_add_cancel hm1).symm ▸ hscl))
  have he (l : ℕ) : 0 < D.eps l := Construction.Stream.ocEpsilon_pos (by omega)
  have hκ (l : ℕ) (hl : l ≤ D.term) : 0 < D.κ l :=
    CycleReference.bandChain_pos (by omega) hζD hbandD hl
  have ha (l : ℕ) : 0 < ocA D.α D.q D.Λ l := Real.rpow_pos_of_pos (he l) _
  have hrs (l : ℕ) (hl : l ≤ D.term) :
      0 < rhoStar D kI.c₀ l ∧ rhoStar D kI.c₀ l ≤ D.eps l := by
    have hh := Buffer.molecular_radius_bounds hc0pos (he l) (hκ l hl) (ha l)
    exact ⟨hh.1, hh.2.1.trans (mul_le_of_le_one_left (he l).le hc0le)⟩
  have hrhos := hradius D hDα hDq hDΛ hDζ hbandD m hmr' hmterm
  have hρe : rhoEnh D kI.cr m ≤ D.eps Gr.level := by
    rw [hGrlevel]
    exact hrhos.trans (hrs (m - 1) (by omega)).2
  have hρE : rhoEnh D kI.cr m ≤ D.eps (Gr.level - 1) :=
    hρe.trans (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hd := hdrift D.Φ hseq M D.κ hband m hmd' (hn.trans hnM.le)
  have hρpos : 0 < rhoEnh D kI.cr m := by
    simpa only [rhoEnh, hDα, hDq, hDΛ] using hd.2.1
  have htptf : tp ≤ tf := by
    have hh := hprep.2.2.1
    rw [hlevel, hDα, hDq, hDΛ] at hh
    exact hh.trans hwindow
  have hsub : Set.Icc tp tf ⊆ Set.Icc (tA + 3 * ocTau α q Λ m) tf := by
    intro t ht
    exact ⟨(hdelay.trans hprep.2.1).trans ht.1, ht.2⟩
  have hSzero : ∀ v u (γ : Gr.fam.Γ v u), IsSpatialRegularizerTorus (rhoEnh D kI.cr m) 0
      (succSchedD D₀ N p (H + 1)) tp tf kI.cker
      (Gr.kernelOf P seedK freshK v u γ).width (Gr.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
    intro v u γ
    exact Buffer.spatialRegularizerTorus_time_restrict ((hker v u γ).2 _ hρpos) hsub
  have hkap : D.kap Gr.level = D.κ (m - 1) := by
    change D.κ (min Gr.level D.term) = _
    rw [Nat.min_eq_left hGrlevelterm, hGrlevel]
  have hsmall : A * (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8 := by
    simpa only [OCData.eps, hDq, hDΛ] using habs m hma
  have hlengthop : ∀ v u (γ : Gr.fam.Γ v u), 3 ≤ (Gr.fam.identity v u γ).maxOrder →
      (Gr.fam.identity v u γ).record.length ≤ D.eps (Gr.level - 1) := by
    intro v u γ hj
    have hb : 1 ≤ (Gr.fam.identity v u γ).record.birthExcess := by
      have hh := (Gr.fam.identity v u γ).le_birth
      omega
    exact (hlenGr v u γ hb).trans
      (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hop' := hop hr D hDα hDq hDΛ hDζ hseq j₀ Mnat Gr kI hctx hnat hshift
    (hGrlevel.symm ▸ hmo') (hGrlevel.symm ▸ hiGr') (hGrlevel.symm ▸ hjGr')
    (he _) (he _) (by rw [hkap]; exact hd.1)
    hslot hmGr hm2Gr P seedK freshK (fun v u γ => (hker v u γ).1) φ₀ hφ₀ tp tf
    (rhoEnh D kI.cr m) (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe)
    (Gr.mass law) (Gr.marker law) htptf hρpos hρE hρe hlengthop
    (fun v => Buffer.birth_compMass_pos hqD hΛD law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD law v.1) hled hsmall.le hSzero
  rw [hkap] at hop'
  obtain ⟨R, hB, hC, hS, hπ, hRadius, hcR, _hθ⟩ := hop' (Gr.marker law) (Or.inr rfl)
  have hSall : ∀ v u γ, IsSpatialRegularizerTorus (rhoEnh D kI.cr m) k
      (succSchedD D₀ N p (H + 1)) tp tf R.c (R.r v u γ) (R.S v u γ) := by
    intro v u γ
    rw [hRadius, hcR, hS]
    exact spatial_regularizer_all_orders _ _ _ _ _ _ _ (hSzero v u γ) k
  let Rk := kernelOperator_order_restrict R hk hSall
  let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
    { G := G, G' := G', law := law, m := m, H := H, J := J, k := k,
      cr := kI.cr, η := succEta0 α q s,
      θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
      θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
      tp := tp, tf := tf, Y0 := Y0, Yw := Yw, yom := yom }
  apply grade_rows_of_kernel_operator F Rk hB hC hπ
    (by
      rw [show Rk.θ = A * (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe) from _hθ]
      exact mul_nonneg hA (mul_nonneg hCI (Real.rpow_nonneg (he _).le _)))
    (Rk.hθ.trans (by norm_num)) hsol.2.1
  intro v u γ hu
  rw [show Rk.S = G'.sysS P seedK freshK φ₀ hφ₀ from hS]
  filter_upwards [hyom v u γ hu] with t ht
  have he := frontier_sysS_parameters_congr G'
    (succProvParams D Cw kI.cr σ₀ (succEta0 α q t) N p) P rfl seedK freshK φ₀ hφ₀
  simpa only [F, he] using ht

end AVRegularity.Construction.Preservation.Frontier
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Frontier

/-! Grade-row production with constants chosen before the stage, root spaces and birth law.
The extended family uses the same uniform kernel price as the retained energy proof. -/

open AVRegularity.Construction.Preservation.Assembly FullLift RetainedEnergy

/-- Uniform grade-row flux, with all thresholds chosen before the stage and birth law.
The degenerate cases are included: empty and singleton families, edgeless seeds, order zero, J=0 and
zero input are covered. Signed preparation constants do not enter the grade-row constant one. -/
theorem grade_rows_production {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    FrontierAnalyticProductionStatement α s q ζ true (fun rows _readout _source => rows) := by
  classical
  obtain ⟨Λc, hΛc, hc⟩ := extended_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  change UniformRecordLengths α q ζ Λl at hlength
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λd, hΛd, hdrift⟩ := actual_enhanced_drift_budget hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Cu, _hCu, Λp, hΛp, hscale⟩ := AVRegularity.Providers.CascadeInvariants.exists_passScales
    hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λc (max Λl (max Λr (max Λd Λp))), by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ (by omega)
  refine ⟨min cmax 1, lt_min hcmax zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨tc, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  let thr : InvConsts := { tc with cker := fun j => max (tc.cker j) 0 }
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  have hkIc := invariant_admissible_of_threshold_bounds (a := tc) (b := thr)
    le_rfl le_rfl le_rfl (fun _ => le_rfl) (fun j => le_max_left _ _) hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkIc
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hledger hstart
  change ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ
    σ₀ kI CI Cw j₀ mc at hc
  obtain ⟨hc0I, hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
  have hc0pos : 0 < kI.c₀ := hc0I.symm ▸ hc₀
  have hc0le : kI.c₀ ≤ 1 := hc0I.symm ▸ hc₀upper.trans (min_le_right _ _)
  have hcrpos : 0 < kI.cr := hcrI.symm ▸ hcr
  have hcrle : kI.cr ≤ 1 := hcrI.symm ▸ hcrupper
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) :=
    Buffer.preparation_schedule_order_ge_two D₀ N p H
  obtain ⟨mr, hmr, hradius⟩ := hradius Λ (by omega) kI.c₀ kI.cr hc0pos hcrpos
  change EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr at hradius
  obtain ⟨md, _hmd, hdrift⟩ := hdrift Λ (by omega) kI.cr hcrpos
  change EnhancedDriftAt α q ζ Λ kI.cr md at hdrift
  have hcker (j : ℕ) (_hj : j + 2 ≤ succSchedD D₀ N p (H + 1)) : 0 ≤ kI.cker j :=
    (le_max_right (tc.cker j) 0).trans (invariant_admissible_kernel_bounds hkI j).2
  obtain ⟨A, hA, mo, _hmo, hop⟩ := uniform_native_kernel_operator_of_certificates
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw Kres
    (succSchedD D₀ N p (H + 1)) hDm kI.cker hcker
  change NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo at hop
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < min (ocDelta α q / 4) τe := lt_min (div_pos hδ (by norm_num)) hτe
  obtain ⟨ma, habs⟩ := retained_absorption_threshold hq.1 h128 hτ A CI
  have hscale' : ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → ∀ m, 2 ≤ m → m ≤ D.term →
        AVRegularity.Providers.CascadeInvariants.PassScales D m Cu := by
    intro D hDα hDq hDΛ hDζ hband m hm hmM
    apply hscale D hDα hDq hDζ (by omega) _ m hm hmM
    simpa only [hDα, hDq, hDζ] using hband
  refine ⟨1, max mc (max mr (max md (max (mo + 3) (max ma (j₀ + 3))))), ?_⟩
  exact grade_rows_at_data hq hζ Λl Λ hlength (by omega) h128 φ₀ hφ₀ bw Q T₀ Ce τe kS
    r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr (zero_le_one.trans (hCe.trans hledger.1)) mc hc hprod
    hc0pos hc0le hcrpos hcrle mr hmr hradius md hdrift Cu hscale' A hA mo hop ma habs

end AVRegularity.Construction.Preservation.Frontier
end
