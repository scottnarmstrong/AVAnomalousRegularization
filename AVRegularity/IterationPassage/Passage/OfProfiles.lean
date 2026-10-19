-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.Passage.StrongEnergyData
public import AVRegularity.IterationPassage.ErrorJets.OfSuccessorBill
import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.IterationPassage.Passage.Profiles.ClausesStatement
import AVRegularity.IterationPassage.Passage.Profiles.SmoothRep
import AVRegularity.Proofs.Results.Construction.SuccessorResidualIdentities

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.IterationPassage.ErrorJets
namespace AVRegularity.IterationPassage.Passage

/-! **The strong energy of the regenerated retained solution**.

`passageRetainedStrongEnergy`: the prefix of `prepared_retained_energy_production` (same
certificates and thresholds), with the data part `passage_strongEnergy_at_data`; the constant is
`C₀ = √2 * |C_pr|`. -/

open AVRegularity.Construction.Preservation.RetainedEnergy
open AVRegularity.Construction.Preservation.Assembly AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation AVRegularity.Construction AVRegularity

/-- **The strong energy of the regenerated retained solution** in the marked weight. -/
theorem passageRetainedStrongEnergy (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : PassageRetainedStrongEnergyStatement α s q ζ := by
  classical
  obtain ⟨Λc, hΛc, hc⟩ := retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  change UniformRecordLengths α q ζ Λl at hlength
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λd, hΛd, hdrift⟩ := actual_enhanced_drift_budget hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λc (max Λl (max Λr Λd)), by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ (by omega)
  refine ⟨min cmax 1, lt_min hcmax zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad
    σ₀ a σ hsched hNaux hNout sX sZ hsX hsZ Ce kS hCe hc₀ hc₀upper hcr hcrupper
    hσf hlamC halloc
  have hsched' : IsSuccessorSchedule α q s Q σ₀ a σ
      (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout := by
    simpa only [hσf, hlamC] using hsched
  obtain ⟨tc, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper
    (by rw [hσf]; exact hσE) (by rw [hlamC]; exact hlamE)
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched'
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
  change RetainedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ
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
  obtain ⟨A, _hA, mo, _hmo, hop⟩ := uniform_native_kernel_operator_of_certificates
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw Kres
    (succSchedD D₀ N p (H + 1)) hDm kI.cker hcker
  change NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo at hop
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < min (ocDelta α q / 4) τe := lt_min (div_pos hδ (by norm_num)) hτe
  obtain ⟨ma, habs⟩ := retained_absorption_threshold hq.1 h128 hτ A CI
  refine ⟨Real.sqrt 2 * |Cpr|, max mc (max mr (max md (max (mo + 3) (max ma (j₀ + 3))))), ?_⟩
  intro C hC
  exact passage_strongEnergy_at_data hq Λl Λ hlength (by omega) h128 hζ φ₀ hφ₀ bw Q T₀ Ce τe kS
    r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr mc hNaux hc hprod
    hc0pos hc0le hcrpos hcrle mr hmr hradius md hdrift A mo hop ma habs C hC

end AVRegularity.IterationPassage.Passage
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.IterationPassage.ErrorJets
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.IterationPassage.ErrorJets.PassageCtx

/-! **The frame and the output of one passage at its data context**.

For a `PassageCtx` (the data of one passage with the common preparation produced by
`preservation_successor`, constants `C_Q, C_pr`):

* `PassageCtx.frame`: `PassageFrame` from the preparation with its buffer and quiet margin, the next
  family clauses, the cascade step, the propagated invariant (`StageInvariantPropagationData`) and
  the readout norm (`PassageReadoutNormStatement` applied to the readout clause of
  `NextFamilyClauses` at order zero);
* `PassageCtx.output`: `PassageOutput` from the retained energy and the comparison of
  `preservation_successor` and the data statements of the strong energy, the profiles and the jets.

The frame is stated with `D.α, D.q, D.Λ, D.ζ`; the ingredient statements with `α, q, Λ, ζ`. -/

open AVRegularity.IterationPassage.Passage

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  (c : PassageCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
    j₀ CQ Cpr Q T₀)

/-- The retained stage is a cascade stage. -/
theorem cascadeStep :
    IsCascadeStage c.D (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
      (succMenu c.Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) c.seed
      (c.G'.retained c.m H J) := by
  have h := IsCascadeStage.step c.hcascade c.hactual
  rw [c.hlevel] at h
  exact h

/-- The propagated invariant of the retained stage, in the form of `PassageFrame`. -/
theorem propagated (mStar : ℕ) (hm : mStar ≤ c.m)
    (h : StageInvariantPropagationData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ σ₀
      kI CI Cw j₀ mStar) :
    IsStageInvariant c.law (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
      φ₀ hφ₀ c.Mnat kI (c.tA + 3 * ocTau c.D.α c.D.q c.D.Λ c.m) c.tf
      (CI * c.D.eps (c.m - 1) ^ min (ocDelta c.D.α c.D.q / 4) τe)
      (CI * c.D.eps ((c.m - 1) - 1) ^ (c.D.q * min (ocDelta c.D.α c.D.q / 4) τe))
      (c.G'.retained c.m H J) := by
  rw [c.hDα, c.hDq, c.hDΛ]
  exact h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw
    c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hn c.hnM c.tA c.htA c.G c.G'
    c.hcascade c.hlevel c.hG c.hactual

/-- The readout norm of the frame from the readout clause of the next family. -/
theorem readoutNorm (Kres : ℕ) (C : ℝ) (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ)
    (hTw : Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ) ≤ C)
    (hnext : NextFamilyClauses c.law (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
      c.seedK c.freshK kI c.seed c.G (c.G'.retained c.m H J) c.m (succEta0 α q s) Kres
      (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card c.tp c.tf)
    (hrn : PassageReadoutNormStatement) :
    ‖readoutCLM c.m (c.D.eps (c.m - 1)) (succEta0 α q s) (c.G.mass c.law)
        ((c.G'.retained c.m H J).mass c.law)‖ ≤
      1 + C * c.D.eps (c.m - 1) ^ (5 * succEta0 α q s / 4) := by
  have hqD : 1 < c.D.q := c.hDq.symm ▸ hq.1
  have hΛD : 128 ≤ c.D.Λ := by rw [c.hDΛ]; exact hΛ
  have hE : 0 ≤ c.D.eps (c.m - 1) := by
    rw [OCData.eps]
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  have hpow : 0 ≤ c.D.eps (c.m - 1) ^ (succEta0 α q s + succEta0 α q s / 4) :=
    Real.rpow_nonneg hE _
  have hb := hrn c.m (c.D.eps (c.m - 1)) (succEta0 α q s) (rhoEnh c.D kI.cr c.m)
    (1 + Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ) *
      c.D.eps (c.m - 1) ^ (succEta0 α q s + succEta0 α q s / 4))
    (c.G.mass c.law) ((c.G'.retained c.m H J).mass c.law)
    (fun v => Construction.Preservation.Buffer.birth_compMass_pos hqD hΛD c.law v.1)
    (fun v => Construction.Preservation.Buffer.birth_compMass_pos hqD hΛD c.law v.1)
    (add_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) hpow))
    (fun X => hnext.2.2.2 0 X)
  have he : succEta0 α q s + succEta0 α q s / 4 = 5 * succEta0 α q s / 4 := by ring
  rw [he] at hb hpow
  exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hTw hpow))

/-- **The frame of the passage.** -/
theorem frame (Kres : ℕ) (C : ℝ) (mStar : ℕ) (hm : mStar ≤ c.m) (hq : IsAdmissibleQ α s q)
    (hΛ : 128 ≤ Λ) (hCp : Cpr ≤ C)
    (hTw : Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ) ≤ C)
    (hbuffer : c.s₀ + rhoStar c.D kI.c₀ c.m ^ 2 / c.D.κ c.m ≤ c.tp)
    (hnext : NextFamilyClauses c.law (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
      c.seedK c.freshK kI c.seed c.G (c.G'.retained c.m H J) c.m (succEta0 α q s) Kres
      (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card c.tp c.tf)
    (hsip : StageInvariantPropagationData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ
      σ₀ kI CI Cw j₀ mStar)
    (hrn : PassageReadoutNormStatement) :
    PassageFrame c.law (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p)
      (succMenu c.Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) c.seedK c.freshK φ₀ hφ₀ c.Mnat
      kI CI τe c.seed c.G (c.G'.retained c.m H J) c.m (succEta0 α q s) Kres
      (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p Nout Naux Q CQ C c.tA c.s₀
      c.tf c.tp c.Preg := by
  have hquietMargin : Set.Icc (c.tp - ocTauP c.D.α c.D.q c.D.Λ c.m)
      (c.tp + ocTauP c.D.α c.D.q c.D.Λ c.m) ⊆ ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ c.m := by
    rw [c.hDα, c.hDq, c.hDΛ, c.hDζ]
    exact c.hquietMargin
  exact ⟨commonPreparation_mono_constant (hC := hCp) (h := c.hprep), hbuffer, hquietMargin, hnext,
    c.cascadeStep, c.propagated mStar hm hsip, c.readoutNorm Kres C hq hΛ hTw hnext hrn⟩

/-- The strong energy at the pair from its data statement. -/
theorem strongOut (K Kres : ℕ) (Cs : ℝ) (mStar : ℕ) (hm : mStar ≤ c.m)
    (h : PassageRetainedStrongEnergyData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
      npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Cs mStar) :
    (c.toPair K Kres).StrongOut Cs := fun f Ain hf Y0 Y Yw Yk htr hsol =>
  h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK
    c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hn c.hnM c.tA c.s₀ c.htA c.hs₀ c.htf
    c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual c.tp c.Preg c.hprep f Ain hf Y0 Y Yw Yk htr
    hsol

/-- The profile clauses at the pair from their data statement. -/
theorem profOut (K : ℕ) (Kres : ℕ) (Pacc C : ℝ) (mStar : ℕ) (hm : mStar ≤ c.m)
    (hpoint : IsSeedPointwiseMolecular c.law kS c.seed c.tS c.tf)
    (hbuffer : c.s₀ + rhoStar c.D kI.c₀ c.m ^ 2 / c.D.κ c.m ≤ c.tp)
    (h : PassageProfilesData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux Nout npad σ₀
      sX sZ Ce kS kI CI Cw j₀ CQ Cpr C mStar) :
    (c.toPair K Kres).ProfOut s (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc (c.freshK (c.m - 1))
      C := fun f A hf U Uw Uk hU Y0 Y Yw Yk htr hsol =>
  h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK
    c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed hpoint c.m hm c.hn c.hnM c.tA c.s₀ c.htA c.hs₀
    c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual c.tp c.Preg c.hprep hbuffer c.hquietMargin
    f A hf U Uw Uk hU Y0 Y Yw Yk htr hsol

/-- The jets at the pair from the data statement of `passage_error_jets`. -/
theorem jetOut (K Kres : ℕ) (Cj : ℝ) (mStar : ℕ) (hm : mStar ≤ c.m)
    (hbuffer : c.s₀ + rhoStar c.D kI.c₀ c.m ^ 2 / c.D.κ c.m ≤ c.tp)
    (h : PassageErrorJetsData α s q ζ Λ φ₀ hφ₀ bw K Q T₀ r₀ D₀ τe H J N p nk Naux Nout npad σ₀ sX
      sZ Ce kS kI CI Cw j₀ CQ Cpr Cj mStar) :
    PassageErrorOutput (c.toPair K Kres).law (c.toPair K Kres).P (c.toPair K Kres).seedK
      (c.toPair K Kres).freshK (c.toPair K Kres).φ₀ (c.toPair K Kres).hφ₀ (c.toPair K Kres).G
      (c.toPair K Kres).Gr (c.toPair K Kres).m (c.toPair K Kres).p (c.toPair K Kres).N
      (c.toPair K Kres).depth (c.toPair K Kres).sX (c.toPair K Kres).sZ (c.toPair K Kres).K
      (c.toPair K Kres).η₀ (c.toPair K Kres).Q Cj (c.toPair K Kres).c₀ (c.toPair K Kres).s₀
      (c.toPair K Kres).tp (c.toPair K Kres).tf (c.toPair K Kres).Preg :=
  h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK
    c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.hpw c.m hm c.hn c.hnM c.tA c.s₀ c.htA c.hs₀
    c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual c.tp c.Preg c.hprep hbuffer c.hquietMargin

/-- **The output of the passage.** -/
theorem output (K Kres : ℕ) (Pacc Cs Cj C : ℝ) (mS mP mJ : ℕ) (hmS : mS ≤ c.m) (hmP : mP ≤ c.m)
    (hmJ : mJ ≤ c.m) (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hNK : Naux ≤ Kres)
    (hC0 : 0 ≤ C) (hCp : Cpr ≤ C) (hCs : Cs ≤ C) (hCj : Cj ≤ C)
    (hpoint : IsSeedPointwiseMolecular c.law kS c.seed c.tS c.tf)
    (hbuffer : c.s₀ + rhoStar c.D kI.c₀ c.m ^ 2 / c.D.κ c.m ≤ c.tp)
    (hrest : PreservationRest (hr := ScalarH) c.law
      (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀ hφ₀ c.G
      (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ Kres (succEta0 α q s) c.s₀
      c.tp c.tf kI.cr Q Cpr c.Preg)
    (hse : PassageRetainedStrongEnergyData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
      npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Cs mS)
    (hprof : PassageProfilesData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux Nout npad
      σ₀ sX sZ Ce kS kI CI Cw j₀ CQ Cpr C mP)
    (hpej : PassageErrorJetsData α s q ζ Λ φ₀ hφ₀ bw K Q T₀ r₀ D₀ τe H J N p nk Naux Nout npad σ₀
      sX sZ Ce kS kI CI Cw j₀ CQ Cpr Cj mJ) :
    PassageOutput c.law (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀
      hφ₀ c.G (c.G'.retained c.m H J) c.m p N (succSchedR r₀ J H) sX sZ K Naux s (succEta0 α q s)
      (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc Q C kI.cr kI.c₀ c.s₀ c.tp c.tf
      (c.freshK (c.m - 1)) c.Preg := by
  have hqD : 1 < c.D.q := c.hDq.symm ▸ hq.1
  have hΛD : 128 ≤ c.D.Λ := by rw [c.hDΛ]; exact hΛ
  have hE : 0 ≤ c.D.eps (c.m - 1) := by
    rw [OCData.eps]
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  exact (c.toPair K Kres).passageOutput s (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc
    (c.freshK (c.m - 1)) Cpr Cs Cpr Cj C hC0 hCp hCs hCp hCj hE hNK
    (fun v => div_pos (Construction.Preservation.Buffer.birth_compMass_pos hqD hΛD c.law v.1)
      (pow_pos (Construction.Preservation.Buffer.birth_compMarker_pos hqD hΛD c.law v.1) 2))
    ((c.toPair K Kres).energyOut_of_rest Cpr hrest) (c.strongOut K Kres Cs mS hmS hse)
    ((c.toPair K Kres).cmpOut_of_rest Cpr hrest)
    (c.profOut K Kres Pacc C mP hmP hpoint hbuffer hprof)
    (c.jetOut K Kres Cj mJ hmJ hbuffer hpej)

end AVRegularity.IterationPassage.ErrorJets.PassageCtx
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.IterationPassage.ErrorJets
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.IterationPassage.ErrorJets.PassageCtx

/-! **The output of one passage with the profile proposition proved at the pair**.

Conversions from data statements to the datum predicates:
`PassageCtx.clausesOut` (the data part of `PassageProfileClausesStatement` with the readout norm of
the frame) and `PassageCtx.bufferAt` (the molecular buffer at an order `n ≤ 2J`, truncated).
`PassageCtx.outputOfClauses` is `PassageOutput`, as `PassageCtx.output`, with the profile
hypothesis in the form `PassageProfileClausesStatement` and the buffer.

Special cases: `A = 0`; an empty family. -/

open AVRegularity.IterationPassage.Passage

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  (c : PassageCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
    j₀ CQ Cpr Q T₀)

/-- The profile proposition at the pair from its data statement and the readout norm. -/
theorem clausesOut (K Kres : ℕ) (Pacc Cn Cr Cj C : ℝ) (mStar : ℕ) (hm : mStar ≤ c.m)
    (hpoint : IsSeedPointwiseMolecular c.law kS c.seed c.tS c.tf)
    (hRn : ‖readoutCLM c.m (c.D.eps (c.m - 1)) (succEta0 α q s) (c.G.mass c.law)
        ((c.G'.retained c.m H J).mass c.law)‖ ≤
      1 + Cn * c.D.eps (c.m - 1) ^ (5 * succEta0 α q s / 4))
    (h : PassageProfileClausesData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux npad σ₀
      sX sZ Ce kS kI CI Cw j₀ Cn Cr Cj C mStar) :
    (c.toPair K Kres).ClausesOut s (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc
      (c.freshK (c.m - 1)) Cr Cj C := fun A hA U Y hUn hYn hjet =>
  h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK
    c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed hpoint c.m hm c.hn c.hnM c.tA c.s₀ c.htA c.hs₀
    c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual c.tp A c.hprep.2.1 hA U Y hRn hUn hYn
    hjet

/-- The molecular buffer at an order `n ≤ 2J`. -/
theorem bufferAt (K Kres Jr n : ℕ) (hn : n ≤ 2 * Jr) (Cb : ℝ) (mStar : ℕ) (hm : mStar ≤ c.m)
    (h : BufferDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
      kI CI Cw j₀ Jr CQ Cpr Q T₀ Cb mStar) :
    (c.toPair K Kres).BufferAt n := fun f U Uw Uk hU t ht => by
  obtain ⟨Un, hUn, -⟩ := h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat
    c.law c.hlaw c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hn c.hnM c.tA
    c.s₀ c.htA c.hs₀ c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual c.tp c.Preg c.hprep
    f (fun _ => 1) (Or.inl rfl) U Uw Uk hU t ht
  exact ⟨fun v => truncateTorusHk hn (Un v), fun v => hUn v⟩

/-- **The output of the passage**, with the profile proposition proved at the pair. -/
theorem outputOfClauses (K Kres Jr : ℕ) (Pacc Cs Cj Cn Creg Cb C : ℝ) (mS mP mJ mB : ℕ)
    (hmS : mS ≤ c.m) (hmP : mP ≤ c.m) (hmJ : mJ ≤ c.m) (hmB : mB ≤ c.m)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hNK : Naux ≤ Kres)
    (hJr : K + N + 2 * p + 4 ≤ 2 * Jr)
    (hC0 : 0 ≤ C) (hCp : Cpr ≤ C) (hCs : Cs ≤ C) (hCj : Cj ≤ C)
    (hR0 : 0 ≤ Creg) (hRp : Cpr ≤ Creg) (hRs : Cs ≤ Creg)
    (hpoint : IsSeedPointwiseMolecular c.law kS c.seed c.tS c.tf)
    (hbuffer : c.s₀ + rhoStar c.D kI.c₀ c.m ^ 2 / c.D.κ c.m ≤ c.tp)
    (hRn : ‖readoutCLM c.m (c.D.eps (c.m - 1)) (succEta0 α q s) (c.G.mass c.law)
        ((c.G'.retained c.m H J).mass c.law)‖ ≤
      1 + Cn * c.D.eps (c.m - 1) ^ (5 * succEta0 α q s / 4))
    (hrest : PreservationRest (hr := ScalarH) c.law
      (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀ hφ₀ c.G
      (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ Kres (succEta0 α q s) c.s₀
      c.tp c.tf kI.cr Q Cpr c.Preg)
    (hse : PassageRetainedStrongEnergyData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
      npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Cs mS)
    (hbuf : BufferDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
      σ₀ kI CI Cw j₀ Jr CQ Cpr Q T₀ Cb mB)
    (hprof : PassageProfileClausesData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux
      npad σ₀ sX sZ Ce kS kI CI Cw j₀ Cn Creg |Cj| C mP)
    (hpej : PassageErrorJetsData α s q ζ Λ φ₀ hφ₀ bw K Q T₀ r₀ D₀ τe H J N p nk Naux Nout npad σ₀
      sX sZ Ce kS kI CI Cw j₀ CQ Cpr Cj mJ) :
    PassageOutput c.law (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK φ₀
      hφ₀ c.G (c.G'.retained c.m H J) c.m p N (succSchedR r₀ J H) sX sZ K Naux s (succEta0 α q s)
      (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc Q C kI.cr kI.c₀ c.s₀ c.tp c.tf
      (c.freshK (c.m - 1)) c.Preg := by
  have hqD : 1 < c.D.q := c.hDq.symm ▸ hq.1
  have hΛD : 128 ≤ c.D.Λ := by rw [c.hDΛ]; exact hΛ
  have hE : 0 ≤ c.D.eps (c.m - 1) := by
    rw [OCData.eps]
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  have hπ : ∀ v, 0 < (c.toPair K Kres).Gr.mass (c.toPair K Kres).law v /
      (c.toPair K Kres).Gr.marker (c.toPair K Kres).law v ^ 2 := fun v =>
    div_pos (Construction.Preservation.Buffer.birth_compMass_pos hqD hΛD c.law v.1)
      (pow_pos (Construction.Preservation.Buffer.birth_compMarker_pos hqD hΛD c.law v.1) 2)
  have henergy := (c.toPair K Kres).energyOut_of_rest Cpr hrest
  have hstrong := c.strongOut K Kres Cs mS hmS hse
  have hcmp := (c.toPair K Kres).cmpOut_of_rest Cpr hrest
  have hjet := c.jetOut K Kres Cj mJ hmJ hbuffer hpej
  exact (c.toPair K Kres).passageOutput s (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc
    (c.freshK (c.m - 1)) Cpr Cs Cpr Cj C hC0 hCp hCs hCp hCj hE hNK hπ henergy hstrong hcmp
    ((c.toPair K Kres).profOut_of_clausesOut s (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc
      (c.freshK (c.m - 1)) Cpr Cs Cpr Creg Cj C hR0 hRs hRp hE hNK hπ henergy hstrong hcmp
      (c.bufferAt K Kres Jr _ hJr Cb mB hmB hbuf) hjet
      (c.clausesOut K Kres Pacc Cn Creg |Cj| C mP hmP hpoint hRn hprof))
    hjet

end AVRegularity.IterationPassage.ErrorJets.PassageCtx
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.IterationPassage.ErrorJets
namespace AVRegularity.IterationPassage.Passage

/-! **`iteration_passage` with the profile proposition proved at the pair**.

`iteration_passage_of_clauses`: the exact statement `IterationPassageStatement` from its
ingredients, with the profile ingredient in the form `PassageProfileClausesStatement` (module
`Passage.Profiles.ClausesStatement`; it follows from the six profile ingredients). The profile
proposition is fed at the pair with the readout norm of the frame (constant `√T_w`), the
regenerated block at the intermediate constant `C_reg = |C_p| + |C_s|`, the jets at `|C_j|`, and
the molecular buffer (`preparation_buffer`, a sixth ingredient with aligned quantifiers) at the
order `2J'`, `J' = ⌊(K+N+2p+1)/2⌋ + 2`:
`K + N + 2p + 4 ≤ 2J'` and `2J' + N + 2p ≤ N_aux` (from `IsPassageOrders` and the lower bound of
`N_aux` in `IsSuccessorSchedule`), `2J' ≤ N_aux ≤ K_res ≤ kI.Ks`.

The buffer is joined to the aligned quantifiers as an outer maximum.
Special cases: empty families; the first admissible level; `A = 0`. -/

/-- The buffer order `2J'` covers the order of the classical representatives. -/
theorem bufferOrder_ge (K N p : ℕ) : K + N + 2 * p + 4 ≤ 2 * ((K + N + 2 * p + 1) / 2 + 2) := by
  omega

/-- The buffer order is admissible: `2J' + N + 2p ≤ N_aux`. -/
theorem bufferOrder_le {K N p L Dn Acl Lc Naux : ℕ} (hord : 2 * (K + 2) + N + 2 * p + L ≤ Naux)
    (hNb : 4 * (N + Dn) + 2 * Acl + 16 + Dn + Lc + 6 * p ≤ Naux) :
    2 * ((K + N + 2 * p + 1) / 2 + 2) + N + 2 * p ≤ Naux := by
  omega

/-- The data part of `iteration_passage`, with the profile proposition proved at the pair. -/
theorem iterationPassageData_of_clauses {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {bw : ℝ} {K : ℕ} {Pacc Q T₀ : ℝ} {r₀ D₀ : ℕ} {τe : ℝ}
    {H J N p nk Naux Nout Kres npad : ℕ} {σ₀ : ℝ} {sX sZ : ℕ} {Ce : ℝ} {kS kI : InvConsts}
    {CI Cw : ℝ} {j₀ : ℕ} (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hNK : Naux ≤ Kres)
    (CQ Cp Cs Cj C : ℝ) (mps msip mse mprof mpej mStar : ℕ)
    (hmps : mps ≤ mStar) (hmsip : msip ≤ mStar) (hmse : mse ≤ mStar) (hmprof : mprof ≤ mStar)
    (hmpej : mpej ≤ mStar) (Jr : ℕ) (hJr : K + N + 2 * p + 4 ≤ 2 * Jr) (Creg Cb : ℝ) (mbuf : ℕ)
    (hmbuf : mbuf ≤ mStar) (hR0 : 0 ≤ Creg) (hRp : Cp ≤ Creg) (hRs : Cs ≤ Creg) (hC0 : 0 ≤ C) (hCp : Cp ≤ C) (hCs : Cs ≤ C) (hCj : Cj ≤ C)
    (hTw : Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ) ≤ C)
    (hps : PreservationSuccessorDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux
      Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Q T₀ Cp mps)
    (hsip : StageInvariantPropagationData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ
      σ₀ kI CI Cw j₀ msip)
    (hse : PassageRetainedStrongEnergyData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
      npad sX sZ σ₀ kI CI Cw j₀ CQ Cp Q T₀ Cs mse)
    (hprof : PassageProfileClausesData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux
      npad σ₀ sX sZ Ce kS kI CI Cw j₀
      (Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ)) Creg |Cj| C
      mprof)
    (hbuf : BufferDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
      σ₀ kI CI Cw j₀ Jr CQ Cp Q T₀ Cb mbuf)
    (hpej : PassageErrorJetsData α s q ζ Λ φ₀ hφ₀ bw K Q T₀ r₀ D₀ τe H J N p nk Naux Nout npad σ₀
      sX sZ Ce kS kI CI Cw j₀ CQ Cp Cj mpej)
    (hrn : PassageReadoutNormStatement) :
    IterationPassageData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux Nout Kres npad σ₀
      sX sZ Ce kS kI CI Cw j₀ C CQ mStar := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hseed hpoint m hm hn hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
  obtain ⟨tp, Preg, hprep, hbuffer, hquietMargin, hnext, hrest⟩ := hps D hDα hDq hDΛ hDζ hseq M hband
    hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hseed hpoint m (hmps.trans hm) hn
    hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
  let c : PassageCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cp Q T₀ :=
    ⟨D, hDα, hDq, hDΛ, hDζ, hseq, M, hband, hterm, Mnat, hMnat, law, hlaw, seedK, freshK, hfresh,
      seed, n, tS, tf, hseed, hpoint, m, hn, hnM, tA, s₀, htA, hs₀, htf, hT₀, G, G', hcascade,
      hlevel, hG, hactual, tp, Preg, hprep, hquietMargin⟩
  have hrest' : PreservationRest (hr := ScalarH) law
      (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ G
      (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ Kres (succEta0 α q s) s₀ tp tf
      kI.cr Q Cp Preg := hrest
  exact ⟨tp, Preg,
    c.frame Kres C msip (hmsip.trans hm) hq hΛ hCp hTw hbuffer hnext hsip hrn,
    c.outputOfClauses K Kres Jr Pacc Cs Cj _ Creg Cb C mse mprof mpej mbuf (hmse.trans hm)
      (hmprof.trans hm) (hmpej.trans hm) (hmbuf.trans hm) hq hΛ hNK hJr hC0 hCp hCs hCj hR0 hRp
      hRs hpoint hbuffer (c.readoutNorm Kres _ hq hΛ le_rfl hnext hrn) hrest' hse hbuf hprof
      hpej⟩

/-- The split form of `iteration_passage`, with the profile proposition proved at the pair. -/
theorem iterationPassageSplit_of_clauses
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hsip0 : StageInvariantPropagationTarget)
    (hpej0 : IterationPassage.Assembly.PassageErrorJetsStatement)
    (hprof0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageProfileClausesStatement α s q ζ)
    (hse0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedStrongEnergyStatement α s q ζ)
    (hrn : PassageReadoutNormStatement) : IterationPassageSplit := by
  classical
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λp, hΛp, hp⟩ := hps0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λi, hΛi, hi⟩ := stageInvariantPropagationSplit_of_target hsip0 α s hα₀ hα₁ hs₀ hs₁ q
    hq ζ hζ
  obtain ⟨Λj, hΛj, hj⟩ := passageErrorJetsSplit_of_statement hpej0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λf, hΛf, hf⟩ := hprof0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λe, hΛe, he⟩ := hse0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λu, hΛu, hu⟩ := buffer_statement α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max (max (max (max Λp Λi) (max Λj Λf)) Λe) Λu, by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cp, hcp, hp⟩ := hp Λ (by omega)
  obtain ⟨ci, hci, hi⟩ := hi Λ (by omega)
  obtain ⟨cj, hcj, hj⟩ := hj Λ (by omega)
  obtain ⟨cf, hcf, hf⟩ := hf Λ (by omega)
  obtain ⟨ce, hce, he⟩ := he Λ (by omega)
  obtain ⟨cu, hcu, hu⟩ := hu Λ (by omega)
  refine ⟨min (min (min (min cp ci) (min cj cf)) ce) cu,
    lt_min (lt_min (lt_min (lt_min hcp hci) (lt_min hcj hcf)) hce) hcu, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK hPacc Q T₀ hQ hT₀ hPQ
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    hsched hNaux hNout hfloor L horders hwidths
  obtain ⟨SXp, SZp, Kp, hp⟩ := hp φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched
    hNaux hNout hfloor
  obtain ⟨SXj, SZj, hj⟩ := hj φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK
    hPacc Q T₀ hQ hT₀ hPQ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad σ₀ a σ hsched hNaux hNout hfloor L horders hwidths
  obtain ⟨SXf, SZf, Kf, hf⟩ := hf φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK
    hPacc Q T₀ hQ hT₀ hPQ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad σ₀ a σ hsched hNaux hNout L horders hwidths
  have he := he φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched
    hNaux hNout
  refine ⟨max (max SXp SXj) (max SXf
      (max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2)),
    max (max SZp SZj) (max SZf
      (max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2)),
    max Kp Kf, ?_⟩
  intro sX sZ hSX hSZ Ce kS hCe hc₀ hc₀upper0 hcr hcrupper hσf hlamC halloc hKs hKan hLan hJm
  have hc₀upper := hc₀upper0.trans (min_le_left _ _)
  have hcu' : kS.c₀ ≤ cu := hc₀upper0.trans (min_le_right _ _)
  have hcp' : kS.c₀ ≤ cp := hc₀upper.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hci' : kS.c₀ ≤ ci := hc₀upper.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hcj' : kS.c₀ ≤ cj := hc₀upper.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcf' : kS.c₀ ≤ cf := hc₀upper.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hce' : kS.c₀ ≤ ce := hc₀upper.trans (min_le_right _ _)
  have hσf' : 0 < kS.σf := hσf.symm ▸ hσE
  have hlamC' : 0 < kS.lamC := hlamC.symm ▸ hlamE
  have hsched' : IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀))
      kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout := by
    simpa only [hσf, hlamC] using hsched
  have hSXp : SXp ≤ sX := ((le_max_left _ _).trans (le_max_left _ _)).trans hSX
  have hSXj : SXj ≤ sX := ((le_max_right _ _).trans (le_max_left _ _)).trans hSX
  have hSXf : SXf ≤ sX := ((le_max_left _ _).trans (le_max_right _ _)).trans hSX
  have hSXe : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hSX
  have hSZp : SZp ≤ sZ := ((le_max_left _ _).trans (le_max_left _ _)).trans hSZ
  have hSZj : SZj ≤ sZ := ((le_max_right _ _).trans (le_max_left _ _)).trans hSZ
  have hSZf : SZf ≤ sZ := ((le_max_left _ _).trans (le_max_right _ _)).trans hSZ
  have hSZe : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hSZ
  obtain ⟨tp, CHp, Υp, hCHp, hΥp, hp⟩ := hp sX sZ hSXp hSZp Ce kS hCe hc₀ hcp' hcr hcrupper hσf
    hlamC halloc ((le_max_left _ _).trans hKs) ((le_max_left _ _).trans hKan)
    ((le_max_left _ _).trans hLan) ((le_max_left _ _).trans hJm)
  obtain ⟨ti, CHi, Υi, hCHi, hΥi, hi⟩ := hi φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hci' hcr hcrupper hσf' hlamC'
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched' hNaux hNout halloc hSXe hSZe
  obtain ⟨tj, CHj, Υj, hCHj, hΥj, hj⟩ := hj sX sZ hSXj hSZj Ce kS hCe hc₀ hcj' hcr hcrupper hσf
    hlamC halloc
  obtain ⟨tf', CHf, Υf, hCHf, hΥf, hf⟩ := hf sX sZ hSXf hSZf Ce kS hCe hc₀ hcf' hcr hcrupper hσf
    hlamC halloc ((le_max_right _ _).trans hKs) ((le_max_right _ _).trans hKan)
    ((le_max_right _ _).trans hLan) ((le_max_right _ _).trans hJm)
  obtain ⟨te, CHe, Υe, hCHe, hΥe, he⟩ := he sX sZ hSXe hSZe Ce kS hCe hc₀ hce' hcr hcrupper hσf
    hlamC halloc
  obtain ⟨tu, CHu, Υu, hCHu, hΥu, hu⟩ := hu φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hcu' hcr hcrupper hσf' hlamC'
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched' hNaux hNout halloc
  refine ⟨certificateThresholdJoin (certificateThresholdJoin (certificateThresholdJoin
      (certificateThresholdJoin tp ti) (certificateThresholdJoin tj tf')) te) tu,
    max (max (max (max CHp CHi) (max CHj CHf)) CHe) CHu,
    max (max (max (max Υp Υi) (max Υj Υf)) Υe) Υu,
    (hCHp.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))).trans
      (le_max_left _ _),
    (hΥp.trans_le ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))).trans_le
      (le_max_left _ _), ?_⟩
  intro kI hkI0
  have hkI := invariant_admissible_threshold_left hkI0
  have hkI_u := invariant_admissible_threshold_right hkI0
  have hk1 := invariant_admissible_threshold_left hkI
  have hkI_e := invariant_admissible_threshold_right hkI
  have hk2 := invariant_admissible_threshold_left hk1
  have hk3 := invariant_admissible_threshold_right hk1
  have hkI_p := invariant_admissible_threshold_left hk2
  have hkI_i := invariant_admissible_threshold_right hk2
  have hkI_j := invariant_admissible_threshold_left hk3
  have hkI_f := invariant_admissible_threshold_right hk3
  obtain ⟨CIp, Cwp, hp⟩ := hp kI hkI_p
  obtain ⟨CIi, Cwi, hi⟩ := hi kI hkI_i
  obtain ⟨CIj, Cwj, hj⟩ := hj kI hkI_j
  obtain ⟨CIf, Cwf, hf⟩ := hf kI hkI_f
  obtain ⟨CIe, Cwe, he⟩ := he kI hkI_e
  obtain ⟨CIu, Cwu, hu⟩ := hu kI hkI_u
  refine ⟨max (max (max (max CIp CIi) (max CIj CIf)) CIe) CIu,
    max (max (max (max Cwp Cwi) (max Cwj Cwf)) Cwe) Cwu, ?_⟩
  intro CI Cw j₀ hledger0 hstart0
  have hledger : IsLedgerAdmissible Ce CI Cw (max (max (max CIp CIi) (max CIj CIf)) CIe)
      (max (max (max Cwp Cwi) (max Cwj Cwf)) Cwe) :=
    ⟨hledger0.1, (le_max_left _ _).trans hledger0.2.1, (le_max_left _ _).trans hledger0.2.2.1,
      hledger0.2.2.2⟩
  have hLu : IsLedgerAdmissible Ce CI Cw CIu Cwu :=
    ⟨hledger0.1, (le_max_right _ _).trans hledger0.2.1, (le_max_right _ _).trans hledger0.2.2.1,
      hledger0.2.2.2⟩
  have hLp : IsLedgerAdmissible Ce CI Cw CIp Cwp :=
    ⟨hledger.1, ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      hledger.2.1, ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      hledger.2.2.1, hledger.2.2.2⟩
  have hLi : IsLedgerAdmissible Ce CI Cw CIi Cwi :=
    ⟨hledger.1, ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      hledger.2.1, ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      hledger.2.2.1, hledger.2.2.2⟩
  have hLj : IsLedgerAdmissible Ce CI Cw CIj Cwj :=
    ⟨hledger.1, ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      hledger.2.1, ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      hledger.2.2.1, hledger.2.2.2⟩
  have hLf : IsLedgerAdmissible Ce CI Cw CIf Cwf :=
    ⟨hledger.1, ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      hledger.2.1, ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      hledger.2.2.1, hledger.2.2.2⟩
  have hLe : IsLedgerAdmissible Ce CI Cw CIe Cwe :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1, (le_max_right _ _).trans hledger.2.2.1,
      hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  have hstart : IsCarrierStart α q Λ bw (max (max (max CHp CHi) (max CHj CHf)) CHe)
      (max (max (max Υp Υi) (max Υj Υf)) Υe) j₀ :=
    IsCarrierStart.mono hA hT (le_max_left _ _) (le_max_left _ _)
      ((zero_le_one.trans hCHp).trans
        ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
      (hΥp.le.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
      hstart0
  have hSu := IsCarrierStart.mono hA hT (le_max_right _ _) (le_max_right _ _)
    (zero_le_one.trans hCHu) hΥu.le hstart0
  have hSp := IsCarrierStart.mono hA hT
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (zero_le_one.trans hCHp) hΥp.le hstart
  have hSi := IsCarrierStart.mono hA hT
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (zero_le_one.trans hCHi) hΥi.le hstart
  have hSj := IsCarrierStart.mono hA hT
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (zero_le_one.trans hCHj) hΥj.le hstart
  have hSf := IsCarrierStart.mono hA hT
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (zero_le_one.trans hCHf) hΥf.le hstart
  have hSe := IsCarrierStart.mono hA hT (le_max_right _ _) (le_max_right _ _)
    (zero_le_one.trans hCHe) hΥe.le hstart
  obtain ⟨Cp, CQ, mp, hp⟩ := hp CI Cw j₀ hLp hSp
  obtain ⟨mi, hi⟩ := hi CI Cw j₀ hLi hSi
  obtain ⟨Cj, mj, hj⟩ := hj CI Cw j₀ hLj hSj CQ Cp
  obtain ⟨Cs, me, he⟩ := he CI Cw j₀ hLe hSe CQ Cp
  obtain ⟨Cf, mf, hf⟩ := hf CI Cw j₀ hLf hSf
    (Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ)) (|Cp| + |Cs|)
    |Cj| (by positivity) (abs_nonneg Cj)
  have hNb : 4 * (N + succSchedD D₀ N p (H + 1)) + 2 * Acl + 16 + succSchedD D₀ N p (H + 1) + Lc +
      6 * p ≤ Naux := (le_max_left _ _).trans hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk := bufferOrder_le horders.1 hNb
  have hKsI : Kres ≤ kI.Ks := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hkI0
    exact h
  obtain ⟨Cb, mu, hu⟩ := hu CI Cw j₀ hLu hSu ((K + N + 2 * p + 1) / 2 + 2) hk
    (((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hk)).trans (hNaux.trans hKsI))
    CQ Cp
  have hTw0 : 0 ≤ Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ) :=
    Real.sqrt_nonneg _
  refine ⟨|Cp| + |Cs| + |Cj| + |Cf| +
      Real.sqrt ((wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card : ℝ),
    CQ, max (max (max (max mp mi) (max mj mf)) me) mu, ?_⟩
  exact iterationPassageData_of_clauses hq h128 hNaux CQ Cp Cs Cj _ mp mi me mf mj _
    (((le_max_left mp mi).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      (le_max_left _ _))
    (((le_max_right mp mi).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))
    (((le_max_right mj mf).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      (le_max_left _ _))
    (((le_max_left mj mf).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      (le_max_left _ _))
    ((K + N + 2 * p + 1) / 2 + 2) (bufferOrder_ge K N p) (|Cp| + |Cs|) Cb mu (le_max_right _ _)
    (by positivity) (by linarith only [le_abs_self Cp, abs_nonneg Cs])
    (by linarith only [le_abs_self Cs, abs_nonneg Cp])
    (by positivity)
    (by linarith only [le_abs_self Cp, abs_nonneg Cs, abs_nonneg Cj, abs_nonneg Cf, hTw0])
    (by linarith only [le_abs_self Cs, abs_nonneg Cp, abs_nonneg Cj, abs_nonneg Cf, hTw0])
    (by linarith only [le_abs_self Cj, abs_nonneg Cp, abs_nonneg Cs, abs_nonneg Cf, hTw0])
    (by linarith only [abs_nonneg Cp, abs_nonneg Cs, abs_nonneg Cj, abs_nonneg Cf])
    hp hi (he Cs le_rfl)
    (hf _ (by linarith only [le_abs_self Cf, abs_nonneg Cp, abs_nonneg Cs, abs_nonneg Cj, hTw0]))
    hu hj hrn

/-- **`iteration_passage`**, with the profile proposition proved at the pair. -/
theorem iteration_passage_of_clauses
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hsip0 : StageInvariantPropagationTarget)
    (hpej0 : IterationPassage.Assembly.PassageErrorJetsStatement)
    (hprof0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageProfileClausesStatement α s q ζ)
    (hse0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedStrongEnergyStatement α s q ζ)
    (hrn : PassageReadoutNormStatement) :
    IterationPassage.Assembly.IterationPassageStatement :=
  iterationPassage_of_split (iterationPassageSplit_of_clauses hps0 hsip0 hpej0 hprof0 hse0 hrn)

/-! **`iteration_passage` from two statements of the preservation argument and the six profile
ingredients**.

`iteration_passage_of_profile_ingredients`: the exact statement `IterationPassageStatement` from

* the statements `preservation_successor` and `successor_bill` (text copies
  `PreservationSuccessorStatement`, `SuccessorBillStatement`), and
* the six profile ingredients.

Everything else is proved: `stage_invariant_propagation`,
`passage_error_jets` from `successor_bill` (module `ErrorJets.OfSuccessorBill`), the readout norm
and the retained strong energy, the profile proposition from its ingredients, and the assembly
`iteration_passage_of_clauses`. -/

/-- **`iteration_passage`** from `preservation_successor`, `successor_bill` and the six profile
ingredients. -/
theorem iteration_passage_of_profile_ingredients
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ)
    (hsm : SmoothRepOfHigherStatement)
    (hr0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageProfilesRegularStatement α s q ζ)
    (hc0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedCovarianceStatement α s q ζ)
    (hl0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedLiftStatement α s q ζ)
    (hd0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageDiscardedProfilesStatement α s q ζ)
    (he0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageErrorProfileStatement α s q ζ) :
    IterationPassage.Assembly.IterationPassageStatement :=
  iteration_passage_of_clauses hps0 Providers.stage_invariant_propagation
    (passage_error_jets_of_successor_bill hbill)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
      passageProfileClauses_of_ingredients hsm hr0 hc0 hl0 hd0 he0 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
      passageRetainedStrongEnergy α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    passageReadoutNorm

end AVRegularity.IterationPassage.Passage
end
end
end
