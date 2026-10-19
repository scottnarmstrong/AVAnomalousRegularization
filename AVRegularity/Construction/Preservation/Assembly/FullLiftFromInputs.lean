-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.Ledger.TaggedRecurrence
import AVRegularity.Proofs.Results.Construction.SuccessorExists
import AVRegularity.Proofs.ComplexContext.Assemble
import AVRegularity.Construction.Preservation.FullLift.UniformNativeLiftEnergy
public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfIngredients

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly

/-! Conditional preservation assembly with one preparation chosen before the datum.
The open preparation producer uses PreparationJointOfInputs for its endpoint and
chart adapters, and takes the shared cover as one named input.
The preparation constant is fixed before applying the energy and bill producers; only
then are the output constants enlarged. Lift floors precede the seed constants.

Empty component sums and suprema keep their actual definitions, and an edgeless seed is
allowed. Nontrivial root spaces are supplied, and one seed-reserve floor is chosen before Ce
and kS. The explicit lift floors are
uniform in those seed constants. Quiet matching is unchanged. -/

theorem preservation_successor_of_ingredients_core (α s q : ℝ) (ζ : ℝ → ℝ)
    (hp0 : CommonPreparationProductionStatement α s q ζ)
    (he0 : PreparedRetainedEnergyProductionStatement α s q ζ)
    (hb0 : SuccessorBillStatement α s q ζ) :
    PreservationSuccessorStatement α s q ζ := by
  classical
  obtain ⟨Λp, hΛp, hp⟩ := hp0
  obtain ⟨Λe, hΛe, he⟩ := he0
  obtain ⟨Λb, hΛb, hb⟩ := hb0
  refine ⟨max (max Λp Λe) Λb, by omega, ?_⟩
  intro Λ hΛ
  obtain ⟨cp, hcp, hp⟩ := hp Λ (by omega)
  obtain ⟨ce, hce, he⟩ := he Λ (by omega)
  obtain ⟨cb, hcb, hb⟩ := hb Λ (by omega)
  refine ⟨min (min cp ce) cb, lt_min (lt_min hcp hce) hcb, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    r₀ D₀ τe lamE σE hτe hlamE hσE
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux hNout hrecon
  obtain ⟨Kneed, hp⟩ := hp φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ r₀ D₀ τe lamE σE hτe hlamE hσE
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux hNout
  have he := he φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ r₀ D₀ τe lamE σE hτe hlamE hσE
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux hNout
  let floor := max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2
  refine ⟨floor, floor, Kneed, ?_⟩
  intro sX sZ hSX hSZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc hKs hKan hLan hJm
  have hcp' : kS.c₀ ≤ cp := hc₀upper.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hce' : kS.c₀ ≤ ce := hc₀upper.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcb' : kS.c₀ ≤ cb := hc₀upper.trans (min_le_right _ _)
  obtain ⟨tp, CHp, Υp, hCHp, hΥp, hp⟩ := hp sX sZ (by omega) (by omega)
    Ce kS hCe hc₀ hcp' hcr hcrupper hσf hlamC halloc hKs hKan hLan hJm
  obtain ⟨te, CHe, Υe, hCHe, hΥe, he⟩ := he sX sZ (by omega) (by omega)
    Ce kS hCe hc₀ hce' hcr hcrupper hσf hlamC halloc
  have hsched' : IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀))
      kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout := by
    simpa only [hσf, hlamC] using hsched
  obtain ⟨tb, CHb, Υb, hCHb, hΥb, hb⟩ := hb φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hcb' hcr hcrupper
    (hσf.symm ▸ hσE) (hlamC.symm ▸ hlamE)
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched' hNaux hNout hrecon halloc
    hSX hSZ
  refine ⟨certificateThresholdJoin (certificateThresholdJoin tp te) tb,
    max (max CHp CHe) CHb, max (max Υp Υe) Υb,
    hCHp.trans ((le_max_left _ _).trans (le_max_left _ _)),
    hΥp.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro kI hkI
  have hkP := invariant_admissible_threshold_left (invariant_admissible_threshold_left hkI)
  have hkE := invariant_admissible_threshold_right (invariant_admissible_threshold_left hkI)
  have hkB := invariant_admissible_threshold_right hkI
  obtain ⟨CIp, Cwp, hp⟩ := hp kI hkP
  obtain ⟨CIe, Cwe, he⟩ := he kI hkE
  obtain ⟨CIb, Cwb, hb⟩ := hb kI hkB
  refine ⟨max (max CIp CIe) CIb, max (max Cwp Cwe) Cwb, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLp : IsLedgerAdmissible Ce CI Cw CIp Cwp :=
    ⟨hledger.1, ((le_max_left _ _).trans (le_max_left _ _)).trans hledger.2.1,
      ((le_max_left _ _).trans (le_max_left _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLe : IsLedgerAdmissible Ce CI Cw CIe Cwe :=
    ⟨hledger.1, ((le_max_right _ _).trans (le_max_left _ _)).trans hledger.2.1,
      ((le_max_right _ _).trans (le_max_left _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLb : IsLedgerAdmissible Ce CI Cw CIb Cwb :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1,
      (le_max_right _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  obtain ⟨Cp, CQ, mp, hp⟩ := hp CI Cw j₀ hLp (IsCarrierStart.mono hA hT
    ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_left _ _).trans (le_max_left _ _))
    (zero_le_one.trans hCHp) hΥp.le hstart)
  obtain ⟨CE, me, he⟩ := he CI Cw j₀ hLe (IsCarrierStart.mono hA hT
    ((le_max_right _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
    (zero_le_one.trans hCHe) hΥe.le hstart) CQ Cp
  obtain ⟨CB, c, mb, hc, hb⟩ := hb CI Cw j₀ hLb (IsCarrierStart.mono hA hT
    (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHb) hΥb.le hstart) CQ Cp
  let C := |Cp| + |CE| + |CB| + CB ^ 2 + 1
  have hCp : Cp ≤ C := (le_abs_self _).trans (by dsimp [C]; linarith only [abs_nonneg CE, abs_nonneg CB, sq_nonneg CB])
  have hCE : CE ≤ C := (le_abs_self _).trans (by dsimp [C]; linarith only [abs_nonneg Cp, abs_nonneg CB, sq_nonneg CB])
  have hCB : CB ≤ C := (le_abs_self _).trans (by dsimp [C]; linarith only [abs_nonneg Cp, abs_nonneg CE, sq_nonneg CB])
  have hCBsq : CB ^ 2 ≤ C := by dsimp [C]; linarith only [abs_nonneg Cp, abs_nonneg CE, abs_nonneg CB]
  refine ⟨C, CQ, max (max mp me) mb, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed hpoint m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
  obtain ⟨tprep, Preg, hprep, hbuffer, hquietMargin⟩ := hp D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed hpoint m (by omega) hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
  obtain ⟨hnext, henergy⟩ := he D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual tprep Preg hprep
  refine ⟨tprep, Preg, commonPreparation_mono_constant (hC := hCp) (h := hprep),
    hbuffer, hquietMargin, hnext, ?_⟩
  intro f Ain hAin
  have hAin' : 0 ≤ Ain := (Real.sqrt_nonneg _).trans hAin
  have hE : 0 ≤ D.eps (m - 1) := by
    rw [OCData.eps, hDq, hDΛ]
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  have heps : 0 ≤ D.eps m := by
    rw [OCData.eps, hDq, hDΛ]
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  constructor
  · intro k hk
    obtain ⟨Y0, htrace, hsol⟩ := henergy f Ain hAin k hk
    refine ⟨Y0, htrace, ?_⟩
    exact retainedSolution_mono_constant (h := hsol) (hA := hAin') (hE := hE) (hC := hCE)
  · intro Y0 Y Yw Yk htrace hsol
    obtain ⟨hbill, hcomp⟩ := hb D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
      seedK freshK hfresh seed n tS tf hseed hpoint m (by omega) hn hnM
      tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual tprep Preg hprep hquietMargin
      f Ain hAin Y0 Y Yw Yk htrace hsol
    have hcI : 0 ≤ kI.c₀ := (hkB.1.symm ▸ hc₀).le
    have hcrI : 0 ≤ kI.cr := (hkB.2.1.symm ▸ hcr).le
    have hbn := succBill_nonneg G m kI.c₀ kI.cr c σ₀ (succEta0 α q s)
      p N Lc Lf Acl J H tprep tf
      (succTheta1 α q s σ₀ (succDstar D₀ N p H))
      (succTheta2 α q s σ₀ (succDstar D₀ N p H)) hE heps hcI hcrI
    have hpow : 0 ≤ D.eps (m - 1) ^ Q := Real.rpow_nonneg hE _
    have hbill' := hbill.trans (mul_le_mul_of_nonneg_right (le_abs_self CB) hpow)
    have hres : CB * Ain * succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s)
        p N Lc Lf Acl J H tprep tf
        (succTheta1 α q s σ₀ (succDstar D₀ N p H))
        (succTheta2 α q s σ₀ (succDstar D₀ N p H)) ≤ C * D.eps (m - 1) ^ Q * Ain := by
      calc
        _ ≤ |CB| * Ain * succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s)
            p N Lc Lf Acl J H tprep tf
            (succTheta1 α q s σ₀ (succDstar D₀ N p H))
            (succTheta2 α q s σ₀ (succDstar D₀ N p H)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hAin') hbn
        _ ≤ |CB| * Ain * (|CB| * D.eps (m - 1) ^ Q) :=
          mul_le_mul_of_nonneg_left hbill' (mul_nonneg (abs_nonneg _) hAin')
        _ = CB ^ 2 * D.eps (m - 1) ^ Q * Ain := by rw [← sq_abs CB]; ring
        _ ≤ C * D.eps (m - 1) ^ Q * Ain :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCBsq hpow) hAin'
    exact comparisonClauses_mono (h := hcomp) (hres := hres)
      (he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB hpow) hAin')

theorem preservation_successor_of_ingredients (α s q : ℝ) (ζ : ℝ → ℝ)
    (hp0 : CommonPreparationProductionStatement α s q ζ)
    (he0 : PreparedRetainedEnergyProductionStatement α s q ζ)
    (hb0 : SuccessorBillStatement α s q ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (C CQ : ℝ) (mStar : ℕ),
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
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ C p Nout Naux s₀ tf tp Preg ∧
      s₀ + rhoStar D kI.c₀ m ^ 2 / D.κ m ≤ tp ∧
      Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m ∧
      NextFamilyClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
        kI seed G (G'.retained m H J) m (succEta0 α q s) Kres
        (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card tp tf ∧
      ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
        weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
        (∀ k ≤ Kres, ∃ Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk k (hr v'.1.root),
          IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 ∧
          RetainedSolutionClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
            φ₀ hφ₀ (G'.retained m H J) m k kI.cr C Q Ain tp tf Y0) ∧
        ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
          (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
          (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
          (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ →
            TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
          IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
          (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
            seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
            (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
          ComparisonClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
            G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) s₀
            tp tf (C * D.eps (m - 1) ^ Q * Ain) (C * D.eps (m - 1) ^ Q * Ain) f Y :=
  preservation_successor_of_ingredients_core α s q ζ hp0 he0 hb0

/-! Assemble the retained stage certificates from the context and ledger inputs,
the marked-ledger recurrence, the kernel regularizers and the structural provenance certificates. -/

section
open AVRegularity.Construction.Preservation.FullLift

private theorem template_compact {φ₀ : Vec 2 → ℝ}
    (h : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall) :
    HasCompactSupport φ₀ := by
  let L := (Homogenization.HilbertVec.continuousLinearEquivVec 2).symm
  have heq : Analysis.Convolution.closedEuclideanUnitBall = L ⁻¹' Metric.closedBall 0 1 := by
    ext z
    simp only [Analysis.Convolution.closedEuclideanUnitBall, Set.mem_ofPred_eq, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right, Analysis.Convolution.euclideanNorm]
    rfl
  have hc : IsCompact Analysis.Convolution.closedEuclideanUnitBall := by
    rw [heq]
    exact L.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall 0 1)
  exact HasCompactSupport.of_support_subset_isCompact hc h

/-- All retained stage certificates, with the producer reserves and pre-data constants. -/
theorem retained_stage_certificates (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : RetainedStageCertificatesStatement α s q ζ := by
  classical
  obtain ⟨Λc, hΛc, hc⟩ := Providers.successor_context_certified α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hl⟩ := Providers.successor_ledger α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λk, hΛk, hk⟩ := Ledger.retained_marked_ledger α s q ζ hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λc (max Λl Λk), by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cc, hcc, hc⟩ := hc Λ (by omega)
  obtain ⟨cl, hcl, hl⟩ := hl Λ (by omega)
  obtain ⟨ck, hck, hk⟩ := hk Λ (by omega)
  refine ⟨min cc (min cl ck), lt_min hcc (lt_min hcl hck), ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨tc, CHc, Υc, hCHc, hΥc, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  obtain ⟨tl, hl⟩ := hl φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans ((min_le_right _ _).trans (min_le_left _ _))) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  obtain ⟨tk, CHk, Υk, hCHk, hΥk, hk⟩ := hk φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans ((min_le_right _ _).trans (min_le_right _ _))) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc
  obtain ⟨cf, _hcf, mf, hmf, hf⟩ := uniform_cascade_kernel_regularizers φ₀
    (template_compact hφsupport) hφsmooth hφ₀ nk.toPNat' α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ h128
  let tbase := certificateThresholdJoin tc (certificateThresholdJoin tl tk)
  let thr : InvConsts := { tbase with cker := fun j => max (tbase.cker j) (cf j) }
  let CH := max CHc CHk
  let Υ := max Υc (max Υk 100)
  have hCH : 1 ≤ CH := hCHc.trans (le_max_left _ _)
  have hΥ : 0 < Υ := hΥc.trans_le (le_max_left _ _)
  have hΥ100 : (100 : ℝ) ≤ Υ := (le_max_right _ _).trans (le_max_right _ _)
  let κ := Providers.ComplexContext.complexContextKappa bw 0
  have hκ : MajOK bw κ := Providers.ComplexContext.complexContextKappa_majOK le_rfl
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  have hb : IsInvariantAdmissible kS tbase kI H J N p nk Kres Lpr Lc Lf σ₀
      (ocDelta α q) q (ocC α q) := invariant_admissible_of_threshold_bounds (a := tbase) (b := thr)
    le_rfl le_rfl le_rfl (fun _ => le_rfl) (fun _ => le_max_left _ _) hkI
  have hcI := invariant_admissible_threshold_left hb
  have hlkI := invariant_admissible_threshold_right hb
  have hlI := invariant_admissible_threshold_left hlkI
  have hkI' := invariant_admissible_threshold_right hlkI
  obtain ⟨CIc, Cwc, hc⟩ := hc kI hcI
  obtain ⟨CIl, Cwl, hl⟩ := hl CH Υ hCH hΥ100 κ hκ kI hlI
  obtain ⟨CIk, Cwk, hk⟩ := hk kI hkI'
  refine ⟨max CIc (max CIl CIk), max Cwc (max Cwl Cwk), ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLc : IsLedgerAdmissible Ce CI Cw CIc Cwc :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1,
      (le_max_left _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLl : IsLedgerAdmissible Ce CI Cw CIl Cwl :=
    ⟨hledger.1, ((le_max_left _ _).trans (le_max_right _ _)).trans hledger.2.1,
      ((le_max_left _ _).trans (le_max_right _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLk : IsLedgerAdmissible Ce CI Cw CIk Cwk :=
    ⟨hledger.1, ((le_max_right _ _).trans (le_max_right _ _)).trans hledger.2.1,
      ((le_max_right _ _).trans (le_max_right _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  have hsc := IsCarrierStart.mono hA hT (le_max_left _ _) (le_max_left _ _)
    (zero_le_one.trans hCHc) hΥc.le hstart
  have hsk := IsCarrierStart.mono hA hT (le_max_right _ _)
    ((le_max_left _ _).trans (le_max_right _ _)) (zero_le_one.trans hCHk) hΥk.le hstart
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hLc hsc
  obtain ⟨ml, hl⟩ := hl CI Cw j₀ hstart
  obtain ⟨mk, hk⟩ := hk CI Cw j₀ hLk hsk
  refine ⟨max mc (max ml (max mk (mf + 1))), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  have hmc : mc ≤ m := by omega
  have hml : ml ≤ m := by omega
  have hmk : mk ≤ m := by omega
  have hmf' : mf ≤ m - 1 := by omega
  have hm2 : 2 ≤ m := by omega
  have hcontext := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmc hn hnM G G' hcascade hlevel ⟨tA, htA, hG⟩ hactual
  have hwitness := hl D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m ⟨hLl, hml⟩ hn hnM G G' hcascade hlevel
    ⟨tA, htA, hG⟩ hactual
  have hmarked := hk D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmk hn hnM tA htA G G' hcascade hlevel hG hactual
    κ hwitness
  obtain ⟨hseedlevel, _, _, _, _, _, _, hseedInv, _⟩ := hseed
  have htags := Providers.CascadeInvariants.hasTags_of_cascade hseedInv.2.1 hcascade
  obtain ⟨_, _, _, _, _, _, _, _, hkseed, _⟩ := id hseedInv
  have hwidthSeed : ∀ v u (γ : seed.fam.Γ v u),
      (seed.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK v u γ).width =
        (seed.fam.identity v u γ).record.width := fun v u γ => (hkseed v u γ).2.1
  have hwidth := cascade_kernel_width_matching _ _ seed G hcascade seedK freshK hseedInv.2.1
    hwidthSeed 1 (fun b hb hbn => (hfresh b hb (by omega)).1) (by omega)
  have hborn : (freshK (G.level - 1)).width =
      (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p).rb (G.level - 1) := by
    exact (hfresh _ (by omega) (by omega)).1
  obtain ⟨hnatural, hwidthGr⟩ := retained_structural_certificates _ _ seedK freshK G G'
    htags hwidth hborn hactual m H J
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hkap : 0 < D.kap G.level := by
    unfold OCData.kap
    rw [hterm]
    exact CycleReference.bandChain_pos (by omega) hζ hband (Nat.min_le_right _ _)
  have hcell : 0 ≤ D.cellScaleSq G.level := div_nonneg (sq_nonneg _) hkap.le
  have hshift : (G'.retained m H J).IsShiftInvariant :=
    (successor_shift_invariant_of_cellScaleSq_nonneg hζD hcell hG.1 hG.2.2.2.1
      hactual).restrict _ _
  have hGrCascade : IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed (G'.retained m H J) := by
    simpa only [hlevel, succMenu] using IsCascadeStage.step hcascade hactual
  have hGrlevel : (G'.retained m H J).level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hreg := hf hr D hDα hDq hDΛ hDζ hseq hbandD _ bw j₀
    (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
    (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) law seedK freshK kS
    kI.cr σ₀ (hkI.2.1.symm ▸ hcr) (by simpa only [hterm] using hfresh)
    Mnat seed (G'.retained m H J) tS tf _ _ (by omega) hseedInv hGrCascade
    (hGrlevel.symm ▸ hmf') kI.cker (fun j _ =>
      ⟨(invariant_admissible_kernel_bounds hkI j).1,
        (le_max_right _ _).trans (invariant_admissible_kernel_bounds hkI j).2⟩)
    (tA + 3 * ocTau α q Λ m) tf (by
      intro t ht
      refine ⟨htA.trans (le_trans ?_ ht.1), ht.2⟩
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
        (Construction.Stream.ocTau_pos (by omega : 1 ≤ Λ)).le))
  refine ⟨hnatural, hshift, hcontext.2.1, hcontext.2.2, hmarked, ?_⟩
  intro v u γ
  refine ⟨hwidthGr v u γ, ?_⟩
  intro ρ hρ
  exact hreg v u γ ρ hρ 0 (Nat.zero_le _)
end

end AVRegularity.Construction.Preservation.Assembly
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Construction.Preservation.Assembly

/-! Discharge the lifted-field existence and energy clauses using the existing analytic lemmas. -/

open AVRegularity.Construction.Preservation.FullLift

theorem uniform_full_lift_clauses_of_inputs {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ bw : ℝ, 0 < bw →
    ∀ Dm H N r sX sZ p : ℕ, 2 ≤ Dm → 1 ≤ N →
    ∀ (Sbar cr : ℝ), 0 ≤ Sbar → 0 < cr → cr ≤ 1 →
    ∃ (Cenergy : ℝ) (m₀ : ℕ), 0 ≤ Cenergy ∧ 2 ≤ m₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (j₀ : ℕ) (G : GenStage D hr Dm bw j₀) (law : BirthLaw) (P : ProvParams)
      (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (M : ℕ) (kI : InvConsts) (tA tB S θK : ℝ),
    IsStageInvariant law P seedK freshK φ₀ hφ₀ M kI tA tB S θK G →
    S ≤ Sbar → m₀ ≤ G.level → G.level < D.term → j₀ ≤ G.level → G.fam.HasDepthAtMost H →
    (∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1) →
    (∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2) →
    (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level) →
    ∀ (Gr : GenStage D hr Dm bw j₀) (Naux : ℕ) (hk : r + N + 2 * p ≤ Naux),
    ∀ (η tp tf : ℝ)
      (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yhi : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 3) (hr v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc tp tf,
      Y v t = truncateTorusHk (by omega : Naux ≤ Naux + 3) (Yhi v t)) →
    ∀ (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root)),
    (∀ v, MemLp (Yw v) 2 (volume.restrict (Set.Icc tp tf))) →
    (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      truncateTorusHk (Nat.le_succ Naux) (Yw v t) = Y v t) →
    0 < rhoStar D kI.c₀ G.level → rhoStar D kI.c₀ G.level ≤ D.eps G.level →
    ∀ Cread Ain : ℝ, 0 ≤ Ain →
      RetainedReadoutBudgetStatement law G Gr G.level p Naux N r hk η cr tp tf Cread Ain Y Yw →
      FullLiftClauses law G Gr G.level p Naux N H sX sZ r hk η kI.c₀ cr tp tf
        (max Cenergy Cread) Ain Y Yw := by
  classical
  obtain ⟨Λe, hΛe, hexists⟩ := uniform_native_lift_existence_of_higher_values
    hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Λu, hΛu, henergy⟩ := uniform_native_lift_energy_of_higher_values
    hα0 hα1 hs0 hs1 hq hζ
  refine ⟨max Λe Λu, by omega, ?_⟩
  intro Λ hΛ bw hb Dm H N r sX sZ p hDm hN Sbar cr hSbar hcr hcr1
  obtain ⟨me, hme, he⟩ := hexists Λ (by omega) bw hb Dm H N r sX sZ hDm hN
  obtain ⟨Cenergy, mu, hCenergy, hmu, hu⟩ := henergy Λ (by omega) bw hb
    Dm H N r sX sZ p hDm hN Sbar cr hSbar hcr hcr1
  refine ⟨Cenergy, max me mu, hCenergy, by omega, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG hSbound hm hterm hj hdepth hreserve hreserve2 hlength
    Gr Naux hk η tp tf Y Yhi hYhi Yw hYw hcompat hrs hrse Cread Ain hAin hread
  have hex := he hr D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG (by omega) hterm hj hdepth hreserve hreserve2 hlength
    Gr p Naux hk η tp tf Y Yhi hYhi
  refine ⟨hex, ?_⟩
  intro CcT PZ aRep u w hfield wgt hwgt
  have hb := hu hr D hDα hDq hDΛ hDζ hseq hband j₀ G law P seedK freshK φ₀ hφ₀
    M kI tA tB S θK hG hSbound (by omega) hterm hj hdepth hreserve hreserve2 hlength
    Gr Naux hk η tp tf Y Yhi hYhi Yw hYw hcompat CcT PZ aRep u w hfield wgt hwgt
    (rhoStar D kI.c₀ G.level) hrs hrse
  change strongEnergy _ _ _ _ _ _ _ ≤
    ENNReal.ofReal Cenergy * readoutEnergy law G Gr G.level η (rhoEnh D cr G.level)
      hk wgt tp tf Y Yw at hb
  refine ⟨hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl), ?_⟩
  exact (hread wgt hwgt).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hAin))

end AVRegularity.Construction.Preservation.Assembly
end
