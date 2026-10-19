-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.Construction.StageEnvelopes.Cauchy.Assembly
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.InitialValue.Cascade
public import AVRegularity.Proofs.CascadeInvariants.ReserveGrade
public import AVRegularity.Construction.StageEnvelopes.Assembly

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly

/-! Exact bill assembly. The residual producer chooses the decay rate; the scalar producer
then supplies its bound at that same rate. -/

private theorem bill_error_bound {Cr Cs B X Ain C : ℝ}
    (hA : 0 ≤ Ain) (hX : 0 ≤ X) (hB : 0 ≤ B) (hscale : B ≤ Cs * X)
    (hC : |Cr| * (|Cs| + 1) ≤ C) : Cr * Ain * (B + X) ≤ C * X * Ain := by
  have hscale' : B ≤ |Cs| * X :=
    hscale.trans (mul_le_mul_of_nonneg_right (le_abs_self Cs) hX)
  calc
    _ ≤ |Cr| * Ain * (B + X) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Cr) hA)
        (add_nonneg hB hX)
    _ ≤ |Cr| * Ain * (|Cs| * X + X) :=
      mul_le_mul_of_nonneg_left (add_le_add hscale' le_rfl)
        (mul_nonneg (abs_nonneg Cr) hA)
    _ = (|Cr| * (|Cs| + 1)) * X * Ain := by ring
    _ ≤ C * X * Ain :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hX) hA

theorem successor_bill_of_ingredients_core (α s q : ℝ) (ζ : ℝ → ℝ)
    (ha0 : SuccessorBillResidualStatement α s q ζ) (hb0 : SuccessorBillScaleStatement α s q ζ) :
    SuccessorBillStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := ha0
  obtain ⟨Λb, hΛb, hb⟩ := hb0
  refine ⟨max Λa Λb, by omega, ?_⟩
  intro Λ hΛ
  obtain ⟨ca, hca, ha⟩ := ha Λ (by omega)
  obtain ⟨cb, hcb, hb⟩ := hb Λ (by omega)
  refine ⟨min ca cb, lt_min hca hcb, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hfloorX hfloorZ
  obtain ⟨ta, CHa, Υa, hCHa, hΥa, ha⟩ := ha φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hfloorX hfloorZ
  obtain ⟨tb, CHb, Υb, hCHb, hΥb, hb⟩ := hb φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_right _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hfloorX hfloorZ
  refine ⟨certificateThresholdJoin ta tb, max CHa CHb, max Υa Υb,
    hCHa.trans (le_max_left _ _), hΥa.trans_le (le_max_left _ _), ?_⟩
  intro kI hkI
  obtain ⟨CIa, Cwa, ha⟩ := ha kI (invariant_admissible_threshold_left hkI)
  obtain ⟨CIb, Cwb, hb⟩ := hb kI (invariant_admissible_threshold_right hkI)
  refine ⟨max CIa CIb, max Cwa Cwb, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLa : IsLedgerAdmissible Ce CI Cw CIa Cwa :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1,
      (le_max_left _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLb : IsLedgerAdmissible Ce CI Cw CIb Cwb :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1,
      (le_max_right _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  intro CQ Cpr
  obtain ⟨Cr, c, mr, hc, ha⟩ := ha CI Cw j₀ hLa (IsCarrierStart.mono hA hT
    (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHa) hΥa.le hstart) CQ Cpr
  obtain ⟨Cs, ms, hb⟩ := hb CI Cw j₀ hLb (IsCarrierStart.mono hA hT
    (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHb) hΥb.le hstart) CQ Cpr c hc
  let C := |Cr| * (|Cs| + 1) + |Cr| + |Cs| + 1
  have hprod : 0 ≤ |Cr| * (|Cs| + 1) :=
    mul_nonneg (abs_nonneg Cr) (add_nonneg (abs_nonneg Cs) zero_le_one)
  have hCr : Cr ≤ C := (le_abs_self _).trans
    (by dsimp [C]; linarith only [abs_nonneg Cs, hprod])
  have hCs : Cs ≤ C := (le_abs_self _).trans
    (by dsimp [C]; linarith only [abs_nonneg Cr, hprod])
  have hCprod : |Cr| * (|Cs| + 1) ≤ C := by
    dsimp [C]
    linarith only [abs_nonneg Cr, abs_nonneg Cs]
  refine ⟨C, c, max mr ms, hc, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed hpw m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep hquietMargin f Ain hAin Y0 Y Yw Yk htrace hsol
  have hr := ha D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed hpw m (by omega) hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep hquietMargin f Ain hAin Y0 Y Yw Yk htrace hsol
  have hs := hb D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol
  have hE : 0 ≤ D.eps (m - 1) := by
    rw [OCData.eps, hDq, hDΛ]
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  have he : 0 ≤ D.eps m := by
    rw [OCData.eps, hDq, hDΛ]
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  have hAin' : 0 ≤ Ain := (Real.sqrt_nonneg _).trans hAin
  have hcI : 0 ≤ kI.c₀ := (hkI.1.symm ▸ hc₀).le
  have hcrI : 0 ≤ kI.cr := (hkI.2.1.symm ▸ hcr).le
  have hbnonneg := succBill_nonneg G m kI.c₀ kI.cr c σ₀ (succEta0 α q s)
    p N Lc Lf Acl J H tp tf
    (succTheta1 α q s σ₀ (succDstar D₀ N p H))
    (succTheta2 α q s σ₀ (succDstar D₀ N p H)) hE he hcI hcrI
  refine ⟨hs.trans (mul_le_mul_of_nonneg_right hCs (Real.rpow_nonneg hE Q)), ?_⟩
  exact comparisonClauses_mono (h := hr)
    (hres := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCr hAin') hbnonneg)
    (he := bill_error_bound hAin' (Real.rpow_nonneg hE Q) hbnonneg hs hCprod)

theorem successor_bill_of_ingredients (α s q : ℝ) (ζ : ℝ → ℝ)
    (ha0 : SuccessorBillResidualStatement α s q ζ) (hb0 : SuccessorBillScaleStatement α s q ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ (C c : ℝ) (mStar : ℕ), 0 < c ∧
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
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
      Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆
        ocQuietTimes α q Λ ζ m →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
      succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s) p N Lc Lf Acl J H tp tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H))
        ≤ C * D.eps (m - 1) ^ Q ∧
      ComparisonClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) s₀ tp tf
        (C * Ain * succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s) p N Lc Lf Acl J H tp tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)))
        (C * D.eps (m - 1) ^ Q * Ain) f Y :=
  successor_bill_of_ingredients_core α s q ζ ha0 hb0

end AVRegularity.Construction.Preservation.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.StageEnvelopes
namespace AVRegularity.Construction.Preservation.Assembly

/-! Fourth preservation assembly: pointwise molecular estimates on the retained inner carrier.
The shared analytic producer is proved. The sole new input contains only its actual geometric,
context-certificate, order, radius and uniform-constant hypotheses, not an envelope conclusion.

An empty component type is permitted, since no `Nontrivial` assumption is made, and an
edgeless seed still has fresh successor identities. The window is arbitrary and the radius is
literally rhoStar, as in the shared producer. -/

/-- Actual shared-producer inputs on one stage. There is no envelope assertion here. -/
def RetainedPointwiseContextClause (estimates : ∀ p, ContextEnvelopeEstimate p)
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} (G : GenStage D hr Dm bw j₀) (k : InvConsts) : Prop :=
  ∃ p : ContextEnvelopeParameters,
    ContextEnvelopeInput p G k k.mEnv (rhoStar D k.c₀ G.level) ∧
    (estimates p).levelFloor ≤ G.level ∧ (estimates p).Ca ≤ k.Ca ∧
    ∀ j, (estimates p).Cm j ≤ k.Cm j

/-- Exact data-dependent tail of the pointwise-envelope statement. -/
def PreservationPointwiseEnvelopeDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk npad sX sZ : ℕ) (σ₀ : ℝ) (kI : InvConsts)
    (CI Cw : ℝ) (j₀ mStar : ℕ) (Cpt : ℕ → ℝ) : Prop :=
∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      ∀ (tA tB : ℝ) (K : CompIn (G'.retained m H J).comps → ℕ),
        (∀ v, K v ≤ kI.Ks) →
      IsPointwiseMolecularEnvelope (G'.retained m H J).fam
        ((G'.retained m H J).mass law) K
        ((G'.retained m H J).innerDomain (Set.Icc tA tB) kI.mEnv)
        (D.kap (G'.retained m H J).level) (D.eps (G'.retained m H J).level)
        (D.eps ((G'.retained m H J).level - 1))
        (rhoStar D kI.c₀ (G'.retained m H J).level) Cpt kI.Jm
        (recordMajorant ((G'.retained m H J).mass law) (G'.retained m H J).fam)

/-- The geometry/certification tail, including trivial and empty root spaces. -/
def RetainedPointwiseContextDataStatement (estimates : ∀ p, ContextEnvelopeEstimate p)
    (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk npad sX sZ : ℕ) (σ₀ : ℝ) (kI : InvConsts)
    (CI Cw : ℝ) (j₀ mStar : ℕ) : Prop :=
∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →      RetainedPointwiseContextClause estimates (G'.retained m H J) kI

/-- Literal statement prefix, including the lift floors on `sX` and `sZ`. -/
def PreservationPointwiseMolecularEnvelopeStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (mStar : ℕ) (Cpt : ℕ → ℝ),
      PreservationPointwiseEnvelopeDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀ mStar Cpt

/-- One uniform adapter supplies the shared producer's exact context,
reserve gap, higher-length/radius, orders and cost domination for each retained stage.
No `Nontrivial` hypothesis is imposed; the empty family has a vacuous edge menu, and an
edgeless seed keeps the original input requirements. -/
def RetainedPointwiseContextInputsStatement (α s q : ℝ) (ζ : ℝ → ℝ)
    (estimates : ∀ p, ContextEnvelopeEstimate p) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
      RetainedPointwiseContextDataStatement estimates α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀ mStar

/-! Exact conditional pointwise-envelope assembly. The shared Cauchy/Fourier producer
is discharged here; the remaining uniform input adapter has no envelope conclusion.

The same estimate covers empty and singleton component types and edgeless seeds; no
root-space nontriviality is assumed. The closed time window and molecular radius are
arbitrary. -/

private theorem pointwise_markerConj_one {ι : Type*} {h : ι → Type*}
    [∀ v, NormedAddCommGroup (h v)] [∀ v, NormedSpace ℝ (h v)]
    {Dm : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h Dm P Ctx) :
    markerConj (fun _ => 1) F = F := by
  unfold markerConj
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_smul]

/-- The literal pointwise statement from its one uniform geometric input adapter.
The estimate constants are chosen before data; Cpt=kI.Cm is fixed before stage and window. -/
theorem preservation_pointwise_molecular_envelope_of_ingredients
    (α s q : ℝ) (ζ : ℝ → ℝ)
    (hinputs : ∀ estimates, RetainedPointwiseContextInputsStatement α s q ζ estimates) :
    PreservationPointwiseMolecularEnvelopeStatement α s q ζ := by
  classical
  let estimates (p : ContextEnvelopeParameters) := Classical.choice (Cauchy.context_stage_envelopes p)
  obtain ⟨Λ₀, hΛ₀, hinputs⟩ := hinputs estimates
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, hinputs⟩ := hinputs Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hinputs⟩ := hinputs φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hinputs⟩ := hinputs kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨mStar, hinputs⟩ := hinputs CI Cw j₀ hledger hstart
  refine ⟨mStar, kI.Cm, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    G G' hcascade hlevel hG hactual tA tB K hK
  obtain ⟨pEnv, hinput, hfloor, hCa, hCm⟩ := hinputs D hDα hDq hDΛ hDζ hseq
    M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hseed
    m hm hn hnM G G' hcascade hlevel hG hactual
  let Gr := G'.retained m H J
  have h := (estimates pEnv).bound hr D _ j₀ bw Gr kI kI.mEnv
    (rhoStar D kI.c₀ Gr.level) hinput hfloor hCa hCm law (Set.Icc tA tB)
  have h1 := h (fun _ => 1) (fun _ => zero_lt_one)
  dsimp only at h1
  rw [pointwise_markerConj_one Gr.fam] at h1
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul] at h1
  exact (h1 K hK).2.2.2

end AVRegularity.Construction.Preservation.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly

/-! One retained marked-ledger step. The per-identity ledger conclusion is
kept verbatim through LedgerConcl. The two ingredients separate tagged finite-path
summation from the numerical choice of the starting level. -/

/-- A fixed menu factor pays the direct and quadratic transport sums. -/
def ledgerTransportConstant (Cw : ℝ) (Tw : ℕ) : ℝ := 2 * ((Tw : ℝ) + 1) * (Cw + 1)

/-- The fixed positive birth mass constant. -/
def successorBirthMass (α q s : ℝ) : ℝ := (1 - (128 : ℝ) ^ (-(succEta0 α q s / 2))) / 2

/-- The finite word factor is included in the source constant; it depends only on the menus. -/
def ledgerBirthConstant (α q s Cw : ℝ) (Tw L : ℕ) : ℝ :=
  2 * ((Tw : ℝ) + 1) * ((L : ℝ) + 1) * (Cw + 1) *
    Real.sqrt ((Tw : ℝ) / successorBirthMass α q s)

/-- Structural one-step recurrence, for either the ordinary or marked inflated ledger.
The constant of the fresh terms is fixed before the root masses. -/
def TaggedLedgerRecurrenceStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
  ∀ (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (α s q : ℝ),
    D.α = α → D.q = q → 1 < q → 128 ≤ D.Λ → 0 < succEta0 α q s →
  ∀ (Cw cr σ₀ : ℝ) (N p Dstar : ℕ) (Mn : SuccMenu), 0 < Cw → 0 ≤ σ₀ →
    (∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ Dstar) →
  ∀ law : BirthLaw,
    IsSuccessorLaw α q s (wordsUpTo Mn.A (Mn.J + 1)).card law →
  ∀ (G G' : GenStage D hr Dm bw j₀),
    G.HasTags (succProvParams D Cw cr σ₀ (succEta0 α q s) N p) →
    (∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale) →
    IsActualSuccessor D (succProvParams D Cw cr σ₀ (succEta0 α q s) N p) Mn G G' →
    2 ≤ G.level →
  ∀ (S : ℝ), 0 ≤ S → markedLedger (G.mass law) (G.marker law) G.fam ≤ S →
    ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card * S ≤ 1 / 2 →
  ∀ H J : ℕ,
    let Gr := G'.retained G.level H J
    markedLedger (Gr.mass law) (Gr.marker law) Gr.fam ≤
      ledgerBirthConstant α q s Cw (wordsUpTo Mn.A (Mn.J + 1)).card Mn.A.card *
        D.eps (G.level - 1) ^ succTheta1 α q s σ₀ Dstar +
      2 * ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card * S

/-- The same structural recurrence before restricting components. This serves the extended
kernel operator needed by the grade frontier. Empty and singleton component
sets, edgeless seeds and the first prefix all use the same finite source sums. -/
def FullTaggedLedgerRecurrenceStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
  ∀ (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (α s q : ℝ),
    D.α = α → D.q = q → 1 < q → 128 ≤ D.Λ → 0 < succEta0 α q s →
  ∀ (Cw cr σ₀ : ℝ) (N p Dstar : ℕ) (Mn : SuccMenu), 0 < Cw → 0 ≤ σ₀ →
    (∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ Dstar) →
  ∀ law : BirthLaw,
    IsSuccessorLaw α q s (wordsUpTo Mn.A (Mn.J + 1)).card law →
  ∀ (G G' : GenStage D hr Dm bw j₀),
    G.HasTags (succProvParams D Cw cr σ₀ (succEta0 α q s) N p) →
    (∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale) →
    IsActualSuccessor D (succProvParams D Cw cr σ₀ (succEta0 α q s) N p) Mn G G' →
    2 ≤ G.level →
  ∀ (S : ℝ), 0 ≤ S → markedLedger (G.mass law) (G.marker law) G.fam ≤ S →
    ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card * S ≤ 1 / 2 →
    markedLedger (G'.mass law) (G'.marker law) G'.fam ≤
      ledgerBirthConstant α q s Cw (wordsUpTo Mn.A (Mn.J + 1)).card Mn.A.card *
        D.eps (G.level - 1) ^ succTheta1 α q s σ₀ Dstar +
      2 * ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card * S

/-- Strictly better birth decay and scale separation absorb both terms of the recurrence.
The floor is at least two because epsilon zero equals one. -/
def LedgerScaleAbsorptionStatement : Prop :=
  ∀ (q : ℝ) (Λ : ℕ), 1 < q → q < 17 / 16 → 128 ≤ Λ →
  ∀ (τ θ A B CI : ℝ), 0 < τ → τ < θ → 1 ≤ A → 0 ≤ B → 0 < CI →
  ∃ mStar : ℕ, 2 ≤ mStar ∧ ∀ m : ℕ, mStar ≤ m →
    A * (CI * ocEpsilon q Λ m ^ τ) ≤ 1 / 2 ∧
    B * ocEpsilon q Λ (m - 1) ^ θ + 2 * A * (CI * ocEpsilon q Λ m ^ τ) ≤
      CI * ocEpsilon q Λ (m - 1) ^ τ

def RetainedMarkedLedgerStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
  IsAdmissibleQ α s q → IsFastProfile ζ →
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
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
    ∀ κc : MajConsts,
      (∀ v' u' (γ' : G'.fam.Γ v' u'), Providers.CascadeInvariants.LedgerConcl kI κc G' v' u' γ') →
      let Gr := G'.retained m H J
      markedLedger (Gr.mass law) (Gr.marker law) Gr.fam ≤
        CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe

/-- The retained marked-ledger binder prefix and ledger conclusion, assembled from the two bounded ingredients. -/
theorem retained_marked_ledger_of_ingredients
    (hrec : TaggedLedgerRecurrenceStatement) (habs : LedgerScaleAbsorptionStatement)
    (α s q : ℝ) (ζ : ℝ → ℝ) : RetainedMarkedLedgerStatement α s q ζ := by
  classical
  intro hα₀ hα₁ hs₀ hs₁ hq hζ
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hη := FullLift.successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq
  refine ⟨128, le_rfl, ?_⟩
  intro Λ hΛ
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ _hφsmooth _hφnonneg _hφmass _hφsupport bw _hbw _hbwmax Q T₀ _hQ _hT
    Ce τe kS r₀ D₀ hCe hτe _hcS _hcSmax _hcr _hcrmax _hσf _hlam H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad sX sZ σ₀ a σ hsched _haux _hres _halloc
  obtain ⟨_, _, _, _, _, hσeq, ha, haσ, _, hσD, _⟩ := hsched
  have hσ₀ : 0 ≤ σ₀ := by linarith only [hσeq, ha, haσ]
  refine ⟨kS, 1, 100, le_rfl, by norm_num, ?_⟩
  intro kI _hkI
  refine ⟨1, 1, ?_⟩
  intro CI Cw j₀ hledger _hstart
  have hCI : 0 < CI := lt_of_lt_of_le (by linarith only [hCe] : 0 < Ce) hledger.1
  let Tw := (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card
  let A := ledgerTransportConstant Cw Tw
  let B := ledgerBirthConstant α q s Cw Tw (succAlphabetOf r₀ D₀ H J N p npad).card
  let τ := min (ocDelta α q / 4) τe
  have hτ : 0 < τ := lt_min (div_pos hδ (by norm_num)) hτe
  have hθ : τ < succTheta1 α q s σ₀ (succDstar D₀ N p H) := by
    have hηle : succEta0 α q s ≤ ocDelta α q / 8 := min_le_left _ _
    have hτle : τ ≤ ocDelta α q / 4 := min_le_left _ _
    dsimp only [succTheta1]
    linarith only [hδ, hηle, hτle, hσD]
  have hCw : 0 < Cw := hledger.2.2.2
  have hA : 1 ≤ A := by
    dsimp only [A, ledgerTransportConstant]
    have ht : 0 ≤ (Tw : ℝ) := Nat.cast_nonneg _
    have hc := hledger.2.2.2
    nlinarith only [ht, hc]
  have hB : 0 ≤ B := by
    dsimp only [B, ledgerBirthConstant]
    positivity
  obtain ⟨mStar, hmStar, hsmall⟩ := habs q Λ hq.1 hq.2.1 hΛ τ
    (succTheta1 α q s σ₀ (succDstar D₀ N p H)) A B CI hτ hθ hA hB hCI
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ _hDζ _hstream M _hband _hterm Mnat _hMnat law hlaw hr _ _ _ _ _ _ _
    seedK freshK _hfresh seed n tS tf hseed m hm _hmn _hnM tA _htA G G' hc hlevel hInv hs κc _hgate
  have hletter : ∀ l ∈ (succAlphabetOf r₀ D₀ H J N p npad),
      letterOrder N p l - 2 ≤ succDstar D₀ N p H := by
    intro l hl
    have hnext : succSchedD D₀ N p (H + 1) = succSchedD D₀ N p H + 2 * N + 4 * p + 4 := rfl
    cases l with
    | diag => simp only [letterOrder, succDstar]; omega
    | mean n h =>
      have hn := (Providers.CascadeInvariants.mean_mem_succAlphabet hl).2.1
      simp only [letterOrder, succDstar]
      omega
    | covariance n h a a' =>
      have hf := Providers.CascadeInvariants.cov_mem_succAlphabet hl
      simp only [letterOrder, succDstar]
      omega
    | eddy n =>
      simp [succAlphabetOf, succAlphabet] at hl
    | padding n => simp only [letterOrder]; omega
  have hold := InitialValue.cascade_invariant hseed.2.1 hc
  have hbounds := hsmall m hm
  have hε : D.eps m = ocEpsilon q Λ m := by simp only [OCData.eps, hDq, hDΛ]
  have hE : D.eps (m - 1) = ocEpsilon q Λ (m - 1) := by simp only [OCData.eps, hDq, hDΛ]
  have hrec' := hrec hr D _ bw j₀ α s q hDα hDq hq.1 (hDΛ.symm ▸ hΛ) hη Cw kI.cr σ₀ N p
    (succDstar D₀ N p H) (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s))
    hledger.2.2.2 hσ₀ hletter law hlaw G G' hInv.2.1 (fun v hv => (hold v hv).1) hs
    (by omega) (CI * D.eps m ^ τ) (mul_nonneg hCI.le (Real.rpow_nonneg (by
      rw [hε]; exact (Scales.epsilon_basic hq.1 hΛ).1.le) _)) hInv.2.2.2.2.2.2.2.1
    (by simpa only [A, Tw, succMenu, hε] using hbounds.1) H J
  rw [hlevel] at hrec'
  exact hrec'.trans (by simpa only [A, B, Tw, succMenu, hε, hE] using hbounds.2)

end AVRegularity.Construction.Preservation.Assembly
end
