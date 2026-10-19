-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Finite.Assembly.TerminalLiftProfileBoundsOfIngredients
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Construction.Scales.Times
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Proofs.Results.Finite.TraceClosure
import AVRegularity.Finite.SeedTransport.Unique
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.Assembly

/-! The seed-to-terminal representation glue, followed by the two
lift estimates and the classical representative theorem. -/

/-- The open local step stops at the retained terminal family, before either
represented lift. It must select the actual entry witnesses, transport the
cascade solution back to the terminal family, and transfer its essential
represented-size bound to the final window. In particular it supplies no
scalar regularity bound and assumes neither lift estimate. -/
def FiniteStrongEntryStatement : Prop :=
  ∀ (cfg : FiniteParameters) (_hvalid : FiniteLocalValidity cfg) (_htransport : TerminalSeedTransportStatement)
    (_hs : 0 < cfg.s) (_hs1 : cfg.s < 1) (_hΛ : 128 ≤ cfg.Λ)
    (_hη : 0 < succEta0 cfg.α cfg.q cfg.s) (_ht₀ : 0 < cfg.t₀) (_htT : cfg.t₀ < cfg.T₀)
    (_hτ : cfg.τ ≤ cfg.t₀) (_hc : 0 < cfg.c) (_hCcas : 0 < cfg.Ccas)
    (_hPw : cfg.Pw = 2) (_hPT : cfg.PT = 2)
    (M : ℕ) (_hM : cfg.m₀ + 2 ≤ M) (_hbudget : FiniteSeedBudgetLevel cfg M)
    (_hwait : (|cfg.C| + 1) * ocTauPP cfg.α cfg.q cfg.Λ M +
      6 * cfg.Jw * ocTauPP cfg.α cfg.q cfg.Λ (M + 1) ≤ cfg.t₀ / 4)
    (_hentry : EntryLevelStatement cfg M) (_hcas : CascadeLevelStatement cfg)
    (D : OCData) (_hDα : D.α = cfg.α) (_hDq : D.q = cfg.q) (_hDΛ : D.Λ = cfg.Λ)
    (_hDζ : D.ζ = cfg.ζ) (_hDΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ)
    (_hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (_hDterm : D.term = M)
    (_haxes : ∀ b', 1 ≤ b' → b' < M → ∃ H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2,
      IsFreshAxes D b' H₁ H₂)
    (a : ℝ) (f : Vec 2 → ℝ) (_hf : MemL2On unitCube f) (θ : ℝ → Vec 2 → ℝ)
    (_hθ : IsWeakSolutionOn (streamVel (D.Φ (M + cfg.Jw))) (D.κ M) a (a + cfg.T₀) f θ),
    ∀ᵐ t ∂(volume.restrict (Set.Icc (a + cfg.t₀) (a + cfg.T₀))),
    ∃ (PW : ProvParams)
      (stage : ℕ → GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀)
      (Gw : GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀)
      (lawW : BirthLaw) (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ) (aM : ℝ),
      IsWeakConstruction D PW (⟨cfg.Nw, cfg.Rw, cfg.sXT, cfg.sZT, cfg.η₀, M + cfg.Jw⟩ : WeakMenu)
        M cfg.Jw (D.termRW cfg.σw M) 0 stage ∧
      IsWeakEncoding cfg.Nw cfg.Jw cfg.η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw ∧
      (∀ i, M < i → i ≤ M + cfg.Jw →
        IsWeakReadoutLifts i cfg.Nw (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT (stage i) (CcR i)) ∧
      IsWeakReadoutChain M cfg.Jw cfg.Nw 0 cfg.η₀ (fun _ => cfg.Jw * cfg.Rw) stage CcR W ∧
      IsWeakStage lawW PW cfg.φ₀ cfg.hφ₀ M (M + cfg.Jw) cfg.Jw (cfg.Jw * cfg.Rw)
        (1 + cfg.Jw * cfg.Nw) cfg.nW cfg.kW a cfg.T₀ cfg.σw cfg.CL cfg.Cχ
        (weakChi cfg.α cfg.q cfg.η₀) Gw aM ∧
    ∃ (tp : ℝ)
      (Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max cfg.Kout (max (2 * cfg.k₀ + 2)
          (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw)
      (Gt' : GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀),
      IsTerminalPrepMap M cfg.Kw (max cfg.Kout (max (2 * cfg.k₀ + 2)
        (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) cfg.c cfg.C Gw aM tp Pterm ∧
      IsTerminalLaw lawW lawT cfg.cH cfg.η₀
        (wordsUpTo (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.RT).card ∧
      IsActualSuccessor D (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
        (termMenu (M + cfg.Jw) (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw))
          cfg.RT cfg.NT cfg.pT cfg.sXT cfg.sZT cfg.η₀ tp cfg.cr) Gw Gt' ∧
    ∃ (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root))
      (Z : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ →
        TorusHk (max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) (ScalarH v.1.root)),
      EntryIdentityClauses Gw (Gt'.retained M 1 cfg.RT) M cfg.pT
        (max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) cfg.Kw cfg.Lw
        cfg.NT (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT cfg.η₀ tp a cfg.τ cfg.T₀ cfg.s cfg.Pw cfg.PT cfg.C cfg.cr f θ
        (fun t g x => W M t (fun v x' => g (ιw v) x') x) V Z ∧
      t ∈ Set.Icc tp (a + cfg.T₀) ∧ a + cfg.τ ≤ t ∧
    ∃ r : Representation (CompSpace (Gt'.retained M 1 cfg.RT).comps),
      IsRepresentationAt (D.eps (M - 1)) (cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4) r ∧
      IsRepOf ((Gt'.retained M 1 cfg.RT).mass lawT)
        (fun v => truncateTorusHk (Nat.zero_le _) (Z v t)) r.value ∧
      representedSize cfg.s (cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4) (D.eps (M - 1)) r ≤
        ENNReal.ofReal (cfg.Ccas * |cfg.Centry| * Real.sqrt (l2NormSq f))

/-- Both lift conclusions fit the actual entry identities. Only the
seed-to-terminal representation and its time-window transfer are assumed. -/
theorem finite_datum_composition_of_strong_entry (hstrong : FiniteStrongEntryStatement) :
    FiniteDatumCompositionStatement := by
  intro cfg hvalid htransport hs hs1 hΛ hη ht₀ htT hτ hc hCcas hPw hPT M hM hbudget hwait hentry
    CT CwLift hCT hCw hterm hweak hcas D hDα hDq hDΛ hDζ hDΦ hband hDterm haxes a f hf θ hθ
  have hae := hstrong cfg hvalid htransport hs hs1 hΛ hη ht₀ htT hτ hc hCcas hPw hPT
    M hM hbudget hwait hentry hcas D hDα hDq hDΛ hDζ hDΦ hband hDterm haxes a f hf θ hθ
  filter_upwards [hae] with t ht
  obtain ⟨PW, stage, Gw, lawW, ιw, CcR, W, aM, hconstruction, hencoding, hlifts, hchain, hstage,
    tp, Pterm, lawT, Gt', hprep, hlaw, hactual, V, Z, hidentity, htwindow, hτt,
    r, hr, hvalue, hsize⟩ := ht
  obtain ⟨CcT, PZ, aRep, û, hlift⟩ := hidentity.1
  obtain ⟨rT, hrT, _, _, hvalueT, hsizeT⟩ := hterm D hDα hDq hDΛ hDζ hDΦ hband hDterm
    PW a Gw lawW aM hstage tp Pterm hprep lawT Gt' hlaw hactual _ Z CcT PZ aRep û hlift
    t htwindow r hr hvalue
  obtain ⟨rW, hrW, hreadout, hsizeW⟩ := hweak D hDα hDq hDΛ hDζ hDΦ hband hDterm
    PW _ stage Gw lawW ιw CcR W hconstruction hencoding hlifts hchain
    t (termLiftedRep Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t) rT hrT hvalueT
  have hroot : (stage (M + cfg.Jw)).comps = {⟨0, []⟩} := hconstruction.2.1.2.1
  have htotal : representedSize cfg.s 3 (D.eps (M + cfg.Jw)) rW ≤
      ENNReal.ofReal ((CwLift * CT) * cfg.Ccas * |cfg.Centry| * Real.sqrt (l2NormSq f)) := by
    calc _ ≤ ENNReal.ofReal CwLift *
        (ENNReal.ofReal CT * ENNReal.ofReal (cfg.Ccas * |cfg.Centry| * Real.sqrt (l2NormSq f))) :=
          hsizeW.trans (mul_le_mul' le_rfl (hsizeT.trans (mul_le_mul' le_rfl hsize)))
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCw, ← ENNReal.ofReal_mul (mul_nonneg hCw hCT)]
        congr 1
        ring
  have hKw := cfg.hLw
  choose aV haV using fun v => Providers.torusHk_classicalRep_exists cfg.Kw (cfg.Lw + 3)
    (by omega : cfg.Lw + 3 + 2 ≤ cfg.Kw) (V v t)
  obtain ⟨Θ, hΘp, hΘae, herr⟩ := (hidentity.2 CcT PZ aRep û hlift t htwindow aV haV).2 hτt
  have heps (j : ℕ) : 0 ≤ D.eps j ∧ D.eps j ≤ 1 := by
    change 0 ≤ ocEpsilon D.q D.Λ j ∧ ocEpsilon D.q D.Λ j ≤ 1
    rw [hDq, hDΛ]
    exact ⟨ocEpsilon_nonneg (by omega) j, ocEpsilon_le_one (by omega) j⟩
  have hpow (j : ℕ) : 0 ≤ D.eps j ^ (2 : ℝ) ∧ D.eps j ^ (2 : ℝ) ≤ 1 := by
    rw [Real.rpow_two]
    constructor
    · positivity
    · nlinarith [heps j]
  have hbound : cfg.C * (D.eps M ^ cfg.Pw + D.eps (M - 1) ^ cfg.PT) * Real.sqrt (l2NormSq f) ≤
      2 * |cfg.C| * Real.sqrt (l2NormSq f) := by
    rw [hPw, hPT]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    calc cfg.C * (D.eps M ^ (2 : ℝ) + D.eps (M - 1) ^ (2 : ℝ)) ≤
        |cfg.C| * (D.eps M ^ (2 : ℝ) + D.eps (M - 1) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (add_nonneg (hpow M).1 (hpow (M - 1)).1)
      _ ≤ |cfg.C| * 2 := mul_le_mul_of_nonneg_left (by linarith [(hpow M).2, (hpow (M - 1)).2]) (abs_nonneg _)
      _ = _ := by ring
  refine ⟨(stage (M + cfg.Jw)).comps, hroot, rW, hrW, htotal, Θ, hΘp, hΘae, ?_⟩
  intro x y z hyz
  have hi := herr x y z hyz
  simp only [hreadout] at ⊢
  exact hi.trans hbound

/-! Assembly of the seed-to-terminal represented transfer. Entry witnesses and timing
are selected once, independently of the time. The remaining seed representation
is reindexed by the already-proved mass-preserving adapter. -/

/-- The actual entry witnesses used by both the seed cascade and the two finite lifts.
No new existence or regularity assumption is introduced: the selector extracts the entry
data from `EntryLevelStatement`. -/
structure FiniteEntryData (cfg : FiniteParameters) (D : OCData) (M : ℕ)
    (a : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) where
  PW : ProvParams
  stage : ℕ → GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀
  Gw : GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀
  lawW : BirthLaw
  ιw : CompIn (stage M).comps ≃ CompIn Gw.comps
  CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root)
  W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ
  aM : ℝ
  construction : IsWeakConstruction D PW (⟨cfg.Nw, cfg.Rw, cfg.sXT, cfg.sZT, cfg.η₀, M + cfg.Jw⟩ : WeakMenu)
    M cfg.Jw (D.termRW cfg.σw M) 0 stage
  encoding : IsWeakEncoding cfg.Nw cfg.Jw cfg.η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw
  lifts : ∀ i, M < i → i ≤ M + cfg.Jw → IsWeakReadoutLifts i cfg.Nw (cfg.Jw * cfg.Rw)
    cfg.sXT cfg.sZT (stage i) (CcR i)
  chain : IsWeakReadoutChain M cfg.Jw cfg.Nw 0 cfg.η₀ (fun _ => cfg.Jw * cfg.Rw) stage CcR W
  weakStage : IsWeakStage lawW PW cfg.φ₀ cfg.hφ₀ M (M + cfg.Jw) cfg.Jw (cfg.Jw * cfg.Rw)
    (1 + cfg.Jw * cfg.Nw) cfg.nW cfg.kW a cfg.T₀ cfg.σw cfg.CL cfg.Cχ
    (weakChi cfg.α cfg.q cfg.η₀) Gw aM
  tp : ℝ
  Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
    (∀ v : CompIn Gw.comps, TorusHk (max cfg.Kout (max (2 * cfg.k₀ + 2)
      (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) (ScalarH v.1.root))
  lawT : BirthLaw
  Gt' : GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀
  prep : IsTerminalPrepMap M cfg.Kw (max cfg.Kout (max (2 * cfg.k₀ + 2)
    (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) cfg.c cfg.C Gw aM tp Pterm
  terminalLaw : IsTerminalLaw lawW lawT cfg.cH cfg.η₀
    (wordsUpTo (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.RT).card
  actual : IsActualSuccessor D (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
    (termMenu (M + cfg.Jw) (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw))
      cfg.RT cfg.NT cfg.pT cfg.sXT cfg.sZT cfg.η₀ tp cfg.cr) Gw Gt'
  V : ∀ v : CompIn Gw.comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root)
  Z : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ →
    TorusHk (max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) (ScalarH v.1.root)
  identity : EntryIdentityClauses Gw (Gt'.retained M 1 cfg.RT) M cfg.pT
    (max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) cfg.Kw cfg.Lw
    cfg.NT (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT cfg.η₀ tp a cfg.τ cfg.T₀ cfg.s cfg.Pw cfg.PT cfg.C cfg.cr f θ
    (fun t g x => W M t (fun v x' => g (ιw v) x') x) V Z
  seed : GenStage D ScalarH (succSchedD (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw)
    (cfg.Jw * cfg.Rw)) cfg.N cfg.p (cfg.H + 1)) cfg.bw cfg.j₀
  rootM : ℕ → ℝ
  rootR : ℕ → ℝ
  seedKc : ℕ → KernelSpec
  ι : CompIn (Gt'.retained M 1 cfg.RT).comps ≃ CompIn seed.comps
  seedEncoding : IsSeedEncoding (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
    lawT rootM rootR (fun _ => isoPairedKernel (D.termRW cfg.σw M) cfg.nW)
    (fun _ => isoPairedKernel (D.termRNew cfg.cr cfg.tT M) cfg.nT)
    seedKc (Gt'.retained M 1 cfg.RT) seed ι
  seedClauses : TerminalSeedClauses rootM rootR seedKc cfg.φ₀ cfg.hφ₀ (M + cfg.Jw) (M - 1)
    cfg.kS cfg.Ce cfg.τe (termR0bar cfg.RT (cfg.Jw * cfg.Rw))
    (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) seed
    (tp + D.termH M) (a + cfg.T₀)
  family : TerminalFamilyClauses (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
    (fun _ => isoPairedKernel (D.termRW cfg.σw M) cfg.nW)
    (fun _ => isoPairedKernel (D.termRNew cfg.cr cfg.tT M) cfg.nT)
    cfg.φ₀ cfg.hφ₀ lawW lawT rootM M
    (max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2)))
    cfg.cr cfg.C cfg.Centry tp (tp + D.termH M) (a + cfg.T₀) f Gw (Gt'.retained M 1 cfg.RT)
    seed ι (Pterm fun v => V v aM) Z
  a_le_tp : a ≤ tp
  seed_wait : tp + D.termH M ≤ a + cfg.t₀ / 4
  terminal_window : tp + D.termH M + 3 * ocTau cfg.α cfg.q cfg.Λ (M - 1) +
    4 * ocTauPP cfg.α cfg.q cfg.Λ (M - 1) ≤ a + cfg.T₀

/-- Actual entry witness extraction and the preparation/seed wait. -/
def FiniteEntrySelectionStatement : Prop :=
  ∀ (cfg : FiniteParameters) (_hvalid : FiniteLocalValidity cfg) (_htransport : TerminalSeedTransportStatement)
    (_hs : 0 < cfg.s) (_hs1 : cfg.s < 1) (_hΛ : 128 ≤ cfg.Λ)
    (_hη : 0 < succEta0 cfg.α cfg.q cfg.s) (_ht₀ : 0 < cfg.t₀) (_htT : cfg.t₀ < cfg.T₀)
    (_hτ : cfg.τ ≤ cfg.t₀) (_hc : 0 < cfg.c) (_hCcas : 0 < cfg.Ccas)
    (_hPw : cfg.Pw = 2) (_hPT : cfg.PT = 2)
    (M : ℕ) (_hM : cfg.m₀ + 2 ≤ M) (_hbudget : FiniteSeedBudgetLevel cfg M)
    (_hwait : (|cfg.C| + 1) * ocTauPP cfg.α cfg.q cfg.Λ M +
      6 * cfg.Jw * ocTauPP cfg.α cfg.q cfg.Λ (M + 1) ≤ cfg.t₀ / 4)
    (_hentry : EntryLevelStatement cfg M) (_hcas : CascadeLevelStatement cfg)
    (D : OCData) (_hDα : D.α = cfg.α) (_hDq : D.q = cfg.q) (_hDΛ : D.Λ = cfg.Λ)
    (_hDζ : D.ζ = cfg.ζ) (_hDΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ)
    (_hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (_hDterm : D.term = M)
    (_haxes : ∀ b', 1 ≤ b' → b' < M → ∃ H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2,
      IsFreshAxes D b' H₁ H₂)
    (a : ℝ) (f : Vec 2 → ℝ) (_hf : MemL2On unitCube f) (θ : ℝ → Vec 2 → ℝ)
    (_hθ : IsWeakSolutionOn (streamVel (D.Φ (M + cfg.Jw))) (D.κ M) a (a + cfg.T₀) f θ),
    Nonempty (FiniteEntryData cfg D M a f θ)

/-- Seed representation obtained by the exact cascade, with the pointwise seed
clause and terminal transport. The bound is already restricted to the final window.
The representation is still in the seed component space, before reindexing. -/
def FiniteSeedRepresentationStatement : Prop :=
  ∀ (cfg : FiniteParameters) (_hvalid : FiniteLocalValidity cfg) (_htransport : TerminalSeedTransportStatement)
    (_hs : 0 < cfg.s) (_hs1 : cfg.s < 1) (_hΛ : 128 ≤ cfg.Λ)
    (_hη : 0 < succEta0 cfg.α cfg.q cfg.s) (_ht₀ : 0 < cfg.t₀) (_htT : cfg.t₀ < cfg.T₀)
    (_hτ : cfg.τ ≤ cfg.t₀) (_hc : 0 < cfg.c) (_hCcas : 0 < cfg.Ccas)
    (_hPw : cfg.Pw = 2) (_hPT : cfg.PT = 2)
    (M : ℕ) (_hM : cfg.m₀ + 2 ≤ M) (_hbudget : FiniteSeedBudgetLevel cfg M)
    (_hwait : (|cfg.C| + 1) * ocTauPP cfg.α cfg.q cfg.Λ M +
      6 * cfg.Jw * ocTauPP cfg.α cfg.q cfg.Λ (M + 1) ≤ cfg.t₀ / 4)
    (_hentry : EntryLevelStatement cfg M) (_hcas : CascadeLevelStatement cfg)
    (D : OCData) (_hDα : D.α = cfg.α) (_hDq : D.q = cfg.q) (_hDΛ : D.Λ = cfg.Λ)
    (_hDζ : D.ζ = cfg.ζ) (_hDΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ)
    (_hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (_hDterm : D.term = M)
    (_haxes : ∀ b', 1 ≤ b' → b' < M → ∃ H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2,
      IsFreshAxes D b' H₁ H₂)
    (a : ℝ) (f : Vec 2 → ℝ) (_hf : MemL2On unitCube f) (θ : ℝ → Vec 2 → ℝ)
    (_hθ : IsWeakSolutionOn (streamVel (D.Φ (M + cfg.Jw))) (D.κ M) a (a + cfg.T₀) f θ),
    ∀ E : FiniteEntryData cfg D M a f θ,
    ∀ᵐ t ∂(volume.restrict (Set.Icc (a + cfg.t₀) (a + cfg.T₀))),
      ∃ r : Representation (CompSpace E.seed.comps),
        IsRepresentationAt (D.eps (M - 1)) (cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4) r ∧
        IsRepOf (fun w => E.rootM w.1.root)
          (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t)) r.value ∧
        representedSize cfg.s (cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4) (D.eps (M - 1)) r ≤
          ENNReal.ofReal (cfg.Ccas * |cfg.Centry| * Real.sqrt (l2NormSq f))

/-- Exact original glue statement from actual entry selection and a seed-space
representation. The mass-preserving reindexing is already proved. -/
theorem finite_strong_entry_of_ingredients (hselect : FiniteEntrySelectionStatement)
    (hseed : FiniteSeedRepresentationStatement) : FiniteStrongEntryStatement := by
  intro cfg hvalid htransport hs hs1 hΛ hη ht₀ htT hτ hc hCcas hPw hPT M hM hbudget hwait
    hentry hcas D hDα hDq hDΛ hDζ hDΦ hband hDterm haxes a f hf θ hθ
  obtain ⟨E⟩ := hselect cfg hvalid htransport hs hs1 hΛ hη ht₀ htT hτ hc hCcas hPw hPT
    M hM hbudget hwait hentry hcas D hDα hDq hDΛ hDζ hDΦ hband hDterm haxes a f hf θ hθ
  have hae := hseed cfg hvalid htransport hs hs1 hΛ hη ht₀ htT hτ hc hCcas hPw hPT
    M hM hbudget hwait hentry hcas D hDα hDq hDΛ hDζ hDΦ hband hDterm haxes a f hf θ hθ E
  have hH : 0 ≤ D.termH M := by
    unfold OCData.termH
    rw [hDα, hDq, hDΛ]
    exact (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ cfg.Λ)).le
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with t ht htw
  obtain ⟨r, hr, hv, hsize⟩ := ht
  have hmass (v : CompIn (E.Gt'.retained M 1 cfg.RT).comps) :
      E.rootM (E.ι v).1.root = (E.Gt'.retained M 1 cfg.RT).mass E.lawT v :=
    (E.seedEncoding.2.2.1 v).1
  obtain ⟨rT, hrT, hvT, hsizeT⟩ := reindex_identified_rep E.ι _ _ hmass _
    (fun v => E.Z v t) (fun w => truncateTorusHk (Nat.zero_le _) (E.Z (E.ι.symm w) t))
    (fun v => congrArg (fun u => truncateTorusHk (Nat.zero_le _) (E.Z u t))
      (E.ι.symm_apply_apply v)) cfg.s hs hs1 _ (by omega)
    (D.eps (M - 1)) r hr hv
  refine ⟨E.PW, E.stage, E.Gw, E.lawW, E.ιw, E.CcR, E.W, E.aM,
    E.construction, E.encoding, E.lifts, E.chain, E.weakStage, E.tp, E.Pterm, E.lawT,
    E.Gt', E.prep, E.terminalLaw, E.actual, E.V, E.Z, E.identity, ?_, ?_,
    rT, hrT, hvT, hsizeT.trans hsize⟩
  · exact ⟨by linarith only [E.seed_wait, htw.1, hH, ht₀], htw.2⟩
  · exact (add_le_add (le_refl a) hτ).trans htw.1

end AVRegularity.Finite.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.WeakLift

/-! Bounded assembly for uniform represented transfer through one actual weak passage.
The scalar parameters, menu floors, constant and terminal threshold retain the statement's order. -/

abbrev WeakPassageProperty := ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (_s : ℝ) (_M _J _N _Lr : ℕ) (_η _Cstep : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (_CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (_depth : ℕ), Prop

def WeakUniformPassageStatement (Q : WeakPassageProperty) : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∃ Cstep : ℝ, 0 ≤ Cstep ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ)
      (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root)),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
      Q s M Jw Nw Lr η₀ Cstep stage CcR (Jw * Rw)

def WeakUniformPassagePairStatement (Qread Qcorr : WeakPassageProperty) : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∃ Cr Cc : ℝ, 0 ≤ Cr ∧ 0 ≤ Cc ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ)
      (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root)),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
      Qread s M Jw Nw Lr η₀ Cr stage CcR (Jw * Rw) ∧
      Qcorr s M Jw Nw Lr η₀ Cc stage CcR (Jw * Rw)


def WeakReadoutStackStatement {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (_s : ℝ) (M J N _Lr : ℕ) (η Cstep : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (_CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (_depth : ℕ) : Prop :=
  ∀ i : ℕ, M < i → i ≤ M + J →
    ‖readoutCLM i (D.eps (i - 1)) η
      (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
      (fun v : CompIn (stage (i - 1)).comps => weakMass D N J η v.1)‖ ≤ Cstep

def WeakCorrectionStackStatement {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (s : ℝ) (M J N Lr : ℕ) (η Cstep : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (depth : ℕ) : Prop :=
  ∀ i : ℕ, M < i → i ≤ M + J → ∀ K : ℕ, K ≤ Lr + 3 →
  ∀ (t : ℝ) (g : CompIn (stage (i - 1)).comps → Vec 2 → ℝ)
    (r : Representation (CompSpace (stage (i - 1)).comps)),
    IsRepresentationAt (D.eps (i - 1)) (K + N) r →
    r.value = compField (fun v => weakMass D N J η v.1) (fun x v => g v x) →
    let R := readoutCLM i (D.eps (i - 1)) η
      (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
      (fun v : CompIn (stage (i - 1)).comps => weakMass D N J η v.1)
    let corr := compField (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
      (fun x v => weakGluedLift i N depth (stage i) (CcR i) t
        (weakReadoutStep i η (stage i) (stage (i - 1)) g) v x) - fun x => R (r.value x)
    ContDiff ℝ (K : ℕ) corr ∧ IsZ2Periodic corr ∧
      profileNorm (D.eps i) K s corr ≤ ENNReal.ofReal Cstep *
        representedSize s (K + N) (D.eps (i - 1)) r

/-- Copy the old labels and append the nonidentity correction at the new label. -/
def WeakPassageAppendStatement : Prop :=
  ∀ {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (s e E Cread Ccorr : ℝ) (K Kin : ℕ),
    0 < e → e ≤ E → s < 1 → K ≤ Kin → 0 ≤ Cread → 0 ≤ Ccorr →
  ∀ (r : Representation H) (R : H →L[ℝ] H') (out : Vec 2 → H'),
    IsRepresentationAt E Kin r → ‖R‖ ≤ Cread →
    ContDiff ℝ (K : ℕ) (out - fun x => R (r.value x)) →
    IsZ2Periodic (out - fun x => R (r.value x)) →
    profileNorm e K s (out - fun x => R (r.value x)) ≤
      ENNReal.ofReal Ccorr * representedSize s Kin E r →
  ∃ r' : Representation H', IsRepresentationAt e K r' ∧ r'.value = out ∧
    representedSize s K e r' ≤ ENNReal.ofReal (Cread + Ccorr) * representedSize s Kin E r

/-- The uniform readout matrix bound of the actual finite weak stack. -/
def WeakReadoutBoundsStatement : Prop := WeakUniformPassageStatement WeakReadoutStackStatement

/-- The nonidentity lift difference is a periodic profile, with all costs uniform
before the carrier start, terminal level, phase and input representation. -/
def WeakLiftCorrectionBoundsStatement : Prop := WeakUniformPassageStatement WeakCorrectionStackStatement

/-- Combine separately uniform menu floors and level thresholds. -/
theorem weak_uniform_passage_pair (hread : WeakReadoutBoundsStatement)
    (hcorr : WeakLiftCorrectionBoundsStatement) :
    WeakUniformPassagePairStatement WeakReadoutStackStatement WeakCorrectionStackStatement := by
  unfold WeakReadoutBoundsStatement WeakUniformPassageStatement at hread
  unfold WeakLiftCorrectionBoundsStatement WeakUniformPassageStatement at hcorr
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λr, hΛr, hr⟩ := hread α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λc, hΛc, hc⟩ := hcorr α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λr Λc, by omega, ?_⟩
  intro Λ hΛ bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SXr, SZr, hrr⟩ := hr Λ (by omega) bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SXc, SZc, hcc⟩ := hc Λ (by omega) bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN hη hη1 hσ hσ1 Lr hLr
  refine ⟨max SXr SXc, max SZr SZc, ?_⟩
  intro sX sZ hsX hsZ
  obtain ⟨Cr, hCr, CHr, Υr, hCHr, hΥr, hMr⟩ := hrr sX sZ (by omega) (by omega)
  obtain ⟨Cc, hCc, CHc, Υc, hCHc, hΥc, hMc⟩ := hcc sX sZ (by omega) (by omega)
  refine ⟨Cr, Cc, hCr, hCc, max CHr CHc, max Υr Υc,
    hCHr.trans (le_max_left _ _), hΥr.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  obtain ⟨hjr, hjc⟩ := weak_carrier_start_pair (by omega : 1 ≤ Λ)
    (zero_le_one.trans hCHr) (zero_le_one.trans hCHc) hΥr.le hΥc.le hj₀
  obtain ⟨Mr, hmr⟩ := hMr j₀ hjr
  obtain ⟨Mc, hmc⟩ := hMc j₀ hjc
  refine ⟨max Mr Mc, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR hconstruction hlifts
  have hR := hmr M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR hconstruction hlifts
  have hC := hmc M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR hconstruction hlifts
  exact ⟨hR, hC⟩

theorem weak_stack_passage_of_readout_correction {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (s : ℝ) (M J N Lr : ℕ) (η Cr Cc : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (depth : ℕ)
    (happend : WeakPassageAppendStatement) (hs1 : s < 1) (hCr : 0 ≤ Cr) (hCc : 0 ≤ Cc)
    (heps : ∀ i, 0 < D.eps i)
    (hstep : ∀ i, M < i → i ≤ M + J → D.eps i ≤ D.eps (i - 1))
    (hR : WeakReadoutStackStatement s M J N Lr η Cr stage CcR depth)
    (hC : WeakCorrectionStackStatement s M J N Lr η Cc stage CcR depth) :
    WeakStackPassageStatement s M J N Lr η (Cr + Cc) stage CcR depth := by
  unfold WeakPassageAppendStatement at happend
  intro i hi hit K hK t g r hr0 hv
  let R := readoutCLM i (D.eps (i - 1)) η
    (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
    (fun v : CompIn (stage (i - 1)).comps => weakMass D N J η v.1)
  let out := compField (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
    (fun x v => weakGluedLift i N depth (stage i) (CcR i) t
      (weakReadoutStep i η (stage i) (stage (i - 1)) g) v x)
  unfold WeakCorrectionStackStatement at hC
  with_reducible obtain ⟨hcd, hper, hcost⟩ := hC i hi hit K hK t g r hr0 hv
  exact happend (H := CompSpace (stage (i - 1)).comps) (H' := CompSpace (stage i).comps) s (D.eps i) (D.eps (i - 1)) Cr Cc K (K + N) (heps i) (hstep i hi hit)
    hs1 (Nat.le_add_right _ _) hCr hCc r R out hr0 (hR i hi hit) hcd hper hcost

/-- The assembly spends the uniform constants once at every selected passage. -/
theorem weak_lift_passage_bounds_of_ingredients
    (hread : WeakReadoutBoundsStatement) (hcorr : WeakLiftCorrectionBoundsStatement)
    (happend : WeakPassageAppendStatement) : WeakLiftPassageBoundsStatement := by
  have hp := weak_uniform_passage_pair hread hcorr
  unfold WeakUniformPassagePairStatement at hp
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, htail⟩ := hp α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SX, SZ, horders⟩ := htail Λ hΛ bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN hη hη1 hσ hσ1 Lr hLr
  refine ⟨SX, SZ, ?_⟩
  intro sX sZ hsX hsZ
  obtain ⟨Cr, Cc, hCr, hCc, CHw, Υw, hCHw, hΥw, hstart⟩ := horders sX sZ hsX hsZ
  refine ⟨Cr + Cc, add_nonneg hCr hCc, CHw, Υw, hCHw, hΥw, ?_⟩
  intro j₀ hj₀
  obtain ⟨M₀, hM₀⟩ := hstart j₀ hj₀
  refine ⟨max 1 M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR hconstruction hlifts
  obtain ⟨hR, hC⟩ := hM₀ M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR hconstruction hlifts
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  apply weak_stack_passage_of_readout_correction s M Jw Nw Lr η₀ Cr Cc stage CcR (Jw * Rw)
    happend (by linarith only [hs₁, hα₀]) hCr hCc ?_ ?_ hR hC
  · intro i
    change 0 < ocEpsilon D.q D.Λ i
    rw [hDq, hDΛ]
    exact (Scales.epsilon_basic hq.1 h128).1
  · intro i hi _hit
    change ocEpsilon D.q D.Λ i ≤ ocEpsilon D.q D.Λ (i - 1)
    rw [hDq, hDΛ]
    have hsucc : i - 1 + 1 = i := by omega
    simpa only [hsucc] using CycleReference.epsilon_succ_le (n := i - 1) hq.1 h128

end AVRegularity.Finite.WeakLift
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance
open scoped ENNReal
namespace AVRegularity.Finite

/-! Weak nonidentity profiles: separate physical scaled jets from finite-order factorial
summation. The analytic jet statement retains the actual lift and all uniform choices. -/

/-- The zero jet and every positive spatial jet, at the profile's own wavelength.
No inverse factorial is included; it is supplied by the norm summation lemma. -/
def RawProfileJetBound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e : ℝ) (K : ℕ) (s : ℝ) (F : Vec 2 → H) (Y : ℝ≥0∞) : Prop :=
  ENNReal.ofReal (e ^ (-s)) * supNorm F ≤ Y ∧
  ∀ a ∈ multiIndicesBetween 1 K,
    ENNReal.ofReal (e ^ (((a 0 + a 1 : ℕ) : ℝ) - s)) *
      supNorm (partialDerivative a F) ≤ Y

/-- The finite number of slots in an order-K profile norm, including the zero jet. -/
def profileJetCount (K : ℕ) : ℕ := 1 + (multiIndicesBetween 1 K).card

/-- Factorial normalization and finite summation of the actual jet estimates. -/
def ProfileJetPackingStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e s : ℝ) (K Kmax : ℕ) (F : Vec 2 → H) (Y : ℝ≥0∞),
    0 < e → K ≤ Kmax → RawProfileJetBound e K s F Y →
      profileNorm e K s F ≤ (profileJetCount Kmax : ℝ≥0∞) * Y

namespace WeakLift

def WeakCorrectionJetStackStatement {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (s : ℝ) (M J N Lr : ℕ) (η Cstep : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (depth : ℕ) : Prop :=
  ∀ i : ℕ, M < i → i ≤ M + J → ∀ K : ℕ, K ≤ Lr + 3 →
  ∀ (t : ℝ) (g : CompIn (stage (i - 1)).comps → Vec 2 → ℝ)
    (r : Representation (CompSpace (stage (i - 1)).comps)),
    IsRepresentationAt (D.eps (i - 1)) (K + N) r →
    r.value = compField (fun v => weakMass D N J η v.1) (fun x v => g v x) →
    let R := readoutCLM i (D.eps (i - 1)) η
      (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
      (fun v : CompIn (stage (i - 1)).comps => weakMass D N J η v.1)
    let corr := compField (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
      (fun x v => weakGluedLift i N depth (stage i) (CcR i) t
        (weakReadoutStep i η (stage i) (stage (i - 1)) g) v x) - fun x => R (r.value x)
    ContDiff ℝ (K : ℕ) corr ∧ IsZ2Periodic corr ∧
      RawProfileJetBound (D.eps i) K s corr (ENNReal.ofReal Cstep *
        representedSize s (K + N) (D.eps (i - 1)) r)

/-- Scaled physical jets of the actual nonidentity lift, with all constants
before j0/M/phase/datum; this still requires the coefficient-to-physical-chart transfer. -/
def WeakLiftCorrectionJetBoundsStatement : Prop :=
  WeakUniformPassageStatement WeakCorrectionJetStackStatement

/-- Assemble the original correction leaf from the physical jets and their norm packing. -/
theorem weak_lift_correction_bounds_of_ingredients (hpack : ProfileJetPackingStatement)
    (hjets : WeakLiftCorrectionJetBoundsStatement) : WeakLiftCorrectionBoundsStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, htail⟩ := hjets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ bw hbw hbw1 J N R η σ hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SX, SZ, hreserve⟩ := htail Λ hΛ bw hbw hbw1 J N R η σ hJ hN hη hη1 hσ hσ1 Lr hLr
  refine ⟨SX, SZ, ?_⟩
  intro sX sZ hsX hsZ
  obtain ⟨Cjet, hCjet, CHw, Υw, hCHw, hΥw, hstart⟩ := hreserve sX sZ hsX hsZ
  refine ⟨(profileJetCount (Lr + 3) : ℝ) * Cjet,
    mul_nonneg (Nat.cast_nonneg _) hCjet, CHw, Υw, hCHw, hΥw, ?_⟩
  intro j₀ hj₀
  obtain ⟨M₀, hMtail⟩ := hstart j₀ hj₀
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm P Dm stage CcR hc hl i hi hit K hK t g r hr hv
  obtain ⟨hcd, hper, hraw⟩ := hMtail M hM D hDα hDq hDΛ hDζ hstream hband hterm P Dm
    stage CcR hc hl i hi hit K hK t g r hr hv
  refine ⟨hcd, hper, ?_⟩
  have he : 0 < D.eps i := by
    change 0 < ocEpsilon D.q D.Λ i
    rw [hDq, hDΛ]
    exact (Scales.epsilon_basic hq.1 (hΛ₀.trans hΛ)).1
  have hp := hpack (D.eps i) s K (Lr + 3) _ _ he hK hraw
  calc
    _ ≤ (profileJetCount (Lr + 3) : ℝ≥0∞) *
        (ENNReal.ofReal Cjet * representedSize s (K + N) (D.eps (i - 1)) r) := hp
    _ = _ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

end WeakLift

/-! The weak physical correction is the positive-degree part of the literal glued lift.
Dimension restoration leaves the gain (new wavelength / parent wavelength)^(1-s). -/

/-- Remove the degree-zero identity and retain every genuine positive-degree coefficient. -/
def positiveLiftCoefficients {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) : ℤ → ℕ → ℕ → LiftCoeff ι h :=
  fun k hh n => if n = 0 then 0 else Cc k hh n

/-- Positive lift degree beats the Hölder loss at a smaller wavelength. -/
def PositiveScaleGainStatement : Prop :=
  ∀ (e E s : ℝ), 0 < e → e ≤ E → s < 1 → (e / E) ^ (1 - s) ≤ 1

namespace WeakLift

def WeakIdentitySeparationStackStatement {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (_s : ℝ) (M J N Lr : ℕ) (η _Cstep : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (depth : ℕ) : Prop :=
  ∀ i : ℕ, M < i → i ≤ M + J → ∀ K : ℕ, K ≤ Lr + 3 →
  ∀ (t : ℝ) (g : CompIn (stage (i - 1)).comps → Vec 2 → ℝ)
    (r : Representation (CompSpace (stage (i - 1)).comps)),
    IsRepresentationAt (D.eps (i - 1)) (K + N) r →
    r.value = compField (fun v => weakMass D N J η v.1) (fun x v => g v x) →
    let R := readoutCLM i (D.eps (i - 1)) η
      (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
      (fun v : CompIn (stage (i - 1)).comps => weakMass D N J η v.1)
    let corr := compField (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
      (fun x v => weakGluedLift i N depth (stage i) (CcR i) t
        (weakReadoutStep i η (stage i) (stage (i - 1)) g) v x) - fun x => R (r.value x)
    corr = compField (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
      (fun x v => weakGluedLift i N depth (stage i) (positiveLiftCoefficients (CcR i)) t
        (weakReadoutStep i η (stage i) (stage (i - 1)) g) v x)

def WeakPositiveResponseStackStatement {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (s : ℝ) (M J N Lr : ℕ) (η Cstep : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (depth : ℕ) : Prop :=
  ∀ i : ℕ, M < i → i ≤ M + J → ∀ K : ℕ, K ≤ Lr + 3 →
  ∀ (t : ℝ) (g : CompIn (stage (i - 1)).comps → Vec 2 → ℝ)
    (r : Representation (CompSpace (stage (i - 1)).comps)),
    IsRepresentationAt (D.eps (i - 1)) (K + N) r →
    r.value = compField (fun v => weakMass D N J η v.1) (fun x v => g v x) →
    let corr := compField (fun v : CompIn (stage i).comps => weakMass D N J η v.1)
      (fun x v => weakGluedLift i N depth (stage i) (positiveLiftCoefficients (CcR i)) t
        (weakReadoutStep i η (stage i) (stage (i - 1)) g) v x)
    ContDiff ℝ (K : ℕ) corr ∧ IsZ2Periodic corr ∧
      RawProfileJetBound (D.eps i) K s corr (ENNReal.ofReal Cstep *
        ENNReal.ofReal ((D.eps i / D.eps (i - 1)) ^ (1 - s)) * representedSize s (K + N) (D.eps (i - 1)) r)

/-- The normalized identity part is exactly the constant component readout. -/
def WeakIdentitySeparationStatement : Prop :=
  WeakUniformPassageStatement WeakIdentitySeparationStackStatement

/-- A certified, graded, chart-transferred positive-degree response, with its
actual dimensional gain and periodic spatial regularity; constants precede j0/M. -/
def WeakPositiveResponseJetStatement : Prop :=
  WeakUniformPassageStatement WeakPositiveResponseStackStatement

theorem weak_uniform_properties_pair (Qread Qcorr : WeakPassageProperty)
    (hread : WeakUniformPassageStatement Qread)
    (hcorr : WeakUniformPassageStatement Qcorr) :
    WeakUniformPassagePairStatement Qread Qcorr := by
  unfold WeakUniformPassageStatement at hread hcorr
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λr, hΛr, hr⟩ := hread α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λc, hΛc, hc⟩ := hcorr α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λr Λc, by omega, ?_⟩
  intro Λ hΛ bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SXr, SZr, hrr⟩ := hr Λ (by omega) bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SXc, SZc, hcc⟩ := hc Λ (by omega) bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN hη hη1 hσ hσ1 Lr hLr
  refine ⟨max SXr SXc, max SZr SZc, ?_⟩
  intro sX sZ hsX hsZ
  obtain ⟨Cr, hCr, CHr, Υr, hCHr, hΥr, hMr⟩ := hrr sX sZ (by omega) (by omega)
  obtain ⟨Cc, hCc, CHc, Υc, hCHc, hΥc, hMc⟩ := hcc sX sZ (by omega) (by omega)
  refine ⟨Cr, Cc, hCr, hCc, max CHr CHc, max Υr Υc,
    hCHr.trans (le_max_left _ _), hΥr.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  obtain ⟨hjr, hjc⟩ := weak_carrier_start_pair (by omega : 1 ≤ Λ)
    (zero_le_one.trans hCHr) (zero_le_one.trans hCHc) hΥr.le hΥc.le hj₀
  obtain ⟨Mr, hmr⟩ := hMr j₀ hjr
  obtain ⟨Mc, hmc⟩ := hMc j₀ hjc
  refine ⟨max Mr Mc, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR hconstruction hlifts
  have hR := hmr M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR hconstruction hlifts
  have hC := hmc M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR hconstruction hlifts
  exact ⟨hR, hC⟩

/-- Separate identity, retain the genuine physical response and absorb only its scale gain. -/
theorem weak_lift_correction_jets_of_ingredients (hidentity : WeakIdentitySeparationStatement)
    (hpositive : WeakPositiveResponseJetStatement) (hgain : PositiveScaleGainStatement) :
    WeakLiftCorrectionJetBoundsStatement := by
  have hpair := weak_uniform_properties_pair WeakIdentitySeparationStackStatement
    WeakPositiveResponseStackStatement hidentity hpositive
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, htail⟩ := hpair α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ bw hbw hbw1 J N R η σ hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SX, SZ, hreserve⟩ := htail Λ hΛ bw hbw hbw1 J N R η σ hJ hN hη hη1 hσ hσ1 Lr hLr
  refine ⟨SX, SZ, ?_⟩
  intro sX sZ hsX hsZ
  obtain ⟨Cr, Cp, _hCr, hCp, CHw, Υw, hCHw, hΥw, hstart⟩ := hreserve sX sZ hsX hsZ
  refine ⟨Cp, hCp, CHw, Υw, hCHw, hΥw, ?_⟩
  intro j₀ hj₀
  obtain ⟨M₀, hMtail⟩ := hstart j₀ hj₀
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm P Dm stage CcR hc hl i hi hit K hK t g r hr hv
  obtain ⟨hId, hPos⟩ := hMtail M hM D hDα hDq hDΛ hDζ hstream hband hterm P Dm stage CcR hc hl
  have hid := hId i hi hit K hK t g r hr hv
  have hp := hPos i hi hit K hK t g r hr hv
  change _ = _ at hid
  change ContDiff ℝ (K : ℕ) _ ∧ IsZ2Periodic _ ∧ RawProfileJetBound _ _ _ _ _
  rw [hid]
  refine ⟨hp.1, hp.2.1, ?_⟩
  have he : 0 < D.eps i := by
    change 0 < ocEpsilon D.q D.Λ i
    rw [hDq, hDΛ]
    exact (Scales.epsilon_basic hq.1 (hΛ₀.trans hΛ)).1
  have heE : D.eps i ≤ D.eps (i - 1) := by
    change ocEpsilon D.q D.Λ i ≤ ocEpsilon D.q D.Λ (i - 1)
    rw [hDq, hDΛ]
    have hi1 : 1 ≤ i := by omega
    simpa only [Nat.sub_add_cancel hi1] using
      CycleReference.epsilon_succ_le (n := i - 1) hq.1 (hΛ₀.trans hΛ)
  have hs : s < 1 := hs₁.trans (by linarith only [hα₀])
  have hpow := hgain (D.eps i) (D.eps (i - 1)) s he heE hs
  have hY : ENNReal.ofReal Cp * ENNReal.ofReal ((D.eps i / D.eps (i - 1)) ^ (1 - s)) *
      representedSize s (K + N) (D.eps (i - 1)) r ≤
      ENNReal.ofReal Cp * representedSize s (K + N) (D.eps (i - 1)) r := by
    simpa only [ENNReal.ofReal_one, mul_one] using
      mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hpow)) le_rfl
  exact ⟨hp.2.2.1.trans hY, fun a ha => (hp.2.2.2 a ha).trans hY⟩

end WeakLift

end AVRegularity.Finite
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.TerminalLift

/-! Terminal covariance and oscillatory differences: physical raw jets followed by
factorial profile summation. The general dW/DW/χw telescope and the regularity clauses of
`TerminalDifferenceBoundsGeneralStatement` stay fixed. -/

/-- Sum the covariance and oscillatory profile costs at their own wavelengths. -/
def TerminalProfileJetPackingStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E e s C : ℝ) (K Kmax : ℕ) (X : ℝ≥0∞) (cov osc : Vec 2 → H),
    0 < E → 0 < e → K ≤ Kmax →
    RawProfileJetBound E K s cov (ENNReal.ofReal C * X) →
    RawProfileJetBound e K s osc (ENNReal.ofReal C * X) →
      profileNorm E K s cov + profileNorm e K s osc ≤
        ENNReal.ofReal ((2 * profileJetCount Kmax : ℕ) * C) * X

/-- Keep the precise covariance and oscillatory regularity clauses consumed by
`TerminalDifferenceBoundsGeneralStatement`.
The analytic estimates are stated separately for the raw physical jets of both differences. -/
def TerminalDifferenceJetsProperty : TerminalProfileProperty :=
  fun s E e C k kin r _R cov osc =>
    ContDiff ℝ (k : ℕ) cov ∧ IsZ2Periodic cov ∧
    ContDiff ℝ (k : ℕ) osc ∧ IsZ2Periodic osc ∧
    RawProfileJetBound E k s cov (ENNReal.ofReal C * representedSize s kin E r) ∧
    RawProfileJetBound e k s osc (ENNReal.ofReal C * representedSize s kin E r)

/-- The actual covariance and nonidentity lift differences have uniform physical
scaled jets. The two regularity clauses are those of `TerminalDifferenceBoundsGeneralStatement`. -/
def TerminalDifferenceJetBoundsGeneralStatement : Prop :=
  TerminalUniformProfileStatement TerminalDifferenceJetsProperty

/-- Preserve all quantifier choices while summing the two physically labelled jet budgets. -/
theorem terminal_difference_bounds_of_ingredients (hpack : TerminalProfileJetPackingStatement)
    (hjets : TerminalDifferenceJetBoundsGeneralStatement) :
    TerminalDifferenceBoundsGeneralStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, htail⟩ := hjets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw
    hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  obtain ⟨SX, SZ, hreserve⟩ := htail Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1
    Jw Lw dW DW T₀ η₀ σw χw hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT
    tT hsched Lr
  refine ⟨SX, SZ, ?_⟩
  intro sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  obtain ⟨Cjet, hCjet, hstart⟩ := hreserve sXT sZT hsXT hsZT cr hcr hcr1
    Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  refine ⟨(2 * profileJetCount (Lr + 3) : ℕ) * Cjet,
    mul_nonneg (Nat.cast_nonneg _) hCjet, ?_⟩
  intro j₀
  obtain ⟨M₀, hMt⟩ := hstart j₀
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  obtain ⟨hcov, hcovp, hosc, hoscp, hcovraw, hoscraw⟩ :=
    hMt M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
      lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  refine ⟨hcov, hcovp, hosc, hoscp, ?_⟩
  have heps : ∀ i, 0 < D.eps i := by
    intro i
    change 0 < ocEpsilon D.q D.Λ i
    rw [hDq, hDΛ]
    exact (Scales.epsilon_basic hq.1 (hΛ₀.trans hΛ)).1
  exact hpack (D.eps (M - 1)) (D.eps M) s Cjet (Lr + 3) (Lr + 3)
    (representedSize s (Lr + (NT + 2 * pT) + 4) (D.eps (M - 1)) r) _ _
    (heps _) (heps _) le_rfl hcovraw hoscraw

end AVRegularity.Finite.TerminalLift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Finite.SeedTransport

/-! Assembly of seed-system uniqueness from its literal order-zero
kernel-energy budget. The remaining ingredient is the actual terminal reencoding,
with its kernel-paid Sobolev lift, not an order-cap comparison premise. -/

/-- The terminal trajectory, restricted, truncated and reindexed, is a seed solution.
All premises are precisely the premises of `terminal_seed_transport`; the second uniqueness conjunct
is proved separately below. -/
def TerminalSeedReencodingStatement : Prop :=
  ∀ {D : OCData} {Dt Ds : ℕ} {b : ℝ} {j₀ : ℕ}
    (Pt : ProvParams) (lawT : BirthLaw) (rootM rootR : ℕ → ℝ)
    (seedKt freshKt seedKc : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (Gt : GenStage D ScalarH Dt b j₀) (seed : GenStage D ScalarH Ds b j₀)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps)
    (henc : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (M Kout : ℕ) (tp sn tf : ℝ) (htp : tp ≤ sn) (hsn : sn ≤ tf)
    (Z₀ : ∀ v : CompIn Gt.comps, TorusHk Kout (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Kout (ScalarH v.1.root))
    (Zw : ∀ v : CompIn Gt.comps, ℝ → TorusHk (Kout + 1) (ScalarH v.1.root))
    (Zk : ∀ v u (_ : Gt.fam.Γ v u), ℝ → TorusHk (Kout + Dt - 1) (ScalarH u.1.root))
    (hZ : Gt.IsRegSolution Pt seedKt freshKt φ₀ hφ₀ (D.termB M) (streamVel (D.Φ (M - 1))) Kout tp
      tf Z₀ (fun _ _ => 0) (fun _ _ => 0) Z Zw Zk) ,
    ∀ (P : ProvParams) (freshK : ℕ → KernelSpec)
      (ρ θ : ℝ) (π : CompIn seed.comps → ℝ) (cker : ℕ → ℝ),
      0 < ρ → 0 < D.κ (M - 1) → 2 ≤ Ds → (∀ w, 0 < π w) → θ ≤ 1 / 8 →
      (∀ w u (γ : seed.fam.Γ w u) (d : ↥(Finset.Icc 2 Ds)),
        (Measurable fun q : Set.Icc sn tf × Vec 2 => seed.physCoeff w u γ d.1 q.1 q.2) ∧
        (∀ t ∈ Set.Icc sn tf, ContDiff ℝ (0 : ℕ) (seed.physCoeff w u γ d.1 t)) ∧
        (∀ t ∈ Set.Icc sn tf, AVenhance.IsZ2Periodic (seed.physCoeff w u γ d.1 t)) ∧
        coefficientSeminorm ρ 0 sn tf (seed.physCoeff w u γ d.1) ≠ ⊤) →
      (∀ w u (γ : seed.fam.Γ w u),
        0 < (seed.kernelOf P seedKc freshK w u γ).width ∧
        IsSpatialRegularizerTorus ρ 0 Ds sn tf cker (seed.kernelOf P seedKc freshK w u γ).width
          (seed.sysS P seedKc freshK φ₀ hφ₀ w u γ)) →
      SchurBound θ (kernelSchurMatrix (ι := CompIn seed.comps) (h := fun w => ScalarH w.1.root)
        (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (D.κ (M - 1)) ρ π 0 Ds sn tf cker
        (fun w u γ => (seed.kernelOf P seedKc freshK w u γ).width)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun w u γ d => seed.physCoeff w u γ d.1)) →
      (∃ (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
          (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ → TorusHk (0 + Ds - 1) (ScalarH u.1.root)),
        seed.IsRegSolution P seedKc freshK φ₀ hφ₀ (D.κ (M - 1)) (streamVel (D.Φ (M - 1))) 0 sn tf
          (fun w => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) sn))
          (fun _ _ => 0) (fun _ _ => 0)
          (fun w t => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) t)) Uw Uk)

/-- The second conjunct of `terminal_seed_transport` follows from order-zero uniqueness. -/
theorem terminal_seed_transport_of_reencoding (hencode : TerminalSeedReencodingStatement) :
    Assembly.TerminalSeedTransportStatement := by
  intro D Dt Ds bw j₀ Pt lawT rootM rootR seedKt freshKt seedKc φ₀ hφ₀ Gt seed ι henc
    M Kout tp sn tf htp hsn Z₀ Z Zw Zk hZ P freshK ρ θ π cker hρ hν hDs hπ hθ hcoeff hkernel hschur
  unfold TerminalSeedReencodingStatement at hencode
  with_reducible
    obtain ⟨Vw, Vk, hV⟩ := hencode (D := D) (Dt := Dt) (Ds := Ds) (b := bw) (j₀ := j₀) Pt lawT rootM rootR seedKt freshKt seedKc φ₀ hφ₀ Gt seed ι
      henc M Kout tp sn tf htp hsn Z₀ Z Zw Zk hZ P freshK ρ θ π cker hρ hν hDs hπ hθ
      hcoeff hkernel hschur
    refine ⟨⟨Vw, Vk, hV⟩, ?_⟩
    intro U Uw Uk hU
    exact seed_order_zero_unique_of_budget P seedKc freshK φ₀ hφ₀ seed M sn tf ρ θ π cker
      hsn hρ hν hDs hπ hθ hcoeff hkernel hschur
      (fun w => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) sn))
      U (fun w t => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) t)) Uw Vw Uk Vk hU hV

end AVRegularity.Finite.SeedTransport
end
end
end
