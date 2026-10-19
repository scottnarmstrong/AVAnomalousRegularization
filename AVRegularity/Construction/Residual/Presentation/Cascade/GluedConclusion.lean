-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Residual.Presentation.Cascade.PointwiseEnvelope
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import AVRegularity.EntryTerminal.Ingredients.Recon.FluxSum.FluxSum
public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FrontierFlux.Jets
public import AVRegularity.Construction.StageEnvelopes.SuccessorPreparation
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.Construction.Residual.Presentation.Cascade.FilterCtx
import Mathlib.Data.Int.Star

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.StageEnvelopes
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The pointwise molecular envelope of a step stage: the assembly** (cascade side of the bill
residual).

`step_pointwise`: at a step stage `G = G₁'.retained G₁.level H J` of the cascade, the
context input of the shared producer (`ContextEnvelopeInput`) is built from the stage's own
invariant (natural, context certificate), the reserves of `IsInvariantAdmissible`, the carrier
constants and the length of the higher identities, and `pointwise_of_estimate` gives
`IsSeedPointwiseMolecular law k_I G a t_f`. The numerical facts of the scales enter as
hypotheses; the proof module derives them from the library scale statements.

For a step stage with empty components the envelope is vacuous. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- **The pointwise molecular envelope of a step stage of the cascade.** -/
theorem step_pointwise {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (h128 : 128 ≤ Λ) (hζ : IsFastProfile ζ)
    (hbw : 0 < bw) (hbwupper : bw ≤ 1 / 10000) (kS kI : InvConsts)
    (est : ContextEnvelopeEstimate
      (successorEnvelopeParameters α s q Λ ζ hα₀ hα₁ hs₀ hs₁ hq h128 hζ bw hbw hbwupper kS Dm))
    {Mn : SuccMenu} {G₁ G₁' : GenStage D hr Dm bw j₀}
    (hDα : D.α = α) (hDq : D.q = q) (hDΛ : D.Λ = Λ) (hDζ : D.ζ = ζ)
    (hseq : IsOCStreamSeq α q Λ ζ D.Φ)
    (hnat : ∃ M, (G₁'.retained G₁.level Mn.H Mn.J).IsNatural M)
    (hcert : (G₁'.retained G₁.level Mn.H Mn.J).IsContextCertified kI)
    (hlev : 1 ≤ (G₁'.retained G₁.level Mn.H Mn.J).level)
    (hjl : j₀ ≤ (G₁'.retained G₁.level Mn.H Mn.J).level)
    (hcar : ∃ CH Υ : ℝ, CarrierOK 100 CH Υ ∧ IsCarrierStart D.α D.q D.Λ bw CH Υ j₀)
    (hqD : 1 < D.q) (hΛD : 128 ≤ D.Λ)
    (hkap : 0 < D.kap (G₁'.retained G₁.level Mn.H Mn.J).level)
    (hρ0 : 0 < rhoStar D kI.c₀ (G₁'.retained G₁.level Mn.H Mn.J).level)
    (hρε : rhoStar D kI.c₀ (G₁'.retained G₁.level Mn.H Mn.J).level ≤
      D.eps (G₁'.retained G₁.level Mn.H Mn.J).level)
    (henv0 : 0 ≤ kI.mEnv) (henvlt : kI.mEnv < 1 / ((kI.Hprod : ℝ) + 1))
    (hHprod : kI.Hprod = kS.Hprod) (hprod : kI.Hprod = kI.G0 + Mn.H + 1)
    (hKs : kI.Ks ≤ kS.Ks) (hKan : kI.Kan ≤ kS.Kan) (hLan : kI.Lan ≤ kS.Lan)
    (hJm : kI.Jm ≤ kS.Jm)
    (hlength : ∀ v u (γ : (G₁'.retained G₁.level Mn.H Mn.J).fam.Γ v u),
      3 ≤ ((G₁'.retained G₁.level Mn.H Mn.J).fam.identity v u γ).maxOrder →
      ((G₁'.retained G₁.level Mn.H Mn.J).fam.identity v u γ).record.length ≤
        rhoStar D kI.c₀ (G₁'.retained G₁.level Mn.H Mn.J).level)
    (hfloor : est.levelFloor ≤ (G₁'.retained G₁.level Mn.H Mn.J).level)
    (hCa : est.Ca ≤ kI.Ca) (hCm : ∀ j, est.Cm j ≤ kI.Cm j) (law : BirthLaw) (a tf : ℝ) :
    IsSeedPointwiseMolecular law kI (G₁'.retained G₁.level Mn.H Mn.J) a tf := by
  refine pointwise_of_estimate est _ kI ?_ hfloor hCa hCm law a tf
  refine { bw_eq := rfl
           alpha_eq := hDα
           q_eq := hDq
           base_eq := hDΛ
           profile_eq := hDζ
           stream := hseq
           natural := hnat
           certified := hcert
           level_pos := hlev
           carrier_start := hjl
           carrier_environment := hcar
           q_pos := hqD
           large := hΛD
           kap_pos := hkap
           radius_pos := hρ0
           radius_le := hρε
           wavelength_le := Providers.CascadeInvariants.eps_le_of_le hqD hΛD (Nat.sub_le _ _)
           inner_nonneg := henv0
           inner_le := ?_
           reserve_le := ?_
           reserve_upper := fun v =>
             (AVRegularity.Construction.Preservation.Buffer.compReserve_le_one kI v.1).trans
               (by norm_num)
           slot_order := hKs
           slow_order := hKan
           fast_order := hLan
           molecular_order := hJm
           source_order := fun v u γ => ((G₁'.retained G₁.level Mn.H Mn.J).fam.identity v u γ).le_D
           higher_length := hlength }
  · change kI.mEnv ≤ 1 / ((kS.Hprod : ℝ) + 1)
    rw [← hHprod]
    exact henvlt.le
  · intro v
    change 2 / ((kS.Hprod : ℝ) + 1) ≤ compReserve kI v.1
    rw [← hHprod]
    exact retained_compReserve_ge hprod (Finset.mem_filter.mp v.2).2.1

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Filter
open scoped Topology Classical
open AVRegularity.Construction.StageEnvelopes
open AVRegularity.Construction.Preservation AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The pointwise molecular envelope of the incoming stage: the proof** (cascade side of the
bill residual).

`seedPointwise` proves `SeedPointwiseStatement`. The constants of the prefix are chosen
as in `retained_pointwise_context_inputs`: `Λ₀` from the scale statements (passage scales,
cascade record length, enhanced radius), `c₀max = 1`, the thresholds
`thr = {kS with C_a, C_m from the producer's estimate}`, `C_H = 1` and the carrier constant of
`common_carrier_constants`; the level `m_*` after `kI`. At a context, by cases on
`IsCascadeStage`: the seed (the premise, `kW = kS`, `a = tS`) or a step (`step_pointwise`
at `kW = kI`, `a = tA`).

The first passage `m = n` is the seed case; for `m < n` it is a step, with `G₁.level = m + 1 ≤ n`. -/

/-- **The pointwise envelope at a context**: the pointwise molecular envelope of the incoming
stage of every context of level `≥ m_*`, from the supplied pointwise envelope of the seed. -/
theorem seedPointwise (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : SeedPointwiseStatement α s q ζ := by
  classical
  let estimates (p : ContextEnvelopeParameters) :=
    Classical.choice (Cauchy.context_stage_envelopes p)
  obtain ⟨Cu, _hCu, Λp, hΛp, hpass⟩ := Providers.CascadeInvariants.exists_passScales hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λl, hΛl, hlens⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λp (max Λl Λr), by omega, ?_⟩
  intro Λ hΛ
  refine ⟨1, one_pos, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout hrecon halloc hsX hsZ
  have h128 : 128 ≤ Λ := by omega
  let pe := successorEnvelopeParameters α s q Λ ζ hα₀ hα₁ hs₀ hs₁ hq h128 hζ bw hbw hbwupper kS
    (succSchedD D₀ N p (H + 1))
  let thr : InvConsts :=
    { kS with Ca := (estimates pe).Ca, Cm := fun j => (estimates pe).Cm j }
  obtain ⟨Υ', hcarrier, hstart_mono⟩ := Cauchy.common_carrier_constants (α := α) (q := q)
    (Λ := Λ) (b := bw) h128 (le_refl (1 : ℝ)) (one_pos : (0 : ℝ) < 1)
  refine ⟨thr, 1, Υ', le_rfl, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 100)
    ((le_max_left _ _).trans hcarrier.2), ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  rcases id hkI with ⟨hcEq, hcrEq, _, _, _, _, _, _, _, _, _, hCa, hCm, _, _, _, _, hKresKs,
    hKs, _, hKan, _, hLan, hKresJm, hJm, _, _, hG0, hHprod, hprod, henvnonneg, _, henvlt⟩
  have hCaI : (estimates pe).Ca ≤ kI.Ca := hCa
  have hCmI (j : ℕ) : (estimates pe).Cm j ≤ kI.Cm j := (hCm j).2
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hdecay := Buffer.preparation_parent_power_tendsto_zero hq.1 h128
    (mul_pos (by norm_num : (0 : ℝ) < 3) hδ)
  have hlim : Tendsto (fun m : ℕ => Cu * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q))
      atTop (𝓝 0) := by simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  obtain ⟨mp, hmp⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds zero_lt_one))
  have hcI : 0 < kI.c₀ := hcEq.symm ▸ hc₀
  have hcIupper : kI.c₀ ≤ 1 := hcEq.symm ▸ hc₀upper
  have hcrI : kI.cr ≤ 1 := hcrEq.symm ▸ hcrupper
  obtain ⟨mr, hmr2, hradius⟩ := hradius Λ (by omega) kI.c₀ 1 hcI zero_lt_one
  refine ⟨max 2 (max mp (max mr (max (j₀ + 2) ((estimates pe).levelFloor + 1)))), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hpw
  have hΛD : 128 ≤ c.D.Λ := by rw [c.hΛ]; exact h128
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hqD : 1 < c.D.q := c.hq.symm ▸ hq.1
  have hζD : IsFastProfile c.D.ζ := c.hζ.symm ▸ hζ
  have hbandD : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    simpa only [c.hα, c.hq, c.hΛ, c.hζ, c.hterm] using c.hband
  have hmM : c.m ≤ c.D.term := by rw [c.hterm]; exact c.hmn.trans c.hnM.le
  have hε (i : ℕ) : 0 < c.D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
  have hκ : 0 < c.D.κ c.m := CycleReference.bandChain_pos hΛ1 hζD hbandD hmM
  have hrho : 0 < rhoStar c.D kI.c₀ c.m := mul_pos hcI
    (lt_min (hε _) (Real.sqrt_pos.mpr (div_pos hκ (Real.rpow_pos_of_pos (hε _) _))))
  have hrhoe : rhoStar c.D kI.c₀ c.m ≤ c.D.eps c.m :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hcI.le).trans
      (mul_le_of_le_one_left (hε _).le hcIupper)
  have hGl := c.hlevel
  have hinv := c.hinv
  have hcasc := c.hcascade
  generalize c.G = G at hGl hinv hcasc ⊢
  cases hcasc with
  | seed => exact ⟨kS, hcEq.symm, halloc.2.1, halloc.2.2.2.2.1, c.tS, c.htA, hpw⟩
  | @step G₁ G₁' hG₁ hact =>
    refine ⟨kI, rfl, hKresKs, hKresJm, c.tA, le_rfl, ?_⟩
    have hGl' : G₁'.level = c.m := hGl
    have hG1 : G₁.level = c.m + 1 := by have := hact.1; have := hact.2.1; omega
    have hlvl : G₁'.level = G₁.level - 1 := hact.2.1
    have hG1T : G₁.level ≤ c.D.term := by
      have h1 := Providers.CascadeInvariants.level_le_of_cascade hG₁
      rw [c.hseed.1] at h1
      have := c.hnM
      rw [c.hterm]; omega
    have hseedT := Providers.CascadeInvariants.hasTags_of_generatedSeed c.hseed
    have hpass' := hpass c.D c.hα c.hq c.hζ (by rw [c.hΛ]; omega)
      (by simpa only [c.hterm, c.hΛ] using c.hband) G₁.level (by omega) hG1T
    have hsmall : Cu * c.D.eps (G₁.level - 1) ^ (3 * ocDelta c.D.α c.D.q) ≤ 1 := by
      simpa only [OCData.eps, c.hα, c.hq, c.hΛ] using hmp G₁.level (by omega)
    have hεlift : c.D.eps G₁.level ≤ liftLength c.D G₁.level := by
      have hd := hpass'.hDρ
      have hρ := hpass'.hρ0
      have hds : ocDStar c.D.q c.D.Λ G₁.level (c.D.kap G₁.level) (c.D.kap (G₁.level - 1)) /
          liftLength c.D G₁.level ≤ 1 := hd.trans hsmall
      exact hpass'.hεd.trans ((div_le_one hρ).mp hds)
    have hlift : liftLength c.D G₁.level ≤ rhoStar c.D kI.c₀ (G₁.level - 1) := by
      have hh := hradius c.D c.hα c.hq c.hΛ c.hζ hbandD G₁.level (by omega) hG1T
      simpa only [rhoEnh, one_mul, liftLength] using hh
    have hlensG := hlens hr c.D c.hα c.hq c.hζ (by rw [c.hΛ]; omega) hbandD _ bw j₀ _ Cw kI.cr
      σ₀ (succEta0 α q s) N p hcrI c.seed G₁ hseedT
      (Providers.CascadeInvariants.length_of_generatedSeed c.hseed)
      (by rw [c.hseed.1, c.hterm]; exact c.hnM.le) hG₁ (by omega)
    have hR : (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p).Rb (G₁.level - 1) ≤
        rhoStar c.D kI.c₀ (G₁.level - 1) := by
      change freshLength c.D kI.cr (G₁.level - 1) ≤ _
      have heq : freshLength c.D kI.cr (G₁.level - 1) = kI.cr * liftLength c.D G₁.level := by
        unfold freshLength liftLength
        rw [Nat.sub_add_cancel (by omega : 1 ≤ G₁.level)]
      rw [heq]
      exact (mul_le_mul_of_nonneg_right hcrI hpass'.hρ0.le).trans
        (by simpa only [one_mul] using hlift)
    have hlength0 := step_higher_length (Providers.CascadeInvariants.hasTags_of_cascade hseedT hG₁) hact
      (fun v u γ hbe => (hlensG v u γ hbe).trans (hεlift.trans hlift)) hR
    refine step_pointwise hα₀ hα₁ hs₀ hs₁ hq h128 hζ hbw hbwupper kS kI (estimates pe)
      c.hα c.hq c.hΛ c.hζ c.hseq ⟨c.Mnat, hinv.1⟩ hinv.2.2.2.2.2.1 ?_ ?_
      ⟨1, Υ', hcarrier, by simpa only [c.hα, c.hq, c.hΛ] using hstart⟩ hqD hΛD ?_ ?_ ?_
      henvnonneg henvlt hHprod hprod hKs hKan hLan hJm ?_ ?_ hCaI hCmI c.law c.tA c.tf
    · change 1 ≤ G₁'.level; omega
    · change j₀ ≤ G₁'.level; omega
    · change 0 < c.D.kap G₁'.level
      rw [hGl']
      unfold OCData.kap
      exact CycleReference.bandChain_pos hΛ1 hζD hbandD (Nat.min_le_right _ _)
    · change 0 < rhoStar c.D kI.c₀ G₁'.level
      rw [hGl']; exact hrho
    · change rhoStar c.D kI.c₀ G₁'.level ≤ c.D.eps G₁'.level
      rw [hGl']; exact hrhoe
    · intro v u γ h3
      change _ ≤ rhoStar c.D kI.c₀ G₁'.level
      rw [hlvl]
      exact hlength0 v u γ h3
    · change _ ≤ G₁'.level
      omega

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The reconstruction defect (i): the mean-flux coefficients of a pulse at any grade**.

`gluedMeanFluxCoeff Q Cc r n` is the diagonal mean-flux coefficient at grade `0` and the positive one at
grades `r ≥ 1`. At a lift setting with a lift sequence it has vanishing zero-order term, a `C¹`
mean coefficient, presents the lift mean in divergence form, and applied at `z = 0` is the cell mean
of the slow lift flux. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}

/-- The mean-flux coefficients of grade `r` and degree `n`. -/
def gluedMeanFluxCoeff (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (r n : ℕ) : Fin 2 → LiftCoeff ι h :=
  fun l => if r = 0 then diagonalMeanFluxCoefficient Q Cc n l
    else positiveMeanFluxCoefficient Q Cc r n l

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
theorem Cfl_zero_eq' (Cc : ℕ → ℕ → LiftCoeff ι h) (n : ℕ) :
    gluedMeanFluxCoeff Q Cc 0 n = diagonalMeanFluxCoefficient Q Cc n := by
  funext l; simp [gluedMeanFluxCoeff]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
theorem Cfl_pos_eq' (Cc : ℕ → ℕ → LiftCoeff ι h) (r n : ℕ) (hr : r ≠ 0) :
    gluedMeanFluxCoeff Q Cc r n = positiveMeanFluxCoefficient Q Cc r n := by
  funext l; simp [gluedMeanFluxCoeff, hr]

variable
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
omit [∀ i, CompleteSpace (h i)] in
theorem Cfl_zero_order' (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (r : ℕ) (hrH : r ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (hnR : n ≤ N + D) (l : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (α : DerivativeWord2 0)
    (X z : Vec 2) (v u : ι) : gluedMeanFluxCoeff Q Cc r n l 0 α t X z v u = 0 := by
  by_cases hr : r = 0
  · simp only [gluedMeanFluxCoeff, hr, ite_true]
    exact setting_diagonal_mean_flux_coefficient_zero_order P sX sZ Cc hseq n hn l t ht α X z v u
  · simp only [gluedMeanFluxCoeff, hr, ite_false]
    exact setting_positive_mean_flux_coefficient_zero_order P sX sZ hsZ Cc hseq 0
      (by have := P.qs_eq; nlinarith [P.N_ge, P.D_ge]) r (Nat.pos_of_ne_zero hr) hrH n hn hnR
      l t ht α X z v u

include P in
omit [∀ i, CompleteSpace (h i)] in
theorem Cfl_pres' (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (r : ℕ) (hrH : r ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (hnR : n ≤ N + D) (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) r n t X =
      meanApply n (meanOf (gluedMeanFluxCoeff Q Cc r n)) (fun _ => f) t X := by
  have hres : 0 + (N + D) ≤ qs := by
    rw [P.qs_eq]
    nlinarith [P.N_ge, P.D_ge, Nat.zero_le K, Nat.zero_le H, sq_nonneg (N + D)]
  by_cases hr : r = 0
  · subst hr
    have := setting_diagonal_mean_flux_meanApply P sX sZ hX hZ Cc hseq 0 hres n hn hnR f hf t ht X
    rw [Cfl_zero_eq']; exact this
  · have := setting_positive_mean_flux_meanApply P sX sZ hX hZ Cc hseq 0 hres r
      (Nat.pos_of_ne_zero hr) hrH n hn hnR f hf t ht X
    rw [Cfl_pos_eq' _ _ _ hr]; exact this

include P in
omit [∀ i, CompleteSpace (h i)] in
theorem Cfl_contDiff' (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (r : ℕ) (hrH : r ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (hnR : n ≤ N + D) (d : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n) (α : DerivativeWord2 (d - 1))
    (l : Fin 2) (v u : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ 1 (fun X => meanOf (gluedMeanFluxCoeff Q Cc r n) d α t X l v u) := by
  have hres : 0 + (N + D) ≤ qs := by
    rw [P.qs_eq]
    nlinarith [P.N_ge, P.D_ge, Nat.zero_le K, Nat.zero_le H, sq_nonneg (N + D)]
  by_cases hr : r = 0
  · have := setting_diagonal_mean_flux_coefficient_contDiff_upto P sX sZ hsZ Cc hseq 0 hres n hn
      hnR l t ht (d - 1) (by omega) α 0 v u
    rw [hr, Cfl_zero_eq']
    have h1 := this
    simp only [Nat.zero_add, Nat.cast_one] at h1
    exact h1
  · have := setting_positive_mean_flux_coefficient_contDiff_upto P sX sZ hsZ Cc hseq 0 hres r
      (Nat.pos_of_ne_zero hr) hrH n hn hnR l t ht (d - 1) (by omega) α 0 v u
    rw [Cfl_pos_eq' _ _ _ hr]
    have h1 := this
    simp only [Nat.zero_add, Nat.cast_one] at h1
    exact h1

include P in
theorem Cfl_hid' (sX sZ : ℕ) (hX : D ≤ sX) (hZ : D ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (r : ℕ) (hrH : r ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : Fin 2) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (X : Vec 2) (v : ι) :
    liftApply (n - 1) (gluedMeanFluxCoeff Q Cc r n l) (fun _ => f) t X 0 v =
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) r n t X z l) v := by
  have hD2 := P.D_ge
  by_cases hr : r = 0
  · subst hr
    simp only [gluedMeanFluxCoeff, ite_true]
    exact congrFun (diag_cellMean_liftFluxX_eq' P sX sZ (by omega) (by omega) Cc hseq n hn f
      hf l t ht X 0) v
  · simp only [gluedMeanFluxCoeff, hr, ite_false]
    exact cellMean_liftFluxX_eq' P sX sZ hX hZ Cc hseq r (Nat.pos_of_ne_zero hr) hrH n hn hnR
      f hf l t ht X 0 v

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Residual.CoarseDefect
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The flux sum at a cascade frame** (cascade side of the bill residual).

`frameReconFluxSumAt_of_factor`: `FrameReconFluxSumAt F law kc cr σ₀ Lc θ₁ θ₂ Ain Cfl Cfs` from
`C_fs ≥ max(1, c_r⁻¹)^{k_c}·C_fl`. It is the terminal `reconFluxSum_at` at a frame: Minkowski in
`L²(I)` over the three mass clauses (`covTrunc_fluxMassLe_sub`, twice), then the change of radius
`rhoEnh D c_r m = c_r·fRho → fRho` (`fluxMassLe_scale` with `s = c_r⁻¹`, factor
`radiusChangeFactor c_r⁻¹ k_c`), then the lower integral form (`fluxSum_lintegral`). The clauses are
passed through the three named definitions and never restated.

For `A_in = 0` all masses are `0`; for `c_r = 1` there is no change of radius (factor `1`); a
stage without components is allowed. -/

section S184FluxSum

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

/-- The time integrand of a mass bound is integrable (the square of an `L²` function). -/
theorem massNormSq_integrableOn {ι : Type} [Fintype ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (k : ℕ) (ν ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ)
    (Y : ℝ) (G : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hG : FluxMassLe (K := fun _ => k) ν ρ π I G Y) :
    IntegrableOn (fun s => massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => k) ρ π (fun v => (G v s).val)) I := by
  have hmem := covTrunc_mass_memLp k ν ρ π I Y G hG
  have hint : Integrable (fun s => ‖covTruncMassCLM h k ρ π (fun v => G v s)‖ ^ 2)
      (volume.restrict I) := by
    have hm2 : MemLp (fun s => covTruncMassCLM h k ρ π (fun v => G v s)) ((2 : ℕ) : ENNReal)
        (volume.restrict I) := by simpa using hmem
    simpa using hm2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  refine hint.congr (Filter.Eventually.of_forall fun s => ?_)
  exact (massWeightedCarrierCLM_normSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
    (fun _ => k) ρ π hπ (fun v => G v s))

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The radius of the mass clauses is `c_r` times the slow length. -/
theorem rhoEnh_eq (cr : ℝ) : rhoEnh D cr F.m = cr * fRho F := rfl

/-- The sum of the three mass clauses, in the form of the window (Minkowski, twice). -/
theorem flux_sub {kc : ℕ} {cr σ₀ : ℝ} {Lc : ℕ} {θ₁ θ₂ Ain Cfl : ℝ}
    (hκ : 0 < D.κ (F.m - 1)) (hπ : ∀ v, 0 < F.G.mass law v)
    {F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    (h1 : FrameCovTruncReal F law kc cr Ain Cfl F1)
    (h2 : FrameFrontierReal F law kc cr θ₁ θ₂ Ain Cfl F2)
    (h3 : FrameFilterReal F law kc cr σ₀ Lc Ain Cfl F3) :
    FluxMassLe (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) (K := fun _ => kc)
      (D.κ (F.m - 1)) (rhoEnh D cr F.m) (F.G.mass law) (Set.Icc F.tp F.tf)
      (frameReconFc F F1 F2 F3)
      (Cfl * fTT F cr σ₀ Lc θ₁ θ₂ * Ain) := by
  have h13 := covTrunc_fluxMassLe_sub kc _ _ _ hκ hπ _ _ _ F1 F3 h1.2 h3.2
  have h132 := covTrunc_fluxMassLe_sub kc _ _ _ hκ hπ _ _ _ _ F2 h13 h2.2
  have hsum : Cfl * succCovPrice D F.m cr F.p F.tp F.tf * Ain +
      Cfl * succFilterPrice D F.G F.m cr σ₀ Lc * Ain +
      Cfl * succFrontPrice D F.m F.η₀ F.J F.H θ₁ θ₂ * Ain =
      Cfl * fTT F cr σ₀ Lc θ₁ θ₂ * Ain := by
    simp only [fTT]; ring
  rw [hsum] at h132
  exact h132

/-- The change of radius `ρ ↦ s ρ` for a mass clause, in a form with the length as a parameter. -/
theorem flux_scale {ι : Type} [Fintype ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (k : ℕ) (ν ρ ρ' s : ℝ) (π : ι → ℝ) (hν : 0 < ν) (hs : 0 ≤ s)
    (hρ : s * ρ = ρ') (hπ : ∀ v, 0 < π v) (I : Set ℝ) (Y : ℝ)
    (G : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hG : FluxMassLe (K := fun _ => k) ν ρ π I G Y) :
    FluxMassLe (K := fun _ => k) ν ρ' π I G (radiusChangeFactor s k * Y) := by
  have hint := massNormSq_integrableOn k ν ρ π hπ I Y G hG
  have hsc := fluxMassLe_scale (K := fun _ => k) s hν hs hπ k (fun _ => le_rfl) hint hG
  rw [hρ] at hsc
  exact hsc

/-- A mass clause with a larger bound. -/
theorem flux_mono {ι : Type} [Fintype ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (k : ℕ) (ν ρ : ℝ) (π : ι → ℝ) (I : Set ℝ) (Y Y' : ℝ)
    (G : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (hYY : Y ≤ Y')
    (hG : FluxMassLe (K := fun _ => k) ν ρ π I G Y) :
    FluxMassLe (K := fun _ => k) ν ρ π I G Y' :=
  ⟨hG.1, hG.2.trans hYY⟩

/-- The bound of the change of radius, in the constants of the frame. -/
theorem bound_le {kc : ℕ} {cr σ₀ : ℝ} {Lc : ℕ} {θ₁ θ₂ Ain Cfl Cfs : ℝ}
    (hAt : 0 ≤ Ain * fTT F cr σ₀ Lc θ₁ θ₂) (hCfs : radiusChangeFactor cr⁻¹ kc * Cfl ≤ Cfs) :
    radiusChangeFactor cr⁻¹ kc * (Cfl * fTT F cr σ₀ Lc θ₁ θ₂ * Ain) ≤
      Cfs * Ain * fTT F cr σ₀ Lc θ₁ θ₂ := by
  calc radiusChangeFactor cr⁻¹ kc * (Cfl * fTT F cr σ₀ Lc θ₁ θ₂ * Ain)
      = (radiusChangeFactor cr⁻¹ kc * Cfl) * (Ain * fTT F cr σ₀ Lc θ₁ θ₂) := by ring
    _ ≤ Cfs * (Ain * fTT F cr σ₀ Lc θ₁ θ₂) := mul_le_mul_of_nonneg_right hCfs hAt
    _ = _ := by ring

/-- The mass clause of the coarse flux at the slow length. -/
theorem flux_slow' {kc : ℕ} {cr σ₀ : ℝ} {Lc : ℕ} {θ₁ θ₂ Ain Cfl Cfs : ℝ}
    (hcr : 0 < cr) (hκ : 0 < D.κ (F.m - 1)) (hπ : ∀ v, 0 < F.G.mass law v)
    (hAt : 0 ≤ Ain * fTT F cr σ₀ Lc θ₁ θ₂) (hCfs : radiusChangeFactor cr⁻¹ kc * Cfl ≤ Cfs)
    {F1 F2 F3 : ∀ v : CompIn F.G.comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    (h1 : FrameCovTruncReal F law kc cr Ain Cfl F1)
    (h2 : FrameFrontierReal F law kc cr θ₁ θ₂ Ain Cfl F2)
    (h3 : FrameFilterReal F law kc cr σ₀ Lc Ain Cfl F3) :
    FluxMassLe (ι := CompIn F.G.comps) (h := fun v => hr v.1.root) (K := fun _ => kc)
      (D.κ (F.m - 1)) (fRho F) (F.G.mass law) (Set.Icc F.tp F.tf)
      (frameReconFc F F1 F2 F3) (Cfs * Ain * fTT F cr σ₀ Lc θ₁ θ₂) := by
  have hsub := flux_sub F law hκ hπ h1 h2 h3
  have hρ : cr⁻¹ * rhoEnh D cr F.m = fRho F := by
    rw [rhoEnh_eq, ← mul_assoc, inv_mul_cancel₀ hcr.ne', one_mul]
  have hsc := flux_scale kc _ _ _ cr⁻¹ _ hκ (inv_nonneg.2 hcr.le) hρ hπ _ _ _ hsub
  exact flux_mono kc _ _ _ _ _ _ _ (bound_le F hAt hCfs) hsc

/-- **The flux-sum step at a frame.** -/
theorem frameReconFluxSumAt_of_factor (kc : ℕ) (cr σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ Ain Cfl Cfs : ℝ)
    (hcr : 0 < cr) (hκ : 0 < D.κ (F.m - 1)) (hπ : ∀ v, 0 < F.G.mass law v)
    (hAt : 0 ≤ Ain * fTT F cr σ₀ Lc θ₁ θ₂) (hCfs : radiusChangeFactor cr⁻¹ kc * Cfl ≤ Cfs) :
    FrameReconFluxSumAt F law kc cr σ₀ Lc θ₁ θ₂ Ain Cfl Cfs := by
  intro F1 F2 F3 h1 h2 h3
  have hmass := flux_slow' F law hcr hκ hπ hAt hCfs h1 h2 h3
  have hwin : F.tp + fTobs F = F.tf := by simp [fTobs]
  unfold FrameReconFluxSumBody
  rw [hwin]
  exact ⟨fun v => (hmass.1 v).aestronglyMeasurable,
    fluxSum_lintegral kc _ _ _ hκ hπ _ _ _ hmass⟩

end S184FluxSum

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Coarse
open AVRegularity.CycleComparison.ActualMeans
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Hilbert-valued pulse mean flux in chart form at a native cascade frame. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The chart of the pulse `k` in the form of the menu. -/
abbrev chart''' (k : ℤ) : ℝ → Vec 2 → Vec 2 :=
  fun s' y => D.flowOf (F.m - 1) s' y (D.slotAnchor F.m k)

/-- The label of the pulse `k` in the form of the menu. -/
abbrev label''' (k : ℤ) : ℝ → Vec 2 → Vec 2 :=
  fun s' y => D.flowOf (F.m - 1) (D.slotAnchor F.m k) y s'

/-- The pulse term of the menu's glued mean flux of grade `r` (without its weight). -/
def gluedPulseFlux (r : ℕ) (a : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root) (k : ℤ) (t : ℝ)
    (z : Vec 2) (v : CompIn F.G.comps) : Fin 2 → hr v.1.root :=
  ∑ n ∈ Finset.Icc 2 (F.N + Dm),
    if hk : Odd k then
      pulseMeanFluxEuler (D.cellScaleSq F.m) (liftLength D F.m)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / liftLength D F.m) n r
        (familyLiftData D F.m k (nativeChain F.m k) (liftLength D F.m)
          (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))) (F.CcT k)
        (chart''' F k) (label''' F k) a t z v
    else 0

theorem pulse_PF_eq' (h : GluedIncomingFacts F)
    (Acl ℓ : ℕ) (CGl Cw' : ℕ → ℝ) (Ca Sb Cg : ℝ) (qs qf : ℕ) (par : ℤ → Fin 2)
    (V : ℤ → ℝ → ℝ → ℝ) (bM : CompIn F.G.comps → CompIn F.G.comps → ℝ)
    (hbody : FrameReconSettingBody F law Acl ℓ CGl Cw' Ca Sb Cg qs qf par V bM) (hseq : FrameReconSeqAt F Acl ℓ)
    (r : ℕ) (hrH : r ≤ F.depth) (a : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root)
    (ha : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) {t : ℝ} (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F))
    {k : ℤ} (hk : k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
    (hw : ocCutoff D.α D.q D.Λ F.m k t ≠ 0) (v : CompIn F.G.comps) (y : Vec 2) (j : Fin 2) :
    gluedPulseFlux F r a k t y v j =
      -eulerFlux (D.cellScaleSq F.m) (liftLength D F.m)
        (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / liftLength D F.m) (F.N + Dm)
        (chart''' F k t) (label''' F k t)
        (fun n => meanOf (gluedMeanFluxCoeff (fLiftData F k) (F.CcT k) r n))
        (fun y' => a t (chart''' F k t y')) ((D.cellScaleSq F.m)⁻¹ * t) v y j := by
  classical
  have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
  obtain ⟨hcs, -⟩ := cellScale_facts F h.base h.profile h.band h.upper
  have hmem := glued_window_mem F h k ht hw
  have hwin : t ∈ ocPulseWindow D.α D.q D.Λ F.m k := by
    by_contra hn
    exact hw (WeakEntryProofs.ocCutoff_zero_off_output _ _ _ _
      (Construction.Stream.ocTau_pos h.base) k t hn)
  have hρ0 : liftLength D F.m ≠ 0 := (glued_rho_pos F h).ne'
  have hP := hbody.1 k hk
  have hN := hP.N_ge
  have hsk := hseq k hk
  obtain ⟨Mnat, hnat⟩ := h.natural
  obtain ⟨hη, hag⟩ := seq_agree' F hnat h.level h.length h.base h.profile h.band h.upper h.lower hodd
  have hag' := hag ((D.cellScaleSq F.m)⁻¹ * t) (by rw [mul_inv_cancel_left₀ hcs.ne']; exact hwin)
  have hQ : familyLiftData D F.m k (nativeChain F.m k) (liftLength D F.m)
      (F.G.fam.fiber ⟨k, hodd⟩ (F.G.actual ⟨k, hodd⟩)) = fSeqQ F k hodd := by
    simp only [fSeqQ, h.length, one_mul]
  have hD : Dm ≤ wKlift Dm F.depth F.N Acl ℓ + Dm + 2 := by omega
  have hD' : Dm ≤ max (wLlift Dm F.depth F.N ℓ + 1) (wLlift Dm F.depth F.N ℓ + 2) := by
    have h1 : Dm * 1 * 1 ≤ Dm * (F.depth + 1) * F.N := by gcongr; omega
    refine le_trans ?_ (le_max_right _ _)
    unfold wLlift
    omega
  have h2X : 2 ≤ wKlift Dm F.depth F.N Acl ℓ + Dm + 2 := by omega
  have h2Z : 2 ≤ max (wLlift Dm F.depth F.N ℓ + 1) (wLlift Dm F.depth F.N ℓ + 2) :=
    le_trans (by unfold wLlift; omega) (le_max_right _ _)
  unfold gluedPulseFlux
  simp only [hodd, dite_true]
  rw [Finset.sum_apply, eulerFlux_eq, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_Icc.1 hn
  rw [hQ]
  rw [pulseMeanFluxEuler_eq (fSeqQ F k hodd) (fLiftData F k) hη (F.CcT k) r n hn'.1
    (gluedMeanFluxCoeff (fLiftData F k) (F.CcT k) r n) (D.cellScaleSq F.m) (liftLength D F.m)
    (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / liftLength D F.m) hcs.ne' hρ0
    (chart''' F k) (label''' F k) a t y (ha t)
    (Providers.QuietAtlas.flowOf_contDiff D (F.m - 1) t (D.slotAnchor F.m k)) ?_ ?_ ?_ v j]
  · rfl
  · exact hag'
  · intro l α v' u
    exact Cfl_zero_order' hP _ _ (by omega) (F.CcT k) hsk r hrH n hn'.1 (by omega) l _ hmem
      α _ _ v' u
  · intro l v'
    exact Cfl_hid' hP _ _ hD hD' (F.CcT k) hsk r hrH n hn'.1 (by omega) _
      ((ha t).comp ((Providers.QuietAtlas.flowOf_contDiff D (F.m - 1) t
        (D.slotAnchor F.m k)).comp (contDiff_const_smul (liftLength D F.m)))) l _ hmem _ v'

theorem gluedMeanFlux_eq' (h : GluedIncomingFacts F) (r : ℕ)
    (a : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root) {t : ℝ}
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F)) (z : Vec 2) (v : CompIn F.G.comps) :
    gluedMeanFlux F.G F.m {r} (Finset.Icc 2 (F.N + Dm)) F.CcT a t z v =
      ∑ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
        F.G.actualFamily.weight (oddSlotOf k) t • gluedPulseFlux F r a k t z v := by
  classical
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos h.base
  unfold gluedMeanFlux
  simp only [Finset.sum_singleton]
  have h1 : ∀ k ∈ ocObsPulses D.α D.q D.Λ F.m t t,
      (∑ n ∈ Finset.Icc 2 (F.N + Dm),
        if hk : Odd k then
          ocCutoff D.α D.q D.Λ F.m k t • pulseMeanFluxEuler (D.cellScaleSq F.m)
            (liftLength D F.m)
            (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / liftLength D F.m) n r
            (familyLiftData D F.m k (nativeChain F.m k) (liftLength D F.m)
              (F.G.fam.fiber ⟨k, hk⟩ (F.G.actual ⟨k, hk⟩))) (F.CcT k)
            (chart''' F k) (label''' F k) a t z v
        else 0) =
      ocCutoff D.α D.q D.Λ F.m k t • gluedPulseFlux F r a k t z v := by
    intro k _
    unfold gluedPulseFlux
    by_cases hodd : Odd k
    · simp only [hodd, dite_true, Finset.smul_sum]
    · simp [hodd]
  rw [Finset.sum_congr rfl h1]
  have hsub := obsPulses_time_subset D.α D.q D.Λ F.m hτ ht
  rw [Finset.sum_subset hsub fun k hk hnk => ?_]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [glued_weight_eq F h k (CycleComparison.LiftSetting.obsPulse_odd hk) t]
  · have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
    have hout : t ∉ ocPulseWindow D.α D.q D.Λ F.m k := fun hin =>
      hnk (mem_obsPulses_time D.α D.q D.Λ F.m hτ hodd hin)
    rw [WeakEntryProofs.ocCutoff_zero_off_output D.α D.q D.Λ F.m hτ k t hout, zero_smul]
end

/-! Vanishing grade-zero tail at a native cascade frame. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The grade-zero menu flux has no degrees beyond `N + 1`. -/
theorem gradeZeroTail (h : GluedIncomingFacts F) (Acl ℓ : ℕ)
    (CGl Cw' : ℕ → ℝ) (Ca Sb Cg : ℝ)
    (hseq : FrameReconSeqAt F Acl ℓ)
    (hset : ∃ qs qf par V bM, FrameReconSettingBody F law Acl ℓ CGl Cw' Ca Sb Cg qs qf par V bM)
    (a : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root)
    (ha : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) {t : ℝ}
    (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F)) (z : Vec 2) (v : CompIn F.G.comps) :
    menuGluedMeanFlux F.Mn F.G F.m {0} (Finset.Icc 2 (F.N + Dm)) F.CcT a t z v =
      menuGluedMeanFlux F.Mn F.G F.m {0} (Finset.Icc 2 (F.N + 1)) F.CcT a t z v := by
  classical
  obtain ⟨qs, qf, par, V, bM, hbody⟩ := hset
  obtain ⟨hcs, -⟩ := cellScale_facts F h.base h.profile h.band h.upper
  have hτ : 0 < ocTau D.α D.q D.Λ F.m := Construction.Stream.ocTau_pos h.base
  simp only [menuGluedMeanFlux, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkobs := obsPulses_time_subset D.α D.q D.Λ F.m hτ ht hk
  have hP := hbody.1 k hkobs
  have hD2 := hP.D_ge
  have hN := hP.N_ge
  have hsub : Finset.Icc 2 (F.N + 1) ⊆ Finset.Icc 2 (F.N + Dm) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  refine (Finset.sum_subset hsub fun n hn hnn => ?_).symm
  simp only [Finset.mem_Icc, not_and, not_le] at hn hnn
  have hnA : F.N + 2 ≤ n := by omega
  by_cases hodd : Odd k
  · simp only [hodd, dite_true]
    by_cases hw : ocCutoff D.α D.q D.Λ F.m k t = 0
    · simp only [hw, zero_smul]
    · have hmem := glued_window_mem F h k ht hw
      have hsk := hseq k hkobs
      rw [pulseMeanFluxEuler_zero _ _ _ _ _ _ _ _ _ hsk (by omega)
        (by unfold wLlift; omega) hN _ _ _ hcs.ne' n hnA _ _ _ _ _ ?_ ?_ hmem v]
      · exact smul_zero _
      · exact ha t
      · exact Providers.QuietAtlas.flowOf_contDiff D (F.m - 1) t (D.slotAnchor F.m k)
  · simp only [hodd, dite_false]
end

/-! Hilbert-valued glued mean identity with the full degree range. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The glued mean identity with the full degree range, before the grade-zero tail removal. -/
theorem gluedMeanCore (h : GluedIncomingFacts F) (Acl ℓ : ℕ)
    (CGl Cw' : ℕ → ℝ) (Ca Sb Cg : ℝ)
    (hseq : FrameReconSeqAt F Acl ℓ)
    (hset : ∃ qs qf par V bM, FrameReconSettingBody F law Acl ℓ CGl Cw' Ca Sb Cg qs qf par V bM)
    (r : ℕ) (hrH : r ≤ F.depth) :
    ∀ a : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root,
      (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) → (∀ t, IsZ2Periodic (a t)) →
      ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), ∀ (y : Vec 2) (v : CompIn F.G.comps),
        gluedMean (ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F))
          (fun k => F.G.actualFamily.weight (oddSlotOf k))
          (ocEll D.q D.Λ F.m (D.κ F.m) ^ 2) (fRho F)
          (ocDStar D.q D.Λ F.m (D.κ F.m) (D.κ (F.m - 1)) / fRho F) F.N r
          (fun k => fLiftData F k) F.CcT
          (fun k => ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
            (ocPulseChartIndex D.α D.q D.Λ F.m k))
          (fun k => ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
            (ocPulseChartIndex D.α D.q D.Λ F.m k)) a t y v =
          -divE (fun z => menuGluedMeanFlux F.Mn F.G F.m {r}
            (Finset.Icc 2 (F.N + Dm)) F.CcT a t z v) y := by
  classical
  intro a ha hper t ht y v
  obtain ⟨qs, qf, par, V, bM, hbody⟩ := hset
  obtain ⟨hcs, hc⟩ := cellScale_facts F h.base h.profile h.band h.upper
  have hτ'' : 0 < ocTauPP D.α D.q D.Λ F.m := Construction.Stream.ocTauPP_pos h.base
  have hchart : ∀ k : ℤ, ocChart D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k) = chart''' F k := by
    intro k
    funext s' y
    show _ = D.flowOf (F.m - 1) s' y (D.slotAnchor F.m k)
    unfold ocChart OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex D.α D.q D.Λ F.m k hτ'']
  have hinv : ∀ k : ℤ, ocChartInv D.α D.q D.Λ F.m (D.Φ (F.m - 1)) (D.hΦ (F.m - 1))
      (ocPulseChartIndex D.α D.q D.Λ F.m k) = label''' F k := by
    intro k
    funext s' y
    show _ = D.flowOf (F.m - 1) (D.slotAnchor F.m k) y s'
    unfold ocChartInv OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex D.α D.q D.Λ F.m k hτ'']
  have hrhs : (fun z => menuGluedMeanFlux F.Mn F.G F.m {r}
      (Finset.Icc 2 (F.N + Dm)) F.CcT a t z v) = fun z =>
      ∑ k ∈ ocObsPulses D.α D.q D.Λ F.m F.tp (F.tp + fTobs F),
        F.G.actualFamily.weight (oddSlotOf k) t • gluedPulseFlux F r a k t z v := by
    funext z
    rw [menuGluedMeanFlux_cascade _ h.length]
    exact gluedMeanFlux_eq' F h r a ht z v
  have h2X : 2 ≤ wKlift Dm F.depth F.N Acl ℓ + Dm + 2 := by omega
  have h2Z : 2 ≤ max (wLlift Dm F.depth F.N ℓ + 1) (wLlift Dm F.depth F.N ℓ + 2) :=
    le_trans (by unfold wLlift; omega) (le_max_right _ _)
  rw [hrhs]
  simp only [hchart, hinv, hc]
  refine gluedMean_eq_neg_div _ _ (D.cellScaleSq F.m) (fRho F) _ hcs.ne'
    ((glued_rho_pos F h).ne') F.N r (fun k => fLiftData F k) F.CcT (chart''' F)
    (label''' F) (fun k => fSeqStart F k) (fun k => fSeqEnd F k)
    (fun k r' n => meanOf (gluedMeanFluxCoeff (fLiftData F k) (F.CcT k) r' n)) a t (ha t)
    (fun k t z v => gluedPulseFlux F r a k t z v) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y v
  · intro k hk hne
    refine glued_window_mem F h k ht ?_
    rwa [glued_weight_eq F h k (CycleComparison.LiftSetting.obsPulse_odd hk) t] at hne
  · intro k _ y'
    exact Construction.Preservation.Residual.FluxCancellation.flowOf_inv D (F.m - 1) _ _ y'
  · intro k _ x'
    exact Construction.Preservation.Residual.FluxCancellation.flowOf_inv D (F.m - 1) _ _ x'
  · intro k _ y'
    exact Providers.QuietAtlas.flowOf_det D (F.m - 1) t _ y'
  · intro k _
    exact Providers.QuietAtlas.flowOf_contDiff D (F.m - 1) t _
  · intro k _
    exact (Providers.QuietAtlas.flowOf_contDiff D (F.m - 1) _ t).differentiable (by simp)
  · intro k hk n hn hnM a₀ ha₀ s hs X'
    exact Cfl_pres' (hbody.1 k hk) _ _ h2X h2Z (F.CcT k) (hseq k hk) r hrH n hn hnM a₀ ha₀ s
      hs X'
  · intro k hk n hn hnM d hd hdn α k₀ v' u s hs
    exact Cfl_contDiff' (hbody.1 k hk) _ _ (le_trans (by omega) h2Z) (F.CcT k) (hseq k hk)
      r hrH n hn hnM d hd hdn α k₀ v' u s hs
  · intro k hk hne v' y' j
    refine pulse_PF_eq' F law h Acl ℓ CGl Cw' Ca Sb Cg qs qf par V bM hbody hseq r hrH a ha
      ht hk ?_ v' y' j
    rwa [glued_weight_eq F h k (CycleComparison.LiftSetting.obsPulse_odd hk) t] at hne
end

/-! The native glued mean statement, with all proof ingredients discharged. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

/-- The native glued mean statement `NativeGluedMeanStatement` holds. -/
theorem nativeGluedMeanStatement_proof (Acl ℓ : ℕ) (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ) :
    NativeGluedMeanStatement F law Acl ℓ CGl Cwl Ca Sb Cgr := by
  intro h hseq hset r hrH a ha hper t ht y v
  have hcore := gluedMeanCore F law h Acl ℓ CGl Cwl Ca Sb Cgr hseq hset r
    (by have := Finset.mem_range.1 hrH; omega) a ha hper t ht y v
  by_cases hr0 : r = 0
  · subst r
    simp only [ite_true]
    rw [hcore]
    apply congrArg Neg.neg
    apply congrArg (fun f => divE f y)
    funext z
    exact gradeZeroTail F law h Acl ℓ CGl Cwl Ca Sb Cgr hseq hset a ha ht z v
  · simp only [hr0, ite_false]
    exact hcore
end

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Exact frame reconstruction defect conversion from genuine incoming context facts. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
variable (F : Frame D hr Dm b j₀) (law : BirthLaw)

theorem frameReconDefectConvAt_of_native_glued_mean (Acl kc ℓ : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hf : fNc F kc ≤ F.Naux - 2 * F.p) (cr σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ Ain Cfl : ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ)
    (h : FrameFacts F)
    (hglue : ∀ t ∈ Set.Icc F.tp F.tf, ∀ v,
      CovTruncGluedPeriodicBounded F.Mn F.G F.m F.depth F.CcT t v)
    {kI : InvConsts} {M : ℕ}
    (hcert : F.G'.IsContextCertified kI) (hST : F.G'.IsSlotTransverse)
    (hnat : F.G'.IsNatural M) (hSH : F.G'.IsShiftInvariant)
    (hlev : 1 ≤ F.G'.level) (hj : j₀ ≤ F.G'.level) (hb : 0 < b)
    (hε : 0 < D.eps (F.G'.level - 1)) (hres : ∀ v : CompIn F.G'.comps, 0 ≤ compReserve kI v.1)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφsupp : Function.support F.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (hK : 2 * F.p + Dm ≤ F.Naux)
    (hincoming : GluedIncomingFacts F)
    (hG : NativeGluedMeanStatement F law Acl ℓ CGl Cwl Ca Sb Cgr) :
    FrameReconDefectConvAt F law Acl kc ℓ hW hf cr σ₀ Lc θ₁ θ₂ Ain Cfl CGl Cwl Ca Sb Cgr := by
  have hreg := macroReg F h kc hW hglue
  have hswap : MacroSwapStatement F law Acl kc ℓ hW CGl Cwl Ca Sb Cgr := by
    intro hseq hset aC B₀C lamC AD CE Aedge Cstar Θc hlet
    exact swap_of_divergence F law kc hW aC B₀C lamC AD CE Aedge Cstar Θc hlet hreg
      (macroDiv F law h kc hW aC B₀C lamC AD CE Aedge Cstar Θc hlet (hG hincoming hseq hset))
  have hRs := readoutSmooth_of_certificate F hcert hST hnat hSH hlev hj hb hε hres hφs hφsupp hK
  exact frameReconDefectConvAt_of_ingredients F law Acl kc ℓ hW hf cr σ₀ Lc θ₁ θ₂ Ain Cfl
    CGl Cwl Ca Sb Cgr hswap (meanFlux_of_readoutSmooth F kc hRs)


/-- The reconstruction defect with genuine incoming and outgoing frame facts as named hypotheses. -/
theorem frameReconDefectConvAt (Acl kc ℓ : ℕ)
    (hW : kc + 1 + (F.N + Dm) ≤ F.Naux - 2 * F.p)
    (hf : fNc F kc ≤ F.Naux - 2 * F.p) (cr σ₀ : ℝ) (Lc : ℕ) (θ₁ θ₂ Ain Cfl : ℝ)
    (CGl Cwl : ℕ → ℝ) (Ca Sb Cgr : ℝ)
    (h : FrameFacts F)
    (hglue : ∀ t ∈ Set.Icc F.tp F.tf, ∀ v,
      CovTruncGluedPeriodicBounded F.Mn F.G F.m F.depth F.CcT t v)
    {kI : InvConsts} {M : ℕ}
    (hcert : F.G'.IsContextCertified kI) (hST : F.G'.IsSlotTransverse)
    (hnat : F.G'.IsNatural M) (hSH : F.G'.IsShiftInvariant)
    (hlev : 1 ≤ F.G'.level) (hj : j₀ ≤ F.G'.level) (hb : 0 < b)
    (hε : 0 < D.eps (F.G'.level - 1)) (hres : ∀ v : CompIn F.G'.comps, 0 ≤ compReserve kI v.1)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) F.φ₀)
    (hφsupp : Function.support F.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (hK : 2 * F.p + Dm ≤ F.Naux)
    {Mnat : ℕ} (hinat : F.G.IsNatural Mnat) (hilevel : F.G.level = F.m)
    (hlength : F.Mn.lenFactor = 1) (hmlower : 1 ≤ F.m) (hmupper : F.m ≤ D.term) :
    FrameReconDefectConvAt F law Acl kc ℓ hW hf cr σ₀ Lc θ₁ θ₂ Ain Cfl CGl Cwl Ca Sb Cgr := by
  have hincoming : GluedIncomingFacts F :=
    ⟨⟨Mnat, hinat⟩, hilevel, hlength, hmlower, hmupper, h.base, h.profile, h.band⟩
  exact frameReconDefectConvAt_of_native_glued_mean F law Acl kc ℓ hW hf cr σ₀ Lc
    θ₁ θ₂ Ain Cfl CGl Cwl Ca Sb Cgr h hglue hcert hST hnat hSH hlev hj hb hε hres
    hφs hφsupp hK hincoming (nativeGluedMeanStatement_proof F law Acl ℓ CGl Cwl Ca Sb Cgr)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
