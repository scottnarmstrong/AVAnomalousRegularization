-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Residual.Presentation.Cascade.PointwiseEnvelope
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.Seed.SeedLedgerDecayConversion
public import AVRegularity.Construction.StageEnvelopes.Assembly
public import AVRegularity.Construction.Preservation.CommonPreparation.CopyJointConst
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual-context neutral family inherits the original inner-carrier
envelopes at every positive copied mass. Each copy uses its own output slot.
For descendants, the shared context estimate may be requested at arbitrary
finite orders: changing its four order caps changes neither the certificate
nor the reserve, so no bound by the old stored Ks is needed. The seed instead
uses its supplied molecular envelope with the requested reserve.

Empty or singleton families, H=0, edgeless seeds and empty windows use the same family and
radius. The seed
radius is never inferred from record lengths. No separate mass-dependent
family, kernel, evolution or model is chosen. -/

open StageEnvelopes Residual.Presentation.Cascade

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Only the four requested derivative caps change; the actual certificate
and every reserve, radius and coefficient constant are retained. -/
def preparationEnvelopeOrders (k : InvConsts) (Ks Kan Lan Jm : ℕ) : InvConsts :=
  { k with Ks := Ks, Kan := Kan, Lan := Lan, Jm := Jm }

/-- The three envelopes needed by the joint preparation and the actual copied-row
solver, for one fixed family and every positive copied mass. -/
def NativeCopyEnvelopesStatement (G : GenStage D hr Dm bw j₀)
    (k : InvConsts) (W : Set ℝ) (ρ : ℝ) (H : ℕ)
    (K : CompIn G.comps × Fin (H + 1) → ℕ) : Prop :=
  ∀ (πc : CompIn G.comps × Fin (H + 1) → ℝ), (∀ v, 0 < πc v) →
  let C := preparationNeutralChain G.actualFamily H
  let B := fun v u => Real.sqrt (πc u / πc v) *
    preparationNeutralMajorant (recordMajorant (fun _ => 1) G.fam) H v u
  IsAnalyticEnvelope C πc (ChartedFamily.Domain.onWindow C W)
      (D.eps (G.level - 1)) k.Ca k.Kan k.Lan B ∧
    IsMolecularEnvelope C πc K (ChartedFamily.Domain.onWindow C W)
      (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ρ k.Cm k.Jm B ∧
    IsPointwiseMolecularEnvelope C πc K (ChartedFamily.Domain.onWindow C W)
      (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ρ k.Cm k.Jm B

private theorem preparation_native_majorant_normalize
    (G : GenStage D hr Dm bw j₀) (π : CompIn G.comps → ℝ) :
    recordMajorant π G.fam = fun v u => Real.sqrt (π u / π v) *
      recordMajorant (fun _ => 1) G.fam v u := by
  funext v u
  simp only [recordMajorant, div_self one_ne_zero, Real.sqrt_one, one_mul]

/-- Transport the supplied seed envelopes or the produced descendant
envelopes to native actual contexts, then to all descending copies and masses. -/
theorem native_copy_envelopes_of_inner (G : GenStage D hr Dm bw j₀) (law : BirthLaw)
    (k : InvConsts) {W W' : Set ℝ} (hW : W ⊆ W') (ρ : ℝ) (H : ℕ)
    (K : CompIn G.comps × Fin (H + 1) → ℕ)
    (hπ : ∀ v, 0 < G.mass law v)
    (hact : ∀ p, (G.actual p).1 = nativeChain G.level p.1)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (ha : IsAnalyticEnvelope G.fam (G.mass law) (G.innerDomain W' k.mEnv)
      (D.eps (G.level - 1)) k.Ca k.Kan k.Lan (recordMajorant (G.mass law) G.fam))
    (hm : ∀ l, IsMolecularEnvelope G.fam (G.mass law) (fun v => K (v, l))
      (G.innerDomain W' k.mEnv) (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
      ρ k.Cm k.Jm (recordMajorant (G.mass law) G.fam))
    (hp : ∀ l, IsPointwiseMolecularEnvelope G.fam (G.mass law) (fun v => K (v, l))
      (G.innerDomain W' k.mEnv) (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))
      ρ k.Cm k.Jm (recordMajorant (G.mass law) G.fam)) :
    NativeCopyEnvelopesStatement G k W ρ H K := by
  intro πc hπc
  have ha' := G.isAnalyticEnvelope_actualFamily hW k.mEnv hact hi hj ha
  have hm' := fun l => G.isMolecularEnvelope_actualFamily hW k.mEnv hact hi hj (hm l)
  have hp' := fun l => G.isPointwiseMolecularEnvelope_actualFamily hW k.mEnv hact hi hj (hp l)
  rw [preparation_native_majorant_normalize G (G.mass law)] at ha' hm' hp'
  exact ⟨preparation_neutral_analytic G.actualFamily H W (G.mass law) hπ πc hπc
      _ _ _ _ _ ha',
    preparation_neutral_molecular G.actualFamily H W (G.mass law) hπ πc hπc
      K _ _ _ ρ _ _ _ hm',
    preparation_neutral_pointwise G.actualFamily H W (G.mass law) hπ πc hπc
      K _ _ _ ρ _ _ _ hp'⟩

/-- The shared context estimate produces all copied envelopes at the
requested finite orders, with no inequality against the old stored caps. -/
theorem native_copy_envelopes_of_context (p : ContextEnvelopeParameters)
    (Ks Kan Lan Jm : ℕ)
    (est : ContextEnvelopeEstimate { p with Ks := Ks, Kan := Kan, Lan := Lan, Jm := Jm })
    (G : GenStage D hr Dm bw j₀) (law : BirthLaw) (k : InvConsts)
    {W W' : Set ℝ} (hW : W ⊆ W') (ρ : ℝ) (H : ℕ)
    (K : CompIn G.comps × Fin (H + 1) → ℕ) (hK : ∀ v, K v ≤ Ks)
    (hinput : ContextEnvelopeInput p G k k.mEnv ρ)
    (hlevel : est.levelFloor ≤ G.level) (hCa : est.Ca ≤ k.Ca)
    (hCm : ∀ j, est.Cm j ≤ k.Cm j) :
    NativeCopyEnvelopesStatement G (preparationEnvelopeOrders k Ks Kan Lan Jm) W ρ H K := by
  let k' := preparationEnvelopeOrders k Ks Kan Lan Jm
  have hinput' : ContextEnvelopeInput
      { p with Ks := Ks, Kan := Kan, Lan := Lan, Jm := Jm } G k' k.mEnv ρ :=
    { hinput with
      slot_order := le_rfl
      slow_order := le_rfl
      fast_order := le_rfl
      molecular_order := le_rfl }
  have hs := est.bound hr D Dm j₀ bw G k' k.mEnv ρ hinput' hlevel hCa hCm law W'
    (fun _ => 1) (fun _ => zero_lt_one)
  dsimp only at hs
  rw [markerConj_one' G.fam] at hs
  simp only [div_self one_ne_zero, one_mul] at hs
  let l₀ : Fin (H + 1) := ⟨0, Nat.zero_lt_succ H⟩
  have hslots (l : Fin (H + 1)) (v : CompIn G.comps) : K (v, l) ≤ k'.Ks := hK (v, l)
  obtain ⟨M, hnat⟩ := hinput.natural
  exact native_copy_envelopes_of_inner G law k' hW ρ H K
    (fun v => Buffer.birth_compMass_pos hinput.q_pos hinput.large law v.1)
    hnat.2.2.1 hinput.level_pos hinput.carrier_start
    (hs _ (hslots l₀)).1 (fun l => (hs _ (hslots l)).2.1)
    (fun l => (hs _ (hslots l)).2.2.2)

/-- At the seed the invariant's ordinary envelope and the separately
supplied pointwise envelope are used at their original radius. -/
theorem native_copy_envelopes_of_supplied
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    (G : GenStage D hr Dm bw j₀) (law : BirthLaw) (k : InvConsts)
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (M : ℕ) (a b S θ : ℝ)
    (hinv : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k a b S θ G)
    (hpw : IsSeedPointwiseMolecular law k G a b)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    {W : Set ℝ} (hW : W ⊆ Set.Icc a b) (H : ℕ)
    (K : CompIn G.comps × Fin (H + 1) → ℕ) (hK : ∀ v, K v ≤ k.Ks) :
    NativeCopyEnvelopesStatement G k W (rhoStar D k.c₀ G.level) H K := by
  let l₀ : Fin (H + 1) := ⟨0, Nat.zero_lt_succ H⟩
  have he := hinv.2.2.2.2.2.2.1
  exact native_copy_envelopes_of_inner G law k hW _ H K
    (fun v => Buffer.birth_compMass_pos hq hΛ law v.1) hinv.1.2.2.1 hi hj
    (he _ (fun v => hK (v, l₀))).1.analytic
    (fun l => (he _ (fun v => hK (v, l))).1.molecular)
    (fun l => hpw _ (fun v => hK (v, l)))

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Put the incoming ordinary and marked ledger budgets into the SAME
copied envelopes supplied by the original-stage producer. The copied
majorant is fixed before the mass; only its mass normalization changes.
The degenerate cases are included: empty and singleton families, H=0, Dm=2, smallest orders,
constants, identity geometry, edgeless seeds and empty windows retain the same statement.
No new Cauchy estimate, envelope constant, model or family is selected. -/

/-- Both physical masses of the same incoming stage satisfy the full
copied envelope and the pointwise envelope, at the original ledger budget. -/
def NativeCopiedWeightedEnvelopeStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Mnat : ℕ) (k kenv : InvConsts)
    (tA tf S θK : ℝ) (G : GenStage D hr Dm bw j₀),
    IsStageInvariant law P seedK freshK φ₀ hφ₀ Mnat k tA tf S θK G →
    1 < D.q → 128 ≤ D.Λ →
    ∀ (W : Set ℝ) (ρ : ℝ) (H : ℕ) (K : CompIn G.comps × Fin (H + 1) → ℕ),
    NativeCopyEnvelopesStatement G kenv W ρ H K →
    ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
      let C := preparationNeutralChain G.actualFamily H
      let πc := fun v : CompIn G.comps × Fin (H + 1) => G.mass law v.1 / w v.1 ^ 2
      let A := preparationNeutralMajorant (recordMajorant (fun _ => 1) G.fam) H
      (∀ v, 0 < πc v) ∧
      IsEnvelope C πc K (ChartedFamily.Domain.onWindow C W)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ρ
        (fun v u => Real.sqrt (πc u / πc v) * A v u)
        S kenv.Ca kenv.Kan kenv.Lan kenv.Cm kenv.Jm ∧
      IsPointwiseMolecularEnvelope C πc K (ChartedFamily.Domain.onWindow C W)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ρ kenv.Cm kenv.Jm
        (fun v u => Real.sqrt (πc u / πc v) * A v u)

/-! The ordinary and marked ledger budgets of the incoming stage supply
the full envelope of its same neutral copies. The copied majorant and all
coefficient estimates are retained; only the effective mass is normalized. -/

/-- Both physical masses inherit the original ledger budget on the same
copied family, together with its supplied pointwise molecular envelope. -/
theorem native_copied_weighted_envelope : NativeCopiedWeightedEnvelopeStatement := by
  intro hr _ _ _ _ _ _ D Dm bw j₀ law P seedK freshK φ₀ hφ₀ Mnat k kenv
    tA tf S θK G hinv hq hΛ W ρ H K hcopy w hchoice
  have hmass (v : CompIn G.comps) : 0 < G.mass law v :=
    Buffer.birth_compMass_pos hq hΛ law v.1
  have hw (v : CompIn G.comps) : 0 < w v := by
    rcases hchoice with rfl | rfl
    · exact zero_lt_one
    · exact Buffer.birth_compMarker_pos hq hΛ law v.1
  let π := fun v : CompIn G.comps => G.mass law v / w v ^ 2
  let πc := fun v : CompIn G.comps × Fin (H + 1) => π v.1
  have hπ (v : CompIn G.comps) : 0 < π v := div_pos (hmass v) (pow_pos (hw v) 2)
  have hπc (v : CompIn G.comps × Fin (H + 1)) : 0 < πc v := hπ v.1
  obtain ⟨hn, hr, hc, hmr, hmc⟩ := FullLift.stage_record_schur_bounds hinv
  have hweighted :
      (∀ v, ∑ u, w v / w u * recordMajorant (G.mass law) G.fam v u ≤ S) ∧
      (∀ u, ∑ v, w v / w u * recordMajorant (G.mass law) G.fam v u ≤ S) := by
    rcases hchoice with rfl | rfl
    · simpa only [div_self one_ne_zero, one_mul] using And.intro hr hc
    · exact ⟨hmr, hmc⟩
  have hsum := FullLift.recordMajorant_effective_mass_schur G.fam (G.mass law)
    w hmass hw S hweighted.1 hweighted.2
  have hnonneg (v u : CompIn G.comps) : 0 ≤ recordMajorant π G.fam v u := by
    rw [FullLift.recordMajorant_effective_mass G.fam (G.mass law) w hmass hw v u]
    exact mul_nonneg (div_pos (hw v) (hw u)).le (hn v u)
  have hs := preparation_neutral_majorant_budgets (recordMajorant π G.fam)
    hnonneg S hsum.1 hsum.2 H
  have hb (v u : CompIn G.comps × Fin (H + 1)) :
      Real.sqrt (πc u / πc v) *
          preparationNeutralMajorant (recordMajorant (fun _ => 1) G.fam) H v u =
        preparationNeutralMajorant (recordMajorant π G.fam) H v u := by
    dsimp only [preparationNeutralMajorant, πc]
    split
    · simp only [recordMajorant, div_self one_ne_zero, Real.sqrt_one, one_mul]
    · exact mul_zero _
  have he := hcopy πc hπc
  dsimp only at he ⊢
  refine ⟨hπc, ⟨?_, ?_, ?_, he.1, he.2.1⟩, he.2.2⟩
  · intro v u
    rw [hb]
    dsimp only [preparationNeutralMajorant]
    split
    · exact hnonneg v.1 u.1
    · exact le_rfl
  · intro v
    exact (Finset.sum_le_sum (fun u _ => (hb v u).le)).trans (hs.1 v)
  · intro u
    exact (Finset.sum_le_sum (fun v _ => (hb v u).le)).trans (hs.2 u)

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **Copied envelopes: monotonicity, the seed case and the cascade cases** (the
original-stage envelope join `OriginalStageEnvelopeJoinStatement`).

* `nativeCopyEnvelopes_mono`: `NativeCopyEnvelopesStatement` at larger analytic and
  molecular constants and smaller slow, fast and molecular orders (the copied majorant is
  nonnegative, `copyMajorant_nonneg`).
* `seedCopyEnvelopes`: at the seed, the envelopes at the requested orders
  `preparationEnvelopeOrders k_I …` from the seed invariant and the supplied pointwise
  envelope at `k_S` (`native_copy_envelopes_of_supplied`), when the requested orders are at most
  those of `k_S`, `k_S.C_a ≤ k_I.C_a`, `k_S.C_m ≤ k_I.C_m` and `k_I.c₀ = k_S.c₀`.
* `cascade_lt_or_eq`: a cascade stage of positive level is the seed or has a level below it;
  `cascade_grade_le`: the components of a cascade stage below the seed have grade at most the
  menu's `H` (they are retained).

For equal constants and orders the comparison is the identity; an empty family and the seed
itself are allowed. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The majorant of the copied family is nonnegative. -/
theorem copyMajorant_nonneg (G : GenStage D hr Dm bw j₀) (H : ℕ)
    (πc : CompIn G.comps × Fin (H + 1) → ℝ) (v u : CompIn G.comps × Fin (H + 1)) :
    0 ≤ Real.sqrt (πc u / πc v) *
      preparationNeutralMajorant (recordMajorant (fun _ => 1) G.fam) H v u := by
  refine mul_nonneg (Real.sqrt_nonneg _) ?_
  unfold preparationNeutralMajorant recordMajorant
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun γ _ =>
      mul_nonneg (norm_nonneg _) (G.fam.identity _ _ γ).record.size_nonneg)
  · exact le_rfl

/-- The pointwise molecular envelope at a larger constant and a smaller molecular order. -/
theorem pointwiseMolecularEnvelope_mono' {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dd : ℕ} {P : Type*}
    {Ctx : P → Type*} (F : ChartedFamily ι h Dd P Ctx) (π : ι → ℝ) (K : ι → ℕ)
    (dom : F.Domain) (ν e E ρ : ℝ) (hE : 0 ≤ E) {C C' : ℕ → ℝ} {J J' : ℕ} (hJ : J ≤ J')
    (hC : ∀ j, C j ≤ C' j) {b : ι → ι → ℝ} (hb : ∀ v u, 0 ≤ b v u)
    (hM : IsPointwiseMolecularEnvelope F π K dom ν e E ρ C J' b) :
    IsPointwiseMolecularEnvelope F π K dom ν e E ρ C' J b := by
  refine ⟨Seed.smoothOn_domain_order_mono F (fun _ _ => le_rfl)
    (fun _ => Nat.add_le_add_left hJ _) hM.1, fun v u j hj => ?_⟩
  exact (hM.2 v u j (hj.trans hJ)).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC j)
      (inv_nonneg.mpr (pow_nonneg hE _))) (hb v u)))

/-- **The copied envelopes at larger constants and smaller orders.** -/
theorem nativeCopyEnvelopes_mono (G : GenStage D hr Dm bw j₀) {k k' : InvConsts}
    {W : Set ℝ} {ρ : ℝ} {H : ℕ} {K : CompIn G.comps × Fin (H + 1) → ℕ}
    (hE : 0 ≤ D.eps (G.level - 1)) (hCa : k.Ca ≤ k'.Ca) (hKan : k'.Kan ≤ k.Kan)
    (hLan : k'.Lan ≤ k.Lan) (hCm : ∀ j, k.Cm j ≤ k'.Cm j) (hJm : k'.Jm ≤ k.Jm)
    (h : NativeCopyEnvelopesStatement G k W ρ H K) :
    NativeCopyEnvelopesStatement G k' W ρ H K := by
  intro πc hπc
  have h' := h πc hπc
  dsimp only at h' ⊢
  obtain ⟨ha, hm, hp⟩ := h'
  have hb := copyMajorant_nonneg G H πc
  exact ⟨Seed.analyticEnvelope_mono _ _ (fun _ _ => subset_rfl) _ _ _ hKan hLan _ hb hCa ha,
    Seed.molecularEnvelope_mono _ _ _ (fun _ _ => subset_rfl) _ _ _ _ hE _ _ hJm hCm _ hb hm,
    pointwiseMolecularEnvelope_mono' _ _ _ _ _ _ _ _ hE hJm hCm hb hp⟩

/-- **The seed case**: the copied envelopes of the seed at the requested orders and the constants
of `k_I`, from its invariant and its supplied pointwise envelope at `k_S`. -/
theorem seedCopyEnvelopes [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    (G seed : GenStage D hr Dm bw j₀) (hGS : G = seed) (law : BirthLaw) (kS kI : InvConsts)
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (M : ℕ) (tS tf S θ : ℝ) (hinv : IsStageInvariant law P seedK freshK φ₀ hφ₀ M kS tS tf S θ seed)
    (hpw : IsSeedPointwiseMolecular law kS seed tS tf) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hi : 1 ≤ seed.level) (hj : j₀ ≤ seed.level) {W : Set ℝ} (hW : W ⊆ Set.Icc tS tf) (H : ℕ)
    (K : CompIn G.comps × Fin (H + 1) → ℕ) {Ks Kan Lan Jm : ℕ} (hK : ∀ v, K v ≤ Ks)
    (hKs : Ks ≤ kS.Ks) (hKan : Kan ≤ kS.Kan) (hLan : Lan ≤ kS.Lan) (hJm : Jm ≤ kS.Jm)
    (hCa : kS.Ca ≤ kI.Ca) (hCm : ∀ j, kS.Cm j ≤ kI.Cm j) (hc : kI.c₀ = kS.c₀) :
    NativeCopyEnvelopesStatement G (preparationEnvelopeOrders kI Ks Kan Lan Jm) W
      (rhoStar D kI.c₀ G.level) H K := by
  subst hGS
  rw [hc]
  have hE : 0 ≤ D.eps (G.level - 1) := by
    unfold OCData.eps
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  exact nativeCopyEnvelopes_mono G hE hCa hKan hLan hCm hJm
    (native_copy_envelopes_of_supplied G law kS P seedK freshK φ₀ hφ₀ M tS tf S θ hinv hpw hq hΛ
      hi hj hW H K (fun v => (hK v).trans hKs))

/-- A cascade stage of positive level is the seed or lies strictly below it. -/
theorem cascade_lt_or_eq {P : ProvParams} {Mn : SuccMenu} {seed G : GenStage D hr Dm bw j₀}
    (h : IsCascadeStage D P Mn seed G) (h1 : 1 ≤ G.level) : G.level < seed.level ∨ G = seed := by
  cases h with
  | seed => exact Or.inr rfl
  | @step G₁ G₁' hc ha =>
    left
    have hl : G₁'.level = G₁.level - 1 := ha.2.1
    have hle := Providers.CascadeInvariants.level_le_of_cascade hc
    change G₁'.level < seed.level
    change 1 ≤ G₁'.level at h1
    omega

/-- The components of a cascade stage strictly below the seed are retained: grade at most `H`. -/
theorem cascade_grade_le {P : ProvParams} {Mn : SuccMenu} {seed G : GenStage D hr Dm bw j₀}
    (h : IsCascadeStage D P Mn seed G) (hlt : G.level < seed.level) (v : CompIn G.comps) :
    compGrade v.1 ≤ Mn.H := by
  cases h with
  | seed => exact absurd hlt (lt_irrefl _)
  | step _ _ => exact (Finset.mem_filter.mp v.2).2.1

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-- Head-class cache: the normed group of the periodic Sobolev carrier. -/
local instance incomingRadiiTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
/-- Head-class cache: the inner product space of the periodic Sobolev carrier. -/
local instance incomingRadiiTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
/-- Head-class cache: the normed space of the periodic Sobolev carrier. -/
local instance incomingRadiiTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

end AVRegularity.Construction.Preservation.CommonPreparation
end

attribute [local instance] AVRegularity.Construction.Preservation.CommonPreparation.incomingRadiiTorusNormed
  AVRegularity.Construction.Preservation.CommonPreparation.incomingRadiiTorusInner
  AVRegularity.Construction.Preservation.CommonPreparation.incomingRadiiTorusSpace

section
/-! The readout bounds for ONE mass of the copied family, from the joint-preparation clauses of the
chain and a bound of the buffered datum. The buffered datum `B f` of an original
datum `f` is placed in copy zero by `preparationNeutralInitial`; its factorial norm at the
incoming radius is bounded by `Cbuf` times a size `N` of `f`. Nothing is divided by `N`.

The degenerate cases are included: `H = 0` (one copy, no edges), an empty component type, zero
datum (`N = 0` forces both sides zero) and `D = 2` use the same formulas. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation
namespace CopyJoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {H : ℕ}

/-- The chain bound of a buffered datum: its norm in copy zero, zero in the new copies. -/
def chainBound (F : ι → ℝ) (v : ι × Fin (H + 1)) : ℝ := if v.2 = 0 then F v.1 else 0

omit [DecidableEq ι] [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem sum_chainBound (π : ι → ℝ) (F : ι → ℝ) :
    ∑ v : ι × Fin (H + 1), (π v.1)⁻¹ * chainBound F v ^ 2 = ∑ i, (π i)⁻¹ * F i ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [chainBound]
  rw [Finset.sum_eq_single (0 : Fin (H + 1))]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The datum of the chain is bounded in copy zero by the buffered bound, and is zero elsewhere. -/
theorem initial_norm_le (K : ι × Fin (H + 1) → ℕ) (ρold : ℝ) (B : ∀ i, TorusHk (K (i, 0)) (h i))
    (v : ι × Fin (H + 1)) :
    torusHkNorm ρold (le_refl (K v)) (preparationNeutralInitial H K B v) ≤
      chainBound (fun i => torusHkNorm ρold (le_refl (K (i, 0))) (B i)) v := by
  obtain ⟨j, l⟩ := v
  by_cases hl : l = 0
  · subst hl
    simp only [chainBound, ite_true]
    rw [preparation_neutral_initial_zero_copy]
  · simp only [chainBound, hl, ite_false]
    rw [preparation_neutral_initial_positive_copy H K B (j, l) hl]
    exact (CycleComparison.Reconstruction.torusHkNorm_zero (E := h j) ρold (le_refl _)).le

variable {D : ℕ} {Part : Type*} {Ctx : Part → Type*}

/-- **Readout bounds for one mass.** From the joint model and error clauses of the copied chain
(one witness `Pd, Pg`), a bound `Cbuf * N` of the buffered datum at the incoming radius and the
chain solution with that datum, the readout approximates the plain readout in `L²` and has a
bounded enhanced jet norm. -/
theorem copy_readout_bounds (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι × Fin (H + 1) → ℕ)
    (Mout : ℕ) (ν tS tp ρs ρold E Pacc CP ρ ρm C S Cbuf N Θ : ℝ) (b : ℝ → Vec 2 → Vec 2)
    (Fch : ChartedFamily (ι × Fin (H + 1)) (fun v => h v.1) D Part Ctx)
    (A' : Matrix (ι × Fin (H + 1)) (ι × Fin (H + 1)) ℝ) (hA : ∀ v u, 0 ≤ A' v u)
    (Ac : ∀ (i i' : ι × Fin (H + 1)) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i'.1)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i.1)))
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1),
      TorusHk 0 (h u.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (hjm : IsJointModel (h := fun v : ι × Fin (H + 1) => h v.1) (fun v => π v.1) K Mout H Fch A'
      Θ E Pacc ρm C CP Pd Pg)
    (hjerr : IsJointError (h := fun v : ι × Fin (H + 1) => h v.1) (fun v => π v.1) K Mout H D
      ν tS tp ρs ρold E Pacc CP b Ac Pd Pg)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u.1 / π v.1) * A' v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u.1 / π v.1) * A' v u ≤ S) (hS : 0 ≤ S)
    (hρ : 0 < ρ) (hρm : 0 < ρm) (hCPE : 0 ≤ CP * E ^ Pacc)
    (B : ∀ i, TorusHk (K (i, 0)) (h i))
    (hbuf : Real.sqrt (∑ i, (π i)⁻¹ * torusHkNorm ρold (le_refl (K (i, 0))) (B i) ^ 2) ≤
      Cbuf * N)
    (u : ∀ v : ι × Fin (H + 1), ℝ → TorusHk (K v) (h v.1))
    (w : ∀ v : ι × Fin (H + 1), ℝ → TorusHk (K v + 1) (h v.1))
    (hsol : IsCoupledWeakSolutionTorus ν tS tp b D K Ac (preparationNeutralInitial H K B)
      (fun _ _ => 0) (fun _ _ => 0) u w) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun i =>
      (truncateTorusHk (Nat.zero_le Mout)
        (readout K Mout Pd Pg (fun v => truncateTorusHk (Nat.zero_le _)
          (preparationNeutralInitial H K B v)) i) - plainReadout K u tp i).val)) ≤
      ((H : ℝ) + 1) * (CP * E ^ Pacc * (Cbuf * N)) ∧
    Real.sqrt (massNormSq (E := h) (K := fun _ => Mout) ρ π (fun i =>
      (readout K Mout Pd Pg (fun v => truncateTorusHk (Nat.zero_le _)
        (preparationNeutralInitial H K B v)) i).val)) ≤
      ((H : ℝ) + 1) * (CycleComparison.Reconstruction.jointModelConst C S H Mout (ρ / ρm) *
        (Cbuf * N)) := by
  have hF := sum_chainBound (H := H) π (fun i => torusHkNorm ρold (le_refl (K (i, 0))) (B i))
  have hbound : Real.sqrt (∑ v : ι × Fin (H + 1), (π v.1)⁻¹ *
      chainBound (fun i => torusHkNorm ρold (le_refl (K (i, 0))) (B i)) v ^ 2) ≤ Cbuf * N := by
    rw [hF]
    exact hbuf
  have hf := initial_norm_le (h := h) K ρold B
  have hH : (0 : ℝ) ≤ (H : ℝ) + 1 := by positivity
  refine ⟨?_, ?_⟩
  · refine (readout_error_le π hπ K Mout D ν tS tp ρs ρold E Pacc CP b Ac Pd Pg hjerr
      (preparationNeutralInitial H K B) _ hf u w hsol).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound hCPE) hH
  · refine (readout_jet_le π hπ K Mout Fch A' hA Θ E Pacc ρm C CP Pd Pg hjm hrow hcol hS hρ hρm
      (preparationNeutralInitial H K B) _ hf).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound
      (CycleComparison.Reconstruction.jointModelConst_nonneg C hS H Mout _)) hH

end CopyJoint
end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! The generic copied-family readout theorem in the vocabulary of `NeutralChainModelStatement`.
The family of components is `CompIn F.G.comps`; the chain is its copy family. The
inputs are exactly: one witness `Pd, Pg` of the joint preparation for the chain, for both masses
`mass/w²` (`w = 1` and `w = marker`); the buffered datum map `B`; the identification of the
model map and the plain trace with the readouts; the bound of the buffered datum. All
constants are fixed before the datum.

The degenerate cases are included: depth zero (`H = 0`), an empty family, a single component
and `D = 2` use the same formulas. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation
namespace CopyJoint

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The order-zero datum of the chain: the buffered datum in copy zero, zero in the new copies. -/
def datum {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {H : ℕ} (K : ι × Fin (H + 1) → ℕ)
    (B : ∀ i, TorusHk (K (i, 0)) (h i)) : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) :=
  fun v => truncateTorusHk (Nat.zero_le _) (preparationNeutralInitial H K B v)

/-- The copy data of a request: copy count, slots (the model order `Nout` is the output order),
the buffered datum and the coefficient data of the chain solution. -/
structure ReadoutInput (F : Request hr D Dm bw j₀) (H : ℕ) where
  K : CompIn F.G.comps × Fin (H + 1) → ℕ
  Pd : ∀ v : CompIn F.G.comps × Fin (H + 1), TorusHk 0 (hr v.1.1.root) →ₗ[ℝ]
    TorusHk (max F.Nout (K v)) (hr v.1.1.root)
  Pg : ℕ → ∀ v u : CompIn F.G.comps × Fin (H + 1), TorusHk 0 (hr u.1.1.root) →ₗ[ℝ]
    TorusHk (max F.Nout (K v)) (hr v.1.1.root)
  B : F.Data 0 → ∀ i : CompIn F.G.comps, TorusHk (K (i, 0)) (hr i.1.root)

/-- The shared data of the joint preparation for the chain: the chain family, the coefficients, the
scales and the constants; all fixed before the weight and the datum. -/
structure GateParams (F : Request hr D Dm bw j₀) (H : ℕ) (I : ReadoutInput F H) where
  Part : Type
  Ctx : Part → Type
  Dord : ℕ
  Fch : ChartedFamily (CompIn F.G.comps × Fin (H + 1)) (fun v => hr v.1.1.root) Dord Part Ctx
  A' : Matrix (CompIn F.G.comps × Fin (H + 1)) (CompIn F.G.comps × Fin (H + 1)) ℝ
  Θ : ℝ
  E : ℝ
  ρm : ℝ
  C : ℝ
  CP : ℝ
  ν : ℝ
  tS : ℝ
  ρs : ℝ
  ρold : ℝ
  S : ℝ
  Cbuf : ℝ
  b : ℝ → Vec 2 → Vec 2
  Ac : ∀ (i i' : CompIn F.G.comps × Fin (H + 1)) (d : admissibleOrders I.K Dord i i'), ℝ →
    Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr i'.1.1.root)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => hr i.1.1.root))
  nonneg : ∀ v u, 0 ≤ A' v u
  S_nonneg : 0 ≤ S
  radius_model_pos : 0 < ρm
  error_scale_nonneg : 0 ≤ CP * E ^ F.Q
  scale_eq : E = D.eps (F.G.level - 1)

/-- The clauses of the joint preparation for the chain with the mass `mass/w²` of the weight
`w`. -/
structure WeightGate (F : Request hr D Dm bw j₀) (H : ℕ) (I : ReadoutInput F H)
    (P : GateParams F H I) (w : CompIn F.G.comps → ℝ) (tp : ℝ) : Prop where
  mass_pos : ∀ v, 0 < F.G.mass F.law v / w v ^ 2
  model : IsJointModel (h := fun v : CompIn F.G.comps × Fin (H + 1) => hr v.1.1.root)
    (fun v => F.G.mass F.law v.1 / w v.1 ^ 2) I.K F.Nout H P.Fch P.A' P.Θ P.E F.Q P.ρm P.C P.CP
    I.Pd I.Pg
  error : IsJointError (h := fun v : CompIn F.G.comps × Fin (H + 1) => hr v.1.1.root)
    (fun v => F.G.mass F.law v.1 / w v.1 ^ 2) I.K F.Nout H P.Dord P.ν P.tS tp P.ρs P.ρold P.E
    F.Q P.CP P.b P.Ac I.Pd I.Pg
  row : ∀ v, ∑ u, Real.sqrt ((F.G.mass F.law u.1 / w u.1 ^ 2) / (F.G.mass F.law v.1 / w v.1 ^ 2))
    * P.A' v u ≤ P.S
  col : ∀ u, ∑ v, Real.sqrt ((F.G.mass F.law u.1 / w u.1 ^ 2) / (F.G.mass F.law v.1 / w v.1 ^ 2))
    * P.A' v u ≤ P.S
  buffer : ∀ f : F.Data 0, Real.sqrt (∑ i : CompIn F.G.comps,
    (F.G.mass F.law i / w i ^ 2)⁻¹ * torusHkNorm P.ρold (le_refl (I.K (i, 0))) (I.B f i) ^ 2) ≤
    P.Cbuf * F.inputNorm w f

/-- **The neutral chain model from the copied-family readout.** Given one witness of the joint
preparation for the chain (for both masses), the buffered datum map `B`, and the identification
of the model map and the plain trace with the readouts, `NeutralChainModelStatement` holds with
the constants
`(H+1) CP Cbuf` and `(H+1) jointModelConst Cbuf`. -/
theorem neutral_chain_model_of_readout (F : Request hr D Dm bw j₀) (H : ℕ)
    (I : ReadoutInput F H) (P : GateParams F H I) {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (M : F.Model) (Cjoint Cjet : ℝ)
    (hgate : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      WeightGate F H I P w M.tp)
    (hρ : 0 < rhoEnh D F.cr F.G.level)
    (hJ : JointConstClause (h := fun i : CompIn F.G.comps => hr i.1.root) I.K F.Nout I.Pd I.Pg)
    (hBconst : ∀ (cv : ∀ v : CompIn F.G.comps, hr v.1.root) (f : F.Data 0),
      (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => cv v) →
      ∀ i, (truncateTorusHk (Nat.zero_le _) (I.B f i)).toFunction.jet (valueIndex2 0)
        =ᵐ[volume.restrict unitCube] fun _ => cv i)
    (hmap : ∀ f : F.Data 0, ∀ i, M.map f i = readout (h := fun i : CompIn F.G.comps => hr i.1.root)
      I.K F.Nout I.Pd I.Pg (datum I.K (I.B f)) i)
    (hsolve : ∀ f : F.Data 0, ∃ (u : ∀ v : CompIn F.G.comps × Fin (H + 1), ℝ →
        TorusHk (I.K v) (hr v.1.1.root))
      (w : ∀ v : CompIn F.G.comps × Fin (H + 1), ℝ → TorusHk (I.K v + 1) (hr v.1.1.root)),
      IsCoupledWeakSolutionTorus (h := fun v : CompIn F.G.comps × Fin (H + 1) => hr v.1.1.root)
        P.ν P.tS M.tp P.b P.Dord I.K P.Ac (preparationNeutralInitial H I.K (I.B f))
        (fun _ _ => 0) (fun _ _ => 0) u w ∧
      R.plainTrace M.tp f = plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root)
        I.K u M.tp)
    (hCjoint : ((H : ℝ) + 1) * (P.CP * P.Cbuf) ≤ Cjoint)
    (hCjet : ((H : ℝ) + 1) * (CycleComparison.Reconstruction.jointModelConst P.C P.S H F.Nout
      (rhoEnh D F.cr F.G.level / P.ρm) * P.Cbuf) ≤ Cjet) :
    F.NeutralChainModelStatement R M Cjoint Cjet := by
  classical
  refine ⟨?_, ?_⟩
  · intro cv f hf v
    have key := readout_const_of_initial (h := fun i : CompIn F.G.comps => hr i.1.root)
      I.K F.Nout I.Pd I.Pg hJ (I.B f) cv (hBconst cv f hf) v
    rw [hmap f v]
    exact key
  · intro w hw f
    obtain ⟨u, w', hsol, hpl⟩ := hsolve f
    have hG := hgate w hw
    have hb := copy_readout_bounds (h := fun i : CompIn F.G.comps => hr i.1.root)
      (fun v => F.G.mass F.law v / w v ^ 2) hG.mass_pos I.K F.Nout P.ν P.tS M.tp P.ρs P.ρold
      P.E F.Q P.CP (rhoEnh D F.cr F.G.level) P.ρm P.C P.S P.Cbuf (F.inputNorm w f) P.Θ P.b
      P.Fch P.A' P.nonneg P.Ac I.Pd I.Pg hG.model hG.error hG.row hG.col P.S_nonneg hρ
      P.radius_model_pos P.error_scale_nonneg (I.B f) (hG.buffer f) u w' hsol
    have hN : 0 ≤ F.inputNorm w f := Real.sqrt_nonneg _
    have hEQ : 0 ≤ D.eps (F.G.level - 1) ^ F.Q :=
      Real.rpow_nonneg (by unfold OCData.eps ocEpsilon; split_ifs <;> positivity) _
    have hb1 := hb.1
    rw [P.scale_eq] at hb1
    refine ⟨?_, ?_⟩
    · have hfun : ((fun v => truncateTorusHk (Nat.zero_le F.Nout) (M.map f v)) -
          R.plainTrace M.tp f) = fun i => truncateTorusHk (Nat.zero_le F.Nout)
              (readout (h := fun i : CompIn F.G.comps => hr i.1.root) I.K F.Nout I.Pd I.Pg
                (datum I.K (I.B f)) i) -
              plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root) I.K u M.tp i := by
        funext i
        have e2 : R.plainTrace M.tp f i =
            plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root) I.K u M.tp i :=
          congrFun hpl i
        show truncateTorusHk (Nat.zero_le F.Nout) (M.map f i) - R.plainTrace M.tp f i = _
        exact congrArg₂ (fun a b => truncateTorusHk (Nat.zero_le F.Nout) a - b) (hmap f i) e2
      have h1 : F.inputNorm w ((fun v => truncateTorusHk (Nat.zero_le F.Nout) (M.map f v)) -
          R.plainTrace M.tp f) = Real.sqrt (massNormSq (E := fun i : CompIn F.G.comps => hr i.1.root)
            (K := fun _ => 0) 1 (fun v => F.G.mass F.law v / w v ^ 2) (fun i =>
            (truncateTorusHk (Nat.zero_le F.Nout)
              (readout (h := fun i : CompIn F.G.comps => hr i.1.root) I.K F.Nout I.Pd I.Pg
                (datum I.K (I.B f)) i) -
              plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root) I.K u M.tp i).val)) := by
        exact (congrArg (F.inputNorm w) hfun).trans rfl
      rw [h1]
      refine hb1.trans ?_
      calc ((H : ℝ) + 1) * (P.CP * D.eps (F.G.level - 1) ^ F.Q * (P.Cbuf * F.inputNorm w f))
          = (((H : ℝ) + 1) * (P.CP * P.Cbuf)) * D.eps (F.G.level - 1) ^ F.Q * F.inputNorm w f := by
            ring
        _ ≤ Cjoint * D.eps (F.G.level - 1) ^ F.Q * F.inputNorm w f :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCjoint hEQ) hN
    · have hmapfun : M.map f = fun i => readout (h := fun i : CompIn F.G.comps => hr i.1.root)
          I.K F.Nout I.Pd I.Pg (datum I.K (I.B f)) i := funext (hmap f)
      have h2 : weightedNorm (rhoEnh D F.cr F.G.level) (F.G.mass F.law) w (M.map f) =
          Real.sqrt (massNormSq (E := fun i : CompIn F.G.comps => hr i.1.root)
            (K := fun _ => F.Nout) (rhoEnh D F.cr F.G.level)
            (fun v => F.G.mass F.law v / w v ^ 2) (fun i =>
            (readout (h := fun i : CompIn F.G.comps => hr i.1.root) I.K F.Nout I.Pd I.Pg
              (datum I.K (I.B f)) i).val)) := by
        exact (congrArg (weightedNorm (rhoEnh D F.cr F.G.level) (F.G.mass F.law) w)
          hmapfun).trans rfl
      rw [h2]
      refine hb.2.trans ?_
      calc ((H : ℝ) + 1) * (CycleComparison.Reconstruction.jointModelConst P.C P.S H F.Nout
            (rhoEnh D F.cr F.G.level / P.ρm) * (P.Cbuf * F.inputNorm w f))
          = (((H : ℝ) + 1) * (CycleComparison.Reconstruction.jointModelConst P.C P.S H F.Nout
            (rhoEnh D F.cr F.G.level / P.ρm) * P.Cbuf)) * F.inputNorm w f := by ring
        _ ≤ Cjet * F.inputNorm w f := mul_le_mul_of_nonneg_right hCjet hN

end CopyJoint
end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! The single joint witness and the same higher buffered datum determine
an explicit linear model map. The map is defined before both masses and the
datum; its application is exactly the readout used by CopyJointBridge.

The degenerate cases are included: H=0, empty and singleton families, zero/constants, identity
geometry, edgeless seeds, Dm=2 and arbitrary finite per-copy slots have the same map.
No mass, datum norm, second evolution or extra joint witness is used. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation
open CopyJoint

local instance copiedModelTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance copiedModelTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance copiedModelTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {H : ℕ}

/-- The blocks are applied once to the copy datum, then copies are summed
at the model order. This is the literal linear version of CopyJoint.readout. -/
def preparationCopiedReadoutMap (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ)
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ]
      TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1), TorusHk 0 (h u.1) →ₗ[ℝ]
      TorusHk (max Mout (K v)) (h v.1)) :
    (∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1)) →ₗ[ℝ] (∀ i, TorusHk Mout (h i)) :=
  LinearMap.pi fun i => ∑ l : Fin (H + 1),
    (truncateTorusHk (E := h i) (le_max_left Mout (K (i, l)))).toLinearMap.comp
      ((Pd (i, l)).comp (LinearMap.proj (i, l)) +
        ∑ j ∈ Finset.Icc 1 H, ∑ u : ι × Fin (H + 1),
          (Pg j (i, l) u).comp (LinearMap.proj u))

/-- The actual higher datum is inserted only in copy zero and truncated
to the order-zero data expected by the joint blocks. -/
def preparationCopiedDatumMap (K : ι × Fin (H + 1) → ℕ) :
    (∀ i, TorusHk (K (i, 0)) (h i)) →ₗ[ℝ]
      (∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1)) :=
  (LinearMap.pi fun v : ι × Fin (H + 1) =>
    (truncateTorusHk (E := h v.1) (Nat.zero_le (K v))).toLinearMap.comp (LinearMap.proj v)).comp
      (preparationNeutralInitial H K)

/-- The actual model is the composition with the SAME linear high buffer map. -/
def preparationCopiedModelMap (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ)
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ]
      TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1), TorusHk 0 (h u.1) →ₗ[ℝ]
      TorusHk (max Mout (K v)) (h v.1))
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (K (i, 0)) (h i))) :
    (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk Mout (h i)) :=
  (preparationCopiedReadoutMap K Mout Pd Pg).comp ((preparationCopiedDatumMap K).comp B)

/-- Exact hmap of CopyJointBridge, preserving the supplied joint blocks
and the same high buffered datum, before either mass or any datum is chosen. -/
theorem preparation_copied_model_apply (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ)
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ]
      TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1), TorusHk 0 (h u.1) →ₗ[ℝ]
      TorusHk (max Mout (K v)) (h v.1))
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (K (i, 0)) (h i)))
    (f : ∀ i, TorusHk 0 (h i)) (i : ι) :
    preparationCopiedModelMap K Mout Pd Pg B f i =
      readout K Mout Pd Pg (datum K (B f)) i := by
  simp only [preparationCopiedModelMap, preparationCopiedReadoutMap, preparationCopiedDatumMap,
    readout, datum, jointOperator, LinearMap.comp_apply, LinearMap.pi_apply,
    LinearMap.sum_apply, LinearMap.add_apply, LinearMap.proj_apply]
  rfl

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! The same joint-preparation witness of the copied family and the same higher buffered datum
produce ONE literal preparation model. The witness is supplied BEFORE masses;
all its bounds, constants and the actual copied solution are existing inputs.
The degenerate cases are included: depth zero, empty and singleton families, smallest output
orders, constants, identity geometry and an edgeless seed keep the exact buffer endpoint and
quiet margin; no alternate time or mass-dependent map is selected. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation
open CopyJoint
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The explicit linear copied readout satisfies the neutral-model and exact
endpoint clauses, with precisely the supplied tp/Pd/Pg and buffer. -/
def CopiedPreparationWitnessJoinStatement (F : Request hr D Dm bw j₀) (H : ℕ)
    (I : ReadoutInput F H) (P : GateParams F H I) {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (tp Cjoint Cjet : ℝ)
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (I.K (i, 0)) (hr i.1.root)))
    (_hB : I.B = B.toFun)
    (_hdelay : F.s ≤ F.bufferEnd ∧
      F.bufferEnd ≤ F.s + 2 * ocTauPP D.α D.q D.Λ F.G.level)
    (_htp : tp ∈ Set.Icc F.bufferEnd
      (F.bufferEnd + 2 * ocTauPP D.α D.q D.Λ F.G.level))
    (_hquiet : tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ F.G.level)
    (_hquietMargin : Set.Icc (tp - ocTauP D.α D.q D.Λ F.G.level)
      (tp + ocTauP D.α D.q D.Λ F.G.level) ⊆
        ocQuietTimes D.α D.q D.Λ D.ζ F.G.level)
    (_hgate : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      WeightGate F H I P w tp)
    (_hρ : 0 < rhoEnh D F.cr F.G.level)
    (_hJ : JointConstClause (h := fun i : CompIn F.G.comps => hr i.1.root) I.K F.Nout I.Pd I.Pg)
    (_hBconst : ∀ (cv : ∀ v : CompIn F.G.comps, hr v.1.root) (f : F.Data 0),
      (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => cv v) →
      ∀ i, (truncateTorusHk (Nat.zero_le _) (I.B f i)).toFunction.jet (valueIndex2 0)
        =ᵐ[volume.restrict unitCube] fun _ => cv i)
    (_hsolve : ∀ f : F.Data 0, ∃ (u : ∀ v : CompIn F.G.comps × Fin (H + 1), ℝ →
        TorusHk (I.K v) (hr v.1.1.root))
      (w : ∀ v : CompIn F.G.comps × Fin (H + 1), ℝ → TorusHk (I.K v + 1) (hr v.1.1.root)),
      IsCoupledWeakSolutionTorus (h := fun v : CompIn F.G.comps × Fin (H + 1) => hr v.1.1.root)
        P.ν P.tS tp P.b P.Dord I.K P.Ac (preparationNeutralInitial H I.K (I.B f))
        (fun _ _ => 0) (fun _ _ => 0) u w ∧
      R.plainTrace tp f = plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root)
        I.K u tp)
    (_hCjoint : ((H : ℝ) + 1) * (P.CP * P.Cbuf) ≤ Cjoint)
    (_hCjet : ((H : ℝ) + 1) * (CycleComparison.Reconstruction.jointModelConst P.C P.S H F.Nout
      (rhoEnh D F.cr F.G.level / P.ρm) * P.Cbuf) ≤ Cjet) : Prop :=
  ∃ M : F.Model,
    M.tp = tp ∧
    M.map = preparationCopiedModelMap I.K F.Nout I.Pd I.Pg B ∧
    F.NeutralChainModelStatement R M Cjoint Cjet ∧ F.EndpointStatement M

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! Join the supplied joint-preparation and buffer witnesses of the copied family into one literal
linear preparation model. Its endpoint, blocks, buffered datum and genuine
copied solution are retained for both weights and every datum. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation
open CopyJoint
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The explicit copied readout is a neutral preparation model at precisely
its supplied buffered endpoint of the joint preparation, with the supplied quiet margin. -/
theorem copiedPreparationWitnessJoin (F : Request hr D Dm bw j₀) (H : ℕ)
    (I : ReadoutInput F H) (P : GateParams F H I) {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (tp Cjoint Cjet : ℝ)
    (B : (∀ i : CompIn F.G.comps, TorusHk 0 (hr i.1.root)) →ₗ[ℝ]
      (∀ i : CompIn F.G.comps, TorusHk (I.K (i, 0)) (hr i.1.root)))
    (hB : I.B = B.toFun)
    (hdelay : F.s ≤ F.bufferEnd ∧
      F.bufferEnd ≤ F.s + 2 * ocTauPP D.α D.q D.Λ F.G.level)
    (htp : tp ∈ Set.Icc F.bufferEnd
      (F.bufferEnd + 2 * ocTauPP D.α D.q D.Λ F.G.level))
    (hquiet : tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ F.G.level)
    (hquietMargin : Set.Icc (tp - ocTauP D.α D.q D.Λ F.G.level)
      (tp + ocTauP D.α D.q D.Λ F.G.level) ⊆
        ocQuietTimes D.α D.q D.Λ D.ζ F.G.level)
    (hgate : ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
      WeightGate F H I P w tp)
    (hρ : 0 < rhoEnh D F.cr F.G.level)
    (hJ : JointConstClause (h := fun i : CompIn F.G.comps => hr i.1.root) I.K F.Nout I.Pd I.Pg)
    (hBconst : ∀ (cv : ∀ v : CompIn F.G.comps, hr v.1.root) (f : F.Data 0),
      (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => cv v) →
      ∀ i, (truncateTorusHk (Nat.zero_le _) (I.B f i)).toFunction.jet (valueIndex2 0)
        =ᵐ[volume.restrict unitCube] fun _ => cv i)
    (hsolve : ∀ f : F.Data 0, ∃ (u : ∀ v : CompIn F.G.comps × Fin (H + 1), ℝ →
        TorusHk (I.K v) (hr v.1.1.root))
      (w : ∀ v : CompIn F.G.comps × Fin (H + 1), ℝ → TorusHk (I.K v + 1) (hr v.1.1.root)),
      IsCoupledWeakSolutionTorus (h := fun v : CompIn F.G.comps × Fin (H + 1) => hr v.1.1.root)
        P.ν P.tS tp P.b P.Dord I.K P.Ac (preparationNeutralInitial H I.K (I.B f))
        (fun _ _ => 0) (fun _ _ => 0) u w ∧
      R.plainTrace tp f = plainReadout (h := fun i : CompIn F.G.comps => hr i.1.root)
        I.K u tp)
    (hCjoint : ((H : ℝ) + 1) * (P.CP * P.Cbuf) ≤ Cjoint)
    (hCjet : ((H : ℝ) + 1) * (CycleComparison.Reconstruction.jointModelConst P.C P.S H F.Nout
      (rhoEnh D F.cr F.G.level / P.ρm) * P.Cbuf) ≤ Cjet) :
    CopiedPreparationWitnessJoinStatement F H I P R tp Cjoint Cjet B hB hdelay htp
      hquiet hquietMargin hgate hρ hJ hBconst hsolve hCjoint hCjet := by
  let M : F.Model :=
    { tp := tp
      map := preparationCopiedModelMap (h := fun i : CompIn F.G.comps => hr i.1.root)
        I.K F.Nout I.Pd I.Pg B }
  refine ⟨M, rfl, rfl, ?_, hdelay.1, hdelay.2, htp, hquiet, hquietMargin⟩
  apply neutral_chain_model_of_readout F H I P R M Cjoint Cjet hgate hρ hJ hBconst
    ?_ hsolve hCjoint hCjet
  intro f i
  rw [hB]
  exact preparation_copied_model_apply (h := fun i : CompIn F.G.comps => hr i.1.root)
    I.K F.Nout I.Pd I.Pg B f i

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! The higher original records of an incoming proper descendant fit its
molecular radius. This is the geometric input of the shared context-envelope
producer at any finite preparation request; no stored-order cap is used.
The scale estimates and the one-step provenance argument are the existing
FullLift lemmas. The seed uses its supplied envelope instead.

The seed is explicitly excluded, empty or edgeless families give vacuous bounds, and the
level floor is at least two. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.CommonPreparation
open FullLift StageEnvelopes Residual.Presentation.Cascade

/-- Frequency and level choices precede every stage, menu and coefficient.
Only the positive molecular-radius coefficient affects the level floor. -/
def IncomingHigherRecordRadiiStatement (α q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ c₀ : ℝ, 0 < c₀ →
  ∃ m₀ : ℕ, 2 ≤ m₀ ∧
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
    IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
  ∀ (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (Mn : SuccMenu) (Cw cr σ₀ η₀ : ℝ) (N p : ℕ), cr ≤ 1 →
  ∀ (seed G : GenStage D hr Dm bw j₀),
    seed.HasTags (succProvParams D Cw cr σ₀ η₀ N p) →
    (∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level) →
    seed.level ≤ D.term →
    IsCascadeStage D (succProvParams D Cw cr σ₀ η₀ N p) Mn seed G →
    m₀ ≤ G.level → G.level < seed.level →
    ∀ v u (γ : G.fam.Γ v u), 3 ≤ (G.fam.identity v u γ).maxOrder →
      (G.fam.identity v u γ).record.length ≤ rhoStar D c₀ G.level

/-- The existing scale and provenance estimates give the incoming radius
without assuming a predecessor invariant or strengthening the seed radius. -/
theorem incoming_higher_record_radii {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    IncomingHigherRecordRadiiStatement α q ζ := by
  obtain ⟨Cu, _, Λp, hΛp, hpass⟩ := Providers.CascadeInvariants.exists_passScales hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λl, hΛl, hlens⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λp (max Λl Λr), by omega, ?_⟩
  intro Λ hΛ c₀ hc₀
  have h128 : 128 ≤ Λ := by omega
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hdecay := Buffer.preparation_parent_power_tendsto_zero hq.1 h128
    (mul_pos (by norm_num : (0 : ℝ) < 3) hδ)
  have hlim : Tendsto (fun m : ℕ => Cu * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q))
      atTop (𝓝 0) := by simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  obtain ⟨mp, hmp⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds zero_lt_one))
  obtain ⟨mr, _, hradius⟩ := hradius Λ (by omega) c₀ 1 hc₀ zero_lt_one
  refine ⟨max 2 (max mp mr), by omega, ?_⟩
  intro hr _ _ D hDα hDq hDΛ hDζ hband Dm bw j₀ Mn Cw cr σ₀ η₀ N p hcr
    seed G hseedT hseedL hseedlevel hcascade hlevel hproper
  cases hcascade with
  | seed => omega
  | @step G₁ G₁' hcascade hactual =>
    have hGl : G₁'.level = G₁.level - 1 := hactual.2.1
    have hlate : max 2 (max mp mr) ≤ G₁'.level := hlevel
    have hG₁term : G₁.level ≤ D.term :=
      (Providers.CascadeInvariants.level_le_of_cascade hcascade).trans hseedlevel
    have hpass' := hpass D hDα hDq hDζ (by omega)
      (by simpa only [hDα, hDq, hDΛ, hDζ] using hband) G₁.level (by omega) hG₁term
    have hsmall : Cu * D.eps (G₁.level - 1) ^ (3 * ocDelta D.α D.q) ≤ 1 := by
      simpa only [OCData.eps, hDα, hDq, hDΛ] using hmp G₁.level (by omega)
    have hεlift : D.eps G₁.level ≤ liftLength D G₁.level :=
      hpass'.hεd.trans ((div_le_one hpass'.hρ0).mp (hpass'.hDρ.trans hsmall))
    have hlift : liftLength D G₁.level ≤ rhoStar D c₀ (G₁.level - 1) := by
      simpa only [rhoEnh, one_mul, liftLength] using
        hradius D hDα hDq hDΛ hDζ hband G₁.level (by omega) hG₁term
    have hlensG := hlens hr D hDα hDq hDζ (by omega) hband Dm bw j₀ Mn Cw cr σ₀ η₀ N p
      hcr seed G₁ hseedT hseedL hseedlevel hcascade (by omega)
    have hR : (succProvParams D Cw cr σ₀ η₀ N p).Rb (G₁.level - 1) ≤
        rhoStar D c₀ (G₁.level - 1) := by
      change freshLength D cr (G₁.level - 1) ≤ _
      have heq : freshLength D cr (G₁.level - 1) = cr * liftLength D G₁.level := by
        unfold freshLength liftLength
        rw [Nat.sub_add_cancel (by omega : 1 ≤ G₁.level)]
      rw [heq]
      exact (mul_le_mul_of_nonneg_right hcr hpass'.hρ0.le).trans
        (by simpa only [one_mul] using hlift)
    have hh := step_higher_length (Providers.CascadeInvariants.hasTags_of_cascade hseedT hcascade)
      hactual (fun v u γ hbe => (hlensG v u γ hbe).trans (hεlift.trans hlift)) hR
    intro v u γ h3
    change _ ≤ rhoStar D c₀ G₁'.level
    rw [hGl]
    exact hh v u γ h3

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
