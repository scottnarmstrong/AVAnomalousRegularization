-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.StageEnvelopes.Assembly
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
public import AVRegularity.Construction.Preservation.Assembly.StageInvariantPropagationOfIngredients
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
import AVRegularity.Construction.StageEnvelopes.Cauchy.Assembly
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs

section
section
/-! Instantiate the single shared context estimate on a retained stage and on weak entry.
The actual carrier/radius and the constant comparison remain explicit caller obligations;
this module neither assumes a stage invariant nor constructs a second analytic producer. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Preservation
namespace AVRegularity.Construction.StageEnvelopes

private theorem markerConj_one {ι : Type*} {h : ι → Type*} [∀ v, NormedAddCommGroup (h v)]
    [∀ v, NormedSpace ℝ (h v)] {Dm : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h Dm P Ctx) : markerConj (fun _ => 1) F = F := by
  unfold markerConj
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_smul]

private theorem record_le_priced {ι : Type*} {h : ι → Type*} [∀ v, NormedAddCommGroup (h v)]
    [∀ v, NormedSpace ℝ (h v)] {Dm : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h Dm P Ctx) (π : ι → ℝ) (v u : ι) :
    recordMajorant π F v u ≤ pricedRecordMajorant π (fun _ => 1) F v u := by
  unfold recordMajorant pricedRecordMajorant
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Finset.sum_le_sum
  intro γ _
  exact le_mul_of_one_le_right
    (mul_nonneg (norm_nonneg _) (F.identity v u γ).record.size_nonneg)
    (le_max_left _ _)

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm j₀ : ℕ} {b : ℝ}

/-- Fixed-stage instantiation for SuccessorEnvelopesOfContextStatement. Its supplied K3
ledger pays both record Schur bounds; the same estimate also returns the pointwise seed form. -/
theorem stage_envelopes_with_ledger_of_context
    (p : ContextEnvelopeParameters) (E : ContextEnvelopeEstimate p)
    (G : GenStage D hr Dm b j₀) (k : InvConsts) (ρ : ℝ)
    (hinput : ContextEnvelopeInput p G k k.mEnv ρ)
    (hlevel : E.levelFloor ≤ G.level)
    (hCa : E.Ca ≤ k.Ca) (hCm : ∀ j, E.Cm j ≤ k.Cm j)
    (law : BirthLaw) (tA tB S : ℝ)
    (hledger : markedLedger (G.mass law) (G.marker law) G.fam ≤ S) :
    (∀ K : CompIn G.comps → ℕ, (∀ v, K v ≤ k.Ks) →
      IsEnvelope G.fam (G.mass law) K (G.innerDomain (Set.Icc tA tB) k.mEnv)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ρ
        (recordMajorant (G.mass law) G.fam) S k.Ca k.Kan k.Lan k.Cm k.Jm ∧
      IsEnvelope (markerConj (G.marker law) G.fam) (G.mass law) K
        (G.innerDomain (Set.Icc tA tB) k.mEnv)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ρ
        (fun v u => G.marker law v / G.marker law u * recordMajorant (G.mass law) G.fam v u)
        S k.Ca k.Kan k.Lan k.Cm k.Jm) ∧
    (∀ K : CompIn G.comps → ℕ, (∀ v, K v ≤ k.Ks) →
      IsPointwiseMolecularEnvelope G.fam (G.mass law) K (G.innerDomain (Set.Icc tA tB) k.mEnv)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ρ k.Cm k.Jm
        (recordMajorant (G.mass law) G.fam)) := by
  have hmarker v : 0 < G.marker law v :=
    Buffer.birth_compMarker_pos hinput.q_pos hinput.large law v.1
  have hmass v : 0 < G.mass law v := Buffer.birth_compMass_pos hinput.q_pos hinput.large law v.1
  have h := E.bound hr D Dm j₀ b G k k.mEnv ρ hinput hlevel hCa hCm law (Set.Icc tA tB)
  have h1 := h (fun _ => 1) (fun _ => zero_lt_one)
  dsimp only at h1
  rw [markerConj_one G.fam] at h1
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul] at h1
  have hm := h (G.marker law) hmarker
  have hp := FullLift.priced_record_ledger_schur G.fam (G.mass law) (G.marker law)
    hmass hmarker S hledger
  have hrec v u := record_le_priced G.fam (G.mass law) v u
  have hrecM v u : G.marker law v / G.marker law u * recordMajorant (G.mass law) G.fam v u ≤
      pricedRecordMajorant (fun v => G.mass law v / G.marker law v ^ 2) (fun _ => 1) G.fam v u := by
    rw [FullLift.pricedRecordMajorant_effective_mass G.fam _ _ hmass hmarker]
    simpa only [pricedRecordMajorant, div_self (by norm_num : (1 : ℝ) ≠ 0),
      one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (hrec v u) (div_nonneg (hmarker v).le (hmarker u).le)
  have hn v u : 0 ≤ recordMajorant (G.mass law) G.fam v u := mul_nonneg (Real.sqrt_nonneg _)
    (Finset.sum_nonneg fun γ _ => mul_nonneg (norm_nonneg _) (G.fam.identity v u γ).record.size_nonneg)
  constructor
  · intro K hK
    have ho := h1 K hK
    have hmk := hm K hK
    exact ⟨⟨hn, fun v => (Finset.sum_le_sum (fun u _ => hrec v u)).trans (hp.1.1 v),
      fun u => (Finset.sum_le_sum (fun v _ => hrec v u)).trans (hp.1.2 u), ho.1, ho.2.1⟩,
      ⟨fun v u => mul_nonneg (div_nonneg (hmarker v).le (hmarker u).le) (hn v u),
        fun v => (Finset.sum_le_sum (fun u _ => hrecM v u)).trans (hp.2.1 v),
        fun u => (Finset.sum_le_sum (fun v _ => hrecM v u)).trans (hp.2.2 u), hmk.1, hmk.2.1⟩⟩
  · intro K hK
    exact (h1 K hK).2.2.2


end AVRegularity.Construction.StageEnvelopes
end
end

section
/-! Exact uniform successor-envelope assembly. The shared estimate is independent of the
successor geometry; the remaining reserve/length and constant comparison is named separately. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.StageEnvelopes

/-- Uniform geometric adapter for a chosen family of shared estimates. It asserts only the
actual carrier, reserve, order and radius inputs and domination of the chosen constants. -/
def ContextEnvelopeAdapterClause
    (estimates : ∀ p, ContextEnvelopeEstimate p) : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun _law _P _seedK _freshK _φ₀ _hφ₀ _M k _tA _tB _S _θ G =>
    ∃ p : ContextEnvelopeParameters,
      ContextEnvelopeInput p G k k.mEnv (rhoStar D k.c₀ G.level) ∧
      (estimates p).levelFloor ≤ G.level ∧
      (estimates p).Ca ≤ k.Ca ∧ ∀ j, (estimates p).Cm j ≤ k.Cm j

/-- The geometric adapter statement under the unchanged propagation prefix. -/
def SuccessorContextEnvelopeAdapterStatement (α s q : ℝ) (ζ : ℝ → ℝ)
    (estimates : ∀ p, ContextEnvelopeEstimate p) : Prop :=
  StageProductionStatement α s q ζ (ContextEnvelopeAdapterClause estimates)

/-- Exact retained-successor leaf from the shared estimate and its uniform geometry adapter.
Structural certificates and the ledger are discharged by the certificate theorem. -/
theorem successor_envelopes_of_context_inputs
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (estimates : ∀ p, ContextEnvelopeEstimate p)
    (hinputs : SuccessorContextEnvelopeAdapterStatement α s q ζ estimates) :
    SuccessorEnvelopesOfContextStatement α s q ζ := by
  classical
  have hbase := stage_base_of_certificates
    (retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
  obtain ⟨Λ₀, hΛ₀, hc⟩ := stage_production_and hbase hinputs
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨mStar, hc⟩ := hc CI Cw j₀ hledger hstart
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hbase, pEnv, hinput, hfloor, hCa, hCm⟩ := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA htA G G' hcascade hlevel hG hactual
  exact (stage_envelopes_with_ledger_of_context pEnv (estimates pEnv) (G'.retained m H J)
    kI (rhoStar D kI.c₀ (G'.retained m H J).level) hinput hfloor hCa hCm law
    (tA + 3 * ocTau α q Λ m) tf _ hbase.2.2.2.2.2.2.1).1

end AVRegularity.Construction.StageEnvelopes
end
end

section
/-! Successor adapter assembly. Structural certification is supplied by the retained
certificates. The remaining ingredient concerns the reserve/radius/order geometry and a common
pre-data choice of envelope constants; it contains no envelope conclusion. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.StageEnvelopes

/-- The quantitative adapter before supplying the already proved structural certificates.
The input builder spells out exactly the geometric obligations through ContextEnvelopeInput;
it does not require any analytic or molecular envelope as an input. -/
def ContextEnvelopePreparationClause
    (estimates : ∀ p, ContextEnvelopeEstimate p) : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun _law _P _seedK _freshK _φ₀ _hφ₀ _M k _tA _tB _S _θ G =>
    ∃ p : ContextEnvelopeParameters,
      ((∃ M, G.IsNatural M) → G.IsContextCertified k →
        ContextEnvelopeInput p G k k.mEnv (rhoStar D k.c₀ G.level)) ∧
      (estimates p).levelFloor ≤ G.level ∧
      (estimates p).Ca ≤ k.Ca ∧ ∀ j, (estimates p).Cm j ≤ k.Cm j

/-- Fixed parameter menus, a strict reserve gap, higher original lengths
inside rhoStar, and common pre-data thresholds dominating the chosen envelope constants. -/
def SuccessorContextEnvelopePreparationStatement (α s q : ℝ) (ζ : ℝ → ℝ)
    (estimates : ∀ p, ContextEnvelopeEstimate p) : Prop :=
  StageProductionStatement α s q ζ (ContextEnvelopePreparationClause estimates)

/-- Exact successor adapter from quantitative preparation. Naturality and certification are
discharged by retained_stage_certificates, with common thresholds chosen by stage_production_and. -/
theorem successor_context_envelope_adapter_of_preparation
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (estimates : ∀ p, ContextEnvelopeEstimate p)
    (hpreparation : SuccessorContextEnvelopePreparationStatement α s q ζ estimates) :
    SuccessorContextEnvelopeAdapterStatement α s q ζ estimates := by
  classical
  have hbase := stage_base_of_certificates
    (retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
  obtain ⟨Λ₀, hΛ₀, hc⟩ := stage_production_and hbase hpreparation
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨mStar, hc⟩ := hc CI Cw j₀ hledger hstart
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hbase, pEnv, hprepare, hfloor, hCa, hCm⟩ := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA htA G G' hcascade hlevel hG hactual
  exact ⟨pEnv, hprepare ⟨Mnat, hbase.1⟩ hbase.2.2.2.2.2.1, hfloor, hCa, hCm⟩

end AVRegularity.Construction.StageEnvelopes
end
end

section
/-! Original higher-record lengths fit the molecular radius after the first transition.
The seed itself is not assigned an improved radius. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.Construction.StageEnvelopes
open Preservation Preservation.Assembly Preservation.FullLift

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The higher original lengths of one actual successor use only old lengths and fresh lengths.
Quadratic conversions have no higher original order. -/
theorem actual_successor_higher_lengths {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm bw j₀} (hG : G.HasTags P)
    (hactual : IsActualSuccessor D P Mn G G') {ρ : ℝ}
    (hold : ∀ v u (γ : G.fam.Γ v u), 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ ρ)
    (hfresh : P.Rb (G.level - 1) ≤ ρ) :
    ∀ v u (γ : G'.fam.Γ v u), 3 ≤ (G'.fam.identity v u γ).maxOrder →
      (G'.fam.identity v u γ).record.length ≤ ρ := by
  obtain ⟨_, _, _, _, htags, _, e, _, _, _, _, hall⟩ := hactual
  intro v u γ h3
  have hbe : 1 ≤ (G'.fam.identity v u γ).record.birthExcess := by
    have := (G'.fam.identity v u γ).le_birth
    omega
  obtain ⟨hT, _⟩ := htags v u γ
  obtain ⟨hprov, _⟩ := hall v u γ
  rw [hT.2.2.1, hprov] at hbe
  rw [hT.2.2.2.1, hprov]
  generalize (e v u γ).1 = s at hbe ⊢
  cases s with
  | copyDir t v₀ u₀ γ₀ =>
    simp only [SuccSource.prov] at hbe ⊢
    rw [(Providers.CascadeInvariants.Prov.tags_dir P _ _).1]
    rw [(Providers.CascadeInvariants.Prov.tags_dir P _ _).2] at hbe
    obtain ⟨hT₀, _⟩ := hG v₀ u₀ γ₀
    rw [← hT₀.2.2.1] at hbe
    rw [← hT₀.2.2.2.1]
    exact hold v₀ u₀ γ₀ hbe
  | copyQuad t h π =>
    simp only [SuccSource.prov, Providers.CascadeInvariants.Prov.tags_quad_birthExcess] at hbe
    omega
  | letterDiag t u₀ =>
    simpa only [SuccSource.prov, Providers.CascadeInvariants.Prov.tags_letter_length] using hfresh
  | letterMean t n h π =>
    simpa only [SuccSource.prov, Providers.CascadeInvariants.Prov.tags_letter_length] using hfresh
  | letterCov t n h a a' π =>
    simpa only [SuccSource.prov, Providers.CascadeInvariants.Prov.tags_letter_length] using hfresh

/-- Exact geometric leaf of the successor envelope adapter, with the propagation prefix. -/
def SuccessorHigherLengthsStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  StageProductionStatement α s q ζ (by
    intro hr _ _ _ _ _ _ _ D Dm bw j₀
    exact fun _law _P _seedK _freshK _φ₀ _hφ₀ _M k _tA _tB _S _θ G =>
      ∀ v u (γ : G.fam.Γ v u), 3 ≤ (G.fam.identity v u γ).maxOrder →
        (G.fam.identity v u γ).record.length ≤ rhoStar D k.c₀ G.level)

/-- At sufficiently late levels the lift radius absorbs the incoming wavelength and every
fresh length. The original length of a copied higher identity stays unchanged. -/
theorem successor_higher_lengths (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : SuccessorHigherLengthsStatement α s q ζ := by
  obtain ⟨Cu, hCu, Λp, hΛp, hpass⟩ := Providers.CascadeInvariants.exists_passScales hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λl, hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λp (max Λl Λr), by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨kS, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hdecay := Buffer.preparation_parent_power_tendsto_zero hq.1 h128
    (mul_pos (by norm_num : (0 : ℝ) < 3) hδ)
  have hlim : Tendsto (fun m : ℕ => Cu * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q))
      atTop (𝓝 0) := by simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  obtain ⟨mp, hmp⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds zero_lt_one))
  have hcI : 0 < kI.c₀ := hkI.1.symm ▸ hc₀
  obtain ⟨mr, hmr, hradius⟩ := hradius Λ (by omega) kI.c₀ 1 hcI zero_lt_one
  refine ⟨max 2 (max mp mr), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hpass' := hpass D hDα hDq hDζ (by omega) (by simpa only [hterm, hDΛ] using hband)
    m (by omega) (by omega)
  have hsmall : Cu * D.eps (m - 1) ^ (3 * ocDelta D.α D.q) ≤ 1 := by
    simpa only [OCData.eps, hDα, hDq, hDΛ] using hmp m (by omega)
  have hεlift : D.eps m ≤ liftLength D m := by
    have hd := hpass'.hDρ
    have hρ := hpass'.hρ0
    have hds : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / liftLength D m ≤ 1 :=
      hd.trans hsmall
    exact hpass'.hεd.trans ((div_le_one hρ).mp hds)
  have hlift : liftLength D m ≤ rhoStar D kI.c₀ (m - 1) := by
    have hh := hradius D hDα hDq hDΛ hDζ hbandD m (by omega) (by omega)
    simpa only [rhoEnh, one_mul, liftLength] using hh
  obtain ⟨hseedlevel, _, _, _, _, hseedlength, _, hseedInv, _⟩ := hseed
  have hlengthG := hlength hr D hDα hDq hDζ (by omega) hbandD _ bw j₀ _ Cw kI.cr σ₀
    (succEta0 α q s) N p (hkI.2.1.symm ▸ hcrupper) seed G hseedInv.2.1
    (fun v u γ hbe => by simpa only [hseedlevel] using (hseedlength v u γ).2.2 hbe)
    (by rw [hseedlevel, hterm]; omega) hcascade (by omega)
  have hR : (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p).Rb (G.level - 1) ≤
      rhoStar D kI.c₀ (m - 1) := by
    change freshLength D kI.cr (G.level - 1) ≤ _
    rw [hlevel]
    have hcrI : kI.cr ≤ 1 := hkI.2.1.symm ▸ hcrupper
    have heq : freshLength D kI.cr (m - 1) = kI.cr * liftLength D m := by
      unfold freshLength liftLength
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hcrI hpass'.hρ0.le).trans
      (by simpa only [one_mul] using hlift)
  have hout := actual_successor_higher_lengths hG.2.1 hactual
    (fun v u γ hbe => (hlengthG v u γ hbe).trans (by rw [hlevel]; exact hεlift.trans hlift)) hR
  intro v u γ h3
  have hGrlevel : (G'.retained m H J).level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  conv_rhs => rw [hGrlevel]
  exact hout ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩ γ h3

end AVRegularity.Construction.StageEnvelopes
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped Classical
namespace AVRegularity.Construction.StageEnvelopes

/-! Fixed reserve and derivative menus instantiate the shared producer on a retained successor.
The estimate is selected before the invariant constants; its constants are paid by the
ordinary admissibility thresholds. -/

open Preservation Preservation.Assembly Preservation.FullLift

/-- Retention leaves TWO reciprocal reserve units; the envelope needs only one. -/
theorem retained_compReserve_ge {k : InvConsts} {H : ℕ}
    (hk : k.Hprod = k.G0 + H + 1) {c : Comp} (hc : compGrade c ≤ H) :
    2 / ((k.Hprod : ℝ) + 1) ≤ compReserve k c := by
  have hd : 0 < (k.Hprod : ℝ) + 1 := by positivity
  have he : compReserve k c =
      (((k.Hprod : ℝ) + 1) - (k.G0 + compGrade c : ℕ)) / ((k.Hprod : ℝ) + 1) := by
    unfold compReserve
    rw [sub_div, div_self hd.ne']
  rw [he]
  apply div_le_div_of_nonneg_right _ hd.le
  have hgrade : (compGrade c : ℝ) ≤ (H : ℝ) := by exact_mod_cast hc
  rw [hk]
  push_cast
  linarith only [hgrade]

/-- The shared analytic request depends on the seed allocation and schedule, before kI. -/
def successorEnvelopeParameters (α s q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
    (bw : ℝ) (hbw : 0 < bw) (hbwupper : bw ≤ 1 / 10000) (kS : InvConsts) (Dm : ℕ) :
    ContextEnvelopeParameters where
  α := α
  s := s
  q := q
  Λ := Λ
  ζ := ζ
  alpha_pos := hα₀
  alpha_lt := hα₁
  s_pos := hs₀
  s_lt := hs₁
  admissible_q := hq
  base_large := hΛ
  profile := hζ
  bw := bw
  bw_pos := hbw
  bw_small := hbwupper
  certReserve := 2 / ((kS.Hprod : ℝ) + 1)
  innerReserve := 1 / ((kS.Hprod : ℝ) + 1)
  inner_nonneg := by positivity
  gap := div_lt_div_of_pos_right (by norm_num) (by positivity)
  cert_le_two := by
    apply (div_le_iff₀ (by positivity : 0 < (kS.Hprod : ℝ) + 1)).mpr
    have hh := Nat.cast_nonneg (α := ℝ) kS.Hprod
    linarith only [hh]
  Ks := kS.Ks
  Kan := kS.Kan
  Lan := kS.Lan
  Jm := kS.Jm
  Dstar := Dm

/-- The moderate successor geometry ingredient is proved. The original seed is used only
through its cascade lengths; it is never assigned a smaller molecular radius. -/
theorem successor_context_envelope_preparation
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (estimates : ∀ p, ContextEnvelopeEstimate p) :
    SuccessorContextEnvelopePreparationStatement α s q ζ estimates := by
  obtain ⟨Λ₀, hΛ₀, hl⟩ := successor_higher_lengths α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨cmax, hcmax, hl⟩ := hl Λ hΛ
  refine ⟨min cmax 1, lt_min hcmax zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr₀, CH, Υ, hCH, hΥ, hl⟩ := hl φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  let pe := successorEnvelopeParameters α s q Λ ζ hα₀ hα₁ hs₀ hs₁ hq h128 hζ bw hbw hbwupper kS
    (succSchedD D₀ N p (H + 1))
  let thr : InvConsts :=
    { thr₀ with
      Ca := max thr₀.Ca (estimates pe).Ca
      Cm := fun j => max (thr₀.Cm j) ((estimates pe).Cm j) }
  obtain ⟨Υ', hcarrier, hstart_mono⟩ := Cauchy.common_carrier_constants h128 hCH hΥ
  refine ⟨thr, CH, Υ', hCH, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 100)
    ((le_max_left _ _).trans hcarrier.2), ?_⟩
  intro kI hkI
  have hkI₀ := invariant_admissible_of_threshold_bounds (a := thr₀) (b := thr)
    le_rfl le_rfl (le_max_left _ _) (fun _ => le_max_left _ _) (fun _ => le_rfl) hkI
  rcases id hkI with ⟨hcEq, _, _, _, _, _, _, _, _, _, _, hCa, hCm, _, _, _, _,
    _, hKs, _, hKan, _, hLan, _, hJm, _, _, hG0, hHprod, hprod, henvnonneg, _, henvlt⟩
  have hCaI : (estimates pe).Ca ≤ kI.Ca := (le_max_right _ _).trans hCa
  have hCmI (j : ℕ) : (estimates pe).Cm j ≤ kI.Cm j := (le_max_right _ _).trans (hCm j).2
  obtain ⟨CIthr, Cwthr, hl⟩ := hl kI hkI₀
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨ml, hl⟩ := hl CI Cw j₀ hledger (hstart_mono j₀ hstart)
  refine ⟨max ml (max (j₀ + 2) ((estimates pe).levelFloor + 1)), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  have hlength := hl D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA htA G G' hcascade hlevel hG hactual
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
    (by rw [hGrlevel, hterm]; omega)
  have hcI : 0 < kI.c₀ := hcEq.symm ▸ hc₀
  have hcIupper : kI.c₀ ≤ 1 := hcEq.symm ▸ hc₀upper.trans (min_le_right _ _)
  have hrho : 0 < rhoStar D kI.c₀ Gr.level := mul_pos hcI
    (lt_min (hε _) (Real.sqrt_pos.mpr (div_pos hκ (Real.rpow_pos_of_pos (hε _) _))))
  have hrhoe : rhoStar D kI.c₀ Gr.level ≤ D.eps Gr.level :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hcI.le).trans
      (mul_le_of_le_one_left (hε _).le hcIupper)
  refine ⟨pe, ?_, by rw [hGrlevel]; omega, hCaI, hCmI⟩
  intro hnatural hcertified
  refine { bw_eq := rfl
           alpha_eq := hDα
           q_eq := hDq
           base_eq := hDΛ
           profile_eq := hDζ
           stream := hseq
           natural := hnatural
           certified := hcertified
           level_pos := by rw [hGrlevel]; omega
           carrier_start := by rw [hGrlevel]; omega
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

/-- The successor geometry adapter has no remaining ingredient. -/
theorem successor_context_envelope_adapter
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (estimates : ∀ p, ContextEnvelopeEstimate p) :
    SuccessorContextEnvelopeAdapterStatement α s q ζ estimates :=
  successor_context_envelope_adapter_of_preparation α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ estimates
    (successor_context_envelope_preparation α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ estimates)

/-- Instantiate the single shared analytic producer on every retained successor. -/
theorem successor_envelopes_of_context
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccessorEnvelopesOfContextStatement α s q ζ := by
  let estimates (p : ContextEnvelopeParameters) := Classical.choice (Cauchy.context_stage_envelopes p)
  exact successor_envelopes_of_context_inputs α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ estimates
    (successor_context_envelope_adapter α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ estimates)

end AVRegularity.Construction.StageEnvelopes
end
end
