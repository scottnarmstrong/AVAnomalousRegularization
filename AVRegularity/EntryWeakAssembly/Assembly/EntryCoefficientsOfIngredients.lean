-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.KernelPricePlan
import AVRegularity.Proofs.WeakGen.WeakStageHistory
import AVRegularity.CycleReference.FluxFastDiscrepancy
import AVRegularity.Definitions.Finite.FiniteLiftBridge

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs.Assembly

/-! I10: the actual weak physical coefficients obey both kernel-price Schur bounds.
The common plan remains valid for every supplied cK in (0,1], and any witness inflation. -/

/-- All weak identities use the same paired-kernel width, irrespective of provenance. -/
theorem weak_kernel_constant_width {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D ScalarH Dm bw j₀) (P : ProvParams) (r : ℝ) (n : ℕ+)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    (G.kernelOf P (fun _ => isoPairedKernel r n) (fun _ => isoPairedKernel r n) v u γ).width = r := by
  unfold GenStage.kernelOf
  cases ((G.prov v u γ).tags P).kernel <;> rfl

/-- Exact I10 at a plan retaining all kernel and allocation constants. Its only refinements
are the common ledger constant and the uniform large-terminal threshold. -/
theorem weak_stage_kernel_prices (plan : WeakCoefficientPlan) (F : WeakWitnessInflation)
    (exports : WeakCoefficientCase (weakKernelPricePlan plan F) → SeedExports) :
    WeakStageKernelPriceStatement (weakKernelPricePlan plan F)
      (weakRootEncodingChoice (weakKernelPricePlan plan F) (fun c => F.factor c.inst.request)
        (fun c => F.one_le c.inst.request) exports) := by
  intro c w
  let x := c.inst
  let A := x.physical
  let R := x.request
  let k := (plan.constants R).kW
  let G := c.stage x.M
  let Gw := (weakRootEncodingChoice (weakKernelPricePlan plan F) (fun c => F.factor c.inst.request)
    (fun c => F.one_le c.inst.request) exports c).stage
  let e : CompIn G.comps ≃ CompIn Gw.comps := weakRootEquiv G.comps
  let ee : ∀ v u, G.fam.Γ v u ≃ Gw.fam.Γ (e v) (e u) :=
    relabelWeakEdge G (weakRootComps G.comps) (weakRootEquiv G.comps)
  let ν := x.D.κ x.M
  let ρ := rhoStar x.D k.c₀ x.M
  let r := x.D.termRW A.σw x.M
  let seedK : ℕ → KernelSpec := fun _ => isoPairedKernel r R.nW
  let V := weakKernelPhysicalData A R.sZ k.Ks
  let C := weakKernelPriceCost plan R
  have h128 : 128 ≤ A.Λ := (plan.baseThreshold_ge x.base).trans x.base_large
  have hΛ : 128 ≤ x.D.Λ := by rw [x.hΛ]; exact h128
  have hΛ1 : 1 ≤ x.D.Λ := (by decide : 1 ≤ 128).trans hΛ
  have hζ : IsFastProfile x.D.ζ := by rw [x.hζ]; exact x.base.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.hα, x.hq, x.hΛ, x.hζ, x.term]
    exact x.band
  have hε : 0 < x.D.eps x.M := Construction.Stream.ocEpsilon_pos hΛ1
  have hε' : 0 < x.D.eps (x.M + 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hε1 : x.D.eps x.M ≤ 1 := by
    simpa only [OCData.eps, x.hq, x.hΛ] using
      (Scales.epsilon_basic (m := x.M) x.base.hq.1 h128).2.1
  have hν : 0 < ν := by
    dsimp only [ν]
    exact CycleReference.bandChain_pos hΛ1 hζ hband (by rw [x.term])
  have hr : 0 < r := Real.rpow_pos_of_pos hε _
  have hre : r ≤ x.D.eps x.M := by
    change x.D.eps x.M ^ (1 + A.σw) ≤ _
    rw [Real.rpow_add hε, Real.rpow_one]
    exact mul_le_of_le_one_right hε.le (Real.rpow_le_one hε.le hε1 A.σw_pos.le)
  have hVs : V.threshold ≤ x.M := (le_max_left _ _).trans
    ((le_max_right _ _).trans x.level_large)
  have hSs : (weakStoredLedgerData A).threshold ≤ x.M := (le_max_right _ _).trans
    ((le_max_right _ _).trans x.level_large)
  have hhr : x.D.eps (x.M + 1) ≤ r := by
    simpa only [r, OCData.eps, OCData.termRW, x.hq, x.hΛ] using
      (weakStoredLedgerData A).price h128 x.M hSs
  have hmin : 0 ≤ min (x.D.eps x.M) (Real.sqrt (x.D.κ x.M /
      ocA x.D.α x.D.q x.D.Λ x.M)) := le_min hε.le (Real.sqrt_nonneg _)
  have hρ : 0 ≤ ρ := by
    dsimp only [ρ, rhoStar]
    rw [(plan.constants R).radius]
    exact mul_nonneg R.cK_pos.le hmin
  have hρe : ρ ≤ x.D.eps x.M := by
    dsimp only [ρ, rhoStar]
    rw [(plan.constants R).radius]
    exact (mul_le_mul_of_nonneg_right R.cK_le hmin).trans
      (by rw [one_mul]; exact min_le_left _ _)
  have hl := EntryWeakProofs.weakConstruction_level x.P x.menu x.M A.Jw 0
    r c.stage c.construction x.M le_rfl (Nat.le_add_right _ _)
  have hkt : x.D.kap Gw.level = ν := by
    change x.D.kap G.level = _
    rw [hl]
    rw [EntryWeakProofs.weakData_kap_terminal x.D x.M (by rw [x.term]), x.term]
  have hρt : rhoStar x.D k.c₀ Gw.level = ρ := by change rhoStar x.D k.c₀ G.level = _; rw [hl]
  have hstream : IsOCStreamSeq x.base.α x.base.q A.Λ x.base.ζ x.D.Φ := x.stream
  have hprod := V.bound h128 x.D (by rw [x.term]; exact hVs) x.hα x.hq x.hΛ x.hζ
    hstream hband x.Dm x.order x.j₀ c.stage x.P x.M R.sX 0 A.η₀ r x.term c.construction
    x.M le_rfl (by have := A.Jw_pos; omega)
  have horder := EntryWeakProofs.weakConstruction_output_maxOrder_bound x.P x.menu
    x.M A.Jw r 0 c.stage c.construction x.M le_rfl (by have := A.Jw_pos; omega)
  have he := (weak_encoding_transport (weakKernelPricePlan plan F)
    (fun c => F.factor c.inst.request) (fun c => F.one_le c.inst.request) exports c).1
  have hm := weakEncoding_marker A.Nw A.Jw A.η₀ _ _ G Gw e he w.law
  have htotal := (weakStoredLedgerData A).total h128 x.M hSs x.D x.hα x.hq x.hΛ
    x.term x.band x.Dm x.j₀ x.P R.sX R.sZ c.stage c.construction
  have hC : 0 ≤ C := weakKernelPriceCost_nonneg plan R
  dsimp only
  intro kk hkk weight hw
  have hw1 : weight = fun _ => 1 := by
    rcases hw with hw | hw
    · exact hw
    · rw [hw]; exact funext hm
  subst weight
  simp only [one_pow, div_one]
  change SchurBound _ (kernelSchurMatrix (x.D.kap Gw.level) (rhoStar x.D k.c₀ Gw.level)
    (Gw.mass w.law) kk x.Dm w.aM (w.a + A.T₀) k.cker
    (fun v u γ => (Gw.kernelOf x.P seedK seedK v u γ).width)
    (fun _ _ _ => ContinuousLinearMap.id ℝ ℝ) (fun v u γ d => Gw.physCoeff v u γ d.1))
  rw [hkt, hρt]
  have hprice (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
      (∑ d : ↥(Finset.Icc 2 x.Dm),
        (coefficientSeminorm ρ kk w.aM (w.a + A.T₀) (G.physCoeff v u γ d.1)).toReal *
          k.cker (d.1 - 2) / (ν * r ^ (d.1 - 2))) ≤ C * (G.fam.identity v u γ).record.size := by
    apply weak_kernel_identity_price (fun d => G.physCoeff v u γ d) ν V.C
      (G.fam.identity v u γ).record.size (x.D.eps (x.M + 1)) (x.D.eps x.M) r ρ k.cker
      (G.fam.identity v u γ).maxOrder (1 + A.Jw * A.Nw) x.Dm kk w.aM (w.a + A.T₀)
      hν V.nonneg (G.fam.identity v u γ).record.size_nonneg hε hε'.le hr hhr hre hρ hρe
      (horder v u γ)
    · intro d hd
      funext t y
      exact CycleJointProofs.constituentPhysical_zero_above_max G.fam
        (x.D.kap G.level) (x.D.eps G.level) (x.D.eps (G.level - 1)) G.actual v u γ d hd t y
    · intro d hd hdn
      exact hprod v u γ d kk hd hdn hkk w.aM (w.a + A.T₀)
  have hschur := weakRelabel_schur_of_stored A.Nw A.Jw A.η₀ G Gw e C hC
    (kernelSchurMatrix ν ρ (Gw.mass w.law) kk x.Dm w.aM (w.a + A.T₀) k.cker
      (fun v u γ => (Gw.kernelOf x.P seedK seedK v u γ).width)
      (fun _ _ _ => ContinuousLinearMap.id ℝ ℝ) (fun v u γ d => Gw.physCoeff v u γ d.1))
  have hpoint (v u : CompIn G.comps) :
      kernelSchurMatrix ν ρ (Gw.mass w.law) kk x.Dm w.aM (w.a + A.T₀) k.cker
        (fun v u γ => (Gw.kernelOf x.P seedK seedK v u γ).width)
        (fun _ _ _ => ContinuousLinearMap.id ℝ ℝ) (fun v u γ d => Gw.physCoeff v u γ d.1)
        (e v) (e u) ≤ C * Real.sqrt (weakMass x.D A.Nw A.Jw A.η₀ u.1 /
          weakMass x.D A.Nw A.Jw A.η₀ v.1) * ∑ γ : G.fam.Γ v u, (G.fam.identity v u γ).record.size := by
    unfold kernelSchurMatrix
    rw [weakEncoding_mass A.Nw A.Jw A.η₀ _ _ G Gw e he w.law w.rootMass u,
      weakEncoding_mass A.Nw A.Jw A.η₀ _ _ G Gw e he w.law w.rootMass v, ← (ee v u).sum_comp]
    dsimp only
    simp only [ContinuousLinearMap.norm_id, one_mul]
    have hp (γ : G.fam.Γ v u) (d : ℕ) :
        Gw.physCoeff (e v) (e u) (ee v u γ) d = G.physCoeff v u γ d :=
      weakScaledRootStage_physCoeff G (F.factor R) (F.one_le R) v u γ d
    simp_rw [hp]
    dsimp only [seedK]
    simp_rw [weak_kernel_constant_width]
    calc
      _ ≤ Real.sqrt _ * ∑ γ : G.fam.Γ v u, C * (G.fam.identity v u γ).record.size :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun γ _ => hprice v u γ) (Real.sqrt_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hs := hschur hpoint
  have hcost : C ≤ max 1 C * F.factor R :=
    (le_max_right _ _).trans (le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _))
      (F.one_le R))
  have hfinal : C * weakStoredTotal G A.Nw A.Jw A.η₀ ≤
      ((weakKernelPricePlan plan F).constants R).Cχ *
        x.D.eps x.M ^ weakChi x.base.α x.base.q A.η₀ := by
    calc
      _ ≤ C * ((weakStoredLedgerData A).C * x.D.eps x.M ^ weakChi x.base.α x.base.q A.η₀) :=
        mul_le_mul_of_nonneg_left htotal hC
      _ ≤ (max 1 C * F.factor R) *
          ((weakStoredLedgerData A).C * x.D.eps x.M ^ weakChi x.base.α x.base.q A.η₀) :=
        mul_le_mul_of_nonneg_right hcost (mul_nonneg (weakStoredLedgerData A).positive.le
          (Real.rpow_nonneg hε.le _))
      _ = _ := by change _ = ((max 1 C * F.factor R) * (weakStoredLedgerData A).C) * _; ring
  exact ⟨fun v => (hs.1 v).trans hfinal, fun u => (hs.2 u).trans hfinal⟩

end AVRegularity.WeakEntryProofs.Assembly
end

section
namespace AVRegularity.WeakEntryProofs.Assembly

/-! One plan and one encoded stage for the proved weak record, kernel and price ingredients.
Only request-dependent constants and thresholds are enlarged, before the ambient cap Dm. -/

section
open Homogenization AVRegularity.Providers.WeakGen

/-- First fix the kernel constants, then pay its physical prices and the common witness factor. -/
def weakCommonPlan (plan : WeakCoefficientPlan) (Kc : WeakConstFn) : WeakCoefficientPlan :=
  weakKernelPricePlan (weakKernelPlan plan) (weakGenInflation Kc)

/-- The common refinement retains the carrier constants of the carrier calculus and raises the level threshold. -/
theorem weakCommonPlan_complexContext (plan : WeakCoefficientPlan) (Kc : WeakConstFn)
    (hplan : WeakComplexContextPlanOK plan) : WeakComplexContextPlanOK (weakCommonPlan plan Kc) := by
  refine ⟨hplan.1, ?_⟩
  intro B A R j₀
  exact (hplan.2 R j₀).trans ((le_max_left _ _).trans (le_max_left _ _))

/-- The ingredient at the very same inflation used by the certificate bridge. -/
theorem weakCommonPlan_record_majorants (plan : WeakCoefficientPlan) (Kc : WeakConstFn) :
    WeakRecordMajorantStatement (weakCommonPlan plan Kc)
      (weakGenEncodingChoice (weakCommonPlan plan Kc) Kc) := by
  apply weak_record_majorants_of_budget (weakCommonPlan plan Kc) (weakGenInflation Kc)
  · intro B A R
    change (weakGenInflation Kc).factor R * (weakStoredLedgerData A).C ≤
      (max 1 (weakKernelPriceCost (weakKernelPlan plan) R) *
        (weakGenInflation Kc).factor R) * (weakStoredLedgerData A).C
    apply mul_le_mul_of_nonneg_right _ (weakStoredLedgerData A).positive.le
    exact le_mul_of_one_le_left (zero_le_one.trans ((weakGenInflation Kc).one_le R))
      (le_max_left _ _)
  · intro B A R j₀
    exact (le_max_right _ _).trans (le_max_right _ _)

/-- The kernel ingredient survives the price refinement, which changes neither kernel nor allocation data. -/
theorem weakCommonPlan_kernels (plan : WeakCoefficientPlan) (Kc : WeakConstFn) :
    WeakStageKernelsStatement (weakCommonPlan plan Kc)
      (weakGenEncodingChoice (weakCommonPlan plan Kc) Kc) := by
  apply weak_stage_kernels_of_plan (weakCommonPlan plan Kc)
  · intro B
    exact le_max_right _ _
  · intro B A R j₀
    exact (le_max_right _ _).trans (le_max_left _ _)
  · intro B A R
    rfl

/-- The kernel price ingredient is the price refinement's existing theorem, with the common certificate inflation. -/
theorem weakCommonPlan_kernel_prices (plan : WeakCoefficientPlan) (Kc : WeakConstFn) :
    WeakStageKernelPriceStatement (weakCommonPlan plan Kc)
      (weakGenEncodingChoice (weakCommonPlan plan Kc) Kc) :=
  weak_stage_kernel_prices (weakKernelPlan plan) (weakGenInflation Kc) (fun _ => noExports)
end

/-! Exact conditional assembly of the weak coefficient statement. The root encoding uses the request-uniform
certificate factor and no exports. The shift law and the size factor are discharged here. Slot transversality
and the former stage-generation/certificate leaves come from the one-passage certificate.
Existence uses the proved local passage and the joint downward induction with certification.
The elementary depth/order/record/mass/positivity clauses use their proofs.
The remaining ingredients are discharged at one common plan, with the same certificate inflation
and kernel constants as the remaining analytic leaves. The envelope ingredient is instantiated from the shared
context-envelope estimate using the proved weak adapters and pre-data WeakEnvPlanOK.
No ingredient assumes a whole stage invariant. -/

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity.EntryWeakProofs
open AVRegularity.WeakEntryProofs

/-- The exact coefficient statement, using the one-passage route and no exports.
The bound on Υ is a harmless choice of the existential carrier constants, used by the generation statement. -/
theorem entry_coefficients_of_ingredients
    (basePlan : WeakCoefficientPlan) (Kc : Providers.WeakGen.WeakConstFn)
    (hΥ : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A),
      1 ≤ (basePlan.constants R).Υ)
    (hplan : Providers.WeakGen.WeakComplexContextPlanOK basePlan)
    (hcert : Providers.WeakGen.WeakPassageCert1Statement (weakCommonPlan basePlan Kc) Kc)
    (hcontext : Construction.StageEnvelopes.ContextStageEnvelopesStatement)
    (henv : WeakEnvPlanOK (weakCommonPlan basePlan Kc) (weakEnvelopeEstimates hcontext))
    (hI11 : WeakStageQuietAtlasStatement (weakCommonPlan basePlan Kc)
      (weakGenEncodingChoice (weakCommonPlan basePlan Kc) Kc))
    (hI12 : WeakStageIndependenceStatement (weakCommonPlan basePlan Kc)
      (weakGenEncodingChoice (weakCommonPlan basePlan Kc) Kc))
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → L + 1 ≤ 2 * (nW : ℕ) →
      Lw + 5 ≤ Kw →
    ∀ cK : ℝ, 0 < cK → cK ≤ 1 →
    ∃ (CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams),
      (∃ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage) ∧
      ∀ stage : ℕ → GenStage D ScalarH Dm bw j₀, IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      ∃ (Gw : GenStage D ScalarH Dm bw j₀) (rootM rootR : ℕ → ℝ) (ι : CompIn (stage M).comps ≃ CompIn Gw.comps),
        IsWeakEncoding Nw Jw η₀ rootM rootR (stage M) Gw ι ∧ (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
      ∀ a aM : ℝ, a ≤ aM → aM ≤ a + 6 * Jw * ocTauPP α q Λ (M + 1) →
        IsWeakStage law P φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀)
          Gw aM := by
  let plan := weakCommonPlan basePlan Kc
  have hplan' : Providers.WeakGen.WeakComplexContextPlanOK plan := weakCommonPlan_complexContext basePlan Kc hplan
  have hΥ' : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakCoefficientRequest A), 1 ≤ (plan.constants R).Υ := hΥ
  have hI7 := weakCommonPlan_record_majorants basePlan Kc
  have hI9 := weakCommonPlan_kernels basePlan Kc
  have hI10 := weakCommonPlan_kernel_prices basePlan Kc
  have hLX : Providers.WeakGen.WeakPassageLiftsStatement plan :=
    Providers.WeakGen.weakPassageLifts (fun B =>
      (show 1 ≤ 128 by omega).trans (plan.baseThreshold_ge B))
  have hex : Providers.WeakGen.WeakPassageExistsStatement plan :=
    Providers.WeakGen.weakPassageExists hplan'.2 hLX
  have hI6 := Providers.WeakGen.weakPassageCert_of_one hcert
  have hI8 := weak_stage_envelopes plan Kc hplan' (weakEnvelopeEstimates hcontext) henv hI6
  have hI5 : Providers.WeakGen.WeakPassageGenStatement plan := by
    intro c i hi hiJ _
    have hW := Providers.WeakGen.weakCertified_stage c hI6
      (c.inst.M + c.inst.physical.Jw - (i - 1)) (by omega)
    rw [show c.inst.M + c.inst.physical.Jw - (c.inst.M + c.inst.physical.Jw - (i - 1)) = i - 1
      by omega] at hW
    exact hW.2.weakHolGen
  let encode := weakGenEncodingChoice plan Kc
  have hI4 : WeakEncodingTransportStatement plan encode :=
    weak_encoding_transport plan _ _ (fun _ => Providers.WeakGen.noExports)
  let B : WeakCoefficientBase := ⟨α, s, hα₀, hα₁, hs₀, hs₁, q, hq, ζ, hζ⟩
  refine ⟨plan.baseThreshold B, plan.baseThreshold_ge B, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφsmooth hφnonneg hφmass hφsupport bw hbw hbwsmall
    Jw τ T₀ Pw η₀ hJ hτ hτT hPw hη hηsmall Nw Rw Lw hN hLw σw hσ hσsmall
  let A : WeakCoefficientPhysical B :=
    ⟨Λ, φ₀, hφ₀, hφsmooth, hφnonneg, hφmass, hφsupport, bw, hbw, hbwsmall,
      Jw, τ, T₀, Pw, η₀, hJ, hτ, hτT, hPw, hη, hηsmall, Nw, Rw, Lw, hN, hLw,
      σw, hσ, hσsmall⟩
  refine ⟨plan.momentThreshold A, ?_⟩
  intro L Kw sX sZ nW kReq hG0 hL hkernel hKw cK hcK hcK1
  let R : WeakCoefficientRequest A := ⟨L, Kw, sX, sZ, nW, kReq, hG0, hkernel, hKw, cK, hcK, hcK1⟩
  let C := plan.constants R
  refine ⟨C.CK, C.CL, C.Cχ, C.Cread, C.Cid, C.kW, C.radius, C.allocation,
    C.CH, C.Υ, C.history_one_le, C.chain_pos, ?_⟩
  intro j₀ hcarrier
  refine ⟨plan.levelThreshold R j₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm Dm hDm P
  let x : WeakCoefficientInstance plan :=
    ⟨B, A, R, hΛ, hL, j₀, hcarrier, M, hM, D, hDα, hDq, hDΛ, hDζ,
      hstream, hband, hterm, Dm, hDm, P⟩
  refine ⟨Providers.WeakGen.weakConstruction_exists hplan' hex hcert x, ?_⟩
  intro stage hc
  let c : WeakCoefficientCase plan := ⟨x, stage, hc⟩
  let E := encode c
  let rootM := weakCaseRootMass c
  let rootR := weakCaseRootReadout c
  obtain ⟨he, hnatural, htags, hshift, hslot⟩ := hI4 c
  have hbase : 1 ≤ D.Λ := by
    rw [hDΛ]
    exact (show 1 ≤ 128 by omega).trans ((plan.baseThreshold_ge B).trans hΛ)
  have hεpos : ∀ i, 0 < D.eps i := fun _ => Construction.Stream.ocEpsilon_pos hbase
  have hrootM : ∀ r, 0 < rootM r :=
    weakRootWeight_pos _ _ (fun v => weakMass_pos D Nw Jw η₀ hN hJ hεpos v.1)
  have hrootR : ∀ r, 0 < rootR r :=
    weakRootWeight_pos _ _ (fun v => weakReadoutWeight_pos D η₀ hεpos v.1)
  refine ⟨E.stage, rootM, rootR, E.relabel, he, hrootM, hrootR, ?_⟩
  intro law hlawM hlawR a aM ha haM
  let w : WeakCoefficientWindow c := ⟨law, hlawM, hlawR, a, aM, ha, haM⟩
  have hshift0 := weak_stage_shift_laws plan c M le_rfl (Nat.le_add_right M Jw)
  have hslot0 := weakGen_stage_slot_laws plan hΥ' hI5 c M le_rfl (Nat.le_add_right M Jw)
  have hgenerated := weakGenEncoding_expr plan Kc hI5 c
  have hctx := weakGenEncoding_certificate plan Kc hI6 c
  obtain ⟨hn, hr, hcol, hmn, hmr, hmc, hledger⟩ := hI7 c w
  have henv := hI8 c w
  have hinvariant : IsStageInvariant law P
      (fun _ => isoPairedKernel (D.termRW σw M) nW)
      (fun _ => isoPairedKernel (D.termRW σw M) nW) φ₀ hφ₀ (M + Jw) C.kW aM (a + T₀)
      (C.Cχ * D.eps M ^ weakChi α q η₀) (C.Cχ * D.eps M ^ weakChi α q η₀) E.stage := by
    have hn0 := weakConstruction_output_natural P x.menu M Jw 0 (D.termRW σw M)
      stage hc M le_rfl (by omega)
    have ht0 := (hc.2.2 (M + 1) (by omega) (by omega)).2
    -- the carried history invariant, from the construction and the encoding
    have hhist : StageHistoryInvariant E.stage (M + Jw) := by
      have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
      have hκD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
        rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
      have hcarD : IsCarrierStart D.α D.q D.Λ bw C.CH C.Υ j₀ := by
        rw [hDα, hDq, hDΛ]; exact hcarrier
      exact Providers.WeakGen.weakStage_stageHistory hbase hζD hκD hbw C.history_one_le (hΥ' R)
        hcarD hc he
    refine ⟨hnatural hn0, htags (by simpa only [Nat.add_sub_cancel] using ht0),
      hgenerated.1, hshift hshift0, hslot hslot0, hctx, ?_, hledger,
      hI9 c w, hI10 c w, hI11 c w, (hI12 c w).1, (hI12 c w).2, hhist⟩
    intro K hK
    have h := henv.1 K hK
    exact ⟨⟨hn, hr, hcol, h.1.1, h.1.2⟩, ⟨hmn, hmr, hmc, h.2.1, h.2.2⟩⟩
  let Mn : WeakMenu := ⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩
  have hε : ∀ i, 0 ≤ D.eps i ∧ D.eps i ≤ 1 :=
    fun i => ⟨(hεpos i).le, ocEpsilon_le_one hbase i⟩
  have hdepth := weakEncoding_depth Nw Jw η₀ rootM rootR (stage M) E.stage E.relabel he
    (Jw * Rw) (weakConstruction_depth P Mn M Jw 0 (D.termRW σw M) stage hc M le_rfl (by omega))
  have horder := weakConstruction_output_maxOrder_bound P Mn M Jw (D.termRW σw M) 0
    stage hc M le_rfl (by omega)
  have hrecords := weakEncoding_orders_records Nw Jw η₀ rootM rootR (stage M) E.stage E.relabel he
    (1 + Jw * Nw) (D.eps (M + 1)) (D.termRW σw M) horder
    (weakConstruction_output_records P Mn M Jw 0 (D.termRW σw M) stage hc hJ)
  have hmass := weakEncoding_mass_sums_le P Mn M Jw 0 (D.termRW σw M) stage hc hN hJ
    hη.le hε rootM rootR E.stage E.relabel he law hlawM hlawR
  have hroots : ∀ v : CompIn E.stage.comps, v.1.births = [] := by
    intro v
    obtain ⟨v, rfl⟩ := E.relabel.surjective v
    exact he.2.1 v
  refine ⟨ha, ?_, ?_, hdepth, hroots, ⟨hrecords.2.2, hgenerated.2, henv.2⟩,
    ?_, hmass.1, hmass.2, hinvariant⟩
  · simpa only [hDα, hDq, hDΛ] using haM
  · exact he.1.trans (weakConstruction_level P Mn M Jw 0 (D.termRW σw M) stage hc
      M le_rfl (by omega))
  · intro v u γ
    have hr := hrecords.2.1 v u γ
    refine ⟨hrecords.1 v u γ, hr.2, ?_,
      weakEncoding_map_norm_le_one Nw Jw η₀ rootM rootR (stage M) E.stage E.relabel he
        (weakConstruction_identity_map_norm_le_one P Mn M Jw 0 (D.termRW σw M) stage hc
          M le_rfl (by omega)) v u γ⟩
    rw [hr.1]
    calc
      D.eps (M + 1) = 1 * D.eps (M + 1) := (one_mul _).symm
      _ ≤ C.CL * D.eps (M + 1) := mul_le_mul_of_nonneg_right C.length_one_le (hε _).1
end

end AVRegularity.WeakEntryProofs.Assembly
end
