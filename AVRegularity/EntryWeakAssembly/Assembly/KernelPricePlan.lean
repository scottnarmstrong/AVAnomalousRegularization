-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.KernelPriceTransport
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
public import AVRegularity.Proofs.WeakGen.InhFacts
public import AVRegularity.Construction.StageEnvelopes.Assembly
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.EntryWeakAssembly.NativeFullLiftRankCentering
import AVRegularity.EntryWeak.UniformWeakPhysicalCoefficientProduction
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.CycleReference.FluxFastDiscrepancy
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup

section
section
/-! I7 at a common, request-uniform witness inflation. Registry choices remain free for I5. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly

/-- The leaf certificate may choose its inflation after requests, before carrier/flow/stage data. -/
structure WeakWitnessInflation where
  factor : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakCoefficientRequest A → ℝ
  one_le : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A),
    1 ≤ factor R

/-- Record majorants at any common plan whose budget and threshold dominate the stored ledger. -/
theorem weak_record_majorants_of_budget (plan : WeakCoefficientPlan) (F : WeakWitnessInflation)
    (hbudget : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakCoefficientRequest A), F.factor R * (weakStoredLedgerData A).C ≤
        (plan.constants R).Cχ)
    (hthreshold : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakCoefficientRequest A) j₀, (weakStoredLedgerData A).threshold ≤
        plan.levelThreshold R j₀)
    (exports : WeakCoefficientCase plan → SeedExports) :
    WeakRecordMajorantStatement plan
      (weakRootEncodingChoice plan (fun c => F.factor c.inst.request)
        (fun c => F.one_le c.inst.request) exports) := by
  intro c w
  let x := c.inst
  let A := x.physical
  let G := c.stage x.M
  let C := F.factor x.request
  let S := (weakStoredLedgerData A).C
  let e := weakRootEquiv G.comps
  let Gw := (weakRootEncodingChoice plan (fun c => F.factor c.inst.request)
    (fun c => F.one_le c.inst.request) exports c).stage
  have hC : 1 ≤ C := F.one_le x.request
  have he := (weak_encoding_transport plan (fun c => F.factor c.inst.request)
    (fun c => F.one_le c.inst.request) exports c).1
  have h128 : 128 ≤ A.Λ := (plan.baseThreshold_ge x.base).trans x.base_large
  have hDΛ : 1 ≤ x.D.Λ := by
    rw [x.hΛ]
    exact (by decide : 1 ≤ 128).trans h128
  have ht : (weakStoredLedgerData A).threshold ≤ x.M := (hthreshold x.request x.j₀).trans x.level_large
  have htotal : weakStoredTotal G A.Nw A.Jw A.η₀ ≤
      S * x.D.eps x.M ^ weakChi x.base.α x.base.q A.η₀ :=
    (weakStoredLedgerData A).total h128 x.M ht x.D x.hα x.hq x.hΛ x.term x.band
      x.Dm x.j₀ x.P x.request.sX x.request.sZ c.stage c.construction
  let ee := relabelWeakEdge G (weakRootComps G.comps) e
  have hm (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
      (Gw.fam.identity (e v) (e u) (ee v u γ)).map = (G.fam.identity v u γ).map := by
    change ((relabelWeakStage G (weakRootComps G.comps) e).fam.identity (e v) (e u) (ee v u γ)).map = _
    rw [relabelWeakStage_identity]
  have hs (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
      (Gw.fam.identity (e v) (e u) (ee v u γ)).record.size = C * (G.fam.identity v u γ).record.size := by
    change C * ((relabelWeakStage G (weakRootComps G.comps) e).fam.identity
      (e v) (e u) (ee v u γ)).record.size = _
    rw [relabelWeakStage_identity]
  have hp (v u : CompIn Gw.comps) (γ : Gw.fam.Γ v u) :
      constituentPrice (Gw.fam.identity v u γ).record = 1 := by
    obtain ⟨v, rfl⟩ := e.surjective v
    obtain ⟨u, rfl⟩ := e.surjective u
    obtain ⟨γ, rfl⟩ := (ee v u).surjective γ
    have hr := weakConstruction_output_records x.P x.menu x.M A.Jw 0
      (x.D.termRW A.σw x.M) c.stage c.construction A.Jw_pos v u γ
    have hlen : (Gw.fam.identity (e v) (e u) (ee v u γ)).record.length = x.D.eps (x.M + 1) := by
      change ((relabelWeakStage G (weakRootComps G.comps) e).fam.identity
        (e v) (e u) (ee v u γ)).record.length = _
      rw [relabelWeakStage_identity]
      exact hr.1
    have hwid : (Gw.fam.identity (e v) (e u) (ee v u γ)).record.width = x.D.termRW A.σw x.M := by
      change ((relabelWeakStage G (weakRootComps G.comps) e).fam.identity
        (e v) (e u) (ee v u γ)).record.width = _
      rw [relabelWeakStage_identity]
      exact hr.2
    have hε : 0 < x.D.eps x.M := Construction.Stream.ocEpsilon_pos hDΛ
    have hwidth : 0 < x.D.termRW A.σw x.M := Real.rpow_pos_of_pos hε _
    have hratio : x.D.eps (x.M + 1) / x.D.termRW A.σw x.M ≤ 1 := by
      apply (div_le_one hwidth).mpr
      simpa only [OCData.eps, OCData.termRW, x.hq, x.hΛ] using
        (weakStoredLedgerData A).price h128 x.M ht
    unfold constituentPrice
    rw [hlen, hwid]
    exact max_eq_left (pow_le_one₀ (div_nonneg
      (Construction.Stream.ocEpsilon_pos hDΛ).le hwidth.le) hratio)
  have hmap := EntryWeakProofs.weakConstruction_identity_map_norm_le_one x.P x.menu x.M A.Jw 0
    (x.D.termRW A.σw x.M) c.stage c.construction x.M le_rfl (by have := A.Jw_pos; omega)
  have hmatrix := weakEncoding_majorant_total A.Nw A.Jw A.η₀ (weakCaseRootMass c)
    (weakCaseRootReadout c) G Gw e he w.law w.rootMass C hC ee hm hs hmap
  have hε : 0 < x.D.eps x.M := Construction.Stream.ocEpsilon_pos hDΛ
  have hbound : (∑ v, ∑ u, recordMajorant (Gw.mass w.law) Gw.fam v u) ≤
      (C * S) * x.D.eps x.M ^ weakChi x.base.α x.base.q A.η₀ := by
    exact hmatrix.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left htotal (zero_lt_one.trans_le hC).le)
  have hcost : C * S ≤ (plan.constants x.request).Cχ := hbudget x.request
  have hcost0 : 0 ≤ (plan.constants x.request).Cχ :=
    (mul_nonneg (zero_lt_one.trans_le hC).le (weakStoredLedgerData A).positive.le).trans hcost
  exact weakMajorantBudget_of_total Gw w.law _
    (mul_nonneg hcost0 (Real.rpow_nonneg hε.le _))
    (weakEncoding_marker A.Nw A.Jw A.η₀ _ _ G Gw e he w.law) hp
    (hbound.trans (mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hε.le _)))

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! Select the kernel constants for every requested radius before the carrier and stage data. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly
open MeasureTheory Homogenization AVRegularity.Sobolev

/-- A base threshold for the uniform width ledger. -/
def weakKernelBaseThreshold (B : WeakCoefficientBase) : ℕ :=
  (exists_weak_kernel_width_budget B).choose

theorem weakKernelBaseThreshold_ge (B : WeakCoefficientBase) :
    128 ≤ weakKernelBaseThreshold B := (exists_weak_kernel_width_budget B).choose_spec.1

/-- Request constants with their elementary width and regularizer certificates. The width
certificate only applies above the base threshold, exactly as instances of the plan do. -/
structure WeakKernelRequestData {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakCoefficientRequest A) where
  Cwid : ℝ
  Cwid_pos : 0 < Cwid
  threshold : ℕ
  bounds : weakKernelBaseThreshold B ≤ A.Λ → ∀ M, threshold ≤ M → ∀ κ,
    IsOCBandChain B.α B.q A.Λ B.ζ M κ →
    ocEpsilon B.q A.Λ M ^ (1 + A.σw) ≤
      Cwid * (R.cK * min (ocEpsilon B.q A.Λ M) (Real.sqrt (κ M / ocA B.α B.q A.Λ M))) *
        ocEpsilon B.q A.Λ M ^ (A.σw / 2) ∧
    ocEpsilon B.q A.Λ M ^ (1 + A.σw) ≤
      Cwid * Real.sqrt (κ (M - 1) * ocTauPP B.α B.q A.Λ M) *
        ocEpsilon B.q A.Λ (M - 1) ^ (B.q * (1 + A.σw) - 1 - ocC B.α B.q)
  cker : ℕ → ℝ
  cker_nonneg : ∀ j, 0 ≤ cker j
  regularizer : ∀ r : ℝ, 0 < r → ∀ ρ a b k Dm,
    IsSpatialRegularizerTorus (G := ℝ) ρ k Dm a b cker r ((isoPairedKernel r R.nW).op A.φ₀ A.hφ₀)

/-- Existence uses only the scale and paired-kernel results. -/
theorem exists_weakKernelRequestData {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakCoefficientRequest A) : Nonempty (WeakKernelRequestData R) := by
  obtain ⟨cker, hcker, hr⟩ := exists_isoPairedKernel_regularizer_constants A.φ₀
    (Providers.hasCompactSupport_of_unitBall A.support) A.smooth A.hφ₀ R.nW
  by_cases hΛ : weakKernelBaseThreshold B ≤ A.Λ
  · obtain ⟨W⟩ := (exists_weak_kernel_width_budget B).choose_spec.2 A.Λ hΛ
      A.σw R.cK A.σw_pos R.cK_pos
    exact ⟨⟨W.C, W.positive, W.threshold, fun _ => W.bounds, cker, hcker, hr⟩⟩
  · exact ⟨⟨1, zero_lt_one, 0, fun hh => (hΛ hh).elim, cker, hcker, hr⟩⟩

def weakKernelRequestData {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakCoefficientRequest A) : WeakKernelRequestData R :=
  Classical.choice (exists_weakKernelRequestData R)

/-- The kernel ingredient changes only its own invariant constants; requests retain their reserve allocation
and supplied molecular radius. The other leaves can share this explicit refinement. -/
def weakKernelConstants {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (plan : WeakCoefficientPlan) (R : WeakCoefficientRequest A) : WeakCoefficientConstants R := by
  let C := plan.constants R
  let W := weakKernelRequestData R
  exact
    { C with
      kW := { C.kW with
        cr := 1
        Γk := 2
        Cwid := W.Cwid
        σf := A.σw / 2
        lamC := B.q * (1 + A.σw) - 1 - ocC B.α B.q
        cker := W.cker
        Lker := R.L }
      radius := C.radius
      allocation := ⟨C.allocation.1, C.allocation.2.1, C.allocation.2.2.1,
        C.allocation.2.2.2.1, C.allocation.2.2.2.2.1, C.allocation.2.2.2.2.2.1,
        C.allocation.2.2.2.2.2.2.1, C.allocation.2.2.2.2.2.2.2.1,
        C.allocation.2.2.2.2.2.2.2.2.1, le_rfl⟩ }

/-- A plan refinement valid for every cK in (0,1]. No flow or stage enters its constants. -/
def weakKernelPlan (plan : WeakCoefficientPlan) : WeakCoefficientPlan where
  baseThreshold B := max (plan.baseThreshold B) (weakKernelBaseThreshold B)
  baseThreshold_ge B := (plan.baseThreshold_ge B).trans (le_max_left _ _)
  momentThreshold := plan.momentThreshold
  constants := weakKernelConstants plan
  levelThreshold R j₀ := max (plan.levelThreshold R j₀) (weakKernelRequestData R).threshold

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! Original weak record lengths fit in every prescribed molecular radius at large levels.
The threshold depends on the request, including cK, and precedes Dm and the band chain. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly
open Filter Topology

theorem exists_weak_envelope_length_threshold {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A)
    (hΛ : weakKernelBaseThreshold B ≤ A.Λ) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∀ κ, IsOCBandChain B.α B.q A.Λ B.ζ M κ →
      ocEpsilon B.q A.Λ (M + 1) ≤
        R.cK * min (ocEpsilon B.q A.Λ M)
          (Real.sqrt (κ M / ocA B.α B.q A.Λ M)) := by
  let W := weakKernelRequestData R
  have h128 := (weakKernelBaseThreshold_ge B).trans hΛ
  have hσ : A.σw < B.q - 1 := A.σw_small.trans_le (min_le_right _ _)
  have he : 0 < B.q - 1 - A.σw / 2 := by linarith [A.σw_pos]
  have hWpos : 0 < W.Cwid := W.Cwid_pos
  have ht := (EntryScales.epsilon_rpow_tendsto_zero B.hq.1 h128 he).eventually
    (gt_mem_nhds (by positivity : 0 < (2 * W.Cwid)⁻¹))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  refine ⟨max N W.threshold, fun M hM κ hκ => ?_⟩
  let e := ocEpsilon B.q A.Λ M
  let ρ := R.cK * min e (Real.sqrt (κ M / ocA B.α B.q A.Λ M))
  have he0 : 0 < e := Construction.Stream.ocEpsilon_pos (by omega)
  have hW := (W.bounds hΛ M ((le_max_right _ _).trans hM) κ hκ).1
  have hsplit : e ^ (1 + A.σw) = e ^ (1 + A.σw / 2) * e ^ (A.σw / 2) := by
    rw [← Real.rpow_add he0]; congr 1; ring
  have hρ : e ^ (1 + A.σw / 2) ≤ W.Cwid * ρ := by
    change e ^ (1 + A.σw) ≤ W.Cwid * ρ * e ^ (A.σw / 2) at hW
    rw [hsplit] at hW
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos he0 _)).mp hW
  have hsmall : 2 * W.Cwid * e ^ (B.q - 1 - A.σw / 2) ≤ 1 := by
    have hh := (hN M ((le_max_left _ _).trans hM)).le
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq
      (mul_inv_cancel₀ (by positivity))
  have hρpos : 0 < ρ := pos_of_mul_pos_right
    ((Real.rpow_pos_of_pos he0 _).trans_le hρ) W.Cwid_pos.le
  calc
    ocEpsilon B.q A.Λ (M + 1) ≤ 2 * e ^ B.q := by
      simpa only [Nat.add_sub_cancel] using
        Scales.epsilon_q_step B.hq.1 B.hq.2.1 h128 (by omega : 1 ≤ M + 1)
    _ = 2 * e ^ (B.q - 1 - A.σw / 2) * e ^ (1 + A.σw / 2) := by
      rw [mul_assoc, ← Real.rpow_add he0]; congr 2; ring
    _ ≤ 2 * e ^ (B.q - 1 - A.σw / 2) * (W.Cwid * ρ) :=
      mul_le_mul_of_nonneg_left hρ (by positivity)
    _ = (2 * W.Cwid * e ^ (B.q - 1 - A.σw / 2)) * ρ := by ring
    _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hsmall hρpos.le
    _ = ρ := one_mul _

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! I9 for every supplied cK in (0,1], at the same rerooting used by I4. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs

/-- The elementary kernel plan closes the exact I9 proposition. Neither the witness inflation
nor the export registry is restricted, so the quantitative analysis can share this encoding. -/
theorem weak_stage_kernels_of_plan (plan : WeakCoefficientPlan)
    (hbase : ∀ B, weakKernelBaseThreshold B ≤ plan.baseThreshold B)
    (hlevel : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakCoefficientRequest A) j₀, (weakKernelRequestData R).threshold ≤
        plan.levelThreshold R j₀)
    (hkernel : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakCoefficientRequest A), (plan.constants R).kW = (weakKernelConstants plan R).kW)
    (Cθ : WeakCoefficientCase plan → ℝ) (hCθ : ∀ c, 1 ≤ Cθ c)
    (exports : WeakCoefficientCase plan → SeedExports) :
    WeakStageKernelsStatement plan
      (weakRootEncodingChoice plan Cθ hCθ exports) := by
  intro c w
  dsimp only
  let x := c.inst
  let W := weakKernelRequestData x.request
  let G := (weakRootEncodingChoice plan Cθ hCθ exports c).stage
  let rW := x.D.termRW x.physical.σw x.M
  let seedK : ℕ → KernelSpec := fun _ => isoPairedKernel rW x.request.nW
  have he := (weak_encoding_transport plan Cθ hCθ exports c).1
  have hl : G.level = x.M := he.1.trans
    (weakConstruction_level x.P x.menu x.M x.physical.Jw 0 rW c.stage c.construction
      x.M le_rfl (by omega))
  have ho := weakConstruction_output_maxOrder_bound x.P x.menu x.M x.physical.Jw rW 0
    c.stage c.construction x.M le_rfl (by have := x.physical.Jw_pos; omega)
  have hr := weakEncoding_orders_records x.physical.Nw x.physical.Jw x.physical.η₀
    (weakCaseRootMass c) (weakCaseRootReadout c) (c.stage x.M) G
    (weakRootEquiv (c.stage x.M).comps) he (1 + x.physical.Jw * x.physical.Nw)
    (x.D.eps (x.M + 1)) rW ho
    (weakConstruction_output_records x.P x.menu x.M x.physical.Jw 0 rW c.stage
      c.construction x.physical.Jw_pos)
  have hb := W.bounds ((hbase x.base).trans x.base_large)
    x.M ((hlevel x.request x.j₀).trans x.level_large) x.D.κ x.band
  have hfine : rW ≤ (plan.constants x.request).kW.Cwid *
      rhoStar x.D (plan.constants x.request).kW.c₀ G.level *
        x.D.eps G.level ^ (plan.constants x.request).kW.σf := by
    rw [hl]
    rw [hkernel x.request]
    change rW ≤ W.Cwid * rhoStar x.D (plan.constants x.request).kW.c₀ x.M *
      x.D.eps x.M ^ (x.physical.σw / 2)
    rw [(plan.constants x.request).radius]
    simpa only [rW, OCData.termRW, OCData.eps, rhoStar, x.hα, x.hq, x.hΛ] using hb.1
  have hcoarse : rW ≤ (plan.constants x.request).kW.Cwid *
      rhoEnh x.D (plan.constants x.request).kW.cr G.level *
        x.D.eps (G.level - 1) ^ (plan.constants x.request).kW.lamC := by
    rw [hl]
    rw [hkernel x.request]
    change rW ≤ W.Cwid * rhoEnh x.D 1 x.M *
      x.D.eps (x.M - 1) ^ (x.base.q * (1 + x.physical.σw) - 1 - ocC x.base.α x.base.q)
    simpa only [rW, OCData.termRW, OCData.eps, rhoEnh, one_mul, x.hα, x.hq, x.hΛ] using hb.2
  have hΛD : 128 ≤ x.D.Λ := by
    rw [x.hΛ]
    exact (plan.baseThreshold_ge x.base).trans x.base_large
  have hrW : 0 < rW := Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega)) _
  have hk (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
      G.kernelOf x.P seedK seedK v u γ = isoPairedKernel rW x.request.nW := by
    unfold GenStage.kernelOf
    split <;> rfl
  rw [hkernel x.request] at hfine hcoarse
  intro v u γ
  change (G.kernelOf x.P seedK seedK v u γ).IsAdmissible _ _ ∧ _
  rw [hk, hkernel x.request]
  refine ⟨isoPairedKernel_isAdmissible rW x.request.nW x.request.L x.request.kernel_order,
    (hr.2.1 v u γ).2.symm, (hr.2.1 v u γ).2.trans_le hfine,
    (hr.2.1 v u γ).2.trans_le hcoarse, ?_⟩
  intro ρ _ k _
  have hsys : G.sysS x.P seedK seedK x.physical.φ₀ x.physical.hφ₀ v u γ =
      (isoPairedKernel rW x.request.nW).op x.physical.φ₀ x.physical.hφ₀ := by
    funext t
    change (G.kernelOf x.P seedK seedK v u γ).op _ _ t = _
    rw [hk]
  rw [hsys]
  exact W.regularizer rW hrW ρ w.aM (w.a + x.physical.T₀) k x.Dm

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! Use the two passage statements at the same inflated root encoding as the size-factor and certificate ingredients. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly
open AVRegularity.Providers.WeakGen Homogenization

/-- The iterated passage constant is request-uniform. Taking the maximum with one enforces
the lower bound even if the passage constant map takes the value zero. -/
def weakGenInflation (Kc : WeakConstFn) : WeakWitnessInflation where
  factor {_B} {A} R := max 1 (2 ^ (2 + A.Jw * A.Nw) * (Kc R)^[A.Jw] 1)
  one_le _ := le_max_left _ _

/-- The shared encoding choice uses no exports and the uniform inflated witnesses. -/
def weakGenEncodingChoice (plan : WeakCoefficientPlan) (Kc : WeakConstFn) :
    WeakCoefficientEncodingChoice plan :=
  weakRootEncodingChoice plan (fun c => (weakGenInflation Kc).factor c.inst.request)
    (fun c => (weakGenInflation Kc).one_le c.inst.request) (fun _ => noExports)

/-- The concrete rerooting supplies exactly the correspondence required by the certificate assembly. -/
theorem weakGenEncodingChoice_corr (plan : WeakCoefficientPlan) (Kc : WeakConstFn)
    (c : WeakCoefficientCase plan) :
    WeakStageCorr (c.stage c.inst.M) (weakGenEncodingChoice plan Kc c).stage (weakCertFactor Kc c) := by
  let G := c.stage c.inst.M
  let e := weakRootEquiv G.comps
  let C := (weakGenInflation Kc).factor c.inst.request
  refine ⟨rfl, e, relabelWeakEdge G _ e, fun v u γ => ?_⟩
  have hid := relabelWeakStage_identity G (weakRootComps G.comps) e v u γ
  refine ⟨?_, ?_, ?_, ?_⟩
  · change weakCertFactor Kc c * (G.fam.identity v u γ).record.size ≤
      C * ((relabelWeakStage G _ e).fam.identity (e v) (e u) (relabelWeakEdge G _ e v u γ)).record.size
    rw [hid]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (G.fam.identity v u γ).record.size_nonneg
  · change ((relabelWeakStage G _ e).fam.identity (e v) (e u) (relabelWeakEdge G _ e v u γ)).record.length = _
    rw [hid]
  · change ((relabelWeakStage G _ e).fam.identity (e v) (e u) (relabelWeakEdge G _ e v u γ)).maxOrder = _
    rw [hid]
  · intro p ctx ctx' hctx d I t X z
    have heq : ctx = ctx' := Subtype.ext hctx
    subst ctx'
    exact congrFun (congrFun (congrFun (congrFun (congrFun
      (relabelWeakStage_flux G _ e v u γ p ctx) d) I) t) X) z

/-- The generation ingredient of the old assembly is discharged by the passage-generation statement. -/
theorem weakGenEncoding_expr (plan : WeakCoefficientPlan) (Kc : WeakConstFn)
    (hgen : WeakPassageGenStatement plan) :
    WeakStageExprStatement plan (weakGenEncodingChoice plan Kc) := by
  apply weakStageExpr_of_ingredients _ hgen
    (weak_encoding_transport plan _ _ (fun _ => noExports))
  intro c i p e he
  exact he

/-- The certificate ingredient of the old assembly is discharged by the passage-certificate statement. -/
theorem weakGenEncoding_certificate (plan : WeakCoefficientPlan) (Kc : WeakConstFn)
    (hcert : WeakPassageCertStatement plan Kc) :
    WeakStageCertificateStatement plan (weakGenEncodingChoice plan Kc) := by
  apply weakStageCertificate_of_ingredients _ Kc hcert
  intro c
  exact weakGenEncodingChoice_corr plan Kc c

/-- The generated route supplies the slot half of the shift law at every stage. This is only composition
with the generation statement, with its empty export registry; no weak slot-transport proof is needed. -/
theorem weakGen_stage_slot_laws (plan : WeakCoefficientPlan)
    (hΥ : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A),
      1 ≤ (plan.constants R).Υ)
    (hgen : WeakPassageGenStatement plan) (c : WeakCoefficientCase plan)
    (i : ℕ) (hi : c.inst.M ≤ i) (hit : i ≤ c.inst.M + c.inst.physical.Jw) :
    (c.stage i).IsSlotTransverse := by
  have hG := weakHolGen_stage c hgen (c.inst.M + c.inst.physical.Jw - i) (by omega)
  rw [show c.inst.M + c.inst.physical.Jw - (c.inst.M + c.inst.physical.Jw - i) = i by omega] at hG
  have hΛ : 1 ≤ c.inst.D.Λ := by
    rw [c.inst.hΛ]
    exact (by decide : 1 ≤ 128).trans ((plan.baseThreshold_ge c.inst.base).trans c.inst.base_large)
  have hζ : IsFastProfile c.inst.D.ζ := by rw [c.inst.hζ]; exact c.inst.base.hζ
  have hstart (k : ℕ) (hk : c.inst.j₀ ≤ k + 1) :
      2 * ocA c.inst.D.α c.inst.D.q c.inst.D.Λ k * ocTauPP c.inst.D.α c.inst.D.q c.inst.D.Λ (k + 1) ≤
        c.inst.physical.bw / (64 * (8 * Real.pi ^ 2)) := by
    have hA (k : ℕ) : 0 ≤ ocA c.inst.base.α c.inst.base.q c.inst.physical.Λ k := by
      apply Real.rpow_nonneg
      unfold ocEpsilon
      split <;> positivity
    have hT (k : ℕ) : 0 ≤ ocTauPP c.inst.base.α c.inst.base.q c.inst.physical.Λ k := by
      unfold ocTauPP
      positivity
    have hcarrier := c.inst.carrier.mono hA hT (plan.constants c.inst.request).history_one_le
      (hΥ c.inst.request) zero_le_one zero_le_one
    have hs := hcarrier.1 k hk
    simpa only [mul_one, c.inst.hα, c.inst.hq, c.inst.hΛ] using hs
  intro p ctx v u γ d I t ht X z s
  funext k
  obtain ⟨f, _F, hf, hc⟩ := hG v u γ d I k
  rw [hc p ctx t ht X _, hc p ctx t ht X z]
  by_cases hctx : IsAdmissibleChain c.inst.D c.inst.physical.bw c.inst.j₀ (c.stage i).level p.1
      (ctx.1.recenter c.inst.D (c.inst.D.eps ((c.stage i).level - 1) • X))
  · rw [ite_eq_left hctx, ite_eq_left hctx]
    exact Providers.GenSem.slotTransverse_of_generated hΛ hζ c.inst.physical.bw_pos hstart
      (fun e he => (he : False).elim) (hf p).1 t ht _ hctx z s
  · rw [ite_eq_right hctx, ite_eq_right hctx]

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! The weak certificate is available at reserve one before rerooting. Envelopes may use
an auxiliary grade allocation: their conclusion depends only on the envelope constants,
whereas the requested invariant allocation may have an unrelated grade offset. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly
open AVRegularity.Providers.WeakGen

/-- The same encoded witnesses certify every allocation whose reserves are at most one
and whose fast weight is the one used in the passage induction. -/
theorem weakGenEncoding_certificate_at_reserve (plan : WeakCoefficientPlan) (Kc : WeakConstFn)
    (hcert : WeakPassageCertStatement plan Kc) (c : WeakCoefficientCase plan)
    (k : InvConsts) (hL : k.Lstar = (plan.constants c.inst.request).kW.Lstar)
    (hμ : ∀ v : CompIn (weakGenEncodingChoice plan Kc c).stage.comps,
      compReserve k v.1 ≤ 1) :
    (weakGenEncodingChoice plan Kc c).stage.IsContextCertified k := by
  obtain ⟨hC0, hW⟩ := weakCertified_stage c hcert c.inst.physical.Jw le_rfl
  rw [Nat.add_sub_cancel] at hW
  have hres : weakReserve c.inst c.inst.M = 1 := by simp [weakReserve]
  have hwt : weakWeight c.inst c.inst.M = (plan.constants c.inst.request).kW.Lstar := by
    simp [weakWeight]
  rw [hres, hwt] at hW
  have hlevM : (c.stage c.inst.M).level = c.inst.M :=
    EntryWeakProofs.weakConstruction_level c.inst.P c.inst.menu c.inst.M c.inst.physical.Jw 0
      _ c.stage c.construction c.inst.M le_rfl (by omega)
  have hb : 0 ≤ c.inst.physical.bw := c.inst.physical.bw_pos.le
  have hε : ∀ k, 0 ≤ c.inst.D.eps k := fun k => (case_eps_pos c.inst k).le
  obtain ⟨hlevw, -⟩ := weakGenEncodingChoice_corr plan Kc c
  rw [← hL] at hW
  intro v' u' γ'
  obtain ⟨v, u, γ, hlen, hord, hsize, hco⟩ := (weakGenEncodingChoice_corr plan Kc c).coeffIs v' u' γ'
  set Cm := (Kc c.inst.request)^[c.inst.physical.Jw] 1 with hCm
  have hlenM : ((c.stage c.inst.M).fam.identity v u γ).record.length = c.inst.D.eps (c.inst.M + 1) :=
    (WeakEntryProofs.weakConstruction_output_records c.inst.P c.inst.menu c.inst.M
      c.inst.physical.Jw 0 _ c.stage c.construction c.inst.physical.Jw_pos v u γ).1
  have hordM : ((c.stage c.inst.M).fam.identity v u γ).maxOrder ≤ 1 + c.inst.physical.Jw * c.inst.physical.Nw :=
    EntryWeakProofs.weakConstruction_output_maxOrder_bound c.inst.P c.inst.menu c.inst.M
      c.inst.physical.Jw _ 0 c.stage c.construction c.inst.M le_rfl
      (by have := c.inst.physical.Jw_pos; omega) v u γ
  set ρ := ((c.stage c.inst.M).fam.identity v u γ).record.length / c.inst.D.eps (c.stage c.inst.M).level with hρ
  have hρ0 : 0 < ρ := div_pos ((c.stage c.inst.M).fam.identity v u γ).record.length_pos (case_eps_pos c.inst _)
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, hlenM, hlevM, div_le_one (case_eps_pos c.inst _)]
    exact case_eps_succ_le c.inst
  set θ₀ := Cm * ((c.stage c.inst.M).fam.identity v u γ).record.size * ρ ^ (((c.stage c.inst.M).fam.identity v u γ).maxOrder - 2)
    with hθ₀
  have hθ₀0 : 0 ≤ θ₀ :=
    mul_nonneg (mul_nonneg hC0 ((c.stage c.inst.M).fam.identity v u γ).record.size_nonneg) (pow_nonneg hρ0.le _)
  refine ⟨fun _ _ _ => θ₀, fun _ _ _ => hθ₀0, fun d hd hdn => ?_, fun d α k => ?_⟩
  · -- the witness inequality
    rw [hord] at hdn
    have hsum : ∑ _α : DerivativeWord2 (d - 1), ∑ _k : Fin 2, θ₀ = 2 ^ d * θ₀ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        DerivativeWord2, DerivativeWord, Fintype.card_fun]
      push_cast
      rw [← mul_assoc, ← pow_succ]
      congr 2
      omega
    have hratio : c.inst.D.eps (weakGenEncodingChoice plan Kc c).stage.level /
        ((weakGenEncodingChoice plan Kc c).stage.fam.identity v' u' γ').record.length = ρ⁻¹ := by
      rw [hρ, hlen, hlevw, inv_div]
    rw [hsum, hratio]
    calc ρ⁻¹ ^ (d - 2) * (2 ^ d * θ₀)
        ≤ 2 ^ (2 + c.inst.physical.Jw * c.inst.physical.Nw) * Cm *
            ((c.stage c.inst.M).fam.identity v u γ).record.size :=
          witness_algebra hρ0 hρ1 hC0 ((c.stage c.inst.M).fam.identity v u γ).record.size_nonneg hd hdn
            (by omega)
      _ = weakCertFactor Kc c * ((c.stage c.inst.M).fam.identity v u γ).record.size := by
          rw [weakCertFactor, hCm]
      _ ≤ ((weakGenEncodingChoice plan Kc c).stage.fam.identity v' u' γ').record.size := hsize
  · -- the extensions
    obtain ⟨f, F, hf, hc, hsz⟩ := hW v u γ d α k
    refine ⟨f, F, fun p => ⟨?_, ?_, hco d α k f hc p⟩, ?_⟩
    · rw [hlevw]; exact isGeneratedCtxFrom_of_noExports (hf p).1
    · rw [hlevw]; exact (hf p).2
    · rw [hlevw]
      exact (ctxSize_mono_reserve hb hε (hμ v') _).trans hsz

end AVRegularity.WeakEntryProofs.Assembly
end
end
end

section
section
/-! Weak instantiation of the shared context estimate. All encoded components are roots.
We use reserve one in an auxiliary grade allocation, retaining every envelope constant of
the requested allocation. Thus an arbitrary requested grade offset causes no reserve loss. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs.Assembly
open AVRegularity.Providers.WeakGen AVRegularity.Construction.StageEnvelopes
open AVRegularity.Construction.Preservation

def weakEnvelopeConsts (k : InvConsts) : InvConsts := { k with G0 := 0, Hprod := 0 }

def weakEnvelopeEstimates (h : ContextStageEnvelopesStatement)
    (p : ContextEnvelopeParameters) : ContextEnvelopeEstimate p := Classical.choice (h p)

/-- No analytic constant (Ca or Cm), ambient cap, stage or flow occurs in these parameters. -/
def weakEnvelopeParameters (plan : WeakCoefficientPlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A) (hΛ : 128 ≤ A.Λ) :
    ContextEnvelopeParameters where
  α := B.α
  s := B.s
  q := B.q
  Λ := A.Λ
  ζ := B.ζ
  alpha_pos := B.hα₀
  alpha_lt := B.hα₁
  s_pos := B.hs₀
  s_lt := B.hs₁
  admissible_q := B.hq
  base_large := hΛ
  profile := B.hζ
  bw := A.bw
  bw_pos := A.bw_pos
  bw_small := A.bw_small
  certReserve := 1
  innerReserve := (plan.constants R).kW.mEnv
  inner_nonneg := (plan.constants R).allocation.2.2.2.2.2.2.2.1
  gap := by
    have hm := (plan.constants R).allocation.2.2.2.2.2.2.2.2.1
    exact hm.trans_le (by
      apply (div_le_one (by positivity)).mpr
      have : (0 : ℝ) ≤ ((plan.constants R).kW.Hprod : ℝ) := Nat.cast_nonneg _
      linarith)
  cert_le_two := by norm_num
  Ks := (plan.constants R).kW.Ks
  Kan := (plan.constants R).kW.Kan
  Lan := (plan.constants R).kW.Lan
  Jm := (plan.constants R).kW.Jm
  Dstar := 1 + A.Jw * A.Nw

def weakEnvelopeLengthFloor {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakCoefficientRequest A) (hΛ : weakKernelBaseThreshold B ≤ A.Λ) : ℕ :=
  (exists_weak_envelope_length_threshold R hΛ).choose

/-- These are pre-data choices: Ca and Cm dominate the shared estimate, and the level
threshold dominates its floor and the proved length floor. Parameters do not use Ca or Cm. -/
def WeakEnvPlanOK (plan : WeakCoefficientPlan)
    (estimates : ∀ p, ContextEnvelopeEstimate p) : Prop :=
  (∀ B, weakKernelBaseThreshold B ≤ plan.baseThreshold B) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A)
    (hΛ : plan.baseThreshold B ≤ A.Λ),
    let p := weakEnvelopeParameters plan R ((plan.baseThreshold_ge B).trans hΛ)
    (estimates p).Ca ≤ (plan.constants R).kW.Ca ∧
    (∀ j, (estimates p).Cm j ≤ (plan.constants R).kW.Cm j) ∧
    ∀ j₀, (estimates p).levelFloor ≤ plan.levelThreshold R j₀ ∧
      ∀ hK : weakKernelBaseThreshold B ≤ A.Λ,
        weakEnvelopeLengthFloor R hK ≤ plan.levelThreshold R j₀

theorem weak_envelope_input (plan : WeakCoefficientPlan) (Kc : WeakConstFn)
    (hplan : WeakComplexContextPlanOK plan) (estimates : ∀ p, ContextEnvelopeEstimate p)
    (henv : WeakEnvPlanOK plan estimates) (hcert : WeakPassageCertStatement plan Kc)
    (c : WeakCoefficientCase plan) :
    ContextEnvelopeInput
      (weakEnvelopeParameters plan c.inst.request (case_Lambda_ge c.inst))
      (weakGenEncodingChoice plan Kc c).stage
      (weakEnvelopeConsts (plan.constants c.inst.request).kW)
      (plan.constants c.inst.request).kW.mEnv
      (rhoStar c.inst.D (plan.constants c.inst.request).kW.c₀
        (weakGenEncodingChoice plan Kc c).stage.level) := by
  let G := (weakGenEncodingChoice plan Kc c).stage
  let k := (plan.constants c.inst.request).kW
  have he := (weak_encoding_transport plan
    (fun c => (weakGenInflation Kc).factor c.inst.request)
    (fun c => (weakGenInflation Kc).one_le c.inst.request) (fun _ => noExports) c).1
  have hl : G.level = c.inst.M := he.1.trans
    (EntryWeakProofs.weakConstruction_level c.inst.P c.inst.menu c.inst.M c.inst.physical.Jw 0 _ c.stage
      c.construction c.inst.M le_rfl (by omega))
  have hroot (v : CompIn G.comps) : v.1.births = [] := by
    obtain ⟨v, rfl⟩ := (weakGenEncodingChoice plan Kc c).relabel.surjective v
    exact he.2.1 v
  have hreserve (v : CompIn G.comps) : compReserve (weakEnvelopeConsts k) v.1 = 1 := by
    simp only [compReserve, weakEnvelopeConsts, compGrade, hroot, List.length_nil,
      Nat.add_zero, Nat.cast_zero, zero_div, sub_zero]
  have hpos := EntryWeakProofs.weakData_kap_pos c.inst.D
    (by rw [c.inst.hΛ]; have := case_Lambda_ge c.inst; omega)
    (by rw [c.inst.hζ]; exact c.inst.base.hζ)
    (by rw [c.inst.hα, c.inst.hq, c.inst.hΛ, c.inst.hζ, c.inst.term]; exact c.inst.band)
  have hJ := c.inst.physical.Jw_pos
  have hκG : 0 < c.inst.D.κ G.level := by
    rw [hl]
    simpa only [OCData.kap, c.inst.term, Nat.min_self] using hpos c.inst.M
  have hA : 0 < ocA c.inst.D.α c.inst.D.q c.inst.D.Λ G.level :=
    Real.rpow_pos_of_pos (case_eps_pos c.inst _) _
  have hρ : 0 < rhoStar c.inst.D k.c₀ G.level := by
    unfold rhoStar
    apply mul_pos
    · rw [(plan.constants c.inst.request).radius]; exact c.inst.request.cK_pos
    · exact lt_min (case_eps_pos c.inst _) (Real.sqrt_pos.mpr
        (div_pos hκG hA))
  have ho := EntryWeakProofs.weakConstruction_output_maxOrder_bound c.inst.P c.inst.menu c.inst.M
    c.inst.physical.Jw _ 0 c.stage c.construction c.inst.M le_rfl
    (by have := c.inst.physical.Jw_pos; omega)
  have hr := weakEncoding_orders_records c.inst.physical.Nw c.inst.physical.Jw c.inst.physical.η₀
    (weakCaseRootMass c) (weakCaseRootReadout c) (c.stage c.inst.M) G
    (weakGenEncodingChoice plan Kc c).relabel he (1 + c.inst.physical.Jw * c.inst.physical.Nw)
    (c.inst.D.eps (c.inst.M + 1)) (c.inst.D.termRW c.inst.physical.σw c.inst.M) ho
    (weakConstruction_output_records c.inst.P c.inst.menu c.inst.M c.inst.physical.Jw 0 _ c.stage
      c.construction c.inst.physical.Jw_pos)
  refine
    { bw_eq := rfl
      alpha_eq := c.inst.hα
      q_eq := c.inst.hq
      base_eq := c.inst.hΛ
      profile_eq := c.inst.hζ
      stream := c.inst.stream
      natural := ⟨c.inst.M + c.inst.physical.Jw, (weak_encoding_transport plan
    (fun c => (weakGenInflation Kc).factor c.inst.request)
    (fun c => (weakGenInflation Kc).one_le c.inst.request) (fun _ => noExports) c).2.1
        (EntryWeakProofs.weakConstruction_output_natural c.inst.P c.inst.menu c.inst.M c.inst.physical.Jw 0 _
          c.stage c.construction c.inst.M le_rfl (by omega))⟩
      certified := weakGenEncoding_certificate_at_reserve plan Kc hcert c _ rfl
        (fun v => (hreserve v).le)
      level_pos := by rw [hl]; have := (hplan.2 c.inst.request c.inst.j₀).trans c.inst.level_large; omega
      carrier_start := by rw [hl]; have := (hplan.2 c.inst.request c.inst.j₀).trans c.inst.level_large; omega
      carrier_environment := ⟨_, _, hplan.1 c.inst.request, by
        simpa only [c.inst.hα, c.inst.hq, c.inst.hΛ] using c.inst.carrier⟩
      q_pos := by rw [c.inst.hq]; exact c.inst.base.hq.1
      large := by rw [c.inst.hΛ]; exact case_Lambda_ge c.inst
      kap_pos := hpos _
      radius_pos := hρ
      radius_le := ?_
      wavelength_le := ?_
      inner_nonneg := (plan.constants c.inst.request).allocation.2.2.2.2.2.2.2.1
      inner_le := le_rfl
      reserve_le := fun v => (hreserve v).ge
      reserve_upper := fun v => (hreserve v).trans_le (by norm_num)
      slot_order := le_rfl
      slow_order := le_rfl
      fast_order := le_rfl
      molecular_order := le_rfl
      source_order := hr.1
      higher_length := ?_ }
  · unfold rhoStar
    calc k.c₀ * min (c.inst.D.eps G.level) _ ≤ 1 * min (c.inst.D.eps G.level) _ :=
        mul_le_mul_of_nonneg_right
          (by rw [(plan.constants c.inst.request).radius]; exact c.inst.request.cK_le)
          (le_of_lt (lt_min (case_eps_pos c.inst _) (Real.sqrt_pos.mpr
            (div_pos hκG hA))))
      _ ≤ c.inst.D.eps G.level := by rw [one_mul]; exact min_le_left _ _
  · exact Applications.eps_antitone
      (by rw [c.inst.hq]; exact c.inst.base.hq.1)
      (by rw [c.inst.hΛ]; exact case_Lambda_ge c.inst) (Nat.sub_le _ _)
  · intro v u γ _
    rw [(hr.2.1 v u γ).1, hl, (plan.constants c.inst.request).radius]
    have hK := (henv.1 c.inst.base).trans c.inst.base_large
    have hf := ((henv.2 c.inst.request c.inst.base_large).2.2 c.inst.j₀).2 hK
    have hh := (exists_weak_envelope_length_threshold c.inst.request hK).choose_spec
      c.inst.M (hf.trans c.inst.level_large) c.inst.D.κ c.inst.band
    simpa only [rhoStar, OCData.eps, c.inst.hα, c.inst.hq, c.inst.hΛ] using hh

/-- I8 uses just the shared analytic producer, with the weak geometric/certificate adapters
proved above. The auxiliary grade constants do not occur in the returned envelopes. -/
theorem weak_stage_envelopes (plan : WeakCoefficientPlan) (Kc : WeakConstFn)
    (hplan : WeakComplexContextPlanOK plan) (estimates : ∀ p, ContextEnvelopeEstimate p)
    (henv : WeakEnvPlanOK plan estimates) (hcert : WeakPassageCertStatement plan Kc) :
    WeakStageEnvelopesStatement plan (weakGenEncodingChoice plan Kc) := by
  intro c w
  let G := (weakGenEncodingChoice plan Kc c).stage
  let k := (plan.constants c.inst.request).kW
  let p := weakEnvelopeParameters plan c.inst.request (case_Lambda_ge c.inst)
  have hinput := weak_envelope_input plan Kc hplan estimates henv hcert c
  have hl : G.level = c.inst.M := (weakGenEncodingChoice_corr plan Kc c).1.trans
    (EntryWeakProofs.weakConstruction_level c.inst.P c.inst.menu c.inst.M c.inst.physical.Jw
      0 _ c.stage c.construction c.inst.M le_rfl (by omega))
  have hC := henv.2 c.inst.request c.inst.base_large
  have h := (estimates p).bound ScalarH c.inst.D _ c.inst.j₀ c.inst.physical.bw G
    (weakEnvelopeConsts k) k.mEnv (rhoStar c.inst.D k.c₀ G.level) hinput
    (by rw [hl]; exact ((hC.2.2 c.inst.j₀).1).trans c.inst.level_large)
    hC.1 hC.2.1 w.law (Set.Icc w.aM (w.a + c.inst.physical.T₀))
  have h1 := h (fun _ => 1) (fun _ => zero_lt_one)
  dsimp only at h1
  have hid : markerConj (fun _ => 1) G.fam = G.fam := by
    unfold markerConj
    simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_smul]
  rw [hid] at h1
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul] at h1
  have hm := h (G.marker w.law) (fun v =>
    Buffer.birth_compMarker_pos hinput.q_pos hinput.large w.law v.1)
  constructor
  · intro K hK
    exact ⟨⟨(h1 K hK).1, (h1 K hK).2.1⟩, ⟨(hm K hK).1, (hm K hK).2.1⟩⟩
  · intro K hK
    exact (h1 K hK).2.2.2

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! The context torus law descends through every stage of an actual weak construction. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly

/-- I3's shift half, at every stage rather than only at the output. -/
def WeakStageShiftStatement (plan : WeakCoefficientPlan) : Prop :=
  ∀ c : WeakCoefficientCase plan, ∀ i, c.inst.M ≤ i → i ≤ c.inst.M + c.inst.physical.Jw →
    (c.stage i).IsShiftInvariant

/-- The finite induction uses only positivity of the actual cell scale on passage levels. -/
theorem weakConstruction_shiftInvariant {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : WeakMenu) (M J r : ℕ) (rW : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm bw j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage) (hζ : IsFastProfile D.ζ)
    (hτ : ∀ i, 0 < ocTau D.α D.q D.Λ i) (heps : ∀ i, 0 < D.eps i)
    (hcs : ∀ i, M < i → i ≤ M + J → 0 ≤ D.cellScaleSq i) :
    ∀ i, M ≤ i → i ≤ M + J → (stage i).IsShiftInvariant := by
  have main : ∀ n, n ≤ J → (stage (M + J - n)).IsShiftInvariant := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      constructor
      · intro p ctx ctx' k hctx v u γ
        exact ((hc.2.1.2.2.1 v u).false γ).elim
      · intro p ctx ctx' k h0 hctx v u γ
        exact ((hc.2.1.2.2.1 v u).false γ).elim
    | succ n ih =>
      intro hn
      let i := M + J - n
      have hi : M < i := by dsimp [i]; omega
      have hit : i ≤ M + J := by dsimp [i]; omega
      have hl := EntryWeakProofs.weakConstruction_level P Mn M J r rW stage hc i hi.le hit
      have hs := weakPassage_isShiftInvariant P Mn rW (1 + (M + J - i) * Mn.N)
        (hc.2.2 i hi hit).1 (ih (by omega)) hζ (hτ _) (by rw [hl]; exact hcs i hi hit) heps
      have he : M + J - (n + 1) = i - 1 := by dsimp [i]; omega
      simpa only [he] using hs
  intro i hi hit
  have he : M + J - (M + J - i) = i := by omega
  simpa only [he] using main (M + J - i) (by omega)

/-- Uniqueness of the actual lifts propagates the torus law, with no incoming-model premise. -/
theorem weak_stage_shift_laws (plan : WeakCoefficientPlan) : WeakStageShiftStatement plan := by
  intro c
  have hΛ : 1 ≤ c.inst.D.Λ := by
    rw [c.inst.hΛ]
    exact (by decide : 1 ≤ 128).trans ((plan.baseThreshold_ge c.inst.base).trans c.inst.base_large)
  have hζ : IsFastProfile c.inst.D.ζ := by rw [c.inst.hζ]; exact c.inst.base.hζ
  have hν : 0 < c.inst.D.κ c.inst.M :=
    CycleReference.bandChain_pos
      ((by decide : 1 ≤ 128).trans ((plan.baseThreshold_ge c.inst.base).trans c.inst.base_large))
      c.inst.base.hζ c.inst.band le_rfl
  apply weakConstruction_shiftInvariant c.inst.P c.inst.menu c.inst.M c.inst.physical.Jw 0
    (c.inst.D.termRW c.inst.physical.σw c.inst.M) c.stage c.construction hζ
    (fun _ => Construction.Stream.ocTau_pos hΛ) (fun _ => Construction.Stream.ocEpsilon_pos hΛ)
  intro i hi _
  unfold OCData.cellScaleSq OCData.kap
  rw [c.inst.term, min_eq_right hi.le]
  exact div_nonneg (sq_nonneg _) hν.le

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! Choose the physical price and its large-level threshold before the carrier and flow.
Only Cχ and the terminal threshold change; the supplied cK and all kernel data are retained. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs.Assembly

/-- Uniform dimensional production, with dependence exactly on the physical menu and Ks. -/
structure WeakKernelPhysicalData {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (sZ Ks : ℕ) where
  C : ℝ
  nonneg : 0 ≤ C
  threshold : ℕ
  bound : 128 ≤ A.Λ → ∀ D : OCData,
    threshold ≤ D.term → D.α = B.α → D.q = B.q → D.Λ = A.Λ → D.ζ = B.ζ →
    IsOCStreamSeq B.α B.q A.Λ B.ζ D.Φ →
    IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ Dm : ℕ, 1 + A.Jw * A.Nw ≤ Dm → ∀ j₀
      (stage : ℕ → GenStage D ScalarH Dm A.bw j₀) (P : ProvParams)
      (M sX r : ℕ) (η rW : ℝ), D.term = M →
    IsWeakConstruction D P ⟨A.Nw, A.Rw, sX, sZ, η, M + A.Jw⟩ M A.Jw rW r stage →
    ∀ i, M ≤ i → i < M + A.Jw →
    ∀ (v u : CompIn (stage i).comps) (γ : (stage i).fam.Γ v u) (d k : ℕ),
      2 ≤ d → d ≤ ((stage i).fam.identity v u γ).maxOrder → k ≤ Ks → ∀ a b : ℝ,
      coefficientSeminorm (D.eps i) k a b ((stage i).physCoeff v u γ d) ≤
        ENNReal.ofReal (C * ((stage i).fam.identity v u γ).record.size * D.κ M *
          D.eps (i + 1) ^ (((stage i).fam.identity v u γ).maxOrder - 2) *
          D.eps i ^ ((d : ℝ) - (((stage i).fam.identity v u γ).maxOrder : ℝ)))

/-- Reuse the physical production, without any independent incoming-model premise. -/
theorem exists_weakKernelPhysicalData {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (sZ Ks : ℕ) : Nonempty (WeakKernelPhysicalData A sZ Ks) := by
  by_cases hΛ : 128 ≤ A.Λ
  · obtain ⟨C, hC, M, _, hbound⟩ := EntryWeakProofs.uniform_weak_physical_coefficient_production
      B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ hΛ B.ζ B.hζ
      A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw sZ Ks A.Jw_pos
    exact ⟨⟨C, hC, M, fun _ => hbound⟩⟩
  · exact ⟨⟨0, le_rfl, 0, fun h => (hΛ h).elim⟩⟩

def weakKernelPhysicalData {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (sZ Ks : ℕ) : WeakKernelPhysicalData A sZ Ks :=
  Classical.choice (exists_weakKernelPhysicalData A sZ Ks)

/-- Finite sum of positive kernel constants through the actual weak menu's maximum order. -/
def weakKernelPriceCost (plan : WeakCoefficientPlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A) : ℝ :=
  (weakKernelPhysicalData A R.sZ (plan.constants R).kW.Ks).C *
    ∑ d ∈ Finset.Icc 2 (1 + A.Jw * A.Nw), max 0 ((plan.constants R).kW.cker (d - 2))

theorem weakKernelPriceCost_nonneg (plan : WeakCoefficientPlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakCoefficientRequest A) :
    0 ≤ weakKernelPriceCost plan R :=
  mul_nonneg (weakKernelPhysicalData A R.sZ (plan.constants R).kW.Ks).nonneg
    (Finset.sum_nonneg fun _ _ => le_max_left _ _)

/-- This refinement accommodates both the witness inflation and the dimensional kernel prices.
All constants are still chosen before the chain depth, terminal level, flow, and stage. -/
def weakKernelPricePlan (plan : WeakCoefficientPlan) (F : WeakWitnessInflation) :
    WeakCoefficientPlan where
  baseThreshold := plan.baseThreshold
  baseThreshold_ge := plan.baseThreshold_ge
  momentThreshold := plan.momentThreshold
  constants {_B} {A} R := { plan.constants R with
    Cχ := (max 1 (weakKernelPriceCost plan R) * F.factor R) * (weakStoredLedgerData A).C }
  levelThreshold {_B} {A} R j₀ := max (plan.levelThreshold R j₀)
    (max (weakKernelPhysicalData A R.sZ (plan.constants R).kW.Ks).threshold
      (weakStoredLedgerData A).threshold)

end AVRegularity.WeakEntryProofs.Assembly
end
end
end
