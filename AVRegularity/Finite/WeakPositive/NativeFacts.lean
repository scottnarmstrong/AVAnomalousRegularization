-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Finite.Assembly.WeakParentNativeFactsOfIngredients
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.TerminalLift.Assembly
import AVRegularity.EntryWeakAssembly.QuietParentSlowJets
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Finite.WeakPositive.NativeAdapter
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleResidualDifferentiated

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev MeasureTheory Filter Topology
open scoped Classical ENNReal
namespace AVRegularity.Finite.WeakLift

/-! Fixed-carrier, explicit-order weak slot lifts, at zero lift-order floors. -/

open Construction.Preservation.FullLift Construction.TerminalLift CycleComparison.Lift EntryWeakProofs
open WeakEntryProofs WeakEntryProofs.Assembly Construction.Preservation.Ledger Providers.WeakGen

/-- Numeric selector with no floor on the supplied lift orders. -/
def WeakParentUniformFactAtStatement
    (Witness : ∀ {B : WeakParentBase}, WeakParentMenu B → Type)
    (claim : ∀ {B : WeakParentBase} (R : WeakParentMenu B), Witness R →
      ∀ {sX sZ : ℕ}, WeakParentCase R sX sZ → Prop) : Prop :=
  ∀ B : WeakParentBase, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
  ∀ R : WeakParentMenu B, Λ₀ ≤ R.Λ → ∀ sX sZ : ℕ,
  ∃ w : Witness R, ∀ j₀ : ℕ, ∃ M₀ : ℕ,
  ∀ C : WeakParentCase R sX sZ, C.j₀ = j₀ → M₀ ≤ C.M → claim R w C

def WeakParentGeometryAtStatement : Prop :=
  WeakParentUniformFactAtStatement (fun {_B} _R => {c : ℝ // 1 ≤ c})
    (fun {_B} R c {_sX _sZ} C => WeakPositiveGeometry
      (weakParentParameters R 0 0 0 0 c.1 le_rfl c.2) C.i C.G)

def WeakParentMassSumsAtStatement : Prop :=
  WeakParentUniformFactAtStatement (fun {_B} _R => {S : ℝ // 0 ≤ S})
    (fun {_B} _R S {_sX _sZ} C => HasRealSchurBudget (weakParentPrice C) S.1)

def WeakParentNativeCoefficientFactsAtStatement : Prop :=
  WeakParentUniformFactAtStatement (fun {_B} _R => ℕ → ℕ → ℝ)
    (fun {_B} _R Cj {_sX _sZ} C => WeakParentNativeCoefficientFacts C Cj)

def WeakParentSettingAssemblyAtStatement : Prop :=
  WeakParentUniformFactAtStatement (fun {_B} _R => (ℕ → ℝ) × (ℕ → ℝ))
    (fun {_B} R g {_sX _sZ} C => ∀ (c : {c : ℝ // 1 ≤ c}) (Cj : ℕ → ℕ → ℝ) (S : {S : ℝ // 0 ≤ S}),
      let P := weakParentParameters R g.1 g.2 Cj S.1 c.1 S.2 c.2
      WeakPositiveGeometry P C.i C.G → WeakParentNativeFacts C Cj →
      HasRealSchurBudget (weakParentPrice C) S.1 →
      Nonempty (∀ slot, WeakPositiveSlot P C.i C.G (weakParentMass C) slot))

private theorem weakParentAt_active_in_window {α q : ℝ} {Λ i : ℕ} (hΛ : 1 ≤ Λ)
    (slot : ℤ) (t : ℝ) (ht : ocCutoff α q Λ i slot t ≠ 0) :
    t ∈ ocPulseWindow α q Λ i slot := by
  have h := CycleReference.cutoff_nonzero_distance hΛ slot t ht
  have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) (m := i) hΛ
  rw [abs_lt] at h
  constructor <;> linarith only [h.1, h.2, hτ]

/-- Expose the existing zero lift-order floors. -/
theorem weak_parent_geometry_at : WeakParentGeometryAtStatement := by
  intro B
  refine ⟨128, le_rfl, ?_⟩
  intro R _
  let K := R.Lr + 3 + R.N
  obtain ⟨Mflow, _hMflow, hflow⟩ := uniform_native_physical_flow_jets B.α B.s B.q
    B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq R.Λ R.hΛ B.ζ B.hζ K
  intro sX sZ
  refine ⟨⟨weakChartJetBudget K 0, weakChartJetBudget_ge_one K 0⟩,
    fun _ => ⟨Mflow, ?_⟩⟩
  intro C _ hM
  have hΛ : 1 ≤ C.D.Λ := by rw [C.hΛ]; have := R.hΛ; omega
  have hζ : IsFastProfile C.D.ζ := C.hζ.symm ▸ B.hζ
  have hband : IsOCBandChain C.D.α C.D.q C.D.Λ C.D.ζ C.D.term C.D.κ := by
    rw [C.hα, C.hq, C.hΛ, C.hζ, C.term]
    exact C.band
  have heps (n : ℕ) : 0 < C.D.eps n := Construction.Stream.ocEpsilon_pos hΛ
  have hlevel : C.G.level = C.i :=
    weakConstruction_level C.PW _ C.M R.J 0 _ C.stage C.construction C.i C.hi.le C.hiJ
  have hnatural : C.G.IsNatural (C.M + R.J) := by
    by_cases hi : C.i = C.M + R.J
    · simpa only [WeakParentCase.G, hi] using C.construction.2.1.2.2.2
    · exact weakConstruction_output_natural C.PW _ C.M R.J 0 _ C.stage
        C.construction C.i C.hi.le (by have := C.hiJ; omega)
  have hshift := WeakEntryProofs.Assembly.weakConstruction_shiftInvariant C.PW _
    C.M R.J 0 _ C.stage C.construction hζ
    (fun _ => Construction.Stream.ocTau_pos hΛ) heps
    (fun i _ _ => (weakData_cellScaleSq_pos C.D hΛ hζ hband i).le) C.i C.hi.le C.hiJ
  have htorus : IsTorusCompatible C.G.fam C.G.actual (C.D.eps (C.i - 1)) := by
    simpa only [hlevel] using GenStage.isTorusCompatible_of_shiftInvariant hnatural hshift
  refine {
    level := hlevel
    q_gt := C.hq.symm ▸ B.hq.1
    Λ_ge := C.hΛ.symm ▸ R.hΛ
    fast := hζ
    stream := ?_
    band := hband
    plateau := C.term.symm ▸ C.hi.le
    torus := htorus
    forward := ?_
    backward := ?_ }
  · simpa only [C.hα, C.hq, C.hΛ, C.hζ] using C.stream
  · intro t slot ht
    exact (hflow C.D C.hα C.hq C.hΛ C.hζ C.stream C.i
      (by have := C.hi; omega) slot.1 slot.2 (C.D.eps (C.i - 1))
      (heps _) le_rfl t (weakParentAt_active_in_window hΛ slot.1 t ht)).1
  · intro t slot ht
    exact (hflow C.D C.hα C.hq C.hΛ C.hζ C.stream C.i
      (by have := C.hi; omega) slot.1 slot.2 (C.D.eps (C.i - 1))
      (heps _) le_rfl t (weakParentAt_active_in_window hΛ slot.1 t ht)).2

/-- Expose the existing zero lift-order floors. -/
theorem weak_parent_mass_sums_at : WeakParentMassSumsAtStatement := by
  intro B
  refine ⟨128, le_rfl, ?_⟩
  intro R _
  let A := weakParentCoefficientPhysical R
  obtain ⟨Ce, hCe, heddy⟩ := exists_weakStoredEddy_constant (weakParentCoefficientBase B) A
  let Q : ℝ := weakStoredPassageBudget R.N R.J R.R
  let Ctot : ℝ := (2 * Q) ^ R.J * Ce
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    exact_mod_cast weakStoredPassageBudget_one_le R.N R.J R.R
  have h2Q : 1 ≤ 2 * Q := hQ.trans (le_mul_of_one_le_left (zero_le_one.trans hQ) (by norm_num))
  have hCtot : 0 < Ctot := mul_pos (pow_pos (by linarith only [hQ]) _)
    (zero_lt_one.trans_le hCe)
  have hχ : 0 < weakChi B.α B.q R.η := weakChi_pos B.hα₀ B.hq.1 B.hq.2.1 R.hη1
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    ((EntryScales.epsilon_rpow_tendsto_zero B.hq.1 R.hΛ hχ).eventually
      (gt_mem_nhds (inv_pos.mpr hCtot)))
  intro sX sZ
  refine ⟨⟨1, zero_le_one⟩, fun _ => ⟨M₀, ?_⟩⟩
  intro C _ hM
  have hΛ : 1 ≤ C.D.Λ := by rw [C.hΛ]; have := R.hΛ; omega
  have heps (i : ℕ) : 0 < C.D.eps i := Construction.Stream.ocEpsilon_pos hΛ
  have hsmall : Ctot * C.D.eps C.M ^ weakChi B.α B.q R.η ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hM₀ C.M hM).le hCtot.le
    rw [mul_inv_cancel₀ hCtot.ne'] at hh
    simpa only [OCData.eps, C.hq, C.hΛ] using hh
  have hbound := weakConstruction_storedTotal_stage_bound C.PW
    (⟨R.N, R.R, sX, sZ, R.η, C.M + R.J⟩ : WeakMenu) C.M R.J 0
    (C.D.termRW R.σ C.M) C.stage C.construction R.hN R.hJ heps
    (Ce * C.D.eps C.M ^ weakChi B.α B.q R.η)
    (mul_nonneg (zero_lt_one.trans_le hCe).le (Real.rpow_nonneg (heps _).le _))
    (fun i hi _ => heddy C.M C.D C.hα C.hq C.hΛ C.term C.band R.hΛ i hi)
    (by simpa only [Ctot, Q, mul_assoc] using hsmall)
    (C.M + R.J - C.i) (by have := C.hi; omega)
  have hidx : C.M + R.J - (C.M + R.J - C.i) = C.i := by have := C.hi; have := C.hiJ; omega
  rw [hidx] at hbound
  have hpow := pow_le_pow_right₀ h2Q (show C.M + R.J - C.i ≤ R.J by have := C.hi; omega)
  have htotal : weakStoredTotal C.G R.N R.J R.η ≤ 1 := hbound.trans
    ((mul_le_mul_of_nonneg_right hpow
      (mul_nonneg (zero_lt_one.trans_le hCe).le (Real.rpow_nonneg (heps _).le _))).trans
      (by simpa only [Ctot, Q, mul_assoc] using hsmall))
  have hsum : (∑ v, ∑ u, weakParentPrice C v u) ≤ 1 :=
    (weak_parent_record_total_le C).trans htotal
  have hn (v u : CompIn C.G.comps) : 0 ≤ weakParentPrice C v u :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun γ _ =>
      mul_nonneg (norm_nonneg _) (C.G.fam.identity v u γ).record.size_nonneg)
  refine ⟨hn, ?_, ?_⟩
  · intro v
    exact (Finset.single_le_sum (fun v _ => Finset.sum_nonneg (fun u _ => hn v u))
      (Finset.mem_univ v)).trans hsum
  · intro u
    rw [Finset.sum_comm] at hsum
    exact (Finset.single_le_sum (fun u _ => Finset.sum_nonneg (fun v _ => hn v u))
      (Finset.mem_univ u)).trans hsum

private theorem weak_parent_at_case_native_geometry {B : WeakParentBase} {R : WeakParentMenu B}
    {sX sZ : ℕ} (C : WeakParentCase R sX sZ) :
    C.G.level = C.i ∧ C.G.IsNatural (C.M + R.J) ∧
    (∀ v u (γ : C.G.fam.Γ v u),
      (C.G.fam.identity v u γ).record.length ≤ C.D.eps C.G.level) ∧
    ∀ v u (γ : C.G.fam.Γ v u), (C.G.fam.identity v u γ).maxOrder ≤ weakParentCap R := by
  have hlevel : C.G.level = C.i := weakConstruction_level C.PW _ C.M R.J 0 _
    C.stage C.construction C.i C.hi.le C.hiJ
  have hnat : C.G.IsNatural (C.M + R.J) := by
    by_cases hi : C.i = C.M + R.J
    · simpa only [WeakParentCase.G, hi] using C.construction.2.1.2.2.2
    · exact weakConstruction_output_natural C.PW _ C.M R.J 0 _ C.stage
        C.construction C.i C.hi.le (by have := C.hiJ; omega)
  refine ⟨hlevel, hnat, ?_, ?_⟩
  · intro v u γ
    by_cases hi : C.i = C.M + R.J
    · have hroot := C.construction.2.1
      rw [← hi] at hroot
      exact ((hroot.2.2.1 v u).false γ).elim
    · have hp := C.construction.2.2 (C.i + 1) (by have := C.hi; omega)
        (by have := C.hiJ; omega)
      have hlen := IsWeakPassage.length_eq hp.1 hp.2
      rw [Nat.add_sub_cancel] at hlen
      have hnext := weakConstruction_level C.PW _ C.M R.J 0 _ C.stage
        C.construction (C.i + 1) (by have := C.hi; omega) (by have := C.hiJ; omega)
      rw [hlen v u γ, hnext, hlevel]
      exact Applications.eps_antitone (C.hq.symm ▸ B.hq.1) (C.hΛ.symm ▸ R.hΛ) (Nat.le_succ _)
  · intro v u γ
    have hb := weakConstruction_stage_maxOrderBound C.PW _ C.M R.J 0 _
      C.construction C.i C.hi.le C.hiJ v u γ
    exact hb.trans (le_max_right _ _)

/-- Expose the existing zero lift-order floors. -/
theorem weak_parent_native_coefficient_facts_at : WeakParentNativeCoefficientFactsAtStatement := by
  intro B
  refine ⟨max 128 (weakCommonCoeffPlan.baseThreshold (weakParentCoefficientBase B)),
    le_max_left _ _, ?_⟩
  intro R hbase
  have hb : weakCommonCoeffPlan.baseThreshold (weakParentCoefficientBase B) ≤ R.Λ :=
    (le_max_right _ _).trans hbase
  intro sX sZ
  let req := weakParentCertificateRequest R sX sZ
  let qs := weakParentSlow R + 4 * (R.J * R.R + 1) * (R.N + weakParentCap R) ^ 2
  let qf := max (weakParentFast R) (weakParentFast R + 2) + R.J * R.R * weakParentCap R +
    2 * R.N + 2 * weakParentCap R
  obtain ⟨BJ, hBJ, hjet⟩ := uniform_weak_native_coefficient_jet_bounds R.bw R.hbw (qs + qf)
  let cost := weakQuietCertificatePrice req
  have hcost : 0 ≤ cost := Finset.sum_nonneg fun _ _ => le_max_left (0 : ℝ) _
  let A : ℕ → ℕ → ℝ := fun r q => BJ (r + q) * (2 * cost)
  have hA : ∀ r q, 0 ≤ A r q := fun r q => mul_nonneg (hBJ _) (mul_nonneg (by norm_num) hcost)
  let Cj : ℕ → ℕ → ℝ := fun r q => ((weakParentCap R + 1 : ℕ) : ℝ) * 2 ^ weakParentCap R * A r q
  refine ⟨Cj, ?_⟩
  intro j₀
  refine ⟨max (j₀ + 2) (weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne req) j₀), ?_⟩
  intro C hj₀ hM
  have hfloor : j₀ + 2 ≤ C.M := (le_max_left _ _).trans hM
  have hl : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne req) C.j₀ ≤ C.M := by
    rw [hj₀]
    exact (le_max_right _ _).trans hM
  have hΛ : 1 ≤ C.D.Λ := by rw [C.hΛ]; have := R.hΛ; omega
  have hζ : IsFastProfile C.D.ζ := C.hζ.symm ▸ B.hζ
  have hband : IsOCBandChain C.D.α C.D.q C.D.Λ C.D.ζ C.D.term C.D.κ := by
    rw [C.hα, C.hq, C.hΛ, C.hζ, C.term]
    exact C.band
  have heps (m : ℕ) : 0 < C.D.eps m := Construction.Stream.ocEpsilon_pos hΛ
  obtain ⟨hlevel, hnat, hlen, hcap⟩ := weak_parent_at_case_native_geometry C
  have hi : 1 ≤ C.G.level := by rw [hlevel]; have := C.hi; omega
  have hj : C.j₀ ≤ C.G.level := by rw [hlevel, hj₀]; have := C.hi; omega
  have hcert : ∃ mres : ℝ, ∃ L : ℕ, 0 ≤ mres ∧ mres ≤ 2 ∧ WeakCertified cost mres L C.G := by
    by_cases hR : R.R = 0
    · refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
      intro v u γ
      exact ((weak_parent_case_empty_zero C hR v u).false γ).elim
    · have hR1 : 1 ≤ R.R := by omega
      let x := weakParentCommonCase C hR1 hb hl
      obtain ⟨_hc, hc⟩ := weak_parent_case_certified C hR1 hb hl
      have hn : C.M + R.J - C.i ≤ R.J := by have := C.hi; omega
      have hprice : ((weakCertConst weakBasePlan (weakCoeffRequestOne req))^[C.M + R.J - C.i] 1) ≤
          cost := by
        apply (le_max_right (0 : ℝ) _).trans
        exact Finset.single_le_sum (f := fun k => max 0
          ((weakCertConst weakBasePlan (weakCoeffRequestOne req))^[k] 1))
          (fun k _ => le_max_left (0 : ℝ) _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
      refine ⟨weakReserve x.inst C.i, weakWeight x.inst C.i, ?_, ?_,
        weakCertified_mono_cost hc hprice (heps _).le⟩
      · exact zero_le_one.trans (le_add_of_nonneg_right
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      · change 1 + ((C.i - C.M : ℕ) : ℝ) / (R.J : ℝ) ≤ 2
        have hJ : (0 : ℝ) < R.J := Nat.cast_pos.mpr (by have := R.hJ; omega)
        have hc : ((C.i - C.M : ℕ) : ℝ) ≤ R.J := by
          have hn : C.i - C.M ≤ R.J := by have := C.hiJ; omega
          exact_mod_cast hn
        have hd := (div_le_one hJ).mpr hc
        linarith only [hd]
  obtain ⟨mres, L, hm, hm2, hc⟩ := hcert
  have hcar : IsCarrierStart C.D.α C.D.q C.D.Λ R.bw 1 400 C.j₀ := by
    rw [C.hα, C.hq, C.hΛ]
    exact C.carrier
  have hstart := Providers.GenSem.startBound_of_carrierStart hΛ le_rfl
    (by norm_num : (1 : ℝ) ≤ 400) hcar
  have hpar : C.G.IsSlotTransverse := hc.weakHolGen.isSlotTransverse hΛ hζ R.hbw hstart
  have hcell := weakData_cellScaleSq_pos C.D hΛ hζ hband C.i
  have hτ := Construction.Stream.ocTau_pos (α := C.D.α) (q := C.D.q) (m := C.i) hΛ
  have hab (slot : OddSlot) : weakSlotLeft C.D C.i slot.1 ≤ weakSlotRight C.D C.i slot.1 := by
    apply (div_le_div_iff_of_pos_right hcell).mpr
    dsimp only [OCData.slotStart]
    exact mul_le_mul_of_nonneg_right (by linarith) hτ.le
  have hdata (slot : OddSlot) : (weakPositiveNativeData C.i C.G slot).edge =
      liftEdges (C.D.cellScaleSq C.G.level) 1 (C.G.fam.fiber slot (C.G.actual slot)) := by
    simp only [weakPositiveNativeData, familyLiftData, hlevel, div_self (heps _).ne']
  have hclock (slot : OddSlot) (t : ℝ)
      (ht : t ∈ Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1)) :
      C.D.cellScaleSq C.G.level * t ∈ ocPulseWindow C.D.α C.D.q C.D.Λ C.G.level slot.1 := by
    simpa only [hlevel] using weak_lift_clock_in_pulse_window C.D hΛ hζ hband C.i slot.1 t ht
  refine { transverse := ?_, measurable := ?_, smooth := ?_, source := ?_ }
  · intro slot
    apply windowEdges_transverse
    have heq : slotParallel slot.1 = pulseParallel slot.1 := by
      have hodd := slot.2
      have hmod : slot.1 % 4 = 1 ∨ slot.1 % 4 = 3 := by obtain ⟨k, hk⟩ := hodd; omega
      rcases hmod with h1 | h3
      · simp only [slotParallel, pulseParallel, h1]; norm_num
      · simp only [slotParallel, pulseParallel, h3]; norm_num
    rw [← heq]
    simpa only [weakPositiveNativeData, weakSlotLeft, weakSlotRight, hlevel] using native_lift_fiber_transverse C.G hpar
      hΛ hζ hband slot (C.D.eps (C.i - 1))
  · intro slot
    apply windowEdges_coefficient_measurable _ _ (hab slot)
    rw [hdata]
    intro v u d γ hγ I X z
    obtain ⟨δ', hδ', rfl⟩ := List.mem_map.mp hγ
    obtain ⟨δ, _hd, he⟩ := fiber_coefficient_identity C.G.fam slot (C.G.actual slot) v u d δ' hδ'
    dsimp only
    rw [he]
    have htime := weakHolGen_flux_time_measurable hc.weakHolGen slot (C.G.actual slot) v u δ d.1 I
      ((1 : ℝ) • X) z
    let clock : Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1) →
        ocPulseWindow C.D.α C.D.q C.D.Λ C.G.level slot.1 := fun t =>
      ⟨C.D.cellScaleSq C.G.level * t.1, hclock slot t.1 t.2⟩
    exact htime.comp ((measurable_const.mul measurable_subtype_coe).subtype_mk : Measurable clock)
  · intro slot
    apply windowEdges_boxSmooth
    rw [hdata]
    apply liftEdges_boxSmooth_of_joint
      (C.D.cellScaleSq C.G.level) 1 (C.G.fam.fiber slot (C.G.actual slot)) qs qf
      (Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1))
      (ocPulseWindow C.D.α C.D.q C.D.Λ C.G.level slot.1) (hclock slot)
    intro v u d γ hγ I t ht
    obtain ⟨δ, _hd, he⟩ := fiber_coefficient_identity C.G.fam slot (C.G.actual slot) v u d γ hγ
    rw [he]
    exact weakCertified_native_flux_joint_contDiff hc hcost hm hm2 hi hj R.hbw
      (heps _) (heps _) hpar slot (hnat.2.2.1 slot) v u δ (hlen v u δ) d.1 I (qs + qf) t ht
  · intro S hS slot
    apply windowEdges_scaled_envelope
    rw [hdata]
    apply weak_source_fixed_cap_envelope C.G.fam (weakParentCap R) hcap slot (C.G.actual slot)
      (weakParentMass C) _ (C.D.cellScaleSq C.G.level) 1 A hA qs qf S hS.row_sum hS.col_sum
    intro v u δ d _hd I r hr q hq
    apply jetSup_clock_scaled_le _ _ (C.D.cellScaleSq C.G.level) 1 _ r q _ (hclock slot)
    intro t ht X z
    have hh := hjet C.D C.Dm C.j₀ C.G hi hj (heps _) (heps _) hpar cost mres L hcost hm hm2 hc
      slot (hnat.2.2.1 slot) v u δ (hlen v u δ) d I 1 zero_le_one t ht r q
      (Nat.add_le_add hr hq) X z
    simpa only [A, one_pow, mul_one, mul_assoc] using hh

/-- Expose the existing zero lift-order floors. -/
theorem weak_parent_setting_selector_at : WeakParentSettingAssemblyAtStatement := by
  intro B
  refine ⟨128, le_rfl, ?_⟩
  intro R _
  let H := R.J * R.R
  let K := weakParentSlow R
  let k := weakParentFast R
  let qs := K + 4 * (H + 1) * (R.N + weakParentCap R) ^ 2
  obtain ⟨CG, m₀, _hCG, hm₀, hmetric⟩ := terminal_lift_metric_certificates
    B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq R.Λ R.hΛ B.ζ B.hζ qs
  let Cw : ℕ → ℝ := fun n => 2 * pulseFastDerivativeConstant n
  intro sX sZ
  refine ⟨(CG, Cw), fun _ => ⟨m₀, ?_⟩⟩
  intro C _ hM c Cj S P hgeom hn hS
  have hΛ : 1 ≤ C.D.Λ := by rw [C.hΛ]; have := R.hΛ; omega
  have hζ : IsFastProfile C.D.ζ := C.hζ.symm ▸ B.hζ
  have hi : 1 ≤ C.i := by have := C.hi; omega
  have hterm : C.D.term < C.i := by rw [C.term]; exact C.hi
  obtain ⟨hρ, hcell, hlam⟩ := plateau_parent_lift_radius_bounds C.D hgeom.q_gt
    hgeom.Λ_ge hζ hgeom.band C.i hterm
  let ρ := C.D.eps (C.i - 1)
  refine ⟨fun slot => ?_⟩
  by_cases hzero : R.R = 0
  · let emptyEdge : ConstituentEdges 2 (fun v : CompIn C.G.comps => ScalarH v.1.root) :=
      fun _ _ _ => []
    let Q := familyLiftData C.D C.i slot.1 (nativeChain C.i slot.1) ρ emptyEdge
    have hz (v u : CompIn C.G.comps) (d : Finset.Icc 2 2) : Q.edge v u d = [] := by
      simp only [Q, familyLiftData, liftEdges, emptyEdge, List.map_nil]
    have hzNative (v u : CompIn C.G.comps) (d : Finset.Icc 2 C.Dm) :
        (weakPositiveNativeData C.i C.G slot).edge v u d = [] := by
      let weakParentZeroDepthIsEmpty : IsEmpty (C.G.fam.Γ v u) := hn.empty_zero hzero v u
      simp [weakPositiveNativeData, familyLiftData, liftEdges, ChartedFamily.fiber]
    have hg := hmetric (CompIn C.G.comps) (fun v => ScalarH v.1.root) 2 C.D
      C.hα C.hq C.hΛ C.hζ C.stream hgeom.band C.i (by have := C.hi; omega)
      slot.1 slot.2 ρ hρ.le emptyEdge
    let a := weakSlotLeft C.D C.i slot.1
    let b := weakSlotRight C.D C.i slot.1
    let qsEmpty := K + 4 * (H + 1) * (R.N + 2) ^ 2
    have hres := effective_lift_reserves_le K k k H R.N (weakParentCap R) 2
      (le_max_left _ _)
    let qf := max k (k + 2) + H * 2 + 2 * R.N + 2 * 2
    have hw := native_lift_balanced_drift_sup_of_bound C.D C.i slot.1
      (nativeChain C.i slot.1) ρ emptyEdge a b qf Cw
      (fun n _hn t _ht z => terminal_plateau_balanced_drift_bound
        B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq R.Λ R.hΛ B.ζ B.hζ C.D
        C.hα C.hq C.hΛ C.hζ hgeom.band C.i hterm.le hi slot.1 slot.2 n t z)
    have hdepth : HasDepthAtMost Q.edge H := by
      intro path
      refine ⟨0, ?_⟩
      intro d
      rw [hz]
    have hsource : IsScaledJetEnvelope (weakParentMass C) Q.edge (Set.Icc a b)
        (ρ / C.D.eps (C.i - 1)) Cj qsEmpty qf (weakParentPrice C) S.1 := by
      refine ⟨hS.nonneg, hS.row_sum, hS.col_sum, ?_⟩
      intro v u r _ q _
      simp only [hz, List.map_nil, List.sum_nil, Finset.sum_const_zero, mul_zero]
      exact zero_le
    have hsetting := native_lift_setting_of_fiber_facts C.D C.i hi hΛ hζ hgeom.band
      slot ρ hρ hcell hlam Q rfl rfl rfl (weakParentMass C) hn.mass_pos
      H R.N K k k R.hN (le_refl 2) CG Cw Cj (weakParentPrice C) S.1
      hg.2 (fun r hr => hg.1 r (hr.trans hres.1)) hw hdepth
      (fun v u d γ hγ => by rw [hz] at hγ; contradiction)
      (fun v u d γ hγ => by rw [hz] at hγ; contradiction)
      (fun v u d γ hγ => by rw [hz] at hγ; contradiction) hsource
    have hex := Providers.cycle_lift_exists R.N K k k 2 H CG Cw Cj Q
      (weakParentMass C) a b (C.D.eps C.i) (C.D.kap C.i) (C.D.kap (C.i - 1))
      ρ (C.D.eps (C.i - 1)) (C.D.eps C.i / Real.sqrt (C.D.kap C.i))
      (ocDStar C.D.q C.D.Λ C.i (C.D.kap C.i) (C.D.kap (C.i - 1)))
      (ocDStar C.D.q C.D.Λ C.i (C.D.kap C.i) (C.D.kap (C.i - 1)) / ρ)
      (ρ / C.D.eps (C.i - 1)) (pulseParallel slot.1)
      (pulseShearProfile C.D.α C.D.q C.D.Λ C.i C.D.ζ (C.D.kap C.i) slot.1)
      qsEmpty qf (weakParentPrice C) S.1 hsetting
    let Cc := Classical.choose hex
    have hc := Classical.choose_spec hex
    refine {
      cap := 2
      cap_ge := le_rfl
      cap_le := le_max_left _ _
      Q := Q
      price := weakParentPrice C
      metric_eq := rfl
      drift_eq := rfl
      eta_eq := rfl
      edge_agree := Or.inl ⟨hz, hzNative⟩
      source_eq := ?_
      edge_fast := by
        intro S _hS _hn v u d γ hγ _α
        rw [hz] at hγ
        contradiction
      setting := hsetting
      coeff := Cc
      sequence := hc
      ambient := weak_root_sequence_degree_congr Q (weakPositiveNativeData C.i C.G slot)
        rfl rfl rfl hz hzNative _ _ R.N H a b Cc hc }
    intro Dc a₀ hh n _hn t _ht X z
    exact congrFun (congrFun
      (weak_root_source_degree_congr Q (weakPositiveNativeData C.i C.G slot)
        rfl rfl rfl hz hzNative Dc a₀ hh n t) X) z
  · have hR : 1 ≤ R.R := by omega
    have hprod : 1 ≤ R.J * R.N := by
      simpa only [one_mul] using Nat.mul_le_mul R.hJ R.hN
    have hKD : weakParentCap R ≤ C.Dm := by
      have hb := hn.cap_nonempty hR
      unfold weakParentCap
      omega
    have hcapN : R.N ≤ weakParentCap R := by
      have hp : R.N ≤ R.J * R.N := by
        simpa only [one_mul] using Nat.mul_le_mul_right R.N R.hJ
      exact hp.trans ((Nat.le_add_left _ _).trans (le_max_right _ _))
    let raw := weakPositiveNativeData C.i C.G slot
    let a := weakSlotLeft C.D C.i slot.1
    let b := weakSlotRight C.D C.i slot.1
    let Q := restrictLiftData (weakParentCap R) hKD {raw with edge := windowEdges a b raw.edge}
    let qf := max k (k + 2) + H * weakParentCap R + 2 * R.N + 2 * weakParentCap R
    have hz (v u : CompIn C.G.comps) (d : Finset.Icc 2 C.Dm)
        (hd : weakParentCap R < d.1) : raw.edge v u d = [] := hn.cap slot v u d hd
    have hzClip (v u : CompIn C.G.comps) (d : Finset.Icc 2 C.Dm)
        (hd : weakParentCap R < d.1) : windowEdges a b raw.edge v u d = [] := by
      simp only [windowEdges, hz v u d hd, List.map_nil]
    have hg := hmetric (CompIn C.G.comps) (fun v => ScalarH v.1.root) C.Dm C.D
      C.hα C.hq C.hΛ C.hζ C.stream hgeom.band C.i (by have := C.hi; omega)
      slot.1 slot.2 ρ hρ.le (C.G.fam.fiber slot (C.G.actual slot))
    have hw := native_lift_balanced_drift_sup_of_bound C.D C.i slot.1
      (nativeChain C.i slot.1) ρ (C.G.fam.fiber slot (C.G.actual slot)) a b qf Cw
      (fun n _hn t _ht z => terminal_plateau_balanced_drift_bound
        B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq R.Λ R.hΛ B.ζ B.hζ C.D
        C.hα C.hq C.hΛ C.hζ hgeom.band C.i hterm.le hi slot.1 slot.2 n t z)
    have hdepth : HasDepthAtMost Q.edge H :=
      restrictSource_depth _ hKD _ (windowEdges_depth a b raw.edge
        (liftEdges_depth _ _ _ (chartedFiber_depth C.G.fam slot (C.G.actual slot) hn.depth)))
    have hsource : IsScaledJetEnvelope (weakParentMass C) Q.edge (Set.Icc a b)
        (ρ / C.D.eps (C.i - 1)) Cj qs qf (weakParentPrice C) S.1 := by
      have he := restrictSource_scaled_envelope (weakParentCap R) hKD
        (windowEdges a b raw.edge) hzClip (weakParentMass C) (Set.Icc a b) 1 Cj
        qs qf (weakParentPrice C) S.1 (hn.source S.1 hS slot)
      simpa only [Q, restrictLiftData, ρ, div_self hρ.ne'] using he
    have hsetting := native_lift_setting_of_fiber_facts C.D C.i hi hΛ hζ hgeom.band
      slot ρ hρ hcell hlam Q rfl rfl rfl (weakParentMass C) hn.mass_pos
      H R.N K k k R.hN (le_max_left _ _) CG Cw Cj (weakParentPrice C) S.1
      hg.2 hg.1 hw hdepth
      (fun v u d γ hγ => hn.transverse slot v u (degreeRangeInclusion _ _ hKD d) γ hγ)
      (fun v u d γ hγ => hn.measurable slot v u (degreeRangeInclusion _ _ hKD d) γ hγ)
      (fun v u d γ hγ => hn.smooth slot v u (degreeRangeInclusion _ _ hKD d) γ hγ) hsource
    have hex := effective_window_lift_exists_with_restricted hsetting hz
    let Cc := Classical.choose hex
    have hc := Classical.choose_spec hex
    refine {
      cap := weakParentCap R
      cap_ge := le_max_left _ _
      cap_le := le_rfl
      Q := Q
      price := weakParentPrice C
      metric_eq := rfl
      drift_eq := rfl
      eta_eq := rfl
      edge_agree := Or.inr ⟨hKD, hz, by
        intro t ht
        exact windowEdges_agree a b
          (restrictConstituentEdges (weakParentCap R) hKD raw.edge) t ht⟩
      source_eq := ?_
      edge_fast := by
        intro S hS hn v u d γ hγ α
        exact weakPositive_windowEdges_fast raw.edge a b S hS hn v u
          (degreeRangeInclusion _ _ hKD d) γ hγ α
      setting := hsetting
      coeff := Cc
      sequence := hc.1
      ambient := hc.2 }
    intro Dc a₀ hh n hnN t ht X z
    have hs := liftCellSource_restrict_effective_order (weakParentCap R) hKD
      {raw with edge := windowEdges a b raw.edge} hzClip Dc a₀ hh n (hnN.trans hcapN) t
    calc
      _ = liftCellSource {raw with edge := windowEdges a b raw.edge} Dc a₀ hh n t X z :=
        congrFun (congrFun hs.symm X) z
      _ = liftCellSource raw Dc a₀ hh n t X z :=
        (liftCellSource_edge_slow_open_congr isOpen_univ raw (windowEdges a b raw.edge)
          Dc a₀ hh n t (windowEdges_agree a b raw.edge t ht) X (Set.mem_univ X) z).symm

/-- Slot-lift interface: explicit cap and orders, carrier `(1, 400)`, and no lift-order floor. -/
def WeakPlateauParentSettingAt : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr →
    ∀ sX sZ : ℕ,
    ∃ P : WeakPositiveParameters Nw (Jw * Rw) (Lr + 3),
    P.capMax = max 2 (1 + Jw * Nw) ∧
    P.slowOrder = Lr + 3 + (Nw + P.capMax) ∧ P.fastOrder = Lr + 3 ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw 1 400 j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm bw j₀),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu)
        M Jw (D.termRW σw M) 0 stage →
    ∀ i, M < i → i ≤ M + Jw →
      WeakPositiveGeometry P i (stage i) ∧
      Nonempty (∀ slot : OddSlot, WeakPositiveSlot P i (stage i)
        (fun v => weakMass D Nw Jw η₀ v.1) slot)


/-- Expose the choices of the complete weak factory without changing its old interface. -/
theorem weak_plateau_parent_setting_at : WeakPlateauParentSettingAt := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let B : WeakParentBase := ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  obtain ⟨Λg, hΛg, hg⟩ := weak_parent_geometry_at B
  obtain ⟨Λn, _hΛn, hn⟩ := weak_parent_native_coefficient_facts_at B
  obtain ⟨Λm, _hΛm, hm⟩ := weak_parent_mass_sums_at B
  obtain ⟨Λa, _hΛa, ha⟩ := weak_parent_setting_selector_at B
  refine ⟨max Λg (max Λn (max Λm Λa)), by omega, ?_⟩
  intro Λ hΛ bw hbw hbw1 J N Rw η σ hJ hN hη hη1 hσ hσ1 Lr hLr sX sZ
  let R : WeakParentMenu B := ⟨Λ, by omega, bw, hbw, hbw1, J, N, Rw, η, σ,
    hJ, hN, hη, hη1, hσ, hσ1, Lr, hLr⟩
  obtain ⟨c, hg⟩ := hg R (by change Λg ≤ Λ; omega) sX sZ
  obtain ⟨Cj, hn⟩ := hn R (by change Λn ≤ Λ; omega) sX sZ
  obtain ⟨S, hm⟩ := hm R (by change Λm ≤ Λ; omega) sX sZ
  obtain ⟨g, ha⟩ := ha R (by change Λa ≤ Λ; omega) sX sZ
  let P := weakParentParameters R g.1 g.2 Cj S.1 c.1 S.2 c.2
  refine ⟨P, rfl, rfl, rfl, ?_⟩
  intro j₀ hcarrier
  obtain ⟨Mg, hg⟩ := hg j₀
  obtain ⟨Mn, hn⟩ := hn j₀
  obtain ⟨Mm, hm⟩ := hm j₀
  obtain ⟨Ma, ha⟩ := ha j₀
  refine ⟨max Mg (max Mn (max Mm Ma)), ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage hconstruction i hi hiJ
  let C : WeakParentCase R sX sZ := ⟨j₀, M, hcarrier, D, hDα, hDq, hDΛ, hDζ, hstream,
    hband, hterm, PW, Dm, stage, hconstruction, i, hi, hiJ⟩
  have hG : WeakPositiveGeometry P i (stage i) := hg C rfl (by change Mg ≤ M; omega)
  exact ⟨hG, ha C rfl (by change Ma ≤ M; omega) c Cj S hG
    (weak_parent_native_facts_of_coefficients C Cj (hn C rfl (by change Mn ≤ M; omega)))
    (hm C rfl (by change Mm ≤ M; omega))⟩

end AVRegularity.Finite.WeakLift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped Classical ENNReal
namespace AVRegularity.Finite.WeakLift

/-! The complete actual weak coefficient selector: original templates, fixed-cap
record sums and uniform constants before every carrier, level and construction. -/

open Construction.Preservation.FullLift CycleComparison.Lift EntryWeakProofs
open Providers.WeakGen WeakEntryProofs.Assembly

private theorem weak_parent_case_native_geometry {B : WeakParentBase} {R : WeakParentMenu B}
    {sX sZ : ℕ} (C : WeakParentCase R sX sZ) :
    C.G.level = C.i ∧ C.G.IsNatural (C.M + R.J) ∧
    (∀ v u (γ : C.G.fam.Γ v u),
      (C.G.fam.identity v u γ).record.length ≤ C.D.eps C.G.level) ∧
    ∀ v u (γ : C.G.fam.Γ v u), (C.G.fam.identity v u γ).maxOrder ≤ weakParentCap R := by
  have hlevel : C.G.level = C.i := weakConstruction_level C.PW _ C.M R.J 0 _
    C.stage C.construction C.i C.hi.le C.hiJ
  have hnat : C.G.IsNatural (C.M + R.J) := by
    by_cases hi : C.i = C.M + R.J
    · simpa only [WeakParentCase.G, hi] using C.construction.2.1.2.2.2
    · exact weakConstruction_output_natural C.PW _ C.M R.J 0 _ C.stage
        C.construction C.i C.hi.le (by have := C.hiJ; omega)
  refine ⟨hlevel, hnat, ?_, ?_⟩
  · intro v u γ
    by_cases hi : C.i = C.M + R.J
    · have hroot := C.construction.2.1
      rw [← hi] at hroot
      exact ((hroot.2.2.1 v u).false γ).elim
    · have hp := C.construction.2.2 (C.i + 1) (by have := C.hi; omega)
        (by have := C.hiJ; omega)
      have hlen := IsWeakPassage.length_eq hp.1 hp.2
      rw [Nat.add_sub_cancel] at hlen
      have hnext := weakConstruction_level C.PW _ C.M R.J 0 _ C.stage
        C.construction (C.i + 1) (by have := C.hi; omega) (by have := C.hiJ; omega)
      rw [hlen v u γ, hnext, hlevel]
      exact Applications.eps_antitone (C.hq.symm ▸ B.hq.1) (C.hΛ.symm ▸ R.hΛ) (Nat.le_succ _)
  · intro v u γ
    have hb := weakConstruction_stage_maxOrderBound C.PW _ C.M R.J 0 _
      C.construction C.i C.hi.le C.hiJ v u γ
    exact hb.trans (le_max_right _ _)

/-- Uniform actual native coefficient facts; no unit certificate is asserted. -/
theorem weak_parent_native_coefficient_facts : WeakParentNativeCoefficientFactsStatement := by
  intro B
  refine ⟨max 128 (weakCommonCoeffPlan.baseThreshold (weakParentCoefficientBase B)),
    le_max_left _ _, ?_⟩
  intro R hbase _
  have hb : weakCommonCoeffPlan.baseThreshold (weakParentCoefficientBase B) ≤ R.Λ :=
    (le_max_right _ _).trans hbase
  refine ⟨0, 0, ?_⟩
  intro sX sZ _ _
  let req := weakParentCertificateRequest R sX sZ
  let qs := weakParentSlow R + 4 * (R.J * R.R + 1) * (R.N + weakParentCap R) ^ 2
  let qf := max (weakParentFast R) (weakParentFast R + 2) + R.J * R.R * weakParentCap R +
    2 * R.N + 2 * weakParentCap R
  obtain ⟨BJ, hBJ, hjet⟩ := uniform_weak_native_coefficient_jet_bounds R.bw R.hbw (qs + qf)
  let cost := weakQuietCertificatePrice req
  have hcost : 0 ≤ cost := Finset.sum_nonneg fun _ _ => le_max_left (0 : ℝ) _
  let A : ℕ → ℕ → ℝ := fun r q => BJ (r + q) * (2 * cost)
  have hA : ∀ r q, 0 ≤ A r q := fun r q => mul_nonneg (hBJ _) (mul_nonneg (by norm_num) hcost)
  let Cj : ℕ → ℕ → ℝ := fun r q => ((weakParentCap R + 1 : ℕ) : ℝ) * 2 ^ weakParentCap R * A r q
  refine ⟨Cj, ?_⟩
  intro j₀
  refine ⟨max (j₀ + 2) (weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne req) j₀), ?_⟩
  intro C hj₀ hM
  have hfloor : j₀ + 2 ≤ C.M := (le_max_left _ _).trans hM
  have hl : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne req) C.j₀ ≤ C.M := by
    rw [hj₀]
    exact (le_max_right _ _).trans hM
  have hΛ : 1 ≤ C.D.Λ := by rw [C.hΛ]; have := R.hΛ; omega
  have hζ : IsFastProfile C.D.ζ := C.hζ.symm ▸ B.hζ
  have hband : IsOCBandChain C.D.α C.D.q C.D.Λ C.D.ζ C.D.term C.D.κ := by
    rw [C.hα, C.hq, C.hΛ, C.hζ, C.term]
    exact C.band
  have heps (m : ℕ) : 0 < C.D.eps m := Construction.Stream.ocEpsilon_pos hΛ
  obtain ⟨hlevel, hnat, hlen, hcap⟩ := weak_parent_case_native_geometry C
  have hi : 1 ≤ C.G.level := by rw [hlevel]; have := C.hi; omega
  have hj : C.j₀ ≤ C.G.level := by rw [hlevel, hj₀]; have := C.hi; omega
  have hcert : ∃ mres : ℝ, ∃ L : ℕ, 0 ≤ mres ∧ mres ≤ 2 ∧ WeakCertified cost mres L C.G := by
    by_cases hR : R.R = 0
    · refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
      intro v u γ
      exact ((weak_parent_case_empty_zero C hR v u).false γ).elim
    · have hR1 : 1 ≤ R.R := by omega
      let x := weakParentCommonCase C hR1 hb hl
      obtain ⟨_hc, hc⟩ := weak_parent_case_certified C hR1 hb hl
      have hn : C.M + R.J - C.i ≤ R.J := by have := C.hi; omega
      have hprice : ((weakCertConst weakBasePlan (weakCoeffRequestOne req))^[C.M + R.J - C.i] 1) ≤
          cost := by
        apply (le_max_right (0 : ℝ) _).trans
        exact Finset.single_le_sum (f := fun k => max 0
          ((weakCertConst weakBasePlan (weakCoeffRequestOne req))^[k] 1))
          (fun k _ => le_max_left (0 : ℝ) _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
      refine ⟨weakReserve x.inst C.i, weakWeight x.inst C.i, ?_, ?_,
        weakCertified_mono_cost hc hprice (heps _).le⟩
      · exact zero_le_one.trans (le_add_of_nonneg_right
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      · change 1 + ((C.i - C.M : ℕ) : ℝ) / (R.J : ℝ) ≤ 2
        have hJ : (0 : ℝ) < R.J := Nat.cast_pos.mpr (by have := R.hJ; omega)
        have hc : ((C.i - C.M : ℕ) : ℝ) ≤ R.J := by
          have hn : C.i - C.M ≤ R.J := by have := C.hiJ; omega
          exact_mod_cast hn
        have hd := (div_le_one hJ).mpr hc
        linarith only [hd]
  obtain ⟨mres, L, hm, hm2, hc⟩ := hcert
  have hcar : IsCarrierStart C.D.α C.D.q C.D.Λ R.bw 1 400 C.j₀ := by
    rw [C.hα, C.hq, C.hΛ]
    exact C.carrier
  have hstart := Providers.GenSem.startBound_of_carrierStart hΛ le_rfl
    (by norm_num : (1 : ℝ) ≤ 400) hcar
  have hpar : C.G.IsSlotTransverse := hc.weakHolGen.isSlotTransverse hΛ hζ R.hbw hstart
  have hcell := weakData_cellScaleSq_pos C.D hΛ hζ hband C.i
  have hτ := Construction.Stream.ocTau_pos (α := C.D.α) (q := C.D.q) (m := C.i) hΛ
  have hab (slot : OddSlot) : weakSlotLeft C.D C.i slot.1 ≤ weakSlotRight C.D C.i slot.1 := by
    apply (div_le_div_iff_of_pos_right hcell).mpr
    dsimp only [OCData.slotStart]
    exact mul_le_mul_of_nonneg_right (by linarith) hτ.le
  have hdata (slot : OddSlot) : (weakPositiveNativeData C.i C.G slot).edge =
      liftEdges (C.D.cellScaleSq C.G.level) 1 (C.G.fam.fiber slot (C.G.actual slot)) := by
    simp only [weakPositiveNativeData, familyLiftData, hlevel, div_self (heps _).ne']
  have hclock (slot : OddSlot) (t : ℝ)
      (ht : t ∈ Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1)) :
      C.D.cellScaleSq C.G.level * t ∈ ocPulseWindow C.D.α C.D.q C.D.Λ C.G.level slot.1 := by
    simpa only [hlevel] using weak_lift_clock_in_pulse_window C.D hΛ hζ hband C.i slot.1 t ht
  refine { transverse := ?_, measurable := ?_, smooth := ?_, source := ?_ }
  · intro slot
    apply windowEdges_transverse
    have heq : slotParallel slot.1 = pulseParallel slot.1 := by
      have hodd := slot.2
      have hmod : slot.1 % 4 = 1 ∨ slot.1 % 4 = 3 := by obtain ⟨k, hk⟩ := hodd; omega
      rcases hmod with h1 | h3
      · simp only [slotParallel, pulseParallel, h1]; norm_num
      · simp only [slotParallel, pulseParallel, h3]; norm_num
    rw [← heq]
    simpa only [weakPositiveNativeData, weakSlotLeft, weakSlotRight, hlevel] using native_lift_fiber_transverse C.G hpar
      hΛ hζ hband slot (C.D.eps (C.i - 1))
  · intro slot
    apply windowEdges_coefficient_measurable _ _ (hab slot)
    rw [hdata]
    intro v u d γ hγ I X z
    obtain ⟨δ', hδ', rfl⟩ := List.mem_map.mp hγ
    obtain ⟨δ, _hd, he⟩ := fiber_coefficient_identity C.G.fam slot (C.G.actual slot) v u d δ' hδ'
    dsimp only
    rw [he]
    have htime := weakHolGen_flux_time_measurable hc.weakHolGen slot (C.G.actual slot) v u δ d.1 I
      ((1 : ℝ) • X) z
    let clock : Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1) →
        ocPulseWindow C.D.α C.D.q C.D.Λ C.G.level slot.1 := fun t =>
      ⟨C.D.cellScaleSq C.G.level * t.1, hclock slot t.1 t.2⟩
    exact htime.comp ((measurable_const.mul measurable_subtype_coe).subtype_mk : Measurable clock)
  · intro slot
    apply windowEdges_boxSmooth
    rw [hdata]
    apply liftEdges_boxSmooth_of_joint
      (C.D.cellScaleSq C.G.level) 1 (C.G.fam.fiber slot (C.G.actual slot)) qs qf
      (Set.Icc (weakSlotLeft C.D C.i slot.1) (weakSlotRight C.D C.i slot.1))
      (ocPulseWindow C.D.α C.D.q C.D.Λ C.G.level slot.1) (hclock slot)
    intro v u d γ hγ I t ht
    obtain ⟨δ, _hd, he⟩ := fiber_coefficient_identity C.G.fam slot (C.G.actual slot) v u d γ hγ
    rw [he]
    exact weakCertified_native_flux_joint_contDiff hc hcost hm hm2 hi hj R.hbw
      (heps _) (heps _) hpar slot (hnat.2.2.1 slot) v u δ (hlen v u δ) d.1 I (qs + qf) t ht
  · intro S hS slot
    apply windowEdges_scaled_envelope
    rw [hdata]
    apply weak_source_fixed_cap_envelope C.G.fam (weakParentCap R) hcap slot (C.G.actual slot)
      (weakParentMass C) _ (C.D.cellScaleSq C.G.level) 1 A hA qs qf S hS.row_sum hS.col_sum
    intro v u δ d _hd I r hr q hq
    apply jetSup_clock_scaled_le _ _ (C.D.cellScaleSq C.G.level) 1 _ r q _ (hclock slot)
    intro t ht X z
    have hh := hjet C.D C.Dm C.j₀ C.G hi hj (heps _) (heps _) hpar cost mres L hcost hm hm2 hc
      slot (hnat.2.2.1 slot) v u δ (hlen v u δ) d I 1 zero_le_one t ht r q
      (Nat.add_le_add hr hq) X z
    simpa only [A, one_pow, mul_one, mul_assoc] using hh

end AVRegularity.Finite.WeakLift
end
