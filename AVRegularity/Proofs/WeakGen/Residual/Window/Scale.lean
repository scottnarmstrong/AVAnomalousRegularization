-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder
public import AVRegularity.Proofs.WeakGen.Residual.Window.Bill
public import AVRegularity.CycleComparison.Reconstruction.PhysicalLiftPartition
import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
import AVRegularity.Construction.TerminalLift.Assembly
import AVRegularity.Finite.WeakPositive.PositiveInputJets
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleResidualDifferentiated

section
@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev MeasureTheory Filter Topology
open scoped Classical ENNReal
namespace AVRegularity.Finite.WeakLift

/-! **The at-form of the weak slot-lift factory.** The slot lifts of all the slots
come with the price `weakParentPrice C = recordMajorant (weakParentMass C) C.G.fam`: the proofs of
`weak_parent_setting_selector_at` and `weak_plateau_parent_setting_at` with the slot lifts named
(`price := weakParentPrice C` at both construction sites).

The degenerate cases are included: `R_w = 0` (the price is the record majorant of an empty
family). -/

open Construction.Preservation.FullLift Construction.TerminalLift CycleComparison.Lift EntryWeakProofs
open WeakEntryProofs WeakEntryProofs.Assembly Construction.Preservation.Ledger Providers.WeakGen

def WeakParentSettingAssemblyUniformAtStatement : Prop :=
  WeakParentUniformFactAtStatement (fun {_B} _R => (ℕ → ℝ) × (ℕ → ℝ))
    (fun {_B} R g {_sX _sZ} C => ∀ (c : {c : ℝ // 1 ≤ c}) (Cj : ℕ → ℕ → ℝ) (S : {S : ℝ // 0 ≤ S}),
      let P := weakParentParameters R g.1 g.2 Cj S.1 c.1 S.2 c.2
      WeakPositiveGeometry P C.i C.G → WeakParentNativeFacts C Cj →
      HasRealSchurBudget (weakParentPrice C) S.1 →
      ∃ pk : ∀ slot, WeakPositiveSlot P C.i C.G (weakParentMass C) slot,
        ∀ slot, (pk slot).price = weakParentPrice C)

theorem weak_parent_setting_selector_uniform_at :
    WeakParentSettingAssemblyUniformAtStatement := by
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
  suffices H : ∀ slot : OddSlot, ∃ pk : WeakPositiveSlot P C.i C.G (weakParentMass C) slot,
      pk.price = weakParentPrice C by
    choose pk hpk using H
    exact ⟨pk, hpk⟩
  intro slot
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
    refine ⟨{
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
        rfl rfl rfl hz hzNative _ _ R.N H a b Cc hc }, rfl⟩
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
    refine ⟨{
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
      ambient := hc.2 }, rfl⟩
    intro Dc a₀ hh n hnN t ht X z
    have hs := liftCellSource_restrict_effective_order (weakParentCap R) hKD
      {raw with edge := windowEdges a b raw.edge} hzClip Dc a₀ hh n (hnN.trans hcapN) t
    calc
      _ = liftCellSource {raw with edge := windowEdges a b raw.edge} Dc a₀ hh n t X z :=
        congrFun (congrFun hs.symm X) z
      _ = liftCellSource raw Dc a₀ hh n t X z :=
        (liftCellSource_edge_slow_open_congr isOpen_univ raw (windowEdges a b raw.edge)
          Dc a₀ hh n t (windowEdges_agree a b raw.edge t ht) X (Set.mem_univ X) z).symm


/-- Slot-lift interface: explicit cap/orders, carrier (1,400), and no lift-order floor. -/
def WeakPlateauParentSettingUniformAt : Prop :=
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
      ∃ pk : ∀ slot : OddSlot, WeakPositiveSlot P i (stage i)
        (fun v => weakMass D Nw Jw η₀ v.1) slot,
        ∀ slot, (pk slot).price = recordMajorant (fun v => weakMass D Nw Jw η₀ v.1) (stage i).fam


/-- Expose the choices of the complete weak factory without changing its old interface. -/
theorem weak_plateau_parent_setting_uniform_at : WeakPlateauParentSettingUniformAt := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let B : WeakParentBase := ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  obtain ⟨Λg, hΛg, hg⟩ := weak_parent_geometry_at B
  obtain ⟨Λn, _hΛn, hn⟩ := weak_parent_native_coefficient_facts_at B
  obtain ⟨Λm, _hΛm, hm⟩ := weak_parent_mass_sums_at B
  obtain ⟨Λa, _hΛa, ha⟩ := weak_parent_setting_selector_uniform_at B
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
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Window

/-! **From the coupled solution of the weak window to the system of the comparison error**.

The physical lift of the reconstruction window of a weak passage returns a solution of the coupled
system of the window's family at the slots `weakWindowSlots c i k₀`, forced by the residual
`(R_res, q_res)`. `weakErrSol_of_coupled_eq`: its truncation to order zero solves the capped kernel
system of the stage (`WeakErrSol`) with the truncated initial value and the truncated forcing; the
kernel lifts are the truncations of the `H¹` lift to the order `J_wN_w`. It is
`kernel_of_coupled_forced` at the stage: the coefficient is the stage's
(`weakWindow_edgeCoefficient`), it vanishes at the non-admissible orders
(`weakWindow_physCoeff_nonadmissible`), and the kernels have width zero
(`sysS_isoPairedKernel_zero`).

The degenerate cases are included: `R_res = 0`, `q_res = 0` gives the homogeneous system; at the
root the stage has no identity and the kernel lifts are vacuous. `J_wN_w ≤ k₀ + 1` is the only
condition on `k₀`. -/

open WeakEntryProofs WeakEntryProofs.Assembly Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The order `J_wN_w` of the kernel lifts is below every slot plus one. -/
theorem weakWindow_lift_le (c : WeakPassageInstance plan R) (i k₀ : ℕ)
    (hk₀ : A.Jw * A.Nw ≤ k₀ + 1) (v : CompIn (c.stage i).comps) :
    0 + (1 + A.Jw * A.Nw) - 1 ≤ weakWindowSlots c i k₀ v + 1 := by
  have := weakWindowSlots_ge c i k₀ v
  omega

/-- **The same, at given data**: an initial value, a flux and a scalar forcing at order zero that
are the truncations of those of the coupled solution. -/
theorem weakErrSol_of_coupled_eq (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (k₀ : ℕ) (hk₀ : A.Jw * A.Nw ≤ k₀ + 1)
    {f : ∀ v : CompIn (c.stage i).comps, TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root)}
    {Rres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {qres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root)}
    {u : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root)}
    {w : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v + 1) (ScalarH v.1.root)}
    {f₀ : ∀ v : CompIn (c.stage i).comps, TorusHk 0 (ScalarH v.1.root)}
    {F₀ : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {g₀ : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root)}
    (hc : IsCoupledWeakSolutionTorus (c.D.κ c.M) (r.tq i) (r.a + A.T₀) (streamVel (c.D.Φ i))
      (1 + A.Jw * A.Nw) (weakWindowSlots c i k₀)
      (edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i)
        (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ()) (weakWindowSlots c i k₀))
      f Rres qres u w)
    (hf : ∀ v, truncateTorusHk (Nat.zero_le _) (f v) = f₀ v)
    (hF : ∀ v t, truncateTorusHk (Nat.zero_le _) (Rres v t) = F₀ v t)
    (hg : ∀ v t, truncateTorusHk (Nat.zero_le _) (qres v t) = g₀ v t) :
    WeakErrSol c r i f₀ F₀ g₀
      (fun v t => truncateTorusHk (Nat.zero_le _) (u v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (w v t))
      (fun _ u' _ t => truncateTorusHk (weakWindow_lift_le c i k₀ hk₀ u') (w u' t)) :=
  kernel_of_coupled_forced_eq (P := fun v u γ n => (c.stage i).physCoeff v u γ n) le_rfl
    (fun _ => Nat.zero_le _) (weakWindow_lift_le c i k₀ hk₀)
    (weakWindow_edgeCoefficient c i hi hit (weakWindowSlots c i k₀))
    (weakWindow_physCoeff_nonadmissible c i hi hit k₀)
    (fun v u γ s => sysS_isoPairedKernel_zero c.P R.nW A.hφ₀ A.mass (c.stage i) v u γ s) hc
    hf hF hg

end AVRegularity.Providers.WeakGen.Window
end

section
open AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.Providers.WeakGen.Window

/-! **The orders of the reconstruction window of a weak passage**.

The physical lift asks its orders to satisfy `ReconOrders`. At a weak passage they are named
functions of the menu `A` and of the slot shift `k₀`, in the shape used at terminal entry: with
`D = weakDw A`, `N_c = N_w`, `H = weakH A`, `A_cl = weakAcl`, `K_max = weakKmax A k₀`,
`K_lift = weakKlift A k₀`, `L_lift = weakLlift A k₀`,

* `weakMprime A k₀ = A_cl + 1 + K_max + 2N_w + D`, the density order `m'`;
* `weakKres A k₀ = A_cl + 3 + K_max + N_w`, the residual reserve;
* `weakNchi A k₀ = A_cl + 2 + K_max + 2N_w + D`, the chart order;
* `weakKcFloor A k₀ = m' + k_res + N_w + 4`, the least coarse order `k_c`;
* `J_c = 0`, `p_c = 1`, `r₀ = k_c + (N_w + D) - 1`.

`weakReconOrders`: for `k_c ≥ weakKcFloor A k₀` these satisfy `ReconOrders`.

The degenerate cases are included: `J_w = N_w = 1`, `R_w = 0`, `k₀ = 0` gives `D = 2`, `K_max = 0`,
`m' = 6`, `k_res = 5`, `k_c ≥ 16`; nothing here reads the request or the plan. -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {B : WeakCoefficientBase}

/-- The density order `m'` of the weak window. -/
abbrev weakMprime (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  weakAcl + 1 + weakKmax A k₀ + 2 * A.Nw + weakDw A

/-- The residual reserve `k_res` of the weak window. -/
abbrev weakKres (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  weakAcl + 3 + weakKmax A k₀ + A.Nw

/-- The chart order `N_χ` of the weak window. -/
abbrev weakNchi (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  weakAcl + 2 + weakKmax A k₀ + 2 * A.Nw + weakDw A

/-- The least coarse order `k_c` of the weak window. -/
abbrev weakKcFloor (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  weakMprime A k₀ + weakKres A k₀ + A.Nw + 4

/-- **The orders of the weak window satisfy `ReconOrders`.** -/
theorem weakReconOrders (A : WeakCoefficientPhysical B) (k₀ kc : ℕ)
    (hkc : weakKcFloor A k₀ ≤ kc) :
    ReconOrders (weakDw A) A.Nw (weakH A) (weakKlift A k₀) (weakLlift A k₀) kc 0 1
      (kc + (A.Nw + weakDw A) - 1) (weakKmax A k₀) weakAcl (weakMprime A k₀) (weakKres A k₀)
      (weakNchi A k₀) := by
  have hN : 1 ≤ A.Nw := A.Nw_pos
  have hJN : 1 ≤ A.Jw * A.Nw := Nat.mul_pos A.Jw_pos A.Nw_pos
  have hD2 : 2 ≤ weakDw A := by show 2 ≤ 1 + A.Jw * A.Nw; omega
  have hDH : weakDw A ≤ weakDw A * (weakH A + 1) * A.Nw := by
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) hN)
  have hJ : 0 ≤ (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4) := Nat.zero_le _
  simp only [weakKcFloor, weakMprime, weakKres, weakNchi, weakKlift, weakLlift, weakAcl]
    at hkc ⊢
  generalize weakDw A * (weakH A + 1) * A.Nw = P at hDH ⊢
  generalize (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4) = Q at hJ ⊢
  generalize weakDw A = D at hD2 hDH hkc ⊢
  generalize weakKmax A k₀ = K at hkc ⊢
  exact
    { hD2 := hD2, hAcl := le_rfl, hK := by omega, hrL := by omega, hJL := by omega,
      hDL := by omega, hK2 := by omega, hord := by omega, hk := by omega, hNχ := by omega,
      hNχ' := by omega, hkres := by omega, hmr := by omega, hrW := by omega,
      hNco := by omega, hordd := by omega, hrK := by omega }

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.ChartTransport
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Window

/-! **The partition hypothesis of the weak window, in the window's own form** (a statement, the target of the adapter).

`WeakWindowPartitionAt` is the hypothesis `hPB` of `ReconPhysicalLiftStatement` at the data of
`WeakWindow`: for every Galerkin approximant `coarseTraj n W` of the coarse field, the partition
terms (the time derivatives of the family's weights against the pulse lifts of the approximant,
with the lift coefficients `h.CcR i`) are bounded in the `r_s`-weighted norm of order `K_max` by
`X_p` times the strong energy of the approximant at the lift length `ε_{i-1}` and the order
`ord`.

`weakReconPartition` proves this bound for a
general field in place of the approximant and with the cutoffs `ocCutoff` in place of the
family's weights. The adapter is: the weights of a natural stage are the cutoffs on the observed
(odd) pulses, and a Galerkin approximant is smooth, periodic and jointly measurable on the window
(`coarseTraj_contDiff`, `coarseTraj_periodic`, `jointlyMeas_coarseTraj`).

The degenerate cases are included: no observed pulse gives `0 ≤ …`; `W = 0` gives `0 ≤ 0`;
`K_max = 0` is the bound of the value alone. -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **`hPB` of the physical lift at the weak window**, for a coarse field `W`, the radius `rs`,
the orders `Kmax`, `ord` and the factor `Xp`. -/
def WeakWindowPartitionAt (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (Kmax ord : ℕ)
    (rs Xp : ℝ) {K' : ℕ} (W : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk K' (ScalarH v.1.root)) :
    Prop :=
  ∀ n, ∫⁻ t in Set.Icc (r.tq i) (r.tq i + wTobs c r i), (∑ j ∈ Finset.range (Kmax + 1),
      ∑ w' : DerivativeWord2 j,
        scalInt (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun x => rs ^ j • orderedDerivative w' (fun x' =>
            ∑ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
              deriv ((weakWindowFamily c i hi hit).weight (oddSlotOf k)) t •
                pulsePhysicalLift (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2)
                  (ocEpsilon c.D.q c.D.Λ (i - 1)) (ocEpsilon c.D.q c.D.Λ i)
                  (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
                    ocEpsilon c.D.q c.D.Λ (i - 1)) A.Nw (weakH A) (h.CcR i k)
                  (ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
                    (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
                  (ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
                    (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
                  (coarseTraj n W) t x') x)) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal Xp * classicalStrongEnergy (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
      (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (Set.Icc (r.tq i) (r.tq i + wTobs c r i)) ord (coarseTraj n W)

end AVRegularity.Providers.WeakGen.Window
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Providers.WeakGen.Window

/-! **The four steps of the weak window, statements and assembly**. Model: the four steps of the
reconstruction window at terminal entry.

* **Family step** `WeakFamilyStep` (`WeakFamilyBody`): descent, torus compatibility, the atlas, the
  pieces, injectivity, the partition at `weakCpart`, fast independence.
* **Lift-sequence step** `WeakSeqStep`: the lift sequences of the observed pulses on the clipped windows.
* **Lift-setting step** `WeakSettingStep` (`WeakSettingBody`): the lift settings and the grading.
* **Scale step** `WeakScaleStep` (`WeakScaleBody`): the scales and the construction fields.
* **Coarse** `WeakCoarseBody`: the hypotheses `hcs, hcd, hrep, hmean` supplied by the coarse defect statements (the coarse
  data are parameters of the assembly).
* **Assembly** `mkWeakReconWindow`: the window from the bodies.

Each step is stated at an instance `c`, a run `r`, a passage `i` and the slot shift `k₀`, under
the deadline `r.tq i < r.a + A.T₀` (on an empty window the comparison residual is proved directly). -/

open WeakEntryProofs WeakEntryProofs.Assembly

section Steps

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}
variable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
  (hit : i ≤ c.M + A.Jw)

/-- The left end of the clipped lift window of the pulse `k`, in cell time. -/
abbrev wSeqStart (k : ℤ) : ℝ :=
  max (((k : ℝ) - 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i) (r.tq i) /
    ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2

/-- The right end of the clipped lift window of the pulse `k`, in cell time. -/
abbrev wSeqEnd (k : ℤ) : ℝ :=
  min (((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i) (r.tq i + wTobs c r i) /
    ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2

/-! ### The family side -/

/-- The family side of the window at an atlas and a partition constant. -/
def WeakFamilyBody (k₀ : ℕ) (T : (weakWindowFamily c i hi hit).Atlas) (Cpart : ℝ) : Prop :=
  (weakWindowFamily c i hi hit).IsDescending (weakWindowSlots c i k₀) ∧
  IsTorusCompatible (weakWindowFamily c i hi hit) (fun _ => ()) (ocEpsilon c.D.q c.D.Λ (i - 1)) ∧
  T.IsConsecutiveClosed (Set.Icc (r.tq i) (r.tq i + wTobs c r i)) ∧
  T.CoversQuiet (ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i) (Set.Icc (r.tq i) (r.tq i + wTobs c r i)) ∧
  T.IsQuiet (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i) (ocEpsilon c.D.q c.D.Λ (i - 1)) ∧
  (∀ p q' (hpq : T.adjacent p q'),
    (((weakWindowFamily c i hi hit).piece p).output ∩
      ((weakWindowFamily c i hi hit).piece q').output ∩
      Set.Icc (r.tq i) (r.tq i + wTobs c r i)).Nonempty → T.sameCtx p q' hpq () ()) ∧
  (∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
    ((weakWindowFamily c i hi hit).piece (oddSlotOf k)).label =
        ocPulseChartIndex c.D.α c.D.q c.D.Λ i k ∧
      (∀ t, ⇑(((weakWindowFamily c i hi hit).piece (oddSlotOf k)).material t) =
        ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) t) ∧
      ocPulseWindow c.D.α c.D.q c.D.Λ i k ∩ Set.Icc (r.tq i) (r.tq i + wTobs c r i) ⊆
        ((weakWindowFamily c i hi hit).piece (oddSlotOf k)).output) ∧
  Set.InjOn oddSlotOf ↑(ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i)) ∧
  IsLiftPartition (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i))
    (fun k => (weakWindowFamily c i hi hit).weight (oddSlotOf k))
    (ocPulseWindow c.D.α c.D.q c.D.Λ i) (ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i)
    (Set.Icc (r.tq i) (r.tq i + wTobs c r i)) (ocTau c.D.α c.D.q c.D.Λ i) Cpart ∧
  (weakWindowFamily c i hi hit).IsFastIndependentOn
    (ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i ∩ Set.Icc (r.tq i) (r.tq i + wTobs c r i))

/-- **The family side of the window of a weak passage**, at the constant `weakCpart`. -/
def WeakFamilyStep (k₀ : ℕ) : Prop :=
  r.tq i < r.a + A.T₀ → ∃ T : (weakWindowFamily c i hi hit).Atlas,
    WeakFamilyBody c r i hi hit k₀ T weakCpart

/-! ### The lift sequences -/

/-- **The lift sequences of the observed pulses on the clipped windows**, at the
orders `(K_lift + D_w + 2, max (L_lift + 1) (L_lift + 2))`, for lift orders `(sX, sZ)` of the
request above them. -/
def WeakSeqStep (h : WeakComparisonInput r i) (k₀ : ℕ) : Prop :=
  r.tq i < r.a + A.T₀ → weakKlift A k₀ + weakDw A + 2 ≤ R.sX →
    max (weakLlift A k₀ + 1) (weakLlift A k₀ + 2) ≤ R.sZ →
    ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
      IsLiftSequence (wLiftData c i hi hit k) (weakKlift A k₀ + weakDw A + 2)
        (max (weakLlift A k₀ + 1) (weakLlift A k₀ + 2))
        (wSeqStart c r i k) (wSeqEnd c r i k) A.Nw (weakH A) (h.CcR i k)

/-! ### The lift settings and the grading -/

/-- The lift settings and the grading at given setting data. -/
def WeakSettingBody (h : WeakComparisonInput r i) (k₀ : ℕ) (qs qf : ℕ) (CGl Cw : ℕ → ℝ)
    (Ca Sb Cg : ℝ)
    (bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ) : Prop :=
  (∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
    IsLiftSetting (wLiftData c i hi hit k) (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (wSeqStart c r i k) (wSeqEnd c r i k) (ocEpsilon c.D.q c.D.Λ i) (c.D.κ c.M) (c.D.κ c.M)
      (ocEpsilon c.D.q c.D.Λ (i - 1)) (ocEpsilon c.D.q c.D.Λ (i - 1))
      (ocEll c.D.q c.D.Λ i (c.D.κ c.M)) (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M))
      (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
      (ocEpsilon c.D.q c.D.Λ (i - 1) / ocEpsilon c.D.q c.D.Λ (i - 1))
      (pulseParallel k) (pulseShearProfile c.D.α c.D.q c.D.Λ i c.D.ζ (c.D.κ c.M) k)
      (weakH A) A.Nw (weakKlift A k₀) (weakLlift A k₀) (weakLlift A k₀) qs qf CGl Cw
      (fun _ _ => Ca) bM Sb) ∧
  ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i), ∀ hh, hh ≤ weakH A →
    ∀ n, 1 ≤ n → n ≤ A.Nw → ∀ m'', 1 ≤ m'' → m'' ≤ n →
      ∀ j, j ≤ weakAcl + 2 + weakKmax A k₀ →
      schurEnergyJet (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (Set.Icc (wSeqStart c r i k) (wSeqEnd c r i k)) (weakLlift A k₀) j (h.CcR i k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ocEpsilon c.D.q c.D.Λ (i - 1) / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ (n - m'' + j))

/-- **The lift settings and the grading of the observed pulses**, at constants chosen
before the level. Ingredients: the slot lifts at the fixed carrier (`weakSlotLiftAt_planOK`),
`isLiftSetting_changeCap`, `isLiftSetting_transfer`, `edgeAgree_native_actual`,
`Providers.cycle_lift_grading`. -/
def WeakSettingStep (h : WeakComparisonInput r i) (k₀ : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb Cg : ℝ) : Prop :=
  r.tq i < r.a + A.T₀ → ∃ (qs qf : ℕ) (bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ),
    WeakSettingBody c r i hi hit h k₀ qs qf CGl Cw Ca Sb Cg bM

/-! ### Tw: the scales -/

/-- The scales of the window and the construction fields. -/
def WeakScaleBody : Prop :=
  0 < c.D.α ∧ c.D.α < 1 / 3 ∧ 0 < B.s ∧ B.s < (1 - c.D.α) / 2 ∧
  IsAdmissibleQ c.D.α B.s c.D.q ∧ IsFastProfile c.D.ζ ∧ 128 ≤ c.D.Λ ∧
  IsOCStreamSeq c.D.α c.D.q c.D.Λ c.D.ζ c.D.Φ ∧ 2 ≤ i ∧ 0 < c.D.κ c.M ∧ 0 < c.D.κ c.M ∧
  0 < wTobs c r i ∧ 0 < ocEpsilon c.D.q c.D.Λ i ∧ ocEpsilon c.D.q c.D.Λ i ≤ ocEpsilon c.D.q c.D.Λ i ∧
  ocEpsilon c.D.q c.D.Λ i ≤ ocEpsilon c.D.q c.D.Λ (i - 1) ∧
  ocEpsilon c.D.q c.D.Λ (i - 1) ≤ ocEpsilon c.D.q c.D.Λ (i - 1)

/-- **Tw (open, easy): the scales** under the deadline. -/
def WeakScaleStep : Prop := r.tq i < r.a + A.T₀ → WeakScaleBody c r i

/-! ### The coarse side -/

/-- The coarse hypotheses of the window: the coarse setting, the coarse defect equation and
the mean presentations, at the coarse data `AD, CE, Aedge, W, f0, Fc`. -/
def WeakCoarseBody (h : WeakComparisonInput r i)
    (aC B₀C lamC : ℝ) (pc Jc kc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (A.Nw + weakDw A), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn (c.stage i).comps) (d : Finset.Icc 2 (A.Nw + weakDw A)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn (c.stage i).comps) (CompIn (c.stage i).comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn (c.stage i).comps,
      TorusHk (kc + (Jc + weakH A + 3) * ((A.Nw + weakDw A) + 8 * pc + 4)) (ScalarH v.1.root))
    (W : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (kc + 1 + (A.Nw + weakDw A)) (ScalarH v.1.root))
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn (c.stage i).comps, ScalarH v.1.root) : Prop :=
  IsCoarseSetting (r.tq i) (r.tq i + wTobs c r i) (wRhoC c i) (c.D.κ c.M) aC B₀C lamC
    (streamVel (c.D.Φ (i - 1))) (A.Nw + weakDw A) (weakH A) pc Jc kc
    ((A.Nw + weakDw A) + 8 * pc + 4) (kc + (Jc + weakH A + 3) * ((A.Nw + weakDw A) + 8 * pc + 4))
    (wJm c) AD CE (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) Aedge Cstar Θc ∧
  IsCoarseDefect (r.tq i) (r.tq i + wTobs c r i) (c.D.κ c.M) (streamVel (c.D.Φ (i - 1)))
    (A.Nw + weakDw A) (weakH A) kc (kc + (Jc + weakH A + 3) * ((A.Nw + weakDw A) + 8 * pc + 4))
    AD CE (wJm c) f0 W Fc ∧
  (∀ t ∈ Set.Icc (r.tq i) (r.tq i + wTobs c r i), ∀ v,
    IsClassicalRep (W v t) (fun x => aRep t x v) (kc + (A.Nw + weakDw A) - 1)) ∧
  ∀ ρ ∈ Finset.range (weakH A + 1),
    IsMeanPresentation (Set.Icc (r.tq i) (r.tq i + wTobs c r i)) (A.Nw + weakDw A) ρ AD CE (wJm c)
      (gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i))
        (fun k => (weakWindowFamily c i hi hit).weight (oddSlotOf k))
        (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) (ocEpsilon c.D.q c.D.Λ (i - 1))
        (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1)) A.Nw ρ
        (fun k => wLiftData c i hi hit k) (h.CcR i)
        (fun k => ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
        (fun k => ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
          (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k)))

/-! ### The assembly -/

/-- **The window of a weak passage from the bodies of the steps.** -/
theorem mkWeakReconWindow (h : WeakComparisonInput r i) (k₀ : ℕ)
    (T : (weakWindowFamily c i hi hit).Atlas) (qs qf : ℕ)
    (CGl Cw : ℕ → ℝ) (Ca Sb Cg : ℝ)
    (bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ)
    (aC B₀C lamC : ℝ) (pc Jc kc : ℕ)
    (AD : ∀ d : Finset.Icc 2 (A.Nw + weakDw A), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : CompIn (c.stage i).comps) (d : Finset.Icc 2 (A.Nw + weakDw A)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (Aedge : Matrix (CompIn (c.stage i).comps) (CompIn (c.stage i).comps) ℝ) (Cstar Θc : ℝ)
    (f0 : ∀ v : CompIn (c.stage i).comps,
      TorusHk (kc + (Jc + weakH A + 3) * ((A.Nw + weakDw A) + 8 * pc + 4)) (ScalarH v.1.root))
    (W : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (kc + 1 + (A.Nw + weakDw A)) (ScalarH v.1.root))
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn (c.stage i).comps, ScalarH v.1.root)
    (hkc : 1 ≤ kc)
    (hfam : WeakFamilyBody c r i hi hit k₀ T weakCpart)
    (hset : WeakSettingBody c r i hi hit h k₀ qs qf CGl Cw Ca Sb Cg bM)
    (hseq : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
      IsLiftSequence (wLiftData c i hi hit k) (weakKlift A k₀ + weakDw A + 2)
        (max (weakLlift A k₀ + 1) (weakLlift A k₀ + 2))
        (wSeqStart c r i k) (wSeqEnd c r i k) A.Nw (weakH A) (h.CcR i k))
    (hsc : WeakScaleBody c r i)
    (hco : WeakCoarseBody c r i hi hit h aC B₀C lamC pc Jc kc AD CE Aedge Cstar Θc f0 W Fc aRep) :
    WeakWindow c r i hi hit h k₀ T weakCpart qs qf CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE Aedge
      Cstar Θc f0 W Fc aRep (kc + (A.Nw + weakDw A) - 1) := by
  obtain ⟨hdesc, htorus, hTcons, hTcov, hTq, hTact, hpp, hppinj, hpart, hquiet⟩ := hfam
  obtain ⟨hα₀, hα₁, hs₀, hs₁, hq, hζ, hΛ, hΦ, hm, hν, hB, hTobs, hρs, hρs_e, hρs_R, hRE⟩ := hsc
  obtain ⟨hcs, hcd, hrep, hmean⟩ := hco
  have hr₀ : kc + (A.Nw + weakDw A) - 1 ≤ kc + 1 + (A.Nw + weakDw A) := by
    generalize A.Nw + weakDw A = n; omega
  have hDr : A.Nw + weakDw A ≤ kc + (A.Nw + weakDw A) - 1 := by
    generalize A.Nw + weakDw A = n; omega
  exact
    { hα₀ := hα₀, hα₁ := hα₁, hs₀ := hs₀, hs₁ := hs₁, hq := hq, hζ := hζ, hΛ := hΛ, hΦ := hΦ,
      hm := hm, hν := hν, hB := hB, hTobs := hTobs, hρs := hρs, hρs_e := hρs_e, hρs_R := hρs_R,
      hRE := hRE, hdesc := hdesc, htorus := htorus, hTcons := hTcons, hTcov := hTcov, hTq := hTq,
      hTact := hTact, hpp := hpp, hppinj := hppinj, hpart := hpart, hquiet := hquiet,
      hsetting := hset.1, hseq := hseq, hcs := hcs, hcd := hcd, hrep := hrep,
      hr₀ := hr₀, hDr := hDr, hmean := hmean }

end Steps

end AVRegularity.Providers.WeakGen.Window
end

section
open Homogenization AVRegularity.EntryWeakProofs AVRegularity.Construction.Stream
namespace AVRegularity.Providers.WeakGen.Window

/-! **Tw: the scales of the window of a weak passage**. `WeakScaleBody` from the
instance, under `2 ≤ M` (a level-floor fact of the plan) and the deadline. -/

open WeakEntryProofs WeakEntryProofs.Assembly

/-- The scales `ε_m` decrease. -/
theorem weakEps_succ_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 1 ≤ Λ) (n : ℕ) :
    ocEpsilon q Λ (n + 1) ≤ ocEpsilon q Λ n := by
  have hbase : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hpos : 0 < (Λ : ℝ) ^ (q ^ (0 + 1) / (q - 1)) :=
      Real.rpow_pos_of_pos (by linarith) _
    have h1 : (1 : ℝ) ≤ (⌈(Λ : ℝ) ^ (q ^ (0 + 1) / (q - 1))⌉₊ : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr hpos
    simp only [ocEpsilon]
    simpa using inv_le_one_of_one_le₀ h1
  · have hn0 : n ≠ 0 := by omega
    have hpos : 0 < (Λ : ℝ) ^ (q ^ n / (q - 1)) := Real.rpow_pos_of_pos (by linarith) _
    have hc : 0 < (⌈(Λ : ℝ) ^ (q ^ n / (q - 1))⌉₊ : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr hpos
    have hmono : (⌈(Λ : ℝ) ^ (q ^ n / (q - 1))⌉₊ : ℝ) ≤
        (⌈(Λ : ℝ) ^ (q ^ (n + 1) / (q - 1))⌉₊ : ℝ) := by
      refine Nat.cast_le.2 (Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hbase ?_))
      exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hq.le (Nat.le_succ n))
        (by linarith)
    simp only [ocEpsilon, hn0, Nat.succ_ne_zero, ite_false]
    exact inv_anti₀ hc hmono

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **Tw**: the scales of the window of the passage `i`, for `2 ≤ M` and under the deadline. -/
theorem weakScaleBody_of (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (h2 : 2 ≤ c.M) : WeakScaleStep c r i := by
  intro hdl
  have hα : c.D.α = B.α := c.alpha
  have hq : c.D.q = B.q := c.q_eq
  have hΛ' : 128 ≤ c.D.Λ := by
    rw [c.base_eq]; exact (plan.base_ge B).trans c.base_ge
  have hΛ : 1 ≤ c.D.Λ := by omega
  have hζ : c.D.ζ = B.ζ := c.profile_eq
  have hqB : IsAdmissibleQ B.α B.s B.q := B.hq
  have hq1 : 1 < c.D.q := by rw [hq]; exact B.hq.1
  have hband : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hα, hq, c.base_eq, hζ, c.terminal]; exact c.band
  have hζp : IsFastProfile c.D.ζ := by rw [hζ]; exact B.hζ
  have hκ : 0 < c.D.κ c.M := by
    have h := weakData_kap_pos c.D hΛ hζp hband c.M
    rwa [weakData_kap_terminal c.D c.M (by rw [c.terminal]), c.terminal] at h
  have hepos : ∀ n, 0 < ocEpsilon c.D.q c.D.Λ n := fun n => ocEpsilon_pos hΛ
  have hsucc : i - 1 + 1 = i := by omega
  refine ⟨by rw [hα]; exact B.hα₀, by rw [hα]; exact B.hα₁, B.hs₀, by rw [hα]; exact B.hs₁,
    by rw [hα, hq]; exact B.hq, hζp, hΛ', by rw [hα, hq, c.base_eq, hζ]; exact c.streams,
    by omega, hκ, hκ, by simp only [wTobs]; linarith, hepos i, le_rfl, ?_, le_rfl⟩
  have := weakEps_succ_le hq1 hΛ (i - 1)
  rwa [hsucc] at this

end AVRegularity.Providers.WeakGen.Window
end
end
end
