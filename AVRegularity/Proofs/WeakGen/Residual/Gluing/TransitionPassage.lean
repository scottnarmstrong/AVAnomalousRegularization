-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.Gluing.TransitionWeights
import AVRegularity.Finite.WeakLift.IdentitySeparation
import AVRegularity.Finite.WeakPositive.PositiveInputJets
import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity
import AVRegularity.CycleComparison.Reconstruction.ReconLiftSlices
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
import AVRegularity.Families.TorusCompatible.WeakStage
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory Filter Topology AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! The comparison representative is prescribed only on its closed time window. Classical
jets continuous on that window give measurable zero-extended jets, with no assumption on
the representative outside the window. Zero extension preserves its classical forcing cost. -/

/-- The instantaneous observed slots are included in the slots meeting the whole comparison
window. No assertion is made outside that window. -/
theorem weak_gluing_observed_subset {α q : ℝ} {Λ i : ℕ} (hΛ : 1 ≤ Λ)
    {a b t : ℝ} (ht : t ∈ Set.Icc a b) :
    ocObsPulses α q Λ i t t ⊆ ocObsPulses α q Λ i a b := by
  classical
  intro k hk
  obtain ⟨hkI, hkodd, s, hsW, hst⟩ := Finset.mem_filter.mp hk
  have hτ : 0 < ocTau α q Λ i := Construction.Stream.ocTau_pos hΛ
  have hlo := Int.floor_mono ((div_le_div_iff_of_pos_right hτ).mpr ht.1)
  have hhi := Int.ceil_mono ((div_le_div_iff_of_pos_right hτ).mpr ht.2)
  obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hkI
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hkodd, s, hsW, ?_⟩
  exact ⟨ht.1.trans hst.1, hst.2.trans ht.2⟩

private theorem weak_gluing_cutoff_derivative_zero {α q : ℝ} {Λ i : ℕ} {k : ℤ}
    {t : ℝ} (hz : ocCutoff α q Λ i k t = 0) : deriv (ocCutoff α q Λ i k) t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards [] with s
  rw [hz]
  exact Real.smoothTransition.nonneg _

/-- Both the cutoff and its derivative have closed support strictly inside the original slot
window. This strict margin is what permits the patch at slot endpoints. -/
theorem weak_gluing_cutoff_support_inside {α q : ℝ} {Λ i : ℕ} (hΛ : 1 ≤ Λ) (k : ℤ) :
    tsupport (ocCutoff α q Λ i k) ⊆ interior (ocPulseWindow α q Λ i k) ∧
    tsupport (deriv (ocCutoff α q Λ i k)) ⊆ interior (ocPulseWindow α q Λ i k) := by
  have hτ : 0 < ocTau α q Λ i := Construction.Stream.ocTau_pos hΛ
  have hs : tsupport (ocCutoff α q Λ i k) ⊆
      Set.Icc (((k : ℝ) - 5 / 4) * ocTau α q Λ i)
        (((k : ℝ) + 5 / 4) * ocTau α q Λ i) := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    have hnear : |t - (k : ℝ) * ocTau α q Λ i| < 5 / 4 * ocTau α q Λ i := by
      have hn : 0 < 5 / 2 - 2 * |t - (k : ℝ) * ocTau α q Λ i| / ocTau α q Λ i := by
        by_contra hn
        exact ht (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hn))
      have hh := (div_lt_iff₀ hτ).mp
        (show 2 * |t - (k : ℝ) * ocTau α q Λ i| / ocTau α q Λ i < 5 / 2 by linarith only [hn])
      linarith only [hh]
    constructor <;> linarith only [(abs_lt.mp hnear).1, (abs_lt.mp hnear).2]
  have hi : Set.Icc (((k : ℝ) - 5 / 4) * ocTau α q Λ i)
      (((k : ℝ) + 5 / 4) * ocTau α q Λ i) ⊆ interior (ocPulseWindow α q Λ i k) := by
    intro t ht
    change t ∈ interior (Set.Icc _ _)
    rw [interior_Icc]
    constructor <;> linarith only [hτ, ht.1, ht.2]
  exact ⟨hs.trans hi, tsupport_deriv_subset.trans (hs.trans hi)⟩

/-- Enlarging the instantaneous observation set adds only zero weighted summands. -/
theorem weak_gluing_observed_derivative_sum {α q : ℝ} {Λ i : ℕ} (hΛ : 1 ≤ Λ)
    {a b t : ℝ} (ht : t ∈ Set.Icc a b) (g : ℤ → ℝ) :
    (∑ k ∈ ocObsPulses α q Λ i t t, deriv (ocCutoff α q Λ i k) t * g k) =
      ∑ k ∈ ocObsPulses α q Λ i a b, deriv (ocCutoff α q Λ i k) t * g k := by
  classical
  apply Finset.sum_subset (weak_gluing_observed_subset hΛ ht)
  intro k hk hnot
  have hodd : Odd k := (Finset.mem_filter.mp hk).2.1
  have hz : ocCutoff α q Λ i k t = 0 := by
    by_contra hne
    exact hnot (Finite.WeakLift.active_cutoff_mem_obs
      (Construction.Stream.ocTau_pos hΛ) hodd hne)
  rw [weak_gluing_cutoff_derivative_zero hz, zero_mul]

/-- The literal time-gluing source is a fixed finite sum on the comparison window. Slots in
the larger observation set but absent at the current time have zero cutoff derivative. -/
theorem weak_gluing_time_eq_fixed_sum {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    (i N H : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (f : WeakField G) (hΛ : 1 ≤ D.Λ) {a b t : ℝ} (ht : t ∈ Set.Icc a b) (x : Vec 2)
    (v : CompIn G.comps) :
    weakResidualGlueTime i N H G Cc f t x v =
      -∑ k ∈ ocObsPulses D.α D.q D.Λ i a b, deriv (ocCutoff D.α D.q D.Λ i k) t *
        (weakSlotLift i N H G Cc k f t x v - f t x v) := by
  exact congrArg Neg.neg (weak_gluing_observed_derivative_sum hΛ ht
    (fun k => weakSlotLift i N H G Cc k f t x v - f t x v))

open Finite.WeakLift Construction.Preservation.FullLift CycleComparison.Reconstruction in
/-- An arbitrary supplied lift has the spatial regularity of the slot lift and physical periodicity
on its own window. The input order is explicit, rather than hidden in a choice of prices. -/
theorem weak_gluing_slot_lift_pulse_regular {N H U : ℕ} {P : WeakPositiveParameters N H U}
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} {slot : OddSlot}
    (W : WeakPositiveSlot P i G π slot (D.eps (i - 1))) (hgeo : WeakPositiveGeometry P i G (D.eps (i - 1)))
    {sX sZ : ℕ} (Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hseq : IsLiftSequence (weakPositiveNativeData i G slot (D.eps (i - 1))) sX sZ
      (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) N H Cc)
    {J : ℕ} (hJslow : J ≤ P.slowOrder) (hJfast : J ≤ P.fastOrder)
    (a : WeakField G) {t : ℝ}
    (ht : (D.cellScaleSq i)⁻¹ * t ∈ Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1))
    (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t)) (haper : AVenhance.IsZ2Periodic (a t)) :
    (∀ v, ContDiff ℝ (J : ℕ∞) (fun x => pulsePhysicalLift (D.cellScaleSq i)
      (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1)) N H Cc
      (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
      (fun s y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y s) a t x v)) ∧
    AVenhance.IsZ2Periodic (pulsePhysicalLift (D.cellScaleSq i)
      (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1)) N H Cc
      (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
      (fun s y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y s) a t) := by
  have hΛ : 1 ≤ D.Λ := by have := hgeo.Λ_ge; omega
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hgeo.fast hgeo.band i
  have hid := (weak_positive_support_identification N H U P D Dm j₀ bw i G π slot (D.eps (i - 1)) W sX sZ Cc hseq).1
  have heq : pulsePhysicalLift (D.cellScaleSq i) (D.eps (i - 1)) (D.eps i)
      (D.eps i / D.eps (i - 1)) N H Cc
      (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
      (fun s y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y s) a t =
    pulsePhysicalLift (D.cellScaleSq i) (D.eps (i - 1)) (D.eps i)
      (D.eps i / D.eps (i - 1)) N H W.coeff
      (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
      (fun s y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y s) a t := by
    funext x
    exact pulsePhysicalLift_coeff_congr _ _ _ _ N H Cc W.coeff _ _ a t
      (fun hh hhh n _hn m α X z v u => hid hh hhh n m α _ ht X z v u) x
  rw [heq]
  constructor
  · have hd := pulsePhysicalLift_contDiff W.setting
      (P.slowOrder + W.cap + 2) (max (P.fastOrder + 1) (P.fastOrder + 2))
      (by omega) W.coeff W.sequence (J := J) (by omega) (by omega) hc.ne'
      (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1))
      (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
      (fun s y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y s) a ht
      ((CycleReference.streamFlow_spatial_smooth (D.hΦ (i - 1)) t (D.slotAnchor i slot.1)).of_le
        (by simp))
      ((CycleReference.streamFlow_spatial_smooth (D.hΦ (i - 1)) (D.slotAnchor i slot.1) t).of_le
        (by simp)) ha
    exact contDiff_pi.mp hd
  · rw [pulsePhysicalLift_freeze_time]
    simp only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    obtain ⟨K, hK⟩ := TorusCompatible.ocEpsilon_inv_natCast D.q D.Λ i
    apply pulsePhysicalLift_static_periodic _ _ _ _ N H _ _ _ (a t) t
      W.setting.ρ_pos.ne' hK
      (fun p Y => native_flow_latticeShift D _ _ _ p Y)
      (fun p Y => native_flow_latticeShift D _ _ _ p Y) haper
    · intro hh hhh n _hn m _hm α p X z v u
      exact weak_positive_slot_coefficient_slow_shift W
        (EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hgeo.fast hgeo.band 1).ne'
        hgeo.level hgeo.torus p hh hhh n m α _ ht X z v u
    · intro hh hhh n _hn m _hm α X v u
      exact (W.sequence.2.2.2.2.2.1 hh hhh n m α v u _ ht).2 X

open Finite.WeakLift in
/-- Spatial regularity and periodicity of the literal first gluing source. Only slots in the
observed finite set are read, so every use of a supplied coefficient is on its own window. -/
theorem weak_gluing_time_spatial_regular {N H U : ℕ} {P : WeakPositiveParameters N H U}
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} (slotLifts : ∀ slot : OddSlot, WeakPositiveSlot P i G π slot (D.eps (i - 1)))
    (hgeo : WeakPositiveGeometry P i G (D.eps (i - 1))) {sX sZ : ℕ}
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hseq : IsWeakReadoutLifts i N H sX sZ G Cc)
    {J : ℕ} (hJslow : J ≤ P.slowOrder) (hJfast : J ≤ P.fastOrder)
    (a : WeakField G) (t : ℝ)
    (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t)) (haper : AVenhance.IsZ2Periodic (a t)) :
    (∀ v, ContDiff ℝ (J : ℕ∞) (fun x => weakResidualGlueTime i N H G Cc a t x v)) ∧
      AVenhance.IsZ2Periodic (weakResidualGlueTime i N H G Cc a t) := by
  classical
  have hΛ : 1 ≤ D.Λ := by have := hgeo.Λ_ge; omega
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hgeo.fast hgeo.band i
  have hpulse : ∀ k ∈ ocObsPulses D.α D.q D.Λ i t t,
      (∀ v, ContDiff ℝ (J : ℕ∞) (fun x => weakSlotLift i N H G Cc k a t x v)) ∧
      AVenhance.IsZ2Periodic (weakSlotLift i N H G Cc k a t) := by
    intro k hk
    have hkodd : Odd k := ((Finset.mem_filter.mp hk).2).1
    obtain ⟨s, hsW, hst⟩ := ((Finset.mem_filter.mp hk).2).2
    have hs : s = t := le_antisymm hst.2 hst.1
    have htW : t ∈ ocPulseWindow D.α D.q D.Λ i k := by simpa only [hs] using hsW
    have ht : (D.cellScaleSq i)⁻¹ * t ∈
        Set.Icc (weakSlotLeft D i k) (weakSlotRight D i k) := by
      change D.slotStart i k / D.cellScaleSq i ≤ _ ∧
        _ ≤ (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / D.cellScaleSq i
      rw [mul_comm, ← div_eq_mul_inv]
      exact ⟨(div_le_div_iff_of_pos_right hc).mpr htW.1,
        (div_le_div_iff_of_pos_right hc).mpr htW.2⟩
    exact weak_gluing_slot_lift_pulse_regular (slotLifts ⟨k, hkodd⟩) hgeo (Cc k)
      (hseq k hkodd) hJslow hJfast a ht ha haper
  constructor
  · intro v
    simp only [weakResidualGlueTime]
    apply ContDiff.neg
    apply ContDiff.sum
    intro k hk
    exact contDiff_const.mul (((hpulse k hk).1 v).sub
      ((contDiff_pi.mp ha v).of_le (by exact_mod_cast Nat.le_add_left J N)))
  · intro p x
    funext v
    simp only [weakResidualGlueTime]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [congrFun ((hpulse k hk).2 p x) v, congrFun (haper p x) v]

end AVRegularity.Providers.WeakGen.Residual
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Periodicity of the glued weak lift** (uniqueness on the slot window).

The lift relation `IsWeakReadoutLifts` gives periodicity of the coefficients in the fast variable
only. A lattice shift of `x` shifts the slow variable by `ε_{i-1}^{-1} n`, so the glued lift is
periodic only if the coefficients are invariant under the slow lattice. This is not a consequence
of the lift relation for abstract coefficients on an abstract stage. It holds on a stage with slot
lifts (`WeakPositiveSlot`, `WeakPositiveGeometry`):
- on the slot window, any coefficients satisfying the lift relation are those of the slot lift
  (`weak_positive_support_identification`);
- the coefficients of the slot lift are invariant under the slow lattice
  (`weak_positive_slot_coefficient_slow_shift`);
- the glued lift at the time `t` reads the slots of `ocObsPulses i t t` only, and `t` is in the
  window of each of them.
No hypothesis on the coefficients beyond `IsWeakReadoutLifts`, and no smoothness of the input.

* `weak_slot_lift_pulse_periodic`: one slot (the periodicity half of
  `weak_gluing_slot_lift_pulse_regular`, without the smoothness of the input).
* `weakGluedLift_periodic_of_slotLifts`: the glued lift.

The degenerate cases are included: no observed pulse at the time `t` gives the zero field;
`g = 0` gives zero. -/

open Finite.WeakLift Construction.Preservation.FullLift CycleComparison.Reconstruction in
/-- **Periodicity of one slot lift** of a periodic field, for any coefficients satisfying the lift
relation on the slot window. No smoothness of the input. -/
theorem weak_slot_lift_pulse_periodic {N H U : ℕ} {P : WeakPositiveParameters N H U}
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} {slot : OddSlot}
    (W : WeakPositiveSlot P i G π slot (D.eps (i - 1))) (hgeo : WeakPositiveGeometry P i G (D.eps (i - 1)))
    {sX sZ : ℕ} (Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hseq : IsLiftSequence (weakPositiveNativeData i G slot (D.eps (i - 1))) sX sZ
      (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) N H Cc)
    (a : WeakField G) {t : ℝ}
    (ht : (D.cellScaleSq i)⁻¹ * t ∈ Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1))
    (haper : AVenhance.IsZ2Periodic (a t)) :
    AVenhance.IsZ2Periodic (pulsePhysicalLift (D.cellScaleSq i)
      (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1)) N H Cc
      (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
      (fun s y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y s) a t) := by
  have hΛ : 1 ≤ D.Λ := by have := hgeo.Λ_ge; omega
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hgeo.fast hgeo.band i
  have hid := (weak_positive_support_identification N H U P D Dm j₀ bw i G π slot (D.eps (i - 1)) W sX sZ Cc hseq).1
  have heq : pulsePhysicalLift (D.cellScaleSq i) (D.eps (i - 1)) (D.eps i)
      (D.eps i / D.eps (i - 1)) N H Cc
      (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
      (fun s y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y s) a t =
    pulsePhysicalLift (D.cellScaleSq i) (D.eps (i - 1)) (D.eps i)
      (D.eps i / D.eps (i - 1)) N H W.coeff
      (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
      (fun s y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y s) a t := by
    funext x
    exact pulsePhysicalLift_coeff_congr _ _ _ _ N H Cc W.coeff _ _ a t
      (fun hh hhh n _hn m α X z v u => hid hh hhh n m α _ ht X z v u) x
  rw [heq, pulsePhysicalLift_freeze_time]
  simp only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  obtain ⟨K, hK⟩ := TorusCompatible.ocEpsilon_inv_natCast D.q D.Λ i
  apply pulsePhysicalLift_static_periodic _ _ _ _ N H _ _ _ (a t) t
    W.setting.ρ_pos.ne' hK
    (fun p Y => native_flow_latticeShift D _ _ _ p Y)
    (fun p Y => native_flow_latticeShift D _ _ _ p Y) haper
  · intro hh hhh n _hn m _hm α p X z v u
    exact weak_positive_slot_coefficient_slow_shift W
      (EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hgeo.fast hgeo.band 1).ne'
      hgeo.level hgeo.torus p hh hhh n m α _ ht X z v u
  · intro hh hhh n _hn m _hm α X v u
    exact (W.sequence.2.2.2.2.2.1 hh hhh n m α v u _ ht).2 X

open Finite.WeakLift in
/-- **The glued weak lift of a periodic field is periodic**, for any lift coefficients with
`IsWeakReadoutLifts`, on a stage with slot lifts. -/
theorem weakGluedLift_periodic_of_slotLifts {N H U : ℕ} {P : WeakPositiveParameters N H U}
    {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ}
    (slotLifts : ∀ slot : OddSlot, WeakPositiveSlot P i G π slot (D.eps (i - 1)))
    (hgeo : WeakPositiveGeometry P i G (D.eps (i - 1))) {sX sZ : ℕ}
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hseq : IsWeakReadoutLifts i N H sX sZ G Cc) (t : ℝ)
    (g : CompIn G.comps → Vec 2 → ℝ) (hg : ∀ v, AVenhance.IsZ2Periodic (g v))
    (v : CompIn G.comps) :
    AVenhance.IsZ2Periodic (weakGluedLift i N H G Cc t g v) := by
  classical
  have hΛ : 1 ≤ D.Λ := by have := hgeo.Λ_ge; omega
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hgeo.fast hgeo.band i
  have haper : AVenhance.IsZ2Periodic
      ((fun (_ : ℝ) (y : Vec 2) (w : CompIn G.comps) => g w y) t) := by
    intro p x
    funext w
    exact hg w p x
  intro p x
  simp only [weakGluedLift, gluedLift, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkodd : Odd k := ((Finset.mem_filter.mp hk).2).1
  obtain ⟨s, hsW, hst⟩ := ((Finset.mem_filter.mp hk).2).2
  have hs : s = t := le_antisymm hst.2 hst.1
  have htW : t ∈ ocPulseWindow D.α D.q D.Λ i k := by simpa only [hs] using hsW
  have ht : (D.cellScaleSq i)⁻¹ * t ∈
      Set.Icc (weakSlotLeft D i k) (weakSlotRight D i k) := by
    change D.slotStart i k / D.cellScaleSq i ≤ _ ∧
      _ ≤ (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / D.cellScaleSq i
    rw [mul_comm, ← div_eq_mul_inv]
    exact ⟨(div_le_div_iff_of_pos_right hc).mpr htW.1,
      (div_le_div_iff_of_pos_right hc).mpr htW.2⟩
  have hper := weak_slot_lift_pulse_periodic (slotLifts ⟨k, hkodd⟩) hgeo (Cc k) (hseq k hkodd)
    (fun (_ : ℝ) (y : Vec 2) (w : CompIn G.comps) => g w y) ht haper
  rw [congrFun (hper p x) v]

end AVRegularity.Providers.WeakGen.Residual
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! Finite coarse reserves suffice for measurability of every transition slice.
The proof reuses the clamped-time argument for lift coefficients, restricting the
input orders to the degrees actually used in the positive label sum. -/

section
open CycleComparison.Reconstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The positive label field uses only the input reserve `N+J` to produce `J` derivatives.
The coefficient box orders are lowered to `J` before applying the existing box-action lemma. -/
theorem weak_gluing_labelSrc_contDiff {D H N sX sZ J : ℕ} {Q : LiftOperatorData ι h D}
    {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ} (hhh : hh ≤ H)
    (hJX : J ≤ sX) (hJZ : J ≤ sZ) (ℓ ρ e εc : ℝ)
    (a : ℝ → Vec 2 → ∀ i, h i)
    (ha : ∀ t, ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t)) {s : ℝ}
    (hs : (ℓ ^ 2)⁻¹ * s ∈ Set.Icc t₀ t₁) :
    ContDiff ℝ (J : ℕ∞) (labelSrc N hh ℓ ρ e εc Cc a s) := by
  refine contDiff_pi.mpr fun v => ?_
  have he : (fun y => labelSrc N hh ℓ ρ e εc Cc a s y v) = fun y =>
      ∑ n ∈ Finset.Icc 1 N, εc ^ n • liftApply n (Cc hh n)
        (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) ((ℓ ^ 2)⁻¹ * s) (ρ⁻¹ • y) (e⁻¹ • y) v :=
    funext fun y => labelSrc_apply N hh ℓ ρ e εc Cc a s y v
  rw [he]
  refine ContDiff.sum fun n hn => ContDiff.const_smul (εc ^ n) ?_
  have hF : ContDiff ℝ ((J + n : ℕ) : ℕ∞)
      (fun X' : Vec 2 => a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s)) (ρ • X')) :=
    ((ha _).comp (contDiff_const_smul ρ)).of_le
      (natCast_le_natCast_order (by have := (Finset.mem_Icc.mp hn).2; omega))
  have hbox := QuietDecay.Partition.isBoxSmooth_liftApply n J J (Cc hh n)
    (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) ((ℓ ^ 2)⁻¹ * s)
    (fun m α v' u => ((hseq.2.2.2.2.2.1 hh hhh n m α v' u _ hs).1).mono hJX hJZ) hF v
  exact CoarseFluxDiff.contDiff_sample hbox le_rfl le_rfl ρ e

/-- The clamped-time measurability proof for a finite-reserve coarse input. Only degrees
through `N` are read, and only `J` spatial derivatives are tested. -/
theorem weak_gluing_labelSrc_slice_aemeasurable {D H N K kl L qs qf : ℕ}
    {Q : LiftOperatorData ι h D} {π : ι → ℝ} {e₀ ν B ρ₀ E ℓ₀ dstar εc₀ lam : ℝ}
    {par : Fin 2} {V : ℝ → ℝ → ℝ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bm : ι → ι → ℝ}
    {Θ : ℝ} {ℓ M₁ M₂ : ℝ}
    (P : IsLiftSetting Q π (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) e₀ ν B ρ₀ E ℓ₀ dstar εc₀ lam par V H N
      K kl L qs qf CG Cw Cj bm Θ)
    {sX sZ : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) N H Cc) (hsZ : 1 ≤ sZ)
    {hh : ℕ} (hhh : hh ≤ H) {J : ℕ} (hJX : J ≤ sX) (hJZ : J ≤ sZ) (hℓ : ℓ ≠ 0)
    (ρ e εc : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) (hA : ∀ t, ContDiff ℝ ((N + J : ℕ) : ℕ∞) (A t))
    (hAm : ∀ X, Measurable fun τ =>
      A (ℓ ^ 2 * Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window τ) (ρ • X))
    (π' : ι → ℝ) (rs : ℝ) {i : ℕ} (hiJ : i ≤ J) (β : DerivativeWord2 i) :
    AEMeasurable (fun t => scalInt π' (fun y => rs ^ i • orderedDerivative β
      (labelSrc N hh ℓ ρ e εc Cc A t) y)) (volume.restrict (Set.Icc M₁ M₂)) := by
  have hc : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  have hc0 : 0 < ℓ ^ 2 := lt_of_le_of_ne (sq_nonneg ℓ) hc.symm
  -- the clamped physical time
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ → ℝ,
      θ = fun t => ℓ ^ 2 * (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window ((ℓ ^ 2)⁻¹ * t) : ℝ) :=
    ⟨_, rfl⟩
  have hθc : ∀ t, (ℓ ^ 2)⁻¹ * θ t =
      Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window ((ℓ ^ 2)⁻¹ * t) := fun t => by
    subst hθ
    exact inv_mul_cancel_left₀ hc _
  have hθS : ∀ t ∈ Set.Icc M₁ M₂, θ t = t := fun t ht => by
    have hmem : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) := by
      have e' : (ℓ ^ 2)⁻¹ * t = t / ℓ ^ 2 := by rw [div_eq_inv_mul]
      rw [e']
      exact ⟨div_le_div_of_nonneg_right ht.1 hc0.le, div_le_div_of_nonneg_right ht.2 hc0.le⟩
    have h1 := hθc t
    rw [projIcc_val_of_mem P.window hmem] at h1
    exact mul_left_cancel₀ (inv_ne_zero hc) h1
  -- the lift actions of the chart-frame field are measurable in clamped cell time
  have hg : ∀ τ, ContDiff ℝ (N : ℕ∞) (fun X' => A (ℓ ^ 2 * τ) (ρ • X')) := fun τ =>
    ((hA _).of_le (natCast_le_natCast_order (Nat.le_add_right N J))).comp (contDiff_const_smul ρ)
  have hL : ∀ n', n' ≤ N → ∀ (X z : Vec 2), Measurable fun τ : ℝ => liftApply n' (Cc hh n')
      (fun s' X' => A (ℓ ^ 2 * s') (ρ • X'))
      (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window τ) X z := by
    intro n' hn' X z
    have hq : Measurable fun τ : ℝ => (τ, X, z) := measurable_id.prodMk measurable_const
    refine Measurable.of_eval fun v => ?_
    have hJ : Measurable fun q : ℝ × Vec 2 × Vec 2 => liftApply n' (Cc hh n')
        (fun s' X' => A (ℓ ^ 2 * s') (ρ • X'))
        (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window q.1) q.2.1 q.2.2 v :=
      setting_liftApply_joint_measurable P sX sZ hsZ Cc hseq hh hhh n'
        (fun s' X' => A (ℓ ^ 2 * s') (ρ • X'))
        (fun τ _ => (hg τ).of_le (natCast_le_natCast_order hn')) hAm v
    have h1 := hJ.comp hq
    simp only [Function.comp_def] at h1
    exact h1
  -- the label field at the clamped time: measurable in time, `C^J` in space
  have hm : ∀ y, Measurable fun t => labelSrc N hh ℓ ρ e εc Cc A (θ t) y := by
    intro y
    have he : (fun t => labelSrc N hh ℓ ρ e εc Cc A (θ t) y) = fun t =>
        ∑ n' ∈ Finset.Icc 1 N, εc ^ n' • liftApply n' (Cc hh n')
          (fun s' X' => A (ℓ ^ 2 * s') (ρ • X'))
          (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window ((ℓ ^ 2)⁻¹ * t)) (ρ⁻¹ • y)
          (e⁻¹ • y) := by
      funext t
      simp only [labelSrc, diagSample, hθc t]
    rw [he]
    exact Finset.measurable_sum _ fun n' hn' =>
      ((hL n' (Finset.mem_Icc.mp hn').2 (ρ⁻¹ • y) (e⁻¹ • y)).comp (measurable_const_mul (ℓ ^ 2)⁻¹)).fun_const_smul _
  have hf : ∀ t, ContDiff ℝ (J : ℕ∞) (labelSrc N hh ℓ ρ e εc Cc A (θ t)) := fun t =>
    weak_gluing_labelSrc_contDiff hseq hhh hJX hJZ ℓ ρ e εc A hA (by
      rw [hθc t]
      exact (Set.projIcc (M₁ / ℓ ^ 2) (M₂ / ℓ ^ 2) P.window _).2)
  -- the slice norm at the clamped time is measurable
  have hM : Measurable fun t => scalInt π' (fun y => rs ^ i • orderedDerivative β
      (labelSrc N hh ℓ ρ e εc Cc A (θ t)) y) :=
    AVRegularity.ChartTransport.measurable_scalInt (r := J)
      (q := fun t => labelSrc N hh ℓ ρ e εc Cc A (θ t)) π' rs
      (fun j' hj' β' v => ((measurable_pi_apply v).comp
        (measurable_orderedDerivative_joint (fun t => labelSrc N hh ℓ ρ e εc Cc A (θ t)) J hm
          hf hj' β')).enorm) hiJ β
  -- the clamp is invisible on the window
  refine hM.aemeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
  simp only [hθS t ht]

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Finite-reserve periodicity of a positive label field. Only the coefficient translations
and the derivatives actually present in degrees through `N` are used. -/
theorem weak_gluing_labelSrc_periodic {D H N sX sZ : ℕ} {Q : LiftOperatorData ι h D}
    {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ} (hhh : hh ≤ H)
    (ℓ ρ e εc : ℝ) (hρ : ρ ≠ 0) (M : ℕ) (hM : e⁻¹ = M)
    (a : ℝ → Vec 2 → ∀ i, h i) {s : ℝ}
    (ha : ContDiff ℝ (N : ℕ∞) (a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s))))
    (hap : IsZ2Periodic (a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s))))
    (hs : (ℓ ^ 2)⁻¹ * s ∈ Set.Icc t₀ t₁)
    (hslow : ∀ (p : Fin 2 → ℤ) n m (α : DerivativeWord2 m) X z v u,
      Cc hh n m α ((ℓ ^ 2)⁻¹ * s) (X + ρ⁻¹ • latticeShift p) z v u =
        Cc hh n m α ((ℓ ^ 2)⁻¹ * s) X z v u) :
    IsZ2Periodic (labelSrc N hh ℓ ρ e εc Cc a s) := by
  intro p y
  funext v
  rw [labelSrc_apply, labelSrc_apply]
  refine Finset.sum_congr rfl fun n hn => ?_
  congr 1
  simp only [liftApply]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  have hX : ρ⁻¹ • (y + latticeShift p) = ρ⁻¹ • y + ρ⁻¹ • latticeShift p := smul_add _ _ _
  have hz : e⁻¹ • (y + latticeShift p) = e⁻¹ • y + latticeShift (fun j => (M : ℤ) * p j) := by
    rw [smul_add, hM, natCast_smul_latticeShift]
  have hfast := (hseq.2.2.2.2.2.1 hh hhh n m α v u ((ℓ ^ 2)⁻¹ * s) hs).2 (ρ⁻¹ • y)
    (fun j => (M : ℤ) * p j) (e⁻¹ • y)
  have hg : ContDiff ℝ (m : ℕ∞)
      (fun X : Vec 2 => a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s)) (ρ • X)) :=
    (ha.comp (contDiff_const_smul ρ)).of_le (natCast_le_natCast_order
      ((Finset.mem_range.mp hm |> Nat.lt_succ_iff.mp).trans (Finset.mem_Icc.mp hn).2))
  have hT : ∀ Y : Vec 2, a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s)) (ρ • (Y + ρ⁻¹ • latticeShift p)) =
      a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s)) (ρ • Y) := by
    intro Y
    rw [smul_add, smul_smul, mul_inv_cancel₀ hρ, one_smul, hap p (ρ • Y)]
  have hjet := orderedDerivative_periodic hg (ρ⁻¹ • latticeShift p) hT α (ρ⁻¹ • y)
  simp only at hfast
  rw [hX, hz, hslow, hfast, hjet]

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- A label-slice estimate on its original window gives global measurability after multiplying
by a measurable supported weight. No regularity or measurability outside that window is used. -/
theorem weak_gluing_weighted_label_slice_aemeasurable (π : ι → ℝ) (rs : ℝ)
    {J : ℕ} (w : DerivativeWord2 J) (L : ℝ → Vec 2 → ∀ v, h v) (I : Set ℝ)
    (hI : MeasurableSet I) (ψ : ℝ → ℝ) (hψ : Measurable ψ)
    (hsupp : Function.support ψ ⊆ I)
    (hL : AEMeasurable (fun t => scalInt π
      (fun y => rs ^ J • orderedDerivative w (L t) y)) (volume.restrict I)) :
    AEMeasurable (fun t => scalInt π
      (fun y => rs ^ J • orderedDerivative w (fun y' => ψ t • L t y') y) ^ (1 / 2 : ℝ)) volume := by
  have hm : AEMeasurable (fun t => (ENNReal.ofReal (ψ t ^ 2) *
      scalInt π (fun y => rs ^ J • orderedDerivative w (L t) y)) ^ (1 / 2 : ℝ))
      (volume.restrict I) :=
    (((hψ.pow_const 2).ennreal_ofReal.aemeasurable.restrict).mul hL).pow_const _
  have hi := (aemeasurable_indicator_iff hI).mpr hm
  refine hi.congr (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [scalInt_word_smul]
  by_cases ht : t ∈ I
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    have hz : ψ t = 0 := by
      by_contra hne
      exact ht (hsupp (Function.mem_support.mpr hne))
    simp only [hz, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, zero_mul,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
end

/-! The actual rising and falling cutoff pieces satisfy one original-window transition
bound. Neither the lift start nor the entrance trace is clipped to the comparison window.
All constants precede the slot, component set, datum and ambient degree cap. -/

section
open Finite.WeakLift CycleComparison.Reconstruction

/-- One cutoff transition at any selected weak slot. The energy is taken only over the
comparison window, including when its left endpoint is inside the falling transition.
Both directions use the delay `τ/48` from their original quiet entrance. -/
theorem weak_gluing_cutoff_transition_bound {N H J Lr Acl r : ℕ}
    (P : WeakPositiveParameters N H (Lr + 3)) (hP : WeakGluingFactoryOrders J Lr P)
    (hL : weakGluingReadoutOrder J N H Acl r ≤ Lr) (hAcl : 1 ≤ Acl) (Dχ : ℝ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
    ∀ {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (i : ℕ)
      (G : GenStage D ScalarH Dm bw j₀) (π : CompIn G.comps → ℝ) (slot : OddSlot)
      (W : WeakPositiveSlot P i G π slot) (rs : ℝ),
      1 ≤ D.Λ → 0 < rs → rs ≤ D.eps i → D.eps i ≤ D.eps (i - 1) →
      D.kap (i - 1) = D.kap i → (∃ M : ℕ, (D.eps i)⁻¹ = (M : ℝ)) →
    ∀ χ χi : ℝ → Vec 2 → Vec 2, (∀ t, IsChart (χ t) (χi t)) →
      (∀ t, ContDiff ℝ (⊤ : ℕ∞) (χ t)) → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (χi t)) →
      (∀ t ∈ ocPulseWindow D.α D.q D.Λ i slot.1,
        JetBound (χ t) (4 * (N + P.capMax) + 2 * Acl + 16 + r + 2) Dχ (D.eps (i - 1)) ∧
        JetBound (χi t) (4 * (N + P.capMax) + 2 * Acl + 16 + r + 2) Dχ (D.eps (i - 1))) →
      (∀ σ : Bool, IsQuietOn W.Q.edge (fun t z => Real.sqrt W.Q.η • W.Q.v t z)
        (Set.Icc (weakGluingGapLeft (ocTau D.α D.q D.Λ i) slot.1 σ /
          (D.eps i / Real.sqrt (D.kap i)) ^ 2)
          (weakGluingGapRight (ocTau D.α D.q D.Λ i) slot.1 σ /
            (D.eps i / Real.sqrt (D.kap i)) ^ 2))) →
    ∀ a b : ℝ, ∀ σ : Bool, ∀ hh, hh ≤ H → ∀ f : ℝ → Vec 2 → CompIn G.comps → ℝ,
      (∀ t ∈ Set.Icc a b, ContDiff ℝ
        ((4 * (N + P.capMax) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞) (f t)) →
      (∀ t ∈ Set.Icc a b, IsZ2Periodic (f t)) → ∀ j, j ≤ r → ∀ w : DerivativeWord2 j,
      ∫⁻ t, scalInt π (fun y => rs ^ j • orderedDerivative w
          (transitionSourceField N hh (D.eps i / Real.sqrt (D.kap i))
            (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1))
            (trWeight (ocCutoff D.α D.q D.Λ i) (ocTau D.α D.q D.Λ i) a b slot.1 σ)
            W.coeff (fun t' y' => f t' (χ t' y')) t) y) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * (D.eps i / Real.sqrt (D.kap i)) *
          Real.sqrt (1 / ocTau D.α D.q D.Λ i) *
          Real.exp (-(c * ocTau D.α D.q D.Λ i / (D.eps i / Real.sqrt (D.kap i)) ^ 2))) *
        classicalStrongEnergy (D.eps (i - 1)) (D.kap (i - 1)) π (Set.Icc a b)
          (4 * (N + P.capMax) + 2 * Acl + 16 + r) f := by
  obtain ⟨C₀, c₀, CI, hC₀, hc₀, hCI, hgate⟩ :=
    weak_gluing_slot_lift_transition_on_window P hP hL hAcl Dχ
  obtain ⟨Kcut, hKcut, hcut⟩ := CycleReference.cutoff_derivative_uniform_bound
  let JT : ℝ := ∑ hh ∈ Finset.range (H + 1),
    ∑ b ∈ Finset.range (hh + 1), P.S ^ (hh - b) * (CI * P.S ^ b)
  have hJT : 0 ≤ JT := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (pow_nonneg P.S_nonneg _) (mul_nonneg hCI (pow_nonneg P.S_nonneg _))
  refine ⟨C₀ * JT * Kcut, c₀ / 48,
    mul_nonneg (mul_nonneg hC₀ hJT) hKcut.le, div_pos hc₀ (by norm_num), ?_⟩
  intro D Dm bw j₀ i G π slot W rs hΛ hrs hrse heE hplateau he χ χi hchart hχ hχi hJ hquiet
    a b σ hh hhh f hf hfp j hj w
  let τ := ocTau D.α D.q D.Λ i
  let ℓ := D.eps i / Real.sqrt (D.kap i)
  let g := weakGluingGapLeft τ slot.1 σ
  let z := weakGluingGapRight τ slot.1 σ
  have hτ : 0 < τ := Construction.Stream.ocTau_pos hΛ
  obtain ⟨hd, hdτ, hδd, hleft, hright⟩ := weak_gluing_original_gap_geometry hτ slot.1 σ
  have hℓ : 0 < ℓ := div_pos W.setting.e_pos (Real.sqrt_pos.mpr W.setting.ν_pos)
  have hcs : D.cellScaleSq i = ℓ ^ 2 := by
    dsimp only [OCData.cellScaleSq, ℓ]
    rw [div_pow, Real.sq_sqrt W.setting.ν_pos.le]
  have hcspos : 0 < D.cellScaleSq i := by rw [hcs]; exact sq_pos_of_pos hℓ
  have hwindowLeft : ℓ ^ 2 * weakSlotLeft D i slot.1 =
      (((slot.1 : ℝ) - 61 / 48) * τ) := by
    rw [← hcs]
    dsimp only [weakSlotLeft]
    rw [mul_div_cancel₀ _ hcspos.ne']
    rfl
  have hwindowRight : ℓ ^ 2 * weakSlotRight D i slot.1 =
      (((slot.1 : ℝ) + 61 / 48) * τ) := by
    rw [← hcs]
    dsimp only [weakSlotRight]
    rw [mul_div_cancel₀ _ hcspos.ne']
  have hgdz : g + (z - g) = z := by ring
  have hsupp := weak_gluing_transition_weight_support hΛ i a b slot.1 σ
  have hb := hgate i G π slot W rs hrs hrse heE hplateau he χ χi hchart hχ hχi
    g (z - g) hd (by rw [hwindowLeft]; exact hleft)
    (by rw [hgdz, hwindowRight]; exact hright)
    (by
      rw [hgdz]
      intro t ht
      apply hJ t
      exact ⟨hleft.trans ht.1, ht.2.trans hright⟩)
    (by rw [hgdz]; exact hquiet σ)
    (trWeight (ocCutoff D.α D.q D.Λ i) τ a b slot.1 σ) (Kcut / τ) (τ / 48)
    (div_nonneg hτ.le (by norm_num)) hδd
    (fun t => (abs_trWeight_le _ _ _ _ _ _ t).trans (hcut _ _ _ _ hΛ slot.1 t))
    (by rw [hgdz]; exact hsupp.1) (Set.Icc a b) measurableSet_Icc hsupp.2 hh hhh f hf hfp j hj w
  have hJhh : (∑ b ∈ Finset.range (hh + 1), P.S ^ (hh - b) * (CI * P.S ^ b)) ≤ JT :=
    Finset.single_le_sum
      (f := fun hh => ∑ b ∈ Finset.range (hh + 1), P.S ^ (hh - b) * (CI * P.S ^ b))
      (fun hh _ => Finset.sum_nonneg fun b _ =>
        mul_nonneg (pow_nonneg P.S_nonneg _) (mul_nonneg hCI (pow_nonneg P.S_nonneg _)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hhh))
  have hfactor := decay_factor_le
    (J := ∑ b ∈ Finset.range (hh + 1), P.S ^ (hh - b) * (CI * P.S ^ b))
    (d := z - g) hC₀
    (Finset.sum_nonneg fun b _ => mul_nonneg (pow_nonneg P.S_nonneg _)
      (mul_nonneg hCI (pow_nonneg P.S_nonneg _))) hKcut.le hℓ.le hτ hdτ
    (c := c₀)
  refine hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hfactor.trans ?_)) le_rfl)
  have hnonneg : 0 ≤ Kcut * ℓ * Real.sqrt (1 / τ) *
      Real.exp (-(c₀ / 48 * τ / ℓ ^ 2)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hKcut.le hℓ.le) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  calc C₀ * (∑ b ∈ Finset.range (hh + 1), P.S ^ (hh - b) * (CI * P.S ^ b)) *
        Kcut * ℓ * Real.sqrt (1 / τ) * Real.exp (-(c₀ / 48 * τ / ℓ ^ 2))
      = (C₀ * ∑ b ∈ Finset.range (hh + 1), P.S ^ (hh - b) * (CI * P.S ^ b)) *
          (Kcut * ℓ * Real.sqrt (1 / τ) * Real.exp (-(c₀ / 48 * τ / ℓ ^ 2))) := by ring
    _ ≤ (C₀ * JT) * (Kcut * ℓ * Real.sqrt (1 / τ) * Real.exp (-(c₀ / 48 * τ / ℓ ^ 2))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJhh hC₀) hnonneg
    _ = _ := by ring
end

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! The literal time-gluing source as a finite sum of original-window positive labels.
The comparison endpoints only clip the time weights; they never restart a lift. -/

open Finite.WeakLift CycleComparison.Reconstruction Construction.Preservation.FullLift

/-- The native physical flow and inverse label are exact volume-preserving torus charts. -/
theorem weak_gluing_native_isChart (D : OCData) (i : ℕ) (t s : ℝ) :
    IsChart (fun x => D.flowOf i t x s) (fun x => D.flowOf i s x t) where
  contΦ := (CycleReference.streamFlow_spatial_smooth (D.hΦ i) t s).of_le (by simp)
  contΨ := (CycleReference.streamFlow_spatial_smooth (D.hΦ i) s t).of_le (by simp)
  left := weak_chart_inverse D i s t
  right := weak_chart_inverse D i t s
  equiv := fun p x => native_flow_latticeShift D i t s p x
  det := CycleReference.streamFlow_jacMatrix_det_one (D.hΦ i) t s

/-- Identify a supplied native lift with the selected slot lift, then remove its identity part.
Every coefficient is read at the original cell time on the original slot window. -/
theorem weak_gluing_slot_lift_positive_split {N H U : ℕ}
    {P : WeakPositiveParameters N H U} {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ}
    {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ} {slot : OddSlot}
    (W : WeakPositiveSlot P i G π slot) {sX sZ : ℕ}
    (Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hseq : IsLiftSequence (weakPositiveNativeData i G slot (D.eps (i - 1))) sX sZ
      (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) N H Cc)
    (a : WeakField G) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i slot.1) (x : Vec 2) :
    weakSlotLift i N H G (fun _ => Cc) slot.1 a t x - a t x =
      ∑ hh ∈ Finset.range (H + 1),
        labelSrc N hh (D.eps i / Real.sqrt (D.kap i)) (D.eps (i - 1)) (D.eps i)
          (D.eps i / D.eps (i - 1)) W.coeff
          (fun s y => a s (D.flowOf (i - 1) s y (D.slotAnchor i slot.1))) t
          (D.flowOf (i - 1) (D.slotAnchor i slot.1) x t) := by
  have hℓ : 0 < D.eps i / Real.sqrt (D.kap i) :=
    div_pos W.setting.e_pos (Real.sqrt_pos.mpr W.setting.ν_pos)
  have hcs : D.cellScaleSq i = (D.eps i / Real.sqrt (D.kap i)) ^ 2 := by
    dsimp only [OCData.cellScaleSq]
    rw [div_pow, Real.sq_sqrt W.setting.ν_pos.le]
  have hc : 0 < D.cellScaleSq i := hcs.symm ▸ sq_pos_of_pos hℓ
  have htcell : (D.cellScaleSq i)⁻¹ * t ∈
      Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) := by
    rw [inv_mul_eq_div]
    exact ⟨(div_le_div_iff_of_pos_right hc).mpr ht.1,
      (div_le_div_iff_of_pos_right hc).mpr ht.2⟩
  have hid := (weak_positive_support_identification N H U P D Dm j₀ bw i G π slot
    (D.eps (i - 1)) W sX sZ Cc hseq).1
  have heq := pulsePhysicalLift_coeff_congr (D.cellScaleSq i) (D.eps (i - 1)) (D.eps i)
    (D.eps i / D.eps (i - 1)) N H Cc W.coeff
    (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
    (fun s y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y s) a t
    (fun hh hhh n _hn m α X z v u => hid hh hhh n m α _ htcell X z v u) x
  change pulsePhysicalLift _ _ _ _ N H Cc _ _ a t x - a t x = _
  rw [heq, hcs]
  rw [pulsePhysicalLift_split W.sequence hℓ.ne' W.setting.ρ_pos.ne' _ _ _ _
    (fun s y => weak_chart_inverse D (i - 1) s (D.slotAnchor i slot.1) y) a
    (by rwa [← hcs]) x]
  exact add_sub_cancel_left _ _

/-- Closed-window decomposition of the actual time-gluing source. The finite observation
set is fixed by the comparison window; inactive weights need no lift identification. -/
theorem weak_gluing_time_transition_decomposition {N H U : ℕ}
    {P : WeakPositiveParameters N H U} {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ}
    {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ}
    (slotLifts : ∀ slot : OddSlot, WeakPositiveSlot P i G π slot) {sX sZ : ℕ}
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hseq : IsWeakReadoutLifts i N H sX sZ G Cc)
    (hΛ : 1 ≤ D.Λ) (a b : ℝ) (f : WeakField G) {t : ℝ} (ht : t ∈ Set.Icc a b) (x : Vec 2) :
    weakResidualGlueTime i N H G Cc f t x =
      -∑ p ∈ ocObsPulses D.α D.q D.Λ i a b ×ˢ (Finset.univ : Finset Bool),
        if hp : Odd p.1 then
        trWeight (ocCutoff D.α D.q D.Λ i) (ocTau D.α D.q D.Λ i) a b p.1 p.2 t •
          ∑ hh ∈ Finset.range (H + 1),
            labelSrc N hh (D.eps i / Real.sqrt (D.kap i)) (D.eps (i - 1)) (D.eps i)
              (D.eps i / D.eps (i - 1))
              (slotLifts ⟨p.1, hp⟩).coeff
              (fun s y => f s (D.flowOf (i - 1) s y (D.slotAnchor i p.1))) t
              (D.flowOf (i - 1) (D.slotAnchor i p.1) x t) else 0 := by
  classical
  funext v
  rw [weak_gluing_time_eq_fixed_sum i N H G Cc f hΛ ht x v]
  simp only [Finset.sum_apply, Pi.neg_apply]
  congr 1
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkodd : Odd k := (Finset.mem_filter.mp hk).2.1
  simp only [hkodd, dite_true, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hweights := weak_gluing_transition_weight_add hΛ i a b k ht
  by_cases hd : deriv (ocCutoff D.α D.q D.Λ i k) t = 0
  · have hz : ∀ σ, trWeight (ocCutoff D.α D.q D.Λ i) (ocTau D.α D.q D.Λ i) a b k σ t = 0 := by
      intro σ
      unfold trWeight
      by_cases hmem : t ∈ Set.Icc (trLo (ocTau D.α D.q D.Λ i) a k σ)
        (trHi (ocTau D.α D.q D.Λ i) b k σ)
      · rw [Set.indicator_of_mem hmem, hd]
      · rw [Set.indicator_of_notMem hmem]
    simp only [hd, hz, zero_mul, Finset.sum_const_zero]
  · have hwin := interior_subset ((weak_gluing_cutoff_support_inside
      (α := D.α) (q := D.q) (i := i) hΛ k).2
      (subset_tsupport _ (Function.mem_support.mpr hd)))
    have hsplit := congrFun (weak_gluing_slot_lift_positive_split (slotLifts ⟨k, hkodd⟩)
      (Cc k) (hseq k hkodd) f hwin x) v
    simp only [Pi.sub_apply, Finset.sum_apply] at hsplit
    change weakSlotLift i N H G Cc k f t x v - f t x v = _ at hsplit
    rw [hsplit, hweights]
    simp only [Fintype.sum_bool, add_mul]

/-- Positive label grades of the selected slot lift have their finite reserved regularity and
physical lattice periodicity on the original slot window. -/
theorem weak_gluing_slot_lift_label_regular {N H U r : ℕ}
    {P : WeakPositiveParameters N H U} {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ}
    {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ} {slot : OddSlot}
    (W : WeakPositiveSlot P i G π slot) (hgeo : WeakPositiveGeometry P i G)
    (hrX : r ≤ P.slowOrder) (hrZ : r ≤ P.fastOrder)
    (f : WeakField G) (hf : ∀ t, ContDiff ℝ ((N + r : ℕ) : ℕ∞) (f t))
    (hfp : ∀ t, IsZ2Periodic (f t)) {hh : ℕ} (hhh : hh ≤ H) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i slot.1) :
    ContDiff ℝ (r : ℕ∞)
      (labelSrc N hh (D.eps i / Real.sqrt (D.kap i)) (D.eps (i - 1)) (D.eps i)
        (D.eps i / D.eps (i - 1)) W.coeff
        (fun s y => f s (D.flowOf (i - 1) s y (D.slotAnchor i slot.1))) t) ∧
    IsZ2Periodic
      (labelSrc N hh (D.eps i / Real.sqrt (D.kap i)) (D.eps (i - 1)) (D.eps i)
        (D.eps i / D.eps (i - 1)) W.coeff
        (fun s y => f s (D.flowOf (i - 1) s y (D.slotAnchor i slot.1))) t) := by
  have hΛ : 1 ≤ D.Λ := by have := hgeo.Λ_ge; omega
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hgeo.fast hgeo.band i
  have hcs : D.cellScaleSq i = (D.eps i / Real.sqrt (D.kap i)) ^ 2 := by
    dsimp only [OCData.cellScaleSq]
    rw [div_pow, Real.sq_sqrt W.setting.ν_pos.le]
  have htcell : ((D.eps i / Real.sqrt (D.kap i)) ^ 2)⁻¹ * t ∈
      Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) := by
    rw [← hcs, inv_mul_eq_div]
    exact ⟨(div_le_div_iff_of_pos_right hc).mpr ht.1,
      (div_le_div_iff_of_pos_right hc).mpr ht.2⟩
  let g : WeakField G := fun s y => f s (D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
  have hg : ∀ s, ContDiff ℝ ((N + r : ℕ) : ℕ∞) (g s) := fun s =>
    (hf s).comp ((CycleReference.streamFlow_spatial_smooth (D.hΦ (i - 1)) s
      (D.slotAnchor i slot.1)).of_le (by simp))
  have hgp : ∀ s, IsZ2Periodic (g s) := by
    intro s p y
    dsimp only [g]
    rw [native_flow_latticeShift D (i - 1) s (D.slotAnchor i slot.1) p y, hfp s p]
  constructor
  · exact weak_gluing_labelSrc_contDiff W.sequence hhh (by omega) (by omega) _ _ _ _ g hg htcell
  · obtain ⟨K, hK⟩ := TorusCompatible.ocEpsilon_inv_natCast D.q D.Λ i
    exact weak_gluing_labelSrc_periodic W.sequence hhh _ _ _ _ W.setting.ρ_pos.ne' K hK g
      ((hg _).of_le (natCast_le_natCast_order (Nat.le_add_right N r))) (hgp _) htcell
      (fun p n m α X z v u => weak_positive_slot_coefficient_slow_shift W
        (EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hgeo.fast hgeo.band 1).ne'
        hgeo.level hgeo.torus p hh hhh n m α _ htcell X z v u)

/-- The label slices of an actual slot lift, weighted by one clipped derivative piece, are
measurable globally. The coefficient clock is clamped only to prove measurability; the
field being estimated still uses the original sequence and original window. -/
theorem weak_gluing_slot_lift_label_slice_aemeasurable {N H U r : ℕ}
    {P : WeakPositiveParameters N H U} {D : OCData} {Dm j₀ : ℕ} {bw : ℝ} {i : ℕ}
    {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ} {slot : OddSlot}
    (W : WeakPositiveSlot P i G π slot) (hΛ : 1 ≤ D.Λ)
    (hrX : r ≤ P.slowOrder) (hrZ : r ≤ P.fastOrder)
    (f : WeakField G) (hf : ∀ t, ContDiff ℝ ((N + r : ℕ) : ℕ∞) (f t))
    (hfm : Measurable (Function.uncurry f)) (a b rs : ℝ) (σ : Bool)
    {hh : ℕ} (hhh : hh ≤ H) {j : ℕ} (hj : j ≤ r) (w : DerivativeWord2 j) :
    AEMeasurable (fun t => scalInt π (fun y => rs ^ j • orderedDerivative w
      (transitionSourceField N hh (D.eps i / Real.sqrt (D.kap i))
        (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1))
        (trWeight (ocCutoff D.α D.q D.Λ i) (ocTau D.α D.q D.Λ i) a b slot.1 σ)
        W.coeff (fun s y => f s (D.flowOf (i - 1) s y (D.slotAnchor i slot.1))) t) y) ^
          (1 / 2 : ℝ)) volume := by
  let ℓ := D.eps i / Real.sqrt (D.kap i)
  let l := ℓ ^ 2 * weakSlotLeft D i slot.1
  let u := ℓ ^ 2 * weakSlotRight D i slot.1
  let g : WeakField G := fun s y => f s (D.flowOf (i - 1) s y (D.slotAnchor i slot.1))
  have hℓ : 0 < ℓ := div_pos W.setting.e_pos (Real.sqrt_pos.mpr W.setting.ν_pos)
  have hc : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ.ne'
  have hcs : D.cellScaleSq i = ℓ ^ 2 := by
    dsimp only [OCData.cellScaleSq, ℓ]
    rw [div_pow, Real.sq_sqrt W.setting.ν_pos.le]
  have hl : l / ℓ ^ 2 = weakSlotLeft D i slot.1 := mul_div_cancel_left₀ _ hc
  have hu : u / ℓ ^ 2 = weakSlotRight D i slot.1 := mul_div_cancel_left₀ _ hc
  have hset := W.setting
  rw [← hl, ← hu] at hset
  have hseq := W.sequence
  rw [← hl, ← hu] at hseq
  have hg : ∀ s, ContDiff ℝ ((N + r : ℕ) : ℕ∞) (g s) := fun s =>
    (hf s).comp ((CycleReference.streamFlow_spatial_smooth (D.hΦ (i - 1)) s
      (D.slotAnchor i slot.1)).of_le (by simp))
  have hflow : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 =>
      D.flowOf (i - 1) z.1 z.2 (D.slotAnchor i slot.1)) :=
    (CycleReference.streamFlow_joint_smooth (D.hΦ (i - 1))).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  have hgm : Measurable (Function.uncurry g) :=
    hfm.comp (measurable_fst.prodMk hflow.continuous.measurable)
  have hclamp : Continuous (fun s => ℓ ^ 2 *
      (Set.projIcc (l / ℓ ^ 2) (u / ℓ ^ 2) hset.window s : ℝ)) :=
    continuous_const.mul (continuous_subtype_val.comp continuous_projIcc)
  have hm := weak_gluing_labelSrc_slice_aemeasurable hset hseq (by omega) hhh
    (show r ≤ P.slowOrder + W.cap + 2 by omega) (show r ≤ max (P.fastOrder + 1) (P.fastOrder + 2) by omega)
    hℓ.ne' (D.eps (i - 1)) (D.eps i) (D.eps i / D.eps (i - 1)) g hg
    (fun X => hgm.comp (hclamp.measurable.prodMk measurable_const)) π rs hj w
  apply weak_gluing_weighted_label_slice_aemeasurable π rs w _ (Set.Icc l u)
    measurableSet_Icc _ (measurable_trWeight _ _ _ _ _ _) _ hm
  intro s hs
  have hwin := (mem_window_of_trIcc (Construction.Stream.ocTau_pos hΛ)
    (trWeight_ne_zero (Function.mem_support.mp hs)).1).1
  simpa only [l, u, ← hcs, weakSlotLeft, weakSlotRight, OCData.slotStart, mul_div_cancel₀ _ (hcs.symm ▸ hc)] using hwin

private theorem weakGluingScalInt_word_neg {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ v, NormedAddCommGroup (h v)] [∀ v, NormedSpace ℝ (h v)]
    (π : ι → ℝ) (rs : ℝ) {j : ℕ} (w : DerivativeWord2 j) (f : Vec 2 → ∀ v, h v) :
    scalInt π (fun y => rs ^ j • orderedDerivative w (fun y' => -f y') y) =
      scalInt π (fun y => rs ^ j • orderedDerivative w f y) := by
  have he : (fun y => -f y) = fun y => (-1 : ℝ) • f y := by
    funext y
    exact (neg_one_smul ℝ (f y)).symm
  rw [he, scalInt_word_smul]
  norm_num

/-- Sum all actual cutoff transitions, retaining the finite coarse energy and the explicit
number of observed pieces. The input is only finitely smooth; the decay constants precede
all data, slots, component families and the ambient degree cap. -/
theorem weak_gluing_time_transition_sum {N H J Lr Acl r : ℕ}
    (P : WeakPositiveParameters N H (Lr + 3)) (hP : WeakGluingFactoryOrders J Lr P)
    (hL : weakGluingReadoutOrder J N H Acl r ≤ Lr) (hAcl : 1 ≤ Acl)
    (Dχ : ℝ) (hDχ : 1 ≤ Dχ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
    ∀ {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {i : ℕ}
      {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ}
      (slotLifts : ∀ slot : OddSlot, WeakPositiveSlot P i G π slot)
      (_hgeo : WeakPositiveGeometry P i G) {sX sZ : ℕ}
      (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
      (_hseq : IsWeakReadoutLifts i N H sX sZ G Cc) (rs : ℝ),
      0 < rs → rs ≤ D.eps i → D.eps i ≤ D.eps (i - 1) →
      D.kap (i - 1) = D.kap i →
      (∀ slot : OddSlot, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i slot.1,
        JetBound (fun y => D.flowOf (i - 1) t y (D.slotAnchor i slot.1))
          (4 * (N + P.capMax) + 2 * Acl + 16 + r + 2) Dχ (D.eps (i - 1)) ∧
        JetBound (fun y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y t)
          (4 * (N + P.capMax) + 2 * Acl + 16 + r + 2) Dχ (D.eps (i - 1))) →
      (∀ slot : OddSlot, ∀ σ : Bool, IsQuietOn (slotLifts slot).Q.edge
        (fun t z => Real.sqrt (slotLifts slot).Q.η • (slotLifts slot).Q.v t z)
        (Set.Icc (weakGluingGapLeft (ocTau D.α D.q D.Λ i) slot.1 σ /
          (D.eps i / Real.sqrt (D.kap i)) ^ 2)
          (weakGluingGapRight (ocTau D.α D.q D.Λ i) slot.1 σ /
            (D.eps i / Real.sqrt (D.kap i)) ^ 2))) →
    ∀ a b : ℝ, ∀ f : WeakField G,
      (∀ t, ContDiff ℝ ((4 * (N + P.capMax) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞) (f t)) →
      (∀ t, IsZ2Periodic (f t)) → Measurable (Function.uncurry f) →
      ∫⁻ t in Set.Icc a b, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
        scalInt π (fun y => rs ^ j • orderedDerivative w
          (weakResidualGlueTime i N H G Cc f t) y)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (sliceConst H r Dχ ^ (1 / 2 : ℝ)) *
          (((ocObsPulses D.α D.q D.Λ i a b).card * 2 *
            ∑ j ∈ Finset.range (r + 1), 2 ^ j * (H + 1) : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (C * (D.eps i / Real.sqrt (D.kap i)) *
            Real.sqrt (1 / ocTau D.α D.q D.Λ i) *
            Real.exp (-(c * ocTau D.α D.q D.Λ i / (D.eps i / Real.sqrt (D.kap i)) ^ 2))) *
            classicalStrongEnergy (h := fun v : CompIn G.comps => ScalarH v.1.root) (D.eps (i - 1)) (D.kap (i - 1)) π (Set.Icc a b)
              (4 * (N + P.capMax) + 2 * Acl + 16 + r) f) := by
  obtain ⟨C, c, hC, hc, hb⟩ := weak_gluing_cutoff_transition_bound P hP hL hAcl Dχ
  refine ⟨C, c, hC, hc, ?_⟩
  intro D Dm bw j₀ i G π slotLifts hgeo sX sZ Cc hseq rs hrs hrse heE hplateau hJ hquiet
    a b f hf hfp hfm
  classical
  let S := ocObsPulses D.α D.q D.Λ i a b ×ˢ (Finset.univ : Finset Bool)
  let ψ (p : ℤ × Bool) := trWeight (ocCutoff D.α D.q D.Λ i) (ocTau D.α D.q D.Λ i) a b p.1 p.2
  let χ (p : ℤ × Bool) (s : ℝ) (y : Vec 2) := D.flowOf (i - 1) s y (D.slotAnchor i p.1)
  let χi (p : ℤ × Bool) (s : ℝ) (y : Vec 2) := D.flowOf (i - 1) (D.slotAnchor i p.1) y s
  let L (p : ℤ × Bool) (hh : ℕ) : WeakField G := if hp : Odd p.1 then
    labelSrc N hh (D.eps i / Real.sqrt (D.kap i)) (D.eps (i - 1)) (D.eps i)
      (D.eps i / D.eps (i - 1)) (slotLifts ⟨p.1, hp⟩).coeff (fun t y => f t (χ p t y)) else 0
  have hodd : ∀ p ∈ S, Odd p.1 := fun p hp => (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2.1
  have hΛ : 1 ≤ D.Λ := by have := hgeo.Λ_ge; omega
  have hτ := Construction.Stream.ocTau_pos (α := D.α) (q := D.q) hΛ (m := i)
  have hrX : r ≤ P.slowOrder := by
    have := (weak_gluing_factory_reserves hP hL).2.1
    omega
  have hrZ : r ≤ P.fastOrder := by
    have := (weak_gluing_factory_reserves hP hL).2.2
    omega
  have hf' : ∀ t, ContDiff ℝ ((N + r : ℕ) : ℕ∞) (f t) := fun t =>
    (hf t).of_le (natCast_le_natCast_order (by omega))
  have hwin (p : ℤ × Bool) (t : ℝ) (ht : ψ p t ≠ 0) :
      t ∈ ocPulseWindow D.α D.q D.Λ i p.1 :=
    (mem_window_of_trIcc hτ (trWeight_ne_zero ht).1).1
  let X := ENNReal.ofReal (C * (D.eps i / Real.sqrt (D.kap i)) *
      Real.sqrt (1 / ocTau D.α D.q D.Λ i) *
      Real.exp (-(c * ocTau D.α D.q D.Λ i / (D.eps i / Real.sqrt (D.kap i)) ^ 2))) *
      classicalStrongEnergy (h := fun v : CompIn G.comps => ScalarH v.1.root) (D.eps (i - 1)) (D.kap (i - 1)) π (Set.Icc a b)
        (4 * (N + P.capMax) + 2 * Acl + 16 + r) f
  have hsum := weak_gluing_transition_sum_bound S H r hDχ hrs (hrse.trans heE) π
    (Set.Icc a b) measurableSet_Icc ψ χ χi L
    (fun p _ t _ _ => weak_gluing_native_isChart D (i - 1) t (D.slotAnchor i p.1))
    (fun p _ t _ _ => (CycleReference.streamFlow_spatial_smooth (D.hΦ (i - 1))
      (D.slotAnchor i p.1) t).of_le (by simp))
    (fun p hp t _ ht n hn hn1 y => (hJ ⟨p.1, hodd p hp⟩ t (hwin p t ht)).2 n hn (by omega) y)
    (by
      intro p hp t _ ht hh hhh
      simpa only [L, hodd p hp, dite_true] using
        (weak_gluing_slot_lift_label_regular (slotLifts ⟨p.1, hodd p hp⟩) hgeo hrX hrZ
          f hf' hfp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)) (hwin p t ht)).1)
    (by
      intro p hp t _ ht hh hhh
      simpa only [L, hodd p hp, dite_true] using
        (weak_gluing_slot_lift_label_regular (slotLifts ⟨p.1, hodd p hp⟩) hgeo hrX hrZ
          f hf' hfp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)) (hwin p t ht)).2)
    (fun t _ => card_active_le_two hodd _ hτ a b t)
    (by
      intro p hp j hj w hh hhh
      have hm := weak_gluing_slot_lift_label_slice_aemeasurable (slotLifts ⟨p.1, hodd p hp⟩)
        hΛ hrX hrZ f hf' hfm a b rs p.2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) w
      simpa only [L, hodd p hp, dite_true, transitionSourceField_eq_smul] using hm.restrict)
    X (by
      intro p hp j hj w hh hhh
      have hbound := hb i G π ⟨p.1, hodd p hp⟩ (slotLifts ⟨p.1, hodd p hp⟩) rs hΛ hrs hrse heE
        hplateau (TorusCompatible.ocEpsilon_inv_natCast D.q D.Λ i) (χ p) (χi p)
        (fun t => weak_gluing_native_isChart D (i - 1) t (D.slotAnchor i p.1))
        (fun t => CycleReference.streamFlow_spatial_smooth (D.hΦ (i - 1)) t (D.slotAnchor i p.1))
        (fun t => CycleReference.streamFlow_spatial_smooth (D.hΦ (i - 1)) (D.slotAnchor i p.1) t)
        (hJ ⟨p.1, hodd p hp⟩) (hquiet ⟨p.1, hodd p hp⟩) a b p.2 hh
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)) f (fun t _ => hf t) (fun t _ => hfp t) j
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) w
      have he := (setLIntegral_le_lintegral (Set.Icc a b) _).trans hbound
      simpa only [L, hodd p hp, dite_true, transitionSourceField_eq_smul] using he)
  have hsource : ∀ t ∈ Set.Icc a b, weakResidualGlueTime i N H G Cc f t =
      fun y => -∑ p ∈ S, ψ p t • ∑ hh ∈ Finset.range (H + 1), L p hh t (χi p t y) := by
    intro t ht
    funext y
    rw [weak_gluing_time_transition_decomposition slotLifts Cc hseq hΛ a b f ht y]
    congr 1
    exact Finset.sum_congr rfl fun p hp => by simp only [L, hodd p hp, dite_true]; rfl
  have heq : (∫⁻ t in Set.Icc a b, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
        scalInt π (fun y => rs ^ j • orderedDerivative w
          (weakResidualGlueTime i N H G Cc f t) y)) ^ (1 / 2 : ℝ)) =
      ∫⁻ t in Set.Icc a b, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
        scalInt π (fun y => rs ^ j • orderedDerivative w (fun y' =>
          ∑ p ∈ S, ψ p t • ∑ hh ∈ Finset.range (H + 1), L p hh t (χi p t y')) y)) ^
            (1 / 2 : ℝ) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp_rw [hsource t ht, weakGluingScalInt_word_neg]
  rw [heq]
  simpa only [S, Finset.card_product, Fintype.card_bool, Finset.card_univ] using hsum

/-- The scalar classical forcing cost is bounded directly by its word-aggregated slice
integral. This is the finite-family Minkowski estimate, with no component-count loss. -/
theorem weak_gluing_classical_cost_le_aggregate {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    {G : GenStage D ScalarH Dm bw j₀} (ν rs : ℝ) (π : CompIn G.comps → ℝ)
    (hπ : ∀ v, 0 < π v) (I : Set ℝ) (hI : MeasurableSet I) (r : ℕ) (q : WeakField G)
    (hq : ∀ t ∈ I, ContDiff ℝ (r : ℕ∞) (q t)) :
    weakClassicalForcingCost ν rs π I r (fun _ _ _ _ => 0) q ≤
      ∫⁻ t in I, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
        scalInt π (fun y => rs ^ j • orderedDerivative w (q t) y)) ^ (1 / 2 : ℝ) := by
  classical
  let W : CompIn G.comps → ℝ≥0∞ := fun v => ENNReal.ofReal (π v)⁻¹
  let u := fun v => W v ^ (1 / 2 : ℝ)
  let g := fun v t => u v * classicalFactorialSq rs r (fun x => q t x v) ^ (1 / 2 : ℝ)
  have hutop : ∀ v, u v ≠ ⊤ := fun v =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have husq : ∀ v, u v ^ 2 = W v := by
    intro v
    change (W v ^ (1 / 2 : ℝ)) ^ 2 = W v
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hzero : classicalFactorialSq rs r (fun _ : Vec 2 =>
      (WithLp.toLp 2 (fun _ : Fin 2 => (0 : ℝ)) : PiLp 2 (fun _ : Fin 2 => ℝ))) = 0 := by
    change classicalFactorialSq rs r (fun _ : Vec 2 => (0 : PiLp 2 (fun _ : Fin 2 => ℝ))) = 0
    simp [classicalFactorialSq, orderedDerivative_zero_fun]
  unfold weakClassicalForcingCost
  simp only [hzero, lintegral_zero, mul_zero, zero_add]
  have hwinv : ∀ v, (ENNReal.ofReal (π v))⁻¹ = W v := fun v =>
    (ENNReal.ofReal_inv_of_pos (hπ v)).symm
  simp_rw [hwinv]
  have he : (∑ v, W v * (∫⁻ t in I, classicalFactorialSq rs r (fun x => q t x v) ^
      (1 / 2 : ℝ)) ^ 2) = ∑ v, (∫⁻ t in I, g v t) ^ 2 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [show (∫⁻ t in I, g v t) = u v * ∫⁻ t in I,
      classicalFactorialSq rs r (fun x => q t x v) ^ (1 / 2 : ℝ) from
        lintegral_const_mul' _ _ (hutop v), mul_pow, husq]
  rw [he]
  refine (weakResidualCost_minkowski (μ := volume.restrict I) g).trans ?_
  apply setLIntegral_mono' hI
  intro t ht
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  have hg : ∀ v, (g v t) ^ 2 = W v * classicalFactorialSq rs r (fun x => q t x v) := by
    intro v
    change (u v * classicalFactorialSq rs r (fun x => q t x v) ^ (1 / 2 : ℝ)) ^ 2 = _
    rw [mul_pow, husq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp_rw [hg]
  calc ∑ v, W v * classicalFactorialSq rs r (fun x => q t x v)
      ≤ ∑ v, W v * ∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
          weakResidualCostScal q rs w t v :=
        Finset.sum_le_sum fun v _ => mul_le_mul_right (weakResidualCost_cfs_scal_le q r t rs v) _
    _ = ∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j, ∑ v,
        W v * weakResidualCostScal q rs w t v := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun w _ => ?_
      unfold scalInt
      refine Finset.sum_congr rfl fun v _ => congrArg (fun x => W v * x) ?_
      unfold weakResidualCostScal
      refine lintegral_congr fun y => ?_
      dsimp only
      rw [Pi.smul_apply, smul_eq_mul, orderedDerivative_apply w
        ((hq t ht).of_le (natCast_le_natCast_order (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))) v y]

/-- Time locality of the literal time-gluing source; the supplied lift arrays and their
original start times are unchanged. -/
theorem weak_gluing_time_input_congr {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    (i N H : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    {f g : WeakField G} {t : ℝ} (hc : D.cellScaleSq i ≠ 0) (he : f t = g t) :
    weakResidualGlueTime i N H G Cc f t = weakResidualGlueTime i N H G Cc g t := by
  classical
  funext x v
  unfold weakResidualGlueTime
  apply congrArg (fun z : ℝ => -z)
  apply Finset.sum_congr rfl
  intro k _
  have hL := congrFun (pulsePhysicalLift_congr_time (D.cellScaleSq i) (D.eps (i - 1))
    (h := fun v : CompIn G.comps => ScalarH v.1.root)
    (D.eps i) (D.eps i / D.eps (i - 1)) N H (Cc k)
    (fun s y => D.flowOf (i - 1) s y (D.slotAnchor i k))
    (fun s y => D.flowOf (i - 1) (D.slotAnchor i k) y s) hc he x) v
  change weakSlotLift i N H G Cc k f t x v = weakSlotLift i N H G Cc k g t x v at hL
  rw [hL, he]

private theorem weakGluingStrongEnergy_congr_on {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ v, NormedAddCommGroup (h v)] [∀ v, NormedSpace ℝ (h v)]
    (ρ ν : ℝ) (π : ι → ℝ) (I : Set ℝ) (hI : MeasurableSet I) (r : ℕ)
    (f g : ℝ → Vec 2 → ∀ v, h v) (he : ∀ t ∈ I, f t = g t) :
    classicalStrongEnergy ρ ν π I r f = classicalStrongEnergy ρ ν π I r g := by
  unfold classicalStrongEnergy
  apply congrArg (fun z : ℝ≥0∞ => z ^ (1 / 2 : ℝ))
  refine Finset.sum_congr rfl fun v _ => congrArg (fun z => ENNReal.ofReal (π v)⁻¹ * z) ?_
  apply congrArg₂ (· + ·)
  · exact iSup_congr fun t => iSup_congr fun ht => by rw [he t ht]
  · apply congrArg (fun z => ENNReal.ofReal ν * z)
    exact setLIntegral_congr_fun hI fun t ht => by rw [he t ht]

/-- The complete classical time-gluing bound on a closed observation window. Values of the
coarse input outside that window are arbitrary. Only the stated finite spatial reserve and
joint measurability of its zero extension are used. -/
theorem weak_gluing_time_classical_bound {N H J Lr Acl r : ℕ}
    (P : WeakPositiveParameters N H (Lr + 3)) (hP : WeakGluingFactoryOrders J Lr P)
    (hL : weakGluingReadoutOrder J N H Acl r ≤ Lr) (hAcl : 1 ≤ Acl)
    (Dχ : ℝ) (hDχ : 1 ≤ Dχ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
    ∀ {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {i : ℕ}
      {G : GenStage D ScalarH Dm bw j₀} {π : CompIn G.comps → ℝ}
      (slotLifts : ∀ slot : OddSlot, WeakPositiveSlot P i G π slot)
      (_hgeo : WeakPositiveGeometry P i G) {sX sZ : ℕ}
      (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
      (_hseq : IsWeakReadoutLifts i N H sX sZ G Cc) (rs : ℝ),
      0 < rs → rs ≤ D.eps i → D.eps i ≤ D.eps (i - 1) →
      D.kap (i - 1) = D.kap i →
      (∀ slot : OddSlot, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i slot.1,
        JetBound (fun y => D.flowOf (i - 1) t y (D.slotAnchor i slot.1))
          (4 * (N + P.capMax) + 2 * Acl + 16 + r + 2) Dχ (D.eps (i - 1)) ∧
        JetBound (fun y => D.flowOf (i - 1) (D.slotAnchor i slot.1) y t)
          (4 * (N + P.capMax) + 2 * Acl + 16 + r + 2) Dχ (D.eps (i - 1))) →
      (∀ slot : OddSlot, ∀ σ : Bool, IsQuietOn (slotLifts slot).Q.edge
        (fun t z => Real.sqrt (slotLifts slot).Q.η • (slotLifts slot).Q.v t z)
        (Set.Icc (weakGluingGapLeft (ocTau D.α D.q D.Λ i) slot.1 σ /
          (D.eps i / Real.sqrt (D.kap i)) ^ 2)
          (weakGluingGapRight (ocTau D.α D.q D.Λ i) slot.1 σ /
            (D.eps i / Real.sqrt (D.kap i)) ^ 2))) →
    ∀ a b : ℝ, ∀ f : WeakField G,
      (∀ t ∈ Set.Icc a b, ContDiff ℝ
        ((4 * (N + P.capMax) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞) (f t)) →
      (∀ t ∈ Set.Icc a b, IsZ2Periodic (f t)) →
      Measurable (fun z : ℝ × Vec 2 => if z.1 ∈ Set.Icc a b then f z.1 z.2 else 0) →
      weakClassicalForcingCost (D.kap i) rs π (Set.Icc a b) r (fun _ _ _ _ => 0)
        (weakResidualGlueTime i N H G Cc f) ≤
        ENNReal.ofReal (sliceConst H r Dχ ^ (1 / 2 : ℝ)) *
          (((ocObsPulses D.α D.q D.Λ i a b).card * 2 *
            ∑ j ∈ Finset.range (r + 1), 2 ^ j * (H + 1) : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (C * (D.eps i / Real.sqrt (D.kap i)) *
            Real.sqrt (1 / ocTau D.α D.q D.Λ i) *
            Real.exp (-(c * ocTau D.α D.q D.Λ i / (D.eps i / Real.sqrt (D.kap i)) ^ 2))) *
            classicalStrongEnergy (h := fun v : CompIn G.comps => ScalarH v.1.root) (D.eps (i - 1)) (D.kap (i - 1)) π (Set.Icc a b)
              (4 * (N + P.capMax) + 2 * Acl + 16 + r) f) := by
  obtain ⟨C, c, hC, hc, hb⟩ := weak_gluing_time_transition_sum P hP hL hAcl Dχ hDχ
  refine ⟨C, c, hC, hc, ?_⟩
  intro D Dm bw j₀ i G π slotLifts hgeo sX sZ Cc hseq rs hrs hrse heE hplateau hJ hquiet
    a b f hf hfp hfm
  classical
  let f₀ : WeakField G := fun t => if t ∈ Set.Icc a b then f t else 0
  have hf₀ : ∀ t, ContDiff ℝ
      ((4 * (N + P.capMax) + 2 * Acl + 16 + r + 1 : ℕ) : ℕ∞) (f₀ t) := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · simpa only [f₀, ht, ite_true] using hf t ht
    · simp only [f₀, ht, ite_false]
      exact contDiff_const
  have hp₀ : ∀ t, IsZ2Periodic (f₀ t) := by
    intro t p x
    by_cases ht : t ∈ Set.Icc a b
    · simpa only [f₀, ht, ite_true] using hfp t ht p x
    · simp only [f₀, ht, ite_false, Pi.zero_apply]
  have hm₀ : Measurable (Function.uncurry f₀) := by
    simpa only [f₀, Function.uncurry_def, ite_apply, Pi.zero_apply] using hfm
  have hbound := hb slotLifts hgeo Cc hseq rs hrs hrse heE hplateau hJ hquiet a b f₀ hf₀ hp₀ hm₀
  have hΛ : 1 ≤ D.Λ := by have := hgeo.Λ_ge; omega
  have hcell := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hgeo.fast hgeo.band i
  have hsource : ∀ t ∈ Set.Icc a b, weakResidualGlueTime i N H G Cc f₀ t =
      weakResidualGlueTime i N H G Cc f t := fun t ht =>
    weak_gluing_time_input_congr i N H G Cc hcell.ne' (by simp only [f₀, ht, ite_true])
  have hrX : r ≤ P.slowOrder := by have := (weak_gluing_factory_reserves hP hL).2.1; omega
  have hrZ : r ≤ P.fastOrder := by have := (weak_gluing_factory_reserves hP hL).2.2; omega
  have hqc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (r : ℕ∞) (weakResidualGlueTime i N H G Cc f t) := by
    intro t ht
    exact contDiff_pi.mpr (weak_gluing_time_spatial_regular slotLifts hgeo Cc hseq hrX hrZ f t
      ((hf t ht).of_le (natCast_le_natCast_order (by omega))) (hfp t ht)).1
  have hcost := weak_gluing_classical_cost_le_aggregate (G := G) (D.kap i) rs π
    ((slotLifts ⟨1, by decide⟩).setting).mass_pos (Set.Icc a b) measurableSet_Icc r (weakResidualGlueTime i N H G Cc f) hqc
  have heq : (∫⁻ t in Set.Icc a b, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
      scalInt π (fun y => rs ^ j • orderedDerivative w
        (weakResidualGlueTime i N H G Cc f₀ t) y)) ^ (1 / 2 : ℝ)) =
      ∫⁻ t in Set.Icc a b, (∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
        scalInt π (fun y => rs ^ j • orderedDerivative w
          (weakResidualGlueTime i N H G Cc f t) y)) ^ (1 / 2 : ℝ) :=
    setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hsource t ht]
  rw [heq] at hbound
  have heqE := weakGluingStrongEnergy_congr_on
    (h := fun v : CompIn G.comps => ScalarH v.1.root)
    (D.eps (i - 1)) (D.kap (i - 1)) π (Set.Icc a b) measurableSet_Icc
    (4 * (N + P.capMax) + 2 * Acl + 16 + r) f₀ f
    (fun t ht => by simp only [f₀, ht, ite_true])
  rw [heqE] at hbound
  exact hcost.trans hbound

end AVRegularity.Providers.WeakGen.Residual
end
end
