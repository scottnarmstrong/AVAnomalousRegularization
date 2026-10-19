-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.EntryWeakAssembly.FullReadoutLocalReserves
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Proofs.Results.Iteration.CascadeSchedule
public import AVRegularity.EntryWeakAssembly.QuietBackwardEvolution
import AVRegularity.CycleComparison.Error.WeakSolution
public import AVRegularity.EntryWeakAssembly.Assembly.WeakComparisonEnergyOfIngredients
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Applications.Global.CompactRangeMain

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The phase-free native flux retains its parent spatial scale under the actual
parent flow. Prices and the flow threshold precede the ambient order cap. -/

open AVRegularity.Providers.QuietAtlas
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.ChartTransport

/-- Finite scaled composition prices a bounded slow jet without bounding the
value of the flow. All constants are chosen before the field and the chart. -/
theorem weak_quiet_scaled_composition_bound {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (N : ℕ) (D E θ : ℝ) (hD : 1 ≤ D) (hE : 0 < E) (hθ : 0 ≤ θ)
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (f : Vec 2 → V) (φ : Vec 2 → Vec 2)
    (hf : ContDiff ℝ (N : ℕ∞) f) (hφ : ContDiff ℝ (N : ℕ∞) φ)
    (hchart : JetBound φ N D E)
    (hj : ∀ j ≤ N, ∀ y, E ^ j * ‖iteratedFDeriv ℝ j f y‖ ≤ C j * θ)
    (n : ℕ) (hn : n ≤ N) (x : Vec 2) :
    E ^ n * ‖iteratedFDeriv ℝ n (f ∘ φ) x‖ ≤
      ((N.factorial : ℝ) * D ^ N * ∑ j ∈ Finset.range (N + 1), C j) * θ := by
  have hD0 := zero_le_one.trans hD
  have hh := scaled_comp_bound (hf.of_le (by exact_mod_cast hn))
    (hφ.of_le (by exact_mod_cast hn)) hD hE (le_refl E) x
    (fun p hp hpn => hchart p hp (hpn.trans hn) x)
  have hsum : (∑ j ∈ Finset.range (n + 1), E ^ j * ‖iteratedFDeriv ℝ j f (φ x)‖) ≤
      (∑ j ∈ Finset.range (N + 1), C j) * θ := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), C j * θ :=
        Finset.sum_le_sum (fun j hjn => hj j (by have := Finset.mem_range.mp hjn; omega) _)
      _ = (∑ j ∈ Finset.range (n + 1), C j) * θ := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun j _ _ => hC j)) hθ
  have hfactor : (n.factorial : ℝ) * D ^ n ≤ N.factorial * D ^ N :=
    mul_le_mul (by exact_mod_cast Nat.factorial_le hn) (pow_le_pow_right₀ hD hn)
      (pow_nonneg hD0 n) (Nat.cast_nonneg _)
  exact hh.trans ((mul_le_mul hfactor hsum
    (Finset.sum_nonneg (fun j _ => mul_nonneg (pow_nonneg hE.le j) (norm_nonneg _)))
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD0 N))).trans_eq (by ring))

/-- Uniform flow sampling of the actual phase-free incoming flux on the
trimmed middle half. The only additional floor is the existing native flow
threshold; it is chosen from the physical parameters and N. -/
theorem weak_quiet_native_flow_jets {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M₀ : ℕ,
    ∀ (plan : WeakPassagePlan), WeakPassageCommonOK plan →
    ∀ (R : WeakPassageRequest A) (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
      (i : ℕ), M₀ ≤ c.M → c.M < i → i ≤ c.M + A.Jw →
    IsHistoryQuiet c.D (c.M + A.Jw) i (weakMiddleHalf c r i) →
    ∀ (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
      (d : ℕ) (I : DerivativeWord2 (d - 1)) (p : OddSlot) (t : ℝ),
    t ∈ weakMiddleHalf c r i →
    t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ (c.stage i).level p.1 →
    let f := fun Y => (c.stage i).fam.slowFlux
      (c.D.eps (i - 1)) p ((c.stage i).actual p) v u γ d I t Y ((c.D.eps i)⁻¹ • Y)
    let φ := fun Y => c.D.flowOf (i - 1) (c.D.slotAnchor i p.1) Y t
    ContDiff ℝ (N : ℕ∞) (f ∘ φ) ∧
    ∀ n ≤ N, ∀ Y : Vec 2, c.D.eps (i - 1) ^ n *
      ‖iteratedFDeriv ℝ n (f ∘ φ) Y‖ ≤
        C * (weakQuietCertificatePrice R * ((c.stage i).fam.identity v u γ).record.size) := by
  obtain ⟨Cs, hCs, hjets⟩ := weak_quiet_native_diagonal_jets A N
  let Cf := EntryWeakProofs.weakChartJetBudget N 0
  have hCf : 1 ≤ Cf := EntryWeakProofs.weakChartJetBudget_ge_one _ _
  let C := (N.factorial : ℝ) * Cf ^ N * ∑ j ∈ Finset.range (N + 1), Cs j
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hCf) N))
    (Finset.sum_nonneg (fun j _ => hCs j))
  by_cases hΛ : 128 ≤ A.Λ
  · obtain ⟨M₀, _hM₀, hflow⟩ := uniform_native_physical_flow_jets B.α B.s B.q B.hα₀ B.hα₁
      B.hs₀ B.hs₁ B.hq A.Λ hΛ B.ζ B.hζ N
    refine ⟨C, hC, M₀, ?_⟩
    intro plan hcommon R c r i hM hi hit hquiet v u γ d I p t ht htp
    dsimp only
    obtain ⟨hs, hj⟩ := hjets plan hcommon R c r i hi.le hit hquiet v u γ d I p t ht htp
    have hlev := EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _ c.construction i hi.le hit
    have htp' : t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ i p.1 := by simpa only [hlev] using htp
    have hE : 0 < c.D.eps (i - 1) := Construction.Stream.ocEpsilon_pos (by
      rw [c.base_eq]; exact (by norm_num : 1 ≤ 128).trans hΛ)
    have hf := (hflow c.D c.alpha c.q_eq c.base_eq c.profile_eq c.streams i (by omega)
      p.1 p.2 (c.D.eps (i - 1)) hE (le_refl _) t htp').2
    have hφ : ContDiff ℝ (N : ℕ∞)
        (fun Y => c.D.flowOf (i - 1) (c.D.slotAnchor i p.1) Y t) :=
      (CycleReference.streamFlow_spatial_smooth (c.D.hΦ (i - 1)) (c.D.slotAnchor i p.1) t).of_le
        (by simp)
    refine ⟨hs.comp hφ, ?_⟩
    intro n hn Y
    apply weak_quiet_scaled_composition_bound N Cf _ _ hCf hE _ Cs hCs _ _ hs hφ hf hj n hn Y
    exact mul_nonneg (Finset.sum_nonneg (fun _ _ => le_max_left 0 _))
      ((c.stage i).fam.identity v u γ).record.size_nonneg
  · refine ⟨C, hC, 0, ?_⟩
    intro plan _ R c
    exact (hΛ ((plan.base_ge B).trans c.base_ge)).elim

/-- Multiplying by the literal dimensional factor preserves the pre-cap
parent-flow price. The factor retains the finer wavelength, ready for Piola
order lowering. -/
theorem weak_quiet_native_dimensional_flow_jets {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M₀ : ℕ,
    ∀ (plan : WeakPassagePlan), WeakPassageCommonOK plan →
    ∀ (R : WeakPassageRequest A) (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
      (i : ℕ), M₀ ≤ c.M → c.M < i → i ≤ c.M + A.Jw →
    IsHistoryQuiet c.D (c.M + A.Jw) i (weakMiddleHalf c r i) →
    ∀ (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
      (d : ℕ) (I : DerivativeWord2 (d - 1)) (p : OddSlot) (t : ℝ),
    t ∈ weakMiddleHalf c r i →
    t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ (c.stage i).level p.1 →
    let f := fun Y => (c.stage i).fam.dimFlux (c.D.κ c.M) (c.D.eps i)
      (c.D.eps (i - 1)) p ((c.stage i).actual p) v u γ d I t
      (c.D.flowOf (i - 1) (c.D.slotAnchor i p.1) Y t)
      ((c.D.eps i)⁻¹ • c.D.flowOf (i - 1) (c.D.slotAnchor i p.1) Y t)
    ContDiff ℝ (N : ℕ∞) f ∧
    ∀ n ≤ N, ∀ Y : Vec 2, c.D.eps (i - 1) ^ n * ‖iteratedFDeriv ℝ n f Y‖ ≤
      C * (c.D.κ c.M * c.D.eps i ^ (d - 2)) *
        (weakQuietCertificatePrice R * ((c.stage i).fam.identity v u γ).record.size) := by
  obtain ⟨C, hC, M₀, hbound⟩ := weak_quiet_native_flow_jets A N
  refine ⟨C, hC, M₀, ?_⟩
  intro plan hcommon R c r i hM hi hit hquiet v u γ d I p t ht htp
  obtain ⟨hs, hj⟩ := hbound plan hcommon R c r i hM hi hit hquiet v u γ d I p t ht htp
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  have hζ : IsFastProfile c.D.ζ := by rw [c.profile_eq]; exact B.hζ
  have hband : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]
    exact c.band
  have hν : 0 < c.D.κ c.M := CycleReference.bandChain_pos hΛ hζ hband
    (by rw [c.terminal])
  let a := c.D.κ c.M * c.D.eps i ^ (d - 2)
  have ha : 0 ≤ a := mul_nonneg hν.le (pow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _)
  let f := (fun Y => (c.stage i).fam.slowFlux (c.D.eps (i - 1)) p ((c.stage i).actual p)
    v u γ d I t Y ((c.D.eps i)⁻¹ • Y)) ∘
    (fun Y => c.D.flowOf (i - 1) (c.D.slotAnchor i p.1) Y t)
  change ContDiff ℝ (N : ℕ∞) (fun Y => a • f Y) ∧ _
  refine ⟨hs.const_smul a, ?_⟩
  intro n hn Y
  change c.D.eps (i - 1) ^ n * ‖iteratedFDeriv ℝ n (fun Y => a • f Y) Y‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hs.of_le (by exact_mod_cast hn)).contDiffAt,
    norm_smul, Real.norm_of_nonneg ha]
  have hh := mul_le_mul_of_nonneg_left (hj n hn Y) ha
  convert hh using 1 <;> ring

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! First pinned quiet margins after each preceding passage time. These are pulse
vanishing statements; no independence on the untrimmed quiet set is used. -/

private theorem pinned_quiet_margin_after {α q : ℝ} {Λ i : ℕ} (hΛ : 1 ≤ Λ)
    (ζ : ℝ → ℝ) (s : ℝ) :
    ∃ t : ℝ, (∃ l : ℤ, t = ((l : ℝ) + 1 / 2) * ocTauPP α q Λ i) ∧
      s + ocTauP α q Λ i ≤ t ∧
      t < s + ocTauPP α q Λ i + ocTauP α q Λ i ∧
      t ≤ s + 2 * ocTauPP α q Λ i ∧ t ∈ ocQuietTimes α q Λ ζ i := by
  let T := ocTauPP α q Λ i
  let P := ocTauP α q Λ i
  have hT : 0 < T := Construction.Stream.ocTauPP_pos hΛ
  have hP : 0 < P := Velocity.Jets.ocTauP_pos hΛ
  have hPT : P ≤ T := by
    have := (CycleReference.pulse_time_scale_relations (α := α) (q := q) (m := i) hΛ).2
    linarith
  let l : ℤ := ⌈(s + P) / T - 1 / 2⌉
  have hlo : (s + P) / T - 1 / 2 ≤ (l : ℝ) := Int.le_ceil _
  have hhi : (l : ℝ) < (s + P) / T - 1 / 2 + 1 := Int.ceil_lt_add_one _
  have hlo' := (div_le_iff₀ hT).mp (show (s + P) / T ≤ (l : ℝ) + 1 / 2 by linarith)
  have hhi' := (lt_div_iff₀ hT).mp (show (l : ℝ) + 1 / 2 < (s + P + T) / T by
    rw [add_div, div_self hT.ne']; linarith)
  refine ⟨((l : ℝ) + 1 / 2) * T, ⟨l, rfl⟩, hlo', ?_, ?_, ?_⟩
  · linarith
  · linarith
  · exact CycleJointProofs.renewal_boundary_quiet_margin hΛ ζ l
      ⟨by change _ - P ≤ _; linarith, by change _ ≤ _ + P; linarith⟩

/-- The complete pinned clock follows from the explicit small-wait condition on
its common plan. The construction and the scalar solution are not consulted. -/
theorem weak_pinned_clock (plan : WeakEntryGluePlan) (hwait : WeakScheduleWaitStatement plan) :
    WeakPinnedClockStatement plan := by
  intro B A R C x
  have hΛ : 1 ≤ x.D.Λ := by
    rw [x.base_eq]
    exact (by norm_num : 1 ≤ 128).trans x.base128
  let PP := fun i => ocTauPP x.D.α x.D.q x.D.Λ i
  let P := fun i => ocTauP x.D.α x.D.q x.D.Λ i
  let T := PP (x.M + 1)
  let top := x.M + A.Jw
  have hT : 0 < T := Construction.Stream.ocTauPP_pos hΛ
  have hmono : Antitone PP := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp only [PP]
    rw [x.alpha, x.q_eq, x.base_eq]
    simpa only [Nat.add_sub_cancel] using
      Construction.Preservation.FullLift.renewal_time_step_le B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq x.base128
        (m := n + 1)
  let next := fun i s => Classical.choose (pinned_quiet_margin_after (α := x.D.α) (q := x.D.q) (i := i) hΛ x.D.ζ s)
  have hn := fun i s => Classical.choose_spec (pinned_quiet_margin_after (α := x.D.α) (q := x.D.q) (i := i) hΛ x.D.ζ s)
  let times : ℕ → ℝ := Nat.rec (x.a + T) (fun n s => next (top - n) s)
  have hstep : ∀ n, (∃ l : ℤ, times (n + 1) = ((l : ℝ) + 1 / 2) * PP (top - n)) ∧
      times n + P (top - n) ≤ times (n + 1) ∧
      times (n + 1) < times n + PP (top - n) + P (top - n) ∧
      times (n + 1) ≤ times n + 2 * PP (top - n) ∧
      times (n + 1) ∈ ocQuietTimes x.D.α x.D.q x.D.Λ x.D.ζ (top - n) := by
    intro n
    exact hn (top - n) (times n)
  have hbounds : ∀ n, n ≤ A.Jw → x.a ≤ times n ∧ times n ≤ x.a + (1 + 2 * n) * T := by
    intro n
    induction n with
    | zero =>
      intro _
      change x.a ≤ x.a + T ∧ x.a + T ≤ _
      norm_num only [Nat.cast_zero, mul_zero, add_zero, one_mul]
      exact ⟨le_add_of_nonneg_right hT.le, le_rfl⟩
    | succ n ih =>
      intro hnJ
      obtain ⟨hlo, hhi⟩ := ih (by omega)
      have hP : 0 < P (top - n) := Velocity.Jets.ocTauP_pos hΛ
      have hPP : PP (top - n) ≤ T := hmono (by dsimp only [top]; omega)
      have hs := hstep n
      constructor
      · linarith [hs.2.1]
      · push_cast
        linarith [hs.2.2.2.1]
  let tq := fun i => times (top + 1 - i)
  have hstart : tq (x.M + A.Jw + 1) = x.a + T := by
    simp only [tq, top, Nat.sub_self, times, Nat.rec_zero]
  have hout : tq (x.M + 1) = times A.Jw := by
    change times (top + 1 - (x.M + 1)) = times A.Jw
    congr 1
    dsimp only [top]
    omega
  have hwait' : (1 + 2 * (A.Jw : ℝ)) * T ≤ A.τ := by
    simpa only [T, PP, x.alpha, x.q_eq, x.base_eq] using hwait x
  have hJ : (1 : ℝ) ≤ A.Jw := by exact_mod_cast A.Jw_pos
  refine ⟨⟨tq, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hstart]; linarith
  · rw [hout]; exact (hbounds _ le_rfl).2.trans (by linarith)
  · rw [hout]; exact (hbounds _ le_rfl).1
  · rw [hout]
    have ht := (hbounds _ le_rfl).2
    change times A.Jw ≤ x.a + 6 * A.Jw * ocTauPP B.α B.q A.Λ (x.M + 1)
    rw [← x.alpha, ← x.q_eq, ← x.base_eq]
    nlinarith only [ht, hJ, hT]
  · intro i hi hit
    have heq : top - (top - i) = i := by dsimp only [top]; omega
    have hpred : top + 1 - (i + 1) = top - i := by omega
    have hsucc : top + 1 - i = (top - i) + 1 := by dsimp only [top]; omega
    simpa only [tq, hpred, hsucc, heq, PP, P] using hstep (top - i)

/-- The numeric wait condition has a datum-independent terminal threshold. A
common plan selects at least this threshold, before Dm, a, or the scalar datum. -/
theorem weak_schedule_wait_threshold (B : WeakCoefficientBase) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ (J : ℕ) (τ : ℝ),
      0 < τ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        (1 + 2 * (J : ℝ)) * ocTauPP B.α B.q Λ (M + 1) ≤ τ := by
  obtain ⟨Λ₀, hΛ₀, hwait⟩ := Providers.cascade_wait B.α B.s B.hα₀ B.hα₁
    B.hs₀ B.hs₁ B.q B.hq
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ J τ hτ => ?_⟩
  have hJ : 0 < 1 + 2 * (J : ℝ) := by positivity
  obtain ⟨M₀, hM₀⟩ := hwait Λ hΛ (τ / (1 + 2 * (J : ℝ))) (div_pos hτ hJ)
  refine ⟨M₀, fun M hM => ?_⟩
  have hs := hM₀ M hM (M + 1)
  simp only [Nat.Ioc_succ_singleton, Finset.sum_singleton] at hs
  have hΛ1 : 1 ≤ Λ := (by norm_num : 1 ≤ 128).trans (hΛ₀.trans hΛ)
  have hPP : 0 < ocTauPP B.α B.q Λ (M + 1) := Construction.Stream.ocTauPP_pos hΛ1
  have hfast : 0 < ocTau B.α B.q Λ (M + 1) := Construction.Stream.ocTau_pos hΛ1
  have hsmall : ocTauPP B.α B.q Λ (M + 1) ≤ τ / (1 + 2 * (J : ℝ)) := by
    linarith only [hs, hPP, hfast]
  have hm := (le_div_iff₀ hJ).mp hsmall
  simpa only [mul_comm] using hm

/-- The entry schedule with the clock and the finite chain discharged. The only stage-dependent
hypothesis is the explicit full-fiber local model statement. -/
theorem weak_entry_schedule_of_wait_and_models (plan : WeakEntryGluePlan)
    (hwait : WeakScheduleWaitStatement plan) (hmodels : WeakFullReadoutModelsStatement plan) :
    WeakEntryScheduleStatement plan :=
  weak_entry_schedule_of_ingredients plan (weak_pinned_clock plan hwait)
    (weak_full_readout_lifts_of_models plan hmodels) (weak_readout_chain plan)

end AVRegularity.WeakEntryProofs.Assembly
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.WeakEntryProofs

/-! Positive endpoint smoothing for arbitrary L² data. Fourier cutoffs are
used only to pass the already proved scalar estimate to the complete Sobolev
carrier; existence, uniqueness and every weak equation remain native. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The explicit positive scalar price on a strict window. -/
def weakScalarEndpointPrice (ν ρ a b : ℝ) (K : ℕ) : ℝ :=
  Real.sqrt (2 * (4 + 8 * ρ ^ 2 * (K + 1) / (ν * (b - a))) ^ K)

/-- Every L² datum has a positive Sobolev endpoint representative with the
same scalar price as the regular-data estimate. -/
theorem weak_scalar_torus_endpoint_lift {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {K Q : ℕ} (hd : WeakScalarTorusDrift ν ρ a b v Q) (hK : K ≤ Q) (hab : a < b)
    (f : TorusHk 0 E) :
    ∃ Z : TorusHk K E,
      truncateTorusHk (Nat.zero_le K) Z = weakScalarTorusForward hd 0 a b f ∧
      Real.sqrt (factorialNormSq ρ Z.val) ≤ weakScalarEndpointPrice ν ρ a b K * ‖f‖ := by
  let : TopologicalSpace.SeparableSpace (TorusHk K E) := torusHkSeparableSpace K
  let C := weakScalarEndpointPrice ν ρ a b K
  let initial (N : ℕ) : TorusHk K E := smoothFourierLift (K := 0) (L := K) N f
  let U (N : ℕ) := weakScalarTorusTrajectory hK hd hab.le (initial N)
  let z (N : ℕ) : TorusHk K E := (U N).value b
  have hnu : 0 < ν := hd.nu_pos
  have htime : 0 < b - a := sub_pos.mpr hab
  have hinit (N : ℕ) : (U N).value a = initial N := (U N).solution.2.2.2.1 0
  have hproject (N : ℕ) : truncateTorusHk (Nat.zero_le K) (initial N) = galerkinProj N f :=
    smoothFourierLift_truncate_eq (Nat.zero_le K) N f
  have hcost (N : ℕ) : Real.sqrt (factorialNormSq ρ (z N).val) ≤ C * ‖f‖ := by
    have hh := weak_scalar_torus_window_smoothing K
      (hd.restrict (Set.Icc_subset_Icc le_rfl le_rfl) hK) hab (U N).solution
    rw [hinit N, hproject N, CycleJointProofs.factorialNormSq_order_zero_measure] at hh
    have hr := Real.sqrt_le_sqrt hh
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] at hr
    exact hr.trans (mul_le_mul_of_nonneg_left (galerkinProj_norm_le N f) (Real.sqrt_nonneg _))
  have hm : 0 < Real.sqrt (factorialWeightMin ρ K) :=
    Real.sqrt_pos.mpr (factorialWeightMin_pos ρ hd.radius_pos)
  have hbound (N : ℕ) : ‖z N‖ ≤ (C * ‖f‖) / Real.sqrt (factorialWeightMin ρ K) :=
    (jetNorm_le_factorialRoot ρ hd.radius_pos (z N).val).trans
      (div_le_div_of_nonneg_right (hcost N) hm.le)
  obtain ⟨Z, σ, hσ, hlim⟩ := exists_strictMono_tendsto_clm_of_norm_le z
    ((C * ‖f‖) / Real.sqrt (factorialWeightMin ρ K)) hbound
  have hz (N : ℕ) : truncateTorusHk (Nat.zero_le K) (z N) =
      weakScalarTorusForward hd 0 a b (galerkinProj N f) := by
    have hh := weak_scalar_torus_forward_eq hd (Nat.zero_le Q) le_rfl hab.le le_rfl
      (weak_scalar_torus_solution_truncate (Nat.zero_le K) (U N).solution)
    rw [hproject N] at hh
    exact hh.symm
  have hzero : Tendsto (fun N => truncateTorusHk (Nat.zero_le K) (z N)) atTop
      (𝓝 (weakScalarTorusForward hd 0 a b f)) := by
    simpa only [hz, Function.comp_def] using ((weakScalarTorusForward hd 0 a b).continuous.tendsto f).comp
      (galerkinProj_tendsto f)
  refine ⟨Z, ?_, ?_⟩
  · apply ext_inner_left ℝ
    intro ψ
    have hh := hlim ((innerSL ℝ ψ).comp (truncateTorusHk (Nat.zero_le K)))
    have hh' := ((continuous_const.inner continuous_id :
      Continuous (fun y : TorusHk 0 E => inner ℝ ψ y)).tendsto _).comp
        (hzero.comp hσ.tendsto_atTop)
    exact tendsto_nhds_unique hh hh'
  · let L : TorusHk K E →L[ℝ] JetL2 (volume.restrict AVenhance.unitCube) K E :=
      (factorialWeightedJetCLM ρ K).comp (torusHkGraph (E := E) K).toSubmodule.subtypeL
    have hL (N : ℕ) : ‖L (z (σ N))‖ ≤ C * ‖f‖ := by
      rw [show L (z (σ N)) = factorialWeightedJet ρ (z (σ N)).val from rfl,
        factorialWeightedJet_norm]
      exact hcost (σ N)
    have hh := norm_le_of_tendsto_clm hL (fun ell => hlim (ell.comp L))
    change ‖factorialWeightedJet ρ Z.val‖ ≤ C * ‖f‖ at hh
    rw [factorialWeightedJet_norm] at hh
    exact hh

/-- A positive endpoint lift of the actual order-zero evolution. The bound
is in the factorial norm, and the value projection retains the native solution. -/
structure WeakScalarEndpointOperator (ν ρ a b : ℝ) (K : ℕ)
    (L : TorusHk 0 E →L[ℝ] TorusHk 0 E) where
  apply : TorusHk 0 E →L[ℝ] TorusHk K E
  value : ∀ f, truncateTorusHk (Nat.zero_le K) (apply f) = L f
  bound : ∀ f, Real.sqrt (factorialNormSq ρ (apply f).val) ≤
    weakScalarEndpointPrice ν ρ a b K * ‖f‖

/-- The endpoint representatives form one bounded linear operator, since the
order-zero value embedding is injective and the native evolution is linear. -/
theorem weak_scalar_torus_endpoint_operator {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {K Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (hK : K ≤ Q) (hab : a < b) :
    Nonempty (WeakScalarEndpointOperator (E := E) ν ρ a b K
      (weakScalarTorusForward hd 0 a b)) := by
  let F (f : TorusHk 0 E) : TorusHk K E := (weak_scalar_torus_endpoint_lift hd hK hab f).choose
  have hF (f : TorusHk 0 E) :
      truncateTorusHk (Nat.zero_le K) (F f) = weakScalarTorusForward hd 0 a b f ∧
      Real.sqrt (factorialNormSq ρ (F f).val) ≤ weakScalarEndpointPrice ν ρ a b K * ‖f‖ :=
    (weak_scalar_torus_endpoint_lift hd hK hab f).choose_spec
  have hinj : Function.Injective (truncateTorusHk (E := E) (Nat.zero_le K)) := by
    intro u w he
    apply TorusHk.ext_value
    exact congrArg (fun y : TorusHk 0 E => torusHkValueCLM y) he
  let L : TorusHk 0 E →ₗ[ℝ] TorusHk K E :=
    { toFun := F
      map_add' := fun f g => by
        apply hinj
        rw [(hF (f + g)).1, map_add,
          (truncateTorusHk (E := E) (Nat.zero_le K)).map_add, (hF f).1, (hF g).1]
      map_smul' := fun r f => by
        apply hinj
        rw [RingHom.id_apply, (hF (r • f)).1,
          (truncateTorusHk (E := E) (Nat.zero_le K)).map_smul, (hF f).1, map_smul] }
  have hm : 0 < Real.sqrt (factorialWeightMin ρ K) :=
    Real.sqrt_pos.mpr (factorialWeightMin_pos ρ hd.radius_pos)
  have hn (f : TorusHk 0 E) : ‖L f‖ ≤
      (weakScalarEndpointPrice ν ρ a b K / Real.sqrt (factorialWeightMin ρ K)) * ‖f‖ := by
    calc
      ‖L f‖ ≤ Real.sqrt (factorialNormSq ρ (F f).val) /
          Real.sqrt (factorialWeightMin ρ K) := jetNorm_le_factorialRoot ρ hd.radius_pos _
      _ ≤ (weakScalarEndpointPrice ν ρ a b K * ‖f‖) /
          Real.sqrt (factorialWeightMin ρ K) := div_le_div_of_nonneg_right (hF f).2 hm.le
      _ = _ := by ring
  exact ⟨{
    apply := L.mkContinuous _ hn
    value := fun f => (hF f).1
    bound := fun f => (hF f).2 }⟩

/-- Positive endpoint lifting agrees with every supplied native regular
trajectory, so it can be inserted into a path without changing its value. -/
theorem weak_scalar_torus_endpoint_operator_native {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {K Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (hab : a ≤ b)
    (L : WeakScalarEndpointOperator (E := E) ν ρ a b K (weakScalarTorusForward hd 0 a b))
    {f : TorusHk K E} {u : ℝ → TorusHk K E} {w : ℝ → TorusHk (K + 1) E}
    (hs : WeakScalarTorusSolution ν a b v K f u w) :
    L.apply (truncateTorusHk (Nat.zero_le K) f) = u b := by
  have he := weak_scalar_torus_forward_eq hd (Nat.zero_le Q) le_rfl hab le_rfl
    (weak_scalar_torus_solution_truncate (Nat.zero_le K) hs)
  have hvalue : truncateTorusHk (Nat.zero_le K)
      (L.apply (truncateTorusHk (Nat.zero_le K) f)) =
      truncateTorusHk (Nat.zero_le K) (u b) := (L.value _).trans he
  apply TorusHk.ext_value
  exact congrArg (fun y : TorusHk 0 E => torusHkValueCLM y) hvalue

/-- A finite negative-order state, expressed as its actual continuous linear
action on positive-order Sobolev tests. -/
def WeakScalarFunctionalBound (ρ : ℝ) (P : ℕ) (ell : TorusHk P E →L[ℝ] ℝ)
    (N : ℝ) : Prop :=
  ∀ φ, |ell φ| ≤ N * Real.sqrt (factorialNormSq ρ φ.val)

/-- A bounded negative-order functional has a positive Sobolev representative
after a strict scalar gap. The representation agrees with every native
backward test, and uses precisely the two proved positive smoothing prices. -/
theorem weak_scalar_functional_endpoint {ν ρ a b c : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {P K Q : ℕ}
    (hd : WeakScalarTorusDrift ν ρ a b v Q) (hP : P ≤ Q) (hK : K ≤ Q)
    (hac : a < c) (hcb : c < b) (ell : TorusHk P E →L[ℝ] ℝ)
    (N : ℝ) (hN : 0 ≤ N) (hbound : WeakScalarFunctionalBound ρ P ell N) :
    ∃ Z : TorusHk K E,
      Real.sqrt (factorialNormSq ρ Z.val) ≤
        N * weakScalarEndpointPrice ν ρ a c P * weakScalarEndpointPrice ν ρ c b K ∧
      ∀ (φ : TorusHk P E) (z : ℝ → TorusHk P E) (zw : ℝ → TorusHk (P + 1) E),
        WeakScalarTorusSolution ν (-b) (-a) (fun t x => -v (-t) x) P φ z zw →
        inner ℝ (truncateTorusHk (Nat.zero_le K) Z)
          (truncateTorusHk (Nat.zero_le P) φ) = ell (z (-a)) := by
  let hd₁ := (hd.restrict (Set.Icc_subset_Icc le_rfl hcb.le) le_rfl).reflected
  let hd₂ := hd.restrict (Set.Icc_subset_Icc hac.le le_rfl) le_rfl
  obtain ⟨B₁⟩ := weak_scalar_torus_endpoint_operator (E := E) hd₁ hP (neg_lt_neg hac)
  obtain ⟨B₂⟩ := weak_scalar_torus_endpoint_operator (E := E) hd₂ hK hcb
  let F : TorusHk 0 E →L[ℝ] ℝ := ell.comp B₁.apply
  let Y : TorusHk 0 E := (InnerProductSpace.toDual ℝ (TorusHk 0 E)).symm F
  have hY (ψ : TorusHk 0 E) : inner ℝ Y ψ = ell (B₁.apply ψ) :=
    InnerProductSpace.toDual_symm_apply
  have hprice : weakScalarEndpointPrice ν ρ (-c) (-a) P =
      weakScalarEndpointPrice ν ρ a c P := by
    simp only [weakScalarEndpointPrice, neg_sub_neg]
  have hnorm : ‖Y‖ ≤ N * weakScalarEndpointPrice ν ρ a c P := by
    rw [show ‖Y‖ = ‖F‖ from (InnerProductSpace.toDual ℝ (TorusHk 0 E)).symm.norm_map F]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hN (Real.sqrt_nonneg _))
    intro ψ
    change ‖ell (B₁.apply ψ)‖ ≤ _
    rw [Real.norm_eq_abs]
    calc
      _ ≤ N * Real.sqrt (factorialNormSq ρ (B₁.apply ψ).val) := hbound _
      _ ≤ N * (weakScalarEndpointPrice ν ρ (-c) (-a) P * ‖ψ‖) :=
        mul_le_mul_of_nonneg_left (B₁.bound ψ) hN
      _ = _ := by
        rw [hprice]
        exact (mul_assoc N (weakScalarEndpointPrice ν ρ a c P) ‖ψ‖).symm
  refine ⟨B₂.apply Y, ?_, ?_⟩
  · exact (B₂.bound Y).trans (by
      calc
        _ ≤ weakScalarEndpointPrice ν ρ c b K *
            (N * weakScalarEndpointPrice ν ρ a c P) :=
          mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
        _ = _ := by ring)
  · intro φ z zw hz
    have hz₁ := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_right
      (neg_le_neg hcb.le) (neg_le_neg hac.le) hz
    have hz₂ := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left
      (neg_le_neg hac.le) hz
    have hB₁ : B₁.apply (truncateTorusHk (Nat.zero_le P) (z (-c))) = z (-a) :=
      weak_scalar_torus_endpoint_operator_native hd₁ (neg_le_neg hac.le) B₁ hz₁
    obtain ⟨u, w, hu, he⟩ := weak_scalar_torus_forward_native hd₂ (Nat.zero_le Q)
      c b le_rfl hcb.le le_rfl Y
    have hp := weak_scalar_adjoint_pair P hcb.le
      (hd₂.restrict (Set.Icc_subset_Icc le_rfl le_rfl) hP) hu hz₂
    have hinitu : u c = Y := hu.2.2.2.1 0
    have hinitz : z (-b) = φ := hz.2.2.2.1 0
    rw [hinitu, hinitz] at hp
    rw [B₂.value Y, he, hp, hY, hB₁]

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Pointwise chronological words at finite signed reserves. The negative
state is its continuous action on positive tests. A positive representative
is inserted only across a long scalar gap; sources after it use the actual
primal map paired with the actual formal adjoint. -/

variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- Insertion times, listed from the latest insertion back to the earliest. -/
def WeakQuietInsertionTimes : ℕ → Type
  | 0 => PUnit
  | n + 1 => ℝ × WeakQuietInsertionTimes n

/-- The recursive closed chronological simplex. Boundaries are retained;
the long-gap estimate remains valid even when some scalar gaps are zero. -/
def WeakQuietTimesOrdered : {n : ℕ} → ℝ → ℝ → WeakQuietInsertionTimes n → Prop
  | 0, a, b, _ => a ≤ b
  | _ + 1, a, b, t => a ≤ t.1 ∧ t.1 ≤ b ∧ WeakQuietTimesOrdered a t.1 t.2

/-- At least one of the scalar gaps has the stated length. -/
def WeakQuietHasLongGap (δ : ℝ) : {n : ℕ} → ℝ → ℝ → WeakQuietInsertionTimes n → Prop
  | 0, a, b, _ => δ ≤ b - a
  | _ + 1, a, b, t => δ ≤ b - t.1 ∨ WeakQuietHasLongGap δ a t.1 t.2

/-- The elementary longest-gap allocation, including coincident source times. -/
theorem weak_quiet_has_long_gap {n : ℕ} {a b δ : ℝ}
    (t : WeakQuietInsertionTimes n) (hlen : (n + 1 : ℕ) * δ ≤ b - a) :
    WeakQuietHasLongGap δ a b t := by
  have hshort : ∀ n (t : WeakQuietInsertionTimes n) (a b : ℝ),
      ¬ WeakQuietHasLongGap δ a b t → b - a < (n + 1 : ℕ) * δ := by
    intro n
    induction n with
    | zero =>
      intro _ a b h
      change ¬ δ ≤ b - a at h
      simpa only [Nat.reduceAdd, Nat.cast_one, one_mul] using lt_of_not_ge h
    | succ n ih =>
      intro t a b h
      have hh : ¬ δ ≤ b - t.1 ∧ ¬ WeakQuietHasLongGap δ a t.1 t.2 := not_or.mp h
      have hp := ih t.2 a t.1 hh.2
      have ht := lt_of_not_ge hh.1
      push_cast
      push_cast at hp
      linarith only [hp, ht]
  exact Classical.byContradiction fun h => (not_lt_of_ge hlen) (hshort n t a b h)

/-- The native scalar drift at the exact finite path cap. -/
abbrev WeakQuietScalarDrift (x : WeakQuietExpansionCase plan prices) :=
  WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
    (streamVel (x.c.D.Φ (x.i - 1))) x.cap

/-- The physical rate of one aggregate insertion, retaining its b-entry. -/
def weakQuietInsertionRate (x : WeakQuietExpansionCase plan prices) (v u : x.Vertex) : ℝ :=
  x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice * x.b v u

theorem weak_quiet_insertion_rate_nonneg (x : WeakQuietExpansionCase plan prices)
    (hd : WeakQuietScalarDrift x) (v u : x.Vertex) : 0 ≤ weakQuietInsertionRate x v u := by
  have hr : 0 < plan.radius x.R := by
    have hp := hd.radius_pos
    change 0 < plan.radius x.R * x.c.D.eps (x.i - 1) at hp
    exact (mul_pos_iff_of_pos_right x.bounds.1).mp hp
  exact mul_nonneg (mul_nonneg (div_nonneg hd.nu_pos.le (sq_nonneg _))
    (pow_nonneg (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hr.le) _))
    (x.bounds.2.2.2.2.1 v u)

/-- The propagation/source price except for the single smoothing gap. -/
def weakQuietInstantCost (x : WeakQuietExpansionCase plan prices) :
    (n : ℕ) → (v u : x.Vertex) → WeakQuietWalk x.Vertex n v u → ℝ
  | 0, _, _, _ => 1
  | n + 1, v, u, π => Real.sqrt 2 * weakQuietInsertionRate x v π.1 *
      weakQuietInstantCost x n π.1 u π.2

theorem weak_quiet_instant_cost_nonneg (x : WeakQuietExpansionCase plan prices)
    (hd : WeakQuietScalarDrift x) (n : ℕ) (v u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n v u) : 0 ≤ weakQuietInstantCost x n v u π := by
  induction n generalizing v with
  | zero => exact zero_le_one
  | succ n ih =>
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (weak_quiet_insertion_rate_nonneg x hd v π.1))
      (ih π.1 π.2)

/-- The literal pointwise dual word at any lower test reserve. -/
def weakQuietInstantOperator (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x) (P : ℕ) :
    (n : ℕ) → n * x.order + P ≤ x.cap → (v u : x.Vertex) →
      WeakQuietWalk x.Vertex n v u → WeakQuietInsertionTimes n → ℝ → ℝ →
      TorusHk (n * x.order + P) ℝ →L[ℝ] TorusHk P ℝ
  | 0, _, _, _, _, _, a, b =>
      (weakQuietBackwardOperator x hd P a b).comp (truncateTorusHk (by omega))
  | n + 1, hn, v, u, π, t, a, b =>
      have hm : (n + 1) * x.order = n * x.order + x.order := Nat.succ_mul n x.order
      (weakQuietInstantOperator x S hd P n (by omega) π.1 u π.2 t.2 a t.1).comp
        ((S.apply v π.1 (n * x.order + P) (by omega) t.1).comp
          ((truncateTorusHk (by rw [Nat.succ_mul]; omega)).comp
            (weakQuietBackwardOperator x hd ((n + 1) * x.order + P) t.1 b)))

/-- Each native pointwise word has its negative-order bound before any
smoothing is allocated. This bound is uniform in all insertion times. -/
theorem weak_quiet_instant_operator_bound (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x) (P n : ℕ)
    (hn : n * x.order + P ≤ x.cap) (v u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n v u) (t : WeakQuietInsertionTimes n)
    (a b : ℝ) (ha : x.left ≤ a) (hb : b ≤ x.right)
    (ht : WeakQuietTimesOrdered a b t) (φ : TorusHk (n * x.order + P) ℝ) :
    Real.sqrt (factorialNormSq x.radius (weakQuietInstantOperator x S hd P n hn v u π t a b φ).val) ≤
      (Real.sqrt 2 * weakQuietInstantCost x n v u π) *
        Real.sqrt (factorialNormSq x.radius φ.val) := by
  induction n generalizing v b with
  | zero =>
    have hh := weak_quiet_backward_factorial_bound x hd (weakQuietBackwardEvolution x hd)
      P (by simpa using hn) a b ha ht hb (truncateTorusHk (by omega) φ)
    exact hh.trans (by
      simpa only [weakQuietInstantCost, mul_one] using
        mul_le_mul_of_nonneg_left (sqrt_fNSq_torus_truncate_le x.radius (by omega) φ)
          (Real.sqrt_nonneg 2))
  | succ n ih =>
    change (Σ w : x.Vertex, WeakQuietWalk x.Vertex n w u) at π
    change ℝ × WeakQuietInsertionTimes n at t
    have hm : (n + 1) * x.order = n * x.order + x.order := Nat.succ_mul n x.order
    have hmem : t.1 ∈ Set.Icc x.left x.right := ⟨ha.trans ht.1, ht.2.1.trans hb⟩
    let ψ := weakQuietBackwardOperator x hd ((n + 1) * x.order + P) t.1 b φ
    let χ : TorusHk ((n * x.order + P) + x.order) ℝ := truncateTorusHk (by omega) ψ
    have hψ := weak_quiet_backward_factorial_bound x hd (weakQuietBackwardEvolution x hd)
      ((n + 1) * x.order + P) hn t.1 b hmem.1 ht.2.1 hb φ
    have hχ := (sqrt_fNSq_torus_truncate_le x.radius
      (show (n * x.order + P) + x.order ≤ (n + 1) * x.order + P by omega) ψ).trans hψ
    obtain ⟨C, Adj, he, hAdj⟩ := S.adjoint v π.1 t.1 hmem
    have hS : Real.sqrt (factorialNormSq x.radius
        (S.apply v π.1 (n * x.order + P) (by omega) t.1 χ).val) ≤
        weakQuietInsertionRate x v π.1 * Real.sqrt (factorialNormSq x.radius χ.val) := by
      rw [he]
      exact hAdj _ _ χ
    have hprev := ih (by omega) π.1 π.2 t.2 t.1 hmem.2 ht.2.2
      (S.apply v π.1 (n * x.order + P) (by omega) t.1 χ)
    change Real.sqrt (factorialNormSq x.radius
      (weakQuietInstantOperator x S hd P n _ π.1 u π.2 t.2 a t.1
        (S.apply v π.1 (n * x.order + P) _ t.1 χ)).val) ≤ _
    calc
      _ ≤ (Real.sqrt 2 * weakQuietInstantCost x n π.1 u π.2) *
          (weakQuietInsertionRate x v π.1 *
            (Real.sqrt 2 * Real.sqrt (factorialNormSq x.radius φ.val))) :=
        hprev.trans (mul_le_mul_of_nonneg_left
          (hS.trans (mul_le_mul_of_nonneg_left hχ
            (weak_quiet_insertion_rate_nonneg x hd v π.1)))
          (mul_nonneg (Real.sqrt_nonneg _) (weak_quiet_instant_cost_nonneg x hd n π.1 u π.2)))
      _ = _ := by simp only [weakQuietInstantCost]; ring

/-- Pure scalar algebra needed to charge a long gap by one common price.
This condition contains only the explicit scalar endpoint prices. -/
def WeakQuietGapPriceBound (x : WeakQuietExpansionCase plan prices) (δ G : ℝ) : Prop :=
  ∀ P K : ℕ, P + K ≤ x.cap → ∀ a b : ℝ,
    x.left ≤ a → a < b → b ≤ x.right → δ ≤ b - a →
    weakScalarEndpointPrice (x.c.D.κ x.c.M) x.radius a ((a + b) / 2) P *
      weakScalarEndpointPrice (x.c.D.κ x.c.M) x.radius ((a + b) / 2) b K ≤ G

private theorem weakQuietFunctional_comp {P Q : ℕ} {ρ N C : ℝ}
    (ell : TorusHk P ℝ →L[ℝ] ℝ) (T : TorusHk Q ℝ →L[ℝ] TorusHk P ℝ)
    (hN : 0 ≤ N) (he : WeakScalarFunctionalBound ρ P ell N)
    (hT : ∀ φ, Real.sqrt (factorialNormSq ρ (T φ).val) ≤
      C * Real.sqrt (factorialNormSq ρ φ.val)) :
    WeakScalarFunctionalBound ρ Q (ell.comp T) (N * C) := by
  intro φ
  exact (he (T φ)).trans ((mul_le_mul_of_nonneg_left (hT φ) hN).trans_eq
    (mul_assoc _ _ _).symm)

/-- Smoothing an arbitrary finite negative functional across a sufficiently
long gap, with the arithmetic price separated from the native analytic proof. -/
theorem weak_quiet_functional_long_gap (x : WeakQuietExpansionCase plan prices)
    (hd : WeakQuietScalarDrift x) {P K : ℕ} (hPK : P + K ≤ x.cap)
    {a b δ G N : ℝ} (ha : x.left ≤ a) (hab : a < b) (hb : b ≤ x.right)
    (hlen : δ ≤ b - a) (hG : WeakQuietGapPriceBound x δ G)
    (ell : TorusHk P ℝ →L[ℝ] ℝ) (hN : 0 ≤ N)
    (he : WeakScalarFunctionalBound x.radius P ell N) :
    ∃ Z : TorusHk K ℝ,
      Real.sqrt (factorialNormSq x.radius Z.val) ≤ N * G ∧
      ∀ φ : TorusHk P ℝ,
        inner ℝ (truncateTorusHk (Nat.zero_le K) Z)
          (truncateTorusHk (Nat.zero_le P) φ) =
        ell (weakQuietBackwardOperator x hd P a b φ) := by
  have hac : a < (a + b) / 2 := by linarith only [hab]
  have hcb : (a + b) / 2 < b := by linarith only [hab]
  obtain ⟨Z, hZ, hp⟩ := weak_scalar_functional_endpoint
    (hd.restrict (Set.Icc_subset_Icc ha hb) le_rfl) (by omega : P ≤ x.cap)
    (by omega : K ≤ x.cap) hac hcb ell N hN he
  refine ⟨Z, hZ.trans ?_, ?_⟩
  · exact (le_of_eq (mul_assoc _ _ _)).trans
      (mul_le_mul_of_nonneg_left (hG P K hPK a b ha hab hb hlen) hN)
  · intro φ
    obtain ⟨z, zw, hz, hez⟩ := (weakQuietBackwardEvolution x hd).native P (by omega)
      a b ha hab.le hb φ
    rw [show weakQuietBackwardOperator x hd P a b φ = z (-a) from hez]
    exact hp φ z zw hz

/-- Native duality for a positive source followed by a scalar gap. This
separate lemma keeps the order casts and the native PDE pairing out of the
finite word induction. -/
theorem weak_quiet_positive_source_pair (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x)
    (K Q L : ℕ) (hK : K + x.order ≤ x.cap) (hQ : Q + x.order ≤ x.cap)
    (hQL : Q + x.order ≤ L) (hL : L ≤ x.cap)
    (v u : x.Vertex) (a b : ℝ) (ha : x.left ≤ a) (hab : a ≤ b) (hb : b ≤ x.right)
    (Z : TorusHk (K + x.order) ℝ)
    {z : ℝ → TorusHk K ℝ} {zw : ℝ → TorusHk (K + 1) ℝ}
    (hz : WeakScalarTorusSolution (x.c.D.κ x.c.M) a b
      (streamVel (x.c.D.Φ (x.i - 1))) K (S.primal v u K hK a Z) z zw)
    (φ : TorusHk L ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le K) (z b))
      (truncateTorusHk (Nat.zero_le L) φ) =
    inner ℝ (truncateTorusHk (Nat.zero_le (K + x.order)) Z)
      (truncateTorusHk (Nat.zero_le Q)
        (S.apply v u Q hQ a (truncateTorusHk hQL (weakQuietBackwardOperator x hd L a b φ)))) := by
  obtain ⟨y, yw, hy, hey⟩ := (weakQuietBackwardEvolution x hd).native L hL a b ha hab hb φ
  have hp := weak_scalar_adjoint_pair L hab
    (hd.restrict (Set.Icc_subset_Icc ha hb) hL)
    (weak_scalar_torus_solution_truncate (Nat.zero_le K) hz) hy
  have hiy : y (-b) = φ := hy.2.2.2.1 0
  have hiz : z a = S.primal v u K hK a Z := hz.2.2.2.1 0
  rw [hiy, show truncateTorusHk (Nat.zero_le K) (z a) =
    truncateTorusHk (Nat.zero_le K) (S.primal v u K hK a Z) from congrArg _ hiz,
    ← hey] at hp
  have ht : truncateTorusHk (Nat.zero_le (Q + x.order))
      (truncateTorusHk hQL (weakQuietBackwardOperator x hd L a b φ)) =
      truncateTorusHk (Nat.zero_le L) (weakQuietBackwardOperator x hd L a b φ) := rfl
  dsimp only [weakQuietBackwardEvolution] at hp
  rw [← ht] at hp
  exact hp.trans (S.paired v u K Q hK hQ a ⟨ha, hab.trans hb⟩ Z _)

/-- Longest-gap representation of a pointwise source word. The initial
negative reserve and the final positive reserve use the same fixed cap.
The sources before the long gap are actions on tests; those after it are
native primal maps, identified by the pairing `S.paired` of the insertion data. -/
theorem weak_quiet_instant_word_represented (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x)
    {δ G : ℝ} (hδ : 0 < δ) (hG : WeakQuietGapPriceBound x δ G)
    (n P K : ℕ) (hcap : P + K + n * x.order ≤ x.cap)
    (v u : x.Vertex) (π : WeakQuietWalk x.Vertex n v u)
    (t : WeakQuietInsertionTimes n) (a b : ℝ)
    (ha : x.left ≤ a) (hb : b ≤ x.right) (ht : WeakQuietTimesOrdered a b t)
    (hlong : WeakQuietHasLongGap δ a b t)
    (ell : TorusHk P ℝ →L[ℝ] ℝ) {N : ℝ} (hN : 0 ≤ N)
    (he : WeakScalarFunctionalBound x.radius P ell N) :
    ∃ Z : TorusHk K ℝ,
      Real.sqrt (factorialNormSq x.radius Z.val) ≤ N * G * weakQuietInstantCost x n v u π ∧
      ∀ φ : TorusHk (n * x.order + P) ℝ,
        inner ℝ (truncateTorusHk (Nat.zero_le K) Z)
          (truncateTorusHk (Nat.zero_le (n * x.order + P)) φ) =
        ell (weakQuietInstantOperator x S hd P n (by omega) v u π t a b φ) := by
  induction n generalizing K v b with
  | zero =>
    change δ ≤ b - a at hlong
    have hab : a < b := by linarith only [hlong, hδ]
    obtain ⟨Z, hZ, hp⟩ := weak_quiet_functional_long_gap x hd (P := P) (K := K) (by simpa using hcap)
      ha hab hb hlong hG ell hN he
    refine ⟨Z, by simpa only [weakQuietInstantCost, mul_one] using hZ, ?_⟩
    intro φ
    exact hp (truncateTorusHk (by omega) φ)
  | succ n ih =>
    change (Σ w : x.Vertex, WeakQuietWalk x.Vertex n w u) at π
    change ℝ × WeakQuietInsertionTimes n at t
    have hm : (n + 1) * x.order = n * x.order + x.order := Nat.succ_mul n x.order
    have hmem : t.1 ∈ Set.Icc x.left x.right := ⟨ha.trans ht.1, ht.2.1.trans hb⟩
    let Q := n * x.order + P
    let V := weakQuietInstantOperator x S hd P n (by omega) π.1 u π.2 t.2 a t.1
    let J : TorusHk ((n + 1) * x.order + P) ℝ →L[ℝ] TorusHk Q ℝ :=
      (S.apply v π.1 Q (by dsimp [Q]; omega) t.1).comp (truncateTorusHk (by dsimp [Q]; omega))
    rcases hlong with hlast | hprefix
    · let F := (ell.comp V).comp J
      have hV := weakQuietFunctional_comp ell V hN he (fun φ =>
        weak_quiet_instant_operator_bound x S hd P n _ π.1 u π.2 t.2 a t.1 ha hmem.2 ht.2.2 φ)
      obtain ⟨C, Adj, hAdj, hAb⟩ := S.adjoint v π.1 t.1 hmem
      have hJ (φ : TorusHk ((n + 1) * x.order + P) ℝ) :
          Real.sqrt (factorialNormSq x.radius (J φ).val) ≤
            weakQuietInsertionRate x v π.1 * Real.sqrt (factorialNormSq x.radius φ.val) := by
        change Real.sqrt (factorialNormSq x.radius
          (S.apply v π.1 Q _ t.1 (truncateTorusHk _ φ)).val) ≤ _
        rw [hAdj]
        exact (hAb _ _ _).trans (mul_le_mul_of_nonneg_left
          (sqrt_fNSq_torus_truncate_le x.radius _ φ) (weak_quiet_insertion_rate_nonneg x hd v π.1))
      have hF := weakQuietFunctional_comp (ell.comp V) J
        (mul_nonneg hN (mul_nonneg (Real.sqrt_nonneg _)
          (weak_quiet_instant_cost_nonneg x hd n π.1 u π.2))) hV hJ
      have hab : t.1 < b := by linarith only [hlast, hδ]
      obtain ⟨Z, hZ, hp⟩ := weak_quiet_functional_long_gap x hd (P := (n + 1) * x.order + P) (K := K) (by omega)
        hmem.1 hab hb hlast hG F
        (mul_nonneg (mul_nonneg hN (mul_nonneg (Real.sqrt_nonneg _)
          (weak_quiet_instant_cost_nonneg x hd n π.1 u π.2)))
          (weak_quiet_insertion_rate_nonneg x hd v π.1)) hF
      refine ⟨Z, ?_, hp⟩
      calc
        _ ≤ _ := hZ
        _ = _ := by simp only [weakQuietInstantCost]; ring
    · obtain ⟨Z, hZ, hp⟩ := ih (K + x.order) (by omega) π.1 π.2 t.2 t.1 hmem.2 ht.2.2 hprefix
      let Zs := S.primal v π.1 K (by omega) t.1 Z
      obtain ⟨z, zw, hz, _⟩ := weak_scalar_torus_forward_native hd (by omega : K ≤ x.cap)
        t.1 b hmem.1 ht.2.1 hb Zs
      have hprop := weak_scalar_torus_factorial_bound (by omega : K ≤ x.cap)
        (hd.restrict (Set.Icc_subset_Icc hmem.1 hb) le_rfl) hz ⟨ht.2.1, le_rfl⟩
      have hprop' := Real.sqrt_le_sqrt hprop
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hprop'
      have hsource := S.primal_bound v π.1 K (by omega) t.1 hmem Z
      refine ⟨z b, ?_, ?_⟩
      · calc
          _ ≤ Real.sqrt 2 * (weakQuietInsertionRate x v π.1 *
              (N * G * weakQuietInstantCost x n π.1 u π.2)) :=
            hprop'.trans (mul_le_mul_of_nonneg_left (hsource.trans
              (mul_le_mul_of_nonneg_left hZ (weak_quiet_insertion_rate_nonneg x hd v π.1)))
              (Real.sqrt_nonneg _))
          _ = _ := by simp only [weakQuietInstantCost]; ring
      · intro φ
        have hpair := weak_quiet_positive_source_pair x S hd K Q
          ((n + 1) * x.order + P) (by omega) (by dsimp [Q]; omega)
          (by dsimp [Q]; omega) (by omega) v π.1 t.1 b hmem.1 ht.2.1 hb Z hz φ
        exact hpair.trans (hp (S.apply v π.1 Q (by dsimp [Q]; omega) t.1
          (truncateTorusHk (by dsimp [Q]; omega)
            (weakQuietBackwardOperator x hd ((n + 1) * x.order + P) t.1 b φ))))

end AVRegularity.WeakEntryProofs.Assembly
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Sum the individual forced-row energy bounds after taking each row's own
supremum. Nonnegative extended-real costs allow infinite forcing integrals. -/

/-- Positive column budgets sum forced row energies without a component-count
factor or any change in the order of the time suprema. -/
theorem comparison_column_sum : ComparisonColumnSumStatement := by
  classical
  intro ι _ K q C hK hcol
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun v _ => hK v u)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hcol u)) le_rfl

end AVRegularity.WeakEntryProofs.Assembly
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Native Piola lowering of phase-free parent-scale jets. The finite source
cap, rather than the ambient cap of a stage, controls every constant. -/

open AVRegularity.Construction.Preservation.FullLift AVRegularity.CycleJointProofs

/-- An ordinary parent-scale sampled flux budget gives a uniform native array
price. The auxiliary record length is the finer wavelength itself; hence the
record ledger is just the number of derivative words, bounded by the finite cap. -/
theorem weak_quiet_parent_transport_price
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N Dγ cap Kmax n dout : ℕ)
    (hD : Dγ ≤ cap) (hkn : n ≤ Kmax) (hdout : 2 ≤ dout) (hout : dout ≤ cap)
    (C E ν e Cs θ : ℝ) (hC : 1 ≤ C) (hE : 0 < E) (hν : 0 < ν)
    (he : 0 < e) (heE : e ≤ E) (hCs : 0 ≤ Cs) (hθ : 0 ≤ θ) (hn : n + Dγ ≤ N)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I, ContDiff ℝ (n : ℕ∞) (B d I))
    (hBj : ∀ d ∈ Finset.Icc dout Dγ, ∀ I j, j ≤ n → ∀ y,
      E ^ j * ‖iteratedFDeriv ℝ j (B d I) y‖ ≤ Cs * (ν * e ^ (d - 2)) * θ)
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Cmap : U →L[ℝ] V) (x : Vec 2) :
    (E ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly (dout - 1) Cmap
      (fun a A => transportedCoeff K Dγ (fun d I => B d I y) (dout - 1) A y a)) x‖) /
        (ν * E ^ (dout - 2)) ≤
      (4 * (2 : ℝ) ^ cap * ‖Cmap‖ *
        (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * C *
          (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ cap) * Cs * (Dγ : ℝ) * 2 ^ cap) * θ := by
  have hledger (d : ℕ) (hd : 2 ≤ d) (hdγ : d ≤ Dγ) :
      (e / e) ^ (d - 2) * (∑ _I : DerivativeWord2 (d - 1), θ) ≤ 2 ^ cap * θ := by
    simp only [div_self he.ne', one_pow, one_mul, Finset.sum_const, Finset.card_univ,
      DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) hθ
  have hj d hd I a j hj y := vector_component_jet_budget (B d I) j
    ((hB d I).of_le (by exact_mod_cast hj)) E (Cs * (ν * e ^ (d - 2)) * θ) hE.le
    (hBj d hd I j hj) a y
  have hh := native_transport_record_price K hK N Dγ cap Kmax n dout hD hkn hdout hout
    C E E ν e e E Cs hC hE hE.le (le_refl _) hν he.le he hE (fun _ => heE)
    hCs hn hKC B (fun d I a => (contDiff_pi.mp (hB d I) a).of_le (by simp))
    (fun _ _ => θ) (fun _ _ => hθ) hj (2 ^ cap * θ)
    (mul_nonneg (pow_nonneg (by norm_num) _) hθ) hledger Cmap x
  have hratio : (e / E) ^ (Dγ - 2) ≤ 1 :=
    pow_le_one₀ (div_nonneg he.le hE.le) ((div_le_one hE).mpr heE)
  rw [max_eq_left hratio, mul_one] at hh
  exact hh.trans_eq (by ring)

/-- Positive native partition assembly transfers active-piece jets directly to
the coefficient seminorm. Only spatial smoothness on the actual time
interval is used; no unit-size context certificate is required. -/
theorem weak_quiet_constituent_seminorm_budget
    {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {D : OCData} {Dm j₀ M : ℕ} {bw : ℝ}
    (G : GenStage D hr Dm bw j₀) (hnat : G.IsNatural M)
    (ν e E a b : ℝ) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (d n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (g : ℝ → OddSlot → Vec 2 →
      ((PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root))))
    (hg : ∀ t p y, g t p y = nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map
      (fun a A => transportedCoeff
        (naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t)
        (G.fam.identity v u γ).maxOrder
        (fun d' I => G.fam.dimFlux ν e E p (G.actual p) v u γ d' I t
          (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)
          (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) y t)) (d - 1) A y a))
    (hs : ∀ t ∈ Set.Icc a b, ∀ p, t ∈ (G.fam.piece p).output →
      ContDiff ℝ (n : ℕ) (g t p))
    (hj : ∀ t ∈ Set.Icc a b, ∀ p, t ∈ (G.fam.piece p).output →
      ∀ j ≤ n, ∀ y, ρ ^ j * ‖iteratedFDeriv ℝ j (g t p) y‖ ≤ B j) :
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (n : ℕ)
      (constituentPhysical G.fam ν e E G.actual v u γ d t)) ∧
    coefficientSeminorm ρ n a b (constituentPhysical G.fam ν e E G.actual v u γ d) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j * B j / (j.factorial : ℝ)) := by
  have hreg (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ContDiff ℝ (n : ℕ) (constituentPhysical G.fam ν e E G.actual v u γ d t) := by
    have he : constituentPhysical G.fam ν e E G.actual v u γ d t =
        fun y => ∑ p ∈ (G.fam.locally_finite a b).toFinset, G.fam.weight p t • g t p y := by
      funext y
      rw [constituentPhysical_eq_window_sum G.fam ν e E G.actual a b t ht v u γ d y]
      apply Finset.sum_congr rfl
      intro p _
      rw [AVRegularity.Construction.Preservation.Buffer.native_inverse_jacobian_eq_natural hnat p t,
        AVRegularity.Construction.Preservation.Buffer.native_inverse_material_eq_flow hnat p t]
      rw [hg t p y]
      rfl
    rw [he]
    apply ContDiff.sum
    intro p _
    by_cases hp : t ∈ (G.fam.piece p).output
    · exact (hs t ht p hp).const_smul _
    · have hz : (fun y => G.fam.weight p t • g t p y) = fun _ => 0 := by
        funext y
        rw [G.fam.weight_zero p t hp]
        exact zero_smul ℝ (g t p y)
      rw [hz]
      exact contDiff_const
  refine ⟨hreg, ?_⟩
  apply pointwise_coefficient_seminorm_budget ρ hρ n a b _ hreg B hB
  intro t ht j hjn y
  exact native_constituentPhysical_positive_jet_budget hnat a b ν e E v u γ d j ρ (B j)
    hρ.le (hB j) ⟨t, ht⟩ (g t) (hg t)
    (fun p hp => (hs t ht p hp).of_le (by exact_mod_cast hjn))
    (fun p hp y => hj t ht p hp j hjn y) y

end AVRegularity.WeakEntryProofs.Assembly
end

section
open Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Uniform native physical coefficient prices on a history-quiet middle half. -/

open AVRegularity.Providers.QuietAtlas
open AVRegularity.Construction.Preservation.FullLift AVRegularity.CycleJointProofs

/-- The actual physical coefficient has a parent-scale price chosen before Dm.
Only orders at most the finite weak cap need this estimate. -/
theorem weak_quiet_native_physical_price {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M₀ : ℕ,
    ∀ (plan : WeakPassagePlan), WeakPassageCommonOK plan →
    ∀ (R : WeakPassageRequest A) (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
      (i : ℕ), M₀ ≤ c.M → c.M < i → i ≤ c.M + A.Jw →
    IsHistoryQuiet c.D (c.M + A.Jw) i (weakMiddleHalf c r i) →
    ∀ (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
      (d : ℕ), 2 ≤ d → d ≤ 1 + A.Jw * A.Nw →
    (∀ t ∈ weakMiddleHalf c r i, ContDiff ℝ (N : ℕ) ((c.stage i).physCoeff v u γ d t)) ∧
    coefficientSeminorm (c.D.eps (i - 1)) N
      (r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2) (r.tq i) ((c.stage i).physCoeff v u γ d) ≤
      ENNReal.ofReal (C * (weakQuietCertificatePrice R * ((c.stage i).fam.identity v u γ).record.size) *
        (c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2))) := by
  obtain ⟨Cs, hCs, Mf, hsample⟩ := weak_quiet_native_dimensional_flow_jets A N
  let cap := 1 + A.Jw * A.Nw
  let Nt := N + cap
  by_cases hΛ : 128 ≤ A.Λ
  · obtain ⟨Cm, hCm, Mp, _hMp, hmatrix⟩ := uniform_native_piola_matrix_jets B.α B.s B.q
      B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ hΛ B.ζ B.hζ Nt
    let T := (((N + 1 : ℕ) * (2 : ℝ) ^ N) ^ 2 * Cm *
      (3 * (Nt + 1 : ℕ) * 2 ^ Nt * Cm) ^ cap)
    let P := 4 * (2 : ℝ) ^ cap * T * Cs * (cap : ℝ) * 2 ^ cap
    let Sn := ∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ j / (j.factorial : ℝ)
    have hCm0 : 0 ≤ Cm := zero_le_one.trans hCm
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hSn : 0 ≤ Sn := Finset.sum_nonneg (fun j _ => by positivity)
    refine ⟨P * Sn, mul_nonneg hP hSn, max Mf Mp, ?_⟩
    intro plan hcommon R c r i hM hi hit hquiet v u γ d hd hdmax
    let G := c.stage i
    let ν := c.D.κ c.M
    let e := c.D.eps i
    let E := c.D.eps (i - 1)
    let θ := weakQuietCertificatePrice R * (G.fam.identity v u γ).record.size
    have hθ : 0 ≤ θ := mul_nonneg
      (Finset.sum_nonneg (fun _ _ => le_max_left 0 _)) (G.fam.identity v u γ).record.size_nonneg
    have hlev : G.level = i := EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _
      c.construction i hi.le hit
    have hκ : c.D.kap i = ν := by
      dsimp only [OCData.kap, ν]
      rw [c.terminal, Nat.min_eq_right hi.le]
    have hnat : G.IsNatural (c.M + A.Jw) := by
      by_cases he : i = c.M + A.Jw
      · have hr : IsWeakRoot (c.M + A.Jw) 0 G := by
          simpa only [G, he] using c.construction.2.1
        exact hr.2.2.2
      · exact EntryWeakProofs.weakConstruction_output_natural _ _ _ _ _ _ _ c.construction
          i hi.le (by omega)
    have horder : (G.fam.identity v u γ).maxOrder ≤ cap :=
      EntryWeakProofs.weakConstruction_stage_maxOrderBound _ _ _ _ _ _ c.construction
        i hi.le hit v u γ
    have hmap : ‖(G.fam.identity v u γ).map‖ ≤ 1 := by
      by_cases he : i = c.M + A.Jw
      · have hr : IsWeakRoot (c.M + A.Jw) 0 G := by
          simpa only [G, he] using c.construction.2.1
        exact ((hr.2.2.1 v u).false γ).elim
      · exact EntryWeakProofs.weakConstruction_identity_map_norm_le_one _ _ _ _ _ _ _
          c.construction i hi.le (by omega) v u γ
    have hΛD : 1 ≤ c.D.Λ := by rw [c.base_eq]; exact (by norm_num : 1 ≤ 128).trans hΛ
    have hE : 0 < E := Construction.Stream.ocEpsilon_pos hΛD
    have he : 0 < e := Construction.Stream.ocEpsilon_pos hΛD
    have heE : e ≤ E := Applications.eps_antitone (by rw [c.q_eq]; exact B.hq.1)
      (by rw [c.base_eq]; exact hΛ) (Nat.sub_le i 1)
    have hζ : IsFastProfile c.D.ζ := by rw [c.profile_eq]; exact B.hζ
    have hband : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
      rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]
      exact c.band
    have hν : 0 < ν := CycleReference.bandChain_pos hΛD hζ hband (by rw [c.terminal])
    let K := fun (p : OddSlot) (t : ℝ) => naturalPreparationJacobian
      (c.D.hΦ (G.level - 1)) (c.D.slotAnchor G.level p.1) t
    let F := fun (p : OddSlot) (t : ℝ) (a : ℕ) (I : DerivativeWord2 (a - 1)) (Y : Vec 2) =>
      G.fam.dimFlux ν e E p (G.actual p) v u γ a I t
        (c.D.flowOf (G.level - 1) (c.D.slotAnchor G.level p.1) Y t)
        (e⁻¹ • c.D.flowOf (G.level - 1) (c.D.slotAnchor G.level p.1) Y t)
    let g := fun (t : ℝ) (p : OddSlot) (Y : Vec 2) => nativeArrayAssembly (d - 1)
      (G.fam.identity v u γ).map (fun a A => transportedCoeff (K p t)
        (G.fam.identity v u γ).maxOrder (fun a I => F p t a I Y) (d - 1) A Y a)
    have hK (p : OddSlot) (t : ℝ) (a b : Fin 2) :
        ContDiff ℝ (⊤ : ℕ∞) (fun Y => K p t Y a b) :=
      (naturalPreparationJacobian_entry_smooth (c.D.hΦ (G.level - 1))
        (c.D.slotAnchor G.level p.1) a b).comp (contDiff_const.prodMk contDiff_id)
    have hF (t : ℝ) (ht : t ∈ weakMiddleHalf c r i) (p : OddSlot)
        (hp : t ∈ (G.fam.piece p).output) (a : ℕ) (I : DerivativeWord2 (a - 1)) :
        ContDiff ℝ (N : ℕ∞) (F p t a I) ∧
        ∀ j ≤ N, ∀ Y, E ^ j * ‖iteratedFDeriv ℝ j (F p t a I) Y‖ ≤ Cs * (ν * e ^ (a - 2)) * θ := by
      have htp : t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ G.level p.1 := by
        rwa [← (hnat.1 p).2.1]
      have hh := hsample plan hcommon R c r i ((le_max_left _ _).trans hM) hi hit hquiet
        v u γ a I p t ht htp
      simpa only [F, hlev, G, ν, e, E, θ] using hh
    have hgs (t : ℝ) (ht : t ∈ weakMiddleHalf c r i) (p : OddSlot)
        (hp : t ∈ (G.fam.piece p).output) : ContDiff ℝ (N : ℕ) (g t p) := by
      apply nativeArrayAssembly_spatial_smooth
      intro a A
      exact transportedCoeff_spatial_smooth (K p t) (hK p t) _ N (F p t)
        (fun a I b => (contDiff_pi.mp (hF t ht p hp a I).1 b).of_le (by simp)) _ A a
    have hgj (t : ℝ) (ht : t ∈ weakMiddleHalf c r i) (p : OddSlot)
        (hp : t ∈ (G.fam.piece p).output) (j : ℕ) (hj : j ≤ N) (Y : Vec 2) :
        E ^ j * ‖iteratedFDeriv ℝ j (g t p) Y‖ ≤ P * θ * (ν * E ^ (d - 2)) := by
      have htp : t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ G.level p.1 := by
        rwa [← (hnat.1 p).2.1]
      have hKC : ∀ a b k, k ≤ Nt → ∀ Y,
          E ^ k * ‖iteratedFDeriv ℝ k (fun X => K p t X a b) Y‖ ≤ Cm := by
        have hh := hmatrix c.D c.alpha c.q_eq c.base_eq c.profile_eq c.streams i
          (by have := (le_max_right _ _).trans hM; omega) hE p.1 p.2 t
          (by simpa only [hlev] using htp)
        simpa only [K, hlev] using hh
      have hraw := weak_quiet_parent_transport_price (K p t) (hK p t) Nt
        (G.fam.identity v u γ).maxOrder cap N j d horder hj hd hdmax Cm E ν e Cs θ hCm
        hE hν he heE hCs hθ (by dsimp [Nt]; omega) hKC (F p t)
        (fun a I => (hF t ht p hp a I).1.of_le (by exact_mod_cast hj))
        (fun a _ I k hk Y => (hF t ht p hp a I).2 k (hk.trans hj) Y)
        (G.fam.identity v u γ).map Y
      have hprice :
          (4 * (2 : ℝ) ^ cap * ‖(G.fam.identity v u γ).map‖ * T * Cs *
            ((G.fam.identity v u γ).maxOrder : ℝ) * 2 ^ cap) ≤ P := by
        let U := 4 * (2 : ℝ) ^ cap * T * Cs * 2 ^ cap
        have hU : 0 ≤ U := by dsimp [U]; positivity
        calc
          _ = U * (‖(G.fam.identity v u γ).map‖ * ((G.fam.identity v u γ).maxOrder : ℝ)) := by
            dsimp [U]; ring
          _ ≤ U * (1 * (cap : ℝ)) := mul_le_mul_of_nonneg_left
            (mul_le_mul hmap (by exact_mod_cast horder) (Nat.cast_nonneg _) zero_le_one) hU
          _ = P := by dsimp [U, P]; ring
      have hh := hraw.trans (mul_le_mul_of_nonneg_right hprice hθ)
      exact (div_le_iff₀ (mul_pos hν (pow_pos hE _))).mp hh
    have hbudget := weak_quiet_constituent_seminorm_budget G hnat ν e E
      (r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2) (r.tq i) v u γ d N E hE
      (fun _ => P * θ * (ν * E ^ (d - 2)))
      (fun _ => mul_nonneg (mul_nonneg hP hθ) (mul_nonneg hν.le (pow_nonneg hE.le _)))
      g (fun _ _ _ => rfl) hgs hgj
    have hphys : G.physCoeff v u γ d = constituentPhysical G.fam ν e E G.actual v u γ d := by
      simp only [GenStage.physCoeff, hlev, hκ, e, E]
    rw [hphys]
    refine ⟨hbudget.1, hbudget.2.trans_eq ?_⟩
    congr 1
    calc
      _ = (∑ j ∈ Finset.range (N + 1), (2 : ℝ) ^ j / (j.factorial : ℝ)) *
          (P * θ * (ν * E ^ (d - 2))) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by dsimp only [Sn, θ, ν, E, G]; ring
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro plan _ R c
    exact (hΛ ((plan.base_ge B).trans c.base_ge)).elim

end AVRegularity.WeakEntryProofs.Assembly
end
end
end
