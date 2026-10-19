-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.CorrectorMeanGeometry
public import AVRegularity.CycleReference.SpacetimeGradientPairing
public import AVenhance.Infra.Ergodic.Flow
public import AVenhance.Infra.Torus.Basic
import AVenhance.Infra.Section5.FlowPiolaDivergence
import AVRegularity.CycleReference.TestDriftIntegrability
public import AVRegularity.Statements.Intermediate.CycleReference.OcPulseStream
public import AVenhance.Infra.Section5.FlowPiola
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Infra.Section3.FluxMatrix
public import Mathlib.Order.CompletePartialOrder
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Section3.CorrectorGradient
import AVenhance.Infra.Section5.PulledGradientTransport
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Integrating finitely many disjoint intervals of pointwise gain. -/

theorem integral_disjoint_interval_lower (S : Finset ℤ) (a b : ℤ → ℝ)
    (A B c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume A B) (hAB : A ≤ B)
    (hsub : ∀ k ∈ S, A ≤ a k ∧ a k ≤ b k ∧ b k ≤ B)
    (hdisj : ∀ k ∈ S, ∀ j ∈ S, k ≠ j → Disjoint (Set.Ioc (a k) (b k)) (Set.Ioc (a j) (b j)))
    (hnonneg : ∀ t ∈ Set.Ioc A B, 0 ≤ f t)
    (hlower : ∀ k ∈ S, ∀ t ∈ Set.Ioc (a k) (b k), c ≤ f t) :
    ∑ k ∈ S, c * (b k - a k) ≤ ∫ t in A..B, f t := by
  let g : ℤ → ℝ → ℝ := fun k => (Set.Ioc (a k) (b k)).indicator (fun _ => c)
  have hg (k : ℤ) (hk : k ∈ S) : Integrable (g k) := by
    rw [show g k = (Set.Ioc (a k) (b k)).indicator (fun _ => c) by rfl,
      integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (by simp)
  have hgint (k : ℤ) (hk : k ∈ S) : (∫ t, g k t) = c * (b k - a k) := by
    dsimp [g]
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (hsub k hk).2.1]
    simp [mul_comm]
  have hpoint (t : ℝ) : ∑ k ∈ S, g k t ≤ (Set.Ioc A B).indicator f t := by
    by_cases he : ∃ k ∈ S, t ∈ Set.Ioc (a k) (b k)
    · obtain ⟨k, hk, ht⟩ := he
      have hsum : (∑ j ∈ S, g j t) = c := by
        rw [Finset.sum_eq_single k]
        · exact Set.indicator_of_mem ht _
        · intro j hj hjk
          have hnot : t ∉ Set.Ioc (a j) (b j) := by
            intro htj
            exact Set.disjoint_left.mp (hdisj k hk j hj (Ne.symm hjk)) ht htj
          exact Set.indicator_of_notMem hnot _
        · exact fun h => (h hk).elim
      rw [hsum, Set.indicator_of_mem (show t ∈ Set.Ioc A B from
        ⟨lt_of_le_of_lt (hsub k hk).1 ht.1, ht.2.trans (hsub k hk).2.2⟩)]
      exact hlower k hk t ht
    · have hsum : (∑ k ∈ S, g k t) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        exact Set.indicator_of_notMem (fun ht => he ⟨k, hk, ht⟩) _
      rw [hsum]
      exact Set.indicator_nonneg hnonneg t
  have hle : (∫ t, ∑ k ∈ S, g k t) ≤ ∫ t, (Set.Ioc A B).indicator f t := by
    apply integral_mono_of_nonneg
    · filter_upwards [] with t
      exact Finset.sum_nonneg (fun k _ => Set.indicator_nonneg (fun _ _ => hc) t)
    · rw [integrable_indicator_iff measurableSet_Ioc]
      simpa [IntervalIntegrable, hAB, intervalIntegral.integral_of_le] using hf.1
    · exact Filter.Eventually.of_forall hpoint
  rw [integral_finsetSum S hg, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hAB] at hle
  have heq : (∑ k ∈ S, ∫ t, g k t) = ∑ k ∈ S, c * (b k - a k) := by
    apply Finset.sum_congr rfl
    exact fun k hk => hgint k hk
  rw [heq] at hle
  exact hle

/-! Exact average of the odd fast profiles before inserting the slow envelopes. -/

noncomputable def fastSquareSum (ζ : ℝ → ℝ) (τ t : ℝ) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, ζ (t / τ - k.1) ^ 2

theorem fastSquareSum_periodic (ζ : ℝ → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Function.Periodic (fastSquareSum ζ τ) (2 * τ) := by
  intro t
  unfold fastSquareSum
  rw [← (oddSlotAddEquiv 2 (by decide)).tsum_eq]
  apply tsum_congr
  intro k
  congr 2
  dsimp [oddSlotAddEquiv]
  push_cast
  field_simp
  ring

theorem fastSquareSum_on_period {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {τ t : ℝ} (hτ : 0 < τ) (ht : t ∈ Set.Icc 0 (2 * τ)) :
    fastSquareSum ζ τ t = ζ (t / τ - 1) ^ 2 := by
  let k1 : {k : ℤ // Odd k} := ⟨1, by decide⟩
  unfold fastSquareSum
  rw [tsum_eq_single k1]
  · simp [k1]
  · intro k hk
    have hk' : k.1 ≠ 1 := by intro he; apply hk; exact Subtype.ext he
    by_cases hz : ζ (t / τ - k.1) = 0
    · simp [hz]
    · have hd := profile_ne_support_interval hζ hz
      have hlo : 0 ≤ t / τ := div_nonneg ht.1 hτ.le
      have hhi : t / τ ≤ 2 := (div_le_iff₀ hτ).mpr ht.2
      have hl : (-1 : ℝ) < k.1 := by linarith only [hd.2, hlo]
      have hh : (k.1 : ℝ) < 3 := by linarith only [hd.1, hhi]
      have hli : -1 < k.1 := by exact_mod_cast hl
      have hhi : k.1 < 3 := by exact_mod_cast hh
      rcases k.2 with ⟨a, ha⟩
      omega

theorem fast_square_integral (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    {τ : ℝ} (hτ : 0 < τ) :
    (∫ t in (0 : ℝ)..(2 * τ), ζ (t / τ - 1) ^ 2) = τ * (9 / 10) := by
  have heq : (fun t : ℝ => ζ (t / τ - 1) ^ 2) =
      (fun t : ℝ => ζ (t - 1) ^ 2) ∘ (fun t => t / τ) := rfl
  rw [heq]
  simp only [Function.comp_def]
  rw [intervalIntegral.integral_comp_div (fun t : ℝ => ζ (t - 1) ^ 2) (ne_of_gt hτ)]
  have he : (2 * τ) / τ = 2 := by field_simp
  rw [zero_div, he]
  have hshift := intervalIntegral.integral_comp_sub_right (fun t : ℝ => ζ t ^ 2) (1 : ℝ)
    (a := (0 : ℝ)) (b := 2)
  rw [hshift]
  have hs : Function.support (fun t : ℝ => ζ t ^ 2) ⊆ Set.Ioc (-1 : ℝ) 1 := by
    intro t ht
    have hz : ζ t ≠ 0 := by intro hz; exact ht (by simp [hz])
    have hd := profile_ne_support_interval hζ hz
    constructor <;> linarith [hd.1, hd.2]
  norm_num
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs, hζ.2.2.2.2.2]
  norm_num

theorem fastSquareSum_integral_period {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {τ : ℝ} (hτ : 0 < τ) :
    (∫ t in (0 : ℝ)..(2 * τ), fastSquareSum ζ τ t) = τ * (9 / 10) := by
  calc
    _ = ∫ t in (0 : ℝ)..(2 * τ), ζ (t / τ - 1) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact fastSquareSum_on_period hζ hτ (by
        simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 2 * τ by positivity)] using ht)
    _ = _ := fast_square_integral ζ hζ hτ

theorem fastSquareSum_intervalIntegrable {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {τ : ℝ} (hτ : 0 < τ) (a b : ℝ) :
    IntervalIntegrable (fastSquareSum ζ τ) volume a b := by
  apply (fastSquareSum_periodic ζ hτ).intervalIntegrable (by positivity : (2 * τ) ≠ 0)
    (t := (0 : ℝ))
  have hi : IntervalIntegrable (fun t : ℝ => ζ (t / τ - 1) ^ 2) volume 0 (2 * τ) :=
    ((hζ.1.continuous.comp (by fun_prop)).pow 2).intervalIntegrable _ _
  simp only [zero_add]
  apply hi.congr
  intro t ht
  exact (fastSquareSum_on_period hζ hτ (by
    rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * τ)] at ht
    exact ⟨ht.1.le, ht.2⟩)).symm

theorem fastSquareSum_integral_multiple {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {τ : ℝ} (hτ : 0 < τ) (n : ℤ) (s : ℝ) :
    (∫ t in s..(s + (n : ℝ) * (2 * τ)), fastSquareSum ζ τ t) =
      (n : ℝ) * τ * (9 / 10) := by
  have hp := fastSquareSum_periodic ζ hτ
  have hi := fastSquareSum_intervalIntegrable hζ hτ
  have he := hp.intervalIntegral_add_zsmul_eq n s hi
  have hsingle : (∫ t in s..(s + 2 * τ), fastSquareSum ζ τ t) = τ * (9 / 10) := by
    rw [hp.intervalIntegral_add_eq s 0, zero_add]
    exact fastSquareSum_integral_period hζ hτ
  simpa only [zsmul_eq_mul, hsingle, mul_assoc] using he

theorem fastSquareSum_cycle_average {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (s : ℝ) :
    (∫ t in s..(s + 4 * ocTauPP α q Λ m), fastSquareSum ζ (ocTau α q Λ m) t) =
      (4 * ocTauPP α q Λ m) * (9 / 20) := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hscale : (ocL α q Λ m : ℝ) ^ 2 * ocTau α q Λ m = ocTauPP α q Λ m := by
    rw [ocTau]
    have hL : (ocL α q Λ m : ℝ) ≠ 0 := by
      have hn : 0 < ocL α q Λ m := by unfold ocL; omega
      exact_mod_cast hn.ne'
    field_simp
  have he := fastSquareSum_integral_multiple hζ hτ (2 * (ocL α q Λ m : ℤ) ^ 2) s
  push_cast at he
  have hend : s + 2 * (ocL α q Λ m : ℝ) ^ 2 * (2 * ocTau α q Λ m) =
      s + 4 * ocTauPP α q Λ m := by rw [← hscale]; ring
  rw [hend] at he
  rw [he, ← hscale]
  ring

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! The active-pulse velocity and its transverse transport cancellation. -/

theorem ocShear_contDiff (α q : ℝ) (Λ m : ℕ) (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (ocShear α q Λ m k) := by
  have hfun := funext (ocShear_sine_formula (α := α) (q := q) (Λ := Λ) (m := m) k)
  rw [hfun]
  split_ifs <;> fun_prop

theorem pulseStreamVel_eq_active {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k : ℤ} (hk : Odd k)
    {t : ℝ} (hp : ocPulse α q Λ ζ m k t ≠ 0) (y : Vec 2) :
    streamVel (ocPulseStream α q Λ ζ m) t y =
      ocPulse α q Λ ζ m k t • ocShearVel α q Λ m k y := by
  have hstream : ocPulseStream α q Λ ζ m t = fun y =>
      ocPulse α q Λ ζ m k t * ocShear α q Λ m k y :=
    funext (fun y => ocPulseStream_eq_active (y := y) hΛ hζ hk hp)
  simp only [ocShearVel, streamVel]
  rw [hstream]
  have hgrad : spaceGrad (fun y => ocPulse α q Λ ζ m k t * ocShear α q Λ m k y) y =
      ocPulse α q Λ ζ m k t • spaceGrad (ocShear α q Λ m k) y := by
    ext i
    unfold spaceGrad
    rw [fderiv_const_mul ((ocShear_contDiff α q Λ m k).differentiable (by simp) y)]
    simp
  rw [hgrad, Matrix.mulVec_smul]

theorem pulseStreamVel_eq_zero_of_quiet {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {t : ℝ} (hp : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k t = 0) (y : Vec 2) :
    streamVel (ocPulseStream α q Λ ζ m) t y = 0 := by
  have hstream : ocPulseStream α q Λ ζ m t = fun _ => 0 := by
    funext y
    unfold ocPulseStream
    calc
      _ = ∑' _k : {k : ℤ // Odd k}, (0 : ℝ) := by
        apply tsum_congr
        intro k
        rw [hp k.1 k.2, zero_mul]
      _ = 0 := tsum_zero
  unfold streamVel
  rw [hstream]
  simp [spaceGrad]

theorem shear_transport_pulseCorrector_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (hk : Odd k) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, ocShearVel α q Λ m k y i *
      fderiv ℝ (fun z => ocPulseCorrector α q Λ ζ m ν k t z j) y (basisVec i)) = 0 := by
  rcases odd_int_mod_four hk with h1 | h3
  · obtain ⟨hf0, hf1⟩ := pulseCorrector_horizontal_components
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h1 ν t
    fin_cases j
    · change (∑ i : Fin 2, ocShearVel α q Λ m k y i *
        fderiv ℝ (fun z => ocPulseCorrector α q Λ ζ m ν k t z (0 : Fin 2)) y (basisVec i)) = 0
      rw [hf0]
      simp
    · change (∑ i : Fin 2, ocShearVel α q Λ m k y i *
        fderiv ℝ (fun z => ocPulseCorrector α q Λ ζ m ν k t z (1 : Fin 2)) y (basisVec i)) = 0
      rw [hf1, Fin.sum_univ_two, ocShearVel_horizontal h1]
      change 0 * _ + _ * spaceGrad (fun z => _ * Real.cos (_ * z 0)) y 1 = 0
      rw [AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
      simp
  · obtain ⟨hf0, hf1⟩ := pulseCorrector_vertical_components
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h3 ν t
    fin_cases j
    · change (∑ i : Fin 2, ocShearVel α q Λ m k y i *
        fderiv ℝ (fun z => ocPulseCorrector α q Λ ζ m ν k t z (0 : Fin 2)) y (basisVec i)) = 0
      rw [hf0, Fin.sum_univ_two, ocShearVel_vertical h3]
      change _ * spaceGrad (fun z => _ * Real.cos (_ * z 1)) y 0 + 0 * _ = 0
      rw [AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
      simp
    · change (∑ i : Fin 2, ocShearVel α q Λ m k y i *
        fderiv ℝ (fun z => ocPulseCorrector α q Λ ζ m ν k t z (1 : Fin 2)) y (basisVec i)) = 0
      rw [hf1]
      simp

theorem pulseStream_transport_refCorrector_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, streamVel (ocPulseStream α q Λ ζ m) t y i *
      fderiv ℝ (fun z => ocRefCorrector α q Λ ζ m ν t z j) y (basisVec i)) = 0 := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k t ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    rw [pulseStreamVel_eq_active hΛ hζ hk hp y, ocRefCorrector_eq_active hΛ hζ hk hp]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [← Finset.mul_sum, shear_transport_pulseCorrector_zero hk]
    ring
  · have hp0 : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k t = 0 := by
      intro k hk
      by_contra hne
      exact hp ⟨k, hk, hne⟩
    rw [pulseStreamVel_eq_zero_of_quiet hp0]
    simp

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open AVenhance.Infra.Ergodic
namespace AVRegularity.CycleReference

/-! Periodic cell transport by the renewal flow. -/

theorem streamFlow_lattice_equivariant {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) (x : Vec 2) (k : Fin 2 → ℤ) :
    AVRegularity.streamFlow φ hφ t (x + latticeShift k) s =
      AVRegularity.streamFlow φ hφ t x s + latticeShift k := by
  apply Infra.Flow.flow_lattice_equivariant _ hφ.vel_lipschitz _
    (flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz)
  intro r n y
  simpa using (Infra.Construction.smoothPeriodic_streamVel hφ).periodic 0 n r y

noncomputable def streamFlowPeriodicDiffeomorphism {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) : PeriodicVolumePreservingDiffeomorphism 2 where
  toFun := streamFlowHomeomorph hφ t s
  invFun := (streamFlowHomeomorph hφ t s).symm
  contDiff_toFun := streamFlow_spatial_smooth hφ t s
  contDiff_invFun := streamFlow_spatial_smooth hφ s t
  left_inv := (streamFlowHomeomorph hφ t s).symm_apply_apply
  right_inv := (streamFlowHomeomorph hφ t s).apply_symm_apply
  lattice_equivariant := fun x k => streamFlow_lattice_equivariant hφ t s x k
  measurePreserving := streamFlow_measurePreserving hφ t s

theorem flowFundamentalCell_ae_unitCube :
    Flow.flowFundamentalCell 2 =ᵐ[volume] unitCube := by
  rw [← Flow.unitCellSet_eq_flowFundamentalCell]
  have he : unitCellSet 2 = Infra.Torus.unitCell 2 := by
    ext x
    simp [unitCellSet, Infra.Torus.unitCell, Infra.Torus.unitCellAt]
  rw [he]
  exact Infra.Torus.unitCell_ae_eq_unitCube

 theorem streamFlow_cell_integral {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) (u : Vec 2 → ℝ)
    (hu : IsZ2Periodic u) :
    (∫ y in unitCube, u (AVRegularity.streamFlow φ hφ t y s)) =
      ∫ x in unitCube, u x := by
  have he := cellAverage_comp_flow_eq u
    ((isZPeriodic_iff_isZ2Periodic u).2 hu) (streamFlowPeriodicDiffeomorphism hφ t s)
  simp only [cellAverage_eq_unitCellIntegral, Flow.unitCellSet_eq_flowFundamentalCell] at he
  rw [setIntegral_congr_set flowFundamentalCell_ae_unitCube,
    setIntegral_congr_set flowFundamentalCell_ae_unitCube] at he
  exact he

 theorem streamFlow_cell_memL2 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) {u : Vec 2 → ℝ}
    (hp : IsZ2Periodic u) (hu : MemL2On unitCube u) :
    MemL2On unitCube (fun y => u (AVRegularity.streamFlow φ hφ t y s)) := by
  let : Countable (Flow.flowLattice 2) := Flow.flowLattice_countable 2
  let X := streamFlowPeriodicDiffeomorphism hφ t s
  let S := Flow.flowFundamentalCell 2
  let T := X.toFun '' S
  have hs := Flow.flowFundamentalCell_isAddFundamentalDomain 2
  have ht := Flow.flow_imageFundamentalCell_isAddFundamentalDomain X
  have hp' := Flow.flowLattice_translation_invariant
    ((isZPeriodic_iff_isZ2Periodic u).2 hp)
  have hm : MemLp u 2 (volume.restrict S) := by
    rw [Measure.restrict_congr_set flowFundamentalCell_ae_unitCube]
    exact hu
  have ha : AEStronglyMeasurable u (volume.restrict T) :=
    (hs.aestronglyMeasurable_on_iff ht hp').mp hm.aestronglyMeasurable
  have hi : IntegrableOn (fun x => u x ^ 2) T := by
    apply (hs.integrableOn_iff ht (f := fun x => u x ^ 2)
      (fun g x => by rw [hp' g x])).mp
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
  have hmt : MemLp u 2 (volume.restrict T) :=
    (memLp_two_iff_integrable_sq ha).mpr hi
  have hc := hmt.comp_measurePreserving
    (X.measurePreserving.restrict_image_emb (Flow.flowMeasurableEquiv X).measurableEmbedding S)
  rw [Measure.restrict_congr_set flowFundamentalCell_ae_unitCube] at hc
  exact hc

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Bilinear cancellation of a volume-preserving chart Jacobian. -/

theorem inverse_pullback_pairing (F : Matrix (Fin 2) (Fin 2) ℝ) (hF : IsUnit F.det)
    (v w : Vec 2) : vecDot (F⁻¹.mulVec v) (Fᵀ.mulVec w) = vecDot v w := by
  change dotProduct _ _ = dotProduct v w
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hF, Matrix.one_mulVec]

theorem metric_pullback_pairing (F : Matrix (Fin 2) (Fin 2) ℝ) (hF : IsUnit F.det)
    (v w : Vec 2) :
    vecDot ((F⁻¹ * (F⁻¹)ᵀ).mulVec (Fᵀ.mulVec v)) (Fᵀ.mulVec w) = vecDot v w := by
  have hT : (F⁻¹)ᵀ * Fᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hF, Matrix.transpose_one]
  have hi : (F⁻¹)ᵀ.mulVec (Fᵀ.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, hi]
  exact inverse_pullback_pairing F hF v w

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Only one odd fast profile can contribute at a fixed time. -/

theorem odd_fast_support_unique {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {u : ℝ} {k j : ℤ} (hk : Odd k) (hj : Odd j)
    (hzk : ζ (u - k) ≠ 0) (hzj : ζ (u - j) ≠ 0) : k = j := by
  have hdk := profile_ne_support_interval hζ hzk
  have hdj := profile_ne_support_interval hζ hzj
  have hgap : |(k : ℝ) - (j : ℝ)| < 2 := by
    rw [abs_lt]
    constructor <;> linarith only [hdk.1, hdk.2, hdj.1, hdj.2]
  have hle : -2 < k - j ∧ k - j < 2 := by
    constructor
    · exact_mod_cast (abs_lt.mp hgap).1
    · exact_mod_cast (abs_lt.mp hgap).2
  rcases hk with ⟨a, ha⟩
  rcases hj with ⟨b, hb⟩
  omega

theorem fastSquareSum_eq_at_nonzero {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (τ t : ℝ) (k : {k : ℤ // Odd k}) (hk : ζ (t / τ - k.1) ≠ 0) :
    fastSquareSum ζ τ t = ζ (t / τ - k.1) ^ 2 := by
  unfold fastSquareSum
  apply tsum_eq_single k
  intro j hj
  have hz : ζ (t / τ - j.1) = 0 := by
    by_contra hz
    exact hj (Subtype.ext (odd_fast_support_unique hζ j.2 k.2 hz hk))
  simp [hz]

theorem fastSquareSum_range {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (τ t : ℝ) :
    0 ≤ fastSquareSum ζ τ t ∧ fastSquareSum ζ τ t ≤ 1 := by
  by_cases he : ∃ k : {k : ℤ // Odd k}, ζ (t / τ - k.1) ≠ 0
  · obtain ⟨k, hk⟩ := he
    rw [fastSquareSum_eq_at_nonzero hζ τ t k hk]
    have hz := hζ.2.2.2.1 (t / τ - k.1)
    exact ⟨sq_nonneg _, by nlinarith only [hz.1, hz.2]⟩
  · have hz : fastSquareSum ζ τ t = 0 := by
      have hk (k : {k : ℤ // Odd k}) : ζ (t / τ - k.1) = 0 := by
        by_contra hk
        exact he ⟨k, hk⟩
      simp [fastSquareSum, hk]
    simp [hz]

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization MeasureTheory
namespace AVRegularity.CycleReference

/-! Weak-gradient testing against compactly supported vector fields. -/

theorem locallyIntegrable_mul_test {u : Vec 2 → ℝ}
    (hu : LocallyIntegrable u volume) {η : Vec 2 → ℝ}
    (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun x => u x * η x) volume := by
  simpa only [smul_eq_mul] using hu.integrable_smul_right_of_hasCompactSupport hη hc

theorem weakGradient_vector_test {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : LocallyIntegrable u volume) (hDu : ∀ i, LocallyIntegrable (fun x => Du x i) volume)
    (hw : HasWeakGradientOn Set.univ u Du) (V : Vec 2 → Vec 2)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hc : HasCompactSupport V) :
    ∫ x, u x * (∑ i : Fin 2, fderiv ℝ (fun y => V y i) x (basisVec i)) =
      -∫ x, vecDot (Du x) (V x) := by
  have hs (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => V x i) :=
    (contDiff_apply ℝ ℝ i).comp hV
  have hsc (i : Fin 2) : HasCompactSupport (fun x => V x i) :=
    hc.comp_left (g := fun v : Vec 2 => v i) rfl
  have hdc (i : Fin 2) : HasCompactSupport
      (fun x => fderiv ℝ (fun y => V y i) x (basisVec i)) :=
    ((hsc i).fderiv ℝ).comp_left (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) rfl
  have hdcont (i : Fin 2) : Continuous
      (fun x => fderiv ℝ (fun y => V y i) x (basisVec i)) := by
    have hd := (hs i).fderiv_right (m := 0) (by simp)
    exact (hd.clm_apply contDiff_const).continuous
  have hi (i : Fin 2) := locallyIntegrable_mul_test hu (hdcont i) (hdc i)
  have hdi (i : Fin 2) := locallyIntegrable_mul_test (hDu i) (hs i).continuous (hsc i)
  have he (i : Fin 2) : ∫ x, u x * fderiv ℝ (fun y => V y i) x (basisVec i) =
      -∫ x, Du x i * V x i := by
    simpa only [Measure.restrict_univ] using hw i (fun x => V x i) (hs i) (hsc i) (Set.subset_univ _)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  congr 1
  simp only [vecDot]
  exact (integral_finsetSum _ (fun i _ => hdi i)).symm

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance AVenhance.Infra.Section5
open scoped Matrix
namespace AVRegularity.CycleReference

/-! The coordinate Piola identity in the renewal Jacobian convention. -/

theorem jacMatrix_eq_gradMatrix_transpose {M : Vec 2 → Vec 2}
    (hM : Differentiable ℝ M) (x : Vec 2) : jacMatrix M x = (gradMatrix M x)ᵀ := by
  ext i j
  exact (gradMatrix_entry_eq_fderiv (hM x) j i).symm

theorem rowCofactor_eq_jacMatrix_inverse {M : Vec 2 → Vec 2}
    (hM : Differentiable ℝ M) (x : Vec 2) (hd : (jacMatrix M x).det = 1) :
    rowCofactor (gradMatrix M x) = (jacMatrix M x)⁻¹ := by
  rw [rowCofactor, ← jacMatrix_eq_gradMatrix_transpose hM]
  rw [Matrix.inv_def, hd]
  simp

theorem vecDiv_eq_sum_fderiv (V : Vec 2 → Vec 2) (x : Vec 2) :
    vecDiv V x = ∑ i : Fin 2, fderiv ℝ (fun y => V y i) x (basisVec i) := rfl

theorem inverse_jacobian_piola {M g : Vec 2 → Vec 2}
    (hM : ContDiff ℝ (⊤ : ℕ∞) M) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hd : ∀ x, (jacMatrix M x).det = 1) (x : Vec 2) :
    vecDiv (fun y => (jacMatrix M y)⁻¹.mulVec (g (M y))) x = vecDiv g (M x) := by
  have hdiff := hM.differentiable (by simp)
  have hcof (y : Vec 2) := rowCofactor_eq_jacMatrix_inverse hdiff y (hd y)
  obtain ⟨hQ, hdiv⟩ := rowCofactor_gradMatrix_piolaInputs (hM.of_le (by simp)) x
  have hdet : (gradMatrix M x).det = 1 := by
    rw [← Matrix.det_transpose, ← jacMatrix_eq_gradMatrix_transpose hdiff]
    exact hd x
  have ht := vecDiv_rowCofactorPiola (hdiff x).hasFDerivAt
    (hg.differentiable (by simp) (M x)).hasFDerivAt hQ hdiv hdet
  simpa only [hcof] using ht

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

theorem refCorrector_cell_mean {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hm : 1 ≤ m) (hζ : IsFastProfile ζ) {ν : ℝ}
    (hν : 0 < ν) (t : ℝ) (i j : Fin 2) :
    (∫ y in unitCube,
      ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ocPulseStream α q Λ ζ m t y • sigmaMat) *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (jacMatrix (ocRefCorrector α q Λ ζ m ν t) y)ᵀ)) i j) =
      ocRefFlux α q Λ ζ m ν t i j := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k t ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    have hstream : ocPulseStream α q Λ ζ m t = fun y =>
        ocPulse α q Λ ζ m k t * ocShear α q Λ m k y := by
      funext y
      exact ocPulseStream_eq_active hΛ hζ hk hp
    rw [hstream, ocRefCorrector_eq_active hΛ hζ hk hp]
    have hmean : spaceAvgMat (fun y : Vec 2 =>
        ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (ocPulse α q Λ ζ m k t * ocShear α q Λ m k y) • sigmaMat) *
          ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (jacMatrix (ocPulseCorrector α q Λ ζ m ν k t) y)ᵀ))) =
        ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (ocMu q Λ m ν * ocHStar α q Λ m ν * ocPulse α q Λ ζ m k t *
            ocPulseMemory α q Λ ζ m ν k t) • ocPi ⟨k, hk⟩ := by
      rcases odd_int_mod_four hk with h1 | h3
      · exact pulseCellFlux_horizontal hΛ hm hν hk h1 t rfl
      · exact pulseCellFlux_vertical hΛ hm hν hk h3 t rfl
    have hflux : ocRefFlux α q Λ ζ m ν t =
        ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (ocMu q Λ m ν * ocHStar α q Λ m ν * ocPulse α q Λ ζ m k t *
            ocPulseMemory α q Λ ζ m ν k t) • ocPi ⟨k, hk⟩ := by
      unfold ocRefFlux
      rw [pulseMatrixSum_eq_at_active hΛ hζ ν t ⟨k, hk⟩ hp, smul_smul]
      congr 2
      ring
    rw [hflux]
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hmean
  · have hp0 (k : ℤ) (hk : Odd k) : ocPulse α q Λ ζ m k t = 0 := by
      by_contra hne
      exact hp ⟨k, hk, hne⟩
    have hstream : ocPulseStream α q Λ ζ m t = fun _ => 0 := by
      funext y
      unfold ocPulseStream
      calc
        _ = ∑' _k : {k : ℤ // Odd k}, (0 : ℝ) := by
          apply tsum_congr
          intro k
          rw [hp0 k.1 k.2]
          exact zero_mul _
        _ = 0 := tsum_zero
    have hflux : ocRefFlux α q Λ ζ m ν t = ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      unfold ocRefFlux
      rw [pulseMatrixSum_eq_zero_of_quiet ν t (fun k => hp0 k.1 k.2)]
      simp
    rw [hstream, hflux]
    have hgrad : spaceAvg (fun y =>
        spaceGrad (fun z => ocRefCorrector α q Λ ζ m ν t z j) y i) = 0 :=
      spaceAvg_spaceGrad_zero_of_periodic
        ((ocRefCorrector_component_contDiff hΛ ν t j).of_le (by simp))
        (ocRefCorrector_component_isZ2Periodic hΛ hm ν t j) i
    have hcont : Continuous (fun y =>
        spaceGrad (fun z => ocRefCorrector α q Λ ζ m ν t z j) y i) := by
      unfold spaceGrad
      exact ((ocRefCorrector_component_contDiff hΛ ν t j).continuous_fderiv
        (by simp)).clm_apply continuous_const
    change spaceAvg (fun y => _) = _
    have hpoint (y : Vec 2) :
        ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (0 : ℝ) • sigmaMat) *
          ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (jacMatrix (ocRefCorrector α q Λ ζ m ν t) y)ᵀ)) i j =
        ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
          ν * spaceGrad (fun z => ocRefCorrector α q Λ ζ m ν t z j) y i := by
      have hf : DifferentiableAt ℝ (ocRefCorrector α q Λ ζ m ν t) y := by
        apply differentiableAt_pi.mpr
        intro a
        exact (ocRefCorrector_component_contDiff (α := α) (q := q) (m := m)
          (ζ := ζ) hΛ ν t a).differentiable (by simp) |>.differentiableAt
      simp only [zero_smul, add_zero, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.transpose_apply]
      rw [jacMatrix_entry_eq_spaceGrad _ _ hf]
      ring
    simp_rw [hpoint]
    rw [AVenhance.Infra.Section3.FluxMatrix.spaceAvg_add_of_continuous
      (f := fun _ => ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
      (g := fun y => ν * spaceGrad (fun z => ocRefCorrector α q Λ ζ m ν t z j) y i)
      continuous_const (continuous_const.mul hcont),
      AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_eq,
      AVenhance.Infra.Section3.FluxMatrix.spaceAvg_const_mul, hgrad]
    simp

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleReference

/-! Ordered coordinate derivatives as evaluations of the iterated Fréchet derivative. -/

theorem orderedPartial_eq_reversed_iteratedFDeriv {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (w : DerivativeWord2 n) (x : Vec 2) :
    orderedPartial f n w x = iteratedFDeriv ℝ n f x (fun j => basisVec (w j.rev)) := by
  induction n generalizing x with
  | zero => simp [orderedPartial]
  | succ n ih =>
    have he : orderedPartial f n (Fin.init w) = fun y =>
        iteratedFDeriv ℝ n f y (fun j => basisVec (Fin.init w j.rev)) :=
      funext (fun y => ih (Fin.init w) y)
    rw [orderedPartial, he]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
      hf.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast ENat.natCast_lt_top n) x
    have hder := hd.iteratedFDeriv_succ_apply_left'
      (m := fun j : Fin (n + 1) => basisVec (w j.rev))
    have ht : Fin.tail (fun j : Fin (n + 1) => basisVec (w j.rev)) =
        (fun j : Fin n => basisVec (Fin.init w j.rev)) := by
      funext j
      change basisVec (w j.succ.rev) = basisVec (w j.rev.castSucc)
      rw [Fin.rev_succ]
    rw [ht] at hder
    simpa only [Fin.rev_zero] using hder.symm

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Comparison of pulse squares with the bare fast-profile squares. -/

noncomputable def pulseSquareSum (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t ^ 2

theorem ocPulse_eq_scaledProduct {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (k : ℤ) (t : ℝ) :
    ocPulse α q Λ ζ m k t = slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
      ζ (t / ocTau α q Λ m - k) := by
  unfold ocPulse
  congr 2
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  field_simp

theorem pulseSquareSum_eq_at_fast {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (t : ℝ) (k : {k : ℤ // Odd k})
    (hk : ζ (t / ocTau α q Λ m - k.1) ≠ 0) :
    pulseSquareSum α q Λ ζ m t = ocPulse α q Λ ζ m k.1 t ^ 2 := by
  unfold pulseSquareSum
  apply tsum_eq_single k
  intro j hj
  have hz : ζ (t / ocTau α q Λ m - j.1) = 0 := by
    by_contra hz
    exact hj (Subtype.ext (odd_fast_support_unique hζ j.2 k.2 hz hk))
  rw [ocPulse_eq_scaledProduct hΛ j.1 t, hz]
  simp

theorem pulseSquareSum_eq_zero_of_fast_quiet {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (t : ℝ)
    (hq : ∀ k : {k : ℤ // Odd k}, ζ (t / ocTau α q Λ m - k.1) = 0) :
    pulseSquareSum α q Λ ζ m t = 0 := by
  have hp (k : {k : ℤ // Odd k}) : ocPulse α q Λ ζ m k.1 t = 0 := by
    rw [ocPulse_eq_scaledProduct hΛ k.1 t, hq k, mul_zero]
  simp [pulseSquareSum, hp]

theorem pulseSquareSum_le_fast {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (t : ℝ) :
    0 ≤ pulseSquareSum α q Λ ζ m t ∧
      pulseSquareSum α q Λ ζ m t ≤ fastSquareSum ζ (ocTau α q Λ m) t := by
  by_cases he : ∃ k : {k : ℤ // Odd k}, ζ (t / ocTau α q Λ m - k.1) ≠ 0
  · obtain ⟨k, hk⟩ := he
    rw [pulseSquareSum_eq_at_fast hΛ hζ t k hk, fastSquareSum_eq_at_nonzero hζ _ _ k hk]
    have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k.1 t
    have hslow := slowEnvelope_range α q Λ m (ocLabel α q Λ m k.1) t
    have hz := hζ.2.2.2.1 (t / ocTau α q Λ m - k.1)
    have hle : ocPulse α q Λ ζ m k.1 t ≤ ζ (t / ocTau α q Λ m - k.1) := by
      rw [ocPulse_eq_scaledProduct hΛ k.1 t]
      exact (mul_le_mul_of_nonneg_right hslow.2 hz.1).trans_eq (one_mul _)
    exact ⟨sq_nonneg _, pow_le_pow_left₀ hp.1 hle 2⟩
  · have hq : ∀ k : {k : ℤ // Odd k}, ζ (t / ocTau α q Λ m - k.1) = 0 := by
      intro k
      by_contra hk
      exact he ⟨k, hk⟩
    rw [pulseSquareSum_eq_zero_of_fast_quiet hΛ t hq]
    exact ⟨le_rfl, (fastSquareSum_range hζ _ _).1⟩

theorem pulseSquareSum_intervalIntegrable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (a b : ℝ) :
    IntervalIntegrable (pulseSquareSum α q Λ ζ m) volume a b := by
  have hm : Measurable (pulseSquareSum α q Λ ζ m) :=
    Measurable.tsum (fun k => ((ocPulse_continuous hζ k.1).pow 2).measurable)
  apply intervalIntegrable_iff.mpr
  apply Measure.integrableOn_of_bounded (M := (1 : ℝ))
  · exact (lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) measure_Icc_lt_top).ne
  · exact hm.aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (pulseSquareSum_le_fast hΛ hζ t).1]
    exact (pulseSquareSum_le_fast hΛ hζ t).2.trans (fastSquareSum_range hζ _ _).2

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! Classical calculus for an isolated shear corrector. -/

theorem second_cosCoordinate (A ω : ℝ) (i r : Fin 2) (y : Vec 2) :
    fderiv ℝ (fun z => fderiv ℝ (fun x : Vec 2 => A * Real.cos (ω * x r))
      z (basisVec i)) y (basisVec i) =
      if i = r then -A * ω ^ 2 * Real.cos (ω * y r) else 0 := by
  have hfirst : (fun z => fderiv ℝ (fun x : Vec 2 => A * Real.cos (ω * x r))
      z (basisVec i)) = fun z =>
      if i = r then -A * ω * Real.sin (ω * z r) else 0 := by
    funext z
    exact AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate A ω r i z
  rw [hfirst]
  by_cases hir : i = r
  · subst i
    simp only [ite_true]
    have hproj := hasFDerivAt_apply (𝕜 := ℝ) r y
    have hlin := hproj.const_mul ω
    have hsin := (Real.hasDerivAt_sin (ω * y r)).comp_hasFDerivAt y hlin
    have hder := hsin.const_mul (-A * ω)
    have hdf : fderiv ℝ (fun z : Vec 2 => -A * ω * Real.sin (ω * z r)) y =
        (-A * ω) • Real.cos (ω * y r) • ω • ContinuousLinearMap.proj r := by
      simpa only [Function.comp_apply] using hder.fderiv
    rw [hdf]
    simp [basisVec, pow_two]
    ring
  · simp [hir]

theorem laplacian_cosCoordinate (A ω : ℝ) (r : Fin 2) (y : Vec 2) :
    (∑ i : Fin 2, fderiv ℝ
      (fun z => fderiv ℝ (fun x : Vec 2 => A * Real.cos (ω * x r)) z (basisVec i))
        y (basisVec i)) = -ω ^ 2 * (A * Real.cos (ω * y r)) := by
  simp_rw [second_cosCoordinate]
  rw [Finset.sum_ite_eq']
  simp
  ring

theorem pulseCorrector_laplacian {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {k : ℤ}
    (hk : Odd k) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, fderiv ℝ
      (fun z => fderiv ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k t x j)
        z (basisVec i)) y (basisVec i)) =
      -(2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 *
        ocPulseCorrector α q Λ ζ m ν k t y j := by
  rcases odd_int_mod_four hk with h1 | h3
  · obtain ⟨hf0, hf1⟩ := pulseCorrector_horizontal_components
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h1 ν t
    fin_cases j
    · change (∑ i : Fin 2, fderiv ℝ
        (fun z => fderiv ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k t x (0 : Fin 2))
          z (basisVec i)) y (basisVec i)) =
          -(2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 *
            ocPulseCorrector α q Λ ζ m ν k t y (0 : Fin 2)
      rw [hf0, congrFun hf0 y]
      simp
    · change (∑ i : Fin 2, fderiv ℝ
        (fun z => fderiv ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k t x (1 : Fin 2))
          z (basisVec i)) y (basisVec i)) =
          -(2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 *
            ocPulseCorrector α q Λ ζ m ν k t y (1 : Fin 2)
      rw [hf1, congrFun hf1 y]
      exact laplacian_cosCoordinate _ _ _ _
  · obtain ⟨hf0, hf1⟩ := pulseCorrector_vertical_components
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h3 ν t
    fin_cases j
    · change (∑ i : Fin 2, fderiv ℝ
        (fun z => fderiv ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k t x (0 : Fin 2))
          z (basisVec i)) y (basisVec i)) =
          -(2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 *
            ocPulseCorrector α q Λ ζ m ν k t y (0 : Fin 2)
      rw [hf0, congrFun hf0 y]
      exact laplacian_cosCoordinate _ _ _ _
    · change (∑ i : Fin 2, fderiv ℝ
        (fun z => fderiv ℝ (fun x => ocPulseCorrector α q Λ ζ m ν k t x (1 : Fin 2))
          z (basisVec i)) y (basisVec i)) =
          -(2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 *
            ocPulseCorrector α q Λ ζ m ν k t y (1 : Fin 2)
      rw [hf1, congrFun hf1 y]
      simp

theorem pulseCorrector_hasDerivAt {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ)
    (y : Vec 2) (j : Fin 2) :
    HasDerivAt (fun s => ocPulseCorrector α q Λ ζ m ν k s y j)
      (-(ocPulse α q Λ ζ m k t - ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k t) *
        ocShearVel α q Λ m k y j) t := by
  simpa [ocPulseCorrector] using
    ((ocPulseMemory_hasDerivAt hΛ hζ ν k t).neg.mul_const (ocShearVel α q Λ m k y j))

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Topology
open AVenhance.Infra.Torus
namespace AVRegularity.CycleReference

/-! Continuous measure-preserving chart maps on the quotient torus. -/

local instance torusChartLiftMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusChartLiftHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusChartLiftProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev ChartTorus := UnitAddTorus (Fin 2)

 theorem toUnitTorus_openQuotientMap : IsOpenQuotientMap (toUnitTorus 2) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

 theorem toUnitTorus_continuous : Continuous (toUnitTorus 2) :=
  toUnitTorus_openQuotientMap.continuous

noncomputable def torusChart {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (z : ChartTorus) : ChartTorus :=
  toUnitTorus 2 (AVRegularity.streamFlow φ hφ t (unitTorusRepresentative 2 z) s)

 theorem torusChart_coe {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (x : Vec 2) :
    torusChart hφ s t (toUnitTorus 2 x) =
      toUnitTorus 2 (AVRegularity.streamFlow φ hφ t x s) := by
  obtain ⟨k, hk⟩ := Basic.representative_int_translate x
  rw [torusChart, hk]
  change toUnitTorus 2 (AVRegularity.streamFlow φ hφ t (x + latticeShift k) s) = _
  rw [streamFlow_lattice_equivariant]
  funext i
  change ((AVRegularity.streamFlow φ hφ t x s i + (k i : ℝ) : ℝ) : UnitAddCircle) = _
  rw [AddCircle.coe_add]
  have hz : ((k i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k i, by simp⟩
  rw [hz, add_zero]
  rfl

 theorem torusChart_joint_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) :
    Continuous (fun p : ℝ × ChartTorus => torusChart hφ s p.1 p.2) := by
  apply ((IsOpenQuotientMap.id.prodMap toUnitTorus_openQuotientMap).isQuotientMap.continuous_iff).mpr
  have he : (fun p : ℝ × ChartTorus => torusChart hφ s p.1 p.2) ∘
      Prod.map id (toUnitTorus 2) =
      (fun p : ℝ × Vec 2 => toUnitTorus 2 (AVRegularity.streamFlow φ hφ p.1 p.2 s)) := by
    funext p
    exact torusChart_coe hφ s p.1 p.2
  rw [he]
  exact toUnitTorus_continuous.comp ((streamFlow_joint_smooth hφ).continuous.comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))

 theorem torusChart_inverse_joint_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) :
    Continuous (fun p : ℝ × ChartTorus => torusChart hφ p.1 s p.2) := by
  apply ((IsOpenQuotientMap.id.prodMap toUnitTorus_openQuotientMap).isQuotientMap.continuous_iff).mpr
  have he : (fun p : ℝ × ChartTorus => torusChart hφ p.1 s p.2) ∘
      Prod.map id (toUnitTorus 2) =
      (fun p : ℝ × Vec 2 => toUnitTorus 2 (AVRegularity.streamFlow φ hφ s p.2 p.1)) := by
    funext p
    exact torusChart_coe hφ p.1 s p.2
  rw [he]
  exact toUnitTorus_continuous.comp ((streamFlow_joint_smooth hφ).continuous.comp
    (continuous_const.prodMk (continuous_snd.prodMk continuous_fst)))

 theorem torusChart_inverse {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (z : ChartTorus) :
    torusChart hφ t s (torusChart hφ s t z) = z := by
  unfold torusChart
  rw [← torusChart, torusChart_coe]
  have hi := (streamFlowHomeomorph hφ t s).symm_apply_apply (unitTorusRepresentative 2 z)
  change AVRegularity.streamFlow φ hφ s
    (AVRegularity.streamFlow φ hφ t (unitTorusRepresentative 2 z) s) t =
    unitTorusRepresentative 2 z at hi
  rw [hi, toUnitTorus_unitTorusRepresentative]

 theorem torusChart_measurePreserving {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) :
    MeasurePreserving (torusChart hφ s t) (volume : Measure ChartTorus) volume := by
  have hc : Continuous (torusChart hφ s t) :=
    (torusChart_joint_continuous hφ s).comp (continuous_const.prodMk continuous_id)
  refine ⟨hc.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_fromUnitTorus_eq_unitCellAt (fun z => f (torusChart hφ s t z)) (fun _ => 0),
    integral_fromUnitTorus_eq_unitCellAt (fun z => f z) (fun _ => 0)]
  simp only [fromUnitTorus, torusChart_coe]
  rw [show unitCellAt 2 (fun _ => 0) = unitCell 2 from rfl]
  rw [integral_unitCell_eq_unitCube, integral_unitCell_eq_unitCube]
  apply streamFlow_cell_integral hφ t s (fun x => f (toUnitTorus 2 x))
  exact (isZdPeriodic_iff_frozen _).mp (isZdPeriodic_fromUnitTorus (fun z => f z))

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Diagonal flux gain and placement of terminal half-cores. -/

theorem slowEnvelope_one_inside_block {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    (l : ℤ) (t : ℝ) (ht : slowEnvelope α q Λ m l t = 1) :
    ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t ∧
      t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m := by
  have hP : 0 < ocTauP α q Λ m := by
    unfold ocTauP
    apply div_pos (AVRegularity.Construction.Stream.ocTauPP_pos hΛ)
    have hL : 0 < ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast hL
  constructor
  · by_contra h
    have hz : Real.smoothTransition
        ((t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) /
          ocTauP α q Λ m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hP.le)
    unfold slowEnvelope at ht
    rw [hz] at ht
    norm_num at ht
  · by_contra h
    have hz : Real.smoothTransition
        (((((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) - t) /
          ocTauP α q Λ m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hP.le)
    unfold slowEnvelope at ht
    rw [hz] at ht
    norm_num at ht

theorem refFlux_diagonal_molecular_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (t : ℝ) (i : Fin 2) :
    ν ≤ ocRefFlux α q Λ ζ m ν t i i := by
  have h := refFlux_qform_molecular_lower (α := α) (q := q) (m := m) hΛ hζ hν t (Pi.single i 1)
  fin_cases i <;> simpa [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.single_apply] using h

theorem refFlux_diagonal_core_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (l k : ℤ) (hcore : IsOCCompleteCore α q Λ m l k)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (t : ℝ)
    (ht : t ∈ Set.Icc ((k : ℝ) * ocTau α q Λ m)
      (((k : ℝ) + 1 / 3) * ocTau α q Λ m)) (i : Fin 2)
    (hi : (i = 1 ∧ k % 4 = 1) ∨ (i = 0 ∧ k % 4 = 3)) :
    ν + ocHStar α q Λ m ν * (1 - Real.exp (-2)) ≤
      ocRefFlux α q Λ ζ m ν t i i := by
  have h := refFlux_core_qform_lower hΛ hζ hν l k hcore hrelax t ht (Pi.single i 1)
  rcases hi with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
  · simpa [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply, hk] using h
  · have hk' : k % 4 ≠ 1 := by omega
    simpa [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply, hk'] using h

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Trace approximation by instantaneous pulse squares. -/

theorem pulseSquareSum_eq_at_active {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (t : ℝ) (k : {k : ℤ // Odd k})
    (hk : ocPulse α q Λ ζ m k.1 t ≠ 0) :
    pulseSquareSum α q Λ ζ m t = ocPulse α q Λ ζ m k.1 t ^ 2 := by
  unfold pulseSquareSum
  apply tsum_eq_single k
  intro j hj
  have hp : ocPulse α q Λ ζ m j.1 t = 0 := by
    by_contra hp
    exact hj (Subtype.ext (odd_pulse_support_unique hΛ hζ j.2 k.2 hp hk))
  simp [hp]

theorem refFlux_trace_at_active {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (k : {k : ℤ // Odd k})
    (hk : ocPulse α q Λ ζ m k.1 t ≠ 0) :
    Matrix.trace (ocRefFlux α q Λ ζ m ν t) = 2 * ν +
      ocMu q Λ m ν * ocHStar α q Λ m ν *
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) := by
  unfold ocRefFlux
  rw [pulseMatrixSum_eq_at_active hΛ hζ ν t k hk, smul_smul]
  by_cases hmod : k.1 % 4 = 1 <;>
    simp [Matrix.trace, Fin.sum_univ_two, ocPi, hmod] <;> ring

theorem refFlux_trace_instantaneous_error {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ ν : ℝ, 0 < ν → ∀ t : ℝ,
      |Matrix.trace (ocRefFlux α q Λ ζ m ν t) - 2 * ν -
        ocHStar α q Λ m ν * pulseSquareSum α q Λ ζ m t| ≤
          ocHStar α q Λ m ν * (K / (ocMu q Λ m ν * ocTau α q Λ m)) := by
  obtain ⟨K, hK, herror⟩ := pulse_memory_instantaneous_error hζ
  refine ⟨K, hK, ?_⟩
  intro α q Λ m hΛ ν hν t
  have hH := ocHStar_pos (α := α) (q := q) (m := m) hΛ hν
  have hμ := ocMu_pos (q := q) (m := m) hΛ hν
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  by_cases he : ∃ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t ≠ 0
  · obtain ⟨k, hk⟩ := he
    rw [refFlux_trace_at_active hΛ hζ ν t k hk, pulseSquareSum_eq_at_active hΛ hζ t k hk]
    have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k.1 t
    have herr := herror α q Λ m hΛ ν hν k.1 t
    calc
      _ = ocHStar α q Λ m ν * ocPulse α q Λ ζ m k.1 t *
          |ocPulse α q Λ ζ m k.1 t - ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t| := by
        rw [show 2 * ν + ocMu q Λ m ν * ocHStar α q Λ m ν *
            (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) - 2 * ν -
            ocHStar α q Λ m ν * ocPulse α q Λ ζ m k.1 t ^ 2 =
            -(ocHStar α q Λ m ν * ocPulse α q Λ ζ m k.1 t) *
              (ocPulse α q Λ ζ m k.1 t - ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t) by ring,
          abs_mul, abs_neg, abs_of_nonneg (mul_nonneg hH.le hp.1)]
      _ ≤ ocHStar α q Λ m ν * (K / (ocMu q Λ m ν * ocTau α q Λ m)) := by
        have hHp : ocHStar α q Λ m ν * ocPulse α q Λ ζ m k.1 t ≤ ocHStar α q Λ m ν := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hp.2 hH.le
        exact mul_le_mul hHp herr (abs_nonneg _) hH.le
  · have hp (k : {k : ℤ // Odd k}) : ocPulse α q Λ ζ m k.1 t = 0 := by
      by_contra hk
      exact he ⟨k, hk⟩
    have hflux : ocRefFlux α q Λ ζ m ν t = ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      unfold ocRefFlux
      rw [pulseMatrixSum_eq_zero_of_quiet ν t hp]
      simp
    rw [hflux]
    have hs : pulseSquareSum α q Λ ζ m t = 0 := by simp [pulseSquareSum, hp]
    rw [hs]
    have ht : Matrix.trace (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 2 * ν := by
      rw [Matrix.trace_smul, Matrix.trace_one]
      norm_num
      ring
    rw [ht]
    simp only [sub_self, mul_zero, abs_zero]
    exact mul_nonneg hH.le (div_nonneg hK (mul_pos hμ hτ).le)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleReference

/-! Coordinate extraction from Jacobian derivative bounds. -/

theorem jacMatrix_entry_smooth {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => jacMatrix f x i j) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (basisVec j)) :=
    hd.clm_apply contDiff_const
  exact (contDiff_apply ℝ ℝ i).comp he

theorem iteratedFDeriv_jacMatrix_entry {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (w : Fin n → Fin 2) (x : Vec 2) (i a : Fin 2) :
    iteratedFDeriv ℝ n (fun y => jacMatrix f y i a) x (fun j => basisVec (w j)) =
      iteratedFDeriv ℝ (n + 1) f x (Fin.snoc (fun j => basisVec (w j)) (basisVec a)) i := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (basisVec a)) :=
    hd.clm_apply contDiff_const
  have hproj := (ContinuousLinearMap.proj i : (Vec 2) →L[ℝ] ℝ).iteratedFDeriv_comp_left
    he.contDiffAt (i := n) (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞)) (x := x)
  have heval := congrArg (fun M => M (fun j => basisVec (w j))) hproj
  change iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (basisVec a) i) x _ = _
  simp only [Function.comp_def, ContinuousLinearMap.proj_apply] at heval
  rw [heval]
  change (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (basisVec a)) x
    (fun j => basisVec (w j))) i = _
  rw [iteratedFDeriv_clm_apply_const_apply hd (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞))]
  rw [iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc, Fin.snoc_last]

end AVRegularity.CycleReference
end
end
end

section
@[expose] public section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Algebra of the tested equation after the material chain rule. -/

theorem material_integrand_algebra (F : Matrix (Fin 2) (Fin 2) ℝ)
    (hF : IsUnit F.det) (θ η ηt ν f : ℝ) (D b b₀ q g : Vec 2) :
    -θ * (ηt + vecDot g b₀) +
      vecDot (F⁻¹.mulVec (b - b₀)) (Fᵀ.mulVec D) * η +
      vecDot ((ν • (F⁻¹ * (F⁻¹)ᵀ)).mulVec (Fᵀ.mulVec D)) (Fᵀ.mulVec g) +
      vecDot (F⁻¹.mulVec q) (Fᵀ.mulVec g) - f * η =
    (-θ * ηt + vecDot b D * η + vecDot ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec D) g +
      vecDot q g - f * η) - (θ * vecDot b₀ g + vecDot b₀ D * η) := by
  rw [inverse_pullback_pairing F hF, inverse_pullback_pairing F hF]
  have he : vecDot ((ν • (F⁻¹ * (F⁻¹)ᵀ)).mulVec (Fᵀ.mulVec D)) (Fᵀ.mulVec g) =
      ν * vecDot D g := by
    rw [Matrix.smul_mulVec]
    change dotProduct (ν • _) _ = _
    rw [smul_dotProduct]
    change ν * vecDot _ _ = _
    rw [metric_pullback_pairing F hF]
  rw [he, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [vecDot, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end AVRegularity.CycleReference
end
end
