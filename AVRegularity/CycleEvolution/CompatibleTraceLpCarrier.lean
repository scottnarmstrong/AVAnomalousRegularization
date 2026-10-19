-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

section
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace AVRegularity.CycleEvolution

/-! Local analytic inversion of an actual bounded operator perturbation vanishing at its base point. -/

variable {X A : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem analyticOperatorPerturbation_inverse {T : X → A} {x : X}
    (hT : AnalyticAt ℂ T x) (hzero : T x = 0) :
    AnalyticAt ℂ (fun y => Ring.inverse (1 - T y)) x := by
  have hi := analyticAt_inverse_one_sub ℂ A
  rw [← hzero] at hi
  exact hi.comp hT

theorem analyticOperatorPerturbation_eventually_isUnit {T : X → A} {x : X}
    (hT : AnalyticAt ℂ T x) (hzero : T x = 0) :
    ∀ᶠ y in 𝓝 x, IsUnit (1 - T y) := by
  have hn : ∀ᶠ y in 𝓝 x, ‖T y‖ < 1 := by
    have h := hT.continuousAt.norm
    change Tendsto (fun y => ‖T y‖) (𝓝 x) (𝓝 ‖T x‖) at h
    rw [hzero, norm_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  exact hn.mono (fun _ h => isUnit_one_sub_of_norm_lt_one h)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Pascal's identity in the finite derivative convolution, abstracted from all cell analysis. -/

/-- The two differentiated factors combine to the next binomial derivative convolution. -/
theorem binomialConvolution_step {M : Type*} [AddCommMonoid M]
    (u : ℕ → ℕ → M) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), n.choose i • u (i + 1) (n - i)) +
      (∑ i ∈ Finset.range (n + 1), n.choose i • u i (n - i + 1)) =
      ∑ i ∈ Finset.range (n + 2), (n + 1).choose i • u i (n + 1 - i) := by
  have hR : (∑ i ∈ Finset.range (n + 2), (n + 1).choose i • u i (n + 1 - i)) =
      (∑ i ∈ Finset.range (n + 1), n.choose i • u (i + 1) (n - i)) +
      (∑ i ∈ Finset.range (n + 1), n.choose (i + 1) • u (i + 1) (n - i)) + u 0 (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ', add_nsmul, Finset.sum_add_distrib,
      Nat.add_sub_add_right, Nat.choose_zero_right, Nat.sub_zero, one_nsmul]
  have hshift : (∑ i ∈ Finset.range (n + 1), n.choose (i + 1) • u (i + 1) (n - i)) =
      ∑ i ∈ Finset.range n, n.choose (i + 1) • u (i + 1) (n - i) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.choose_succ_self, zero_nsmul, add_zero]
  have hL : (∑ i ∈ Finset.range (n + 1), n.choose i • u i (n - i + 1)) =
      (∑ i ∈ Finset.range n, n.choose (i + 1) • u (i + 1) (n - i)) + u 0 (n + 1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, one_nsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show n - (i + 1) + 1 = n - i by omega]
  rw [hR, hshift, hL, add_assoc]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Finite array norm budgets abstracted before the periodic Hilbert subtype is introduced. -/

/-- The L2 finite-array norm is bounded by the sum of its component norms. -/
theorem cellFiniteArray_enorm_le_sum {J E : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] (u : PiLp 2 (fun _ : J => E)) :
    ‖u‖ₑ ≤ ∑ j, ‖u j‖ₑ := by
  have he : u = ∑ j, (PiLp.single 2 j (u j) : PiLp 2 (fun _ : J => E)) := by
    apply PiLp.ext
    intro j
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
    simp
  calc
    _ = ‖∑ j, (PiLp.single 2 j (u j) : PiLp 2 (fun _ : J => E))‖ₑ :=
      congrArg (fun v : PiLp 2 (fun _ : J => E) => ‖v‖ₑ) he
    _ ≤ ∑ j, ‖(PiLp.single 2 j (u j) : PiLp 2 (fun _ : J => E))‖ₑ :=
      enorm_sum_le Finset.univ (fun j : J => (PiLp.single 2 j (u j) : PiLp 2 (fun _ : J => E)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [← ofReal_norm, PiLp.norm_single]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open Filter Function Set
open scoped Topology
namespace AVRegularity.CycleEvolution

/-! Sequential weak compactness for bounded sequences in separable real Hilbert spaces. -/

/-- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence whose inner products converge against every test vector. -/
theorem cellHilbert_weak_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ z : H,
        Tendsto (fun n => inner ℝ (u (φ n)) z) atTop
          (𝓝 (inner ℝ v z)) := by
  let f : ℕ → WeakDual ℝ H := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
  have hf : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ H) R := by
    intro n
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    change ‖InnerProductSpace.toDual ℝ H (u n) - 0‖ ≤ R
    simpa using hu n
  obtain ⟨ℓ, hℓ, φ, hφ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) R) hf
  let v : H :=
    (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ℓ)
  refine ⟨v, φ, hφ, fun z => ?_⟩
  simpa [f, v, Function.comp_def] using
    ((WeakDual.eval_continuous z).tendsto ℓ).comp hlim

/-- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence converging against every continuous linear functional. -/
theorem cellHilbert_weak_subsequence_clm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : H →L[ℝ] ℝ,
        Tendsto (fun n => ell (u (φ n))) atTop (𝓝 (ell v)) := by
  obtain ⟨v, φ, hφ, hinner⟩ := cellHilbert_weak_subsequence u R hu
  refine ⟨v, φ, hφ, fun ell => ?_⟩
  let z := (InnerProductSpace.toDual ℝ H).symm ell
  simp_rw [← InnerProductSpace.toDual_symm_apply]
  simpa only [z, real_inner_comm] using hinner z

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Bounded complex multiplication on arbitrary product L2 spaces. -/

/-- Bounded almost measurable multipliers preserve genuine L2 fields on arbitrary measure spaces. -/
theorem cellL2_bounded_multiplier_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (b f : X → ℂ) (B : ℝ)
    (hb : AEStronglyMeasurable b μ) (hB : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (hf : MemLp f 2 μ) :
    MemLp (fun x => b x * f x) 2 μ := by
  have hm := hb.mul hf.aestronglyMeasurable
  have he : eLpNorm (fun x => b x * f x) 2 μ ≤ ENNReal.ofReal B * eLpNorm f 2 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm _ 2
    filter_upwards [hB] with x hx
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  exact he.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Transfer joint almost-everywhere statements from integer unit windows to all time. -/

/-- A joint property true almost everywhere in each integer time window is true almost everywhere globally. -/
theorem cellProduct_ae_of_integer_windows {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (P : ℝ × X → Prop)
    (hP : ∀ n : ℤ, ∀ᵐ p ∂(volume.restrict (Set.Icc (n : ℝ) ((n : ℝ) + 1))).prod μ, P p) :
    ∀ᵐ p ∂volume.prod μ, P p := by
  have hall : ∀ᵐ p ∂volume.prod μ, ∀ n : ℤ,
      p.1 ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) → P p := by
    apply ae_all_iff.mpr
    intro n
    have hn := hP n
    rw [Measure.restrict_prod_eq_prod_univ] at hn
    simpa only [Set.mem_prod, Set.mem_univ, and_true] using
      (ae_restrict_iff' (measurableSet_Icc.prod MeasurableSet.univ)).mp hn
  filter_upwards [hall] with p hp
  exact hp ⌊p.1⌋ ⟨Int.floor_le p.1, (Int.lt_floor_add_one p.1).le⟩

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Literal time reflection preserves the corresponding closed-interval volume measures. -/

theorem cellTimeReverse_measurePreserving_Icc (a b : ℝ) :
    MeasurePreserving (fun t : ℝ => -t) (volume.restrict (Icc (-b) (-a))) (volume.restrict (Icc a b)) := by
  have he : (fun t : ℝ => -t) ⁻¹' Icc a b = Icc (-b) (-a) := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simpa only [he] using (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Icc : MeasurableSet (Icc a b))

theorem cellTimeReverse_memLp {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f : ℝ → E} {p : ℝ≥0∞} (hf : MemLp f p (volume.restrict (Icc a b))) :
    MemLp (fun t => f (-t)) p (volume.restrict (Icc (-b) (-a))) :=
  hf.comp_measurePreserving (cellTimeReverse_measurePreserving_Icc a b)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Transfer almost-everywhere time statements from the countable unit-window cover. -/

/-- A property holding almost everywhere on each integral unit window holds on all time. -/
theorem cellTime_ae_of_integer_windows (P : ℝ → Prop)
    (hP : ∀ n : ℤ, ∀ᵐ t ∂volume.restrict (Set.Icc (n : ℝ) ((n : ℝ) + 1)), P t) :
    ∀ᵐ t ∂volume, P t := by
  have hall : ∀ᵐ t ∂volume, ∀ n : ℤ,
      t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) → P t :=
    ae_all_iff.mpr (fun n => (ae_restrict_iff' measurableSet_Icc).mp (hP n))
  filter_upwards [hall] with t ht
  exact ht ⌊t⌋ ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! A complete linear carrier matching a continuous Hilbert trace to its Bochner spatial state. -/

variable {X V H : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

def compatibleTraceLpMismatch (μ : Measure X) [IsFiniteMeasure μ] (ι : V →L[ℂ] H) :
    C(X, H) × Lp V 2 μ →L[ℂ] Lp H 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).comp (ContinuousLinearMap.fst ℂ C(X, H) (Lp V 2 μ)) -
    (ι.compLpL 2 μ).comp (ContinuousLinearMap.snd ℂ C(X, H) (Lp V 2 μ))

def compatibleTraceLpSpace (μ : Measure X) [IsFiniteMeasure μ] (ι : V →L[ℂ] H) :
    Submodule ℂ (C(X, H) × Lp V 2 μ) := (compatibleTraceLpMismatch μ ι).ker

abbrev CompatibleTraceLp (μ : Measure X) [IsFiniteMeasure μ] (ι : V →L[ℂ] H) :=
  ↥(compatibleTraceLpSpace μ ι)

instance compatibleTraceLp_complete (μ : Measure X) [IsFiniteMeasure μ]
    [CompleteSpace V] [CompleteSpace H] (ι : V →L[ℂ] H) :
    CompleteSpace (CompatibleTraceLp μ ι) :=
  completeSpace_coe_iff_isComplete.mpr (compatibleTraceLpMismatch μ ι).isComplete_ker

theorem compatibleTraceLp_mem_iff (μ : Measure X) [IsFiniteMeasure μ] (ι : V →L[ℂ] H)
    (u : C(X, H) × Lp V 2 μ) :
    u ∈ compatibleTraceLpSpace μ ι ↔ ContinuousMap.toLp 2 μ ℂ u.1 = ι.compLpL 2 μ u.2 := by
  change ContinuousMap.toLp 2 μ ℂ u.1 - ι.compLpL 2 μ u.2 = 0 ↔ _
  exact sub_eq_zero

theorem compatibleTraceLp_agrees (μ : Measure X) [IsFiniteMeasure μ] (ι : V →L[ℂ] H)
    (u : CompatibleTraceLp μ ι) : ∀ᵐ x ∂μ, u.val.1 x = ι (u.val.2 x) := by
  have heq := (compatibleTraceLp_mem_iff μ ι u.val).mp u.property
  have ht := ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ) u.val.1
  have hs := ι.coeFn_compLpL u.val.2
  rw [heq] at ht
  filter_upwards [ht, hs] with x hx hy
  exact hx.symm.trans hy

end AVRegularity.CycleEvolution
end
end
