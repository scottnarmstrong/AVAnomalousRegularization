-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.JointDiagonalChainRule
import AVRegularity.CoupledEnergy.Variational.FactorialPairing
import AVRegularity.EntryWeak.SobolevCellFourier
public import AVRegularity.EntryWeak.JointSourceCongruence
import AVRegularity.CycleReference.CoreFlux
public import AVRegularity.CycleEvolution.FibreScalarSeriesHighIncrementBound
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public section
namespace AVRegularity.WeakEntryProofs

/-! Literal finite-list identities for the ordered-word time-dependent forcing sums. -/

theorem window_list_sum_apply {I X E : Type*} [AddCommMonoid E]
    (l : List I) (f : I → X → E) (x : X) :
    ((l.map f).sum) x = (l.map (fun i => f i x)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]

theorem window_list_sum_sub {I E : Type*} [AddCommGroup E]
    (l : List I) (f g : I → E) :
    (l.map f).sum - (l.map g).sum = (l.map (fun i => f i - g i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, sub_self]
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    abel

theorem window_list_sum_quotient {I E : Type*} [AddCommGroup E] [Module ℝ E]
    (l : List I) (f g h : I → E) (r : ℝ) :
    r • ((l.map f).sum - (l.map g).sum) - (l.map h).sum =
      (l.map (fun i => r • (f i - g i) - h i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, sub_self, smul_zero]
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [show f i + (l.map f).sum - (g i + (l.map g).sum) =
      (f i - g i) + ((l.map f).sum - (l.map g).sum) by abel, smul_add, ← ih]
    abel

/-! Positive changes of cell clock preserve finite-window integrability and almost-everywhere identities. -/

section
open MeasureTheory
open scoped ENNReal

theorem map_window_mul (a b c : ℝ) (hc : 0 < c) :
    Measure.map (fun t : ℝ => c * t) (volume.restrict (Set.Icc a b)) =
      ENNReal.ofReal |c⁻¹| • volume.restrict (Set.Icc (c * a) (c * b)) := by
  have hpre : (fun t : ℝ => c * t) ⁻¹' Set.Icc (c * a) (c * b) = Set.Icc a b := by
    ext t
    change (c * a ≤ c * t ∧ c * t ≤ c * b) ↔ (a ≤ t ∧ t ≤ b)
    rw [mul_le_mul_iff_right₀ hc, mul_le_mul_iff_right₀ hc]
  rw [← hpre, ← Measure.restrict_map (show Measurable (fun t : ℝ => c * t) from measurable_const.mul measurable_id) measurableSet_Icc,
    Real.map_volume_mul_left hc.ne', Measure.restrict_smul]

theorem memLp_window_comp_mul {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p : ℝ≥0∞} (a b c : ℝ) (hc : 0 < c)
    (hf : MemLp f p (volume.restrict (Set.Icc (c * a) (c * b)))) :
    MemLp (fun t => f (c * t)) p (volume.restrict (Set.Icc a b)) := by
  have hh := hf.smul_measure (c := ENNReal.ofReal |c⁻¹|) ENNReal.ofReal_ne_top
  rw [← map_window_mul a b c hc] at hh
  exact hh.comp_of_map (measurable_const.mul measurable_id).aemeasurable

theorem ae_window_comp_mul {P : ℝ → Prop} (a b c : ℝ) (hc : 0 < c)
    (hP : ∀ᵐ t ∂volume.restrict (Set.Icc (c * a) (c * b)), P t) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), P (c * t) := by
  have hq : Measure.QuasiMeasurePreserving (fun t : ℝ => c * t)
      (volume.restrict (Set.Icc a b)) (volume.restrict (Set.Icc (c * a) (c * b))) := by
    refine ⟨measurable_const.mul measurable_id, ?_⟩
    rw [map_window_mul a b c hc]
    exact Measure.smul_absolutelyContinuous
  exact hq.ae hP
end

/-! The finite weak passage budget increases root mass by at most four thirds. -/

theorem weakMass_budget_denominator (J : ℕ) (hJ : 1 ≤ J) :
    (3 / 4 : ℝ) ≤ (1 - 1 / (4 * (J : ℝ))) ^ J := by
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hj0 : (J : ℝ) ≠ 0 := by exact_mod_cast (by omega : J ≠ 0)
  have ht : 1 / (4 * (J : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith only [hj]
  have hb := one_add_mul_le_pow (a := -(1 / (4 * (J : ℝ))))
    (by linarith only [ht] : -(2 : ℝ) ≤ -(1 / (4 * (J : ℝ)))) J
  calc
    (3 / 4 : ℝ) = 1 + (J : ℝ) * (-(1 / (4 * (J : ℝ)))) := by field_simp; ring
    _ ≤ (1 + -(1 / (4 * (J : ℝ)))) ^ J := hb
    _ = _ := by rw [sub_eq_add_neg]

 theorem weakMass_budget_price (J : ℕ) (hJ : 1 ≤ J) :
    (1 / 2 : ℝ) * (1 / (1 - 1 / (4 * (J : ℝ)))) ^ J ≤ 2 / 3 := by
  have hd := weakMass_budget_denominator J hJ
  rw [one_div_pow]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 4) hd
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
    (by norm_num)

/-! Joint measurability and finite energy survive a positive clock change. -/

section
open MeasureTheory
open scoped ENNReal

theorem window_mul_quasiMeasurePreserving (a b c : ℝ) (hc : 0 < c) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => c * t)
      (volume.restrict (Set.Icc a b)) (volume.restrict (Set.Icc (c * a) (c * b))) := by
  refine ⟨measurable_const.mul measurable_id, ?_⟩
  rw [map_window_mul a b c hc]
  exact Measure.smul_absolutelyContinuous

theorem window_prod_comp_mul_aestronglyMeasurable {E Z : Type*}
    [NormedAddCommGroup E] [MeasurableSpace Z] (μ : Measure Z) [SFinite μ]
    (a b c : ℝ) (hc : 0 < c) (f : ℝ × Z → E)
    (hf : AEStronglyMeasurable f
      ((volume.restrict (Set.Icc (c * a) (c * b))).prod μ)) :
    AEStronglyMeasurable (fun p : ℝ × Z => f (c * p.1, p.2))
      ((volume.restrict (Set.Icc a b)).prod μ) := by
  exact hf.comp_quasiMeasurePreserving
    (MeasureTheory.QuasiMeasurePreserving.prodMap
      (window_mul_quasiMeasurePreserving a b c hc) (Measure.QuasiMeasurePreserving.id μ))

theorem lintegral_window_comp_mul_lt_top (a b c : ℝ) (hc : 0 < c)
    (f : ℝ → ℝ≥0∞) (hf : ∫⁻ t in Set.Icc (c * a) (c * b), f t < ⊤) :
    ∫⁻ t in Set.Icc a b, f (c * t) < ⊤ := by
  have he := (Homeomorph.mulLeft₀ c hc.ne').measurableEmbedding.lintegral_map
    (μ := volume.restrict (Set.Icc a b)) f
  change (∫⁻ t, f t ∂Measure.map (fun t : ℝ => c * t) (volume.restrict (Set.Icc a b))) =
    ∫⁻ t in Set.Icc a b, f (c * t) at he
  rw [map_window_mul a b c hc, lintegral_smul_measure] at he
  rw [← he]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf
end

/-! Finite full-cell ranks leave enough reserve for calibration and the genuine inverse. -/

section
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift

def weakLiftRankReserve (D base N height hh n : ℕ) : ℕ :=
  weakJointRecurrenceReserve (4 * (N + D + 6)) base
    (ambientRecurrenceRank N height N) (ambientRecurrenceRank N hh n)

theorem weakLiftRankReserve_base (D base N height hh n : ℕ) :
    base + 1 ≤ weakLiftRankReserve D base N height hh n :=
  weakJointRecurrenceReserve_base _ _ _ _ (by omega)

theorem weakLiftRankReserve_source_room (D base N height hh n p q : ℕ)
    (hhh : hh ≤ height) (hn : n ≤ N) (hq : q ≤ N)
    (hpre : p < hh ∨ (p = hh ∧ q < n)) :
    (4 * weakLiftRankReserve D base N height hh n + 5) + N + D + 2 ≤
      weakLiftRankReserve D base N height p q := by
  have hr : ambientRecurrenceRank N hh n ≤ ambientRecurrenceRank N height N := by
    unfold ambientRecurrenceRank
    have hm := Nat.mul_le_mul_right (N + 1) hhh
    omega
  have hp : ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n := by
    rcases hpre with hp | ⟨rfl, hq'⟩
    · exact ambientRecurrenceRank_height N hh n p q hp hq
    · unfold ambientRecurrenceRank
      omega
  have h := weakJointRecurrenceReserve_inverse_room base (N + D + 2)
    (ambientRecurrenceRank N height N) (ambientRecurrenceRank N hh n)
    (ambientRecurrenceRank N p q) hr hp
  simpa only [weakLiftRankReserve, show N + D + 2 + 4 = N + D + 6 by omega,
    show ∀ R : ℕ, 4 * R + (N + D + 2) + 5 = (4 * R + 5) + N + D + 2 by omega] using h
end

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! A scalar linear cell response commutes with the finite coefficient action at a fixed slow point. -/

open Homogenization AVRegularity.Sobolev

variable {ι : Type*} [Fintype ι]

def respondedScalarLiftCoeff
    (R : Vec 2 → (ℝ → Vec 2 → ℝ) →ₗ[ℝ] (ℝ → Vec 2 → ℝ))
    (B : LiftCoeff ι (fun _ => ℝ)) : LiftCoeff ι (fun _ => ℝ) :=
  fun m α t X z v u => R X (fun s y => B m α s X y v u 1) t z • ContinuousLinearMap.id ℝ ℝ

theorem respondedScalarLiftCoeff_apply
    (R : Vec 2 → (ℝ → Vec 2 → ℝ) →ₗ[ℝ] (ℝ → Vec 2 → ℝ))
    (B : LiftCoeff ι (fun _ => ℝ)) (n : ℕ) (a₀ : Vec 2 → ι → ℝ)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n (respondedScalarLiftCoeff R B) (fun _ => a₀) t X z v =
      R X (fun s y => liftApply n B (fun _ => a₀) s X y v) t z := by
  classical
  have he (m : ℕ) (α : DerivativeWord2 m) (u : ι) (s : ℝ) (y : Vec 2) :
      B m α s X y v u (orderedDerivative α a₀ X u) =
        orderedDerivative α a₀ X u * B m α s X y v u 1 := by
    simpa only [smul_eq_mul, mul_one] using
      map_smul (B m α s X y v u) (orderedDerivative α a₀ X u) (1 : ℝ)
  have hsrc : (fun s y => liftApply n B (fun _ => a₀) s X y v) =
      ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u : ι,
        (orderedDerivative α a₀ X u) • (fun s y => B m α s X y v u 1) := by
    funext s y
    simp only [liftApply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, he]
  rw [hsrc]
  simp only [liftApply, respondedScalarLiftCoeff, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro α _hα
  apply Finset.sum_congr rfl
  intro u _hu
  exact mul_comm _ _

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public section
namespace AVRegularity.WeakEntryProofs

/-! Finite response-word counting, without any assumption on the response depth. -/

 theorem length_of_mem_wordsOfLength (A : Finset WordLetter) (n : ℕ)
    {w : List WordLetter} (hw : w ∈ wordsOfLength A n) : w.length = n := by
  induction n generalizing w with
  | zero =>
      have he : w = [] := Finset.mem_singleton.mp hw
      exact congrArg List.length he
  | succ n ih =>
      obtain ⟨⟨a, v⟩, hav, rfl⟩ := Finset.mem_image.mp hw
      have hv := (Finset.mem_product.mp hav).2
      simp only [List.length_append, List.length_singleton, ih hv]

 theorem card_wordsOfLength_le (A : Finset WordLetter) (n : ℕ) :
    (wordsOfLength A n).card ≤ A.card ^ n := by
  induction n with
  | zero => simp only [wordsOfLength, Finset.card_singleton, pow_zero, le_refl]
  | succ n ih =>
      calc
        (wordsOfLength A (n + 1)).card ≤ (A ×ˢ wordsOfLength A n).card :=
          Finset.card_image_le
        _ = A.card * (wordsOfLength A n).card := Finset.card_product _ _
        _ ≤ A.card * A.card ^ n := Nat.mul_le_mul_left _ ih
        _ = A.card ^ (n + 1) := (pow_succ' _ _).symm

 theorem sum_word_weight_le (A : Finset WordLetter) (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∑ w ∈ wordsOfLength A n, r ^ w.length ≤ (A.card : ℝ) ^ n * r ^ n := by
  have he : ∑ w ∈ wordsOfLength A n, r ^ w.length =
      ((wordsOfLength A n).card : ℝ) * r ^ n := by
    calc
      _ = ∑ _w ∈ wordsOfLength A n, r ^ n :=
        Finset.sum_congr rfl (fun _ hw => congrArg (fun k => r ^ k)
          (length_of_mem_wordsOfLength A n hw))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr n)
  exact_mod_cast card_wordsOfLength_le A n

theorem sum_wordsUpTo_weight_le (A : Finset WordLetter) (R : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∑ w ∈ wordsUpTo A R, r ^ w.length ≤
      ∑ n ∈ Finset.Icc 1 R, (A.card : ℝ) ^ n * r ^ n := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.Icc 1 R : Finset ℕ)) (wordsOfLength A) := by
    intro i _hi j _hj hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    exact hij ((length_of_mem_wordsOfLength A i hwi).symm.trans
      (length_of_mem_wordsOfLength A j hwj))
  rw [wordsUpTo, Finset.sum_biUnion hd]
  exact Finset.sum_le_sum (fun n _ => sum_word_weight_le A n r hr)

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Smooth spacetime data have finite slow jet budgets on compact time and parameter sets. -/

open Homogenization Set AVRegularity.EntryWeakProofs
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem spacetime_slow_jet_norm_le (f : ℝ × Vec d → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (t : ℝ) (Y : Vec d) :
    ‖iteratedFDeriv ℝ n (fun X => f (t, X)) Y‖ ≤ ‖iteratedFDeriv ℝ n f (t, Y)‖ := by
  have hh := finite_realWordJet_affine_derivative_bound f 0 n (hf.of_le (by simp))
    (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
    (ContinuousLinearMap.inr ℝ ℝ (Vec d)) (ContinuousLinearMap.norm_inr_le_one ℝ ℝ (Vec d))
    (t, 0) Y
  rw [Nat.zero_add] at hh
  simpa only [realWordJet, iteratedFDeriv_zero_apply, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, zero_add, add_zero] using hh

theorem compact_spacetime_slow_jet_budget (f : ℝ × Vec d → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : ℝ) (S : Set (Vec d)) (hS : IsCompact S) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ n t, t ∈ Icc a b → ∀ Y ∈ S,
      ‖iteratedFDeriv ℝ n (fun X => f (t, X)) Y‖ ≤ B n := by
  have hb (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ Y ∈ S,
      ‖iteratedFDeriv ℝ n (fun X => f (t, X)) Y‖ ≤ B := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod hS).exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedFDeriv (m := n) (by simp) hf).continuousOn
    refine ⟨max M 0, le_max_right _ _, fun t ht Y hY => ?_⟩
    exact (spacetime_slow_jet_norm_le f hf n t Y).trans ((hM (t, Y) ⟨ht, hY⟩).trans (le_max_left _ _))
  choose B hB hb using hb
  exact ⟨B, hB, hb⟩

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public section
namespace AVRegularity.WeakEntryProofs

/-! A bounded increasing rank excludes paths longer than its bound. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem family_hasDepthAtMost_of_rank (F : ChartedFamily ι h D P Ctx)
    (rank : ι → ℕ) (H : ℕ) (hb : ∀ v, rank v ≤ H)
    (he : ∀ v u, F.Γ v u → rank u < rank v) : F.HasDepthAtMost H := by
  classical
  intro p
  by_contra hn
  have hedge : ∀ k : Fin (H + 1), Nonempty (F.Γ (p k.succ) (p k.castSucc)) := by
    intro k
    exact not_isEmpty_iff.mp (fun hk => hn ⟨k, hk⟩)
  have main : ∀ n (hn : n ≤ H + 1), n ≤ rank (p ⟨n, by omega⟩) := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
        intro hns
        have hprev := ih (by omega)
        obtain ⟨γ⟩ := hedge ⟨n, by omega⟩
        have hs := he (p ⟨n + 1, by omega⟩) (p ⟨n, by omega⟩) γ
        omega
  have hl := main (H + 1) le_rfl
  have hu := hb (p ⟨H + 1, by omega⟩)
  omega

end AVRegularity.WeakEntryProofs
end
end

section
public noncomputable section
open MeasureTheory Set
namespace AVRegularity.WeakEntryProofs

/-! The carrier-independent positive-order part of quiet margin smoothing. Restarted
scalar energy and the one-jet bridge imply a short-time gain. The argument also
applies to plane energies; no spatial representation enters it. -/

/-- A scalar energy hierarchy gains `q` orders after `q` short windows. The
one-jet comparison may hold only almost everywhere, as for Sobolev lifts.
For factorial energies its coefficient `σ` is the squared spatial radius. -/
theorem weak_scalar_smoothing_from_restarted_energy
    (E G : ℕ → ℝ → ℝ) (a b ν σ δ : ℝ) (q : ℕ)
    (hν : 0 < ν) (hσ : 0 ≤ σ) (hδ : 0 < δ)
    (hc : ∀ j ≤ q, ContinuousOn (E j) (Icc a b))
    (hn : ∀ j ≤ q, ∀ t ∈ Icc a b, 0 ≤ E j t)
    (hG : ∀ j ≤ q, IntegrableOn (G j) (Icc a b))
    (hGn : ∀ j ≤ q, ∀ t ∈ Icc a b, 0 ≤ G j t)
    (hbridge : ∀ j < q, ∀ᵐ t ∂(volume.restrict (Icc a b)),
      E (j + 1) t ≤ E j t + σ * G j t)
    (henergy : ∀ j ≤ q, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      E j t + ν / 2 * (∫ u in s..t, G j u) ≤ 2 * E j s)
    (t : ℝ) (ht : a + q * δ ≤ t) (hb : t ≤ b) :
    E q t ≤ 2 * (4 + 8 * σ / (ν * δ)) ^ q * E 0 a := by
  have ha : a ≤ b := (le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg q) hδ.le)).trans (ht.trans hb)
  have hprop (j : ℕ) (hj : j ≤ q) (s u : ℝ)
      (hs : a ≤ s) (hsu : s ≤ u) (hu : u ≤ b) : E j u ≤ 2 * E j s := by
    have hg : 0 ≤ ∫ z in s..u, G j z :=
      intervalIntegral.integral_nonneg hsu fun z hz =>
        hGn j hj z ⟨hs.trans hz.1, hz.2.trans hu⟩
    exact (le_add_of_nonneg_right (mul_nonneg (div_nonneg hν.le (by norm_num)) hg)).trans
      (henergy j hj s u hs hsu hu)
  have hint (j : ℕ) (hj : j < q) (s : ℝ) (hs : a ≤ s) (hsb : s + δ ≤ b) :
      (∫ u in s..(s + δ), E (j + 1) u) ≤
        (2 * δ + 4 * σ / ν) * E j s := by
    have hsj : s ≤ s + δ := le_add_of_nonneg_right hδ.le
    have hsub : Icc s (s + δ) ⊆ Icc a b := Icc_subset_Icc hs hsb
    have hEj : IntervalIntegrable (E j) volume s (s + δ) := ((hc j hj.le).mono hsub).intervalIntegrable_of_Icc hsj
    have hEj1 : IntervalIntegrable (E (j + 1)) volume s (s + δ) := ((hc (j + 1) (Nat.succ_le_of_lt hj)).mono hsub).intervalIntegrable_of_Icc hsj
    have hGj : IntervalIntegrable (G j) volume s (s + δ) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hsj).mpr ((hG j hj.le).mono_set hsub)
    have hp : (∫ u in s..(s + δ), E j u) ≤ δ * (2 * E j s) := by
      have hh := intervalIntegral.integral_mono_on hsj hEj
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2 * E j s) volume s (s + δ))
        (fun u hu => hprop j hj.le s u hs hu.1 (hu.2.trans hsb))
      simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] using hh
    have hg : (∫ u in s..(s + δ), G j u) ≤ 4 / ν * E j s := by
      have he := henergy j hj.le s (s + δ) hs hsj hsb
      have he' : ν / 2 * (∫ u in s..(s + δ), G j u) ≤ 2 * E j s :=
        (le_add_of_nonneg_left (hn j hj.le (s + δ) ⟨hs.trans hsj, hsb⟩)).trans he
      calc
        _ ≤ (2 * E j s) / (ν / 2) :=
          (le_div_iff₀ (div_pos hν (by norm_num))).mpr (by
            simpa only [mul_comm] using he')
        _ = _ := by field_simp; ring
    have hh := intervalIntegral.integral_mono_ae_restrict hsj hEj1
      (hEj.add (hGj.const_mul σ))
      (ae_restrict_of_ae_restrict_of_subset hsub (hbridge j hj))
    rw [intervalIntegral.integral_add hEj (hGj.const_mul σ),
      intervalIntegral.integral_const_mul] at hh
    calc
      _ ≤ δ * (2 * E j s) + σ * (4 / ν * E j s) :=
        hh.trans (add_le_add hp (mul_le_mul_of_nonneg_left hg hσ))
      _ = _ := by ring
  have hs := CycleWords.continuous_energy_short_window_polynomial_price E
    (2 * δ + 4 * σ / ν) 2 (2 * E 0 a) a b δ q hδ
    (add_nonneg (mul_nonneg (by norm_num) hδ.le)
      (div_nonneg (mul_nonneg (by norm_num) hσ) hν.le)) (by norm_num) hc
    (fun u hu => hprop 0 (Nat.zero_le q) a u le_rfl hu.1 hu.2)
    (mul_nonneg (by norm_num) (hn 0 (Nat.zero_le q) a ⟨le_rfl, ha⟩)) hint
    (fun j _ hj s u hs hsu hu _ => hprop j hj s u hs hsu hu) t ht hb
  have hp : 2 * (2 * δ + 4 * σ / ν) / δ = 4 + 8 * σ / (ν * δ) := by
    field_simp
    ring
  rw [hp] at hs
  exact hs.trans_eq (by ring)

private theorem weak_factorialWeight_succ_le (ρ : ℝ) (j : ℕ) :
    Sobolev.factorialWeight ρ (j + 1) ≤ ρ ^ 2 * Sobolev.factorialWeight ρ j := by
  have hden : 0 < (j.factorial : ℝ) ^ 2 := by positivity
  have hj : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
    have hn : (1 : ℝ) ≤ (j : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg j)
    exact one_le_pow₀ hn
  have hnum : 0 ≤ ρ ^ 2 * ρ ^ (2 * j) :=
    mul_nonneg (sq_nonneg _) (by
      rw [show 2 * j = j * 2 by omega, pow_mul]
      exact sq_nonneg _)
  unfold Sobolev.factorialWeight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow,
    Nat.mul_add, Nat.mul_one, pow_add, mul_comm (ρ ^ (2 * j))]
  calc
    _ ≤ (ρ ^ 2 * ρ ^ (2 * j)) / (j.factorial : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hnum hden (le_mul_of_one_le_left hden.le hj)
    _ = _ := by ring

/-- The exact factorial one-jet bridge used by the scalar hierarchy. It is an
identity/inequality of genuine ambient jet norms, independent of the carrier. -/
theorem weak_factorial_one_jet_bridge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {μ : Measure (Homogenization.Vec 2)} {K : ℕ}
    (ρ : ℝ) (D : Sobolev.JetL2 μ (K + 1) E) :
    Sobolev.factorialNormSq ρ D ≤
      Sobolev.factorialNormSq ρ (Sobolev.truncateJet (Nat.le_succ K) D) +
        ρ ^ 2 * gradFactorialNormSq ρ D := by
  have h0 : Sobolev.factorialWeight ρ 0 = 1 := by simp only
    [Sobolev.factorialWeight, Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, div_one]
  have he : Sobolev.factorialNormSq ρ D = Sobolev.derivativeNormSq D 0 +
      ∑ j : Fin (K + 1), Sobolev.factorialWeight ρ (j.val + 1) *
        Sobolev.derivativeNormSq D j.succ := by
    rw [Sobolev.factorialNormSq, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, h0, one_mul]
  rw [he]
  apply add_le_add
  · exact CoupledEnergy.Variational.derivativeNormSq_zero_le_factorial ρ
      (Sobolev.truncateJet (Nat.le_succ K) D)
  · change (∑ j : Fin (K + 1), Sobolev.factorialWeight ρ (j.val + 1) *
        Sobolev.derivativeNormSq D j.succ) ≤
      ρ ^ 2 * ∑ j : Fin (K + 1), Sobolev.factorialWeight ρ j.val *
        Sobolev.derivativeNormSq D j.succ
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact (mul_le_mul_of_nonneg_right (weak_factorialWeight_succ_le ρ j.val)
      (Sobolev.derivativeNormSq_nonneg D j.succ)).trans_eq (by ring)

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public section
namespace AVRegularity.WeakEntryProofs

/-! Clock changes preserve the admissible divergence-free drift. -/

open MeasureTheory Homogenization AVRegularity.Sobolev

theorem cellDrift_comp_mul (v : ℝ → Vec 2 → Vec 2) (c : ℝ) (h : IsCellDrift v) :
    IsCellDrift (fun t => c • v (c * t)) := by
  have hclock : Measurable (fun p : ℝ × Vec 2 => (c * p.1, p.2)) :=
    (measurable_const.mul measurable_fst).prodMk measurable_snd
  refine ⟨(measurable_const : Measurable (fun _ : ℝ × Vec 2 => c)).smul (h.1.comp hclock),
    ?_, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := h.2.1
    refine ⟨c * M, fun t z => ?_⟩
    calc
      (∑ i, ((c • v (c * t)) z i) ^ 2) = c ^ 2 * ∑ i, v (c * t) z i ^ 2 := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
      _ ≤ c ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left (hM _ _) (sq_nonneg c)
      _ = (c * M) ^ 2 := (mul_pow _ _ _).symm
  · intro t n z
    exact congrArg (fun w : Vec 2 => c • w) (h.2.2.1 (c * t) n z)
  · intro t φ
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [integral_const_mul, h.2.2.2 (c * t) φ, mul_zero]

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Literal slice algebra holds at every spatially square-integrable time. -/

open MeasureTheory Homogenization AVRegularity.CycleEvolution

theorem cellSourceSlice_add_of_memLp (f g : ℝ → Vec 2 → ℂ) (t : ℝ)
    (hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp (g t) 2 (volume.restrict AVenhance.unitCube)) :
    cellSourceSlice (fun s z => f s z + g s z) t = cellSourceSlice f t + cellSourceSlice g t := by
  apply Lp.ext
  exact (cellSourceSlice_ae _ t (hf.add hg)).trans
    (((cellSourceSlice_ae f t hf).add (cellSourceSlice_ae g t hg)).symm.trans
      (Lp.coeFn_add _ _).symm)

theorem cellSourceSlice_sub_of_memLp (f g : ℝ → Vec 2 → ℂ) (t : ℝ)
    (hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp (g t) 2 (volume.restrict AVenhance.unitCube)) :
    cellSourceSlice (fun s z => f s z - g s z) t = cellSourceSlice f t - cellSourceSlice g t := by
  apply Lp.ext
  exact (cellSourceSlice_ae _ t (hf.sub hg)).trans
    (((cellSourceSlice_ae f t hf).sub (cellSourceSlice_ae g t hg)).symm.trans
      (Lp.coeFn_sub _ _).symm)

theorem cellSourceSlice_smul_of_memLp (f : ℝ → Vec 2 → ℂ) (t c : ℝ)
    (hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube)) :
    cellSourceSlice (fun s z => c • f s z) t = c • cellSourceSlice f t := by
  apply Lp.ext
  exact (cellSourceSlice_ae _ t (hf.const_smul c)).trans
    (((cellSourceSlice_ae f t hf).const_smul c).symm.trans (Lp.coeFn_smul c _).symm)

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology Metric
namespace AVRegularity.WeakEntryProofs

/-! A fixed finite-dimensional slow cutoff has finite derivative budgets before any construction data. -/

open AVRegularity.EntryWeakProofs

theorem local_slow_cutoff_reserve_exists (H : ℕ) (U : Set (Vec 2)) (hU : IsOpen U)
    (Y₀ : Vec 2) (hY : Y₀ ∈ U) :
    ∃ (χ : Vec 2 → ℝ) (_Q : JointSourceReserve H (fun _ _ Y => χ Y)),
      tsupport χ ⊆ U ∧ χ =ᶠ[𝓝 Y₀] 1 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU Y₀ hY
  let c : ContDiffBump Y₀ :=
    ⟨r / 4, r / 2, div_pos hr (by norm_num), by linarith only [hr]⟩
  have hb (n : ℕ) : ∃ B : ℝ, ∀ Y, ‖iteratedFDeriv ℝ n (c : Vec 2 → ℝ) Y‖ ≤ B :=
    (c.hasCompactSupport.iteratedFDeriv n).exists_bound_of_continuous
      (ContDiff.continuous_iteratedFDeriv (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
        (c.contDiff : ContDiff ℝ (⊤ : ℕ∞) (c : Vec 2 → ℝ)))
  choose B hB using hb
  have hBn : ∀ n, 0 ≤ B n := fun n =>
    (norm_nonneg (iteratedFDeriv ℝ n (c : Vec 2 → ℝ) 0)).trans (hB n 0)
  let Q := slowIndependentJointSourceReserve H (fun _ => (c : Vec 2 → ℝ))
    (fun _ => c.contDiff) (fun _ => measurable_const) B hBn (fun n _ _ Y => hB n Y)
  refine ⟨c, Q, ?_, c.eventuallyEq_one⟩
  intro Y hY
  rw [c.tsupport_eq] at hY
  exact hball (mem_ball.mpr ((mem_closedBall.mp hY).trans_lt (half_lt_self hr)))

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Every fixed finite native history has smooth spacetime geometry, without a large-base restriction. -/

open Homogenization AVRegularity.EntryWeakProofs

def GeomSpacetimeSmooth (g : ChainGeom) : Prop :=
  ∀ r : ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => g.1 p.1 p.2 r)

theorem relDisp_spacetime_smooth (D : OCData) (hζ : IsFastProfile D.ζ)
    (k : ℕ) (pk : ℤ) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => D.relDisp k pk p.1 r p.2) := by
  have hc := AVRegularity.CycleReference.ocPulse_contDiff (α := D.α) (q := D.q)
    (Λ := D.Λ) (m := k) hζ pk
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v)
      (ocPulse D.α D.q D.Λ D.ζ k pk u) u :=
    intervalIntegral.integral_hasDerivAt_right (hc.continuous.intervalIntegrable _ _)
      (hc.continuous.stronglyMeasurableAtFilter _ _) hc.continuous.continuousAt
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun u => (hd u).differentiableAt, ?_⟩
    have he : deriv (fun u : ℝ => ∫ v in r..u, ocPulse D.α D.q D.Λ D.ζ k pk v) =
        ocPulse D.α D.q D.Λ D.ζ k pk := funext (fun u => (hd u).deriv)
    rw [he]
    exact hc
  unfold OCData.relDisp
  exact ((hF.comp contDiff_fst).smul
    ((ocShearVel_spatial_smooth _ _ _ _ _).comp (contDiff_snd.const_smul _))).const_smul _

theorem geom_spacetime_smooth_childGeom (D : OCData) (hζ : IsFastProfile D.ζ) (k : ℕ) (pk : ℤ) (s' : ℝ)
    (c : ChainChild) {g : ChainGeom} (hg : GeomSpacetimeSmooth g) : GeomSpacetimeSmooth (D.childGeom k pk s' c g) := by
  intro r
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => g.1 g.2.2 p.2 r) :=
    (hg r).comp (contDiff_const.prodMk contDiff_snd)
  have hR : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => D.relDisp k pk p.1 r
      ((D.eps k)⁻¹ • g.1 g.2.2 p.2 r + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) :=
    (relDisp_spacetime_smooth D hζ k pk r).comp
      (contDiff_fst.prodMk ((hA.const_smul _).add contDiff_const))
  exact (hg g.2.2).comp (contDiff_fst.prodMk (hA.add (hR.const_smul _)))

theorem geom_spacetime_smooth_geomAux (D : OCData) (hζ : IsFastProfile D.ζ) :
    ∀ (cs : List ChainChild) (k : ℕ) (sl : List ℤ) {g : ChainGeom},
      GeomSpacetimeSmooth g → GeomSpacetimeSmooth (D.geomAux k sl cs g)
  | [], k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | _ :: _ :: _ => exact hg
  | c :: cs, k, sl, g, hg => by
    match sl with
    | [] => exact hg
    | [_] => exact hg
    | pk :: pk1 :: rest =>
      exact geom_spacetime_smooth_geomAux D hζ cs (k + 1) (pk1 :: rest) (geom_spacetime_smooth_childGeom D hζ k pk _ c hg)

/-- **The chain geometry is jointly `C¹`.** -/
theorem geom_spacetime_smooth_geom (D : OCData) (hζ : IsFastProfile D.ζ) (ch : RealChain) :
    GeomSpacetimeSmooth (ch.geom D) := by
  refine geom_spacetime_smooth_geomAux D hζ _ _ _ ?_
  intro r
  have h := AVRegularity.CycleReference.streamFlow_joint_smooth (D.hΦ ch.baseLevel)
  exact (h.comp
    (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)))

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public section
namespace AVRegularity.WeakEntryProofs

/-! Replacing a trace outside the solving window preserves its actual Hilbert equation. -/

open MeasureTheory Set Filter AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

theorem cellWeakHilbert_trace_congr {a b : ℝ}
    {u v : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (he : ∀ t ∈ Icc a b, v t = u t) :
    CellWeakHilbertCurve a b v slice g := by
  refine ⟨h.trace.congr he, h.state, h.dual, ?_, ?_⟩
  · filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
    rw [he t hti]
    exact ht
  · intro s hs t ht hst z
    rw [he s hs, he t ht]
    exact h.increment s hs t ht hst z

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution AVenhance.Infra.ODE
namespace AVRegularity.WeakEntryProofs

/-! The finite-Fourier weak-time pairing argument, for arbitrary finite real
Hilbert fibres, through projection, energy and pairing steps; no PDE or adjoint pairing is
assumed here. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- L² orthogonal initial state defined by the nondegenerate finite mass form. -/
def weakScalarGalerkinL2Initial (N : ℕ)
    (u₀ : Lp E 2 (volume.restrict AVenhance.unitCube)) : CellGalerkinSpace (E := E) N :=
  weakMassSource (cellGalerkinMass N) (cellGalerkinMass_injective N)
    ((innerSL ℝ u₀).comp (cellGalerkinValue N)).toLinearMap

/-- The initial state has exactly the prescribed L² moments in the retained modes. -/
theorem weakScalarGalerkinL2Initial_pairing (N : ℕ)
    (u₀ : Lp E 2 (volume.restrict AVenhance.unitCube)) (z : CellGalerkinSpace (E := E) N) :
    inner ℝ (cellGalerkinValue N (weakScalarGalerkinL2Initial N u₀)) (cellGalerkinValue N z) =
      inner ℝ u₀ (cellGalerkinValue N z) := by
  exact congrArg (fun f => f z)
    (weakMassSource_mass (cellGalerkinMass N) (cellGalerkinMass_injective N)
      ((innerSL ℝ u₀).comp (cellGalerkinValue N)).toLinearMap)

/-- Every cell L² class is a periodic order-zero Sobolev class. -/
def weakScalarL2AsH0 (u : Lp E 2 (volume.restrict AVenhance.unitCube)) : TorusHk 0 E :=
  ⟨WithLp.toLp 2 (fun _ : JetIndex2 0 => u), by simp [torusHkGraph]⟩

/-- Realize the Fourier cutoff of L² data by a retained H¹ state. -/
def weakScalarL2FourierState (N : ℕ) (u : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    CellGalerkinSpace (E := E) N :=
  cellGalerkinInitial N (smoothFourierLift (K := 0) (L := 1) N (weakScalarL2AsH0 u))

/-- The retained H¹ state has the literal L² Fourier cutoff as its value. -/
theorem weakScalarL2FourierState_value (N : ℕ) (u : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    cellGalerkinValue N (weakScalarL2FourierState N u) = cellVectorFourierProjection N u := by
  change (galerkinProj N (smoothFourierLift (K := 0) (L := 1) N (weakScalarL2AsH0 u))).val
    (valueIndex2 1) = _
  rw [galerkinProj_val, cellJetFourierProjection_apply,
    smoothFourierLift_value_eq_projection (by decide : 0 ≤ 1),
    galerkinProj_val, cellJetFourierProjection_apply]
  change cellVectorFourierProjection N (cellVectorFourierProjection N u) = _
  exact cellVectorFourierProjection_idempotent N u

/-- Every retained state's L² value is fixed by the Fourier cutoff. -/
theorem weakScalarGalerkinValue_fourier_fixed (N : ℕ) (z : CellGalerkinSpace (E := E) N) :
    cellVectorFourierProjection N (cellGalerkinValue N z) = cellGalerkinValue N z := by
  have hf := galerkinProj_fixed_of_range N z
  have h := congrArg (fun f : TorusHk 1 E => f.val (valueIndex2 1)) hf
  change cellVectorFourierProjection N (z.val.val (valueIndex2 1)) =
    z.val.val (valueIndex2 1)
  simpa only [galerkinProj_val, cellJetFourierProjection_apply] using h

/-- Mass projection of arbitrary initial data equals its L² Fourier cutoff. -/
theorem weakScalarGalerkinL2Initial_eq_fourier (N : ℕ)
    (u : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    weakScalarGalerkinL2Initial N u = weakScalarL2FourierState N u := by
  apply cellGalerkinMass_injective N
  ext z
  change inner ℝ (cellGalerkinValue N (weakScalarGalerkinL2Initial N u)) (cellGalerkinValue N z) =
    inner ℝ (cellGalerkinValue N (weakScalarL2FourierState N u)) (cellGalerkinValue N z)
  rw [weakScalarGalerkinL2Initial_pairing, weakScalarL2FourierState_value,
    cellVectorFourierProjection_inner, weakScalarGalerkinValue_fourier_fixed]

/-- Finite initial states converge in L² for every L² datum, with no endpoint H¹ premise. -/
theorem weakScalarGalerkinL2Initial_tendsto
    (u : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    Tendsto (fun N => cellGalerkinValue N (weakScalarGalerkinL2Initial N u)) atTop (𝓝 u) := by
  simp only [weakScalarGalerkinL2Initial_eq_fourier, weakScalarL2FourierState_value]
  exact cellVectorFourierProjection_tendsto u

/-- Continuous finite initial projection expressed in L² moments. -/
def weakScalarGalerkinL2InitialCLM (N : ℕ) :
    Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ] CellGalerkinSpace (E := E) N :=
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := E) N)
  ∑ i, (innerSL ℝ (cellGalerkinValue N (basis i))).smulRight
    (weakMassSource (cellGalerkinMass N) (cellGalerkinMass_injective N) (basis.coord i))

/-- Finite mass inversion of an H¹ Hilbert representative of a dual derivative. -/
def weakScalarGalerkinDualMomentCLM (N : ℕ) : TorusHk 1 E →L[ℝ] CellGalerkinSpace (E := E) N :=
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := E) N)
  ∑ i, (innerSL ℝ (basis i).val).smulRight
    (weakMassSource (cellGalerkinMass N) (cellGalerkinMass_injective N) (basis.coord i))

/-- The dual moment map has the intended mass identity against every retained test. -/
theorem weakScalarGalerkinDualMomentCLM_pairing (N : ℕ) (g : TorusHk 1 E)
    (z : CellGalerkinSpace (E := E) N) :
    inner ℝ (cellGalerkinValue N (weakScalarGalerkinDualMomentCLM N g)) (cellGalerkinValue N z) =
      inner ℝ g z.val := by
  have he : weakScalarGalerkinDualMomentCLM N g =
      weakMassSource (cellGalerkinMass N) (cellGalerkinMass_injective N)
        (cellGalerkinSource N (innerSL ℝ g).toLinearMap) := by
    rw [weakMassSource_eq_sum (Module.finBasis ℝ (CellGalerkinSpace (E := E) N))]
    simp only [weakScalarGalerkinDualMomentCLM, sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact real_inner_comm _ _
  rw [he]
  exact congrArg (fun f => f z)
    (weakMassSource_mass (cellGalerkinMass N) (cellGalerkinMass_injective N)
      (cellGalerkinSource N (innerSL ℝ g).toLinearMap))

/-- An H¹-in-space L² curve whose H⁻¹ time derivative is represented through the H¹ Hilbert
inner product. Fixed-test time increments are the only differential premise. -/
structure WeakScalarHilbertCurve (a b : ℝ)
    (u : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube))
    (slice g : ℝ → TorusHk 1 E) : Prop where
  trace : ContinuousOn u (Icc a b)
  state : MemLp slice 2 (volume.restrict (Icc a b))
  dual : MemLp g 2 (volume.restrict (Icc a b))
  agrees : ∀ᵐ t ∂volume.restrict (Icc a b), u t = torusHkValueCLM (slice t)
  increment : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → ∀ z : TorusHk 1 E,
    inner ℝ (u t) (torusHkValueCLM z) - inner ℝ (u s) (torusHkValueCLM z) =
      ∫ r in s..t, inner ℝ (g r) z

/-- At H¹ slices, the finite L² mass projection is the usual H¹ Fourier projection. -/
theorem weakScalarGalerkinL2Initial_of_H1 (N : ℕ) (z : TorusHk 1 E) :
    weakScalarGalerkinL2Initial N (torusHkValueCLM z) = cellGalerkinInitial N z := by
  apply Subtype.ext
  apply TorusHk.ext_value
  have hleft : cellGalerkinValue N (weakScalarGalerkinL2Initial N (torusHkValueCLM z)) =
      cellVectorFourierProjection N (torusHkValueCLM z) := by
    rw [weakScalarGalerkinL2Initial_eq_fourier, weakScalarL2FourierState_value]
  have hright : cellGalerkinValue N (cellGalerkinInitial N z) =
      cellVectorFourierProjection N (torusHkValueCLM z) := by
    change (galerkinProj N z).val (valueIndex2 1) = _
    rw [galerkinProj_val, cellJetFourierProjection_apply]
    rfl
  exact hleft.trans hright.symm

/-- The projected H⁻¹ derivative is integrable on the finite time interval. -/
theorem weakScalarWeakDualMoment_intervalIntegrable {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (g : ℝ → TorusHk 1 E) (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => weakScalarGalerkinDualMomentCLM N (g t)) volume a b := by
  have hm := (weakScalarGalerkinDualMomentCLM N).comp_memLp' hg
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  exact (hm.integrable (by norm_num)).mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

/-- A fixed-test weak time equation gives the literal finite integral coefficient equation. -/
theorem WeakScalarHilbertCurve.projected_integral_solution {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 E} (h : WeakScalarHilbertCurve a b u slice g) (N : ℕ) :
    IsLinearIntegralSolution (fun _ => 0) (fun t => weakScalarGalerkinDualMomentCLM N (g t))
      (weakScalarGalerkinL2Initial N (u a)) a b (fun t => weakScalarGalerkinL2Initial N (u t)) := by
  intro t ht
  change weakScalarGalerkinL2Initial N (u t) = weakScalarGalerkinL2Initial N (u a) +
    ∫ r in a..t, (0 : CellGalerkinSpace (E := E) N →L[ℝ] CellGalerkinSpace (E := E) N)
      (weakScalarGalerkinL2Initial N (u r)) + weakScalarGalerkinDualMomentCLM N (g r)
  simp only [zero_apply, zero_add]
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := (weakScalarWeakDualMoment_intervalIntegrable hab N g h.dual).mono_set hsub
  apply cellGalerkinMass_injective N
  ext z
  change inner ℝ (cellGalerkinValue N (weakScalarGalerkinL2Initial N (u t))) (cellGalerkinValue N z) =
    inner ℝ (cellGalerkinValue N (weakScalarGalerkinL2Initial N (u a) +
      ∫ r in a..t, weakScalarGalerkinDualMomentCLM N (g r))) (cellGalerkinValue N z)
  rw [map_add, inner_add_left, weakScalarGalerkinL2Initial_pairing, weakScalarGalerkinL2Initial_pairing]
  have he : inner ℝ (cellGalerkinValue N (∫ r in a..t, weakScalarGalerkinDualMomentCLM N (g r)))
      (cellGalerkinValue N z) = ∫ r in a..t, inner ℝ (g r) z.val := by
    let L := (innerSL ℝ (cellGalerkinValue N z)).comp (cellGalerkinValue N)
    calc
      _ = L (∫ r in a..t, weakScalarGalerkinDualMomentCLM N (g r)) := real_inner_comm _ _
      _ = ∫ r in a..t, L (weakScalarGalerkinDualMomentCLM N (g r)) :=
        (L.intervalIntegral_comp_comm hint).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro r _
        exact (real_inner_comm _ _).trans (weakScalarGalerkinDualMomentCLM_pairing N (g r) z)
  rw [he]
  change inner ℝ (u t) (torusHkValueCLM z.val) =
    inner ℝ (u a) (torusHkValueCLM z.val) + ∫ r in a..t, inner ℝ (g r) z.val
  have hw := h.increment a ⟨le_rfl, hab⟩ t ht ht.1 z.val
  linarith

/-- Finite Fourier projections have strong time derivatives even when the full derivative is H⁻¹. -/
theorem WeakScalarHilbertCurve.projected_strongTime {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 E} (h : WeakScalarHilbertCurve a b u slice g) (N : ℕ) :
    StrongTimeRegularity a b (fun t => weakScalarGalerkinL2Initial N (u t))
      (fun t => weakScalarGalerkinDualMomentCLM N (g t)) := by
  have hy := h.projected_integral_solution hab N
  have he : linearRhs (fun _ => (0 : CellGalerkinSpace (E := E) N →L[ℝ]
      CellGalerkinSpace (E := E) N)) (fun t => weakScalarGalerkinDualMomentCLM N (g t))
      (fun t => weakScalarGalerkinL2Initial N (u t)) =
      (fun t => weakScalarGalerkinDualMomentCLM N (g t)) := by
    funext t
    change 0 + weakScalarGalerkinDualMomentCLM N (g t) = _
    exact zero_add _
  have hint : IntervalIntegrable
      (linearRhs (fun _ => 0) (fun t => weakScalarGalerkinDualMomentCLM N (g t))
        (fun t => weakScalarGalerkinL2Initial N (u t))) volume a b := by
    rw [he]
    exact
      weakScalarWeakDualMoment_intervalIntegrable hab N g h.dual
  refine ⟨hy.absolutelyContinuousOnInterval hab hint, ?_⟩
  apply (ae_restrict_iff' measurableSet_uIcc).mpr
  have hd := hy.ae_hasDerivAt hab hint
  filter_upwards [hd] with t ht
  simpa only [uIcc_of_le hab, he] using ht

/-- The weak-time cell curve satisfies the exact energy identity. No strong L² time
 derivative or energy-identity premise is required for the full curve. -/
theorem WeakScalarHilbertCurve.energy_increment {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 E} (h : WeakScalarHilbertCurve a b u slice g) :
    ‖u b‖ ^ 2 - ‖u a‖ ^ 2 = ∫ t in a..b, 2 * inner ℝ (g t) (slice t) := by
  let μ := volume.restrict (Icc a b)
  have hm : Integrable (fun t => ‖g t‖ * ‖slice t‖) μ :=
    memLp_one_iff_integrable.mp (h.dual.norm.mul h.state.norm : MemLp _ 1 μ)
  have hbound : IntegrableOn (fun t => 2 * (‖g t‖ * ‖slice t‖)) (Ioc a b) :=
    (hm.const_mul 2).mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have ha : ∀ᵐ t ∂volume.restrict (Ioc a b), u t = torusHkValueCLM (slice t) :=
    h.agrees.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  apply energy_increment_of_dominated_approximation hab
    (fun N t => cellGalerkinValue N (weakScalarGalerkinL2Initial N (u t)))
    (fun N t => cellGalerkinValue N (weakScalarGalerkinDualMomentCLM N (g t)))
    (fun N => (h.projected_strongTime hab N).map (cellGalerkinValue N))
    (u a) (u b) (weakScalarGalerkinL2Initial_tendsto (u a)) (weakScalarGalerkinL2Initial_tendsto (u b))
    (fun t => 2 * inner ℝ (g t) (slice t)) (fun t => 2 * (‖g t‖ * ‖slice t‖)) hbound
  · intro N
    filter_upwards [ha] with t hat
    rw [real_inner_comm, weakScalarGalerkinDualMomentCLM_pairing, hat, weakScalarGalerkinL2Initial_of_H1]
    change ‖2 * inner ℝ (g t) (galerkinProj N (slice t))‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (galerkinProj_norm_le N (slice t)) (norm_nonneg _))
  · filter_upwards [ha] with t hat
    have hp : Tendsto (fun N => 2 * inner ℝ (g t) (galerkinProj N (slice t))) atTop
        (𝓝 (2 * inner ℝ (g t) (slice t))) :=
      (tendsto_const_nhds.inner (galerkinProj_tendsto (slice t))).const_mul 2
    apply hp.congr'
    filter_upwards with N
    have he : inner ℝ (cellGalerkinValue N (weakScalarGalerkinL2Initial N (u t)))
        (cellGalerkinValue N (weakScalarGalerkinDualMomentCLM N (g t))) =
        inner ℝ (g t) (galerkinProj N (slice t)) := by
      rw [real_inner_comm, weakScalarGalerkinDualMomentCLM_pairing, hat, weakScalarGalerkinL2Initial_of_H1]
      rfl
    rw [he]

omit [FiniteDimensional ℝ E] in
/-- Weak Hilbert cell curves restrict to smaller closed intervals. -/
theorem WeakScalarHilbertCurve.mono {a b c d : ℝ}
    {u : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 E} (h : WeakScalarHilbertCurve a b u slice g)
    (hsub : Icc c d ⊆ Icc a b) : WeakScalarHilbertCurve c d u slice g := by
  refine ⟨h.trace.mono hsub,
    h.state.mono_measure (Measure.restrict_mono hsub le_rfl),
    h.dual.mono_measure (Measure.restrict_mono hsub le_rfl),
    h.agrees.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)), ?_⟩
  intro s hs t ht hst z
  exact h.increment s (hsub hs) t (hsub ht) hst z

omit [FiniteDimensional ℝ E] in
/-- Weak energy production is integrable, as a product of two Bochner L² fields. -/
theorem WeakScalarHilbertCurve.production_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 E} (h : WeakScalarHilbertCurve a b u slice g) :
    IntervalIntegrable (fun t => 2 * inner ℝ (g t) (slice t)) volume a b := by
  have hm : Integrable (fun t => 2 * (‖g t‖ * ‖slice t‖)) (volume.restrict (Icc a b)) :=
    (memLp_one_iff_integrable.mp (h.dual.norm.mul h.state.norm : MemLp _ 1 _)).const_mul 2
  have hp : Integrable (fun t => 2 * inner ℝ (g t) (slice t)) (volume.restrict (Icc a b)) := by
    apply hm.mono'
    · exact aestronglyMeasurable_const.mul (h.dual.aestronglyMeasurable.inner h.state.aestronglyMeasurable)
    · apply Filter.Eventually.of_forall
      intro t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  exact hp.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

omit [FiniteDimensional ℝ E] in
/-- Every fixed H¹ test has an integrable pairing with the Hilbert dual derivative. -/
theorem weakScalarWeakPair_intervalIntegrable {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hst : s ≤ t) (g : ℝ → TorusHk 1 E)
    (hg : MemLp g 2 (volume.restrict (Icc a b))) (z : TorusHk 1 E) :
    IntervalIntegrable (fun r => inner ℝ (g r) z) volume s t := by
  have hm := (innerSL ℝ z).comp_memLp' hg
  have hi : Integrable (fun r => inner ℝ (g r) z) (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
      hm.integrable (by norm_num)
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hst]
  exact hi.mono_measure (Measure.restrict_mono
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)

omit [FiniteDimensional ℝ E] in
/-- Differences retain the weak Hilbert time equation and almost-everywhere H¹ lift. -/
theorem WeakScalarHilbertCurve.sub {a b : ℝ}
    {u v : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube)}
    {slice g slice' g' : ℝ → TorusHk 1 E}
    (h : WeakScalarHilbertCurve a b u slice g) (h' : WeakScalarHilbertCurve a b v slice' g') :
    WeakScalarHilbertCurve a b (fun t => u t - v t) (fun t => slice t - slice' t)
      (fun t => g t - g' t) := by
  refine ⟨h.trace.sub h'.trace, h.state.sub h'.state, h.dual.sub h'.dual, ?_, ?_⟩
  · filter_upwards [h.agrees, h'.agrees] with t ht ht'
    rw [ht, ht', map_sub]
  · intro s hs t ht hst z
    have hg := weakScalarWeakPair_intervalIntegrable hs ht hst g h.dual z
    have hg' := weakScalarWeakPair_intervalIntegrable hs ht hst g' h'.dual z
    simp only [inner_sub_left]
    rw [intervalIntegral.integral_sub hg hg']
    have hu := h.increment s hs t ht hst z
    have hv := h'.increment s hs t ht hst z
    linarith

omit [FiniteDimensional ℝ E] in
theorem weakScalarH1Pair_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    {g z : ℝ → TorusHk 1 E}
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hz : MemLp z 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => inner ℝ (g t) (z t)) volume a b := by
  have hm : Integrable (fun t => ‖g t‖ * ‖z t‖) (volume.restrict (Icc a b)) :=
    memLp_one_iff_integrable.mp (hg.norm.mul hz.norm : MemLp _ 1 _)
  have hp : Integrable (fun t => inner ℝ (g t) (z t)) (volume.restrict (Icc a b)) := by
    apply hm.mono'
    · exact hg.aestronglyMeasurable.inner hz.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs]
        exact abs_real_inner_le_norm (g t) (z t))
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  exact hp.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

theorem WeakScalarHilbertCurve.pairing_increment {a b : ℝ} (hab : a ≤ b)
    {u v : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube)}
    {slice g slice' g' : ℝ → TorusHk 1 E}
    (h : WeakScalarHilbertCurve a b u slice g) (h' : WeakScalarHilbertCurve a b v slice' g') :
    inner ℝ (u b) (v b) - inner ℝ (u a) (v a) =
      ∫ t in a..b, inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t) := by
  have h₁ := h.energy_increment hab
  have h₂ := h'.energy_increment hab
  have h₃ := (h.sub h').energy_increment hab
  have hi₁ := h.production_intervalIntegrable hab
  have hi₂ := h'.production_intervalIntegrable hab
  have hi₃ := weakScalarH1Pair_intervalIntegrable hab h.dual h'.state
  have hi₄ := weakScalarH1Pair_intervalIntegrable hab h'.dual h.state
  have hfun : (fun t => 2 * inner ℝ (g t - g' t) (slice t - slice' t)) =
      (fun t => (2 * inner ℝ (g t) (slice t) + 2 * inner ℝ (g' t) (slice' t)) -
        2 * (inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t))) := by
    funext t
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hi : (∫ t in a..b,
      (2 * inner ℝ (g t) (slice t) + 2 * inner ℝ (g' t) (slice' t)) -
        2 * (inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t))) =
      (∫ t in a..b, 2 * inner ℝ (g t) (slice t)) +
        (∫ t in a..b, 2 * inner ℝ (g' t) (slice' t)) -
          2 * ∫ t in a..b, inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t) := by
    rw [intervalIntegral.integral_sub (hi₁.add hi₂) ((hi₃.add hi₄).const_mul 2),
      intervalIntegral.integral_add hi₁ hi₂]
    rw [intervalIntegral.integral_const_mul
      (f := fun t => inner ℝ (g t) (slice' t) + inner ℝ (g' t) (slice t))]
  rw [norm_sub_sq_real, norm_sub_sq_real, hfun, hi] at h₃
  linarith

omit [FiniteDimensional ℝ E] in
theorem WeakScalarHilbertCurve.timeReverse {a b : ℝ}
    {u : ℝ → Lp E 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 E} (h : WeakScalarHilbertCurve a b u slice g) :
    WeakScalarHilbertCurve (-b) (-a) (fun t => u (-t)) (fun t => slice (-t)) (fun t => -g (-t)) := by
  have hmem {t : ℝ} (ht : t ∈ Icc (-b) (-a)) : -t ∈ Icc a b := by
    constructor <;> rcases ht with ⟨h₁, h₂⟩ <;> linarith
  refine ⟨h.trace.comp continuous_neg.continuousOn (fun t ht => hmem ht),
    cellTimeReverse_memLp h.state, (cellTimeReverse_memLp h.dual).neg, ?_, ?_⟩
  · exact (cellTimeReverse_measurePreserving_Icc a b).quasiMeasurePreserving.ae h.agrees
  · intro s hs t ht hst z
    have he := h.increment (-t) (hmem ht) (-s) (hmem hs) (by linarith) z
    have hrev : (∫ r in s..t, inner ℝ (g (-r)) z) =
        ∫ r in -t..-s, inner ℝ (g r) z :=
      intervalIntegral.integral_comp_neg (f := fun r => inner ℝ (g r) z)
    simp only [inner_neg_left]
    rw [intervalIntegral.integral_neg, hrev]
    linarith

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Finite sums of genuine spatial L2 representatives retain their literal raw sum. -/

open MeasureTheory Homogenization AVRegularity.CycleEvolution

theorem window_list_L2_ae {I : Type*} (l : List I)
    (F : I → ComplexCellL2) (f : I → Vec 2 → ℂ)
    (he : ∀ i ∈ l, F i =ᵐ[volume.restrict AVenhance.unitCube] f i) :
    (l.map F).sum =ᵐ[volume.restrict AVenhance.unitCube] (l.map f).sum := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.sum_nil] using!
      (Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube))
  | cons i l ih =>
    have ht := ih (fun j hj => he j (List.mem_cons_of_mem i hj))
    simp only [List.map_cons, List.sum_cons]
    filter_upwards [Lp.coeFn_add (F i) (l.map F).sum, he i List.mem_cons_self, ht] with x ha hi ht
    rw [ha, Pi.add_apply, hi, ht, Pi.add_apply]

end AVRegularity.WeakEntryProofs
end
end
