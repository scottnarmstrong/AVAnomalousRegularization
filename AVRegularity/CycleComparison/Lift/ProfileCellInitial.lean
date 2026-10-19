-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.ParameterIntegral
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Weighted fast Fourier response jets have the same independent slow reserve. -/

def profileWeightedResponse (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a b z : ℝ) (j : ℕ) : ℂ :=
  profileFourierSeries (fun m => profileFourierFrequency m ^ j * profileModeResponse g f a b m) z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Slow differentiation preserves the entire fast reserve of a rectangular jet. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBoxSmooth_slow_direction {p q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth (p + 1) q f) (v : Vec 2) :
    IsBoxSmooth p q (fun X z => fderiv ℝ (fun Y => f Y z) X v) := by
  rw [isBoxSmooth_iff]
  refine ⟨fun X => (slowDir_aux q E f (hf.mono (by omega) le_rfl) v X).1,
    fun j hj => ?_⟩
  have he : (fun X z => iteratedFDeriv ℝ j
      (fun y => fderiv ℝ (fun Y => f Y y) X v) z) =
      fun X z => fderiv ℝ (fun Y => iteratedFDeriv ℝ j (f Y) z) X v := by
    funext X z
    exact (slowDir_aux j E f (hf.mono (by omega) hj) v X).2 z
  rw [he]
  exact isSlowSmooth_slowDir ((isBoxSmooth_iff.mp hf).2 j hj) v

theorem isBoxSmooth_fderiv_slow {p q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth (p + 1) q f) :
    IsBoxSmooth p q (fun X z => fderiv ℝ (fun Y => f Y z) X) :=
  isBoxSmooth_clm_of_apply p q _ (fun v => isBoxSmooth_slow_direction hf v)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Finite coefficient synthesis preserves the actual classical cell time equation. -/

variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem finite_cell_time_primitives
    (G : ℝ → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (w : J → ℝ) (c f : J → ℝ → Vec 2 → E) (a t : ℝ) (z : Vec 2)
    (hc : ∀ j, ∀ s ∈ uIcc a t, ContDiff ℝ 2 (c j s))
    (h : ∀ j, IntervalIntegrable
      (fun s => -cellOperator (G s) (v s) (c j s) z + f j s z) volume a t ∧
      c j t z = ∫ s in a..t, -cellOperator (G s) (v s) (c j s) z + f j s z) :
    IntervalIntegrable (fun s =>
      -cellOperator (G s) (v s) (fun y => ∑ j, w j • c j s y) z + ∑ j, w j • f j s z)
      volume a t ∧
      (∑ j, w j • c j t z) = ∫ s in a..t,
        -cellOperator (G s) (v s) (fun y => ∑ j, w j • c j s y) z + ∑ j, w j • f j s z := by
  obtain ⟨hi, heq⟩ := finset_time_primitives Finset.univ w (fun j => c j t z)
    (fun j s => -cellOperator (G s) (v s) (c j s) z + f j s z) a t (fun j _ => h j)
  have he (s : ℝ) (hs : s ∈ uIcc a t) :
      (∑ j, w j • (-cellOperator (G s) (v s) (c j s) z + f j s z)) =
      -cellOperator (G s) (v s) (fun y => ∑ j, w j • c j s y) z + ∑ j, w j • f j s z := by
    rw [cellOperator_finite_synthesis (G s) (v s) w (fun j => c j s) (fun j => hc j s hs) z]
    simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  refine ⟨hi.congr (fun s hs => he s (uIoc_subset_uIcc hs)), ?_⟩
  rw [heq]
  exact intervalIntegral.integral_congr he

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Positive constituent budgets equal the normalized envelope table after finite sum interchange. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def positiveSourceMixedBudget (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q : ℕ) (lam : ℝ) (v u : ι) : ℝ≥0∞ :=
  ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ =>
    ENNReal.ofReal ‖γ.map‖ * ∑ α, constituentPositiveMixedBudget I p q lam (γ.coeff α)).sum

omit [Fintype ι] in
theorem positiveSourceMixedBudget_reordering (π : ι → ℝ) (edge : ConstituentEdges D h)
    (I : Set ℝ) (lam : ℝ) (p q : ℕ) (v u : ι) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) * positiveSourceMixedBudget edge I p q lam v u =
      normalizedSourceEnvelopeSum π edge I lam p q v u := by
  classical
  have hlist (a : ℝ≥0∞) (l : List ℝ≥0∞) : a * l.sum = (l.map fun x => a * x).sum := by
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]
  let W := ENNReal.ofReal (Real.sqrt (π u / π v))
  let R := Finset.range (p + 1)
  let S := Finset.range (q + 1)
  unfold positiveSourceMixedBudget
  rw [Finset.mul_sum]
  simp only [hlist, List.map_map, Function.comp_def]
  unfold constituentPositiveMixedBudget normalizedSourceEnvelopeSum
  have hγ (d : Finset.Icc 2 D) (γ : Constituent d.val (h u) (h v)) :
      W * (ENNReal.ofReal ‖γ.map‖ * ∑ α, ∑ r ∈ R, ∑ s ∈ S,
        ENNReal.ofReal ((lam ^ r)⁻¹) * jetSup I r s (γ.coeff α)) =
      ∑ r ∈ R, ∑ s ∈ S, ENNReal.ofReal ((lam ^ r)⁻¹) *
        (W * (ENNReal.ofReal ‖γ.map‖ * ∑ α, jetSup I r s (γ.coeff α))) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro α _
    ring
  change (∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ =>
      W * (ENNReal.ofReal ‖γ.map‖ * ∑ α, ∑ r ∈ R, ∑ s ∈ S,
        ENNReal.ofReal ((lam ^ r)⁻¹) * jetSup I r s (γ.coeff α))).sum) = _
  have hd (d : Finset.Icc 2 D) :
      ((edge v u d).map fun γ => W * (ENNReal.ofReal ‖γ.map‖ * ∑ α, ∑ r ∈ R, ∑ s ∈ S,
        ENNReal.ofReal ((lam ^ r)⁻¹) * jetSup I r s (γ.coeff α))).sum =
      ∑ r ∈ R, ∑ s ∈ S,
        ((edge v u d).map fun γ => ENNReal.ofReal ((lam ^ r)⁻¹) *
          (W * (ENNReal.ofReal ‖γ.map‖ * ∑ α, jetSup I r s (γ.coeff α)))).sum := by
    have hm := List.map_congr_left (fun γ (_ : γ ∈ edge v u d) => hγ d γ)
    rw [hm, list_finset_sum_interchange]
    apply Finset.sum_congr rfl
    intro r _
    exact list_finset_sum_interchange _ _ _
  simp_rw [hd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [W, Finset.mul_sum, hlist, List.map_map, Function.comp_def]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Arbitrary slow jets retain the original rectangular fast reserve. -/

theorem isBoxSmooth_iteratedFDeriv_slow (r : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (p q : ℕ) (f : Vec 2 → Vec 2 → E), IsBoxSmooth (p + r) q f →
      IsBoxSmooth p q (fun X z => iteratedFDeriv ℝ r (fun Y => f Y z) X) := by
  induction r with
  | zero =>
    intro E _ _ p q f hf
    simpa only [Nat.add_zero, iteratedFDeriv_zero_eq_comp, Function.comp_apply] using!
      hf.clm_comp (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  | succ r ih =>
    intro E _ _ p q f hf
    have hd : IsBoxSmooth (p + r) q (fun X z => fderiv ℝ (fun Y => f Y z) X) :=
      isBoxSmooth_fderiv_slow (by simpa only [Nat.add_assoc] using hf)
    have hj := ih p q (fun X z => fderiv ℝ (fun Y => f Y z) X) hd
    have he : (fun X z => iteratedFDeriv ℝ (r + 1) (fun Y => f Y z) X) =
        fun X z => (continuousMultilinearCurryRightEquiv' ℝ r (Vec 2) E).symm
          (iteratedFDeriv ℝ r (fun Y => fderiv ℝ (fun Z => f Z z) Y) X) := by
      funext X z
      rw [iteratedFDeriv_succ_eq_comp_right]
      rfl
    rw [he]
    exact hj.clm_comp
      (continuousMultilinearCurryRightEquiv' ℝ r (Vec 2) E).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-! Centered transverse flux synthesis commutes with fixed maps and finite sums. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem transverseCenteredFlux_clm (par k : Fin 2) (L : E →L[ℝ] F)
    (f : ℝ → E) (hf : Continuous f) (z : Vec 2) :
    transverseCenteredFlux par (fun y => L (f y)) k z = L (transverseCenteredFlux par f k z) := by
  unfold transverseCenteredFlux
  split_ifs
  · exact centeredIntervalPrimitive_clm L f hf _
  · exact (L.map_zero).symm

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
theorem transverseCenteredFlux_finset_sum {J : Type*} (par k : Fin 2)
    (s : Finset J) (f : J → ℝ → E) (hf : ∀ j ∈ s, Continuous (f j)) (z : Vec 2) :
    transverseCenteredFlux par (fun y => ∑ j ∈ s, f j y) k z =
      ∑ j ∈ s, transverseCenteredFlux par (f j) k z := by
  unfold transverseCenteredFlux
  split_ifs
  · exact centeredIntervalPrimitive_finset_sum s f hf _
  · simp only [Finset.sum_const_zero]
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite slow regularity of a time integral from measurable sections and bounded jets. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
theorem parameter_integral_contDiff (μ : Measure T) [IsFiniteMeasure μ]
    (n : ℕ) (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j) :
    ContDiff ℝ (n : ℕ∞) (fun x => ∫ t, f t x ∂μ) := by
  induction n generalizing f C with
  | zero =>
    apply contDiff_zero.mpr
    apply parameter_integral_continuous μ f hm (fun t => (hs t).continuous) (C 0)
    intro t x
    simpa using hb 0 (by omega) t x
  | succ n ih =>
    have hd : ∀ t, Differentiable ℝ (f t) :=
      fun t => (hs t).differentiable (by simp)
    have hb₀ : ∀ t x, ‖f t x‖ ≤ C 0 := by
      intro t x
      simpa using hb 0 (by omega) t x
    have hb₁ : ∀ t x, ‖fderiv ℝ (f t) x‖ ≤ C 1 := by
      intro t x
      simpa only [norm_iteratedFDeriv_one] using hb 1 (by omega) t x
    have hder := parameter_integral_hasFDerivAt μ f hm hd (C 0) (C 1) hb₀ hb₁
    have hcoord : ∀ q : Fin 2, ContDiff ℝ (n : ℕ∞)
        (fun x => ∫ t, fderiv ℝ (f t) x (basisVec q) ∂μ) := by
      intro q
      let α : DerivativeWord2 1 := fun _ => q
      have he : ∀ t, (fun x => fderiv ℝ (f t) x (basisVec q)) =
          orderedDerivative α (f t) := by
        intro t
        funext x
        simp [α, orderedDerivative_one]
      refine ih (fun t x => fderiv ℝ (f t) x (basisVec q))
        (fun x => fderiv_apply_parameter_measurable f hm hd x (basisVec q))
        ?_ (fun j => C (j + 1)) ?_
      · intro t
        rw [he t]
        exact contDiff_orderedDerivative α (hs t)
      · intro j hj t x
        rw [he t]
        exact (norm_iteratedFDeriv_orderedDerivative_le α
          ((hs t).of_le (by exact_mod_cast Nat.add_le_add_right hj 1)) x).trans
          (hb (j + 1) (by omega) t x)
    have hcast : (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) =
        (n : WithTop ℕ∞) + 1 := by simp
    rw [hcast]
    apply (contDiff_succ_iff_fderiv_apply (n := (n : WithTop ℕ∞))).mpr
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · simp
    · intro y
      have he : (fun x => fderiv ℝ (fun x => ∫ t, f t x ∂μ) x y) =
          fun x => ∑ q : Fin 2, y q • (∫ t, fderiv ℝ (f t) x (basisVec q) ∂μ) := by
        funext x
        rw [(hder x).fderiv]
        have hi : Integrable (fun t => fderiv ℝ (f t) x) μ :=
          (integrable_const (C 1)).mono'
            (fderiv_parameter_stronglyMeasurable f hm hd x).aestronglyMeasurable
            (MeasureTheory.ae_of_all μ (fun t => hb₁ t x))
        conv_lhs => arg 2; rw [vec_eq_sum_basis y]
        simp only [map_sum, map_smul]
        congr 1
        funext q
        rw [ContinuousLinearMap.integral_apply hi]
      rw [he]
      exact ContDiff.sum (fun q _ => (hcoord q).const_smul (y q))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Classical synthesis of the measurable-metric finite-past transverse Fourier response. -/

def profileCellResponse (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a t x : ℝ) : ℂ :=
  profileFourierSeries (profileModeResponse g f a t) x

theorem profileCellResponse_contDiff (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a t κ : ℝ) (hat : a ≤ t) (hκ : 0 < κ) (hi : IntegrableOn g (Icc a t))
    (hg : ∀ s ∈ Icc a t, κ ≤ g s) (q : ℕ) (C : ℕ → ℝ)
    (hC : ∀ j ≤ q, 0 ≤ C j) (hf : ∀ s ∈ Icc a t, ContDiff ℝ q (f s))
    (hp : ∀ s ∈ Icc a t, Function.Periodic (f s) 1)
    (hj : ∀ j ≤ q, ∀ s ∈ Icc a t, ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv j (f s) x‖ ≤ C j) :
    ContDiff ℝ q (profileCellResponse g f a t) := by
  apply profileFourierSeries_contDiff
  intro j hjq
  apply profileFourier_jet_summable _ j (C j / κ)
  intro n hn
  exact profileModeResponse_frequency_weight_bound g f a t κ hat hκ hi hg j (C j) (hC j hjq)
    (fun s hs => (hf s hs).of_le (by exact_mod_cast hjq)) hp (hj j hjq) n hn

theorem profileCellResponse_periodic (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a t : ℝ) :
    Function.Periodic (profileCellResponse g f a t) 1 := by
  intro x
  unfold profileCellResponse profileFourierSeries
  apply tsum_congr
  intro n
  rw [AddCircle.coe_add_period]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Real source majorants inherit the original weighted envelope bound. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceUniformMixedBudget (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q : ℕ) (lam : ℝ) (v u : ι) : ℝ :=
  ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ =>
    ‖γ.map‖ * ∑ α, constituentUniformMixedBudget I p q lam (γ.coeff α)).sum

omit [Fintype ι] in
theorem sourceUniformMixedBudget_nonneg (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (v u : ι) :
    0 ≤ sourceUniformMixedBudget edge I p q lam v u := by
  apply Finset.sum_nonneg
  intro d _
  apply List.sum_nonneg
  intro x hx
  obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun α _ =>
    constituentUniformMixedBudget_nonneg I p q lam hlam (γ.coeff α))

omit [Fintype ι] in
theorem sourceUniformMixedBudget_ofReal_le (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (v u : ι) :
    ENNReal.ofReal (sourceUniformMixedBudget edge I p q lam v u) ≤
      positiveSourceMixedBudget edge I p q lam v u := by
  have hγ (d : Finset.Icc 2 D) (γ : Constituent d.val (h u) (h v)) :
      ENNReal.ofReal (‖γ.map‖ * ∑ α, constituentUniformMixedBudget I p q lam (γ.coeff α)) ≤
        ENNReal.ofReal ‖γ.map‖ * ∑ α, constituentPositiveMixedBudget I p q lam (γ.coeff α) := by
    rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_sum_of_nonneg
      (fun α _ => constituentUniformMixedBudget_nonneg I p q lam hlam (γ.coeff α))]
    exact mul_le_mul_right (Finset.sum_le_sum fun α _ =>
      constituentUniformMixedBudget_ofReal_le I p q lam hlam (γ.coeff α)) _
  have hl (d : Finset.Icc 2 D) (l : List (Constituent d.val (h u) (h v))) :
      ENNReal.ofReal ((l.map fun γ =>
        ‖γ.map‖ * ∑ α, constituentUniformMixedBudget I p q lam (γ.coeff α)).sum) ≤
      (l.map fun γ => ENNReal.ofReal ‖γ.map‖ *
        ∑ α, constituentPositiveMixedBudget I p q lam (γ.coeff α)).sum := by
    induction l with
    | nil => simp
    | cons γ l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact ENNReal.ofReal_add_le.trans (add_le_add (hγ d γ) ih)
  unfold sourceUniformMixedBudget positiveSourceMixedBudget
  rw [ENNReal.ofReal_sum_of_nonneg (fun d _ => by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun α _ =>
      constituentUniformMixedBudget_nonneg I p q lam hlam (γ.coeff α)))]
  exact Finset.sum_le_sum fun d _ => hl d (edge v u d)

theorem sourceUniformMixedBudget_weighted_le (π : ι → ℝ) (edge : ConstituentEdges D h)
    (I : Set ℝ) (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (p q : ℕ) (hp : p ≤ qs) (hq : q ≤ qf) (v u : ι) :
    Real.sqrt (π u / π v) * sourceUniformMixedBudget edge I p q lam v u ≤
      sourceEnvelopeJetConstant p q Cj * b v u := by
  have hc : 0 ≤ sourceEnvelopeJetConstant p q Cj * b v u :=
    mul_nonneg (Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ => abs_nonneg _)
      (he.nonneg v u)
  apply (ENNReal.ofReal_le_ofReal_iff hc).mp
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (π u / π v)) * positiveSourceMixedBudget edge I p q lam v u :=
      mul_le_mul_right (sourceUniformMixedBudget_ofReal_le edge I p q lam hlam.le v u) _
    _ = _ := positiveSourceMixedBudget_reordering π edge I lam p q v u
    _ ≤ _ := normalizedSourceEnvelopeSum_le π edge I lam hlam Cj qs qf b Θ he p q hp hq v u

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set AVenhance.Infra.ODE
namespace AVRegularity.CycleComparison.Lift

/-! The explicit response inherits the compiled finite ODE's integral equation and time regularity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem transverseModeResponse_vector_solves (rate : ℝ) (g : ℝ → ℝ) (f : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (M : ℝ) (hM : 0 ≤ M) (hg : AEStronglyMeasurable g volume)
    (hgb : ∀ t, |g t| ≤ M) (hf : IntervalIntegrable f volume a b) :
    IsLinearIntegralSolution (fun t => (-rate * g t) • ContinuousLinearMap.id ℝ E)
        f 0 a b (fun t => transverseModeResponse rate g f a t) ∧
      AbsolutelyContinuousOnInterval (fun t => transverseModeResponse rate g f a t) a b := by
  let D := transverseModeVectorODEData rate g f a b hab M hM hg hgb hf
  obtain ⟨y, hy, _⟩ := D.existsUnique_absolutelyContinuous hab
  let u := extendCurve hab y
  have hu : AbsolutelyContinuousOnInterval u a b := hy.2
  have hgi : IntegrableOn g (uIcc a b) := by
    apply Measure.integrableOn_of_bounded isCompact_uIcc.measure_lt_top.ne hg
    exact Filter.Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hgb t
  have hrhs : IntervalIntegrable (linearRhs D.operator D.forcing u) volume a b := by
    exact (D.toLinearODE hab).rhs_intervalIntegrable y
  have hd : ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt u ((-rate * g t) • u t + f t) t := by
    simpa only [linearRhs, D, transverseModeVectorODEData, smul_apply,
      ContinuousLinearMap.id_apply] using!
      hy.1.ae_hasDerivAt hab hrhs
  have hua : u a = 0 := by
    simpa only [linearRhs, intervalIntegral.integral_same, add_zero, D, transverseModeVectorODEData] using
      hy.1 a ⟨le_rfl, hab⟩
  have heq : ∀ t ∈ Icc a b, u t = transverseModeResponse rate g f a t := by
    intro t ht
    have hsub := uIcc_subset_uIcc_left (a := a) (b := b) (x := t)
      (by simpa only [uIcc_of_le hab] using ht)
    apply transverseMode_vector_eq_response rate g f u a t (hgi.mono_set hsub)
      (hf.mono_set hsub) (hu.mono hsub) ?_ hua
    have hd' := hd.filter_mono (ae_mono (Measure.restrict_le_self : volume.restrict (uIcc a t) ≤ volume))
    filter_upwards [hd', ae_restrict_mem measurableSet_uIcc] with s hs hst
    exact hs (by simpa only [uIcc_of_le hab] using hsub hst)
  refine ⟨?_, hu.congr (fun t ht => heq t (by simpa only [uIcc_of_le hab] using ht))⟩
  intro t ht
  dsimp only
  rw [← heq t ht]
  have he := hy.1 t ht
  change u t = 0 + ∫ s in a..t, (-rate * g s) • u s + f s at he
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hsb : s ∈ Icc a b := by
    have hsub := uIcc_subset_uIcc_left (a := a) (b := b) (x := t)
      (by simpa only [uIcc_of_le hab] using ht)
    simpa only [uIcc_of_le hab] using hsub hs
  simp only [linearRhs, smul_apply, ContinuousLinearMap.id_apply, heq s hsb]

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! One explicit finite real-coordinate synthesis for the literal Fourier response on a coefficient carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def finiteProfileResponse (g : ℝ → ℝ) (f : ℝ → ℝ → E) (a t x : ℝ) : E :=
  let e := (Module.finBasis ℝ E).equivFunL
  e.symm (fun j => (profileCellResponse g
    (fun s y => ((e (f s y) j : ℝ) : ℂ)) a t x).re)

theorem finiteProfileResponse_coordinate (g : ℝ → ℝ) (f : ℝ → ℝ → E)
    (a t x : ℝ) (j : Fin (Module.finrank ℝ E)) :
    (Module.finBasis ℝ E).equivFunL (finiteProfileResponse g f a t x) j =
      (profileCellResponse g (fun s y =>
        (((Module.finBasis ℝ E).equivFunL (f s y) j : ℝ) : ℂ)) a t x).re := by
  unfold finiteProfileResponse
  rw [ContinuousLinearEquiv.apply_symm_apply]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.CycleComparison.Lift

/-! Slow regularity survives integration over any oriented finite time window. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
theorem parameter_intervalIntegral_contDiff (n : ℕ) (f : ℝ → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j)
    (a b : ℝ) : ContDiff ℝ (n : ℕ∞) (fun x => ∫ t in a..b, f t x) := by
  have h₁ := parameter_integral_contDiff (volume.restrict (Ioc a b)) n f hm hs C hb
  have h₂ := parameter_integral_contDiff (volume.restrict (Ioc b a)) n f hm hs C hb
  simpa only [intervalIntegral] using h₁.sub h₂

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! The finite-past profile construction has its literal zero initial field and zero initial jets. -/

@[simp] theorem profileModeResponse_same (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a : ℝ) (n : ℤ) :
    profileModeResponse g f a a n = 0 := by simp [profileModeResponse, transverseModeResponse]

@[simp] theorem profileCellResponse_same (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a : ℝ) :
    profileCellResponse g f a a = 0 := by
  funext x
  simp [profileCellResponse, profileFourierSeries]

@[simp] theorem profileCellResponse_initial_iteratedDeriv (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a : ℝ) (j : ℕ) : iteratedDeriv j (profileCellResponse g f a a) = 0 := by
  rw [profileCellResponse_same]
  funext x
  exact iteratedDeriv_const_zero

end AVRegularity.CycleComparison.Lift
end
