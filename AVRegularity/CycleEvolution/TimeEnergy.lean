-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Tactic.Monotonicity.Lemmas
public import AVenhance.Infra.ODE.Linear.Basic
public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
public import Homogenization.Ambient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

section
@[expose] public noncomputable section
open Metric Set
namespace AVRegularity.CycleEvolution

/-! A Banach-domain complex derivative estimate from the exact Schwarz lemma hypotheses. -/

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem complex_ball_fderiv_norm_le {f : V → E} {x : V} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball x R))
    (hb : ∀ y ∈ ball x R, ‖f y‖ ≤ M) :
    ‖fderiv ℂ f x‖ ≤ 2 * M / R := by
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball hf _ hR
  intro y hy
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_sub_le _ _).trans ((add_le_add (hb y hy)
    (hb x (mem_ball_self hR))).trans_eq (by ring))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Bounded almost strongly measurable potentials have bounded measurable representatives. -/

theorem complexBounded_measurable_representative {μ : Measure ℝ} (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f μ) (k : ℝ) (hk : 0 ≤ k)
    (hb : ∀ᵐ t ∂μ, ‖f t‖ ≤ k) :
    ∃ g : ℝ → ℂ, Measurable g ∧ f =ᵐ[μ] g ∧ ∀ t, ‖g t‖ ≤ k := by
  let g := fun t => if ‖hf.mk f t‖ ≤ k then hf.mk f t else 0
  have hm := hf.stronglyMeasurable_mk.measurable
  have hg : Measurable g := hm.ite (measurableSet_le hm.norm measurable_const) measurable_const
  refine ⟨g, hg, ?_, ?_⟩
  · filter_upwards [hf.ae_eq_mk, hb] with t ht hbt
    dsimp only [g]
    rw [← ht, ite_eq_left hbt]
  · intro t
    dsimp only [g]
    split_ifs with h
    · exact h
    · simpa only [norm_zero] using hk

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Filter Topology
namespace AVRegularity.CycleEvolution

/-! Actual Frechet derivatives yield complex directional difference quotients in the Banach norm. -/

theorem complexDirectional_differenceQuotient_tendsto {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : X → E) (f' : X →L[ℂ] E) (x v : X) (hf : HasFDerivAt f f' x) :
    Tendsto (fun h : ℂ => h⁻¹ • (f (x + h • v) - f x) - f' v) (𝓝[≠] 0) (𝓝 0) := by
  have hl : HasDerivAt (fun h : ℂ => x + h • v) v 0 := by
    have hm := (hasDerivAt_id (0 : ℂ)).smul_const v
    have ha := (hasDerivAt_const (0 : ℂ) x).add hm
    simpa only [zero_add, one_smul, id_eq, Pi.add_def] using ha
  have hd : HasDerivAt (fun h : ℂ => f (x + h • v)) (f' v) 0 := by
    have hf0 : HasFDerivAt f f' (x + (0 : ℂ) • v) := by
      simpa only [zero_smul, add_zero] using hf
    simpa only [Function.comp_def] using hf0.comp_hasDerivAt 0 hl
  have hq := hd.tendsto_slope_zero.sub (tendsto_const_nhds (x := f' v))
  simpa only [zero_add, zero_smul, add_zero, sub_self] using hq

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Canonical coordinate words for the two-index complex derivatives. -/

def complexFrequencyCanonicalWord (p : ℕ × ℕ) : Fin (p.1 + p.2) → Fin 2 → ℂ :=
  Fin.append (fun _ : Fin p.1 => Pi.single 0 1) (fun _ : Fin p.2 => Pi.single 1 1)

theorem complexFrequencyCanonicalWord_left (a b : ℕ) :
    complexFrequencyCanonicalWord (a + 1, b) =
      Fin.cons (Pi.single 0 1) (complexFrequencyCanonicalWord (a, b)) ∘
        Fin.cast (Nat.add_right_comm a 1 b) := by
  have h : (fun _ : Fin (a + 1) => (Pi.single 0 1 : Fin 2 → ℂ)) =
      Fin.cons (Pi.single 0 1) (fun _ : Fin a => Pi.single 0 1) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  unfold complexFrequencyCanonicalWord
  rw [h, Fin.append_cons]

theorem complexFrequencyCanonicalWord_right (a b : ℕ) :
    complexFrequencyCanonicalWord (a, b + 1) =
      Fin.snoc (complexFrequencyCanonicalWord (a, b)) (Pi.single 1 1) := by
  have h : (fun _ : Fin (b + 1) => (Pi.single 1 1 : Fin 2 → ℂ)) =
      Fin.snoc (fun _ : Fin b => Pi.single 1 1) (Pi.single 1 1) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  unfold complexFrequencyCanonicalWord
  rw [h, Fin.append_snoc]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped ContDiff
namespace AVRegularity.CycleEvolution

/-! Actual ordered complex frequency derivatives in a complete Banach space. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def complexFrequencyWordJet (f : (Fin 2 → ℂ) → E) (n : ℕ)
    (w : Fin n → Fin 2 → ℂ) (ξ : Fin 2 → ℂ) : E := iteratedFDeriv ℂ n f ξ w

theorem complexFrequencyWordJet_analyticAt (f : (Fin 2 → ℂ) → E)
    (U : Set (Fin 2 → ℂ)) (hf : AnalyticOnNhd ℂ f U) (n : ℕ)
    (w : Fin n → Fin 2 → ℂ) (ξ : Fin 2 → ℂ) (hξ : ξ ∈ U) :
    AnalyticAt ℂ (complexFrequencyWordJet f n w) ξ :=
  ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Fin 2 → ℂ) E w).analyticAt
    (iteratedFDeriv ℂ n f ξ)).comp (hf.iteratedFDeriv n ξ hξ)

theorem complexFrequencyWordJet_hasFDerivAt (f : (Fin 2 → ℂ) → E)
    (U : Set (Fin 2 → ℂ)) (hf : AnalyticOnNhd ℂ f U) (n : ℕ)
    (w : Fin n → Fin 2 → ℂ) (ξ : Fin 2 → ℂ) (hξ : ξ ∈ U) :
    HasFDerivAt (complexFrequencyWordJet f n w)
      ((fderiv ℂ (iteratedFDeriv ℂ n f) ξ).flipMultilinear w) ξ :=
  (hf.iteratedFDeriv n ξ hξ).differentiableAt.hasFDerivAt.continuousMultilinear_apply_const w

omit [CompleteSpace E] in
theorem complexFrequencyWordJet_derivative_cons (f : (Fin 2 → ℂ) → E) (n : ℕ)
    (w : Fin n → Fin 2 → ℂ) (v ξ : Fin 2 → ℂ) :
    (fderiv ℂ (iteratedFDeriv ℂ n f) ξ).flipMultilinear w v =
      complexFrequencyWordJet f (n + 1) (Fin.cons v w) ξ := by
  change fderiv ℂ (iteratedFDeriv ℂ n f) ξ v w =
    iteratedFDeriv ℂ (n + 1) f ξ (Fin.cons v w)
  rw [iteratedFDeriv_succ_apply_left]
  simp only [Fin.cons_zero, Fin.tail_cons]

theorem complexFrequencyWordJet_cons_eq_snoc (f : (Fin 2 → ℂ) → E) (n : ℕ)
    (w : Fin n → Fin 2 → ℂ) (v ξ : Fin 2 → ℂ) (hf : AnalyticAt ℂ f ξ) :
    complexFrequencyWordJet f (n + 1) (Fin.cons v w) ξ =
      complexFrequencyWordJet f (n + 1) (Fin.snoc w v) ξ := by
  have hc : ContDiffAt ℂ ω f ξ := hf.contDiffAt
  have he := hc.iteratedFDeriv_comp_perm (Fin.cons v w) (finRotate (n + 1))
  simpa only [complexFrequencyWordJet, Fin.snoc_eq_cons_rotate, Function.comp_def] using he.symm

omit [CompleteSpace E] in
theorem complexFrequencyWordJet_cast (f : (Fin 2 → ℂ) → E) {m n : ℕ} (h : m = n)
    (w : Fin n → Fin 2 → ℂ) (ξ : Fin 2 → ℂ) :
    complexFrequencyWordJet f m (w ∘ Fin.cast h) ξ = complexFrequencyWordJet f n w ξ := by
  subst n
  rfl

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Scalar algebra for actual normalized adjoint pairing ratios. -/

theorem complex_normalized_pairing_ratio (k d p n : ℂ)
    (hd : k * d = 1) (hp : p ≠ 0) : k * n = (p * n) / (p * d) := by
  have hdn : d ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hd
    exact zero_ne_one hd
  apply (eq_div_iff (mul_ne_zero hp hdn)).mpr
  calc
    _ = p * n * (k * d) := by ring
    _ = _ := by rw [hd, mul_one]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Quantitative polynomial increments with the full small-radius power retained. -/

theorem complex_power_increment_bound (z w : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) (n : ℕ) :
    ‖z ^ (n + 1) - w ^ (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) * M ^ n * ‖z - w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z ^ (n + 1 + 1) - w ^ (n + 1 + 1) =
        z ^ (n + 1) * (z - w) + (z ^ (n + 1) - w ^ (n + 1)) * w := by
      rw [pow_succ, pow_succ]
      ring
    have hzpow : ‖z ^ (n + 1)‖ ≤ M ^ (n + 1) := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hz _
    calc
      _ = ‖z ^ (n + 1) * (z - w) + (z ^ (n + 1) - w ^ (n + 1)) * w‖ := by rw [he]
      _ ≤ ‖z ^ (n + 1) * (z - w)‖ + ‖(z ^ (n + 1) - w ^ (n + 1)) * w‖ := norm_add_le _ _
      _ = ‖z ^ (n + 1)‖ * ‖z - w‖ + ‖z ^ (n + 1) - w ^ (n + 1)‖ * ‖w‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ M ^ (n + 1) * ‖z - w‖ +
          (((n + 1 : ℕ) : ℝ) * M ^ n * ‖z - w‖) * M := by
        exact add_le_add (mul_le_mul_of_nonneg_right hzpow (norm_nonneg _))
          (mul_le_mul ih hw (norm_nonneg _) (by positivity))
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Cancelling the nonzero integral phase in a conserved normalized pairing ratio. -/

theorem complex_ratio_phase_transport (p nB dB nA dA : ℂ) (hp : p ≠ 0)
    (he : nB / (p * dB) = nA / dA) : nB / dB = p * (nA / dA) := by
  have h := congrArg (fun z => p * z) he
  rwa [← mul_div_assoc p nB (p * dB), mul_div_mul_left _ _ hp] at h

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Extended-norm error bounds for bilinear perturbations converge without any Banach-space carrier. -/

/-- Four norm-small errors and two finite reference norms give a vanishing inverse error budget. -/
theorem ennreal_bilinear_error_tendsto_zero {A : Type*} (l : Filter A)
    (sf vf mf df : A → ℝ≥0∞) (b e : ℝ≥0∞) (hb : b ≠ ⊤) (he : e ≠ ⊤)
    (hs : Tendsto sf l (𝓝 0)) (hv : Tendsto vf l (𝓝 0))
    (hm : Tendsto mf l (𝓝 0)) (hd : Tendsto df l (𝓝 0)) :
    Tendsto (fun a => ENNReal.ofReal 13 *
      (sf a + vf a + 2 * mf a * (df a + e) + 2 * b * df a)) l (𝓝 0) := by
  have hde : Tendsto (fun a => df a + e) l (𝓝 e) := by
    simpa only [zero_add] using hd.add_const e
  have hme := ENNReal.Tendsto.mul hm (Or.inr he) hde (Or.inr (by simp))
  have hme2 := ENNReal.Tendsto.const_mul hme (a := 2) (Or.inr (by norm_num))
  have hb2 : 2 * b ≠ ⊤ := (ENNReal.mul_ne_top (by norm_num) hb)
  have hbd := ENNReal.Tendsto.const_mul hd (a := 2 * b) (Or.inr hb2)
  have hsum := ((hs.add hv).add hme2).add hbd
  have hlim := ENNReal.Tendsto.const_mul hsum (a := ENNReal.ofReal 13) (Or.inr (by simp))
  simpa only [mul_zero, zero_mul, add_zero, zero_add, mul_assoc] using hlim

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Finite extended-real absorption for the cell factorial majorant. -/

/-- A finite quantity bounded by a source plus half itself is at most twice the source. -/
theorem ennreal_half_absorption (e a : ℝ≥0∞) (he : e < ⊤)
    (h : e ≤ a + (1 / 2 : ℝ≥0∞) * e) : e ≤ 2 * a := by
  by_cases ha : a = ⊤
  · simp [ha]
  have hm : (1 / 2 : ℝ≥0∞) * e ≠ ⊤ :=
    (ENNReal.mul_lt_top (by norm_num) he).ne
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ha, hm⟩) h
  rw [ENNReal.toReal_add ha hm, ENNReal.toReal_mul] at hr
  norm_num at hr
  apply (ENNReal.toReal_le_toReal he.ne
    (ENNReal.mul_ne_top (by norm_num) ha)).mp
  rw [ENNReal.toReal_mul]
  norm_num
  linarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Abstract real-to-extended-real algebra for nonnegative energy budgets. -/

/-- A real energy inequality gives exactly the extended-real energy inequality for nonnegative data. -/
theorem cellEnergy_ofReal {A B G S F c C E : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hS : 0 ≤ S) (hF : 0 ≤ F)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (h : A + c * G ≤ E * (B + S + C * F)) :
    ENNReal.ofReal A + ENNReal.ofReal c * ENNReal.ofReal G ≤
      ENNReal.ofReal E *
        (ENNReal.ofReal B + ENNReal.ofReal S + ENNReal.ofReal C * ENNReal.ofReal F) := by
  rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hC,
    ← ENNReal.ofReal_add hB hS,
    ← ENNReal.ofReal_add (add_nonneg hB hS) (mul_nonneg hC hF),
    ← ENNReal.ofReal_mul hE, ← ENNReal.ofReal_add hA (mul_nonneg hc hG)]
  exact ENNReal.ofReal_le_ofReal h

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Coordinatewise L² membership for finite pointwise Hilbert arrays. -/

/-- Finite sums of strongly measurable functions are strongly measurable.
Adapted from the upstream FourierGalerkin MatrixOperator time-only lemma. -/
theorem cellFinite_sum_aestronglyMeasurable {α ι E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} (s : Finset ι) (f : ι → α → E)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact aestronglyMeasurable_const
  | @insert a s ha ih =>
    have he : (fun x => ∑ i ∈ insert a s, f i x) =
        fun x => f a x + ∑ i ∈ s, f i x := by
      funext x
      exact Finset.sum_insert ha
    rw [he]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A single entry of a finite pointwise Hilbert array is inserted by a norm-one operator. -/
def cellFiniteEntryCLM {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i : ι) :
    E →L[ℝ] PiLp 2 (fun _ : ι => E) :=
  let L : E →ₗ[ℝ] PiLp 2 (fun _ : ι => E) :=
    { toFun := PiLp.single (β := fun _ : ι => E) 2 i
      map_add' := by intro x y; exact PiLp.single_add (β := fun _ : ι => E) 2 i
      map_smul' := by
        intro r x
        apply PiLp.ext
        intro j
        by_cases h : j = i
        · subst j; simp
        · simp [h] }
  L.mkContinuous 1 (by intro x; change ‖PiLp.single (β := fun _ : ι => E) 2 i x‖ ≤ 1 * ‖x‖; rw [PiLp.norm_single, one_mul])

/-- Coordinatewise strong measurability gives strong measurability of a finite Hilbert array. -/
theorem cellFiniteArray_aestronglyMeasurable {α ι E : Type*} [MeasurableSpace α]
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    (f : α → ι → E) (hf : ∀ i, AEStronglyMeasurable (fun x => f x i) μ) :
    AEStronglyMeasurable (fun x => WithLp.toLp 2 (f x)) μ := by
  have hs := cellFinite_sum_aestronglyMeasurable Finset.univ
    (fun i x => cellFiniteEntryCLM i (f x i))
    (fun i _ => (cellFiniteEntryCLM i).continuous.comp_aestronglyMeasurable (hf i))
  apply hs.congr
  apply Filter.Eventually.of_forall
  intro x
  apply PiLp.ext
  intro j
  change (∑ i : ι, PiLp.single (β := fun _ : ι => E) 2 i (f x i)) j = f x j
  simp

/-- A finite Hilbert array is L² whenever each of its pointwise coordinates is L². -/
theorem cellFiniteArray_memLp {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    (f : α → ι → E) (hf : ∀ i, MemLp (fun x => f x i) 2 μ) :
    MemLp (fun x => WithLp.toLp 2 (f x)) 2 μ := by
  have hs := memLp_finsetSum Finset.univ
    (fun i _ => (cellFiniteEntryCLM i).comp_memLp' (hf i))
  apply hs.ae_eq
  apply Filter.Eventually.of_forall
  intro x
  apply PiLp.ext
  intro j
  change (∑ i : ι, PiLp.single (β := fun _ : ι => E) 2 i (f x i)) j = f x j
  simp

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace AVRegularity.CycleEvolution

/-! Integrating a uniform absolute coefficient majorant preserves its weighted budget. -/

variable {X E J : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [Countable J]

theorem integral_coefficient_majorant (μ : Measure X) (a : J → X → E)
    (w : J → ENNReal) (M : ENNReal)
    (ha : ∀ j, AEStronglyMeasurable (a j) μ)
    (hb : ∀ x, (∑' j, w j * ‖a j x‖ₑ) ≤ M) :
    (∑' j, w j * ‖∫ x, a j x ∂μ‖ₑ) ≤ M * μ Set.univ := by
  calc
    _ ≤ ∑' j, w j * ∫⁻ x, ‖a j x‖ₑ ∂μ :=
      ENNReal.tsum_le_tsum (fun j => mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _))
    _ = ∑' j, ∫⁻ x, w j * ‖a j x‖ₑ ∂μ := by
      congr 1
      funext j
      exact (lintegral_const_mul'' (w j) (ha j).enorm).symm
    _ = ∫⁻ x, ∑' j, w j * ‖a j x‖ₑ ∂μ :=
      (lintegral_tsum (fun j => aemeasurable_const.mul (ha j).enorm)).symm
    _ ≤ ∫⁻ _x, M ∂μ := lintegral_mono hb
    _ = _ := lintegral_const M

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Transfer Cauchy sequences along exact distance identities. -/

/-- Equality of pairwise distances transfers the Cauchy property. -/
theorem cellCauchy_of_distance_eq {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (u : ℕ → E) (v : ℕ → F) (h : ∀ n m, dist (u n) (u m) = dist (v n) (v m))
    (hv : CauchySeq v) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hv ε hε
  exact ⟨N, fun m hm n hn => by rw [h]; exact hN m hm n hn⟩

/-- Equal squared norms of vectors give equal norms. -/
theorem cellNorm_eq_of_square_eq {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (u : E) (v : F) (h : ‖u‖ ^ 2 = ‖v‖ ^ 2) : ‖u‖ = ‖v‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Square-integrable time derivatives for bounded measurable linear systems.
Together with the finite cell construction this supplies genuine strong H¹-in-time
paths when the projected forcing belongs to L². No infinite-dimensional limit is used. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
/-- Every continuous closed-time Hilbert curve is square integrable. -/
theorem continuousOn_memLp_Icc {a b : ℝ} (y : ℝ → H) (hy : ContinuousOn y (Icc a b)) :
    MemLp y 2 (volume.restrict (Icc a b)) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  apply MemLp.of_bound (hy.aestronglyMeasurable measurableSet_Icc) R
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hR t ht

/-- A bounded measurable operator applied to a continuous closed-time curve belongs to L². -/
theorem boundedOperator_apply_memLp {a b : ℝ} (A : ℝ → H →L[ℝ] H)
    (hA : AEStronglyMeasurable A volume) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t, ‖A t‖ ≤ C) (y : ℝ → H) (hy : ContinuousOn y (Icc a b)) :
    MemLp (fun t => A t (y t)) 2 (volume.restrict (Icc a b)) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  have hAm := hA.mono_measure (Measure.restrict_le_self :
    volume.restrict (Icc a b) ≤ volume)
  have hym : AEStronglyMeasurable y (volume.restrict (Icc a b)) :=
    hy.aestronglyMeasurable measurableSet_Icc
  have happ : AEStronglyMeasurable (fun t => A t (y t))
      (volume.restrict (Icc a b)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hAm.prodMk hym)
  apply MemLp.of_bound happ (C * R)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (A t).le_opNorm (y t) |>.trans
    ((mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hR t ht) hC))

/-- L² forcing and bounded measurable operators give an L² strong time derivative. -/
theorem linearRhs_memLp {a b : ℝ} (A : ℝ → H →L[ℝ] H)
    (hA : AEStronglyMeasurable A volume) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t, ‖A t‖ ≤ C) (y : ℝ → H) (hy : ContinuousOn y (Icc a b))
    (f : ℝ → H) (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    MemLp (AVenhance.Infra.ODE.linearRhs A f y) 2 (volume.restrict (Icc a b)) :=
  (boundedOperator_apply_memLp A hA C hC hbound y hy).add hf

/-- Transport a square-integrable strong derivative to another normed carrier. -/
theorem linearRhs_map_memLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (A : ℝ → H →L[ℝ] H)
    (hA : AEStronglyMeasurable A volume) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t, ‖A t‖ ≤ C) (y : ℝ → H) (hy : ContinuousOn y (Icc a b))
    (f : ℝ → H) (hf : MemLp f 2 (volume.restrict (Icc a b))) (J : H →L[ℝ] F) :
    MemLp (fun t => J (AVenhance.Infra.ODE.linearRhs A f y t))
      2 (volume.restrict (Icc a b)) := by
  exact J.comp_memLp' (linearRhs_memLp A hA C hC hbound y hy f hf)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Complex-linear restriction of Lp classes to a smaller measure. -/

variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X}

def lpComplexMeasureRestriction (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : μ ≤ ν) :
    Lp ℂ p ν →L[ℂ] Lp ℂ p μ := by
  let R : Lp ℂ p ν →L[ℝ] Lp ℂ p μ :=
    Lp.LpToLpOfMeasureLeSMul (c := 1) (by norm_num) (by simpa using h)
  have hr f : R f =ᵐ[μ] f := Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f
  let L : Lp ℂ p ν →ₗ[ℂ] Lp ℂ p μ :=
    { toFun := R
      map_add' := R.map_add
      map_smul' := fun c f => by
        change R (c • f) = c • R f
        apply Lp.ext
        have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le h
        filter_upwards [hr (c • f), hr f, Lp.coeFn_smul c (R f),
          hac.ae_eq (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
        change (c • R f) x = c • (R f) x at h3
        change (c • f) x = c • f x at h4
        rw [h1, h3, h2, h4] }
  exact L.mkContinuous ‖R‖ (fun f => R.le_opNorm f)

theorem lpComplexMeasureRestriction_ae (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : μ ≤ ν) (f : Lp ℂ p ν) : lpComplexMeasureRestriction p h f =ᵐ[μ] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by norm_num) (by simpa using h) f

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Representatives of finite complex linear combinations of Bochner classes. -/

theorem lpFiniteLinearCombination_ae {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    {p : ENNReal} {μ : Measure α} (c : ι → ℂ) (f : ι → Lp E p μ)
    (g : ι → α → E) (h : ∀ i, f i =ᵐ[μ] g i) :
    (∑ i, c i • f i : Lp E p μ) =ᵐ[μ] fun t => ∑ i, c i • g i t := by
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i => c i • f i)
  have hm : ∀ᵐ t ∂μ, ∀ i, (c i • f i : Lp E p μ) t = c i • g i t := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (f i), h i] with t ht hi
    simpa only [Pi.smul_apply, hi] using ht
  filter_upwards [hs, hm] with t ht hm'
  rw [ht]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => hm' i)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Bounded complex scalar multiplication from L-infinity coefficients to L2 forcing classes. -/

section
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

def lpTopScalarMultiplier (μ : Measure X) :
    Lp ℂ ∞ μ →L[ℂ] Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).holderL μ ∞ 2 2

theorem lpTopScalarMultiplier_ae (μ : Measure X) (c : Lp ℂ ∞ μ) (u : Lp E 2 μ) :
    lpTopScalarMultiplier μ c u =ᵐ[μ] fun x => c x • u x :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).coeFn_holder c u
end

/-! The L-infinity coefficient class is bounded by its literal uniform representative budget. -/

section
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem lpTopClass_enorm_le_iSup (μ : Measure X) (f : X → E) (hf : MemLp f ⊤ μ) :
    ‖hf.toLp f‖ₑ ≤ ⨆ x, ‖f x‖ₑ := by
  rw [Lp.enorm_toLp, eLpNorm_exponent_top hf.aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_enorm_bound
    (Filter.Eventually.of_forall (fun x => le_iSup (fun y => ‖f y‖ₑ) x))
end

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! The actual Bochner L2 norm reads the square integral in any real Hilbert space. -/

theorem lpTwoHilbert_normSq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure X) (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ∫ t, ‖u t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun t => real_inner_self_eq_norm_sq (u t)))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Bounded measurable spatial coefficients act linearly on L² classes.
As for the Galerkin `L²` multiplier construction,
with the continuity premise replaced by actual almost-everywhere strong measurability. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
/-- Bounded measurable operator fields preserve L² integrability. -/
theorem memLp_measurable_operator_mul {U : Set (Vec 2)}
    {C : Vec 2 → E →L[ℝ] F} {u : Vec 2 → E}
    (hC : AEStronglyMeasurable C (volume.restrict U))
    (hu : MemLp u 2 (volume.restrict U)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖C x‖ ≤ M) :
    MemLp (fun x => C x (u x)) 2 (volume.restrict U) := by
  apply (hu.const_smul M).of_le
  · exact (ContinuousLinearMap.apply ℝ F).flip.aestronglyMeasurable_comp₂
      hC hu.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    calc
      ‖C x (u x)‖ ≤ ‖C x‖ * ‖u x‖ := (C x).le_opNorm _
      _ ≤ M * ‖u x‖ := mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
      _ = ‖M • u x‖ := by rw [norm_smul, Real.norm_of_nonneg hM]

/-- Pointwise coefficient multiplication, using its L² integrability proof. -/
def measurableCoefficientL2 {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : AEStronglyMeasurable C (volume.restrict U)) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume.restrict U)) : Lp F 2 (volume.restrict U) :=
  (memLp_measurable_operator_mul hC (Lp.memLp u) hM hb).toLp (fun x => C x (u x))

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
theorem measurableCoefficientL2_ae {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : AEStronglyMeasurable C (volume.restrict U)) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume.restrict U)) :
    measurableCoefficientL2 C hC M hM hb u =ᵐ[volume.restrict U] fun x => C x (u x) :=
  (memLp_measurable_operator_mul hC (Lp.memLp u) hM hb).coeFn_toLp

/-- The coefficient multiplier respects the L² quotient and is linear. -/
def measurableCoefficientL2LinearMap {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : AEStronglyMeasurable C (volume.restrict U)) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M) :
    Lp E 2 (volume.restrict U) →ₗ[ℝ] Lp F 2 (volume.restrict U) where
  toFun := measurableCoefficientL2 C hC M hM hb
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [measurableCoefficientL2_ae C hC M hM hb (u + v),
      measurableCoefficientL2_ae C hC M hM hb u,
      measurableCoefficientL2_ae C hC M hM hb v,
      Lp.coeFn_add u v,
      Lp.coeFn_add (measurableCoefficientL2 C hC M hM hb u)
        (measurableCoefficientL2 C hC M hM hb v)] with x huv hu hv hadd hout
    rw [huv, hout, hadd]
    simp only [Pi.add_apply]
    rw [hu, hv]
    exact (C x).map_add _ _
  map_smul' := by
    intro c u
    apply Lp.ext
    filter_upwards [measurableCoefficientL2_ae C hC M hM hb (c • u),
      measurableCoefficientL2_ae C hC M hM hb u,
      Lp.coeFn_smul c u,
      Lp.coeFn_smul c (measurableCoefficientL2 C hC M hM hb u)] with x hcu hu hin hout
    change measurableCoefficientL2 C hC M hM hb (c • u) x =
      (c • measurableCoefficientL2 C hC M hM hb u) x
    rw [hcu, hout, hin]
    simp only [Pi.smul_apply]
    rw [hu]
    exact (C x).map_smul c _

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
theorem measurableCoefficientL2_norm_le {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : AEStronglyMeasurable C (volume.restrict U)) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume.restrict U)) :
    ‖measurableCoefficientL2 C hC M hM hb u‖ ≤ M * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [measurableCoefficientL2_ae C hC M hM hb u] with x hx
  rw [hx]
  exact ((C x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

/-- The genuine bounded L² coefficient operator. -/
def measurableCoefficientL2CLM {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : AEStronglyMeasurable C (volume.restrict U)) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M) :
    Lp E 2 (volume.restrict U) →L[ℝ] Lp F 2 (volume.restrict U) :=
  (measurableCoefficientL2LinearMap C hC M hM hb).mkContinuous M
    (measurableCoefficientL2_norm_le C hC M hM hb)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Abstract real time scaling for the frequency derivatives of the phase. -/

theorem phase_time_high_order_scaling (S δ K : ℝ) (hS : 1 ≤ S) (hδ : δ ≤ S)
    (hK : 0 ≤ K) (n : ℕ) (hn : 2 ≤ n) : K * δ ≤ K * Real.sqrt S ^ n := by
  have hroot : 1 ≤ Real.sqrt S := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hS
  have hp : Real.sqrt S ^ 2 ≤ Real.sqrt S ^ n := pow_le_pow_right₀ hroot hn
  rw [Real.sq_sqrt (by linarith : 0 ≤ S)] at hp
  exact mul_le_mul_of_nonneg_left (hδ.trans hp) hK

theorem phase_time_first_order_scaling (S δ K x : ℝ) (hS : 0 ≤ S) (hδ : δ ≤ S)
    (hK : 0 ≤ K) (hx : 0 ≤ x) :
    K * δ * x ≤ K * Real.sqrt S * (Real.sqrt S * x) := by
  calc
    _ ≤ K * S * x := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ hK) hx
    _ = K * (Real.sqrt S * Real.sqrt S) * x := by
      rw [← pow_two, Real.sq_sqrt hS]
    _ = _ := by ring

/-! Discrete dissipative recurrence bounds used for uniformly local forcing. -/

/-- The same geometric bound requires only the steps in the finite approximation interval. -/
theorem scalar_discrete_forced_bound_on (E : ℕ → ℝ) {q B : ℝ} (N : ℕ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hB : 0 ≤ B)
    (hstep : ∀ n, n < N → E (n + 1) ≤ q * E n + B) :
    ∀ n, n ≤ N → E n ≤ q ^ n * E 0 + B / (1 - q) := by
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hA : 0 ≤ B / (1 - q) := div_nonneg hB hden.le
  have he : q * (B / (1 - q)) + B = B / (1 - q) := by
    have hx := div_mul_cancel₀ B (ne_of_gt hden)
    nlinarith
  intro n
  induction n with
  | zero =>
    intro _
    simpa only [pow_zero, one_mul] using
      (show E 0 ≤ E 0 + B / (1 - q) by linarith)
  | succ n ih =>
    intro hn
    have hlt : n < N := Nat.lt_of_succ_le hn
    calc
      E (n + 1) ≤ q * E n + B := hstep n hlt
      _ ≤ q * (q ^ n * E 0 + B / (1 - q)) + B :=
        add_le_add (mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hlt)) hq) le_rfl
      _ = q ^ (n + 1) * E 0 + B / (1 - q) := by
        rw [mul_add, add_assoc, he, pow_succ]
        ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Real exponential estimates used by the normalized fibre energy argument. -/

theorem norm_bound_of_squared_exponential {E : Type*} [SeminormedAddCommGroup E]
    (u v : E) (c δ : ℝ)
    (h : ‖u‖ ^ 2 ≤ Real.exp (-c * δ) * ‖v‖ ^ 2) :
    ‖u‖ ≤ Real.exp (-c * δ / 2) * ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg u) (mul_nonneg (Real.exp_pos _).le (norm_nonneg v))).mp
  calc
    ‖u‖ ^ 2 ≤ Real.exp (-c * δ) * ‖v‖ ^ 2 := h
    _ = (Real.exp (-c * δ / 2) * ‖v‖) ^ 2 := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 1
      congr 1
      ring

theorem exponential_decay_integral_bound {a b c : ℝ} (hc : 0 < c) :
    (∫ t in a..b, Real.exp (-c * (t - a))) ≤ 1 / c := by
  have he : (∫ t in a..b, Real.exp (-c * (t - a))) =
      (1 - Real.exp (-c * (b - a))) / c := by
    have hd : ∀ t ∈ uIcc a b,
        HasDerivAt (fun t : ℝ => -Real.exp (-c * (t - a)) / c)
          (Real.exp (-c * (t - a))) t := by
      intro t _
      convert (((((hasDerivAt_id t).sub_const a).const_mul (-c)).exp).neg).div_const c using 1
      all_goals try funext x
      all_goals simp [div_eq_mul_inv, hc.ne']
    have hi : IntervalIntegrable (fun t : ℝ => Real.exp (-c * (t - a))) volume a b :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    simp only [sub_self, mul_zero, Real.exp_zero]
    ring
  rw [he]
  exact (div_le_div_iff_of_pos_right hc).mpr (by linarith [Real.exp_pos (-c * (b - a))])

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Abstract-real absorption of the degree factor in a high-order Taylor increment. -/

theorem nat_three_add_le_three_two_pow (m : ℕ) : m + 3 ≤ 3 * 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ]
    omega

theorem scalar_high_power_increment_bound (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hMR : M ≤ R / 2) (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) * M ^ (n - 1) ≤ (3 * M ^ 2 / R ^ 3) * R ^ n := by
  let m := n - 3
  have hne : n = m + 3 := by dsimp only [m]; omega
  have hnm : ((m + 3 : ℕ) : ℝ) ≤ 3 * (2 : ℝ) ^ m := by
    exact_mod_cast nat_three_add_le_three_two_pow m
  have hpow : M ^ m ≤ (R / 2) ^ m := pow_le_pow_left₀ hM hMR _
  have hlow : ((m + 3 : ℕ) : ℝ) * M ^ m ≤ 3 * R ^ m := by
    calc
      _ ≤ (3 * (2 : ℝ) ^ m) * (R / 2) ^ m :=
        mul_le_mul hnm hpow (pow_nonneg hM _) (by positivity)
      _ = _ := by rw [mul_assoc, ← mul_pow]; congr 1; ring
  rw [hne, show m + 3 - 1 = m + 2 by omega]
  calc
    _ = M ^ 2 * (((m + 3 : ℕ) : ℝ) * M ^ m) := by rw [pow_add]; ring
    _ ≤ M ^ 2 * (3 * R ^ m) := mul_le_mul_of_nonneg_left hlow (sq_nonneg M)
    _ = _ := by rw [pow_add]; field_simp

/-! Abstract-real bounds for dissipative inverse budgets. -/

/-- A decay rate at least one gives a uniformly positive geometric denominator. -/
theorem scalar_exp_denominator_lower {c : ℝ} (hc : 1 ≤ c) :
    (1 / 2 : ℝ) ≤ 1 - Real.exp (-c) := by
  have he : 2 ≤ Real.exp c := (by linarith : 2 ≤ c + 1).trans (Real.add_one_le_exp c)
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he
  have hsmall : Real.exp (-c) ≤ (1 / 2 : ℝ) := by
    simpa only [Real.exp_neg, one_div] using hi
  linarith

/-- A forced geometric budget is bounded by three times its unit-window source budget. -/
theorem scalar_inverse_budget_le {c B : ℝ} (hc : 1 ≤ c) (hB : 0 ≤ B) :
    B / (1 - Real.exp (-c)) + B ≤ 3 * B := by
  have hd := scalar_exp_denominator_lower hc
  have hdiv := div_le_div_of_nonneg_left hB (by norm_num : (0 : ℝ) < 1 / 2) hd
  have hi : B / (1 - Real.exp (-c)) ≤ 2 * B := by
    simpa only [div_eq_mul_inv, inv_div, one_mul, inv_inv, mul_comm] using hdiv
  linarith

/-- The scalar and flux source budget is controlled by the square of their summed norms. -/
theorem scalar_cell_source_budget_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 * x ^ 2 + 8 * y ^ 2 ≤ 8 * (x + y) ^ 2 := by
  nlinarith [mul_nonneg hx hy, sq_nonneg x]

/-! Abstract-real passage from squared spectral decay to the norm decay in the cell inverse statement. -/

/-- Squared decay at rate four times c implies norm decay at rate c divided by two. -/
theorem scalar_norm_decay_of_sq {r r0 c δ : ℝ} (hr : 0 ≤ r) (hr0 : 0 ≤ r0)
    (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hs : r ^ 2 ≤ Real.exp (-(4 * c) * δ) * r0 ^ 2) :
    r ≤ Real.exp (-c * δ / 2) * r0 := by
  have he : Real.exp (-(2 * c) * δ) ^ 2 = Real.exp (-(4 * c) * δ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : r ^ 2 ≤ (Real.exp (-(2 * c) * δ) * r0) ^ 2 := by
    rw [mul_pow, he]
    exact hs
  have hstrong := (sq_le_sq₀ hr (mul_nonneg (Real.exp_pos _).le hr0)).mp hsq
  have hcmp : -(2 * c) * δ ≤ -c * δ / 2 := by nlinarith [mul_nonneg hc hδ]
  exact hstrong.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcmp) hr0)

/-! Exact abstract-real passage from squared exponential decay to norm decay. -/

theorem scalar_sharp_norm_decay {r r0 c δ : ℝ} (hr : 0 ≤ r) (hr0 : 0 ≤ r0)
    (hs : r ^ 2 ≤ Real.exp (-(2 * c) * δ) * r0 ^ 2) :
    r ≤ Real.exp (-c * δ) * r0 := by
  have he : Real.exp (-c * δ) ^ 2 = Real.exp (-(2 * c) * δ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : r ^ 2 ≤ (Real.exp (-c * δ) * r0) ^ 2 := by
    rw [mul_pow, he]
    exact hs
  exact (sq_le_sq₀ hr (mul_nonneg (Real.exp_pos _).le hr0)).mp hsq

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Restriction of nonnegative unit-window forcing budgets to shorter intervals. -/

/-- Every short interval inside a time set has no more forcing than its enclosing unit window. -/
theorem scalar_short_interval_le_window (I : Set ℝ) (f : ℝ → ℝ) {s t : ℝ}
    (hst : s ≤ t) (hl : t - s ≤ 1) (hI : Icc s t ⊆ I)
    (hi : IntegrableOn f (Icc s (s + 1) ∩ I))
    (hn : ∀ᵐ r ∂volume.restrict (Icc s (s + 1) ∩ I), 0 ≤ f r) :
    (∫ r in s..t, f r) ≤ ∫ r in Icc s (s + 1) ∩ I, f r := by
  rw [intervalIntegral.integral_of_le hst, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_mono_set hi hn
  apply Filter.Eventually.of_forall
  intro r hr
  exact ⟨⟨hr.1, by have := hr.2; linarith⟩, hI hr⟩

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Strong time-regularity energy calculus. These helpers concern absolutely continuous
Hilbert curves with an almost-everywhere strong derivative. They do not assert the
Lions–Magenes theorem for derivatives in H⁻¹. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Strong time regularity, independent of any choice of spatial Sobolev representative. -/
structure StrongTimeRegularity (a b : ℝ) (u du : ℝ → H) : Prop where
  ac : AbsolutelyContinuousOnInterval u a b
  derivative : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt u (du t) t

/-- Squared Hilbert norm is absolutely continuous, including at zeros of the curve. -/
theorem StrongTimeRegularity.norm_sq_ac {a b : ℝ} {u du : ℝ → H}
    (h : StrongTimeRegularity a b u du) :
    AbsolutelyContinuousOnInterval (fun t => ‖u t‖ ^ 2) a b := by
  have hn : AbsolutelyContinuousOnInterval (fun t => ‖u t‖) a b :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval h.ac
  simpa only [pow_two] using hn.fun_mul hn

/-- The energy increment is proved from the strong time derivative, not assumed. -/
theorem StrongTimeRegularity.energy_increment {a b : ℝ} {u du : ℝ → H}
    (h : StrongTimeRegularity a b u du) :
    ‖u b‖ ^ 2 - ‖u a‖ ^ 2 = ∫ t in a..b, 2 * inner ℝ (u t) (du t) := by
  rw [← h.norm_sq_ac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae_restrict
  have hd := h.derivative.filter_mono
    (ae_mono (Measure.restrict_mono (uIoc_subset_uIcc) le_rfl))
  filter_upwards [hd] with t ht
  exact ht.norm_sq.deriv

/-- Difference curves retain the strong time-regularity interface. -/
theorem StrongTimeRegularity.sub {a b : ℝ} {u du v dv : ℝ → H}
    (hu : StrongTimeRegularity a b u du) (hv : StrongTimeRegularity a b v dv) :
    StrongTimeRegularity a b (fun t => u t - v t) (fun t => du t - dv t) := by
  refine ⟨hu.ac.sub hv.ac, ?_⟩
  filter_upwards [hu.derivative, hv.derivative] with t hut hvt
  exact hut.sub hvt

/-- Restriction keeps the strong derivative and absolute continuity. -/
theorem StrongTimeRegularity.mono {a b c d : ℝ} {u du : ℝ → H}
    (h : StrongTimeRegularity a b u du) (hsub : uIcc c d ⊆ uIcc a b) :
    StrongTimeRegularity c d u du := by
  exact ⟨h.ac.mono hsub, h.derivative.filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))⟩

/-- Energy production is integrable; this is a consequence of time regularity. -/
theorem StrongTimeRegularity.energy_integrable {a b : ℝ} {u du : ℝ → H}
    (h : StrongTimeRegularity a b u du) :
    IntervalIntegrable (fun t => 2 * inner ℝ (u t) (du t)) volume a b := by
  apply h.norm_sq_ac.intervalIntegrable_deriv.congr_ae
  have hd := h.derivative.filter_mono
    (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  filter_upwards [hd] with t ht
  exact ht.norm_sq.deriv

/-- A continuous linear map transports the time derivative and energy regularity. -/
theorem StrongTimeRegularity.map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a b : ℝ} {u du : ℝ → H} (h : StrongTimeRegularity a b u du)
    (J : H →L[ℝ] F) :
    StrongTimeRegularity a b (fun t => J (u t)) (fun t => J (du t)) := by
  refine ⟨J.lipschitzWith.comp_absolutelyContinuousOnInterval h.ac, ?_⟩
  filter_upwards [h.derivative] with t ht
  exact J.hasFDerivAt.comp_hasDerivAt t ht

/-- A fixed Hilbert test gives the integrated strong time equation. -/
theorem StrongTimeRegularity.pairing_increment {a b : ℝ} {u du : ℝ → H}
    (h : StrongTimeRegularity a b u du) (z : H) :
    inner ℝ (u b) z - inner ℝ (u a) z = ∫ t in a..b, inner ℝ (du t) z := by
  let L : H →L[ℝ] ℝ := innerSL ℝ z
  have hm := h.map L
  have hd := hm.derivative.filter_mono
    (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  have heq : (fun t => deriv (fun s => L (u s)) t) =ᵐ[volume.restrict (uIoc a b)]
      (fun t => L (du t)) := by
    filter_upwards [hd] with t ht
    exact ht.deriv
  have he := hm.ac.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae_restrict heq] at he
  simpa only [L, innerSL_apply_apply, real_inner_comm] using he.symm

end AVRegularity.CycleEvolution
end
end
