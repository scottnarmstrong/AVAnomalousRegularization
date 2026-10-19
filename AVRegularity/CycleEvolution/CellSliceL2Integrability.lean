-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellTimeReverseAdmissibility
import AVRegularity.CycleEvolution.StrongUniqueness
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Finite-interval source energy follows from the uniformly local norm by a finite cover. -/

section
variable {E : Type*} [NormedAddCommGroup E]

/-- A finite union of consecutive unit windows has finite source energy. -/
theorem cellUl_integer_interval_lt_top (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : cellUlNorm I f < ⊤) (a : ℝ) (n : ℕ) :
    (∫⁻ τ in Set.Icc a (a + n) ∩ I, cellL2Norm (f τ) ^ 2) < ⊤ := by
  induction n with
  | zero =>
    have hm : volume.restrict ({a} ∩ I) = 0 := Measure.restrict_eq_zero.mpr
      (measure_mono_null Set.inter_subset_left (measure_singleton a))
    simp only [Nat.cast_zero, add_zero, Set.Icc_self]
    rw [hm]
    simp
  | succ n ih =>
    have hcover : Set.Icc a (a + (n + 1 : ℕ)) ∩ I ⊆
        (Set.Icc a (a + n) ∩ I) ∪ (Set.Icc (a + n) (a + n + 1) ∩ I) := by
      rintro t ⟨ht, hI⟩
      by_cases h : t ≤ a + n
      · exact Or.inl ⟨⟨ht.1, h⟩, hI⟩
      · exact Or.inr ⟨⟨le_of_lt (lt_of_not_ge h), by simpa only [Nat.cast_add, Nat.cast_one,
          add_assoc] using ht.2⟩, hI⟩
    exact (lintegral_mono_set hcover).trans_lt
      ((lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.2
        ⟨ih, cellUl_window_integral_lt_top I f hf (a + n)⟩))

/-- Uniformly local L² sources have finite energy on every bounded interval. -/
theorem cellUl_interval_integral_lt_top (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : cellUlNorm I f < ⊤) (a b : ℝ) :
    (∫⁻ τ in Set.Icc a b ∩ I, cellL2Norm (f τ) ^ 2) < ⊤ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (b - a)
  apply (lintegral_mono_set (show Set.Icc a b ∩ I ⊆ Set.Icc a (a + n) ∩ I from ?_)).trans_lt
    (cellUl_integer_interval_lt_top I f hf a n)
  rintro t ⟨ht, hI⟩
  exact ⟨⟨ht.1, by have := ht.2; linarith⟩, hI⟩
end

/-! Uniformly local norm bounds from squared window budgets. -/

/-- A squared extended budget bounds its half-power without a finiteness side condition. -/
theorem ennreal_half_power_le_of_sq_le {a b : ENNReal} (h : a ≤ b ^ 2) :
    a ^ (1 / 2 : ℝ) ≤ b := by
  have hr := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show (2 : ℕ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one] using hr

/-- A uniform bound for squared unit-window budgets controls the actual uniformly local norm. -/
theorem cellUlNorm_le_of_window_sq_bound {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E) (B : ENNReal)
    (h : ∀ a : ℝ, (∫⁻ t in Set.Icc a (a + 1) ∩ I, cellL2Norm (f t) ^ 2) ≤ B ^ 2) :
    cellUlNorm I f ≤ B := by
  apply iSup_le
  intro a
  exact ennreal_half_power_le_of_sq_le (h a)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Exact finite fibres for regrouping the two-variable Taylor Cauchy product. -/

/-- Addition fibres are exactly the finite convolution rectangles. -/
def fibreCoefficientConvolutionFibreEquiv (p : ℕ × ℕ) :
    {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1 + q.2 = p} ≃ ↥(fibreCoefficientPairs p) where
  toFun q := ⟨q.1.1, by
    have h₁ := congrArg Prod.fst q.2
    have h₂ := congrArg Prod.snd q.2
    simp only [Prod.add_def] at h₁ h₂
    simp only [fibreCoefficientPairs, Finset.mem_product, Finset.mem_range]
    omega⟩
  invFun a := ⟨(a.1, fibreCoefficientComplement p a.1), fibreCoefficientPairs_recover a.2⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h₁ := congrArg Prod.fst q.2
      have h₂ := congrArg Prod.snd q.2
      apply Prod.ext <;> simp only [fibreCoefficientComplement, Prod.add_def] at h₁ h₂ ⊢ <;> omega
  right_inv a := by
    apply Subtype.ext
    rfl

/-- The first index of the inverse convolution fibre is unchanged. -/
theorem fibreCoefficientConvolutionFibreEquiv_symm_fst (p : ℕ × ℕ)
    (a : ↥(fibreCoefficientPairs p)) :
    ((fibreCoefficientConvolutionFibreEquiv p).symm a).1.1 = a.1 := rfl

/-- The second index of the inverse convolution fibre is its literal complement. -/
theorem fibreCoefficientConvolutionFibreEquiv_symm_snd (p : ℕ × ℕ)
    (a : ↥(fibreCoefficientPairs p)) :
    ((fibreCoefficientConvolutionFibreEquiv p).symm a).1.2 = fibreCoefficientComplement p a.1 := rfl

/-! Exact inverse indices for frequency shifts of coefficient series. -/

/-- Adding a frequency direction makes that direction active. -/
theorem fibreCoefficientDirections_add (p : ℕ × ℕ) (j : Fin 2) :
    j ∈ fibreCoefficientDirections (p + cellJetDirection j) := by
  fin_cases j <;> simp [fibreCoefficientDirections, cellJetDirection, Prod.add_def]

/-- Removing a direction immediately after adding it recovers the original index. -/
theorem fibreCoefficientPrevious_add (p : ℕ × ℕ) (j : Fin 2) :
    fibreCoefficientPrevious (p + cellJetDirection j) j = p := by
  fin_cases j <;> apply Prod.ext <;>
    simp [fibreCoefficientPrevious, cellJetDirection, Prod.add_def]

/-- Adding one frequency direction injects coefficient indices. -/
theorem fibreCoefficient_add_direction_injective (j : Fin 2) :
    Function.Injective (fun p : ℕ × ℕ => p + cellJetDirection j) := by
  intro p q h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext <;> simp only [Prod.add_def] at h1 h2 ⊢ <;> omega

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Geometric coefficient weights for finite nonlinear Taylor majorants. -/

/-- The unweighted Taylor coefficient energy carries the ordinary geometric frequency weight. -/
def fibreCoefficientWeight (ρ : ℝ≥0∞) (p : ℕ × ℕ) : ℝ≥0∞ := ρ ^ (p.1 + p.2)

/-- One frequency factor contributes one power of the geometric weight. -/
theorem fibreCoefficientWeight_previous (ρ : ℝ≥0∞) {p : ℕ × ℕ} {j : Fin 2}
    (hj : j ∈ fibreCoefficientDirections p) :
    fibreCoefficientWeight ρ p = ρ * fibreCoefficientWeight ρ (fibreCoefficientPrevious p j) := by
  unfold fibreCoefficientWeight
  rw [← fibreCoefficientPrevious_order hj, pow_succ]
  ac_rfl

/-- Coefficient convolution factors the geometric weight exactly. -/
theorem fibreCoefficientWeight_convolution (ρ : ℝ≥0∞) {p a : ℕ × ℕ}
    (ha : a ∈ fibreCoefficientPairs p) :
    fibreCoefficientWeight ρ p =
      fibreCoefficientWeight ρ a * fibreCoefficientWeight ρ (fibreCoefficientComplement p a) := by
  have hb := fibreCoefficientPairs_bounds ha
  have ho : p.1 + p.2 = (a.1 + a.2) +
      ((fibreCoefficientComplement p a).1 + (fibreCoefficientComplement p a).2) := by
    dsimp only [fibreCoefficientComplement]
    omega
  unfold fibreCoefficientWeight
  rw [ho, pow_add]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! The actual bounded, measurable scaled drift multiplier of the fibre graph. -/

/-- The complex bilinear coupling of the scaled cell drift to a fixed frequency. -/
def fibreDriftCoupling (η : ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ) :
    ℝ → Vec 2 → ℂ :=
  fun t x => (Real.sqrt η : ℂ) * ∑ k, (v t x k : ℂ) * ξ k

/-- The literal scaled drift coupling is jointly measurable. -/
theorem fibreDriftCoupling_measurable (η : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) :
    Measurable (Function.uncurry (fibreDriftCoupling η v ξ)) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  exact (Complex.continuous_ofReal.measurable.comp
    ((measurable_pi_apply k).comp hv.1)).mul_const (ξ k)

/-- The coupling bound is uniform in the contrast and the unscaled drift. -/
theorem fibreDriftCoupling_norm_le (η Cw : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2) :
    ‖fibreDriftCoupling η v ξ t x‖ ≤ Cw * fibreNorm ξ :=
  fibreScaledDrift_norm_le η Cw (v t x) ξ (hw t x)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Continuity of the literal fibre norm and the exact affine frequency change. -/

theorem fibreNorm_continuous : Continuous (fibreNorm : (Fin 2 → ℂ) → ℝ) := by
  unfold fibreNorm
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ (fun j _ => (continuous_apply j).norm.pow 2))

theorem fibreCoefficients_theta_add_shift (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (ξ ζ : Fin 2 → ℂ) (lam : ℝ → ℂ) :
    (fibreCoefficients η G v ξ lam).θ + (Real.sqrt η : ℂ) • (ζ - ξ) =
      (fibreCoefficients η G v ζ lam).θ := by
  funext j
  change (Real.sqrt η : ℂ) * ξ j + (Real.sqrt η : ℂ) * (ζ j - ξ j) =
    (Real.sqrt η : ℂ) * ζ j
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Exact parity algebra for the minus-conjugate symmetry of triangular Taylor coefficients. -/

def fibreRealitySign (p : ℕ × ℕ) : ℂ := (-1) ^ (p.1 + p.2)

theorem fibreRealitySign_previous {p : ℕ × ℕ} {j : Fin 2}
    (hj : j ∈ fibreCoefficientDirections p) :
    fibreRealitySign p = -fibreRealitySign (fibreCoefficientPrevious p j) := by
  unfold fibreRealitySign
  rw [← fibreCoefficientPrevious_order hj, pow_succ]
  ring

theorem fibreRealitySign_pair {p a : ℕ × ℕ} (ha : a ∈ fibreCoefficientPairs p) :
    fibreRealitySign a * fibreRealitySign (fibreCoefficientComplement p a) = fibreRealitySign p := by
  have hh := fibreCoefficientPairs_bounds ha
  have he : (a.1 + a.2) + ((fibreCoefficientComplement p a).1 +
      (fibreCoefficientComplement p a).2) = p.1 + p.2 := by
    simp only [fibreCoefficientComplement]
    omega
  unfold fibreRealitySign
  rw [← pow_add, he]

theorem fibreRealitySign_direction (j : Fin 2) : fibreRealitySign (cellJetDirection j) = -1 := by
  fin_cases j <;> norm_num [fibreRealitySign, cellJetDirection]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Actual triangular coefficients for the reciprocal of one plus a zero-constant scalar series. -/

theorem fibreCoefficientComplement_order_lt {p a : ℕ × ℕ}
    (ha : a ∈ fibreCoefficientPairs p) (ha0 : a ≠ 0) :
    (fibreCoefficientComplement p a).1 + (fibreCoefficientComplement p a).2 < p.1 + p.2 := by
  have hb := fibreCoefficientPairs_bounds ha
  have haorder : 0 < a.1 + a.2 := by
    by_contra h
    have hz : a = 0 := by
      apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> omega
    exact ha0 hz
  dsimp only [fibreCoefficientComplement]
  omega

def fibreScalarInverseCoefficient (d : ℕ × ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  if p = 0 then 1 else
    -∑ a : ((fibreCoefficientPairs p).filter (fun a => a ≠ 0)),
      d a * fibreScalarInverseCoefficient d (fibreCoefficientComplement p a)
termination_by p.1 + p.2
decreasing_by
  exact fibreCoefficientComplement_order_lt (Finset.mem_filter.mp a.property).1
    (Finset.mem_filter.mp a.property).2

theorem fibreScalarInverseCoefficient_zero (d : ℕ × ℕ → ℂ) :
    fibreScalarInverseCoefficient d 0 = 1 := by
  rw [fibreScalarInverseCoefficient]
  simp

theorem fibreScalarInverseCoefficient_nonzero (d : ℕ × ℕ → ℂ) {p : ℕ × ℕ} (hp : p ≠ 0) :
    fibreScalarInverseCoefficient d p =
      -∑ a ∈ (fibreCoefficientPairs p).filter (fun a => a ≠ 0),
        d a * fibreScalarInverseCoefficient d (fibreCoefficientComplement p a) := by
  rw [fibreScalarInverseCoefficient, ite_eq_right hp]
  exact congrArg Neg.neg (Finset.sum_finset_coe
    (fun a : ℕ × ℕ => d a * fibreScalarInverseCoefficient d (fibreCoefficientComplement p a))
    ((fibreCoefficientPairs p).filter (fun a => a ≠ 0)))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Absolute L1 summability is preserved by the finite linear operations of a weak integrand. -/

/-- Sum two absolutely L1-summable families on the same measure space. -/
theorem cellL1Series_add_lt_top {J X : Type*} [Countable J] [MeasurableSpace X]
    (μ : Measure X) (f g : J → X → ℂ)
    (hf : (∑' j, eLpNorm (f j) 1 μ) < ⊤) (hg : (∑' j, eLpNorm (g j) 1 μ) < ⊤) :
    (∑' j, eLpNorm (f j + g j) 1 μ) < ⊤ := by
  calc
    _ ≤ ∑' j, (eLpNorm (f j) 1 μ + eLpNorm (g j) 1 μ) :=
      ENNReal.tsum_le_tsum (fun j => eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 1))
    _ = (∑' j, eLpNorm (f j) 1 μ) + ∑' j, eLpNorm (g j) 1 μ := ENNReal.tsum_add
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hf, hg⟩

/-- Negation preserves absolute L1 summability. -/
theorem cellL1Series_neg_lt_top {J X : Type*} [Countable J] [MeasurableSpace X]
    (μ : Measure X) (f : J → X → ℂ) (hf : (∑' j, eLpNorm (f j) 1 μ) < ⊤) :
    (∑' j, eLpNorm (-f j) 1 μ) < ⊤ := by
  simpa only [eLpNorm_neg] using hf

/-- A finite sum of absolutely L1-summable families is absolutely L1 summable. -/
theorem cellL1Series_finset_sum_lt_top {J X K : Type*} [Countable J] [MeasurableSpace X]
    (μ : Measure X) (s : Finset K) (f : K → J → X → ℂ)
    (hf : ∀ k ∈ s, (∑' j, eLpNorm (f k j) 1 μ) < ⊤) :
    (∑' j, eLpNorm (∑ k ∈ s, f k j) 1 μ) < ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact cellL1Series_add_lt_top μ (f k) (fun j => ∑ l ∈ s, f l j)
      (hf k (Finset.mem_insert_self k s))
      (ih (fun l hl => hf l (Finset.mem_insert_of_mem hl)))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The fixed-test product series is absolutely summable in its L1 seminorm. -/

/-- Multiplication by a fixed L2 test sends an absolutely L2-summable family to an absolutely L1-summable family. -/
theorem cellL2_product_series_eLpNorm_one_lt_top {J X : Type*} [Countable J] [MeasurableSpace X]
    (μ : Measure X) (f : J → X → ℂ) (g : X → ℂ)
    (hf : ∀ j, AEStronglyMeasurable (f j) μ) (hg : MemLp g 2 μ)
    (hs : (∑' j, eLpNorm (f j) 2 μ) < ⊤) :
    (∑' j, eLpNorm (fun x => f j x * g x) 1 μ) < ⊤ := by
  have he j : eLpNorm (fun x => f j x * g x) 1 μ = ∫⁻ x, ‖f j x * g x‖ₑ ∂μ :=
    eLpNorm_one_eq_lintegral_enorm ((hf j).mul hg.aestronglyMeasurable)
  simp_rw [he]
  exact cellL2_product_series_lintegral_lt_top μ f g hf hg hs

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute convergence of double cell pairings follows from the two L2 series bounds. -/

theorem cellMean_double_series_summable_norm {J K : Type*} [Countable J] [Countable K]
    (f : J → Vec 2 → ℂ) (g : K → Vec 2 → ℂ)
    (hf : (∑' j, cellL2Norm (f j)) < ⊤) (hg : (∑' k, cellL2Norm (g k)) < ⊤) :
    Summable (fun q : J × K => ‖cellMean (fun x => f q.1 x * g q.2 x)‖) := by
  have hfm j : MemLp (f j) 2 (volume.restrict AVenhance.unitCube) :=
    (ENNReal.le_tsum j).trans_lt hf
  have hgm k : MemLp (g k) 2 (volume.restrict AVenhance.unitCube) :=
    (ENNReal.le_tsum k).trans_lt hg
  have hb (q : J × K) : ‖cellMean (fun x => f q.1 x * g q.2 x)‖ₑ ≤
      cellL2Norm (f q.1) * cellL2Norm (g q.2) :=
    (enorm_integral_le_lintegral_enorm _).trans
      (cellL2_product_lintegral_le _ _ _ (hfm q.1).aestronglyMeasurable
        (hgm q.2).aestronglyMeasurable)
  have hh : (∑' q : J × K, ‖cellMean (fun x => f q.1 x * g q.2 x)‖ₑ) < ⊤ := by
    apply (ENNReal.tsum_le_tsum hb).trans_lt
    rw [ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    exact ENNReal.mul_lt_top hf hg
  exact tsum_enorm_ne_top_iff_summable_norm.mp hh.ne

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! The actual near-identity quadratic-form premise gives sharp complex diffusion coercivity. -/

theorem cellMetric_complex_near_identity_coercive
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {g : ℝ}
    (hG : IsMetricNearIdentity G g) (t : ℝ) (x : Vec 2) (w : Fin 2 → ℂ) :
    (1 - g) * ∑ i, ‖w i‖ ^ 2 ≤ cellMetricPairing (G t x) w w := by
  have hr := (abs_le.mp (hG t x (fun i => (w i).re))).1
  have hi := (abs_le.mp (hG t x (fun i => (w i).im))).1
  have he (i : Fin 2) : ‖w i‖ ^ 2 = (w i).re ^ 2 + (w i).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  simp [cellMetricPairing, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply,
    Complex.mul_re, Complex.mul_im, he] at *
  nlinarith

/-! Elliptic metrics and their differences have finite entrywise uniform size. -/

/-- The normalized ellipticity hypotheses give a uniform entrywise bound. -/
theorem cellMetricSupNorm_le_two
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G) :
    cellMetricSupNorm G ≤ 2 := by
  apply iSup_le
  intro t
  apply iSup_le
  intro x
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  rw [Real.enorm_eq_ofReal_abs]
  exact (ENNReal.ofReal_le_ofReal (cellMetric_entry_bound hG t x i j)).trans_eq (by norm_num)

/-- Differences of normalized elliptic metrics have finite uniform size. -/
theorem cellMetricSupNorm_sub_lt_top
    {G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (hH : IsCellMetric H) :
    cellMetricSupNorm (H - G) < ⊤ := by
  rw [sub_eq_add_neg]
  have h := cellMetricSupNorm_add H (-G)
  rw [cellMetricSupNorm_neg] at h
  exact h.trans_lt ((add_le_add (cellMetricSupNorm_le_two hH)
    (cellMetricSupNorm_le_two hG)).trans_lt (by norm_num))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The order-one ordered jet consists of its value and the two gradient components. -/

/-- Every order-one index is the value or one of the first derivatives. -/
theorem cellOrderOneIndex_cases (a : JetIndex2 1) :
    a = valueIndex2 1 ∨ ∃ j : Fin 2, a = ⟨⟨1, by decide⟩, fun _ => j⟩ := by
  rcases a with ⟨k, w⟩
  fin_cases k
  · left
    simp only [valueIndex2, valueIndex]
    congr 1
    funext i
    exact Fin.elim0 i
  · right
    refine ⟨w 0, ?_⟩
    congr 1
    funext i
    have hi : i = 0 := Fin.eq_zero i
    rw [hi]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Pointwise drift and potential bounds for the cell energy calculation. -/

/-- Realification of a directional drift term tested against the conjugate value. -/
def cellDriftPairing (v : Fin 2 → ℝ) (p : Fin 2 → ℂ) (u : ℂ) : ℝ :=
  (∑ j, (v j : ℂ) * p j * star u).re

/-- Drift pairing is linear in the gradient argument. -/
theorem cellDriftPairing_add (v : Fin 2 → ℝ) (p a : Fin 2 → ℂ) (u : ℂ) :
    cellDriftPairing v (p + a) u = cellDriftPairing v p u + cellDriftPairing v a u := by
  simp [cellDriftPairing, mul_add, add_mul, Finset.sum_add_distrib]

/-- Directional drift bounds control the full complex pairing. -/
theorem cellDriftPairing_abs_le (v : Fin 2 → ℝ) (p : Fin 2 → ℂ) (u : ℂ)
    (V : ℝ) (hv : ∀ j, |v j| ≤ |V|) :
    |cellDriftPairing v p u| ≤ ∑ j, |V| * ‖p j‖ * ‖u‖ := by
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_star]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hv j) (norm_nonneg _)) (norm_nonneg _)

/-- A small gradient coefficient absorbs the principal drift term. -/
theorem cellDriftPairing_young (v : Fin 2 → ℝ) (p : Fin 2 → ℂ) (u : ℂ)
    (V : ℝ) (hv : ∀ j, |v j| ≤ |V|) :
    2 * |cellDriftPairing v p u| ≤
      (1 / 8) * ∑ j, ‖p j‖ ^ 2 + 16 * V ^ 2 * ‖u‖ ^ 2 := by
  have hb := cellDriftPairing_abs_le v p u V hv
  simp only [Fin.sum_univ_two] at *
  nlinarith [sq_nonneg (‖p 0‖ / 4 - 2 * |V| * ‖u‖),
    sq_nonneg (‖p 1‖ / 4 - 2 * |V| * ‖u‖), sq_abs V]

/-- The Bloch part of the drift is a zero-order energy term. -/
theorem cellDriftPairing_bloch (v : Fin 2 → ℝ) (θ : Fin 2 → ℂ) (u : ℂ)
    (V : ℝ) (hv : ∀ j, |v j| ≤ |V|) :
    2 * |cellDriftPairing v (cellBlochShift θ u) u| ≤
      (2 * V ^ 2 + ∑ j, ‖θ j‖ ^ 2) * ‖u‖ ^ 2 := by
  have hb := cellDriftPairing_abs_le v (cellBlochShift θ u) u V hv
  simp only [cellBlochShift, norm_mul, Complex.norm_I, one_mul, Fin.sum_univ_two] at *
  have hcoef : 2 * |V| * (‖θ 0‖ + ‖θ 1‖) ≤ 2 * V ^ 2 + ‖θ 0‖ ^ 2 + ‖θ 1‖ ^ 2 := by
    nlinarith [sq_nonneg (|V| - ‖θ 0‖), sq_nonneg (|V| - ‖θ 1‖), sq_abs V]
  have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖u‖)
  nlinarith

/-- A bounded complex potential contributes at most its modulus times the value energy. -/
theorem cellPotential_re_le (κ u : ℂ) (k : ℝ) (hk : ‖κ‖ ≤ k) :
    (κ * u * star u).re ≤ k * ‖u‖ ^ 2 := by
  apply (Complex.re_le_norm _).trans
  rw [norm_mul, norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hk (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Quantitative finite-cover bounds for uniformly local cell energies. -/

/-- `n` consecutive windows cost at most `n` times the squared uniformly local norm. -/
theorem cellUl_integer_interval_sq_le {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E) (a : ℝ) (n : ℕ) :
    (∫⁻ τ in Set.Icc a (a + n) ∩ I, cellL2Norm (f τ) ^ 2) ≤
      (n : ℝ≥0∞) * cellUlNorm I f ^ 2 := by
  induction n with
  | zero =>
    have hm : volume.restrict ({a} ∩ I) = 0 := Measure.restrict_eq_zero.mpr
      (measure_mono_null Set.inter_subset_left (measure_singleton a))
    simp only [Nat.cast_zero, add_zero, Set.Icc_self]
    rw [hm]
    simp
  | succ n ih =>
    have hcover : Set.Icc a (a + (n + 1 : ℕ)) ∩ I ⊆
        (Set.Icc a (a + n) ∩ I) ∪ (Set.Icc (a + n) (a + n + 1) ∩ I) := by
      rintro t ⟨ht, hI⟩
      by_cases h : t ≤ a + n
      · exact Or.inl ⟨⟨ht.1, h⟩, hI⟩
      · exact Or.inr ⟨⟨le_of_lt (lt_of_not_ge h), by simpa only [Nat.cast_add, Nat.cast_one,
          add_assoc] using ht.2⟩, hI⟩
    calc
      _ ≤ (∫⁻ τ in Set.Icc a (a + n) ∩ I, cellL2Norm (f τ) ^ 2) +
          ∫⁻ τ in Set.Icc (a + n) (a + n + 1) ∩ I, cellL2Norm (f τ) ^ 2 :=
        (lintegral_mono_set hcover).trans (lintegral_union_le _ _ _)
      _ ≤ (n : ℝ≥0∞) * cellUlNorm I f ^ 2 + cellUlNorm I f ^ 2 :=
        add_le_add ih (cellUl_window_integral_le I f (a + n))
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-! Product-space formulas for the uniformly local norm and its triangle inequality. -/

section
variable {E : Type*} [NormedAddCommGroup E]

/-- Each window size is exactly its joint L² seminorm, including infinite values. -/
theorem cellUl_window_eq_product (I : Set ℝ) (f : ℝ → Vec 2 → E) (a : ℝ)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Set.Icc a (a + 1) ∩ I)).prod
        (volume.restrict AVenhance.unitCube))) :
    (∫⁻ t in Set.Icc a (a + 1) ∩ I, cellL2Norm (f t) ^ 2) ^ (1 / 2 : ℝ) =
      eLpNorm (Function.uncurry f) 2
        ((volume.restrict (Set.Icc a (a + 1) ∩ I)).prod
          (volume.restrict AVenhance.unitCube)) := by
  have hs : (eLpNorm (Function.uncurry f) 2
      ((volume.restrict (Set.Icc a (a + 1) ∩ I)).prod
        (volume.restrict AVenhance.unitCube))) ^ 2 =
      ∫⁻ t in Set.Icc a (a + 1) ∩ I, cellL2Norm (f t) ^ 2 := by
    rw [← ENNReal.rpow_two]
    have hp := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hf
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at hp
    rw [hp]
    rw [lintegral_prod _ (hf.enorm.pow_const 2)]
    apply lintegral_congr_ae
    filter_upwards [hf.prodMk_left] with t ht
    simpa only [Function.uncurry_def, ENNReal.rpow_two] using
      (cellL2Norm_sq_eq_lintegral ht).symm
  rw [← hs]
  simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show (2 : ℕ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]

/-- Joint almost measurability suffices for the uniformly local triangle inequality. -/
theorem cellUlNorm_add (I : Set ℝ) (f g : ℝ → Vec 2 → E)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hg : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm I (f + g) ≤ cellUlNorm I f + cellUlNorm I g := by
  apply iSup_le
  intro a
  have hm : (volume.restrict (Set.Icc a (a + 1) ∩ I)).prod
      (volume.restrict AVenhance.unitCube) ≤
      (volume.restrict I).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono Set.inter_subset_right le_rfl) le_rfl
  have hf' := hf.mono_measure hm
  have hg' := hg.mono_measure hm
  rw [cellUl_window_eq_product I (f + g) a (hf'.add hg')]
  calc
    _ ≤ eLpNorm (Function.uncurry f) 2 _ + eLpNorm (Function.uncurry g) 2 _ :=
      eLpNorm_add_le (by norm_num)
    _ ≤ cellUlNorm I f + cellUlNorm I g := by
      rw [← cellUl_window_eq_product I f a hf', ← cellUl_window_eq_product I g a hg']
      unfold cellUlNorm
      apply add_le_add
      · exact le_iSup (fun b : ℝ => (∫⁻ t in Set.Icc b (b + 1) ∩ I, cellL2Norm (f t) ^ 2) ^ (1 / 2 : ℝ)) a
      · exact le_iSup (fun b : ℝ => (∫⁻ t in Set.Icc b (b + 1) ∩ I, cellL2Norm (g t) ^ 2) ^ (1 / 2 : ℝ)) a

/-- Real scaling of a joint field scales its uniformly local size. -/
theorem cellUlNorm_smul [NormedSpace ℝ E] (I : Set ℝ) (r : ℝ)
    (f : ℝ → Vec 2 → E)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm I (r • f) ≤ ‖r‖ₑ * cellUlNorm I f := by
  apply iSup_le
  intro a
  have hm : (volume.restrict (Set.Icc a (a + 1) ∩ I)).prod
      (volume.restrict AVenhance.unitCube) ≤
      (volume.restrict I).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono Set.inter_subset_right le_rfl) le_rfl
  have hf' := hf.mono_measure hm
  rw [cellUl_window_eq_product I (r • f) a (hf'.const_smul r)]
  change eLpNorm (r • Function.uncurry f) 2 _ ≤ _
  rw [eLpNorm_const_smul, ← cellUl_window_eq_product I f a hf']
  gcongr
  exact le_iSup (fun b : ℝ => (∫⁻ t in Set.Icc b (b + 1) ∩ I,
    cellL2Norm (f t) ^ 2) ^ (1 / 2 : ℝ)) a

/-- A pointwise operator bound gives the same bound on every uniformly local window. -/
theorem cellUlNorm_le_mul {H : Type*} [NormedAddCommGroup H]
    (I : Set ℝ) (f : ℝ → Vec 2 → E) (g : ℝ → Vec 2 → H)
    (B : ℝ) (hB : 0 ≤ B)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hg : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hbound : ∀ t x, ‖f t x‖ ≤ B * ‖g t x‖) :
    cellUlNorm I f ≤ ENNReal.ofReal B * cellUlNorm I g := by
  apply iSup_le
  intro a
  have hm : (volume.restrict (Set.Icc a (a + 1) ∩ I)).prod
      (volume.restrict AVenhance.unitCube) ≤
      (volume.restrict I).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono Set.inter_subset_right le_rfl) le_rfl
  have hf' := hf.mono_measure hm
  have hg' := hg.mono_measure hm
  rw [cellUl_window_eq_product I f a hf']
  calc
    _ ≤ eLpNorm (fun p : ℝ × Vec 2 => B * ‖g p.1 p.2‖) 2 _ :=
      eLpNorm_mono_ae_real hf' (Filter.Eventually.of_forall fun p => hbound p.1 p.2)
    _ = ENNReal.ofReal B * eLpNorm (Function.uncurry g) 2
        ((volume.restrict (Set.Icc a (a + 1) ∩ I)).prod
          (volume.restrict AVenhance.unitCube)) := by
      change eLpNorm (B • fun p : ℝ × Vec 2 => ‖g p.1 p.2‖) 2 _ = _
      rw [eLpNorm_const_smul, Real.enorm_of_nonneg hB]
      congr 1
      simpa only [Function.uncurry_def] using eLpNorm_norm (Function.uncurry g) hg'
    _ ≤ _ := by
      rw [← cellUl_window_eq_product I g a hg']
      gcongr
      exact le_iSup (fun b : ℝ => (∫⁻ t in Set.Icc b (b + 1) ∩ I,
        cellL2Norm (g t) ^ 2) ^ (1 / 2 : ℝ)) a

/-- Negation preserves each uniformly local norm, without any measurability premise. -/
theorem cellUlNorm_neg (I : Set ℝ) (f : ℝ → Vec 2 → E) :
    cellUlNorm I (-f) = cellUlNorm I f := by
  unfold cellUlNorm
  congr 1
  funext a
  congr 1
  apply lintegral_congr
  intro t
  change (eLpNorm (-(f t)) 2 _) ^ 2 = _
  rw [eLpNorm_neg]
  rfl

/-- The difference of two joint fields has the sum bound in the uniformly local norm. -/
theorem cellUlNorm_sub (I : Set ℝ) (f g : ℝ → Vec 2 → E)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hg : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm I (f - g) ≤ cellUlNorm I f + cellUlNorm I g := by
  rw [sub_eq_add_neg, ← cellUlNorm_neg I g]
  exact cellUlNorm_add I f (-g) hf hg.neg
end

/-! Uniform cell L2 bounds give admissible uniformly local source bounds. -/

/-- A uniform-in-time literal cell L2 bound controls every unit time window. -/
theorem cellUlNorm_le_uniform_cellL2Norm {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → Vec 2 → E) (B : ℝ≥0∞) (hb : ∀ t, cellL2Norm (f t) ≤ B) :
    cellUlNorm Set.univ f ≤ B := by
  apply cellUlNorm_le_of_window_sq_bound
  intro a
  simp only [Set.inter_univ]
  calc
    _ ≤ ∫⁻ _ in Set.Icc a (a + 1), B ^ 2 :=
      lintegral_mono (fun t => pow_le_pow_left' (hb t) 2)
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        show a + 1 - a = 1 by ring]
      simp

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Exact two-variable Cauchy products for absolutely summable Taylor coefficient series. -/

/-- Absolute summability justifies the literal finite-rectangle two-variable Cauchy product. -/
theorem fibreCoefficient_cauchy_product (f g : ℕ × ℕ → ℂ)
    (hf : Summable (fun p => ‖f p‖)) (hg : Summable (fun p => ‖g p‖)) :
    ((∑' p, f p) * ∑' p, g p) =
      ∑' p, ∑ a ∈ fibreCoefficientPairs p, f a * g (fibreCoefficientComplement p a) := by
  let H := fun q : (ℕ × ℕ) × (ℕ × ℕ) => f q.1 * g q.2
  have hH : Summable H := summable_mul_of_summable_norm hf hg
  have hsum := hH.hasSum.tsum_fiberwise (fun q => q.1 + q.2)
  have he (p : ℕ × ℕ) :
      (∑' q : {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1 + q.2 = p}, H q.1) =
        ∑ a ∈ fibreCoefficientPairs p, f a * g (fibreCoefficientComplement p a) := by
    rw [← (fibreCoefficientConvolutionFibreEquiv p).symm.tsum_eq (fun q => H q.1)]
    simp only [H, fibreCoefficientConvolutionFibreEquiv_symm_fst,
      fibreCoefficientConvolutionFibreEquiv_symm_snd]
    rw [tsum_fintype]
    exact Finset.sum_finset_coe (fun a => f a * g (fibreCoefficientComplement p a)) (fibreCoefficientPairs p)
  calc
    _ = ∑' q, H q := tsum_mul_tsum_of_summable_norm hf hg
    _ = ∑' p, ∑' q : {q : (ℕ × ℕ) × (ℕ × ℕ) // q.1 + q.2 = p}, H q.1 := hsum.tsum_eq.symm
    _ = _ := tsum_congr he

/-! The constructed scalar reciprocal coefficients satisfy their literal convolution equation. -/

theorem fibreScalarInverseCoefficient_equation (d : ℕ × ℕ → ℂ) (hd : d 0 = 0)
    (p : ℕ × ℕ) :
    fibreScalarInverseCoefficient d p +
      ∑ a ∈ fibreCoefficientPairs p,
        d a * fibreScalarInverseCoefficient d (fibreCoefficientComplement p a) =
      if p = 0 then 1 else 0 := by
  classical
  by_cases hp : p = 0
  · subst p
    have hd' : d (0, 0) = 0 := hd
    simp [fibreCoefficientPairs, fibreScalarInverseCoefficient_zero, hd']
  · rw [ite_eq_right hp, fibreScalarInverseCoefficient_nonzero d hp]
    have he :
        (∑ a ∈ (fibreCoefficientPairs p).filter (fun a => a ≠ 0),
          d a * fibreScalarInverseCoefficient d (fibreCoefficientComplement p a)) =
        ∑ a ∈ fibreCoefficientPairs p,
          d a * fibreScalarInverseCoefficient d (fibreCoefficientComplement p a) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = 0
      · subst a
        simp [hd]
      · simp [ha]
    rw [he, neg_add_cancel]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Uniform coefficient majorants for the actual scalar reciprocal recursion. -/

theorem fibreScalarInverseCoefficient_uniform_recurrence
    (d : ℕ × ℕ → ℝ → ℂ) (p : ℕ × ℕ) :
    (⨆ t, ‖fibreScalarInverseCoefficient (fun a => d a t) p‖ₑ) ≤
      if p = 0 then 1 else
        ∑ a ∈ (fibreCoefficientPairs p).filter (fun a => a ≠ 0),
          (⨆ t, ‖d a t‖ₑ) *
            ⨆ t, ‖fibreScalarInverseCoefficient (fun b => d b t)
              (fibreCoefficientComplement p a)‖ₑ := by
  classical
  by_cases hp : p = 0
  · subst p
    simp [fibreScalarInverseCoefficient_zero, enorm_eq_nnnorm]
  · rw [ite_eq_right hp]
    apply iSup_le
    intro t
    rw [fibreScalarInverseCoefficient_nonzero _ hp, enorm_neg]
    apply (enorm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    rw [enorm_mul]
    exact mul_le_mul' (le_iSup (fun s => ‖d a s‖ₑ) t)
      (le_iSup (fun s => ‖fibreScalarInverseCoefficient (fun b => d b s)
        (fibreCoefficientComplement p a)‖ₑ) t)

theorem fibreScalarInverseCoefficient_uniform_full_recurrence
    (d : ℕ × ℕ → ℝ → ℂ) (p : ℕ × ℕ) :
    (⨆ t, ‖fibreScalarInverseCoefficient (fun a => d a t) p‖ₑ) ≤
      (if p = 0 then 1 else 0) +
        ∑ a ∈ fibreCoefficientPairs p, (⨆ t, ‖d a t‖ₑ) *
          ⨆ t, ‖fibreScalarInverseCoefficient (fun b => d b t)
            (fibreCoefficientComplement p a)‖ₑ := by
  classical
  apply (fibreScalarInverseCoefficient_uniform_recurrence d p).trans
  by_cases hp : p = 0
  · rw [ite_eq_left hp, ite_eq_left hp]
    exact le_add_right le_rfl
  · rw [ite_eq_right hp, ite_eq_right hp, zero_add]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute L1 seminorm summability justifies actual integration of literal series. -/

/-- Absolute L1 seminorm summability gives an integrable literal pointwise series. -/
theorem cellL1Series_integrable {J X : Type*} [Countable J] [MeasurableSpace X]
    (μ : Measure X) (f : J → X → ℂ) (hs : (∑' j, eLpNorm (f j) 1 μ) < ⊤) :
    Integrable (fun x => ∑' j, f j x) μ := by
  have hf j : MemLp (f j) 1 μ := (ENNReal.le_tsum j).trans_lt hs
  let u := fun j => (hf j).toLp (f j)
  have hu : (∑' j, ‖u j‖ₑ) < ⊤ := by simpa only [u, Lp.enorm_toLp] using hs
  have hall : ∀ᵐ x ∂μ, ∀ j, u j x = f j x :=
    ae_all_iff.mpr (fun j => (hf j).coeFn_toLp)
  have he : (⇑(∑' j, u j) : X → ℂ) =ᵐ[μ] (fun x => ∑' j, f j x) := by
    filter_upwards [Lp.coeFn_tsum hu.ne, hall] with x hx hx'
    exact hx.trans (tsum_congr (fun j => hx' j))
  exact memLp_one_iff_integrable.mp ((memLp_congr_ae he).mp (Lp.memLp (∑' j, u j)))

/-- Absolute L1 seminorm summability permits exchanging the literal series and its integral. -/
theorem cellL1Series_integral_tsum {J X : Type*} [Countable J] [MeasurableSpace X]
    (μ : Measure X) (f : J → X → ℂ) (hs : (∑' j, eLpNorm (f j) 1 μ) < ⊤) :
    (∫ x, ∑' j, f j x ∂μ) = ∑' j, ∫ x, f j x ∂μ := by
  have hf j : MemLp (f j) 1 μ := (ENNReal.le_tsum j).trans_lt hs
  apply integral_tsum (fun j => (hf j).aestronglyMeasurable)
  have he j : (∫⁻ x, ‖f j x‖ₑ ∂μ) = eLpNorm (f j) 1 μ :=
    (eLpNorm_one_eq_lintegral_enorm (hf j).aestronglyMeasurable).symm
  simp_rw [he]
  exact hs.ne

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The literal cell mean of a fixed multiplier commutes with absolute L2 series. -/

/-- An L2 multiplier can be paired term by term with an absolutely L2-summable cell series. -/
theorem cellMean_product_tsum {J : Type*} [Countable J]
    (b : Vec 2 → ℂ) (hb : MemLp b 2 (volume.restrict AVenhance.unitCube))
    (f : J → Vec 2 → ℂ) (hs : (∑' j, cellL2Norm (f j)) < ⊤) :
    cellMean (fun x => b x * ∑' j, f j x) = ∑' j, cellMean (fun x => b x * f j x) := by
  have hf j : MemLp (f j) 2 (volume.restrict AVenhance.unitCube) :=
    (ENNReal.le_tsum j).trans_lt hs
  have he := cellL2_product_series_integral (volume.restrict AVenhance.unitCube) f b
    (fun j => (hf j).aestronglyMeasurable) hb hs
  simpa only [cellMean, mul_comm] using he

/-- The multiplier pairings of an absolutely L2-summable cell series are absolutely summable. -/
theorem cellMean_product_series_enorm_lt_top {J : Type*} [Countable J]
    (b : Vec 2 → ℂ) (hb : MemLp b 2 (volume.restrict AVenhance.unitCube))
    (f : J → Vec 2 → ℂ) (hs : (∑' j, cellL2Norm (f j)) < ⊤) :
    (∑' j, ‖cellMean (fun x => b x * f j x)‖ₑ) < ⊤ := by
  have hf j : MemLp (f j) 2 (volume.restrict AVenhance.unitCube) :=
    (ENNReal.le_tsum j).trans_lt hs
  have hl := cellL2_product_series_lintegral_lt_top (volume.restrict AVenhance.unitCube) f b
    (fun j => (hf j).aestronglyMeasurable) hb hs
  apply (ENNReal.tsum_le_tsum (fun j => ?_)).trans_lt hl
  simpa only [cellMean, mul_comm] using
    enorm_integral_le_lintegral_enorm (fun x => f j x * b x)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Pointwise scalar and divergence-source energy bounds. -/

/-- Complex flux pairing with a spatial test gradient. -/
def cellFluxPairing (F p : Fin 2 → ℂ) : ℝ := (∑ j, F j * star (p j)).re

/-- Flux pairing is additive in the test gradient. -/
theorem cellFluxPairing_add (F p b : Fin 2 → ℂ) :
    cellFluxPairing F (p + b) = cellFluxPairing F p + cellFluxPairing F b := by
  simp [cellFluxPairing, mul_add, Finset.sum_add_distrib]

/-- Absolute flux pairing is bounded componentwise. -/
theorem cellFluxPairing_abs_le (F p : Fin 2 → ℂ) :
    |cellFluxPairing F p| ≤ ∑ j, ‖F j‖ * ‖p j‖ := by
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_mul, norm_star]
  exact le_rfl

/-- The divergence source is absorbed by a small part of the gradient energy. -/
theorem cellFluxPairing_young (F p : Fin 2 → ℂ) :
    2 * |cellFluxPairing F p| ≤ (1 / 8) * ∑ j, ‖p j‖ ^ 2 + 8 * ∑ j, ‖F j‖ ^ 2 := by
  have hb := cellFluxPairing_abs_le F p
  simp only [Fin.sum_univ_two] at *
  nlinarith [sq_nonneg (‖p 0‖ / 4 - 2 * ‖F 0‖),
    sq_nonneg (‖p 1‖ / 4 - 2 * ‖F 1‖)]

/-- The Bloch part of a divergence source needs only its L² norm. -/
theorem cellFluxPairing_bloch (F θ : Fin 2 → ℂ) (u : ℂ) :
    2 * |cellFluxPairing F (cellBlochShift θ u)| ≤
      (∑ j, ‖F j‖ ^ 2) + (∑ j, ‖θ j‖ ^ 2) * ‖u‖ ^ 2 := by
  have hb := cellFluxPairing_abs_le F (cellBlochShift θ u)
  simp only [cellBlochShift, norm_mul, Complex.norm_I, one_mul, Fin.sum_univ_two] at *
  nlinarith [sq_nonneg (‖F 0‖ - ‖θ 0‖ * ‖u‖),
    sq_nonneg (‖F 1‖ - ‖θ 1‖ * ‖u‖)]

/-- The scalar source uses its L² norm and one value-energy term. -/
theorem cellScalarSource_young (src u : ℂ) :
    2 * (src * star u).re ≤ ‖src‖ ^ 2 + ‖u‖ ^ 2 := by
  have hb := Complex.re_le_norm (src * star u)
  rw [norm_mul, norm_star] at hb
  nlinarith [sq_nonneg (‖src‖ - ‖u‖)]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Unit-window integrability of literal spatial L2 norms, including exceptional slices. -/

/-- Joint almost measurability implies almost measurability of the literal slice L2 norm. -/
theorem cellSliceL2Norm_aemeasurable {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    AEMeasurable (fun t => cellL2Norm (f t)) (volume.restrict I) := by
  have hm := (hf.enorm.pow_const 2).lintegral_prod_right'
  have he : (fun t => (∫⁻ x in AVenhance.unitCube, ‖f t x‖ₑ ^ 2) ^ (1 / 2 : ℝ))
      =ᵐ[volume.restrict I] (fun t => cellL2Norm (f t)) := by
    filter_upwards [hf.prodMk_left] with t ht
    have ht' : AEStronglyMeasurable (f t) (volume.restrict AVenhance.unitCube) := ht
    rw [← cellL2Norm_sq_eq_lintegral ht']
    simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      show (2 : ℕ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  exact (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hm).congr he

/-- A unit window bounds the L1 time integral of spatial L2 norms by the joint L2 norm. -/
theorem cellSliceL2Norm_lintegral_le_product {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → Vec 2 → E) (a : ℝ)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Set.Icc a (a + 1))).prod
        (volume.restrict AVenhance.unitCube))) :
    (∫⁻ t in Set.Icc a (a + 1), cellL2Norm (f t)) ≤
      eLpNorm (Function.uncurry f) 2
        ((volume.restrict (Set.Icc a (a + 1))).prod
          (volume.restrict AVenhance.unitCube)) := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (Set.Icc a (a + 1)))
    (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨(by norm_num : 1 < (2 : ℝ)), by norm_num⟩)
    (cellSliceL2Norm_aemeasurable _ f hf)
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Icc,
    show a + 1 - a = 1 by ring, ENNReal.ofReal_one] at hh
  have he := cellUl_window_eq_product Set.univ f a (by simpa only [Set.inter_univ] using hf)
  simp only [Set.inter_univ] at he
  simp only [ENNReal.rpow_two] at hh
  exact hh.trans_eq he

end AVRegularity.CycleEvolution
end
end
