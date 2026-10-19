-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.NormalizedProductSquare
public import AVRegularity.CycleWords.FrequencyNormalFormSum
import AVRegularity.CycleWords.L2StrongOperatorContinuity
public import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Weighted.JointRegularityBoxSmooth
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Pointwise factorial density bounds for the literal positional Leibniz product. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def rawFactorialDensity {K : ℕ} (ρ : ℝ) (D : RawJet2 K E) (x : Vec 2) : ℝ :=
  ∑ a : JetIndex2 K, factorialWeight ρ a.1.val * ‖D a x‖ ^ 2

omit [NormedSpace ℝ E] in
theorem rawFactorialDensity_term_le {K : ℕ} (ρ : ℝ) (D : RawJet2 K E)
    (a : JetIndex2 K) (x : Vec 2) :
    factorialWeight ρ a.1.val * ‖D a x‖ ^ 2 ≤ rawFactorialDensity ρ D x := by
  exact Finset.single_le_sum
    (f := fun a : JetIndex2 K => factorialWeight ρ a.1.val * ‖D a x‖ ^ 2)
    (fun a _ => mul_nonneg (factorialWeight_nonneg _ _) (sq_nonneg _)) (Finset.mem_univ a)

theorem multiplicationRawJet_word_density_le {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) {ρ A q : ℝ}
    (hρ : 0 ≤ ρ) (x : Vec 2)
    (hb : ∀ l ≤ K, ∀ w : DerivativeWord2 l,
      ρ ^ l * ‖orderedCoefficientDerivative C l w x‖ ≤ A * q)
    (a : JetIndex2 K) :
    factorialWeight ρ a.1.val * ‖multiplicationRawJet C D a x‖ ^ 2 ≤
      (Fintype.card (PositionMask a.1.val) : ℝ) ^ 2 * A ^ 2 * q ^ 2 * rawFactorialDensity ρ D x := by
  let f := fun m : PositionMask a.1.val =>
    multiplicationTerm (Nat.le_of_lt_succ a.1.isLt) C D m a.2 x
  have hn : ‖∑ m, f m‖ ^ 2 ≤ (Fintype.card (PositionMask a.1.val) : ℝ) * ∑ m, ‖f m‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
      (by simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun m => ‖f m‖))
  have ht (m : PositionMask a.1.val) :
      factorialWeight ρ a.1.val * ‖f m‖ ^ 2 ≤ A ^ 2 * q ^ 2 * rawFactorialDensity ρ D x := by
    let l := maskLeftLength a.1.val m
    let r := maskRightLength a.1.val m
    let w := (maskWordEquiv 2 a.1.val m a.2).1
    let b := maskJetIndex (Nat.le_of_lt_succ a.1.isLt) m a.2
    have hp : ρ ^ l * ‖f m‖ ≤ A * q * ‖D b x‖ := by
      have hnorm : ‖f m‖ ≤ ‖orderedCoefficientDerivative C l w x‖ * ‖D b x‖ :=
        (orderedCoefficientDerivative C l w x).le_opNorm _
      calc
        _ ≤ ρ ^ l * (‖orderedCoefficientDerivative C l w x‖ * ‖D b x‖) :=
          mul_le_mul_of_nonneg_left hnorm (pow_nonneg hρ l)
        _ = (ρ ^ l * ‖orderedCoefficientDerivative C l w x‖) * ‖D b x‖ := (mul_assoc _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (hb l ((maskLeftLength_le a.1.val m).trans (Nat.le_of_lt_succ a.1.isLt)) w) (norm_nonneg _)
    have hh := normalizedProduct_square_budget l r hρ (norm_nonneg (f m)) hp
    rw [mask_lengths_add] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (rawFactorialDensity_term_le ρ D b x) (by positivity))
  change factorialWeight ρ a.1.val * ‖∑ m, f m‖ ^ 2 ≤ _
  calc
    _ ≤ factorialWeight ρ a.1.val * ((Fintype.card (PositionMask a.1.val) : ℝ) * ∑ m, ‖f m‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hn (factorialWeight_nonneg _ _)
    _ = (Fintype.card (PositionMask a.1.val) : ℝ) *
        ∑ m, factorialWeight ρ a.1.val * ‖f m‖ ^ 2 := by rw [mul_left_comm, Finset.mul_sum]
    _ ≤ (Fintype.card (PositionMask a.1.val) : ℝ) *
        ∑ _m : PositionMask a.1.val, A ^ 2 * q ^ 2 * rawFactorialDensity ρ D x :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ => ht m)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

def multiplicationDensityBudget (K : ℕ) : ℝ :=
  ∑ a : JetIndex2 K, (Fintype.card (PositionMask a.1.val) : ℝ) ^ 2

theorem multiplicationDensityBudget_nonneg (K : ℕ) : 0 ≤ multiplicationDensityBudget K :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem multiplicationRawJet_density_le {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) {ρ A q : ℝ}
    (hρ : 0 ≤ ρ) (x : Vec 2)
    (hb : ∀ l ≤ K, ∀ w : DerivativeWord2 l,
      ρ ^ l * ‖orderedCoefficientDerivative C l w x‖ ≤ A * q) :
    rawFactorialDensity ρ (multiplicationRawJet C D) x ≤
      multiplicationDensityBudget K * A ^ 2 * q ^ 2 * rawFactorialDensity ρ D x := by
  apply (Finset.sum_le_sum (fun a _ => multiplicationRawJet_word_density_le C D hρ x hb a)).trans_eq
  simp only [multiplicationDensityBudget, Finset.sum_mul]

end AVRegularity.CycleWords
end
end

section
public noncomputable section
namespace AVRegularity.CycleWords

/-! Coordinate derivative regularity controls the full derivative on complex two-space. -/

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem twoCoordinateComplexMap_contDiffOn (f₀ f₁ : V → E) (s : Set V)
    (n : WithTop ℕ∞) (h₀ : ContDiffOn ℂ n f₀ s) (h₁ : ContDiffOn ℂ n f₁ s) :
    ContDiffOn ℂ n (fun y => twoCoordinateComplexMap (f₀ y) (f₁ y)) s := by
  have hh₀ : ContDiffOn ℂ n (fun y =>
      (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight (f₀ y)) s :=
    contDiffOn_const.smulRight h₀
  have hh₁ : ContDiffOn ℂ n (fun y =>
      (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ).smulRight (f₁ y)) s :=
    contDiffOn_const.smulRight h₁
  exact hh₀.add hh₁

theorem twoCoordinateComplexMap_of_coordinates (D : (Fin 2 → ℂ) →L[ℂ] E) :
    twoCoordinateComplexMap (D (Pi.single 0 1)) (D (Pi.single 1 1)) = D := by
  apply ContinuousLinearMap.ext
  intro ν
  rw [twoCoordinateComplexMap_apply]
  have he : ν = ν 0 • Pi.single 0 1 + ν 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  conv_rhs => rw [he, map_add, map_smul, map_smul]

theorem contDiffOn_succ_of_two_coordinate_derivatives (f : (Fin 2 → ℂ) → E)
    (s : Set (Fin 2 → ℂ)) (hs : IsOpen s) (n : ℕ)
    (hd : DifferentiableOn ℂ f s)
    (h₀ : ContDiffOn ℂ n (fun y => fderiv ℂ f y (Pi.single 0 1)) s)
    (h₁ : ContDiffOn ℂ n (fun y => fderiv ℂ f y (Pi.single 1 1)) s) :
    ContDiffOn ℂ (n + 1 : ℕ) f s := by
  have hfd : ContDiffOn ℂ n (fderiv ℂ f) s := by
    apply (twoCoordinateComplexMap_contDiffOn _ _ s n h₀ h₁).congr
    intro y _
    exact (twoCoordinateComplexMap_of_coordinates (fderiv ℂ f y)).symm
  have hh : ContDiffOn ℂ ((n : WithTop ℕ∞) + 1) f s := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen hs).mpr
    refine ⟨hd, ?_, hfd⟩
    intro hω
    simp at hω
  simpa only [Nat.cast_add, Nat.cast_one] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! Uniform pointwise bounds give genuine bounded operators on native Bochner L2 classes. -/

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance variableL2BoundSeminormed {Y Z : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup Z] (μ : Measure Y) :
    SeminormedAddCommGroup (Lp Z 2 μ) :=
  (inferInstance : NormedAddCommGroup (Lp Z 2 μ)).toSeminormedAddCommGroup

local instance variableL2BoundAddCommMonoid {Y Z : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup Z] (μ : Measure Y) :
    AddCommMonoid (Lp Z 2 μ) :=
  (inferInstance : NormedAddCommGroup (Lp Z 2 μ)).toAddCommMonoid

local instance variableL2BoundModule {Y Z : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (μ : Measure Y) : Module ℝ (Lp Z 2 μ) :=
  (inferInstance : NormedSpace ℝ (Lp Z 2 μ)).toModule

theorem variableL2LinearMap_norm_le (μ : Measure X) (A : X → E →L[ℝ] F)
    (hmem : ∀ f : Lp E 2 μ, MemLp (fun x => A x (f x)) 2 μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ∀ e, ‖A x e‖ ≤ C * ‖e‖) (f : Lp E 2 μ) :
    ‖variableL2LinearMap μ A hmem f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [variableL2LinearMap_ae μ A hmem f, hbound] with x hx hb
  rw [hx]
  exact hb (f x)

def variableL2Operator (μ : Measure X) (A : X → E →L[ℝ] F)
    (hmem : ∀ f : Lp E 2 μ, MemLp (fun x => A x (f x)) 2 μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ∀ e, ‖A x e‖ ≤ C * ‖e‖) : Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  (variableL2LinearMap μ A hmem).mkContinuous C
    (variableL2LinearMap_norm_le μ A hmem C hbound)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The fixed product-jet majorant is a genuine L2 scalar field. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weightedRawProductMajorant_memLp {K : ℕ} {U : Set (Vec 2)}
    (A : Fin (K + 1) → ℝ) (D : RawJet2 K E) (q : Vec 2 → ℝ)
    (hw : JetMemL2On U (fun b x => q x • D b x)) (a : JetIndex2 K) :
    MemLp (weightedRawProductMajorant A D q a) 2 (volume.restrict U) := by
  apply memLp_finsetSum Finset.univ
  intro m _
  exact (hw (maskJetIndex (Nat.le_of_lt_succ a.1.isLt) m a.2)).norm.const_mul
    (A (rawProductMaskOrder a m))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! Bounded measurable real weights induce genuine continuous operators on Bochner L2. -/

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boundedScalar_smul_memLp (μ : Measure X) (q : X → ℝ) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖q x‖ ≤ C) (f : Lp E 2 μ) :
    MemLp (fun x => q x • f x) 2 μ := by
  apply ((Lp.memLp f).const_smul C).of_le
    (hq.aestronglyMeasurable.smul (Lp.memLp f).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖q x • f x‖ ≤ ‖C • f x‖
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

def boundedScalarL2Operator (μ : Measure X) (q : X → ℝ) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖q x‖ ≤ C) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  variableL2Operator μ (fun x => q x • ContinuousLinearMap.id ℝ E)
    (boundedScalar_smul_memLp μ q hq C hC hb) C
    (Filter.Eventually.of_forall (fun x e => by
      change ‖q x • e‖ ≤ C * ‖e‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg e)))

theorem boundedScalarL2Operator_ae (μ : Measure X) (q : X → ℝ) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖q x‖ ≤ C) (f : Lp E 2 μ) :
    boundedScalarL2Operator μ q hq C hC hb f =ᵐ[μ] (fun x => q x • f x) :=
  variableL2LinearMap_ae μ (fun x => q x • ContinuousLinearMap.id ℝ E)
    (boundedScalar_smul_memLp μ q hq C hC hb) f

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleWords

/-! Short-window smoothing separates a finite growth price from the frequency radius. -/

 theorem continuous_energy_short_window_smoothing
    (E : ℕ → ℝ → ℝ) (A P : ℕ → ℝ) (B a b δ : ℝ) (q : ℕ)
    (hδ : 0 < δ) (hA : ∀ j, 0 ≤ A j) (hP : ∀ j, 0 ≤ P j)
    (hc : ∀ j ≤ q, ContinuousOn (E j) (Icc a b))
    (hzero : ∀ t ∈ Icc a b, E 0 t ≤ B)
    (hint : ∀ j < q, ∀ s, a ≤ s → s + δ ≤ b →
      (∫ t in s..(s + δ), E (j + 1) t) ≤ A j * E j s)
    (hprop : ∀ j, 0 < j → j ≤ q → ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      t - s ≤ δ → E j t ≤ P j * E j s) :
    ∀ t, a + q * δ ≤ t → t ≤ b →
      E q t ≤ energyGrowthSmoothingConstant (fun j => A j / δ) P q * B := by
  induction q with
  | zero =>
      intro t ht hb
      simpa only [energyGrowthSmoothingConstant, one_mul, Nat.cast_zero, zero_mul, add_zero] using
        hzero t ⟨by simpa only [Nat.cast_zero, zero_mul, add_zero] using ht, hb⟩
  | succ q ih =>
      intro t ht hb
      have hs : a + q * δ ≤ t - δ := by
        rw [Nat.cast_add, Nat.cast_one] at ht
        linarith only [ht]
      have hsa : a ≤ t - δ := (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg q) hδ.le)).trans hs
      have hswindow : t - δ ≤ b := (sub_le_self t hδ.le).trans hb
      have hprev := ih (fun j hj => hc j (hj.trans (Nat.le_succ q)))
        (fun j hj s has hsb => hint j (hj.trans_le (Nat.le_succ q)) s has hsb)
        (fun j hj hjq s u has hsu hub hlen =>
          hprop j hj (hjq.trans (Nat.le_succ q)) s u has hsu hub hlen)
        (t - δ) hs hswindow
      have hi := hint q (Nat.lt_succ_self q) (t - δ) hsa
        (by simpa only [sub_add_cancel] using hb)
      have hi' : (∫ u in (t - δ)..((t - δ) + δ), E (q + 1) u) ≤
          (((t - δ) + δ) - (t - δ)) *
            ((A q / δ) * energyGrowthSmoothingConstant (fun j => A j / δ) P q * B) := by
        exact (hi.trans (mul_le_mul_of_nonneg_left hprev (hA q))).trans_eq (by field_simp; ring)
      have hcontinuous : ContinuousOn (E (q + 1)) (Icc (t - δ) ((t - δ) + δ)) :=
        (hc (q + 1) le_rfl).mono (fun u hu =>
          ⟨hsa.trans hu.1, hu.2.trans (by simpa only [sub_add_cancel] using hb)⟩)
      obtain ⟨s, hsI, hsE⟩ := exists_energy_le_integral_average (E (q + 1))
        (t - δ) ((t - δ) + δ) _ (by linarith only [hδ]) hcontinuous hi'
      have hp := hprop (q + 1) (Nat.succ_pos _) le_rfl s t (hsa.trans hsI.1)
        (by simpa only [sub_add_cancel] using hsI.2) hb (by linarith only [hsI.1])
      exact (hp.trans (mul_le_mul_of_nonneg_left hsE (hP (q + 1)))).trans_eq (by
        simp only [energyGrowthSmoothingConstant]
        ring)

 theorem energyGrowthSmoothingConstant_le_power (A P : ℕ → ℝ) (q : ℕ)
    (CA CP : ℝ) (hCA : 0 ≤ CA) (hCP : 0 ≤ CP)
    (hA : ∀ j, 0 ≤ A j) (hP : ∀ j, 0 ≤ P j)
    (hAb : ∀ j ≤ q, A j ≤ CA) (hPb : ∀ j ≤ q, P j ≤ CP) :
    energyGrowthSmoothingConstant A P q ≤ (CP * CA) ^ q := by
  induction q with
  | zero => simp only [energyGrowthSmoothingConstant, pow_zero, le_refl]
  | succ q ih =>
      have hp := ih (fun j hj => hAb j (hj.trans (Nat.le_succ q)))
        (fun j hj => hPb j (hj.trans (Nat.le_succ q)))
      rw [energyGrowthSmoothingConstant, pow_succ]
      calc
        _ ≤ (CP * CA) * (CP * CA) ^ q := mul_le_mul
          (mul_le_mul (hPb (q + 1) le_rfl) (hAb q (Nat.le_succ q)) (hA q) hCP)
          hp (energyGrowthSmoothingConstant_nonneg A P hA hP q) (mul_nonneg hCP hCA)
        _ = _ := mul_comm _ _

 theorem continuous_energy_short_window_polynomial_price
    (E : ℕ → ℝ → ℝ) (CA CP B a b δ : ℝ) (q : ℕ)
    (hδ : 0 < δ) (hCA : 0 ≤ CA) (hCP : 0 ≤ CP)
    (hc : ∀ j ≤ q, ContinuousOn (E j) (Icc a b))
    (hzero : ∀ t ∈ Icc a b, E 0 t ≤ B) (hB : 0 ≤ B)
    (hint : ∀ j < q, ∀ s, a ≤ s → s + δ ≤ b →
      (∫ t in s..(s + δ), E (j + 1) t) ≤ CA * E j s)
    (hprop : ∀ j, 0 < j → j ≤ q → ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      t - s ≤ δ → E j t ≤ CP * E j s)
    (t : ℝ) (ht : a + q * δ ≤ t) (hb : t ≤ b) :
    E q t ≤ (CP * CA / δ) ^ q * B := by
  have hs := continuous_energy_short_window_smoothing E (fun _ => CA) (fun _ => CP)
    B a b δ q hδ (fun _ => hCA) (fun _ => hCP) hc hzero hint hprop t ht hb
  have hp := energyGrowthSmoothingConstant_le_power (fun _ => CA / δ) (fun _ => CP) q
    (CA / δ) CP (div_nonneg hCA hδ.le) hCP (fun _ => div_nonneg hCA hδ.le)
    (fun _ => hCP) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  exact hs.trans (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hp hB)

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite chart renewals preserve the geometric response level gain when the
same graded moment is transported at each renewal. -/

theorem finite_response_renewal_budget {P N : ℕ} (hP : P ≤ N) (J : ℕ)
    (E data : Fin P → ℕ → ℝ≥0∞) (D A R L ε : ℝ≥0∞)
    (hA : 1 ≤ A) (hR : 1 ≤ R) (hL : 1 ≤ L)
    (hzero : ∀ i : Fin P, i.val = 0 → data i 0 ≤ D)
    (hzeroHigher : ∀ i : Fin P, i.val = 0 → ∀ j, 1 ≤ j → j ≤ J → data i j = 0)
    (hrenew : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ j ≤ J, data i' j ≤ L * E i j)
    (hpiece : ∀ i : Fin P, ∀ j ≤ J,
      E i j ≤ ennResponseMassMajorant R ε (fun l => A * data i l) j) :
    ∀ i : Fin P, ∀ j ≤ J,
      E i j ≤ ((2 * R * A * L) ^ N) ^ (j + 1) * ε ^ j * D := by
  let C := 2 * R * A * L
  have hC : 1 ≤ C := by
    exact (by norm_num : (1 : ℝ≥0∞) ≤ 2).trans
      (by simpa only [mul_one] using mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hR) hA) hL)
  have haux : ∀ k, ∀ i : Fin P, i.val = k → ∀ j ≤ J,
      E i j ≤ (C ^ (k + 1)) ^ (j + 1) * ε ^ j * D := by
    intro k
    induction k with
    | zero =>
      intro i hi j hj
      have hd : ∀ l ≤ J, A * data i l ≤ A ^ (l + 1) * ε ^ l * D := by
        intro l hl
        by_cases hz : l = 0
        · subst l
          simpa only [Nat.zero_add, pow_one, pow_zero, mul_one] using mul_le_mul_right (hzero i hi) A
        · rw [hzeroHigher i hi l (by omega) hl, mul_zero]
          exact zero_le
      have hb := (hpiece i j hj).trans (ennResponseMassMajorant_geometric_le R A ε D hR hA _ J hd j hj)
      have hc : 2 * R * A ≤ C := by
        simpa only [mul_one] using mul_le_mul' (le_rfl : 2 * R * A ≤ 2 * R * A) hL
      exact hb.trans (mul_le_mul_left (mul_le_mul_left
        (by simpa only [Nat.zero_add, pow_one] using pow_le_pow_left₀ zero_le hc (j + 1)) _) D)
    | succ k ih =>
      intro i' hi' j hj
      let i : Fin P := ⟨k, by omega⟩
      have hi : i'.val = i.val + 1 := by simpa only [i] using hi'
      let I := A * L * C ^ (k + 1)
      have hI : 1 ≤ I := by
        simpa only [one_mul] using mul_le_mul' (mul_le_mul' hA hL) (one_le_pow₀ hC)
      have hAL : 1 ≤ A * L := by simpa only [one_mul] using mul_le_mul' hA hL
      have hd : ∀ l ≤ J, A * data i' l ≤ I ^ (l + 1) * ε ^ l * D := by
        intro l hl
        have hh := mul_le_mul_right ((hrenew i i' hi l hl).trans
          (mul_le_mul_right (ih i rfl l hl) L)) A
        have hp : A * L ≤ (A * L) ^ (l + 1) := by
          rw [pow_succ]
          simpa only [one_mul] using mul_le_mul_left (one_le_pow₀ hAL : (1 : ℝ≥0∞) ≤ (A * L) ^ l) (A * L)
        calc
          _ ≤ _ := hh
          _ = (A * L) * (C ^ (k + 1)) ^ (l + 1) * ε ^ l * D := by ring
          _ ≤ (A * L) ^ (l + 1) * (C ^ (k + 1)) ^ (l + 1) * ε ^ l * D :=
            mul_le_mul_left (mul_le_mul_left (mul_le_mul_left hp _) _) D
          _ = _ := by dsimp [I]; simp only [mul_pow, mul_assoc]
      have hb := (hpiece i' j hj).trans (ennResponseMassMajorant_geometric_le R I ε D hR hI _ J hd j hj)
      have heq : 2 * R * I = C ^ (k + 1 + 1) := by dsimp [I]; rw [pow_succ]; dsimp [C]; ring
      simpa only [heq] using hb
  intro i j hj
  apply (haux i.val i rfl j hj).trans
  exact mul_le_mul_left (mul_le_mul_left (pow_le_pow_left₀ zero_le
    (pow_le_pow_right₀ hC (by omega : i.val + 1 ≤ N)) (j + 1)) _) D

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Sum the actual absolutely continuous word energies before applying forcing budgets. -/

theorem finite_weighted_strong_growth {ι : Type*} [Fintype ι]
    (a b : ℝ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (E D L U R : ι → ℝ → ℝ) (A B : ℝ)
    (h : ∀ i, ∃ P : ℝ → ℝ, StrongTimeRegularity a b (E i) P ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b),
        P t + D i t ≤ A * E i t + 8 * L i t + B * U i t + 2 * R i t)) :
    ∃ P : ℝ → ℝ, StrongTimeRegularity a b (fun t => ∑ i, c i * E i t) P ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b),
        P t + (∑ i, c i * D i t) ≤ A * (∑ i, c i * E i t) +
          8 * (∑ i, c i * L i t) + B * (∑ i, c i * U i t) + 2 * (∑ i, c i * R i t)) := by
  classical
  choose P hP hbound using h
  refine ⟨fun t => ∑ i, c i * P i t, ?_, ?_⟩
  · exact strongTimeRegularity_finset_sum Finset.univ
      (fun i t => c i * E i t) (fun i t => c i * P i t)
      (fun i _ => strongTimeRegularity_const_mul (hP i) (c i))
  · have hall := ae_all_iff.mpr hbound
    filter_upwards [hall] with t ht
    exact finite_weighted_growth_sum c (fun i => P i t) (fun i => D i t)
      (fun i => E i t) (fun i => L i t) (fun i => U i t) (fun i => R i t) hc A B ht

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Iterating the literal product rule keeps the chronological order of frequency derivatives. -/

variable {I V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def frequencyNormalFormOrdered (direction : I → V) (w : List I)
    (ts : List (FrequencyNormalTerm I V E F)) : List (FrequencyNormalTerm I V E F) :=
  w.foldl (fun us i => frequencyNormalFormDerivative us direction i) ts

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Complex Metric
open scoped NNReal ENNReal
namespace AVRegularity.CycleWords

/-! Proved bounded higher-state existence yields a genuine native Cauchy realization of the lower analytic state. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace E] [CompleteSpace F]
  [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
  [MeasurableSpace F] [BorelSpace F]

theorem injectiveNative_cauchy_realization (A : E →L[ℂ] F) (hA : Function.Injective A)
    (g : ℂ → F) (c : ℂ) (R : ℝ≥0) (hR : 0 < R) (M : ℝ)
    (hc : ContinuousOn g (closedBall c R)) (hd : DifferentiableOn ℂ g (ball c R))
    (hex : ∀ z ∈ closedBall c R, ∃ U : E, A U = g z ∧ ‖U‖ ≤ M) :
    ∃ f : ℂ → E,
      (∀ z ∈ closedBall c R, A (f z) = g z ∧ ‖f z‖ ≤ M) ∧
        HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R := by
  classical
  let f := fun z => if hz : z ∈ closedBall c R then Classical.choose (hex z hz) else 0
  have hf (z : ℂ) (hz : z ∈ closedBall c R) : A (f z) = g z ∧ ‖f z‖ ≤ M := by
    dsimp only [f]
    rw [dite_eq_left hz]
    exact Classical.choose_spec (hex z hz)
  refine ⟨f, hf, injectiveBoundedComplex_cauchy_lift A hA f c R hR M ?_ ?_ (fun z hz => (hf z hz).2)⟩
  · exact hc.congr (fun z hz => (hf z hz).1)
  · exact hd.congr (fun z hz => (hf z (ball_subset_closedBall hz)).1)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! The lattice isometry's range contains every single-coordinate L2 field. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem planeFrequencySingleLift_eq_compLp (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (g : Lp E 2 (volume.restrict (planeFrequencyCell a P))) (m : Fin 2 → ℤ) :
    planeFrequencyL2Isometry a P hP (planeFrequencySingleLift a P g m) =
      (lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 → ℤ => E) 2 m).compLp g := by
  apply Lp.ext
  filter_upwards [planeFrequencySingleLift_fibre_ae a P hP g m,
    (lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 → ℤ => E) 2 m).coeFn_compLp g]
    with θ hθ hg
  exact hθ.trans hg.symm

theorem planeFrequencyL2Isometry_single_mem_range (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (g : Lp E 2 (volume.restrict (planeFrequencyCell a P))) (m : Fin 2 → ℤ) :
    (lp.singleContinuousLinearMap ℝ (fun _ : Fin 2 → ℤ => E) 2 m).compLp g ∈
      Set.range (planeFrequencyL2Isometry a P hP) :=
  ⟨planeFrequencySingleLift a P g m, planeFrequencySingleLift_eq_compLp a P hP g m⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier
open scoped FourierTransform
namespace AVRegularity.CycleWords

/-! The actual plane Fourier unitary translates frequency under integer physical modulation. -/

def planeIntegerFrequency (n : Fin 2 → ℤ) : Vec 2 := fun i => (n i : ℝ)

theorem coordinate_integerModulation_fourier (n : Fin 2 → ℤ)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (fourierL2 (planeIntegerModulationOperator n f)) =
      hilbertFrequencyTranslation (integerHilbertFrequency n) (coordinateL2Equiv (fourierL2 f)) := by
  rw [coordinate_fourierL2, coordinate_integerModulation,
    hilbertCharacterModulationOperator_fourier, ← coordinate_fourierL2]

theorem planeIntegerModulation_fourier_ae (n : Fin 2 → ℤ)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    fourierL2 (planeIntegerModulationOperator n f) =ᵐ[volume]
      fun ξ => fourierL2 f (ξ - planeIntegerFrequency n) := by
  have he : ∀ᵐ ξ : HilbertTwo ∂volume,
      fourierL2 (planeIntegerModulationOperator n f) (WithLp.ofLp ξ) =
        fourierL2 f (WithLp.ofLp (ξ - integerHilbertFrequency n)) := by
    have hc := coordinate_integerModulation_fourier n f
    have ht := hilbertFrequencyTranslation_ae (integerHilbertFrequency n)
      (coordinateL2Equiv (fourierL2 f))
    rw [← hc] at ht
    filter_upwards [coordinateL2Equiv_ae (fourierL2 (planeIntegerModulationOperator n f)), ht,
      (hilbertFrequencyTranslation_measurePreserving (integerHilbertFrequency n)).quasiMeasurePreserving.ae
        (coordinateL2Equiv_ae (fourierL2 f))] with ξ h₁ h₂ h₃
    exact h₁.symm.trans (h₂.trans h₃)
  have hp := (PiLp.volume_preserving_toLp (Fin 2)).quasiMeasurePreserving.ae he
  filter_upwards [hp] with ξ hξ
  have hv : WithLp.ofLp (WithLp.toLp 2 ξ - integerHilbertFrequency n) =
      ξ - planeIntegerFrequency n := by
    funext i
    rfl
  simpa only [WithLp.ofLp_toLp, hv] using hξ

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A genuine torus-valued Bloch transform of complex scalar plane L2 data. -/

local instance planeScalarBlochTransformMeasureSpace : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

abbrev ScalarTorusL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

def scalarFibreSynthesis : lp (fun _ : Fin 2 → ℤ => ℂ) 2 →ₗᵢ[ℝ] ScalarTorusL2 where
  toLinearMap := (mFourierBasis (d := Fin 2)).repr.symm.toLinearMap.restrictScalars ℝ
  norm_map' := (mFourierBasis (d := Fin 2)).repr.symm.norm_map

theorem scalarFibreSynthesis_fourierCoeff (F : lp (fun _ : Fin 2 → ℤ => ℂ) 2)
    (n : Fin 2 → ℤ) : mFourierCoeff (scalarFibreSynthesis F) n = F n := by
  calc
    _ = ((mFourierBasis (d := Fin 2)).repr (scalarFibreSynthesis F)) n :=
      (mFourierBasis_repr (scalarFibreSynthesis F) n).symm
    _ = F n := by
      change ((mFourierBasis (d := Fin 2)).repr ((mFourierBasis (d := Fin 2)).repr.symm F)) n = _
      rw [LinearIsometryEquiv.apply_symm_apply]

def planeScalarBlochTransform (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Lp ℂ 2 (volume : Measure (Vec 2)) →ₗᵢ[ℝ]
      Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)) :=
  (liftLinearIsometryL2 (volume.restrict (planeFrequencyCell a P)) scalarFibreSynthesis).comp
    (planeBlochCoefficients a P hP)

theorem planeScalarBlochTransform_norm (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) : ‖planeScalarBlochTransform a P hP f‖ = ‖f‖ :=
  (planeScalarBlochTransform a P hP).norm_map f

theorem planeScalarBlochTransform_fourierCoeff_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (planeScalarBlochTransform a P hP f θ) n =
        AVRegularity.CoupledEnergyPlane.Fourier.fourierL2 f (planeLatticeEmbedding P n + θ) := by
  have hh := liftLinearIsometryL2_ae (volume.restrict (planeFrequencyCell a P))
    scalarFibreSynthesis (planeBlochCoefficients a P hP f)
  filter_upwards [hh, planeBlochCoefficients_ae a P hP f] with θ hθ hc n
  change mFourierCoeff
    (liftLinearIsometryL2 (volume.restrict (planeFrequencyCell a P)) scalarFibreSynthesis
      (planeBlochCoefficients a P hP f) θ) n = _
  rw [hθ, scalarFibreSynthesis_fourierCoeff]
  exact hc n

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Finite factorial word densities are actual Hilbert sequence norms, without a constituent count loss. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rawFactorialArray {K : ℕ} (ρ : ℝ) (D : RawJet2 K E) (x : Vec 2) :
    PiLp 2 (fun _ : JetIndex2 K => E) :=
  WithLp.toLp 2 (fun a => factorialRootWeight ρ a.1.val • D a x)

theorem rawFactorialArray_norm_sq {K : ℕ} (ρ : ℝ) (D : RawJet2 K E) (x : Vec 2) :
    ‖rawFactorialArray ρ D x‖ ^ 2 = rawFactorialDensity ρ D x := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold rawFactorialArray rawFactorialDensity
  apply Finset.sum_congr rfl
  intro a _
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    factorialRootWeight_sq]

theorem rawFactorialArray_sum {K : ℕ} {ι : Type*} [Fintype ι]
    (ρ : ℝ) (D : ι → RawJet2 K E) (x : Vec 2) :
    rawFactorialArray ρ (fun a z => ∑ i, D i a z) x = ∑ i, rawFactorialArray ρ (D i) x := by
  apply PiLp.ext
  intro a
  simp only [rawFactorialArray, WithLp.ofLp_toLp, WithLp.ofLp_sum, Finset.sum_apply, Finset.smul_sum]

theorem rawFactorialArray_sum_norm_le {K : ℕ} {ι : Type*} [Fintype ι]
    (ρ : ℝ) (D : ι → RawJet2 K E) (x : Vec 2) :
    ‖rawFactorialArray ρ (fun a z => ∑ i, D i a z) x‖ ≤
      ∑ i, ‖rawFactorialArray ρ (D i) x‖ := by
  rw [rawFactorialArray_sum]
  exact norm_sum_le _ _

theorem rawFactorialDensity_sum_price_le {K : ℕ} {ι : Type*} [Fintype ι]
    (ρ : ℝ) (D : ι → RawJet2 K E) (x : Vec 2) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ i, rawFactorialDensity ρ (D i) x ≤ (p i) ^ 2 * B) :
    rawFactorialDensity ρ (fun a z => ∑ i, D i a z) x ≤ (∑ i, p i) ^ 2 * B := by
  have hi (i : ι) : ‖rawFactorialArray ρ (D i) x‖ ≤ p i * Real.sqrt B := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hp i) (Real.sqrt_nonneg _))).mp
    rw [rawFactorialArray_norm_sq, mul_pow, Real.sq_sqrt hB]
    exact hb i
  have hh := (rawFactorialArray_sum_norm_le ρ D x).trans (Finset.sum_le_sum (fun i _ => hi i))
  rw [← Finset.sum_mul] at hh
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  rwa [rawFactorialArray_norm_sq, mul_pow, Real.sq_sqrt hB] at hs

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Compact smooth plane functions and their exact homeomorphic pullbacks define native weak carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem orderedDerivative_hasCompactSupport {f : Vec 2 → E}
    (hf : HasCompactSupport f) {n : ℕ} (w : DerivativeWord2 n) :
    HasCompactSupport (orderedDerivative w f) := by
  induction n with
  | zero =>
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    simpa only [orderedDerivative_zero] using hf
  | succ n ih =>
    rw [orderedDerivative_succ]
    exact (ih (fun i => w i.castSucc)).fderiv_apply (𝕜 := ℝ) (basisVec (w (Fin.last n)))

def smoothCompactPlaneHk (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) : PlaneHk Set.univ K E :=
  smoothPlaneHk K f hf (fun a =>
    (ChartTransport.contDiff_orderedDerivative (p := 0) a.2 (hf.of_le (by simp))).continuous
      |>.memLp_of_hasCompactSupport (orderedDerivative_hasCompactSupport hc a.2))

theorem smoothCompactPlaneHk_jet_ae (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    planeJetOrder (smoothCompactPlaneHk K f hf hc) j w =ᵐ[volume] orderedDerivative w f :=
  smoothPlaneHk_jet_ae K f hf _ j hj w

def smoothCompactPlanePullback (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2)) :
    PlaneHk Set.univ K E :=
  smoothCompactPlaneHk K (f ∘ X) (hf.comp hX) (hc.comp_homeomorph X)

theorem smoothCompactPlanePullback_value_ae (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2)) :
    planeValue (smoothCompactPlanePullback K f hf hc X hX) =ᵐ[volume] f ∘ X := by
  unfold smoothCompactPlanePullback
  simpa only [planeValue, orderedDerivative_zero] using
    smoothCompactPlaneHk_jet_ae K (f ∘ X) (hf.comp hX) (hc.comp_homeomorph X)
      0 (Nat.zero_le K) Fin.elim0

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter UnitAddTorus
open scoped ENNReal Topology
namespace AVRegularity.CycleWords

/-! Uniformly bounded continuous approximations to a bounded measurable torus symbol. -/

local instance boundedTorusSymbolApproximationMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

local instance boundedTorusSymbolApproximationProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem boundedTorusSymbol_continuous_approximation (b : ScalarTorusL2) (C : ℝ)
    (hC : 0 < C) (hb : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin 2))), ‖b x‖ ≤ C) :
    ∃ c : ℕ → C(UnitAddTorus (Fin 2), ℂ),
      (∀ n x, ‖c n x‖ ≤ C) ∧
      ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin 2))),
        Tendsto (fun n => c n x) atTop (𝓝 (b x)) := by
  let μ : Measure (UnitAddTorus (Fin 2)) := volume
  let : IsFiniteMeasure μ := inferInstanceAs
    (IsFiniteMeasure (volume : Measure (UnitAddTorus (Fin 2))))
  let : μ.WeaklyRegular := inferInstanceAs
    ((volume : Measure (UnitAddTorus (Fin 2))).WeaklyRegular)
  let L : C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] ScalarTorusL2 :=
    ContinuousMap.toLp 2 μ ℂ
  have hd : DenseRange L := ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)
  obtain ⟨f, hf, ht⟩ := mem_closure_iff_seq_limit.mp (hd b)
  choose c hc using hf
  have ht' : Tendsto (fun n => L (c n)) atTop (𝓝 b) := by
    simpa only [hc] using ht
  have hm := tendstoInMeasure_of_tendsto_Lp ht'
  have hm' : TendstoInMeasure μ (fun n x => c n x) atTop b :=
    TendstoInMeasure.congr (fun n => ContinuousMap.coeFn_toLp (p := 2) μ (𝕜 := ℂ) (c n))
      EventuallyEq.rfl hm
  obtain ⟨ns, _, hns⟩ := hm'.exists_seq_tendsto_ae
  let d (n : ℕ) : C(UnitAddTorus (Fin 2), ℂ) :=
    ⟨fun x => normBallClip C (c (ns n) x),
      (continuous_normBallClip C hC).comp (c (ns n)).continuous⟩
  refine ⟨d, fun n x => norm_normBallClip_le C hC (c (ns n) x), ?_⟩
  filter_upwards [hns, hb] with x hx hbx
  change Tendsto (fun n => normBallClip C (c (ns n) x)) atTop (𝓝 (b x))
  have hh := (continuous_normBallClip C hC).continuousAt.tendsto.comp hx
  simpa only [Function.comp_def, normBallClip_eq_self C hC (b x) hbx] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! A continuous weight is a bounded native L2 operator on fields supported in a fixed compact set. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_compactWeightL2Operator (A : Set (Vec 2)) (hA : IsCompact A)
    (q : Vec 2 → ℝ) (hq : Continuous q) :
    ∃ W : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 volume,
      ∀ f : Lp E 2 volume, (∀ᵐ x ∂volume, x ∉ A → f x = 0) →
        W f =ᵐ[volume] (fun x => q x • f x) := by
  classical
  obtain ⟨C, hC, hb⟩ := (hA.image hq).isBounded.exists_pos_norm_le
  let b := A.indicator q
  have hm : Measurable b := hq.measurable.indicator hA.measurableSet
  have hbound (x : Vec 2) : ‖b x‖ ≤ C := by
    by_cases hx : x ∈ A
    · simpa only [b, Set.indicator_of_mem hx] using hb (q x) ⟨x, hx, rfl⟩
    · simpa only [b, Set.indicator_of_notMem hx, norm_zero] using hC.le
  refine ⟨boundedScalarL2Operator volume b hm C hC.le hbound, ?_⟩
  intro f hf
  filter_upwards [boundedScalarL2Operator_ae volume b hm C hC.le hbound f, hf] with x hx hs
  rw [hx]
  by_cases ha : x ∈ A
  · simp only [b, Set.indicator_of_mem ha]
  · simp only [b, Set.indicator_of_notMem ha, hs ha, smul_zero]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Actual dimensional mixed jets yield the normalized cell budget with no additional derivative cost. -/

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]

theorem molecular_normalized_reserve_le {f : Vec 2 → Vec 2 → E₁}
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (K d j a b : ℕ) (hf : IsBoxSmooth (j + a) b f)
    (X z : Vec 2) (M : ℝ)
    (hb : ρ ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b) *
      ‖iteratedFDeriv ℝ (j + a) (fun Y => iteratedFDeriv ℝ b
        (fun z' => (ν * e ^ d) • f (E⁻¹ • Y) z') z) (E • X)‖ ≤ M) :
    (ρ / e) ^ (a + b) * (e / E) ^ a *
      ‖iteratedFDeriv ℝ (j + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ *
        derivativeReserveFactor (ρ / e) K d ≤
      ((a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j /
        ((ν * ρ ^ d) * ((K.factorial : ℝ) / ((K + d).factorial : ℝ)))) * M := by
  have hdim := mixedJet_dimensional_norm_eq hf (ν * e ^ d) E⁻¹ (E • X) z
  have hcancel : E⁻¹ • E • X = X := by rw [inv_smul_smul₀ hE.ne']
  rw [hcancel, abs_of_pos (mul_pos hν (pow_pos he d)),
    abs_of_pos (inv_pos.mpr hE)] at hdim
  rw [hdim] at hb
  have hR : 0 ≤ derivativeReserveFactor (ρ / e) K d := by
    unfold derivativeReserveFactor
    positivity
  have hden : 0 < ν * e ^ d * (E⁻¹) ^ (j + a) := by positivity
  have hw : 0 < ρ ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b) := by positivity
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ ((ρ / e) ^ (a + b) * (e / E) ^ a) /
      (ν * e ^ d * (E⁻¹) ^ (j + a)) *
      (ρ ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b))⁻¹ *
      derivativeReserveFactor (ρ / e) K d by positivity)
  have hp := molecular_scaling_price ν e E ρ hν he hE hρ K d j a b
  have hn : (ν * ρ ^ d) * ((K.factorial : ℝ) / ((K + d).factorial : ℝ)) ≠ 0 := by positivity
  have hprice : ((ρ / e) ^ (a + b) * (e / E) ^ a) /
      (ν * e ^ d * (E⁻¹) ^ (j + a)) *
      (ρ ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b))⁻¹ *
      derivativeReserveFactor (ρ / e) K d =
      (a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j /
        ((ν * ρ ^ d) * ((K.factorial : ℝ) / ((K + d).factorial : ℝ))) := by
    apply (eq_div_iff hn).mpr
    convert hp using 1; ring
  rw [hprice] at hh
  have hleft : ((a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j /
      ((ν * ρ ^ d) * ((K.factorial : ℝ) / ((K + d).factorial : ℝ)))) *
      (ρ ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b) *
      (ν * e ^ d * (E⁻¹) ^ (j + a) *
        ‖iteratedFDeriv ℝ (j + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖)) =
      (ρ / e) ^ (a + b) * (e / E) ^ a *
        ‖iteratedFDeriv ℝ (j + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ *
        derivativeReserveFactor (ρ / e) K d := by
    rw [← hprice]
    field_simp
  rw [hleft] at hh
  exact hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Contractive plane reconstruction from actual torus-valued scalar Bloch fibres. -/

def planeScalarBlochReconstruct (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Lp ScalarTorusL2 2 (volume.restrict (planeFrequencyCell a P)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Vec 2)) :=
  isometryAdjointReconstruct (planeScalarBlochTransform a P hP)

theorem planeScalarBlochReconstruct_transform (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    planeScalarBlochReconstruct a P hP (planeScalarBlochTransform a P hP f) = f :=
  isometryAdjointReconstruct_leftInverse _ f

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Exact normal forms for finite chronological words of multiplication and differentiation. -/

variable {I V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

inductive FrequencyOperatorStep (I V E : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | multiply (coefficient : V → E →L[ℝ] E)
  | differentiate (word : List I)

def FrequencyOperatorStep.apply (s : FrequencyOperatorStep I V E)
    (direction : I → V) (f : V → E) : V → E :=
  match s with
  | .multiply A => fun x => A x (f x)
  | .differentiate w => frequencyOrderedDerivative direction w f

def FrequencyOperatorStep.smooth (s : FrequencyOperatorStep I V E) : Prop :=
  match s with
  | .multiply A => ContDiff ℝ (⊤ : ℕ∞) A
  | .differentiate _ => True

def FrequencyOperatorStep.normalForm (s : FrequencyOperatorStep I V E)
    (direction : I → V) (ts : List (FrequencyNormalTerm I V E E)) :
    List (FrequencyNormalTerm I V E E) :=
  match s with
  | .multiply A => frequencyNormalFormMultiply ts A
  | .differentiate w => frequencyNormalFormOrdered direction w ts

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.FastJets
namespace AVRegularity.CycleWords

/-! Diagonal differentiation consumes one joint derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_fderiv_diag {f : Vec 2 → Vec 2 → E}
    (hf : ContDiff ℝ (1 : ℕ) (Function.uncurry f)) (a b : ℝ) (x v : Vec 2) :
    fderiv ℝ (fun y => f (a • y) (b • y)) x v =
      a • fderiv ℝ (fun X => f X (b • x)) (a • x) v +
        b • fderiv ℝ (f (a • x)) (b • x) v := by
  have ht := (hf.differentiable (by norm_num) (a • x, b • x)).hasFDerivAt
  have hs := ht.comp (a • x) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (a • x) (b • x))
  have hz := ht.comp (b • x) (hasFDerivAt_prodMk_right (𝕜 := ℝ) (a • x) (b • x))
  have hg := (((ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt (x := x)).const_smul a).prodMk
    (((ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt (x := x)).const_smul b)
  have hc := ht.comp x hg
  simp only [Function.comp_def, Function.uncurry_apply_pair, Pi.smul_apply,
    ContinuousLinearMap.id_apply] at hc hs hz
  rw [hc.fderiv, hs.fderiv, hz.fderiv]
  change fderiv ℝ (Function.uncurry f) (a • x, b • x) (a • v, b • v) = _
  calc
    _ = fderiv ℝ (Function.uncurry f) (a • x, b • x)
        (a • (v, (0 : Vec 2)) + b • ((0 : Vec 2), v)) := by congr 1; simp
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

theorem joint_differentiableAt_diagTerm {N : ℕ} {W : Vec 2 → Vec 2 → E}
    (hW : ContDiff ℝ (N : ℕ) (Function.uncurry W)) (ρ e : ℝ)
    (p : List (Fin 2) × List (Fin 2)) (hp : p.1.length + p.2.length < N) (x : Vec 2) :
    DifferentiableAt ℝ (diagTerm W ρ e p) x := by
  have ht : ContDiff ℝ (1 : ℕ) (Function.uncurry (mixL p.1 p.2 W)) :=
    joint_mixL_contDiff 1 _ _ W (hW.of_le (by exact_mod_cast (by omega : 1 + p.1.length + p.2.length ≤ N)))
  exact ((ht.differentiable (by norm_num) _).comp x
    (by fun_prop : DifferentiableAt ℝ (fun y : Vec 2 => (ρ⁻¹ • y, e⁻¹ • y)) x)).const_smul _

theorem joint_fderiv_diagTerm {N : ℕ} {W : Vec 2 → Vec 2 → E}
    (hW : ContDiff ℝ (N : ℕ) (Function.uncurry W)) (ρ e : ℝ)
    (p : List (Fin 2) × List (Fin 2)) (hp : p.1.length + p.2.length < N) (x : Vec 2) (i : Fin 2) :
    fderiv ℝ (diagTerm W ρ e p) x (basisVec i) =
      termCoef ρ e p • (ρ⁻¹ • mixL (p.1 ++ [i]) p.2 W (ρ⁻¹ • x) (e⁻¹ • x) +
        e⁻¹ • mixL p.1 (p.2 ++ [i]) W (ρ⁻¹ • x) (e⁻¹ • x)) := by
  have ht : ContDiff ℝ (1 : ℕ) (Function.uncurry (mixL p.1 p.2 W)) :=
    joint_mixL_contDiff 1 _ _ W (hW.of_le (by exact_mod_cast (by omega : 1 + p.1.length + p.2.length ≤ N)))
  have hd : DifferentiableAt ℝ (fun y => mixL p.1 p.2 W (ρ⁻¹ • y) (e⁻¹ • y)) x :=
    (ht.differentiable (by norm_num) _).comp x
      (by fun_prop : DifferentiableAt ℝ (fun y : Vec 2 => (ρ⁻¹ • y, e⁻¹ • y)) x)
  change fderiv ℝ (fun y => termCoef ρ e p • mixL p.1 p.2 W (ρ⁻¹ • y) (e⁻¹ • y)) x (basisVec i) = _
  rw [fderiv_fun_const_smul hd]
  change termCoef ρ e p • fderiv ℝ (fun y => mixL p.1 p.2 W (ρ⁻¹ • y) (e⁻¹ • y)) x (basisVec i) = _
  rw [joint_fderiv_diag ht]
  have hf : IsBoxSmooth p.1.length 1 (fastL p.2 W) :=
    Weighted.isBoxSmooth_of_joint_contDiff _ _ _
      (joint_fastL_contDiff (p.1.length + 1) p.2 W
        (hW.of_le (by exact_mod_cast (by omega : p.1.length + 1 + p.2.length ≤ N))))
  have he := congrFun (congrFun (fastPartial_slowL i p.1 hf) (ρ⁻¹ • x)) (e⁻¹ • x)
  simp only [mixL, slowL_append_singleton, fastL_append_singleton, slowPartial, fastPartial] at he ⊢
  rw [he]

end AVRegularity.CycleWords
end
end
