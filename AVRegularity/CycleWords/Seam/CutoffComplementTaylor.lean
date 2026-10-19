-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.Adjoint
public import AVRegularity.Analysis.Convolution.Kernel.ApproximationBounds
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam.NegLowBand

/-! # the weighted jet norm of `q · U`
For a smooth scalar `q` with `‖D^i q(z)‖ ≤ C_i ⟨ϖz⟩^n` and smooth fields `U_x`:
`‖(q U_x)_x‖_{jet, -n, k} ≤ C · max_{l ≤ k} (∑_x π_x⁻¹ ‖(∑_{|w|=l} |D^w U_x|²)^{1/2}‖₂²)^{1/2}`.
-/

open AVRegularity.CycleWords.Seam.YoungKernel AVRegularity

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The size of the jet of order `l`. -/
def jetS (l : ℕ) (U : Vec 2 → E) (z : Vec 2) : ℝ :=
  Real.sqrt (∑ w : DerivativeWord2 l, ‖orderedDerivative w U z‖ ^ 2)

theorem jetS_nonneg (l : ℕ) (U : Vec 2 → E) (z : Vec 2) : 0 ≤ jetS l U z := Real.sqrt_nonneg _

theorem norm_iteratedFDeriv_le_jetS {l : ℕ} {U : Vec 2 → E} (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (z : Vec 2) : ‖iteratedFDeriv ℝ l U z‖ ≤ 2 ^ l * jetS l U z := by
  have h := norm_iteratedFDeriv_sq_le_words (hU.of_le (nat_le_top l)) z
  have h1 : ‖iteratedFDeriv ℝ l U z‖ ^ 2 ≤ (2 ^ l * jetS l U z) ^ 2 := by
    refine h.trans ?_
    unfold jetS
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    have : (2 : ℝ) ^ l ≤ ((2 : ℝ) ^ l) ^ 2 := by
      have : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
      nlinarith
    exact mul_le_mul_of_nonneg_right this (Finset.sum_nonneg fun _ _ => by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := jetS_nonneg l U z; positivity)
    (by norm_num)).1 h1

theorem jetS_le_iteratedFDeriv {l : ℕ} {U : Vec 2 → E} (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (z : Vec 2) : jetS l U z ≤ 2 ^ l * ‖iteratedFDeriv ℝ l U z‖ := by
  have h := sum_orderedDerivative_sq_le (hU.of_le (nat_le_top l)) z
  have h1 : jetS l U z ^ 2 ≤ (2 ^ l * ‖iteratedFDeriv ℝ l U z‖) ^ 2 := by
    unfold jetS
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), mul_pow]
    refine h.trans ?_
    have : (2 : ℝ) ^ l ≤ ((2 : ℝ) ^ l) ^ 2 := by
      have : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
      nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  exact (pow_le_pow_iff_left₀ (jetS_nonneg l U z) (by positivity) (by norm_num)).1 h1

theorem jetS_smul_le {q : Vec 2 → ℝ} {U : Vec 2 → E} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hU : ContDiff ℝ (⊤ : ℕ∞) U) (a : ℕ) (z : Vec 2) :
    jetS a (fun y => q y • U y) z ≤
      ∑ i ∈ Finset.range (a + 1), (4 : ℝ) ^ a * (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i q z‖ *
        jetS (a - i) U z := by
  have hqU : ContDiff ℝ (⊤ : ℕ∞) (fun y => q y • U y) := hq.smul hU
  have h1 := jetS_le_iteratedFDeriv hqU (l := a) z
  have h2 := norm_iteratedFDeriv_smul_le hq hU z (n := a) (nat_le_top a)
  refine h1.trans ?_
  have h3 : ‖iteratedFDeriv ℝ a (fun y => q y • U y) z‖ ≤
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i q z‖ *
        (2 ^ (a - i) * jetS (a - i) U z) := by
    refine h2.trans (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_jetS hU z) (by positivity)
  calc (2 : ℝ) ^ a * ‖iteratedFDeriv ℝ a (fun y => q y • U y) z‖
      ≤ 2 ^ a * ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i q z‖ *
        (2 ^ (a - i) * jetS (a - i) U z) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ∑ i ∈ Finset.range (a + 1), 2 ^ a * 2 ^ (a - i) * (a.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i q z‖ * jetS (a - i) U z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h4 : (2 : ℝ) ^ a * 2 ^ (a - i) ≤ 4 ^ a := by
          calc (2 : ℝ) ^ a * 2 ^ (a - i) ≤ 2 ^ a * 2 ^ a :=
                mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.sub_le a i))
                  (by positivity)
            _ = 4 ^ a := by rw [← mul_pow]; norm_num
        have := jetS_nonneg (a - i) U z
        have h5 : 0 ≤ (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i q z‖ * jetS (a - i) U z := by
          positivity
        calc 2 ^ a * 2 ^ (a - i) * (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i q z‖ *
              jetS (a - i) U z
            = (2 ^ a * 2 ^ (a - i)) * ((a.choose i : ℝ) * ‖iteratedFDeriv ℝ i q z‖ *
              jetS (a - i) U z) := by ring
          _ ≤ 4 ^ a * ((a.choose i : ℝ) * ‖iteratedFDeriv ℝ i q z‖ * jetS (a - i) U z) :=
              mul_le_mul_of_nonneg_right h4 h5
          _ = _ := by ring

theorem jetS_continuous {l : ℕ} {U : Vec 2 → E}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U) : Continuous (jetS l U) := by
  unfold jetS
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => ?_)
  exact (AVRegularity.orderedDerivative_contDiff w hU).continuous.norm.pow 2

end Pointwise

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem ennreal_sq_sum_le (m : ℕ) (y : ℕ → ℝ≥0∞) :
    (∑ j ∈ Finset.range m, y j) ^ 2 ≤ (m : ℝ≥0∞) * ∑ j ∈ Finset.range m, y j ^ 2 := by
  have := ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.range m) y (p := 2) (by norm_num)
  rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at this
  simpa [ENNReal.rpow_two] using this

theorem family_l2_bound (w : ι → ℝ≥0∞) (m : ℕ) (c : ℕ → ℝ≥0∞) (E : ℕ → ι → ℝ≥0∞) (Q : ℝ≥0∞)
    (hQ : ∀ j < m, ∑ x, w x * E j x ^ 2 ≤ Q) :
    ∑ x, w x * (∑ j ∈ Finset.range m, c j * E j x) ^ 2 ≤
      (m : ℝ≥0∞) * (∑ j ∈ Finset.range m, c j ^ 2) * Q := by
  calc ∑ x, w x * (∑ j ∈ Finset.range m, c j * E j x) ^ 2
      ≤ ∑ x, w x * ((m : ℝ≥0∞) * ∑ j ∈ Finset.range m, (c j * E j x) ^ 2) :=
        Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (ennreal_sq_sum_le m _)
    _ = (m : ℝ≥0∞) * ∑ j ∈ Finset.range m, c j ^ 2 * ∑ x, w x * E j x ^ 2 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ (m : ℝ≥0∞) * ∑ j ∈ Finset.range m, c j ^ 2 * Q := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun j hj => ?_)
        exact mul_le_mul' le_rfl (hQ j (Finset.mem_range.1 hj))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The constant of `weightedJet_smul_le`. -/
def jetCoeff (k : ℕ) (Cq : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range (k + 1), (1 / (a.factorial : ℝ)) *
    Real.sqrt (((a : ℝ) + 1) *
      ∑ i ∈ Finset.range (a + 1), ((4 : ℝ) ^ a * (a.choose i : ℝ) * Cq i) ^ 2)

theorem jetCoeff_nonneg (k : ℕ) (Cq : ℕ → ℝ) : 0 ≤ jetCoeff k Cq :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem weightedJet_smul_le (π : ι → ℝ) (n k : ℕ) (ϖ : ℝ) (Cq : ℕ → ℝ)
    (hCq : ∀ i, 0 ≤ Cq i) {q : Vec 2 → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqb : ∀ i z, ‖iteratedFDeriv ℝ i q z‖ ≤ Cq i * wbase ϖ z ^ ((n : ℝ) / 2))
    {U : ∀ x, Vec 2 → h x} (hU : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (U x)) (Q : ℝ≥0∞)
    (hQ : ∀ l ≤ k, ∑ x, ENNReal.ofReal ((π x)⁻¹) * eLpNorm (jetS l (U x)) 2 volume ^ 2 ≤ Q) :
    weightedJetNorm π (-(n : ℝ)) k ϖ 1
        (fun x _ wd z => orderedDerivative wd (fun y => q y • U x y) z) ≤
      ENNReal.ofReal (jetCoeff k Cq) * Q ^ (1 / 2 : ℝ) := by
  unfold weightedJetNorm jetCoeff
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity), Finset.sum_mul]
  refine Finset.sum_le_sum fun a ha => ?_
  have hak : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  set Kc : ℕ → ℝ := fun i => (4 : ℝ) ^ a * (a.choose i : ℝ) * Cq i with hKc
  have hKc0 : ∀ i, 0 ≤ Kc i := fun i => by have := hCq i; simp only [hKc]; positivity
  set c : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (Kc i) with hc
  set E : ℕ → ι → ℝ≥0∞ := fun j x => eLpNorm (jetS j (U x)) 2 volume with hE
  have hqU : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (fun y => q y • U x y) := fun x => hq.smul (hU x)
  have hW : ∀ z : Vec 2, wbase ϖ z ^ (-(n : ℝ) / 2) * wbase ϖ z ^ ((n : ℝ) / 2) = 1 := by
    intro z
    rw [← Real.rpow_add (wbase_pos ϖ z)]
    have : -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  -- the pointwise bound
  have hpt : ∀ x (z : Vec 2), wbase ϖ z ^ (-(n : ℝ) / 2) * jetS a (fun y => q y • U x y) z ≤
      ∑ i ∈ Finset.range (a + 1), Kc i * jetS (a - i) (U x) z := by
    intro x z
    have hw0 : 0 ≤ wbase ϖ z ^ (-(n : ℝ) / 2) := Real.rpow_nonneg (wbase_pos ϖ z).le _
    have h1 := jetS_smul_le hq (hU x) a z
    calc wbase ϖ z ^ (-(n : ℝ) / 2) * jetS a (fun y => q y • U x y) z
        ≤ wbase ϖ z ^ (-(n : ℝ) / 2) * ∑ i ∈ Finset.range (a + 1), (4 : ℝ) ^ a *
          (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i q z‖ * jetS (a - i) (U x) z :=
          mul_le_mul_of_nonneg_left h1 hw0
      _ = ∑ i ∈ Finset.range (a + 1), (4 : ℝ) ^ a * (a.choose i : ℝ) *
          (wbase ϖ z ^ (-(n : ℝ) / 2) * ‖iteratedFDeriv ℝ i q z‖) * jetS (a - i) (U x) z := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ Finset.range (a + 1), Kc i * jetS (a - i) (U x) z := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h2 : wbase ϖ z ^ (-(n : ℝ) / 2) * ‖iteratedFDeriv ℝ i q z‖ ≤ Cq i := by
            calc wbase ϖ z ^ (-(n : ℝ) / 2) * ‖iteratedFDeriv ℝ i q z‖
                ≤ wbase ϖ z ^ (-(n : ℝ) / 2) * (Cq i * wbase ϖ z ^ ((n : ℝ) / 2)) :=
                  mul_le_mul_of_nonneg_left (hqb i z) hw0
              _ = Cq i * (wbase ϖ z ^ (-(n : ℝ) / 2) * wbase ϖ z ^ ((n : ℝ) / 2)) := by ring
              _ = Cq i := by rw [hW z, mul_one]
          have hj := jetS_nonneg (a - i) (U x) z
          simp only [hKc]
          calc (4 : ℝ) ^ a * (a.choose i : ℝ) *
                (wbase ϖ z ^ (-(n : ℝ) / 2) * ‖iteratedFDeriv ℝ i q z‖) * jetS (a - i) (U x) z
              ≤ (4 : ℝ) ^ a * (a.choose i : ℝ) * Cq i * jetS (a - i) (U x) z := by
                have : 0 ≤ (4 : ℝ) ^ a * (a.choose i : ℝ) := by positivity
                gcongr
            _ = _ := rfl
  -- the `L²` bound of one component
  have hLp : ∀ x, eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((-(n : ℝ)) / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a,
        ‖orderedDerivative w (fun y => q y • U x y) z‖ ^ 2)) 2 volume ≤
      ∑ i ∈ Finset.range (a + 1), c i * E (a - i) x := by
    intro x
    have hmeasF : Continuous (fun z : Vec 2 => wbase ϖ z ^ (-(n : ℝ) / 2) *
        jetS a (fun y => q y • U x y) z) :=
      (Continuous.rpow_const (wbase_continuous ϖ) fun z => Or.inl (wbase_pos ϖ z).ne').mul
        (jetS_continuous (hqU x))
    have hG : (fun z : Vec 2 => ∑ i ∈ Finset.range (a + 1), Kc i * jetS (a - i) (U x) z) =
        ∑ i ∈ Finset.range (a + 1), (Kc i • jetS (a - i) (U x)) := by
      funext z
      simp [Finset.sum_apply]
    calc _ ≤ eLpNorm (fun z : Vec 2 => ∑ i ∈ Finset.range (a + 1), Kc i * jetS (a - i) (U x) z) 2
          volume := by
          refine eLpNorm_mono (f := fun z => wbase ϖ z ^ (-(n : ℝ) / 2) *
            jetS a (fun y => q y • U x y) z) hmeasF.aestronglyMeasurable fun z => ?_
          have hnn : 0 ≤ wbase ϖ z ^ (-(n : ℝ) / 2) * jetS a (fun y => q y • U x y) z :=
            mul_nonneg (Real.rpow_nonneg (wbase_pos ϖ z).le _) (jetS_nonneg _ _ _)
          rw [Real.norm_of_nonneg hnn]
          exact (hpt x z).trans (le_abs_self _ |>.trans_eq (Real.norm_eq_abs _).symm)
      _ = eLpNorm (∑ i ∈ Finset.range (a + 1), (Kc i • jetS (a - i) (U x))) 2 volume := by
          rw [hG]
      _ ≤ ∑ i ∈ Finset.range (a + 1), eLpNorm (Kc i • jetS (a - i) (U x)) 2 volume :=
          eLpNorm_sum_le (by norm_num)
      _ = ∑ i ∈ Finset.range (a + 1), c i * E (a - i) x := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [eLpNorm_const_smul, Real.enorm_of_nonneg (hKc0 i)]
  have hsum : ∑ x, ENNReal.ofReal ((π x)⁻¹) * eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^
      ((-(n : ℝ)) / 2) * Real.sqrt (∑ w : DerivativeWord2 a,
        ‖orderedDerivative w (fun y => q y • U x y) z‖ ^ 2)) 2 volume ^ 2 ≤
      ((a + 1 : ℕ) : ℝ≥0∞) * (∑ i ∈ Finset.range (a + 1), c i ^ 2) * Q := by
    refine le_trans (Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl
      (pow_le_pow_left' (hLp x) 2)) ?_
    exact family_l2_bound (fun x => ENNReal.ofReal ((π x)⁻¹)) (a + 1) c (fun j x => E (a - j) x) Q
      (fun j hj => hQ (a - j) (by omega))
  have e1 : ((a + 1 : ℕ) : ℝ≥0∞) * (∑ i ∈ Finset.range (a + 1), c i ^ 2) =
      ENNReal.ofReal (((a : ℝ) + 1) * ∑ i ∈ Finset.range (a + 1), (Kc i) ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
      (fun i _ => sq_nonneg _)]
    congr 1
    · rw [show ((a : ℝ) + 1) = ((a + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc, ENNReal.ofReal_pow (hKc0 i)]
  have hmain := ENNReal.rpow_le_rpow hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [e1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)] at hmain
  calc ENNReal.ofReal (1 ^ a / (a.factorial : ℝ)) * _ ≤ ENNReal.ofReal (1 ^ a / (a.factorial : ℝ)) *
        (ENNReal.ofReal ((((a : ℝ) + 1) * ∑ i ∈ Finset.range (a + 1), (Kc i) ^ 2) ^ (1 / 2 : ℝ)) *
          Q ^ (1 / 2 : ℝ)) := mul_le_mul' le_rfl hmain
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_pow, ← Real.sqrt_eq_rpow]

end Family

end AVRegularity.CycleWords.Seam.NegLowBand
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter Topology AVRegularity
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam.NegLowBand

/-! # the truncated kernels converge in the pairing
`⟨f, κ_R ⋆ G⟩ → ⟨f, K ⋆ G⟩` as `R → ∞` for `f, G ∈ L²`, `K = cutoffKernel μ`, `κ_R = χ(·/R) K`
(dominated convergence on the product of two planes). Also: the convolution of an `L¹` kernel
with an `L²` function is `L²` and measurable.
-/

open AVRegularity.CycleWords.Seam.YoungKernel

section Conv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

theorem conv_measurable {κ : Vec 2 → ℝ} (hκ : Measurable κ) {G : Vec 2 → E}
    (hG : Measurable G) : Measurable (conv κ G) := by
  have : StronglyMeasurable fun p : Vec 2 × Vec 2 => κ p.2 • G (p.1 - p.2) :=
    ((hκ.comp measurable_snd).smul (hG.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  exact (this.integral_prod_right' (ν := volume)).measurable

theorem conv_memLp {κ : Vec 2 → ℝ} (hκ : Measurable κ) (hκ1 : Integrable κ) [CompleteSpace E]
    {G : Vec 2 → E} (hG : Measurable G) (hG2 : MemLp G 2 volume) :
    MemLp (conv κ G) 2 volume := by
  have hm := conv_measurable hκ hG
  refine memLp_iff.2 ?_
  have ham : Measurable fun t => ‖κ t‖ₑ := hκ.enorm
  have hgm : Measurable fun y => ‖G y‖ₑ := hG.enorm
  have hafin : ∫⁻ t, ‖κ t‖ₑ ≠ ⊤ := hκ1.2.ne
  have hp : ∀ y, ‖conv κ G y‖ₑ ≤ ∫⁻ t, ‖κ t‖ₑ * ‖G (y - t)‖ₑ := fun y =>
    (enorm_integral_le_lintegral_enorm _).trans
      (le_of_eq (lintegral_congr fun t => by simp only [enorm_smul]))
  have hsq : ∫⁻ y, ‖conv κ G y‖ₑ ^ 2 ≤ (∫⁻ t, ‖κ t‖ₑ) ^ 2 * ∫⁻ y, ‖G y‖ₑ ^ 2 :=
    (lintegral_mono fun y => pow_le_pow_left' (hp y) 2).trans (young2 ham hgm hafin)
  have hne : (eLpNorm (conv κ G) 2 volume) ^ 2 ≠ ⊤ := by
    rw [eLpNorm_two_sq''' _ hm.aestronglyMeasurable]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top hafin) (lintegral_sq_ne_top hG2)) hsq
  refine lt_top_iff_ne_top.2 fun h => hne ?_
  rw [h]; simp

end Conv

section Limit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

theorem kernel_integrable' {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) : Integrable (cutoffKernel μ) := by
  have := kernel_weighted_integrable hm hs 0 0
  have h2 : Integrable (fun t => ‖cutoffKernel μ t‖) := by simpa using this
  exact (integrable_norm_iff (kernel_contDiff hm hs).continuous.aestronglyMeasurable).1 h2

theorem kernel_memLp2 {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) : MemLp (cutoffKernel μ) 2 volume := by
  have := (seamRealCutoffSchwartz μ (Real.pi / 2) hm hs).memLp 2 volume
  rwa [seamRealCutoffSchwartz_eq μ (Real.pi / 2) hm hs] at this

theorem pairInt_measurable {κ : Vec 2 → ℝ} (hκm : Measurable κ) {f G : Vec 2 → E}
    (hf : Measurable f) (hG : Measurable G) : Measurable (pairInt κ f G) :=
  (hκm.comp measurable_snd).mul
    ((hf.comp measurable_fst).inner (hG.comp (measurable_fst.sub measurable_snd)))

theorem kappa_abs_le (μ : Vec 2 → ℝ) (R : ℝ) (t : Vec 2) :
    |kappa μ R t| ≤ |cutoffKernel μ t| := by
  unfold kappa
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (chi_abs_le _)

theorem kappa_tendsto (μ : Vec 2 → ℝ) (t : Vec 2) :
    Tendsto (fun R : ℝ => kappa μ R t) atTop (𝓝 (cutoffKernel μ t)) := by
  have h1 : Tendsto (fun R : ℝ => R⁻¹ • t) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const t
  have h2 := (chi_contDiff.continuous.tendsto 0).comp h1
  have h3 := h2.mul_const (cutoffKernel μ t)
  rw [chi_zero, one_mul] at h3
  exact h3

theorem kappa_even {μ : Vec 2 → ℝ} (R : ℝ) (t : Vec 2) : kappa μ R (-t) = kappa μ R t := by
  unfold kappa
  rw [kernel_even, smul_neg]
  congr 1
  exact chiBump.neg _

theorem pair_tendsto {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) [CompleteSpace E] {f G : Vec 2 → E}
    (hf : Measurable f) (hG : Measurable G) (hf2 : MemLp f 2 volume) (hG2 : MemLp G 2 volume) :
    Tendsto (fun R : ℝ => ∫ y, inner ℝ (f y) (conv (kappa μ R) G y)) atTop
      (𝓝 (∫ y, inner ℝ (f y) (conv (cutoffKernel μ) G y))) := by
  have hK := kernel_contDiff hm hs
  have hK1 := kernel_integrable' hm hs
  have hK2 := kernel_memLp2 hm hs
  have hkc (R : ℝ) : Continuous (kappa μ R) := (kappa_contDiff hm hs R).continuous
  have hk1 (R : ℝ) (hR : R ≠ 0) : Integrable (kappa μ R) :=
    (hkc R).integrable_of_hasCompactSupport (kappa_compact μ hR)
  have hk2 (R : ℝ) (hR : R ≠ 0) : MemLp (kappa μ R) 2 volume :=
    (hkc R).memLp_of_hasCompactSupport (kappa_compact μ hR)
  have eK : ∫ y, inner ℝ (f y) (conv (cutoffKernel μ) G y) =
      ∫ p, pairInt (cutoffKernel μ) f G p ∂(volume.prod volume) := by
    simp_rw [conv_inner_eq_integral hK2 hG2]
    exact (integral_prod _ (pairInt_integrable hK.continuous.measurable hK1 hf hG hf2 hG2)).symm
  have eR : ∀ R : ℝ, 1 ≤ R → ∫ y, inner ℝ (f y) (conv (kappa μ R) G y) =
      ∫ p, pairInt (kappa μ R) f G p ∂(volume.prod volume) := by
    intro R hR
    have hR0 : R ≠ 0 := by positivity
    simp_rw [conv_inner_eq_integral (hk2 R hR0) hG2]
    exact (integral_prod _ (pairInt_integrable (hkc R).measurable (hk1 R hR0) hf hG hf2 hG2)).symm
  rw [eK]
  refine Tendsto.congr' (f₁ := fun R => ∫ p, pairInt (kappa μ R) f G p ∂(volume.prod volume)) ?_ ?_
  · exact (eventuallyEq_of_mem (Ici_mem_atTop (1 : ℝ)) fun R hR => (eR R hR).symm)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p => ‖pairInt (cutoffKernel μ) f G p‖) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun R =>
      (pairInt_measurable (hkc R).measurable hf hG).aestronglyMeasurable
  · refine Eventually.of_forall fun R => Eventually.of_forall fun p => ?_
    unfold pairInt
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using kappa_abs_le μ R p.2) (norm_nonneg _)
  · exact (pairInt_integrable hK.continuous.measurable hK1 hf hG hf2 hG2).norm
  · refine Eventually.of_forall fun p => ?_
    unfold pairInt
    exact (kappa_tendsto μ p.2).mul_const _

end Limit

end AVRegularity.CycleWords.Seam.NegLowBand
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam.NegLowBand

/-! # the weighted jet norm of a family of convolutions
`‖(κ ⋆ f_x)_x‖_{weighted jet, -n} ≤ (∑_a 2^a A_a / a!) · (∑_x π_x⁻¹ ‖⟨ϖ z⟩^{-n} f_x‖₂²)^{1/2}`,
where `A_a` bounds the weighted `L¹` norms of the `a`-th ordered derivatives of `κ`.
-/

open AVRegularity.CycleWords.Seam.YoungKernel AVRegularity

theorem ennreal_sum_sq_rpow_half {ι : Type*} [Fintype ι] (c : ℝ≥0∞) (w e : ι → ℝ≥0∞)
    (S : ℝ≥0∞) (hS : S = ∑ x, w x * e x ^ 2) :
    (∑ x, w x * (c * e x) ^ 2) ^ (1 / 2 : ℝ) = c * S ^ (1 / 2 : ℝ) := by
  have : (∑ x, w x * (c * e x) ^ 2) = c ^ 2 * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem jet_family_le {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (π : ι → ℝ) (n k : ℕ) {ϖ : ℝ} {κ : Vec 2 → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hc : HasCompactSupport κ) (f : ∀ x, Vec 2 → h x)
    (hf : ∀ x, Measurable (f x)) (hfl : ∀ x, LocallyIntegrable (f x) volume) (A : ℕ → ℝ)
    (hA : ∀ a, 0 ≤ A a)
    (hAw : ∀ a, a ≤ k → ∀ w : DerivativeWord2 a, ∫⁻ t, ENNReal.ofReal
      ((2 * wbase ϖ t) ^ ((n : ℝ) / 2) * ‖orderedDerivative w κ t‖) ≤ ENNReal.ofReal (A a)) :
    weightedJetNorm π (-(n : ℝ)) k ϖ 1
        (fun x _ wd z => orderedDerivative wd (conv κ (f x)) z) ≤
      ENNReal.ofReal (∑ a ∈ Finset.range (k + 1), (2 : ℝ) ^ a * A a / (a.factorial : ℝ)) *
        (∑ x, ENNReal.ofReal ((π x)⁻¹) *
          eLpNorm (fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f x z‖) 2 volume ^ 2) ^ (1 / 2 : ℝ) := by
  set S : ℝ≥0∞ := ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    eLpNorm (fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f x z‖) 2 volume ^ 2 with hS
  unfold weightedJetNorm
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by have := hA a; positivity), Finset.sum_mul]
  refine Finset.sum_le_sum fun a ha => ?_
  have hak : a ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  have hpt (x : ι) : eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((-(n : ℝ)) / 2) *
        Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (conv κ (f x)) z‖ ^ 2)) 2 volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ a * A a) *
        eLpNorm (fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f x z‖) 2 volume :=
    jet_component_le hκ hc (hf x) (hfl x) n a (hAw a hak)
  have h1 : (∑ x, ENNReal.ofReal ((π x)⁻¹) *
      eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((-(n : ℝ)) / 2) *
        Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (conv κ (f x)) z‖ ^ 2)) 2
        volume ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ a * A a) * S ^ (1 / 2 : ℝ) := by
    rw [← ennreal_sum_sq_rpow_half (ENNReal.ofReal ((2 : ℝ) ^ a * A a))
      (fun x => ENNReal.ofReal ((π x)⁻¹))
      (fun x => eLpNorm (fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f x z‖) 2 volume) S hS]
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun x _ => ?_) (by norm_num)
    exact mul_le_mul' le_rfl (pow_le_pow_left' (hpt x) 2)
  calc _ ≤ ENNReal.ofReal (1 ^ a / (a.factorial : ℝ)) *
        (ENNReal.ofReal ((2 : ℝ) ^ a * A a) * S ^ (1 / 2 : ℝ)) := mul_le_mul' le_rfl h1
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [one_pow]
        ring

end AVRegularity.CycleWords.Seam.NegLowBand
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Metric
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam.NegLowBand

/-! # The truncated weighted datum

For `u ∈ L²` the datum `f = 1_{B_ρ} ⟨ϖz⟩^{n} u` is in `L²` with compact support; with
`g = ⟨ϖz⟩^{-n/2} ‖f‖` one has `⟨f, u⟩ = g²` pointwise and `‖g‖₂² = ∫_{B_ρ} ⟨ϖz⟩^n ‖u‖²`.
-/

open AVRegularity.CycleWords.Seam.YoungKernel AVRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The truncated weighted datum. -/
def trunc (ϖ : ℝ) (n : ℕ) (ρ : ℝ) (u : Vec 2 → E) : Vec 2 → E :=
  (closedBall (0 : Vec 2) ρ).indicator (fun y => (wbase ϖ y ^ n) • u y)

/-- The weighted norm of the truncated datum. -/
def truncG (ϖ : ℝ) (n : ℕ) (ρ : ℝ) (u : Vec 2 → E) : Vec 2 → ℝ :=
  fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖trunc ϖ n ρ u z‖

theorem trunc_hasCompactSupport (ϖ : ℝ) (n : ℕ) (ρ : ℝ) (u : Vec 2 → E) :
    HasCompactSupport (trunc ϖ n ρ u) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Vec 2) ρ) fun _ hy =>
    Set.indicator_of_notMem hy _

theorem wbase_le_on_ball {ϖ : ℝ} (hϖ : ϖ ≤ 1) (hϖ0 : 0 < ϖ) {ρ : ℝ} {y : Vec 2}
    (hy : y ∈ closedBall (0 : Vec 2) ρ) : wbase ϖ y ≤ 1 + 2 * ρ ^ 2 := by
  have hn : ‖y‖ ≤ ρ := by simpa using hy
  have h0 : |y 0| ≤ ‖y‖ := by simpa using norm_le_pi_norm y 0
  have h1 : |y 1| ≤ ‖y‖ := by simpa using norm_le_pi_norm y 1
  have e0 : y 0 ^ 2 ≤ ρ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h0.trans hn) 2
  have e1 : y 1 ^ 2 ≤ ρ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans hn) 2
  have hϖ2 : ϖ ^ 2 ≤ 1 := by nlinarith
  unfold wbase
  have : ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) ≤ 1 * (y 0 ^ 2 + y 1 ^ 2) :=
    mul_le_mul_of_nonneg_right hϖ2 (by positivity)
  linarith

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem trunc_measurable {u : Vec 2 → E} (hu : Measurable u) (ϖ : ℝ) (n : ℕ) (ρ : ℝ) :
    Measurable (trunc ϖ n ρ u) := by
  have hw : Measurable fun y : Vec 2 => wbase ϖ y ^ n :=
    ((wbase_continuous ϖ).pow n).measurable
  exact (hw.smul hu).indicator measurableSet_closedBall

theorem trunc_memLp {u : Vec 2 → E} (hu : Measurable u) (hu2 : MemLp u 2 volume) {ϖ : ℝ}
    (hϖ : ϖ ≤ 1) (hϖ0 : 0 < ϖ) (n : ℕ) (ρ : ℝ) : MemLp (trunc ϖ n ρ u) 2 volume := by
  refine hu2.of_le_mul (c := (1 + 2 * ρ ^ 2) ^ n) (trunc_measurable hu ϖ n ρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  unfold trunc
  by_cases hy : y ∈ closedBall (0 : Vec 2) ρ
  · rw [Set.indicator_of_mem hy, norm_smul, Real.norm_eq_abs,
      abs_of_pos (pow_pos (wbase_pos ϖ y) n)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (wbase_pos ϖ y).le (wbase_le_on_ball hϖ hϖ0 hy) n) (norm_nonneg _)
  · rw [Set.indicator_of_notMem hy, norm_zero]
    positivity

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem truncG_nonneg (ϖ : ℝ) (n : ℕ) (ρ : ℝ) (u : Vec 2 → E) (z : Vec 2) :
    0 ≤ truncG ϖ n ρ u z :=
  mul_nonneg (Real.rpow_nonneg (wbase_pos ϖ z).le _) (norm_nonneg _)

theorem truncG_measurable {u : Vec 2 → E} (hu : Measurable u) (ϖ : ℝ) (n : ℕ) (ρ : ℝ) :
    Measurable (truncG ϖ n ρ u) :=
  (((wbase_continuous ϖ).measurable).pow_const _).mul (trunc_measurable hu ϖ n ρ).norm

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem truncG_le {u : Vec 2 → E} (ϖ : ℝ) (n : ℕ) (ρ : ℝ) (z : Vec 2) :
    ‖truncG ϖ n ρ u z‖ ≤ ‖trunc ϖ n ρ u z‖ := by
  rw [Real.norm_of_nonneg (truncG_nonneg ϖ n ρ u z)]
  unfold truncG
  have h1 : wbase ϖ z ^ (-(n : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (wbase_one_le ϖ z) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith [show -(n : ℝ) / 2 ≤ 0 by linarith])
  exact mul_le_of_le_one_left (norm_nonneg _) h1

theorem truncG_memLp {u : Vec 2 → E} (hu : Measurable u) (hu2 : MemLp u 2 volume) {ϖ : ℝ}
    (hϖ : ϖ ≤ 1) (hϖ0 : 0 < ϖ) (n : ℕ) (ρ : ℝ) : MemLp (truncG ϖ n ρ u) 2 volume :=
  (trunc_memLp hu hu2 hϖ hϖ0 n ρ).of_le (truncG_measurable hu ϖ n ρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => truncG_le ϖ n ρ z)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- `⟨f, u⟩ = g²` pointwise. -/
theorem trunc_inner_eq (ϖ : ℝ) (n : ℕ) (ρ : ℝ) (u : Vec 2 → E) (z : Vec 2) :
    inner ℝ (trunc ϖ n ρ u z) (u z) = truncG ϖ n ρ u z ^ 2 := by
  simp only [trunc, truncG]
  by_cases hz : z ∈ closedBall (0 : Vec 2) ρ
  · rw [Set.indicator_of_mem hz, inner_smul_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos (pow_pos (wbase_pos ϖ z) n)]
    simp only [conj_trivial, real_inner_self_eq_norm_sq]
    have hw := wbase_pos ϖ z
    have h2 : (wbase ϖ z ^ (-(n : ℝ) / 2)) ^ 2 = (wbase ϖ z ^ n)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
      rw [show (-(n : ℝ) / 2) * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring, Real.rpow_neg hw.le,
        Real.rpow_natCast]
    rw [mul_pow, mul_pow, h2]
    have : wbase ϖ z ^ n ≠ 0 := (pow_pos hw n).ne'
    field_simp
  · simp [Set.indicator_of_notMem hz]

/-- The squared `L²` norm of `g` is the weighted integral of `u` over the ball. -/
theorem truncG_eLpNorm_sq {u : Vec 2 → E} (hu : Measurable u) (ϖ : ℝ) (n : ℕ) (ρ : ℝ) :
    eLpNorm (truncG ϖ n ρ u) 2 volume ^ 2 =
      ∫⁻ y in closedBall (0 : Vec 2) ρ, ENNReal.ofReal (wbase ϖ y ^ n) * ‖u y‖ₑ ^ 2 := by
  rw [eLpNorm_two_sq''' _ (truncG_measurable hu ϖ n ρ).aestronglyMeasurable,
    ← lintegral_indicator measurableSet_closedBall]
  refine lintegral_congr fun z => ?_
  have h1 : ‖truncG ϖ n ρ u z‖ₑ ^ 2 = ENNReal.ofReal (truncG ϖ n ρ u z ^ 2) := by
    rw [Real.enorm_of_nonneg (truncG_nonneg ϖ n ρ u z), ENNReal.ofReal_pow (truncG_nonneg ϖ n ρ u z)]
  rw [h1, ← trunc_inner_eq]
  simp only [trunc]
  by_cases hz : z ∈ closedBall (0 : Vec 2) ρ
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, inner_smul_left]
    simp only [conj_trivial, real_inner_self_eq_norm_sq]
    rw [ENNReal.ofReal_mul (pow_pos (wbase_pos ϖ z) n).le, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
  · simp [Set.indicator_of_notMem hz]

theorem truncG_sq_integral {u : Vec 2 → E} (hu : Measurable u) (hu2 : MemLp u 2 volume) {ϖ : ℝ}
    (hϖ : ϖ ≤ 1) (hϖ0 : 0 < ϖ) (n : ℕ) (ρ : ℝ) :
    ENNReal.ofReal (∫ z, truncG ϖ n ρ u z ^ 2) = eLpNorm (truncG ϖ n ρ u) 2 volume ^ 2 := by
  rw [eLpNorm_two_sq''' _ (truncG_measurable hu ϖ n ρ).aestronglyMeasurable,
    ofReal_integral_eq_lintegral_ofReal (truncG_memLp hu hu2 hϖ hϖ0 n ρ).integrable_sq
      (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  refine lintegral_congr fun z => ?_
  rw [Real.enorm_of_nonneg (truncG_nonneg ϖ n ρ u z), ENNReal.ofReal_pow (truncG_nonneg ϖ n ρ u z)]

end AVRegularity.CycleWords.Seam.NegLowBand
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Metric Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam.NegLowBand

/-! # the duality step for the cell low pass

For `G_x ∈ L²` and `u_x = K ⋆ G_x` (`K = cutoffKernel μ`, `μ` supported in `|ξ| < π/2`), the
weighted moments of `u` over every ball are bounded by the negative jet norm of `G`:
`∑_x π_x⁻¹ ∫_{B_ρ} ⟨ϖz⟩^n |u_x|² ≤ (A · ‖G‖_{-n,k})²`, `A` depending only on `μ, n, k`.
The test is `κ_R ⋆ f` with `f = 1_{B_ρ} ⟨ϖz⟩^n u`; it pairs with `G` to
`⟨κ_R ⋆ G, f⟩ → ∫_{B_ρ} ⟨ϖz⟩^n |u|²`.
-/

section
open AVRegularity.CycleWords.Seam.YoungKernel AVRegularity

universe u v

theorem sq_le_of_le_mul_sqrt {P A D : ℝ} (hP : 0 ≤ P)
    (h : P ≤ A * Real.sqrt P * D) : P ≤ (A * D) ^ 2 := by
  rcases hP.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hs : 0 < Real.sqrt P := Real.sqrt_pos.2 hpos
    have hsq : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
    have h1 : Real.sqrt P ≤ A * D := by
      have : Real.sqrt P * Real.sqrt P ≤ Real.sqrt P * (A * D) := by nlinarith
      exact le_of_mul_le_mul_left this hs
    calc P = Real.sqrt P ^ 2 := hsq.symm
      _ ≤ (A * D) ^ 2 := pow_le_pow_left₀ hs.le h1 2

theorem duality_core {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (n k : ℕ) :
    ∃ A : ℝ, 0 < A ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
      [∀ i, SecondCountableTopology (h i)] [∀ i, CompleteSpace (h i)]
      (π : ι → ℝ), (∀ x, 0 < π x) → ∀ ϖ : ℝ, 0 < ϖ → ϖ ≤ 1 →
      ∀ G : ∀ x, Vec 2 → h x, (∀ x, Measurable (G x)) → (∀ x, MemLp (G x) 2 volume) →
      ∀ ρ : ℝ,
      ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∫⁻ y in closedBall (0 : Vec 2) ρ,
          ENNReal.ofReal (wbase ϖ y ^ n) * ‖conv (cutoffKernel μ) (G x) y‖ₑ ^ 2 ≤
        (ENNReal.ofReal A * AVRegularity.CycleWords.Assembly.negJetNorm π (n : ℝ) k ϖ 1 G) ^ 2 := by
  choose A hA0 hA using fun a : ℕ => kappa_young_const hm hs a n
  set sA : ℝ := ∑ a ∈ Finset.range (k + 1), (2 : ℝ) ^ a * A a / (a.factorial : ℝ) with hsA
  have hsAnn : 0 ≤ sA :=
    Finset.sum_nonneg fun a _ => by have := hA0 a; positivity
  refine ⟨1 + sA, by linarith, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ ϖ hϖ0 hϖ1 G hGm hG2 ρ
  have hK := kernel_contDiff hm hs
  have hK1 := kernel_integrable' hm hs
  have hKm : Measurable (cutoffKernel μ) := hK.continuous.measurable
  set u : ∀ x, Vec 2 → h x := fun x => conv (cutoffKernel μ) (G x) with hu
  have hum : ∀ x, Measurable (u x) := fun x => conv_measurable hKm (hGm x)
  have hu2 : ∀ x, MemLp (u x) 2 volume := fun x => conv_memLp hKm hK1 (hGm x) (hG2 x)
  set f : ∀ x, Vec 2 → h x := fun x => trunc ϖ n ρ (u x) with hf
  have hfm : ∀ x, Measurable (f x) := fun x => trunc_measurable (hum x) ϖ n ρ
  have hf2 : ∀ x, MemLp (f x) 2 volume := fun x => trunc_memLp (hum x) (hu2 x) hϖ1 hϖ0 n ρ
  have hfl : ∀ x, LocallyIntegrable (f x) volume := fun x =>
    (hf2 x).locallyIntegrable (by norm_num)
  set P : ℝ := ∑ x, (π x)⁻¹ * ∫ z, truncG ϖ n ρ (u x) z ^ 2 with hP
  have hpi : ∀ x, 0 ≤ (π x)⁻¹ := fun x => (inv_pos.2 (hπ x)).le
  have hint : ∀ x, 0 ≤ ∫ z, truncG ϖ n ρ (u x) z ^ 2 := fun x =>
    integral_nonneg fun z => sq_nonneg _
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun x _ => mul_nonneg (hpi x) (hint x)
  -- the left side is `ofReal P`
  have hS : ∑ x, ENNReal.ofReal ((π x)⁻¹) * eLpNorm (truncG ϖ n ρ (u x)) 2 volume ^ 2 =
      ENNReal.ofReal P := by
    rw [hP, ENNReal.ofReal_sum_of_nonneg fun x _ => mul_nonneg (hpi x) (hint x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_mul (hpi x), truncG_sq_integral (hum x) (hu2 x) hϖ1 hϖ0 n ρ]
  have hL : ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∫⁻ y in closedBall (0 : Vec 2) ρ,
      ENNReal.ofReal (wbase ϖ y ^ n) * ‖conv (cutoffKernel μ) (G x) y‖ₑ ^ 2 = ENNReal.ofReal P := by
    rw [← hS]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [truncG_eLpNorm_sq (hum x) ϖ n ρ]
  rw [hL]
  set D := AVRegularity.CycleWords.Assembly.negJetNorm π (n : ℝ) k ϖ 1 G with hD
  by_cases hDtop : D = ⊤
  · rw [hDtop, ENNReal.mul_top (by simp; linarith)]
    simp
  have hDr : D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hDtop).symm
  by_cases hP00 : P = 0
  · rw [hP00]; simp
  have hPpos : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hP00)
  set Bnd : ℝ := (1 + sA) * Real.sqrt P with hBnd
  have hBpos : 0 < Bnd := by positivity
  -- the tests
  have hT : ∀ R : ℝ, 1 ≤ R → ∀ x, ContDiff ℝ (⊤ : ℕ∞) (conv (kappa μ R) (f x)) ∧
      HasCompactSupport (conv (kappa μ R) (f x)) := by
    intro R hR x
    have hR0 : R ≠ 0 := by positivity
    exact ⟨conv_contDiff (kappa_contDiff hm hs R) (kappa_compact μ hR0) (hfl x),
      HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (kappa_compact μ hR0)
        (trunc_hasCompactSupport ϖ n ρ (u x))⟩
  have hjet : ∀ R : ℝ, 1 ≤ R → weightedJetNorm π (-(n : ℝ)) k ϖ 1
      (fun x _ wd z => orderedDerivative wd (conv (kappa μ R) (f x)) z) ≤
      ENNReal.ofReal Bnd := by
    intro R hR
    have hR0 : R ≠ 0 := by positivity
    have hj := jet_family_le π n k (kappa_contDiff hm hs R) (kappa_compact μ hR0) f hfm hfl A hA0
      (fun a _ w => hA a R ϖ hR hϖ0 hϖ1 w)
    have hS' : (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        eLpNorm (fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f x z‖) 2 volume ^ 2) = ENNReal.ofReal P := hS
    rw [hS', ENNReal.ofReal_rpow_of_nonneg hP0 (by norm_num), ← ENNReal.ofReal_mul hsAnn] at hj
    refine hj.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hBnd, ← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hpair : ∀ R : ℝ, 1 ≤ R → ENNReal.ofReal
      |∑ x, (π x)⁻¹ * ∫ z, inner ℝ (G x z) (conv (kappa μ R) (f x) z)| ≤
      ENNReal.ofReal Bnd * D :=
    fun R hR => cutoff_compact_test_pair_le π (n : ℝ) k ϖ 1 G _ (hT R hR) Bnd hBpos (hjet R hR)
  have hlim : Tendsto (fun R : ℝ => ∑ x, (π x)⁻¹ *
      ∫ z, inner ℝ (G x z) (conv (kappa μ R) (f x) z)) atTop (𝓝 P) := by
    have hlim' : Tendsto (fun R : ℝ => ∑ x, (π x)⁻¹ *
        ∫ y, inner ℝ (f x y) (conv (kappa μ R) (G x) y)) atTop (𝓝 P) := by
      rw [hP]
      refine tendsto_finsetSum _ fun x _ => ?_
      have := (pair_tendsto hm hs (hfm x) (hGm x) (hf2 x) (hG2 x)).const_mul ((π x)⁻¹)
      have e : ∫ z, truncG ϖ n ρ (u x) z ^ 2 =
          ∫ y, inner ℝ (f x y) (conv (cutoffKernel μ) (G x) y) :=
        integral_congr_ae (Filter.Eventually.of_forall fun y =>
          (trunc_inner_eq ϖ n ρ (u x) y).symm)
      rw [e]
      exact this
    refine hlim'.congr' (eventuallyEq_of_mem (Ici_mem_atTop (1 : ℝ)) fun R hR => ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    have hRn : R ≠ 0 := by have : (1 : ℝ) ≤ R := hR; positivity
    rw [conv_self_adjoint (kappa_contDiff hm hs R).continuous (kappa_compact μ hRn)
      (kappa_even R) (hfm x) (hGm x) (hf2 x) (hG2 x)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => real_inner_comm _ _)
  have hlim2 : Tendsto (fun R : ℝ => ENNReal.ofReal |∑ x, (π x)⁻¹ *
      ∫ z, inner ℝ (G x z) (conv (kappa μ R) (f x) z)|) atTop (𝓝 (ENNReal.ofReal |P|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (continuous_abs.tendsto _ |>.comp hlim)
  have hle : ENNReal.ofReal |P| ≤ ENNReal.ofReal Bnd * D :=
    le_of_tendsto hlim2 (eventually_atTop.2 ⟨1, hpair⟩)
  rw [abs_of_nonneg hP0, hDr, ← ENNReal.ofReal_mul hBpos.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hfin := sq_le_of_le_mul_sqrt hP0
    (by simpa [hBnd, mul_assoc] using hle)
  rw [hDr, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal hfin
end

/-! # the moment norm of the cell low pass
From the duality step: `momentNorm π n ϖ (K ⋆ G) ≤ C · ‖G‖_{-n,k}` for measurable `G_x ∈ L²`.
The weighted integral over the plane is the supremum of the integrals over the balls.
-/

section
open AVRegularity.CycleWords.Seam.YoungKernel AVRegularity

universe u v

theorem lintegral_eq_iSup_ball (F : Vec 2 → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y = ⨆ j : ℕ, ∫⁻ y in closedBall (0 : Vec 2) (j : ℝ), F y := by
  have hmono : Monotone fun j : ℕ => (closedBall (0 : Vec 2) (j : ℝ)).indicator F := by
    intro i j hij y
    dsimp only
    by_cases hy : y ∈ closedBall (0 : Vec 2) (i : ℝ)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem
        (closedBall_subset_closedBall (by exact_mod_cast hij) hy)]
    · rw [Set.indicator_of_notMem hy]; exact zero_le
  have h1 := lintegral_iSup (μ := (volume : Measure (Vec 2)))
    (fun j : ℕ => hF.indicator measurableSet_closedBall) hmono
  have hsup : ∀ y, (⨆ j : ℕ, (closedBall (0 : Vec 2) (j : ℝ)).indicator F y) = F y := by
    intro y
    obtain ⟨j, hj⟩ := exists_nat_ge ‖y‖
    apply le_antisymm
    · exact iSup_le fun i => Set.indicator_le_self' (fun _ _ => zero_le) y
    · refine le_iSup_of_le (f := fun j : ℕ => (closedBall (0 : Vec 2) (j : ℝ)).indicator F y) j ?_
      rw [Set.indicator_of_mem (by simpa using hj)]
  simp_rw [hsup] at h1
  rw [h1]
  refine iSup_congr fun j => ?_
  rw [lintegral_indicator measurableSet_closedBall]

theorem poly_sq_le (ϖ : ℝ) (n b1 b2 : ℕ) (hb : b1 + b2 ≤ n) (z : Vec 2) :
    (((ϖ * z 0) ^ b1 * (ϖ * z 1) ^ b2) ^ 2) ≤ wbase ϖ z ^ n := by
  have h0 : (ϖ * z 0) ^ 2 ≤ wbase ϖ z := by
    unfold wbase; nlinarith [sq_nonneg (ϖ * z 1)]
  have h1 : (ϖ * z 1) ^ 2 ≤ wbase ϖ z := by
    unfold wbase; nlinarith [sq_nonneg (ϖ * z 0)]
  calc ((ϖ * z 0) ^ b1 * (ϖ * z 1) ^ b2) ^ 2
      = ((ϖ * z 0) ^ 2) ^ b1 * ((ϖ * z 1) ^ 2) ^ b2 := by
        ring
    _ ≤ wbase ϖ z ^ b1 * wbase ϖ z ^ b2 :=
        mul_le_mul (pow_le_pow_left₀ (sq_nonneg _) h0 _) (pow_le_pow_left₀ (sq_nonneg _) h1 _)
          (by positivity) (by have := wbase_pos ϖ z; positivity)
    _ = wbase ϖ z ^ (b1 + b2) := (pow_add _ _ _).symm
    _ ≤ wbase ϖ z ^ n := pow_le_pow_right₀ (wbase_one_le ϖ z) hb

theorem moment_le_core {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (n k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
      [∀ i, SecondCountableTopology (h i)] [∀ i, CompleteSpace (h i)]
      (π : ι → ℝ), (∀ x, 0 < π x) → ∀ ϖ : ℝ, 0 < ϖ → ϖ ≤ 1 →
      ∀ G : ∀ x, Vec 2 → h x, (∀ x, Measurable (G x)) → (∀ x, MemLp (G x) 2 volume) →
      momentNorm π n ϖ (fun x => conv (cutoffKernel μ) (G x)) ≤
        ENNReal.ofReal C * AVRegularity.CycleWords.Assembly.negJetNorm π (n : ℝ) k ϖ 1 G := by
  obtain ⟨A, hA, hdual⟩ := duality_core.{u, v} hm hs n k
  have hcard : 0 < ((momentIndices n).card : ℝ) := by
    have : (0, 0) ∈ momentIndices n := by simp [momentIndices]
    exact_mod_cast Finset.card_pos.2 ⟨_, this⟩
  refine ⟨A * (momentIndices n).card, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ ϖ hϖ0 hϖ1 G hGm hG2
  have hK := kernel_contDiff hm hs
  have hK1 := kernel_integrable' hm hs
  have hKm : Measurable (cutoffKernel μ) := hK.continuous.measurable
  set D := AVRegularity.CycleWords.Assembly.negJetNorm π (n : ℝ) k ϖ 1 G with hD
  have hum : ∀ x, Measurable (conv (cutoffKernel μ) (G x)) := fun x =>
    conv_measurable hKm (hGm x)
  have hw : Measurable fun y : Vec 2 => ENNReal.ofReal (wbase ϖ y ^ n) :=
    ENNReal.measurable_ofReal.comp ((wbase_continuous ϖ).pow n).measurable
  have hsum : ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∫⁻ y, ENNReal.ofReal (wbase ϖ y ^ n) *
      ‖conv (cutoffKernel μ) (G x) y‖ₑ ^ 2 ≤ (ENNReal.ofReal A * D) ^ 2 := by
    have e : ∀ x, ∫⁻ y, ENNReal.ofReal (wbase ϖ y ^ n) * ‖conv (cutoffKernel μ) (G x) y‖ₑ ^ 2 =
        ⨆ j : ℕ, ∫⁻ y in closedBall (0 : Vec 2) (j : ℝ),
          ENNReal.ofReal (wbase ϖ y ^ n) * ‖conv (cutoffKernel μ) (G x) y‖ₑ ^ 2 :=
      fun x => lintegral_eq_iSup_ball _ (hw.mul ((hum x).enorm.pow_const 2))
    simp_rw [e, ENNReal.mul_iSup]
    rw [ENNReal.finsetSum_iSup_of_monotone (s := Finset.univ)
      (f := fun x (j : ℕ) => ENNReal.ofReal ((π x)⁻¹) * ∫⁻ y in closedBall (0 : Vec 2) (j : ℝ),
        ENNReal.ofReal (wbase ϖ y ^ n) * ‖conv (cutoffKernel μ) (G x) y‖ₑ ^ 2)
      (fun x i j hij => mul_le_mul' le_rfl (lintegral_mono_set
        (closedBall_subset_closedBall (by exact_mod_cast hij))))]
    exact iSup_le fun j => hdual π hπ ϖ hϖ0 hϖ1 G hGm hG2 (j : ℝ)
  unfold momentNorm
  have hβ : ∀ β ∈ momentIndices n, ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
      (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2) •
        conv (cutoffKernel μ) (G v) z) 2 volume ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal A * D := by
    intro β hβ
    have hβn : β.1 + β.2 ≤ n := by simpa [momentIndices] using (Finset.mem_filter.1 hβ).2
    have h1 : ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ ?_)
      exact_mod_cast Nat.one_le_iff_ne_zero.2
        (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
    have h2 : (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2) •
        conv (cutoffKernel μ) (G v) z) 2 volume ^ 2) ≤ (ENNReal.ofReal A * D) ^ 2 := by
      refine le_trans (Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl ?_) hsum
      have hpm : Measurable fun z : Vec 2 => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2) •
          conv (cutoffKernel μ) (G x) z := by
        have : Measurable fun z : Vec 2 => (ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2 := by fun_prop
        exact this.smul (hum x)
      rw [eLpNorm_two_sq''' _ hpm.aestronglyMeasurable]
      refine lintegral_mono fun z => ?_
      rw [enorm_smul, mul_pow]
      refine mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
      exact ENNReal.ofReal_le_ofReal (poly_sq_le ϖ n β.1 β.2 hβn z)
    have h3 := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h3
    norm_num at h3
    calc _ ≤ 1 * (ENNReal.ofReal A * D) := mul_le_mul' h1 h3
      _ = _ := one_mul _
  calc _ ≤ ∑ β ∈ momentIndices n, ENNReal.ofReal A * D := Finset.sum_le_sum hβ
    _ = ENNReal.ofReal (A * (momentIndices n).card) * D := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul hA.le, ENNReal.ofReal_natCast]
        ring
end

end AVRegularity.CycleWords.Seam.NegLowBand
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open scoped SchwartzMap
namespace AVRegularity.CycleWords.Seam

/-! Kernel moment cancellation removes the finite Taylor polynomial of a translation pairing. -/

/-- A fixed directional tensor is polynomial, so it is integrable against a Schwartz kernel. -/
theorem cutoff_tensor_integrable (κ : 𝓢(Vec 2, ℝ)) (n : ℕ) (A : DerivativeWord2 n → ℝ) :
    Integrable (fun y => κ y * directionalTensorValue n A y) := by
  have he : (fun y : Vec 2 => κ y * directionalTensorValue n A y) =
      fun y => ∑ w : DerivativeWord2 n, A w * ((∏ i, y (w i)) * κ y) := by
    funext y
    simp only [directionalTensorValue, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he]
  convert integrable_finsetSum' Finset.univ (fun w _ =>
    (cutoff_schwartz_coordinate_integrable κ w).const_mul (A w)) using 1
  funext y
  simp only [Finset.sum_apply, smul_eq_mul]

/-- Coordinate moment cancellation removes every fixed directional tensor of that degree. -/
theorem cutoff_tensor_integral_zero (κ : 𝓢(Vec 2, ℝ)) (n : ℕ) (A : DerivativeWord2 n → ℝ)
    (hm : ∀ w : DerivativeWord2 n, (∫ y, (∏ i, y (w i)) * κ y) = 0) :
    (∫ y, κ y * directionalTensorValue n A y) = 0 := by
  have he : (fun y : Vec 2 => κ y * directionalTensorValue n A y) =
      fun y => ∑ w : DerivativeWord2 n, A w * ((∏ i, y (w i)) * κ y) := by
    funext y
    simp only [directionalTensorValue, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro w _
    rw [integral_const_mul, hm w, mul_zero]
  · intro w _
    exact (cutoff_schwartz_coordinate_integrable κ w).const_mul (A w)

theorem cutoff_taylor_integrable (κ : 𝓢(Vec 2, ℝ)) (F : Vec 2 → ℝ) (K : ℕ) :
    Integrable (fun y => κ y * taylorSlow 0 K F 0 y) := by
  have hi (n : ℕ) : Integrable (fun y => κ y * iteratedFDeriv ℝ n F 0 (fun _ => y)) := by
    simp_rw [iteratedFDeriv_same_direction_eq_tensor F n 0]
    exact cutoff_tensor_integrable κ n _
  have he : (fun y : Vec 2 => κ y * taylorSlow 0 K F 0 y) =
      fun y => ∑ n ∈ Finset.Icc 0 K, (n.factorial : ℝ)⁻¹ *
        (κ y * iteratedFDeriv ℝ n F 0 (fun _ => y)) := by
    funext y
    simp only [taylorSlow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he]
  convert integrable_finsetSum' (Finset.Icc 0 K)
    (fun n _ => (hi n).const_mul (n.factorial : ℝ)⁻¹) using 1
  funext y
  simp only [Finset.sum_apply]

/-- The literal cutoff averages every finite Taylor polynomial to its constant term. -/
theorem cutoffKernel_taylor_integral_eq (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (hflat : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → m ξ = 1)
    (F : Vec 2 → ℝ) (K : ℕ) :
    (∫ y, cutoffKernel m y * taylorSlow 0 K F 0 y) = F 0 := by
  let κ := seamRealCutoffSchwartz m R hm hs
  have hi (n : ℕ) : Integrable (fun y => cutoffKernel m y *
      iteratedFDeriv ℝ n F 0 (fun _ => y)) := by
    simp_rw [iteratedFDeriv_same_direction_eq_tensor F n 0]
    simpa only [κ, seamRealCutoffSchwartz_eq] using cutoff_tensor_integrable κ n
      (fun w => iteratedFDeriv ℝ n F 0 (fun i => basisVec (w i)))
  have hz (n : ℕ) (hn : n ≠ 0) :
      (∫ y, cutoffKernel m y * iteratedFDeriv ℝ n F 0 (fun _ => y)) = 0 := by
    simp_rw [iteratedFDeriv_same_direction_eq_tensor F n 0]
    simpa only [κ, seamRealCutoffSchwartz_eq] using cutoff_tensor_integral_zero κ n
      (fun w => iteratedFDeriv ℝ n F 0 (fun i => basisVec (w i)))
      (fun w => by simpa only [κ, seamRealCutoffSchwartz_eq] using
        cutoffKernel_coordinate_moment_zero m R hm hs hflat hn w)
  obtain ⟨ε, hε, hεm⟩ := hflat
  have hm0 : m 0 = 1 := hεm 0 (by simpa [vecDot] using hε.le)
  have he : (fun y : Vec 2 => cutoffKernel m y * taylorSlow 0 K F 0 y) =
      fun y => ∑ n ∈ Finset.Icc 0 K, (n.factorial : ℝ)⁻¹ *
        (cutoffKernel m y * iteratedFDeriv ℝ n F 0 (fun _ => y)) := by
    funext y
    simp only [taylorSlow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he, integral_finsetSum]
  · simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
        iteratedFDeriv_zero_apply]
      rw [integral_mul_const, seamCutoffKernel_integral m R hm hs, hm0, one_mul]
    · intro n _ hn
      rw [hz n hn, mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩))
  · intro n _
    exact (hi n).const_mul _

/-- Word bounds control a full repeated-direction tensor without any target-space dimension cost. -/
theorem cutoff_directional_derivative_bound (F : Vec 2 → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (n : ℕ) (z y : Vec 2) (B : ℝ)
    (hb : ∀ w : DerivativeWord2 n, ‖orderedDerivative w F z‖ ≤ B) :
    ‖iteratedFDeriv ℝ n F z (fun _ => y)‖ ≤ (2 : ℝ) ^ n * ‖y‖ ^ n * B := by
  have hc (w : DerivativeWord2 n) :
      ‖iteratedFDeriv ℝ n F z (fun i => basisVec (w i))‖ ≤ B := by
    have he : orderedDerivative (fun i => w (Fin.rev i)) F z =
        iteratedFDeriv ℝ n F z (fun i => basisVec (w i)) := by
      rw [orderedDerivative_eq_iteratedFDeriv _ (hF.of_le (by simp))]
      simp only [Fin.rev_rev]
    rw [← he]
    exact hb _
  rw [iteratedFDeriv_same_direction_eq_tensor]
  unfold directionalTensorValue
  calc
    _ ≤ ∑ w : DerivativeWord2 n, ‖(∏ i, y (w i)) •
        iteratedFDeriv ℝ n F z (fun i => basisVec (w i))‖ := norm_sum_le _ _
    _ ≤ ∑ _w : DerivativeWord2 n, ‖y‖ ^ n * B := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_smul]
      exact mul_le_mul (cutoff_coordinate_product_norm_le w y) (hc w)
        (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, DerivativeWord2, DerivativeWord,
        Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

theorem cutoffBracket_segment_le (s : ℝ) (y : Vec 2) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    cutoffBracket s (t • y) ≤ cutoffBracket s y := by
  have htp : t ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ ht.1 ht.2 2
  have hh := mul_le_mul_of_nonneg_right htp
    (mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))))
  dsimp only [cutoffBracket, Pi.smul_apply, smul_eq_mul]
  nlinarith only [hh]

/-- Integral Taylor remainder using only the values of the highest word jets on the segment. -/
theorem cutoff_taylor_remainder_bound (F : Vec 2 → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (K p : ℕ) (s B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z (w : DerivativeWord2 (K + 1)),
      ‖orderedDerivative w F z‖ ≤ B * (2 * cutoffBracket s z) ^ p) (y : Vec 2) :
    ‖F y - taylorSlow 0 K F 0 y‖ ≤
      (2 : ℝ) ^ (K + 1) * ‖y‖ ^ (K + 1) * B * (2 * cutoffBracket s y) ^ p := by
  let A := (2 : ℝ) ^ (K + 1) * ‖y‖ ^ (K + 1) * B * (2 * cutoffBracket s y) ^ p
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg (by positivity) hB)
      (pow_nonneg (by linarith only [cutoffBracket_one_le s y]) _)
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ‖iteratedFDeriv ℝ (K + 1) F (t • y) (fun _ => y)‖ ≤ A := by
    have hp := pow_le_pow_left₀
      (show 0 ≤ 2 * cutoffBracket s (t • y) by linarith only [cutoffBracket_one_le s (t • y)])
      (mul_le_mul_of_nonneg_left (cutoffBracket_segment_le s y ht) (by norm_num)) p
    exact (cutoff_directional_derivative_bound F hF (K + 1) (t • y) y
      (B * (2 * cutoffBracket s (t • y)) ^ p) (hb _)).trans
      (by dsimp only [A]; simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hp (show 0 ≤ (2 : ℝ) ^ (K + 1) * ‖y‖ ^ (K + 1) * B
          from mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) _)) hB))
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (f := F) (x := (0 : Vec 2))
    (y := y) (n := K) (fun t _ => (hF.of_le (by simp)).contDiffAt)
  have hp : taylorSlow 0 K F 0 y =
      ∑ n ∈ Finset.range (K + 1), (n.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ n F 0 (fun _ => y) := by
    simp only [taylorSlow, ← Nat.range_succ_eq_Icc_zero, smul_eq_mul]
  have hr : F y - taylorSlow 0 K F 0 y = (K.factorial : ℝ)⁻¹ •
      ∫ t in (0 : ℝ)..1, (1 - t) ^ K •
        iteratedFDeriv ℝ (K + 1) F (t • y) (fun _ => y) := by
    rw [hp]
    simpa only [zero_add, add_sub_cancel_left] using
      congrArg (fun c => c - ∑ n ∈ Finset.range (K + 1), (n.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ n F 0 (fun _ => y)) ht
  have hi : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ K •
        iteratedFDeriv ℝ (K + 1) F (t • y) (fun _ => y)‖ ≤ A := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1, A := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · filter_upwards with t ht
          have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
          have hw : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
          have hwle : (1 - t) ^ K * A ≤ A := by
            have hh : (1 - t) ^ K * A ≤ 1 * A := mul_le_mul_of_nonneg_right
              (pow_le_one₀ hw (by linarith only [ht'.1])) hA
            simpa only [one_mul] using hh
          rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hw _)]
          exact (mul_le_mul_of_nonneg_left (hd t ht') (pow_nonneg hw _)).trans
            hwle
        · exact intervalIntegrable_const
      _ = A := by simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  rw [hr, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hf : (K.factorial : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero K))
  exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (Nat.cast_nonneg _))).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hf hA)

/-- A scalar translation pairing gains arbitrary order on the cutoff complement. -/
theorem cutoff_scalar_complement_bound (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (hflat : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → m ξ = 1)
    (F : Vec 2 → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (N p : ℕ) (s B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z (w : DerivativeWord2 N), ‖orderedDerivative w F z‖ ≤
      B * (2 * cutoffBracket s z) ^ p) :
    |F 0 - ∫ y, cutoffKernel m y * F y| ≤ B *
      ((2 : ℝ) ^ N * cutoffWeightedMoment (cutoffKernel m) s N p +
        2 ^ p + cutoffWeightedMoment (cutoffKernel m) s 0 p) := by
  let κ := seamRealCutoffSchwartz m R hm hs
  have hκ (y : Vec 2) : κ y = cutoffKernel m y := congrFun (seamRealCutoffSchwartz_eq m R hm hs) y
  cases N with
  | zero =>
    have hf (y : Vec 2) : ‖F y‖ ≤ B * (2 * cutoffBracket s y) ^ p := by
      simpa only [orderedDerivative_zero] using hb y Fin.elim0
    have hbound : Integrable (fun y : Vec 2 => B *
        (‖cutoffKernel m y‖ * ‖y‖ ^ 0 * (2 * cutoffBracket s y) ^ p)) := by
      simpa only [hκ] using (cutoff_schwartz_weightedMoment_integrable κ s 0 p).const_mul B
    have hi : ‖∫ y, cutoffKernel m y * F y‖ ≤
        B * cutoffWeightedMoment (cutoffKernel m) s 0 p := by
      calc
        _ ≤ ∫ y : Vec 2, B * (‖cutoffKernel m y‖ * ‖y‖ ^ 0 * (2 * cutoffBracket s y) ^ p) := by
          apply norm_integral_le_of_norm_le hbound
          exact Filter.Eventually.of_forall fun y => by
            rw [norm_mul, pow_zero, mul_one]
            exact (mul_le_mul_of_nonneg_left (hf y) (norm_nonneg _)).trans_eq (by ring)
        _ = _ := integral_const_mul _ _
    have h0 : |F 0| ≤ B * 2 ^ p := by
      simpa only [Real.norm_eq_abs, cutoffBracket, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
        zero_add, mul_zero, add_zero, mul_one] using hf 0
    have hn := cutoffWeightedMoment_nonneg (cutoffKernel m) s 0 p
    have hmain := (abs_sub (F 0) (∫ y, cutoffKernel m y * F y)).trans
      (add_le_add h0 (by simpa only [Real.norm_eq_abs] using hi))
    simp only [pow_zero, one_mul]
    nlinarith only [hmain, mul_nonneg hB hn]
  | succ K =>
    let A := (2 : ℝ) ^ (K + 1) * B
    have hA : 0 ≤ A := mul_nonneg (by positivity) hB
    have hbound : Integrable (fun y : Vec 2 => A *
        (‖cutoffKernel m y‖ * ‖y‖ ^ (K + 1) * (2 * cutoffBracket s y) ^ p)) := by
      simpa only [hκ] using (cutoff_schwartz_weightedMoment_integrable κ s (K + 1) p).const_mul A
    have hr (y : Vec 2) : ‖cutoffKernel m y * (F y - taylorSlow 0 K F 0 y)‖ ≤ A *
        (‖cutoffKernel m y‖ * ‖y‖ ^ (K + 1) * (2 * cutoffBracket s y) ^ p) := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (cutoff_taylor_remainder_bound F hF K p s B hB hb y)
        (norm_nonneg _)).trans_eq (by dsimp only [A]; ring)
    have hrem : Integrable (fun y => cutoffKernel m y * (F y - taylorSlow 0 K F 0 y)) := by
      apply Integrable.mono' hbound
      · have ht : Continuous (fun y : Vec 2 => taylorSlow 0 K F 0 y) := by
          unfold taylorSlow
          fun_prop
        exact ((seamCutoffKernel_contDiff m R hm hs.continuous).continuous.mul
          (hF.continuous.sub ht)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall hr
    have hpoly : Integrable (fun y => cutoffKernel m y * taylorSlow 0 K F 0 y) := by
      simpa only [hκ] using cutoff_taylor_integrable κ F K
    have hfull : Integrable (fun y => cutoffKernel m y * F y) := by
      convert hrem.add hpoly using 1
      funext y
      simp only [Pi.add_apply]
      ring
    have hi : (∫ y, cutoffKernel m y * (F y - taylorSlow 0 K F 0 y)) =
        (∫ y, cutoffKernel m y * F y) - F 0 := by
      simp_rw [mul_sub]
      rw [integral_sub hfull hpoly, cutoffKernel_taylor_integral_eq m R hm hs hflat F K]
    have hn0 := cutoffWeightedMoment_nonneg (cutoffKernel m) s 0 p
    calc
      _ = ‖∫ y, cutoffKernel m y * (F y - taylorSlow 0 K F 0 y)‖ := by
        rw [hi, Real.norm_eq_abs, abs_sub_comm]
      _ ≤ ∫ y : Vec 2, A * (‖cutoffKernel m y‖ * ‖y‖ ^ (K + 1) * (2 * cutoffBracket s y) ^ p) :=
        norm_integral_le_of_norm_le hbound (Filter.Eventually.of_forall hr)
      _ = A * cutoffWeightedMoment (cutoffKernel m) s (K + 1) p := integral_const_mul _ _
      _ ≤ _ := by
        have hh := mul_nonneg hB (add_nonneg (show 0 ≤ (2 : ℝ) ^ p by positivity) hn0)
        dsimp only [A]
        nlinarith only [hh]

end AVRegularity.CycleWords.Seam
end
