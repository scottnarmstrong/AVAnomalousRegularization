-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.TransCalc
public import AVRegularity.CycleWords.MixedWords.GaussianAbsorb
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import AVRegularity.CycleWords.MixedWords.FibreDuality
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The amplitude jet norm of a cut-off transform

`Pair c H θ` is the family size of the pair of transforms of a family `H` at `θ`.

For a family `F` with `n` integrable moments and a smooth cutoff `χ` with
`ϖ^l ‖D^l χ‖ ≤ B` for `l ≤ n`, the amplitude jet norm of `(χ F̂_cos, χ F̂_sin)` at `θ` is at most
`|momentIndices n| 2^n B` times the sum over the words `w` of length `j ≤ n` of the pair sizes of
the moment families `ϖ^j y^w F` (`amplitudeJetNorm_trans_le`): Leibniz, differentiation under
the integral (`Trans_orderedDerivative`) and the invariance of the pair
(`Trans_pair_iteratedDeriv`). -/

open AVRegularity.CycleWords.Assembly

section Component

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Reversal of a word. -/
def RevEquiv (j : ℕ) : (Fin j → Fin 2) ≃ (Fin j → Fin 2) where
  toFun idx := fun i => idx (Fin.rev i)
  invFun idx := fun i => idx (Fin.rev i)
  left_inv idx := by funext i; simp
  right_inv idx := by funext i; simp

/-- The iterated derivative of a transform by the transforms of the moments. -/
theorem Trans_norm_iteratedFDeriv_le {ψ : ℝ → ℝ} (hψ : IsUnitPhase ψ) {j : ℕ}
    {H : Vec 2 → E} (hH : HasIntegrableMoments j H) (θ : Vec 2) :
    ‖iteratedFDeriv ℝ j (phaseTransform ψ H) θ‖ ≤
      ∑ w : DerivativeWord2 j,
        ‖phaseTransform (iteratedDeriv j ψ) (fun y => wordMonomial w y • H y) θ‖ := by
  refine (norm_le_sum_basis _).trans (le_of_eq ?_)
  rw [← (RevEquiv j).sum_comp (fun w : Fin j → Fin 2 =>
    ‖phaseTransform (iteratedDeriv j ψ) (fun y => wordMonomial w y • H y) θ‖)]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have h1 := congrFun (orderedDerivative_eq_iteratedFDeriv (RevEquiv j idx)
    (Trans_contDiff j hψ hH)) θ
  have h2 := congrFun (Trans_orderedDerivative (RevEquiv j idx) hψ hH) θ
  rw [← h2, h1]
  simp [RevEquiv]

/-- **Leibniz for one component** of a cut-off transform. -/
theorem norm_thetaPartial_trans_le {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {ψ : ℝ → ℝ}
    (hψ : IsUnitPhase ψ) (α : ℕ × ℕ) {H : Vec 2 → E} (hH : HasIntegrableMoments (α.1 + α.2) H) (θ : Vec 2) :
    ‖thetaPartial α.1 α.2 (fun θ => χ θ • phaseTransform ψ H θ) θ‖ ≤
      ∑ l ∈ Finset.range (α.1 + α.2 + 1), ∑ w : DerivativeWord2 (α.1 + α.2 - l),
        (((α.1 + α.2).choose l : ℝ) * ‖iteratedFDeriv ℝ l χ θ‖) *
          ‖phaseTransform (iteratedDeriv (α.1 + α.2 - l) ψ) (fun y => wordMonomial w y • H y) θ‖ := by
  set a := α.1 + α.2 with ha
  refine (norm_thetaPartial_le α.1 α.2 _ θ).trans ?_
  have hT : ContDiff ℝ (a : ℕ∞) (phaseTransform ψ H) := Trans_contDiff a hψ hH
  refine (norm_iteratedFDeriv_smul_le (hχ.of_le (by exact_mod_cast le_top)) hT θ le_rfl).trans ?_
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (Trans_norm_iteratedFDeriv_le hψ (hH.mono (Nat.sub_le a l)) θ) (by positivity)

end Component

theorem sq_rpow_half' (a : ℝ≥0∞) : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The family size of the pair of transforms. -/
def Pair (c : ι → ℝ≥0∞) (H : ∀ x, Vec 2 → h x) (θ : Vec 2) : ℝ≥0∞ :=
  (∑ x, c x * (ENNReal.ofReal (‖phaseTransform Real.cos (H x) θ‖ ^ 2) +
    ENNReal.ofReal (‖phaseTransform Real.sin (H x) θ‖ ^ 2))) ^ (1 / 2 : ℝ)

theorem Pair_sq (c : ι → ℝ≥0∞) (H : ∀ x, Vec 2 → h x) (θ : Vec 2) :
    Pair c H θ ^ 2 = ∑ x, c x * (ENNReal.ofReal (‖phaseTransform Real.cos (H x) θ‖ ^ 2) +
      ENNReal.ofReal (‖phaseTransform Real.sin (H x) θ‖ ^ 2)) := by
  unfold Pair
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Homogeneity of the pair size. -/
theorem Pair_const_smul (c : ι → ℝ≥0∞) (H : ∀ x, Vec 2 → h x) {r : ℝ} (hr : 0 ≤ r)
    (θ : Vec 2) :
    Pair c (fun x y => r • H x y) θ = ENNReal.ofReal r * Pair c H θ := by
  unfold Pair
  have he : ∀ x, c x * (ENNReal.ofReal (‖phaseTransform Real.cos (fun y => r • H x y) θ‖ ^ 2) +
      ENNReal.ofReal (‖phaseTransform Real.sin (fun y => r • H x y) θ‖ ^ 2)) =
      ENNReal.ofReal r ^ 2 * (c x * (ENNReal.ofReal (‖phaseTransform Real.cos (H x) θ‖ ^ 2) +
        ENNReal.ofReal (‖phaseTransform Real.sin (H x) θ‖ ^ 2))) := by
    intro x
    rw [Trans_const_smul, Trans_const_smul, norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr, mul_pow, mul_pow, ENNReal.ofReal_mul (sq_nonneg r),
      ENNReal.ofReal_mul (sq_nonneg r), ENNReal.ofReal_pow hr]
    ring
  simp only [he, ← Finset.mul_sum]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

variable [∀ i, CompleteSpace (h i)]

/-- **Leibniz for the family pair** of a cut-off transform at one multi-index. -/
theorem pair_thetaPartial_trans_le (c : ι → ℝ≥0∞) {χ : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (α : ℕ × ℕ) {F : ∀ x, Vec 2 → h x}
    (hF : ∀ x, HasIntegrableMoments (α.1 + α.2) (F x)) (θ : Vec 2) :
    (∑ x, c x * (ENNReal.ofReal (‖thetaPartial α.1 α.2
          (fun θ' => χ θ' • phaseTransform Real.cos (F x) θ') θ‖ ^ 2) +
        ENNReal.ofReal (‖thetaPartial α.1 α.2
          (fun θ' => χ θ' • phaseTransform Real.sin (F x) θ') θ‖ ^ 2))) ^ (1 / 2 : ℝ) ≤
      ∑ l ∈ Finset.range (α.1 + α.2 + 1), ∑ w : DerivativeWord2 (α.1 + α.2 - l),
        ENNReal.ofReal (((α.1 + α.2).choose l : ℝ) * ‖iteratedFDeriv ℝ l χ θ‖) *
          Pair c (fun x y => wordMonomial w y • F x y) θ := by
  set a := α.1 + α.2 with ha
  set κ : ℕ → ℝ := fun l => (a.choose l : ℝ) * ‖iteratedFDeriv ℝ l χ θ‖ with hκ
  have hκ0 : ∀ l, 0 ≤ κ l := fun l => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  set p : ℕ → ι → ℝ≥0∞ := fun l x => ∑ w : DerivativeWord2 (a - l),
    ENNReal.ofReal (κ l) * ENNReal.ofReal
      ‖phaseTransform (iteratedDeriv (a - l) Real.cos) (fun y => wordMonomial w y • F x y) θ‖ with hp
  set q : ℕ → ι → ℝ≥0∞ := fun l x => ∑ w : DerivativeWord2 (a - l),
    ENNReal.ofReal (κ l) * ENNReal.ofReal
      ‖phaseTransform (iteratedDeriv (a - l) Real.sin) (fun y => wordMonomial w y • F x y) θ‖ with hq
  have hcomp : ∀ (ψ : ℝ → ℝ), IsUnitPhase ψ → ∀ x,
      ENNReal.ofReal ‖thetaPartial α.1 α.2 (fun θ' => χ θ' • phaseTransform ψ (F x) θ') θ‖ ≤
        ∑ l ∈ Finset.range (a + 1), ∑ w : DerivativeWord2 (a - l),
          ENNReal.ofReal (κ l) * ENNReal.ofReal
            ‖phaseTransform (iteratedDeriv (a - l) ψ) (fun y => wordMonomial w y • F x y) θ‖ := by
    intro ψ hψ x
    refine (ENNReal.ofReal_le_ofReal (norm_thetaPartial_trans_le hχ hψ α (hF x) θ)).trans
      (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg fun l _ => Finset.sum_nonneg fun w _ =>
      mul_nonneg (hκ0 l) (norm_nonneg _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun w _ => mul_nonneg (hκ0 l) (norm_nonneg _)]
    exact Finset.sum_congr rfl fun w _ => ENNReal.ofReal_mul (hκ0 l)
  have h1 : (∑ x, c x * (ENNReal.ofReal (‖thetaPartial α.1 α.2
        (fun θ' => χ θ' • phaseTransform Real.cos (F x) θ') θ‖ ^ 2) +
      ENNReal.ofReal (‖thetaPartial α.1 α.2
        (fun θ' => χ θ' • phaseTransform Real.sin (F x) θ') θ‖ ^ 2))) ^ (1 / 2 : ℝ) ≤
      (∑ x, c x * ((∑ l ∈ Finset.range (a + 1), p l x) ^ 2 +
        (∑ l ∈ Finset.range (a + 1), q l x) ^ 2)) ^ (1 / 2 : ℝ) := by
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl ?_)
      (by norm_num)
    rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
    exact add_le_add (pow_le_pow_left₀ (by positivity) (hcomp _ isUnitPhase_cos x) 2)
      (pow_le_pow_left₀ (by positivity) (hcomp _ isUnitPhase_sin x) 2)
  refine h1.trans ((weighted_sum_minkowski (Finset.range (a + 1)) c p q).trans ?_)
  refine Finset.sum_le_sum fun l _ => ?_
  refine (weighted_sum_minkowski (Finset.univ : Finset (DerivativeWord2 (a - l))) c
    (fun w x => ENNReal.ofReal (κ l) * ENNReal.ofReal
      ‖phaseTransform (iteratedDeriv (a - l) Real.cos) (fun y => wordMonomial w y • F x y) θ‖)
    (fun w x => ENNReal.ofReal (κ l) * ENNReal.ofReal
      ‖phaseTransform (iteratedDeriv (a - l) Real.sin) (fun y => wordMonomial w y • F x y) θ‖)).trans
    (le_of_eq ?_)
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold Pair
  have he : ∀ x, c x * ((ENNReal.ofReal (κ l) * ENNReal.ofReal
        ‖phaseTransform (iteratedDeriv (a - l) Real.cos) (fun y => wordMonomial w y • F x y) θ‖) ^ 2 +
      (ENNReal.ofReal (κ l) * ENNReal.ofReal
        ‖phaseTransform (iteratedDeriv (a - l) Real.sin) (fun y => wordMonomial w y • F x y) θ‖) ^ 2) =
      ENNReal.ofReal (κ l) ^ 2 * (c x *
        (ENNReal.ofReal (‖phaseTransform Real.cos (fun y => wordMonomial w y • F x y) θ‖ ^ 2) +
          ENNReal.ofReal (‖phaseTransform Real.sin (fun y => wordMonomial w y • F x y) θ‖ ^ 2))) := by
    intro x
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← Trans_pair_iteratedDeriv (fun y => wordMonomial w y • F x y) θ (a - l),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _)]
    ring
  simp only [he, ← Finset.mul_sum]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half']

/-- **The amplitude jet norm of a cut-off transform** by the pair sizes of the moment families. -/
theorem amplitudeJetNorm_trans_le (π : ι → ℝ) (n : ℕ) {ϖ B : ℝ} (hϖ : 0 ≤ ϖ) (hB : 0 ≤ B)
    {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχb : ∀ l ≤ n, ∀ θ, ϖ ^ l * ‖iteratedFDeriv ℝ l χ θ‖ ≤ B)
    {F : ∀ x, Vec 2 → h x} (hF : ∀ x, HasIntegrableMoments n (F x)) (θ : Vec 2) :
    amplitudeJetNorm π n ϖ (fun x θ' => χ θ' • phaseTransform Real.cos (F x) θ')
        (fun x θ' => χ θ' • phaseTransform Real.sin (F x) θ') θ ≤
      ENNReal.ofReal (((momentIndices n).card : ℝ) * (2 ^ n * B)) *
        ∑ j ∈ Finset.range (n + 1), ∑ w : DerivativeWord2 j,
          Pair (fun x => ENNReal.ofReal ((π x)⁻¹))
            (fun x y => (ϖ ^ j * wordMonomial w y) • F x y) θ := by
  set c : ι → ℝ≥0∞ := fun x => ENNReal.ofReal ((π x)⁻¹) with hc
  set g : ℕ → ℝ≥0∞ := fun j => ∑ w : DerivativeWord2 j,
    Pair c (fun x y => (ϖ ^ j * wordMonomial w y) • F x y) θ with hg
  set S : ℝ≥0∞ := ∑ j ∈ Finset.range (n + 1), g j with hS
  have hterm : ∀ β ∈ momentIndices n,
      ENNReal.ofReal (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
        (∑ x, c x * (ENNReal.ofReal (‖thetaPartial β.1 β.2
            (fun θ' => χ θ' • phaseTransform Real.cos (F x) θ') θ‖ ^ 2) +
          ENNReal.ofReal (‖thetaPartial β.1 β.2
            (fun θ' => χ θ' • phaseTransform Real.sin (F x) θ') θ‖ ^ 2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (2 ^ n * B) * S := by
    intro β hβ
    have hβn : β.1 + β.2 ≤ n := (Finset.mem_filter.1 hβ).2
    set a := β.1 + β.2 with ha
    have hfac : (1 : ℝ) ≤ ((β.1.factorial * β.2.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    refine (mul_le_mul' le_rfl (pair_thetaPartial_trans_le c hχ β
      (fun x => (hF x).mono hβn) θ)).trans ?_
    rw [Finset.mul_sum]
    have h2 : ∀ l ∈ Finset.range (a + 1),
        ENNReal.ofReal (ϖ ^ a / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          ∑ w : DerivativeWord2 (a - l),
            ENNReal.ofReal ((a.choose l : ℝ) * ‖iteratedFDeriv ℝ l χ θ‖) *
              Pair c (fun x y => wordMonomial w y • F x y) θ ≤
          ENNReal.ofReal (2 ^ n * B) * g (a - l) := by
      intro l hl
      have hla : l ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      rw [hg, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun w _ => ?_
      have hmono : (fun x y => (ϖ ^ (a - l) * wordMonomial w y) • F x y) =
          fun x y => ϖ ^ (a - l) • (wordMonomial w y • F x y) := by
        funext x y
        rw [mul_smul]
      rw [hmono, Pair_const_smul c _ (pow_nonneg hϖ _), ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hch : (a.choose l : ℝ) ≤ 2 ^ n := by
        have h1 : (a.choose l : ℝ) ≤ 2 ^ a := by exact_mod_cast Nat.choose_le_two_pow a l
        exact h1.trans (pow_le_pow_right₀ (by norm_num) hβn)
      have hχl := hχb l (hla.trans hβn) θ
      have hpow : ϖ ^ a = ϖ ^ (a - l) * ϖ ^ l := (pow_sub_mul_pow ϖ hla).symm
      have hn0 : 0 ≤ ‖iteratedFDeriv ℝ l χ θ‖ := norm_nonneg _
      have hϖal : 0 ≤ ϖ ^ (a - l) := pow_nonneg hϖ _
      calc ϖ ^ a / ((β.1.factorial * β.2.factorial : ℕ) : ℝ) *
            ((a.choose l : ℝ) * ‖iteratedFDeriv ℝ l χ θ‖)
          ≤ ϖ ^ a * ((a.choose l : ℝ) * ‖iteratedFDeriv ℝ l χ θ‖) :=
            mul_le_mul_of_nonneg_right (div_le_self (pow_nonneg hϖ _) hfac)
              (mul_nonneg (Nat.cast_nonneg _) hn0)
        _ = (a.choose l : ℝ) * (ϖ ^ l * ‖iteratedFDeriv ℝ l χ θ‖) * ϖ ^ (a - l) := by
            rw [hpow]
            ring
        _ ≤ 2 ^ n * B * ϖ ^ (a - l) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hch hχl (mul_nonneg (pow_nonneg hϖ _) hn0) (by positivity)) hϖal
    refine (Finset.sum_le_sum h2).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul' le_rfl ?_
    have hrefl : ∑ l ∈ Finset.range (a + 1), g (a - l) = ∑ j ∈ Finset.range (a + 1), g j := by
      have := Finset.sum_range_reflect g (a + 1)
      simpa only [Nat.add_sub_cancel] using this
    rw [hrefl, hS]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hβn))
  unfold amplitudeJetNorm
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  congr 1
  rw [show (((momentIndices n).card : ℕ) : ℝ≥0∞) =
    ENNReal.ofReal (((momentIndices n).card : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

end Family

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # Gaussian Plancherel, negative input: the amplitude side

`SeamGaussianNegStatement` is reduced to one estimate on the frequency cube
(`FibreKeyStatement`): the Gaussian-weighted `L²` norm over the cube of the Bloch fibre norms of
the low pass `μ(D)G` is at most the negative jet norm of `G`.

The reduction is the amplitude side of `gaussianPlancherel`: the weighted jets of a band-limited
family by the integral of its amplitude jet norm (`weightedJetNorm_ampFun_le`), and the Gaussian
absorption on the cube (`ampJetIntegral_le_cube`), here with half of the Gaussian rate, the other
half being kept as a weight on the fibre norms. The output scale `r ≤ max 1 C_out · ϖ⁻¹` costs
`max(1, C_out)^M` (`weightedJetNorm_scale_le`). -/

section
open AVRegularity.CycleWords.Assembly

universe u v

/-- **The key estimate.** The Gaussian-weighted `L²` norm over the frequency cube of the
Bloch fibre norms of the low pass `μ(D)G` of an `L²` field is at most the negative jet norm of `G`
with weight `n + 2`, at every order `L`. The constant depends on the orders, the rate and the
cutoffs only. -/
def FibreKeyStatement : Prop :=
  ∀ (n L : ℕ) (c : ℝ), 0 < c →
  ∀ μ χlo : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ ξ, μ (-ξ) = μ ξ) →
    (∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0) →
    ContDiff ℝ (⊤ : ℕ∞) χlo → HasCompactSupport χlo →
  ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (η ϖ : ℝ), 0 < η → η ≤ 1 → 0 < ϖ → ϖ ≤ Real.sqrt η →
  ∀ G : ∀ x, Vec 2 → h x, (∀ x, MemLp (G x) 2 volume) →
    ∫⁻ θ in freqCube, (ENNReal.ofReal (Real.exp (-c * (vecDot θ θ / ϖ ^ 2))) *
        ∑ α ∈ momentIndices n,
          ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
            blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α
              (fun x => fourierCutoff μ (G x)) θ) ^ 2 ≤
      (ENNReal.ofReal C * negJetNorm π ((n + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ G) ^ 2

section Scale

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]

/-- The weighted jet norm at a smaller output scale: `r ≤ K r'` with `K ≥ 1` costs `K^j`. -/
theorem weightedJetNorm_scale_le (π : ι → ℝ) (p : ℝ) (j : ℕ) (s : ℝ) {r r' K : ℝ}
    (hr : 0 ≤ r) (hK : 1 ≤ K) (hrr : r ≤ K * r')
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) :
    weightedJetNorm π p j s r J ≤ ENNReal.ofReal (K ^ j) * weightedJetNorm π p j s r' J := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hr' : 0 ≤ r' := by
    by_contra hneg
    have : K * r' < 0 := mul_neg_of_pos_of_neg (zero_lt_one.trans_le hK) (not_le.1 hneg)
    linarith
  unfold weightedJetNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  have haj : a ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hK0 j)]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hfac : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  rw [← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hfac.le
  calc r ^ a ≤ (K * r') ^ a := pow_le_pow_left₀ hr hrr a
    _ = K ^ a * r' ^ a := mul_pow _ _ _
    _ ≤ K ^ j * r' ^ a :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK haj) (pow_nonneg hr' a)

end Scale

/-- **Gaussian Plancherel from the key estimate** (the amplitude side of `gaussianPlancherel`). -/
theorem seamGaussianNeg_of_key (hkey : FibreKeyStatement.{u, v}) :
    SeamGaussianNegStatement.{u, v} := by
  intro m n p M L cGa Cout hcGa hCout μ χlo hμ hμc hμe hμs hχ hχc
  have hc2 : 0 < cGa / 2 := half_pos hcGa
  obtain ⟨Ck, hCk, hk⟩ := hkey n L (cGa / 2) hc2 μ χlo hμ hμc hμe hμs hχ hχc
  set Km : ℝ := max 1 Cout with hKm
  have hKm1 : 1 ≤ Km := le_max_left _ _
  have hKm0 : 0 < Km := zero_lt_one.trans_le hKm1
  set C : ℝ := Km ^ M * gaussJetConst m M * gaussConst (M + p) (cGa / 2) * Ck with hC
  have hC0 : 0 < C :=
    mul_pos (mul_pos (mul_pos (pow_pos hKm0 M) (gaussJetConst_pos m M))
      (gaussConst_pos _ hc2)) hCk
  refine ⟨C, hC0, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ η ϖ r ρ CGa hη hη1 hϖ hϖη hr hrle hCGa g A Bamp G hG hret hAB
    hvan hgauss
  set N := negJetNorm π ((n + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ G with hN
  let Φ : Vec 2 → ℝ≥0∞ := fun θ => ∑ α ∈ momentIndices n,
    ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
      blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α
        (fun x => fourierCutoff μ (G x)) θ
  let Φ' : Vec 2 → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal (Real.exp (-(cGa / 2) * (vecDot θ θ / ϖ ^ 2))) * Φ θ
  have hgauss' : ∀ θ ∈ freqCube, amplitudeJetNorm π m ϖ A Bamp θ ≤
      ENNReal.ofReal (CGa * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ p *
        Real.exp (-(cGa / 2) * (vecDot θ θ / ϖ ^ 2))) * Φ' θ := by
    intro θ hθ
    refine (hgauss θ hθ).trans (le_of_eq ?_)
    change _ = ENNReal.ofReal (CGa * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ p *
        Real.exp (-(cGa / 2) * (vecDot θ θ / ϖ ^ 2))) *
      (ENNReal.ofReal (Real.exp (-(cGa / 2) * (vecDot θ θ / ϖ ^ 2))) * Φ θ)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have he : Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2)) =
        Real.exp (-(cGa / 2) * (vecDot θ θ / ϖ ^ 2)) *
          Real.exp (-(cGa / 2) * (vecDot θ θ / ϖ ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have hint := ampJetIntegral_le_cube (M := M) π hϖ hc2 hCGa hvan Φ' hgauss'
  have hkey' : (∫⁻ θ in freqCube, Φ' θ ^ 2) ≤ (ENNReal.ofReal Ck * N) ^ 2 :=
    hk π hπ η ϖ hη hη1 hϖ hϖη G hG
  have hamp : ampJetIntegral π m M ϖ A Bamp ≤
      (ENNReal.ofReal (CGa * gaussConst (M + p) (cGa / 2)) * (ENNReal.ofReal Ck * N)) ^ 2 := by
    refine hint.trans ?_
    rw [mul_pow]
    exact mul_le_mul_right hkey' _
  have hroot := ENNReal.rpow_le_rpow hamp (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [sq_rpow_half] at hroot
  have hA (x : ι) : IsBandAmp |ρ| m (A x) := by
    refine ⟨(hAB x).1, fun θ hθ => ?_⟩
    exact ((hret x).1 θ (by simpa only [sq_abs] using hθ)).1
  have hBamp (x : ι) : IsBandAmp |ρ| m (Bamp x) := by
    refine ⟨(hAB x).2, fun θ hθ => ?_⟩
    exact ((hret x).1 θ (by simpa only [sq_abs] using hθ)).2
  have hg : g = fun x => ampFun |ρ| (A x) (Bamp x) := by
    funext x z
    simpa only [ampFun, sq_abs] using (hret x).2.2.2 z
  rw [hg]
  have hscale := weightedJetNorm_scale_le π (m : ℝ) M ϖ hr.le hKm1 hrle
    (fun x _ wd z => orderedDerivative wd (ampFun |ρ| (A x) (Bamp x)) z)
  refine hscale.trans ((mul_le_mul_right ((weightedJetNorm_ampFun_le π (abs_nonneg ρ) hϖ hA
    hBamp).trans (mul_le_mul_right hroot _)) _).trans (le_of_eq ?_))
  rw [ENNReal.ofReal_mul hC0.le, hC,
    ENNReal.ofReal_mul (mul_pos (mul_pos (pow_pos hKm0 M) (gaussJetConst_pos m M))
      (gaussConst_pos _ hc2)).le,
    ENNReal.ofReal_mul (mul_pos (pow_pos hKm0 M) (gaussJetConst_pos m M)).le,
    ENNReal.ofReal_mul (pow_pos hKm0 M).le, ENNReal.ofReal_mul hCGa]
  ring
end

/-! # Gaussian Plancherel, negative input: the key estimate from its three parts

`FibreKeyStatement` (the Gaussian-weighted cube integral of the Bloch fibre norms of the low
pass) is reduced to:

* `SeamLowPassMomentStatement` at weight `n + 2`: the low pass has `n + 2` moments, so it
  is integrable;
* `LowPassFibreStatement`: for an integrable low pass, the Bloch fibre at a frequency of the open
  cube is the plane wave whose amplitude is the transform (the cell modes `θ + 2πk`, `k ≠ 0`, miss
  the band `π/2`); this is where the low pass is used;
* `TransformBoundStatement`: the Gaussian-weighted `L²` norm of the amplitude jet norm of the
  cut-off transform is at most the negative jet norm of `G` (duality).

The boundary of the cube is a null set (`freqCube_ae_eq`). -/

section
open AVRegularity.CycleWords.Assembly

universe u v

/-- The open frequency cube `(-π, π)²`. -/
def OpenCube : Set (Vec 2) := {θ | ∀ i, |θ i| < Real.pi}

theorem OpenCube_eq_pi :
    OpenCube = Set.univ.pi fun _ : Fin 2 => Set.Ioo (-Real.pi) Real.pi := by
  ext θ
  constructor
  · intro h i _
    exact abs_lt.1 (h i)
  · intro h i
    exact abs_lt.2 (h i (Set.mem_univ i))

theorem isOpen_openCube : IsOpen OpenCube := by
  rw [OpenCube_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

/-- The boundary of the frequency cube is a null set. -/
theorem freqCube_ae_eq : (freqCube : Set (Vec 2)) =ᵐ[volume] OpenCube := by
  rw [freqCube_eq_pi, OpenCube_eq_pi]
  exact (Measure.pi_Ioo_ae_eq_pi_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ))).symm

/-- **The Bloch fibres of an integrable low pass** at the frequencies of the open cube are the
plane waves of its transform: the fibre derivative norm is the amplitude jet term of the cut-off
transform. -/
def LowPassFibreStatement : Prop :=
  ∀ μ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ ξ, μ (-ξ) = μ ξ) →
    (∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0) →
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (G : ∀ x, Vec 2 → h x), (∀ x, MemLp (G x) 2 volume) →
    (∀ x, Integrable (fourierCutoff μ (G x)) volume) →
  ∀ (χ : Vec 2 → ℝ) (α : ℕ × ℕ) (θ : Vec 2), θ ∈ OpenCube →
    blochFibreDerivNorm π χ α (fun x => fourierCutoff μ (G x)) θ ≤
      (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal (‖thetaPartial α.1 α.2
            (fun θ' => χ θ' • phaseTransform Real.cos (fourierCutoff μ (G x)) θ') θ‖ ^ 2) +
          ENNReal.ofReal (‖thetaPartial α.1 α.2
            (fun θ' => χ θ' • phaseTransform Real.sin (fourierCutoff μ (G x)) θ') θ‖ ^ 2))) ^
        (1 / 2 : ℝ)

/-- **The dual estimate on the transform.** If the low pass `F = μ(D)G` has `n + 2` moments, the
Gaussian-weighted `L²` norm over the cube of the amplitude jet norm of `χ_lo(θ/√η) F̂(θ)` is at
most the negative jet norm of `G` with weight `n + 2`, at every order `L`. -/
def TransformBoundStatement : Prop :=
  ∀ (n L : ℕ) (c : ℝ), 0 < c →
  ∀ μ χlo : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ ξ, μ (-ξ) = μ ξ) →
    (∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0) →
    ContDiff ℝ (⊤ : ℕ∞) χlo → HasCompactSupport χlo →
  ∃ C : ℝ, 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (η ϖ : ℝ), 0 < η → η ≤ 1 → 0 < ϖ → ϖ ≤ Real.sqrt η →
  ∀ G : ∀ x, Vec 2 → h x, (∀ x, MemLp (G x) 2 volume) →
    momentNorm π (n + 2) ϖ (fun x => fourierCutoff μ (G x)) < ⊤ →
    ∫⁻ θ in freqCube, (ENNReal.ofReal (Real.exp (-c * (vecDot θ θ / ϖ ^ 2))) *
        amplitudeJetNorm π n ϖ
          (fun x θ' => χlo ((Real.sqrt η)⁻¹ • θ') • phaseTransform Real.cos (fourierCutoff μ (G x)) θ')
          (fun x θ' => χlo ((Real.sqrt η)⁻¹ • θ') • phaseTransform Real.sin (fourierCutoff μ (G x)) θ')
          θ) ^ 2 ≤
      (ENNReal.ofReal C * negJetNorm π ((n + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ G) ^ 2

/-- **The key estimate from the moments, the fibre identification and the dual estimate.** -/
theorem fibreKey_of_parts (hmom : SeamLowPassMomentStatement.{u, v})
    (hfib : LowPassFibreStatement.{u, v}) (htr : TransformBoundStatement.{u, v}) :
    FibreKeyStatement.{u, v} := by
  intro n L c hc μ χlo hμ hμc hμe hμs hχ hχc
  obtain ⟨C, hC, hb⟩ := htr n L c hc μ χlo hμ hμc hμe hμs hχ hχc
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ η ϖ hη hη1 hϖ hϖη G hG
  by_cases hN : negJetNorm π ((n + 2 : ℕ) : ℝ) L ϖ ϖ⁻¹ G = ⊤
  · rw [hN, ENNReal.mul_top (by simpa using hC), ENNReal.top_pow two_ne_zero]
    exact le_top
  have hϖ1 : ϖ ≤ 1 := hϖη.trans (Real.sqrt_le_one.2 hη1)
  have hM := hmom (n + 2) L μ hμ hμc hμe hμs π hπ ϖ hϖ hϖ1 G hG (lt_top_iff_ne_top.2 hN)
  have hFm : ∀ x, AEStronglyMeasurable (fourierCutoff μ (G x)) volume := fun x =>
    (fourierCutoff_memLp_of_memLp μ (Real.pi / 2) hμs hμ (hG x)).aestronglyMeasurable
  have hFi : ∀ x, Integrable (fourierCutoff μ (G x)) volume := by
    intro x
    have h1 := integrable_bracket_of_momentNorm (n := n) hϖ hM (hπ x) (hFm x)
    refine h1.mono (hFm x) (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (jbracket_pos z).le n)]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_jbracket z))
  have hbound := hb π hπ η ϖ hη hη1 hϖ hϖη G hG hM
  rw [setLIntegral_congr freqCube_ae_eq] at hbound ⊢
  refine (setLIntegral_mono_ae' ?_ ?_).trans hbound
  · exact isOpen_openCube.measurableSet
  refine Filter.Eventually.of_forall fun θ hθ => ?_
  refine pow_le_pow_left₀ (by positivity) (mul_le_mul' le_rfl ?_) 2
  unfold amplitudeJetNorm
  refine Finset.sum_le_sum fun α _ => mul_le_mul' le_rfl ?_
  exact hfib μ hμ hμc hμe hμs π G hG hFi (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α θ hθ
end

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Filter Complex Homogenization
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The product kernel reproduces the low pass

* Real forms of the inversion and of the Poisson summation of `productKernel`
  (`K_integral_cos`, `K_integral_sin`, `K_lattice_cos`, `K_lattice_sin`).
* `K_conv_cutoffKernel`: `∫ K(b) k_μ(c - b) db = k_μ(c)` when `μ ν = μ` (inversion and Fubini).
* `smooth_fourierCutoff`: for a square-integrable `G`, the low pass `F = μ(D)G` satisfies
  `∫ K(w - y) F(y) dy = F(w)` at every point `w` (Fubini; the integrability on the product comes
  from `|k(c-b)| |G(w-c)| ≤ (k(c-b)² + |G(w-c)|²)/2`). -/

section RealForms

theorem re_exp_mul (b r : ℝ) : (Complex.exp (↑b * Complex.I) * (r : ℂ)).re = Real.cos b * r := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]

theorem im_exp_mul (b r : ℝ) : (Complex.exp (↑b * Complex.I) * (r : ℂ)).im = Real.sin b * r := by
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    Complex.exp_ofReal_mul_I_im]

theorem K_integrable_exp (θ : Vec 2) (a : ℝ) :
    Integrable (fun u => Complex.exp (↑(vecDot θ u + a) * Complex.I) * (productKernel u : ℂ)) := by
  refine (K_integrable.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) ?_ ?_
  · exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      ((by unfold vecDot; fun_prop : Continuous fun u : Vec 2 => vecDot θ u).add
        continuous_const)).mul continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun u => by rw [Complex.norm_exp_ofReal_mul_I]

theorem K_integral_exp_shift (θ : Vec 2) (a : ℝ) :
    ∫ u, Complex.exp (↑(vecDot θ u + a) * Complex.I) * (productKernel u : ℂ) =
      Complex.exp (↑a * Complex.I) * (productCutoff θ : ℂ) := by
  have he : ∀ u : Vec 2, Complex.exp (↑(vecDot θ u + a) * Complex.I) * (productKernel u : ℂ) =
      Complex.exp (↑a * Complex.I) * (Complex.exp (↑(vecDot θ u) * Complex.I) * (productKernel u : ℂ)) := by
    intro u
    rw [exp_add_two]
    ring
  simp only [he]
  rw [integral_const_mul, K_inversion]

/-- `∫ cos(θ·u + a) K(u) du = ν(θ) cos a`. -/
theorem K_integral_cos (θ : Vec 2) (a : ℝ) :
    ∫ u, Real.cos (vecDot θ u + a) * productKernel u = productCutoff θ * Real.cos a := by
  have h := congrArg Complex.re (K_integral_exp_shift θ a)
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _
    (K_integrable_exp θ a)] at h
  simp only [Complex.reCLM_apply, re_exp_mul] at h
  rw [h, mul_comm]

/-- `∫ sin(θ·u + a) K(u) du = ν(θ) sin a`. -/
theorem K_integral_sin (θ : Vec 2) (a : ℝ) :
    ∫ u, Real.sin (vecDot θ u + a) * productKernel u = productCutoff θ * Real.sin a := by
  have h := congrArg Complex.im (K_integral_exp_shift θ a)
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm _
    (K_integrable_exp θ a)] at h
  simp only [Complex.imCLM_apply, im_exp_mul] at h
  rw [h, mul_comm]

theorem vecDot_add (θ x y : Vec 2) : vecDot θ (x + y) = vecDot θ x + vecDot θ y := by
  simp only [vecDot_two, Pi.add_apply]
  ring

theorem vecDot_sub (θ x y : Vec 2) : vecDot θ (x - y) = vecDot θ x - vecDot θ y := by
  simp only [vecDot_two, Pi.sub_apply]
  ring

theorem vecDot_neg_left' (θ x : Vec 2) : vecDot (-θ) x = -vecDot θ x := by
  simp only [vecDot_two, Pi.neg_apply]
  ring

theorem K_lattice_exp_shift {θ : Vec 2} (hθ : ∀ i, |θ i| ≤ Real.pi) (x : Vec 2) (a : ℝ) :
    HasSum (fun k : Fin 2 → ℤ => Complex.exp (↑(vecDot θ (Shift x k) + a) * Complex.I) *
      (productKernel (Shift x k) : ℂ)) (Complex.exp (↑a * Complex.I) * (productCutoff θ : ℂ)) := by
  have he : (fun k : Fin 2 → ℤ => Complex.exp (↑(vecDot θ (Shift x k) + a) * Complex.I) *
      (productKernel (Shift x k) : ℂ)) = fun k => Complex.exp (↑a * Complex.I) *
        (Complex.exp (↑(vecDot θ (Shift x k)) * Complex.I) * (productKernel (Shift x k) : ℂ)) := by
    funext k
    rw [exp_add_two]
    ring
  rw [he]
  have hs := (K_poisson_summable θ x).hasSum
  rw [K_poisson hθ x] at hs
  exact hs.mul_left _

/-- `∑_k cos(θ·(x+k) + a) K(x+k) = ν(θ) cos a` on the closed cube. -/
theorem K_lattice_cos {θ : Vec 2} (hθ : ∀ i, |θ i| ≤ Real.pi) (x : Vec 2) (a : ℝ) :
    HasSum (fun k : Fin 2 → ℤ => Real.cos (vecDot θ (Shift x k) + a) * productKernel (Shift x k))
      (productCutoff θ * Real.cos a) := by
  have h := (Complex.reCLM.hasSum (K_lattice_exp_shift hθ x a))
  simp only [Complex.reCLM_apply, re_exp_mul] at h
  rwa [mul_comm (Real.cos a)] at h

/-- `∑_k sin(θ·(x+k) + a) K(x+k) = ν(θ) sin a` on the closed cube. -/
theorem K_lattice_sin {θ : Vec 2} (hθ : ∀ i, |θ i| ≤ Real.pi) (x : Vec 2) (a : ℝ) :
    HasSum (fun k : Fin 2 → ℤ => Real.sin (vecDot θ (Shift x k) + a) * productKernel (Shift x k))
      (productCutoff θ * Real.sin a) := by
  have h := (Complex.imCLM.hasSum (K_lattice_exp_shift hθ x a))
  simp only [Complex.imCLM_apply, im_exp_mul] at h
  rwa [mul_comm (Real.sin a)] at h

end RealForms

section Cutoff

theorem Nu_eq_one {θ : Vec 2} (hθ : Real.sqrt (vecDot θ θ) < Real.pi / 2) : productCutoff θ = 1 := by
  have hi : ∀ i, |θ i| ≤ Real.pi / 2 := by
    intro i
    have hs : θ i ^ 2 ≤ vecDot θ θ := by
      rw [vecDot_two]
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (θ 0), sq_nonneg (θ 1)]
    have h1 : |θ i| ≤ Real.sqrt (vecDot θ θ) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hs
    linarith
  rw [productCutoff, Bump1_one (hi 0), Bump1_one (hi 1), mul_one]

/-- `μ ν = μ` for a cutoff vanishing outside the ball of radius `π/2`. -/
theorem mul_nu {μ : Vec 2 → ℝ} (hμs : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (θ : Vec 2) : μ θ * productCutoff θ = μ θ := by
  by_cases h : Real.sqrt (vecDot θ θ) < Real.pi / 2
  · rw [Nu_eq_one h, mul_one]
  · rw [hμs θ (not_lt.1 h), zero_mul]

/-- **The product kernel reproduces the cutoff kernel.** -/
theorem K_conv_cutoffKernel {μ : Vec 2 → ℝ} (hμc : Continuous μ) (hμi : Integrable μ)
    (hμν : ∀ θ, μ θ * productCutoff θ = μ θ) (c : Vec 2) :
    ∫ b, productKernel b * cutoffKernel μ (c - b) = cutoffKernel μ c := by
  set f : Vec 2 → Vec 2 → ℝ := fun b θ => productKernel b * (μ θ * Real.cos (vecDot θ (c - b))) with hfd
  have hcont : Continuous (Function.uncurry f) := by
    simp only [hfd]
    refine (K_continuous.comp continuous_fst).mul ((hμc.comp continuous_snd).mul
      (Real.continuous_cos.comp ?_))
    simp only [vecDot_two, Pi.sub_apply]
    fun_prop
  have hint : Integrable (Function.uncurry f) (volume.prod volume) := by
    refine (K_integrable.mul_prod hμi).norm.mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    simp only [hfd, Function.uncurry, norm_mul, Real.norm_eq_abs]
    have hc1 := Real.abs_cos_le_one (vecDot q.2 (c - q.1))
    have h1 := abs_nonneg (productKernel q.1)
    have h2 := abs_nonneg (μ q.2)
    calc |productKernel q.1| * (|μ q.2| * |Real.cos (vecDot q.2 (c - q.1))|)
        ≤ |productKernel q.1| * (|μ q.2| * 1) := by gcongr
      _ = |productKernel q.1| * |μ q.2| := by rw [mul_one]
  have hin : ∀ θ : Vec 2, ∫ b, productKernel b * Real.cos (vecDot θ (c - b)) = productCutoff θ * Real.cos (vecDot θ c) := by
    intro θ
    have he : ∀ b : Vec 2, productKernel b * Real.cos (vecDot θ (c - b)) =
        Real.cos (vecDot (-θ) b + vecDot θ c) * productKernel b := by
      intro b
      rw [vecDot_sub, vecDot_neg_left', mul_comm]
      congr 2
      ring
    simp only [he]
    rw [K_integral_cos, Nu_neg]
  unfold cutoffKernel
  calc ∫ b, productKernel b * ((2 * Real.pi)⁻¹ ^ 2 * ∫ θ, μ θ * Real.cos (vecDot θ (c - b)))
      = ∫ b, (2 * Real.pi)⁻¹ ^ 2 * ∫ θ, f b θ := by
        refine integral_congr_ae (Eventually.of_forall fun b => ?_)
        simp only [hfd]
        rw [integral_const_mul]
        ring
    _ = (2 * Real.pi)⁻¹ ^ 2 * ∫ b, ∫ θ, f b θ := integral_const_mul _ _
    _ = (2 * Real.pi)⁻¹ ^ 2 * ∫ θ, ∫ b, f b θ := by rw [integral_integral_swap hint]
    _ = (2 * Real.pi)⁻¹ ^ 2 * ∫ θ, μ θ * Real.cos (vecDot θ c) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
        simp only [hfd]
        have he : (fun b => productKernel b * (μ θ * Real.cos (vecDot θ (c - b)))) =
            fun b => μ θ * (productKernel b * Real.cos (vecDot θ (c - b))) := by
          funext b
          ring
        rw [he, integral_const_mul, hin θ, ← mul_assoc, hμν θ]

end Cutoff

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Filter Complex Homogenization AVRegularity.Sobolev
open scoped ENNReal Topology
namespace AVRegularity.CycleWords.Seam

/-! # The Bloch fibres of an integrable low pass

`lowPassFibre : LowPassFibreStatement`.

For `F = μ(D)G` (`G ∈ L²`, `μ = 0` outside the ball `π/2`), the product kernel `K` of the cutoff
`ν = ν₁ ⊗ ν₁` (`ν = 1` on the support of `μ`) reproduces `F` at every point
(`smooth_fourierCutoff`). For an integrable `F` with `F = K ⋆ F`:

* `blochCos θ F z = ν(θ) F̂_cos(θ)` for every `z` and every `θ` of the closed cube (Poisson for `K`,
  and the exchange of the lattice sum with the integral, `blochCos_smooth`);
* `F̂_cos(θ) = ν(θ) F̂_cos(θ)` (inversion for `K` and Fubini, `trans_smooth`);

so the Bloch fibre is the plane wave of the transform on the open cube, its `θ`-derivatives are
those of the transform there, and the fibre norm, an integral over the unit cell of a constant,
is the amplitude term (an equality). -/

open AVRegularity.CycleWords.Assembly

universe u v

section Reproduce

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The product kernel reproduces the low pass** at every point. -/
theorem smooth_fourierCutoff {μ : Vec 2 → ℝ} (hμ : ContDiff ℝ (⊤ : ℕ∞) μ)
    (hμc : HasCompactSupport μ) (hμs : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    {G : Vec 2 → E} (hG : MemLp G 2 volume) (w : Vec 2) :
    ∫ y, productKernel (w - y) • fourierCutoff μ G y = fourierCutoff μ G w := by
  set k := cutoffKernel μ with hkd
  have hks : (seamRealCutoffSchwartz μ (Real.pi / 2) hμs hμ : Vec 2 → ℝ) = k :=
    seamRealCutoffSchwartz_eq _ _ _ _
  have hkc : Continuous k := hks ▸ (seamRealCutoffSchwartz μ _ hμs hμ).continuous
  have hk2 : MemLp k 2 volume := hks ▸ (seamRealCutoffSchwartz μ _ hμs hμ).memLp 2
  have hμi : Integrable μ := hμ.continuous.integrable_of_hasCompactSupport hμc
  have hKk : ∀ c, ∫ b, productKernel b * k (c - b) = k c :=
    K_conv_cutoffKernel hμ.continuous hμi (mul_nu hμs)
  have h1 : ∫ y, productKernel (w - y) • fourierCutoff μ G y = ∫ b, productKernel b • fourierCutoff μ G (w - b) := by
    have h := integral_sub_left_eq_self (fun y => productKernel (w - y) • fourierCutoff μ G y) volume w
    simp only [sub_sub_cancel] at h
    exact h.symm
  have h2 : ∀ b, fourierCutoff μ G (w - b) = ∫ c, k (c - b) • G (w - c) := by
    intro b
    have h := integral_sub_right_eq_self (μ := volume) (fun a => k a • G (w - b - a)) b
    simp only [show ∀ c : Vec 2, w - b - (c - b) = w - c from fun c => by abel] at h
    rw [h]
    rfl
  set Φ : Vec 2 × Vec 2 → E := fun q => (productKernel q.1 * k (q.2 - q.1)) • G (w - q.2) with hΦd
  have hGw : AEStronglyMeasurable (fun c => G (w - c)) volume :=
    hG.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume w)
  have hΦm : AEStronglyMeasurable Φ (volume.prod volume) :=
    ((K_continuous.comp continuous_fst).mul
      (hkc.comp (continuous_snd.sub continuous_fst))).aestronglyMeasurable.smul hGw.comp_snd
  have hk2' : Integrable (fun x => k x ^ 2) := hk2.integrable_sq
  have hG2' : Integrable (fun x => ‖G x‖ ^ 2) := by
    have h := hG.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  set M : ℝ := ((∫ x, k x ^ 2) + ∫ x, ‖G x‖ ^ 2) / 2 with hMd
  have hsec : ∀ b, Integrable (fun c => k (c - b) • G (w - c)) := by
    intro b
    have hkb : MemLp (fun c => k (c - b)) 2 volume :=
      hk2.comp_measurePreserving (measurePreserving_sub_right volume b)
    have hGb : MemLp (fun c => G (w - c)) 2 volume :=
      hG.comp_measurePreserving (Measure.measurePreserving_sub_left volume w)
    exact memLp_one_iff_integrable.1 (hkb.smul hGb)
  have hbound : ∀ b, ∫ c, ‖Φ (b, c)‖ ≤ |productKernel b| * M := by
    intro b
    have hpt : ∀ c, ‖Φ (b, c)‖ ≤ |productKernel b| * ((k (c - b) ^ 2 + ‖G (w - c)‖ ^ 2) / 2) := by
      intro c
      simp only [hΦd, norm_smul, norm_mul, Real.norm_eq_abs]
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      nlinarith [sq_nonneg (|k (c - b)| - ‖G (w - c)‖), sq_abs (k (c - b))]
    have hint : Integrable fun c => |productKernel b| * ((k (c - b) ^ 2 + ‖G (w - c)‖ ^ 2) / 2) :=
      (((hk2'.comp_sub_right b).add (hG2'.comp_sub_left w)).div_const 2).const_mul _
    refine (integral_mono_of_nonneg (Eventually.of_forall fun c => norm_nonneg _) hint
      (Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_div, integral_add (hk2'.comp_sub_right b)
      (hG2'.comp_sub_left w), integral_sub_right_eq_self (fun x => k x ^ 2),
      integral_sub_left_eq_self (fun x => ‖G x‖ ^ 2)]
  have hΦi : Integrable Φ (volume.prod volume) := by
    rw [integrable_prod_iff hΦm]
    refine ⟨Eventually.of_forall fun b => ?_, ?_⟩
    · refine ((hsec b).smul (productKernel b)).congr (Eventually.of_forall fun c => ?_)
      simp only [hΦd, Pi.smul_apply, smul_smul]
    · refine (K_integrable.norm.mul_const M).mono' hΦm.norm.integral_prod_right'
        (Eventually.of_forall fun b => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
        Real.norm_eq_abs]
      exact hbound b
  rw [h1]
  calc ∫ b, productKernel b • fourierCutoff μ G (w - b)
      = ∫ b, ∫ c, Φ (b, c) := by
        refine integral_congr_ae (Eventually.of_forall fun b => ?_)
        show productKernel b • fourierCutoff μ G (w - b) = ∫ c, Φ (b, c)
        rw [h2 b, ← integral_smul]
        refine integral_congr_ae (Eventually.of_forall fun c => ?_)
        simp only [hΦd, smul_smul]
    _ = ∫ c, ∫ b, Φ (b, c) := integral_integral_swap hΦi
    _ = ∫ c, k c • G (w - c) := by
        refine integral_congr_ae (Eventually.of_forall fun c => ?_)
        simp only [hΦd]
        rw [integral_smul_const, hKk c]
    _ = fourierCutoff μ G w := rfl

end Reproduce

section Fibre

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem Shift_sub (z y : Vec 2) (k : Fin 2 → ℤ) :
    (z + fun i => (k i : ℝ)) - y = Shift (z - y) k := by
  unfold Shift
  abel

theorem vecDot_shift (θ z y : Vec 2) (k : Fin 2 → ℤ) :
    vecDot θ (z + fun i => (k i : ℝ)) = vecDot θ (Shift (z - y) k) + vecDot θ y := by
  rw [← vecDot_add]
  congr 1
  unfold Shift
  abel

omit [CompleteSpace E] in
/-- The lattice sums of the kernel against an integrable function are finite. -/
theorem lattice_lintegral_ne_top {F : Vec 2 → E} (hF : Integrable F) (ψ : ℝ → ℝ)
    (hψ : ∀ t, |ψ t| ≤ 1) (θ z : Vec 2) :
    ∑' k : Fin 2 → ℤ, ∫⁻ y, ‖(ψ (vecDot θ (z + fun i => (k i : ℝ))) *
      productKernel ((z + fun i => (k i : ℝ)) - y)) • F y‖ₑ ≠ ⊤ := by
  have hpt : ∀ (k : Fin 2 → ℤ) y, ‖(ψ (vecDot θ (z + fun i => (k i : ℝ))) *
      productKernel ((z + fun i => (k i : ℝ)) - y)) • F y‖ₑ ≤
      ‖productKernel (Shift (z - y) k)‖ₑ * ‖F y‖ₑ := by
    intro k y
    rw [enorm_smul, enorm_mul, Shift_sub]
    refine mul_le_mul' ?_ le_rfl
    calc ‖ψ (vecDot θ (z + fun i => (k i : ℝ)))‖ₑ * ‖productKernel (Shift (z - y) k)‖ₑ
        ≤ 1 * ‖productKernel (Shift (z - y) k)‖ₑ := by
          refine mul_le_mul' ?_ le_rfl
          rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hψ _)
      _ = _ := one_mul _
  have hmeas : ∀ k : Fin 2 → ℤ, AEMeasurable (fun y => ‖productKernel (Shift (z - y) k)‖ₑ * ‖F y‖ₑ) := by
    intro k
    refine (Measurable.aemeasurable ?_).mul hF.aestronglyMeasurable.enorm
    refine (K_continuous.comp ?_).measurable.enorm
    unfold Shift
    fun_prop
  refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => lintegral_mono (hpt k)) ?_)
  rw [← lintegral_tsum hmeas]
  calc ∫⁻ y, ∑' k : Fin 2 → ℤ, ‖productKernel (Shift (z - y) k)‖ₑ * ‖F y‖ₑ
      ≤ ∫⁻ y, kernelLatticeConst * kernelLatticeConst * ‖F y‖ₑ := lintegral_mono fun y => by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_mul' (K_lattice_le (z - y)) le_rfl
    _ = kernelLatticeConst * kernelLatticeConst * ∫⁻ y, ‖F y‖ₑ := lintegral_const_mul'' _ hF.aestronglyMeasurable.enorm
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top S1_lt_top S1_lt_top) hF.2

omit [CompleteSpace E] in
theorem lattice_meas {F : Vec 2 → E} (hF : Integrable F) (ψ : ℝ → ℝ) (θ z : Vec 2)
    (k : Fin 2 → ℤ) :
    AEStronglyMeasurable (fun y => (ψ (vecDot θ (z + fun i => (k i : ℝ))) *
      productKernel ((z + fun i => (k i : ℝ)) - y)) • F y) volume :=
  ((continuous_const.mul (K_continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable).smul
    hF.aestronglyMeasurable

omit [CompleteSpace E] in
/-- **The Bloch cosine sum of a reproduced integrable function.** -/
theorem blochCos_smooth {F : Vec 2 → E} (hF : Integrable F)
    (hrep : ∀ w, ∫ y, productKernel (w - y) • F y = F w) {θ : Vec 2} (hθ : ∀ i, |θ i| ≤ Real.pi)
    (z : Vec 2) : blochCos θ F z = productCutoff θ • phaseTransform Real.cos F θ := by
  unfold blochCos phaseTransform
  have h1 : ∀ k : Fin 2 → ℤ, Real.cos (vecDot θ (z + fun i => (k i : ℝ))) •
      F (z + fun i => (k i : ℝ)) = ∫ y, (Real.cos (vecDot θ (z + fun i => (k i : ℝ))) *
        productKernel ((z + fun i => (k i : ℝ)) - y)) • F y := by
    intro k
    rw [← hrep (z + fun i => (k i : ℝ)), ← integral_smul]
    simp only [smul_smul]
  simp only [h1]
  rw [← integral_tsum (lattice_meas hF Real.cos θ z)
    (lattice_lintegral_ne_top hF Real.cos Real.abs_cos_le_one θ z),
    ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hs := K_lattice_cos hθ (z - y) (vecDot θ y)
  simp only [Shift_sub, vecDot_shift θ z y]
  rw [hs.summable.tsum_smul_const, hs.tsum_eq, smul_smul]

omit [CompleteSpace E] in
/-- **The Bloch sine sum of a reproduced integrable function.** -/
theorem blochSin_smooth {F : Vec 2 → E} (hF : Integrable F)
    (hrep : ∀ w, ∫ y, productKernel (w - y) • F y = F w) {θ : Vec 2} (hθ : ∀ i, |θ i| ≤ Real.pi)
    (z : Vec 2) : blochSin θ F z = productCutoff θ • phaseTransform Real.sin F θ := by
  unfold blochSin phaseTransform
  have h1 : ∀ k : Fin 2 → ℤ, Real.sin (vecDot θ (z + fun i => (k i : ℝ))) •
      F (z + fun i => (k i : ℝ)) = ∫ y, (Real.sin (vecDot θ (z + fun i => (k i : ℝ))) *
        productKernel ((z + fun i => (k i : ℝ)) - y)) • F y := by
    intro k
    rw [← hrep (z + fun i => (k i : ℝ)), ← integral_smul]
    simp only [smul_smul]
  simp only [h1]
  rw [← integral_tsum (lattice_meas hF Real.sin θ z)
    (lattice_lintegral_ne_top hF Real.sin Real.abs_sin_le_one θ z),
    ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hs := K_lattice_sin hθ (z - y) (vecDot θ y)
  simp only [Shift_sub, vecDot_shift θ z y]
  rw [hs.summable.tsum_smul_const, hs.tsum_eq, smul_smul]

/-- **The transform of a reproduced integrable function** is cut off by `ν`. -/
theorem trans_smooth {F : Vec 2 → E} (hF : Integrable F)
    (hrep : ∀ w, ∫ y, productKernel (w - y) • F y = F w) (ψ : ℝ → ℝ) (hψ : ∀ t, |ψ t| ≤ 1)
    (hψc : Continuous ψ) (hψK : ∀ (θ : Vec 2) (a : ℝ), ∫ u, ψ (vecDot θ u + a) * productKernel u = productCutoff θ * ψ a)
    (θ : Vec 2) : phaseTransform ψ F θ = productCutoff θ • phaseTransform ψ F θ := by
  set Φ : Vec 2 × Vec 2 → E := fun q => (ψ (vecDot θ q.1) * productKernel (q.1 - q.2)) • F q.2 with hΦd
  have hdot : Continuous fun u : Vec 2 => vecDot θ u := by
    simp only [vecDot_two]
    fun_prop
  have hΦm : AEStronglyMeasurable Φ (volume.prod volume) :=
    (((hψc.comp (hdot.comp continuous_fst)).mul
      (K_continuous.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable).smul
      hF.aestronglyMeasurable.comp_snd
  have hsec : ∀ y, Integrable fun w => Φ (w, y) := by
    intro y
    refine ((K_integrable.comp_sub_right y).bdd_mul (c := 1)
      (hψc.comp hdot).aestronglyMeasurable (Eventually.of_forall fun w => ?_)).smul_const (F y)
    rw [Real.norm_eq_abs]
    exact hψ _
  have hΦi : Integrable Φ (volume.prod volume) := by
    rw [integrable_prod_iff' hΦm]
    refine ⟨Eventually.of_forall hsec, ?_⟩
    refine (hF.norm.const_mul (∫ u, ‖productKernel u‖)).mono' (AEStronglyMeasurable.integral_prod_right'
      (AEStronglyMeasurable.prod_swap hΦm.norm)) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ w, ‖Φ (w, y)‖ ≤ ∫ w, ‖productKernel (w - y)‖ * ‖F y‖ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun w => norm_nonneg _)
            ((K_integrable.comp_sub_right y).norm.mul_const _) (Eventually.of_forall fun w => ?_)
          simp only [hΦd, norm_smul, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) (hψ _))
            (norm_nonneg _)
      _ = (∫ u, ‖productKernel u‖) * ‖F y‖ := by
          rw [integral_mul_const, integral_sub_right_eq_self (fun u => ‖productKernel u‖)]
  have hin : ∀ y, ∫ w, ψ (vecDot θ w) * productKernel (w - y) = productCutoff θ * ψ (vecDot θ y) := by
    intro y
    have h := integral_add_right_eq_self (μ := volume) (fun w => ψ (vecDot θ w) * productKernel (w - y)) y
    simp only [add_sub_cancel_right, vecDot_add] at h
    rw [← h, hψK]
  unfold phaseTransform
  calc ∫ w, ψ (vecDot θ w) • F w
      = ∫ w, ∫ y, Φ (w, y) := by
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        show ψ (vecDot θ w) • F w = ∫ y, Φ (w, y)
        rw [← hrep w, ← integral_smul]
        simp only [hΦd, smul_smul]
    _ = ∫ y, ∫ w, Φ (w, y) := integral_integral_swap hΦi
    _ = ∫ y, (productCutoff θ * ψ (vecDot θ y)) • F y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hΦd]
        rw [integral_smul_const, hin y]
    _ = productCutoff θ • ∫ y, ψ (vecDot θ y) • F y := by
        rw [← integral_smul]
        simp only [smul_smul]

end Fibre

section Statement

theorem volume_unitCube' : volume AVenhance.unitCube = 1 := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- **The Bloch fibres of an integrable low pass** (`LowPassFibreStatement`). -/
theorem lowPassFibre : LowPassFibreStatement.{u, v} := by
  intro μ hμ hμc _ hμs ι _ h _ _ _ _ _ _ π G hG hFi χ α θ hθ
  have hcube : ∀ θ' ∈ OpenCube, ∀ i, |θ' i| ≤ Real.pi := fun θ' h' i => (h' i).le
  have hrep : ∀ x w, ∫ y, productKernel (w - y) • fourierCutoff μ (G x) y = fourierCutoff μ (G x) w :=
    fun x w => smooth_fourierCutoff hμ hμc hμs (hG x) w
  have hcos : ∀ x z, ∀ θ' ∈ OpenCube, blochCos θ' (fourierCutoff μ (G x)) z =
      phaseTransform Real.cos (fourierCutoff μ (G x)) θ' := by
    intro x z θ' h'
    rw [blochCos_smooth (hFi x) (hrep x) (hcube θ' h') z,
      ← trans_smooth (hFi x) (hrep x) Real.cos Real.abs_cos_le_one Real.continuous_cos
        K_integral_cos θ']
  have hsin : ∀ x z, ∀ θ' ∈ OpenCube, blochSin θ' (fourierCutoff μ (G x)) z =
      phaseTransform Real.sin (fourierCutoff μ (G x)) θ' := by
    intro x z θ' h'
    rw [blochSin_smooth (hFi x) (hrep x) (hcube θ' h') z,
      ← trans_smooth (hFi x) (hrep x) Real.sin Real.abs_sin_le_one Real.continuous_sin
        K_integral_sin θ']
  have hpc : ∀ x z, thetaPartial α.1 α.2
      (fun θ' => χ θ' • blochCos θ' (fourierCutoff μ (G x)) z) θ =
      thetaPartial α.1 α.2 (fun θ' => χ θ' • phaseTransform Real.cos (fourierCutoff μ (G x)) θ') θ := by
    intro x z
    have hev : (fun θ' => χ θ' • blochCos θ' (fourierCutoff μ (G x)) z) =ᶠ[𝓝 θ]
        fun θ' => χ θ' • phaseTransform Real.cos (fourierCutoff μ (G x)) θ' :=
      Filter.eventuallyEq_of_mem (isOpen_openCube.mem_nhds hθ) fun θ' h' => by
        simp only [hcos x z θ' h']
    unfold thetaPartial
    rw [(hev.iteratedFDeriv ℝ (α.1 + α.2)).eq_of_nhds]
  have hps : ∀ x z, thetaPartial α.1 α.2
      (fun θ' => χ θ' • blochSin θ' (fourierCutoff μ (G x)) z) θ =
      thetaPartial α.1 α.2 (fun θ' => χ θ' • phaseTransform Real.sin (fourierCutoff μ (G x)) θ') θ := by
    intro x z
    have hev : (fun θ' => χ θ' • blochSin θ' (fourierCutoff μ (G x)) z) =ᶠ[𝓝 θ]
        fun θ' => χ θ' • phaseTransform Real.sin (fourierCutoff μ (G x)) θ' :=
      Filter.eventuallyEq_of_mem (isOpen_openCube.mem_nhds hθ) fun θ' h' => by
        simp only [hsin x z θ' h']
    unfold thetaPartial
    rw [(hev.iteratedFDeriv ℝ (α.1 + α.2)).eq_of_nhds]
  unfold blochFibreDerivNorm
  simp only [hpc, hps]
  rw [setLIntegral_const, volume_unitCube', mul_one]

end Statement

end AVRegularity.CycleWords.Seam
end
