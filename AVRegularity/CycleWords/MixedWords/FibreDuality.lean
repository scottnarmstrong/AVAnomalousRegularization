-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.GaussianAbsorb
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public section
open MeasureTheory Homogenization Filter
open scoped ENNReal RealInnerProductSpace
namespace AVRegularity.CycleWords.Assembly

/-! # Parseval for finite lattice sums on the frequency cube

`∫_{[-π,π]²} cos(θ·m) dθ = (2π)² [m = 0]` for `m ∈ ℤ²` (`integral_cube_cos`), so for a finite set
of lattice points `∫_{[-π,π]²} ‖∑_k cos(θ·(z+k)) H_k‖² + ‖∑_k sin(θ·(z+k)) H_k‖² dθ =
(2π)² ∑_k ‖H_k‖²` (`lintegral_cube_parseval`): the cross terms are `cos(θ·(k-l))`. -/

theorem freqCube_eq_pi : freqCube = Set.univ.pi fun _ : Fin 2 => Set.Icc (-Real.pi) Real.pi := by
  ext θ
  constructor
  · intro h i _
    exact abs_le.1 (h i)
  · intro h i
    exact abs_le.2 (h i (Set.mem_univ i))

theorem integral_Icc_cos_int (m : ℤ) :
    ∫ t in Set.Icc (-Real.pi) Real.pi, Real.cos (m * t) = if m = 0 then 2 * Real.pi else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  split_ifs with hm
  · subst hm
    simp
    ring
  · have hc : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos,
      mul_neg, Real.sin_neg, Real.sin_int_mul_pi]
    simp

theorem integral_Icc_sin_int (m : ℤ) :
    ∫ t in Set.Icc (-Real.pi) Real.pi, Real.sin (m * t) = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  by_cases hm : m = 0
  · subst hm
    simp
  · have hc : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc, integral_sin,
      mul_neg, Real.cos_neg]
    simp

theorem volume_restrict_freqCube :
    (volume : Measure (Vec 2)).restrict freqCube =
      Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc (-Real.pi) Real.pi) := by
  rw [freqCube_eq_pi, volume_pi, Measure.restrict_pi_pi]

/-- **Orthogonality of the lattice characters** on the frequency cube. -/
theorem integral_cube_cos (m : Fin 2 → ℤ) :
    ∫ θ in freqCube, Real.cos (vecDot θ fun i => (m i : ℝ)) =
      if m = 0 then (2 * Real.pi) ^ 2 else 0 := by
  have hsplit : ∀ θ : Vec 2, Real.cos (vecDot θ fun i => (m i : ℝ)) =
      (∏ i : Fin 2, Real.cos ((m i : ℝ) * θ i)) - ∏ i : Fin 2, Real.sin ((m i : ℝ) * θ i) := by
    intro θ
    simp only [vecDot, Fin.sum_univ_two, Fin.prod_univ_two]
    rw [mul_comm (θ 0), mul_comm (θ 1), Real.cos_add]
  simp_rw [hsplit]
  rw [volume_restrict_freqCube]
  have hfin : IsFiniteMeasure (Measure.pi fun _ : Fin 2 =>
      (volume : Measure ℝ).restrict (Set.Icc (-Real.pi) Real.pi)) := inferInstance
  have hbound : ∀ g : Vec 2 → ℝ, Continuous g → (∀ θ, |g θ| ≤ 1) → Integrable g
      (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc (-Real.pi) Real.pi)) :=
    fun g hg hb => Integrable.of_bound hg.aestronglyMeasurable 1
      (Eventually.of_forall fun θ => by rw [Real.norm_eq_abs]; exact hb θ)
  rw [integral_sub (hbound _ (by fun_prop) fun θ => by
      rw [Fin.prod_univ_two, abs_mul]
      exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _)
        zero_le_one).trans (le_of_eq (one_mul 1)))
    (hbound _ (by fun_prop) fun θ => by
      rw [Fin.prod_univ_two, abs_mul]
      exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _) (abs_nonneg _)
        zero_le_one).trans (le_of_eq (one_mul 1))),
    integral_fintype_prod_eq_prod (fun i t => Real.cos ((m i : ℝ) * t)),
    integral_fintype_prod_eq_prod (fun i t => Real.sin ((m i : ℝ) * t))]
  simp only [integral_Icc_cos_int, integral_Icc_sin_int, Fin.prod_univ_two, mul_zero, sub_zero]
  by_cases h0 : m 0 = 0 <;> by_cases h1 : m 1 = 0
  · have hm : m = 0 := by
      funext i
      fin_cases i <;> simp [h0, h1]
    simp [hm]
    ring
  · have hm : m ≠ 0 := fun h => h1 (by rw [h]; rfl)
    simp [h0, h1, hm]
  · have hm : m ≠ 0 := fun h => h0 (by rw [h]; rfl)
    simp [h0, h1, hm]
  · have hm : m ≠ 0 := fun h => h0 (by rw [h]; rfl)
    simp [h0, h1, hm]

theorem vecDot_sub_lattice (θ z : Vec 2) (k l : Fin 2 → ℤ) :
    vecDot θ (z + fun i => (k i : ℝ)) - vecDot θ (z + fun i => (l i : ℝ)) =
      vecDot θ fun i => ((k - l) i : ℝ) := by
  simp only [vecDot, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Int.cast_sub]
  ring

theorem norm_sq_lattice_sum_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Finset (Fin 2 → ℤ)) (z θ : Vec 2) (H : (Fin 2 → ℤ) → E) :
    ‖∑ k ∈ K, Real.cos (vecDot θ (z + fun i => (k i : ℝ))) • H k‖ ^ 2 +
      ‖∑ k ∈ K, Real.sin (vecDot θ (z + fun i => (k i : ℝ))) • H k‖ ^ 2 =
    ∑ k ∈ K, ∑ l ∈ K, Real.cos (vecDot θ fun i => ((k - l) i : ℝ)) * ⟪H k, H l⟫ := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, sum_inner, sum_inner,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum, inner_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    ← vecDot_sub_lattice, Real.cos_sub]
  ring

/-- **Parseval for finite lattice sums** on the frequency cube. -/
theorem lintegral_cube_parseval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Finset (Fin 2 → ℤ)) (z : Vec 2) (H : (Fin 2 → ℤ) → E) :
    ∫⁻ θ in freqCube,
        (ENNReal.ofReal ‖∑ k ∈ K, Real.cos (vecDot θ (z + fun i => (k i : ℝ))) • H k‖ ^ 2 +
          ENNReal.ofReal ‖∑ k ∈ K, Real.sin (vecDot θ (z + fun i => (k i : ℝ))) • H k‖ ^ 2) =
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * ∑ k ∈ K, ENNReal.ofReal (‖H k‖ ^ 2) := by
  have hpt : ∀ θ : Vec 2,
      ENNReal.ofReal ‖∑ k ∈ K, Real.cos (vecDot θ (z + fun i => (k i : ℝ))) • H k‖ ^ 2 +
        ENNReal.ofReal ‖∑ k ∈ K, Real.sin (vecDot θ (z + fun i => (k i : ℝ))) • H k‖ ^ 2 =
      ENNReal.ofReal (∑ k ∈ K, ∑ l ∈ K,
        Real.cos (vecDot θ fun i => ((k - l) i : ℝ)) * ⟪H k, H l⟫) := by
    intro θ
    rw [← norm_sq_lattice_sum_eq, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
  simp_rw [hpt]
  have : IsFiniteMeasure (volume.restrict freqCube) := by
    rw [volume_restrict_freqCube]
    infer_instance
  have hint : ∀ k l : Fin 2 → ℤ, Integrable (fun θ : Vec 2 =>
      Real.cos (vecDot θ fun i => ((k - l) i : ℝ)) * ⟪H k, H l⟫)
      (volume.restrict freqCube) := fun k l =>
    Integrable.of_bound ((Real.continuous_cos.comp (by unfold vecDot; fun_prop)).mul
      continuous_const).aestronglyMeasurable |⟪H k, H l⟫|
      (Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
  have hsumint : Integrable (fun θ : Vec 2 => ∑ k ∈ K, ∑ l ∈ K,
      Real.cos (vecDot θ fun i => ((k - l) i : ℝ)) * ⟪H k, H l⟫) (volume.restrict freqCube) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l
  have hnn : 0 ≤ᵐ[volume.restrict freqCube] fun θ : Vec 2 => ∑ k ∈ K, ∑ l ∈ K,
      Real.cos (vecDot θ fun i => ((k - l) i : ℝ)) * ⟪H k, H l⟫ :=
    Eventually.of_forall fun θ => by
      show 0 ≤ ∑ k ∈ K, ∑ l ∈ K, Real.cos (vecDot θ fun i => ((k - l) i : ℝ)) * ⟪H k, H l⟫
      rw [← norm_sq_lattice_sum_eq K z θ H]
      positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hsumint hnn,
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  have hkl : ∀ k ∈ K, ∫ θ in freqCube, ∑ l ∈ K,
      Real.cos (vecDot θ fun i => ((k - l) i : ℝ)) * ⟪H k, H l⟫ =
      (2 * Real.pi) ^ 2 * ‖H k‖ ^ 2 := by
    intro k hk
    rw [integral_finsetSum _ fun l _ => hint k l]
    simp_rw [integral_mul_const, integral_cube_cos, sub_eq_zero]
    rw [Finset.sum_eq_single k (fun l _ hlk => by simp [Ne.symm hlk]) (fun h => absurd hk h)]
    simp
  rw [Finset.sum_congr rfl hkl, ← Finset.mul_sum, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
open MeasureTheory Homogenization Filter AVRegularity.Sobolev
open scoped ENNReal RealInnerProductSpace
namespace AVRegularity.CycleWords.Assembly

/-! # Derivatives of cut-off finite lattice sums

A multilinear map on `Vec 2` is bounded by the sum of its values on basis tuples
(`norm_le_sum_basis`). On a basis tuple `idx`, the `j`-th derivative of `θ ↦ ψ(θ·y) v` is
`ψ^{(j)}(θ·y) y^{idx} v` (`iteratedFDeriv_phase_smul_basis`), and the pair
`(cos^{(j)}, sin^{(j)})` is `(cos, sin)` up to a sign and a swap, so the squared pair norms of the
lattice sums do not change (`pair_norm_sq_iteratedDeriv`). With the Leibniz bound for the cutoff,
the squared pair of the `α`-derivatives of `χ ∑_k cos(θ·y_k) H_k`, `χ ∑_k sin(θ·y_k) H_k` is bounded
by the pairs of the lattice sums of `y^{idx} H` (`pair_thetaPartial_le`). -/

theorem vec_eq_sum_basis (v : Vec 2) : v = ∑ i, v i • basisVec i := by
  funext k
  simp [basisVec_apply]

section Basis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A multilinear map on `Vec 2` is bounded by its values on basis tuples. -/
theorem norm_le_sum_basis {j : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec 2) F) :
    ‖T‖ ≤ ∑ idx : Fin j → Fin 2, ‖T fun l => basisVec (idx l)‖ := by
  classical
  refine T.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : T v = ∑ r : Fin j → Fin 2, (∏ l, v l (r l)) • T fun l => basisVec (r l) := by
    conv_lhs => rw [show v = fun l => ∑ i, v l i • basisVec i from
      funext fun l => vec_eq_sum_basis (v l)]
    rw [T.map_sum (fun l i => v l i • basisVec i)]
    exact Finset.sum_congr rfl fun r _ => T.map_smul_univ (fun l => v l (r l)) _
  rw [hv, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => norm_le_pi_norm (v l) (r l)

/-- On a basis tuple, the derivatives of `θ ↦ ψ(θ·y) v`. -/
theorem iteratedFDeriv_phase_smul_basis {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : Vec 2)
    (v : F) {j : ℕ} (idx : Fin j → Fin 2) (θ : Vec 2) :
    iteratedFDeriv ℝ j (fun θ => ψ (vecDot θ y) • v) θ (fun l => basisVec (idx l)) =
      (iteratedDeriv j ψ (vecDot θ y) * wordMonomial idx y) • v := by
  have h1 : (fun θ => ψ (vecDot θ y) • v) =
      (ContinuousLinearMap.toSpanSingleton ℝ v) ∘ (ψ ∘ phaseCLM y) := by
    funext θ
    simp [ContinuousLinearMap.toSpanSingleton_apply, phaseCLM_apply]
  have hc : ContDiff ℝ (⊤ : ℕ∞) (ψ ∘ phaseCLM y) := hψ.comp (phaseCLM y).contDiff
  rw [h1, (ContinuousLinearMap.toSpanSingleton ℝ v).iteratedFDeriv_comp_left hc.contDiffAt
    (by exact_mod_cast le_top), ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, (phaseCLM y).iteratedFDeriv_comp_right hψ θ (by exact_mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, ContinuousLinearMap.toSpanSingleton_apply,
    phaseCLM_apply]
  congr 1
  rw [smul_eq_mul, mul_comm]
  congr 1
  unfold wordMonomial
  refine Finset.prod_congr rfl fun l _ => ?_
  exact phaseCLM_basisVec y (idx l)

end Basis

section Pair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared pair norm of the lattice sums is invariant under differentiating the phases. -/
theorem pair_norm_sq_iteratedDeriv {ι : Type*} (s : Finset ι) (t : ι → ℝ) (w : ι → E)
    (j : ℕ) :
    ‖∑ k ∈ s, iteratedDeriv j Real.cos (t k) • w k‖ ^ 2 +
        ‖∑ k ∈ s, iteratedDeriv j Real.sin (t k) • w k‖ ^ 2 =
      ‖∑ k ∈ s, Real.cos (t k) • w k‖ ^ 2 + ‖∑ k ∈ s, Real.sin (t k) • w k‖ ^ 2 := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' j
  · simp only [Real.iteratedDeriv_even_cos, Real.iteratedDeriv_even_sin, Pi.mul_apply,
      Pi.pow_apply, Pi.neg_apply, Pi.one_apply, mul_smul, ← Finset.smul_sum, norm_smul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul]
  · simp only [Real.iteratedDeriv_odd_cos, Real.iteratedDeriv_odd_sin, Pi.mul_apply,
      Pi.pow_apply, Pi.neg_apply, Pi.one_apply, mul_smul, ← Finset.smul_sum, norm_smul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul]
    ring

omit [InnerProductSpace ℝ E] in
theorem contDiff_phase_smul [NormedSpace ℝ E] {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (y : Vec 2) (v : E) : ContDiff ℝ (⊤ : ℕ∞) fun θ => ψ (vecDot θ y) • v := by
  have h : (fun θ => ψ (vecDot θ y) • v) = fun θ => (ψ ∘ phaseCLM y) θ • v :=
    funext fun θ => by simp [phaseCLM_apply]
  rw [h]
  exact (hψ.comp (phaseCLM y).contDiff).smul contDiff_const

/-- **Derivatives of a finite lattice sum**, bounded on basis tuples. -/
theorem norm_iteratedFDeriv_latticeSum_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (K : Finset (Fin 2 → ℤ)) (y : (Fin 2 → ℤ) → Vec 2) (H : (Fin 2 → ℤ) → E) (j : ℕ)
    (θ : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun θ => ∑ k ∈ K, ψ (vecDot θ (y k)) • H k) θ‖ ≤
      ∑ idx : Fin j → Fin 2,
        ‖∑ k ∈ K, iteratedDeriv j ψ (vecDot θ (y k)) • (wordMonomial idx (y k) • H k)‖ := by
  refine (norm_le_sum_basis _).trans (le_of_eq (Finset.sum_congr rfl fun idx _ => ?_))
  have hc : ∀ k ∈ K, ContDiffAt ℝ j (fun θ => ψ (vecDot θ (y k)) • H k) θ := fun k _ =>
    ((contDiff_phase_smul hψ (y k) (H k)).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [show (fun θ => ∑ k ∈ K, ψ (vecDot θ (y k)) • H k) =
    ∑ k ∈ K, fun θ => ψ (vecDot θ (y k)) • H k from (Finset.sum_fn _ _).symm,
    iteratedFDeriv_sum_apply hc, _root_.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_phase_smul_basis hψ (y k) (H k) idx θ, mul_smul]

/-- **Pair bound** for the `α`-derivatives of a cut-off finite lattice sum. -/
theorem pair_thetaPartial_le {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (K : Finset (Fin 2 → ℤ)) (y : (Fin 2 → ℤ) → Vec 2) (H : (Fin 2 → ℤ) → E) (α : ℕ × ℕ)
    (θ : Vec 2) :
    ‖thetaPartial α.1 α.2 (fun θ => χ θ • ∑ k ∈ K, Real.cos (vecDot θ (y k)) • H k) θ‖ ^ 2 +
        ‖thetaPartial α.1 α.2 (fun θ => χ θ • ∑ k ∈ K, Real.sin (vecDot θ (y k)) • H k) θ‖ ^ 2 ≤
      ((α.1 + α.2 + 1 : ℕ) * 2 ^ (α.1 + α.2) : ℝ) *
        ∑ l ∈ Finset.range (α.1 + α.2 + 1), ∑ idx : Fin (α.1 + α.2 - l) → Fin 2,
          (((α.1 + α.2).choose l : ℝ) * ‖iteratedFDeriv ℝ l χ θ‖) ^ 2 *
            (‖∑ k ∈ K, Real.cos (vecDot θ (y k)) • (wordMonomial idx (y k) • H k)‖ ^ 2 +
              ‖∑ k ∈ K, Real.sin (vecDot θ (y k)) • (wordMonomial idx (y k) • H k)‖ ^ 2) := by
  set n := α.1 + α.2 with hn
  -- the lattice sums are smooth
  have hsm : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      ContDiff ℝ (⊤ : ℕ∞) (fun θ => ∑ k ∈ K, ψ (vecDot θ (y k)) • H k) := fun ψ hψ =>
    ContDiff.sum fun k _ => contDiff_phase_smul hψ (y k) (H k)
  -- the per-term bound
  set c : ℕ → ℝ := fun l => ((n.choose l : ℝ) * ‖iteratedFDeriv ℝ l χ θ‖) with hc
  have hbound : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      ‖thetaPartial α.1 α.2 (fun θ => χ θ • ∑ k ∈ K, ψ (vecDot θ (y k)) • H k) θ‖ ≤
        ∑ l ∈ Finset.range (n + 1), ∑ idx : Fin (n - l) → Fin 2, c l *
          ‖∑ k ∈ K, iteratedDeriv (n - l) ψ (vecDot θ (y k)) •
            (wordMonomial idx (y k) • H k)‖ := by
    intro ψ hψ
    refine (norm_thetaPartial_le α.1 α.2 _ θ).trans ?_
    refine (norm_iteratedFDeriv_smul_le hχ (hsm ψ hψ) θ (by exact_mod_cast le_top)).trans ?_
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_latticeSum_le hψ K y H (n - l) θ) (by positivity)
  -- Cauchy–Schwarz over the derivative split and the basis tuples
  have hcs : ∀ X : ∀ l : ℕ, (Fin (n - l) → Fin 2) → ℝ,
      (∑ l ∈ Finset.range (n + 1), ∑ idx : Fin (n - l) → Fin 2, c l * X l idx) ^ 2 ≤
        ((n + 1 : ℕ) * 2 ^ n : ℝ) * ∑ l ∈ Finset.range (n + 1), ∑ idx : Fin (n - l) → Fin 2,
          c l ^ 2 * X l idx ^ 2 := by
    intro X
    calc (∑ l ∈ Finset.range (n + 1), ∑ idx : Fin (n - l) → Fin 2, c l * X l idx) ^ 2
        ≤ ((Finset.range (n + 1)).card : ℝ) * ∑ l ∈ Finset.range (n + 1),
            (∑ idx : Fin (n - l) → Fin 2, c l * X l idx) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ ((n + 1 : ℕ) : ℝ) * ∑ l ∈ Finset.range (n + 1),
            (2 ^ n : ℝ) * ∑ idx : Fin (n - l) → Fin 2, (c l * X l idx) ^ 2 := by
          rw [Finset.card_range]
          gcongr with l hl
          refine sq_sum_le_card_mul_sum_sq.trans ?_
          gcongr
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
          exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le n l)
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [mul_pow]
          ring
  set Xc : ∀ l : ℕ, (Fin (n - l) → Fin 2) → ℝ := fun l idx =>
    ‖∑ k ∈ K, iteratedDeriv (n - l) Real.cos (vecDot θ (y k)) • (wordMonomial idx (y k) • H k)‖
    with hXc
  set Xs : ∀ l : ℕ, (Fin (n - l) → Fin 2) → ℝ := fun l idx =>
    ‖∑ k ∈ K, iteratedDeriv (n - l) Real.sin (vecDot θ (y k)) • (wordMonomial idx (y k) • H k)‖
    with hXs
  have hc1 := (pow_le_pow_left₀ (norm_nonneg _) (hbound Real.cos Real.contDiff_cos) 2).trans
    (hcs Xc)
  have hs1 := (pow_le_pow_left₀ (norm_nonneg _) (hbound Real.sin Real.contDiff_sin) 2).trans
    (hcs Xs)
  refine (add_le_add hc1 hs1).trans (le_of_eq ?_)
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have hp := pair_norm_sq_iteratedDeriv K (fun k => vecDot θ (y k))
    (fun k => wordMonomial idx (y k) • H k) (n - l)
  rw [← mul_add, hXc, hXs]
  simp only at hp ⊢
  rw [hp]

end Pair

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Amplitude pairs rotated by a gauge

`amplitudeJetNorm ≤ (m+1) 2^m ampDerivNorm` (`amplitudeJetNorm_le_ampDerivNorm`). If on an open set
`A = Re E • A_c + Im E • A_s` and `B = Re E • A_s - Im E • A_c` for a `C^m` complex gauge `E`, the
Leibniz rule bounds the derivatives of `(A, B)` by those of `E` and of `(A_c, A_s)`
(`norm_iteratedFDeriv_rot_le`), and Minkowski over the family gives
`ampDerivNorm (A, B) ≤ 2 (m+1) G ampDerivNorm (A_c, A_s)` when `ϖ^l ‖D^l E‖ ≤ G` for `l ≤ m`
(`ampDerivNorm_rot_le`). -/

section Pointwise

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDerivWithin_re_le {U : Set (Vec 2)} {E : Vec 2 → ℂ} {m : ℕ}
    (hE : ContDiffOn ℝ m E U) (hU : IsOpen U) {θ : Vec 2} (hθ : θ ∈ U) {l : ℕ} (hl : l ≤ m)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ‖iteratedFDerivWithin ℝ l (fun θ' => L (E θ')) U θ‖ ≤ ‖iteratedFDeriv ℝ l E θ‖ := by
  have h := L.iteratedFDerivWithin_comp_left (hE θ hθ) hU.uniqueDiffOn hθ
    (i := l) (by exact_mod_cast hl)
  have hc : (fun θ' => L (E θ')) = L ∘ E := rfl
  rw [hc, h, ← iteratedFDerivWithin_of_isOpen l hU hθ]
  refine (L.norm_compContinuousMultilinearMap_le _).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) hL

/-- **Leibniz for a rotated pair**, one component. -/
theorem norm_iteratedFDeriv_rot_le {U : Set (Vec 2)} (hU : IsOpen U) {E : Vec 2 → ℂ} {m : ℕ}
    (hE : ContDiffOn ℝ m E U) {X Y Z : Vec 2 → F} (hX : ContDiff ℝ m X) (hY : ContDiff ℝ m Y)
    (s : ℝ) (hZ : ∀ θ ∈ U, Z θ = (E θ).re • X θ + s • ((E θ).im • Y θ)) {θ : Vec 2}
    (hθ : θ ∈ U) {k : ℕ} (hk : k ≤ m) (hs : |s| ≤ 1) :
    ‖iteratedFDeriv ℝ k Z θ‖ ≤ ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
      ‖iteratedFDeriv ℝ l E θ‖ * (‖iteratedFDeriv ℝ (k - l) X θ‖ +
        ‖iteratedFDeriv ℝ (k - l) Y θ‖) := by
  have hud := hU.uniqueDiffOn (𝕜 := ℝ)
  have hre : ContDiffOn ℝ m (fun θ' => (E θ').re) U :=
    Complex.reCLM.contDiff.comp_contDiffOn hE
  have him : ContDiffOn ℝ m (fun θ' => (E θ').im) U :=
    Complex.imCLM.contDiff.comp_contDiffOn hE
  have hsm : ContDiffOn ℝ m (fun θ' => s * (E θ').im) U := contDiffOn_const.mul him
  have hc1 : ContDiffOn ℝ m (fun θ' => (E θ').re • X θ') U := hre.smul hX.contDiffOn
  have hc2 : ContDiffOn ℝ m (fun θ' => (s * (E θ').im) • Y θ') U := hsm.smul hY.contDiffOn
  rw [← iteratedFDerivWithin_of_isOpen k hU hθ,
    iteratedFDerivWithin_congr (f := fun θ' => (E θ').re • X θ' + (s * (E θ').im) • Y θ')
      (fun θ' hθ' => by rw [hZ θ' hθ']; simp only [mul_smul]) hθ]
  rw [show (fun θ' => (E θ').re • X θ' + (s * (E θ').im) • Y θ') =
    (fun θ' => (E θ').re • X θ') + fun θ' => (s * (E θ').im) • Y θ' from rfl,
    iteratedFDerivWithin_add_apply (f := fun θ' => (E θ').re • X θ')
      (g := fun θ' => (s * (E θ').im) • Y θ')
      ((hc1.contDiffWithinAt hθ).of_le (by exact_mod_cast hk))
      ((hc2.contDiffWithinAt hθ).of_le (by exact_mod_cast hk)) hud hθ]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_iteratedFDerivWithin_smul_le hre hX.contDiffOn hud hθ
    (n := k) (by exact_mod_cast hk)
  have h2 := norm_iteratedFDerivWithin_smul_le hsm hY.contDiffOn hud hθ
    (n := k) (by exact_mod_cast hk)
  refine (add_le_add h1 h2).trans ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l hl => ?_
  have hlk : l ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  have hre' : ‖iteratedFDerivWithin ℝ l (fun θ' => (E θ').re) U θ‖ ≤
      ‖iteratedFDeriv ℝ l E θ‖ :=
    norm_iteratedFDerivWithin_re_le hE hU hθ (hlk.trans hk) Complex.reCLM Complex.reCLM_norm.le
  have him' : ‖iteratedFDerivWithin ℝ l (fun θ' => s * (E θ').im) U θ‖ ≤
      ‖iteratedFDeriv ℝ l E θ‖ := by
    refine norm_iteratedFDerivWithin_re_le hE hU hθ (hlk.trans hk) (s • Complex.imCLM) ?_
    refine (norm_smul_le s Complex.imCLM).trans ?_
    rw [Complex.imCLM_norm, mul_one, Real.norm_eq_abs]
    exact hs
  rw [iteratedFDerivWithin_of_isOpen (k - l) hU hθ,
    iteratedFDerivWithin_of_isOpen (k - l) hU hθ]
  have hc : (0 : ℝ) ≤ k.choose l := Nat.cast_nonneg _
  calc (k.choose l : ℝ) * ‖iteratedFDerivWithin ℝ l (fun θ' => (E θ').re) U θ‖ *
        ‖iteratedFDeriv ℝ (k - l) X θ‖ +
      (k.choose l : ℝ) * ‖iteratedFDerivWithin ℝ l (fun θ' => s * (E θ').im) U θ‖ *
        ‖iteratedFDeriv ℝ (k - l) Y θ‖
      ≤ (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l E θ‖ * ‖iteratedFDeriv ℝ (k - l) X θ‖ +
        (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l E θ‖ * ‖iteratedFDeriv ℝ (k - l) Y θ‖ := by
        gcongr
    _ = _ := by ring

end Pointwise

section Family

variable {ι : Type*} [Fintype ι]

/-- **Weighted Minkowski** for finite families. -/
theorem sqrt_weighted_sum_sq_le {κ : Type*} (s : Finset κ) (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x)
    (y : κ → ι → ℝ) :
    Real.sqrt (∑ x, w x * (∑ l ∈ s, y l x) ^ 2) ≤ ∑ l ∈ s, Real.sqrt (∑ x, w x * y l x ^ 2) := by
  set v : κ → PiLp 2 (fun _ : ι => ℝ) :=
    fun l => WithLp.toLp 2 (fun x => Real.sqrt (w x) * y l x) with hv
  have hvn : ∀ l, ‖v l‖ = Real.sqrt (∑ x, w x * y l x ^ 2) := fun l => by
    rw [PiLp.norm_eq_of_L2]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hv, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hw x)]
  have hsn : ‖∑ l ∈ s, v l‖ = Real.sqrt (∑ x, w x * (∑ l ∈ s, y l x) ^ 2) := by
    rw [PiLp.norm_eq_of_L2]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp only [hv, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, ← Finset.mul_sum, mul_pow,
      Real.sq_sqrt (hw x)]
  rw [← hsn]
  exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => hvn l))

variable {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The weighted pair norm of the `k`-th derivatives at `θ`. -/
noncomputable def derivPairNorm (π : ι → ℝ) (k : ℕ) (A B : ∀ x, Vec 2 → h x) (θ : Vec 2) : ℝ :=
  Real.sqrt (∑ x, (π x)⁻¹ *
    (‖iteratedFDeriv ℝ k (A x) θ‖ ^ 2 + ‖iteratedFDeriv ℝ k (B x) θ‖ ^ 2))

theorem derivPairNorm_nonneg (π : ι → ℝ) (k : ℕ) (A B : ∀ x, Vec 2 → h x) (θ : Vec 2) :
    0 ≤ derivPairNorm π k A B θ :=
  Real.sqrt_nonneg _

theorem ampDerivNorm_eq (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (m : ℕ) {ϖ : ℝ} (hϖ : 0 ≤ ϖ)
    (A B : ∀ x, Vec 2 → h x) (θ : Vec 2) :
    ampDerivNorm π m ϖ A B θ = ENNReal.ofReal (∑ k ∈ Finset.range (m + 1),
      ϖ ^ k / (k.factorial : ℝ) * derivPairNorm π k A B θ) := by
  have hw : ∀ k x, 0 ≤ (π x)⁻¹ *
      (‖iteratedFDeriv ℝ k (A x) θ‖ ^ 2 + ‖iteratedFDeriv ℝ k (B x) θ‖ ^ 2) := fun k x =>
    mul_nonneg (inv_nonneg.2 (hπ x).le) (by positivity)
  unfold ampDerivNorm
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ =>
    mul_nonneg (by positivity) (derivPairNorm_nonneg π k A B θ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), derivPairNorm, Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun x _ => hw k x) (by norm_num),
    ENNReal.ofReal_sum_of_nonneg fun x _ => hw k x]
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ x).le),
    ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **The rotated pair, one order.** -/
theorem derivPairNorm_rot_le {U : Set (Vec 2)} (hU : IsOpen U) {E : Vec 2 → ℂ} {m : ℕ}
    (hE : ContDiffOn ℝ m E U) (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {A B Ac As : ∀ x, Vec 2 → h x}
    (hAc : ∀ x, ContDiff ℝ m (Ac x)) (hAs : ∀ x, ContDiff ℝ m (As x))
    (hrot : ∀ θ ∈ U, ∀ x, A x θ = (E θ).re • Ac x θ + (E θ).im • As x θ ∧
      B x θ = (E θ).re • As x θ - (E θ).im • Ac x θ)
    {θ : Vec 2} (hθ : θ ∈ U) {k : ℕ} (hk : k ≤ m) :
    derivPairNorm π k A B θ ≤ 2 * ∑ l ∈ Finset.range (k + 1),
      (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l E θ‖ * derivPairNorm π (k - l) Ac As θ := by
  set w : ι → ℝ := fun x => (π x)⁻¹ with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => inv_nonneg.2 (hπ x).le
  set c : ℕ → ℝ := fun l => (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l E θ‖ with hc
  have hc0 : ∀ l, 0 ≤ c l := fun l => by positivity
  set pq : ℕ → ι → ℝ := fun l x => ‖iteratedFDeriv ℝ (k - l) (Ac x) θ‖ +
    ‖iteratedFDeriv ℝ (k - l) (As x) θ‖ with hpq
  have hA : ∀ x, ‖iteratedFDeriv ℝ k (A x) θ‖ ≤ ∑ l ∈ Finset.range (k + 1), c l * pq l x :=
    fun x => (norm_iteratedFDeriv_rot_le hU hE (hAc x) (hAs x) 1
      (fun θ' hθ' => by rw [(hrot θ' hθ' x).1, one_smul]) hθ hk (by norm_num)).trans
      (le_of_eq (Finset.sum_congr rfl fun l _ => by simp only [hc, hpq]))
  have hB : ∀ x, ‖iteratedFDeriv ℝ k (B x) θ‖ ≤ ∑ l ∈ Finset.range (k + 1), c l * pq l x :=
    fun x => (norm_iteratedFDeriv_rot_le hU hE (hAs x) (hAc x) (-1)
      (fun θ' hθ' => by rw [(hrot θ' hθ' x).2, neg_one_smul, sub_eq_add_neg]) hθ hk
      (by norm_num)).trans
      (le_of_eq (Finset.sum_congr rfl fun l _ => by simp only [hc, hpq, add_comm]))
  have hT0 : ∀ x, 0 ≤ ∑ l ∈ Finset.range (k + 1), c l * pq l x := fun x =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hc0 l) (by positivity)
  -- the pair at order `k` by twice the square of the majorant
  have h1 : derivPairNorm π k A B θ ≤ Real.sqrt 2 *
      Real.sqrt (∑ x, w x * (∑ l ∈ Finset.range (k + 1), c l * pq l x) ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num), Finset.mul_sum]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun x _ => ?_)
    have ha := pow_le_pow_left₀ (norm_nonneg _) (hA x) 2
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
    calc (π x)⁻¹ * (‖iteratedFDeriv ℝ k (A x) θ‖ ^ 2 + ‖iteratedFDeriv ℝ k (B x) θ‖ ^ 2)
        ≤ w x * ((∑ l ∈ Finset.range (k + 1), c l * pq l x) ^ 2 +
          (∑ l ∈ Finset.range (k + 1), c l * pq l x) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add ha hb) (hw0 x)
      _ = 2 * (w x * (∑ l ∈ Finset.range (k + 1), c l * pq l x) ^ 2) := by ring
  -- Minkowski over the derivative split
  have h2 := sqrt_weighted_sum_sq_le (Finset.range (k + 1)) w hw0 (fun l x => c l * pq l x)
  -- each term by the pair norm of `(A_c, A_s)`
  have h3 : ∀ l, Real.sqrt (∑ x, w x * (c l * pq l x) ^ 2) ≤
      Real.sqrt 2 * (c l * derivPairNorm π (k - l) Ac As θ) := by
    intro l
    have hle : ∑ x, w x * (c l * pq l x) ^ 2 ≤ c l ^ 2 * 2 * ∑ x, (π x)⁻¹ *
        (‖iteratedFDeriv ℝ (k - l) (Ac x) θ‖ ^ 2 + ‖iteratedFDeriv ℝ (k - l) (As x) θ‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have hpq2 : pq l x ^ 2 ≤ 2 * (‖iteratedFDeriv ℝ (k - l) (Ac x) θ‖ ^ 2 +
          ‖iteratedFDeriv ℝ (k - l) (As x) θ‖ ^ 2) := by
        simp only [hpq]
        nlinarith [sq_nonneg (‖iteratedFDeriv ℝ (k - l) (Ac x) θ‖ -
          ‖iteratedFDeriv ℝ (k - l) (As x) θ‖)]
      calc w x * (c l * pq l x) ^ 2 = c l ^ 2 * (w x * pq l x ^ 2) := by ring
        _ ≤ c l ^ 2 * (w x * (2 * (‖iteratedFDeriv ℝ (k - l) (Ac x) θ‖ ^ 2 +
            ‖iteratedFDeriv ℝ (k - l) (As x) θ‖ ^ 2))) := by gcongr; exact hw0 x
        _ = _ := by simp only [hw]; ring
    calc Real.sqrt (∑ x, w x * (c l * pq l x) ^ 2)
        ≤ Real.sqrt (c l ^ 2 * 2 * ∑ x, (π x)⁻¹ * (‖iteratedFDeriv ℝ (k - l) (Ac x) θ‖ ^ 2 +
            ‖iteratedFDeriv ℝ (k - l) (As x) θ‖ ^ 2)) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt 2 * (c l * derivPairNorm π (k - l) Ac As θ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hc0 l),
          derivPairNorm]
        ring
  calc derivPairNorm π k A B θ
      ≤ Real.sqrt 2 * Real.sqrt (∑ x, w x * (∑ l ∈ Finset.range (k + 1), c l * pq l x) ^ 2) := h1
    _ ≤ Real.sqrt 2 * ∑ l ∈ Finset.range (k + 1), Real.sqrt (∑ x, w x * (c l * pq l x) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * ∑ l ∈ Finset.range (k + 1),
          Real.sqrt 2 * (c l * derivPairNorm π (k - l) Ac As θ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => h3 l) (Real.sqrt_nonneg _)
    _ = 2 * ∑ l ∈ Finset.range (k + 1), c l * derivPairNorm π (k - l) Ac As θ := by
        rw [← Finset.mul_sum, ← mul_assoc, Real.mul_self_sqrt (by norm_num)]

theorem rot_term_le {ϖ g D : ℝ} (hϖ : 0 ≤ ϖ) (hg : 0 ≤ g) (hD : 0 ≤ D) {k l : ℕ} (hlk : l ≤ k) :
    ϖ ^ k / (k.factorial : ℝ) * ((k.choose l : ℝ) * g * D) ≤
      (ϖ ^ l * g) * (ϖ ^ (k - l) / ((k - l).factorial : ℝ) * D) := by
  have hpow : ϖ ^ k = ϖ ^ l * ϖ ^ (k - l) := by rw [← pow_add, Nat.add_sub_cancel' hlk]
  have hl : (1 : ℝ) ≤ l.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero l)
  have heq : ϖ ^ k / (k.factorial : ℝ) * ((k.choose l : ℝ) * g * D) =
      (ϖ ^ l * g) * (ϖ ^ (k - l) / ((k - l).factorial : ℝ) * D) / l.factorial := by
    rw [Nat.cast_choose ℝ hlk, hpow]
    field_simp
  rw [heq]
  exact div_le_self (by positivity) hl

/-- **The rotated family.** If `ϖ^l ‖D^l E(θ)‖ ≤ G` for `l ≤ m`, the normalized derivatives of the
rotated pair are at most `2 (m+1) G` times those of `(A_c, A_s)`. -/
theorem ampDerivNorm_rot_le {U : Set (Vec 2)} (hU : IsOpen U) {E : Vec 2 → ℂ} {m : ℕ}
    (hE : ContDiffOn ℝ m E U) (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {A B Ac As : ∀ x, Vec 2 → h x}
    (hAc : ∀ x, ContDiff ℝ m (Ac x)) (hAs : ∀ x, ContDiff ℝ m (As x))
    (hrot : ∀ θ ∈ U, ∀ x, A x θ = (E θ).re • Ac x θ + (E θ).im • As x θ ∧
      B x θ = (E θ).re • As x θ - (E θ).im • Ac x θ)
    {θ : Vec 2} (hθ : θ ∈ U) {ϖ G : ℝ} (hϖ : 0 ≤ ϖ)
    (hG : ∀ l ≤ m, ϖ ^ l * ‖iteratedFDeriv ℝ l E θ‖ ≤ G) :
    ampDerivNorm π m ϖ A B θ ≤
      ENNReal.ofReal (2 * ((m + 1 : ℕ) : ℝ) * G) * ampDerivNorm π m ϖ Ac As θ := by
  have hG0 : 0 ≤ G := (mul_nonneg (pow_nonneg hϖ 0)
    (norm_nonneg (iteratedFDeriv ℝ 0 E θ))).trans (hG 0 (Nat.zero_le _))
  rw [ampDerivNorm_eq π hπ m hϖ, ampDerivNorm_eq π hπ m hϖ, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set f : ℕ → ℝ := fun j => ϖ ^ j / (j.factorial : ℝ) * derivPairNorm π j Ac As θ with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => mul_nonneg (by positivity) (derivPairNorm_nonneg _ _ _ _ _)
  set T := ∑ j ∈ Finset.range (m + 1), f j with hT
  have hk : ∀ k ∈ Finset.range (m + 1),
      ϖ ^ k / (k.factorial : ℝ) * derivPairNorm π k A B θ ≤ 2 * G * T := by
    intro k hkm
    have hkm' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hkm)
    calc ϖ ^ k / (k.factorial : ℝ) * derivPairNorm π k A B θ
        ≤ ϖ ^ k / (k.factorial : ℝ) * (2 * ∑ l ∈ Finset.range (k + 1),
            (k.choose l : ℝ) * ‖iteratedFDeriv ℝ l E θ‖ * derivPairNorm π (k - l) Ac As θ) :=
          mul_le_mul_of_nonneg_left
            (derivPairNorm_rot_le hU hE π hπ hAc hAs hrot hθ hkm') (by positivity)
      _ = 2 * ∑ l ∈ Finset.range (k + 1), ϖ ^ k / (k.factorial : ℝ) *
            ((k.choose l : ℝ) * ‖iteratedFDeriv ℝ l E θ‖ * derivPairNorm π (k - l) Ac As θ) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ ≤ 2 * ∑ l ∈ Finset.range (k + 1), G * f (k - l) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l hl => ?_) (by norm_num)
          have hlk : l ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
          refine (rot_term_le hϖ (norm_nonneg (iteratedFDeriv ℝ l E θ))
            (derivPairNorm_nonneg π (k - l) Ac As θ) hlk).trans ?_
          exact mul_le_mul_of_nonneg_right (hG l (hlk.trans hkm')) (hf0 _)
      _ = 2 * G * ∑ j ∈ Finset.range (k + 1), f j := by
          rw [← Finset.mul_sum, ← mul_assoc, ← Finset.sum_range_reflect f (k + 1)]
          congr 2
      _ ≤ 2 * G * T := by
          gcongr
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (Nat.succ_le_succ hkm')) fun j _ _ => hf0 j
  calc ∑ k ∈ Finset.range (m + 1), ϖ ^ k / (k.factorial : ℝ) * derivPairNorm π k A B θ
      ≤ ∑ _k ∈ Finset.range (m + 1), 2 * G * T := Finset.sum_le_sum hk
    _ = 2 * ((m + 1 : ℕ) : ℝ) * G * T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- The `θ`-partials by the full derivatives. -/
theorem amplitudeJetNorm_le_ampDerivNorm (π : ι → ℝ) (m : ℕ) {ϖ : ℝ} (hϖ : 0 ≤ ϖ)
    (A B : ∀ x, Vec 2 → h x) (θ : Vec 2) :
    amplitudeJetNorm π m ϖ A B θ ≤
      ENNReal.ofReal (((m + 1 : ℕ) : ℝ) * 2 ^ m) * ampDerivNorm π m ϖ A B θ := by
  set t : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (ϖ ^ k / (k.factorial : ℝ)) *
    (∑ x, ENNReal.ofReal ((π x)⁻¹) *
      (ENNReal.ofReal (‖iteratedFDeriv ℝ k (A x) θ‖ ^ 2) +
        ENNReal.ofReal (‖iteratedFDeriv ℝ k (B x) θ‖ ^ 2))) ^ (1 / 2 : ℝ) with ht
  have hterm : ∀ β ∈ momentIndices m,
      ENNReal.ofReal (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
        (∑ x, ENNReal.ofReal ((π x)⁻¹) *
          (ENNReal.ofReal (‖thetaPartial β.1 β.2 (A x) θ‖ ^ 2) +
            ENNReal.ofReal (‖thetaPartial β.1 β.2 (B x) θ‖ ^ 2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (2 ^ m) * t (β.1 + β.2) := by
    intro β hβ
    have hβm : β.1 + β.2 ≤ m := (Finset.mem_filter.1 hβ).2
    rw [ht, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
    · have hfac : ((β.1 + β.2).factorial : ℝ) ≤ 2 ^ m * (β.1.factorial * β.2.factorial : ℕ) := by
        have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right β.1 β.2)
        rw [Nat.add_sub_cancel_left] at h1
        have h2 : (β.1 + β.2).choose β.1 ≤ 2 ^ m :=
          (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right two_pos hβm)
        have h3 : (β.1 + β.2).factorial ≤ 2 ^ m * (β.1.factorial * β.2.factorial) := by
          rw [← h1, mul_assoc]
          exact Nat.mul_le_mul_right _ h2
        exact_mod_cast h3
      have hpos : (0 : ℝ) < ((β.1 + β.2).factorial : ℝ) := by positivity
      have hpos' : (0 : ℝ) < ((β.1.factorial * β.2.factorial : ℕ) : ℝ) := by positivity
      have hinv : (1 : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ) ≤
          2 ^ m / ((β.1 + β.2).factorial : ℝ) := by
        rw [div_le_div_iff₀ hpos' hpos]
        linarith
      calc ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)
          = ϖ ^ (β.1 + β.2) * (1 / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) := by ring
        _ ≤ ϖ ^ (β.1 + β.2) * (2 ^ m / ((β.1 + β.2).factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv (pow_nonneg hϖ _)
        _ = _ := by ring
    · refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl
        (add_le_add ?_ ?_)) (by norm_num)
      · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
          (norm_thetaPartial_le _ _ _ _) 2)
      · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
          (norm_thetaPartial_le _ _ _ _) 2)
  have hmaps : ∀ β ∈ momentIndices m, β.1 + β.2 ∈ Finset.range (m + 1) := fun β hβ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_filter.1 hβ).2)
  have hcard : ∀ k, ((momentIndices m).filter fun β => β.1 + β.2 = k).card ≤ m + 1 := by
    intro k
    calc ((momentIndices m).filter fun β => β.1 + β.2 = k).card
        ≤ (Finset.range (m + 1)).card := by
          refine Finset.card_le_card_of_injOn (fun β => β.1) (fun β hβ => ?_) ?_
          · have hβ' := (Finset.mem_filter.1 hβ).1
            simp only [momentIndices, Finset.mem_filter, Finset.mem_product] at hβ'
            exact hβ'.1.1
          · intro β hβ β' hβ' hββ'
            have e1 := (Finset.mem_filter.1 hβ).2
            have e2 := (Finset.mem_filter.1 hβ').2
            simp only at hββ'
            exact Prod.ext hββ' (by omega)
      _ = m + 1 := Finset.card_range _
  calc amplitudeJetNorm π m ϖ A B θ
      ≤ ∑ β ∈ momentIndices m, ENNReal.ofReal (2 ^ m) * t (β.1 + β.2) := by
        unfold amplitudeJetNorm
        exact Finset.sum_le_sum hterm
    _ = ∑ k ∈ Finset.range (m + 1), ∑ β ∈ momentIndices m with β.1 + β.2 = k,
          ENNReal.ofReal (2 ^ m) * t k := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun β hβ => ?_
        rw [(Finset.mem_filter.1 hβ).2]
    _ ≤ ∑ k ∈ Finset.range (m + 1), ((m + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (2 ^ m) * t k) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul' (by exact_mod_cast hcard k) le_rfl
    _ = ENNReal.ofReal (((m + 1 : ℕ) : ℝ) * 2 ^ m) * ampDerivNorm π m ϖ A B θ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ampDerivNorm,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ht]
        ring

end Family

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
open MeasureTheory Homogenization Filter AVRegularity.Sobolev
open scoped ENNReal RealInnerProductSpace
namespace AVRegularity.CycleWords.Assembly

/-! # The Bloch fibre norms of compactly supported data by their moment norm

For smooth compactly supported data the Bloch sums at a point of the unit cell are finite sums
over a lattice box. The cutoff `χ_lo(θ/√η)` has `ϖ^l ‖D^l χ‖ ≤ B` when
`ϖ ≤ √η` (`norm_iteratedFDeriv_scaled_le`), the word monomials of `ϖ y` are the moment monomials
(`wordMonomial_smul_eq`), and the pair bound of the Bloch derivatives holds at every point of the
cell (`pair_bound_point`). Parseval on the cube and the tiling of the plane bound the cube–cell
integral of one squared lattice pair by `(2π)² ‖H‖₂²` (`lintegral_cube_cell_latticePair_le`);
`lintegral_weighted_sum` pulls the weighted finite sums out of the integrals. -/

/-- The lattice box `|k_i| ≤ N`. -/
def latticeBox (N : ℕ) : Finset (Fin 2 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

theorem exists_support_radius {E : Type*} [NormedAddCommGroup E] {G : Vec 2 → E}
    (hG : HasCompactSupport G) : ∃ R : ℝ, 0 ≤ R ∧ ∀ y : Vec 2, R < ‖y‖ → G y = 0 := by
  obtain ⟨R, hR⟩ := hG.isCompact.isBounded.subset_closedBall (0 : Vec 2)
  refine ⟨max R 0, le_max_right _ _, fun y hy => image_eq_zero_of_notMem_tsupport fun hyt => ?_⟩
  have := hR hyt
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R 0]

theorem lattice_far {R : ℝ} {N : ℕ} (hN : R + 1 ≤ N) {z : Vec 2} (hz : z ∈ AVenhance.unitCube)
    {k : Fin 2 → ℤ} (hk : k ∉ latticeBox N) : R < ‖z + fun i => (k i : ℝ)‖ := by
  simp only [latticeBox, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hk
  obtain ⟨i, hi⟩ := hk
  have hzi := hz i (Set.mem_univ i)
  have hki : (N : ℝ) + 1 ≤ |(k i : ℝ)| := by
    have : (N : ℤ) + 1 ≤ |k i| := by
      rcases le_or_gt (-(N : ℤ)) (k i) with h | h
      · have := not_le.1 (fun h' => hi ⟨h, h'⟩)
        rw [abs_of_pos (by omega)]
        omega
      · rw [abs_of_neg (by omega)]
        omega
    exact_mod_cast this
  have hzk : |(k i : ℝ)| - 1 < |z i + k i| := by
    have := abs_sub_abs_le_abs_sub (k i : ℝ) (-(z i))
    rw [sub_neg_eq_add, add_comm] at this
    have hz' : |z i| < 1 := by rw [abs_lt]; constructor <;> linarith [hzi.1, hzi.2]
    rw [abs_neg] at this
    linarith
  calc R ≤ N - 1 + 1 - 1 := by linarith
    _ < |z i + k i| := by linarith
    _ = ‖(z + fun i => (k i : ℝ)) i‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖z + fun i => (k i : ℝ)‖ := norm_le_pi_norm _ i

theorem blochPhase_eq_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ψ : ℝ → ℝ)
    {G : Vec 2 → E} {R : ℝ} (hG : ∀ y : Vec 2, R < ‖y‖ → G y = 0) {N : ℕ} (hN : R + 1 ≤ N)
    {z : Vec 2} (hz : z ∈ AVenhance.unitCube) (θ : Vec 2) :
    blochPhase ψ θ G z = ∑ k ∈ latticeBox N, ψ (vecDot θ (z + fun i => (k i : ℝ))) •
      G (z + fun i => (k i : ℝ)) := by
  unfold blochPhase
  refine tsum_eq_sum fun k hk => ?_
  rw [hG _ (lattice_far hN hz hk), smul_zero]

/-- The derivatives of a rescaled cutoff. -/
theorem norm_iteratedFDeriv_scaled_le {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (s : ℝ)
    (l : ℕ) (θ : Vec 2) :
    ‖iteratedFDeriv ℝ l (fun θ => χ (s • θ)) θ‖ ≤ ‖iteratedFDeriv ℝ l χ (s • θ)‖ * |s| ^ l := by
  have h : (fun θ : Vec 2 => χ (s • θ)) = χ ∘ (s • ContinuousLinearMap.id ℝ (Vec 2)) := by
    funext θ
    simp
  rw [h, (s • ContinuousLinearMap.id ℝ (Vec 2)).iteratedFDeriv_comp_right hχ θ
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine mul_le_mul (le_of_eq (by simp)) (pow_le_pow_left₀ (norm_nonneg _) ?_ l)
    (by positivity) (norm_nonneg _)
  refine (norm_smul_le s _).trans ?_
  rw [Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg s) ContinuousLinearMap.norm_id_le

/-- The multi-index of the coordinates of a word. -/
def idxCount {j : ℕ} (idx : Fin j → Fin 2) : ℕ × ℕ :=
  ((Finset.univ.filter fun l => idx l = 0).card, (Finset.univ.filter fun l => idx l = 1).card)

theorem idxCount_sum {j : ℕ} (idx : Fin j → Fin 2) : (idxCount idx).1 + (idxCount idx).2 = j := by
  have h := Finset.card_eq_sum_card_fiberwise (f := idx) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  rw [Fin.sum_univ_two, Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

/-- The word monomial of `ϖ y` is the moment monomial of `idxCount`. -/
theorem wordMonomial_smul_eq {j : ℕ} (idx : Fin j → Fin 2) (ϖ : ℝ) (y : Vec 2) :
    wordMonomial idx (ϖ • y) = (ϖ * y 0) ^ (idxCount idx).1 * (ϖ * y 1) ^ (idxCount idx).2 := by
  unfold wordMonomial idxCount
  rw [← Finset.prod_fiberwise_of_maps_to' (g := idx) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) (fun i => (ϖ • y) i), Fin.prod_univ_two]
  simp [Finset.prod_const]

theorem wordMonomial_smul_eq_pow {j : ℕ} (idx : Fin j → Fin 2) (ϖ : ℝ) (y : Vec 2) :
    wordMonomial idx (ϖ • y) = ϖ ^ j * wordMonomial idx y := by
  unfold wordMonomial
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

section Point

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The pointwise pair bound** at a point of the unit cell, with the moment weights. -/
theorem pair_bound_point {n : ℕ} {χlo : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {B : ℝ}
    (hB : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ B) {η ϖ : ℝ} (hη : 0 < η) (hϖ : 0 < ϖ)
    (hϖη : ϖ ≤ Real.sqrt η) {G : Vec 2 → E} {R : ℝ} (hG : ∀ y : Vec 2, R < ‖y‖ → G y = 0)
    {N : ℕ} (hN : R + 1 ≤ N) {z : Vec 2} (hz : z ∈ AVenhance.unitCube) {α : ℕ × ℕ}
    (hαn : α.1 + α.2 ≤ n) (θ : Vec 2) :
    ϖ ^ (2 * (α.1 + α.2)) *
        (‖thetaPartial α.1 α.2 (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ') • blochCos θ' G z) θ‖ ^ 2 +
          ‖thetaPartial α.1 α.2 (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ') • blochSin θ' G z) θ‖ ^ 2) ≤
      ((α.1 + α.2 + 1 : ℕ) * 2 ^ (α.1 + α.2) : ℝ) *
        ∑ l ∈ Finset.range (α.1 + α.2 + 1), ∑ idx : Fin (α.1 + α.2 - l) → Fin 2,
          (((α.1 + α.2).choose l : ℝ) * B) ^ 2 *
            (‖∑ q ∈ latticeBox N, Real.cos (vecDot θ (z + fun i => (q i : ℝ))) •
                (wordMonomial idx (ϖ • (z + fun i => (q i : ℝ))) •
                  G (z + fun i => (q i : ℝ)))‖ ^ 2 +
              ‖∑ q ∈ latticeBox N, Real.sin (vecDot θ (z + fun i => (q i : ℝ))) •
                (wordMonomial idx (ϖ • (z + fun i => (q i : ℝ))) •
                  G (z + fun i => (q i : ℝ)))‖ ^ 2) := by
  set k := α.1 + α.2 with hk
  set s : ℝ := (Real.sqrt η)⁻¹ with hs
  have hs0 : 0 ≤ s := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hϖs : ϖ * s ≤ 1 := by
    rw [hs, mul_inv_le_iff₀ (Real.sqrt_pos.2 hη), one_mul]
    exact hϖη
  have hχs : ContDiff ℝ (⊤ : ℕ∞) fun θ => χlo (s • θ) :=
    hχ.comp (contDiff_const_smul s)
  set y : (Fin 2 → ℤ) → Vec 2 := fun q => z + fun i => (q i : ℝ) with hy
  -- the Bloch sums are finite sums on the unit cell
  have hcos : (fun θ' => χlo (s • θ') • blochCos θ' G z) =
      fun θ' => χlo (s • θ') • ∑ q ∈ latticeBox N, Real.cos (vecDot θ' (y q)) • G (y q) := by
    funext θ'
    rw [blochCos_eq_blochPhase, blochPhase_eq_box Real.cos hG hN hz]
  have hsin : (fun θ' => χlo (s • θ') • blochSin θ' G z) =
      fun θ' => χlo (s • θ') • ∑ q ∈ latticeBox N, Real.sin (vecDot θ' (y q)) • G (y q) := by
    funext θ'
    rw [blochSin_eq_blochPhase, blochPhase_eq_box Real.sin hG hN hz]
  rw [hcos, hsin]
  have hpair := pair_thetaPartial_le hχs (latticeBox N) y (fun q => G (y q)) α θ
  rw [← hk] at hpair
  have hϖ2 : 0 ≤ ϖ ^ (2 * k) := by positivity
  refine (mul_le_mul_of_nonneg_left hpair hϖ2).trans ?_
  calc _ = ((k + 1 : ℕ) * 2 ^ k : ℝ) * ∑ l ∈ Finset.range (k + 1),
        ∑ idx : Fin (k - l) → Fin 2, ((k.choose l : ℝ) * (ϖ ^ l * ‖iteratedFDeriv ℝ l
          (fun θ => χlo (s • θ)) θ‖)) ^ 2 *
          (‖∑ q ∈ latticeBox N, Real.cos (vecDot θ (y q)) •
              (wordMonomial idx (ϖ • y q) • G (y q))‖ ^ 2 +
            ‖∑ q ∈ latticeBox N, Real.sin (vecDot θ (y q)) •
              (wordMonomial idx (ϖ • y q) • G (y q))‖ ^ 2) := by
        rw [mul_left_comm, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun l hl => ?_
        have hlk : l ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun idx _ => ?_
        have hsplit : ϖ ^ (2 * k) = (ϖ ^ l) ^ 2 * (ϖ ^ (k - l)) ^ 2 := by
          rw [← mul_pow, ← pow_add, Nat.add_sub_cancel' hlk, ← pow_mul, mul_comm]
        have hw : ∀ ψ : ℝ → ℝ, ∑ q ∈ latticeBox N, ψ (vecDot θ (y q)) •
            (wordMonomial idx (ϖ • y q) • G (y q)) = ϖ ^ (k - l) •
              ∑ q ∈ latticeBox N, ψ (vecDot θ (y q)) • (wordMonomial idx (y q) • G (y q)) :=
          fun ψ => by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [wordMonomial_smul_eq_pow, mul_smul]
            exact smul_comm _ _ _
        rw [hw Real.cos, hw Real.sin, norm_smul, norm_smul,
          Real.norm_of_nonneg (pow_nonneg hϖ.le _), hsplit]
        ring
    _ ≤ _ := by
        gcongr with l hl idx
        have hlk : l ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
        calc ϖ ^ l * ‖iteratedFDeriv ℝ l (fun θ => χlo (s • θ)) θ‖
            ≤ ϖ ^ l * (‖iteratedFDeriv ℝ l χlo (s • θ)‖ * |s| ^ l) :=
              mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_scaled_le hχ s l θ)
                (by positivity)
          _ = (ϖ * s) ^ l * ‖iteratedFDeriv ℝ l χlo (s • θ)‖ := by
              rw [abs_of_nonneg hs0, mul_pow]
              ring
          _ ≤ 1 * B := mul_le_mul (pow_le_one₀ (by positivity) hϖs)
              (hB l (hlk.trans hαn) _) (norm_nonneg _) zero_le_one
          _ = B := one_mul B

/-- The squared pair of finite lattice sums at `(θ, z)`. -/
noncomputable def latticePair (K : Finset (Fin 2 → ℤ)) (H : Vec 2 → E) (θ z : Vec 2) : ℝ≥0∞ :=
  ENNReal.ofReal ‖∑ q ∈ K, Real.cos (vecDot θ (z + fun i => (q i : ℝ))) •
      H (z + fun i => (q i : ℝ))‖ ^ 2 +
    ENNReal.ofReal ‖∑ q ∈ K, Real.sin (vecDot θ (z + fun i => (q i : ℝ))) •
      H (z + fun i => (q i : ℝ))‖ ^ 2

theorem measurable_latticePair (K : Finset (Fin 2 → ℤ)) {H : Vec 2 → E} (hH : Continuous H) :
    Measurable fun p : Vec 2 × Vec 2 => latticePair K H p.1 p.2 := by
  have hc : ∀ ψ : ℝ → ℝ, Continuous ψ → Continuous fun p : Vec 2 × Vec 2 =>
      ‖∑ q ∈ K, ψ (vecDot p.1 (p.2 + fun i => (q i : ℝ))) • H (p.2 + fun i => (q i : ℝ))‖ := by
    intro ψ hψ
    refine (continuous_finsetSum _ fun q _ => (hψ.comp ?_).smul (hH.comp ?_)).norm
    · unfold vecDot
      fun_prop
    · fun_prop
  unfold latticePair
  exact ((ENNReal.measurable_ofReal.comp (hc _ Real.continuous_cos).measurable).pow_const 2).add
    ((ENNReal.measurable_ofReal.comp (hc _ Real.continuous_sin).measurable).pow_const 2)

/-- **Parseval on the cube and tiling of the plane** for one finite lattice sum. -/
theorem lintegral_cube_cell_latticePair_le (K : Finset (Fin 2 → ℤ)) {H : Vec 2 → E}
    (hH : Continuous H) :
    ∫⁻ θ in freqCube, ∫⁻ z in AVenhance.unitCube, latticePair K H θ z ≤
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * eLpNorm H 2 volume ^ 2 := by
  rw [lintegral_lintegral_swap (measurable_latticePair K hH).aemeasurable]
  have hpar : ∀ z, ∫⁻ θ in freqCube, latticePair K H θ z =
      ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        ∑ q ∈ K, ENNReal.ofReal (‖H (z + fun i => (q i : ℝ))‖ ^ 2) :=
    fun z => lintegral_cube_parseval K z fun q => H (z + fun i => (q i : ℝ))
  have hmq : ∀ q : Fin 2 → ℤ, Measurable fun z : Vec 2 =>
      ENNReal.ofReal (‖H (z + fun i => (q i : ℝ))‖ ^ 2) := fun q =>
    ENNReal.measurable_ofReal.comp
      ((hH.comp (continuous_id.add continuous_const)).norm.pow 2).measurable
  have hmH : Measurable fun y : Vec 2 => ENNReal.ofReal (‖H y‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hH.norm.pow 2).measurable
  rw [lintegral_congr hpar, lintegral_const_mul _ (Finset.measurable_sum _ fun q _ => hmq q)]
  gcongr
  calc ∫⁻ z in AVenhance.unitCube, ∑ q ∈ K, ENNReal.ofReal (‖H (z + fun i => (q i : ℝ))‖ ^ 2)
      ≤ ∫⁻ z in AVenhance.unitCube,
          ∑' q : Fin 2 → ℤ, ENNReal.ofReal (‖H (z + fun i => (q i : ℝ))‖ ^ 2) :=
        lintegral_mono fun z => ENNReal.sum_le_tsum K
    _ = ∑' q : Fin 2 → ℤ, ∫⁻ z in Applications.cellI,
          ENNReal.ofReal (‖H (z + AVenhance.latticeShift q)‖ ^ 2) := by
        rw [lintegral_tsum fun q => (hmq q).aemeasurable,
          ← Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube]
        rfl
    _ = ∫⁻ y, ENNReal.ofReal (‖H y‖ ^ 2) :=
        (CycleJointProofs.lintegral_tiling_translate _ hmH).symm
    _ = eLpNorm H 2 volume ^ 2 := by
        rw [eLpNorm_two_sq hH.aestronglyMeasurable]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end Point

/-- Pulling weighted finite sums out of a lower integral. -/
theorem lintegral_weighted_sum {X : Type*} [MeasurableSpace X] (μ : Measure X) {ι : Type*}
    [Fintype ι] (a : ι → ℝ≥0∞) (b : ℝ≥0∞) (L : Finset ℕ) {J : ℕ → Type*}
    [∀ l, Fintype (J l)] (c : ℕ → ℝ≥0∞) (Q : ι → ∀ l, J l → X → ℝ≥0∞)
    (hQ : ∀ x l j, Measurable (Q x l j)) :
    ∫⁻ t, ∑ x, a x * (b * ∑ l ∈ L, ∑ j : J l, c l * Q x l j t) ∂μ =
      ∑ x, a x * (b * ∑ l ∈ L, ∑ j : J l, c l * ∫⁻ t, Q x l j t ∂μ) := by
  have hj : ∀ x l, Measurable fun t => ∑ j : J l, c l * Q x l j t := fun x l =>
    Finset.measurable_sum _ fun j _ => (hQ x l j).const_mul _
  have hl : ∀ x, Measurable fun t => ∑ l ∈ L, ∑ j : J l, c l * Q x l j t := fun x =>
    Finset.measurable_sum _ fun l _ => hj x l
  rw [lintegral_finsetSum _ fun x _ => ((hl x).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lintegral_const_mul _ ((hl x).const_mul _), lintegral_const_mul _ (hl x),
    lintegral_finsetSum _ fun l _ => hj x l]
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [lintegral_finsetSum _ fun j _ => (hQ x l j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => lintegral_const_mul _ (hQ x l j)

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # Fibre duality

A forced cell solution `W` of the fibre problem at `ξ` (flux `Φ`, no scalar source) on `[a, b]`
and a homogeneous cell solution `Ψ` of the reversed fibre problem at `-ξ` on `[-b, -a]` satisfy
`⟨W(b), Ψ(-b)⟩ - ⟨W(a), Ψ(-a)⟩ = ∫_a^b ℓ_t` (bilinear cell pairing `⟨W, conj (conj Ψ)⟩`), where
`ℓ_t = cellComplexSource θ 0 Φ(t) (conj Ψ(-t)) = -∑_j ⟨Φ_j(t), conj (D_{-θ,j} Ψ(-t))⟩`,
`θ = √η ξ`. The Hilbert form is `cellWeakAdjointPairing_forced`: the generator
terms cancel (`cellComplexGenerator_opposite_drift`), only the source survives. -/

/-- A forced forward curve against a genuine homogeneous backward adjoint curve. -/
theorem cellWeakAdjointPairing_forced {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {u v : ℝ → ComplexCellL2} {slice other : ℝ → TorusHk 1 ℂ}
    {S : ℝ → ComplexCellL2} {F : ℝ → Fin 2 → ComplexCellL2}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative C hG V hv.1 hb t (slice t) (S t) (F t)))
    (h' : CellWeakHilbertCurve a b v other (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (other t) 0 0)) :
    cellComplexPair (u b) (v b) - cellComplexPair (u a) (v a) =
      ∫ t in a..b, cellComplexSource C.θ (S t) (F t) (other t) := by
  rw [h.complex_pairing_increment hab h']
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [cellDualComplexPair_neg,
    cellDualComplexPair_derivative C hG V hv.1 hb t (slice t) (other t) (S t) (F t),
    cellDualComplexPair_derivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
      (cellDrift_neg_bound hb) t (other t) (slice t) 0 0,
    show (0 : Fin 2 → ComplexCellL2) = fun _ => 0 from rfl, cellComplexSource_zero, add_zero,
    star_neg, cellComplexGenerator_opposite_drift C hG V hv hb]
  ring

/-- The integrand of the forced pairing is the source tested against the adjoint slice. -/
theorem cellWeakAdjoint_forced_integrand_eq
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (s o : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualComplexPair (cellDualDerivative C hG V hv.1 hb t s S F) o +
      star (cellDualComplexPair (-cellDualDerivative (cellAdjointCoefficients C) hG V
        (cellDrift_neg hv).1 (cellDrift_neg_bound hb) t o 0 0) s) =
      cellComplexSource C.θ S F o := by
  rw [cellDualComplexPair_neg,
    cellDualComplexPair_derivative C hG V hv.1 hb t s o S F,
    cellDualComplexPair_derivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
      (cellDrift_neg_bound hb) t o s 0 0,
    show (0 : Fin 2 → ComplexCellL2) = fun _ => 0 from rfl, cellComplexSource_zero, add_zero,
    star_neg, cellComplexGenerator_opposite_drift C hG V hv hb]
  ring

/-- The forced source tested against a genuine adjoint curve is interval integrable. -/
theorem cellWeakAdjoint_forced_source_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {u v : ℝ → ComplexCellL2} {slice other : ℝ → TorusHk 1 ℂ}
    {S : ℝ → ComplexCellL2} {F : ℝ → Fin 2 → ComplexCellL2}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative C hG V hv.1 hb t (slice t) (S t) (F t)))
    (h' : CellWeakHilbertCurve a b v other (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (other t) 0 0)) :
    IntervalIntegrable (fun t => cellComplexSource C.θ (S t) (F t) (other t)) MeasureTheory.volume
      a b := by
  have hi₁ := cellDualComplexPair_cross_intervalIntegrable hab h.dual h'.state
  have hi₂ := cellDualComplexPair_cross_intervalIntegrable hab h'.dual h.state
  have hi₂star : IntervalIntegrable (fun t => star (cellDualComplexPair
      (-cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (other t) 0 0) (slice t))) MeasureTheory.volume a b :=
    intervalIntegrable_iff.mpr
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp (intervalIntegrable_iff.mp hi₂))
  refine (hi₁.add hi₂star).congr fun t _ => ?_
  exact cellWeakAdjoint_forced_integrand_eq C hG V hv hb t (slice t) (other t) (S t) (F t)

theorem fibreCoefficients_zero_eq (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ) :
    fibreCoefficients η G v ξ (fun _ => 0) =
      ⟨fun t _ => G t, v, fun k => (Real.sqrt η : ℂ) * ξ k, 0⟩ := by
  unfold fibreCoefficients
  congr 1
  funext t
  simp

end AVRegularity.CycleWords.Assembly
end
end
