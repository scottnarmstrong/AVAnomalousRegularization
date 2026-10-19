-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVenhance.Infra.Classical.PeriodicCalculus
public import AVenhance.Statements.Roots.UnitCube
public import AVenhance.Statements.Roots.IsZ2Periodic
public import Homogenization.Sobolev.WeakDerivatives
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.Weighted

/-! Generic source addition keeps the canonical normed-space topology in its interface. -/

theorem bochnerSource_memLp_add {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] {μ : Measure T} {p : ENNReal}
    {f g : T → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (fun t => f t + g t) p μ := hf.add hg

theorem bochnerSource_memLp_sub {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] {μ : Measure T} {p : ENNReal}
    {f g : T → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (fun t => f t - g t) p μ := hf.sub hg

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! A compact smooth time cutoff identically one on a neighborhood of a prescribed window. -/

theorem exists_compact_time_cutoff (a b : ℝ) :
    ∃ τ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) τ ∧ HasCompactSupport τ ∧
      (∀ t, 0 ≤ τ t ∧ τ t ≤ 1) ∧
      (∀ t ∈ Icc a b, τ t = 1 ∧ HasDerivAt τ 0 t) := by
  let R := max |a| |b| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let φ : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, fun _ => ⟨φ.nonneg, φ.le_one⟩, ?_⟩
  intro t ht
  have htr : |t| < R := by
    have ha := neg_abs_le a
    have hb := le_abs_self b
    have hma := le_max_left |a| |b|
    have hmb := le_max_right |a| |b|
    rw [abs_lt]
    dsimp [R]
    constructor <;> linarith [ht.1, ht.2]
  have hball : t ∈ Metric.ball (0 : ℝ) R := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using htr
  have hone : ∀ y ∈ Metric.ball (0 : ℝ) R, φ y = 1 := by
    intro y hy
    apply φ.one_of_mem_closedBall
    exact Metric.ball_subset_closedBall hy
  refine ⟨hone t hball, ?_⟩
  apply (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds hball] with y hy
  exact hone y hy

end AVRegularity.Weighted
end
end

section
@[expose] public section
open Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Strong convergence of uniformly contractive operators on moving inputs. -/

/-- Contractive operators converging on fixed vectors also converge on any strongly convergent input. -/
theorem tendsto_contractive_operator_moving {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S : ℕ → H →L[ℝ] H) (hS : ∀ N z, ‖S N z‖ ≤ ‖z‖)
    (hlim : ∀ z, Tendsto (fun N => S N z) atTop (𝓝 z))
    (z : ℕ → H) (z₀ : H) (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun N => S N (z N)) atTop (𝓝 z₀) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h₁ := tendsto_iff_norm_sub_tendsto_zero.mp hz
  have h₂ := tendsto_iff_norm_sub_tendsto_zero.mp (hlim z₀)
  apply squeeze_zero (fun _ => norm_nonneg _) ?_ (by simpa using h₁.add h₂)
  intro N
  calc
    ‖S N (z N) - z₀‖ ≤ ‖S N (z N) - S N z₀‖ + ‖S N z₀ - z₀‖ := by
      simpa only [dist_eq_norm] using dist_triangle (S N (z N)) (S N z₀) z₀
    _ = ‖S N (z N - z₀)‖ + ‖S N z₀ - z₀‖ := by rw [map_sub]
    _ ≤ ‖z N - z₀‖ + ‖S N z₀ - z₀‖ := add_le_add (hS N (z N - z₀)) le_rfl

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Numerical absorption of the compact chart test's source and cutoff errors. -/

theorem compact_weight_cutoff_young
    {χ η r M d u f : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hη : 0 ≤ η) (hM : 0 ≤ M) :
    8 * χ * η * M * u ^ 2 + 32 * χ * η * r * u ^ 2 +
      40 * χ * η * d * u + 2 * χ ^ 2 * r * d * u +
      2 * χ ^ 2 * f * d + 2 * χ ^ 2 * r * f * u + 8 * χ * η * f * u ≤
      (1 / 2 : ℝ) * χ ^ 2 * d ^ 2 + 16 * r ^ 2 * χ ^ 2 * u ^ 2 +
        8 * f ^ 2 + (4096 * η ^ 2 + 16 * M * η) * u ^ 2 := by
  have hc : χ ^ 2 ≤ 1 := by nlinarith only [hχ, hχ1]
  have hcf : χ ^ 2 * f ^ 2 ≤ f ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg f)
  have hce : χ ^ 2 * (η ^ 2 * u ^ 2) ≤ η ^ 2 * u ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg η) (sq_nonneg u))
  have hv : 8 * χ * η * M * u ^ 2 ≤ 8 * η * M * u ^ 2 := by
    have he := mul_le_mul_of_nonneg_right hχ1
      (show 0 ≤ 8 * η * M * u ^ 2 by positivity)
    nlinarith only [he]
  have hr : 32 * χ * η * r * u ^ 2 ≤ r ^ 2 * χ ^ 2 * u ^ 2 + 256 * η ^ 2 * u ^ 2 := by
    nlinarith only [sq_nonneg (χ * r * u - 16 * η * u)]
  have hg : 40 * χ * η * d * u ≤ (1 / 8 : ℝ) * χ ^ 2 * d ^ 2 + 3200 * η ^ 2 * u ^ 2 := by
    nlinarith only [sq_nonneg (χ * d - 160 * η * u)]
  have hp : 2 * χ ^ 2 * r * d * u ≤ (1 / 8 : ℝ) * χ ^ 2 * d ^ 2 + 8 * r ^ 2 * χ ^ 2 * u ^ 2 := by
    nlinarith only [sq_nonneg (χ * d - 8 * χ * r * u)]
  have hf : 2 * χ ^ 2 * f * d ≤ (1 / 4 : ℝ) * χ ^ 2 * d ^ 2 + 4 * f ^ 2 := by
    nlinarith only [sq_nonneg (χ * d - 4 * χ * f), hcf]
  have hfl : 2 * χ ^ 2 * r * f * u ≤ f ^ 2 + r ^ 2 * χ ^ 2 * u ^ 2 := by
    nlinarith only [sq_nonneg (χ * f - χ * r * u), hcf]
  have hfe : 8 * χ * η * f * u ≤ f ^ 2 + 16 * η ^ 2 * u ^ 2 := by
    nlinarith only [sq_nonneg (f - 4 * χ * η * u), hce]
  nlinarith only [hv, hr, hg, hp, hf, hfl, hfe,
    sq_nonneg f, mul_nonneg (sq_nonneg η) (sq_nonneg u),
    mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg χ)) (sq_nonneg u),
    mul_nonneg (mul_nonneg hM hη) (sq_nonneg u)]

end AVRegularity.Weighted
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.Weighted

/-! The quadratic family budget gives the stated sum of data and flux norms. -/

theorem family_energy_square_root {e i f : ℝ≥0∞} {A : ℝ} (hA : 0 ≤ A)
    (h : e ≤ ENNReal.ofReal A * (i + 16 * f)) :
    e ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal ((16 * A) ^ (1 / 2 : ℝ)) *
      (i ^ (1 / 2 : ℝ) + f ^ (1 / 2 : ℝ)) := by
  have hi : i ≤ 16 * i := by
    have hh := mul_le_mul' (show (1 : ℝ≥0∞) ≤ 16 by norm_num) (le_rfl : i ≤ i)
    simpa only [one_mul] using hh
  have hh : e ≤ ENNReal.ofReal (16 * A) * (i + f) := by
    apply h.trans
    have hsum := add_le_add hi (le_rfl : 16 * f ≤ 16 * f)
    have hm := mul_le_mul' (le_rfl : ENNReal.ofReal A ≤ _) hsum
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16), ENNReal.ofReal_ofNat]
    exact hm.trans_eq (by ring)
  calc
    _ ≤ (ENNReal.ofReal (16 * A) * (i + f)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hh (by norm_num)
    _ = ENNReal.ofReal ((16 * A) ^ (1 / 2 : ℝ)) * (i + f) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    _ ≤ _ := mul_le_mul' le_rfl (ENNReal.rpow_add_le_add_rpow i f (by norm_num) (by norm_num))

end AVRegularity.Weighted
end
end

section
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Weighted

/-! The component supremum is summed before taking the family energy norm. -/

theorem family_weighted_energy_budget {ι : Type*} [Fintype ι] {T : Type*}
    [MeasurableSpace T] (μ : Measure T) (mass : ι → ℝ≥0∞)
    (hmass : ∀ i, mass i ≠ ⊤)
    (energy initial : ι → ℝ≥0∞) (forcing : ι → T → ℝ≥0∞) (A : ℝ≥0∞)
    (hforcing : ∀ i, AEMeasurable (forcing i) μ)
    (h : ∀ i, energy i ≤ A * (initial i + 16 * ∫⁻ t, forcing i t ∂μ)) :
    (∑ i, mass i * energy i) ≤
      A * ((∑ i, mass i * initial i) + 16 * ∫⁻ t, ∑ i, mass i * forcing i t ∂μ) := by
  have hf : (∫⁻ t, ∑ i, mass i * forcing i t ∂μ) =
      ∑ i, mass i * ∫⁻ t, forcing i t ∂μ := by
    rw [lintegral_finsetSum']
    · apply Finset.sum_congr rfl
      intro i _
      exact lintegral_const_mul' _ _ (hmass i)
    · intro i _
      exact (hforcing i).const_mul _
  rw [hf]
  calc
    _ ≤ ∑ i, mass i * (A * (initial i + 16 * ∫⁻ t, forcing i t ∂μ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl (h i))
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]; congr 1 <;>
      apply Finset.sum_congr rfl <;> intro i _ <;> ring

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Weighted

/-! Genuine successive states can be assembled into one finite chronological family. -/

theorem exists_finite_chronological_family {N : ℕ} (S : Fin (N + 1) → Type*)
    (P : ∀ i, S i → Prop) (R : ∀ j : Fin N, S j.castSucc → S j.succ → Prop)
    (h0 : ∃ s, P 0 s)
    (hstep : ∀ j s, P j.castSucc s → ∃ s', P j.succ s' ∧ R j s s') :
    ∃ s : ∀ i, S i, (∀ i, P i (s i)) ∧ ∀ j, R j (s j.castSucc) (s j.succ) := by
  classical
  let B := fun i => {s : S i // P i s}
  let b0 : B 0 := ⟨h0.choose, h0.choose_spec⟩
  let step := fun (j : Fin N) (s : B j.castSucc) =>
    (⟨(hstep j s.val s.property).choose,
      (hstep j s.val s.property).choose_spec.1⟩ : B j.succ)
  let b : ∀ i, B i := Fin.induction b0 step
  refine ⟨fun i => (b i).val, fun i => (b i).property, ?_⟩
  intro j
  have hb : b j.succ = step j (b j.castSucc) := Fin.induction_succ b0 step j
  change R j (b j.castSucc).val (b j.succ).val
  rw [hb]
  exact (hstep j (b j.castSucc).val (b j.castSucc).property).choose_spec.2

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! A finite drift envelope admits a common small radius for every level of the word. -/

theorem exists_finite_drift_radius (a : ℝ) (ha : 0 ≤ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ a * ρ ^ 2 ≤ 1 / 8 := by
  let ρ := 1 / (4 * (a + 1))
  have hd : 0 < 4 * (a + 1) := by positivity
  have hr : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨ρ, hr, ?_, ?_⟩
  · exact (div_le_iff₀ hd).mpr (by nlinarith only [ha])
  · have he : a * ρ ^ 2 = a / (16 * (a + 1) ^ 2) := by
      dsimp [ρ]
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 16 * (a + 1) ^ 2)).mpr
    nlinarith only [ha, sq_nonneg a]

/-! Finite weighted sums of the three genuine energy budgets. -/

theorem finite_weighted_sum_add {ι : Type*} [Fintype ι] (c f g : ι → ℝ) :
    (∑ i, c i * (f i + g i)) = (∑ i, c i * f i) + ∑ i, c i * g i := by
  simp only [mul_add, Finset.sum_add_distrib]

theorem finite_three_energy_budget_sum {ι : Type*} [Fintype ι]
    (c f g h : ι → ℝ) :
    (∑ i, c i * (f i + 8 * g i + 2 * h i)) =
      (∑ i, c i * f i) + 8 * (∑ i, c i * g i) + 2 * (∑ i, c i * h i) := by
  calc
    _ = ∑ i, (c i * f i + 8 * (c i * g i) + 2 * (c i * h i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! Dimension-independent two-component Hilbert flux bounds for compact chart tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem piLp_two_norm_le_sum (u : PiLp 2 (fun _ : Fin 2 => E)) :
    ‖u‖ ≤ ‖u 0‖ + ‖u 1‖ := by
  have hs : ‖u‖ ^ 2 = ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 := by
    simpa only [Fin.sum_univ_two] using PiLp.norm_sq_eq_of_L2 _ u
  nlinarith only [hs, norm_nonneg u, norm_nonneg (u 0), norm_nonneg (u 1),
    mul_nonneg (norm_nonneg (u 0)) (norm_nonneg (u 1))]

def finiteMetricFlux (G : Matrix (Fin 2) (Fin 2) ℝ) (u : PiLp 2 (fun _ : Fin 2 => E)) :
    PiLp 2 (fun _ : Fin 2 => E) := WithLp.toLp 2 (fun k => ∑ j : Fin 2, G k j • u j)

theorem finiteMetricFlux_norm_le (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, |G k j| ≤ 5 / 4) (u : PiLp 2 (fun _ : Fin 2 => E)) :
    ‖finiteMetricFlux G u‖ ≤ 5 * ‖u‖ := by
  have hb k : ‖finiteMetricFlux G u k‖ ≤ (5 / 2 : ℝ) * ‖u‖ := by
    change ‖∑ j : Fin 2, G k j • u j‖ ≤ _
    calc
      _ ≤ ∑ j : Fin 2, ‖G k j • u j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 2, (5 / 4 : ℝ) * ‖u‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hG k j) (PiLp.norm_apply_le u j) (norm_nonneg _) (by norm_num)
      _ = _ := by simp; ring
  exact (piLp_two_norm_le_sum _).trans (by linarith only [hb 0, hb 1])

theorem scalar_vector_piLp_norm_le_two (v : Vec 2) :
    ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤ 2 * ‖v‖ := by
  have h0 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
  have h1 : ‖v 1‖ ≤ ‖v‖ := norm_le_pi_norm v 1
  exact (piLp_two_norm_le_sum _).trans (by change ‖v 0‖ + ‖v 1‖ ≤ _; linarith only [h0, h1])

theorem cutoff_gradient_piLp_norm_le
    (χ : Vec 2 → ℝ) (x : Vec 2) {η : ℝ} (hη : ‖fderiv ℝ χ x‖ ≤ η) :
    ‖(WithLp.toLp 2 (fun k : Fin 2 => fderiv ℝ χ x (basisVec k)) :
      PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤ 2 * η := by
  have hb k : ‖fderiv ℝ χ x (basisVec k)‖ ≤ η := by
    calc
      _ ≤ ‖fderiv ℝ χ x‖ * ‖basisVec k‖ := (fderiv ℝ χ x).le_opNorm _
      _ = ‖fderiv ℝ χ x‖ := by simp [basisVec, Pi.norm_single]
      _ ≤ η := hη
  exact (piLp_two_norm_le_sum _).trans (by
    change ‖fderiv ℝ χ x (basisVec 0)‖ + ‖fderiv ℝ χ x (basisVec 1)‖ ≤ _
    linarith only [hb 0, hb 1])

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Weighted

/-! Cauchy bounds for scalar cutoff fluxes against finite Hilbert gradients. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def scalarHilbertTensor (a : PiLp 2 (fun _ : Fin 2 => ℝ)) (e : E) :
    PiLp 2 (fun _ : Fin 2 => E) := WithLp.toLp 2 (fun i => a i • e)

theorem scalarHilbertTensor_norm (a : PiLp 2 (fun _ : Fin 2 => ℝ)) (e : E) :
    ‖scalarHilbertTensor a e‖ = ‖a‖ * ‖e‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2 _ _, mul_pow, PiLp.norm_sq_eq_of_L2 _ a,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [scalarHilbertTensor, norm_smul, mul_pow]

theorem finite_gradient_tensor_inner
    (a : PiLp 2 (fun _ : Fin 2 => ℝ)) (du : PiLp 2 (fun _ : Fin 2 => E)) (e : E) :
    inner ℝ du (scalarHilbertTensor a e) = inner ℝ (∑ i : Fin 2, a i • du i) e := by
  simp only [PiLp.inner_apply, scalarHilbertTensor, real_inner_smul_right,
    sum_inner, real_inner_smul_left]

end AVRegularity.Weighted
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.Weighted

/-! Finite factorial energy sums commute with their actual time integrals. -/

theorem intervalIntegral_weighted_sum {ι : Type*} [Fintype ι]
    (a b : ℝ) (c : ι → ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) volume a b) :
    (∑ i, c i * (∫ t in a..b, f i t)) =
      ∫ t in a..b, ∑ i, c i * f i t := by
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hf i).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i _
  exact (intervalIntegral.integral_const_mul (c i) (f i)).symm

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.Weighted

/-! Finite sums of genuine Lp representatives preserve their literal conditional source fields. -/

theorem finiteLp_conditional_sum_ae {J T E : Type*} [Fintype J]
    [MeasurableSpace T] [NormedAddCommGroup E] {μ : Measure T}
    (P : J → Prop) [DecidablePred P] (f : J → T → E) (hf : ∀ j, MemLp (f j) 2 μ) :
    (∑ j : J, if P j then (hf j).toLp (f j) else 0) =ᵐ[μ]
      fun x => ∑ j : J, if P j then f j x else 0 := by
  have ht : ∀ᵐ x ∂μ, ∀ j : J,
      (if P j then (hf j).toLp (f j) else (0 : Lp E 2 μ)) x =
        if P j then f j x else 0 := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : P j
    · filter_upwards [(hf j).coeFn_toLp] with x hx
      simpa only [hj, ite_true] using hx
    · filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
      simpa only [hj, ite_false, Pi.zero_apply] using hx
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun j => if P j then (hf j).toLp (f j) else 0), ht] with x hx ht
  rw [hx]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => ht j)

end AVRegularity.Weighted
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Finiteness of the energy norm controls every positive-mass component. -/

theorem finite_mass_energy_components {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A B : ι → ℝ≥0∞)
    (he : (∑ i, ENNReal.ofReal ((π i)⁻¹) * (A i + B i)) ^ (1 / 2 : ℝ) < ⊤) :
    ∀ i, A i ≠ ⊤ ∧ B i ≠ ⊤ := by
  have hs : (∑ i, ENNReal.ofReal ((π i)⁻¹) * (A i + B i)) < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp he
  intro i
  have hi : ENNReal.ofReal ((π i)⁻¹) * (A i + B i) < ⊤ :=
    lt_of_le_of_lt (Finset.single_le_sum
      (f := fun j => ENNReal.ofReal ((π j)⁻¹) * (A j + B j))
      (fun _ _ => bot_le) (Finset.mem_univ i)) hs
  have hn : ENNReal.ofReal ((π i)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hπ i))).ne'
  have hab : A i + B i ≠ ⊤ := by
    intro hh
    rw [hh, ENNReal.mul_top hn] at hi
    exact (lt_irrefl ⊤) hi
  exact ENNReal.add_ne_top.mp hab

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.Weighted

/-! Finite sums of actual L2 time readouts retain their literal almost-everywhere representatives. -/

variable {T X E ι : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [NormedAddCommGroup E] [Fintype ι]

theorem exists_finite_time_l2_readout_sum (μ : Measure T) (ν : Measure X)
    (f : ι → T → X → E)
    (hf : ∀ i, ∃ R : T → Lp E 2 ν, MemLp R 2 μ ∧ ∀ᵐ t ∂μ, R t =ᵐ[ν] f i t) :
    ∃ R : T → Lp E 2 ν, MemLp R 2 μ ∧ ∀ᵐ t ∂μ,
      R t =ᵐ[ν] fun x => ∑ i, f i t x := by
  classical
  choose R hR hRae using hf
  refine ⟨fun t => ∑ i, R i t, memLp_finsetSum Finset.univ (fun i _ => hR i), ?_⟩
  filter_upwards [ae_all_iff.mpr hRae] with t ht
  apply (Lp.coeFn_finsetSum _ _).trans
  have hs := eventuallyEq_sum (s := Finset.univ) (fun i _ => ht i)
  filter_upwards [hs] with x hx
  simpa only [Finset.sum_apply] using hx

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! Polynomial growth degrees add under multiplication of classical scalar jets. -/

theorem growing_scalar_jet_product_bound (J p q : ℕ) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (J : ℕ) f) (hg : ContDiff ℝ (J : ℕ) g)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfb : ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A * (1 + ‖x‖) ^ p)
    (hgb : ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B * (1 + ‖x‖) ^ q) :
    ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (fun x => f x * g x) x‖ ≤
      ((∑ i ∈ Finset.range (J + 1), (J.choose i : ℝ)) * A * B) * (1 + ‖x‖) ^ (p + q) := by
  intro j hj x
  have hm := norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast hj)
  have hs : (∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖) ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * A * B * (1 + ‖x‖) ^ (p + q) := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hiJ : i ≤ J := by have := Finset.mem_range.mp hi; omega
    calc
      _ ≤ (j.choose i : ℝ) * (A * (1 + ‖x‖) ^ p) * (B * (1 + ‖x‖) ^ q) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hfb i hiJ x) (by positivity))
          (hgb (j - i) (Nat.le_trans (Nat.sub_le _ _) hj) x)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) ≤
      ∑ i ∈ Finset.range (J + 1), (J.choose i : ℝ) := by
    exact_mod_cast (show (∑ i ∈ Finset.range (j + 1), j.choose i) ≤
      ∑ i ∈ Finset.range (J + 1), J.choose i from by
        rw [Nat.sum_range_choose, Nat.sum_range_choose]
        exact Nat.pow_le_pow_right (by omega) hj)
  exact (hm.trans hs).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchoose hA) hB) (by positivity))

end AVRegularity.Weighted
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.Weighted

/-! A retained half-production bound controls the separate supremum and full production. -/

theorem half_production_supremum_le {T : Type*} (I : Set T) (b : T) (hb : b ∈ I)
    (e : T → ℝ≥0∞) (D R : ℝ≥0∞)
    (h : ∀ t ∈ I, e t + ENNReal.ofReal (1 / 2 : ℝ) * D ≤ R) :
    (⨆ t ∈ I, e t) + D ≤ 3 * R := by
  have he : (⨆ t ∈ I, e t) ≤ R := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact le_self_add.trans (h t ht)
  have hd : D ≤ 2 * R := by
    have hh := mul_le_mul' (le_rfl : (2 : ℝ≥0∞) ≤ 2) (le_add_self.trans (h b hb))
    have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    simpa only [← mul_assoc, htwo, one_mul] using hh
  exact (add_le_add he hd).trans_eq (by ring)

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Inner-product bounds with explicit nonnegative norm budgets. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem abs_inner_le_budgets (x y : H) {A B : ℝ} (hx : ‖x‖ ≤ A) (hy : ‖y‖ ≤ B) :
    |inner ℝ x y| ≤ A * B :=
  (abs_real_inner_le_norm x y).trans
    (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx))

theorem inner_le_budgets (x y : H) {A B : ℝ} (hx : ‖x‖ ≤ A) (hy : ‖y‖ ≤ B) :
    inner ℝ x y ≤ A * B := (le_abs_self _).trans (abs_inner_le_budgets x y hx hy)

theorem neg_inner_le_budgets (x y : H) {A B : ℝ} (hx : ‖x‖ ≤ A) (hy : ‖y‖ ≤ B) :
    -inner ℝ x y ≤ A * B := (neg_le_abs _).trans (abs_inner_le_budgets x y hx hy)

end AVRegularity.Weighted
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.Weighted

/-! Convert the time budgets on a closed solution window to interval integrals. -/

theorem intervalIntegrable_of_integrable_Icc {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : Integrable f (volume.restrict (Icc a b))) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff, uIoc_of_le hab]
  exact hf.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

/-! Integrating the two actual scalar source budgets requires only their true time integrability. -/

theorem interval_residual_source_budgets {a b c ν : ℝ} {r p d f : ℝ → ℝ}
    (hab : a ≤ b) (hr : IntervalIntegrable r volume a b)
    (hp : IntervalIntegrable p volume a b) (hd : IntervalIntegrable d volume a b)
    (hf : IntervalIntegrable f volume a b)
    (h : ∀ᵐ t ∂volume.restrict (Icc a b),
      r t ≤ (ν / 4) * d t ∧ p t ≤ 2 * (c * d t) + 2 * f t) :
    (∫ t in a..b, r t) ≤ (ν / 4) * (∫ t in a..b, d t) ∧
      (∫ t in a..b, p t) ≤ 2 * (c * (∫ t in a..b, d t)) + 2 * (∫ t in a..b, f t) := by
  constructor
  · have hi := intervalIntegral.integral_mono_ae_restrict hab hr (hd.const_mul (ν / 4))
      (h.mono (fun _ ht => ht.1))
    rw [intervalIntegral.integral_const_mul] at hi
    exact hi
  · have hc := (hd.const_mul c).const_mul 2
    have hg := hf.const_mul 2
    have hi := intervalIntegral.integral_mono_ae_restrict hab hp (hc.add hg)
      (h.mono (fun _ ht => ht.2))
    rw [intervalIntegral.integral_add hc hg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
    exact hi

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Weighted

/-! Finite joint regularity supplies the reserved partial derivative fields. -/

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem joint_partialFDeriv_right_contDiff (n : ℕ) (f : P × E → F)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ (n : ℕ) (fun p : P × E => fderiv ℝ (fun x => f (p.1, x)) p.2) := by
  let D : P × E → E →L[ℝ] F := fun p =>
    (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ P E)
  have hD : ContDiff ℝ (n : ℕ) D :=
    (hf.fderiv_right (by norm_cast)).clm_comp contDiff_const
  have he p : fderiv ℝ (fun x => f (p.1, x)) p.2 = D p := by
    rcases p with ⟨p, x⟩
    have ht := (hf.differentiable (by norm_cast) (p, x)).hasFDerivAt
    have hs := ht.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) p x)
    exact hs.fderiv
  simpa only [he] using hD

theorem joint_partialIteratedFDeriv_right_contDiff (n r : ℕ) (f : P × E → F)
    (hf : ContDiff ℝ (n + r : ℕ) f) :
    ContDiff ℝ (n : ℕ)
      (fun p : P × E => iteratedFDeriv ℝ r (fun x => f (p.1, x)) p.2) := by
  induction r generalizing n with
  | zero =>
    have hh := (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp hf
    simpa only [Nat.add_zero, iteratedFDeriv_zero_eq_comp, Function.comp_def] using hh
  | succ r ih =>
    have hprev := ih (n + 1) (by simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hf)
    have hd := joint_partialFDeriv_right_contDiff n _ hprev
    have hh := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => E) F).symm.contDiff.comp hd
    simpa only [Nat.succ_eq_add_one, iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using hh

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.Weighted

/-! Norm-product Cauchy-Schwarz for genuine spatial L2 fields and their finite arrays. -/

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] {μ : Measure T}

theorem L2_norm_product_integral_le (g u : Lp E 2 μ) :
    (∫ x, ‖g x‖ * ‖u x‖ ∂μ) ≤ ‖g‖ * ‖u‖ := by
  let G := (Lp.memLp g).norm.toLp (fun x => ‖g x‖)
  let U := (Lp.memLp u).norm.toLp (fun x => ‖u x‖)
  have hp : inner ℝ G U = ∫ x, ‖g x‖ * ‖u x‖ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memLp g).norm.coeFn_toLp, (Lp.memLp u).norm.coeFn_toLp]
      with x hg hu
    change inner ℝ (G x) (U x) = _
    rw [hg, hu]
    simp only [Real.inner_apply]
  have hG : ‖G‖ = ‖g‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable g), Lp.norm_def]
  have hU : ‖U‖ = ‖u‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable u), Lp.norm_def]
  rw [← hp, ← hG, ← hU]
  exact (le_abs_self _).trans (abs_real_inner_le_norm G U)

theorem finiteL2_norm_product_integral_le {J : Type*} [Fintype J]
    (g u : PiLp 2 (fun _ : J => Lp E 2 μ)) :
    (∑ w : J, ∫ x, ‖g w x‖ * ‖u w x‖ ∂μ) ≤ ‖g‖ * ‖u‖ := by
  let G : PiLp 2 (fun _ : J => ℝ) := WithLp.toLp 2 (fun w => ‖g w‖)
  let U : PiLp 2 (fun _ : J => ℝ) := WithLp.toLp 2 (fun w => ‖u w‖)
  have hp : inner ℝ G U = ∑ w : J, ‖g w‖ * ‖u w‖ := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro w _
    change inner ℝ ‖g w‖ ‖u w‖ = _
    simp only [Real.inner_apply]
  have hG : ‖G‖ = ‖g‖ := by
    apply (sq_eq_sq₀ (norm_nonneg G) (norm_nonneg g)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro w _
    change ‖‖g w‖‖ ^ 2 = _
    rw [Real.norm_of_nonneg (norm_nonneg _)]
  have hU : ‖U‖ = ‖u‖ := by
    apply (sq_eq_sq₀ (norm_nonneg U) (norm_nonneg u)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro w _
    change ‖‖u w‖‖ ^ 2 = _
    rw [Real.norm_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ ∑ w : J, ‖g w‖ * ‖u w‖ :=
      Finset.sum_le_sum (fun w _ => L2_norm_product_integral_le (g w) (u w))
    _ = inner ℝ G U := hp.symm
    _ ≤ |inner ℝ G U| := le_abs_self _
    _ ≤ ‖G‖ * ‖U‖ := abs_real_inner_le_norm G U
    _ = _ := by rw [hG, hU]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Weighted

/-! Every derivative of a linear coordinate has at most linear polynomial growth. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem linear_iteratedFDeriv_growth (L : E →L[ℝ] F) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j L x‖ ≤ ‖L‖ * (1 + ‖x‖) := by
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg L))
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L = fun _ => L := by funext y; exact L.fderiv
    rw [he]
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact le_mul_of_one_le_right (norm_nonneg L) (by linarith [norm_nonneg x])
    | succ j =>
      rw [iteratedFDeriv_succ_const]
      simpa only [Pi.zero_apply, norm_zero] using mul_nonneg (norm_nonneg L)
        (by linarith [norm_nonneg x] : 0 ≤ 1 + ‖x‖)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
namespace AVRegularity.Weighted

/-! A finite sum of actual Lp carriers has the sum of their prescribed readouts. -/

variable {X J E : Type*} [MeasurableSpace X] [Fintype J] [NormedAddCommGroup E]

theorem lp_finite_sum_readout {μ : Measure X} (U : J → Lp E 2 μ) (f : J → X → E)
    (h : ∀ j, U j =ᵐ[μ] f j) : (∑ j, U j) =ᵐ[μ] fun x => ∑ j, f j x := by
  have hs := Lp.coeFn_finsetSum Finset.univ U
  have ht := ae_all_iff.mpr h
  filter_upwards [hs, ht] with x hx hf
  rw [hx, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hf j)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.Weighted

/-! The literal pointwise norm as a contraction of spatial L2 carriers. -/

section
variable {E : Type*} [NormedAddCommGroup E]

def planeLpNorm (u : Lp E 2 (volume : Measure (Fin 2 → ℝ))) :
    Lp ℝ 2 (volume : Measure (Fin 2 → ℝ)) :=
  (lipschitzWith_one_norm (E := E)).compLp (by simp) u

theorem planeLpNorm_ae (u : Lp E 2 (volume : Measure (Fin 2 → ℝ))) :
    planeLpNorm u =ᵐ[volume] fun x => ‖u x‖ :=
  (lipschitzWith_one_norm (E := E)).coeFn_compLp (by simp) u

theorem planeLpNorm_memLp {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (u : T → Lp E 2 (volume : Measure (Fin 2 → ℝ))) (hu : MemLp u 2 μ) :
    MemLp (fun t => planeLpNorm (u t)) 2 μ := by
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  have h := (lipschitzWith_one_norm (E := E)).lipschitzWith_compLp (by simp)
    (p := (2 : ENNReal)) (μ := (volume : Measure (Fin 2 → ℝ)))
  exact h.comp_memLp (by simp only [LipschitzWith.compLp_zero]) hu
end

/-! Almost-everywhere analytic bounds can be enforced on a measurable set of full measure. -/

theorem exists_measurable_good_times {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (P : T → Prop) (hP : ∀ᵐ t ∂μ, P t) :
    ∃ s : Set T, MeasurableSet s ∧ (∀ t ∈ s, P t) ∧ ∀ᵐ t ∂μ, t ∈ s := by
  classical
  let bad : Set T := {t | ¬ P t}
  have hb : μ bad = 0 := ae_iff.mp hP
  refine ⟨(toMeasurable μ bad)ᶜ, (measurableSet_toMeasurable μ bad).compl, ?_, ?_⟩
  · intro t ht
    by_contra hn
    exact ht (subset_toMeasurable μ bad hn)
  · exact compl_mem_ae_iff.mpr (by rw [measure_toMeasurable, hb])

end AVRegularity.Weighted
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Weighted

/-! Subtracting the identity leaves every positive derivative unchanged and adds a finite zeroth envelope. -/

theorem scalar_iteratedDerivative_sub_const_bound (f : Vec 2 → ℝ) (j : ℕ)
    (hf : ContDiff ℝ (j : ℕ) f) (c M : ℝ) (hc : |c| ≤ 1)
    (x : Vec 2) (hb : ‖iteratedFDeriv ℝ j f x‖ ≤ M) :
    ‖iteratedFDeriv ℝ j (fun y => f y - c) x‖ ≤ |M| + 1 := by
  by_cases hj : j = 0
  · subst j
    rw [norm_iteratedFDeriv_zero] at hb ⊢
    exact (norm_sub_le _ _).trans (add_le_add (hb.trans (le_abs_self M))
      (by simpa only [Real.norm_eq_abs] using hc))
  · have he : (fun y => f y - c) = f - fun _ => c := rfl
    rw [he, iteratedFDeriv_sub_apply hf.contDiffAt contDiffAt_const,
      iteratedFDeriv_const_of_ne hj]
    simp only [Pi.zero_apply, sub_zero]
    exact (hb.trans (le_abs_self M)).trans (le_add_of_nonneg_right (by norm_num))

theorem identityMatrix_entry_abs_le_one (k j : Fin 2) :
    |(1 : Matrix (Fin 2) (Fin 2) ℝ) k j| ≤ 1 := by
  fin_cases k <;> fin_cases j <;> norm_num

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Exact regrouping of the identity diffusion and metric-deviation flux. -/

/-- Adding the identity gradient to the deviation flux gives the full metric gradient. -/
theorem metricDeviation_flux_add {E : Type*} [AddCommGroup E] [Module ℝ E]
    (M : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → E) (k : Fin 2) :
    u k + (∑ j : Fin 2, (M - 1) k j • u j) = ∑ j : Fin 2, M k j • u j := by
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have hI : (∑ j : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℝ) k j • u j) = u k := by
    simp [Matrix.one_apply]
  rw [hI]
  abel

/-- The identity and metric-deviation terms of the weak identity regroup exactly:
`-(u, ∂φ) - ((M - 1)u + F, ∂φ) = -(Mu + F, ∂φ)`. -/
theorem metricDeviation_weak_pairing {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Matrix (Fin 2) (Fin 2) ℝ) (u dφ F : Fin 2 → E) :
    -(∑ k : Fin 2, inner ℝ (u k) (dφ k))
      - (∑ k : Fin 2, inner ℝ ((∑ j : Fin 2, (M - 1) k j • u j) + F k) (dφ k)) =
      -(∑ k : Fin 2, inner ℝ ((∑ j : Fin 2, M k j • u j) + F k) (dφ k)) := by
  have he (k : Fin 2) : inner ℝ ((∑ j : Fin 2, M k j • u j) + F k) (dφ k) =
      inner ℝ (u k) (dφ k) +
        inner ℝ ((∑ j : Fin 2, (M - 1) k j • u j) + F k) (dφ k) := by
    rw [← metricDeviation_flux_add M u k, add_assoc, inner_add_left]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  ring

end AVRegularity.Weighted
end
end

section
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace AVRegularity.Weighted

/-! The retained real energy estimate has its exact nonnegative-integral form. -/

theorem ofReal_intervalIntegral_nonneg {a b : ℝ} (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : Integrable f (volume.restrict (Icc a b))) (hf0 : ∀ t, 0 ≤ f t) :
    ENNReal.ofReal (∫ t in a..b, f t) = ∫⁻ t in Icc a b, ENNReal.ofReal (f t) := by
  rw [intervalIntegral.integral_of_le hab,
    ofReal_integral_eq_lintegral_ofReal
      (hf.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
      (Filter.Eventually.of_forall hf0), restrict_Ioc_eq_restrict_Icc]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace AVRegularity.Weighted

/-! Difference quotients give parameter measurability of classical directional derivatives.
The argument uses difference quotients along spatial slices. -/

variable {T E F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

theorem parameter_fderiv_apply_measurable (f : T → E → F)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hd : ∀ t, Differentiable ℝ (f t)) (x e : E) :
    Measurable (fun t => fderiv ℝ (f t) x e) := by
  let a : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have ha_pos (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [Function.comp_def, a] using
      (tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1)
  have hane : Tendsto a atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ha, ?_⟩
    filter_upwards with n
    simpa only [Function.comp_def, Set.mem_compl_iff, Set.mem_singleton_iff] using
      (ha_pos n).ne'
  apply measurable_of_tendsto_metrizable
    (f := fun n t => (a n)⁻¹ • (f t (x + a n • e) - f t x))
    (fun n => ((hm (x + a n • e)).sub (hm x)).const_smul ((a n)⁻¹))
  apply tendsto_pi_nhds.mpr
  intro t
  have hline : HasDerivAt (fun r : ℝ => x + r • e) e 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const e).const_add x
  have hg : HasDerivAt (fun r : ℝ => f t (x + r • e)) (fderiv ℝ (f t) x e) 0 := by
    have hf : HasFDerivAt (f t) (fderiv ℝ (f t) x) (x + (0 : ℝ) • e) := by
      simpa only [zero_smul, add_zero] using (hd t x).hasFDerivAt
    exact hf.comp_hasDerivAt 0 hline
  simpa only [Function.comp_def, zero_smul, add_zero, zero_add] using hg.tendsto_slope_zero.comp hane

theorem parameter_iteratedFDeriv_apply_measurable (f : T → E → F)
    (hm : ∀ x, Measurable (fun t => f t x)) (K j : ℕ)
    (hf : ∀ t, ContDiff ℝ (K : ℕ) (f t)) (hj : j ≤ K)
    (x : E) (e : Fin j → E) :
    Measurable (fun t => iteratedFDeriv ℝ j (f t) x e) := by
  induction j generalizing x with
  | zero => simpa only [iteratedFDeriv_zero_apply] using hm x
  | succ j ih =>
    have hdiff (t : T) : Differentiable ℝ (iteratedFDeriv ℝ j (f t)) :=
      (hf t).differentiable_iteratedFDeriv (by exact_mod_cast (show j < K by omega))
    have hediff (t : T) : Differentiable ℝ
        (fun y => iteratedFDeriv ℝ j (f t) y (Fin.tail e)) :=
      fun y => (hdiff t y).continuousMultilinear_apply_const (Fin.tail e)
    have heq (t : T) := (hdiff t x).iteratedFDeriv_succ_apply_left' (m := e)
    simp_rw [heq]
    exact parameter_fderiv_apply_measurable
      (fun t y => iteratedFDeriv ℝ j (f t) y (Fin.tail e))
      (fun y => ih (by omega) y (Fin.tail e)) hediff x (e 0)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open AVenhance.Infra.Torus AVenhance.Infra.Classical
namespace AVRegularity.Weighted

/-! A continuous periodic scalar field of zero cell energy vanishes pointwise. -/

theorem periodic_scalar_zero_of_cell_square_integral (q : Vec 2 → ℝ)
    (hq : Continuous q) (hp : AVenhance.IsZ2Periodic q)
    (he : (∫ x in AVenhance.unitCube, q x ^ 2) = 0) : ∀ x, q x = 0 := by
  have hi : IntegrableOn (fun x => q x ^ 2) AVenhance.unitCube := by
    have hh := PeriodicCalculus.continuous_integrableOn_unitCell (hq.pow 2)
    exact (integrableOn_congr_set_ae unitCell_ae_eq_unitCube).mp hh
  have hae : q =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
    have hh := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (q x)) hi).mp he
    filter_upwards [hh] with x hx
    exact sq_eq_zero_iff.mp hx
  have hopen : IsOpen AVenhance.unitCube :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have heq := Measure.eqOn_open_of_ae_eq hae hopen hq.continuousOn continuous_zero.continuousOn
  have hcl := heq.closure hq continuous_zero
  intro x
  let y := unitTorusRepresentative 2 (toUnitTorus 2 x)
  have hy : y ∈ closure AVenhance.unitCube := by
    rw [AVenhance.unitCube, closure_pi_set]
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    intro i
    have hh := (AddCircle.equivIoc (1 : ℝ) 0 (toUnitTorus 2 x i)).property
    exact ⟨hh.1.le, by simpa only [y, unitTorusRepresentative, zero_add] using! hh.2⟩
  have hz : q y = 0 := hcl hy
  obtain ⟨k, hk⟩ := Basic.representative_int_translate x
  have hpy : q y = q x := by
    rw [show y = x + intVector k from hk]
    exact hp k x
  exact hpy.symm.trans hz

end AVRegularity.Weighted
end
end
