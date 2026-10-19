-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.TimeEnergy
public import AVRegularity.CycleEvolution.CompatibleTraceLpCarrier
public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
import AVenhance.Infra.ODE.Linear.Gronwall
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Temporal L² indicator restriction in an abstract normed carrier. -/

theorem cellTime_memLp_indicator {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ}
    (s : Set ℝ) (hs : MeasurableSet s) (w : ℝ → E) (hw : MemLp w 2 μ) :
    MemLp (s.indicator w) 2 μ :=
  hw.indicator hs

/-! Integrability of temporal Hilbert pairings of L² curves. -/

theorem cellTime_inner_intervalIntegrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (u w : ℝ → H) (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hw : MemLp w 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun r => inner ℝ (u r) (w r)) volume s t := by
  have hi := L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hw.toLp w)
  have hp : Integrable (fun r => inner ℝ (u r) (w r)) (volume.restrict (Icc a b)) := by
    apply hi.congr
    filter_upwards [hu.coeFn_toLp, hw.coeFn_toLp] with r hur hwr
    rw [hur, hwr]
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hst]
  exact hp.mono_measure (Measure.restrict_mono
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open Filter
open scoped Topology
namespace AVRegularity.CycleEvolution

/-! Weak convergence with strongly converging continuous test functionals. -/

/-- Uniformly bounded weakly convergent vectors may be tested with norm-convergent functionals. -/
theorem cellWeak_eval_perturbed_test {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (limit : E) (R : ℝ) (hb : ∀ n, ‖u n‖ ≤ R)
    (hw : ∀ ell : E →L[ℝ] ℝ, Tendsto (fun n => ell (u n)) atTop (𝓝 (ell limit)))
    (ell : ℕ → E →L[ℝ] ℝ) (test : E →L[ℝ] ℝ) (ht : Tendsto ell atTop (𝓝 test)) :
    Tendsto (fun n => ell n (u n)) atTop (𝓝 (test limit)) := by
  have hnorm : Tendsto (fun n => ‖ell n - test‖ * R) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_mul] using (ht.sub (tendsto_const_nhds (x := test))).norm.mul_const R
  have hd : Tendsto (fun n => (ell n - test) (u n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hnorm
    intro n
    exact ((ell n - test).le_opNorm (u n)).trans
      (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _))
  have hsum := (hw test).add hd
  simpa only [sub_apply, add_sub_cancel, add_zero] using hsum

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Abstract-real polynomial bounds for the homogeneous word operator. -/

theorem word_homogeneous_cov_budget_le (R c q S δ : ℝ)
    (hR : 0 < R) (hc : 0 ≤ c) (hq : 0 ≤ q) (hS : 1 ≤ S) (hδ : δ ≤ S) :
    144 + 16 * c ^ 2 * (δ + 1) * (q / R) ^ 2 + 4 * c ^ 2 * δ * q ^ 2 ≤
      (12 + c * Real.sqrt (32 / R ^ 2 + 4) * (Real.sqrt S * q)) ^ 2 := by
  have hS0 : 0 ≤ S := by linarith
  have hd : 0 ≤ 32 / R ^ 2 + 4 := by positivity
  have hx : 0 ≤ Real.sqrt S * q := mul_nonneg (Real.sqrt_nonneg _) hq
  have hδ1 : δ + 1 ≤ 2 * S := by linarith
  have hbudget : 144 + 16 * c ^ 2 * (δ + 1) * (q / R) ^ 2 + 4 * c ^ 2 * δ * q ^ 2 ≤
      144 + 32 * c ^ 2 * S * (q / R) ^ 2 + 4 * c ^ 2 * S * q ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hδ1 (by positivity : 0 ≤ 16 * c ^ 2 * (q / R) ^ 2)
    have h2 := mul_le_mul_of_nonneg_right hδ (by positivity : 0 ≤ 4 * c ^ 2 * q ^ 2)
    nlinarith
  have he : 144 + 32 * c ^ 2 * S * (q / R) ^ 2 + 4 * c ^ 2 * S * q ^ 2 =
      144 + (c * Real.sqrt (32 / R ^ 2 + 4) * (Real.sqrt S * q)) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hd, Real.sq_sqrt hS0]
    field_simp
    ring
  have hn : 0 ≤ c * Real.sqrt (32 / R ^ 2 + 4) * (Real.sqrt S * q) := by positivity
  exact hbudget.trans (he.le.trans (by nlinarith))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Metric
namespace AVRegularity.CycleEvolution

/-! Iterating the Banach-domain Schwarz estimate for analytic Fréchet derivatives. -/

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem analytic_ball_iterated_derivative_step {f : V → E} {x : V} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (ball x R)) (n : ℕ)
    (hb : ∀ y ∈ ball x R, ‖iteratedFDeriv ℂ n f y‖ ≤ M) :
    ‖iteratedFDeriv ℂ (n + 1) f x‖ ≤ 2 * M / R := by
  rw [← norm_fderiv_iteratedFDeriv]
  exact complex_ball_fderiv_norm_le hR (hf.iteratedFDeriv n).differentiableOn hb

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Metric Set
namespace AVRegularity.CycleEvolution

/-! Vanishing of the linear Taylor coefficient gives the required linear frequency gain. -/

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem analytic_ball_first_derivative_gain {f : V → E} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hb : ∀ y ∈ ball 0 R, ‖f y‖ ≤ M) (hz : fderiv ℂ f 0 = 0)
    (x : V) (hx : x ∈ ball 0 (R / 2)) :
    ‖fderiv ℂ f x‖ ≤ (8 * M / R ^ 2) * ‖x‖ := by
  have hhalf : 0 < R / 2 := half_pos hR
  have hsub : ball (0 : V) (R / 2) ⊆ ball 0 R := ball_subset_ball (by linarith)
  have hbound y (hy : y ∈ ball (0 : V) (R / 2)) : ‖fderiv ℂ f y‖ ≤ 4 * M / R := by
    have hi : ball y (R / 2) ⊆ ball 0 R := by
      intro z hz'
      rw [mem_ball] at hy hz' ⊢
      have ht := dist_triangle z y 0
      linarith
    have hd := complex_ball_fderiv_norm_le hhalf (hf.mono hi).differentiableOn
      (fun z hz' => hb z (hi hz'))
    apply hd.trans_eq
    field_simp
    ring
  have hmap : MapsTo (fderiv ℂ f) (ball 0 (R / 2))
      (closedBall (fderiv ℂ f 0) (4 * M / R)) := by
    intro y hy
    rw [mem_closedBall, hz, dist_zero_right]
    exact hbound y hy
  have hd := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    (hf.fderiv.mono hsub).differentiableOn hmap hx
  rw [hz, dist_zero_right, dist_zero_right] at hd
  apply hd.trans_eq
  field_simp
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Pascal identities for each coordinate of a rectangular derivative convolution. -/

/-- Differentiation in the first coordinate of a two-coordinate convolution. -/
theorem binomialConvolution_rectangle_first {M : Type*} [AddCommMonoid M]
    (u : ℕ → ℕ → ℕ → ℕ → M) (n m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (n + 1),
      (n.choose i * m.choose j) • u (i + 1) j (n - i) (m - j)) +
    (∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (n + 1),
      (n.choose i * m.choose j) • u i j (n - i + 1) (m - j)) =
    ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (n + 2),
      ((n + 1).choose i * m.choose j) • u i j (n + 1 - i) (m - j) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [← smul_smul] using
    binomialConvolution_step (fun i k => m.choose j • u i j k (m - j)) n

/-- Differentiation in the second coordinate of a two-coordinate convolution. -/
theorem binomialConvolution_rectangle_second {M : Type*} [AddCommMonoid M]
    (u : ℕ → ℕ → ℕ → ℕ → M) (n m : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      (n.choose i * m.choose j) • u i (j + 1) (n - i) (m - j)) +
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      (n.choose i * m.choose j) • u i j (n - i) (m - j + 1)) =
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 2),
      (n.choose i * (m + 1).choose j) • u i j (n - i) (m + 1 - j) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun z : M => n.choose i • z)
    (binomialConvolution_step (fun j k => u i j (n - i) k) m)
  simpa only [smul_add, Finset.smul_sum, ← smul_smul] using h

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.CycleEvolution

/-! Complex scalar closure of the actual real-tested periodic weak-jet identity. -/

/-- Moving a complex scalar to the real-inner-product test uses its adjoint. -/
theorem cellComplex_real_inner_smul (e z u : ℂ) :
    inner ℝ e (z • u) = inner ℝ (star z • e) u := by
  simp only [real_inner_eq_re_inner, inner_smul_right, inner_smul_left, starRingEnd_apply, star_star]

/-- Periodic raw weak jets are closed under arbitrary complex scalar multiplication. -/
theorem cellPeriodicWeakJet_complex_smul {K : ℕ} {D : RawJet2 K ℂ}
    (hD : HasPeriodicOrderedWeakJet D) (z : ℂ) :
    HasPeriodicOrderedWeakJet (z • D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a n x
    change z • D a (x + AVenhance.latticeShift n) = z • D a x
    rw [hD.1 a n x]
  · intro a
    exact (hD.2.1 a).const_smul z
  · intro j w i e φ hφ hc hsub
    simpa only [Pi.smul_apply, cellComplex_real_inner_smul] using
      hD.2.2 j w i (star z • e) φ hφ hc hsub

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Numerical trace and gradient budgets for the mean-zero cell inverse. -/

/-- Scalar source and trace budgets control the two energy-norm components. -/
theorem scalar_pair_energy_budgets {B R L : ℝ} (hR : R ≤ 3 * B) (hB : B ≤ 8 * L ^ 2) :
    R ≤ 24 * L ^ 2 ∧ 2 * R + 2 * B ≤ 64 * L ^ 2 := by
  constructor <;> linarith

/-- The numerical unit-cell decay rate yields universal trace and gradient budgets. -/
theorem cellInverse_numerical_budgets {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    let B := 4 * x ^ 2 + 8 * y ^ 2
    let R := B / (1 - Real.exp (-(Real.pi ^ 2))) + B
    R ≤ 24 * (x + y) ^ 2 ∧ 2 * R + 2 * B ≤ 64 * (x + y) ^ 2 := by
  exact scalar_pair_energy_budgets
    (scalar_inverse_budget_le (by nlinarith [Real.pi_gt_three]) (by positivity))
    (scalar_cell_source_budget_le hx hy)

/-- A squared trace bound yields the convenient integer multiple of the source norm. -/
theorem scalar_trace_le_five {r L : ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hsq : r ^ 2 ≤ 24 * L ^ 2) : r ≤ 5 * L := by
  nlinarith

/-- The initial L² norm and source budget control finite-past trace and gradient components. -/
theorem scalar_finite_past_energy_budgets {B R L z : ℝ} (hL : 0 ≤ L) (hz : 0 ≤ z)
    (hR : R ≤ z ^ 2 + 3 * B) (hB : B ≤ 8 * L ^ 2) :
    R ≤ 25 * (L + z) ^ 2 ∧ 2 * R + 2 * B ≤ 81 * (L + z) ^ 2 := by
  constructor <;> nlinarith [mul_nonneg hL hz, sq_nonneg L, sq_nonneg z]

/-- The actual finite-past construction's budgets have universal bounds including the initial norm. -/
theorem cellFinitePast_numerical_budgets {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    let B := 4 * x ^ 2 + 8 * y ^ 2
    let R := z ^ 2 + B / (1 - Real.exp (-(Real.pi ^ 2))) + B
    R ≤ 25 * (x + y + z) ^ 2 ∧ 2 * R + 2 * B ≤ 81 * (x + y + z) ^ 2 := by
  have hgeo := scalar_inverse_budget_le
    (show 1 ≤ Real.pi ^ 2 by nlinarith [Real.pi_gt_three])
    (show 0 ≤ 4 * x ^ 2 + 8 * y ^ 2 by positivity)
  apply scalar_finite_past_energy_budgets (add_nonneg hx hy) hz _ (scalar_cell_source_budget_le hx hy)
  calc
    _ = z ^ 2 + ((4 * x ^ 2 + 8 * y ^ 2) / (1 - Real.exp (-(Real.pi ^ 2))) +
      (4 * x ^ 2 + 8 * y ^ 2)) := by ring
    _ ≤ _ := add_le_add le_rfl hgeo

/-- A squared finite-past trace bound yields a simple multiple of the total data norm. -/
theorem scalar_trace_le_five_of_sq {r L : ℝ} (_hr : 0 ≤ r) (hL : 0 ≤ L)
    (hsq : r ^ 2 ≤ 25 * L ^ 2) : r ≤ 5 * L := by
  nlinarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Linear trace and spatial-state readouts, and construction from compatible actual representatives. -/

variable {X V H : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

def compatibleTraceLpOf (μ : Measure X) [IsFiniteMeasure μ] (ι : V →L[ℂ] H)
    (u : C(X, H)) (z : X → V) (hz : MemLp z 2 μ)
    (ha : ∀ᵐ x ∂μ, u x = ι (z x)) : CompatibleTraceLp μ ι :=
  ⟨(u, hz.toLp z), by
    apply (compatibleTraceLp_mem_iff μ ι _).mpr
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ) u,
      ι.coeFn_compLpL (hz.toLp z), hz.coeFn_toLp, ha] with x hu hi hz' ha'
    rw [hu, hi, hz']
    exact ha'⟩

def compatibleTraceLpTraceCLM (μ : Measure X) [IsFiniteMeasure μ] (ι : V →L[ℂ] H) :
    CompatibleTraceLp μ ι →L[ℂ] C(X, H) :=
  (ContinuousLinearMap.fst ℂ C(X, H) (Lp V 2 μ)).comp (compatibleTraceLpSpace μ ι).subtypeL

def compatibleTraceLpStateCLM (μ : Measure X) [IsFiniteMeasure μ] (ι : V →L[ℂ] H) :
    CompatibleTraceLp μ ι →L[ℂ] Lp V 2 μ :=
  (ContinuousLinearMap.snd ℂ C(X, H) (Lp V 2 μ)).comp (compatibleTraceLpSpace μ ι).subtypeL

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Every argument in a canonical frequency derivative word has unit norm. -/

theorem complexFrequencyCanonicalWord_norm (p : ℕ × ℕ) (i : Fin (p.1 + p.2)) :
    ‖complexFrequencyCanonicalWord p i‖ = 1 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [complexFrequencyCanonicalWord, Pi.norm_single]

/-! Two-coordinate polynomial increment with total degree and the full radius power retained. -/

theorem complex_mixed_power_increment_bound (z0 z1 w0 w1 : ℂ) (M D : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hz0 : ‖z0‖ ≤ M) (hz1 : ‖z1‖ ≤ M) (hw0 : ‖w0‖ ≤ M) (hw1 : ‖w1‖ ≤ M)
    (hd0 : ‖z0 - w0‖ ≤ D) (hd1 : ‖z1 - w1‖ ≤ D) (p q : ℕ) :
    ‖z0 ^ p * z1 ^ q - w0 ^ p * w1 ^ q‖ ≤ ((p + q : ℕ) : ℝ) * M ^ (p + q - 1) * D := by
  have hp (n : ℕ) : ‖z0 ^ (n + 1) - w0 ^ (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) * M ^ n * D :=
    (complex_power_increment_bound z0 w0 M hM hz0 hw0 n).trans
      (mul_le_mul_of_nonneg_left hd0 (by positivity))
  have hq (n : ℕ) : ‖z1 ^ (n + 1) - w1 ^ (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) * M ^ n * D :=
    (complex_power_increment_bound z1 w1 M hM hz1 hw1 n).trans
      (mul_le_mul_of_nonneg_left hd1 (by positivity))
  cases p with
  | zero =>
    cases q with
    | zero => simp
    | succ q => simpa only [pow_zero, one_mul, Nat.zero_add, Nat.add_sub_cancel] using hq q
  | succ p =>
    cases q with
    | zero => simpa only [pow_zero, mul_one, Nat.add_zero, Nat.add_sub_cancel] using hp p
    | succ q =>
      have he : z0 ^ (p + 1) * z1 ^ (q + 1) - w0 ^ (p + 1) * w1 ^ (q + 1) =
          z0 ^ (p + 1) * (z1 ^ (q + 1) - w1 ^ (q + 1)) +
          (z0 ^ (p + 1) - w0 ^ (p + 1)) * w1 ^ (q + 1) := by ring
      have hzp : ‖z0 ^ (p + 1)‖ ≤ M ^ (p + 1) := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hz0 _
      have hwq : ‖w1 ^ (q + 1)‖ ≤ M ^ (q + 1) := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hw1 _
      calc
        _ = ‖z0 ^ (p + 1) * (z1 ^ (q + 1) - w1 ^ (q + 1)) +
            (z0 ^ (p + 1) - w0 ^ (p + 1)) * w1 ^ (q + 1)‖ := by rw [he]
        _ ≤ ‖z0 ^ (p + 1) * (z1 ^ (q + 1) - w1 ^ (q + 1))‖ +
            ‖(z0 ^ (p + 1) - w0 ^ (p + 1)) * w1 ^ (q + 1)‖ := norm_add_le _ _
        _ = ‖z0 ^ (p + 1)‖ * ‖z1 ^ (q + 1) - w1 ^ (q + 1)‖ +
            ‖z0 ^ (p + 1) - w0 ^ (p + 1)‖ * ‖w1 ^ (q + 1)‖ := by rw [norm_mul, norm_mul]
        _ ≤ M ^ (p + 1) * (((q + 1 : ℕ) : ℝ) * M ^ q * D) +
            (((p + 1 : ℕ) : ℝ) * M ^ p * D) * M ^ (q + 1) := by
          exact add_le_add (mul_le_mul hzp (hq q) (norm_nonneg _) (by positivity))
            (mul_le_mul (hp p) hwq (norm_nonneg _) (by positivity))
        _ = _ := by
          rw [show p + 1 + (q + 1) - 1 = p + q + 1 by omega]
          simp only [Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
          ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Complex strong time curves are genuinely bounded and almost measurable on each compact interval. -/

theorem StrongTimeRegularity.complex_memLp_top {a b : ℝ} (hab : a ≤ b)
    {u du : ℝ → ℂ} (h : StrongTimeRegularity a b u du) :
    MemLp u ⊤ (volume.restrict (Icc a b)) := by
  have hc : ContinuousOn u (Icc a b) := by
    simpa only [uIcc_of_le hab] using h.ac.continuousOn
  obtain ⟨R, hR⟩ := h.ac.exists_bound
  apply MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Icc) R
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hR t (by simpa only [uIcc_of_le hab] using ht)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Product and increment rules for absolutely continuous complex scalar time curves. -/

theorem StrongTimeRegularity.complex_mul {a b : ℝ} {u du v dv : ℝ → ℂ}
    (hu : StrongTimeRegularity a b u du) (hv : StrongTimeRegularity a b v dv) :
    StrongTimeRegularity a b (fun t => u t * v t) (fun t => du t * v t + u t * dv t) := by
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul] using hu.ac.fun_smul hv.ac
  · filter_upwards [hu.derivative, hv.derivative] with t hut hvt
    exact hut.mul hvt

theorem StrongTimeRegularity.complex_increment {a b : ℝ} {u du : ℝ → ℂ}
    (h : StrongTimeRegularity a b u du) (hd : IntervalIntegrable du volume a b) :
    u b - u a = ∫ t in a..b, du t := by
  have hr := (h.map Complex.reCLM).pairing_increment (1 : ℝ)
  have hi := (h.map Complex.imCLM).pairing_increment (1 : ℝ)
  change inner ℝ (u b).re (1 : ℝ) - inner ℝ (u a).re (1 : ℝ) =
    ∫ t in a..b, inner ℝ (du t).re (1 : ℝ) at hr
  change inner ℝ (u b).im (1 : ℝ) - inner ℝ (u a).im (1 : ℝ) =
    ∫ t in a..b, inner ℝ (du t).im (1 : ℝ) at hi
  simp only [Real.inner_apply, mul_one] at hr hi
  have her := Complex.reCLM.intervalIntegral_comp_comm hd
  have hei := Complex.imCLM.intervalIntegral_comp_comm hd
  change (∫ t in a..b, (du t).re) = (∫ t in a..b, du t).re at her
  change (∫ t in a..b, (du t).im) = (∫ t in a..b, du t).im at hei
  apply Complex.ext
  · rw [Complex.sub_re, ← her]
    exact hr
  · rw [Complex.sub_im, ← hei]
    exact hi

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Set MeasureTheory
namespace AVRegularity.CycleEvolution

/-! The exponential of an actual complex absolutely continuous phase has its expected derivative. -/

theorem StrongTimeRegularity.complex_exp {a b : ℝ} {u du : ℝ → ℂ}
    (h : StrongTimeRegularity a b u du) :
    StrongTimeRegularity a b (fun t => Complex.exp (u t))
      (fun t => Complex.exp (u t) * du t) := by
  obtain ⟨R, hR⟩ := h.ac.exists_bound
  have he : ContDiffOn ℝ 1 Complex.exp (Metric.closedBall (0 : ℂ) R) :=
    Complex.contDiff_exp.contDiffOn
  obtain ⟨K, hK⟩ := he.exists_lipschitzOnWith (by decide)
    (convex_closedBall (0 : ℂ) R) (isCompact_closedBall (0 : ℂ) R)
  have hm : MapsTo u (uIcc a b) (Metric.closedBall (0 : ℂ) R) := by
    intro t ht
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR t ht
  refine ⟨hK.comp_absolutelyContinuousOnInterval hm h.ac, ?_⟩
  filter_upwards [h.derivative] with t ht
  exact ht.cexp

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Grönwall estimates retaining the integrated dissipation term. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A strong-time energy inequality retains nonnegative dissipation in its Grönwall bound. -/
theorem StrongTimeRegularity.energy_dissipation_le_gronwall {a b : ℝ} (hab : a ≤ b)
    {u du : ℝ → H} (h : StrongTimeRegularity a b u du)
    (C : ℝ) (hC : 0 ≤ C) (f d : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b) (hd : IntervalIntegrable d volume a b)
    (hf_nonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ f t)
    (hd_nonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ d t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * inner ℝ (u t) (du t) + d t ≤ C * ‖u t‖ ^ 2 + f t) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 + ∫ s in a..t, d s ≤
        (‖u a‖ ^ 2 + ∫ s in a..b, f s) * Real.exp (C * (t - a)) := by
  let E : ℝ → ℝ := fun t => ‖u t‖ ^ 2 + ∫ s in a..t, d s
  have hucont : ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc a b) := by
    simpa only [uIcc_of_le hab] using h.norm_sq_ac.continuousOn
  have hdcont : ContinuousOn (fun t => ∫ s in a..t, d s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hd left_mem_uIcc
  have hEcont : ContinuousOn E (Icc a b) := hucont.add hdcont
  have hCEint : IntervalIntegrable (fun t => C * E t) volume a b :=
    (continuousOn_const.mul hEcont).intervalIntegrable_of_Icc hab
  have hCuInt : IntervalIntegrable (fun t => C * ‖u t‖ ^ 2) volume a b :=
    (continuousOn_const.mul hucont).intervalIntegrable_of_Icc hab
  have hule : ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ E t := by
    intro t ht
    have hdt : ∀ᵐ s ∂volume.restrict (Icc a t), 0 ≤ d s := by
      rw [← restrict_Ioc_eq_restrict_Icc]
      exact hd_nonneg.filter_mono (ae_mono
        (Measure.restrict_mono (Ioc_subset_Ioc le_rfl ht.2) le_rfl))
    have hn := intervalIntegral.integral_nonneg_of_ae_restrict ht.1 hdt
    exact le_add_of_nonneg_right hn
  have hineq : ∀ t ∈ Icc a b,
      E t ≤ (‖u a‖ ^ 2 + ∫ s in a..b, f s) + ∫ s in a..t, C * E s := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hg := hgrowth.filter_mono (ae_mono
      (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
    have hbound := intervalIntegral.integral_mono_ae_restrict ht.1
      ((h.mono hsub).energy_integrable.add (hd.mono_set hsub))
      ((hCuInt.mono_set hsub).add (hf.mono_set hsub)) hg
    rw [intervalIntegral.integral_add (h.mono hsub).energy_integrable (hd.mono_set hsub),
      ← (h.mono hsub).energy_increment,
      intervalIntegral.integral_add (hCuInt.mono_set hsub) (hf.mono_set hsub)] at hbound
    have hfbound := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hf_nonneg hf
    have hCbound : (∫ s in a..t, C * ‖u s‖ ^ 2) ≤ ∫ s in a..t, C * E s := by
      apply intervalIntegral.integral_mono_on ht.1 (hCuInt.mono_set hsub)
        (hCEint.mono_set hsub)
      intro s hs
      exact mul_le_mul_of_nonneg_left (hule s ⟨hs.1, hs.2.trans ht.2⟩) hC
    dsimp only [E]
    linarith
  have hgr := AVenhance.Infra.ODE.integral_gronwall_bound hab
    (continuous_const.intervalIntegrable a b) hCEint (fun _ _ => hC) hineq
  intro t ht
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - a) C]
    using hgr t ht
end

/-! Strong-time energy estimates with integrable source production. Constants remain
abstract real numbers. No coefficient regularity or PDE existence is asserted here. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A derivative pairing bound gives a Grönwall estimate with integrated forcing. -/
theorem StrongTimeRegularity.norm_sq_le_gronwall {a b : ℝ} (hab : a ≤ b)
    {u du : ℝ → H} (h : StrongTimeRegularity a b u du)
    (C : ℝ) (hC : 0 ≤ C) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b)
    (hf_nonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ f t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * inner ℝ (u t) (du t) ≤ C * ‖u t‖ ^ 2 + f t) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 ≤ (‖u a‖ ^ 2 + ∫ s in a..b, f s) * Real.exp (C * (t - a)) := by
  have hcont : ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc a b) := by
    simpa only [uIcc_of_le hab] using h.norm_sq_ac.continuousOn
  have hint : IntervalIntegrable (fun t => C * ‖u t‖ ^ 2) volume a b :=
    (continuousOn_const.mul hcont).intervalIntegrable_of_Icc hab
  have hineq : ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 ≤ (‖u a‖ ^ 2 + ∫ s in a..b, f s) +
        ∫ s in a..t, C * ‖u s‖ ^ 2 := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hg := hgrowth.filter_mono (ae_mono
      (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
    have hbound := intervalIntegral.integral_mono_ae_restrict ht.1
      (h.mono hsub).energy_integrable
      ((hint.mono_set hsub).add (hf.mono_set hsub)) hg
    rw [← (h.mono hsub).energy_increment,
      intervalIntegral.integral_add (hint.mono_set hsub) (hf.mono_set hsub)] at hbound
    have hfbound := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hf_nonneg hf
    linarith
  have hgr := AVenhance.Infra.ODE.integral_gronwall_bound hab
    (continuous_const.intervalIntegrable a b) hint (fun _ _ => hC) hineq
  intro t ht
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - a) C]
    using hgr t ht
end

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace AVRegularity.CycleEvolution

/-! Pass strong-time energy identities to a limit. This is an approximation helper:
endpoint convergence and dominated convergence of energy production are analytic
premises. No energy identity of the limiting curve is assumed. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Endpoint convergence and dominated energy production pass the energy increment.
This can be applied to Fourier approximants once their convergence is established. -/
theorem energy_increment_of_dominated_approximation {a b : ℝ} (hab : a ≤ b)
    (u du : ℕ → ℝ → H) (h : ∀ n, StrongTimeRegularity a b (u n) (du n))
    (ua ub : H) (ha : Tendsto (fun n => u n a) atTop (𝓝 ua))
    (hb : Tendsto (fun n => u n b) atTop (𝓝 ub))
    (production bound : ℝ → ℝ)
    (hbound : IntegrableOn bound (Ioc a b))
    (hdom : ∀ n, ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖2 * inner ℝ (u n t) (du n t)‖ ≤ bound t)
    (hlim : ∀ᵐ t ∂volume.restrict (Ioc a b),
      Tendsto (fun n => 2 * inner ℝ (u n t) (du n t)) atTop (𝓝 (production t))) :
    ‖ub‖ ^ 2 - ‖ua‖ ^ 2 = ∫ t in a..b, production t := by
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun t => 2 * inner ℝ (u n t) (du n t)) (volume.restrict (Ioc a b)) := by
    intro n
    simpa only [intervalIntegrable_iff, uIoc_of_le hab] using
      (h n).energy_integrable.aestronglyMeasurable
  have hi := tendsto_integral_of_dominated_convergence bound hmeas hbound hdom hlim
  have hn : Tendsto (fun n => ‖u n b‖ ^ 2 - ‖u n a‖ ^ 2) atTop
      (𝓝 (‖ub‖ ^ 2 - ‖ua‖ ^ 2)) := (hb.norm.pow 2).sub (ha.norm.pow 2)
  have heq : (fun n => ∫ t in Ioc a b, 2 * inner ℝ (u n t) (du n t)) =
      (fun n => ‖u n b‖ ^ 2 - ‖u n a‖ ^ 2) := by
    funext n
    rw [← intervalIntegral.integral_of_le hab]
    exact (h n).energy_increment.symm
  rw [heq] at hi
  rw [intervalIntegral.integral_of_le hab]
  exact tendsto_nhds_unique hn hi

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Contrast-uniform pointwise bounds for the bilinear fibre frequency couplings. -/

/-- The literal fibre frequency norm is nonnegative. -/
theorem fibreNorm_nonneg (ξ : Fin 2 → ℂ) : 0 ≤ fibreNorm ξ := Real.sqrt_nonneg _

/-- A real vector paired bilinearly with a complex frequency obeys Cauchy--Schwarz. -/
theorem fibreRealPair_norm_le (a : Fin 2 → ℝ) (ξ : Fin 2 → ℂ) :
    ‖∑ k, (a k : ℂ) * ξ k‖ ≤ Real.sqrt (∑ k, a k ^ 2) * fibreNorm ξ := by
  calc
    _ ≤ ∑ k, ‖(a k : ℂ) * ξ k‖ := norm_sum_le _ _
    _ = ∑ k, |a k| * ‖ξ k‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ k, |a k| ^ 2) * Real.sqrt (∑ k, ‖ξ k‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => |a k|) (fun k => ‖ξ k‖)
    _ = _ := by simp only [sq_abs, fibreNorm]

/-- The scaled drift couples to the frequency through its prescribed uniform bound alone. -/
theorem fibreScaledDrift_norm_le (η Cw : ℝ) (a : Fin 2 → ℝ) (ξ : Fin 2 → ℂ)
    (ha : Real.sqrt η * Real.sqrt (∑ k, a k ^ 2) ≤ Cw) :
    ‖(Real.sqrt η : ℂ) * ∑ k, (a k : ℂ) * ξ k‖ ≤ Cw * fibreNorm ξ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg η)]
  calc
    _ ≤ Real.sqrt η * (Real.sqrt (∑ k, a k ^ 2) * fibreNorm ξ) :=
      mul_le_mul_of_nonneg_left (fibreRealPair_norm_le a ξ) (Real.sqrt_nonneg η)
    _ = (Real.sqrt η * Real.sqrt (∑ k, a k ^ 2)) * fibreNorm ξ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (fibreNorm_nonneg ξ)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Exact frequency norms under negation and conjugation. -/

theorem fibreNorm_neg (ξ : Fin 2 → ℂ) : fibreNorm (fun j => -ξ j) = fibreNorm ξ := by
  simp only [fibreNorm, norm_neg]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Abstract finite-energy absorption for the nonlinear graph metric estimate. -/

theorem fibreMetric_stability_absorption (e d h : ℝ≥0∞) (he : e < ⊤)
    (B w q : ℝ) (hB : 0 ≤ B) (hw : 0 ≤ w) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hd : d ≤ 1) (hh : h ≤ 1) (hsmall : 13 * (4 * w + 8) * q ≤ 1 / 2)
    (hb : e ≤ (13 * (ENNReal.ofReal (w * q) * (2 + d + h) +
        ENNReal.ofReal (8 * q))) * e +
      13 * (ENNReal.ofReal (4 * B * q) + 2 * ENNReal.ofReal B) * d) :
    e ≤ 156 * ENNReal.ofReal B * d := by
  have hc : 13 * (ENNReal.ofReal (w * q) * (2 + d + h) +
      ENNReal.ofReal (8 * q)) ≤ (1 / 2 : ℝ≥0∞) := by
    calc
      _ ≤ 13 * (ENNReal.ofReal (w * q) * (2 + 1 + 1) + ENNReal.ofReal (8 * q)) := by
        gcongr
      _ = ENNReal.ofReal (13 * (4 * w + 8) * q) := by
        rw [show (2 + 1 + 1 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          show (13 : ℝ≥0∞) = ENNReal.ofReal 13 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hsmall
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have hs : 13 * (ENNReal.ofReal (4 * B * q) + 2 * ENNReal.ofReal B) * d ≤
      78 * ENNReal.ofReal B * d := by
    have hqB : ENNReal.ofReal (4 * B * q) ≤ 4 * ENNReal.ofReal B := by
      calc
        _ ≤ ENNReal.ofReal (4 * B) := ENNReal.ofReal_le_ofReal (by nlinarith)
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    calc
      _ ≤ 13 * (4 * ENNReal.ofReal B + 2 * ENNReal.ofReal B) * d := by gcongr
      _ = _ := by ring
  have ha := ennreal_half_absorption e (78 * ENNReal.ofReal B * d) he
    (hb.trans (by rw [add_comm]; exact add_le_add hs (mul_le_mul' hc le_rfl)))
  convert ha using 1
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Exact convergent monomial series of one literal Taylor coefficient. -/

/-- A single monomial coefficient gives an actual convergent series with its literal value. -/
theorem fibreMonomial_delta_hasSum (ξ : Fin 2 → ℂ) (q : ℕ × ℕ) (c : ℂ) :
    HasSum (fun p => fibreMonomial ξ p * (if p = q then c else 0)) (fibreMonomial ξ q * c) := by
  have he : (fun p => fibreMonomial ξ p * (if p = q then c else 0)) =
      (fun p => if p = q then fibreMonomial ξ q * c else 0) := by
    funext p
    by_cases hp : p = q
    · subst p
      simp
    · simp only [ite_eq_right hp, mul_zero]
  rw [he]
  exact hasSum_ite_eq q _

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Genuine multilinear coefficients for the two-variable fibre Taylor series. -/

def fibreMonomialMultilinear (α : ℕ × ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (α.1 + α.2) => Fin 2 → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin (α.1 + α.2)) ℂ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (if i.val < α.1 then (0 : Fin 2) else 1))

theorem fibreMonomialMultilinear_norm_le (α : ℕ × ℕ) : ‖fibreMonomialMultilinear α‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro m
  simp only [fibreMonomialMultilinear, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.proj_apply, norm_prod, one_mul]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => norm_le_pi_norm (m i) _)

theorem fibreMonomialMultilinear_diag (α : ℕ × ℕ) (ξ : Fin 2 → ℂ) :
    fibreMonomialMultilinear α (fun _ => ξ) = fibreMonomial ξ α := by
  simp only [fibreMonomialMultilinear, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.proj_apply]
  rw [Fin.prod_univ_add]
  have hleft : (∏ i : Fin α.1, ξ (if (Fin.castAdd α.2 i).val < α.1 then 0 else 1)) = ξ 0 ^ α.1 := by
    simp only [Fin.val_castAdd, Fin.is_lt]
    simp
  have hright : (∏ i : Fin α.2, ξ (if (Fin.natAdd α.1 i).val < α.1 then 0 else 1)) = ξ 1 ^ α.2 := by
    have hn (i : Fin α.2) : ¬ α.1 + i.val < α.1 := by omega
    simp only [Fin.val_natAdd, hn]
    simp
  rw [hleft, hright]
  rfl

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Banach-valued analytic coefficient families retain analyticity after restriction in time. -/

theorem lpComplexMeasureRestriction_analyticAt {X Y : Type*} [MeasurableSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {μ ν : Measure X}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : μ ≤ ν) (f : Y → Lp ℂ p ν) (x : Y)
    (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun y => lpComplexMeasureRestriction p h (f y)) x :=
  ((lpComplexMeasureRestriction p h).analyticAt (f x)).comp hf

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! A bounded L2 representative has the sharp square-root time-length norm budget. -/

 theorem lpTwoFiniteInterval_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a b : ℝ} (hab : a ≤ b)
    (u : Lp E 2 (volume.restrict (Icc a b))) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ᵐ t ∂volume.restrict (Icc a b), ‖u t‖ ≤ M) :
    ‖u‖ ≤ Real.sqrt (b - a) * M := by
  have hi := (Lp.memLp u).norm.integrable_sq
  have hc : Integrable (fun _ : ℝ => M ^ 2) (volume.restrict (Icc a b)) := integrable_const _
  have hb := integral_mono_ae hi hc (hu.mono (fun t ht =>
    (sq_le_sq₀ (norm_nonneg (u t)) hM).2 ht))
  rw [← lpTwoHilbert_normSq_integral, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at hb
  have hs := Real.sq_sqrt (sub_nonneg.mpr hab)
  have hn := norm_nonneg u
  have hr := Real.sqrt_nonneg (b - a)
  apply (sq_le_sq₀ hn (mul_nonneg hr hM)).mp
  simpa only [mul_pow, hs] using hb

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Measurable matrix entries of bounded spatial coefficient forms. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
/-- Pairing a coefficient multiplier with a test is the literal spatial integral. -/
theorem measurableCoefficientL2_inner_eq_integral {U : Set (Vec 2)}
    (C : Vec 2 → E →L[ℝ] F) (hC : AEStronglyMeasurable C (volume.restrict U)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, ‖C x‖ ≤ M) (u : Lp E 2 (volume.restrict U))
    (z : Lp F 2 (volume.restrict U)) :
    inner ℝ (measurableCoefficientL2 C hC M hM hb u) z =
      ∫ x, inner ℝ (C x (u x)) (z x) ∂volume.restrict U := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [measurableCoefficientL2_ae C hC M hM hb u] with x hx
  rw [hx]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
/-- The uniform operator bound controls a weak matrix entry. -/
theorem measurableCoefficientL2_inner_abs_le {U : Set (Vec 2)}
    (C : Vec 2 → E →L[ℝ] F) (hC : AEStronglyMeasurable C (volume.restrict U)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, ‖C x‖ ≤ M) (u : Lp E 2 (volume.restrict U))
    (z : Lp F 2 (volume.restrict U)) :
    |inner ℝ (measurableCoefficientL2 C hC M hM hb u) z| ≤ M * ‖u‖ * ‖z‖ := by
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (measurableCoefficientL2_norm_le C hC M hM hb u)
      (norm_nonneg z))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Integrating an exponentially decaying derivative costs a fixed constant. -/

theorem decay_derivative_integral_norm_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b c M : ℝ} (hab : a ≤ b) (hc : 0 < c) (hM : 0 ≤ M)
    (f : ℝ → E)
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ‖f t‖ ≤ M * Real.exp (-c * (t - a))) :
    ‖∫ t in a..b, f t‖ ≤ M / c := by
  have hi : IntervalIntegrable (fun t : ℝ => M * Real.exp (-c * (t - a))) volume a b :=
    (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable _ _
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le hab
    (ae_imp_of_ae_restrict (hf.filter_mono (ae_mono
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)))) hi
  apply hbnd.trans
  rw [intervalIntegral.integral_const_mul]
  calc
    M * (∫ t in a..b, Real.exp (-c * (t - a))) ≤ M * (1 / c) :=
      mul_le_mul_of_nonneg_left (exponential_decay_integral_bound hc) hM
    _ = M / c := by ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Topology
namespace AVRegularity.CycleEvolution

/-! Strong scalar time regularity recovered from an actual integrable primitive. -/

/-- An integrable primitive representation gives absolute continuity and its a.e. derivative. -/
theorem scalarStrongTime_of_primitive {a b : ℝ} (hab : a ≤ b) (E P : ℝ → ℝ)
    (hP : IntervalIntegrable P volume a b)
    (he : ∀ t ∈ Icc a b, E t = E a + ∫ s in a..t, P s) :
    StrongTimeRegularity a b E P := by
  let A := fun t => E a + ∫ s in a..t, P s
  have hA : AbsolutelyContinuousOnInterval A a b :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => E a)).contDiffOn.absolutelyContinuousOnInterval).fun_add
      (hP.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  refine ⟨hA.congr (fun t ht => (he t (by simpa only [uIcc_of_le hab] using ht)).symm), ?_⟩
  rw [uIcc_of_le hab, ← restrict_Ioo_eq_restrict_Icc]
  have hd := hP.ae_hasDerivAt_integral.filter_mono
    (ae_mono (Measure.restrict_le_self : volume.restrict (Ioo a b) ≤ volume))
  filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t hdt ht
  have hprim : HasDerivAt A (P t) t := by
    exact (hdt (by simpa only [uIcc_of_le hab] using ⟨ht.1.le, ht.2.le⟩) a left_mem_uIcc).const_add (E a)
  apply hprim.congr_of_eventuallyEq
  have hI : ∀ᶠ x in 𝓝 t, x ∈ Ioo a b := isOpen_Ioo.mem_nhds ht
  filter_upwards [hI] with x hx
  exact he x ⟨hx.1.le, hx.2.le⟩

/-! Integrating-factor energy calculus in abstract real variables. -/

/-- Exact integrating-factor identity for an absolutely continuous scalar energy. -/
theorem StrongTimeRegularity.scalar_weighted_increment {a b : ℝ} {E P : ℝ → ℝ}
    (h : StrongTimeRegularity a b E P) (c : ℝ) :
    Real.exp (c * (b - a)) * E b - E a =
      ∫ t in a..b, Real.exp (c * (t - a)) * (P t + c * E t) := by
  let w := fun t : ℝ => Real.exp (c * (t - a))
  have hw : ContDiff ℝ 1 w := (contDiff_const.mul (contDiff_id.sub contDiff_const)).exp
  have hwd (t : ℝ) : HasDerivAt w (c * w t) t := by
    simpa only [w, id_eq, mul_one, mul_comm] using
      (((hasDerivAt_id t).sub_const a).const_mul c).exp
  have he := hw.contDiffOn.absolutelyContinuousOnInterval.integral_deriv_mul_eq_sub h.ac
  have hwa : w a = 1 := by simp only [w, sub_self, mul_zero, Real.exp_zero]
  rw [hwa, one_mul] at he
  apply he.symm.trans
  apply intervalIntegral.integral_congr_ae_restrict
  have hd := h.derivative.filter_mono
    (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  filter_upwards [hd] with t ht
  rw [(hwd t).deriv, ht.deriv]
  dsimp only [w]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Addition of actual strong time curves. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem StrongTimeRegularity.add {a b : ℝ} {u du v dv : ℝ → H}
    (hu : StrongTimeRegularity a b u du) (hv : StrongTimeRegularity a b v dv) :
    StrongTimeRegularity a b (fun t => u t + v t) (fun t => du t + dv t) := by
  refine ⟨hu.ac.fun_add hv.ac, ?_⟩
  filter_upwards [hu.derivative, hv.derivative] with t hut hvt
  exact hut.add hvt

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Conditional uniqueness from a one-sided Hilbert growth bound. The hypothesis is a
bound on the derivative pairing, not an assumed energy inequality. No existence is used. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Zero initial trace and a one-sided growth bound force a strong-time curve to vanish. -/
theorem StrongTimeRegularity.eq_zero_of_growth {a b : ℝ} (hab : a ≤ b)
    {u du : ℝ → H} (h : StrongTimeRegularity a b u du) (hinitial : u a = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * inner ℝ (u t) (du t) ≤ C * ‖u t‖ ^ 2) :
    ∀ t ∈ Icc a b, u t = 0 := by
  have hcont : ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc a b) := by
    simpa only [uIcc_of_le hab] using h.norm_sq_ac.continuousOn
  have hint : IntervalIntegrable (fun t => C * ‖u t‖ ^ 2) volume a b :=
    (continuousOn_const.mul hcont).intervalIntegrable_of_Icc hab
  have hineq : ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 ≤ 0 + ∫ s in a..t, C * ‖u s‖ ^ 2 := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have henergy := (h.mono hsub).energy_increment
    have hg : ∀ᵐ s ∂volume.restrict (Icc a t),
        2 * inner ℝ (u s) (du s) ≤ C * ‖u s‖ ^ 2 :=
      hgrowth.filter_mono (ae_mono
        (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
    have hbound := intervalIntegral.integral_mono_ae_restrict ht.1
      (h.mono hsub).energy_integrable (hint.mono_set hsub) hg
    rw [← henergy] at hbound
    simpa [hinitial] using hbound
  have hgr := AVenhance.Infra.ODE.integral_gronwall_bound hab
    (continuous_const.intervalIntegrable a b) hint (fun _ _ => hC) hineq
  intro t ht
  have hsq : ‖u t‖ ^ 2 = 0 :=
    le_antisymm (by simpa using hgr t ht) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

end AVRegularity.CycleEvolution
end
end
