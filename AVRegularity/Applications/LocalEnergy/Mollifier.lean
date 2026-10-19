-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

section
public section
open Homogenization
namespace AVRegularity.Applications

/-! # Pointwise algebra for the Caccioppoli inequality

For `V = U - c`, a cutoff value `χ` with gradient `g`, put `a = χ DU`, `b = V g`,
`s = a + b`.  The integrand of the local energy identity expands (using skewness of `K`) as
`(|s|² - |b|²) + 2 (K a)·b - χ² V d·DU - 2 χ V² d·g`, and after the drift cancellation the
remaining terms are controlled by Young's inequality. -/

/-- A skew-symmetric `2 × 2` matrix has `(K e)·e = 0`. -/
theorem vecDot_mulVec_self_of_skew {K : Matrix (Fin 2) (Fin 2) ℝ}
    (hK : K.transpose = -K) (e : Vec 2) : vecDot (K.mulVec e) e = 0 := by
  have h : ∀ i j, K j i = -K i j := fun i j => by
    have := congrFun (congrFun hK i) j
    simpa using this
  have h00 := h 0 0
  have h11 := h 1 1
  have h01 := h 0 1
  simp only [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have : K 0 0 = 0 := by linarith
  have : K 1 1 = 0 := by linarith
  rw [‹K 0 0 = 0›, ‹K 1 1 = 0›]
  rw [h01]
  ring

/-- Exact expansion of the energy-identity integrand. -/
theorem caccioppoli_expand {K : Matrix (Fin 2) (Fin 2) ℝ} {DU d g : Vec 2} {χ V : ℝ}
    (hK0 : vecDot (K.mulVec DU) DU = 0) :
    vecDot ((1 + K).mulVec DU - V • d) (χ ^ 2 • DU + (2 * χ * V) • g) =
      (vecNormSq (χ • DU + V • g) - vecNormSq (V • g))
        + 2 * vecDot (K.mulVec (χ • DU)) (V • g)
        - (χ ^ 2 * V * vecDot d DU + 2 * χ * V ^ 2 * vecDot d g) := by
  have h : ∀ x y : Vec 2, vecDot x y = x 0 * y 0 + x 1 * y 1 := fun x y => by
    simp [vecDot, Fin.sum_univ_two]
  have hn : ∀ x : Vec 2, vecNormSq x = x 0 * x 0 + x 1 * x 1 := fun x => h x x
  have hm : ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (x : Vec 2), M.mulVec x 0 = M 0 0 * x 0 + M 0 1 * x 1
      ∧ M.mulVec x 1 = M 1 0 * x 0 + M 1 1 * x 1 := fun M x => by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h] at hK0
  rw [h, hn, hn, h, h, h]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_mulVec,
    Matrix.one_mulVec, (hm K _).1, (hm K _).2] at hK0 ⊢
  linear_combination (χ ^ 2) * hK0

theorem vecNormSq_smul_sq (r : ℝ) (x : Vec 2) : vecNormSq (r • x) = r ^ 2 * vecNormSq x := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  ring

theorem vecNormSq_nonneg (x : Vec 2) : 0 ≤ vecNormSq x := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1)]

theorem young_vec (m b : Vec 2) : -(4 * vecDot m b) ≤ vecNormSq m / 2 + 8 * vecNormSq b := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  nlinarith [sq_nonneg (m 0 + 4 * b 0), sq_nonneg (m 1 + 4 * b 1)]

theorem vecNormSq_sub_le (s b : Vec 2) :
    vecNormSq (s - b) ≤ 2 * vecNormSq s + 2 * vecNormSq b := by
  simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.sub_apply]
  nlinarith [sq_nonneg (s 0 + b 0), sq_nonneg (s 1 + b 1)]

theorem abs_vecDot_le {d g : Vec 2} {kd L : ℝ} (hkd : 0 ≤ kd) (hL : 0 ≤ L)
    (hd : vecNormSq d ≤ kd ^ 2) (hg : vecNormSq g ≤ L ^ 2) : |vecDot d g| ≤ kd * L := by
  have h1 := sq_vecDot_le_vecNormSq_mul_vecNormSq d g
  have h2 : vecNormSq d * vecNormSq g ≤ kd ^ 2 * L ^ 2 :=
    mul_le_mul hd hg (vecNormSq_nonneg g) (sq_nonneg kd)
  apply abs_le_of_sq_le_sq _ (mul_nonneg hkd hL)
  calc vecDot d g ^ 2 ≤ kd ^ 2 * L ^ 2 := h1.trans h2
    _ = (kd * L) ^ 2 := by ring

/-- The pointwise Young estimate for the remainder terms. -/
theorem caccioppoli_remainder_le {K : Matrix (Fin 2) (Fin 2) ℝ} {DU d g : Vec 2}
    {χ V kK kd L : ℝ} (hkK : 0 ≤ kK) (hkd : 0 ≤ kd) (hsum : kK + kd ≤ 1) (hL : 0 ≤ L)
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hK : ∀ e : Vec 2, vecNormSq (K.mulVec e) ≤ kK ^ 2 * vecNormSq e)
    (hd : vecNormSq d ≤ kd ^ 2) (hg : vecNormSq g ≤ L ^ 2) :
    2 * vecNormSq (V • g) - 4 * vecDot (K.mulVec (χ • DU)) (V • g)
        + 2 * χ * V ^ 2 * vecDot d g
      ≤ vecNormSq (χ • DU + V • g) + (11 * L ^ 2 + 2 * L) * V ^ 2 := by
  set a : Vec 2 := χ • DU with ha
  set b : Vec 2 := V • g with hb
  set s : Vec 2 := a + b with hs
  have hkK1 : kK ≤ 1 := by linarith
  have hkd1 : kd ≤ 1 := by linarith
  have hm : vecNormSq (K.mulVec a) ≤ vecNormSq a := by
    refine (hK a).trans ?_
    have : kK ^ 2 ≤ 1 := by nlinarith
    nlinarith [vecNormSq_nonneg a]
  have has : a = s - b := by rw [hs]; abel
  have ha2 : vecNormSq a ≤ 2 * vecNormSq s + 2 * vecNormSq b := by
    rw [has]; exact vecNormSq_sub_le s b
  have hy := young_vec (K.mulVec a) b
  have hbL : vecNormSq b ≤ L ^ 2 * V ^ 2 := by
    rw [hb, vecNormSq_smul_sq]
    nlinarith [sq_nonneg V]
  have hdg : |vecDot d g| ≤ L := by
    have := abs_vecDot_le hkd hL hd hg
    nlinarith
  have hdg2 : 2 * χ * V ^ 2 * vecDot d g ≤ 2 * L * V ^ 2 := by
    have h1 : vecDot d g ≤ L := (le_abs_self _).trans hdg
    have h2 : 0 ≤ χ * V ^ 2 := mul_nonneg hχ0 (sq_nonneg V)
    have h3 : χ * V ^ 2 ≤ V ^ 2 := by nlinarith [sq_nonneg V]
    have h4 : χ * V ^ 2 * vecDot d g ≤ χ * V ^ 2 * L := mul_le_mul_of_nonneg_left h1 h2
    have h5 : χ * V ^ 2 * L ≤ V ^ 2 * L := mul_le_mul_of_nonneg_right h3 hL
    nlinarith
  nlinarith [vecNormSq_nonneg b, vecNormSq_nonneg s]

/-- The full pointwise estimate: after subtracting twice the drift term
`χ V d·(χ DU + V g)` (whose integral vanishes), the energy-identity integrand is bounded by
`-|s|² + (11 L² + 2 L) V²`. -/
theorem caccioppoli_pointwise {K : Matrix (Fin 2) (Fin 2) ℝ} {DU d g : Vec 2}
    {χ V kK kd L : ℝ} (hkK : 0 ≤ kK) (hkd : 0 ≤ kd) (hsum : kK + kd ≤ 1) (hL : 0 ≤ L)
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hskew : K.transpose = -K)
    (hK : ∀ e : Vec 2, vecNormSq (K.mulVec e) ≤ kK ^ 2 * vecNormSq e)
    (hd : vecNormSq d ≤ kd ^ 2) (hg : vecNormSq g ≤ L ^ 2) :
    -2 * vecDot ((1 + K).mulVec DU - V • d) (χ ^ 2 • DU + (2 * χ * V) • g)
        - 2 * (χ * V * vecDot d (χ • DU + V • g))
      ≤ -vecNormSq (χ • DU + V • g) + (11 * L ^ 2 + 2 * L) * V ^ 2 := by
  have hr := caccioppoli_remainder_le (K := K) (DU := DU) (d := d) (g := g) (χ := χ) (V := V)
    hkK hkd hsum hL hχ0 hχ1 hK hd hg
  rw [caccioppoli_expand (vecDot_mulVec_self_of_skew hskew DU)]
  have hlin : vecDot d (χ • DU + V • g) = χ * vecDot d DU + V * vecDot d g := by
    simp only [vecDot, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hlin]
  linarith [hr]

end AVRegularity.Applications
end
end

section
@[expose] public section
open Function Filter MeasureTheory Set Topology Homogenization
open scoped ENNReal Convolution Pointwise
namespace AVRegularity.Applications.LocalEnergy

/-!
# Space-time mollification with shifted kernels on `ℝ × Vec 2`

Shifted normalized bump kernels `shiftedKernel s r` (centred at `(s, 0)`, so in general
non-symmetric), the convolution `mollify f k p = ∫ q, f q * k (p - q)`, its smoothness and
derivative formula, linearity, the `L²` contraction bound and `L²` convergence
`mollify f (k n) → f` for kernel families supported in shrinking balls around `0`, and the
continuity of the `L²` pairing. This is the Escauriaza–Seregin–Šverák time-mollification
argument, with kernels on the right.

Smoothness hypotheses use `ContDiff ℝ (⊤ : ℕ∞)` (i.e. `C^∞`); note that a bare `⊤` in
`ContDiff` means analytic in current Mathlib.
-/

noncomputable section

/-! ### Haar instances on space-time -/

instance spaceTimeVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (ℝ × Vec 2)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure (Vec 2))

instance spaceTimeVolumeIsAddLeftInvariant :
    Measure.IsAddLeftInvariant (volume : Measure (ℝ × Vec 2)) :=
  spaceTimeVolumeIsAddHaarMeasure.toIsAddLeftInvariant

instance spaceTimeVolumeIsAddRightInvariant :
    Measure.IsAddRightInvariant (volume : Measure (ℝ × Vec 2)) := by
  constructor
  intro t
  rw [show (fun x : ℝ × Vec 2 => x + t) = fun x => t + x by
    funext x
    exact add_comm x t]
  exact MeasureTheory.map_add_left_eq_self (μ := (volume : Measure (ℝ × Vec 2))) t

instance spaceTimeVolumeIsNegInvariant :
    Measure.IsNegInvariant (volume : Measure (ℝ × Vec 2)) :=
  inferInstance

/-! ### Shifted kernels -/

/-- The bump of outer radius `r` centred at `(s, 0)`. -/
def shiftedBump (s r : ℝ) (hr : 0 < r) : ContDiffBump ((s, 0) : ℝ × Vec 2) :=
  { rIn := r / 2
    rOut := r
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith only [hr] }

/-- The normalized smooth bump kernel centred at `(s, 0)` with outer radius `r`. -/
def shiftedKernel (s r : ℝ) (hr : 0 < r) : ℝ × Vec 2 → ℝ :=
  (shiftedBump s r hr).normed (volume : Measure (ℝ × Vec 2))

theorem shiftedKernel_contDiff {s r : ℝ} {hr : 0 < r} (n : ℕ∞) :
    ContDiff ℝ n (shiftedKernel s r hr) :=
  (shiftedBump s r hr).contDiff_normed

theorem shiftedKernel_hasCompactSupport {s r : ℝ} {hr : 0 < r} :
    HasCompactSupport (shiftedKernel s r hr) :=
  (shiftedBump s r hr).hasCompactSupport_normed

theorem shiftedKernel_nonneg {s r : ℝ} {hr : 0 < r} (z : ℝ × Vec 2) :
    0 ≤ shiftedKernel s r hr z :=
  (shiftedBump s r hr).nonneg_normed z

theorem shiftedKernel_integral_one {s r : ℝ} {hr : 0 < r} :
    ∫ z, shiftedKernel s r hr z = 1 :=
  (shiftedBump s r hr).integral_normed

theorem shiftedKernel_support {s r : ℝ} {hr : 0 < r} :
    Function.support (shiftedKernel s r hr) = Metric.ball ((s, 0) : ℝ × Vec 2) r :=
  (shiftedBump s r hr).support_normed_eq

theorem shiftedKernel_tsupport_subset {s r : ℝ} {hr : 0 < r} :
    tsupport (shiftedKernel s r hr) ⊆ Metric.closedBall ((s, 0) : ℝ × Vec 2) r := by
  have h : tsupport (shiftedKernel s r hr) = Metric.closedBall ((s, 0) : ℝ × Vec 2) r :=
    (shiftedBump s r hr).tsupport_normed_eq
  exact h.le

/-- Coordinatewise form of the support bound. -/
theorem shiftedKernel_tsupport_coord {s r : ℝ} {hr : 0 < r} :
    ∀ q ∈ tsupport (shiftedKernel s r hr),
      s - r ≤ q.1 ∧ q.1 ≤ s + r ∧ ∀ i, |q.2 i| ≤ r := by
  intro q hq
  have h := shiftedKernel_tsupport_subset hq
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [Real.dist_eq, abs_le] at h1
  refine ⟨by linarith [h1.1], by linarith [h1.2], fun i => ?_⟩
  rw [dist_zero_right] at h2
  have := norm_le_pi_norm q.2 i
  rw [Real.norm_eq_abs] at this
  exact this.trans h2

/-- The support of a shifted kernel lies in the ball of radius `|s| + r` around `0`. -/
theorem shiftedKernel_support_subset_ball {s r : ℝ} {hr : 0 < r} :
    Function.support (shiftedKernel s r hr) ⊆ Metric.ball (0 : ℝ × Vec 2) (|s| + r) := by
  rw [shiftedKernel_support]
  intro q hq
  rw [Metric.mem_ball] at hq ⊢
  have h0 : dist ((s, 0) : ℝ × Vec 2) 0 = |s| := by
    rw [Prod.dist_eq]
    simp
  calc dist q 0 ≤ dist q ((s, 0) : ℝ × Vec 2) + dist ((s, 0) : ℝ × Vec 2) 0 := dist_triangle _ _ _
    _ < r + |s| := by rw [h0]; linarith
    _ = |s| + r := add_comm _ _

/-! ### The mollification operator -/

/-- `mollify f k p = ∫ q, f q * k (p - q)`: convolution of data `f` with the kernel `k`. -/
def mollify (f : ℝ × Vec 2 → ℝ) (k : ℝ × Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  MeasureTheory.convolution f k (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem mollify_eq_integral (f k : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) :
    mollify f k p = ∫ q, f q * k (p - q) := by
  simp [mollify, MeasureTheory.convolution_def]

/-- The kernel-on-the-left form of the convolution. -/
theorem mollify_eq_convolution_left (f k : ℝ × Vec 2 → ℝ) :
    mollify f k = MeasureTheory.convolution k f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext p
  rw [mollify_eq_integral, MeasureTheory.convolution_lsmul_swap]
  simp [mul_comm]

theorem mollify_contDiff {k : ℝ × Vec 2 → ℝ} {f : ℝ × Vec 2 → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k)
    (hf : LocallyIntegrable f volume) : ContDiff ℝ (⊤ : ℕ∞) (mollify f k) :=
  hkc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hk

theorem mollify_continuous {k f : ℝ × Vec 2 → ℝ} (hk : Continuous k)
    (hkc : HasCompactSupport k) (hf : LocallyIntegrable f volume) :
    Continuous (mollify f k) :=
  (hkc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (n := 0) hf
    (contDiff_zero.2 hk)).continuous

theorem mollify_integrand_integrable {k f : ℝ × Vec 2 → ℝ} (hk : Continuous k)
    (hkc : HasCompactSupport k) (hf : LocallyIntegrable f volume) (p : ℝ × Vec 2) :
    Integrable (fun q => f q * k (p - q)) volume := by
  exact hkc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hk p

theorem hasFDerivAt_mollify {k f : ℝ × Vec 2 → ℝ} (hk : ContDiff ℝ 1 k)
    (hkc : HasCompactSupport k) (hf : LocallyIntegrable f volume) (p : ℝ × Vec 2) :
    HasFDerivAt (mollify f k)
      (MeasureTheory.convolution f (fderiv ℝ k)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (ℝ × Vec 2)) volume p) p :=
  hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hk p

theorem fderiv_mollify_apply {k f : ℝ × Vec 2 → ℝ} (hk : ContDiff ℝ 1 k)
    (hkc : HasCompactSupport k) (hf : LocallyIntegrable f volume) (p v : ℝ × Vec 2) :
    fderiv ℝ (mollify f k) p v = mollify f (fun z => fderiv ℝ k z v) p := by
  rw [(hasFDerivAt_mollify hk hkc hf p).fderiv, mollify_eq_integral]
  have hint : ConvolutionExistsAt f (fderiv ℝ k) p
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (ℝ × Vec 2)) volume :=
    (hkc.fderiv ℝ).convolutionExists_right _ hf (hk.continuous_fderiv one_ne_zero) p
  rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hint]
  simp

/-! ### Linearity -/

theorem mollify_add_left {k f f' : ℝ × Vec 2 → ℝ} (hk : Continuous k)
    (hkc : HasCompactSupport k) (hf : LocallyIntegrable f volume)
    (hf' : LocallyIntegrable f' volume) :
    mollify (f + f') k = mollify f k + mollify f' k := by
  funext p
  simp only [Pi.add_apply, mollify_eq_integral, add_mul]
  exact integral_add (mollify_integrand_integrable hk hkc hf p)
    (mollify_integrand_integrable hk hkc hf' p)

theorem mollify_sub_right {k k' f : ℝ × Vec 2 → ℝ} (hk : Continuous k) (hk' : Continuous k')
    (hkc : HasCompactSupport k) (hkc' : HasCompactSupport k')
    (hf : LocallyIntegrable f volume) :
    mollify f (k - k') = mollify f k - mollify f k' := by
  funext p
  simp only [Pi.sub_apply, mollify_eq_integral, mul_sub]
  exact integral_sub (mollify_integrand_integrable hk hkc hf p)
    (mollify_integrand_integrable hk' hkc' hf p)

/-! ### `L²` theory -/

private lemma convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := by
  have h1 : ConvexOn ℝ Set.univ (fun x : ℝ => |x|) := by
    convert (convexOn_univ_norm : ConvexOn ℝ Set.univ (fun x : ℝ => ‖x‖)) using 1
  have h2 : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t ^ p) := convexOn_rpow hp
  have h3 : MonotoneOn (fun t : ℝ => t ^ p) (Set.Ici 0) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow ha hab (le_trans zero_le_one hp)
  have himg : (fun x : ℝ => |x|) '' Set.univ ⊆ Set.Ici 0 := by
    rintro _ ⟨x, -, rfl⟩
    exact abs_nonneg x
  have himg_convex : Convex ℝ ((fun x : ℝ => |x|) '' Set.univ) := by
    have heq : (fun x : ℝ => |x|) '' Set.univ = Set.Ici 0 := by
      ext y
      simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ici]
      constructor
      · rintro ⟨x, rfl⟩
        exact abs_nonneg x
      · intro hy
        exact ⟨y, abs_of_nonneg hy⟩
    rw [heq]
    exact convex_Ici 0
  exact (h2.subset himg himg_convex).comp h1 (h3.mono himg)

private lemma jensen_abs_rpow_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : Integrable f μ) (hfpow : Integrable (fun x => |f x| ^ p) μ) :
    |∫ x, f x ∂μ| ^ p ≤ ∫ x, |f x| ^ p ∂μ := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := convexOn_abs_rpow hp
  have hcont : ContinuousOn (fun x : ℝ => |x| ^ p) Set.univ := by
    exact (continuous_abs.rpow_const fun _ => Or.inr (le_trans zero_le_one hp)).continuousOn
  exact hconv.map_integral_le hcont isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hf hfpow

private lemma lintegral_comp_sub_right (f : ℝ × Vec 2 → ℝ≥0∞) (hf : Measurable f)
    (t : ℝ × Vec 2) :
    ∫⁻ x, f (x - t) ∂(volume : Measure (ℝ × Vec 2)) = ∫⁻ x, f x ∂volume := by
  have heq : (fun x => f (x - t)) = f ∘ ((· + (-t)) : ℝ × Vec 2 → ℝ × Vec 2) := by
    funext x
    simp [sub_eq_add_neg]
  rw [heq, lintegral_comp hf (measurable_add_const (-t))]
  have hmap : Measure.map (fun x : ℝ × Vec 2 => x + (-t)) (volume : Measure (ℝ × Vec 2)) = volume := by
    rw [show (fun x : ℝ × Vec 2 => x + (-t)) = fun x => (-t) + x by
      funext x
      exact add_comm x (-t)]
    exact MeasureTheory.map_add_left_eq_self (μ := (volume : Measure (ℝ × Vec 2))) (-t)
  rw [hmap]

private lemma fubini_translation_key (ρ : ℝ × Vec 2 → ℝ≥0∞) (g : ℝ × Vec 2 → ℝ) (p : ℝ)
    (hρ : Measurable ρ) (hg : Measurable g) :
    ∫⁻ x, ∫⁻ t, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
      (∫⁻ t, ρ t ∂volume) * (∫⁻ x, (ENNReal.ofReal |g x|) ^ p ∂volume) := by
  have hswap :
      ∫⁻ x, ∫⁻ t, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
        ∫⁻ t, ∫⁻ x, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume := by
    apply lintegral_lintegral_swap
    apply AEMeasurable.mul
    · exact (hρ.comp measurable_snd).aemeasurable
    · have hpow : Measurable (fun z : (ℝ × Vec 2) × (ℝ × Vec 2) =>
          (ENNReal.ofReal |g (z.1 - z.2)|) ^ p) := by
        have hbase : Measurable (fun z : (ℝ × Vec 2) × (ℝ × Vec 2) =>
            ENNReal.ofReal |g (z.1 - z.2)|) := by
          exact ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp (hg.comp (measurable_fst.sub measurable_snd)))
        exact Measurable.pow_const hbase p
      exact hpow.aemeasurable
  rw [hswap]
  have hfactor :
      ∫⁻ t, ∫⁻ x, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
        ∫⁻ t, ρ t * ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume := by
    congr 1
    ext t
    have hsub : Measurable (fun x : ℝ × Vec 2 => x - t) := measurable_id.sub measurable_const
    exact lintegral_const_mul _ (Measurable.pow_const
      (ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp (hg.comp hsub))) p)
  rw [hfactor]
  have htrans : ∀ t, ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p ∂(volume : Measure (ℝ × Vec 2)) =
      ∫⁻ x, (ENNReal.ofReal |g x|) ^ p ∂volume := by
    intro t
    exact lintegral_comp_sub_right _ (Measurable.pow_const
      (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hg)) p) t
  simp_rw [htrans]
  rw [lintegral_mul_const _ hρ, mul_comm]

private lemma integral_withDensity_ofReal_eq_integral_mul
    {f g : ℝ × Vec 2 → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_meas : AEMeasurable f volume) :
    ∫ x, g x ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) =
      ∫ x, f x * g x := by
  have heq : (fun x => ENNReal.ofReal (f x)) =
      fun x => (Real.toNNReal (f x) : ℝ≥0∞) := by
    funext x
    rw [ENNReal.ofReal_eq_coe_nnreal (hf_nonneg x),
      Real.toNNReal_of_nonneg (hf_nonneg x)]
  rw [heq, integral_withDensity_eq_integral_smul₀ (hf_meas.real_toNNReal)]
  congr 1
  funext x
  simp [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hf_nonneg x)]

private theorem young_convolution_nonneg_integral_one
    {ρ g : ℝ × Vec 2 → ℝ} {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x) (hρ_int : Integrable ρ volume)
    (hρ_one : ∫ x, ρ x = 1) (hρ_meas : Measurable ρ) (hg_meas : Measurable g)
    (hconv_aestrong : AEStronglyMeasurable
      (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume) :
    eLpNorm (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume ≤
      eLpNorm g p volume := by
  have hp_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  have hp_ge_one : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
  let μ : Measure (ℝ × Vec 2) := volume.withDensity fun t => ENNReal.ofReal (ρ t)
  let _ : IsProbabilityMeasure μ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hρ_int (ae_of_all _ hρ_nonneg), hρ_one]
    simp
  have hg_aestrong : AEStronglyMeasurable g volume := hg_meas.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hconv_aestrong]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hg_aestrong]
  apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ 1 / p.toReal)
  have hfubini := fubini_translation_key (fun t => ENNReal.ofReal (ρ t)) g
    p.toReal hρ_meas.ennreal_ofReal hg_meas
  have hρ_lint_one : ∫⁻ t, ENNReal.ofReal (ρ t) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρ_int (ae_of_all _ hρ_nonneg), hρ_one]
    simp
  have hpointwise : ∀ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ≤
      ∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume := by
    intro x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [Real.enorm_eq_ofReal_abs]
    have heq_int : ∫ t, ρ t * g (x - t) = ∫ t, g (x - t) ∂μ := by
      symm
      exact integral_withDensity_ofReal_eq_integral_mul hρ_nonneg hρ_meas.aemeasurable
    rw [heq_int]
    by_cases hg_int_μ : Integrable (fun t => g (x - t)) μ
    · by_cases hgpow_int_μ : Integrable (fun t => |g (x - t)| ^ p.toReal) μ
      · have hJensen := jensen_abs_rpow_integral μ hp_ge_one hg_int_μ hgpow_int_μ
        have heq_pow : ∫ t, |g (x - t)| ^ p.toReal ∂μ =
            (∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal
              ∂volume).toReal := by
          rw [integral_withDensity_ofReal_eq_integral_mul hρ_nonneg hρ_meas.aemeasurable]
          rw [integral_eq_lintegral_of_nonneg_ae]
          · congr 1
            apply lintegral_congr
            intro t
            rw [ENNReal.ofReal_mul (hρ_nonneg t)]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          · exact ae_of_all _ (fun t => mul_nonneg (hρ_nonneg t)
              (Real.rpow_nonneg (abs_nonneg _) _))
          · have habs_rpow_meas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
              have hcont : Continuous (fun y : ℝ => |y| ^ p.toReal) :=
                continuous_abs.rpow_const (fun _ => Or.inr hp_pos.le)
              exact hcont.measurable.comp (hg_meas.comp (measurable_const.sub measurable_id))
            exact (hρ_meas.mul habs_rpow_meas).aestronglyMeasurable
        calc
          ENNReal.ofReal |∫ t, g (x - t) ∂μ| ^ p.toReal =
              ENNReal.ofReal (|∫ t, g (x - t) ∂μ| ^ p.toReal) := by
                rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          _ ≤ ENNReal.ofReal (∫ t, |g (x - t)| ^ p.toReal ∂μ) :=
            ENNReal.ofReal_le_ofReal hJensen
          _ = ENNReal.ofReal ((∫⁻ t, ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume).toReal) := by
            rw [heq_pow]
          _ ≤ ∫⁻ t, ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume :=
            ENNReal.ofReal_toReal_le
      · have hnot_finite : ∫⁻ t, ENNReal.ofReal (ρ t) *
            (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume = ⊤ := by
          have h_eq : ∫⁻ t, ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume =
              ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂μ := by
            have hsub : Measurable (fun t : ℝ × Vec 2 => x - t) := measurable_const.sub measurable_id
            have h_abs_meas : Measurable (fun t => |g (x - t)|) :=
              continuous_abs.measurable.comp (hg_meas.comp hsub)
            have h_meas_pow : Measurable
                (fun t => (ENNReal.ofReal |g (x - t)|) ^ p.toReal) :=
              Measurable.pow_const h_abs_meas.ennreal_ofReal p.toReal
            symm
            convert lintegral_withDensity_eq_lintegral_mul volume
              hρ_meas.ennreal_ofReal h_meas_pow using 2
          rw [h_eq]
          have habs_rpow_nonneg : ∀ t, 0 ≤ |g (x - t)| ^ p.toReal :=
            fun t => Real.rpow_nonneg (abs_nonneg _) _
          have habs_rpow_meas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
            have hcont : Continuous (fun y : ℝ => |y| ^ p.toReal) :=
              continuous_abs.rpow_const (fun _ => Or.inr hp_pos.le)
            have hsub : Measurable (fun t : ℝ × Vec 2 => x - t) := measurable_const.sub measurable_id
            exact hcont.measurable.comp (hg_meas.comp hsub)
          have htop : ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂μ = ⊤ := by
            rw [← lintegral_ofReal_ne_top_iff_integrable habs_rpow_meas.aestronglyMeasurable
                (ae_of_all _ habs_rpow_nonneg)] at hgpow_int_μ
            have htop' : ∫⁻ t, ENNReal.ofReal (|g (x - t)| ^ p.toReal) ∂μ = ⊤ := by
              exact not_ne_iff.mp hgpow_int_μ
            convert htop' using 1
            congr 1
            ext t
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          rw [htop]
        simp [hnot_finite]
    · rw [integral_undef hg_int_μ]
      simp only [abs_zero, ENNReal.ofReal_zero]
      rw [ENNReal.zero_rpow_of_pos hp_pos]
      exact zero_le
  calc
    ∫⁻ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ∂volume ≤
        ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ t) *
          (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume ∂volume :=
      lintegral_mono hpointwise
    _ = (∫⁻ t, ENNReal.ofReal (ρ t) ∂volume) *
          (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := hfubini
    _ = 1 * (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := by rw [hρ_lint_one]
    _ = ∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume := one_mul _
    _ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume := by
      congr 1
      ext x
      rw [Real.enorm_eq_ofReal_abs]

/-- Convolution `ρ ⋆ g` by a nonnegative kernel of integral one is an `L²` contraction
(kernel on the left; internal). -/
private theorem convolution_eLpNorm_le_aux
    {ρ g : ℝ × Vec 2 → ℝ} (hρ_nonneg : ∀ x, 0 ≤ ρ x) (hρ_cont : Continuous ρ)
    (hρ_comp : HasCompactSupport ρ) (hρ_one : ∫ x, ρ x = 1)
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (ℝ × Vec 2))) :
    eLpNorm (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤
      eLpNorm g 2 volume := by
  let g' := hg.aestronglyMeasurable.mk g
  have hg'meas : Measurable g' := hg.aestronglyMeasurable.measurable_mk
  have hfg : g =ᵐ[volume] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hg'mem : MemLp g' (2 : ℝ≥0∞) volume := MemLp.ae_eq hfg hg
  have hkint : Integrable ρ volume := hρ_cont.integrable_of_hasCompactSupport hρ_comp
  have hconvEq : convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume =
      convolution ρ g' (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    MeasureTheory.convolution_congr (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure (ℝ × Vec 2))) EventuallyEq.rfl hfg
  have hconvCont : Continuous (convolution ρ g' (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    (hρ_comp.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (n := 0) (contDiff_zero.2 hρ_cont) (hg'mem.locallyIntegrable (by norm_num))).continuous
  have hbound := young_convolution_nonneg_integral_one
    (ρ := ρ) (g := g') (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    hρ_nonneg hkint hρ_one hρ_cont.measurable hg'meas hconvCont.aestronglyMeasurable
  rw [hconvEq]
  exact hbound.trans_eq (eLpNorm_congr_ae hfg.symm)

/-- Mollification by a nonnegative continuous compactly supported kernel of integral one is an
`L²` contraction. -/
theorem eLpNorm_mollify_le {k f : ℝ × Vec 2 → ℝ} (hk_nonneg : ∀ x, 0 ≤ k x)
    (hk_cont : Continuous k) (hk_comp : HasCompactSupport k) (hk_one : ∫ x, k x = 1)
    (hf : MemLp f (2 : ℝ≥0∞) volume) :
    eLpNorm (mollify f k) 2 volume ≤ eLpNorm f 2 volume := by
  rw [mollify_eq_convolution_left]
  exact convolution_eLpNorm_le_aux hk_nonneg hk_cont hk_comp hk_one hf

/-- Mollification preserves `L²`. -/
theorem memLp_mollify {k f : ℝ × Vec 2 → ℝ} (hk_nonneg : ∀ x, 0 ≤ k x)
    (hk_cont : Continuous k) (hk_comp : HasCompactSupport k) (hk_one : ∫ x, k x = 1)
    (hf : MemLp f (2 : ℝ≥0∞) volume) : MemLp (mollify f k) (2 : ℝ≥0∞) volume := by
  exact (eLpNorm_mollify_le hk_nonneg hk_cont hk_comp hk_one hf).trans_lt hf

private theorem tendsto_eLpNorm_mollify_of_continuous
    {f : ℝ × Vec 2 → ℝ} (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
    {k : ℕ → ℝ × Vec 2 → ℝ} {R : ℕ → ℝ} (hR : Tendsto R atTop (𝓝 0))
    (hk_nonneg : ∀ n x, 0 ≤ k n x) (hk_one : ∀ n, ∫ x, k n x = 1)
    (hk_cont : ∀ n, Continuous (k n)) (hk_comp : ∀ n, HasCompactSupport (k n))
    (hk_supp : ∀ n, Function.support (k n) ⊆ Metric.ball 0 (R n)) :
    Tendsto (fun n => eLpNorm (fun x => mollify f (k n) x - f x) 2 volume) atTop (𝓝 0) := by
  have hp_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  let K : Set (ℝ × Vec 2) := Metric.closedBall 0 1 + tsupport f
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : ℝ × Vec 2) 1).add hf_supp.isCompact
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have hK_ne_top : volume K ≠ ⊤ := hK_compact.measure_lt_top.ne
  have hpow_ne_top : volume K ^ (1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK_ne_top).ne
  let cK : ℝ := (volume K ^ (1 / (2 : ℝ≥0∞).toReal)).toReal
  have hcK_nonneg : 0 ≤ cK := ENNReal.toReal_nonneg
  have hpow_eq : ENNReal.ofReal cK = volume K ^ (1 / (2 : ℝ≥0∞).toReal) :=
    ENNReal.ofReal_toReal hpow_ne_top
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hη_top : η = ⊤
  · exact Eventually.of_forall (fun n => by simp only [hη_top, le_top])
  let δ : ℝ := η.toReal / (cK + 1)
  have hη_real : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hη_top
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨γ, hγ_pos, hγ⟩ :=
    Metric.uniformContinuous_iff.mp (hf_supp.uniformContinuous_of_continuous hf_cont) δ hδ_pos
  have hR_small : ∀ᶠ n in atTop, R n < γ := (tendsto_order.1 hR).2 _ hγ_pos
  have hR_le_one : ∀ᶠ n in atTop, R n ≤ 1 :=
    ((tendsto_order.1 hR).2 _ zero_lt_one).mono (fun _ hn => le_of_lt hn)
  filter_upwards [hR_small, hR_le_one] with n hn_small hn_one
  have hdist : ∀ x, dist (mollify f (k n) x) (f x) ≤ δ := by
    intro x
    rw [mollify_eq_convolution_left]
    refine MeasureTheory.dist_convolution_le (le_of_lt hδ_pos) (hk_supp n) (hk_nonneg n)
      (hk_one n) hf_cont.aestronglyMeasurable ?_
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm_sub] at hy
    apply (hγ ?_).le
    rw [dist_eq_norm_sub]
    exact hy.trans hn_small
  have hconv_support : support (mollify f (k n)) ⊆ K := by
    rw [mollify_eq_convolution_left]
    calc
      support (convolution (k n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          support (k n) + support f := support_convolution_subset _
      _ ⊆ Metric.closedBall 0 1 + tsupport f := by
        apply add_subset_add
        · intro z hz
          exact ((Metric.mem_ball.mp (hk_supp n hz)).le).trans hn_one
        · exact subset_tsupport _
  have hf_support : support f ⊆ K := by
    intro x hx
    refine ⟨0, ?_, x, subset_tsupport f hx, by simp only [zero_add]⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact zero_le_one
  have hbound :
      eLpNorm (fun x => mollify f (k n) x - f x) 2 volume ≤
        ENNReal.ofReal δ * volume K ^ (1 / (2 : ℝ≥0∞).toReal) := by
    have hmeas : AEStronglyMeasurable (fun x => mollify f (k n) x - f x) volume :=
      ((mollify_continuous (hk_cont n) (hk_comp n)
        (hf_cont.integrable_of_hasCompactSupport hf_supp).locallyIntegrable).sub
          hf_cont).aestronglyMeasurable
    exact eLpNorm_sub_le_of_dist_bdd volume hp_top hK_meas.nullMeasurableSet hδ_pos.le
      hmeas hdist hconv_support hf_support
  have hδmul : δ * cK ≤ η.toReal := by
    have hfrac_le : cK / (cK + 1) ≤ 1 :=
      div_le_one_of_le₀ (by linarith only [hcK_nonneg]) (by linarith only [hcK_nonneg])
    calc
      δ * cK = η.toReal * (cK / (cK + 1)) := by
        dsimp [δ]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring_nf
      _ ≤ η.toReal * 1 := mul_le_mul_of_nonneg_left hfrac_le hη_real.le
      _ = η.toReal := mul_one _
  calc
    eLpNorm (fun x => mollify f (k n) x - f x) 2 volume ≤
        ENNReal.ofReal δ * volume K ^ (1 / (2 : ℝ≥0∞).toReal) := hbound
    _ = ENNReal.ofReal (δ * cK) := by
      rw [← hpow_eq, ← ENNReal.ofReal_mul]
      positivity
    _ ≤ η := by
      rw [← ENNReal.ofReal_toReal hη_top]
      exact ENNReal.ofReal_le_ofReal hδmul

/-- `L²` convergence of mollification along kernels supported in shrinking balls. -/
theorem tendsto_eLpNorm_mollify
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f (2 : ℝ≥0∞) volume)
    {k : ℕ → ℝ × Vec 2 → ℝ} {R : ℕ → ℝ} (hR : Tendsto R atTop (𝓝 0))
    (hk_nonneg : ∀ n x, 0 ≤ k n x) (hk_one : ∀ n, ∫ x, k n x = 1)
    (hk_cont : ∀ n, Continuous (k n)) (hk_comp : ∀ n, HasCompactSupport (k n))
    (hk_supp : ∀ n, Function.support (k n) ⊆ Metric.ball 0 (R n)) :
    Tendsto (fun n => eLpNorm (fun x => mollify f (k n) x - f x) 2 volume) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (ℝ × Vec 2)))
      (ε := ℝ) (p := (2 : ℝ≥0∞)) hη.ne'
  obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (ℝ × Vec 2)))
      (ε := ℝ) (p := (2 : ℝ≥0∞)) hη₁_pos.ne'
  let δ : ℝ≥0∞ := min η₁ η₂
  have hδ_pos : 0 < δ := lt_min hη₁_pos hη₂_pos
  obtain ⟨f', hf'_supp, happrox', hf'_cont, hf'_mem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hδ_pos.ne'
  have hdiff_mem : MemLp (fun x => f x - f' x) (2 : ℝ≥0∞) volume := hf.sub hf'_mem
  have hthird_norm : eLpNorm (fun x => f' x - f x) 2 volume ≤ η₁ := by
    have hneg : (fun x => f' x - f x) = -(fun x => f x - f' x) := by
      ext x
      change f' x - f x = -(f x - f' x)
      abel_nf
    rw [hneg, eLpNorm_neg]
    exact happrox'.trans (min_le_left _ _)
  have hmid_eventually : ∀ᶠ n in atTop,
      eLpNorm (fun x => mollify f' (k n) x - f' x) 2 volume ≤ η₂ :=
    ENNReal.tendsto_nhds_zero.1
      (tendsto_eLpNorm_mollify_of_continuous hf'_cont hf'_supp hR hk_nonneg hk_one hk_cont
        hk_comp hk_supp) η₂ hη₂_pos
  filter_upwards [hmid_eventually] with n hmid
  have hf_loc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hf'_loc : LocallyIntegrable f' volume := hf'_mem.locallyIntegrable (by norm_num)
  have hsplit : f = (f - f') + f' := by
    ext x
    simp
  have hconv_split : mollify f (k n) = mollify (f - f') (k n) + mollify f' (k n) := by
    conv_lhs => rw [hsplit]
    exact mollify_add_left (hk_cont n) (hk_comp n) (hf_loc.sub hf'_loc) hf'_loc
  have hfirst_norm : eLpNorm (mollify (f - f') (k n)) 2 volume ≤ η₂ :=
    (eLpNorm_mollify_le (hk_nonneg n) (hk_cont n) (hk_comp n) (hk_one n) hdiff_mem).trans
      (happrox'.trans (min_le_right _ _))
  have hfirst_middle :
      eLpNorm (mollify (f - f') (k n) + fun x => mollify f' (k n) x - f' x) 2 volume < η₁ :=
    hη₂ _ _ hfirst_norm hmid
  have hsum :
      eLpNorm ((mollify (f - f') (k n) + fun x => mollify f' (k n) x - f' x) +
        fun x => f' x - f x) 2 volume < η := hη₁ _ _ hfirst_middle.le hthird_norm
  have hdecomp : (fun x => mollify f (k n) x - f x) =
      (mollify (f - f') (k n) + fun x => mollify f' (k n) x - f' x) +
        fun x => f' x - f x := by
    ext x
    have := congrFun hconv_split x
    simp only [Pi.add_apply] at this ⊢
    rw [this]
    ring
  rw [hdecomp]
  exact hsum.le

/-- Convergence for the shifted bump family: if `|s n| + r n → 0` then
`mollify f (shiftedKernel (s n) (r n) _) → f` in `L²`. -/
theorem tendsto_eLpNorm_mollify_shifted
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f (2 : ℝ≥0∞) volume)
    {s r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hsr : Tendsto (fun n => |s n| + r n) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => mollify f (shiftedKernel (s n) (r n) (hr n)) x - f x) 2 volume)
      atTop (𝓝 0) :=
  tendsto_eLpNorm_mollify hf (R := fun n => |s n| + r n) hsr
    (fun _ x => shiftedKernel_nonneg x) (fun _ => shiftedKernel_integral_one)
    (fun _ => (shiftedKernel_contDiff 0).continuous)
    (fun _ => shiftedKernel_hasCompactSupport)
    (fun _ => shiftedKernel_support_subset_ball)

/-! ### Continuity of the `L²` pairing -/

/-- If `f_n → f` and `h_n → h` in `L²(μ)`, then `∫ f_n h_n → ∫ f h`. -/
theorem tendsto_integral_mul_of_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {fn hn : ℕ → α → ℝ} {f h : α → ℝ}
    (hfn : ∀ n, MemLp (fn n) 2 μ) (hhn : ∀ n, MemLp (hn n) 2 μ)
    (hf : MemLp f 2 μ) (hh : MemLp h 2 μ)
    (hf_lim : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 μ) atTop (𝓝 0))
    (hh_lim : Tendsto (fun n => eLpNorm (fun x => hn n x - h x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, fn n x * hn n x ∂μ) atTop (𝓝 (∫ x, f x * h x ∂μ)) := by
  have h1 := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := atTop) fn hfn f hf).2 hf_lim
  have h2 := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := atTop) hn hhn h hh).2 hh_lim
  have h3 := Filter.Tendsto.inner (𝕜 := ℝ) h1 h2
  have key : ∀ (u v : α → ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ),
      inner ℝ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂μ := by
    intro u v hu hv
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
    simp [mul_comm]
  simp only [key] at h3
  exact h3

end

end AVRegularity.Applications.LocalEnergy
end
end
