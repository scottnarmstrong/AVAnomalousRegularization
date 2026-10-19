-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientPeriodization
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star

@[expose] public section
noncomputable section

section
open Homogenization
namespace AVRegularity.Applications

/-! # Elementary facts on the torus distance

`d(y,z) ≤ |y - z|`, `d ≥ 0`, and `d(y,z) = |y - z|` when `|y - z| ≤ 1/2`.
-/

/-- The Euclidean norm `|v| = √(v·v)` on `ℝ²`. -/
def eNorm (v : Vec 2) : ℝ := Real.sqrt (vecNormSq v)

theorem eNorm_nonneg (v : Vec 2) : 0 ≤ eNorm v := Real.sqrt_nonneg _

theorem eNorm_add_le (a b : Vec 2) : eNorm (a + b) ≤ eNorm a + eNorm b := by
  unfold eNorm
  rw [Real.sqrt_le_left (by positivity)]
  have hdot : vecDot a b ≤ Real.sqrt (vecNormSq a) * Real.sqrt (vecNormSq b) := by
    have h := sq_vecDot_le_vecNormSq_mul_vecNormSq a b
    have hab : 0 ≤ Real.sqrt (vecNormSq a) * Real.sqrt (vecNormSq b) := by positivity
    rw [← Real.sqrt_mul (vecNormSq_nonneg a)]
    exact Real.le_sqrt_of_sq_le h
  have hexp : vecNormSq (a + b) = vecNormSq a + 2 * vecDot a b + vecNormSq b := by
    simp only [vecNormSq, vecDot, Pi.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hexp]
  have ha := Real.sq_sqrt (vecNormSq_nonneg a)
  have hb := Real.sq_sqrt (vecNormSq_nonneg b)
  nlinarith

theorem latticeShift_zero : AVenhance.latticeShift 0 = 0 := by
  funext i; simp [AVenhance.latticeShift]

theorem eNorm_neg (v : Vec 2) : eNorm (-v) = eNorm v := by
  simp [eNorm, vecNormSq, vecDot]

theorem torusDist_nonneg (y z : Vec 2) : 0 ≤ torusDist y z :=
  Real.iInf_nonneg fun _ => Real.sqrt_nonneg _

theorem torusDist_bddBelow (y z : Vec 2) :
    BddBelow (Set.range fun n : Fin 2 → ℤ =>
      Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n))) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact Real.sqrt_nonneg _⟩

theorem torusDist_le_eNorm (y z : Vec 2) : torusDist y z ≤ eNorm (y - z) := by
  have h := ciInf_le (torusDist_bddBelow y z) 0
  rw [latticeShift_zero, sub_zero] at h
  exact h

theorem torusDist_le_shift (y z : Vec 2) (n : Fin 2 → ℤ) :
    torusDist y z ≤ eNorm (y - z - AVenhance.latticeShift n) :=
  ciInf_le (torusDist_bddBelow y z) n

theorem one_le_eNorm_latticeShift {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    1 ≤ eNorm (AVenhance.latticeShift n) := by
  unfold eNorm
  rw [Real.le_sqrt (by norm_num) (vecNormSq_nonneg _), one_pow]
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  have hi1 : (1 : ℝ) ≤ (n i : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n i ^ 2 := by
      rcases lt_or_gt_of_ne hi with h | h <;> nlinarith
    exact_mod_cast this
  have hcoord := sq_apply_le_vecNormSq (AVenhance.latticeShift n) i
  simp only [AVenhance.latticeShift] at hcoord
  linarith

/-- On discs of radius `1/2` the torus distance is the Euclidean one. -/
theorem torusDist_eq_of_small {y z : Vec 2} (h : eNorm (y - z) ≤ 1 / 2) :
    torusDist y z = eNorm (y - z) := by
  refine le_antisymm (torusDist_le_eNorm y z) ?_
  refine le_ciInf fun n => ?_
  change eNorm (y - z) ≤ eNorm (y - z - AVenhance.latticeShift n)
  by_cases hn : n = 0
  · subst hn; rw [latticeShift_zero, sub_zero]
  · have h1 := one_le_eNorm_latticeShift hn
    have h2 := eNorm_add_le (y - z - AVenhance.latticeShift n) (-(y - z))
    have hneg : eNorm (-(y - z)) = eNorm (y - z) := eNorm_neg _
    have hsum : y - z - AVenhance.latticeShift n + -(y - z) = -AVenhance.latticeShift n := by
      abel
    rw [hsum, hneg] at h2
    have hneg2 : eNorm (-AVenhance.latticeShift n) = eNorm (AVenhance.latticeShift n) :=
      eNorm_neg _
    rw [hneg2] at h2
    linarith

theorem torusDist_pos_of_small {y z : Vec 2} (hne : y ≠ z) (h : eNorm (y - z) ≤ 1 / 2) :
    0 < torusDist y z := by
  rw [torusDist_eq_of_small h]
  unfold eNorm
  apply Real.sqrt_pos.mpr
  have hne' : y - z ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i, hi⟩ : ∃ i, (y - z) i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hne' (funext hh)
  have := sq_apply_le_vecNormSq (y - z) i
  have hpos : 0 < (y - z) i ^ 2 := by positivity
  linarith

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity.Applications

/-! # Joint continuity from slice Hölder bounds

If the slices of a weak solution have periodic representatives `Θ t` with a uniform
`C^s(𝕋²)` bound on a time set `I`, then `(t, x) ↦ Θ t x` is continuous on `I × ℝ²`.
Only the weak continuity in time of the solution is used:
the representative is compared with its spatial mollification, whose time dependence is a
weakly continuous pairing. -/

theorem csNormLe_increment {s K : ℝ} {g : Vec 2 → ℝ} (hg : CsNormLe s g K) {y z : Vec 2}
    (hyz : torusDist y z ≠ 0) : |g y - g z| ≤ K * torusDist y z ^ s := by
  have h := hg y y z hyz
  have hpos : 0 < torusDist y z ^ s := by
    have := torusDist_nonneg y z
    exact Real.rpow_pos_of_pos (lt_of_le_of_ne this (Ne.symm hyz)) s
  have h' : |g y - g z| / torusDist y z ^ s ≤ K := by linarith [abs_nonneg (g y)]
  rwa [div_le_iff₀ hpos] at h'

theorem csNormLe_increment_euclid {s K : ℝ} (hs : 0 < s) {g : Vec 2 → ℝ} (hg : CsNormLe s g K)
    {y z : Vec 2} (hyz : eNorm (y - z) ≤ 1 / 2) :
    |g y - g z| ≤ K * eNorm (y - z) ^ s := by
  by_cases h : y = z
  · subst h; simp [eNorm, Real.zero_rpow hs.ne', vecNormSq, vecDot]
  · have hpos := torusDist_pos_of_small h hyz
    have := csNormLe_increment hg hpos.ne'
    rwa [torusDist_eq_of_small hyz] at this

theorem csNormLe_K_nonneg {s K : ℝ} {g : Vec 2 → ℝ} (hg : CsNormLe s g K) : 0 ≤ K := by
  have hne : torusDist (0 : Vec 2) (fun _ => 1 / 4) ≠ 0 := by
    have hsmall : eNorm ((0 : Vec 2) - fun _ => 1 / 4) ≤ 1 / 2 := by
      unfold eNorm
      rw [Real.sqrt_le_left (by norm_num)]
      simp [vecNormSq, vecDot]
      norm_num
    have hne0 : (0 : Vec 2) ≠ fun _ => 1 / 4 := by
      intro h; have := congrFun h 0; norm_num at this
    exact (torusDist_pos_of_small hne0 hsmall).ne'
  have h := hg 0 0 (fun _ => 1 / 4) hne
  have h1 : 0 ≤ |g 0 - g fun _ => 1 / 4| / torusDist 0 (fun _ => 1 / 4) ^ s :=
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (torusDist_nonneg _ _) _)
  linarith [abs_nonneg (g 0)]

theorem continuous_of_csNormLe {s K : ℝ} (hs : 0 < s) {g : Vec 2 → ℝ} (hg : CsNormLe s g K) :
    Continuous g := by
  have hK := csNormLe_K_nonneg hg
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨δ, hδ, hδ4, hδε⟩ : ∃ δ > 0, δ ≤ 1 / 4 ∧ K * (2 * δ) ^ s < ε := by
    have ht : Tendsto (fun δ : ℝ => K * (2 * δ) ^ s) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun δ : ℝ => K * (2 * |δ|) ^ s :=
        continuous_const.mul ((continuous_const.mul continuous_abs).rpow_const
          fun _ => Or.inr hs.le)
      have := hc.tendsto 0
      simp only [abs_zero, mul_zero, Real.zero_rpow hs.ne'] at this
      refine (this.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [abs_of_pos hδ]
    have hev := (ht.eventually (gt_mem_nhds hε)).and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))
    obtain ⟨δ, hδ1, hδ2⟩ := hev.exists
    exact ⟨δ, hδ2.1, hδ2.2.le, hδ1⟩
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [Real.dist_eq]
  have he : eNorm (y - x) ≤ 2 * δ := by
    unfold eNorm
    rw [Real.sqrt_le_left (by positivity)]
    have h0 := (dist_pi_lt_iff hδ).1 hy 0
    have h1 := (dist_pi_lt_iff hδ).1 hy 1
    rw [Real.dist_eq] at h0 h1
    simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.sub_apply]
    nlinarith [abs_lt.1 h0, abs_lt.1 h1]
  have he2 : eNorm (y - x) ≤ 1 / 2 := by linarith
  calc |g y - g x| ≤ K * eNorm (y - x) ^ s := csNormLe_increment_euclid hs hg he2
    _ ≤ K * (2 * δ) ^ s := by
        gcongr
        exact eNorm_nonneg _
    _ < ε := hδε

/-! # Joint continuity of the slice representatives -/

section
/-- The mollifier `y ↦ ρ_r(x - y)` with `ρ_r` a normed bump supported in the sup-ball `B_r`. -/
def molKernel (r : ℝ) (hr : 0 < r) (x : Vec 2) : Vec 2 → ℝ :=
  fun y => (⟨r / 2, r, by positivity, by linarith⟩ : ContDiffBump (0 : Vec 2)).normed volume (x - y)

theorem molKernel_nonneg {r : ℝ} (hr : 0 < r) (x y : Vec 2) : 0 ≤ molKernel r hr x y :=
  ContDiffBump.nonneg_normed _ _

theorem molKernel_contDiff {r : ℝ} (hr : 0 < r) (x : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (molKernel r hr x) :=
  (ContDiffBump.contDiff_normed _).comp (contDiff_const.sub contDiff_id)

theorem molKernel_hasCompactSupport {r : ℝ} (hr : 0 < r) (x : Vec 2) :
    HasCompactSupport (molKernel r hr x) := by
  have h := (ContDiffBump.hasCompactSupport_normed
    (⟨r / 2, r, by positivity, by linarith⟩ : ContDiffBump (0 : Vec 2)) (μ := volume))
  have hh : Topology.IsClosedEmbedding (fun y : Vec 2 => x - y) :=
    (Homeomorph.subLeft x).isClosedEmbedding
  exact h.comp_isClosedEmbedding hh

theorem molKernel_integral {r : ℝ} (hr : 0 < r) (x : Vec 2) : ∫ y, molKernel r hr x y = 1 := by
  unfold molKernel
  rw [integral_sub_left_eq_self (fun y => (⟨r / 2, r, by positivity, by linarith⟩ :
    ContDiffBump (0 : Vec 2)).normed volume y) volume x]
  exact ContDiffBump.integral_normed _

theorem molKernel_support {r : ℝ} (hr : 0 < r) {x y : Vec 2} (hy : molKernel r hr x y ≠ 0) :
    dist y x < r := by
  have h : x - y ∈ Function.support
      ((⟨r / 2, r, by positivity, by linarith⟩ : ContDiffBump (0 : Vec 2)).normed volume) := hy
  rw [ContDiffBump.support_normed_eq] at h
  simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using h

theorem eNorm_le_of_dist {x y : Vec 2} {r : ℝ} (h : dist y x < r) : eNorm (y - x) ≤ 2 * r := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg h
  unfold eNorm
  rw [Real.sqrt_le_left (by positivity)]
  have h0 := (dist_pi_lt_iff hr).1 h 0
  have h1 := (dist_pi_lt_iff hr).1 h 1
  rw [Real.dist_eq] at h0 h1
  simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.sub_apply]
  nlinarith [abs_lt.1 h0, abs_lt.1 h1]

/-- The mollification of a `C^s(𝕋²)` function is `K (2r)^s`-close to it. -/
theorem abs_sub_mollify_le {s K r : ℝ} (hs : 0 < s) (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {g : Vec 2 → ℝ} (hg : CsNormLe s g K) (x : Vec 2) :
    |g x - ∫ y, g y * molKernel r hr x y| ≤ K * (2 * (2 * r)) ^ s := by
  have hK := csNormLe_K_nonneg hg
  have hgc := continuous_of_csNormLe hs hg
  have hwc := (molKernel_contDiff hr x).continuous
  have hint : Integrable (fun y => g y * molKernel r hr x y) volume :=
    (hgc.mul hwc).integrable_of_hasCompactSupport ((molKernel_hasCompactSupport hr x).mul_left)
  have hint1 : Integrable (fun y => molKernel r hr x y) volume :=
    hwc.integrable_of_hasCompactSupport (molKernel_hasCompactSupport hr x)
  have hrepr : g x - ∫ y, g y * molKernel r hr x y = ∫ y, (g x - g y) * molKernel r hr x y := by
    have e1 := integral_sub (μ := volume) (f := fun y => g x * molKernel r hr x y)
      (g := fun y => g y * molKernel r hr x y) (hint1.const_mul _) hint
    have e2 := integral_const_mul (μ := volume) (g x) (fun y => molKernel r hr x y)
    have e3 : (fun y => (g x - g y) * molKernel r hr x y) =
        fun y => g x * molKernel r hr x y - g y * molKernel r hr x y := by
      funext y; ring
    rw [e3, e1, e2, molKernel_integral, mul_one]
  rw [hrepr]
  calc |∫ y, (g x - g y) * molKernel r hr x y|
      ≤ ∫ y, |(g x - g y) * molKernel r hr x y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, K * (2 * (2 * r)) ^ s * molKernel r hr x y := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hint1.const_mul _) (Eventually.of_forall fun y => ?_)
        simp only
        rw [abs_mul, abs_of_nonneg (molKernel_nonneg hr x y)]
        by_cases hy : molKernel r hr x y = 0
        · simp [hy]
        · refine mul_le_mul_of_nonneg_right ?_ (molKernel_nonneg hr x y)
          have hd := molKernel_support hr hy
          have he := eNorm_le_of_dist hd
          have he2 : eNorm (x - y) ≤ 1 / 2 := by
            rw [show x - y = -(y - x) by abel, eNorm_neg]; linarith
          calc |g x - g y| ≤ K * eNorm (x - y) ^ s := csNormLe_increment_euclid hs hg he2
            _ ≤ K * (2 * (2 * r)) ^ s := by
                gcongr
                · exact eNorm_nonneg _
                · rw [show x - y = -(y - x) by abel, eNorm_neg]; linarith
    _ = K * (2 * (2 * r)) ^ s := by rw [integral_const_mul, molKernel_integral, mul_one]

open AVenhance.Infra.Parabolic.FourierGalerkin in
/-- The mollified slice pairs against the periodized kernel. -/
theorem integral_mul_molKernel_eq {r : ℝ} (hr : 0 < r) (x : Vec 2) {g h : Vec 2 → ℝ}
    (hg : MemLp g 2 (volume.restrict unitCube)) (hgp : IsZ2Periodic g)
    (hgh : g =ᵐ[volume.restrict unitCube] h) :
    ∫ y, g y * molKernel r hr x y =
      ∫ y in unitCube, h y * compactTestPeriodization (molKernel r hr x) y := by
  have h1 := (WeakGradientPeriodization.integral_periodic_mul_compact_eq_cell_periodization hg hgp
    (molKernel_contDiff hr x).continuous (molKernel_hasCompactSupport hr x)).2
  rw [h1, setIntegral_congr_set WeakGradientPeriodization.periodCell_ae_unitCube]
  refine setIntegral_congr_ae (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) |>.1 hgh]
    with y hy hmem
  rw [hy hmem]

open AVenhance.Infra.Parabolic.FourierGalerkin in
/-- **Joint continuity**: uniform `C^s(𝕋²)` bounds on periodic representatives of the slices
of a weak solution make them jointly continuous (the continuity of `θ^κ` in Corollary D(a) of
the paper). -/
theorem continuousOn_of_csNormLe_slices {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} (hθ : IsWeakSolutionOn b κ t₁ t₂ f θ) {s K : ℝ}
    (hs : 0 < s) {I : Set ℝ} (hI : I ⊆ Set.Icc t₁ t₂) {Θ : ℝ → Vec 2 → ℝ}
    (hΘ : ∀ t ∈ I, IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
      CsNormLe s (Θ t) K) :
    ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (I ×ˢ Set.univ) := by
  obtain ⟨Dθ, hslice, -, -, -, -, -, hcont, -⟩ := hθ
  rw [Metric.continuousOn_iff]
  rintro ⟨t, x⟩ ⟨ht, -⟩ ε hε
  have hK : 0 ≤ K := csNormLe_K_nonneg (hΘ t ht).2.2
  -- choose the mollification radius
  obtain ⟨r, hr, hr4, hrε⟩ : ∃ r > 0, r ≤ 1 / 4 ∧ 2 * (K * (2 * (2 * r)) ^ s) < ε / 3 := by
    have hc : Continuous fun r : ℝ => 2 * (K * (2 * (2 * |r|)) ^ s) :=
      continuous_const.mul (continuous_const.mul ((continuous_const.mul
        (continuous_const.mul continuous_abs)).rpow_const fun _ => Or.inr hs.le))
    have := hc.tendsto 0
    simp only [abs_zero, mul_zero, Real.zero_rpow hs.ne'] at this
    have hev := (this.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).filter_mono
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    obtain ⟨r, hr1, hr2⟩ := (hev.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
    refine ⟨r, hr2.1, hr2.2.le, ?_⟩
    rwa [abs_of_pos hr2.1] at hr1
  set ψ := compactTestPeriodization (molKernel r hr x)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    compactTestPeriodization_contDiff (molKernel_hasCompactSupport hr x) (molKernel_contDiff hr x)
  have hψp : IsZ2Periodic ψ := compactTestPeriodization_periodic
  have hA : ContinuousOn (fun τ => ∫ y in unitCube, θ τ y * ψ y) I :=
    (hcont ψ hψ hψp).mono hI
  have hAeq : ∀ τ ∈ I, ∫ y, Θ τ y * molKernel r hr x y = ∫ y in unitCube, θ τ y * ψ y := by
    intro τ hτ
    obtain ⟨hp, hae, -⟩ := hΘ τ hτ
    have hmem : MemLp (Θ τ) 2 (volume.restrict unitCube) :=
      (hslice τ (hI hτ)).2.ae_eq hae.symm
    exact integral_mul_molKernel_eq hr x hmem hp hae
  -- time continuity of the pairing
  obtain ⟨δ₁, hδ₁, hδ₁ε⟩ := (Metric.continuousOn_iff.1 hA) t ht (ε / 3) (by linarith)
  -- spatial modulus
  obtain ⟨δ₂, hδ₂, hδ₂4, hδ₂ε⟩ : ∃ δ > 0, δ ≤ 1 / 4 ∧ K * (2 * δ) ^ s < ε / 3 := by
    have hc : Continuous fun δ : ℝ => K * (2 * |δ|) ^ s :=
      continuous_const.mul ((continuous_const.mul continuous_abs).rpow_const
        fun _ => Or.inr hs.le)
    have := hc.tendsto 0
    simp only [abs_zero, mul_zero, Real.zero_rpow hs.ne'] at this
    have hev := (this.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).filter_mono
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    obtain ⟨δ, hd1, hd2⟩ := (hev.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
    refine ⟨δ, hd2.1, hd2.2.le, ?_⟩
    rwa [abs_of_pos hd2.1] at hd1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  rintro ⟨t', x'⟩ ⟨ht', -⟩ hdist
  have hd1 : dist t' t < δ₁ := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hdist (min_le_left _ _))
  have hd2 : dist x' x < δ₂ := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hdist (min_le_right _ _))
  simp only [Real.dist_eq]
  have hmolt' := abs_sub_mollify_le hs hr hr4 (hΘ t' ht').2.2 x
  have hmolt := abs_sub_mollify_le hs hr hr4 (hΘ t ht).2.2 x
  have hpair := hδ₁ε t' ht' hd1
  rw [Real.dist_eq, ← hAeq t' ht', ← hAeq t ht] at hpair
  have hsp : |Θ t' x' - Θ t' x| ≤ K * (2 * δ₂) ^ s := by
    have he := eNorm_le_of_dist hd2
    have he2 : eNorm (x' - x) ≤ 1 / 2 := by linarith
    calc |Θ t' x' - Θ t' x| ≤ K * eNorm (x' - x) ^ s :=
          csNormLe_increment_euclid hs (hΘ t' ht').2.2 he2
      _ ≤ K * (2 * δ₂) ^ s := by gcongr; exact eNorm_nonneg _
  have htri : |Θ t' x' - Θ t x| ≤ |Θ t' x' - Θ t' x| +
      |Θ t' x - ∫ y, Θ t' y * molKernel r hr x y| +
      |(∫ y, Θ t' y * molKernel r hr x y) - ∫ y, Θ t y * molKernel r hr x y| +
      |Θ t x - ∫ y, Θ t y * molKernel r hr x y| := by
    have := abs_sub_le (Θ t' x') (Θ t' x) (Θ t x)
    have h2 := abs_sub_le (Θ t' x) (∫ y, Θ t' y * molKernel r hr x y) (Θ t x)
    have h3 := abs_sub_le (∫ y, Θ t' y * molKernel r hr x y) (∫ y, Θ t y * molKernel r hr x y)
      (Θ t x)
    rw [abs_sub_comm (∫ y, Θ t y * molKernel r hr x y) (Θ t x)] at h3
    linarith
  linarith
end

end AVRegularity.Applications
end
