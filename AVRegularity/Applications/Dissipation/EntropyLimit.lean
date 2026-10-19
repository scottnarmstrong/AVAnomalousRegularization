-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Dissipation.EntropyCutoff
public import AVenhance.Infra.Parabolic.WeakUniqueness.WeakEnergyPassage
public import AVenhance.Statements.Roots.IsDivFree
import AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy
import Mathlib.Algebra.Order.Chebyshev
import AVenhance.Infra.Classical.GalerkinGenerator

/-! # Convex entropy inequality for weak solutions: the passage `N → ∞`

Unit window, upstream form. From the cutoff inequality `integral_comp_cutoff_le`
`∫ J(u_N(t)) ≤ ∫ J(u_N(0)) - ∫_0^t ∫ P_N(B·D) J'(u_N)`, with `0 ≤ J'' ≤ L`:

* `∫ J(u_N(t)) → ∫ J(u(t))` and `∫ J(u_N(0)) = ∫ J(P_N f) → ∫ J(f)`
  (`tendsto_integral_comp_of_tendsto_l2NormSq`);
* `P_N G → G` in spacetime `L²` for every spacetime-`L²` path `G` with cell-`L²` slices
  (`tendsto_integral_sq_sub_cutoff_timeCube`);
* `∫∫ B·∇u_N J'(u_N) = ∫∫ B·∇(J(u_N)) = 0` for a divergence-free drift, and
  `P_N(B·D) - B·∇u_N → 0` in spacetime `L²` while `J'(u_N)` stays bounded there, so the drift
  term of the cutoff inequality tends to `0`.

Hence `∫ J(u(t)) ≤ ∫ J(f)` (`integral_convex_le_of_isWeakSolutionGrad`). -/

public section

open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Parabolic.WeakUniqueness AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Classical

namespace AVRegularity.Applications.Dissipation

/-- The unit cell has finite measure. -/
local instance dissipationLimitFiniteCube : IsFiniteMeasure (volume.restrict unitCube) :=
  isFiniteMeasure_restrict.2 unitCube_measure_ne_top

/-! ### Growth of `J` from a bounded second derivative -/

/-- `|J'(r)| ≤ |J'(0)| + L |r|` when `|J''| ≤ L`. -/
theorem abs_deriv_le_of_abs_deriv2_le {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) {L : ℝ}
    (hL : ∀ r, |deriv (deriv J) r| ≤ L) (r : ℝ) :
    |deriv J r| ≤ |deriv J 0| + L * |r| := by
  have hd := differentiable_deriv_of_smooth hJ
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (f := deriv J)
    (fun x _ => hd x) (fun x _ => by simpa [Real.norm_eq_abs] using hL x) convex_univ
    (Set.mem_univ 0) (Set.mem_univ r)
  simp only [Real.norm_eq_abs, sub_zero] at h
  have := abs_sub_abs_le_abs_sub (deriv J r) (deriv J 0)
  linarith

/-- `|J(a) - J(b)| ≤ (|J'(0)| + L(|a| + |b|)) |a - b|` when `|J''| ≤ L`. -/
theorem abs_sub_le_of_abs_deriv2_le {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) {L : ℝ}
    (hL : ∀ r, |deriv (deriv J) r| ≤ L) (a b : ℝ) :
    |J a - J b| ≤ (|deriv J 0| + L * (|a| + |b|)) * |a - b| := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hd : Differentiable ℝ J := hJ.differentiable (by simp)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.uIcc b a) (f := J)
    (C := |deriv J 0| + L * (|a| + |b|)) (fun x _ => hd x) (fun x hx => by
      rw [Real.norm_eq_abs]
      refine (abs_deriv_le_of_abs_deriv2_le hJ hL x).trans ?_
      have hx' : |x| ≤ |a| + |b| := by
        rcases Set.mem_uIcc.1 hx with h | h
        · exact (abs_le.2 ⟨by linarith [neg_abs_le b, neg_abs_le a, abs_nonneg a],
            by linarith [le_abs_self a, abs_nonneg b]⟩)
        · exact (abs_le.2 ⟨by linarith [neg_abs_le a, neg_abs_le b, abs_nonneg b],
            by linarith [le_abs_self b, abs_nonneg a]⟩)
      nlinarith [mul_le_mul_of_nonneg_left hx' hL0])
    (convex_uIcc b a) Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using h

/-- `|J(r)| ≤ |J(0)| + (|J'(0)| + L|r|) |r|` when `|J''| ≤ L`. -/
theorem abs_le_of_abs_deriv2_le {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) {L : ℝ}
    (hL : ∀ r, |deriv (deriv J) r| ≤ L) (r : ℝ) :
    |J r| ≤ |J 0| + (|deriv J 0| + L * |r|) * |r| := by
  have h := abs_sub_le_of_abs_deriv2_le hJ hL r 0
  simp only [abs_zero, add_zero, sub_zero] at h
  have := abs_sub_abs_le_abs_sub (J r) (J 0)
  linarith

/-- `J ∘ g` is integrable on the cell for a cell-`L²` `g` when `|J''| ≤ L`. -/
theorem integrable_comp_of_abs_deriv2_le {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) {L : ℝ}
    (hL : ∀ r, |deriv (deriv J) r| ≤ L) {g : Vec 2 → ℝ} (hg : MemL2On unitCube g) :
    Integrable (fun x => J (g x)) (volume.restrict unitCube) := by
  have hb : Integrable (fun x => |J 0| + (|deriv J 0| * |g x| + L * g x ^ 2))
      (volume.restrict unitCube) :=
    (integrable_const _).add (((hg.integrable one_le_two).abs.const_mul _).add
      (hg.integrable_sq.const_mul L))
  refine hb.mono' (hJ.continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  have := abs_le_of_abs_deriv2_le hJ hL (g x)
  have e : (|deriv J 0| + L * |g x|) * |g x| = |deriv J 0| * |g x| + L * g x ^ 2 := by
    rw [add_mul, mul_assoc, ← sq, sq_abs]
  linarith

/-- If `g_N → g` in cell `L²` then `∫ J(g_N) → ∫ J(g)`, when `|J''| ≤ L`. -/
theorem tendsto_integral_comp_of_tendsto_l2NormSq {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J)
    {L : ℝ} (hL : ∀ r, |deriv (deriv J) r| ≤ L) {g : Vec 2 → ℝ} {gN : ℕ → Vec 2 → ℝ}
    (hg : MemL2On unitCube g) (hgN : ∀ N, MemL2On unitCube (gN N))
    (hlim : Tendsto (fun N => l2NormSq (fun x => g x - gN N x)) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ x in unitCube, J (gN N x)) atTop (𝓝 (∫ x in unitCube, J (g x))) := by
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  set A := |deriv J 0|
  -- the weight `F_N = A + L|g| + L|g_N|`
  have hF : ∀ N, MemL2On unitCube (fun x => A + L * |g x| + L * |gN N x|) := fun N =>
    ((memLp_const A).add (hg.norm.const_mul L)).add ((hgN N).norm.const_mul L)
  have hdiff : ∀ N, MemL2On unitCube (fun x => gN N x - g x) := fun N => (hgN N).sub hg
  have hpoint : ∀ N, |(∫ x in unitCube, J (gN N x)) - ∫ x in unitCube, J (g x)| ≤
      Real.sqrt (∫ x in unitCube, (A + L * |g x| + L * |gN N x|) ^ 2) *
        Real.sqrt (l2NormSq (fun x => g x - gN N x)) := by
    intro N
    rw [← integral_sub (integrable_comp_of_abs_deriv2_le hJ hL (hgN N))
      (integrable_comp_of_abs_deriv2_le hJ hL hg)]
    have hprod : Integrable (fun x => (A + L * |g x| + L * |gN N x|) * |gN N x - g x|)
        (volume.restrict unitCube) :=
      weak_product_integrable_cell (hF N) (hdiff N).norm
    refine (abs_integral_le_integral_abs).trans ((integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => abs_nonneg _) hprod
      (Filter.Eventually.of_forall fun x => ?_)).trans ?_)
    · have h := abs_sub_le_of_abs_deriv2_le hJ hL (gN N x) (g x)
      simp only
      linarith [h]
    · have h := WeakEnergyPassage.weakEnergy_l2_pairing_bound (hF N) (hdiff N).norm
      have e1 : (∫ x in unitCube, (A + L * |g x| + L * |gN N x|) * |gN N x - g x|) =
          abs (∫ x in unitCube, (A + L * |g x| + L * |gN N x|) * |gN N x - g x|) :=
        (abs_of_nonneg (integral_nonneg fun x => mul_nonneg
          (by positivity) (abs_nonneg _))).symm
      have e2 : (∫ x in unitCube, |gN N x - g x| ^ 2) = l2NormSq (fun x => g x - gN N x) := by
        unfold l2NormSq
        congr 1
        funext x
        rw [sq_abs]
        ring
      rw [e1]
      simpa only [Real.norm_eq_abs, e2] using h
  have hev : ∀ᶠ N in atTop, l2NormSq (fun x => g x - gN N x) ≤ 1 :=
    hlim.eventually (ge_mem_nhds one_pos)
  have hi1 : Integrable (fun x => 3 * A ^ 2 + 9 * L ^ 2 * g x ^ 2) (volume.restrict unitCube) :=
    (integrable_const _).add (hg.integrable_sq.const_mul _)
  have hbound : ∀ N, ∫ x in unitCube, (A + L * |g x| + L * |gN N x|) ^ 2 ≤
      (∫ x in unitCube, (3 * A ^ 2 + 9 * L ^ 2 * g x ^ 2)) +
        6 * L ^ 2 * l2NormSq (fun x => g x - gN N x) := by
    intro N
    have hi2 : Integrable (fun x => (g x - gN N x) ^ 2) (volume.restrict unitCube) :=
      (hg.sub (hgN N)).integrable_sq
    have h := integral_mono (hF N).integrable_sq (hi1.add (hi2.const_mul (6 * L ^ 2)))
      (fun x => by
        have hb : (L * |g x|) ^ 2 = L ^ 2 * g x ^ 2 := by rw [mul_pow, sq_abs]
        have hc : (L * |gN N x|) ^ 2 = L ^ 2 * gN N x ^ 2 := by rw [mul_pow, sq_abs]
        have h1 : (A + L * |g x| + L * |gN N x|) ^ 2 ≤
            3 * (A ^ 2 + (L * |g x|) ^ 2 + (L * |gN N x|) ^ 2) := by
          nlinarith [sq_nonneg (A - L * |g x|), sq_nonneg (L * |g x| - L * |gN N x|),
            sq_nonneg (A - L * |gN N x|)]
        have h2 : gN N x ^ 2 ≤ 2 * g x ^ 2 + 2 * (g x - gN N x) ^ 2 := by
          nlinarith [sq_nonneg (2 * g x - gN N x)]
        have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
        simp only [Pi.add_apply]
        nlinarith [h1, h3, hb, hc])
    refine h.trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    rw [integral_add hi1 (hi2.const_mul _), integral_const_mul]
    rfl
  have hsq : Tendsto (fun N => Real.sqrt ((∫ x in unitCube, (3 * A ^ 2 + 9 * L ^ 2 * g x ^ 2)) +
      6 * L ^ 2) * Real.sqrt (l2NormSq (fun x => g x - gN N x))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    simpa using this.const_mul (Real.sqrt ((∫ x in unitCube, (3 * A ^ 2 + 9 * L ^ 2 * g x ^ 2)) +
      6 * L ^ 2))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_ hsq
  filter_upwards [hev] with N hN
  rw [Real.norm_eq_abs]
  refine (hpoint N).trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
  have := hbound N
  nlinarith [mul_le_mul_of_nonneg_left hN (sq_nonneg L)]

/-! ### Cutoffs of a spacetime-`L²` path -/

/-- The unit cylinder has finite measure. -/
local instance dissipationLimitFiniteTimeCube : IsFiniteMeasure (volume.restrict timeCube) := by
  rw [weakEnergy_timeCube_measure_eq_product]
  infer_instance

/-- **Spacetime convergence of cutoffs.** For a spacetime-`L²` path `G` on the unit cylinder
with cell-`L²` slices, the cutoffs `P_N G` are spacetime `L²` and converge to `G` there. -/
theorem tendsto_integral_sq_sub_cutoff_timeCube {G : ℝ → Vec 2 → ℝ}
    (hG : MemLp (fun p : ℝ × Vec 2 => G p.1 p.2) 2 (volume.restrict timeCube))
    (hGs : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), MemL2On unitCube (G s)) :
    (∀ N, MemLp (fun p : ℝ × Vec 2 => weakFourierModeProjection N G p.1 p.2) 2
      (volume.restrict timeCube)) ∧
    Tendsto (fun N => ∫ p in timeCube,
      (G p.1 p.2 - weakFourierModeProjection N G p.1 p.2) ^ 2) atTop (𝓝 0) := by
  classical
  have hμ := weakEnergy_timeCube_measure_eq_product
  have hℓ : Integrable (fun s => l2NormSq (G s)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h := hG.integrable_sq
    rw [hμ] at h
    exact h.integral_prod_left
  have hproj : ∀ N, MemLp (fun p : ℝ × Vec 2 => weakFourierModeProjection N G p.1 p.2) 2
      (volume.restrict timeCube) := by
    intro N
    have hGe : ∀ j, Integrable (fun p : ℝ × Vec 2 => G p.1 p.2 * cutMode N j p.2)
        ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict unitCube)) := by
      intro j
      rw [← hμ]
      obtain ⟨C, hC⟩ := exists_bound_cube (cutMode_continuous N j)
      refine (hG.integrable one_le_two).mul_bdd
        ((cutMode_continuous N j).comp continuous_snd).aestronglyMeasurable (c := C) ?_
      filter_upwards [ae_restrict_mem WeakEnergyPassage.weakEnergy_timeCube_measurable] with p hp
      simpa [Real.norm_eq_abs] using hC p.2 hp.2
    have hexpand : (fun p : ℝ × Vec 2 => weakFourierModeProjection N G p.1 p.2) =
        fun p => ∑ j, (∫ x in unitCube, G p.1 x * cutMode N j x) * cutMode N j p.2 := by
      funext p
      simp only [weakFourierModeProjection, realFourierModeAmbientExpansion,
        coefficientPath_apply]
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × Vec 2 => weakFourierModeProjection N G p.1 p.2)
        (volume.restrict timeCube) := by
      rw [hexpand, hμ]
      refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
      exact ((hGe j).integral_prod_left.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).mul
        ((cutMode_continuous N j).comp continuous_snd).aestronglyMeasurable
    have hB := fun j => exists_bound_cube (cutMode_continuous N j)
    choose B hB using hB
    let K : ℝ := (Fintype.card (Fin (RealFourierDimension N)) : ℝ) *
      ∑ j, (∫ x in unitCube, cutMode N j x ^ 2) * B j ^ 2
    have hdom : Integrable (fun p : ℝ × Vec 2 => K * l2NormSq (G p.1))
        (volume.restrict timeCube) := by
      rw [hμ]
      exact (hℓ.const_mul K).comp_fst _
    rw [memLp_two_iff_integrable_sq hmeas]
    refine hdom.mono' (hmeas.pow 2) ?_
    rw [hμ]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hGs,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_unitCube')]
      with p hp hx
    have hγ : ∀ j, (∫ x in unitCube, G p.1 x * cutMode N j x) ^ 2 ≤
        l2NormSq (G p.1) * ∫ x in unitCube, cutMode N j x ^ 2 := by
      intro j
      have h := WeakEnergyPassage.weakEnergy_l2_pairing_bound hp
        (weak_continuous_memL2On (cutMode_continuous N j))
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
        Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)] at h2
      exact h2
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    rw [show weakFourierModeProjection N G p.1 p.2 = _ from congrFun hexpand p]
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => (∫ x in unitCube, G p.1 x * cutMode N j x) * cutMode N j p.2)).trans ?_
    have hK : K * l2NormSq (G p.1) = ((Finset.univ : Finset (Fin (RealFourierDimension N))).card : ℝ) *
        ∑ j, (∫ x in unitCube, cutMode N j x ^ 2) * B j ^ 2 * l2NormSq (G p.1) := by
      simp only [K, Finset.card_univ]
      rw [mul_assoc, Finset.sum_mul]
    rw [hK]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg (α := ℝ) _)
    rw [mul_pow]
    have he : cutMode N j p.2 ^ 2 ≤ B j ^ 2 := by
      have := hB j p.2 hx
      nlinarith [abs_nonneg (cutMode N j p.2), sq_abs (cutMode N j p.2)]
    have hℓ0 : 0 ≤ l2NormSq (G p.1) := integral_nonneg fun x => sq_nonneg _
    have hE0 : 0 ≤ ∫ x in unitCube, cutMode N j x ^ 2 := integral_nonneg fun x => sq_nonneg _
    calc (∫ x in unitCube, G p.1 x * cutMode N j x) ^ 2 * cutMode N j p.2 ^ 2
        ≤ (l2NormSq (G p.1) * ∫ x in unitCube, cutMode N j x ^ 2) * B j ^ 2 :=
          mul_le_mul (hγ j) he (sq_nonneg _) (mul_nonneg hℓ0 hE0)
      _ = (∫ x in unitCube, cutMode N j x ^ 2) * B j ^ 2 * l2NormSq (G p.1) := by ring
  refine ⟨hproj, ?_⟩
  have herr : ∀ N, Integrable (fun p : ℝ × Vec 2 =>
      (G p.1 p.2 - weakFourierModeProjection N G p.1 p.2) ^ 2) (volume.restrict timeCube) :=
    fun N => (hG.sub (hproj N)).integrable_sq
  have hF : ∀ N, ∫ p in timeCube, (G p.1 p.2 - weakFourierModeProjection N G p.1 p.2) ^ 2 =
      ∫ s in Set.Ioo (0 : ℝ) 1, l2NormSq (fun x => G s x - weakFourierModeProjection N G s x) :=
    fun N => WeakEnergyPassage.weakEnergy_timeCube_integral_eq_Ioo_cell (herr N)
  simp only [hF]
  have hmeasF : ∀ N, AEStronglyMeasurable
      (fun s => l2NormSq (fun x => G s x - weakFourierModeProjection N G s x))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    intro N
    have h := herr N
    rw [hμ] at h
    exact h.integral_prod_left.aestronglyMeasurable
  have hlim := tendsto_integral_of_dominated_convergence (fun s => l2NormSq (G s)) hmeasF hℓ
    (fun N => by
      filter_upwards [hGs] with s hs
      have h0 : (0 : ℝ) ≤ l2NormSq (fun x => G s x - weakFourierModeProjection N G s x) :=
        integral_nonneg fun x => sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact l2NormSq_sub_cutoff_le hs N)
    (by
      filter_upwards [hGs] with s hs
      exact tendsto_l2NormSq_sub_cutoff hs)
  simpa using hlim

/-! ### Pairings on the truncated cylinder -/

/-- If `X_N → 0` in spacetime `L²` and `Y_N` stays bounded there, the pairings of `X_N` and
`Y_N` on `(0, t) × 𝕋²` tend to `0`. -/
theorem tendsto_region_pairing_zero {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {X Y : ℕ → ℝ × Vec 2 → ℝ} (hX : ∀ N, MemLp (X N) 2 (volume.restrict timeCube))
    (hY : ∀ N, MemLp (Y N) 2 (volume.restrict timeCube))
    (hX0 : Tendsto (fun N => ∫ p in timeCube, X N p ^ 2) atTop (𝓝 0)) {M : ℝ}
    (hYb : ∀ᶠ N in atTop, ∫ p in timeCube, Y N p ^ 2 ≤ M) :
    Tendsto (fun N => ∫ p in weakEnergyRegion t, X N p * Y N p) atTop (𝓝 0) := by
  have hμ : volume.restrict (weakEnergyRegion t) ≤ volume.restrict timeCube :=
    Measure.restrict_mono (weakEnergy_region_subset_timeCube ht) le_rfl
  have hupper : Tendsto (fun N => Real.sqrt (∫ p in timeCube, X N p ^ 2) * Real.sqrt M) atTop
      (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).comp hX0).mul_const (Real.sqrt M)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_ hupper
  filter_upwards [hYb] with N hN
  rw [Real.norm_eq_abs]
  have hpair := WeakEnergyPassage.weakEnergy_l2_pairing_bound ((hX N).mono_measure hμ)
    ((hY N).mono_measure hμ)
  refine hpair.trans (mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · exact integral_mono_measure hμ (Filter.Eventually.of_forall fun p => sq_nonneg _)
      (hX N).integrable_sq
  · exact (integral_mono_measure hμ (Filter.Eventually.of_forall fun p => sq_nonneg _)
      (hY N).integrable_sq).trans hN

/-! ### The drift term of the cutoff inequality -/

/-- The divergence-free transport of `J(u_N)` vanishes on `(0, t) × 𝕋²`:
`∫∫ B·∇u_N J'(u_N) = ∫∫ B·∇(J(u_N)) = 0`. -/
theorem integral_region_drift_cutoff_eq_zero {B : ℝ → Vec 2 → Vec 2} {u : ℝ → Vec 2 → ℝ}
    (hBslice : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      AEStronglyMeasurable (fun x => B s x) volume)
    {C : ℝ} (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖B t x‖ ≤ C)
    (hBp : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (B t)) (hdiv : IsDivFree B)
    {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) (N : ℕ)
    (hint : Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (B p.1 p.2) (spaceGrad (weakFourierModeProjection N u p.1) p.2) *
        deriv J (weakFourierModeProjection N u p.1 p.2)) (volume.restrict timeCube))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p in weakEnergyRegion t,
      Homogenization.vecDot (B p.1 p.2) (spaceGrad (weakFourierModeProjection N u p.1) p.2) *
        deriv J (weakFourierModeProjection N u p.1 p.2) = 0 := by
  rw [weakEnergy_region_integral_eq_interval hint ht]
  have hzero : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), ∫ x in unitCube,
      Homogenization.vecDot (B s x) (spaceGrad (weakFourierModeProjection N u s) x) *
        deriv J (weakFourierModeProjection N u s x) = 0 := by
    filter_upwards [hBslice, ae_restrict_mem measurableSet_Ioo] with s hbs hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hs
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC s hs' 0)
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (weakFourierModeProjection N u s) :=
      (realFourierModeAmbientExpansion_contDiff N _).of_le le_top
    have hJu : ContDiff ℝ (⊤ : ℕ∞) (fun y => J (weakFourierModeProjection N u s y)) :=
      hJ.comp hsm
    have hJp : IsZ2Periodic (fun y => J (weakFourierModeProjection N u s y)) := by
      intro k x
      change J (realFourierModeAmbientExpansion N _ (x + latticeShift k)) =
        J (realFourierModeAmbientExpansion N _ x)
      rw [realFourierModeAmbientExpansion_periodic N _ k x]
    have h := isDivFree_integral_periodic_smooth_test hbs ⟨C, hC0, hC s hs'⟩ (hBp s hs')
      (fun φ hφ hφc => hdiv s hs' φ hφ hφc) hJu hJp
    rw [Infra.Torus.integral_unitCell_eq_unitCube] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hg : spaceGrad (fun y => J (weakFourierModeProjection N u s y)) x =
        fun k => deriv J (weakFourierModeProjection N u s x) *
          spaceGrad (weakFourierModeProjection N u s) x k := by
      funext k
      exact spaceGrad_comp_of_differentiable (hsm.differentiable (by simp))
        (hJ.differentiable (by simp)) x k
    simp only [hg, Homogenization.vecDot, Fin.sum_univ_two]
    ring
  have hzero' := (ae_restrict_iff' measurableSet_Ioo).1 hzero
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 1 := by simp [ae_iff, measure_singleton]
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
  filter_upwards [hzero', hne] with s hs hs1 hsI
  rw [Set.uIoc_of_le ht.1] at hsI
  exact hs ⟨hsI.1, lt_of_le_of_ne (hsI.2.trans ht.2) hs1⟩

/-- **The drift term tends to zero.** -/
theorem tendsto_cutoff_drift_pairing_zero {B : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2} (hu : IsWeakSolutionGrad B κ f u D)
    (hBm : AEStronglyMeasurable (fun p : ℝ × Vec 2 => B p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hBb : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖B t x‖ ≤ C)
    (hBp : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (B t)) (hdiv : IsDivFree B)
    {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) {L : ℝ} (hL : ∀ r, |deriv (deriv J) r| ≤ L)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => ∫ s in (0 : ℝ)..t, ∫ x in unitCube,
      weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) s x *
        deriv J (weakFourierModeProjection N u s x)) atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC⟩ := hBb
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hsub : timeCube ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ := fun p hp =>
    ⟨⟨hp.1.1.le, hp.1.2.le⟩, Set.mem_univ _⟩
  have hBk : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => B p.1 p.2 k) ⊤ (volume.restrict timeCube) := by
    intro k
    refine MemLp.of_bound ((continuous_apply k).comp_aestronglyMeasurable (hBm.mono_set hsub)) C ?_
    filter_upwards [ae_restrict_mem WeakEnergyPassage.weakEnergy_timeCube_measurable] with p hp
    exact (norm_le_pi_norm (B p.1 p.2) k).trans (hC p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2)
  have hBslice : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      AEStronglyMeasurable (fun x => B s x) volume := by
    have hopen : AEStronglyMeasurable (fun p : ℝ × Vec 2 => B p.1 p.2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)))) :=
      hBm.mono_measure (Measure.restrict_mono (Set.prod_mono Set.Ioo_subset_Icc_self subset_rfl)
        le_rfl)
    rw [DivergenceFreeEnergy.divFree_openCylinder_measure] at hopen
    exact hopen.prodMk_left
  -- the drift path and its cutoffs
  have hGmem := weakEnergy_drift_memLp_two hu hBm ⟨C, hC⟩
  have hGs : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      MemL2On unitCube (fun x => Homogenization.vecDot (B s x) (D s x)) := by
    filter_upwards [hBslice, hu.2.2.2.2.1, ae_restrict_mem measurableSet_Ioo] with s hbs hH hs
    have hbk : ∀ k : Fin 2, MemLp (fun x => B s x k) ⊤ (volume.restrict unitCube) := fun k =>
      MemLp.of_bound ((continuous_apply k).comp_aestronglyMeasurable hbs).restrict C
        (Filter.Eventually.of_forall fun x =>
          (norm_le_pi_norm (B s x) k).trans (hC s ⟨hs.1.le, hs.2.le⟩ x))
    have h0 : MemLp (fun x => B s x 0 * D s x 0) 2 (volume.restrict unitCube) :=
      (hbk 0).mul (hH.2.2.2.1 0)
    have h1 : MemLp (fun x => B s x 1 * D s x 1) 2 (volume.restrict unitCube) :=
      (hbk 1).mul (hH.2.2.2.1 1)
    have h := h0.add h1
    convert h using 1
    funext x
    simp [Homogenization.vecDot, Fin.sum_univ_two]
  obtain ⟨hPmem, hPlim⟩ := tendsto_integral_sq_sub_cutoff_timeCube hGmem hGs
  -- the cutoffs of `u`, their gradients, and `J'(u_N)`
  have huN := weakEnergyProjection_memLp hu
  have hgN := weakEnergyGradient_memLp hu
  have hJd : Continuous (deriv J) := (differentiable_deriv_of_smooth hJ).continuous
  have hhN : ∀ N, MemLp (fun p : ℝ × Vec 2 => deriv J (weakFourierModeProjection N u p.1 p.2)) 2
      (volume.restrict timeCube) := by
    intro N
    refine MemLp.of_le ((memLp_const |deriv J 0|).add ((huN N).norm.const_mul L))
      (hJd.comp_aestronglyMeasurable (huN N).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |deriv J 0| + L * |weakFourierModeProjection N u p.1 p.2|)]
    exact abs_deriv_le_of_abs_deriv2_le hJ hL _
  -- `∫ J'(u_N)²` is eventually bounded
  have hu2 := hu.2.2.1.integrable_sq
  have hev : ∀ᶠ N in atTop, ∫ p in timeCube,
      (u p.1 p.2 - weakFourierModeProjection N u p.1 p.2) ^ 2 ≤ 1 :=
    (weakFourierProjection_scalar_spacetime_L2_tendsto hu).eventually (ge_mem_nhds one_pos)
  have hYb : ∀ᶠ N in atTop, ∫ p in timeCube,
      deriv J (weakFourierModeProjection N u p.1 p.2) ^ 2 ≤
        (∫ p in timeCube, (2 * |deriv J 0| ^ 2 + 4 * L ^ 2 * u p.1 p.2 ^ 2)) + 4 * L ^ 2 := by
    filter_upwards [hev] with N hN
    have hi1 : Integrable (fun p : ℝ × Vec 2 => 2 * |deriv J 0| ^ 2 + 4 * L ^ 2 * u p.1 p.2 ^ 2)
        (volume.restrict timeCube) := (integrable_const _).add (hu2.const_mul _)
    have hi2 : Integrable (fun p : ℝ × Vec 2 =>
        (u p.1 p.2 - weakFourierModeProjection N u p.1 p.2) ^ 2) (volume.restrict timeCube) :=
      (hu.2.2.1.sub (huN N)).integrable_sq
    have h := integral_mono (hhN N).integrable_sq (hi1.add (hi2.const_mul (4 * L ^ 2)))
      (fun p => by
        have hd := abs_deriv_le_of_abs_deriv2_le hJ hL (weakFourierModeProjection N u p.1 p.2)
        have hsq : deriv J (weakFourierModeProjection N u p.1 p.2) ^ 2 ≤
            (|deriv J 0| + L * |weakFourierModeProjection N u p.1 p.2|) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hd 2
        have h2 : (|deriv J 0| + L * |weakFourierModeProjection N u p.1 p.2|) ^ 2 ≤
            2 * |deriv J 0| ^ 2 + 2 * L ^ 2 * weakFourierModeProjection N u p.1 p.2 ^ 2 := by
          nlinarith [sq_nonneg (|deriv J 0| - L * |weakFourierModeProjection N u p.1 p.2|),
            sq_abs (weakFourierModeProjection N u p.1 p.2)]
        have h3 : weakFourierModeProjection N u p.1 p.2 ^ 2 ≤
            2 * u p.1 p.2 ^ 2 + 2 * (u p.1 p.2 - weakFourierModeProjection N u p.1 p.2) ^ 2 := by
          nlinarith [sq_nonneg (2 * u p.1 p.2 - weakFourierModeProjection N u p.1 p.2)]
        have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg L)
        simp only [Pi.add_apply]
        nlinarith [hsq, h2, h4])
    refine h.trans ?_
    simp only [Pi.add_apply]
    rw [integral_add hi1 (hi2.const_mul _), integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hN (sq_nonneg L)]
  -- the error pieces tend to zero
  have hX0 : Tendsto (fun N => ∫ p in timeCube,
      (weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) p.1 p.2 -
        Homogenization.vecDot (B p.1 p.2) (D p.1 p.2)) ^ 2) atTop (𝓝 0) := by
    refine hPlim.congr fun N => ?_
    congr 1
    funext p
    ring
  have hXk : ∀ k : Fin 2, Tendsto (fun N => ∫ p in timeCube, (B p.1 p.2 k *
      (D p.1 p.2 k - spaceGrad (weakFourierModeProjection N u p.1) p.2 k)) ^ 2) atTop (𝓝 0) := by
    intro k
    have hlim := weakFourierProjection_gradient_spacetime_L2_tendsto hu k
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩ 0)
    refine squeeze_zero (fun N => integral_nonneg fun p => sq_nonneg _) (fun N => ?_)
      (by simpa using hlim.const_mul (C ^ 2))
    have hint : Integrable (fun p : ℝ × Vec 2 =>
        (D p.1 p.2 k - spaceGrad (weakFourierModeProjection N u p.1) p.2 k) ^ 2)
        (volume.restrict timeCube) := ((hu.2.2.2.1 k).sub (hgN N k)).integrable_sq
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => sq_nonneg _)
      (hint.const_mul _) ?_
    filter_upwards [ae_restrict_mem WeakEnergyPassage.weakEnergy_timeCube_measurable] with p hp
    have hb : |B p.1 p.2 k| ≤ C := by
      simpa [Real.norm_eq_abs] using
        (norm_le_pi_norm (B p.1 p.2) k).trans (hC p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (B p.1 p.2 k), sq_abs (B p.1 p.2 k)])
      (sq_nonneg _)
  -- memberships of the pieces
  have hX0mem : ∀ N, MemLp (fun p : ℝ × Vec 2 =>
      weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) p.1 p.2 -
        Homogenization.vecDot (B p.1 p.2) (D p.1 p.2)) 2 (volume.restrict timeCube) :=
    fun N => (hPmem N).sub hGmem
  have hXkmem : ∀ (k : Fin 2) N, MemLp (fun p : ℝ × Vec 2 => B p.1 p.2 k *
      (D p.1 p.2 k - spaceGrad (weakFourierModeProjection N u p.1) p.2 k)) 2
      (volume.restrict timeCube) := fun k N => (hBk k).mul ((hu.2.2.2.1 k).sub (hgN N k))
  have hV : ∀ N, MemLp (fun p : ℝ × Vec 2 => Homogenization.vecDot (B p.1 p.2)
      (spaceGrad (weakFourierModeProjection N u p.1) p.2)) 2 (volume.restrict timeCube) := by
    intro N
    have h0 : MemLp (fun p : ℝ × Vec 2 =>
        B p.1 p.2 0 * spaceGrad (weakFourierModeProjection N u p.1) p.2 0) 2
        (volume.restrict timeCube) := (hBk 0).mul (hgN N 0)
    have h1 : MemLp (fun p : ℝ × Vec 2 =>
        B p.1 p.2 1 * spaceGrad (weakFourierModeProjection N u p.1) p.2 1) 2
        (volume.restrict timeCube) := (hBk 1).mul (hgN N 1)
    convert h0.add h1 using 1
    funext p
    simp [Homogenization.vecDot, Fin.sum_univ_two]
  -- decomposition of the drift term
  have hR : volume.restrict (weakEnergyRegion t) ≤ volume.restrict timeCube :=
    Measure.restrict_mono (weakEnergy_region_subset_timeCube ht) le_rfl
  have hdecomp : ∀ N, (∫ s in (0 : ℝ)..t, ∫ x in unitCube,
      weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) s x *
        deriv J (weakFourierModeProjection N u s x)) =
      (∫ p in weakEnergyRegion t,
        (weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) p.1 p.2 -
          Homogenization.vecDot (B p.1 p.2) (D p.1 p.2)) *
          deriv J (weakFourierModeProjection N u p.1 p.2)) +
      ((∫ p in weakEnergyRegion t, B p.1 p.2 0 *
          (D p.1 p.2 0 - spaceGrad (weakFourierModeProjection N u p.1) p.2 0) *
          deriv J (weakFourierModeProjection N u p.1 p.2)) +
        ∫ p in weakEnergyRegion t, B p.1 p.2 1 *
          (D p.1 p.2 1 - spaceGrad (weakFourierModeProjection N u p.1) p.2 1) *
          deriv J (weakFourierModeProjection N u p.1 p.2)) := by
    intro N
    have iP := weak_product_integrable_timeCube (hPmem N) (hhN N)
    have i0 := (weak_product_integrable_timeCube (hX0mem N) (hhN N)).mono_measure hR
    have i1 := (weak_product_integrable_timeCube (hXkmem 0 N) (hhN N)).mono_measure hR
    have i2 := (weak_product_integrable_timeCube (hXkmem 1 N) (hhN N)).mono_measure hR
    have iV := weak_product_integrable_timeCube (hV N) (hhN N)
    have hzero := integral_region_drift_cutoff_eq_zero hBslice hC hBp hdiv hJ N iV ht
    rw [show (∫ s in (0 : ℝ)..t, ∫ x in unitCube,
        weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) s x *
          deriv J (weakFourierModeProjection N u s x)) =
        ∫ p in weakEnergyRegion t,
          weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) p.1 p.2 *
            deriv J (weakFourierModeProjection N u p.1 p.2) from
        (weakEnergy_region_integral_eq_interval iP ht).symm]
    have e : (fun p : ℝ × Vec 2 =>
        weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x)) p.1 p.2 *
          deriv J (weakFourierModeProjection N u p.1 p.2)) =
        fun p => ((weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x))
            p.1 p.2 - Homogenization.vecDot (B p.1 p.2) (D p.1 p.2)) *
            deriv J (weakFourierModeProjection N u p.1 p.2) +
          (B p.1 p.2 0 * (D p.1 p.2 0 - spaceGrad (weakFourierModeProjection N u p.1) p.2 0) *
              deriv J (weakFourierModeProjection N u p.1 p.2) +
            B p.1 p.2 1 * (D p.1 p.2 1 - spaceGrad (weakFourierModeProjection N u p.1) p.2 1) *
              deriv J (weakFourierModeProjection N u p.1 p.2))) +
          Homogenization.vecDot (B p.1 p.2) (spaceGrad (weakFourierModeProjection N u p.1) p.2) *
            deriv J (weakFourierModeProjection N u p.1 p.2) := by
      funext p
      simp only [Homogenization.vecDot, Fin.sum_univ_two]
      ring
    have i12 : Integrable (fun p : ℝ × Vec 2 =>
        B p.1 p.2 0 * (D p.1 p.2 0 - spaceGrad (weakFourierModeProjection N u p.1) p.2 0) *
            deriv J (weakFourierModeProjection N u p.1 p.2) +
          B p.1 p.2 1 * (D p.1 p.2 1 - spaceGrad (weakFourierModeProjection N u p.1) p.2 1) *
            deriv J (weakFourierModeProjection N u p.1 p.2))
        (volume.restrict (weakEnergyRegion t)) := i1.add i2
    have i012 : Integrable (fun p : ℝ × Vec 2 =>
        (weakFourierModeProjection N (fun s x => Homogenization.vecDot (B s x) (D s x))
            p.1 p.2 - Homogenization.vecDot (B p.1 p.2) (D p.1 p.2)) *
            deriv J (weakFourierModeProjection N u p.1 p.2) +
          (B p.1 p.2 0 * (D p.1 p.2 0 - spaceGrad (weakFourierModeProjection N u p.1) p.2 0) *
              deriv J (weakFourierModeProjection N u p.1 p.2) +
            B p.1 p.2 1 * (D p.1 p.2 1 - spaceGrad (weakFourierModeProjection N u p.1) p.2 1) *
              deriv J (weakFourierModeProjection N u p.1 p.2)))
        (volume.restrict (weakEnergyRegion t)) := i0.add i12
    rw [e, integral_add i012 (iV.mono_measure hR), hzero, add_zero, integral_add i0 i12,
      integral_add i1 i2]
  simp only [hdecomp]
  have t0 := tendsto_region_pairing_zero ht hX0mem hhN hX0 hYb
  have t1 := tendsto_region_pairing_zero ht (hXkmem 0) hhN (hXk 0) hYb
  have t2 := tendsto_region_pairing_zero ht (hXkmem 1) hhN (hXk 1) hYb
  simpa using t0.add (t1.add t2)

/-! ### The convex entropy inequality on the unit window -/

/-- **Convex entropy inequality** (unit window, upstream form). For a bounded measurable
periodic divergence-free drift, `κ ≥ 0` and a smooth `J` with `0 ≤ J'' ≤ L`:
`∫ J(u(t)) ≤ ∫ J(f)` for every `t ∈ [0, 1]`. -/
theorem integral_convex_le_of_isWeakSolutionGrad {B : ℝ → Vec 2 → Vec 2} {κ : ℝ} (hκ : 0 ≤ κ)
    {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : IsWeakSolutionGrad B κ f u D) (hf : MemL2On unitCube f)
    (hBm : AEStronglyMeasurable (fun p : ℝ × Vec 2 => B p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hBb : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖B t x‖ ≤ C)
    (hBp : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (B t)) (hdiv : IsDivFree B)
    {J : ℝ → ℝ} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) (hJ2 : ∀ r, 0 ≤ deriv (deriv J) r)
    (hJL : ∃ L : ℝ, ∀ r, deriv (deriv J) r ≤ L) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∫ x in unitCube, J (u t x) ≤ ∫ x in unitCube, J (f x) := by
  intro t ht
  obtain ⟨L, hJL⟩ := hJL
  have hL : ∀ r, |deriv (deriv J) r| ≤ L := fun r => by rw [abs_of_nonneg (hJ2 r)]; exact hJL r
  have hcont : ∀ N s, Continuous (weakFourierModeProjection N u s) := fun N s =>
    (realFourierModeAmbientExpansion_contDiff N _).continuous
  -- the three limits
  have hlimT : Tendsto (fun N => ∫ x in unitCube, J (weakFourierModeProjection N u t x)) atTop
      (𝓝 (∫ x in unitCube, J (u t x))) :=
    tendsto_integral_comp_of_tendsto_l2NormSq hJ hL (hu.1 t ht).2
      (fun N => weak_continuous_memL2On (hcont N t)) (tendsto_l2NormSq_sub_cutoff (hu.1 t ht).2)
  have h0eq : ∀ N, weakFourierModeProjection N u 0 =
      weakFourierModeProjection N (fun _ x => f x) 0 := by
    intro N
    have hc : weakFourierCoefficientPath N u 0 = weakFourierCoefficientPath N (fun _ x => f x) 0 := by
      ext j
      have h0 := weak_solution_mode_integral_path hu hf (cutMode_contDiff N j)
        (realFourierModeAmbient_periodic N _) 0 ⟨le_rfl, zero_le_one⟩
      rw [intervalIntegral.integral_same, sub_zero] at h0
      simpa [weakFourierCoefficientPath] using h0
    simp only [weakFourierModeProjection, hc]
  have hlim0 : Tendsto (fun N => ∫ x in unitCube, J (weakFourierModeProjection N u 0 x)) atTop
      (𝓝 (∫ x in unitCube, J (f x))) := by
    simp only [h0eq]
    exact tendsto_integral_comp_of_tendsto_l2NormSq hJ hL hf
      (fun N => weak_continuous_memL2On (realFourierModeAmbientExpansion_contDiff N _).continuous)
      (tendsto_l2NormSq_sub_cutoff (U := fun _ x => f x) (s := 0) hf)
  have hlimD := tendsto_cutoff_drift_pairing_zero hu hBm hBb hBp hdiv hJ hL ht
  have hcut := fun N => integral_comp_cutoff_le hκ hu hf hJ hJ2 N ht
  have h := le_of_tendsto_of_tendsto' hlimT (hlim0.sub hlimD) hcut
  simpa using h

end AVRegularity.Applications.Dissipation

end
