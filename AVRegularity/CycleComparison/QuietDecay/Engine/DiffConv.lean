-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Analysis.Convolution.Kernel.Commutation.TorusBridge
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Analysis.Convolution.Kernel.Spatial
public import AVRegularity.CycleComparison.Residual.TimeIntegration
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public noncomputable section

section
open MeasureTheory Homogenization
open AVenhance.Infra.Torus
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Cell integrals of periodic functions are invariant under translations: the periodic function
factors through the torus, where translations preserve the Haar measure. -/

theorem periodic_eq_rep {β : Type*} {g : Vec 2 → β} (hp : AVenhance.IsZ2Periodic g) (y : Vec 2) :
    g (unitTorusRepresentative 2 (torusQuotient y)) = g y := by
  obtain ⟨k, hk⟩ := Basic.representative_int_translate (d := 2) y
  change g (unitTorusRepresentative 2 (toUnitTorus 2 y)) = g y
  rw [hk]
  exact hp k y

theorem measurable_unitTorusRepresentative : Measurable (unitTorusRepresentative 2) :=
  measurePreserving_unitTorusRepresentative_cell.measurable

/-- Translation invariance of the cell integral of a periodic function. -/
theorem lintegral_cube_add_of_periodic {g : Vec 2 → ℝ≥0∞} (hg : Measurable g)
    (hp : AVenhance.IsZ2Periodic g) (w : Vec 2) :
    ∫⁻ z in AVenhance.unitCube, g (z + w) = ∫⁻ z in AVenhance.unitCube, g z := by
  set g' : UnitAddTorus (Fin 2) → ℝ≥0∞ := g ∘ unitTorusRepresentative 2 with hg'
  have hg'm : Measurable g' := hg.comp measurable_unitTorusRepresentative
  have hkey : ∀ y, g y = g' (torusQuotient y) := fun y => (periodic_eq_rep hp y).symm
  have hmp := measurePreserving_torusQuotient_cell
  calc ∫⁻ z in AVenhance.unitCube, g (z + w)
      = ∫⁻ z in AVenhance.unitCube, (fun q => g' (q + torusQuotient w)) (torusQuotient z) := by
        refine lintegral_congr fun z => ?_
        simp only [hkey (z + w), map_add]
    _ = ∫⁻ q, g' (q + torusQuotient w) ∂torusMeasure :=
        hmp.lintegral_comp (hg'm.comp (measurable_add_const _))
    _ = ∫⁻ q, g' q ∂torusMeasure := lintegral_add_right_eq_self g' (torusQuotient w)
    _ = ∫⁻ z in AVenhance.unitCube, g' (torusQuotient z) := (hmp.lintegral_comp hg'm).symm
    _ = ∫⁻ z in AVenhance.unitCube, g z := lintegral_congr fun z => (hkey z).symm

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Difference quotients: the one-step quotient is the average of the directional derivative
along the step, hence its cell `L²` norm is at most the supremum of the cell `L²` norms of the
derivative (slow steps), or at most the cell `L²` norm of the derivative (fast steps of periodic
fields). -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The difference quotient in the direction `i` with step `h`. -/
def sdiff (i : Fin 2) (h : ℝ) (φ : Vec 2 → E) : Vec 2 → E :=
  fun X => h⁻¹ • (φ (X + h • basisVec i) - φ X)

/-- The difference quotient is the average of the directional derivative along the step. -/
theorem sdiff_eq_integral [CompleteSpace E] (i : Fin 2) {h : ℝ} (hh : h ≠ 0) {φ : Vec 2 → E}
    (hφ : Differentiable ℝ φ) (hc : Continuous fun X => fderiv ℝ φ X (basisVec i)) (X : Vec 2) :
    sdiff i h φ X = ∫ θ in (0 : ℝ)..1, fderiv ℝ φ (X + (θ * h) • basisVec i) (basisVec i) := by
  have hγ : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => φ (X + (θ * h) • basisVec i))
      (h • fderiv ℝ φ (X + (θ * h) • basisVec i) (basisVec i)) θ := by
    intro θ
    have hl : HasDerivAt (fun θ : ℝ => X + (θ * h) • basisVec i) (h • basisVec i) θ := by
      have := ((hasDerivAt_id θ).mul_const h).smul_const (basisVec i)
      simpa using this.const_add X
    have := (hφ _).hasFDerivAt.comp_hasDerivAt θ hl
    simpa [map_smul, Function.comp_def] using this
  have hint : IntervalIntegrable (fun θ : ℝ => h • fderiv ℝ φ (X + (θ * h) • basisVec i)
      (basisVec i)) volume 0 1 := by
    refine (Continuous.intervalIntegrable ?_ _ _)
    exact (hc.comp (continuous_const.add
      ((continuous_id.mul continuous_const).smul continuous_const))).const_smul h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hγ θ) hint
  rw [intervalIntegral.integral_smul] at hftc
  simp only [zero_mul, zero_smul, add_zero, one_mul] at hftc
  unfold sdiff
  rw [← hftc, smul_smul, inv_mul_cancel₀ hh, one_smul]

/-- Jensen on the unit interval: the square of an average is at most the average of squares. -/
theorem enorm_intervalIntegral_sq_le [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) :
    ‖∫ θ in (0 : ℝ)..1, f θ‖ₑ ^ 2 ≤ ∫⁻ θ in Ioc (0 : ℝ) 1, ‖f θ‖ₑ ^ 2 := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have h1 : ‖∫ θ in Ioc (0 : ℝ) 1, f θ‖ₑ ≤ ∫⁻ θ in Ioc (0 : ℝ) 1, ‖f θ‖ₑ :=
    enorm_integral_le_lintegral_enorm _
  have hcs : ∫⁻ θ in Ioc (0 : ℝ) 1, ‖f θ‖ₑ * 1 ≤
      (∫⁻ θ in Ioc (0 : ℝ) 1, ‖f θ‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ _θ in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two
      hf.enorm.aemeasurable aemeasurable_const
  simp only [mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_one] at hcs
  have h2 : ‖∫ θ in Ioc (0 : ℝ) 1, f θ‖ₑ ≤
      (∫⁻ θ in Ioc (0 : ℝ) 1, ‖f θ‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := h1.trans hcs
  calc ‖∫ θ in Ioc (0 : ℝ) 1, f θ‖ₑ ^ 2
      ≤ ((∫⁻ θ in Ioc (0 : ℝ) 1, ‖f θ‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ∫⁻ θ in Ioc (0 : ℝ) 1, ‖f θ‖ₑ ^ 2 := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

/-- Slow difference quotients: the cell `L²` norm is at most the supremum over slow points of the
cell `L²` norm of the directional derivative. -/
theorem lintegral_slow_sdiff_le [CompleteSpace E] (i : Fin 2) {h : ℝ} (hh : h ≠ 0)
    (φ : Vec 2 → Vec 2 → E) (hd : ∀ z, Differentiable ℝ fun X => φ X z)
    (hc : Continuous fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => φ X p.2) p.1 (basisVec i))
    (X : Vec 2) :
    ∫⁻ z in AVenhance.unitCube, ‖sdiff i h (fun X' => φ X' z) X‖ₑ ^ 2 ≤
      ⨆ X' : Vec 2, ∫⁻ z in AVenhance.unitCube,
        ‖fderiv ℝ (fun X'' => φ X'' z) X' (basisVec i)‖ₑ ^ 2 := by
  set g : Vec 2 → Vec 2 → E := fun X' z => fderiv ℝ (fun X'' => φ X'' z) X' (basisVec i)
  have hpt : ∀ z, ‖sdiff i h (fun X' => φ X' z) X‖ₑ ^ 2 ≤
      ∫⁻ θ in Ioc (0 : ℝ) 1, ‖g (X + (θ * h) • basisVec i) z‖ₑ ^ 2 := by
    intro z
    have hcz : Continuous fun X' => g X' z := hc.comp (continuous_id.prodMk continuous_const)
    rw [sdiff_eq_integral i hh (hd z) hcz X]
    exact enorm_intervalIntegral_sq_le (hcz.comp (continuous_const.add
      ((continuous_id.mul continuous_const).smul continuous_const)))
  have hmeas : Measurable fun q : Vec 2 × ℝ => ‖g (X + (q.2 * h) • basisVec i) q.1‖ₑ ^ 2 := by
    exact ((hc.comp ((continuous_const.add ((continuous_snd.mul continuous_const).smul
      continuous_const)).prodMk continuous_fst)).enorm.measurable).pow_const 2
  calc ∫⁻ z in AVenhance.unitCube, ‖sdiff i h (fun X' => φ X' z) X‖ₑ ^ 2
      ≤ ∫⁻ z in AVenhance.unitCube, ∫⁻ θ in Ioc (0 : ℝ) 1,
          ‖g (X + (θ * h) • basisVec i) z‖ₑ ^ 2 := lintegral_mono hpt
    _ = ∫⁻ θ in Ioc (0 : ℝ) 1, ∫⁻ z in AVenhance.unitCube,
          ‖g (X + (θ * h) • basisVec i) z‖ₑ ^ 2 :=
        lintegral_lintegral_swap (hmeas.aemeasurable)
    _ ≤ ∫⁻ _θ in Ioc (0 : ℝ) 1, ⨆ X' : Vec 2, ∫⁻ z in AVenhance.unitCube, ‖g X' z‖ₑ ^ 2 :=
        lintegral_mono fun θ => le_iSup (fun X' => ∫⁻ z in AVenhance.unitCube, ‖g X' z‖ₑ ^ 2) _
    _ = ⨆ X' : Vec 2, ∫⁻ z in AVenhance.unitCube, ‖g X' z‖ₑ ^ 2 := by
        simp [Real.volume_Ioc]

/-- Fast difference quotients of periodic fields: the cell `L²` norm is at most the cell `L²`
norm of the directional derivative. -/
theorem lintegral_fast_sdiff_le [CompleteSpace E] (i : Fin 2) {h : ℝ} (hh : h ≠ 0)
    {g : Vec 2 → E} (hd : Differentiable ℝ g) (hc : Continuous fun z => fderiv ℝ g z (basisVec i))
    (hp : AVenhance.IsZ2Periodic g) :
    ∫⁻ z in AVenhance.unitCube, ‖sdiff i h g z‖ₑ ^ 2 ≤
      ∫⁻ z in AVenhance.unitCube, ‖fderiv ℝ g z (basisVec i)‖ₑ ^ 2 := by
  set dg : Vec 2 → E := fun z => fderiv ℝ g z (basisVec i)
  have hdp : AVenhance.IsZ2Periodic dg := by
    intro n z
    have : g = fun y => g (y + AVenhance.latticeShift n) := funext fun y => (hp n y).symm
    simp only [dg]
    conv_rhs => rw [this]
    rw [fderiv_comp_add_right]
  have hpt : ∀ z, ‖sdiff i h g z‖ₑ ^ 2 ≤
      ∫⁻ θ in Ioc (0 : ℝ) 1, ‖dg (z + (θ * h) • basisVec i)‖ₑ ^ 2 := by
    intro z
    rw [sdiff_eq_integral i hh hd hc z]
    exact enorm_intervalIntegral_sq_le (hc.comp (continuous_const.add
      ((continuous_id.mul continuous_const).smul continuous_const)))
  have hmeas : Measurable fun q : Vec 2 × ℝ => ‖dg (q.1 + (q.2 * h) • basisVec i)‖ₑ ^ 2 :=
    ((hc.comp (continuous_fst.add ((continuous_snd.mul continuous_const).smul
      continuous_const))).enorm.measurable).pow_const 2
  calc ∫⁻ z in AVenhance.unitCube, ‖sdiff i h g z‖ₑ ^ 2
      ≤ ∫⁻ z in AVenhance.unitCube, ∫⁻ θ in Ioc (0 : ℝ) 1,
          ‖dg (z + (θ * h) • basisVec i)‖ₑ ^ 2 := lintegral_mono hpt
    _ = ∫⁻ θ in Ioc (0 : ℝ) 1, ∫⁻ z in AVenhance.unitCube,
          ‖dg (z + (θ * h) • basisVec i)‖ₑ ^ 2 :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ _θ in Ioc (0 : ℝ) 1, ∫⁻ z in AVenhance.unitCube, ‖dg z‖ₑ ^ 2 := by
        refine lintegral_congr fun θ => ?_
        exact lintegral_cube_add_of_periodic (hc.enorm.measurable.pow_const 2)
          (fun n y => by simp only [hdp n y]) _
    _ = ∫⁻ z in AVenhance.unitCube, ‖dg z‖ₑ ^ 2 := by simp [Real.volume_Ioc]
end

/-! Iterated slow difference quotients of slow-smooth fields: they stay slow smooth, commute with
slow derivatives, and their cell `L²` norms are bounded by the suprema of the cell `L²` norms of the
corresponding slow derivatives (letters in reversed order). -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterated slow difference quotients along the list `l` (first letter first). -/
def slowDiffs (l : List (Fin 2)) (h : ℝ) (φ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  l.foldl (fun g i => fun X z => sdiff i h (fun X' => g X' z) X) φ

/-- Iterated slow derivatives along the list `l` (first letter first). -/
def slowDerivs (l : List (Fin 2)) (φ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  l.foldl (fun g i => AVRegularity.slowPartial i g) φ

theorem slowDiffs_append (l : List (Fin 2)) (i : Fin 2) (h : ℝ) (φ : Vec 2 → Vec 2 → E) :
    slowDiffs (l ++ [i]) h φ = fun X z => sdiff i h (fun X' => slowDiffs l h φ X' z) X := by
  simp [slowDiffs, List.foldl_append]

theorem slowDerivs_cons (l : List (Fin 2)) (i : Fin 2) (φ : Vec 2 → Vec 2 → E) :
    slowDerivs (i :: l) φ = slowDerivs l (AVRegularity.slowPartial i φ) := rfl

theorem isSlowSmooth_shift {m : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsSlowSmooth m f) (c : Vec 2) :
    IsSlowSmooth m (fun X z => f (X + c) z) := by
  refine ⟨fun y => (hf.1 y).comp (contDiff_id.add contDiff_const), fun a ha => ?_⟩
  have e : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ a (fun X => f (X + c) p.2) p.1) =
      fun p => iteratedFDeriv ℝ a (fun X => f X p.2) (p.1 + c) := by
    funext p
    exact iteratedFDeriv_comp_add_right (f := fun X => f X p.2) a c p.1
  rw [e]
  exact (hf.2 a ha).comp ((continuous_fst.add continuous_const).prodMk continuous_snd)

theorem isSlowSmooth_sdiff {m : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsSlowSmooth m f) (i : Fin 2)
    (h : ℝ) : IsSlowSmooth m (fun X z => sdiff i h (fun X' => f X' z) X) := by
  unfold AVRegularity.QuietDecay.sdiff
  exact ((isSlowSmooth_shift hf (h • basisVec i)).sub hf).const_smul h⁻¹

theorem isSlowSmooth_slowDiffs {m : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsSlowSmooth m f)
    (l : List (Fin 2)) (h : ℝ) : IsSlowSmooth m (slowDiffs l h f) := by
  induction l using List.reverseRecOn with
  | nil => exact hf
  | append_singleton l i ih =>
      rw [slowDiffs_append]
      exact isSlowSmooth_sdiff ih i h

/-- A slow partial of a one-step slow difference quotient is the difference quotient of the
slow partial. -/
theorem slowPartial_sdiff {f : Vec 2 → Vec 2 → E} (hf : ∀ z, Differentiable ℝ fun X => f X z)
    (i j : Fin 2) (h : ℝ) :
    AVRegularity.slowPartial j (fun X z => sdiff i h (fun X' => f X' z) X) =
      fun X z => sdiff i h (fun X' => AVRegularity.slowPartial j f X' z) X := by
  funext X z
  have hadd : HasFDerivAt (fun X' : Vec 2 => X' + h • basisVec i)
      (ContinuousLinearMap.id ℝ (Vec 2)) X := (hasFDerivAt_id X).add_const _
  have hd1 : HasFDerivAt (fun X' => f (X' + h • basisVec i) z)
      (fderiv ℝ (fun X' => f X' z) (X + h • basisVec i)) X := by
    have := HasFDerivAt.comp X ((hf z) (X + h • basisVec i)).hasFDerivAt hadd
    simpa [Function.comp_def] using this
  have hd2 : HasFDerivAt (fun X' => f X' z) (fderiv ℝ (fun X' => f X' z) X) X :=
    ((hf z) X).hasFDerivAt
  have hd : HasFDerivAt (fun X' => h⁻¹ • (f (X' + h • basisVec i) z - f X' z))
      (h⁻¹ • (fderiv ℝ (fun X' => f X' z) (X + h • basisVec i) -
        fderiv ℝ (fun X' => f X' z) X)) X := (hd1.sub hd2).const_smul h⁻¹
  change fderiv ℝ (fun X' => h⁻¹ • (f (X' + h • basisVec i) z - f X' z)) X (basisVec j) = _
  rw [hd.fderiv]
  rfl

theorem slowPartial_slowDiffs {m : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsSlowSmooth (m + 1) f)
    (l : List (Fin 2)) (h : ℝ) (j : Fin 2) :
    AVRegularity.slowPartial j (slowDiffs l h f) =
      slowDiffs l h (AVRegularity.slowPartial j f) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l i ih =>
      rw [slowDiffs_append, slowDiffs_append, slowPartial_sdiff, ih]
      intro z
      exact ((isSlowSmooth_slowDiffs hf l h).1 z).differentiable (by simp)

/-- The iterated slow difference quotient is bounded in cell `L²` by the suprema of the slow
derivatives in reversed letter order. -/
theorem lintegral_slowDiffs_le [CompleteSpace E] {h : ℝ} (hh : h ≠ 0) :
    ∀ (l : List (Fin 2)) (f : Vec 2 → Vec 2 → E), IsSlowSmooth (l.length + 1) f → ∀ X : Vec 2,
      ∫⁻ z in AVenhance.unitCube, ‖slowDiffs l h f X z‖ₑ ^ 2 ≤
        ⨆ X' : Vec 2, ∫⁻ z in AVenhance.unitCube, ‖slowDerivs l.reverse f X' z‖ₑ ^ 2 := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
      intro f _ X
      exact le_iSup (fun X' => ∫⁻ z in AVenhance.unitCube, ‖slowDerivs [] f X' z‖ₑ ^ 2) X
  | append_singleton l i ih =>
      intro f hf X
      have hlen : (l ++ [i]).length + 1 = (l.length + 1) + 1 := by simp
      rw [hlen] at hf
      have hd := isSlowSmooth_slowDiffs hf l h
      rw [slowDiffs_append]
      refine (lintegral_slow_sdiff_le i hh (slowDiffs l h f)
        (fun z => (hd.1 z).differentiable (by simp)) ?_ X).trans ?_
      · have := (hd.slowPartial i).continuous_orderedDerivative (j := 0) (by omega) (fun k => k.elim0)
        simpa [orderedDerivative, AVRegularity.slowPartial] using this
      · refine iSup_le fun X' => ?_
        have e : (fun z => fderiv ℝ (fun X'' => slowDiffs l h f X'' z) X' (basisVec i)) =
            fun z => slowDiffs l h (AVRegularity.slowPartial i f) X' z := by
          funext z
          have := congrFun (congrFun (slowPartial_slowDiffs hf l h i) X') z
          simpa [AVRegularity.slowPartial] using this
        rw [show (∫⁻ z in AVenhance.unitCube,
            ‖fderiv ℝ (fun X'' => slowDiffs l h f X'' z) X' (basisVec i)‖ₑ ^ 2) =
            ∫⁻ z in AVenhance.unitCube, ‖slowDiffs l h (AVRegularity.slowPartial i f) X' z‖ₑ ^ 2 from
          lintegral_congr fun z => by rw [congrFun e z]]
        refine (le_iSup (fun X' => ∫⁻ z in AVenhance.unitCube,
          ‖slowDiffs l h (AVRegularity.slowPartial i f) X' z‖ₑ ^ 2) X').trans ?_
        refine (iSup_le fun X'' => (ih (AVRegularity.slowPartial i f) (hf.slowPartial i) X'')).trans ?_
        simp [List.reverse_append, slowDerivs_cons]
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Filter Topology Homogenization
namespace AVRegularity.QuietDecay

/-! Iterated slow difference quotients of slow-smooth fields converge, locally uniformly in the
slow point, to the slow derivatives in reversed letter order. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem slowDerivs_append (l : List (Fin 2)) (i : Fin 2) (f : Vec 2 → Vec 2 → E) :
    slowDerivs (l ++ [i]).reverse f = slowDerivs l.reverse (AVRegularity.slowPartial i f) := by
  simp [slowDerivs_cons]

/-- Locally uniform convergence of iterated slow difference quotients. -/
theorem slowDiffs_locUnif :
    ∀ (l : List (Fin 2)) (f : Vec 2 → Vec 2 → E), IsSlowSmooth (l.length + 1) f →
      ∀ (z X : Vec 2) (ε : ℝ), 0 < ε → ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ Y : Vec 2,
        dist Y X < δ → ‖slowDiffs l h f Y z - slowDerivs l.reverse f X z‖ < ε := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
      intro f hf z X ε hε
      have hc : ContinuousAt (fun Y => f Y z) X := ((hf.1 z).continuous).continuousAt
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hc ε hε
      refine ⟨δ, hδ, fun h _ _ Y hY => ?_⟩
      simpa [slowDiffs, slowDerivs, dist_eq_norm] using hball hY
  | append_singleton l i ih =>
      intro f hf z X ε hε
      have hlen : (l ++ [i]).length + 1 = (l.length + 1) + 1 := by simp
      rw [hlen] at hf
      have hg : IsSlowSmooth (l.length + 1) (AVRegularity.slowPartial i f) := hf.slowPartial i
      obtain ⟨δ₀, hδ₀, hδ₀b⟩ := ih (AVRegularity.slowPartial i f) hg z X (ε / 2) (by linarith)
      refine ⟨δ₀ / 2, by linarith, fun h hh hhδ Y hY => ?_⟩
      have hd := isSlowSmooth_slowDiffs hf l h
      have hdiff : Differentiable ℝ fun X' => slowDiffs l h f X' z :=
        (hd.1 z).differentiable (by simp)
      have hcont : Continuous fun X' => fderiv ℝ (fun X'' => slowDiffs l h f X'' z) X' (basisVec i) := by
        have := (hd.slowPartial i).continuous_orderedDerivative (j := 0) (by omega)
          (fun k => k.elim0)
        have h2 := this.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : Vec 2 => z))
        simpa [orderedDerivative, AVRegularity.slowPartial, Function.comp_def] using h2
      have hrep := sdiff_eq_integral i hh hdiff hcont Y
      have hcomm : ∀ Y', fderiv ℝ (fun X'' => slowDiffs l h f X'' z) Y' (basisVec i) =
          slowDiffs l h (AVRegularity.slowPartial i f) Y' z := fun Y' => by
        have := congrFun (congrFun (slowPartial_slowDiffs hf l h i) Y') z
        simpa [AVRegularity.slowPartial] using this
      set c := slowDerivs l.reverse (AVRegularity.slowPartial i f) X z
      have hpt : ∀ θ ∈ Set.uIcc (0 : ℝ) 1,
          ‖slowDiffs l h (AVRegularity.slowPartial i f) (Y + (θ * h) • basisVec i) z - c‖ ≤
            ε / 2 := by
        intro θ hθ
        rw [Set.uIcc_of_le zero_le_one] at hθ
        refine (hδ₀b h hh (by linarith) _ ?_).le
        have hn : ‖(θ * h) • basisVec i‖ ≤ |h| := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ.1]
          have hb : ‖(basisVec i : Vec 2)‖ ≤ 1 := by
            rw [pi_norm_le_iff_of_nonneg zero_le_one]
            intro k
            by_cases hk : k = i <;> simp [basisVec, hk]
          calc θ * |h| * ‖(basisVec i : Vec 2)‖ ≤ 1 * |h| * 1 := by
                gcongr
                · exact hθ.2
            _ = |h| := by ring
        calc dist (Y + (θ * h) • basisVec i) X ≤ dist Y X + ‖(θ * h) • basisVec i‖ := by
              rw [dist_eq_norm, dist_eq_norm]
              calc ‖Y + (θ * h) • basisVec i - X‖ = ‖(Y - X) + (θ * h) • basisVec i‖ := by
                    congr 1; abel
                _ ≤ ‖Y - X‖ + ‖(θ * h) • basisVec i‖ := norm_add_le _ _
          _ < δ₀ / 2 + δ₀ / 2 := by linarith
          _ = δ₀ := by ring
      rw [slowDiffs_append, slowDerivs_append]
      change ‖sdiff i h (fun X' => slowDiffs l h f X' z) Y - c‖ < ε
      rw [hrep]
      simp_rw [hcomm]
      have hint : IntervalIntegrable (fun θ : ℝ =>
          slowDiffs l h (AVRegularity.slowPartial i f) (Y + (θ * h) • basisVec i) z) volume 0 1 := by
        refine Continuous.intervalIntegrable ?_ _ _
        have := ((isSlowSmooth_slowDiffs hg l h).1 z).continuous
        exact this.comp (continuous_const.add ((continuous_id.mul continuous_const).smul
          continuous_const))
      have hc1 : (∫ θ in (0 : ℝ)..1, c) = c := by simp
      calc ‖(∫ θ in (0 : ℝ)..1, slowDiffs l h (AVRegularity.slowPartial i f)
              (Y + (θ * h) • basisVec i) z) - c‖
          = ‖∫ θ in (0 : ℝ)..1, (slowDiffs l h (AVRegularity.slowPartial i f)
              (Y + (θ * h) • basisVec i) z - c)‖ := by
            rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hc1]
        _ ≤ (ε / 2) * |(1 : ℝ) - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ =>
              hpt θ (Set.uIoc_subset_uIcc hθ)
        _ < ε := by norm_num; linarith

/-- Pointwise convergence of iterated slow difference quotients. -/
theorem slowDiffs_tendsto (l : List (Fin 2)) (f : Vec 2 → Vec 2 → E)
    (hf : IsSlowSmooth (l.length + 1) f) (X z : Vec 2) :
    Tendsto (fun h => slowDiffs l h f X z) (𝓝[≠] 0) (𝓝 (slowDerivs l.reverse f X z)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := slowDiffs_locUnif l f hf z X ε hε
  have h1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 := self_mem_nhdsWithin
  have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ := by
    refine nhdsWithin_le_nhds ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    simpa [Real.dist_eq] using hh
  filter_upwards [h1, h2] with h hh0 hhδ
  rw [dist_eq_norm]
  exact hb h hh0 hhδ X (by simpa using hδ)

end AVRegularity.QuietDecay
end
