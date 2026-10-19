-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexCell.Mode
public import AVRegularity.Proofs.ComplexContext.Leaf
import AVRegularity.Proofs.ComplexChain.Vel
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Interval
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the complex Duhamel modes with measurable data.** The transverse inverse of a flux
that is only measurable in time (`ComplexCell.modeWC`):
* `norm_modeKC_le_one`, `norm_modeWC_le'`: the kernel is at most one and the gain of the inverse
  is `(2π|h| a₀)⁻¹` when `Re a ≥ a₀ > 0` on the history, for an integrable metric entry;
* `modeWC_congr`: the amplitude depends only on the data on the history;
* `modeWC_neg_conj`: for a real metric entry and conjugate symmetric flux modes the amplitudes are
  conjugate symmetric;
* `continuousOn_modeWC`: the amplitude is continuous in the output time on a window where the
  data are integrable (factorization of the kernel through the primitive of `a`);
* `aestronglyMeasurable_of_window`: measurability on a window subtype gives measurability on any
  measurable part of it. -/

open AVRegularity.Providers.Transverse AVRegularity.Providers.ComplexCell

/-- Measurability on a window subtype gives a.e. strong measurability on a part of it. -/
theorem aestronglyMeasurable_of_window {J S : Set ℝ} (hJ : MeasurableSet J) (hS : S ⊆ J)
    {g : ℝ → ℂ} (hg : Measurable fun t : J => g t) : AEStronglyMeasurable g (volume.restrict S) :=
  ((aemeasurable_restrict_of_measurable_subtype hJ hg).mono_set hS).aestronglyMeasurable

/-- **The complex kernel is at most one** for a metric entry with nonnegative real part. -/
theorem norm_modeKC_le_one {c : ℝ} (hc : 0 < c) {a : ℝ → ℂ} {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (h : ℤ)
    {s t : ℝ} (hst : s ≤ t) (hai : IntervalIntegrable a volume s t)
    (hre : ∀ u ∈ Icc s t, a₀ ≤ (a u).re) : ‖modeKC c a h t s‖ ≤ 1 := by
  refine (norm_modeKC_le hc h hst hai hre).trans ?_
  rw [Real.exp_le_one_iff, neg_nonpos]
  have := ComplexCell.modeRate_nonneg hc h
  have : 0 ≤ t - s := by linarith
  positivity

/-- **The gain of the complex transverse inverse** with integrable metric entry and measurable,
bounded flux. -/
theorem norm_modeWC_le' {c : ℝ} (hc : 0 < c) {a : ℝ → ℂ} {a₀ : ℝ} (ha₀ : 0 < a₀) {F : ℝ → ℂ}
    {M : ℝ} {h : ℤ} (hh : h ≠ 0) {t₀ t : ℝ} (ht : t₀ ≤ t) (hai : IntervalIntegrable a volume t₀ t)
    (hre : ∀ u ∈ Icc t₀ t, a₀ ≤ (a u).re) (hM : ∀ s ∈ Icc t₀ t, ‖F s‖ ≤ M) :
    ‖modeWC c a F t₀ h t‖ ≤ M / (2 * Real.pi * |(h : ℝ)| * a₀) := by
  have hr : 0 < modeRate c h := by
    unfold modeRate
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, ht⟩)
  have hcoup : ‖modeCoup c h‖ = 2 * Real.pi * |(h : ℝ)| / c := by
    unfold modeCoup
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hc]
    norm_num
  have hK : ∀ s ∈ Ioc t₀ t, ‖modeKC c a h t s * F s‖ ≤
      Real.exp (-(modeRate c h * a₀ * (t - s))) * M := by
    intro s hs
    rw [norm_mul]
    have hai' : IntervalIntegrable a volume s t :=
      hai.mono_set (by rw [uIcc_of_le hs.2, uIcc_of_le ht]; exact Icc_subset_Icc hs.1.le le_rfl)
    refine mul_le_mul (norm_modeKC_le hc h hs.2 hai'
      fun u hu => hre u ⟨hs.1.le.trans hu.1, hu.2⟩) (hM s ⟨hs.1.le, hs.2⟩) (norm_nonneg _)
      (Real.exp_pos _).le
  have hint : ‖∫ s in t₀..t, modeKC c a h t s * F s‖ ≤
      ∫ s in t₀..t, Real.exp (-(modeRate c h * a₀ * (t - s))) * M :=
    intervalIntegral.norm_integral_le_of_norm_le ht (Filter.Eventually.of_forall hK)
      ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _ |>.mul_const _)
  have hexp : ∫ s in t₀..t, Real.exp (-(modeRate c h * a₀ * (t - s))) * M ≤
      M / (modeRate c h * a₀) := by
    rw [intervalIntegral.integral_mul_const]
    have := integral_exp_decay_le (mul_pos hr ha₀) t₀ t
    simp_rw [mul_assoc] at this ⊢
    calc (∫ s in t₀..t, Real.exp (-(modeRate c h * (a₀ * (t - s))))) * M ≤
          1 / (modeRate c h * a₀) * M :=
          mul_le_mul_of_nonneg_right (by simpa [mul_assoc] using this) hM0
      _ = M / (modeRate c h * a₀) := by ring
  unfold modeWC
  rw [norm_mul, hcoup]
  calc 2 * Real.pi * |(h : ℝ)| / c * ‖∫ s in t₀..t, modeKC c a h t s * F s‖
      ≤ 2 * Real.pi * |(h : ℝ)| / c * (M / (modeRate c h * a₀)) :=
        mul_le_mul_of_nonneg_left (hint.trans hexp) (by positivity)
    _ = M / (2 * Real.pi * |(h : ℝ)| * a₀) := by
        unfold modeRate
        have hh' : |(h : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hh)
        have hsq : (h : ℝ) ^ 2 = |(h : ℝ)| ^ 2 := (sq_abs _).symm
        rw [hsq]
        field_simp
        ring

/-- **The amplitude depends only on the data on the history.** -/
theorem modeWC_congr {c : ℝ} {a a' F F' : ℝ → ℂ} {t₀ : ℝ} (h : ℤ) {t : ℝ} (ht : t₀ ≤ t)
    (ha : ∀ u ∈ Icc t₀ t, a u = a' u) (hF : ∀ s ∈ Icc t₀ t, F s = F' s) :
    modeWC c a F t₀ h t = modeWC c a' F' t₀ h t := by
  unfold modeWC
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  rw [hF s hs]
  congr 1
  unfold modeKC
  congr 2
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hs.2] at hu
  exact ha u ⟨hs.1.trans hu.1, hu.2⟩

/-- Conjugation commutes with interval integrals. -/
theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x) := by
  simp only [intervalIntegral, map_sub, integral_conj]

/-- **Conjugate symmetry of the amplitudes** for a real metric entry. -/
theorem modeWC_neg_conj {c : ℝ} (ar : ℝ → ℝ) {F F' : ℝ → ℂ} (hF : ∀ s, F' s = conj (F s))
    (t₀ : ℝ) (h : ℤ) (t : ℝ) :
    modeWC c (fun u => (ar u : ℂ)) F' t₀ (-h) t = conj (modeWC c (fun u => (ar u : ℂ)) F t₀ h t) := by
  rw [modeWC_ofReal, modeWC_ofReal]
  unfold modeW
  rw [map_mul, ← intervalIntegral_conj]
  congr 1
  · unfold modeCoup
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast,
      Int.cast_neg]
    ring
  · refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [map_mul, hF]
    congr 1
    unfold modeK modeRate
    rw [Complex.conj_ofReal]
    push_cast
    ring_nf

/-- **Continuity of the amplitude in the output time** on a window where the data are integrable
(the kernel factors through the primitive `P` of `a`). -/
theorem continuousOn_modeWC {c : ℝ} {a F : ℝ → ℂ} {t₀ t₁ : ℝ}
    (ha : IntervalIntegrable a volume t₀ t₁) (hF : IntervalIntegrable F volume t₀ t₁)
    (hFb : ∃ M, ∀ s ∈ Icc t₀ t₁, ‖F s‖ ≤ M) (h : ℤ) (ht : t₀ ≤ t₁) :
    ContinuousOn (fun t => modeWC c a F t₀ h t) (Icc t₀ t₁) := by
  set r : ℂ := ((modeRate c h : ℝ) : ℂ) with hr
  set P : ℝ → ℂ := fun x => ∫ u in t₀..x, a u with hP
  have hPc : ContinuousOn P (Icc t₀ t₁) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      ((intervalIntegrable_iff' (f := a) (μ := volume)).1 ha)
    rwa [uIcc_of_le ht] at this
  have hai : ∀ x y, x ∈ Icc t₀ t₁ → y ∈ Icc t₀ t₁ → IntervalIntegrable a volume x y :=
    fun x y hx hy => ha.mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le ht]) (by rwa [uIcc_of_le ht]))
  -- the integrand of the factorized amplitude
  set g : ℝ → ℂ := fun s => Complex.exp (r * P s) * F s with hg
  obtain ⟨M, hM⟩ := hFb
  have hgi : IntervalIntegrable g volume t₀ t₁ := by
    have hcont : ContinuousOn (fun s => Complex.exp (r * P s)) (uIcc t₀ t₁) := by
      rw [uIcc_of_le ht]; exact (continuousOn_const.mul hPc).cexp
    exact hF.continuousOn_mul hcont
  have hfac : ∀ t ∈ Icc t₀ t₁, modeWC c a F t₀ h t =
      modeCoup c h * (Complex.exp (-(r * P t)) * ∫ s in t₀..t, g s) := by
    intro t htJ
    unfold modeWC
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le htJ.1] at hs
    have hsJ : s ∈ Icc t₀ t₁ := ⟨hs.1, hs.2.trans htJ.2⟩
    have hsplit : ∫ u in s..t, a u = P t - P s := by
      rw [hP]
      exact (intervalIntegral.integral_interval_sub_left (hai t₀ t ⟨le_rfl, ht⟩ htJ)
        (hai t₀ s ⟨le_rfl, ht⟩ hsJ)).symm
    simp only [modeKC, hg]
    rw [hsplit, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hr]
    ring
  refine ContinuousOn.congr ?_ hfac
  refine continuousOn_const.mul (((continuousOn_const.mul hPc).neg.cexp).mul ?_)
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
    ((intervalIntegrable_iff' (f := g) (μ := volume)).1 hgi)
  rwa [uIcc_of_le ht] at this

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: sums and products of cell and family expressions; the mean and `famCell`.**
* Cell functions are transverse phase series `∑_h W_h e^{2πihη_q}`; sums add the mode functions
  and products convolve them (`CellInv.add`, `CellInv.mul`). The convolution of exponentially
  decaying modes decays at half the rate (`tsum_exp_conv_le`), and the
  convolution series of holomorphic modes is holomorphic (`differentiableOn_tsum_of_locBound`).
* Family functions do not depend on the final phase; sums and products are pointwise
  (`FamInv.add`, `FamInv.mul`).
* The mean over the real internal phase is the zero mode (`CellInv.mean`, through
  `integral_unitCube_tser`); a family function read as a cell function (`famCell`) is the zero
  mode (`FamInv.famCell`). -/

open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.Transverse

/-! ### Phase sums -/

theorem modeExp_eq_emode (q : Fin 2) (h : ℤ) (η : Vec 2) : modeExp q h η = emode h (η q) := rfl

/-- **The product of two absolutely convergent phase sums** is the phase sum of the convolution. -/
theorem hasSum_conv_emode {a c : ℤ → ℂ} {A C : ℂ} {s : ℝ}
    (ha : Summable fun h => ‖a h‖) (hc : Summable fun h => ‖c h‖)
    (hA : HasSum (fun h => a h * emode h s) A) (hC : HasSum (fun h => c h * emode h s) C) :
    HasSum (fun h => conv a c h * emode h s) (A * C) := by
  have ha' : Summable fun j => ‖a j * emode j s‖ := by simpa [norm_mul, norm_emode] using ha
  have hc' : Summable fun j => ‖c j * emode j s‖ := by simpa [norm_mul, norm_emode] using hc
  have h := (hasSum_conv ha' hc').1
  rw [hA.tsum_eq, hC.tsum_eq] at h
  convert h using 1
  funext h'
  unfold conv
  rw [← tsum_mul_right]
  congr 1; funext j
  rw [show a j * c (h' - j) * emode h' s = a j * emode j s * (c (h' - j) * emode (h' - j) s) by
    rw [show a j * emode j s * (c (h' - j) * emode (h' - j) s) =
      a j * c (h' - j) * (emode j s * emode (h' - j) s) by ring, emode_mul]
    congr 2; ring]

/-- **The cell mean of a transverse series** is its zero mode. -/
theorem integral_unitCube_tser (q : Fin 2) {A : ℤ → ℂ} (hA : Summable fun h => ‖A h‖) :
    ∫ x in AVenhance.unitCube, tser q A x = A 0 := by
  have hint : ∀ h, Integrable (fun x => A h * modeExp q h x)
      ((volume : Measure (Vec 2)).restrict AVenhance.unitCube) := by
    intro h
    rw [volume_restrict_unitCube]
    refine Integrable.of_bound (C := ‖A h‖)
      ((continuous_const.mul (contDiff_modeExp q h (n := 0)).continuous).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simp [norm_modeExp])
  have hnorm : ∀ h, ∫ x in AVenhance.unitCube, ‖A h * modeExp q h x‖ = ‖A h‖ := by
    intro h
    simp only [norm_mul, norm_modeExp, mul_one]
    rw [setIntegral_const]
    simp [Measure.real, AVenhance.unitCube, volume_pi_pi]
  have hsum : ∫ x in AVenhance.unitCube, tser q A x =
      ∑' h, ∫ x in AVenhance.unitCube, A h * modeExp q h x := by
    unfold tser
    exact (integral_tsum_of_summable_integral_norm hint (hA.congr fun h => (hnorm h).symm)).symm
  rw [hsum]
  simp_rw [integral_const_mul, integral_unitCube_modeExp]
  simp

/-- The exponential rate is monotone. -/
theorem exp_rate_le {w w' : ℝ} (hww : w' ≤ w) (h : ℤ) :
    Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)) ≤ Real.exp (-(2 * Real.pi * w' * |(h : ℝ)|)) := by
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  have := Real.pi_pos
  have : 0 ≤ |(h : ℝ)| := abs_nonneg _
  have : 2 * Real.pi * w' ≤ 2 * Real.pi * w := by nlinarith
  nlinarith

/-- The summable dominating sequence of an exponential decay. -/
theorem summable_exp_rate {w : ℝ} (hw : 0 < w) (M : ℝ) :
    Summable fun h : ℤ => M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)) := by
  have := summable_pw_mul_exp 0 (a := 2 * Real.pi * w) (by positivity)
  simpa [pw] using this.mul_left M

section Alg

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-! ### Cell expressions -/

/-- The constant of an exponential decay is nonnegative. -/
theorem decay_const_nonneg {M w : ℝ} {g : ℂ} (hg : ‖g‖ ≤ M * Real.exp (-(2 * Real.pi * w * |((0 : ℤ) : ℝ)|))) :
    0 ≤ M := by
  simpa using (norm_nonneg _).trans hg

/-- **Sums of cell expressions.** -/
theorem CellInv.add {fa fb : GenSort.Sem .cell} {Wa Wb : ℤ → Ext}
    {Ba Bb : ℝ → ℤ → ℝ → ℝ≥0∞} (ha : CellInv D b j₀ i p fa Wa Ba)
    (hc : CellInv D b j₀ i p fb Wb Bb) :
    CellInv D b j₀ i p (GenSort.add .cell fa fb) (fun h dd n t x => Wa h dd n t x + Wb h dd n t x)
      (fun mres h t => Ba mres h t + Bb mres h t) where
  hol h dd n t ht := (ha.hol h dd n t ht).add (hc.hol h dd n t ht)
  meas h dd n x hx := (ha.meas h dd n x hx).add (hc.meas h dd n x hx)
  indep h dd n t x z := by simp only [ha.indep h dd n t x z, hc.indep h dd n t x z]
  agree ch t ht hch η := by
    have := (ha.agree ch t ht hch η).add (hc.agree ch t ht hch η)
    simpa [add_mul, GenSort.add, Complex.ofReal_add] using this
  child h dd n t ht x hx k v hv := by
    simp only [ha.child h dd n t ht x hx k v hv, hc.child h dd n t ht x hx k v hv]
  decay dd n x hx := by
    obtain ⟨U, hU, M, w, hw, hM⟩ := ha.decay dd n x hx
    obtain ⟨V, hV, N, w', hw', hN⟩ := hc.decay dd n x hx
    refine ⟨U ∩ V, inter_mem hU hV, M + N, min w w', lt_min hw hw', fun h t ht y hy => ?_⟩
    have hM0 := decay_const_nonneg (hM 0 t ht y hy.1)
    have hN0 := decay_const_nonneg (hN 0 t ht y hy.2)
    calc ‖Wa h dd n t y + Wb h dd n t y‖ ≤ ‖Wa h dd n t y‖ + ‖Wb h dd n t y‖ := norm_add_le _ _
      _ ≤ M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)) +
          N * Real.exp (-(2 * Real.pi * w' * |(h : ℝ)|)) :=
          add_le_add (hM h t ht y hy.1) (hN h t ht y hy.2)
      _ ≤ M * Real.exp (-(2 * Real.pi * min w w' * |(h : ℝ)|)) +
          N * Real.exp (-(2 * Real.pi * min w w' * |(h : ℝ)|)) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (exp_rate_le (min_le_left _ _) h) hM0)
            (mul_le_mul_of_nonneg_left (exp_rate_le (min_le_right _ _) h)
              hN0)
      _ = (M + N) * Real.exp (-(2 * Real.pi * min w w' * |(h : ℝ)|)) := by ring
  mode mres hm0 hm2 h t ht dd n hdd x hx :=
    (enorm_add_le _ _).trans (add_le_add (ha.mode mres hm0 hm2 h t ht dd n hdd x hx)
      (hc.mode mres hm0 hm2 h t ht dd n hdd x hx))

/-- The modes of a cell invariant are absolutely summable on the outer carrier. -/
theorem CellInv.summable {f : GenSort.Sem .cell} {W : ℤ → Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hW : CellInv D b j₀ i p f W B) {dd : ChainData} {n : ℕ} {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n 2) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    Summable fun h => ‖W h dd n t x‖ := by
  obtain ⟨U, hU, M, w, hw, hM⟩ := hW.decay dd n x hx
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun h => hM h t ht x (mem_of_mem_nhds hU)) (summable_exp_rate hw M)

/-- **Products of cell expressions.** -/
theorem CellInv.mul (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {fa fb : GenSort.Sem .cell} {Wa Wb : ℤ → Ext}
    {Ba Bb : ℝ → ℤ → ℝ → ℝ≥0∞} (ha : CellInv D b j₀ i p fa Wa Ba)
    (hc : CellInv D b j₀ i p fb Wb Bb) :
    CellInv D b j₀ i p (GenSort.mul .cell fa fb)
      (fun h dd n t x => conv (fun k => Wa k dd n t x) (fun k => Wb k dd n t x) h)
      (fun mres h t => ∑' k, Ba mres k t * Bb mres (h - k) t) where
  hol h dd n t ht := by
    refine differentiableOn_tsum_of_locBound (isOpen_carrierC D b dd n 2)
      (fun k => (ha.hol k dd n t ht).mul (hc.hol (h - k) dd n t ht)) fun x hx => ?_
    obtain ⟨U, hU, M, w, hw, hM⟩ := ha.decay dd n x hx
    obtain ⟨V, hV, N, w', hw', hN⟩ := hc.decay dd n x hx
    have hN0 := decay_const_nonneg (hN 0 t ht x (mem_of_mem_nhds hV))
    refine ⟨U ∩ V, inter_mem hU hV, fun k => M * Real.exp (-(2 * Real.pi * w * |(k : ℝ)|)) * N,
      (summable_exp_rate hw M).mul_right N, fun k y hy => ?_⟩
    rw [norm_mul]
    refine mul_le_mul (hM k t ht y hy.1) ((hN (h - k) t ht y hy.2).trans ?_) (norm_nonneg _)
      ((norm_nonneg _).trans (hM k t ht y hy.1))
    calc N * Real.exp (-(2 * Real.pi * w' * |((h - k : ℤ) : ℝ)|)) ≤ N * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by
            have := Real.pi_pos; have := abs_nonneg ((h - k : ℤ) : ℝ)
            have : 0 ≤ 2 * Real.pi * w' * |((h - k : ℤ) : ℝ)| := by positivity
            linarith)) hN0
      _ = N := mul_one N
  meas h dd n x hx := by
    refine measurable_tsum_int (fun k => (ha.meas k dd n x hx).mul (hc.meas (h - k) dd n x hx))
      fun t => ?_
    exact (hasSum_conv (ha.summable hx t.2) (hc.summable hx t.2)).2 h
  indep h dd n t x z := by
    unfold conv
    simp only [ha.indep _ dd n t x z, hc.indep _ dd n t x z]
  agree ch t ht hch η := by
    have hx := GenSem.paramsC_mem_carrierC hΛ hb hch 0
    have := hasSum_conv_emode (ha.summable hx ht) (hc.summable hx ht) (ha.agree ch t ht hch η)
      (hc.agree ch t ht hch η)
    simpa [GenSort.mul, Complex.ofReal_mul] using this
  child h dd n t ht x hx k v hv := by
    unfold conv
    simp only [ha.child _ dd n t ht x hx k v hv, hc.child _ dd n t ht x hx k v hv]
  decay dd n x hx := by
    obtain ⟨U, hU, M, w, hw, hM⟩ := ha.decay dd n x hx
    obtain ⟨V, hV, N, w', hw', hN⟩ := hc.decay dd n x hx
    set r := min w w' with hr
    have hr0 : 0 < r := lt_min hw hw'
    set S := ∑' k : ℤ, Real.exp (-(2 * Real.pi * r / 2 * |(k : ℝ)|)) with hS
    have hS0 : 0 ≤ S := tsum_nonneg fun _ => (Real.exp_pos _).le
    refine ⟨U ∩ V, inter_mem hU hV, M * N * S, r / 2, by positivity, fun h t ht y hy => ?_⟩
    have hM0 := decay_const_nonneg (hM 0 t ht y hy.1)
    have hN0 := decay_const_nonneg (hN 0 t ht y hy.2)
    have hA : ∀ k : ℤ, ‖Wa k dd n t y‖ ≤ M * Real.exp (-(2 * Real.pi * r * |(k : ℝ)|)) :=
      fun k => (hM k t ht y hy.1).trans
        (mul_le_mul_of_nonneg_left (exp_rate_le (min_le_left _ _) k) hM0)
    have hC : ∀ k : ℤ, ‖Wb k dd n t y‖ ≤ N * Real.exp (-(2 * Real.pi * r * |(k : ℝ)|)) :=
      fun k => (hN k t ht y hy.2).trans
        (mul_le_mul_of_nonneg_left (exp_rate_le (min_le_right _ _) k) hN0)
    have hsA : Summable fun k => ‖Wa k dd n t y‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hA (summable_exp_rate hr0 M)
    have hsC : Summable fun k => ‖Wb k dd n t y‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hC (summable_exp_rate hr0 N)
    have hs1 : Summable fun k : ℤ => Real.exp (-(2 * Real.pi * r * |(k : ℝ)|)) := by
      simpa using summable_exp_rate hr0 1
    have hle1 : ∀ k : ℤ, Real.exp (-(2 * Real.pi * r * |((h - k : ℤ) : ℝ)|)) ≤ 1 := fun k =>
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by have := Real.pi_pos; positivity))
    have hsum2 : Summable fun k : ℤ => Real.exp (-(2 * Real.pi * r * |(k : ℝ)|)) *
        Real.exp (-(2 * Real.pi * r * |((h - k : ℤ) : ℝ)|)) :=
      Summable.of_nonneg_of_le (fun _ => by positivity)
        (fun k => mul_le_of_le_one_right (Real.exp_pos _).le (hle1 k)) hs1
    have hterm : ∀ k : ℤ, ‖Wa k dd n t y‖ * ‖Wb (h - k) dd n t y‖ ≤ M * N *
        (Real.exp (-(2 * Real.pi * r * |(k : ℝ)|)) *
          Real.exp (-(2 * Real.pi * r * |((h - k : ℤ) : ℝ)|))) := fun k => by
      calc ‖Wa k dd n t y‖ * ‖Wb (h - k) dd n t y‖ ≤
            (M * Real.exp (-(2 * Real.pi * r * |(k : ℝ)|))) *
              (N * Real.exp (-(2 * Real.pi * r * |((h - k : ℤ) : ℝ)|))) :=
            mul_le_mul (hA k) (hC (h - k)) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hconv := tsum_exp_conv_le (a := 2 * Real.pi * r) (by positivity) h
    calc ‖conv (fun k => Wa k dd n t y) (fun k => Wb k dd n t y) h‖
        ≤ ∑' k, ‖Wa k dd n t y‖ * ‖Wb (h - k) dd n t y‖ := norm_conv_le hsA hsC h
      _ ≤ ∑' k : ℤ, M * N * (Real.exp (-(2 * Real.pi * r * |(k : ℝ)|)) *
            Real.exp (-(2 * Real.pi * r * |((h - k : ℤ) : ℝ)|))) :=
          Summable.tsum_le_tsum hterm
            ((summable_conv_real (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hsA hsC).2 h)
            (hsum2.mul_left _)
      _ = M * N * ∑' k : ℤ, Real.exp (-(2 * Real.pi * r * |(k : ℝ)|)) *
            Real.exp (-(2 * Real.pi * r * |((h - k : ℤ) : ℝ)|)) := tsum_mul_left
      _ ≤ M * N * (S * Real.exp (-(2 * Real.pi * r / 2 * |(h : ℝ)|))) :=
          mul_le_mul_of_nonneg_left hconv (mul_nonneg hM0 hN0)
      _ = M * N * S * Real.exp (-(2 * Real.pi * (r / 2) * |(h : ℝ)|)) := by
          rw [show 2 * Real.pi * (r / 2) = 2 * Real.pi * r / 2 by ring]; ring
  mode mres hm0 hm2 h t ht dd n hdd x hx := by
    have hx2 := carrierC_mono hb.le hm2 hx
    refine (enorm_conv_le (ha.summable hx2 ht) (hc.summable hx2 ht) h).trans ?_
    exact ENNReal.tsum_le_tsum fun k => mul_le_mul' (ha.mode mres hm0 hm2 k t ht dd n hdd x hx)
      (hc.mode mres hm0 hm2 (h - k) t ht dd n hdd x hx)

/-! ### Family expressions -/

/-- **Sums of family expressions.** -/
theorem FamInv.add {fa fb : GenSort.Sem .fam} {Ga Gb : Ext} {Ba Bb : ℝ → ℤ → ℝ → ℝ≥0∞}
    (ha : FamInv D b j₀ i p fa Ga Ba) (hc : FamInv D b j₀ i p fb Gb Bb) :
    FamInv D b j₀ i p (GenSort.add .fam fa fb) (fun dd n t x => Ga dd n t x + Gb dd n t x)
      (fun mres h t => Ba mres h t + Bb mres h t) where
  hol dd n t ht := (ha.hol dd n t ht).add (hc.hol dd n t ht)
  meas dd n x hx := (ha.meas dd n x hx).add (hc.meas dd n x hx)
  indep dd n t x z := by simp only [ha.indep dd n t x z, hc.indep dd n t x z]
  agree ch t ht hch := by
    simp only [ha.agree ch t ht hch, hc.agree ch t ht hch, GenSort.add, Complex.ofReal_add]
  child dd n t ht x hx k v hv := by
    simp only [ha.child dd n t ht x hx k v hv, hc.child dd n t ht x hx k v hv]
  bdd dd n := (ha.bdd dd n).add (hc.bdd dd n)
  mode mres hm0 hm2 t ht dd n hdd x hx :=
    (enorm_add_le _ _).trans (add_le_add (ha.mode mres hm0 hm2 t ht dd n hdd x hx)
      (hc.mode mres hm0 hm2 t ht dd n hdd x hx))

/-- **Products of family expressions.** -/
theorem FamInv.mul {fa fb : GenSort.Sem .fam} {Ga Gb : Ext} {Ba Bb : ℝ → ℤ → ℝ → ℝ≥0∞}
    (ha : FamInv D b j₀ i p fa Ga Ba) (hc : FamInv D b j₀ i p fb Gb Bb) :
    FamInv D b j₀ i p (GenSort.mul .fam fa fb) (fun dd n t x => Ga dd n t x * Gb dd n t x)
      (fun mres h t => ∑' k, Ba mres k t * Bb mres (h - k) t) where
  hol dd n t ht := (ha.hol dd n t ht).mul (hc.hol dd n t ht)
  meas dd n x hx := (ha.meas dd n x hx).mul (hc.meas dd n x hx)
  indep dd n t x z := by simp only [ha.indep dd n t x z, hc.indep dd n t x z]
  agree ch t ht hch := by
    simp only [ha.agree ch t ht hch, hc.agree ch t ht hch, GenSort.mul, Complex.ofReal_mul]
  child dd n t ht x hx k v hv := by
    simp only [ha.child dd n t ht x hx k v hv, hc.child dd n t ht x hx k v hv]
  bdd dd n := (ha.bdd dd n).mul (hc.bdd dd n)
  mode mres hm0 hm2 t ht dd n hdd x hx := by
    rw [enorm_mul]
    refine (mul_le_mul' (ha.mode mres hm0 hm2 t ht dd n hdd x hx)
      (hc.mode mres hm0 hm2 t ht dd n hdd x hx)).trans ?_
    exact le_of_eq_of_le (by simp) (ENNReal.le_tsum (f := fun k => Ba mres k t * Bb mres (0 - k) t) 0)

/-! ### Changes of sort -/

/-- **A family function read as a cell function** is its own zero mode. -/
theorem FamInv.famCell {fc : GenSort.Sem .fam} {G : Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hG : FamInv D b j₀ i p fc G B) :
    CellInv D b j₀ i p (fun t ch _ => fc t ch) (fun h dd n t x => if h = 0 then G dd n t x else 0)
      (fun mres h t => if h = 0 then B mres 0 t else 0) where
  hol h dd n t ht := by
    split_ifs
    · exact hG.hol dd n t ht
    · exact differentiableOn_const 0
  meas h dd n x hx := by
    split_ifs
    · exact hG.meas dd n x hx
    · exact measurable_const
  indep h dd n t x z := by simp only [hG.indep dd n t x z]
  agree ch t ht hch η := by
    convert hasSum_ite_eq (0 : ℤ) (G ch.data ch.children.length t (ch.paramsC 0)) using 1
    · funext h
      split_ifs with h0
      · subst h0; simp [emode]
      · simp
    · rw [hG.agree ch t ht hch]
  child h dd n t ht x hx k v hv := by
    simp only [hG.child dd n t ht x hx k v hv]
  decay dd n x hx := by
    obtain ⟨U, hU, M, hM⟩ := hG.bdd dd n x hx
    refine ⟨U, hU, M, 1, one_pos, fun h t ht y hy => ?_⟩
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t ht y hy)
    split_ifs with h0
    · subst h0; simpa using hM t ht y hy
    · rw [norm_zero]; positivity
  mode mres hm0 hm2 h t ht dd n hdd x hx := by
    split_ifs with h0
    · exact hG.mode mres hm0 hm2 t ht dd n hdd x hx
    · simp

/-- **The mean over the real internal phase** (K5) is the zero mode. -/
theorem CellInv.mean (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {fw : GenSort.Sem .cell} {W : ℤ → Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hW : CellInv D b j₀ i p fw W B) :
    FamInv D b j₀ i p (cellMeanSem fw) (W 0) (fun mres h t => if h = 0 then B mres 0 t else 0) where
  hol dd n t ht := hW.hol 0 dd n t ht
  meas dd n x hx := hW.meas 0 dd n x hx
  indep dd n t := hW.indep 0 dd n t
  agree ch t ht hch := by
    have hx := GenSem.paramsC_mem_carrierC hΛ hb hch 0
    have hs := hW.summable hx ht
    have heq : ∀ η : Vec 2, ((fw t ch η : ℝ) : ℂ) =
        tser (transverseIndex p) (fun h => W h ch.data ch.children.length t (ch.paramsC 0)) η :=
      fun η => (hW.agree ch t ht hch η).tsum_eq.symm
    unfold cellMeanSem
    rw [← integral_complex_ofReal]
    simp_rw [heq]
    rw [integral_unitCube_tser _ hs]
  child dd n t ht := hW.child 0 dd n t ht
  bdd dd n x hx := by
    obtain ⟨U, hU, M, w, hw, hM⟩ := hW.decay dd n x hx
    exact ⟨U, hU, M, fun t ht y hy => by simpa using hM 0 t ht y hy⟩
  mode mres hm0 hm2 t ht dd n hdd x hx := by
    simpa using hW.mode mres hm0 hm2 0 t ht dd n hdd x hx

end Alg

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization ComplexConjugate
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the transverse primitive and the internal-phase derivative of cell functions.**
At real parameters a cell function is real, so its modes are conjugate symmetric
(`CellInv.conj_symm`, from `Transverse.phaseCoeff_neg`), and a conjugate symmetric phase sum is
real (`ofReal_re_of_conj`). This removes the real part in the semantics of the transverse primitive
(`transversePrimitiveSem`, multiplier `(2πih)⁻¹`, zero mean): `CellInv.transPrim`. The internal
derivative `∂_{η_q}` multiplies the mode `h` by `2πih` (`Transverse.fderiv_re_tser`):
`CellInv.dInternal`. The modes of the real cell function are its transverse Fourier coefficients
(`CellInv.phaseCoeff_eq`). -/

open AVRegularity.Providers.ComplexFlow AVRegularity.Providers.Transverse

/-- Exponentially decaying coefficients are rapidly decreasing. -/
theorem rapid_of_decay {c : ℤ → ℂ} {M w : ℝ} (hw : 0 < w)
    (hc : ∀ h, ‖c h‖ ≤ M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|))) : Rapid c := by
  intro k
  refine Summable.of_nonneg_of_le (fun h => mul_nonneg (pw_nonneg k h) (norm_nonneg _))
    (fun h => ?_) ((summable_pw_mul_exp k (a := 2 * Real.pi * w) (by positivity)).mul_left M)
  calc pw k h * ‖c h‖ ≤ pw k h * (M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|))) :=
        mul_le_mul_of_nonneg_left (hc h) (pw_nonneg k h)
    _ = M * (pw k h * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|))) := by ring

/-- Weighted summability (with the weight `wt`) from exponential decay. -/
theorem summable_wt_of_decay {c : ℤ → ℂ} {M w : ℝ} (hw : 0 < w)
    (hc : ∀ h, ‖c h‖ ≤ M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|))) :
    Summable fun h => ‖c h‖ * wt h ^ 1 := by
  have := (rapid_of_decay hw hc 1).mul_left (2 * Real.pi)
  refine this.congr fun h => ?_
  simp only [wt, pw, pow_one]
  ring

/-- **A conjugate symmetric phase sum is real.** -/
theorem ofReal_re_of_conj {c : ℤ → ℂ} {S : ℂ} {s : ℝ}
    (hS : HasSum (fun h => c h * emode h s) S) (hc : ∀ h, c (-h) = conj (c h)) :
    ((S.re : ℝ) : ℂ) = S := by
  have h1 := hS.mapL Complex.conjCLE.toContinuousLinearMap
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at h1
  have h2 : HasSum (fun h => c (-h) * emode (-h) s) (conj S) := by
    convert h1 using 1
    funext h
    simp only [map_mul, hc]
    congr 1
    unfold emode
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast,
      Int.cast_neg]
    ring
  have h3 : HasSum (fun h => c h * emode h s) (conj S) :=
    (Equiv.neg ℤ).hasSum_iff.mp h2
  have hcS : conj S = S := h3.unique hS
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hcS
  rw [hr, Complex.ofReal_re]

section Cell

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- Exponential decay of the real modes of a cell invariant. -/
theorem CellInv.decay_at (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {fw : GenSort.Sem .cell} {W : ℤ → Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hW : CellInv D b j₀ i p fw W B) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    ∃ M w : ℝ, 0 < w ∧ ∀ h, ‖W h ch.data ch.children.length t (ch.paramsC 0)‖ ≤
      M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)) := by
  obtain ⟨U, hU, M, w, hw, hM⟩ :=
    hW.decay _ _ _ (GenSem.paramsC_mem_carrierC hΛ hb hch 0)
  exact ⟨M, w, hw, fun h => hM h t ht _ (mem_of_mem_nhds hU)⟩

/-- **The real modes are the transverse Fourier coefficients** of the real cell function. -/
theorem CellInv.phaseCoeff_eq (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {fw : GenSort.Sem .cell}
    {W : ℤ → Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hW : CellInv D b j₀ i p fw W B) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p)
    (h : ℤ) :
    phaseCoeff (transverseIndex p) (fw t ch) h = W h ch.data ch.children.length t (ch.paramsC 0) := by
  obtain ⟨M, w, hw, hM⟩ := hW.decay_at hΛ hb hch ht
  have hps : IsPS (fun s : ℝ => ((fw t ch (s • basisVec (transverseIndex p)) : ℝ) : ℂ))
      (fun h => W h ch.data ch.children.length t (ch.paramsC 0)) := by
    refine ⟨rapid_of_decay hw hM, fun s => ?_⟩
    have := hW.agree ch t ht hch (s • basisVec (transverseIndex p))
    simpa using this
  exact hps.pcoeff_eq h

/-- The real cell function as the real part of its transverse series. -/
theorem CellInv.eq_re_tser {fw : GenSort.Sem .cell} {W : ℤ → Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hW : CellInv D b j₀ i p fw W B) {ch : RealChain} (hch : IsAdmissibleChain D b j₀ i p ch)
    {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) :
    fw t ch = fun η => (tser (transverseIndex p)
      (fun h => W h ch.data ch.children.length t (ch.paramsC 0)) η).re := by
  funext η
  have := congrArg Complex.re (hW.agree ch t ht hch η).tsum_eq
  simpa [tser, modeExp_eq_emode] using this.symm

/-- **The real modes are conjugate symmetric.** -/
theorem CellInv.conj_symm (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {fw : GenSort.Sem .cell} {W : ℤ → Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hW : CellInv D b j₀ i p fw W B) {ch : RealChain}
    (hch : IsAdmissibleChain D b j₀ i p ch) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p)
    (h : ℤ) :
    W (-h) ch.data ch.children.length t (ch.paramsC 0) =
      conj (W h ch.data ch.children.length t (ch.paramsC 0)) := by
  obtain ⟨M, w, hw, hM⟩ := hW.decay_at hΛ hb hch ht
  have hc : Continuous (fw t ch) := by
    rw [hW.eq_re_tser hch ht]
    exact Complex.continuous_re.comp
      (differentiable_tser _ (summable_wt_of_decay hw hM)).continuous
  rw [← hW.phaseCoeff_eq hΛ hb hch ht, ← hW.phaseCoeff_eq hΛ hb hch ht]
  exact phaseCoeff_neg _ _ hc h

/-! ### The transverse primitive -/

/-- The modes of the transverse primitive. -/
def transPrimW (W : ℤ → Ext) (h : ℤ) : Ext :=
  fun dd n t x => if h = 0 then 0 else (2 * Real.pi * Complex.I * (h : ℂ))⁻¹ * W h dd n t x

theorem norm_two_pi_I_mul (h : ℤ) (z : ℂ) :
    ‖2 * Real.pi * Complex.I * (h : ℂ) * z‖ = 2 * Real.pi * |(h : ℝ)| * ‖z‖ := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp

theorem norm_two_pi_I_inv_le {h : ℤ} (hh : h ≠ 0) :
    ‖(2 * Real.pi * Complex.I * (h : ℂ))⁻¹‖ ≤ 1 := by
  have hh' : (1 : ℝ) ≤ |(h : ℝ)| := by
    have := Int.one_le_abs hh
    exact_mod_cast this
  have hn : ‖(2 * Real.pi * Complex.I * (h : ℂ))‖ = 2 * Real.pi * |(h : ℝ)| := by
    simp
  rw [norm_inv, hn]
  refine inv_le_one_of_one_le₀ ?_
  have := Real.pi_gt_three
  nlinarith

/-- **The transverse primitive of a cell expression.** -/
theorem CellInv.transPrim (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {fw : GenSort.Sem .cell} {W : ℤ → Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hW : CellInv D b j₀ i p fw W B) :
    CellInv D b j₀ i p (transversePrimitiveSem p fw) (transPrimW W)
      (fun mres h t => modeGain h * B mres h t) where
  hol h dd n t ht := by
    unfold transPrimW
    split_ifs
    · exact differentiableOn_const 0
    · exact (hW.hol h dd n t ht).const_mul _
  meas h dd n x hx := by
    unfold transPrimW
    split_ifs
    · exact measurable_const
    · exact (hW.meas h dd n x hx).const_mul _
  indep h dd n t x z := by simp only [transPrimW, hW.indep h dd n t x z]
  agree ch t ht hch η := by
    set q := transverseIndex p
    obtain ⟨M, w, hw, hM⟩ := hW.decay_at hΛ hb hch ht
    set c : ℤ → ℂ := fun h => transPrimW W h ch.data ch.children.length t (ch.paramsC 0) with hc
    have hcb : ∀ h, ‖c h‖ ≤ ‖W h ch.data ch.children.length t (ch.paramsC 0)‖ := by
      intro h
      simp only [hc, transPrimW]
      split_ifs with h0
      · rw [norm_zero]; exact norm_nonneg _
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_two_pi_I_inv_le h0)
    have hs : Summable fun h => c h * emode h (η q) := by
      refine Summable.of_norm_bounded (summable_exp_rate hw M) fun h => ?_
      rw [norm_mul, norm_emode, mul_one]
      exact (hcb h).trans (hM h)
    have hcs : ∀ h, c (-h) = conj (c h) := by
      intro h
      simp only [hc, transPrimW, neg_eq_zero]
      split_ifs with h0
      · simp
      · rw [hW.conj_symm hΛ hb hch ht h, map_mul, map_inv₀]
        congr 1
        simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast,
          Int.cast_neg]
        ring
    have hsem : transversePrimitiveSem p fw t ch η = (∑' h, c h * emode h (η q)).re := by
      unfold transversePrimitiveSem
      congr 1
      refine tsum_congr fun h => ?_
      simp only [hc, transPrimW]
      split_ifs <;> simp [hW.phaseCoeff_eq hΛ hb hch ht, emode, q]
    rw [hsem, ofReal_re_of_conj hs.hasSum hcs]
    exact hs.hasSum
  child h dd n t ht x hx k v hv := by
    simp only [transPrimW, hW.child h dd n t ht x hx k v hv]
  decay dd n x hx := by
    obtain ⟨U, hU, M, w, hw, hM⟩ := hW.decay dd n x hx
    refine ⟨U, hU, M, w, hw, fun h t ht y hy => ?_⟩
    have hM0 := decay_const_nonneg (hM 0 t ht y hy)
    unfold transPrimW
    split_ifs with h0
    · rw [norm_zero]; positivity
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_two_pi_I_inv_le h0)).trans
        (hM h t ht y hy)
  mode mres hm0 hm2 h t ht dd n hdd x hx := by
    unfold transPrimW modeGain
    split_ifs with h0
    · simp
    · rw [enorm_mul]
      refine mul_le_mul' (le_of_eq ?_) (hW.mode mres hm0 hm2 h t ht dd n hdd x hx)
      have hpos : 0 < 2 * Real.pi * |(h : ℝ)| := by
        have : (h : ℝ) ≠ 0 := by exact_mod_cast h0
        positivity
      rw [← ofReal_norm, modeMul, norm_inv, ← ENNReal.ofReal_inv_of_pos hpos]
      congr 1
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      simp

/-! ### The internal-phase derivative -/

/-- The modes of the internal-phase derivative. -/
def dInternalW (W : ℤ → Ext) (h : ℤ) : Ext :=
  fun dd n t x => 2 * Real.pi * Complex.I * (h : ℂ) * W h dd n t x

/-- `2π|h| e^{-2πw|h|} ≤ (2/w) e^{-πw|h|}`. -/
theorem mode_mul_exp_le {w : ℝ} (hw : 0 < w) (h : ℤ) :
    2 * Real.pi * |(h : ℝ)| * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)) ≤
      2 / w * Real.exp (-(2 * Real.pi * (w / 2) * |(h : ℝ)|)) := by
  set x := Real.pi * w * |(h : ℝ)| with hx
  have hx0 : 0 ≤ x := by positivity
  have hle : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have e1 : Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; rw [hx]; ring
  have e2 : Real.exp (-(2 * Real.pi * (w / 2) * |(h : ℝ)|)) = Real.exp (-x) := by
    congr 1; rw [hx]; ring
  rw [e1, e2]
  have hxe : x * Real.exp (-x) ≤ 1 := by
    calc x * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : 2 * Real.pi * |(h : ℝ)| = 2 / w * x := by rw [hx]; field_simp
  rw [h2]
  have hw2 : 0 ≤ 2 / w := by positivity
  calc 2 / w * x * (Real.exp (-x) * Real.exp (-x)) = 2 / w * (x * Real.exp (-x)) * Real.exp (-x) := by
        ring
    _ ≤ 2 / w * 1 * Real.exp (-x) := by gcongr
    _ = 2 / w * Real.exp (-x) := by ring

/-- **The internal-phase derivative of a cell expression.** -/
theorem CellInv.dInternal (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {fw : GenSort.Sem .cell} {W : ℤ → Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hW : CellInv D b j₀ i p fw W B) :
    CellInv D b j₀ i p (fun t ch η => fderiv ℝ (fw t ch) η (basisVec (transverseIndex p)))
      (dInternalW W) (fun mres h t => modeMul h * B mres h t) where
  hol h dd n t ht := (hW.hol h dd n t ht).const_mul _
  meas h dd n x hx := (hW.meas h dd n x hx).const_mul _
  indep h dd n t x z := by simp only [dInternalW, hW.indep h dd n t x z]
  agree ch t ht hch η := by
    set q := transverseIndex p
    obtain ⟨M, w, hw, hM⟩ := hW.decay_at hΛ hb hch ht
    have hM0 := decay_const_nonneg (hM 0)
    set A : ℤ → ℂ := fun h => W h ch.data ch.children.length t (ch.paramsC 0) with hA
    have hAw := summable_wt_of_decay hw hM
    set c : ℤ → ℂ := fun h => 2 * Real.pi * Complex.I * (h : ℂ) * A h with hc
    have hcb : ∀ h, ‖c h‖ ≤ 2 / w * M * Real.exp (-(2 * Real.pi * (w / 2) * |(h : ℝ)|)) := by
      intro h
      simp only [hc]
      rw [norm_two_pi_I_mul]
      calc 2 * Real.pi * |(h : ℝ)| * ‖A h‖ ≤
            2 * Real.pi * |(h : ℝ)| * (M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|))) :=
            mul_le_mul_of_nonneg_left (hM h) (by positivity)
        _ = M * (2 * Real.pi * |(h : ℝ)| * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|))) := by ring
        _ ≤ M * (2 / w * Real.exp (-(2 * Real.pi * (w / 2) * |(h : ℝ)|))) :=
            mul_le_mul_of_nonneg_left (mode_mul_exp_le hw h) hM0
        _ = 2 / w * M * Real.exp (-(2 * Real.pi * (w / 2) * |(h : ℝ)|)) := by ring
    have hs : Summable fun h => c h * emode h (η q) := by
      refine Summable.of_norm_bounded (summable_exp_rate (by positivity : 0 < w / 2) (2 / w * M))
        fun h => ?_
      rw [norm_mul, norm_emode, mul_one]
      exact hcb h
    have hcs : ∀ h, c (-h) = conj (c h) := by
      intro h
      simp only [hc, hA, hW.conj_symm hΛ hb hch ht h, map_mul, map_ofNat, Complex.conj_ofReal,
        Complex.conj_I, map_intCast, Int.cast_neg]
      ring
    rw [hW.eq_re_tser hch ht, fderiv_re_tser q hAw η q]
    have e : (fun h : ℤ => (if q = q then 2 * Real.pi * Complex.I * (h : ℂ) else 0) * A h) = c := by
      funext h; simp [hc]
    rw [e]
    show HasSum _ (((∑' h, c h * modeExp q h η).re : ℝ) : ℂ)
    simp only [modeExp_eq_emode]
    rw [ofReal_re_of_conj hs.hasSum hcs]
    exact hs.hasSum
  child h dd n t ht x hx k v hv := by
    simp only [dInternalW, hW.child h dd n t ht x hx k v hv]
  decay dd n x hx := by
    obtain ⟨U, hU, M, w, hw, hM⟩ := hW.decay dd n x hx
    refine ⟨U, hU, 2 / w * M, w / 2, by positivity, fun h t ht y hy => ?_⟩
    have hM0 := decay_const_nonneg (hM 0 t ht y hy)
    simp only [dInternalW]
    rw [norm_two_pi_I_mul]
    calc 2 * Real.pi * |(h : ℝ)| * ‖W h dd n t y‖ ≤
          2 * Real.pi * |(h : ℝ)| * (M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|))) :=
          mul_le_mul_of_nonneg_left (hM h t ht y hy) (by positivity)
      _ = M * (2 * Real.pi * |(h : ℝ)| * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|))) := by ring
      _ ≤ M * (2 / w * Real.exp (-(2 * Real.pi * (w / 2) * |(h : ℝ)|))) :=
          mul_le_mul_of_nonneg_left (mode_mul_exp_le hw h) hM0
      _ = 2 / w * M * Real.exp (-(2 * Real.pi * (w / 2) * |(h : ℝ)|)) := by ring
  mode mres hm0 hm2 h t ht dd n hdd x hx := by
    simp only [dInternalW]
    rw [enorm_mul]
    refine mul_le_mul' (le_of_eq ?_) (hW.mode mres hm0 hm2 h t ht dd n hdd x hx)
    rw [← ofReal_norm, modeMul]
    congr 1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp

end Cell

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal Interval
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the restriction of a context function to real phases** (`restrict`). A context
function at real phases is a cell function with internal phase `η = ζ`. Its cell modes are the
final-phase coefficients at the real final phase `0` (`restrictW`): holomorphic in the parameters
(parametric integral of a holomorphic family), measurable in time (Carathéodory), and decaying
like `e^{-4πb|h|}` locally uniformly and uniformly in time (contour shift on the strip
`|Im ζ_q| < 3b`, with the time-uniform bound on a compact set, `LocBdd.exists_bound`). The cell
function is their phase series by the final-phase periodicity and the parallel invariance
(`CtxInv.restrict`). -/

open AVRegularity.Providers.ComplexFlow

/-- **A locally bounded family is bounded on compact sets**, uniformly in time. -/
theorem LocBdd.exists_bound {n : ℕ} {F : ℝ → ChainParamsC n → ℂ} {T : Set ℝ}
    {S : Set (ChainParamsC n)} (hF : LocBdd F T S) {K : Set (ChainParamsC n)} (hK : IsCompact K)
    (hKS : K ⊆ S) : ∃ M : ℝ, ∀ t ∈ T, ∀ y ∈ K, ‖F t y‖ ≤ M := by
  choose U hU M hM using fun x (hx : x ∈ K) => hF x (hKS hx)
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' U hU
  refine ⟨∑ x ∈ s, |M x.1 x.2|, fun t ht y hy => ?_⟩
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs hy)
  refine (hM x.1 x.2 t ht y hyx).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun x : K => |M x.1 x.2|) (fun _ _ => abs_nonneg _) hxs

/-- **Measurability of a parametric interval integral** of a function continuous in the
integration variable and measurable in the parameter (Carathéodory). -/
theorem measurable_intervalIntegral_caratheodory {α : Type*} [MeasurableSpace α]
    {u : ℝ → α → ℂ} (hc : ∀ x, Continuous fun s => u s x) (hm : ∀ s, Measurable (u s))
    (a c : ℝ) : Measurable fun x => ∫ s in a..c, u s x := by
  have hu : StronglyMeasurable (Function.uncurry u) :=
    (measurable_uncurry_of_continuous_of_measurable hc hm).stronglyMeasurable
  have h1 := hu.integral_prod_left (μ := volume.restrict (Ioc a c))
  have h2 := hu.integral_prod_left (μ := volume.restrict (Ioc c a))
  simp only [intervalIntegral]
  exact (h1.sub h2).measurable

/-- The real final-phase line through the parameters `x` with final phase `0`. -/
def realLine {n : ℕ} (q : Fin 2) (x : ChainParamsC n) (z : ℂ) : ChainParamsC n :=
  (x.1, x.2.1, evec q z)

theorem continuous_realLine {n : ℕ} (q : Fin 2) :
    Continuous fun r : ChainParamsC n × ℂ => realLine q r.1 r.2 := by
  unfold realLine evec
  refine continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk ?_)
  refine continuous_pi fun a => ?_
  split_ifs
  · exact continuous_snd
  · exact continuous_const

/-- The real final-phase line stays in the outer carrier on the strip `|Im z| < 7b/2`. -/
theorem realLine_mem {D : OCData} {b : ℝ} {dd : ChainData} {n : ℕ} (q : Fin 2)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) (hb : 0 < b) {z : ℂ}
    (hz : |z.im| < (3 + 2 / 4) * b) : realLine q x z ∈ carrierC D b dd n 2 := by
  refine ⟨hx.1, hx.2.1, ?_⟩
  show |(evec q z (transverseIndex (dd.slots.getLastD 0))).im| < _
  unfold evec
  split_ifs
  · exact hz
  · simp only [Complex.zero_im, abs_zero]; positivity

/-- The real final-phase line is the final-phase line at the final phase `0`. -/
theorem lineF_realLine {n : ℕ} (q : Fin 2) (G : ChainParamsC n → ℂ) (x : ChainParamsC n)
    (z : ℂ) : lineF q G (x.1, x.2.1, 0) z = G (realLine q x z) := by
  simp [lineF, realLine]

/-- The unit translation of the real final-phase line. -/
theorem realLine_add_one {n : ℕ} (q : Fin 2) (x : ChainParamsC n) (z : ℂ) :
    ChainParamsC.shiftFinal (realLine q x z) (rvec q) = realLine q x (z + 1) := by
  simp only [realLine, ChainParamsC.shiftFinal, Prod.mk.injEq, true_and]
  funext a
  simp only [Pi.add_apply, evec, rvec]
  split_ifs <;> push_cast <;> ring

theorem tInt_rvec_any (p : ℤ) (q : Fin 2) : TInt p (rvec q) := by
  unfold TInt rvec
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

/-- The cell modes of the restriction: the final-phase coefficients at the final phase `0`. -/
def restrictW (q : Fin 2) (F : Ext) (h : ℤ) : Ext :=
  fun dd n t x => finalPhaseCoeff q (F dd n t) (x.1, x.2.1, 0) h

section Restrict

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- **The modes of the restriction decay** locally uniformly and uniformly in time. -/
theorem restrictW_decay {f : GenSort.Sem .ctx} {F : Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : CtxInv D b j₀ i p f F B) (hb : 0 < b) (q : Fin 2) (dd : ChainData) (n : ℕ)
    {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n 2) :
    ∃ U ∈ 𝓝 x, ∃ M w : ℝ, 0 < w ∧ ∀ (h : ℤ), ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ y ∈ U,
      ‖restrictW q F h dd n t y‖ ≤ M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|)) := by
  have : ProperSpace (ChainParamsC n) := FiniteDimensional.proper ℂ _
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp (isOpen_carrierC D b dd n 2) x hx
  set K : Set (ChainParamsC n) := (fun r : ChainParamsC n × ℂ => realLine q r.1 r.2) ''
    (closedBall x (r / 2) ×ˢ (Icc (0 : ℝ) 1 ×ℂ Icc (-(3 * b)) (3 * b))) with hK
  have hKc : IsCompact K :=
    ((isCompact_closedBall x _).prod (isCompact_Icc.reProdIm isCompact_Icc)).image
      (continuous_realLine q)
  have hKS : K ⊆ carrierC D b dd n 2 := by
    rintro _ ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
    have hy' : y ∈ carrierC D b dd n 2 :=
      hrS (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith)))
    refine realLine_mem q hy' hb ?_
    have := (Complex.mem_reProdIm.mp hz).2
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  obtain ⟨M, hM⟩ := (hF.bdd dd n).exists_bound hKc hKS
  refine ⟨ball x (r / 2), ball_mem_nhds x (by positivity), M, 2 * b, by positivity,
    fun h t ht y hy => ?_⟩
  have hy' : y ∈ carrierC D b dd n 2 := hrS (mem_ball.mpr (lt_trans (mem_ball.mp hy) (by linarith)))
  have hline : ∀ z : ℂ, |z.im| < (3 + 2 / 4) * b → realLine q y z ∈ carrierC D b dd n 2 :=
    fun z hz => realLine_mem q hy' hb hz
  have hper : ∀ z : ℂ, |z.im| < 3 * b →
      F dd n t (realLine q y (z + 1)) = F dd n t (realLine q y z) := by
    intro z hz
    rw [← realLine_add_one]
    exact hF.fin dd n t ht _ (hline z (by linarith)) _ (tInt_rvec_any _ q)
  have hbd : ∀ z : ℂ, |z.im| < 3 * b → ‖F dd n t (realLine q y z)‖ ≤ M := by
    intro z hz
    have hp' : ∀ z : ℂ, z.im ∈ {s : ℝ | |s| < 3 * b} →
        F dd n t (realLine q y (z + 1)) = F dd n t (realLine q y z) := fun z hz => hper z hz
    have e := strip_periodic_int (G := fun z => F dd n t (realLine q y z)) hp' (-⌊z.re⌋) z hz
    rw [← e]
    refine hM t ht _ ⟨(y, z + (-⌊z.re⌋ : ℤ)), ⟨mem_closedBall.mpr (le_of_lt (mem_ball.mp hy)),
      Complex.mem_reProdIm.mpr ⟨?_, ?_⟩⟩, rfl⟩
    · have h1 := Int.floor_le z.re
      have h2 := Int.lt_floor_add_one z.re
      simp only [Complex.add_re, Complex.intCast_re]
      push_cast
      constructor <;> linarith
    · simp only [Complex.add_im, Complex.intCast_im, add_zero]
      exact ⟨by linarith [neg_abs_le z.im], by linarith [le_abs_self z.im]⟩
  have hl : Differentiable ℂ fun z : ℂ => realLine q y z := by
    unfold realLine
    refine (differentiable_const _).prodMk ((differentiable_const _).prodMk ?_)
    rw [differentiable_pi]
    intro a
    unfold evec
    split_ifs
    · exact differentiable_id
    · exact differentiable_const _
  have hdiff : DifferentiableOn ℂ (fun z => F dd n t (realLine q y z))
      {z : ℂ | |z.im| < 3 * b} :=
    (hF.hol dd n t ht).comp hl.differentiableOn fun z hz => hline z (by
      have : |z.im| < 3 * b := hz
      linarith)
  have := norm_pcoeff_le_of_strip (G := fun z => F dd n t (realLine q y z)) (w := 3 * b)
    (M := M) hdiff hper hbd h (w' := 2 * b) (by positivity) (by linarith)
  simpa [restrictW, finalPhaseCoeff_eq_pcoeff, lineF_realLine] using this

/-- The modes of the restriction as integrals along the real final-phase line. -/
theorem restrictW_eq (q : Fin 2) (F : Ext) (h : ℤ) (dd : ChainData) (n : ℕ) (t : ℝ)
    (x : ChainParamsC n) :
    restrictW q F h dd n t x = ∫ s in (0 : ℝ)..1, F dd n t (realLine q x s) *
      Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * (s : ℂ))) := by
  unfold restrictW finalPhaseCoeff realLine evec
  simp only [zero_add]

/-- **The restriction of a context function to real phases** (K4). -/
theorem CtxInv.restrict (hΛ : 1 ≤ D.Λ) (hb : 0 < b) {fa : GenSort.Sem .ctx} {F : Ext}
    {B : ℝ → ℤ → ℝ → ℝ≥0∞} (hF : CtxInv D b j₀ i p fa F B) :
    CellInv D b j₀ i p fa (restrictW (transverseIndex p) F) B where
  hol h dd n t ht := by
    have hU := isOpen_carrierC D b dd n 2
    have hmem : ∀ x ∈ carrierC D b dd n 2, ∀ s : ℝ,
        realLine (transverseIndex p) x s ∈ carrierC D b dd n 2 := fun x hx s =>
      realLine_mem _ hx hb (by simp only [Complex.ofReal_im, abs_zero]; positivity)
    have e : restrictW (transverseIndex p) F h dd n t = fun x => ∫ s in (0 : ℝ)..1,
        F dd n t (realLine (transverseIndex p) x s) *
          Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * (s : ℂ))) :=
      funext fun x => restrictW_eq _ F h dd n t x
    rw [e]
    refine differentiableOn_intervalIntegral_of_param hU (fun s _ => ?_) ?_
    · have hl : Differentiable ℂ fun x : ChainParamsC n => realLine (transverseIndex p) x s := by
        unfold realLine
        exact differentiable_fst.prodMk (differentiable_snd.fst.prodMk (differentiable_const _))
      exact ((hF.hol dd n t ht).comp hl.differentiableOn fun x hx => hmem x hx s).mul_const _
    · refine ContinuousOn.mul ?_ (by fun_prop)
      refine (hF.hol dd n t ht).continuousOn.comp ((continuous_realLine _).comp
        (continuous_fst.prodMk (Complex.continuous_ofReal.comp continuous_snd))).continuousOn ?_
      rintro ⟨x, s⟩ ⟨hx, -⟩
      exact hmem x hx s
  meas h dd n x hx := by
    have hmem : ∀ s : ℝ, realLine (transverseIndex p) x s ∈ carrierC D b dd n 2 := fun s =>
      realLine_mem _ hx hb (by simp only [Complex.ofReal_im, abs_zero]; positivity)
    simp_rw [restrictW_eq]
    refine measurable_intervalIntegral_caratheodory (fun t => ?_) (fun s => ?_) 0 1
    · refine ContinuousOn.comp_continuous ?_ ((continuous_realLine _).comp
        (continuous_const.prodMk Complex.continuous_ofReal)) hmem |>.mul (by fun_prop)
      exact (hF.hol dd n t t.2).continuousOn
    · exact (hF.meas dd n _ (hmem s)).mul_const _
  indep h dd n t x z := rfl
  agree ch t ht hch η := by
    set q := transverseIndex p
    have hx := GenSem.paramsC_mem_carrierC hΛ hb hch 0
    have hdd : AdmData D b j₀ i p ch.data ch.children.length := ⟨ch, hch, rfl, rfl⟩
    have hre : RealFinal (ch.paramsC 0) := fun a => by simp [RealChain.paramsC]
    have h0 : ((ch.paramsC 0).1, (ch.paramsC 0).2.1, (0 : Fin 2 → ℂ)) = ch.paramsC 0 := by
      refine Prod.ext rfl (Prod.ext rfl (funext fun a => ?_))
      simp [RealChain.paramsC]
    have hps := hF.isPS hb ht hdd le_rfl hx hre
    have hsum := hps.sum (η q)
    have hcoef : ∀ h, restrictW q F h ch.data ch.children.length t (ch.paramsC 0) =
        pcoeff (fun s : ℝ => lineF q (F ch.data ch.children.length t) (ch.paramsC 0) s) h := by
      intro h
      unfold restrictW
      rw [h0, finalPhaseCoeff_eq_pcoeff]
    simp_rw [hcoef]
    convert hsum using 1
    -- the value of the line at `η_q` is the value at `η`, by the parallel invariance
    have hsl : (ch.data.slots.getLastD 0) = p := hdd.lastSlot
    set y : ChainParamsC ch.children.length :=
      ((ch.paramsC 0).1, (ch.paramsC 0).2.1, (ch.paramsC 0).2.2 + evec q (η q)) with hy
    have hyC : y ∈ carrierC D b ch.data ch.children.length 2 := by
      have := mem_carrierC_line hx (hre _) (z := ((η q : ℝ) : ℂ)) (by
        simp only [Complex.ofReal_im, abs_zero]; positivity)
      rwa [hsl] at this
    set v : Vec 2 := fun a => if a = q then 0 else η a with hv
    have hTv : TInt (ch.data.slots.getLastD 0) v := by
      refine ⟨0, ?_⟩
      rw [hsl]
      simp only [hv, q, ↓reduceIte, Int.cast_zero]
    have hshift : y.shiftFinal v = ch.paramsC η := by
      refine Prod.ext rfl (Prod.ext rfl (funext fun a => ?_))
      simp only [hy, ChainParamsC.shiftFinal, Pi.add_apply, evec, hv, RealChain.paramsC]
      split_ifs with ha
      · subst ha; simp
      · simp
    rw [← hF.agree ch t ht η hch, ← hshift, hF.fin _ _ t ht y hyC v hTv]
    rfl
  child h dd n t ht x hx k v hv := by
    have hmem : ∀ s : ℝ, realLine (transverseIndex p) x s ∈ carrierC D b dd n 2 := fun s =>
      realLine_mem _ hx hb (by simp only [Complex.ofReal_im, abs_zero]; positivity)
    rw [restrictW_eq, restrictW_eq]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show realLine (transverseIndex p) (x.shiftChild k v) s =
      (realLine (transverseIndex p) x s).shiftChild k v from rfl,
      hF.child dd n t ht _ (hmem s) k v hv]
  decay dd n x hx := restrictW_decay hF hb _ dd n hx
  mode mres hm0 hm2 h t ht dd n hdd x hx :=
    hF.mode mres hm0 hm2 h t ht dd n hdd _ (carrierC_final_zero (by linarith) hx hb)
      (fun a => by simp)

end Restrict

end AVRegularity.Providers.ComplexContext
end
