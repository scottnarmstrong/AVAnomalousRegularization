-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.First.Identity
import AVRegularity.Proofs.GenSem.Op.FamChart
import AVRegularity.Proofs.CascadeInvariants.Scales
public import AVRegularity.Proofs.ComplexContext.CellInvC
import AVRegularity.CycleComparison.Diagonal.Main
import AVRegularity.CycleReference.SingleModeFlux
public import AVRegularity.EntryWeak.NormalizedPulseTransverse
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open MeasureTheory Set
open scoped Interval
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: two metrics in the complex transverse inverse.** For metric entries
`a, a'` with real parts at least `a₀ > 0` on the history and `|a − a'| ≤ δ` there, the Duhamel
amplitudes of a bounded flux differ by at most `δ M / (2π|h| a₀²)` (`norm_modeWC_sub_le`). This is
the mode estimate of the quadratic difference `𝒫^𝒢(χ_𝒢 − χ_I) = div((𝒢 − I)∇χ_I)`, for
transverse correctors with one phase direction:
* `norm_cexp_neg_sub_le`: two exponentials on the half-plane `Re ≥ X`;
* `integral_mul_exp_decay_le`: `∫ (t − s) e^{−k(t−s)} ≤ k⁻²`;
* `norm_modeKC_sub_le`: the kernels differ by `r δ (t − s) e^{−r a₀ (t − s)}`. -/

open AVRegularity.Providers.Transverse AVRegularity.Providers.ComplexCell

/-- **Two exponentials on a half-plane.** -/
theorem norm_cexp_neg_sub_le {X : ℝ} {z w : ℂ} (hz : X ≤ z.re) (hw : X ≤ w.re) :
    ‖Complex.exp (-z) - Complex.exp (-w)‖ ≤ Real.exp (-X) * ‖z - w‖ := by
  have hs : Convex ℝ {u : ℂ | X ≤ u.re} := convex_halfSpace_re_ge X
  have hd : ∀ u ∈ {u : ℂ | X ≤ u.re}, DifferentiableAt ℂ (fun u : ℂ => Complex.exp (-u)) u :=
    fun u _ => (Complex.differentiable_exp.comp differentiable_neg).differentiableAt
  have hb : ∀ u ∈ {u : ℂ | X ≤ u.re}, ‖deriv (fun u : ℂ => Complex.exp (-u)) u‖ ≤
      Real.exp (-X) := by
    intro u hu
    have e : deriv (fun u : ℂ => Complex.exp (-u)) u = -Complex.exp (-u) := by
      rw [((hasDerivAt_neg u).cexp).deriv]; ring
    rw [e, norm_neg, Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (by linarith [show X ≤ u.re from hu])
  exact hs.norm_image_sub_le_of_norm_deriv_le hd hb hw hz

/-- **The first moment of the decaying exponential.** -/
theorem integral_mul_exp_decay_le {k : ℝ} (hk : 0 < k) {t₀ t : ℝ} (ht : t₀ ≤ t) :
    ∫ s in t₀..t, (t - s) * Real.exp (-(k * (t - s))) ≤ 1 / k ^ 2 := by
  have hder : ∀ s ∈ uIcc t₀ t, HasDerivAt
      (fun s => ((t - s) / k + 1 / k ^ 2) * Real.exp (-(k * (t - s))))
      ((t - s) * Real.exp (-(k * (t - s)))) s := by
    intro s _
    have h0 : HasDerivAt (fun s => t - s) (-1) s := by
      have := (hasDerivAt_id s).const_sub t
      simpa using this
    have h1 : HasDerivAt (fun s => -(k * (t - s))) k s := by
      convert (h0.const_mul k).neg using 1; ring
    have h3 : HasDerivAt (fun s => (t - s) / k + 1 / k ^ 2) (-1 / k) s := by
      convert (h0.div_const k).add_const (1 / k ^ 2) using 1
    convert h3.mul h1.exp using 1
    field_simp
    ring
  have hcont : Continuous fun s => (t - s) * Real.exp (-(k * (t - s))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable _ _)]
  simp only [sub_self, zero_div, zero_add, mul_zero, neg_zero, Real.exp_zero, mul_one]
  have : 0 ≤ ((t - t₀) / k + 1 / k ^ 2) * Real.exp (-(k * (t - t₀))) := by
    have : 0 ≤ t - t₀ := by linarith
    positivity
  linarith

/-- The real part of `r ∫_s^t b` is at least `r a₀ (t − s)`. -/
theorem re_mul_integral_ge {r a₀ : ℝ} (hr : 0 ≤ r) {b : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t)
    (hb : IntervalIntegrable b volume s t) (hbr : ∀ u ∈ Icc s t, a₀ ≤ (b u).re) :
    r * a₀ * (t - s) ≤ ((r : ℂ) * ∫ u in s..t, b u).re := by
  have hre_int : (∫ u in s..t, b u).re = ∫ u in s..t, (b u).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hb).symm
  have h1 : ∫ _ in s..t, a₀ ≤ ∫ u in s..t, (b u).re :=
    intervalIntegral.integral_mono_on hst intervalIntegrable_const ⟨hb.1.re, hb.2.re⟩ hbr
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  rw [Complex.re_ofReal_mul, hre_int]
  have h2 : r * ((t - s) * a₀) ≤ r * ∫ u in s..t, (b u).re := mul_le_mul_of_nonneg_left h1 hr
  linarith

/-- **Two kernels.** -/
theorem norm_modeKC_sub_le {c : ℝ} (hc : 0 < c) {a a' : ℝ → ℂ} {a₀ δ : ℝ} (h : ℤ) {s t : ℝ}
    (hst : s ≤ t) (hai : IntervalIntegrable a volume s t)
    (hai' : IntervalIntegrable a' volume s t) (hre : ∀ u ∈ Icc s t, a₀ ≤ (a u).re)
    (hre' : ∀ u ∈ Icc s t, a₀ ≤ (a' u).re) (hδ : ∀ u ∈ Icc s t, ‖a u - a' u‖ ≤ δ) :
    ‖modeKC c a h t s - modeKC c a' h t s‖ ≤
      Real.exp (-(modeRate c h * a₀ * (t - s))) * (modeRate c h * (δ * (t - s))) := by
  have hr := AVRegularity.Providers.ComplexCell.modeRate_nonneg hc h
  have e : ∀ b : ℝ → ℂ, modeKC c b h t s =
      Complex.exp (-(((modeRate c h : ℝ) : ℂ) * ∫ u in s..t, b u)) := fun b => by
    unfold modeKC; rw [neg_mul]
  rw [e a, e a']
  refine (norm_cexp_neg_sub_le (re_mul_integral_ge hr hst hai hre)
    (re_mul_integral_ge hr hst hai' hre')).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [← mul_sub, ← intervalIntegral.integral_sub hai hai', norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr]
  refine mul_le_mul_of_nonneg_left ?_ hr
  have hb : ∀ u ∈ Ι s t, ‖a u - a' u‖ ≤ δ := fun u hu => by
    rw [uIoc_of_le hst] at hu
    exact hδ u ⟨hu.1.le, hu.2⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [abs_of_nonneg (by linarith : 0 ≤ t - s)] at this

/-- The kernel is integrable against an integrable flux on the history. -/
theorem intervalIntegrable_modeKC_mul {c : ℝ} {a F : ℝ → ℂ} {t₀ t : ℝ} (ht : t₀ ≤ t)
    (ha : IntervalIntegrable a volume t₀ t) (hF : IntervalIntegrable F volume t₀ t) (h : ℤ) :
    IntervalIntegrable (fun s => modeKC c a h t s * F s) volume t₀ t := by
  set P : ℝ → ℂ := fun x => ∫ u in t₀..x, a u with hP
  have hPc : ContinuousOn P (Icc t₀ t) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      ((intervalIntegrable_iff' (f := a) (μ := volume)).1 ha)
    rwa [uIcc_of_le ht] at this
  have hai : ∀ x y, x ∈ Icc t₀ t → y ∈ Icc t₀ t → IntervalIntegrable a volume x y :=
    fun x y hx hy => ha.mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le ht])
      (by rwa [uIcc_of_le ht]))
  have hK : ContinuousOn (fun s => modeKC c a h t s) (uIcc t₀ t) := by
    rw [uIcc_of_le ht]
    have e : EqOn (fun s => modeKC c a h t s)
        (fun s => Complex.exp (-((modeRate c h : ℝ) : ℂ) * (P t - P s))) (Icc t₀ t) := by
      intro s hs
      have hsplit : ∫ u in s..t, a u = P t - P s :=
        (intervalIntegral.integral_interval_sub_left (hai t₀ t ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩)
          (hai t₀ s ⟨le_rfl, ht⟩ hs)).symm
      simp only [modeKC, hsplit]
    refine ContinuousOn.congr ?_ e
    exact (continuousOn_const.mul (continuousOn_const.sub hPc)).cexp
  exact hF.continuousOn_mul hK

/-- **Two metrics in the complex transverse inverse.** -/
theorem norm_modeWC_sub_le {c : ℝ} (hc : 0 < c) {a a' : ℝ → ℂ} {a₀ δ : ℝ} (ha₀ : 0 < a₀)
    {F : ℝ → ℂ} {M : ℝ} {h : ℤ} (hh : h ≠ 0) {t₀ t : ℝ} (ht : t₀ ≤ t)
    (hai : IntervalIntegrable a volume t₀ t) (hai' : IntervalIntegrable a' volume t₀ t)
    (hFi : IntervalIntegrable F volume t₀ t)
    (hre : ∀ u ∈ Icc t₀ t, a₀ ≤ (a u).re) (hre' : ∀ u ∈ Icc t₀ t, a₀ ≤ (a' u).re)
    (hδ : ∀ u ∈ Icc t₀ t, ‖a u - a' u‖ ≤ δ) (hM : ∀ s ∈ Icc t₀ t, ‖F s‖ ≤ M) :
    ‖modeWC c a F t₀ h t - modeWC c a' F t₀ h t‖ ≤ δ * M / (2 * Real.pi * |(h : ℝ)| * a₀ ^ 2) := by
  have hr : 0 < modeRate c h := by
    unfold modeRate
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, ht⟩)
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ t₀ ⟨le_rfl, ht⟩)
  have hcoup : ‖modeCoup c h‖ = 2 * Real.pi * |(h : ℝ)| / c := by
    unfold modeCoup
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hc]
    norm_num
  set k := modeRate c h * a₀ with hk
  have hk0 : 0 < k := mul_pos hr ha₀
  have hK : ∀ s ∈ Ioc t₀ t, ‖(modeKC c a h t s - modeKC c a' h t s) * F s‖ ≤
      (modeRate c h * δ * M) * ((t - s) * Real.exp (-(k * (t - s)))) := by
    intro s hs
    have hsub : uIcc s t ⊆ uIcc t₀ t := by
      rw [uIcc_of_le hs.2, uIcc_of_le ht]; exact Icc_subset_Icc hs.1.le le_rfl
    have hIcc : ∀ u ∈ Icc s t, u ∈ Icc t₀ t := fun u hu => ⟨hs.1.le.trans hu.1, hu.2⟩
    rw [norm_mul]
    have h1 := norm_modeKC_sub_le hc h hs.2 (hai.mono_set hsub) (hai'.mono_set hsub)
      (fun u hu => hre u (hIcc u hu)) (fun u hu => hre' u (hIcc u hu))
      (fun u hu => hδ u (hIcc u hu)) (a₀ := a₀) (δ := δ)
    have h2 := hM s ⟨hs.1.le, hs.2⟩
    have hts : 0 ≤ t - s := by linarith [hs.2]
    calc ‖modeKC c a h t s - modeKC c a' h t s‖ * ‖F s‖
        ≤ (Real.exp (-(modeRate c h * a₀ * (t - s))) * (modeRate c h * (δ * (t - s)))) * M :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (modeRate c h * δ * M) * ((t - s) * Real.exp (-(k * (t - s)))) := by
          rw [hk]; ring_nf
  have hint : ‖∫ s in t₀..t, (modeKC c a h t s - modeKC c a' h t s) * F s‖ ≤
      ∫ s in t₀..t, (modeRate c h * δ * M) * ((t - s) * Real.exp (-(k * (t - s)))) :=
    intervalIntegral.norm_integral_le_of_norm_le ht (Filter.Eventually.of_forall hK)
      ((by fun_prop : Continuous fun s =>
        (modeRate c h * δ * M) * ((t - s) * Real.exp (-(k * (t - s))))).intervalIntegrable _ _)
  have hbd : ∫ s in t₀..t, (modeRate c h * δ * M) * ((t - s) * Real.exp (-(k * (t - s)))) ≤
      modeRate c h * δ * M * (1 / k ^ 2) := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_mul_exp_decay_le hk0 ht) (by positivity)
  have hdiff : modeWC c a F t₀ h t - modeWC c a' F t₀ h t =
      modeCoup c h * ∫ s in t₀..t, (modeKC c a h t s - modeKC c a' h t s) * F s := by
    unfold modeWC
    rw [← mul_sub, ← intervalIntegral.integral_sub
      (intervalIntegrable_modeKC_mul ht hai hFi h) (intervalIntegrable_modeKC_mul ht hai' hFi h)]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  rw [hdiff, norm_mul, hcoup]
  calc 2 * Real.pi * |(h : ℝ)| / c * ‖∫ s in t₀..t, (modeKC c a h t s - modeKC c a' h t s) * F s‖
      ≤ 2 * Real.pi * |(h : ℝ)| / c * (modeRate c h * δ * M * (1 / k ^ 2)) :=
        mul_le_mul_of_nonneg_left (hint.trans hbd) (by positivity)
    _ = δ * M / (2 * Real.pi * |(h : ℝ)| * a₀ ^ 2) := by
        rw [hk]
        unfold modeRate
        have hh' : |(h : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hh)
        have hsq : (h : ℝ) ^ 2 = |(h : ℝ)| ^ 2 := (sq_abs _).symm
        rw [hsq]
        field_simp
        ring

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the quadratic bridge in the charts of the appended children.** The
bridge arrays `K_2 − 𝖩_m∇` of the first source (`dmArr … 2 − matGradArr 𝖩_m`) are, at a time of the
slot window, the cutoff-weighted sum over the scheduled finer slots of the chart arrays of the
label tensor `Ŝ = K^lab_2 − DΨ⁻¹𝖩_m DΨ⁻ᵀ` of each appended child (`bridgeArr_eq`). This puts the
reference tensor inside each child, where it cancels the flat part of the grade-zero mean:
* `fdbArr_one_one`, `fdbArr_one_ne`: the Faà di Bruno array of one derivative;
* `chartArr_matGradArr_labJ`: a constant Eulerian tensor `𝖩`, written in the labels as
  `DΨ⁻¹𝖩DΨ⁻ᵀ` and pushed back, is `𝖩` again;
* `chartArr_sub`: the chart arrays are linear in the input arrays;
* the cutoff weights of the scheduled finer slots add up to one on the slot window
  (`sum_ocCutoff_eq_one`). -/

open AVRegularity.Providers.GenSem

/-- The label tensor `DΨ⁻¹ J DΨ⁻ᵀ` of a constant Eulerian tensor `J` in the chart `Ψ`. -/
def labJ (Ψ : Vec 2 → Vec 2) (J : Matrix (Fin 2) (Fin 2) ℝ) (y : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (jacMatrix Ψ y)⁻¹ * J * ((jacMatrix Ψ y)⁻¹).transpose

/-! ### Faà di Bruno arrays of one derivative -/

theorem slowPartial_unitArr (i : Fin 2) (m : ℕ) (β : DerivativeWord2 m) (w z : Vec 2) :
    slowPartial i (unitArr m β) w z = 0 := by
  unfold slowPartial
  cases m with
  | zero => simp [unitArr]
  | succ m => simp [unitArr]

theorem fdbArr_one_one (Ψ : Vec 2 → Vec 2) (α γ : DerivativeWord2 1) (w z : Vec 2) :
    fdbArr Ψ α 1 γ w z = jacMatrix Ψ w (γ 0) (α 0) := by
  simp only [fdbArr, fdbIter, fdbStep, fdbExtra, slowPartial_unitArr, zero_add, jacMatrix,
    Matrix.of_apply]
  simp [unitArr, Fin.last]

theorem fdbArr_one_ne (Ψ : Vec 2 → Vec 2) (α : DerivativeWord2 1) {m : ℕ} (hm : m ≠ 1)
    (γ : DerivativeWord2 m) (w z : Vec 2) : fdbArr Ψ α m γ w z = 0 := by
  simp only [fdbArr, fdbIter, fdbStep, slowPartial_unitArr, zero_add]
  match m, hm with
  | 0, _ => simp [fdbExtra]
  | m + 2, _ => simp [fdbExtra, unitArr]

/-! ### Linearity and the constant tensor -/

theorem chartArr_sub (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (N Ψ : Vec 2 → Vec 2) (K : ℕ)
    (A B : Fin 2 → CArr) (c : Fin 2) :
    chartArr M N Ψ K (fun k => A k - B k) c = chartArr M N Ψ K A c - chartArr M N Ψ K B c := by
  funext m' γ p z
  simp only [chartArr, chartCoef, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem sum_word_one (f : Fin 2 → ℝ) : ∑ α : DerivativeWord2 1, f (α 0) = ∑ a : Fin 2, f a :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) _ _ fun _ => rfl

/-- **A constant tensor written in the labels and pushed back by the chart.** -/
theorem chartArr_matGradArr_labJ (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (N Ψ : Vec 2 → Vec 2)
    {K : ℕ} (hK : 1 ≤ K) (J : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ p, M p = jacMatrix Ψ (N p))
    (hdet : ∀ y, IsUnit (jacMatrix Ψ y).det) (c : Fin 2) :
    chartArr M N Ψ K (fun k => matGradArr (labJ Ψ J) k) c = matGradArr (fun _ => J) c := by
  funext m' γ p z
  simp only [chartArr, chartCoef]
  -- only the inputs of order one contribute
  have hone : ∀ k, ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m,
      matGradArr (labJ Ψ J) k m α (N p) 0 * fdbArr Ψ α m' γ (N p) 0 =
      ∑ α : DerivativeWord2 1, labJ Ψ J (N p) k (α 0) * fdbArr Ψ α m' γ (N p) 0 := by
    intro k
    rw [Finset.sum_eq_single 1]
    · rfl
    · intro m _ hm1
      refine Finset.sum_eq_zero fun α _ => ?_
      match m, hm1 with
      | 0, _ => simp [matGradArr]
      | m + 2, _ => simp [matGradArr]
    · intro h1
      exact absurd (Finset.mem_range.mpr (by omega)) h1
  simp only [hone]
  match m', γ with
  | 0, γ =>
    simp only [fdbArr_one_ne Ψ _ (by omega : (0 : ℕ) ≠ 1), mul_zero, Finset.sum_const_zero]
    simp [matGradArr]
  | m' + 2, γ =>
    simp only [fdbArr_one_ne Ψ _ (by omega : m' + 2 ≠ 1), mul_zero, Finset.sum_const_zero]
    simp [matGradArr]
  | 1, γ =>
    simp only [fdbArr_one_one]
    have hsum : ∀ k, ∑ α : DerivativeWord2 1, labJ Ψ J (N p) k (α 0) *
        jacMatrix Ψ (N p) (γ 0) (α 0) =
        (labJ Ψ J (N p) * (jacMatrix Ψ (N p)).transpose) k (γ 0) := by
      intro k
      rw [sum_word_one (fun a => labJ Ψ J (N p) k a * jacMatrix Ψ (N p) (γ 0) a)]
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [hsum, hM p]
    have hmat : jacMatrix Ψ (N p) * (labJ Ψ J (N p) * (jacMatrix Ψ (N p)).transpose) = J := by
      have hu := hdet (N p)
      unfold labJ
      rw [Matrix.transpose_nonsing_inv]
      have h1 : jacMatrix Ψ (N p) * (jacMatrix Ψ (N p))⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
      have h2 : ((jacMatrix Ψ (N p)).transpose)⁻¹ * (jacMatrix Ψ (N p)).transpose = 1 :=
        Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hu)
      calc jacMatrix Ψ (N p) * ((jacMatrix Ψ (N p))⁻¹ * J * ((jacMatrix Ψ (N p)).transpose)⁻¹ *
            (jacMatrix Ψ (N p)).transpose)
          = (jacMatrix Ψ (N p) * (jacMatrix Ψ (N p))⁻¹) * J *
              (((jacMatrix Ψ (N p)).transpose)⁻¹ * (jacMatrix Ψ (N p)).transpose) := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    have e : ∑ k : Fin 2, jacMatrix Ψ (N p) c k *
        (labJ Ψ J (N p) * (jacMatrix Ψ (N p)).transpose) k (γ 0) = J c (γ 0) := by
      rw [← Matrix.mul_apply, hmat]
    rw [e]
    rfl

/-! ### The bridge arrays -/

variable {D : OCData} {b : ℝ} {j₀ Dm m : ℕ} {ρ : ℝ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- The reference tensor `𝖩_m(t)` at the level `m`. -/
abbrev refJ (D : OCData) (m : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t

/-- The label arrays `Ŝ = K^lab_2 − DΨ⁻¹𝖩_mDΨ⁻ᵀ` of the child `B` appended for the finer slot `k`. -/
def bridgeLab (D : OCData) (Dm m : ℕ) (ρ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (k : ℤ) (t : ℝ)
    (B : RealChain) (κ : Fin 2) : CArr :=
  pmArr D m ρ (diagQ D Dm m k B ρ) (Cc0 k B) 2 t κ - matGradArr (labJ (B.famMap D t) (refJ D m t)) κ

/-- The chart arrays of the label arrays `Ŝ` of the appended child `B`. -/
def bridgeChild (D : OCData) (Dm m : ℕ) (ρ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (k : ℤ) (t : ℝ)
    (B : RealChain) (c : Fin 2) : CArr :=
  chartArr (fun x => jacMatrix (B.famMap D t) (B.famMapInv D t x)) (B.famMapInv D t)
    (B.famMap D t) 2 (bridgeLab D Dm m ρ Cc0 k t B) c

/-- **The bridge arrays are the cutoff-weighted chart arrays of the appended children.** -/
theorem bridgeArr_eq (hζ : IsFastProfile D.ζ) (hτ : 0 < ocTau D.α D.q D.Λ m) (S : Finset ℤ)
    (hS : ∀ k ∈ S, Odd k) (t : ℝ) (ch : RealChain) (ζ : Vec 2)
    (hact : ∀ k : ℤ, Odd k → ocCutoff D.α D.q D.Λ m k t ≠ 0 → k ∈ S)
    (hadm : ∀ k ∈ S, ocCutoff D.α D.q D.Λ m k t ≠ 0 →
      IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ)) (c : Fin 2) :
    dmArr D b j₀ Dm m ρ Cc0 S t ch ζ 2 c - matGradArr (fun _ => refJ D m t) c =
      ∑ k ∈ S, ocCutoff D.α D.q D.Λ m k t •
        bridgeChild D Dm m ρ Cc0 k t (ch.appendChild D k t ζ) c := by
  classical
  have hsum := sum_ocCutoff_eq_one hτ S hS t hact
  have hterm : ∀ k ∈ S, (if IsAdmissibleChain D b j₀ m k (ch.appendChild D k t ζ) then
      ocCutoff D.α D.q D.Λ m k t • diagChildArr D Dm m ρ Cc0 k 2 t (ch.appendChild D k t ζ) c
      else 0) = ocCutoff D.α D.q D.Λ m k t •
        (bridgeChild D Dm m ρ Cc0 k t (ch.appendChild D k t ζ) c +
          matGradArr (fun _ => refJ D m t) c) := by
    intro k hk
    by_cases h0 : ocCutoff D.α D.q D.Λ m k t = 0
    · simp [h0]
    have hA := hadm k hk h0
    simp only [hA, ↓reduceIte]
    congr 1
    set B := ch.appendChild D k t ζ with hB
    have hdet : ∀ y, IsUnit (jacMatrix (B.famMap D t) y).det := fun y => by
      rw [jacMatrix_famMap hζ B hA.2.2.1 t y]
      exact famJac_isUnit D hζ _ t
    unfold bridgeChild bridgeLab diagChildArr covB1
    rw [chartArr_sub, chartArr_matGradArr_labJ _ _ _ (by norm_num) _ (fun _ => rfl) hdet]
    abel
  unfold dmArr
  rw [Finset.sum_congr rfl hterm]
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, one_smul]
  abel

end AVRegularity.Providers.CascadeInvariants
end

section
open MeasureTheory Set Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the degree-two label mean of the grade-zero lift.** On the grade-zero
lift setup of the appended children (`diagLiftGenSetup`), the label array `pmArr … 2` of the
quadratic mean is explicit:
* the first corrector `C_{0,1,1}` in the direction `j` is the transverse inverse, from zero at the
  slot start and with the molecular metric of the recentered family, of the transverse primitive of
  the source `−√η v_j` (`cc011_eq`, from `coeff_eq_cellInv`);
* the entries of order one are `−κ_{m−1}(⟨√η v_κ χ_j⟩ − η 𝒢_{κj})` at the recentered family
  (`pmArr_two_one`, the tensor `kLab`), and those of order zero vanish (`pmArr_two_zero`).
The fast flux `√η 𝒢∇_zχ` has zero cell mean, and `c₀ρ = −d_*²/ℓ² = −κ_{m−1}`. -/

open AVRegularity.Providers.GenSem

/-! ### The explicit first corrector and the label tensor -/

/-- The source `−√η v_j` of the first corrector in the direction `j`. -/
def srcSem (D : OCData) (m : ℕ) (k : ℤ) (j : Fin 2) : GenSort.Sem .cell :=
  fun t ch η => -driftSem D m k j t ch η

/-- The flux of the first corrector: the transverse primitive of the source. -/
def chiFlux (D : OCData) (m : ℕ) (k : ℤ) (j : Fin 2) : Fin 2 → GenSort.Sem .cell :=
  fun c => if c = transverseIndex k then transversePrimitiveSem k (srcSem D m k j)
    else GenSort.ofTime .cell (TimeLetter.eval D (.const 0))

/-- The first corrector in the direction `j`, from zero at the start of the slot `k`. -/
def chiSem (D : OCData) (m : ℕ) (k : ℤ) (j : Fin 2) : GenSort.Sem .cell :=
  transverseInverseSem D m k (chiFlux D m k j) (D.slotStart m k)
    (GenSort.ofTime .cell (TimeLetter.eval D (.const 0)))

/-- The degree-two label mean tensor `−κ_{m−1}(⟨√η v_κ χ_j⟩ − η 𝒢_{κj})` at a family. -/
def kLab (D : OCData) (m : ℕ) (k : ℤ) (κ j : Fin 2) : GenSort.Sem .fam :=
  fun t A => -D.kap (m - 1) *
    (cellMeanSem (fun t ch η => driftSem D m k κ t ch η * chiSem D m k j t ch η) t A -
      D.kap m / D.kap (m - 1) * A.famMetric D t κ j)

/-! ### The grade-zero lift setup -/

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {Dm m : ℕ} {k : ℤ}
  {𝒜 : Set RealChain} {ρ : ℝ} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N : ℕ}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- The grade-zero lift setup of the first source (no edge, all slow offsets). -/
abbrev DiagSetup (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (Dm m : ℕ) (k : ℤ)
    (𝒜 : Set RealChain) (ρ : ℝ) (sX sZ : ℕ) (t₀ t₁ : ℝ) (N : ℕ)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) : Prop :=
  LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ (fun _ => (fun _ _ _ => [] : ConstituentEdges Dm (fun _ : Fin 1 => ℝ)))
    (fun _ => Set.univ) sX sZ t₀ t₁ N 0 Cc

/-- The coefficient of order zero of the identity lift is one. -/
theorem cc000_eq_one (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc) {A : RealChain}
    (hA : A ∈ 𝒜) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) (X z : Vec 2) (α : DerivativeWord2 0) :
    Cc A 0 0 0 α τ X z 0 0 1 = 1 := by
  have h := (hS.loc A hA).init (fun _ _ => 1) contDiff_const τ hτ X (Set.mem_univ _) z
  have h0 := congrFun h 0
  simp only [liftApply, zero_add, Finset.sum_range_one] at h0
  rw [Fintype.sum_eq_single α (fun β hβ => absurd (Subsingleton.elim β α) hβ),
    Fintype.sum_eq_single (0 : Fin 1) (fun u hu => absurd (Subsingleton.elim u 0) hu)] at h0
  have hod : AVRegularity.orderedDerivative α (fun (_ : Vec 2) (_ : Fin 1) => (1 : ℝ)) X 0 = 1 := by
    simp [AVRegularity.orderedDerivative, List.ofFn_zero]
  rw [hod] at h0
  exact h0

theorem slowPartial_const_fun (j : Fin 2) (c : ℝ) (X z : Vec 2) :
    slowPartial j (fun _ _ => c) X z = 0 := by
  simp [slowPartial]

theorem fastPartial_const_fun (j : Fin 2) (c : ℝ) (X z : Vec 2) :
    fastPartial j (fun _ _ => c) X z = 0 := by
  simp [fastPartial]

/-- The slow array of the identity entry of order zero at a word of length one. -/
theorem slowArr_entry_one (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc)
    {A : RealChain} (hA : A ∈ 𝒜) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) (α : DerivativeWord2 1)
    (j : Fin 2) : slowArr j (entryArr (Cc A 0 0) 0 0 τ 0) 1 α = fun _ _ =>
      if α 0 = j then 1 else 0 := by
  funext X z
  have h1 : entryArr (Cc A 0 0) 0 0 τ 0 1 α = fun _ _ => 0 := by
    funext X' z'; simp [entryArr]
  simp only [slowArr, slowExtra, h1, slowPartial_const_fun, zero_add]
  have : α (Fin.last 0) = α 0 := rfl
  rw [this]
  split_ifs
  · simp only [entryArr, le_refl, ↓reduceIte]
    exact cc000_eq_one hS hA hτ X z _
  · rfl

theorem fastArr_slowArr_entry_one (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc)
    {A : RealChain} (hA : A ∈ 𝒜) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) (α : DerivativeWord2 1)
    (i j : Fin 2) (X z : Vec 2) :
    fastArr i (slowArr j (entryArr (Cc A 0 0) 0 0 τ 0)) 1 α X z = 0 := by
  simp only [fastArr, slowArr_entry_one hS hA hτ α j]
  exact fastPartial_const_fun i _ X z

theorem slowArr_mul_fast_entry_one (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc)
    {A : RealChain} (hA : A ∈ 𝒜) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) (α : DerivativeWord2 1)
    (g : Vec 2 → Vec 2 → ℝ) (i j : Fin 2) (X z : Vec 2) :
    slowArr i (mulArr g (fastArr j (entryArr (Cc A 0 0) 0 0 τ 0))) 1 α X z = 0 := by
  have h1 : mulArr g (fastArr j (entryArr (Cc A 0 0) 0 0 τ 0)) 1 α = fun _ _ => 0 := by
    funext X' z'
    have e : entryArr (Cc A 0 0) 0 0 τ 0 1 α = fun _ _ => 0 := by
      funext X'' z''; simp [entryArr]
    simp only [mulArr, fastArr, e, fastPartial_const_fun, mul_zero]
  have h0 : entryArr (Cc A 0 0) 0 0 τ 0 0 (Fin.init α) = fun _ _ => 1 := by
    funext X' z'
    simp only [entryArr, le_refl, ↓reduceIte]
    exact cc000_eq_one hS hA hτ X' z' _
  simp only [slowArr, slowExtra, h1, slowPartial_const_fun, zero_add, mulArr, fastArr, h0,
    fastPartial_const_fun, mul_zero, ite_self]

/-- **The normalised source of the first corrector** is `−√η v_j`. -/
theorem srcArr_one (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc) (hk : Odd k)
    (hΛ : 1 ≤ D.Λ) (hκ : ∀ i, 0 < D.kap i) {A : RealChain} (hA : A ∈ 𝒜) {τ : ℝ}
    (hτ : τ ∈ Icc t₀ t₁) (α : DerivativeWord2 1) (X z : Vec 2) :
    srcArr (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ (fun _ _ _ => []))
        (Cc A) 0 0 1 τ 0 1 α X z =
      srcSem D m k (α 0) (D.cellScaleSq m * τ) (A.recenter D (ρ • X)) z := by
  set Q := familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ (fun _ _ _ => [])
    with hQ
  have hA1 : ∀ X' z', liftAArr Q (Cc A) 0 0 1 τ 0 1 α X' z' =
      Real.sqrt Q.η * Q.v τ z' (α 0) := by
    intro X' z'
    simp only [liftAArr, cellB1Arr, show (1 : ℕ) - 1 = 0 from rfl, show ¬ (2 ≤ 1) by omega,
      ↓reduceIte, sub_zero, add_zero, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    simp only [mulArr, slowArr_entry_one hS hA hτ α, fastArr_slowArr_entry_one hS hA hτ α,
      slowArr_mul_fast_entry_one hS hA hτ α, mul_zero, add_zero, Finset.sum_const_zero,
      mul_ite, mul_one]
    rw [Finset.sum_ite_eq]
    simp
  have hmean : meanArr (liftAArr Q (Cc A) 0 0 1 τ 0) 1 α X z = 0 := by
    simp only [meanArr, hA1, fieldCellMean]
    rw [integral_const_mul]
    simp only [hQ, familyLiftData]
    rw [EntryWeakProofs.normalizedPulseDrift_mean_zero hΛ (hκ m) hk τ (α 0), mul_zero]
  have hc : D.cellScaleSq m ≠ 0 := by
    unfold OCData.cellScaleSq
    exact div_ne_zero (pow_ne_zero 2 (Construction.Stream.ocEpsilon_pos hΛ).ne') (hκ m).ne'
  simp only [srcArr, Pi.add_apply, Pi.neg_apply, Pi.sub_apply,
    show Finset.Icc 1 (1 - 2) = ∅ from rfl, Finset.sum_empty]
  rw [hA1 X z, hmean, sub_zero]
  simp only [Pi.zero_apply, add_zero]
  simp only [srcSem, driftSem, hQ, familyLiftData]
  rw [mul_div_cancel_left₀ τ hc]

/-- **The first corrector** in the direction `α 0`. -/
theorem cc011_eq (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc) (hk : Odd k)
    (hΛ : 1 ≤ D.Λ) (hκ : ∀ i, 0 < D.kap i) (hN : 1 ≤ N) {A : RealChain} (hA : A ∈ 𝒜)
    (α : DerivativeWord2 1) (X : Vec 2) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) (z : Vec 2) :
    Cc A 0 1 1 α τ X z 0 0 1 =
      chiSem D m k (α 0) (D.cellScaleSq m * τ) (A.recenter D (ρ • X)) z := by
  refine hS.coeff_eq_cellInv hA le_rfl le_rfl hN le_rfl α 0 0 (Set.mem_univ X)
    (f := srcSem D m k (α 0)) (fun τ' hτ' z' => ?_) (fun τ' _ z' s => ?_) τ hτ z
  · have hreg := hS.reg A hA 0 le_rfl 1 le_rfl hN τ' hτ' 0
    rw [liftCellSource_monoField _ (Cc A) 0 hreg X z' 0 α (by omega)]
    have hu : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by
      ext σ; simp [Subsingleton.elim σ 1]
    rw [hu, Finset.sum_singleton]
    simp only [Equiv.Perm.coe_one, Function.comp_id, Nat.factorial_one, Nat.cast_one, inv_one,
      one_mul]
    exact srcArr_one hS hk hΛ hκ hA hτ' α X z'
  · simp only [srcSem, driftSem]
    rw [ocPulseCellDrift_par m (D.kap m) hk]

/-- The transverse inverse is periodic in the internal phase. -/
theorem transverseInverseSem_periodic (D : OCData) (i : ℕ) (p : ℤ) (F : Fin 2 → GenSort.Sem .cell)
    (t₀ : ℝ) (ι : GenSort.Sem .cell) (t : ℝ) (ch : RealChain) :
    AVenhance.IsZ2Periodic (transverseInverseSem D i p F t₀ ι t ch) := by
  intro n x
  unfold transverseInverseSem
  congr 1
  refine tsum_congr fun h => ?_
  congr 1
  have e : (((x + AVenhance.latticeShift n) (transverseIndex p) : ℝ) : ℂ) =
      ((x (transverseIndex p) : ℝ) : ℂ) + ((n (transverseIndex p) : ℤ) : ℂ) := by
    simp [AVenhance.latticeShift]
  rw [e, mul_add, Complex.exp_add]
  have h1 : Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((n (transverseIndex p) : ℤ) : ℂ)) =
      1 := Complex.exp_eq_one_iff.mpr ⟨h * n (transverseIndex p), by push_cast; ring⟩
  rw [h1, mul_one]

/-- **The entries of order one of the degree-two label mean** are the tensor `kLab` at the
recentered family. -/
theorem pmArr_two_one (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc) (hk : Odd k)
    (hΛ : 1 ≤ D.Λ) (hκ : ∀ i, 0 < D.kap i) (hN : 1 ≤ N) {A : RealChain} (hA : A ∈ 𝒜)
    (hρ : ρ ≠ 0)
    (hDst : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = D.kap (m - 1) * D.cellScaleSq m)
    {t : ℝ} (ht : (D.cellScaleSq m)⁻¹ * t ∈ Icc t₀ t₁) (κ : Fin 2) (α : DerivativeWord2 1)
    (y : Vec 2) :
    pmArr D m ρ (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ (fun _ _ _ => []))
        (Cc A) 2 t κ 1 α y 0 = kLab D m k κ (α 0) t (A.recenter D y) := by
  set τ := (D.cellScaleSq m)⁻¹ * t with hτdef
  set X := ρ⁻¹ • y with hXdef
  have hc : D.cellScaleSq m ≠ 0 := by
    unfold OCData.cellScaleSq
    exact div_ne_zero (pow_ne_zero 2 (Construction.Stream.ocEpsilon_pos hΛ).ne') (hκ m).ne'
  have hτt : D.cellScaleSq m * τ = t := by rw [hτdef, mul_inv_cancel_left₀ hc]
  have hXy : ρ • X = y := by rw [hXdef, smul_inv_smul₀ hρ]
  set f : Vec 2 → ℝ := fun z => Cc A 0 1 1 α τ X z 0 0 1 with hf
  have hχ : ∀ z, f z = chiSem D m k (α 0) t (A.recenter D y) z := fun z => by
    show Cc A 0 1 1 α τ X z 0 0 1 = _
    rw [cc011_eq hS hk hΛ hκ hN hA α X ht z, hτt, hXy]
  have hreg := (hS.reg A hA 0 le_rfl 1 le_rfl hN τ ht 0).coeff 0 le_rfl 1 le_rfl 1 α 0
  have hf1 : ContDiff ℝ 1 f := by
    have := hreg.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ (1 + Dm + 2 : ℕ)
      (fun z : Vec 2 => (X, z)))
    exact this.of_le (by exact_mod_cast (by omega : 1 ≤ 1 + Dm + 2))
  have hper : AVenhance.IsZ2Periodic f := by
    have e : f = chiSem D m k (α 0) t (A.recenter D y) := funext hχ
    rw [e]
    exact transverseInverseSem_periodic _ _ _ _ _ _ _ _
  have hfc : Continuous fun z => fderiv ℝ f z := hf1.continuous_fderiv one_ne_zero
  set η := D.kap m / D.kap (m - 1) with hη
  set G : Fin 2 → ℝ := fun j => (A.recenter D (ρ • X)).famMetric D (D.cellScaleSq m * τ) κ j
    with hG
  set v : Vec 2 → ℝ := fun z => ocPulseCellDrift D.α D.q D.Λ D.ζ m (D.kap m) k τ z κ with hvd
  have hv : Continuous v := by
    have := (hS.reg A hA 0 le_rfl 1 le_rfl hN τ ht 0).drift κ
    exact (this.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ (1 + Dm + 2 : ℕ)
      (fun z : Vec 2 => (X, z)))).continuous
  -- the slow flux at the order one, pointwise
  have hflux : ∀ z, fluxXArr (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ
      (fun _ _ _ => [])) (Cc A) 0 0 2 τ (Fin.last 0) κ 1 α X z =
      Real.sqrt η * v z * f z - Real.sqrt η * ∑ j : Fin 2, G j * fderiv ℝ f z (basisVec j) -
        η * G (α 0) := by
    intro z
    simp only [fluxXArr, fluxXA, fluxXB, fluxXC, fluxXD, ↓reduceIte, show (2 : ℕ) - 1 = 1 from rfl,
      show (2 : ℕ) - 2 = 0 from rfl, le_refl, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, Pi.zero_apply, Finset.sum_apply, smul_eq_mul, mulArr, sub_zero, Fin.last_zero]
    simp only [entryArr, le_refl, ↓reduceIte, fastArr, fastPartial, slowArr_entry_one hS hA ht α,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
    simp only [hf, hG, hvd, hη, familyLiftData]
    ring
  have hcB : ∀ j, Continuous fun z => G j * fderiv ℝ f z (basisVec j) := fun j =>
    continuous_const.mul (hfc.clm_apply continuous_const)
  have hmeanB : ∫ z in AVenhance.unitCube, ∑ j : Fin 2, G j * fderiv ℝ f z (basisVec j) = 0 := by
    rw [integral_finsetSum _ fun j _ => integrableOn_unitCube_of_continuous (hcB j)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul]
    have := fieldCellMean_fastPartial_eq_zero f hf1 hper j
    simp only [fieldCellMean] at this
    rw [this, mul_zero]
  have hA1 : Continuous fun z => Real.sqrt η * v z * f z :=
    (continuous_const.mul hv).mul hf1.continuous
  have hB1 : Continuous fun z => Real.sqrt η * ∑ j : Fin 2, G j * fderiv ℝ f z (basisVec j) :=
    continuous_const.mul (continuous_finsetSum _ fun j _ => hcB j)
  have hAB : Continuous fun z => Real.sqrt η * v z * f z -
      Real.sqrt η * ∑ j : Fin 2, G j * fderiv ℝ f z (basisVec j) := hA1.sub hB1
  unfold pmArr
  simp only [pow_one, fieldCellMean]
  rw [show (fun z => fluxXArr (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ
      (fun _ _ _ => [])) (Cc A) 0 0 2 ((D.cellScaleSq m)⁻¹ * t) (Fin.last 0) κ 1 α (ρ⁻¹ • y) z)
      = fun z => fluxXArr (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ
      (fun _ _ _ => [])) (Cc A) 0 0 2 τ (Fin.last 0) κ 1 α X z from rfl]
  simp only [hflux]
  have hint : ∫ z in AVenhance.unitCube, (Real.sqrt η * v z * f z -
      Real.sqrt η * ∑ j : Fin 2, G j * fderiv ℝ f z (basisVec j) - η * G (α 0)) =
      (∫ z in AVenhance.unitCube, Real.sqrt η * v z * f z) - η * G (α 0) := by
    rw [integral_sub (integrableOn_unitCube_of_continuous hAB)
      (integrableOn_unitCube_of_continuous continuous_const),
      integral_sub (integrableOn_unitCube_of_continuous hA1)
      (integrableOn_unitCube_of_continuous hB1), integral_const_mul, hmeanB, mul_zero, sub_zero]
    have h2 := fieldCellMean_const (η * G (α 0))
    simp only [fieldCellMean] at h2
    rw [h2]
  rw [hint]
  have hdrift : ∀ z, Real.sqrt η * v z * f z =
      driftSem D m k κ t (A.recenter D y) z * chiSem D m k (α 0) t (A.recenter D y) z := by
    intro z
    rw [hχ z]
    simp only [hvd, hη, driftSem]
    rw [← hτt, mul_div_cancel_left₀ τ hc]
  have hGe : G (α 0) = (A.recenter D y).famMetric D t κ (α 0) := by
    simp only [hG]
    rw [hXy, hτt]
  simp only [hdrift, hGe]
  unfold kLab cellMeanSem
  have hc0 : -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ 2 * ρ) *
      ρ = -D.kap (m - 1) := by
    rw [div_pow, hDst]
    field_simp
  rw [hc0]

theorem slowArr_entry_zero (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc)
    {A : RealChain} (hA : A ∈ 𝒜) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) (α : DerivativeWord2 0)
    (j : Fin 2) : slowArr j (entryArr (Cc A 0 0) 0 0 τ 0) 0 α = fun _ _ => 0 := by
  have hB : entryArr (Cc A 0 0) 0 0 τ 0 0 α = fun _ _ => 1 := by
    funext X' z'
    simp only [entryArr, le_refl, ↓reduceIte]
    exact cc000_eq_one hS hA hτ X' z' _
  funext X' z'
  simp only [slowArr, slowExtra, hB, slowPartial_const_fun, add_zero]

theorem fastArr_entry_zero (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc)
    {A : RealChain} (hA : A ∈ 𝒜) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) (α : DerivativeWord2 0)
    (j : Fin 2) : fastArr j (entryArr (Cc A 0 0) 0 0 τ 0) 0 α = fun _ _ => 0 := by
  have hB : entryArr (Cc A 0 0) 0 0 τ 0 0 α = fun _ _ => 1 := by
    funext X' z'
    simp only [entryArr, le_refl, ↓reduceIte]
    exact cc000_eq_one hS hA hτ X' z' _
  funext X' z'
  simp only [fastArr, hB, fastPartial_const_fun]

/-- The source of the coefficient of order zero of the first corrector vanishes. -/
theorem srcArr_zero (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc) {A : RealChain}
    (hA : A ∈ 𝒜) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) (α : DerivativeWord2 0) (X z : Vec 2) :
    srcArr (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ (fun _ _ _ => []))
        (Cc A) 0 0 1 τ 0 0 α X z = 0 := by
  have hfs : ∀ i j X' z', fastArr i (slowArr j (entryArr (Cc A 0 0) 0 0 τ 0)) 0 α X' z' = 0 := by
    intro i j X' z'
    simp only [fastArr, slowArr_entry_zero hS hA hτ α j, fastPartial_const_fun]
  have hsm : ∀ (g : Vec 2 → Vec 2 → ℝ) i j X' z',
      slowArr i (mulArr g (fastArr j (entryArr (Cc A 0 0) 0 0 τ 0))) 0 α X' z' = 0 := by
    intro g i j X' z'
    have e : mulArr g (fastArr j (entryArr (Cc A 0 0) 0 0 τ 0)) 0 α = fun _ _ => 0 := by
      funext X'' z''
      simp only [mulArr, fastArr_entry_zero hS hA hτ α j, mul_zero]
    simp only [slowArr, slowExtra, e, slowPartial_const_fun, add_zero]
  have hA0 : ∀ X' z', liftAArr (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ
      (fun _ _ _ => [])) (Cc A) 0 0 1 τ 0 0 α X' z' = 0 := by
    intro X' z'
    simp only [liftAArr, cellB1Arr, show (1 : ℕ) - 1 = 0 from rfl, show ¬ (2 ≤ 1) by omega,
      ↓reduceIte, sub_zero, add_zero, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul]
    simp only [mulArr, slowArr_entry_zero hS hA hτ α, hfs, hsm, mul_zero, add_zero,
      Finset.sum_const_zero]
  simp only [srcArr, Pi.add_apply, Pi.neg_apply, Pi.sub_apply,
    show Finset.Icc 1 (1 - 2) = ∅ from rfl, Finset.sum_empty, meanArr, hA0, Pi.zero_apply]
  simp [fieldCellMean]

/-- The coefficient of order zero of the first corrector vanishes. -/
theorem cc010_eq_zero (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc) (hN : 1 ≤ N)
    {A : RealChain} (hA : A ∈ 𝒜) (α : DerivativeWord2 0) (X : Vec 2) {τ : ℝ}
    (hτ : τ ∈ Icc t₀ t₁) (z : Vec 2) : Cc A 0 1 0 α τ X z 0 0 1 = 0 := by
  rw [hS.coeff_eq_cellInv hA le_rfl le_rfl hN (by omega : 0 ≤ 1) α 0 0 (Set.mem_univ X)
    (f := fun _ _ _ => 0) (fun τ' hτ' z' => ?_) (fun _ _ _ _ => rfl) τ hτ z]
  · simp [transverseInverseSem, transversePrimitiveSem, phaseCoeff, GenSort.ofTime,
      TimeLetter.eval]
  · have hreg := hS.reg A hA 0 le_rfl 1 le_rfl hN τ' hτ' 0
    rw [liftCellSource_monoField _ (Cc A) 0 hreg X z' 0 α (by omega)]
    have hu : (Finset.univ : Finset (Equiv.Perm (Fin 0))) = {1} := by
      ext σ; simp [Subsingleton.elim σ 1]
    rw [hu, Finset.sum_singleton]
    simp only [Equiv.Perm.coe_one, Function.comp_id, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_mul]
    exact srcArr_zero hS hA hτ' α X z'

/-- **The entries of order zero of the degree-two label mean vanish.** -/
theorem pmArr_two_zero (hS : DiagSetup D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc) (hN : 1 ≤ N)
    {A : RealChain} (hA : A ∈ 𝒜) {t : ℝ} (ht : (D.cellScaleSq m)⁻¹ * t ∈ Icc t₀ t₁) (κ : Fin 2)
    (α : DerivativeWord2 0) (y : Vec 2) :
    pmArr D m ρ (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ (fun _ _ _ => []))
        (Cc A) 2 t κ 0 α y 0 = 0 := by
  have hB0 : entryArr (Cc A 0 0) 0 0 ((D.cellScaleSq m)⁻¹ * t) 0 0 α = fun _ _ => 1 := by
    funext X' z''
    simp only [entryArr, le_refl, ↓reduceIte]
    exact cc000_eq_one hS hA ht X' z'' _
  have hE : entryArr (Cc A 0 1) 1 0 ((D.cellScaleSq m)⁻¹ * t) 0 0 α = fun _ _ => 0 := by
    funext X' z'
    simp only [entryArr, zero_le, ↓reduceIte]
    exact cc010_eq_zero hS hN hA α X' ht z'
  have hflux : ∀ X z, fluxXArr (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ
      (fun _ _ _ => [])) (Cc A) 0 0 2 ((D.cellScaleSq m)⁻¹ * t) (Fin.last 0) κ 0 α X z = 0 := by
    intro X z
    simp only [fluxXArr, fluxXA, fluxXB, fluxXC, fluxXD, ↓reduceIte, show (2 : ℕ) - 1 = 1 from rfl,
      show (2 : ℕ) - 2 = 0 from rfl, le_refl, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, Pi.zero_apply, Finset.sum_apply, smul_eq_mul, mulArr, Fin.last_zero]
    simp only [fastArr, slowArr, slowExtra, hE, hB0, fastPartial_const_fun, slowPartial_const_fun,
      mul_zero, Finset.sum_const_zero, sub_zero, add_zero, neg_zero]
  unfold pmArr
  simp only [hflux]
  simp [fieldCellMean]

end AVRegularity.Providers.CascadeInvariants
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the flat value of the quadratic label mean is the reference flux.**
With the metric `I`, the first corrector of the pulse `k` of level `m`, from zero at the slot start,
has the single mode `−(2ℓ²)⁻¹ ∫_{t₀}^t e^{−μ(t−s)} A_j(s) ds` (amplitude `A_j = driftAmp`), and the
quadratic label mean `κ_{m−1}(A_κ ∫…)/(2ℓ²) + κ_m δ` is exactly `𝖩_m(t)` on the pulse window
(`flat_identity`): the pulse vanishes before the slot start (`tsupport ζ ⊆ (−2/3, 2/3)`), so its
all-time memory there is zero (`ocPulseMemory_slotStart_eq_zero`), and the memory of `𝖩_m` is the
flat zero-past memory. There is no switching term. -/

open AVRegularity.Providers.ComplexContext AVRegularity.CycleComparison.Diagonal

/-- The flat memory `∫_{t₀}^t e^{−(4π²/ℓ²)(t−s)} A_j(s) ds` of the drift amplitude from the slot
start. -/
def flatMem (D : OCData) (m : ℕ) (k : ℤ) (j : Fin 2) (t : ℝ) : ℝ :=
  ∫ s in D.slotStart m k..t,
    Real.exp (-(4 * Real.pi ^ 2 / D.cellScaleSq m * (t - s))) * driftAmp D m k j s

variable {D : OCData} {m : ℕ}

/-- **The pulse vanishes before the start of its slot.** -/
theorem ocPulse_eq_zero_of_le_slotStart (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (k : ℤ) {r : ℝ}
    (hr : r ≤ D.slotStart m k) : ocPulse D.α D.q D.Λ D.ζ m k r = 0 := by
  have hτ := Construction.Stream.ocTau_pos (α := D.α) (q := D.q) (Λ := D.Λ) (m := m) hΛ
  unfold ocPulse
  have hz : D.ζ ((r - (k : ℝ) * ocTau D.α D.q D.Λ m) / ocTau D.α D.q D.Λ m) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := (hζ.2.2.1 hmem).1
    have h2 : (r - (k : ℝ) * ocTau D.α D.q D.Λ m) / ocTau D.α D.q D.Λ m ≤ -(61 / 48) := by
      rw [div_le_iff₀ hτ]
      have : r ≤ ((k : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ m := hr
      nlinarith
    linarith
  rw [hz, mul_zero]

/-- **The all-time memory of the pulse vanishes at the start of its slot.** -/
theorem ocPulseMemory_slotStart_eq_zero (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (ν : ℝ) (k : ℤ) :
    ocPulseMemory D.α D.q D.Λ D.ζ m ν k (D.slotStart m k) = 0 := by
  unfold ocPulseMemory
  have : ∀ r ∈ Ioi (0 : ℝ), Real.exp (-(ocMu D.q D.Λ m ν) * r) *
      ocPulse D.α D.q D.Λ D.ζ m k (D.slotStart m k - r) = 0 := by
    intro r hr
    rw [ocPulse_eq_zero_of_le_slotStart hΛ hζ k (by linarith [show (0 : ℝ) < r from hr]),
      mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi this, integral_zero]

/-- The product of the shear components at the origin is `(2πε^α)²` on the parallel direction. -/
theorem ocShearVel_zero_mul (k : ℤ) (hk : Odd k) (κ j : Fin 2) :
    ocShearVel D.α D.q D.Λ m k 0 κ * ocShearVel D.α D.q D.Λ m k 0 j =
      (2 * Real.pi * ocEpsilon D.q D.Λ m ^ (1 + D.α) * (ocEpsilon D.q D.Λ m)⁻¹) ^ 2 *
        (basisVec (EntryWeakProofs.pulseParallel k) κ *
          basisVec (EntryWeakProofs.pulseParallel k) j) := by
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by obtain ⟨r, rfl⟩ := hk; omega
  rcases hk4 with h1 | h3
  · rw [CycleReference.ocShearVel_horizontal h1]
    simp only [EntryWeakProofs.pulseParallel, h1, ↓reduceIte]
    fin_cases κ <;> fin_cases j
    all_goals simp [basisVec]
    all_goals ring
  · rw [CycleReference.ocShearVel_vertical h3]
    have h1 : k % 4 ≠ 1 := by omega
    simp only [EntryWeakProofs.pulseParallel, h1, ↓reduceIte]
    fin_cases κ <;> fin_cases j
    all_goals simp [basisVec]
    all_goals ring

/-- **The flat identity**: the flat quadratic label mean is the reference flux on the pulse
window. -/
theorem flat_identity (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : ∀ i, 0 < D.kap i)
    (hκm : D.kap m = D.κ m) {k : ℤ} (hk : Odd k) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) (κ j : Fin 2) :
    D.kap (m - 1) * (driftAmp D m k κ t * flatMem D m k j t) / (2 * D.cellScaleSq m) +
      D.kap m * (if κ = j then 1 else 0) =
    ocRefFlux D.α D.q D.Λ D.ζ m (D.κ m) t κ j := by
  rw [← hκm]
  have hν0 : 0 < D.kap m := hκ m
  have hB0 : 0 < D.kap (m - 1) := hκ (m - 1)
  have he0 : 0 < ocEpsilon D.q D.Λ m := Construction.Stream.ocEpsilon_pos hΛ
  have hc : D.cellScaleSq m = ocEpsilon D.q D.Λ m ^ 2 / D.kap m := rfl
  have hell : ocEll D.q D.Λ m (D.kap m) ^ 2 = ocEpsilon D.q D.Λ m ^ 2 / D.kap m :=
    ocEll_sq_eq_div hν0
  have hrate : 4 * Real.pi ^ 2 / D.cellScaleSq m = ocMu D.q D.Λ m (D.kap m) := by
    rw [hc, ocMu]
    field_simp
  -- the memory of `𝖩_m` is the flat zero-past memory
  have hmem : ocPulseMemory D.α D.q D.Λ D.ζ m (D.kap m) k t =
      ∫ r in D.slotStart m k..t, Real.exp (-(ocMu D.q D.Λ m (D.kap m)) * (t - r)) *
        ocPulse D.α D.q D.Λ D.ζ m k r := by
    have h := ocPulseMemory_sub_interval (α := D.α) (q := D.q) (m := m) hΛ hζ (D.kap m) k
      (D.slotStart m k) t
    rw [ocPulseMemory_slotStart_eq_zero hΛ hζ, mul_zero, sub_eq_zero] at h
    exact h
  set M := ∫ r in D.slotStart m k..t, Real.exp (-(ocMu D.q D.Λ m (D.kap m)) * (t - r)) *
    ocPulse D.α D.q D.Λ D.ζ m k r with hM
  set a := Real.sqrt (D.kap m / D.kap (m - 1)) * (ocEpsilon D.q D.Λ m ^ 2 / D.kap m /
    ocEpsilon D.q D.Λ m) with ha
  -- the flat memory of the amplitude
  have hflat : flatMem D m k j t = a * ocShearVel D.α D.q D.Λ m k 0 j * M := by
    unfold flatMem
    rw [hM, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [driftAmp, hrate, hell, ha]
    rw [show D.eps m = ocEpsilon D.q D.Λ m from rfl, neg_mul]
    ring
  have hamp : driftAmp D m k κ t = a * (ocPulse D.α D.q D.Λ D.ζ m k t *
      ocShearVel D.α D.q D.Λ m k 0 κ) := by
    simp only [driftAmp, hell, ha]
    rw [show D.eps m = ocEpsilon D.q D.Λ m from rfl]
    ring
  rw [ocRefFlux_window_entry hΛ hζ (D.kap m) hk ht κ j, hmem, hflat, hamp]
  have hsq : Real.sqrt (D.kap m / D.kap (m - 1)) * Real.sqrt (D.kap m / D.kap (m - 1)) =
      D.kap m / D.kap (m - 1) := Real.mul_self_sqrt (div_nonneg hν0.le hB0.le)
  have hshear := ocShearVel_zero_mul (D := D) (m := m) k hk κ j
  have hμH : ocMu D.q D.Λ m (D.kap m) * ocHStar D.α D.q D.Λ m (D.kap m) =
      (2 * Real.pi * ocEpsilon D.q D.Λ m ^ (1 + D.α) * (ocEpsilon D.q D.Λ m)⁻¹) ^ 2 / 2 := by
    rw [ocMu, ocHStar, rpow_two_mul_eq_sq' he0.le]
    field_simp
    ring
  rw [hμH]
  have key : D.kap (m - 1) * (a * (ocPulse D.α D.q D.Λ D.ζ m k t * ocShearVel D.α D.q D.Λ m k 0 κ) *
      (a * ocShearVel D.α D.q D.Λ m k 0 j * M)) / (2 * D.cellScaleSq m) =
      (ocShearVel D.α D.q D.Λ m k 0 κ * ocShearVel D.α D.q D.Λ m k 0 j) / 2 *
        (ocPulse D.α D.q D.Λ D.ζ m k t * M) := by
    have e1 : D.kap (m - 1) * (a * (ocPulse D.α D.q D.Λ D.ζ m k t *
        ocShearVel D.α D.q D.Λ m k 0 κ) * (a * ocShearVel D.α D.q D.Λ m k 0 j * M)) =
        D.kap (m - 1) * (Real.sqrt (D.kap m / D.kap (m - 1)) *
          Real.sqrt (D.kap m / D.kap (m - 1))) *
          (ocEpsilon D.q D.Λ m ^ 2 / D.kap m / ocEpsilon D.q D.Λ m) ^ 2 *
          (ocShearVel D.α D.q D.Λ m k 0 κ * ocShearVel D.α D.q D.Λ m k 0 j) *
          (ocPulse D.α D.q D.Λ D.ζ m k t * M) := by
      rw [ha]; ring
    rw [e1, hsq, hc]
    field_simp
  rw [key, hshear]
  ring

end AVRegularity.Providers.CascadeInvariants
end
