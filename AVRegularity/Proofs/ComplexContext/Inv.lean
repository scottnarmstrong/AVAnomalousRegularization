-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.ChartCorrectionIntegrability
import AVRegularity.Construction.Scales.Times
import AVRegularity.Proofs.ComplexChain.Family
public import AVRegularity.Definitions.Construction.Gen.Majorant
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Complex
open scoped Interval
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: phase series.** The final-phase and internal-phase dependence of the generated
functions is through `1`-periodic functions of one real phase `s`. A *phase series* is a function `g : ℝ → ℂ` that is the sum of an
absolutely convergent Fourier series `∑_h c_h e^{2πihs}` with rapidly decreasing coefficients
(`IsPS g c`). Then the coefficients are the Fourier coefficients over a period
(`IsPS.pcoeff_eq`), and phase series form an algebra in which the coefficients of a product are
the convolution of the coefficients (`IsPS.mul`). -/

/-- The Fourier coefficient over a period. -/
def pcoeff (g : ℝ → ℂ) (h : ℤ) : ℂ :=
  ∫ s in (0 : ℝ)..1, g s * Complex.exp (-(2 * Real.pi * I * (h : ℂ) * (s : ℂ)))

/-- The Fourier mode `e^{2πihs}`. -/
def emode (h : ℤ) (s : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * (h : ℂ) * (s : ℂ))

/-- The weight `(1 + |h|)^k`. -/
def pw (k : ℕ) (h : ℤ) : ℝ := (1 + |(h : ℝ)|) ^ k

/-- Rapidly decreasing coefficients. -/
def Rapid (c : ℤ → ℂ) : Prop := ∀ k : ℕ, Summable fun h => pw k h * ‖c h‖

/-- **A phase series** with the rapidly decreasing coefficients `c`. -/
structure IsPS (g : ℝ → ℂ) (c : ℤ → ℂ) : Prop where
  rapid : Rapid c
  sum : ∀ s, HasSum (fun h => c h * emode h s) (g s)

theorem norm_emode (h : ℤ) (s : ℝ) : ‖emode h s‖ = 1 := by
  rw [emode, Complex.norm_exp]
  simp

theorem one_le_pw (k : ℕ) (h : ℤ) : 1 ≤ pw k h :=
  one_le_pow₀ (by linarith [abs_nonneg (h : ℝ)])

theorem pw_nonneg (k : ℕ) (h : ℤ) : 0 ≤ pw k h := zero_le_one.trans (one_le_pw k h)

theorem Rapid.summable {c : ℤ → ℂ} (hc : Rapid c) : Summable fun h => ‖c h‖ := by
  simpa [pw] using hc 0

theorem emode_mul (h k : ℤ) (s : ℝ) : emode h s * emode k s = emode (h + k) s := by
  rw [emode, emode, emode, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem continuous_emode (h : ℤ) : Continuous (emode h) := by
  unfold emode; fun_prop

/-- The orthogonality of the modes over a period. -/
theorem integral_emode (h : ℤ) : ∫ s in (0 : ℝ)..1, emode h s = if h = 0 then 1 else 0 := by
  split_ifs with h0
  · subst h0; simp [emode]
  · have hh : (h : ℂ) ≠ 0 := by exact_mod_cast h0
    have hc : (2 * Real.pi * I * (h : ℂ)) ≠ 0 := by
      have : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      exact mul_ne_zero this hh
    have e : (fun s : ℝ => emode h s) = fun s : ℝ => Complex.exp ((2 * Real.pi * I * (h : ℂ)) * s) := by
      funext s; rfl
    rw [e, integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * Real.pi * I * (h : ℂ)) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * Real.pi * I * (h : ℂ)) * ((1 : ℝ) : ℂ) = (h : ℂ) * (2 * Real.pi * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I h
    rw [h1]
    simp

theorem exp_neg_eq_emode (h : ℤ) (s : ℝ) :
    Complex.exp (-(2 * Real.pi * I * (h : ℂ) * (s : ℂ))) = emode (-h) s := by
  unfold emode; congr 1; push_cast; ring

/-- **The coefficients of a phase series are its Fourier coefficients.** -/
theorem IsPS.pcoeff_eq {g : ℝ → ℂ} {c : ℤ → ℂ} (hg : IsPS g c) (h : ℤ) : pcoeff g h = c h := by
  unfold pcoeff
  have hs := hg.rapid.summable
  -- termwise integration of `∑_k c_k e_k e_{-h}`
  set f : ℤ → C(ℝ, ℂ) := fun k => ⟨fun s => c k * emode k s * emode (-h) s,
    (continuous_const.mul (continuous_emode k)).mul (continuous_emode (-h))⟩ with hf
  have hnorm : ∀ k, ‖(f k).restrict (⟨uIcc (0 : ℝ) 1, isCompact_uIcc⟩ :
      TopologicalSpace.Compacts ℝ)‖ ≤ ‖c k‖ := by
    intro k
    refine ContinuousMap.norm_le _ (norm_nonneg _) |>.2 fun x => ?_
    simp only [ContinuousMap.restrict_apply, hf, ContinuousMap.coe_mk, norm_mul, norm_emode,
      mul_one, le_refl]
  have hsum : Summable fun k => ‖(f k).restrict (⟨uIcc (0 : ℝ) 1, isCompact_uIcc⟩ :
      TopologicalSpace.Compacts ℝ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm hs
  have heq : (fun s => g s * Complex.exp (-(2 * Real.pi * I * (h : ℂ) * (s : ℂ)))) =
      fun s => ∑' k, f k s := by
    funext s
    rw [exp_neg_eq_emode, ← (hg.sum s).tsum_eq, ← tsum_mul_right]
    rfl
  rw [heq, ← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum]
  have hk : ∀ k, ∫ s in (0 : ℝ)..1, f k s = if k = h then c k else 0 := by
    intro k
    have e : (fun s => f k s) = fun s => c k * emode (k + -h) s := by
      funext s
      show c k * emode k s * emode (-h) s = _
      rw [mul_assoc, emode_mul]
    rw [e, intervalIntegral.integral_const_mul, integral_emode]
    by_cases hkh : k = h
    · subst hkh; simp
    · have : k + -h ≠ 0 := by omega
      simp [this, hkh]
  simp_rw [hk]
  rw [tsum_ite_eq]

/-! ### The algebra of phase series -/

/-- The convolution of two coefficient sequences. -/
def conv (a b : ℤ → ℂ) (h : ℤ) : ℂ := ∑' j, a j * b (h - j)

theorem pw_mul_le (k : ℕ) (h j : ℤ) : pw k h ≤ pw k j * pw k (h - j) := by
  unfold pw
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have h1 : |(h : ℝ)| ≤ |(j : ℝ)| + |((h - j : ℤ) : ℝ)| := by
    push_cast
    calc |(h : ℝ)| = |(j : ℝ) + ((h : ℝ) - j)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have h2 : 0 ≤ |(j : ℝ)| * |((h - j : ℤ) : ℝ)| := by positivity
  nlinarith

/-- The reindexing `(h, j) ↦ (j, h - j)` of `ℤ × ℤ`. -/
def convEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun q := (q.2, q.1 - q.2)
  invFun q := (q.1 + q.2, q.1)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp

/-- **The convolution of absolutely summable sequences**: the sum over `h` of the convolution is
the product of the sums, and every fiber is summable. -/
theorem hasSum_conv {a b : ℤ → ℂ} (ha : Summable fun j => ‖a j‖) (hb : Summable fun j => ‖b j‖) :
    HasSum (conv a b) ((∑' j, a j) * ∑' j, b j) ∧
      ∀ h, Summable fun j => a j * b (h - j) := by
  have hab : Summable fun q : ℤ × ℤ => ‖a q.1 * b q.2‖ := by
    simp_rw [norm_mul]
    exact ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hp : HasSum (fun q : ℤ × ℤ => a q.1 * b q.2) ((∑' j, a j) * ∑' j, b j) := by
    rw [tsum_mul_tsum_of_summable_norm ha hb]
    exact (summable_mul_of_summable_norm ha hb).hasSum
  have hp' : HasSum (fun q : ℤ × ℤ => a q.2 * b (q.1 - q.2)) ((∑' j, a j) * ∑' j, b j) := by
    have := (convEquiv.hasSum_iff (f := fun q : ℤ × ℤ => a q.1 * b q.2)).mpr hp
    exact this
  have hsum' : Summable fun q : ℤ × ℤ => ‖a q.2 * b (q.1 - q.2)‖ := by
    have := (convEquiv.summable_iff (f := fun q : ℤ × ℤ => ‖a q.1 * b q.2‖)).mpr hab
    exact this
  have hfib : ∀ h, Summable fun j => a j * b (h - j) := fun h =>
    (hsum'.comp_injective (Prod.mk_right_injective h)).of_norm
  exact ⟨hp'.prod_fiberwise fun h => (hfib h).hasSum, hfib⟩

theorem norm_conv_le {a b : ℤ → ℂ} (ha : Summable fun j => ‖a j‖)
    (hb : Summable fun j => ‖b j‖) (h : ℤ) :
    ‖conv a b h‖ ≤ ∑' j, ‖a j‖ * ‖b (h - j)‖ := by
  have hs := (hasSum_conv ha hb).2 h
  refine (norm_tsum_le_tsum_norm hs.norm).trans (le_of_eq ?_)
  simp_rw [norm_mul]

/-- The convolution of nonnegative summable real sequences is summable. -/
theorem summable_conv_real {A B : ℤ → ℝ} (hA0 : ∀ j, 0 ≤ A j) (hB0 : ∀ j, 0 ≤ B j)
    (hA : Summable A) (hB : Summable B) :
    Summable (fun h => ∑' j, A j * B (h - j)) ∧ ∀ h, Summable fun j => A j * B (h - j) := by
  have hp : Summable fun q : ℤ × ℤ => A q.1 * B q.2 := hA.mul_of_nonneg hB hA0 hB0
  have hp' : Summable fun q : ℤ × ℤ => A q.2 * B (q.1 - q.2) :=
    (convEquiv.summable_iff (f := fun q : ℤ × ℤ => A q.1 * B q.2)).mpr hp
  exact ⟨hp'.prod, fun h => hp'.prod_factor h⟩

/-- **Rapid decrease is preserved by convolution.** -/
theorem Rapid.conv {a b : ℤ → ℂ} (ha : Rapid a) (hb : Rapid b) : Rapid (conv a b) := by
  intro k
  set A : ℤ → ℝ := fun j => pw k j * ‖a j‖ with hAdef
  set B : ℤ → ℝ := fun j => pw k j * ‖b j‖ with hBdef
  have hA0 : ∀ j, 0 ≤ A j := fun j => mul_nonneg (pw_nonneg k j) (norm_nonneg _)
  have hB0 : ∀ j, 0 ≤ B j := fun j => mul_nonneg (pw_nonneg k j) (norm_nonneg _)
  obtain ⟨hs, hfib⟩ := summable_conv_real hA0 hB0 (ha k) (hb k)
  refine Summable.of_nonneg_of_le (fun h => mul_nonneg (pw_nonneg k h) (norm_nonneg _))
    (fun h => ?_) hs
  have hterm : ∀ j, pw k h * (‖a j‖ * ‖b (h - j)‖) ≤ A j * B (h - j) := fun j =>
    calc pw k h * (‖a j‖ * ‖b (h - j)‖) ≤ (pw k j * pw k (h - j)) * (‖a j‖ * ‖b (h - j)‖) :=
          mul_le_mul_of_nonneg_right (pw_mul_le k h j) (by positivity)
      _ = A j * B (h - j) := by simp only [hAdef, hBdef]; ring
  have hs1 : Summable fun j => pw k h * (‖a j‖ * ‖b (h - j)‖) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (pw_nonneg k h) (by positivity)) hterm (hfib h)
  calc pw k h * ‖ComplexContext.conv a b h‖ ≤ pw k h * ∑' j, ‖a j‖ * ‖b (h - j)‖ :=
        mul_le_mul_of_nonneg_left (norm_conv_le ha.summable hb.summable h) (pw_nonneg k h)
    _ = ∑' j, pw k h * (‖a j‖ * ‖b (h - j)‖) := (tsum_mul_left).symm
    _ ≤ ∑' j, A j * B (h - j) := hs1.tsum_le_tsum hterm (hfib h)

/-- **The product of two phase series** is the phase series of the convolution. -/
theorem IsPS.mul {g g' : ℝ → ℂ} {c c' : ℤ → ℂ} (hg : IsPS g c) (hg' : IsPS g' c') :
    IsPS (fun s => g s * g' s) (conv c c') := by
  refine ⟨hg.rapid.conv hg'.rapid, fun s => ?_⟩
  have ha : Summable fun j => ‖c j * emode j s‖ := by
    simpa [norm_mul, norm_emode] using hg.rapid.summable
  have hb : Summable fun j => ‖c' j * emode j s‖ := by
    simpa [norm_mul, norm_emode] using hg'.rapid.summable
  have h := (hasSum_conv ha hb).1
  rw [(hg.sum s).tsum_eq, (hg'.sum s).tsum_eq] at h
  convert h using 1
  funext h'
  unfold conv
  rw [← tsum_mul_right]
  congr 1; funext j
  rw [show c j * c' (h' - j) * emode h' s = c j * emode j s * (c' (h' - j) * emode (h' - j) s) by
    rw [show c j * emode j s * (c' (h' - j) * emode (h' - j) s) =
      c j * c' (h' - j) * (emode j s * emode (h' - j) s) by ring, emode_mul]
    congr 2; ring]

/-- Constants. -/
theorem IsPS.const (a : ℂ) : IsPS (fun _ => a) (fun h => if h = 0 then a else 0) := by
  refine ⟨fun k => ?_, fun s => ?_⟩
  · refine (summable_of_ne_finset_zero (s := {0}) fun h hh => ?_)
    simp only [Finset.mem_singleton] at hh
    simp [hh]
  · convert hasSum_ite_eq (0 : ℤ) a using 1
    funext h
    split_ifs with h0
    · subst h0; simp [emode]
    · simp

/-- Sums. -/
theorem IsPS.add {g g' : ℝ → ℂ} {c c' : ℤ → ℂ} (hg : IsPS g c) (hg' : IsPS g' c') :
    IsPS (fun s => g s + g' s) (fun h => c h + c' h) := by
  refine ⟨fun k => ?_, fun s => ?_⟩
  · refine Summable.of_nonneg_of_le (fun h => mul_nonneg (pw_nonneg k h) (norm_nonneg _))
      (fun h => ?_) ((hg.rapid k).add (hg'.rapid k))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (pw_nonneg k h)
  · have := (hg.sum s).add (hg'.sum s)
    simpa [add_mul] using this

end AVRegularity.Providers.ComplexContext
end

section
open Real
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the scale bound of the normalized cell drift.** The amplitude
of the normalized drift `w = √(κ_i/κ_{i-1}) v` of a pulse of level `i` is at most
`2π ε_i^{1+α} / √(κ_i κ_{i-1})` (diffusivities with the terminal convention, `κ_{min(m, M)}`). On a
band chain this is bounded uniformly in the terminal level and in the level
(`drift_scale_bound`):
* at levels `2 ≤ i ≤ M`, `κ_m ≥ C⁻¹ ε_m^{1+α+γ}` and `ε_i ≤ 2 ε_{i-1}^q` balance exactly, because
  `(q+1)γ = (q-1)(1+α)`;
* at the level `1`, `κ_0 ≥ κ_1` (the mean flux enhances), with a constant depending on `Λ`;
* at weak levels `i > M`, `ε_i^{1+α}/κ_M ≤ C 2^{1+α} ε_M^{q(1+α) - (1+α+γ)} ≤ C 2^{1+α}`;
* for `M = 0`, `κ_0 ≥ 1/2` (the band of level `0`). -/

/-- The balance of the exponents. -/
theorem gamma_balance (α q : ℝ) (hq : 1 < q) :
    q * ((1 + α) - ocGamma α q) / 2 = ((1 + α) + ocGamma α q) / 2 := by
  unfold ocGamma
  field_simp
  ring

/-- **The scale bound of the normalized cell drift.** -/
theorem drift_scale_bound {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ Cd : ℝ, 0 < Cd ∧ ∀ (M : ℕ) (κ : ℕ → ℝ),
      IsOCBandChain α q Λ ζ M κ → ∀ i : ℕ, 1 ≤ i →
        ocEpsilon q Λ i ^ (1 + α) ≤ Cd * Real.sqrt (κ (min i M) * κ (min (i - 1) M)) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hb⟩ := CycleReference.bandChain_all_level_bounds hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hq1 : 1 < q := hq.1
  have hq17 : q < 17 / 16 := hq.2.1
  set γ := ocGamma α q with hγ
  have hγ0 : 0 ≤ γ := by
    rw [hγ]; unfold ocGamma; have : 0 < q + 1 := by linarith
    have : 0 ≤ q - 1 := by linarith
    positivity
  have hγlt : γ < 1 + α := by
    rw [hγ]; unfold ocGamma
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  set e := (1 + α) + γ with he
  set a := ((1 + α) - γ) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have heps : ∀ m, 0 < ocEpsilon q Λ m ∧ ocEpsilon q Λ m ≤ 1 := fun m =>
    ⟨(AVRegularity.Scales.epsilon_basic hq1 h128).1, (AVRegularity.Scales.epsilon_basic hq1 h128).2.1⟩
  have hC0 : 0 < C := by linarith
  -- the constant at the level 1 depends on `Λ`
  set ε₁ := ocEpsilon q Λ 1
  have hε₁ := heps 1
  set Cd := max (max ((2 : ℝ) ^ a * C) (C * ε₁ ^ (-γ))) (max (C * 2 ^ (1 + α)) 2) with hCd
  have hCd0 : 0 < Cd := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨Cd, hCd0, fun M κ hκ i hi => ?_⟩
  have hpos : ∀ m, m ≤ M → 0 < κ m := fun m hm =>
    CycleReference.bandChain_pos (by omega) hζ hκ hm
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · -- terminal level `0`
    subst hM0
    simp only [Nat.min_zero]
    have hk : (1 : ℝ) / 2 ≤ κ 0 := by
      have := hκ.1.1
      simpa [ocEpsilon] using this
    have hk0 : 0 < κ 0 := by linarith
    rw [Real.sqrt_mul_self hk0.le]
    have hε := heps i
    have h1 : ocEpsilon q Λ i ^ (1 + α) ≤ 1 := Real.rpow_le_one hε.1.le hε.2 (by linarith)
    calc ocEpsilon q Λ i ^ (1 + α) ≤ 1 := h1
      _ ≤ 2 * κ 0 := by linarith
      _ ≤ Cd * κ 0 := mul_le_mul_of_nonneg_right
          (le_trans (le_max_right _ _) (le_max_right _ _)) hk0.le
  by_cases hiM : i ≤ M
  · rw [min_eq_left hiM, min_eq_left (by omega : i - 1 ≤ M)]
    have hki := (hb Λ hΛ M hMpos κ hκ i hi hiM).1
    by_cases hi1 : i = 1
    · -- the level `1`: `κ_0 ≥ κ_1`
      subst hi1
      have hk1 := hpos 1 hiM
      have hk0 : κ 1 ≤ κ 0 := by
        have hrel := hκ.2 1 le_rfl hiM
        simp only [Nat.sub_self] at hrel
        rw [hrel]
        exact CycleReference.meanFlux_ge_input (by omega) hζ hk1
      have hsq : κ 1 ≤ Real.sqrt (κ 1 * κ 0) :=
        calc κ 1 = Real.sqrt (κ 1 * κ 1) := (Real.sqrt_mul_self hk1.le).symm
          _ ≤ Real.sqrt (κ 1 * κ 0) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hk0 hk1.le)
      simp only [Nat.sub_self]
      -- `ε₁^{1+α} = ε₁^{-γ} ε₁^{e} ≤ C ε₁^{-γ} κ_1`
      have hsplit : ε₁ ^ (1 + α) = ε₁ ^ (-γ) * ε₁ ^ e := by
        rw [← Real.rpow_add hε₁.1]; congr 1; rw [he]; ring
      have hke : ε₁ ^ e ≤ C * κ 1 := by
        have := hki
        rw [inv_mul_le_iff₀ hC0] at this
        exact this
      calc ocEpsilon q Λ 1 ^ (1 + α) = ε₁ ^ (-γ) * ε₁ ^ e := hsplit
        _ ≤ ε₁ ^ (-γ) * (C * κ 1) := mul_le_mul_of_nonneg_left hke (Real.rpow_nonneg hε₁.1.le _)
        _ = C * ε₁ ^ (-γ) * κ 1 := by ring
        _ ≤ Cd * Real.sqrt (κ 1 * κ 0) := by
            refine mul_le_mul ?_ hsq hk1.le hCd0.le
            exact le_trans (le_max_right _ _) (le_max_left _ _)
    · -- levels `2 ≤ i ≤ M`
      have hi2 : 2 ≤ i := by omega
      have hki1 := (hb Λ hΛ M hMpos κ hκ (i - 1) (by omega) (by omega)).1
      set x := ocEpsilon q Λ (i - 1)
      set y := ocEpsilon q Λ i
      have hx := heps (i - 1)
      have hy := heps i
      have hyx : y ≤ 2 * x ^ q := AVRegularity.Scales.epsilon_q_step hq1 hq17 h128 hi
      -- `y^a ≤ 2^a x^{e/2}`
      have hya : y ^ a ≤ 2 ^ a * x ^ (e / 2) := by
        have h1 : y ^ a ≤ (2 * x ^ q) ^ a := Real.rpow_le_rpow hy.1.le hyx ha0.le
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx.1.le _), ← Real.rpow_mul hx.1.le]
          at h1
        have hqa : q * a = e / 2 := by rw [ha, he, ← gamma_balance α q hq1]; ring
        rwa [hqa] at h1
      have hy1 : y ^ (1 + α) = y ^ a * y ^ (e / 2) := by
        rw [← Real.rpow_add hy.1]; congr 1; rw [ha, he]; ring
      have hprod : (x * y) ^ (e / 2) ≤ C * Real.sqrt (κ i * κ (i - 1)) := by
        have hxe : x ^ e ≤ C * κ (i - 1) := by
          have := hki1; rw [inv_mul_le_iff₀ hC0] at this; exact this
        have hye : y ^ e ≤ C * κ i := by
          have := hki; rw [inv_mul_le_iff₀ hC0] at this; exact this
        have h2 : (x * y) ^ e ≤ (C * Real.sqrt (κ i * κ (i - 1))) ^ 2 := by
          rw [Real.mul_rpow hx.1.le hy.1.le, mul_pow, Real.sq_sqrt (mul_nonneg
            (hpos i hiM).le (hpos (i - 1) (by omega)).le)]
          calc x ^ e * y ^ e ≤ (C * κ (i - 1)) * (C * κ i) :=
                mul_le_mul hxe hye (Real.rpow_nonneg hy.1.le _)
                  (mul_nonneg hC0.le (hpos (i - 1) (by omega)).le)
            _ = C ^ 2 * (κ i * κ (i - 1)) := by ring
        have hxy0 : 0 ≤ x * y := mul_nonneg hx.1.le hy.1.le
        calc (x * y) ^ (e / 2) = Real.sqrt ((x * y) ^ e) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxy0]; ring_nf
          _ ≤ Real.sqrt ((C * Real.sqrt (κ i * κ (i - 1))) ^ 2) := Real.sqrt_le_sqrt h2
          _ = C * Real.sqrt (κ i * κ (i - 1)) := Real.sqrt_sq (by positivity)
      calc y ^ (1 + α) = y ^ a * y ^ (e / 2) := hy1
        _ ≤ (2 ^ a * x ^ (e / 2)) * y ^ (e / 2) :=
            mul_le_mul_of_nonneg_right hya (Real.rpow_nonneg hy.1.le _)
        _ = 2 ^ a * (x * y) ^ (e / 2) := by
            rw [Real.mul_rpow hx.1.le hy.1.le]; ring
        _ ≤ 2 ^ a * (C * Real.sqrt (κ i * κ (i - 1))) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = 2 ^ a * C * Real.sqrt (κ i * κ (i - 1)) := by ring
        _ ≤ Cd * Real.sqrt (κ i * κ (i - 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
            exact le_trans (le_max_left _ _) (le_max_left _ _)
  · -- weak levels `i > M`
    replace hiM : M < i := not_le.mp hiM
    rw [min_eq_right hiM.le, min_eq_right (by omega : M ≤ i - 1)]
    have hkM := hpos M le_rfl
    rw [Real.sqrt_mul_self hkM.le]
    have hkMe := (hb Λ hΛ M hMpos κ hκ M hMpos le_rfl).1
    set x := ocEpsilon q Λ M
    have hx := heps M
    have hyM : ocEpsilon q Λ i ≤ ocEpsilon q Λ (M + 1) := by
      have : ∀ k, ocEpsilon q Λ (M + 1 + k) ≤ ocEpsilon q Λ (M + 1) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          exact (CycleReference.epsilon_succ_le hq1 h128).trans (by simpa [add_assoc] using ih)
      have := this (i - (M + 1))
      rwa [show M + 1 + (i - (M + 1)) = i by omega] at this
    have hstep : ocEpsilon q Λ (M + 1) ≤ 2 * x ^ q :=
      AVRegularity.Scales.epsilon_q_step hq1 hq17 h128 (by omega)
    have hy := heps i
    have h1 : ocEpsilon q Λ i ^ (1 + α) ≤ (2 * x ^ q) ^ (1 + α) :=
      Real.rpow_le_rpow hy.1.le (hyM.trans hstep) (by linarith)
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx.1.le _), ← Real.rpow_mul hx.1.le] at h1
    -- `x^{q(1+α)} ≤ x^e ≤ C κ_M`
    have hexp : e ≤ q * (1 + α) := by
      rw [he, hγ]; unfold ocGamma
      have hn : 0 ≤ (q - 1) * (1 + α) := mul_nonneg (by linarith) (by linarith)
      have : (q - 1) * (1 + α) / (q + 1) ≤ (q - 1) * (1 + α) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hn (by linarith : (0 : ℝ) ≤ q)]
      nlinarith
    have hxq : x ^ (q * (1 + α)) ≤ x ^ e := Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 hexp
    have hxe : x ^ e ≤ C * κ M := by
      have := hkMe; rw [inv_mul_le_iff₀ hC0] at this; exact this
    calc ocEpsilon q Λ i ^ (1 + α) ≤ 2 ^ (1 + α) * x ^ (q * (1 + α)) := h1
      _ ≤ 2 ^ (1 + α) * (C * κ M) :=
          mul_le_mul_of_nonneg_left (hxq.trans hxe) (by positivity)
      _ = C * 2 ^ (1 + α) * κ M := by ring
      _ ≤ Cd * κ M := by
          refine mul_le_mul_of_nonneg_right ?_ hkM.le
          exact le_trans (le_max_left _ _) (le_max_right _ _)

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Metric Set Filter
open scoped Topology Interval
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: holomorphy of parametric integrals of measurable families.** If `g(x, u)` is
holomorphic in `x ∈ U` (an open subset of a finite-dimensional complex space) for every `u` of a
compact interval, measurable in `u` for every `x`, and locally bounded uniformly in `u`, then
`x ↦ ∫_a^b g(x, u) du` is holomorphic on `U` (`differentiableOn_intervalIntegral_of_meas`). This
is the version of `ComplexFlow.differentiableOn_intervalIntegral_of_param` without continuity in
`u`: the transverse inverse integrates fluxes that are only measurable in time (gated child letters,
certified leaves). The derivative is dominated by Cauchy's estimate; it is measurable in `u` because
its values on a basis are limits of difference quotients (`aestronglyMeasurable_fderiv_param`). -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]

/-- A continuous linear functional is the combination of the coordinate functionals of a basis
with its values on the basis. -/
theorem clm_eq_sum_basis (L : X →L[ℂ] ℂ) :
    L = ∑ i, L (Module.finBasis ℂ X i) •
      LinearMap.toContinuousLinearMap ((Module.finBasis ℂ X).coord i) := by
  ext x
  simp only [sum_apply, smul_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, smul_eq_mul]
  conv_lhs => rw [← (Module.finBasis ℂ X).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- **The derivative of a measurable holomorphic family is measurable in the parameter.** -/
theorem aestronglyMeasurable_fderiv_param {U : Set X} (hU : IsOpen U) {g : X → ℝ → ℂ}
    {μ : Measure ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hd : ∀ u ∈ S, DifferentiableOn ℂ (fun x => g x u) U)
    (hm : ∀ x ∈ U, AEStronglyMeasurable (g x) (μ.restrict S)) {x₀ : X} (hx₀ : x₀ ∈ U) :
    AEStronglyMeasurable (fun u => fderiv ℂ (fun x => g x u) x₀) (μ.restrict S) := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  -- each value on a vector is a limit of difference quotients
  have happ : ∀ v : X, AEStronglyMeasurable (fun u => fderiv ℂ (fun x => g x u) x₀ v)
      (μ.restrict S) := by
    intro v
    set K : ℝ := 2 * (‖v‖ + 1) / r with hK
    have hK0 : 0 < K := by positivity
    set c : ℕ → ℂ := fun n => (((n : ℝ) + 1) * K : ℝ) with hc
    have hcn : ∀ n, ‖c n‖ = ((n : ℝ) + 1) * K := fun n => by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hmem : ∀ n, x₀ + (c n)⁻¹ • v ∈ U := by
      intro n
      apply hrU
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv, hcn]
      have h1 : 1 ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
      have h2 : K ≤ ((n : ℝ) + 1) * K := le_mul_of_one_le_left hK0.le h1
      calc (((n : ℝ) + 1) * K)⁻¹ * ‖v‖ ≤ K⁻¹ * ‖v‖ :=
            mul_le_mul_of_nonneg_right (inv_anti₀ hK0 h2) (norm_nonneg v)
        _ = r * ‖v‖ / (2 * (‖v‖ + 1)) := by rw [hK]; field_simp
        _ < r := by
            rw [div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg v]
    have htend : Tendsto (fun n => ‖c n‖) atTop atTop := by
      simp_rw [hcn]
      exact Tendsto.atTop_mul_const hK0 (tendsto_atTop_add_const_right _ 1
        tendsto_natCast_atTop_atTop)
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n u => c n • (g (x₀ + (c n)⁻¹ • v) u - g x₀ u)) (fun n => ?_) ?_
    · exact ((hm _ (hmem n)).sub (hm x₀ hx₀)).const_smul (c n)
    · filter_upwards [ae_restrict_mem hS] with u hu
      have hdiff : HasFDerivAt (fun x => g x u) (fderiv ℂ (fun x => g x u) x₀) x₀ :=
        ((hd u hu) x₀ hx₀).differentiableAt (hU.mem_nhds hx₀) |>.hasFDerivAt
      exact hdiff.lim v htend
  -- the derivative is the basis combination of these values
  have heq : (fun u => fderiv ℂ (fun x => g x u) x₀) = fun u =>
      ∑ i, fderiv ℂ (fun x => g x u) x₀ (Module.finBasis ℂ X i) •
        LinearMap.toContinuousLinearMap ((Module.finBasis ℂ X).coord i) :=
    funext fun u => clm_eq_sum_basis _
  rw [heq]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (happ _).smul_const _

/-- **Holomorphy of a parametric interval integral of a measurable family.** -/
theorem differentiableOn_intervalIntegral_of_meas {U : Set X} (hU : IsOpen U) {g : X → ℝ → ℂ}
    {a b : ℝ} (hd : ∀ u ∈ uIcc a b, DifferentiableOn ℂ (fun x => g x u) U)
    (hm : ∀ x ∈ U, AEStronglyMeasurable (g x) (volume.restrict (Ι a b)))
    (hb : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ M : ℝ, ∀ u ∈ uIcc a b, ∀ y ∈ V, ‖g y u‖ ≤ M) :
    DifferentiableOn ℂ (fun x => ∫ u in a..b, g x u) U := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  obtain ⟨V, hV, M, hM⟩ := hb x₀ hx₀
  obtain ⟨ε', hε', hε'V⟩ := Metric.mem_nhds_iff.mp hV
  set ρ : ℝ := min ε ε' / 4 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hmin : 4 * ρ = min ε ε' := by rw [hρ_def]; ring
  have hcb : closedBall x₀ (3 * ρ) ⊆ U ∩ V := fun x hx => by
    rw [mem_closedBall] at hx
    refine ⟨hεU ?_, hε'V ?_⟩ <;> rw [mem_ball]
    · linarith [min_le_left ε ε']
    · linarith [min_le_right ε ε']
  have hball : ball x₀ ρ ⊆ U := fun x hx =>
    (hcb (mem_closedBall.mpr (by rw [mem_ball] at hx; linarith))).1
  have hIoc : ∀ u ∈ Ι a b, u ∈ uIcc a b := fun u hu => uIoc_subset_uIcc hu
  -- Cauchy's estimate for the derivative on the ball
  have hbd : ∀ u ∈ uIcc a b, ∀ x ∈ ball x₀ ρ, ‖fderiv ℂ (fun x => g x u) x‖ ≤ M / ρ := by
    intro u hu x hx
    have hsub : closedBall x ρ ⊆ closedBall x₀ (3 * ρ) := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      rw [mem_ball] at hx
      have := dist_triangle w x x₀
      linarith
    exact GenSem.norm_fderiv_le_of_closedBall hρ ((hd u hu).mono fun w hw => (hcb (hsub hw)).1)
      fun w hw => hM u hu w (hcb (hsub hw)).2
  have hint : IntervalIntegrable (g x₀) volume a b := by
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound (by simp [Real.volume_Ioc, uIoc]) (hm x₀ hx₀) M ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    exact hM u (hIoc u hu) x₀ (hcb (mem_closedBall_self (by positivity))).2
  have hF' := aestronglyMeasurable_fderiv_param hU measurableSet_uIoc
    (fun u hu => hd u (hIoc u hu)) hm hx₀
  have hB : HasFDerivAt (fun x => ∫ u in a..b, g x u)
      (∫ u in a..b, fderiv ℂ (fun x => g x u) x₀) x₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (μ := volume) (F := g) (F' := fun x u => fderiv ℂ (fun x => g x u) x)
      (bound := fun _ => M / ρ) (s := ball x₀ ρ) (ball_mem_nhds x₀ hρ) ?_ hint hF' ?_
      intervalIntegrable_const ?_
    · exact eventually_of_mem (ball_mem_nhds x₀ hρ) fun x hx => hm x (hball hx)
    · exact Eventually.of_forall fun u hu x hx => hbd u (hIoc u hu) x hx
    · refine Eventually.of_forall fun u hu x hx => ?_
      exact ((hd u (hIoc u hu)) x (hball hx)).differentiableAt
        (hU.mem_nhds (hball hx)) |>.hasFDerivAt
  exact hB.differentiableAt.differentiableWithinAt

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Complex Filter
open scoped Interval Topology
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: Fourier inversion for holomorphic periodic functions.**
* `hasSum_pcoeff_of_summable`: a continuous `1`-periodic function with summable Fourier
  coefficients is the sum of its Fourier series (through `UnitAddCircle`).
* `norm_pcoeff_le_of_strip`: the coefficients of a periodic function holomorphic and bounded on
  `|Im z| < w` decay like `e^{-2π w'|h|}`, `w' < w` (the contour shift of
  `ComplexFlow.norm_fourierCoeff_le_of_strip`).
* `isPS_of_strip`: a periodic function holomorphic on a strip around the real axis is a phase
  series in the real variable (`IsPS`), with its Fourier coefficients.
* `pcoeff_deriv`: the coefficients of the derivative of a periodic `C¹` function are
  `2πih` times the coefficients (the final-phase and internal-phase derivatives, `dPhase`,
  `dInternal`). -/

/-- **Fourier inversion** for a continuous `1`-periodic function with summable coefficients. -/
theorem hasSum_pcoeff_of_summable {g : ℝ → ℂ} (hc : Continuous g) (hp : Function.Periodic g 1)
    (hs : Summable fun h => ‖pcoeff g h‖) (s : ℝ) :
    HasSum (fun h => pcoeff g h * emode h s) (g s) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let F : C(UnitAddCircle, ℂ) := ⟨hp.lift, continuous_coinduced_dom.mpr hc⟩
  have hF : ∀ x : ℝ, F (x : UnitAddCircle) = g x := fun x => by
    simp only [F, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
  have hcoef : ∀ h : ℤ, fourierCoeff F h = pcoeff g h := by
    intro h
    rw [fourierCoeff_eq_intervalIntegral _ h 0, zero_add, div_one, one_smul, pcoeff]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [smul_eq_mul, hF, fourier_coe_apply]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hsum : Summable (fourierCoeff F) := by
    refine Summable.of_norm ?_
    simpa only [hcoef] using hs
  have := has_pointwise_sum_fourier_series_of_summable hsum (s : UnitAddCircle)
  rw [hF] at this
  convert this using 1
  funext h
  rw [hcoef, smul_eq_mul, fourier_coe_apply, emode, ofReal_one, div_one]

/-- A function `1`-periodic on a strip is invariant under integer translations. -/
theorem strip_periodic_int {G : ℂ → ℂ} {S : Set ℝ}
    (hp : ∀ z : ℂ, z.im ∈ S → G (z + 1) = G z) (n : ℤ) (z : ℂ) (hz : z.im ∈ S) :
    G (z + n) = G z := by
  have hnat : ∀ k : ℕ, ∀ z : ℂ, z.im ∈ S → G (z + k) = G z := by
    intro k
    induction k with
    | zero => intro z _; simp
    | succ k ih =>
      intro z hz
      have hzk : (z + k).im ∈ S := by simpa using hz
      rw [Nat.cast_succ, ← add_assoc, hp _ hzk, ih z hz]
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact_mod_cast hnat k z hz
  · have hz' : (z + -(k : ℂ)).im ∈ S := by simpa using hz
    have := hnat k (z + -(k : ℂ)) hz'
    rw [neg_add_cancel_right] at this
    push_cast
    exact this.symm

/-- **A periodic function continuous on a closed strip is bounded there.** -/
theorem exists_bound_strip {G : ℂ → ℂ} {w : ℝ} (hc : ContinuousOn G {z : ℂ | |z.im| ≤ w})
    (hp : ∀ z : ℂ, |z.im| ≤ w → G (z + 1) = G z) :
    ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ w → ‖G z‖ ≤ M := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-w) w) := isCompact_Icc.reProdIm isCompact_Icc
  have hKs : Icc (0 : ℝ) 1 ×ℂ Icc (-w) w ⊆ {z : ℂ | |z.im| ≤ w} := fun z hz =>
    abs_le.mpr ((mem_reProdIm.mp hz).2)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc.mono hKs)
  refine ⟨M, fun z hz => ?_⟩
  have hp' : ∀ z : ℂ, z.im ∈ {y : ℝ | |y| ≤ w} → G (z + 1) = G z := fun z hz => hp z hz
  have e := strip_periodic_int hp' (-⌊z.re⌋) z hz
  rw [← e]
  refine hM _ (mem_reProdIm.mpr ⟨?_, ?_⟩)
  · have h1 := Int.floor_le z.re
    have h2 := Int.lt_floor_add_one z.re
    simp only [add_re, intCast_re]
    push_cast
    constructor <;> linarith
  · simp only [add_im, intCast_im, add_zero]
    exact abs_le.mp hz

/-- **Exponential decay of the coefficients** of a periodic function holomorphic and bounded on a
strip. -/
theorem norm_pcoeff_le_of_strip {G : ℂ → ℂ} {w M : ℝ}
    (hG : DifferentiableOn ℂ G {z : ℂ | |z.im| < w})
    (hp : ∀ z : ℂ, |z.im| < w → G (z + 1) = G z)
    (hM : ∀ z : ℂ, |z.im| < w → ‖G z‖ ≤ M) (h : ℤ) {w' : ℝ} (hw' : 0 ≤ w') (hw'w : w' < w) :
    ‖pcoeff (fun s : ℝ => G s) h‖ ≤ M * Real.exp (-(2 * Real.pi * w' * |(h : ℝ)|)) :=
  ComplexFlow.norm_fourierCoeff_le_of_strip hG hp hM h hw' hw'w

/-- The weighted exponentials are summable over `ℤ`. -/
theorem summable_pw_mul_exp (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable fun h : ℤ => pw k h * Real.exp (-(a * |(h : ℝ)|)) := by
  have hnat : Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * Real.exp (-(a * ((n : ℝ) + 1))) := by
    have h0 := Real.summable_pow_mul_exp_neg_nat_mul k ha
    have := (summable_nat_add_iff 1).mpr h0
    refine this.congr fun n => ?_
    push_cast
    ring_nf
  have hnat' : Summable fun n : ℕ => pw k n * Real.exp (-(a * |((n : ℤ) : ℝ)|)) := by
    have := hnat.mul_left (Real.exp a)
    refine this.congr fun n => ?_
    simp only [pw, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    · ring
    · ring
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨hnat', ?_⟩
  refine hnat'.congr fun n => ?_
  simp [pw, abs_neg]

/-- **A periodic function holomorphic on a strip is a phase series.** -/
theorem isPS_of_strip {G : ℂ → ℂ} {w : ℝ} (hw : 0 < w)
    (hG : DifferentiableOn ℂ G {z : ℂ | |z.im| < w})
    (hp : ∀ z : ℂ, |z.im| < w → G (z + 1) = G z) :
    IsPS (fun s : ℝ => G s) (pcoeff fun s : ℝ => G s) := by
  have hsub : {z : ℂ | |z.im| ≤ w / 2} ⊆ {z : ℂ | |z.im| < w} := fun z hz => by
    simp only [mem_ofPred_eq] at hz ⊢; linarith
  obtain ⟨M, hM⟩ := exists_bound_strip (hG.continuousOn.mono hsub)
    fun z hz => hp z (hsub hz)
  have hdec : ∀ h : ℤ, ‖pcoeff (fun s : ℝ => G s) h‖ ≤
      M * Real.exp (-(2 * Real.pi * (w / 4) * |(h : ℝ)|)) := by
    intro h
    refine norm_pcoeff_le_of_strip (w := w / 2) (M := M) (hG.mono fun z hz => ?_)
      (fun z hz => hp z ?_) (fun z hz => hM z ?_) h (w' := w / 4) (by positivity) (by linarith)
    · simp only [mem_ofPred_eq] at hz ⊢; linarith
    · linarith
    · exact hz.le
  have hrapid : Rapid (pcoeff fun s : ℝ => G s) := by
    intro k
    have hs := (summable_pw_mul_exp k (a := 2 * Real.pi * (w / 4)) (by positivity)).mul_left M
    refine Summable.of_nonneg_of_le (fun h => mul_nonneg (pw_nonneg k h) (norm_nonneg _))
      (fun h => ?_) hs
    calc pw k h * ‖pcoeff (fun s : ℝ => G s) h‖
        ≤ pw k h * (M * Real.exp (-(2 * Real.pi * (w / 4) * |(h : ℝ)|))) :=
          mul_le_mul_of_nonneg_left (hdec h) (pw_nonneg k h)
      _ = M * (pw k h * Real.exp (-(2 * Real.pi * (w / 4) * |(h : ℝ)|))) := by ring
  have hreal : ∀ s : ℝ, (s : ℂ) ∈ {z : ℂ | |z.im| < w} := fun s => by simpa using hw
  have hcont : Continuous fun s : ℝ => G s :=
    continuous_iff_continuousAt.mpr fun s =>
      ((hG _ (hreal s)).differentiableAt
        ((isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds
          (hreal s))).continuousAt.comp continuous_ofReal.continuousAt
  have hper : Function.Periodic (fun s : ℝ => G s) 1 := fun s => by
    simp only [ofReal_add, ofReal_one]
    exact hp _ (hreal s)
  exact ⟨hrapid, hasSum_pcoeff_of_summable hcont hper hrapid.summable⟩

/-- **The coefficients of a derivative.** -/
theorem pcoeff_deriv {g g' : ℝ → ℂ} (hd : ∀ s, HasDerivAt g (g' s) s) (hc : Continuous g')
    (hp : Function.Periodic g 1) (h : ℤ) :
    pcoeff g' h = 2 * Real.pi * I * h * pcoeff g h := by
  set e : ℝ → ℂ := fun s => Complex.exp (-(2 * Real.pi * I * (h : ℂ) * (s : ℂ))) with he
  have hed : ∀ s, HasDerivAt e (-(2 * Real.pi * I * (h : ℂ)) * e s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -(2 * Real.pi * I * (h : ℂ) * (s : ℂ)))
        (-(2 * Real.pi * I * (h : ℂ))) s := by
      have := ((hasDerivAt_id (s : ℂ)).const_mul (-(2 * Real.pi * I * (h : ℂ)))).comp_ofReal
      simpa [neg_mul] using this
    have := (Complex.hasDerivAt_exp _).comp s h1
    exact this.congr_deriv (by simp only [he]; ring)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
  have hec : Continuous e := by rw [he]; fun_prop
  have hprod : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => g s * e s)
      (g' s * e s + g s * (-(2 * Real.pi * I * (h : ℂ)) * e s)) s :=
    fun s _ => (hd s).mul (hed s)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod
    ((((hc.mul hec).add (hgc.mul (continuous_const.mul hec)))).intervalIntegrable 0 1)
  have hb : g 1 * e 1 - g 0 * e 0 = 0 := by
    have h1 : e 1 = 1 := by
      rw [he]
      simp only [ofReal_one, mul_one]
      rw [show -(2 * (Real.pi : ℂ) * I * (h : ℂ)) = ((-h : ℤ) : ℂ) * (2 * Real.pi * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    have h0 : e 0 = 1 := by rw [he]; simp
    have hg : g 1 = g 0 := by simpa using hp 0
    rw [h1, h0, hg, sub_self]
  rw [hb, intervalIntegral.integral_add (f := fun s => g' s * e s)
    (g := fun s => g s * (-(2 * Real.pi * I * (h : ℂ)) * e s))
    ((hc.mul hec).intervalIntegrable 0 1)
    ((hgc.mul (continuous_const.mul hec)).intervalIntegrable 0 1)] at hint
  unfold pcoeff
  have e2 : ∫ s in (0 : ℝ)..1, g s * (-(2 * Real.pi * I * (h : ℂ)) * e s) =
      -(2 * Real.pi * I * (h : ℂ)) * ∫ s in (0 : ℝ)..1, g s * e s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  rw [e2] at hint
  have : ∫ s in (0 : ℝ)..1, g' s * e s = 2 * Real.pi * I * (h : ℂ) * ∫ s in (0 : ℝ)..1, g s * e s := by
    linear_combination hint
  simpa [he] using this

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: series of mode functions.**
* `measurable_tsum_int`: a pointwise summable series of measurable functions indexed by `ℤ` is
  measurable (limit of the symmetric partial sums);
* `differentiableOn_tsum_of_locBound`: a series of holomorphic functions on an open subset of a
  finite-dimensional complex space with locally summable bounds is holomorphic (derivatives
  dominated by Cauchy's estimate);
* `tsum_exp_conv_le`: the convolution of two exponentially decaying sequences decays at half the
  rate. -/

/-- **Measurability of a series indexed by `ℤ`.** -/
theorem measurable_tsum_int {α : Type*} [MeasurableSpace α] {f : ℤ → α → ℂ}
    (hf : ∀ k, Measurable (f k)) (hs : ∀ a, Summable fun k => f k a) :
    Measurable fun a => ∑' k, f k a := by
  have hlim : ∀ a, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (f n a + f (-(n : ℤ)) a) - f 0 a)
      atTop (𝓝 (∑' k, f k a)) := by
    intro a
    have h1 := ((hs a).hasSum.nat_add_neg).tendsto_sum_nat
    have h2 := h1.sub_const (f 0 a)
    simpa using h2
  refine measurable_of_tendsto_metrizable (fun N => ?_) (tendsto_pi_nhds.mpr hlim)
  exact (Finset.measurable_fun_sum (Finset.range N) fun n _ =>
    (hf (n : ℤ)).add (hf (-(n : ℤ)))).sub (hf 0)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]

omit [FiniteDimensional ℂ X] in
/-- **A locally dominated series of holomorphic functions is holomorphic.** -/
theorem differentiableOn_tsum_of_locBound {ι : Type*} {F : ι → X → ℂ} {U : Set X}
    (hU : IsOpen U) (hd : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ k, ∀ y ∈ V, ‖F k y‖ ≤ u k) :
    DifferentiableOn ℂ (fun y => ∑' k, F k y) U := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  obtain ⟨V, hV, u, hu, hFu⟩ := hb x₀ hx₀
  obtain ⟨ε', hε', hε'V⟩ := Metric.mem_nhds_iff.mp hV
  set ρ : ℝ := min ε ε' / 4 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hcb : closedBall x₀ (3 * ρ) ⊆ U ∩ V := fun x hx => by
    rw [mem_closedBall] at hx
    refine ⟨hεU ?_, hε'V ?_⟩ <;> rw [mem_ball]
    · linarith [min_le_left ε ε']
    · linarith [min_le_right ε ε']
  have hball : ball x₀ ρ ⊆ U := fun x hx =>
    (hcb (mem_closedBall.mpr (by rw [mem_ball] at hx; linarith))).1
  have hder : ∀ k, ∀ x ∈ ball x₀ ρ, ‖fderiv ℂ (F k) x‖ ≤ u k / ρ := by
    intro k x hx
    have hsub : closedBall x ρ ⊆ closedBall x₀ (3 * ρ) := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      rw [mem_ball] at hx
      have := dist_triangle w x x₀
      linarith
    exact GenSem.norm_fderiv_le_of_closedBall hρ ((hd k).mono fun w hw => (hcb (hsub hw)).1)
      fun w hw => hFu k w (hcb (hsub hw)).2
  have hsum0 : Summable fun k => F k x₀ :=
    Summable.of_norm_bounded hu fun k => hFu k x₀ (hcb (mem_closedBall_self (by positivity))).2
  have hD := hasFDerivAt_tsum_of_isPreconnected (u := fun k => u k / ρ) (hu.div_const ρ)
    isOpen_ball (convex_ball x₀ ρ).isPreconnected
    (f' := fun k x => fderiv ℂ (F k) x)
    (fun k x hx => ((hd k) x (hball hx)).differentiableAt (hU.mem_nhds (hball hx)) |>.hasFDerivAt)
    hder (mem_ball_self hρ) hsum0 (mem_ball_self hρ)
  exact hD.differentiableAt.differentiableWithinAt

/-- **The convolution of exponentially decaying sequences.** -/
theorem tsum_exp_conv_le {a : ℝ} (ha : 0 < a) (h : ℤ) :
    ∑' k : ℤ, Real.exp (-(a * |(k : ℝ)|)) * Real.exp (-(a * |((h - k : ℤ) : ℝ)|)) ≤
      (∑' k : ℤ, Real.exp (-(a / 2 * |(k : ℝ)|))) * Real.exp (-(a / 2 * |(h : ℝ)|)) := by
  have hs : Summable fun k : ℤ => Real.exp (-(a / 2 * |(k : ℝ)|)) := by
    have := summable_pw_mul_exp 0 (a := a / 2) (by positivity)
    simpa [pw] using this
  have hterm : ∀ k : ℤ, Real.exp (-(a * |(k : ℝ)|)) * Real.exp (-(a * |((h - k : ℤ) : ℝ)|)) ≤
      Real.exp (-(a / 2 * |(k : ℝ)|)) * Real.exp (-(a / 2 * |(h : ℝ)|)) := by
    intro k
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have htri : |(h : ℝ)| ≤ |(k : ℝ)| + |((h - k : ℤ) : ℝ)| := by
      push_cast
      calc |(h : ℝ)| = |(k : ℝ) + ((h : ℝ) - k)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h0 : 0 ≤ |((h - k : ℤ) : ℝ)| := abs_nonneg _
    nlinarith [abs_nonneg (k : ℝ)]
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum hterm
    (Summable.of_nonneg_of_le (fun k => by positivity) hterm (hs.mul_right _)) (hs.mul_right _)

end AVRegularity.Providers.ComplexContext
end

section
open MeasureTheory Set Filter Topology Metric Homogenization
open scoped ENNReal
namespace AVRegularity.Providers.ComplexContext

/-! **Carrier calculus: the invariants of the induction.** The holomorphic carrier calculus
(`gen_carrier_calculus`) is proved by induction on the generated expression, with one invariant per
sort.
* `CtxInv`: a context extension `F dd n t x` is holomorphic on the outer carrier `𝔇_i(2;𝗉)`,
  measurable in time, equal to the real function at admissible real chains, invariant under the
  real phase translations (`FinalSymm`, `ChildSymm`: `ChainParamsC.shiftFinal`,
  `ChainParamsC.shiftChild` with integer transverse component), locally bounded
  uniformly in time, and its final-phase modes at real final phase are bounded by the majorant.
  Measurability in time is required on the outer carrier only (an extension is set to zero off
  the carrier at the end).
* `FamInv`: a family extension does not depend on the final phase; its values are bounded by the
  zero mode of the majorant.
* `CellInv`: a cell function is a phase series in the transverse internal phase, `∑_h W_h e^{2πihη_q}`,
  with mode extensions `W_h` holomorphic on the carrier, decaying exponentially, locally uniformly
  and uniformly in time, and bounded by the majorant.
The final-phase line `lineF q G x z = G(x + z e_q)` carries the final-phase coefficients
(`finalPhaseCoeff_eq_pcoeff`); at a real final phase of the outer carrier it is holomorphic on the
strip `|Im z| < 7b/2` (`mem_carrierC_line`). -/

open AVRegularity.Providers.ComplexFlow

/-- The type of the extensions: discrete data, number of children, time, parameters. -/
abbrev Ext : Type := ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ

/-- The complex vector `z e_q`. -/
def evec (q : Fin 2) (z : ℂ) : Fin 2 → ℂ := fun a => if a = q then z else 0

/-- The final-phase line through `x` in the direction `e_q`. -/
def lineF {n : ℕ} (q : Fin 2) (G : ChainParamsC n → ℂ) (x : ChainParamsC n) (z : ℂ) : ℂ :=
  G (x.1, x.2.1, x.2.2 + evec q z)

theorem finalPhaseCoeff_eq_pcoeff {n : ℕ} (q : Fin 2) (G : ChainParamsC n → ℂ)
    (x : ChainParamsC n) (h : ℤ) :
    finalPhaseCoeff q G x h = pcoeff (fun s : ℝ => lineF q G x s) h := rfl

/-- A real vector with integer transverse component for the slot `p`. -/
def TInt (p : ℤ) (v : Vec 2) : Prop := ∃ m : ℤ, v (transverseIndex p) = m

/-- Invariance under the final-phase translations with integer transverse component. -/
def FinalSymm (dd : ChainData) {n : ℕ} (G : ChainParamsC n → ℂ) (S : Set (ChainParamsC n)) :
    Prop :=
  ∀ x ∈ S, ∀ v : Vec 2, TInt (dd.slots.getLastD 0) v → G (x.shiftFinal v) = G x

/-- Invariance under the child-phase translations with integer transverse component. -/
def ChildSymm (dd : ChainData) {n : ℕ} (G : ChainParamsC n → ℂ) (S : Set (ChainParamsC n)) :
    Prop :=
  ∀ x ∈ S, ∀ (k : Fin n) (v : Vec 2), TInt (dd.slots.getD k 0) v → G (x.shiftChild k v) = G x

/-- Local boundedness uniformly in time. -/
def LocBdd {n : ℕ} (F : ℝ → ChainParamsC n → ℂ) (T : Set ℝ) (S : Set (ChainParamsC n)) : Prop :=
  ∀ x ∈ S, ∃ U ∈ 𝓝 x, ∃ M : ℝ, ∀ t ∈ T, ∀ y ∈ U, ‖F t y‖ ≤ M

/-- Independence of the final phase. -/
def FinalIndep {n : ℕ} (G : ChainParamsC n → ℂ) : Prop :=
  ∀ (x : ChainParamsC n) (z : Fin 2 → ℂ), G (x.1, x.2.1, z) = G x

/-- Discrete data carried by an admissible chain over the slot `p` of level `i`. -/
def AdmData (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (dd : ChainData) (n : ℕ) : Prop :=
  ∃ ch : RealChain, IsAdmissibleChain D b j₀ i p ch ∧ ch.data = dd ∧ ch.children.length = n

/-- A real final phase. -/
def RealFinal {n : ℕ} (x : ChainParamsC n) : Prop := ∀ a, (x.2.2 a).im = 0

/-! ### The invariants -/

section Inv

variable (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ)

/-- **The invariant of a context expression** with majorant `B mres h t`. -/
structure CtxInv (f : GenSort.Sem .ctx) (F : Ext) (B : ℝ → ℤ → ℝ → ℝ≥0∞) : Prop where
  hol : ∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    DifferentiableOn ℂ (F dd n t) (carrierC D b dd n 2)
  meas : ∀ dd n, ∀ x ∈ carrierC D b dd n 2,
    Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => F dd n t x
  agree : ∀ (ch : RealChain), ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ (ζ : Vec 2),
    IsAdmissibleChain D b j₀ i p ch → F ch.data ch.children.length t (ch.paramsC ζ) = f t ch ζ
  fin : ∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, FinalSymm dd (F dd n t) (carrierC D b dd n 2)
  child : ∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    ChildSymm dd (F dd n t) (carrierC D b dd n 2)
  bdd : ∀ dd n, LocBdd (F dd n) (ocPulseWindow D.α D.q D.Λ i p) (carrierC D b dd n 2)
  mode : ∀ mres : ℝ, 0 ≤ mres → mres ≤ 2 → ∀ (h : ℤ), ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    ∀ dd n, AdmData D b j₀ i p dd n → ∀ x ∈ carrierC D b dd n mres, RealFinal x →
      ‖finalPhaseCoeff (transverseIndex p) (F dd n t) x h‖ₑ ≤ B mres h t

/-- **The invariant of a family expression** with majorant `B mres h t` (only the zero mode
matters). -/
structure FamInv (f : GenSort.Sem .fam) (G : Ext) (B : ℝ → ℤ → ℝ → ℝ≥0∞) : Prop where
  hol : ∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    DifferentiableOn ℂ (G dd n t) (carrierC D b dd n 2)
  meas : ∀ dd n, ∀ x ∈ carrierC D b dd n 2,
    Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => G dd n t x
  indep : ∀ dd n t, FinalIndep (G dd n t)
  agree : ∀ (ch : RealChain), ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    IsAdmissibleChain D b j₀ i p ch → G ch.data ch.children.length t (ch.paramsC 0) = f t ch
  child : ∀ dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    ChildSymm dd (G dd n t) (carrierC D b dd n 2)
  bdd : ∀ dd n, LocBdd (G dd n) (ocPulseWindow D.α D.q D.Λ i p) (carrierC D b dd n 2)
  mode : ∀ mres : ℝ, 0 ≤ mres → mres ≤ 2 → ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    ∀ dd n, AdmData D b j₀ i p dd n → ∀ x ∈ carrierC D b dd n mres,
      ‖G dd n t x‖ₑ ≤ B mres 0 t

/-- **The invariant of a cell expression** with majorant `B mres h t`: a phase series in the
transverse internal phase with mode extensions `W h`. -/
structure CellInv (f : GenSort.Sem .cell) (W : ℤ → Ext) (B : ℝ → ℤ → ℝ → ℝ≥0∞) : Prop where
  hol : ∀ h dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    DifferentiableOn ℂ (W h dd n t) (carrierC D b dd n 2)
  meas : ∀ h dd n, ∀ x ∈ carrierC D b dd n 2,
    Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => W h dd n t x
  indep : ∀ h dd n t, FinalIndep (W h dd n t)
  agree : ∀ (ch : RealChain), ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    IsAdmissibleChain D b j₀ i p ch → ∀ η : Vec 2,
      HasSum (fun h => W h ch.data ch.children.length t (ch.paramsC 0) *
        emode h (η (transverseIndex p))) (f t ch η : ℂ)
  child : ∀ h dd n, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    ChildSymm dd (W h dd n t) (carrierC D b dd n 2)
  decay : ∀ dd n, ∀ x ∈ carrierC D b dd n 2, ∃ U ∈ 𝓝 x, ∃ M w : ℝ, 0 < w ∧
    ∀ (h : ℤ), ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ y ∈ U,
      ‖W h dd n t y‖ ≤ M * Real.exp (-(2 * Real.pi * w * |(h : ℝ)|))
  mode : ∀ mres : ℝ, 0 ≤ mres → mres ≤ 2 → ∀ (h : ℤ), ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p,
    ∀ dd n, AdmData D b j₀ i p dd n → ∀ x ∈ carrierC D b dd n mres,
      ‖W h dd n t x‖ₑ ≤ B mres h t

end Inv

/-! ### The carrier under translations and along the final-phase line -/

section Carrier

variable {D : OCData} {b : ℝ} {dd : ChainData} {n : ℕ} {mres : ℝ}

/-- **The final-phase line stays in the carrier** on the strip of the reserve. -/
theorem mem_carrierC_line {x : ChainParamsC n} (hx : x ∈ carrierC D b dd n mres)
    (hre : (x.2.2 (transverseIndex (dd.slots.getLastD 0))).im = 0) {z : ℂ}
    (hz : |z.im| < (3 + mres / 4) * b) :
    (x.1, x.2.1, x.2.2 + evec (transverseIndex (dd.slots.getLastD 0)) z) ∈
      carrierC D b dd n mres := by
  refine ⟨hx.1, hx.2.1, ?_⟩
  show |((x.2.2 + evec _ z) (transverseIndex (dd.slots.getLastD 0))).im| < _
  simp only [Pi.add_apply, evec, ↓reduceIte, Complex.add_im, hre, zero_add]
  exact hz

theorem carrierC_final_zero {x : ChainParamsC n} (hm : -12 < mres) (hx : x ∈ carrierC D b dd n mres)
    (hb : 0 < b) : (x.1, x.2.1, (0 : Fin 2 → ℂ)) ∈ carrierC D b dd n mres := by
  refine ⟨hx.1, hx.2.1, ?_⟩
  show |((0 : Fin 2 → ℂ) _).im| < _
  simp only [Pi.zero_apply, Complex.zero_im, abs_zero]
  have : 0 < 3 + mres / 4 := by linarith
  positivity

end Carrier

/-- The slot of admissible data is the slot of the expression. -/
theorem AdmData.lastSlot {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ} {dd : ChainData} {n : ℕ}
    (h : AdmData D b j₀ i p dd n) : dd.slots.getLastD 0 = p := by
  obtain ⟨ch, hch, hd, -⟩ := h
  rw [← hd]
  exact hch.2.2.2.1

/-- The pointwise mode bound from the bound on the mode supremum. -/
theorem le_ctxModeSupAt {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ} {F : Ext} {mres : ℝ} {h : ℤ}
    {t : ℝ} {dd : ChainData} {n : ℕ} (hdd : AdmData D b j₀ i p dd n) {x : ChainParamsC n}
    (hx : x ∈ carrierC D b dd n mres) (hre : RealFinal x) :
    ‖finalPhaseCoeff (transverseIndex p) (F dd n t) x h‖ₑ ≤ ctxModeSupAt D b j₀ i p F mres h t := by
  unfold ctxModeSupAt
  exact le_iSup₂_of_le dd n (le_iSup_of_le hdd (le_iSup₂_of_le x hx (le_iSup_of_le hre le_rfl)))

/-- The mode supremum is bounded by a pointwise bound. -/
theorem ctxModeSupAt_le {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ} {F : Ext} {mres : ℝ} {h : ℤ}
    {t : ℝ} {B : ℝ≥0∞}
    (hB : ∀ dd n, AdmData D b j₀ i p dd n → ∀ x ∈ carrierC D b dd n mres, RealFinal x →
      ‖finalPhaseCoeff (transverseIndex p) (F dd n t) x h‖ₑ ≤ B) :
    ctxModeSupAt D b j₀ i p F mres h t ≤ B := by
  unfold ctxModeSupAt
  exact iSup₂_le fun dd n => iSup_le fun hdd => iSup₂_le fun x hx => iSup_le fun hre =>
    hB dd n hdd x hx hre

end AVRegularity.Providers.ComplexContext
end
