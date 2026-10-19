-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.AmplitudeLimit
public import AVRegularity.CycleWords.Assembly.MixedWordsB1Statements
import AVRegularity.CycleWords.MixedWords.AdjointExists
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

@[expose] public noncomputable section

section
open Homogenization Set Filter Topology AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! Extension by zero of the inverse-gauged amplitudes across a strict support quiet margin. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cosine component of the inverse-gauged pair, extended by zero outside the analytic disc. -/
def factorGaugeCos (η ξ0 : ℝ) (Φ : Vec 2 → ℂ) (C S : Vec 2 → E) : Vec 2 → E :=
  {θ | fibreNorm (planeFibreFrequency η θ) < ξ0}.indicator
    (fun θ => (Complex.exp (-Φ θ)).re • C θ + (Complex.exp (-Φ θ)).im • S θ)

/-- The sine component of the inverse-gauged pair, extended by zero outside the analytic disc. -/
def factorGaugeSin (η ξ0 : ℝ) (Φ : Vec 2 → ℂ) (C S : Vec 2 → E) : Vec 2 → E :=
  {θ | fibreNorm (planeFibreFrequency η θ) < ξ0}.indicator
    (fun θ => (Complex.exp (-Φ θ)).re • S θ - (Complex.exp (-Φ θ)).im • C θ)

private theorem factorGauge_zero_near {η ξ0 ρ : ℝ} (Φ : Vec 2 → ℂ)
    {C S : Vec 2 → E} (hs : ∀ θ, ρ < fibreNorm (planeFibreFrequency η θ) → C θ = 0 ∧ S θ = 0)
    {θ : Vec 2} (hθ : ρ < fibreNorm (planeFibreFrequency η θ)) :
    factorGaugeCos η ξ0 Φ C S =ᶠ[𝓝 θ] 0 ∧ factorGaugeSin η ξ0 Φ C S =ᶠ[𝓝 θ] 0 := by
  have hV : IsOpen {z | ρ < fibreNorm (planeFibreFrequency η z)} :=
    isOpen_lt continuous_const (continuous_fibreNorm_planeFibreFrequency η)
  have hmem : θ ∈ {z | ρ < fibreNorm (planeFibreFrequency η z)} := hθ
  have hz : ∀ᶠ z in 𝓝 θ,
      factorGaugeCos η ξ0 Φ C S z = 0 ∧ factorGaugeSin η ξ0 Φ C S z = 0 := by
    filter_upwards [hV.mem_nhds hmem] with z hz
    obtain ⟨hc, hs'⟩ := hs z hz
    by_cases hu : fibreNorm (planeFibreFrequency η z) < ξ0
    · have huSet : z ∈ {θ | fibreNorm (planeFibreFrequency η θ) < ξ0} := hu
      simp only [factorGaugeCos, factorGaugeSin, indicator_of_mem huSet, hc, hs', smul_zero,
        add_zero, sub_zero, and_self]
    · have huSet : z ∉ {θ | fibreNorm (planeFibreFrequency η θ) < ξ0} := hu
      simp only [factorGaugeCos, factorGaugeSin, indicator_of_notMem huSet, and_self]
  exact ⟨hz.mono (fun _ h => h.1), hz.mono (fun _ h => h.2)⟩

/-- The support quiet margin makes both inverse-gauged amplitudes globally smooth. -/
theorem factorGauge_contDiff {η ξ0 ρ : ℝ} (hρ : ρ < ξ0) {m : ℕ} {Φ : Vec 2 → ℂ}
    (hΦ : ContDiffOn ℝ m (fun θ => Complex.exp (-Φ θ))
      {θ | fibreNorm (planeFibreFrequency η θ) < ξ0})
    {C S : Vec 2 → E} (hC : ContDiff ℝ m C) (hS : ContDiff ℝ m S)
    (hs : ∀ θ, ρ < fibreNorm (planeFibreFrequency η θ) → C θ = 0 ∧ S θ = 0) :
    ContDiff ℝ m (factorGaugeCos η ξ0 Φ C S) ∧ ContDiff ℝ m (factorGaugeSin η ξ0 Φ C S) := by
  have hU : IsOpen {θ | fibreNorm (planeFibreFrequency η θ) < ξ0} :=
    isOpen_lt (continuous_fibreNorm_planeFibreFrequency η) continuous_const
  have hc := Complex.reCLM.contDiff.comp_contDiffOn hΦ
  have hs' := Complex.imCLM.contDiff.comp_contDiffOn hΦ
  constructor <;> apply contDiff_iff_contDiffAt.mpr <;> intro θ
  · by_cases hθ : fibreNorm (planeFibreFrequency η θ) < ξ0
    · apply (((hc θ hθ).contDiffAt (hU.mem_nhds hθ)).smul hC.contDiffAt |>.add
        (((hs' θ hθ).contDiffAt (hU.mem_nhds hθ)).smul hS.contDiffAt)).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hθ] with z hz
      simpa only [factorGaugeCos, factorGaugeSin, Pi.smul_apply', Function.comp_apply,
        Complex.reCLM_apply, Complex.imCLM_apply] using
        indicator_of_mem (show z ∈ {θ | fibreNorm (planeFibreFrequency η θ) < ξ0} from hz) _
    · exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq (factorGauge_zero_near Φ hs (hρ.trans_le (le_of_not_gt hθ))).1
  · by_cases hθ : fibreNorm (planeFibreFrequency η θ) < ξ0
    · apply (((hc θ hθ).contDiffAt (hU.mem_nhds hθ)).smul hS.contDiffAt |>.sub
        (((hs' θ hθ).contDiffAt (hU.mem_nhds hθ)).smul hC.contDiffAt)).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hθ] with z hz
      simpa only [factorGaugeCos, factorGaugeSin, Pi.smul_apply', Function.comp_apply,
        Complex.reCLM_apply, Complex.imCLM_apply] using
        indicator_of_mem (show z ∈ {θ | fibreNorm (planeFibreFrequency η θ) < ξ0} from hz) _
    · exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq (factorGauge_zero_near Φ hs (hρ.trans_le (le_of_not_gt hθ))).2

/-- Multiplication by the forward gauge recovers the original amplitudes on the analytic disc. -/
theorem factorGauge_rotation (η ξ0 : ℝ) (Φ : Vec 2 → ℂ) (C S : Vec 2 → E) {θ : Vec 2}
    (hθ : fibreNorm (planeFibreFrequency η θ) < ξ0) :
    C θ = (Complex.exp (Φ θ)).re • factorGaugeCos η ξ0 Φ C S θ +
      (Complex.exp (Φ θ)).im • factorGaugeSin η ξ0 Φ C S θ ∧
    S θ = (Complex.exp (Φ θ)).re • factorGaugeSin η ξ0 Φ C S θ -
      (Complex.exp (Φ θ)).im • factorGaugeCos η ξ0 Φ C S θ := by
  have hp : Complex.exp (Φ θ) * Complex.exp (-Φ θ) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hr := congrArg Complex.re hp
  have hi := congrArg Complex.im hp
  simp only [Complex.mul_re, Complex.one_re] at hr
  simp only [Complex.mul_im, Complex.one_im] at hi
  simp only [factorGaugeCos, factorGaugeSin,
    indicator_of_mem (show θ ∈ {z | fibreNorm (planeFibreFrequency η z) < ξ0} from hθ)]
  constructor
  · symm
    calc _ = ((Complex.exp (Φ θ)).re * (Complex.exp (-Φ θ)).re -
          (Complex.exp (Φ θ)).im * (Complex.exp (-Φ θ)).im) • C θ +
        ((Complex.exp (Φ θ)).re * (Complex.exp (-Φ θ)).im +
          (Complex.exp (Φ θ)).im * (Complex.exp (-Φ θ)).re) • S θ := by module
      _ = C θ := by rw [hr, hi, one_smul, zero_smul, add_zero]
  · symm
    calc _ = ((Complex.exp (Φ θ)).re * (Complex.exp (-Φ θ)).re -
          (Complex.exp (Φ θ)).im * (Complex.exp (-Φ θ)).im) • S θ -
        ((Complex.exp (Φ θ)).re * (Complex.exp (-Φ θ)).im +
          (Complex.exp (Φ θ)).im * (Complex.exp (-Φ θ)).re) • C θ := by module
      _ = S θ := by rw [hr, hi, one_smul, zero_smul, sub_zero]

/-- Beyond the cutoff support every derivative of the extended gauge pair vanishes. -/
theorem factorGauge_jets_zero {η ξ0 ρ : ℝ} (Φ : Vec 2 → ℂ)
    {C S : Vec 2 → E} (hs : ∀ θ, ρ < fibreNorm (planeFibreFrequency η θ) → C θ = 0 ∧ S θ = 0)
    {θ : Vec 2} (hθ : ρ < fibreNorm (planeFibreFrequency η θ)) (k : ℕ) :
    iteratedFDeriv ℝ k (factorGaugeCos η ξ0 Φ C S) θ = 0 ∧
      iteratedFDeriv ℝ k (factorGaugeSin η ξ0 Φ C S) θ = 0 := by
  have hzero := factorGauge_zero_near (ξ0 := ξ0) Φ hs hθ
  have hc := (hzero.1.iteratedFDeriv ℝ k).eq_of_nhds
  have hs' := (hzero.2.iteratedFDeriv ℝ k).eq_of_nhds
  simpa only [iteratedFDeriv_zero, Pi.zero_apply] using And.intro hc hs'

end AVRegularity.CycleWords.Assembly
end

section
open Homogenization Set Filter AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! Restoring a cutoff inside a derivative by multiplying with a sufficiently high cutoff power. -/

private theorem factorReciprocalJet (i : ℕ) {a : ℝ} (ha : a ≠ 0) :
    ‖iteratedFDerivWithin ℝ i (fun x : ℝ => x⁻¹) {x | x ≠ 0} a‖ =
      (i.factorial : ℝ) / |a| ^ (i + 1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have ht : IsOpen {x : ℝ | x ≠ 0} := isOpen_ne
  have he := iteratedDerivWithin_one_div (𝕜 := ℝ) i ht ha
  simp only [one_div] at he
  rw [he, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _), abs_zpow]
  rw [show (-1 - (i : ℤ)) = -((i + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- A normalized reciprocal derivative costs one more inverse cutoff power than its order. -/
theorem factorReciprocal_normalized_jet_le {χ : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {θ : Vec 2} (hθ : χ θ ≠ 0)
    {w H : ℝ} (hw : 0 < w) (hH : 1 ≤ H) (hval : |χ θ| ≤ H) (k : ℕ)
    (hjet : ∀ i ≤ k, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H) :
    w ^ k * |χ θ| ^ (k + 1) * ‖iteratedFDeriv ℝ k (fun z => (χ z)⁻¹) θ‖ ≤
      (k.factorial : ℝ) ^ 2 * H ^ (2 * k) := by
  let U : Set (Vec 2) := {z | χ z ≠ 0}
  let T : Set ℝ := {x | x ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage hχ.continuous
  have hT : IsOpen T := isOpen_ne
  have ha : 0 < |χ θ| := abs_pos.mpr hθ
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hInv : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => x⁻¹) T :=
    contDiff_id.contDiffOn.inv (fun _ hx => hx)
  have hOuter (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDerivWithin ℝ i (fun x : ℝ => x⁻¹) T (χ θ)‖ ≤
        (k.factorial : ℝ) * H ^ k / |χ θ| ^ (k + 1) := by
    rw [factorReciprocalJet i hθ]
    apply (div_le_div_iff₀ (pow_pos ha _) (pow_pos ha _)).mpr
    have hf : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
    have hp : |χ θ| ^ (k - i) ≤ H ^ k :=
      (pow_le_pow_left₀ ha.le hval _).trans (pow_le_pow_right₀ hH (Nat.sub_le _ _))
    calc (i.factorial : ℝ) * |χ θ| ^ (k + 1) =
          ((i.factorial : ℝ) * |χ θ| ^ (k - i)) * |χ θ| ^ (i + 1) := by
            rw [mul_assoc, ← pow_add, show k - i + (i + 1) = k + 1 by omega]
      _ ≤ ((k.factorial : ℝ) * H ^ k) * |χ θ| ^ (i + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hf hp (by positivity) (by positivity)) (by positivity)
  have hInner (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      ‖iteratedFDerivWithin ℝ i χ U θ‖ ≤ (H / w) ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hU hθ, div_pow]
    apply (le_div_iff₀ (pow_pos hw _)).mpr
    rw [mul_comm]
    exact (hjet i hik).trans (le_self_pow₀ hH (by omega))
  have hc := norm_iteratedFDerivWithin_comp_le (n := k) hInv hχ.contDiffOn
    (by exact_mod_cast le_top) hT.uniqueDiffOn hU.uniqueDiffOn (fun _ hz => hz) hθ hOuter hInner
  rw [iteratedFDerivWithin_of_isOpen k hU hθ] at hc
  change ‖iteratedFDeriv ℝ k (fun z => (χ z)⁻¹) θ‖ ≤ _ at hc
  refine (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ w ^ k * |χ θ| ^ (k + 1))).trans
    (le_of_eq ?_)
  rw [div_pow, show 2 * k = k + k by omega, pow_add]
  field_simp [hw.ne', ha.ne']
  ring

/-- A high cutoff power restores the cutoff inside all full derivatives of the datum. -/
theorem factorCutoffSpan_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (θ : Vec 2) {w H : ℝ} (hw : 0 < w) (hH : 1 ≤ H)
    (hval : |χ θ| ≤ H) (n k : ℕ) (hk : k ≤ n)
    (hjet : ∀ i ≤ k, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H) :
    w ^ k * |χ θ| ^ (n + 1) * ‖iteratedFDeriv ℝ k f θ‖ ≤
      ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * (l.factorial : ℝ) ^ 2 * H ^ (n + l) *
        (w ^ (k - l) * ‖iteratedFDeriv ℝ (k - l) (fun z => χ z • f z) θ‖) := by
  by_cases hθ : χ θ = 0
  · rw [hθ, abs_zero, zero_pow (by omega), mul_zero, zero_mul]
    exact Finset.sum_nonneg (fun l _ => by positivity)
  let U : Set (Vec 2) := {z | χ z ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage hχ.continuous
  have hχi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (χ z)⁻¹) U :=
    hχ.contDiffOn.inv (fun _ hz => hz)
  have heq : EqOn f (fun z => (χ z)⁻¹ • (χ z • f z)) U := by
    intro z hz
    change f z = (χ z)⁻¹ • (χ z • f z)
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
  have hb : ‖iteratedFDeriv ℝ k f θ‖ ≤
      ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l (fun z => (χ z)⁻¹) θ‖ *
          ‖iteratedFDeriv ℝ (k - l) (fun z => χ z • f z) θ‖ := by
    rw [← iteratedFDerivWithin_of_isOpen k hU hθ,
      iteratedFDerivWithin_congr heq hθ]
    have hp := norm_iteratedFDerivWithin_smul_le (g := fun z => χ z • f z)
      hχi (hχ.smul hf).contDiffOn hU.uniqueDiffOn hθ
      (n := k) (by exact_mod_cast le_top)
    simpa only [iteratedFDerivWithin_of_isOpen _ hU hθ, Pi.smul_apply] using hp
  refine (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ w ^ k * |χ θ| ^ (n + 1))).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hlw : w ^ k = w ^ l * w ^ (k - l) := by rw [← pow_add, Nat.add_sub_of_le hlk]
  have hla : |χ θ| ^ (n + 1) = |χ θ| ^ (l + 1) * |χ θ| ^ (n - l) := by
    rw [← pow_add, show l + 1 + (n - l) = n + 1 by omega]
  have hinv := factorReciprocal_normalized_jet_le hχ hθ hw hH hval l
    (fun i hi => hjet i (hi.trans hlk))
  have ha : |χ θ| ^ (n - l) ≤ H ^ (n - l) := pow_le_pow_left₀ (abs_nonneg _) hval _
  calc w ^ k * |χ θ| ^ (n + 1) * ((k.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l (fun z => (χ z)⁻¹) θ‖ *
          ‖iteratedFDeriv ℝ (k - l) (fun z => χ z • f z) θ‖) =
        (k.choose l : ℝ) *
          (w ^ l * |χ θ| ^ (l + 1) * ‖iteratedFDeriv ℝ l (fun z => (χ z)⁻¹) θ‖) *
          |χ θ| ^ (n - l) * (w ^ (k - l) * ‖iteratedFDeriv ℝ (k - l) (fun z => χ z • f z) θ‖) := by
            rw [hlw, hla]
            ring
    _ ≤ (k.choose l : ℝ) * ((l.factorial : ℝ) ^ 2 * H ^ (2 * l)) * H ^ (n - l) *
        (w ^ (k - l) * ‖iteratedFDeriv ℝ (k - l) (fun z => χ z • f z) θ‖) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)) ha
            (by positivity) (by positivity)
    _ = _ := by
      rw [show H ^ (n + l) = H ^ (2 * l) * H ^ (n - l) by
        rw [← pow_add, show 2 * l + (n - l) = n + l by omega]]
      ring

/-- The full cutoff span estimate in the sorted mixed partials used by the Bloch norm. -/
theorem factorCutoffSpan_partials (n : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : Vec 2 → ℝ) (f : Vec 2 → E), ContDiff ℝ (⊤ : ℕ∞) χ →
    ContDiff ℝ (⊤ : ℕ∞) f → ∀ (θ : Vec 2) {w : ℝ}, 0 < w → |χ θ| ≤ H →
    (∀ i ≤ n, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H) → ∀ k ≤ n,
    w ^ k * |χ θ| ^ (n + 1) * ‖iteratedFDeriv ℝ k f θ‖ ≤
      C * ∑ α ∈ momentIndices n, w ^ (α.1 + α.2) *
        ‖thetaPartial α.1 α.2 (fun z => χ z • f z) θ‖ := by
  let c : ℕ → ℕ → ℝ := fun k l => (k.choose l : ℝ) * (l.factorial : ℝ) ^ 2 * H ^ (n + l)
  let A : ℝ := ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (k + 1), c k l
  have hc (k l : ℕ) : 0 ≤ c k l := by dsimp [c]; positivity
  have hA : 0 ≤ A := Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => hc k l))
  let C : ℝ := 1 + ((n + 1 : ℕ) : ℝ) ^ 3 * A * 2 ^ n
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro E _ _ χ f hχ hf θ w hw hval hjet k hk
  let X : Vec 2 → E := fun z => χ z • f z
  have hX : ContDiff ℝ (⊤ : ℕ∞) X := hχ.smul hf
  let T : ℝ := ∑ α ∈ momentIndices n, w ^ (α.1 + α.2) * ‖thetaPartial α.1 α.2 X θ‖
  have hT : 0 ≤ T := Finset.sum_nonneg (fun α _ => by positivity)
  have hcoord (j : ℕ) (hj : j ≤ n) (a : ℕ) (ha : a ≤ j) :
      w ^ j * ‖thetaPartial a (j - a) X θ‖ ≤ T := by
    have hm : (a, j - a) ∈ momentIndices n := by
      simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    have he : a + (j - a) = j := Nat.add_sub_of_le ha
    simpa only [he] using Finset.single_le_sum
      (f := fun α : ℕ × ℕ => w ^ (α.1 + α.2) * ‖thetaPartial α.1 α.2 X θ‖)
      (fun α _ => by positivity) hm
  have hfull (j : ℕ) (hj : j ≤ n) :
      w ^ j * ‖iteratedFDeriv ℝ j X θ‖ ≤ 2 ^ n * ((n + 1 : ℕ) : ℝ) * T := by
    have hs := norm_iteratedFDeriv_le_sum_thetaPartial
      (hX.of_le (by exact_mod_cast le_top) : ContDiff ℝ j X) θ
    have ht : ∑ a ∈ Finset.range (j + 1), w ^ j * ‖thetaPartial a (j - a) X θ‖ ≤
        ((n + 1 : ℕ) : ℝ) * T := by
      calc _ ≤ ∑ _a ∈ Finset.range (j + 1), T :=
          Finset.sum_le_sum (fun a ha => hcoord j hj a (by have := Finset.mem_range.mp ha; omega))
        _ = ((j + 1 : ℕ) : ℝ) * T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ((n + 1 : ℕ) : ℝ) * T := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hj 1) hT
    calc w ^ j * ‖iteratedFDeriv ℝ j X θ‖ ≤
          w ^ j * (2 ^ j * ∑ a ∈ Finset.range (j + 1), ‖thetaPartial a (j - a) X θ‖) :=
            mul_le_mul_of_nonneg_left hs (pow_nonneg hw.le _)
      _ = 2 ^ j * ∑ a ∈ Finset.range (j + 1), w ^ j * ‖thetaPartial a (j - a) X θ‖ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ 2 ^ n * (((n + 1 : ℕ) : ℝ) * T) :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hj) ht
          (Finset.sum_nonneg (fun a _ => by positivity)) (by positivity)
      _ = _ := by ring
  have hcoeff (l : ℕ) (hl : l ≤ k) : c k l ≤ A := by
    refine (Finset.single_le_sum (s := Finset.range (k + 1)) (a := l) (f := c k) (fun l _ => hc k l)
      (Finset.mem_range.mpr (by omega))).trans ?_
    exact Finset.single_le_sum (s := Finset.range (n + 1)) (a := k)
      (f := fun k => ∑ l ∈ Finset.range (k + 1), c k l)
      (fun k _ => Finset.sum_nonneg (fun l _ => hc k l)) (Finset.mem_range.mpr (by omega))
  have hs := factorCutoffSpan_full hχ hf θ hw hH hval n k hk (fun i hi => hjet i (hi.trans hk))
  refine hs.trans ?_
  calc (∑ l ∈ Finset.range (k + 1), c k l *
          (w ^ (k - l) * ‖iteratedFDeriv ℝ (k - l) X θ‖)) ≤
        ∑ _l ∈ Finset.range (k + 1), A * (2 ^ n * ((n + 1 : ℕ) : ℝ) * T) := by
          apply Finset.sum_le_sum
          intro l hl
          exact mul_le_mul (hcoeff l (by have := Finset.mem_range.mp hl; omega))
            (hfull (k - l) ((Nat.sub_le _ _).trans hk)) (by positivity) hA
    _ ≤ ((n + 1 : ℕ) : ℝ) * (A * (2 ^ n * ((n + 1 : ℕ) : ℝ) * T)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hk 1) (by positivity)
    _ ≤ C * T := by
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hp : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 3 := pow_le_pow_right₀ hn (by norm_num)
      calc _ = (((n + 1 : ℕ) : ℝ) ^ 2 * A * 2 ^ n) * T := by ring
        _ ≤ (((n + 1 : ℕ) : ℝ) ^ 3 * A * 2 ^ n) * T :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hp hA) (by positivity)) hT
        _ ≤ C * T := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hT

end AVRegularity.CycleWords.Assembly
end

section
open Homogenization Set AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! Normalized jets of high cutoff powers retain the unused cutoff factors. -/

/-- A finite list of globally bounded jets admits one bound, at least one. -/
theorem factorCutoff_finite_jet_bound {χ : Vec 2 → ℝ}
    (hχ : ∀ i : ℕ, ∃ B : ℝ, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ B) (m : ℕ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ i ≤ m, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ H := by
  choose B hB using hχ
  refine ⟨1 + ∑ i ∈ Finset.range (m + 1), max (B i) 0, ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => le_max_right _ _))
  · intro i hi θ
    refine (hB i θ).trans ((le_max_left (B i) 0).trans ?_)
    exact (Finset.single_le_sum (f := fun i => max (B i) 0)
      (fun i _ => le_max_right _ _) (Finset.mem_range.mpr (by omega))).trans
        (le_add_of_nonneg_left zero_le_one)

/-- The normalized derivative of a high cutoff power retains every undifferentiated factor. -/
theorem factorCutoffPower_normalized_jet_le {χ : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (θ : Vec 2) {w H : ℝ} (hw : 0 < w) (hH : 1 ≤ H)
    (hval : |χ θ| ≤ H) (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N)
    (hjet : ∀ i ≤ k, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H) :
    w ^ k * ‖iteratedFDeriv ℝ k (fun z => χ z ^ N) θ‖ ≤
      (k.factorial : ℝ) * (N : ℝ) ^ k * H ^ (2 * k) * |χ θ| ^ (N - k) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hOuter (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (fun x : ℝ => x ^ N) (χ θ)‖ ≤
        (N : ℝ) ^ k * H ^ k * |χ θ| ^ (N - k) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_pow, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
    have hd : (N.descFactorial i : ℝ) ≤ (N : ℝ) ^ k := by
      exact (by exact_mod_cast Nat.descFactorial_le_pow N i : (N.descFactorial i : ℝ) ≤ (N : ℝ) ^ i).trans
        (pow_le_pow_right₀ (by exact_mod_cast hN) hi)
    have hp : |χ θ| ^ (k - i) ≤ H ^ k :=
      (pow_le_pow_left₀ (abs_nonneg _) hval _).trans (pow_le_pow_right₀ hH (Nat.sub_le _ _))
    rw [show N - i = (k - i) + (N - k) by omega, pow_add]
    calc (N.descFactorial i : ℝ) * (|χ θ| ^ (k - i) * |χ θ| ^ (N - k)) =
          ((N.descFactorial i : ℝ) * |χ θ| ^ (k - i)) * |χ θ| ^ (N - k) := by ring
      _ ≤ ((N : ℝ) ^ k * H ^ k) * |χ θ| ^ (N - k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hd hp (by positivity) (by positivity)) (by positivity)
  have hInner (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) : ‖iteratedFDeriv ℝ i χ θ‖ ≤ (H / w) ^ i := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hw _)).mpr
    rw [mul_comm]
    exact (hjet i hik).trans (le_self_pow₀ hH (by omega))
  have hc := norm_iteratedFDeriv_comp_le (n := k) (contDiff_id.pow N) hχ
    (by exact_mod_cast le_top) θ hOuter hInner
  change ‖iteratedFDeriv ℝ k (fun z => χ z ^ N) θ‖ ≤ _ at hc
  refine (mul_le_mul_of_nonneg_left hc (pow_nonneg hw.le _)).trans (le_of_eq ?_)
  rw [div_pow, show 2 * k = k + k by omega, pow_add]
  field_simp [hw.ne']

/-- Multiplying by another smooth cutoff preserves the unused high-power cutoff factors. -/
theorem factorCutoffProduct_normalized_jet_le {χ ψ : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (θ : Vec 2) {w H : ℝ} (hw : 0 < w) (hH : 1 ≤ H) (hval : |χ θ| ≤ H)
    (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N)
    (hχjet : ∀ i ≤ k, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H)
    (hψjet : ∀ i ≤ k, w ^ i * ‖iteratedFDeriv ℝ i ψ θ‖ ≤ H) :
    w ^ k * ‖iteratedFDeriv ℝ k (fun z => χ z ^ N * ψ z) θ‖ ≤
      (∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * (l.factorial : ℝ) *
        (N : ℝ) ^ l * H ^ (k + l + 1)) * |χ θ| ^ (N - k) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hc := norm_iteratedFDeriv_mul_le (hχ.pow N) hψ θ (n := k) (by exact_mod_cast le_top)
  refine (mul_le_mul_of_nonneg_left hc (pow_nonneg hw.le _)).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l hl
  have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hp := factorCutoffPower_normalized_jet_le hχ θ hw hH hval N l hN (hlk.trans hk)
    (fun i hi => hχjet i (hi.trans hlk))
  have hq := hψjet (k - l) (Nat.sub_le _ _)
  have ha : |χ θ| ^ (k - l) ≤ H ^ (k - l) := pow_le_pow_left₀ (abs_nonneg _) hval _
  have hwk : w ^ k = w ^ l * w ^ (k - l) := by rw [← pow_add, Nat.add_sub_of_le hlk]
  calc w ^ k * ((k.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun z => χ z ^ N) θ‖ *
        ‖iteratedFDeriv ℝ (k - l) ψ θ‖) =
      (k.choose l : ℝ) * (w ^ l * ‖iteratedFDeriv ℝ l (fun z => χ z ^ N) θ‖) *
        (w ^ (k - l) * ‖iteratedFDeriv ℝ (k - l) ψ θ‖) := by
          rw [hwk]
          ring
    _ ≤ (k.choose l : ℝ) *
        ((l.factorial : ℝ) * (N : ℝ) ^ l * H ^ (2 * l) * |χ θ| ^ (N - l)) * H :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)) hq (by positivity) (by positivity)
    _ = ((k.choose l : ℝ) * (l.factorial : ℝ) * (N : ℝ) ^ l * H ^ (2 * l) * H) *
        |χ θ| ^ (k - l) * |χ θ| ^ (N - k) := by
      rw [show N - l = (k - l) + (N - k) by omega, pow_add]
      ring
    _ ≤ ((k.choose l : ℝ) * (l.factorial : ℝ) * (N : ℝ) ^ l * H ^ (2 * l) * H) *
        H ^ (k - l) * |χ θ| ^ (N - k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by
      rw [show H ^ (k + l + 1) = H ^ (2 * l) * H * H ^ (k - l) by
        rw [← pow_succ, ← pow_add, show 2 * l + 1 + (k - l) = k + l + 1 by omega]]
      ring

/-- One constant controls all retained-power product jets up to the prescribed order. -/
theorem factorCutoffProduct_uniform (N m : ℕ) (hN : 1 ≤ N) (hmN : m ≤ N)
    {H : ℝ} (hH : 1 ≤ H) : ∃ C : ℝ, 0 < C ∧
    ∀ (χ ψ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → ContDiff ℝ (⊤ : ℕ∞) ψ →
    ∀ θ {w : ℝ}, 0 < w → |χ θ| ≤ H →
    (∀ i ≤ m, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H) →
    (∀ i ≤ m, w ^ i * ‖iteratedFDeriv ℝ i ψ θ‖ ≤ H) → ∀ k ≤ m,
    w ^ k * ‖iteratedFDeriv ℝ k (fun z => χ z ^ N * ψ z) θ‖ ≤ C * |χ θ| ^ (N - k) := by
  let c : ℕ → ℕ → ℝ := fun k l => (k.choose l : ℝ) * (l.factorial : ℝ) *
    (N : ℝ) ^ l * H ^ (k + l + 1)
  have hc (k l : ℕ) : 0 ≤ c k l := by dsimp [c]; positivity
  let C : ℝ := 1 + ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (k + 1), c k l
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro χ ψ hχ hψ θ w hw hval hχj hψj k hk
  refine (factorCutoffProduct_normalized_jet_le hχ hψ θ hw hH hval N k hN (hk.trans hmN)
    (fun i hi => hχj i (hi.trans hk)) (fun i hi => hψj i (hi.trans hk))).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (Finset.single_le_sum (s := Finset.range (m + 1)) (a := k)
    (f := fun k => ∑ l ∈ Finset.range (k + 1), c k l)
    (fun k _ => Finset.sum_nonneg (fun l _ => hc k l))
    (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)

/-- A dilation is harmless for normalized cutoff jets when its normalized scale is at most one. -/
theorem factorCutoff_scaled_normalized_jet_le {χ : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {H : ℝ} (hH : 0 ≤ H) {m : ℕ}
    (hb : ∀ i ≤ m, ∀ θ, ‖iteratedFDeriv ℝ i χ θ‖ ≤ H)
    {w a : ℝ} (hw : 0 ≤ w) (hscale : w * |a| ≤ 1) (θ : Vec 2) {k : ℕ} (hk : k ≤ m) :
    w ^ k * ‖iteratedFDeriv ℝ k (fun z => χ (a • z)) θ‖ ≤ H := by
  calc w ^ k * ‖iteratedFDeriv ℝ k (fun z => χ (a • z)) θ‖ ≤
        w ^ k * (‖iteratedFDeriv ℝ k χ (a • θ)‖ * |a| ^ k) :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_scaled_le hχ a k θ) (pow_nonneg hw _)
    _ ≤ w ^ k * (H * |a| ^ k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb k hk _) (pow_nonneg (abs_nonneg _) _))
        (pow_nonneg hw _)
    _ = H * (w * |a|) ^ k := by rw [mul_pow]; ring
    _ ≤ H * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) hscale) hH
    _ = H := mul_one _

/-- A product of two normalized jet bounds has an order-only loss. -/
theorem factorCutoff_mul_normalized_jet_le {χ ψ : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {m : ℕ} {w H : ℝ} (hw : 0 ≤ w) (hH : 0 ≤ H) (θ : Vec 2)
    (hχj : ∀ i ≤ m, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H)
    (hψj : ∀ i ≤ m, w ^ i * ‖iteratedFDeriv ℝ i ψ θ‖ ≤ H) {k : ℕ} (hk : k ≤ m) :
    w ^ k * ‖iteratedFDeriv ℝ k (fun z => χ z * ψ z) θ‖ ≤ 2 ^ m * H ^ 2 := by
  refine (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_mul_le hχ hψ θ (n := k) (by exact_mod_cast le_top))
    (pow_nonneg hw _)).trans ?_
  rw [Finset.mul_sum]
  calc
    (∑ l ∈ Finset.range (k + 1), w ^ k * ((k.choose l : ℝ) *
          ‖iteratedFDeriv ℝ l χ θ‖ * ‖iteratedFDeriv ℝ (k - l) ψ θ‖)) ≤
        ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * H ^ 2 := by
      apply Finset.sum_le_sum
      intro l hl
      have hlk : l ≤ k := by have := Finset.mem_range.mp hl; omega
      have he : w ^ k = w ^ l * w ^ (k - l) := by rw [← pow_add, Nat.add_sub_of_le hlk]
      calc _ = (k.choose l : ℝ) * (w ^ l * ‖iteratedFDeriv ℝ l χ θ‖) *
            (w ^ (k - l) * ‖iteratedFDeriv ℝ (k - l) ψ θ‖) := by rw [he]; ring
        _ ≤ (k.choose l : ℝ) * H * H :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hχj l (hlk.trans hk)) (Nat.cast_nonneg _))
            (hψj (k - l) ((Nat.sub_le _ _).trans hk)) (by positivity) (by positivity)
        _ = _ := by ring
    _ = 2 ^ k * H ^ 2 := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (sq_nonneg H)

/-- The actual two-cutoff multiplier retains enough cutoff factors uniformly in the scales. -/
theorem factorPieceCutoff_uniform (m s : ℕ) {χ ψ χr χ₃ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hbψ : ∀ i : ℕ, ∃ B : ℝ, ∀ θ, ‖iteratedFDeriv ℝ i ψ θ‖ ≤ B)
    (hr : ContDiff ℝ (⊤ : ℕ∞) χr)
    (hbr : ∀ i : ℕ, ∃ B : ℝ, ∀ θ, ‖iteratedFDeriv ℝ i χr θ‖ ≤ B)
    (h₃ : ContDiff ℝ (⊤ : ℕ∞) χ₃)
    (hb₃ : ∀ i : ℕ, ∃ B : ℝ, ∀ θ, ‖iteratedFDeriv ℝ i χ₃ θ‖ ≤ B)
    (hfac : ∀ z, χ z = χr z ^ (m + s + 1) * χ₃ z) :
    ∃ H C : ℝ, 1 ≤ H ∧ 0 < C ∧ ∀ η w : ℝ, 0 < η → 0 < w → w ≤ 1 →
      w / Real.sqrt η ≤ 1 → ∀ θ,
      (∀ i ≤ m + s, w ^ i * ‖iteratedFDeriv ℝ i
        (fun z => χr ((Real.sqrt η)⁻¹ • z)) θ‖ ≤ H) ∧
      ∀ k ≤ m, w ^ k * ‖iteratedFDeriv ℝ k (pieceCutoff χ ψ η) θ‖ ≤
        C * |χr ((Real.sqrt η)⁻¹ • θ)| ^ (m + s + 1 - k) := by
  obtain ⟨Hr, hHr, hJr⟩ := factorCutoff_finite_jet_bound hbr (m + s)
  obtain ⟨H₃, hH₃, hJ₃⟩ := factorCutoff_finite_jet_bound hb₃ (m + s)
  obtain ⟨Hp, hHp, hJp⟩ := factorCutoff_finite_jet_bound hbψ (m + s)
  let A : ℝ := Hr + H₃ + Hp
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hAr : Hr ≤ A := by dsimp [A]; linarith
  have hA₃ : H₃ ≤ A := by dsimp [A]; linarith
  have hAp : Hp ≤ A := by dsimp [A]; linarith
  let H : ℝ := 1 + A + 2 ^ m * A ^ 2
  have hH : 1 ≤ H := by dsimp [H]; linarith only [hA, show 0 ≤ (2 : ℝ) ^ m * A ^ 2 by positivity]
  have hAH : A ≤ H := by dsimp [H]; linarith only [show 0 ≤ (2 : ℝ) ^ m * A ^ 2 by positivity]
  obtain ⟨C, hC, hprod⟩ := factorCutoffProduct_uniform (m + s + 1) m (by omega) (by omega) hH
  refine ⟨H, C, hH, hC, ?_⟩
  intro η w hη hw hw1 hws θ
  have hsqrt := Real.sqrt_pos.mpr hη
  have hscale : w * |(Real.sqrt η)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hsqrt), ← div_eq_mul_inv]
    exact hws
  let ar : Vec 2 → ℝ := fun z => χr ((Real.sqrt η)⁻¹ • z)
  let a₃ : Vec 2 → ℝ := fun z => χ₃ ((Real.sqrt η)⁻¹ • z)
  have har : ContDiff ℝ (⊤ : ℕ∞) ar := hr.comp (contDiff_id.const_smul _)
  have ha₃ : ContDiff ℝ (⊤ : ℕ∞) a₃ := h₃.comp (contDiff_id.const_smul _)
  have hjr (i : ℕ) (hi : i ≤ m + s) : w ^ i * ‖iteratedFDeriv ℝ i ar θ‖ ≤ A :=
    (factorCutoff_scaled_normalized_jet_le hr (zero_le_one.trans hHr) hJr hw.le hscale θ hi).trans hAr
  have hj₃ (i : ℕ) (hi : i ≤ m + s) : w ^ i * ‖iteratedFDeriv ℝ i a₃ θ‖ ≤ A :=
    (factorCutoff_scaled_normalized_jet_le h₃ (zero_le_one.trans hH₃) hJ₃ hw.le hscale θ hi).trans hA₃
  have hjp (i : ℕ) (hi : i ≤ m + s) : w ^ i * ‖iteratedFDeriv ℝ i ψ θ‖ ≤ A :=
    (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hw.le hw1)).trans ((hJp i hi θ).trans hAp)
  have hval : |ar θ| ≤ H := by
    have hv := (hjr 0 (by omega)).trans hAH
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hv
  refine ⟨fun i hi => (hjr i hi).trans hAH, ?_⟩
  have he : pieceCutoff χ ψ η = fun z => ar z ^ (m + s + 1) * (a₃ z * ψ z) := by
    funext z
    dsimp [pieceCutoff, ar, a₃]
    rw [hfac]
    ring
  rw [he]
  apply hprod ar (fun z => a₃ z * ψ z) har (ha₃.mul hψ) θ hw hval
    (fun i hi => (hjr i (by omega)).trans hAH)
  intro i hi
  exact (factorCutoff_mul_normalized_jet_le ha₃ hψ hw.le (zero_le_one.trans hA) θ
    (fun j hj => hj₃ j (by omega)) (fun j hj => hjp j (by omega)) hi).trans
      (by dsimp [H]; linarith only [hA])

end AVRegularity.CycleWords.Assembly
end
