-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.FamilyNorm
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivativeRev
public import AVRegularity.CycleWords.MixedWords.AmplitudeLimit
import AVRegularity.CycleWords.Seam.LetterTransposeNorm
public import AVRegularity.CycleWords.MixedWords.GaugeJetsCore
import AVRegularity.Analysis.Convolution
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open MeasureTheory Homogenization
open AVRegularity.CycleWords.Seam
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! **The scaled moments of a datum by its weighted norm**. Every scaled moment
`(ϖz₀)^{β₁}(ϖz₁)^{β₂}` with `β₁ + β₂ ≤ n` is at most the weight `(1 + ϖ²|z|²)^{n/2}`, so the
moment norm of order `n` at scale `ϖ` is at most the number of moment indices times the weight-`n`
`L²` norm (`momentNorm_le_weighted`).

Special cases:
- `n = 0`: one index; the moment norm is the `L²` norm and the weight is `1`.
- `ϖ = 0`: every moment is the value; the weight is `1`.
- An empty family: both sides vanish. -/

/-- One scaled coordinate is at most the square root of the weight base. -/
theorem abs_scaled_coord_le (ϖ : ℝ) (z : Vec 2) (i : Fin 2) :
    |ϖ * z i| ≤ Real.sqrt (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) := by
  refine Real.abs_le_sqrt ?_
  rw [mul_pow]
  fin_cases i
  · simp only [Fin.zero_eta]
    nlinarith [sq_nonneg (ϖ * z 1), sq_nonneg ϖ, sq_nonneg (z 1)]
  · simp only [Fin.mk_one]
    nlinarith [sq_nonneg (ϖ * z 0), sq_nonneg ϖ, sq_nonneg (z 0)]

/-- A scaled moment of total order at most `n` is at most the weight of order `n`. -/
theorem abs_scaled_moment_le (ϖ : ℝ) (z : Vec 2) {b₁ b₂ n : ℕ} (hb : b₁ + b₂ ≤ n) :
    |(ϖ * z 0) ^ b₁ * (ϖ * z 1) ^ b₂| ≤ (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) := by
  set q := 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) with hq
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith [sq_nonneg ϖ, sq_nonneg (z 0), sq_nonneg (z 1)]
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  rw [abs_mul, abs_pow, abs_pow]
  calc |ϖ * z 0| ^ b₁ * |ϖ * z 1| ^ b₂ ≤ Real.sqrt q ^ b₁ * Real.sqrt q ^ b₂ :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (abs_scaled_coord_le ϖ z 0) _)
          (pow_le_pow_left₀ (abs_nonneg _) (abs_scaled_coord_le ϖ z 1) _) (by positivity)
          (by positivity)
    _ = q ^ (((b₁ + b₂ : ℕ) : ℝ) / 2) := by
        rw [← pow_add, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        congr 1
        ring
    _ ≤ q ^ ((n : ℝ) / 2) := by
        refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
        have : ((b₁ + b₂ : ℕ) : ℝ) ≤ n := by exact_mod_cast hb
        linarith

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The moment norm by the weighted norm.** -/
theorem momentNorm_le_weighted (π : ι → ℝ) (n : ℕ) (ϖ : ℝ) (F : ∀ x, Vec 2 → h x)
    (hF : ∀ x, AEStronglyMeasurable (F x) volume) :
    momentNorm π n ϖ F ≤ ENNReal.ofReal ((momentIndices n).card : ℝ) *
      familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹)) (fun x => eLpNorm (fun z =>
        (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) * ‖F x z‖) 2 volume) := by
  unfold momentNorm
  rw [ENNReal.ofReal_natCast, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun β hβ => ?_
  have hβn : β.1 + β.2 ≤ n := (Finset.mem_filter.1 hβ).2
  have hfact : ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    exact inv_le_one_of_one_le₀ (Nat.one_le_cast.2
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)))
  calc ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z => ((ϖ * z 0) ^ β.1 *
          (ϖ * z 1) ^ β.2) • F v z) 2 volume ^ 2) ^ (1 / 2 : ℝ)
      ≤ 1 * familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹)) (fun x => eLpNorm (fun z =>
          (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) * ‖F x z‖) 2 volume) := by
        refine mul_le_mul' hfact ?_
        refine familyNorm_mono _ fun x => ?_
        refine eLpNorm_mono_real (((((continuous_const.mul (continuous_apply 0)).pow _).mul
          ((continuous_const.mul (continuous_apply 1)).pow _)).aestronglyMeasurable).smul
            (hF x)) fun z => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_scaled_moment_le ϖ z hβn) (norm_nonneg _)
    _ = _ := one_mul _

end Family

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped InnerProductSpace
namespace AVRegularity.CycleWords.Assembly

/-! **Band-limited functions against smooth tests** (a step of the old scalar bound).
- Integration by parts: `∫ ⟪Dʷ ampFun r U V, φ⟫ = (-1)^{|w|} ∫ ⟪ampFun r U V, D^{rev w} φ⟫` for a
  smooth compactly supported test `φ` (`integral_inner_orderedDerivative_ampFun`). The derivatives
  land on the test in the reverse order (`orderedDerivativeRev`).
- The Bessel weight: `ampFun r (μ_k Ã) (μ_k B̃)`, `μ_k(θ) = (1 + |θ|²/ϖ²)^k`, is the sum over
  `i ≤ k` and words `u` of length `i` of `C(k, i) (-ϖ⁻²)^i D^{uu} ampFun r Ã B̃`
  (`ampFun_besselWeight_eq`): `|θ|^{2i} = ∑_u θ^{uu}` and the even rotations are signs.

For `k = 0` the sum is the single term `ampFun r Ã B̃`. For the empty word the integration by
parts is the identity, and for `U = V = 0` both sides vanish. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The directional derivative of a smooth test is smooth. -/
theorem contDiff_dirTest {φ : Vec 2 → E} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ φ z (basisVec j)) := by
  have h := hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact h.clm_apply contDiff_const

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem hasCompactSupport_dirTest [NormedSpace ℝ E] {φ : Vec 2 → E} (hφc : HasCompactSupport φ)
    (j : Fin 2) : HasCompactSupport (fun z => fderiv ℝ φ z (basisVec j)) :=
  hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)

omit [CompleteSpace E] in
/-- `⟪F, ψ⟫` is integrable for a continuous `F` and a continuous compactly supported `ψ`. -/
theorem integrable_inner_compact {F ψ : Vec 2 → E} (hF : Continuous F) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) : Integrable (fun z => ⟪F z, ψ z⟫_ℝ) := by
  refine (hF.inner hψ).integrable_of_hasCompactSupport (hψc.mono ?_)
  intro z hz
  simp only [Function.mem_support] at hz ⊢
  intro h0
  exact hz (by rw [h0, inner_zero_right])

omit [CompleteSpace E] in
/-- The test after reverse derivatives: the first letter is applied last. -/
theorem orderedDerivativeRev_succ {a : ℕ} (w : DerivativeWord2 (a + 1)) (φ : Vec 2 → E) :
    orderedDerivativeRev w φ =
      fun z => fderiv ℝ (orderedDerivativeRev (fun i : Fin a => w i.succ) φ) z (basisVec (w 0)) := by
  simp [orderedDerivativeRev, List.ofFn_succ]

omit [CompleteSpace E] in
theorem orderedDerivativeRev_zero (w : DerivativeWord2 0) (φ : Vec 2 → E) :
    orderedDerivativeRev w φ = φ := by
  simp [orderedDerivativeRev]

omit [CompleteSpace E] in
/-- Reverse derivatives of a smooth compactly supported test are smooth and compactly
supported. -/
theorem orderedDerivativeRev_test {φ : Vec 2 → E} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) : ∀ {a : ℕ} (w : DerivativeWord2 a),
    ContDiff ℝ (⊤ : ℕ∞) (orderedDerivativeRev w φ) ∧
      HasCompactSupport (orderedDerivativeRev w φ)
  | 0, w => by rw [orderedDerivativeRev_zero]; exact ⟨hφ, hφc⟩
  | a + 1, w => by
    obtain ⟨h1, h2⟩ := orderedDerivativeRev_test hφ hφc (fun i : Fin a => w i.succ)
    rw [orderedDerivativeRev_succ]
    exact ⟨contDiff_dirTest h1 _, hasCompactSupport_dirTest h2 _⟩

/-- **One integration by parts** of a band-limited function against a smooth test. -/
theorem integral_inner_ampFun_deriv {r : ℝ} (hr : 0 ≤ r) {U V : Vec 2 → E}
    (hU : IntegrableOn U {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hV : IntegrableOn V {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) {φ : Vec 2 → E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (j : Fin 2) :
    ∫ z, ⟪ampFun r (derivAmpA j V) (derivAmpB j U) z, φ z⟫_ℝ =
      -∫ z, ⟪ampFun r U V z, fderiv ℝ φ z (basisVec j)⟫_ℝ := by
  have hG : ContDiff ℝ 1 (ampFun r U V) := ampFun_contDiff hr 1 hU hV
  have hG' : Continuous (ampFun r (derivAmpA j V) (derivAmpB j U)) :=
    (ampFun_contDiff hr 0 (integrableOn_derivAmpA hr hV j)
      (integrableOn_derivAmpB hr hU j)).continuous
  have hD : ∀ z, fderiv ℝ (ampFun r U V) z (basisVec j) =
      ampFun r (derivAmpA j V) (derivAmpB j U) z := fun z => fderiv_ampFun_basisVec hr hU hV z j
  have hφ1 : Continuous φ := hφ.continuous
  have hDφ : Continuous (fun z => fderiv ℝ φ z (basisVec j)) := (contDiff_dirTest hφ j).continuous
  have hi1 : Integrable (fun z => ⟪fderiv ℝ (ampFun r U V) z (basisVec j), φ z⟫_ℝ) := by
    simp only [hD]
    exact integrable_inner_compact hG' hφ1 hφc
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)) (f := ampFun r U V) (g := φ) (v := basisVec j)
    (μ := volume) hi1
    (integrable_inner_compact hG.continuous hDφ (hasCompactSupport_dirTest hφc j))
    (integrable_inner_compact hG.continuous hφ1 hφc)
    (fun x _ => hG.differentiable (by norm_num) x)
    (fun x _ => hφ.differentiable (by simp) x)
  have h' : ∫ z, ⟪ampFun r U V z, fderiv ℝ φ z (basisVec j)⟫_ℝ =
      -∫ z, ⟪fderiv ℝ (ampFun r U V) z (basisVec j), φ z⟫_ℝ := h
  simp only [hD] at h'
  rw [h', neg_neg]

/-- **Integration by parts along a word**: the derivatives move to the test in reverse order. -/
theorem integral_inner_orderedDerivative_ampFun {r : ℝ} (hr : 0 ≤ r) :
    ∀ {a : ℕ} (w : DerivativeWord2 a) {U V : Vec 2 → E},
    IntegrableOn U {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} →
    IntegrableOn V {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} → ∀ {φ : Vec 2 → E},
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ z, ⟪orderedDerivative w (ampFun r U V) z, φ z⟫_ℝ =
      (-1) ^ a * ∫ z, ⟪ampFun r U V z, orderedDerivativeRev w φ z⟫_ℝ
  | 0, w, U, V, _, _, φ, _, _ => by
    simp [orderedDerivative, orderedDerivativeRev]
  | a + 1, w, U, V, hU, hV, φ, hφ, hφc => by
    have e1 : orderedDerivative w (ampFun r U V) =
        orderedDerivative (fun i : Fin a => w i.succ)
          (ampFun r (derivAmpA (w 0) V) (derivAmpB (w 0) U)) := by
      have h0 : (fun x => fderiv ℝ (ampFun r U V) x (basisVec (w 0))) =
          ampFun r (derivAmpA (w 0) V) (derivAmpB (w 0) U) :=
        funext fun z => fderiv_ampFun_basisVec hr hU hV z (w 0)
      rw [← h0]
      simp [orderedDerivative, List.ofFn_succ]
    obtain ⟨hψ, hψc⟩ := orderedDerivativeRev_test hφ hφc (fun i : Fin a => w i.succ)
    rw [e1, integral_inner_orderedDerivative_ampFun hr (fun i : Fin a => w i.succ)
      (integrableOn_derivAmpA hr hV (w 0)) (integrableOn_derivAmpB hr hU (w 0)) hφ hφc,
      integral_inner_ampFun_deriv hr hU hV hψ hψc (w 0)]
    simp only [orderedDerivativeRev_succ w φ]
    ring

/-! ### The Bessel weight -/

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Even rotations are signs: `J^{2i} = (-1)^i`. -/
theorem jRot_add_self [Module ℝ E] (i : ℕ) (p : (Vec 2 → E) × (Vec 2 → E)) :
    jRot (i + i) p = ((-1 : ℝ) ^ i • p.1, (-1 : ℝ) ^ i • p.2) := by
  induction i with
  | zero => simp [jRot]
  | succ i ih =>
    rw [show i + 1 + (i + 1) = 2 + (i + i) by ring, jRot_add, ih]
    simp only [jRot, pow_succ, mul_neg, mul_one, neg_smul]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- `ampFun` commutes with scalars. -/
theorem ampFun_smul [NormedSpace ℝ E] {r : ℝ} (c : ℝ) (X Y : Vec 2 → E) :
    ampFun r (fun θ => c • X θ) (fun θ => c • Y θ) = fun z => c • ampFun r X Y z := by
  funext z
  unfold ampFun
  simp only [smul_comm _ c, ← smul_add]
  rw [integral_smul]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- `ampFun` of a finite sum of amplitude pairs. -/
theorem ampFun_finset_sum [NormedSpace ℝ E] {r : ℝ} {κ : Type*} (s : Finset κ)
    (X Y : κ → Vec 2 → E) (hX : ∀ n ∈ s, IntegrableOn (X n) {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hY : ∀ n ∈ s, IntegrableOn (Y n) {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) :
    ampFun r (fun θ => ∑ n ∈ s, X n θ) (fun θ => ∑ n ∈ s, Y n θ) =
      fun z => ∑ n ∈ s, ampFun r (X n) (Y n) z := by
  funext z
  unfold ampFun
  rw [← integral_finsetSum s fun n hn => integrableOn_ampIntegrand (hX n hn) (hY n hn) z]
  congr 1
  funext θ
  simp only [Finset.smul_sum, Finset.sum_add_distrib]

omit [CompleteSpace E] in
/-- The doubled monomial: `θ^{uu} = ∏_l θ_{u_l}²`. -/
theorem wordMonomial_append_self {i : ℕ} (u : Fin i → Fin 2) (θ : Vec 2) :
    wordMonomial (Fin.append u u) θ = ∏ l, θ (u l) ^ 2 := by
  unfold wordMonomial
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, ← Finset.prod_mul_distrib, sq]

omit [CompleteSpace E] in
/-- `|θ|^{2i} = ∑_u θ^{uu}`. -/
theorem vecDot_pow_eq_sum (θ : Vec 2) (i : ℕ) :
    vecDot θ θ ^ i = ∑ u : Fin i → Fin 2, wordMonomial (Fin.append u u) θ := by
  simp only [wordMonomial_append_self]
  have h := Finset.sum_pow' (Finset.univ : Finset (Fin 2)) (fun j => θ j ^ 2) i
  rw [Fintype.piFinset_univ] at h
  rw [show vecDot θ θ = ∑ j, θ j ^ 2 by simp [vecDot, sq], h]

/-- The Bessel weight `μ_k(θ) = (1 + |θ|²/ϖ²)^k`. -/
def besselWeight (ϖ : ℝ) (k : ℕ) (θ : Vec 2) : ℝ := (1 + vecDot θ θ / ϖ ^ 2) ^ k

omit [CompleteSpace E] in
theorem besselWeight_eq_sum (ϖ : ℝ) (k : ℕ) (θ : Vec 2) :
    besselWeight ϖ k θ = ∑ i ∈ Finset.range (k + 1), ∑ u : Fin i → Fin 2,
      ((k.choose i : ℝ) * ((ϖ ^ 2)⁻¹) ^ i) * wordMonomial (Fin.append u u) θ := by
  unfold besselWeight
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← vecDot_pow_eq_sum, one_pow, mul_one, div_eq_mul_inv, mul_pow]
  ring

/-- **The Bessel weight as even derivatives**: `ampFun r (μ_k Ã) (μ_k B̃)` is
`∑_{i ≤ k} ∑_u C(k,i) (-ϖ⁻²)^i D^{uu} ampFun r Ã B̃`. -/
theorem ampFun_besselWeight_eq {r : ℝ} (hr : 0 ≤ r) (ϖ : ℝ) (k : ℕ) {A B : Vec 2 → E}
    (hA : IsBandAmp r 0 A) (hB : IsBandAmp r 0 B) :
    ampFun r (fun θ => besselWeight ϖ k θ • A θ) (fun θ => besselWeight ϖ k θ • B θ) =
      fun z => ∑ i ∈ Finset.range (k + 1), ∑ u : Fin i → Fin 2,
        ((k.choose i : ℝ) * (-(ϖ ^ 2)⁻¹) ^ i) •
          orderedDerivative (Fin.append u u) (ampFun r A B) z := by
  have hterm : ∀ (i : ℕ) (u : Fin i → Fin 2) (z : Vec 2),
      ampFun r (fun θ => wordMonomial (Fin.append u u) θ • A θ)
          (fun θ => wordMonomial (Fin.append u u) θ • B θ) z =
        (-1 : ℝ) ^ i • orderedDerivative (Fin.append u u) (ampFun r A B) z := by
    intro i u z
    have h2 : orderedDerivative (Fin.append u u) (ampFun r A B) z =
        ampFun r (fun θ => (-1 : ℝ) ^ i • (wordMonomial (Fin.append u u) θ • A θ))
          (fun θ => (-1 : ℝ) ^ i • (wordMonomial (Fin.append u u) θ • B θ)) z := by
      rw [orderedDerivative_ampFun_eq hr (Fin.append u u) hA hB, jRot_add_self]
      rfl
    simp only [ampFun_smul] at h2
    rw [h2, smul_smul, ← mul_pow]
    norm_num
  set c : ℕ → ℝ := fun i => (k.choose i : ℝ) * ((ϖ ^ 2)⁻¹) ^ i with hc
  have hsplit : ∀ X : Vec 2 → E, (fun θ => besselWeight ϖ k θ • X θ) =
      fun θ => ∑ i ∈ Finset.range (k + 1), ∑ u : Fin i → Fin 2,
        c i • (wordMonomial (Fin.append u u) θ • X θ) := fun X => by
    funext θ
    rw [besselWeight_eq_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_smul]
  have hint3 : ∀ X : Vec 2 → E, IsBandAmp r 0 X → ∀ (i : ℕ) (u : Fin i → Fin 2),
      Integrable (fun θ => c i • (wordMonomial (Fin.append u u) θ • X θ)) := fun X hX i u =>
    (hX.monomial_smul (Fin.append u u)).integrable.smul (c i)
  have hint2 : ∀ X : Vec 2 → E, IsBandAmp r 0 X → ∀ (i : ℕ) (u : Fin i → Fin 2),
      IntegrableOn (fun θ => c i • (wordMonomial (Fin.append u u) θ • X θ))
        {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := fun X hX i u => (hint3 X hX i u).integrableOn
  have hint : ∀ X : Vec 2 → E, IsBandAmp r 0 X → ∀ i ∈ Finset.range (k + 1),
      IntegrableOn (fun θ => ∑ u : Fin i → Fin 2, c i • (wordMonomial (Fin.append u u) θ • X θ))
        {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := fun X hX i _ =>
    (integrable_finsetSum _ fun u _ => hint3 X hX i u).integrableOn
  rw [hsplit A, hsplit B, ampFun_finset_sum _ _ _ (hint A hA) (hint B hB)]
  funext z
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ampFun_finset_sum _ _ _ (fun u _ => hint2 A hA i u) (fun u _ => hint2 B hB i u)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [ampFun_smul]
  show c i • ampFun r (fun θ => wordMonomial (Fin.append u u) θ • A θ)
    (fun θ => wordMonomial (Fin.append u u) θ • B θ) z = _
  rw [hterm i u z, smul_smul]
  congr 1
  rw [hc, neg_pow]
  ring

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! **The Bloch moment bound for compactly supported `L²` data** (the moment step of the old scalar bound). The squared
Bloch jets of a datum, integrated over the frequency cube, are bounded by its moment norm
(`lintegral_compact_bloch_sum_sq_le`) for continuous compactly supported data. The proof uses
continuity only for measurability, so it holds verbatim for strongly measurable data with a
pointwise support radius (`*_sm`, copies of `measurable_latticePair`,
`lintegral_cube_cell_latticePair_le`, `compact_bloch_fibre_sq_le`, `compact_bloch_fibre_majorant`
and `lintegral_compact_bloch_sum_sq_le`). For an `L²` datum vanishing a.e. off a ball (the datum of the old scalar bound,
and the datum of the retained amplitude factor statement), a strongly measurable representative with a pointwise support
radius has the same Bloch jets and moments, since the lattice translates of a null set are null
(`blochFibreDerivNorm_congr_ae`, `momentNorm_congr_ae`); hence `lintegral_bloch_sum_sq_le_of_ae`.

For a continuous compactly supported datum this is the original bound, and for the zero datum
both sides vanish. For `n = 0` it compares the value fibres with the `L²` norm (Parseval and
tiling). -/

section Point

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem measurable_latticePair_sm (K : Finset (Fin 2 → ℤ)) {H : Vec 2 → E}
    (hH : StronglyMeasurable H) :
    Measurable fun p : Vec 2 × Vec 2 => latticePair K H p.1 p.2 := by
  have hc : ∀ ψ : ℝ → ℝ, Continuous ψ → Measurable fun p : Vec 2 × Vec 2 =>
      ‖∑ q ∈ K, ψ (vecDot p.1 (p.2 + fun i => (q i : ℝ))) • H (p.2 + fun i => (q i : ℝ))‖ := by
    intro ψ hψ
    have hs : StronglyMeasurable fun p : Vec 2 × Vec 2 =>
        ∑ q ∈ K, ψ (vecDot p.1 (p.2 + fun i => (q i : ℝ))) • H (p.2 + fun i => (q i : ℝ)) := by
      refine Finset.stronglyMeasurable_fun_sum _ fun q _ => ?_
      refine StronglyMeasurable.smul ?_ ?_
      · exact (hψ.comp (by unfold vecDot; fun_prop)).stronglyMeasurable
      · exact hH.comp_measurable (by fun_prop)
    exact hs.norm.measurable
  unfold latticePair
  exact ((ENNReal.measurable_ofReal.comp (hc _ Real.continuous_cos)).pow_const 2).add
    ((ENNReal.measurable_ofReal.comp (hc _ Real.continuous_sin)).pow_const 2)

theorem lintegral_cube_cell_latticePair_le_sm (K : Finset (Fin 2 → ℤ)) {H : Vec 2 → E}
    (hH : StronglyMeasurable H) :
    ∫⁻ θ in freqCube, ∫⁻ z in AVenhance.unitCube, latticePair K H θ z ≤
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * eLpNorm H 2 volume ^ 2 := by
  rw [lintegral_lintegral_swap (measurable_latticePair_sm K hH).aemeasurable]
  have hpar : ∀ z, ∫⁻ θ in freqCube, latticePair K H θ z =
      ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        ∑ q ∈ K, ENNReal.ofReal (‖H (z + fun i => (q i : ℝ))‖ ^ 2) :=
    fun z => lintegral_cube_parseval K z fun q => H (z + fun i => (q i : ℝ))
  have hmq : ∀ q : Fin 2 → ℤ, Measurable fun z : Vec 2 =>
      ENNReal.ofReal (‖H (z + fun i => (q i : ℝ))‖ ^ 2) := fun q =>
    ENNReal.measurable_ofReal.comp
      ((hH.comp_measurable (measurable_add_const _)).norm.measurable.pow_const 2)
  have hmH : Measurable fun y : Vec 2 => ENNReal.ofReal (‖H y‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hH.norm.measurable.pow_const 2)
  rw [lintegral_congr hpar, lintegral_const_mul _ (Finset.measurable_sum _ fun q _ => hmq q)]
  gcongr
  calc ∫⁻ z in AVenhance.unitCube, ∑ q ∈ K, ENNReal.ofReal (‖H (z + fun i => (q i : ℝ))‖ ^ 2)
      ≤ ∫⁻ z in AVenhance.unitCube,
          ∑' q : Fin 2 → ℤ, ENNReal.ofReal (‖H (z + fun i => (q i : ℝ))‖ ^ 2) :=
        lintegral_mono fun z => ENNReal.sum_le_tsum K
    _ = ∑' q : Fin 2 → ℤ, ∫⁻ z in Applications.cellI,
          ENNReal.ofReal (‖H (z + AVenhance.latticeShift q)‖ ^ 2) := by
        rw [lintegral_tsum fun q => (hmq q).aemeasurable,
          ← Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube]
        rfl
    _ = ∫⁻ y, ENNReal.ofReal (‖H y‖ ^ 2) :=
        (CycleJointProofs.lintegral_tiling_translate _ hmH).symm
    _ = eLpNorm H 2 volume ^ 2 := by
        rw [eLpNorm_two_sq hH.aestronglyMeasurable]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end Point

section Family
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

theorem compact_bloch_fibre_sq_le_sm {n : ℕ} {χlo : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {B : ℝ}
    (hB : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ B)
    {η ϖ : ℝ} (hη : 0 < η) (hϖ : 0 < ϖ) (hϖη : ϖ ≤ Real.sqrt η)
    (π : ι → ℝ) (F : ∀ x, Vec 2 → h x) (R : ι → ℝ) (N : ι → ℕ)
    (hF : ∀ x, StronglyMeasurable (F x))
    (hsupp : ∀ x y, R x < ‖y‖ → F x y = 0) (hN : ∀ x, R x + 1 ≤ N x)
    {α : ℕ × ℕ} (hα : α.1 + α.2 ≤ n) (θ : Vec 2) :
    ENNReal.ofReal (ϖ ^ (2 * (α.1 + α.2))) *
        blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ ^ 2 ≤
      ∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal ((α.1 + α.2 + 1 : ℕ) * 2 ^ (α.1 + α.2) : ℝ) *
          ∑ l ∈ Finset.range (α.1 + α.2 + 1), ∑ idx : Fin (α.1 + α.2 - l) → Fin 2,
            ENNReal.ofReal (((α.1 + α.2).choose l : ℝ) * B) ^ 2 *
              ∫⁻ z in AVenhance.unitCube,
                latticePair (latticeBox (N x)) (fun y => wordMonomial idx (ϖ • y) • F x y) θ z) := by
  unfold blochFibreDerivNorm
  rw [rpow_half_sq, ← lintegral_const_mul' _ _ (by simp)]
  have hcont (x : ι) (l : ℕ) (idx : Fin (α.1 + α.2 - l) → Fin 2) :
      StronglyMeasurable fun y => wordMonomial idx (ϖ • y) • F x y :=
    ((wordMonomial_contDiff idx).continuous.comp (continuous_const_smul ϖ)).stronglyMeasurable.smul
      (hF x)
  have hQ (x : ι) (l : ℕ) (idx : Fin (α.1 + α.2 - l) → Fin 2) :
      Measurable fun z => latticePair (latticeBox (N x))
        (fun y => wordMonomial idx (ϖ • y) • F x y) θ z :=
    Measurable.of_uncurry_left
      (measurable_latticePair_sm (E := h x) (latticeBox (N x)) (hcont x l idx))
  have hout := lintegral_weighted_sum (volume.restrict AVenhance.unitCube)
    (fun x => ENNReal.ofReal ((π x)⁻¹))
    (ENNReal.ofReal ((α.1 + α.2 + 1 : ℕ) * 2 ^ (α.1 + α.2) : ℝ))
    (Finset.range (α.1 + α.2 + 1))
    (fun l => ENNReal.ofReal (((α.1 + α.2).choose l : ℝ) * B) ^ 2)
    (fun x l (idx : Fin (α.1 + α.2 - l) → Fin 2) z =>
      latticePair (latticeBox (N x)) (fun y => wordMonomial idx (ϖ • y) • F x y) θ z)
    hQ
  rw [← hout]
  have hcell : MeasurableSet AVenhance.unitCube :=
    MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioo
  refine lintegral_mono_ae (ae_restrict_of_forall_mem hcell fun z hz => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_right
    (pair_bound_point_ennreal hχ hB hη hϖ hϖη (hsupp x) (hN x) hz hα θ) _

theorem compact_bloch_fibre_majorant_sm {n : ℕ} {χlo : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {B : ℝ}
    (hB : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ B)
    {η ϖ : ℝ} (hη : 0 < η) (hϖ : 0 < ϖ) (hϖη : ϖ ≤ Real.sqrt η)
    (π : ι → ℝ) (F : ∀ x, Vec 2 → h x)
    (hF : ∀ x, StronglyMeasurable (F x))
    (hsupp : ∀ x, ∃ R : ℝ, 0 ≤ R ∧ ∀ y : Vec 2, R < ‖y‖ → F x y = 0)
    {α : ℕ × ℕ} (hα : α.1 + α.2 ≤ n) :
    ∃ P : Vec 2 → ℝ≥0∞, Measurable P ∧
      (∀ θ, ENNReal.ofReal (ϖ ^ (2 * (α.1 + α.2))) *
        blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ ^ 2 ≤ P θ) ∧
      (∫⁻ θ in freqCube, P θ) ≤
        ENNReal.ofReal (blochMomentCoeff n (α.1 + α.2) B) * momentNorm π n ϖ F ^ 2 := by
  choose R hR0 hR using hsupp
  let N x := ⌈R x + 1⌉₊
  let k := α.1 + α.2
  let C : ℝ≥0∞ := ENNReal.ofReal ((k + 1 : ℕ) * 2 ^ k : ℝ)
  let c (l : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((k.choose l : ℝ) * B) ^ 2
  let H (x : ι) (l : ℕ) (idx : Fin (k - l) → Fin 2) (y : Vec 2) :=
    wordMonomial idx (ϖ • y) • F x y
  have hH x l (idx : Fin (k - l) → Fin 2) : StronglyMeasurable (H x l idx) :=
    ((wordMonomial_contDiff idx).continuous.comp (continuous_const_smul ϖ)).stronglyMeasurable.smul
      (hF x)
  have hQ x l (idx : Fin (k - l) → Fin 2) :
      Measurable fun θ => ∫⁻ z in AVenhance.unitCube,
        latticePair (latticeBox (N x)) (H x l idx) θ z :=
    (measurable_latticePair_sm _ (hH x l idx)).lintegral_prod_right'
  let P θ := ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    (C * ∑ l ∈ Finset.range (k + 1), ∑ idx : Fin (k - l) → Fin 2,
      c l * ∫⁻ z in AVenhance.unitCube, latticePair (latticeBox (N x)) (H x l idx) θ z)
  have hPm : Measurable P := by
    refine Finset.measurable_sum _ fun x _ => ?_
    apply Measurable.const_mul
    apply Measurable.const_mul
    refine Finset.measurable_sum _ fun l _ => ?_
    exact Finset.measurable_sum _ fun idx _ => (hQ x l idx).const_mul _
  refine ⟨P, hPm, fun θ => compact_bloch_fibre_sq_le_sm hχ hB hη hϖ hϖη π F R N
    hF hR (fun x => Nat.le_ceil _) hα θ, ?_⟩
  dsimp only [P]
  rw [lintegral_weighted_sum (volume.restrict freqCube) _ _ _ _ _ hQ]
  calc
    ∑ x, ENNReal.ofReal ((π x)⁻¹) * (C * ∑ l ∈ Finset.range (k + 1),
        ∑ idx : Fin (k - l) → Fin 2, c l *
          ∫⁻ θ in freqCube, ∫⁻ z in AVenhance.unitCube,
            latticePair (latticeBox (N x)) (H x l idx) θ z)
      ≤ ∑ x, ENNReal.ofReal ((π x)⁻¹) * (C * ∑ l ∈ Finset.range (k + 1),
          ∑ idx : Fin (k - l) → Fin 2, c l *
            (ENNReal.ofReal ((2 * Real.pi) ^ 2) * eLpNorm (H x l idx) 2 volume ^ 2)) := by
        gcongr with x hx l hl idx
        exact lintegral_cube_cell_latticePair_le_sm _ (hH x l idx)
    _ = C * ∑ l ∈ Finset.range (k + 1), ∑ idx : Fin (k - l) → Fin 2,
          (c l * ENNReal.ofReal ((2 * Real.pi) ^ 2)) *
            ∑ x, ENNReal.ofReal ((π x)⁻¹) * eLpNorm (H x l idx) 2 volume ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun idx _ => Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ C * ∑ l ∈ Finset.range (k + 1), ∑ _idx : Fin (k - l) → Fin 2,
          (c l * ENNReal.ofReal ((2 * Real.pi) ^ 2)) *
            (ENNReal.ofReal (n.factorial : ℝ) * momentNorm π n ϖ F) ^ 2 := by
        gcongr with l hl idx
        have hidx : idxCount idx ∈ momentIndices n := by
          have hs := idxCount_sum idx
          have hk : k - l ≤ n := (Nat.sub_le k l).trans hα
          simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          omega
        simpa only [H, wordMonomial_smul_eq] using
          sum_eLpNorm_sq_le_momentNorm π ϖ F hidx
    _ = ENNReal.ofReal (blochMomentCoeff n k B) * momentNorm π n ϖ F ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, mul_pow]
        have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le n) 0)
        have hs : ENNReal.ofReal (∑ l ∈ Finset.range (k + 1),
            (2 : ℝ) ^ (k - l) * ((k.choose l : ℝ) * B) ^ 2) =
            ∑ l ∈ Finset.range (k + 1),
              ENNReal.ofReal ((2 : ℝ) ^ (k - l) * ((k.choose l : ℝ) * B) ^ 2) :=
          ENNReal.ofReal_sum_of_nonneg (by intros; positivity)
        have hc : ENNReal.ofReal (blochMomentCoeff n k B) =
            C * (∑ l ∈ Finset.range (k + 1), (2 : ℝ≥0∞) ^ (k - l) * c l) *
              ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (n.factorial : ℝ) ^ 2 := by
          unfold blochMomentCoeff
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), hs]
          simp (disch := positivity) only [C, c, ENNReal.ofReal_mul, ENNReal.ofReal_pow,
            ENNReal.ofReal_ofNat]
        rw [hc]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Nat.cast_pow, Nat.cast_ofNat]
        dsimp only [c]
        ring_nf

theorem lintegral_compact_bloch_sum_sq_le_sm {n : ℕ} {χlo : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {B : ℝ}
    (hB : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ B)
    {η ϖ : ℝ} (hη : 0 < η) (hϖ : 0 < ϖ) (hϖη : ϖ ≤ Real.sqrt η)
    (π : ι → ℝ) (F : ∀ x, Vec 2 → h x)
    (hF : ∀ x, StronglyMeasurable (F x))
    (hsupp : ∀ x, ∃ R : ℝ, 0 ≤ R ∧ ∀ y : Vec 2, R < ‖y‖ → F x y = 0) :
    (∫⁻ θ in freqCube, (∑ α ∈ momentIndices n,
      ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
        blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ) ^ 2) ≤
      ENNReal.ofReal (blochMomentTotal n B) * momentNorm π n ϖ F ^ 2 := by
  let S := momentIndices n
  have hα (a : ↥S) : a.val.1 + a.val.2 ≤ n := (Finset.mem_filter.1 a.property).2
  choose P hPm hPl hPi using fun a : ↥S =>
    compact_bloch_fibre_majorant_sm hχ hB hη hϖ hϖη π F hF hsupp (hα a)
  let V (a : ℕ × ℕ) θ :=
    blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) a F θ
  let w (a : ℕ × ℕ) :=
    ENNReal.ofReal (ϖ ^ (a.1 + a.2) / ((a.1.factorial * a.2.factorial : ℕ) : ℝ))
  have hw (a : ℕ × ℕ) : w a ^ 2 ≤ ENNReal.ofReal (ϖ ^ (2 * (a.1 + a.2))) := by
    have hf : (1 : ℝ) ≤ ((a.1.factorial * a.2.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (mul_ne_zero (Nat.factorial_ne_zero _)
        (Nat.factorial_ne_zero _))
    calc w a ^ 2 ≤ ENNReal.ofReal (ϖ ^ (a.1 + a.2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal
            (div_le_self (pow_nonneg hϖ.le _) hf)) 2
      _ = _ := by
          rw [← ENNReal.ofReal_pow (pow_nonneg hϖ.le _), ← pow_mul]
          congr 2
          omega
  have hp θ : (∑ a ∈ S, w a * V a θ) ^ 2 ≤ (S.card : ℝ≥0∞) * ∑ a : ↥S, P a θ := by
    rw [← Finset.sum_coe_sort S]
    have hcs := ennreal_sum_mul_sq_le Finset.univ (fun _ : ↥S => 1)
      (fun a => w a.val * V a.val θ)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Fintype.card_coe] at hcs
    refine hcs.trans (mul_le_mul_right (Finset.sum_le_sum fun a _ => ?_) _)
    rw [mul_pow]
    exact (mul_le_mul_left (hw a.val) _).trans (hPl a θ)
  have hm : Measurable fun θ => ∑ a : ↥S, P a θ :=
    Finset.measurable_sum _ fun a _ => hPm a
  calc
    (∫⁻ θ in freqCube, (∑ a ∈ S, w a * V a θ) ^ 2)
      ≤ ∫⁻ θ in freqCube, (S.card : ℝ≥0∞) * ∑ a : ↥S, P a θ := lintegral_mono hp
    _ = (S.card : ℝ≥0∞) * ∑ a : ↥S, ∫⁻ θ in freqCube, P a θ := by
        rw [lintegral_const_mul _ hm, lintegral_finsetSum _ fun a _ => hPm a]
    _ ≤ (S.card : ℝ≥0∞) * ∑ a : ↥S,
        ENNReal.ofReal (blochMomentCoeff n (a.val.1 + a.val.2) B) * momentNorm π n ϖ F ^ 2 :=
      mul_le_mul_right (Finset.sum_le_sum fun a _ => hPi a) _
    _ = ENNReal.ofReal (blochMomentTotal n B) * momentNorm π n ϖ F ^ 2 := by
        rw [← Finset.sum_mul]
        rw [Finset.sum_coe_sort S (fun a =>
          ENNReal.ofReal (blochMomentCoeff n (a.1 + a.2) B))]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => blochMomentCoeff_nonneg n _ B)]
        unfold blochMomentTotal
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

end Family

section AE

/-- A strongly measurable representative with a pointwise support radius. -/
theorem exists_representative_supported {E : Type*} [NormedAddCommGroup E] {F : Vec 2 → E}
    (hF : AEStronglyMeasurable F volume) {R : ℝ}
    (hR : ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → F z = 0) :
    ∃ G : Vec 2 → E, StronglyMeasurable G ∧ F =ᵐ[volume] G ∧
      ∀ y : Vec 2, |R| < ‖y‖ → G y = 0 := by
  set S : Set (Vec 2) := {z | z 0 ^ 2 + z 1 ^ 2 ≤ R ^ 2} with hSdef
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  refine ⟨S.indicator hF.mk, hF.stronglyMeasurable_mk.indicator hS, ?_, ?_⟩
  · filter_upwards [hF.ae_eq_mk, hR] with z h1 h2
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz, h1]
    · rw [Set.indicator_of_notMem hz]
      exact h2 (lt_of_not_ge hz)
  · intro y hy
    apply Set.indicator_of_notMem
    intro hyS
    have hle : ‖y‖ ≤ |R| := by
      refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      have hyS' : y 0 ^ 2 + y 1 ^ 2 ≤ R ^ 2 := hyS
      have hi : y i ^ 2 ≤ R ^ 2 := by
        fin_cases i
        · simp only [Fin.zero_eta]; nlinarith [sq_nonneg (y 1)]
        · simp only [Fin.mk_one]; nlinarith [sq_nonneg (y 0)]
      exact sq_le_sq.1 hi
    linarith

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- **The Bloch moment bound for an `L²` datum vanishing a.e. off a ball.** -/
theorem lintegral_bloch_sum_sq_le_of_ae {n : ℕ} {χlo : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {B : ℝ}
    (hB : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ B)
    {η ϖ : ℝ} (hη : 0 < η) (hϖ : 0 < ϖ) (hϖη : ϖ ≤ Real.sqrt η)
    (π : ι → ℝ) (F : ∀ x, Vec 2 → h x) (hF : ∀ x, AEStronglyMeasurable (F x) volume) {R : ℝ}
    (hR : ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → F x z = 0) :
    (∫⁻ θ in freqCube, (∑ α ∈ momentIndices n,
      ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
        blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ) ^ 2) ≤
      ENNReal.ofReal (blochMomentTotal n B) * momentNorm π n ϖ F ^ 2 := by
  choose G hGm hFG hGs using fun x => exists_representative_supported (hF x) (hR x)
  simp only [blochFibreDerivNorm_congr_ae hFG]
  rw [momentNorm_congr_ae hFG]
  exact lintegral_compact_bloch_sum_sq_le_sm hχ hB hη hϖ hϖη π G hGm
    (fun x => ⟨|R|, abs_nonneg R, hGs x⟩)

end AE

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleWords.Seam
open scoped ENNReal InnerProductSpace
namespace AVRegularity.CycleWords.Assembly

/-! **The `R`-scale negative norm of a band-limited family by its amplitude jets** (a step of the old scalar bound).
For a family `g_x = ampFun r (μ_k A_x) (μ_k B_x)` with the Bessel weight
`μ_k(θ) = (1 + |θ|²/ϖ²)^k` and amplitudes of class `C^p`:
`‖g‖_{R, -2k; p} ≤ C_k C_p (∫ amplitudeJetNorm π p ϖ A B (θ)² dθ)^{1/2}`, `R = ϖ⁻¹`
(`negJetNorm_besselWeight_le`).

Proof. `g_x = ∑_{i ≤ k} ∑_u C(k,i)(-ϖ⁻²)^i D^{uu} G_x`, `G_x = ampFun r A_x B_x`
(`ampFun_besselWeight_eq`); against a test `φ` the derivatives move to `φ`
(`integral_inner_orderedDerivative_ampFun`). Each pairing is at most the weight-`p` norm of `G`
times the weight-`(-p)` norm of a derivative of order `2i` of `φ` (`weighted_fun_family_pairing_le`).
The first is bounded by the amplitude jets (`weightedJetNorm_ampFun_le`), the second by
`(2i)! ϖ^{2i}` from the test norm `≤ 1`, which cancels `ϖ^{-2i}`.

For `k = 0` there is no negative order and the bound is the weighted `L²` norm of `g` itself.
For an empty family both sides vanish, and for `A = B = 0` one has `g = 0`. -/

/-- The constant of the Bessel duality: `∑_{i ≤ k} 2^i C(k,i) (2i)!`. -/
def besselDualConst (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (2 : ℝ) ^ i * ((k.choose i : ℝ) * ((i + i).factorial : ℝ))

theorem besselDualConst_nonneg (k : ℕ) : 0 ≤ besselDualConst k :=
  Finset.sum_nonneg fun _ _ => by positivity

section One

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **One weighted pairing**, through the weights `w_q w_{-q} = 1`. -/
theorem weighted_fun_pairing_le {F ψ : Vec 2 → E} (hF : AEStronglyMeasurable F volume)
    (hψ : AEStronglyMeasurable ψ volume) (q ϖ : ℝ) :
    ‖∫ z, ⟪F z, ψ z⟫_ℝ‖ₑ ≤
      eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (q / 2) * ‖F z‖) 2 volume *
        eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-q / 2) * ‖ψ z‖) 2 volume := by
  set wq : Vec 2 → ℝ := fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (q / 2) with hwq
  set wq' : Vec 2 → ℝ := fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-q / 2) with hwq'
  have hpos : ∀ z : Vec 2, 0 < 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := fun z => by positivity
  have hprod : ∀ z, wq z * wq' z = 1 := fun z => by
    rw [hwq, hwq']
    dsimp only
    rw [← Real.rpow_add (hpos z), show q / 2 + -q / 2 = 0 by ring, Real.rpow_zero]
  have hwq0 : ∀ z, 0 ≤ wq z := fun z => Real.rpow_nonneg (hpos z).le _
  have hwq0' : ∀ z, 0 ≤ wq' z := fun z => Real.rpow_nonneg (hpos z).le _
  set A : Vec 2 → ℝ := fun z => wq z * ‖F z‖ with hA
  set Bf : Vec 2 → ℝ := fun z => wq' z * ‖ψ z‖ with hB
  have hAm : AEStronglyMeasurable A volume :=
    (weight_continuous ϖ q).aestronglyMeasurable.mul hF.norm
  have hBm : AEStronglyMeasurable Bf volume :=
    (weight_continuous ϖ (-q)).aestronglyMeasurable.mul hψ.norm
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    (hAm.aemeasurable.ennreal_ofReal) (hBm.aemeasurable.ennreal_ofReal)
  have heL : ∀ (f : Vec 2 → ℝ), AEStronglyMeasurable f volume → (∀ z, 0 ≤ f z) →
      eLpNorm f 2 volume = (∫⁻ z, ENNReal.ofReal (f z) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    intro f hf hf0
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
      ENNReal.toReal_ofNat]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 z)]
  rw [heL A hAm fun z => mul_nonneg (hwq0 z) (norm_nonneg _),
    heL Bf hBm fun z => mul_nonneg (hwq0' z) (norm_nonneg _)]
  refine le_trans ?_ hholder
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
  rw [Real.enorm_eq_ofReal_abs, Pi.mul_apply, ← ENNReal.ofReal_mul (mul_nonneg (hwq0 z)
    (norm_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ((abs_real_inner_le_norm _ _).trans (le_of_eq ?_))
  show _ = wq z * ‖F z‖ * (wq' z * ‖ψ z‖)
  calc ‖F z‖ * ‖ψ z‖ = (wq z * wq' z) * (‖F z‖ * ‖ψ z‖) := by rw [hprod, one_mul]
    _ = _ := by ring

end One

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- **The weighted family pairing**: Cauchy–Schwarz over the components. -/
theorem weighted_fun_family_pairing_le (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (F ψ : ∀ x, Vec 2 → h x)
    (hF : ∀ x, AEStronglyMeasurable (F x) volume) (hψ : ∀ x, AEStronglyMeasurable (ψ x) volume)
    (q ϖ : ℝ) :
    ENNReal.ofReal |∑ x, (π x)⁻¹ * ∫ z, ⟪F x z, ψ x z⟫_ℝ| ≤
      familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹)) (fun x => eLpNorm (fun z =>
          (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (q / 2) * ‖F x z‖) 2 volume) *
        familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹)) (fun x => eLpNorm (fun z =>
          (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-q / 2) * ‖ψ x z‖) 2 volume) := by
  set c : ι → ℝ≥0∞ := fun x => ENNReal.ofReal ((π x)⁻¹) with hc
  set A : ι → ℝ≥0∞ := fun x => eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (q / 2) *
    ‖F x z‖) 2 volume with hA
  set Bf : ι → ℝ≥0∞ := fun x => eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-q / 2) *
    ‖ψ x z‖) 2 volume with hB
  have h1 : ENNReal.ofReal |∑ x, (π x)⁻¹ * ∫ z, ⟪F x z, ψ x z⟫_ℝ| ≤
      ∑ x, c x * (A x * Bf x) := by
    refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun x _ => abs_nonneg _]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [abs_mul, abs_of_nonneg (inv_pos.mpr (hπ x)).le, ENNReal.ofReal_mul
      (inv_pos.mpr (hπ x)).le, ← Real.enorm_eq_ofReal_abs]
    exact mul_le_mul_right (weighted_fun_pairing_le (hF x) (hψ x) q ϖ) _
  have h2 : ∑ x, c x * (A x * Bf x) ≤ familyNorm c A * familyNorm c Bf := by
    have hcs := ENNReal.inner_le_Lp_mul_Lq (s := Finset.univ)
      (fun x => c x ^ (1 / 2 : ℝ) * A x) (fun x => c x ^ (1 / 2 : ℝ) * Bf x)
      Real.HolderConjugate.two_two
    have hsq : ∀ x, (c x ^ (1 / 2 : ℝ)) * (c x ^ (1 / 2 : ℝ)) = c x := fun x => by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    have hpow : ∀ (X : ℝ≥0∞) x, (c x ^ (1 / 2 : ℝ) * X) ^ (2 : ℝ) = c x * X ^ 2 := by
      intro X x
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
      norm_num
    unfold familyNorm
    calc ∑ x, c x * (A x * Bf x)
        = ∑ x, (c x ^ (1 / 2 : ℝ) * A x) * (c x ^ (1 / 2 : ℝ) * Bf x) :=
          Finset.sum_congr rfl fun x _ => by rw [mul_mul_mul_comm, hsq]
      _ ≤ _ := hcs
      _ = _ := by simp only [hpow]
  exact h1.trans h2

end Family

section Rev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orderedDerivative_snoc {a : ℕ} (α : DerivativeWord2 (a + 1)) (g : Vec 2 → E) :
    orderedDerivative α g = fun x => fderiv ℝ (orderedDerivative (fun i : Fin a => α i.castSucc) g)
      x (basisVec (α (Fin.last a))) := by
  unfold orderedDerivative
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
  rfl

/-- Reverse derivatives are the ordered derivatives of the reversed word. -/
theorem orderedDerivativeRev_eq_comp_rev : ∀ {a : ℕ} (w : DerivativeWord2 a) (φ : Vec 2 → E),
    orderedDerivativeRev w φ = orderedDerivative (w ∘ Fin.rev) φ
  | 0, w, φ => by simp [orderedDerivativeRev, orderedDerivative]
  | a + 1, w, φ => by
    rw [orderedDerivativeRev_succ, orderedDerivativeRev_eq_comp_rev (fun i : Fin a => w i.succ),
      orderedDerivative_snoc (w ∘ Fin.rev)]
    simp only [Function.comp_apply, Fin.rev_castSucc, Fin.rev_last]
    rfl

/-- A reverse derivative is one term of the word sum. -/
theorem norm_orderedDerivativeRev_le {a : ℕ} (w : DerivativeWord2 a) (φ : Vec 2 → E) (z : Vec 2) :
    ‖orderedDerivativeRev w φ z‖ ≤
      Real.sqrt (∑ w' : DerivativeWord2 a, ‖orderedDerivative w' φ z‖ ^ 2) := by
  rw [orderedDerivativeRev_eq_comp_rev]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun w' : DerivativeWord2 a => ‖orderedDerivative w' φ z‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ (w ∘ Fin.rev))

end Rev

section Decomp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- **The pairing with the Bessel weight**, as pairings of `ampFun r A B` with even derivatives of
the test. -/
theorem integral_inner_besselWeight {r : ℝ} (hr : 0 ≤ r) (ϖ : ℝ) (k : ℕ) {A B : Vec 2 → E}
    (hA : IsBandAmp r 0 A) (hB : IsBandAmp r 0 B) {φ : Vec 2 → E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ z, ⟪ampFun r (fun θ => besselWeight ϖ k θ • A θ) (fun θ => besselWeight ϖ k θ • B θ) z,
        φ z⟫_ℝ =
      ∑ i ∈ Finset.range (k + 1), ∑ u : Fin i → Fin 2,
        ((k.choose i : ℝ) * (-(ϖ ^ 2)⁻¹) ^ i) *
          ∫ z, ⟪ampFun r A B z, orderedDerivativeRev (Fin.append u u) φ z⟫_ℝ := by
  have hint : ∀ (i : ℕ) (u : Fin i → Fin 2), Integrable (fun z =>
      ((k.choose i : ℝ) * (-(ϖ ^ 2)⁻¹) ^ i) *
        ⟪orderedDerivative (Fin.append u u) (ampFun r A B) z, φ z⟫_ℝ) := fun i u =>
    (integrable_inner_compact (continuous_orderedDerivative_ampFun hr hA hB _) hφ.continuous
      hφc).const_mul _
  rw [ampFun_besselWeight_eq hr ϖ k hA hB]
  simp only [sum_inner, real_inner_smul_left]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun u _ => hint i u]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun u _ => hint i u]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_const_mul, integral_inner_orderedDerivative_ampFun hr (Fin.append u u)
    hA.integrableOn hB.integrableOn hφ hφc]
  have h1 : ((-1 : ℝ)) ^ (i + i) = 1 := by rw [← two_mul, pow_mul]; norm_num
  rw [h1, one_mul]

end Decomp

section Main

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]

/-- **The `R`-scale negative norm of order `2k` of a Bessel-weighted band-limited family.** -/
theorem negJetNorm_besselWeight_le (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {r : ℝ} (hr : 0 ≤ r)
    (p k : ℕ) {ϖ : ℝ} (hϖ : 0 < ϖ) {A B : ∀ x, Vec 2 → h x}
    (hA : ∀ x, IsBandAmp r p (A x)) (hB : ∀ x, IsBandAmp r p (B x)) :
    negJetNorm π p (k + k) ϖ ϖ⁻¹ (fun x => ampFun r (fun θ => besselWeight ϖ k θ • A x θ)
        (fun θ => besselWeight ϖ k θ • B x θ)) ≤
      ENNReal.ofReal (besselDualConst k) *
        (ENNReal.ofReal (gaussJetConst p 0) * ampJetIntegral π p 0 ϖ A B ^ (1 / 2 : ℝ)) := by
  set c : ι → ℝ≥0∞ := fun x => ENNReal.ofReal ((π x)⁻¹) with hc
  set NG := ENNReal.ofReal (gaussJetConst p 0) * ampJetIntegral π p 0 ϖ A B ^ (1 / 2 : ℝ)
    with hNG
  have hA0 : ∀ x, IsBandAmp r 0 (A x) := fun x => (hA x).of_le (Nat.zero_le _)
  have hB0 : ∀ x, IsBandAmp r 0 (B x) := fun x => (hB x).of_le (Nat.zero_le _)
  have hG : ∀ x, Continuous (ampFun r (A x) (B x)) := fun x =>
    (ampFun_contDiff hr 0 (hA0 x).integrableOn (hB0 x).integrableOn).continuous
  have hGN : familyNorm c (fun x => eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^
      ((p : ℝ) / 2) * ‖ampFun r (A x) (B x) z‖) 2 volume) ≤ NG := by
    refine le_trans (le_of_eq ?_) (weightedJetNorm_ampFun_le (M := 0) π hr hϖ hA hB)
    rw [weightedJetNorm_eq_familyNorm, Finset.sum_range_one]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one, one_mul]
    congr 1
    funext x
    congr 1
    funext z
    congr 1
    rw [Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    simp [orderedDerivative]
  unfold negJetNorm
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hφn => ?_
  set T : ℕ → ℝ≥0∞ := fun a => familyNorm c (fun x => eLpNorm (fun z =>
    (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p : ℝ) / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (φ x) z‖ ^ 2)) 2 volume) with hT
  have hTa : ∀ a ≤ k + k, ENNReal.ofReal ((ϖ⁻¹) ^ a / (a.factorial : ℝ)) * T a ≤ 1 :=
    fun a ha => by
      rw [weightedJetNorm_eq_familyNorm] at hφn
      exact le_trans (Finset.single_le_sum (f := fun a =>
        ENNReal.ofReal ((ϖ⁻¹) ^ a / (a.factorial : ℝ)) * T a) (fun _ _ => bot_le)
        (Finset.mem_range.2 (Nat.lt_succ_of_le ha))) hφn
  set κ : ℕ → ℝ := fun i => (k.choose i : ℝ) * (-(ϖ ^ 2)⁻¹) ^ i with hκ
  set S : (i : ℕ) → (Fin i → Fin 2) → ℝ := fun i u => ∑ x, (π x)⁻¹ *
    ∫ z, ⟪ampFun r (A x) (B x) z, orderedDerivativeRev (Fin.append u u) (φ x) z⟫_ℝ with hS
  have hP : ∑ x, (π x)⁻¹ * ∫ z, ⟪ampFun r (fun θ => besselWeight ϖ k θ • A x θ)
      (fun θ => besselWeight ϖ k θ • B x θ) z, φ x z⟫_ℝ =
      ∑ i ∈ Finset.range (k + 1), ∑ u : Fin i → Fin 2, κ i * S i u := by
    simp only [integral_inner_besselWeight hr ϖ k (hA0 _) (hB0 _) (hφ _).1 (hφ _).2,
      Finset.mul_sum, hS]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hSb : ∀ i (u : Fin i → Fin 2), ENNReal.ofReal |S i u| ≤ NG * T (i + i) := by
    intro i u
    have hψ : ∀ x, Continuous (orderedDerivativeRev (Fin.append u u) (φ x)) := fun x =>
      (orderedDerivativeRev_test (hφ x).1 (hφ x).2 (Fin.append u u)).1.continuous
    refine (weighted_fun_family_pairing_le π hπ (fun x => ampFun r (A x) (B x))
      (fun x => orderedDerivativeRev (Fin.append u u) (φ x))
      (fun x => (hG x).aestronglyMeasurable) (fun x => (hψ x).aestronglyMeasurable)
      p ϖ).trans (mul_le_mul' hGN (familyNorm_mono _ fun x => ?_))
    have hwc := weight_continuous ϖ (-(p : ℝ))
    refine eLpNorm_mono_real ((hwc.mul (hψ x).norm).aestronglyMeasurable) fun z => ?_
    have hw0 : 0 ≤ (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (mul_nonneg hw0 (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (norm_orderedDerivativeRev_le _ _ z) hw0
  have hκT : ∀ i ∈ Finset.range (k + 1), ENNReal.ofReal |κ i| * T (i + i) ≤
      ENNReal.ofReal ((k.choose i : ℝ) * ((i + i).factorial : ℝ)) := by
    intro i hi
    have hik : i + i ≤ k + k := by have := Finset.mem_range.1 hi; omega
    have hf : (0 : ℝ) < ((i + i).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have habs : |κ i| = ((k.choose i : ℝ) * ((i + i).factorial : ℝ)) *
        ((ϖ⁻¹) ^ (i + i) / ((i + i).factorial : ℝ)) := by
      rw [hκ]
      simp only [abs_mul, abs_pow, abs_neg, Nat.abs_cast, abs_inv, abs_of_pos (pow_pos hϖ 2)]
      rw [← two_mul, pow_mul, inv_pow]
      field_simp
      rw [mul_assoc, ← mul_pow, one_div, mul_inv_cancel₀ (pow_ne_zero 2 hϖ.ne'), one_pow,
        mul_one]
    rw [habs, ENNReal.ofReal_mul (by positivity), mul_assoc]
    calc _ ≤ ENNReal.ofReal ((k.choose i : ℝ) * ((i + i).factorial : ℝ)) * 1 :=
          mul_le_mul' le_rfl (hTa (i + i) hik)
      _ = _ := mul_one _
  rw [hP]
  calc ENNReal.ofReal |∑ i ∈ Finset.range (k + 1), ∑ u : Fin i → Fin 2, κ i * S i u|
      ≤ ∑ i ∈ Finset.range (k + 1), ∑ u : Fin i → Fin 2,
          ENNReal.ofReal |κ i| * ENNReal.ofReal |S i u| := by
        refine (ENNReal.ofReal_le_ofReal ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _))).trans ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun u _ => abs_nonneg _]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun u _ => abs_nonneg _]
        refine Finset.sum_le_sum fun u _ => ?_
        rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ u : Fin i → Fin 2,
          NG * ENNReal.ofReal ((k.choose i : ℝ) * ((i + i).factorial : ℝ)) := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun u _ => ?_
        calc ENNReal.ofReal |κ i| * ENNReal.ofReal |S i u|
            ≤ ENNReal.ofReal |κ i| * (NG * T (i + i)) := mul_le_mul' le_rfl (hSb i u)
          _ = NG * (ENNReal.ofReal |κ i| * T (i + i)) := by ring
          _ ≤ _ := mul_le_mul' le_rfl (hκT i hi)
    _ = ENNReal.ofReal (besselDualConst k) * NG := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        rw [besselDualConst, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h2 : ENNReal.ofReal ((2 : ℝ) ^ i) = ((2 ^ i : ℕ) : ℝ≥0∞) := by
          rw [ENNReal.ofReal_pow (by norm_num)]
          simp
        rw [ENNReal.ofReal_mul (p := (2 : ℝ) ^ i) (by positivity), h2,
          ENNReal.ofReal_mul (p := (k.choose i : ℝ)) (by positivity)]
        ring

end Main

end AVRegularity.CycleWords.Assembly
end

section
open Metric Homogenization
namespace AVRegularity.CycleWords.Assembly

/-! **The jets of the Bessel multiplier** (a step of `SeamOldScalarStatement`). The multiplier
`ν_k(θ) = (1 + |θ/ϖ|²)^{-k}` turns the positive amplitude jets of the old output into its `R`-scale
negative norm (`R = ϖ⁻¹`). Its normalized jets decay like the multiplier itself:
`ϖ^l ‖Dˡν_k(θ)‖ ≤ (16/3)^k (8l)^l (1 + ‖θ‖²/ϖ²)^{-k}` (`bessel_jet_le`, sup norm).

Proof: `ν_k` is the restriction of the analytic `besselC k ζ = (1 + ζ₀² + ζ₁²)^{-k}` along
`θ ↦ θ/ϖ` (`fibreEmbed (ϖ²)`). On the polydisc of radius `(1 + ‖t‖)/8` around `t = θ/ϖ` the
denominator stays above `(3/16)(1 + ‖t‖²)` (`besselDen_lower`), so Cauchy's estimate
(`norm_iteratedFDeriv_le_of_closedBall`) bounds the complex jets, and the real jets of the
restriction are at most those times `‖θ ↦ θ/ϖ‖ ^ l ≤ ϖ^{-l}` (`norm_iteratedFDeriv_comp_clm_le`).

For `k = 0` the multiplier is `1` and the bound is `(8l)^l`, which is `1` for `l = 0`. For `l = 0`
the bound is `(16/3)^k ν_k`-like, the value bound on the real line. For `θ = 0` the polydisc has
radius `1/8` and the denominator is at least `3/16`. -/

/-- The denominator `1 + ζ₀² + ζ₁²` of the Bessel multiplier. -/
def besselDen (ζ : Fin 2 → ℂ) : ℂ := 1 + ζ 0 ^ 2 + ζ 1 ^ 2

/-- The complexified Bessel multiplier `(1 + ζ₀² + ζ₁²)^{-k}`. -/
def besselC (k : ℕ) (ζ : Fin 2 → ℂ) : ℂ := (besselDen ζ)⁻¹ ^ k

theorem continuous_besselDen : Continuous besselDen := by
  unfold besselDen
  fun_prop

theorem isOpen_besselDom : IsOpen {ζ : Fin 2 → ℂ | besselDen ζ ≠ 0} :=
  isOpen_ne_fun continuous_besselDen continuous_const

theorem besselC_analyticOnNhd (k : ℕ) :
    AnalyticOnNhd ℂ (besselC k) {ζ : Fin 2 → ℂ | besselDen ζ ≠ 0} := by
  intro ζ hζ
  have h0 : AnalyticAt ℂ (fun ζ : Fin 2 → ℂ => ζ 0) ζ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt ζ
  have h1 : AnalyticAt ℂ (fun ζ : Fin 2 → ℂ => ζ 1) ζ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt ζ
  have hp : AnalyticAt ℂ besselDen ζ := (analyticAt_const.add (h0.pow 2)).add (h1.pow 2)
  exact (hp.inv hζ).pow k

/-- **The denominator on the polydisc** of radius `(1 + ‖t‖)/8` around a real point `t`. -/
theorem besselDen_lower {t : Vec 2} {ζ : Fin 2 → ℂ}
    (hζ : ζ ∈ closedBall (fun i => ((t i : ℝ) : ℂ)) ((1 + ‖t‖) / 8)) :
    3 / 16 * (1 + ‖t‖ ^ 2) ≤ ‖besselDen ζ‖ := by
  set s := ‖t‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  set w : Fin 2 → ℂ := ζ - fun i => ((t i : ℝ) : ℂ) with hwdef
  have hw : ∀ i, ‖w i‖ ≤ (1 + s) / 8 := fun i => by
    rw [mem_closedBall, dist_eq_norm] at hζ
    exact (norm_le_pi_norm w i).trans hζ
  have ht : ∀ i, |t i| ≤ s := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm t i
  have hsum : s ^ 2 ≤ t 0 ^ 2 + t 1 ^ 2 := by
    have hle : s ≤ Real.sqrt (t 0 ^ 2 + t 1 ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
      rw [Fin.forall_fin_two, Real.norm_eq_abs, Real.norm_eq_abs]
      exact ⟨Real.abs_le_sqrt (by nlinarith [sq_nonneg (t 1)]),
        Real.abs_le_sqrt (by nlinarith [sq_nonneg (t 0)])⟩
    have := pow_le_pow_left₀ hs0 hle 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have hζi : ∀ i, ζ i = ((t i : ℝ) : ℂ) + w i := fun i => by simp [hwdef]
  set P : ℝ := 1 + t 0 ^ 2 + t 1 ^ 2 with hP
  set Bc : ℂ := 2 * ((t 0 : ℝ) : ℂ) * w 0 + w 0 ^ 2 + 2 * ((t 1 : ℝ) : ℂ) * w 1 + w 1 ^ 2
    with hBc
  have he : besselDen ζ = (P : ℂ) + Bc := by
    simp only [besselDen, hζi, hP, hBc]
    push_cast
    ring
  have hPn : ‖(P : ℂ)‖ = P := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hBn : ‖Bc‖ ≤ 2 * |t 0| * ‖w 0‖ + ‖w 0‖ ^ 2 + 2 * |t 1| * ‖w 1‖ + ‖w 1‖ ^ 2 := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hn0 : ‖2 * ((t 0 : ℝ) : ℂ) * w 0‖ = 2 * |t 0| * ‖w 0‖ := by
      rw [norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_eq_abs]
    have hn1 : ‖2 * ((t 1 : ℝ) : ℂ) * w 1‖ = 2 * |t 1| * ‖w 1‖ := by
      rw [norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_eq_abs]
    calc ‖Bc‖ ≤ ‖2 * ((t 0 : ℝ) : ℂ) * w 0‖ + ‖w 0 ^ 2‖ + ‖2 * ((t 1 : ℝ) : ℂ) * w 1‖ +
          ‖w 1 ^ 2‖ := by
          refine (norm_add_le _ _).trans ?_
          refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
          exact add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by rw [hn0, hn1, norm_pow, norm_pow]
  have hlow : P - ‖Bc‖ ≤ ‖besselDen ζ‖ := by
    have := norm_sub_norm_le (P : ℂ) (-Bc)
    rw [norm_neg, sub_neg_eq_add, hPn] at this
    rw [he]
    exact this
  have hR := hw 0
  have hR1 := hw 1
  have h0 := ht 0
  have h1 := ht 1
  have hw0 := norm_nonneg (w 0)
  have hw1 := norm_nonneg (w 1)
  have hB : ‖Bc‖ ≤ 4 * s * ((1 + s) / 8) + 2 * ((1 + s) / 8) ^ 2 := by
    refine hBn.trans ?_
    have e0 : 2 * |t 0| * ‖w 0‖ ≤ 2 * s * ((1 + s) / 8) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h0 (by norm_num)) hR hw0 (by positivity)
    have e1 : 2 * |t 1| * ‖w 1‖ ≤ 2 * s * ((1 + s) / 8) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hR1 hw1 (by positivity)
    have f0 : ‖w 0‖ ^ 2 ≤ ((1 + s) / 8) ^ 2 := pow_le_pow_left₀ hw0 hR 2
    have f1 : ‖w 1‖ ^ 2 ≤ ((1 + s) / 8) ^ 2 := pow_le_pow_left₀ hw1 hR1 2
    linarith
  have hpoly : 3 / 16 * (1 + s ^ 2) ≤ 1 + s ^ 2 - (4 * s * ((1 + s) / 8) + 2 * ((1 + s) / 8) ^ 2) := by
    nlinarith [sq_nonneg (s - 1)]
  have hPs : 1 + s ^ 2 ≤ P := by rw [hP]; linarith
  linarith

/-- The value bound on the polydisc. -/
theorem besselC_norm_le {k : ℕ} {t : Vec 2} {ζ : Fin 2 → ℂ}
    (hζ : ζ ∈ closedBall (fun i => ((t i : ℝ) : ℂ)) ((1 + ‖t‖) / 8)) :
    ‖besselC k ζ‖ ≤ (16 / 3) ^ k * ((1 + ‖t‖ ^ 2)⁻¹) ^ k := by
  have hlow := besselDen_lower hζ
  have hpos : 0 < 3 / 16 * (1 + ‖t‖ ^ 2) := by positivity
  rw [besselC, norm_pow, norm_inv, ← mul_pow]
  refine pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) ?_ k
  calc ‖besselDen ζ‖⁻¹ ≤ (3 / 16 * (1 + ‖t‖ ^ 2))⁻¹ := inv_anti₀ hpos hlow
    _ = 16 / 3 * (1 + ‖t‖ ^ 2)⁻¹ := by rw [mul_inv]; norm_num

/-- **The normalized jets of the Bessel multiplier** `θ ↦ (1 + |θ/ϖ|²)^{-k}` (sup norm). -/
theorem bessel_jet_le (k l : ℕ) {ϖ : ℝ} (hϖ : 0 < ϖ) (θ : Vec 2) :
    ϖ ^ l * ‖iteratedFDeriv ℝ l (fun θ' => besselC k (fibreEmbed (ϖ ^ 2) θ')) θ‖ ≤
      (16 / 3) ^ k * ((1 + (‖θ‖ / ϖ) ^ 2)⁻¹) ^ k * (8 * l) ^ l := by
  set L := fibreEmbed (ϖ ^ 2) with hLdef
  have hsq : Real.sqrt (ϖ ^ 2) = ϖ := Real.sqrt_sq hϖ.le
  have hL : ‖L‖ ≤ ϖ⁻¹ := by
    have := norm_fibreEmbed_le (pow_pos hϖ 2)
    rwa [hsq] at this
  set t : Vec 2 := ϖ⁻¹ • θ with htdef
  have hLt : L θ = fun i => ((t i : ℝ) : ℂ) := by
    funext i
    rw [hLdef, fibreEmbed_apply]
    simp [planeFibreFrequency, hsq, htdef, div_eq_inv_mul]
  have hnt : ‖t‖ = ‖θ‖ / ϖ := by
    rw [htdef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hϖ, div_eq_inv_mul]
  set R : ℝ := (1 + ‖t‖) / 8 with hRdef
  have hR : 0 < R := by positivity
  have hR8 : 1 / 8 ≤ R := by
    rw [hRdef]
    have := norm_nonneg t
    linarith
  have hball : closedBall (L θ) R ⊆ {ζ : Fin 2 → ℂ | besselDen ζ ≠ 0} := fun ζ hζ => by
    rw [hLt] at hζ
    have hlow := besselDen_lower hζ
    exact norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hlow)
  have hM : ∀ ζ ∈ closedBall (L θ) R, ‖besselC k ζ‖ ≤ (16 / 3) ^ k * ((1 + ‖t‖ ^ 2)⁻¹) ^ k :=
    fun ζ hζ => by
      rw [hLt] at hζ
      exact besselC_norm_le hζ
  have hC := AVRegularity.Analysis.norm_iteratedFDeriv_le_of_closedBall isOpen_besselDom
    (besselC_analyticOnNhd k) l hR hball hM
  have hcomp := norm_iteratedFDeriv_comp_clm_le isOpen_besselDom (besselC_analyticOnNhd k) L
    (hball (mem_closedBall_self hR.le)) l
  have hϖL : ϖ ^ l * ‖L‖ ^ l ≤ 1 := by
    rw [← mul_pow]
    refine pow_le_one₀ (by positivity) ?_
    calc ϖ * ‖L‖ ≤ ϖ * ϖ⁻¹ := mul_le_mul_of_nonneg_left hL hϖ.le
      _ = 1 := mul_inv_cancel₀ hϖ.ne'
  have hD0 : 0 ≤ ‖iteratedFDeriv ℂ l (besselC k) (L θ)‖ := norm_nonneg _
  have hM0 : 0 ≤ (16 / 3 : ℝ) ^ k * ((1 + ‖t‖ ^ 2)⁻¹) ^ k := by positivity
  have hRl : (l : ℝ) ^ l / R ^ l ≤ (8 * l) ^ l := by
    rw [div_le_iff₀ (pow_pos hR l), mul_pow, mul_comm ((8 : ℝ) ^ l), mul_assoc]
    refine le_mul_of_one_le_right (by positivity) ?_
    rw [← mul_pow]
    exact one_le_pow₀ (by linarith)
  calc ϖ ^ l * ‖iteratedFDeriv ℝ l (fun θ' => besselC k (L θ')) θ‖
      ≤ ϖ ^ l * (‖iteratedFDeriv ℂ l (besselC k) (L θ)‖ * ‖L‖ ^ l) :=
        mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = ‖iteratedFDeriv ℂ l (besselC k) (L θ)‖ * (ϖ ^ l * ‖L‖ ^ l) := by ring
    _ ≤ ‖iteratedFDeriv ℂ l (besselC k) (L θ)‖ := mul_le_of_le_one_right hD0 hϖL
    _ ≤ (16 / 3) ^ k * ((1 + ‖t‖ ^ 2)⁻¹) ^ k * (l : ℝ) ^ l / R ^ l := hC
    _ = (16 / 3) ^ k * ((1 + ‖t‖ ^ 2)⁻¹) ^ k * ((l : ℝ) ^ l / R ^ l) := by ring
    _ ≤ (16 / 3) ^ k * ((1 + ‖t‖ ^ 2)⁻¹) ^ k * (8 * l) ^ l :=
        mul_le_mul_of_nonneg_left hRl hM0
    _ = _ := by rw [hnt]

end AVRegularity.CycleWords.Assembly
end
