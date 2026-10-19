-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.OldScalar.Bessel
public import AVRegularity.CycleWords.Seam.OldScalar.WindowRegions
import AVRegularity.CycleWords.MixedWords.FactorOfMomentsRepresentation
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import AVRegularity.CycleWords.Seam.LetterTransposeNorm

@[expose] public noncomputable section

section
open Metric Homogenization
namespace AVRegularity.CycleWords.Assembly

/-! **The gauge divided by the Bessel weight**. The rotation that turns X1's gauged pair into
the old output's amplitudes is `e^Ξ`; dividing by the Bessel weight `μ_k` multiplies it by
`ν_k = μ_k⁻¹`. The product `E = ν_k e^Ξ` has normalized jets at most
`2^m (16/3)^k (8m + 1)^m ν̃_k(θ)` times those of `e^Ξ`, with `ν̃_k(θ) = (1 + ‖θ‖²/ϖ²)^{-k}`
(`besselGauge_jet_le`; Leibniz and `bessel_jet_le`). The multiplier is real
(`besselPlane_eq_ofReal`), so the product rotates the pair by `ν_k` times the gauge.

Degenerate cases:
- `k = 0`: `E = e^Ξ` and the factor is `2^m (8m+1)^m`.
- `m = 0`: the value bound `|E| ≤ (16/3)^k ν̃_k |e^Ξ|`.
- `θ = 0`: `ν_k(0) = 1`. -/

/-- The Bessel multiplier `θ ↦ (1 + |θ/ϖ|²)^{-k}` as a complex function. -/
def besselPlane (ϖ : ℝ) (k : ℕ) (θ : Vec 2) : ℂ := besselC k (fibreEmbed (ϖ ^ 2) θ)

/-- The real multiplier `(1 + |θ|²/ϖ²)^{-k}`. -/
def besselInv (ϖ : ℝ) (k : ℕ) (θ : Vec 2) : ℝ := ((1 + vecDot θ θ / ϖ ^ 2)⁻¹) ^ k

theorem besselPlane_eq_ofReal {ϖ : ℝ} (hϖ : 0 < ϖ) (k : ℕ) (θ : Vec 2) :
    besselPlane ϖ k θ = (besselInv ϖ k θ : ℂ) := by
  have hsq : Real.sqrt (ϖ ^ 2) = ϖ := Real.sqrt_sq hϖ.le
  unfold besselPlane besselInv besselC besselDen
  rw [fibreEmbed_apply]
  simp only [planeFibreFrequency, hsq, vecDot, Fin.sum_univ_two]
  push_cast
  congr 2
  field_simp
  ring

theorem besselDen_ne_zero_of_real (t : Vec 2) :
    besselDen (fun i => ((t i : ℝ) : ℂ)) ≠ 0 := by
  have h := besselDen_lower (t := t) (ζ := fun i => ((t i : ℝ) : ℂ))
    (mem_closedBall_self (by positivity))
  exact norm_pos_iff.1 (lt_of_lt_of_le (by positivity) h)

/-- The multiplier is smooth. -/
theorem besselPlane_contDiff {ϖ : ℝ} (hϖ : 0 < ϖ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (besselPlane ϖ k) := by
  have hsq : Real.sqrt (ϖ ^ 2) = ϖ := Real.sqrt_sq hϖ.le
  refine contDiff_iff_contDiffAt.2 fun θ => ?_
  set L := fibreEmbed (ϖ ^ 2) with hLdef
  have hLθ : L θ = fun i => (((ϖ⁻¹ • θ) i : ℝ) : ℂ) := by
    funext i
    rw [hLdef, fibreEmbed_apply]
    simp [planeFibreFrequency, hsq, div_eq_inv_mul]
  have hmem : L θ ∈ {ζ : Fin 2 → ℂ | besselDen ζ ≠ 0} := by
    rw [hLθ]
    exact besselDen_ne_zero_of_real _
  have hA := (besselC_analyticOnNhd k (L θ) hmem).contDiffAt (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
  exact (hA.restrict_scalars ℝ).comp θ L.contDiff.contDiffAt

/-- **The jets of the Bessel multiplier times a gauge.** -/
theorem besselGauge_jet_le {U : Set (Vec 2)} (hU : IsOpen U) {g : Vec 2 → ℂ} {m : ℕ}
    (hg : ContDiffOn ℝ m g U) (k : ℕ) {ϖ : ℝ} (hϖ : 0 < ϖ) {θ : Vec 2} (hθ : θ ∈ U)
    {Cg : ℝ} (hgj : ∀ j ≤ m, ϖ ^ j * ‖iteratedFDeriv ℝ j g θ‖ ≤ Cg) :
    ∀ l ≤ m, ϖ ^ l * ‖iteratedFDeriv ℝ l (fun θ' => besselPlane ϖ k θ' * g θ') θ‖ ≤
      2 ^ m * ((16 / 3) ^ k * ((1 + (‖θ‖ / ϖ) ^ 2)⁻¹) ^ k * (8 * m + 1) ^ m) * Cg := by
  intro l hl
  have hCg : 0 ≤ Cg := (mul_nonneg (pow_nonneg hϖ.le 0) (norm_nonneg _)).trans (hgj 0 (Nat.zero_le _))
  set W : ℝ := (16 / 3) ^ k * ((1 + (‖θ‖ / ϖ) ^ 2)⁻¹) ^ k * (8 * m + 1) ^ m with hW
  have hW0 : 0 ≤ W := by positivity
  have hb : ContDiffOn ℝ m (besselPlane ϖ k) U :=
    ((besselPlane_contDiff hϖ k).of_le (by exact_mod_cast le_top)).contDiffOn
  have hprod := norm_iteratedFDerivWithin_mul_le hb hg hU.uniqueDiffOn hθ (n := l)
    (by exact_mod_cast hl)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hθ] at hprod
  have hbj : ∀ i ≤ l, ϖ ^ i * ‖iteratedFDeriv ℝ i (besselPlane ϖ k) θ‖ ≤ W := by
    intro i hi
    have h := bessel_jet_le k i hϖ θ
    refine h.trans ?_
    rw [hW]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((8 : ℝ) * i) ^ i ≤ (8 * m + 1) ^ i :=
          pow_le_pow_left₀ (by positivity) (by
            have : (i : ℝ) ≤ m := by exact_mod_cast hi.trans hl
            linarith) i
      _ ≤ (8 * m + 1) ^ m := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
          (hi.trans hl)
  calc ϖ ^ l * ‖iteratedFDeriv ℝ l (fun θ' => besselPlane ϖ k θ' * g θ') θ‖
      ≤ ϖ ^ l * ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (besselPlane ϖ k) θ‖ * ‖iteratedFDeriv ℝ (l - i) g θ‖ := by
        exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
          ((ϖ ^ i * ‖iteratedFDeriv ℝ i (besselPlane ϖ k) θ‖) *
            (ϖ ^ (l - i) * ‖iteratedFDeriv ℝ (l - i) g θ‖)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hil : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [show ϖ ^ l = ϖ ^ i * ϖ ^ (l - i) by rw [← pow_add, Nat.add_sub_of_le hil]]
        ring
    _ ≤ ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * (W * Cg) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hil : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        refine mul_le_mul_of_nonneg_left (mul_le_mul (hbj i hil) (hgj (l - i) (by omega))
          (by positivity) hW0) (by positivity)
    _ = 2 ^ l * (W * Cg) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ ≤ 2 ^ m * (W * Cg) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hl)
          (mul_nonneg hW0 hCg)
    _ = 2 ^ m * W * Cg := (mul_assoc _ _ _).symm

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! **The amplitude jets of the old output divided by the Bessel weight**. On the low disc
the cutoff amplitudes of the old output are `e^Ξ` times X1's pair `(Ã_c, Ã_s)`, whose jets are
at most `C₁(1 + x_ξ)^P J(θ)`. Dividing by `μ_k` rotates the pair by `ν_k e^Ξ`
(`besselGauge_jet_le`, `ampDerivNorm_rot_le`). The polynomial factor `(1 + x_ξ)^{p+P}` is
absorbed by `ν_k` when `p + P ≤ 2k` (`besselInv_poly_le`), so the jets of the divided amplitudes are
at most `C C_g C₁ J(θ)` (`amplitudeJetNorm_besselInv_le`).

Degenerate cases:
- `P = p = 0`, `k = 0`: no division; the rotation alone.
- `θ = 0`: every weight is `1`.
- `J = 0`: the divided amplitudes have zero jets at `θ`. -/

/-- **Absorption**: `(1 + ‖θ‖²/ϖ²)^{-k} (1 + |θ|/ϖ)^{n} ≤ 4^k` for `n ≤ 2k`. -/
theorem besselInv_poly_le {ϖ : ℝ} (hϖ : 0 < ϖ) (θ : Vec 2) {n k : ℕ} (hn : n ≤ k + k) :
    ((1 + (‖θ‖ / ϖ) ^ 2)⁻¹) ^ k * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ n ≤ 4 ^ k := by
  set s := ‖θ‖ / ϖ with hs
  set x := Real.sqrt (vecDot θ θ) / ϖ with hx
  have hx0 : 0 ≤ x := by positivity
  have hdot : vecDot θ θ ≤ 2 * ‖θ‖ ^ 2 := by
    have h0 : |θ 0| ≤ ‖θ‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm θ 0
    have h1 : |θ 1| ≤ ‖θ‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm θ 1
    have e0 : θ 0 * θ 0 ≤ ‖θ‖ ^ 2 := by
      rw [← abs_mul_abs_self, sq]; exact mul_le_mul h0 h0 (abs_nonneg _) (norm_nonneg _)
    have e1 : θ 1 * θ 1 ≤ ‖θ‖ ^ 2 := by
      rw [← abs_mul_abs_self, sq]; exact mul_le_mul h1 h1 (abs_nonneg _) (norm_nonneg _)
    simp only [vecDot, Fin.sum_univ_two]
    linarith
  have hx2 : x ^ 2 ≤ 2 * s ^ 2 := by
    rw [hx, hs, div_pow, div_pow, Real.sq_sqrt (show 0 ≤ vecDot θ θ from Finset.sum_nonneg fun i _ => mul_self_nonneg (θ i))]
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right hdot (by positivity)
  have hbase : (1 + x) ^ 2 ≤ 4 * (1 + s ^ 2) := by nlinarith [sq_nonneg (x - 1)]
  have hpos : 0 < 1 + s ^ 2 := by positivity
  have h1 : (1 + x) ^ n ≤ (1 + x) ^ (k + k) := pow_le_pow_right₀ (by linarith) hn
  have h2 : (1 + x) ^ (k + k) ≤ (4 * (1 + s ^ 2)) ^ k := by
    rw [← two_mul, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hbase k
  calc ((1 + s ^ 2)⁻¹) ^ k * (1 + x) ^ n ≤ ((1 + s ^ 2)⁻¹) ^ k * (4 * (1 + s ^ 2)) ^ k :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = 4 ^ k := by
        rw [← mul_pow, ← mul_assoc, mul_comm _ (4 : ℝ), mul_assoc, inv_mul_cancel₀ hpos.ne',
          mul_one]

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The jets of the amplitudes divided by the Bessel weight.** -/
theorem amplitudeJetNorm_besselInv_le (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {p P k : ℕ}
    (hk : p + P ≤ k + k) {ϖ : ℝ} (hϖ : 0 < ϖ) {U : Set (Vec 2)} (hU : IsOpen U)
    {Eg : Vec 2 → ℂ} (hEg : ContDiffOn ℝ p Eg U) {A B Ac As : ∀ x, Vec 2 → h x}
    (hAc : ∀ x, ContDiff ℝ p (Ac x)) (hAs : ∀ x, ContDiff ℝ p (As x))
    (hrot : ∀ θ ∈ U, ∀ x, A x θ = (Eg θ).re • Ac x θ + (Eg θ).im • As x θ ∧
      B x θ = (Eg θ).re • As x θ - (Eg θ).im • Ac x θ)
    {θ : Vec 2} (hθ : θ ∈ U) {Cg C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgj : ∀ j ≤ p, ϖ ^ j * ‖iteratedFDeriv ℝ j Eg θ‖ ≤
      Cg * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ p)
    {J : ℝ≥0∞}
    (hX1 : ampDerivNorm π p ϖ Ac As θ ≤ ENNReal.ofReal (C₁ * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P) * J) :
    amplitudeJetNorm π p ϖ (fun x θ => besselInv ϖ k θ • A x θ)
        (fun x θ => besselInv ϖ k θ • B x θ) θ ≤
      ENNReal.ofReal (((p + 1 : ℕ) : ℝ) * 2 ^ p * (2 * ((p + 1 : ℕ) : ℝ) *
        (2 ^ p * ((16 / 3) ^ k * 4 ^ k * (8 * p + 1) ^ p) * Cg)) * C₁) * J := by
  set x := Real.sqrt (vecDot θ θ) / ϖ with hx
  have hx0 : 0 ≤ x := by positivity
  set W : ℝ := ((1 + (‖θ‖ / ϖ) ^ 2)⁻¹) ^ k with hW
  have hW0 : 0 ≤ W := by positivity
  have hCg : 0 ≤ Cg := by
    have h0 := (mul_nonneg (pow_nonneg hϖ.le 0) (norm_nonneg _)).trans (hgj 0 (Nat.zero_le _))
    by_contra hneg
    have : Cg * (1 + x) ^ p < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hneg) (pow_pos (by linarith) _)
    linarith
  set E : Vec 2 → ℂ := fun θ' => besselPlane ϖ k θ' * Eg θ' with hE
  have hEc : ContDiffOn ℝ p E U :=
    (((besselPlane_contDiff hϖ k).of_le (by exact_mod_cast le_top)).contDiffOn).mul hEg
  have hGj := besselGauge_jet_le hU hEg k hϖ hθ hgj
  set G : ℝ := 2 ^ p * ((16 / 3) ^ k * W * (8 * p + 1) ^ p) * (Cg * (1 + x) ^ p) with hG
  have hrot' : ∀ θ' ∈ U, ∀ y, besselInv ϖ k θ' • A y θ' =
      (E θ').re • Ac y θ' + (E θ').im • As y θ' ∧
      besselInv ϖ k θ' • B y θ' = (E θ').re • As y θ' - (E θ').im • Ac y θ' := by
    intro θ' hθ' y
    obtain ⟨h1, h2⟩ := hrot θ' hθ' y
    simp only [hE, besselPlane_eq_ofReal hϖ, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    rw [h1, h2]
    constructor
    · simp only [smul_add, smul_smul]
    · simp only [smul_sub, smul_smul]
  have hrotb := ampDerivNorm_rot_le hU hEc π hπ hAc hAs hrot' hθ hϖ.le (G := G) hGj
  have hjet := amplitudeJetNorm_le_ampDerivNorm π p hϖ.le
    (fun y θ' => besselInv ϖ k θ' • A y θ') (fun y θ' => besselInv ϖ k θ' • B y θ') θ
  have habs : W * (1 + x) ^ (p + P) ≤ 4 ^ k := besselInv_poly_le hϖ θ hk
  have hGP : G * (C₁ * (1 + x) ^ P) ≤
      2 ^ p * ((16 / 3) ^ k * 4 ^ k * (8 * p + 1) ^ p) * Cg * C₁ := by
    rw [hG]
    have e : 2 ^ p * ((16 / 3) ^ k * W * (8 * p + 1) ^ p) * (Cg * (1 + x) ^ p) *
        (C₁ * (1 + x) ^ P) = 2 ^ p * ((16 / 3) ^ k * (8 * p + 1) ^ p) * Cg * C₁ *
          (W * (1 + x) ^ (p + P)) := by
      rw [pow_add]
      ring
    rw [e]
    have : (0 : ℝ) ≤ 2 ^ p * ((16 / 3) ^ k * (8 * p + 1) ^ p) * Cg * C₁ := by positivity
    calc _ ≤ 2 ^ p * ((16 / 3) ^ k * (8 * p + 1) ^ p) * Cg * C₁ * 4 ^ k :=
          mul_le_mul_of_nonneg_left habs this
      _ = _ := by ring
  have hG0 : 0 ≤ G := by positivity
  calc amplitudeJetNorm π p ϖ (fun y θ' => besselInv ϖ k θ' • A y θ')
        (fun y θ' => besselInv ϖ k θ' • B y θ') θ
      ≤ ENNReal.ofReal (((p + 1 : ℕ) : ℝ) * 2 ^ p) *
          (ENNReal.ofReal (2 * ((p + 1 : ℕ) : ℝ) * G) * ampDerivNorm π p ϖ Ac As θ) :=
        hjet.trans (mul_le_mul' le_rfl hrotb)
    _ ≤ ENNReal.ofReal (((p + 1 : ℕ) : ℝ) * 2 ^ p) *
          (ENNReal.ofReal (2 * ((p + 1 : ℕ) : ℝ) * G) *
            (ENNReal.ofReal (C₁ * (1 + x) ^ P) * J)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hX1)
    _ = ENNReal.ofReal (((p + 1 : ℕ) : ℝ) * 2 ^ p * (2 * ((p + 1 : ℕ) : ℝ) *
          (G * (C₁ * (1 + x) ^ P)))) * J := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ ≤ _ := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have h2 : (0 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) * 2 ^ p := by positivity
        have h3 : (0 : ℝ) ≤ 2 * ((p + 1 : ℕ) : ℝ) := by positivity
        calc ((p + 1 : ℕ) : ℝ) * 2 ^ p * (2 * ((p + 1 : ℕ) : ℝ) * (G * (C₁ * (1 + x) ^ P)))
            ≤ ((p + 1 : ℕ) : ℝ) * 2 ^ p * (2 * ((p + 1 : ℕ) : ℝ) *
                (2 ^ p * ((16 / 3) ^ k * 4 ^ k * (8 * p + 1) ^ p) * Cg * C₁)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGP h3) h2
          _ = _ := by ring

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! **The old scalar bound from a factorized amplitude** (the core of
`SeamOldScalarStatement`). Let `g = ampFun r A B` be band-limited in the disc `|θ| ≤ r ≤ π`, with
`A, B` on a neighbourhood `U` of the disc equal to a gauge `E_g` times a pair `(Ã_c, Ã_s)` whose
jets are at most `C₁(1 + x_ξ)^P J(θ)`, `J` the normalized Bloch jets of a datum `F` (the
conclusion), and with the jets of `E_g` at most `C_g(1 + x_ξ)^p` (the gauge bound). Then, for
`p + P ≤ 2k`,
`‖g‖_{ϖ⁻¹,-2k;p} ≤ C ‖F‖_{moment n}` (`negJetNorm_le_of_factor`): write `A = μ_k(ν_k A)`; the
duality bound `negJetNorm_besselWeight_le` reduces to the jets of `ν_k A`, which
`amplitudeJetNorm_besselInv_le` bounds by `J`; they vanish off the disc
(`amplitudeJetNorm_eq_zero_of_gt`), so the jet integral is a cube integral
(`ampJetIntegral_le_of_disc`), bounded by the Bloch moment bound
(`lintegral_bloch_sum_sq_le_of_ae`).

For `r = 0` the amplitudes vanish off a null set and `g = 0`. For `F = 0` one has `J = 0`, so `g`
has zero negative norm. For `k = 0`, `p = P = 0` there is no division, only the duality bound and
the value fibres. -/

/-- The disc of radius `r ≤ π` lies in the frequency cube. -/
theorem mem_freqCube_of_vecDot_le {r : ℝ} (hr : 0 ≤ r) (hrπ : r ≤ Real.pi) {θ : Vec 2}
    (hθ : vecDot θ θ ≤ r ^ 2) : θ ∈ freqCube := by
  intro i
  have hv : vecDot θ θ = θ 0 ^ 2 + θ 1 ^ 2 := by simp [vecDot, Fin.sum_univ_two, sq]
  have hi : θ i ^ 2 ≤ Real.pi ^ 2 := by
    have hr2 : r ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ hr hrπ 2
    fin_cases i
    · simp only [Fin.zero_eta]; nlinarith [sq_nonneg (θ 1)]
    · simp only [Fin.mk_one]; nlinarith [sq_nonneg (θ 0)]
  have h := sq_le_sq.1 hi
  rwa [abs_of_pos Real.pi_pos] at h

/-- `μ_k ν_k = 1`. -/
theorem besselWeight_mul_besselInv (ϖ : ℝ) (k : ℕ) (θ : Vec 2) :
    besselWeight ϖ k θ * besselInv ϖ k θ = 1 := by
  have hv : 0 ≤ vecDot θ θ / ϖ ^ 2 :=
    div_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (sq_nonneg _)
  unfold besselWeight besselInv
  rw [← mul_pow, mul_inv_cancel₀ (by linarith), one_pow]

/-- The real multiplier `ν_k` is smooth. -/
theorem besselInv_contDiff (ϖ : ℝ) (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (besselInv ϖ k) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) fun θ : Vec 2 => 1 + vecDot θ θ / ϖ ^ 2 := by
    unfold vecDot
    fun_prop
  have hne : ∀ θ : Vec 2, 1 + vecDot θ θ / ϖ ^ 2 ≠ 0 := fun θ => by
    have : 0 ≤ vecDot θ θ / ϖ ^ 2 :=
      div_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (sq_nonneg _)
    linarith
  exact (hv.inv hne).pow k

section Disc

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- Off the disc of radius `r` the amplitude jet norm of amplitudes vanishing there is zero. -/
theorem amplitudeJetNorm_eq_zero_of_gt (π : ι → ℝ) (m : ℕ) (ϖ : ℝ) {r : ℝ}
    {A B : ∀ x, Vec 2 → h x} (hvan : ∀ x θ, r ^ 2 < vecDot θ θ → A x θ = 0 ∧ B x θ = 0)
    {θ : Vec 2} (hθ : r ^ 2 < vecDot θ θ) : amplitudeJetNorm π m ϖ A B θ = 0 := by
  have hopen : IsOpen {θ : Vec 2 | r ^ 2 < vecDot θ θ} :=
    isOpen_lt continuous_const (by unfold vecDot; fun_prop)
  have hev : ∀ x, (A x =ᶠ[𝓝 θ] fun _ => 0) ∧ (B x =ᶠ[𝓝 θ] fun _ => 0) := fun x =>
    ⟨eventually_of_mem (hopen.mem_nhds hθ) fun y hy => (hvan x y hy).1,
      eventually_of_mem (hopen.mem_nhds hθ) fun y hy => (hvan x y hy).2⟩
  have hz : ∀ x (a b : ℕ), thetaPartial a b (A x) θ = 0 ∧ thetaPartial a b (B x) θ = 0 := by
    intro x a b
    unfold thetaPartial
    rw [((hev x).1.iteratedFDeriv ℝ (a + b)).eq_of_nhds,
      ((hev x).2.iteratedFDeriv ℝ (a + b)).eq_of_nhds]
    simp
  unfold amplitudeJetNorm
  refine Finset.sum_eq_zero fun β _ => ?_
  simp [hz, ENNReal.zero_rpow_of_pos]

/-- **The jet integral of amplitudes in a disc by a cube integral.** -/
theorem ampJetIntegral_le_of_disc (π : ι → ℝ) {m : ℕ} {ϖ r : ℝ} (hr : 0 ≤ r)
    (hrπ : r ≤ Real.pi) {A B : ∀ x, Vec 2 → h x}
    (hvan : ∀ x θ, r ^ 2 < vecDot θ θ → A x θ = 0 ∧ B x θ = 0) (Φ : Vec 2 → ℝ≥0∞) {K : ℝ}
    (hK : ∀ θ, vecDot θ θ ≤ r ^ 2 → amplitudeJetNorm π m ϖ A B θ ≤ ENNReal.ofReal K * Φ θ) :
    ampJetIntegral π m 0 ϖ A B ≤ ENNReal.ofReal K ^ 2 * ∫⁻ θ in freqCube, Φ θ ^ 2 := by
  unfold ampJetIntegral
  simp only [pow_zero, ENNReal.ofReal_one, one_mul]
  have hsupp : Function.support (fun θ => amplitudeJetNorm π m ϖ A B θ ^ 2) ⊆ freqCube := by
    intro θ hθ
    by_contra hθc
    apply hθ
    have hgt : r ^ 2 < vecDot θ θ := by
      by_contra hle
      exact hθc (mem_freqCube_of_vecDot_le hr hrπ (not_lt.1 hle))
    simp [amplitudeJetNorm_eq_zero_of_gt π m ϖ hvan hgt]
  rw [← setLIntegral_eq_of_support_subset hsupp, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun θ => ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  by_cases hθ : vecDot θ θ ≤ r ^ 2
  · exact hK θ hθ
  · rw [amplitudeJetNorm_eq_zero_of_gt π m ϖ hvan (lt_of_not_ge hθ)]
    positivity

end Disc

/-- The constant of the amplitude step (`amplitudeJetNorm_besselInv_le`). -/
def oldAmpConst (p k : ℕ) (Cg C₁ : ℝ) : ℝ :=
  ((p + 1 : ℕ) : ℝ) * 2 ^ p * (2 * ((p + 1 : ℕ) : ℝ) *
    (2 ^ p * ((16 / 3) ^ k * 4 ^ k * (8 * p + 1) ^ p) * Cg)) * C₁

theorem oldAmpConst_nonneg (p k : ℕ) {Cg C₁ : ℝ} (hCg : 0 ≤ Cg) (hC₁ : 0 ≤ C₁) :
    0 ≤ oldAmpConst p k Cg C₁ := by
  unfold oldAmpConst
  positivity

/-- The constant of the core bound. -/
def oldScalarConst (p k : ℕ) (Cg C₁ BT : ℝ) : ℝ :=
  besselDualConst k * (gaussJetConst p 0 * (oldAmpConst p k Cg C₁ * Real.sqrt BT))

theorem oldScalarConst_nonneg (p k : ℕ) {Cg C₁ : ℝ} (hCg : 0 ≤ Cg) (hC₁ : 0 ≤ C₁) (BT : ℝ) :
    0 ≤ oldScalarConst p k Cg C₁ BT :=
  mul_nonneg (besselDualConst_nonneg k) (mul_nonneg (gaussJetConst_pos p 0).le
    (mul_nonneg (oldAmpConst_nonneg p k hCg hC₁) (Real.sqrt_nonneg _)))

section Core

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]

/-- **The old scalar bound from a factorized amplitude.** -/
theorem negJetNorm_le_of_factor (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {p P k n : ℕ}
    (hk : p + P ≤ k + k) {ϖ η r : ℝ} (hϖ : 0 < ϖ) (hη : 0 < η) (hϖη : ϖ ≤ Real.sqrt η)
    (hr : 0 ≤ r) (hrπ : r ≤ Real.pi) {U : Set (Vec 2)} (hU : IsOpen U)
    (hrU : ∀ θ, vecDot θ θ ≤ r ^ 2 → θ ∈ U)
    (g A B : ∀ x, Vec 2 → h x) (hg : ∀ x, g x = ampFun r (A x) (B x))
    (hA : ∀ x, IsBandAmp r p (A x)) (hB : ∀ x, IsBandAmp r p (B x))
    {Eg : Vec 2 → ℂ} (hEg : ContDiffOn ℝ p Eg U) {Ac As : ∀ x, Vec 2 → h x}
    (hAc : ∀ x, ContDiff ℝ p (Ac x)) (hAs : ∀ x, ContDiff ℝ p (As x))
    (hrot : ∀ θ ∈ U, ∀ x, A x θ = (Eg θ).re • Ac x θ + (Eg θ).im • As x θ ∧
      B x θ = (Eg θ).re • As x θ - (Eg θ).im • Ac x θ)
    {Cg C₁ : ℝ} (hCg : 0 ≤ Cg) (hC₁ : 0 ≤ C₁)
    (hgj : ∀ θ, vecDot θ θ ≤ r ^ 2 → ∀ j ≤ p, ϖ ^ j * ‖iteratedFDeriv ℝ j Eg θ‖ ≤
      Cg * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ p)
    {χlo : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {Bχ : ℝ}
    (hBχ : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ Bχ)
    (F : ∀ x, Vec 2 → h x) (hF : ∀ x, AEStronglyMeasurable (F x) volume) {R : ℝ}
    (hR : ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → F x z = 0)
    (hX1 : ∀ θ, vecDot θ θ ≤ r ^ 2 → ampDerivNorm π p ϖ Ac As θ ≤
      ENNReal.ofReal (C₁ * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P) *
        ∑ α ∈ momentIndices n,
          ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
            blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ) :
    negJetNorm π p (k + k) ϖ ϖ⁻¹ g ≤
      ENNReal.ofReal (oldScalarConst p k Cg C₁ (blochMomentTotal n Bχ)) *
        momentNorm π n ϖ F := by
  have hinvc := besselInv_contDiff ϖ k
  have hA'b : ∀ x, IsBandAmp r p (fun θ => besselInv ϖ k θ • A x θ) := fun x =>
    ⟨(hinvc.of_le (by exact_mod_cast le_top)).smul (hA x).1, fun θ hθ => by
      simp only [(hA x).2 θ hθ, smul_zero]⟩
  have hB'b : ∀ x, IsBandAmp r p (fun θ => besselInv ϖ k θ • B x θ) := fun x =>
    ⟨(hinvc.of_le (by exact_mod_cast le_top)).smul (hB x).1, fun θ hθ => by
      simp only [(hB x).2 θ hθ, smul_zero]⟩
  have hgeq : g = fun x => ampFun r (fun θ => besselWeight ϖ k θ • (besselInv ϖ k θ • A x θ))
      (fun θ => besselWeight ϖ k θ • (besselInv ϖ k θ • B x θ)) := by
    funext x
    rw [hg x]
    congr 1 <;> funext θ <;> rw [smul_smul, besselWeight_mul_besselInv, one_smul]
  rw [hgeq]
  refine (negJetNorm_besselWeight_le π hπ hr p k hϖ hA'b hB'b).trans ?_
  set M := momentNorm π n ϖ F with hM
  set BT := blochMomentTotal n Bχ with hBTdef
  have hBT : 0 ≤ BT := blochMomentTotal_nonneg n Bχ
  have hpt : ∀ θ, vecDot θ θ ≤ r ^ 2 →
      amplitudeJetNorm π p ϖ (fun x θ => besselInv ϖ k θ • A x θ)
        (fun x θ => besselInv ϖ k θ • B x θ) θ ≤
      ENNReal.ofReal (oldAmpConst p k Cg C₁) * ∑ α ∈ momentIndices n,
          ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
            blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ :=
    fun θ hθ => amplitudeJetNorm_besselInv_le π hπ hk hϖ hU hEg hAc hAs hrot (hrU θ hθ) hC₁
      (hgj θ hθ) (hX1 θ hθ)
  have hvan' : ∀ x θ, r ^ 2 < vecDot θ θ →
      besselInv ϖ k θ • A x θ = 0 ∧ besselInv ϖ k θ • B x θ = 0 :=
    fun x θ hθ => ⟨(hA'b x).2 θ hθ, (hB'b x).2 θ hθ⟩
  have hint := ampJetIntegral_le_of_disc π hr hrπ hvan' _ hpt
  have hmom := lintegral_bloch_sum_sq_le_of_ae hχ hBχ hη hϖ hϖη π F hF hR
  have hJ : ampJetIntegral π p 0 ϖ (fun x θ => besselInv ϖ k θ • A x θ)
      (fun x θ => besselInv ϖ k θ • B x θ) ≤
      (ENNReal.ofReal (oldAmpConst p k Cg C₁) * (ENNReal.ofReal (Real.sqrt BT) * M)) ^ 2 := by
    refine hint.trans ?_
    rw [mul_pow, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hBT]
    exact mul_le_mul_right hmom _
  have hroot := ENNReal.rpow_le_rpow hJ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [sq_rpow_half] at hroot
  calc ENNReal.ofReal (besselDualConst k) * (ENNReal.ofReal (gaussJetConst p 0) *
        ampJetIntegral π p 0 ϖ (fun x θ => besselInv ϖ k θ • A x θ)
          (fun x θ => besselInv ϖ k θ • B x θ) ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (besselDualConst k) * (ENNReal.ofReal (gaussJetConst p 0) *
          (ENNReal.ofReal (oldAmpConst p k Cg C₁) * (ENNReal.ofReal (Real.sqrt BT) * M))) := by
        gcongr
    _ = ENNReal.ofReal (oldScalarConst p k Cg C₁ BT) * M := by
        unfold oldScalarConst
        rw [ENNReal.ofReal_mul (besselDualConst_nonneg k),
          ENNReal.ofReal_mul (gaussJetConst_pos p 0).le,
          ENNReal.ofReal_mul (oldAmpConst_nonneg p k hCg hC₁)]
        ring

end Core

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! **The old scalar bound at the seam data**. On the seam, the cutoff is `χ₋(θ/√η)` with
`χ₋ = 0` for `|ξ| ≥ 2ξ_lo`, so the amplitudes live in the disc of radius `r = 2ξ_lo√η ≤ π`,
which lies in the low disc `|ξ| < ξ₀` where X1 factorizes them and X2 bounds the gauge. With
X1's cutoff split `χ₋ = 1^{n+1} χ₋` (`χ_r = 1`, so the Bloch jets are uncut), X1's conjuncts at
the old output `e` and X2's jets give `negJetNorm_le_of_factor` its premises
(`oldScalar_chain_le`). The moment norm of a datum `F =ᵐ planeValue f` is at most the number of
moment indices times the weighted `L²` norm of `f` at weight `n` (`momentNorm_le_planeJet`).

Degenerate cases:
- `χ₋ = 0`: the output is `0`.
- `η = 1`, `S = 1`: `ϖ = 1` and `r = 2ξ_lo`.
- `n = 0`: one moment index; the weighted norm is the `L²` norm. -/

section
/-- The seam cutoff as a piece cutoff with `ψ = 1`. -/
theorem pieceCutoff_one (χ : Vec 2 → ℝ) (η : ℝ) :
    pieceCutoff χ (fun _ => 1) η = fun θ => χ ((Real.sqrt η)⁻¹ • θ) := by
  funext θ
  simp only [pieceCutoff, mul_one]

/-- A smooth function vanishing off a disc has bounded derivatives of every order. -/
theorem iteratedFDeriv_bounded_of_vanish {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {ρ : ℝ}
    (hsupp : ∀ ξ, ρ ≤ Real.sqrt (vecDot ξ ξ) → χ ξ = 0) (k : ℕ) :
    ∃ B : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ B := by
  have hc : HasCompactSupport χ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec 2) |ρ|) fun ξ hξ => hsupp ξ ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hξ
    exact (le_abs_self ρ).trans ((hξ.le).trans (norm_le_sqrt_vecDot ξ))
  obtain ⟨B, -, hB⟩ := exists_iteratedFDeriv_bound hχ hc k
  exact ⟨B, hB k le_rfl⟩

/-- The constant `1` has derivatives at most `1`. -/
theorem norm_iteratedFDeriv_one_le (l : ℕ) (θ : Vec 2) :
    ‖iteratedFDeriv ℝ l (fun _ : Vec 2 => (1 : ℝ)) θ‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    simp
  · rw [iteratedFDeriv_const_of_ne hl.ne' (1 : ℝ)]
    simp

/-- The fibre frequency of a plane frequency in the disc of radius `ρ√η`. -/
theorem fibreNorm_le_of_vecDot_le {η ρ : ℝ} (hη : 0 < η) (hρ : 0 ≤ ρ) {θ : Vec 2}
    (hθ : vecDot θ θ ≤ (ρ * Real.sqrt η) ^ 2) : fibreNorm (planeFibreFrequency η θ) ≤ ρ := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  rw [fibreNorm_planeFibreFrequency_eq_div hη, div_le_iff₀ hs]
  calc Real.sqrt (vecDot θ θ) ≤ Real.sqrt ((ρ * Real.sqrt η) ^ 2) := Real.sqrt_le_sqrt hθ
    _ = ρ * Real.sqrt η := Real.sqrt_sq (by positivity)

theorem vecDot_smul_self (c : ℝ) (θ : Vec 2) :
    vecDot (c • θ) (c • θ) = c ^ 2 * vecDot θ θ := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The seam cutoff vanishes off the disc of radius `2ξ_lo√η`. -/
theorem seamCutoff_vanish {η ρ : ℝ} (hη : 0 < η) (hρ : 0 ≤ ρ) {χ : Vec 2 → ℝ}
    (hsupp : ∀ ξ, ρ ≤ Real.sqrt (vecDot ξ ξ) → χ ξ = 0) {θ : Vec 2}
    (hθ : (ρ * Real.sqrt η) ^ 2 < vecDot θ θ) : pieceCutoff χ (fun _ => 1) η θ = 0 := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  rw [pieceCutoff_one]
  refine hsupp _ ?_
  rw [vecDot_smul_self, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hs.le),
    ← div_eq_inv_mul, le_div_iff₀ hs]
  have h1 : ρ * Real.sqrt η = Real.sqrt ((ρ * Real.sqrt η) ^ 2) :=
    (Real.sqrt_sq (by positivity)).symm
  rw [h1]
  exact Real.sqrt_le_sqrt hθ.le

/-- The low disc of the fibre frequency is open. -/
theorem isOpen_lowDisc {η : ℝ} (hη : 0 < η) (ξ0 : ℝ) :
    IsOpen {θ : Vec 2 | fibreNorm (planeFibreFrequency η θ) < ξ0} := by
  have he : {θ : Vec 2 | fibreNorm (planeFibreFrequency η θ) < ξ0} =
      {θ : Vec 2 | Real.sqrt (vecDot θ θ) / Real.sqrt η < ξ0} := by
    ext θ
    simp only [Set.mem_ofPred_eq, fibreNorm_planeFibreFrequency_eq_div hη]
  rw [he]
  exact isOpen_lt ((Real.continuous_sqrt.comp (by unfold vecDot; fun_prop)).div_const _)
    continuous_const

section Chain

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]

/-- **The old scalar bound at the seam data, from X1's and X2's conclusions.** -/
theorem oldScalar_chain_le {ξlo ξ0 : ℝ} (hξ : 0 < ξlo) (hξ0 : 2 * ξlo < ξ0)
    (hξπ : 2 * ξlo ≤ Real.pi) (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {p P k n : ℕ}
    (hk : p + P ≤ k + k) {η S ϖ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hS : 1 ≤ S)
    (hϖ : ϖ = Real.sqrt (η / S)) {χm : Vec 2 → ℝ}
    (hχsupp : ∀ ξ, 2 * ξlo ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0) (e : ∀ x, Vec 2 → h x)
    (hret : ∀ r : ℝ, 0 < r →
      (∀ θ : Vec 2, r ^ 2 < vecDot θ θ → pieceCutoff χm (fun _ => 1) η θ = 0) → ∀ x,
      IsRetainedAmplitude (fourierCutoff (pieceCutoff χm (fun _ => 1) η) (e x)) r
        (cutoffCosAmplitude (pieceCutoff χm (fun _ => 1) η) (e x))
        (cutoffSinAmplitude (pieceCutoff χm (fun _ => 1) η) (e x)))
    (hcd : ∀ x, ContDiff ℝ p (cutoffCosAmplitude (pieceCutoff χm (fun _ => 1) η) (e x)) ∧
      ContDiff ℝ p (cutoffSinAmplitude (pieceCutoff χm (fun _ => 1) η) (e x)))
    {Eg : Vec 2 → ℂ} {Ac As : ∀ x, Vec 2 → h x}
    (hAcs : ∀ x, ContDiff ℝ p (Ac x) ∧ ContDiff ℝ p (As x))
    (hrot : ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) < ξ0 → ∀ x,
      cutoffCosAmplitude (pieceCutoff χm (fun _ => 1) η) (e x) θ =
          (Eg θ).re • Ac x θ + (Eg θ).im • As x θ ∧
        cutoffSinAmplitude (pieceCutoff χm (fun _ => 1) η) (e x) θ =
          (Eg θ).re • As x θ - (Eg θ).im • Ac x θ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (F : ∀ x, Vec 2 → h x)
    (hbound : ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) < ξ0 →
      ampDerivNorm π p ϖ Ac As θ ≤
        ENNReal.ofReal (C₁ * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P) *
          ∑ α ∈ momentIndices n,
            ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
              blochFibreDerivNorm π (fun θ' => (fun _ => (1 : ℝ)) ((Real.sqrt η)⁻¹ • θ')) α F θ)
    (hEg : ContDiffOn ℝ p Eg {θ | fibreNorm (planeFibreFrequency η θ) < ξ0}) {Cg : ℝ}
    (hCg : 0 ≤ Cg)
    (hgj : ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ 2 * ξlo → ∀ j ≤ p,
      ϖ ^ j * ‖iteratedFDeriv ℝ j Eg θ‖ ≤ Cg * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ j)
    (hF : ∀ x, AEStronglyMeasurable (F x) volume) {R : ℝ}
    (hR : ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → F x z = 0) :
    negJetNorm π p (k + k) ϖ ϖ⁻¹
        (fun x => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (e x)) ≤
      ENNReal.ofReal (oldScalarConst p k Cg C₁ (blochMomentTotal n 1)) * momentNorm π n ϖ F := by
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hsη1 : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη1
  have hρ : 0 ≤ 2 * ξlo := by linarith
  set r := 2 * ξlo * Real.sqrt η with hrdef
  have hr : 0 < r := mul_pos (by linarith) hsη
  have hrπ : r ≤ Real.pi := by
    calc r ≤ 2 * ξlo * 1 := mul_le_mul_of_nonneg_left hsη1 hρ
      _ ≤ Real.pi := by linarith
  have hϖ0 : 0 < ϖ := by rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hϖη : ϖ ≤ Real.sqrt η := by
    rw [hϖ]
    exact Real.sqrt_le_sqrt (div_le_self hη.le hS)
  have hRA := hret r hr (fun θ hθ => seamCutoff_vanish hη hρ hχsupp hθ)
  have hrU : ∀ θ, vecDot θ θ ≤ r ^ 2 → fibreNorm (planeFibreFrequency η θ) ≤ 2 * ξlo :=
    fun θ hθ => fibreNorm_le_of_vecDot_le hη hρ hθ
  have hg : ∀ x, fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ)) (e x) =
      ampFun r (cutoffCosAmplitude (pieceCutoff χm (fun _ => 1) η) (e x))
        (cutoffSinAmplitude (pieceCutoff χm (fun _ => 1) η) (e x)) := by
    intro x
    funext z
    rw [← pieceCutoff_one]
    exact (hRA x).2.2.2 z
  refine negJetNorm_le_of_factor π hπ hk hϖ0 hη hϖη hr.le hrπ (isOpen_lowDisc hη ξ0)
    (fun θ hθ => lt_of_le_of_lt (hrU θ hθ) hξ0) _ _ _ hg
    (fun x => ⟨(hcd x).1, fun θ hθ => ((hRA x).1 θ hθ).1⟩)
    (fun x => ⟨(hcd x).2, fun θ hθ => ((hRA x).1 θ hθ).2⟩) hEg (fun x => (hAcs x).1)
    (fun x => (hAcs x).2) hrot hCg hC₁ ?_ contDiff_const (fun l _ θ => norm_iteratedFDeriv_one_le l θ)
    F hF hR (fun θ hθ => hbound θ (lt_of_le_of_lt (hrU θ hθ) hξ0))
  intro θ hθ j hj
  refine (hgj θ (hrU θ hθ) j hj).trans (mul_le_mul_of_nonneg_left ?_ hCg)
  have hx : 1 ≤ 1 + Real.sqrt (vecDot θ θ) / ϖ :=
    le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) hϖ0.le)
  exact pow_le_pow_right₀ hx hj

end Chain

section Moment

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The moment norm of a plane datum by its weighted `L²` norm.** -/
theorem momentNorm_le_planeJet {κ : ι → ℕ} (π : ι → ℝ) (n : ℕ) (ϖ : ℝ)
    (f : ∀ x, PlaneHk Set.univ (κ x) (h x)) {F : ∀ x, Vec 2 → h x}
    (hF : ∀ x, F x =ᵐ[volume] planeValue (f x)) :
    momentNorm π n ϖ F ≤ ENNReal.ofReal ((momentIndices n).card : ℝ) *
      weightedJetNorm π (n : ℝ) 0 ϖ 1 (fun x a wd z => planeJetOrder (f x) a wd z) := by
  have hword : ∀ (x : ι) (z : Vec 2),
      Real.sqrt (∑ w : DerivativeWord2 0, ‖planeJetOrder (f x) 0 w z‖ ^ 2) =
        ‖planeValue (f x) z‖ := by
    intro x z
    have hdef : ∀ w : DerivativeWord2 0, planeJetOrder (f x) 0 w = planeValue (f x) := fun w => by
      rw [Subsingleton.elim w (fun i => i.elim0)]
      rfl
    rw [Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _), hdef]
  rw [momentNorm_congr_ae hF]
  refine (momentNorm_le_weighted π n ϖ _
    fun x => (planeValue_memLp (f x)).aestronglyMeasurable).trans (le_of_eq ?_)
  rw [Seam.weightedJetNorm_eq_familyNorm, Finset.sum_range_one]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one, one_mul,
    hword]

end Moment
end

/-! **The old word as a word piece, and the constants of the old scalar bound.** The premises of
`SeamOldScalarStatement` make the old letters on `[a, b]` a word piece (`IsWordPiece`) on the
regions cut to the package window (`isWordPiece_of_seam`; quiet is given on `reg.quiet ∩ window`).
The switching factor of the amplitude factor statement `1 + P_e^Q(1+S)^Q((1 + B_p)e^{-c D_q^{reg}} + e^{-c D_q})` is at most
`1 + 2C₀` under the two scale premises of the old scalar bound (`oldSwitch_le`), and the constant of the core bound is
linear in the constant of the amplitude factor statement (`oldScalarConst_mul_right`). The package gives the constants it uses,
`2ξ_lo < ξ₀`, `0 < ξ_lo` and `2ξ_lo ≤ π` (`seamConsts_of_pkg`, from `consts_pos` and `C_w ≥ 0`).

With no old letters the letter fields are vacuous. For `C₀ < 0` the scale premises fail, and
`max C₀ 0 = 0` keeps the constant nonnegative. For `Θ = 1` the constant is unchanged. -/

section
/-- The constant of the core bound is linear in the constant of the amplitude factor statement. -/
theorem oldScalarConst_mul_right (p k : ℕ) (Cg C₁ Θ BT : ℝ) :
    oldScalarConst p k Cg (C₁ * Θ) BT = oldScalarConst p k Cg C₁ BT * Θ := by
  unfold oldScalarConst oldAmpConst
  ring

/-- **The switching factor under the scale premises of the old scalar bound.** -/
theorem oldSwitch_le {C Θ x C0 c Dq P S B J : ℝ} (hC : 0 ≤ C) (hΘ : 0 ≤ Θ) (hx : 0 ≤ x)
    (h1 : P * S * J * Real.exp (-c * B) ≤ C0) (h2 : P * S * Real.exp (-c * Dq) ≤ C0) {Q : ℕ} :
    C * Θ * (1 + x) ^ Q * (1 + P * S * (J * Real.exp (-c * B) + Real.exp (-c * Dq))) ≤
      C * (1 + 2 * max C0 0) * Θ * (1 + x) ^ Q := by
  have hle : 1 + P * S * (J * Real.exp (-c * B) + Real.exp (-c * Dq)) ≤ 1 + 2 * max C0 0 := by
    have e : P * S * (J * Real.exp (-c * B) + Real.exp (-c * Dq)) =
        P * S * J * Real.exp (-c * B) + P * S * Real.exp (-c * Dq) := by ring
    rw [e]
    have := le_max_left C0 0
    linarith
  calc C * Θ * (1 + x) ^ Q * (1 + P * S * (J * Real.exp (-c * B) + Real.exp (-c * Dq)))
      ≤ C * Θ * (1 + x) ^ Q * (1 + 2 * max C0 0) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = C * (1 + 2 * max C0 0) * Θ * (1 + x) ^ Q := by ring

/-- The package constants used by the old scalar bound: `2ξ_lo < ξ₀`, `0 < ξ_lo`, `2ξ_lo ≤ π`. -/
theorem seamConsts_of_pkg {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ} {reg : BlockRegions}
    (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (hCw : 0 ≤ K.Cw) :
    2 * K.ξlo < K.ξ0 ∧ 0 < K.ξlo ∧ 2 * K.ξlo ≤ Real.pi := by
  obtain ⟨-, hlo, h2, hCg, -, -, -, -, -, hπ⟩ := pkg.consts_pos
  refine ⟨h2, hlo, ?_⟩
  have hCC : 0 ≤ K.Cw * K.Cg := mul_nonneg hCw hCg.le
  have hsq : (2 * K.ξlo) ^ 2 ≤ Real.pi ^ 2 := by nlinarith [sq_nonneg (2 * K.ξlo), Real.pi_pos]
  have h := sq_le_sq.1 hsq
  rwa [abs_of_pos (by linarith), abs_of_pos Real.pi_pos] at h

section Piece

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The old letters are a word piece** on the regions cut to the package window. -/
theorem isWordPiece_of_seam {K : ScalarConstants} {g₁ : ℝ} {D Nw H J : ℕ} (hD : 2 ≤ D)
    {π : ι → ℝ} (hπ : ∀ x, 0 < π x) {letters : Fin Nw → CycleLetter ι h D}
    {η S ηg ϖ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hS : 1 ≤ S) (hηg : 0 < ηg) (hηg1 : ηg ≤ 1)
    (hϖ : ϖ = Real.sqrt (η / S)) {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {g : ℝ} (hGm : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hv0 : ∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj j)
    (hg0 : 0 ≤ g) (hg : g ≤ K.g0) (hg₁ : g ≤ g₁)
    (hGn : IsMetricNearIdentity (fun t _ => G t) g) {reg : BlockRegions} {t₀ Sw a b : ℝ}
    (hlet : ∀ i, IsCycleLetter π (letters i) (Set.Icc a b ×ˢ Set.univ) J H)
    (htrans : ∀ i, IsTransverseOnPulses (letters i).edge
      (fun p : Fin reg.P => Set.Icc (reg.lo p) (reg.hi p)) reg.orient)
    (hquiet : ∀ i, IsQuietOn (letters i).edge v (reg.quiet ∩ Set.Icc t₀ (t₀ + Sw)))
    (hmeas : ∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z) :
    IsWordPiece K g₁ H J π letters η S ηg ϖ G v g (reg.inWindow t₀ Sw) a b where
  hD := hD
  hπ := hπ
  hη := hη
  hη1 := hη1
  hS := hS
  hηg := hηg
  hηg1 := hηg1
  hϖ := hϖ
  hGm := hGm
  hv := hv
  hv0 := hv0
  hvs := hvs
  hvw := hvw
  hvj := hvj
  hg0 := hg0
  hg := hg
  hg₁ := hg₁
  hGn := hGn
  hlet := hlet
  htrans := fun i => (htrans i).inWindow t₀ Sw
  hquiet := hquiet
  hmeas := hmeas

end Piece
end

/-! **The old scalar bound of the seam from the retained amplitude factor** (`SeamOldScalarStatement` from
`RetainedAmplitudeFactorStatement`).

The old word ends on a piece `[a_O, b_O]` of the old window, which is a word piece of the window
restricted to `[t_O, t_O + S_O]` (`isWordPiece_of_seam`, `BlockRegions.inWindow`). The amplitude factor statement is applied
there with:
- the cutoff `χ = χ_m`, `ψ = 1`, `χ_r = 1`, `χ₃ = χ_m` and the radius `ρ = 2ξ_lo`;
- the jet order `p + P` of the amplitude;
- the plane datum `f`, whose value vanishes a.e. outside a ball (the seam's datum premise).

The gauge jets of the window (`gaugeJetsPiece`) and the rotation and amplitude bound give the
negative-norm bound of the cut-off output (`oldScalar_chain_le`), and the moments of the datum
are its Bloch jets (`momentNorm_le_planeJet`). The orders are `m = 2(p + P)`, `q = ∑ K_s^O`, and
`Q` is that of the amplitude factor statement. The switching error `P_e^Q(1+S)^Q(…)` sits under the two stipulated scales `≤ C₀`
(`oldSwitch_le`).

For constants with `2ξ_lo ≥ ξ₀` (or `ξ_lo ≤ 0`) no `CoreScalarPackage` exists (`seamConsts_of_pkg`),
and the bound holds vacuously with `C = 0`. For `f = 0` the right side is `0`, so the cut-off old
output has zero negative norm. For `p = 0` and `P = 0` one has `m = 0`, an `L²` bound of the low
part. For an empty old word (`N_m = 0`), `q = 0` and `Θ_w = 1` (empty product). -/

section
universe u v

/-- **The old scalar bound from the retained amplitude factor.** -/
theorem seamOldScalar_of (hX1 : RetainedAmplitudeFactorStatement.{u, v}) :
    SeamOldScalarStatement.{u, v} := by
  intro K
  obtain ⟨g₁, hg₁, hX1K⟩ := hX1 K
  refine ⟨g₁, hg₁, fun σ hσK p hp => ?_⟩
  subst hσK
  obtain ⟨P, Q, hX1P⟩ := hX1K σ.Nm σ.D σ.H p σ.dO σ.KsO σ.posO
  refine ⟨(p + P) + (p + P), ∑ i, σ.KsO i, Q, fun CH C0 χm hCH hχ _ hχsupp _ => ?_⟩
  by_cases hK : 2 * σ.K.ξlo < σ.K.ξ0 ∧ 0 < σ.K.ξlo ∧ 2 * σ.K.ξlo ≤ Real.pi
  swap
  · refine ⟨0, 1, le_rfl, one_pos, ?_⟩
    intro ι _ h _ _ _ _ _ _ π _ lettersO _ η S ηg ϖ δ _ _ _ _ _ _ _ tO SO aO bO GO vO gO _ _ _ _
      hvw _ _ _ _ _ regO pkg
    exact absurd (seamConsts_of_pkg pkg ((mul_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)).trans (hvw 0 0))) hK
  obtain ⟨hξ0, hξ, hξπ⟩ := hK
  set n := wordReserveN p σ.KsO with hn
  obtain ⟨C1, c, hC1, hc, hX1C⟩ := hX1P CH (2 * σ.K.ξlo) χm (fun _ => 1) hξ0 le_rfl hχ hχsupp
    contDiff_const (fun k => ⟨1, norm_iteratedFDeriv_one_le k⟩) (fun _ => 1) χm contDiff_const
    (fun k => ⟨1, norm_iteratedFDeriv_one_le k⟩) hχ (iteratedFDeriv_bounded_of_vanish hχ hχsupp)
    (fun ξ => by simp)
  obtain ⟨Cg, hCg, hX2C⟩ := gaugeJetsPiece σ.K p CH (2 * σ.K.ξlo) hξ0
  set C' := C1 * (1 + 2 * max C0 0) with hC'
  have hC'0 : 0 ≤ C' := mul_nonneg hC1.le (by have := le_max_right C0 0; linarith)
  set A0 := oldScalarConst p (p + P) Cg C' (blochMomentTotal n 1) with hA0
  have hA00 : 0 ≤ A0 := oldScalarConst_nonneg p (p + P) hCg.le hC'0 _
  refine ⟨A0 * ((momentIndices n).card : ℝ), c, mul_nonneg hA00 (Nat.cast_nonneg _), hc, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ lettersO hshape η S ηg ϖ δ hη hη1 hS hηg hηg1 hϖ hδ tO SO aO bO GO
    vO gO hGm hv hv0 hvs hvw hvj hg0 hg hg1 hGn regO pkg hab hdur hC0a Dq hDq hDqq hC0b hlet
    htrans hquiet hmeas X₀O κO hslots f uO wO hfsupp hchain
  subst hδ
  obtain ⟨R, hR⟩ := hfsupp
  have hΘ : 0 ≤ wordTheta ηg lettersO :=
    Finset.prod_nonneg fun i _ => mul_nonneg (hlet i).theta_nonneg (by split <;> linarith)
  have hpiece := isWordPiece_of_seam (g₁ := g₁) σ.hD hπ hη hη1 hS hηg hηg1 hϖ hGm hv hv0 hvs
    hvw hvj hg0 hg hg1 hGn hlet htrans hquiet hmeas
  obtain ⟨-, hret, hcd, Ac, As, hAcs, hrot, hbd⟩ := hX1C σ.Jstar π lettersO hshape η S ηg tO SO
    ϖ aO bO Dq GO vO gO (regO.inWindow tO SO) pkg.inWindow hpiece hab.1 hab.2.1 hab.2.2 hdur hDq
    (fun t ht => hDqq ⟨ht.1.le, ht.2⟩) (σ.oldReserve_le hp) X₀O κO hslots f uO wO ⟨R, hR⟩ hchain
  obtain ⟨hEg, hgj⟩ := hX2C η S tO SO ϖ aO bO GO vO (regO.inWindow tO SO) pkg.inWindow hη hη1 hS
    hϖ hGm hv hvw hab.1 hab.2.1 hab.2.2 hdur
  have hϖ0 : 0 < ϖ := by rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hbound : ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) < σ.K.ξ0 →
      ampDerivNorm π p ϖ Ac As θ ≤
        ENNReal.ofReal (C' * wordTheta ηg lettersO * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P) *
          ∑ α ∈ momentIndices n,
            ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
              blochFibreDerivNorm π (fun θ' => (fun _ => (1 : ℝ)) ((Real.sqrt η)⁻¹ • θ')) α
                (fun x => planeValue (f x)) θ := by
    intro θ hθ
    refine (hbd θ hθ).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    exact oldSwitch_le (C := C1) (Θ := wordTheta ηg lettersO)
      (x := Real.sqrt (vecDot θ θ) / ϖ) (Q := P) hC1.le hΘ
      (div_nonneg (Real.sqrt_nonneg _) hϖ0.le)
      (hC0a : peFactor η ^ Q * (1 + S) ^ Q * (1 + ((regO.inWindow tO SO).joins : ℝ)) *
        Real.exp (-c * (regO.inWindow tO SO).buffer) ≤ C0) hC0b
  have hmain := oldScalar_chain_le hξ hξ0 hξπ π hπ (k := p + P) (by omega) hη hη1 hS hϖ hχsupp
    (fun x => planeValue (uO (Fin.last σ.Nm) x bO)) hret hcd hAcs hrot
    (mul_nonneg hC'0 hΘ) (fun x => planeValue (f x)) hbound hEg hCg.le hgj
    (fun x => (planeValue_memLp (f x)).aestronglyMeasurable) hR
  have hmom := momentNorm_le_planeJet π n ϖ f (F := fun x => planeValue (f x))
    (fun x => Filter.EventuallyEq.rfl)
  refine hmain.trans ((mul_le_mul_right hmom _).trans (le_of_eq ?_))
  rw [oldScalarConst_mul_right, ← hA0, ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hA00 hΘ),
    show A0 * wordTheta ηg lettersO * ((momentIndices n).card : ℝ) =
      A0 * ((momentIndices n).card : ℝ) * wordTheta ηg lettersO by ring]
  rfl
end

end AVRegularity.CycleWords.Assembly
end
