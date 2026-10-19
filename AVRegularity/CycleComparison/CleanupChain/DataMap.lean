-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Infra.Torus.FourierCalculus
import Mathlib.Analysis.PSeries
public import AVRegularity.CycleComparison.Residual.TimeIntegration
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

section
@[expose] public noncomputable section
open AVenhance.Infra.Torus
open scoped Real
namespace AVRegularity.CleanupChain

/-! Integer frequencies on the two-torus: the `ℓ¹` length `|k|₁` and the squared length `|k|²`,
the summability of `(1 + |k|₁)⁻⁴` over `ℤ²`, and the real inequality behind the decay of the
inverse-Laplacian multiplier. -/

/-- The `ℓ¹` length `|k₀| + |k₁|` of an integer frequency. -/
def freqL1 (k : Fin 2 → ℤ) : ℝ := ∑ i : Fin 2, |(k i : ℝ)|

/-- The squared Euclidean length `k₀² + k₁²` of an integer frequency. -/
def freqSq (k : Fin 2 → ℤ) : ℝ := ∑ i : Fin 2, (k i : ℝ) ^ 2

theorem freqL1_nonneg (k : Fin 2 → ℤ) : 0 ≤ freqL1 k :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem freqL1_neg (k : Fin 2 → ℤ) : freqL1 (-k) = freqL1 k := by
  simp [freqL1]

theorem freqL1_eq (k : Fin 2 → ℤ) : freqL1 k = |(k 0 : ℝ)| + |(k 1 : ℝ)| := by
  simp [freqL1, Fin.sum_univ_two]

theorem freqSq_nonneg (k : Fin 2 → ℤ) : 0 ≤ freqSq k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem freqSq_eq_abs (k : Fin 2 → ℤ) :
    freqSq k = |(k 0 : ℝ)| ^ 2 + |(k 1 : ℝ)| ^ 2 := by
  simp [freqSq, Fin.sum_univ_two, sq_abs]

theorem one_le_freqSq {k : Fin 2 → ℤ} (hk : k ≠ 0) : 1 ≤ freqSq k :=
  FourierCalculus.intFrequencySq_ge_one (n := 1) hk

theorem one_le_freqL1 {k : Fin 2 → ℤ} (hk : k ≠ 0) : 1 ≤ freqL1 k := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
  have h2 : |(k i : ℝ)| ≤ freqL1 k :=
    Finset.single_le_sum (f := fun j : Fin 2 => |(k j : ℝ)|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  linarith

/-- `|kᵢ| ≤ |k|²` for an integer frequency. -/
theorem abs_le_freqSq (k : Fin 2 → ℤ) (i : Fin 2) : |(k i : ℝ)| ≤ freqSq k := by
  have h1 : |(k i : ℝ)| ≤ (k i : ℝ) ^ 2 := by
    rcases eq_or_ne (k i) 0 with h | h
    · rw [h]
      simp
    · have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs h
      rw [← sq_abs (k i : ℝ)]
      nlinarith
  have h2 : (k i : ℝ) ^ 2 ≤ freqSq k :=
    Finset.single_le_sum (f := fun j : Fin 2 => (k j : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  linarith

theorem summable_int_inv_sq : Summable (fun n : ℤ => ((1 + |(n : ℝ)|) ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded_eventually
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)) ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  have hn' : n ≠ 0 := hn
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn'
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    rw [← sq_abs (n : ℝ)]
    exact pow_pos (by linarith) 2
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ((1 + |(n : ℝ)|) ^ 2)⁻¹), one_div]
  refine inv_anti₀ hpos ?_
  rw [← sq_abs (n : ℝ)]
  exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2

theorem one_add_sq_mul_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 + a) ^ 2 * (1 + b) ^ 2 ≤ (1 + (a + b)) ^ 4 := by
  have h1 : (1 + a) * (1 + b) ≤ (1 + (a + b)) ^ 2 := by
    nlinarith [mul_nonneg ha hb]
  have h2 : 0 ≤ (1 + a) * (1 + b) := by positivity
  calc (1 + a) ^ 2 * (1 + b) ^ 2 = ((1 + a) * (1 + b)) ^ 2 := by ring
    _ ≤ ((1 + (a + b)) ^ 2) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = (1 + (a + b)) ^ 4 := by ring

/-- `∑_{k ∈ ℤ²} (1 + |k|₁)⁻⁴ < ∞`. -/
theorem summable_inv_one_add_freqL1_pow_four :
    Summable (fun k : Fin 2 → ℤ => ((1 + freqL1 k) ^ 4)⁻¹) := by
  have hnn : 0 ≤ fun n : ℤ => ((1 + |(n : ℝ)|) ^ 2)⁻¹ :=
    Pi.le_def.mpr fun n => by
      simp only [Pi.zero_apply]
      positivity
  have hprod := summable_int_inv_sq.mul_of_nonneg summable_int_inv_sq hnn hnn
  have hpi : Summable (fun k : Fin 2 → ℤ =>
      ((1 + |(k 0 : ℝ)|) ^ 2)⁻¹ * ((1 + |(k 1 : ℝ)|) ^ 2)⁻¹) :=
    (finTwoArrowEquiv ℤ).summable_iff.mpr hprod
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hpi
  rw [freqL1_eq, ← mul_inv]
  refine inv_anti₀ (by positivity) ?_
  exact one_add_sq_mul_le _ _ (abs_nonneg _) (abs_nonneg _)

/-- The decay inequality behind the inverse-Laplacian multiplier: with `L = a + b ≥ 1`,
`[(2π)^s (a^s + b^s) 4π² (a² + b²)]⁻² (1 + L)^{2s} ≤ 2^{2s+2} (1 + L)⁻⁴`. -/
theorem inv_sq_mul_le (s : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 1 ≤ a + b) :
    (((2 * π) ^ s * (a ^ s + b ^ s) * (4 * π ^ 2 * (a ^ 2 + b ^ 2)))⁻¹) ^ 2 *
      (1 + (a + b)) ^ (2 * s) ≤ 2 ^ (2 * s + 2) * ((1 + (a + b)) ^ 4)⁻¹ := by
  have hπ : (1 : ℝ) ≤ π := by linarith [Real.two_le_pi]
  have hL0 : 0 < a + b := by linarith
  have h1 : ((a + b) / 2) ^ s ≤ a ^ s + b ^ s := by
    rcases le_total a b with h | h
    · calc ((a + b) / 2) ^ s ≤ b ^ s := pow_le_pow_left₀ (by linarith) (by linarith) s
        _ ≤ a ^ s + b ^ s := le_add_of_nonneg_left (pow_nonneg ha s)
    · calc ((a + b) / 2) ^ s ≤ a ^ s := pow_le_pow_left₀ (by linarith) (by linarith) s
        _ ≤ a ^ s + b ^ s := le_add_of_nonneg_right (pow_nonneg hb s)
  have h2 : (a + b) ^ 2 / 2 ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h3 : (a + b) ^ s ≤ (2 * π) ^ s * (a ^ s + b ^ s) := by
    calc (a + b) ^ s ≤ (π * (a + b)) ^ s :=
          pow_le_pow_left₀ hL0.le (le_mul_of_one_le_left hL0.le hπ) s
      _ = (2 * π) ^ s * ((a + b) / 2) ^ s := by
          rw [← mul_pow]
          congr 1
          ring
      _ ≤ (2 * π) ^ s * (a ^ s + b ^ s) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 2 * (a + b) ^ 2 ≤ 4 * π ^ 2 * (a ^ 2 + b ^ 2) := by
    have hπ2 : (1 : ℝ) ≤ π ^ 2 := one_le_pow₀ hπ
    calc 2 * (a + b) ^ 2 = 1 * (2 * (a + b) ^ 2) := by ring
      _ ≤ π ^ 2 * (2 * (a + b) ^ 2) := mul_le_mul_of_nonneg_right hπ2 (by positivity)
      _ = 4 * π ^ 2 * ((a + b) ^ 2 / 2) := by ring
      _ ≤ 4 * π ^ 2 * (a ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hS : 0 ≤ (2 * π) ^ s * (a ^ s + b ^ s) :=
    mul_nonneg (by positivity) (add_nonneg (pow_nonneg ha s) (pow_nonneg hb s))
  have hD : 2 * (a + b) ^ (s + 2) ≤
      (2 * π) ^ s * (a ^ s + b ^ s) * (4 * π ^ 2 * (a ^ 2 + b ^ 2)) := by
    calc 2 * (a + b) ^ (s + 2) = (a + b) ^ s * (2 * (a + b) ^ 2) := by ring
      _ ≤ _ := mul_le_mul h3 h4 (by positivity) hS
  have hP : 0 < 2 * (a + b) ^ (s + 2) := mul_pos two_pos (pow_pos hL0 _)
  have hDpos : 0 < (2 * π) ^ s * (a ^ s + b ^ s) * (4 * π ^ 2 * (a ^ 2 + b ^ 2)) :=
    lt_of_lt_of_le hP hD
  generalize (2 * π) ^ s * (a ^ s + b ^ s) * (4 * π ^ 2 * (a ^ 2 + b ^ 2)) = D at hD hDpos ⊢
  generalize a + b = L at hL hL0 hD hP ⊢
  have e1 : (D⁻¹) ^ 2 * (1 + L) ^ (2 * s) = (1 + L) ^ (2 * s) / D ^ 2 := by
    rw [inv_pow, div_eq_inv_mul]
  have e2 : (2 : ℝ) ^ (2 * s + 2) * ((1 + L) ^ 4)⁻¹ = 2 ^ (2 * s + 2) / (1 + L) ^ 4 := by
    rw [div_eq_mul_inv]
  rw [e1, e2, div_le_div_iff₀ (pow_pos hDpos 2) (pow_pos (by linarith) 4)]
  calc (1 + L) ^ (2 * s) * (1 + L) ^ 4 = (1 + L) ^ (2 * s + 4) := by ring
    _ ≤ (2 * L) ^ (2 * s + 4) := pow_le_pow_left₀ (by linarith) (by linarith) _
    _ = 2 ^ (2 * s + 2) * (2 * L ^ (s + 2)) ^ 2 := by ring
    _ ≤ 2 ^ (2 * s + 2) * D ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP.le hD 2) (by positivity)

end AVRegularity.CleanupChain
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus
open scoped Real
namespace AVRegularity.CleanupChain

/-! The torus characters `torusCharacter k`: their derivative, the bound
`‖Dᶜ torusCharacter k‖ ≤ ‖charLin k‖ᶜ` on iterated derivatives, products, and orthonormality over
the unit cell (from Parseval for the constant function). -/

theorem vec_eq_sum_basisVec (v : Vec 2) : v = ∑ i, v i • basisVec i := by
  funext j
  simp [basisVec, Pi.single_apply]

/-- The phase `v ↦ -2πi k·v` of `torusCharacter k`. -/
def charLin (k : Fin 2 → ℤ) : Vec 2 →L[ℝ] ℂ :=
  ∑ i : Fin 2, (-2 * (π : ℂ) * Complex.I * (k i : ℂ)) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i))

theorem charLin_apply (k : Fin 2 → ℤ) (v : Vec 2) :
    charLin k v = ∑ i : Fin 2, (-2 * (π : ℂ) * Complex.I * (k i : ℂ)) * (v i : ℂ) := by
  simp only [charLin, FunLike.coe_sum, FunLike.coe_smul,
    Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, smul_eq_mul]

theorem norm_charLin_coeff (m : ℤ) :
    ‖(-2 * (π : ℂ) * Complex.I * (m : ℂ))‖ = 2 * π * |(m : ℝ)| := by
  rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_two,
    Complex.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, Complex.norm_intCast]
  ring

theorem norm_charLin_le (k : Fin 2 → ℤ) : ‖charLin k‖ ≤ 2 * π * freqL1 k := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by positivity) (freqL1_nonneg k)) fun v => ?_
  rw [charLin_apply]
  calc ‖∑ i : Fin 2, (-2 * (π : ℂ) * Complex.I * (k i : ℂ)) * (v i : ℂ)‖
      ≤ ∑ i : Fin 2, ‖(-2 * (π : ℂ) * Complex.I * (k i : ℂ)) * (v i : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 2, 2 * π * |(k i : ℝ)| * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_charLin_coeff, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (by positivity)
    _ = 2 * π * freqL1 k * ‖v‖ := by
        rw [freqL1_eq, Fin.sum_univ_two]
        ring

theorem fderiv_torusCharacter_apply (k : Fin 2 → ℤ) (x v : Vec 2) :
    fderiv ℝ (torusCharacter k) x v = torusCharacter k x * charLin k v := by
  have hc : ∀ i : Fin 2, fderiv ℝ (torusCharacter k) x (basisVec i) =
      (-2 * (π : ℂ) * Complex.I * (k i : ℂ)) * torusCharacter k x :=
    fun i => FourierCalculus.coordDeriv_torusCharacter i k x
  conv_lhs => rw [vec_eq_sum_basisVec v]
  rw [map_sum]
  simp only [map_smul, hc, charLin_apply, Fin.sum_univ_two, Complex.real_smul]
  ring

/-- `w ↦ w • charLin k`. -/
def charSmul (k : Fin 2 → ℤ) : ℂ →L[ℝ] (Vec 2 →L[ℝ] ℂ) :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (charLin k)

theorem charSmul_apply (k : Fin 2 → ℤ) (w : ℂ) : charSmul k w = w • charLin k := rfl

theorem fderiv_torusCharacter (k : Fin 2 → ℤ) :
    fderiv ℝ (torusCharacter k) = fun y => charSmul k (torusCharacter k y) := by
  funext y
  refine ContinuousLinearMap.ext fun v => ?_
  rw [fderiv_torusCharacter_apply, charSmul_apply, _root_.smul_apply, smul_eq_mul]

theorem norm_charSmul_le (k : Fin 2 → ℤ) : ‖charSmul k‖ ≤ ‖charLin k‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  rw [charSmul_apply, norm_smul]
  exact (mul_comm _ _).le

theorem norm_torusCharacter_le (k : Fin 2 → ℤ) (x : Vec 2) : ‖torusCharacter k x‖ ≤ 1 := by
  have h := (UnitAddTorus.mFourier (-k)).norm_coe_le_norm (toUnitTorus 2 x)
  rw [UnitAddTorus.mFourier_norm] at h
  exact h

theorem norm_iteratedFDeriv_torusCharacter_le (k : Fin 2 → ℤ) (c : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ c (torusCharacter k) x‖ ≤ ‖charLin k‖ ^ c := by
  induction c generalizing x with
  | zero => simpa using norm_torusCharacter_le k x
  | succ c ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_torusCharacter]
    have hτ : ContDiff ℝ c (torusCharacter k) := (torusCharacter_contDiff k).of_le le_top
    have e : iteratedFDeriv ℝ c (fun y => charSmul k (torusCharacter k y)) x =
        (charSmul k).compContinuousMultilinearMap
          (iteratedFDeriv ℝ c (torusCharacter k) x) :=
      (charSmul k).iteratedFDeriv_comp_left hτ.contDiffAt le_rfl
    rw [e]
    calc ‖(charSmul k).compContinuousMultilinearMap (iteratedFDeriv ℝ c (torusCharacter k) x)‖
        ≤ ‖charSmul k‖ * ‖iteratedFDeriv ℝ c (torusCharacter k) x‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ ‖charLin k‖ * ‖charLin k‖ ^ c :=
          mul_le_mul (norm_charSmul_le k) (ih x) (norm_nonneg _) (norm_nonneg _)
      _ = ‖charLin k‖ ^ (c + 1) := by ring

theorem torusCharacter_mul (m n : Fin 2 → ℤ) (x : Vec 2) :
    torusCharacter m x * torusCharacter n x = torusCharacter (m + n) x := by
  simp only [torusCharacter]
  rw [neg_add, UnitAddTorus.mFourier_add]

theorem volume_unitCell_two : (volume : Measure (Vec 2)) (unitCell 2) = 1 := by
  have hcell : unitCell 2 = Set.pi Set.univ (fun _ : Fin 2 => Set.Ioc (0 : ℝ) 1) := by
    ext x
    simp [unitCell, unitCellAt, Set.pi]
  rw [hcell, volume_pi_pi]
  simp

theorem integral_unitCell_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (c : E) :
    ∫ _x in unitCell 2, c = c := by
  rw [setIntegral_const]
  change ((volume : Measure (Vec 2)) (unitCell 2)).toReal • c = c
  rw [volume_unitCell_two]
  norm_num

/-- Orthogonality: `∫_{cell} torusCharacter n = [n = 0]`. -/
theorem integral_unitCell_torusCharacter (n : Fin 2 → ℤ) :
    ∫ x in unitCell 2, torusCharacter n x = if n = 0 then 1 else 0 := by
  have hs : HasSum (fun k => ‖smoothFourierCoeff (fun _ : Vec 2 => (1 : ℂ)) k‖ ^ 2) 1 := by
    have h := hasSum_sq_smoothFourierCoeff (f := fun _ : Vec 2 => (1 : ℂ)) continuous_const
    simp only [norm_one, one_pow, integral_unitCell_const] at h
    exact h
  have hcoef : ∀ k, smoothFourierCoeff (fun _ : Vec 2 => (1 : ℂ)) k =
      ∫ x in unitCell 2, torusCharacter k x := by
    intro k
    simp only [smoothFourierCoeff, mul_one]
  have h0 : smoothFourierCoeff (fun _ : Vec 2 => (1 : ℂ)) 0 = 1 := by
    rw [FourierCalculus.smoothFourierCoeff_zero_eq_integral (n := 1)]
    exact integral_unitCell_const 1
  split_ifs with hn
  · subst hn
    rw [← hcoef]
    exact h0
  · rw [← hcoef]
    have hle := sum_le_hasSum ({0, n} : Finset (Fin 2 → ℤ)) (fun k _ => sq_nonneg _) hs
    rw [Finset.sum_pair (Ne.symm hn), h0, norm_one, one_pow] at hle
    have h1 : ‖smoothFourierCoeff (fun _ : Vec 2 => (1 : ℂ)) n‖ ^ 2 ≤ 0 := by linarith
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm h1 (sq_nonneg _)))

theorem integral_unitCell_torusCharacter_mul (m k : Fin 2 → ℤ) :
    ∫ x in unitCell 2, torusCharacter m x * torusCharacter (-k) x = if m = k then 1 else 0 := by
  simp_rw [torusCharacter_mul]
  rw [integral_unitCell_torusCharacter]
  by_cases h : m = k
  · subst h
    simp
  · have h' : m + -k ≠ 0 := fun h'' => h (add_neg_eq_zero.mp h'')
    simp [h, h']

end AVRegularity.CleanupChain
end
end

section
@[expose] public section
open MeasureTheory Homogenization
namespace AVRegularity.CleanupChain

/-! Linear algebra of cell antidivergences: sums and finite sums (`IsCellAntidivergence.clm_comp`
handles continuous linear images). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isCellAntidivergence_zero (sX sZ : ℕ) :
    IsCellAntidivergence sX sZ (fun _ _ => (0 : E)) (fun _ _ _ => (0 : E)) := by
  refine ⟨IsBoxSmooth.zero, fun _ _ _ => rfl, fun _ _ => (0 : E), IsBoxSmooth.zero,
    fun _ _ _ => rfl, fun _ => ?_, fun _ _ _ => ?_, fun _ _ => ?_⟩
  · simp [fieldCellMean]
  · simp
  · simp

variable [CompleteSpace E]

theorem integrableOn_unitCube {u : Vec 2 → E} (hu : Continuous u) :
    IntegrableOn u AVenhance.unitCube :=
  (AVenhance.Infra.Torus.Calculus.continuous_integrableOn_unitCell hu).congr_set_ae
    AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.symm

theorem isCellAntidivergence_add {sX sZ : ℕ} (hZ : 1 ≤ sZ) {f g : Vec 2 → Vec 2 → E}
    {V W : Vec 2 → Vec 2 → Fin 2 → E} (hV : IsCellAntidivergence sX sZ f V)
    (hW : IsCellAntidivergence sX sZ g W) :
    IsCellAntidivergence sX sZ (fun X z => f X z + g X z) (fun X z k => V X z k + W X z k) := by
  obtain ⟨hVbox, hVper, φ, hφbox, hφper, hφmean, hVφ, hdivV⟩ := hV
  obtain ⟨hWbox, hWper, ψ, hψbox, hψper, hψmean, hWψ, hdivW⟩ := hW
  have hφ1 : ∀ X, Differentiable ℝ (φ X) := fun X =>
    (hφbox.1 X).differentiable (by exact_mod_cast Nat.succ_ne_zero sZ)
  have hψ1 : ∀ X, Differentiable ℝ (ψ X) := fun X =>
    (hψbox.1 X).differentiable (by exact_mod_cast Nat.succ_ne_zero sZ)
  have hVk : ∀ X (k : Fin 2), Differentiable ℝ (fun z => V X z k) := fun X k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k).contDiff.comp
      ((hVbox.1 X).of_le (show (1 : WithTop ℕ∞) ≤ (sZ : ℕ∞) by exact_mod_cast hZ))).differentiable
      (by norm_num)
  have hWk : ∀ X (k : Fin 2), Differentiable ℝ (fun z => W X z k) := fun X k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k).contDiff.comp
      ((hWbox.1 X).of_le (show (1 : WithTop ℕ∞) ≤ (sZ : ℕ∞) by exact_mod_cast hZ))).differentiable
      (by norm_num)
  refine ⟨hVbox.add hWbox, fun X n z => ?_, fun X z => φ X z + ψ X z, hφbox.add hψbox,
    fun X n z => ?_, fun X => ?_, fun X z k => ?_, fun X z => ?_⟩
  · funext k
    show V X (z + AVenhance.latticeShift n) k + W X (z + AVenhance.latticeShift n) k =
      V X z k + W X z k
    rw [hVper X n z, hWper X n z]
  · show φ X (z + AVenhance.latticeShift n) + ψ X (z + AVenhance.latticeShift n) =
      φ X z + ψ X z
    rw [hφper X n z, hψper X n z]
  · show ∫ z in AVenhance.unitCube, (φ X z + ψ X z) = 0
    have h1 : ∫ z in AVenhance.unitCube, φ X z = 0 := hφmean X
    have h2 : ∫ z in AVenhance.unitCube, ψ X z = 0 := hψmean X
    rw [integral_add (integrableOn_unitCube (hφbox.1 X).continuous)
      (integrableOn_unitCube (hψbox.1 X).continuous), h1, h2, add_zero]
  · show V X z k + W X z k = fderiv ℝ (fun z => φ X z + ψ X z) z (basisVec k)
    rw [fderiv_fun_add (hφ1 X z) (hψ1 X z), _root_.add_apply, hVφ X z k, hWψ X z k]
  · have h : ∀ k : Fin 2, fderiv ℝ (fun z' => V X z' k + W X z' k) z (basisVec k) =
        fderiv ℝ (fun z' => V X z' k) z (basisVec k) +
          fderiv ℝ (fun z' => W X z' k) z (basisVec k) := fun k => by
      rw [fderiv_fun_add (hVk X k z) (hWk X k z), _root_.add_apply]
    show ∑ k : Fin 2, fderiv ℝ (fun z' => V X z' k + W X z' k) z (basisVec k) =
      f X z + g X z
    rw [Finset.sum_congr rfl fun k _ => h k, Finset.sum_add_distrib, hdivV X z, hdivW X z]

theorem isCellAntidivergence_sum {ι : Type*} (s : Finset ι) {sX sZ : ℕ} (hZ : 1 ≤ sZ)
    {f : ι → Vec 2 → Vec 2 → E} {V : ι → Vec 2 → Vec 2 → Fin 2 → E}
    (h : ∀ i ∈ s, IsCellAntidivergence sX sZ (f i) (V i)) :
    IsCellAntidivergence sX sZ (fun X z => ∑ i ∈ s, f i X z)
      (fun X z k => ∑ i ∈ s, V i X z k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCellAntidivergence_zero (E := E) sX sZ
  | insert a s ha ih =>
    have := isCellAntidivergence_add hZ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

end AVRegularity.CleanupChain
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus
open scoped ENNReal
namespace AVRegularity.CleanupChain

/-! The coefficient space `ℓ²(ℤ²; ℂ)`, the coefficient sequence `coeffL2 u` of a continuous periodic
function (Parseval: `‖coeffL2 u‖² = ∫_{cell} |u|²`, hence `‖coeffL2 u‖ ≤ sup_{cell} |u|`), its
linearity, and bounded diagonal multipliers. -/

/-- `ℓ²(ℤ²; ℂ)`, the space of Fourier coefficient sequences on the two-torus. -/
abbrev FreqL2 : Type := lp (fun _ : Fin 2 → ℤ => ℂ) 2

theorem memℓp_two_iff {a : (Fin 2 → ℤ) → ℂ} : Memℓp a 2 ↔ Summable fun k => ‖a k‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

theorem hasSum_norm_sq (a : FreqL2) : HasSum (fun k => ‖a k‖ ^ 2) (‖a‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) a
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

open Classical in
/-- The `ℓ²` element with coordinates `a`, or `0` if `a` is not square summable. -/
def mkL2 (a : (Fin 2 → ℤ) → ℂ) : FreqL2 := if h : Memℓp a 2 then ⟨a, h⟩ else 0

theorem mkL2_apply {a : (Fin 2 → ℤ) → ℂ} (h : Summable fun k => ‖a k‖ ^ 2) (k : Fin 2 → ℤ) :
    mkL2 a k = a k := by
  have hm : Memℓp a 2 := memℓp_two_iff.mpr h
  rw [mkL2, dite_eq_left hm]

/-- The Fourier coefficient sequence of `u` over the unit cell, as an element of `ℓ²`. -/
def coeffL2 (u : Vec 2 → ℂ) : FreqL2 := mkL2 (smoothFourierCoeff u)

theorem coeffL2_apply {u : Vec 2 → ℂ} (hu : Continuous u) (k : Fin 2 → ℤ) :
    coeffL2 u k = smoothFourierCoeff u k :=
  mkL2_apply (hasSum_sq_smoothFourierCoeff hu).summable k

theorem norm_coeffL2_sq {u : Vec 2 → ℂ} (hu : Continuous u) :
    ‖coeffL2 u‖ ^ 2 = ∫ x in unitCell 2, ‖u x‖ ^ 2 := by
  have h1 := hasSum_norm_sq (coeffL2 u)
  simp only [coeffL2_apply hu] at h1
  exact h1.unique (hasSum_sq_smoothFourierCoeff hu)

/-- `‖coeffL2 u‖ ≤ M` when `|u| ≤ M` on the cell. -/
theorem norm_coeffL2_le {u : Vec 2 → ℂ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z ∈ unitCell 2, ‖u z‖ ≤ M) : ‖coeffL2 u‖ ≤ M := by
  have h2 : ‖coeffL2 u‖ ^ 2 ≤ M ^ 2 := by
    rw [norm_coeffL2_sq hu]
    calc ∫ x in unitCell 2, ‖u x‖ ^ 2 ≤ ∫ _x in unitCell 2, M ^ 2 :=
          setIntegral_mono_on (Calculus.continuous_integrableOn_unitCell (hu.norm.pow 2))
            (Calculus.continuous_integrableOn_unitCell continuous_const) (measurableSet_unitCell 2)
            fun x hx => pow_le_pow_left₀ (norm_nonneg _) (h x hx) 2
      _ = M ^ 2 := integral_unitCell_const _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hM two_ne_zero).mp h2

theorem coeffL2_sub {u w : Vec 2 → ℂ} (hu : Continuous u) (hw : Continuous w) :
    coeffL2 (fun z => u z - w z) = coeffL2 u - coeffL2 w := by
  refine lp.ext (funext fun k => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, coeffL2_apply (u := fun z => u z - w z) (hu.sub hw),
    coeffL2_apply hu, coeffL2_apply hw]
  exact smoothFourierCoeff_sub hu hw k

theorem coeffL2_smul_add {u w : Vec 2 → ℂ} (hu : Continuous u) (hw : Continuous w) (a b : ℝ) :
    coeffL2 (fun z => a • u z + b • w z) = a • coeffL2 u + b • coeffL2 w := by
  have hu' : Continuous fun z => (a : ℂ) * u z := continuous_const.mul hu
  have hw' : Continuous fun z => (b : ℂ) * w z := continuous_const.mul hw
  have e : (fun z => a • u z + b • w z) = fun z => (a : ℂ) * u z + (b : ℂ) * w z := by
    funext z
    simp only [Complex.real_smul]
  refine lp.ext (funext fun k => ?_)
  rw [e, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply,
    coeffL2_apply (u := fun z => (a : ℂ) * u z + (b : ℂ) * w z) (hu'.add hw'),
    coeffL2_apply hu, coeffL2_apply hw,
    smoothFourierCoeff_add hu' hw' k, smoothFourierCoeff_const_mul,
    smoothFourierCoeff_const_mul, Complex.real_smul, Complex.real_smul]

/-! ### Bounded diagonal multipliers -/

theorem summable_mul_of_bounded {c : (Fin 2 → ℤ) → ℂ} {C : ℝ} (hc : ∀ k, ‖c k‖ ≤ C)
    (a : FreqL2) : Summable fun k => ‖c k * a k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((hasSum_norm_sq a).summable.mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc k) 2) (sq_nonneg _)

/-- The diagonal multiplier `a ↦ (c_k a_k)_k` for a bounded symbol `c`. -/
def diagCLM (c : (Fin 2 → ℤ) → ℂ) (C : ℝ) (hc : ∀ k, ‖c k‖ ≤ C) : FreqL2 →L[ℝ] FreqL2 :=
  LinearMap.mkContinuous
    { toFun := fun a => mkL2 fun k => c k * a k
      map_add' := fun a b => by
        refine lp.ext (funext fun k => ?_)
        rw [mkL2_apply (summable_mul_of_bounded hc (a + b)), lp.coeFn_add, lp.coeFn_add,
          Pi.add_apply, Pi.add_apply, mkL2_apply (summable_mul_of_bounded hc a),
          mkL2_apply (summable_mul_of_bounded hc b), mul_add]
      map_smul' := fun r a => by
        refine lp.ext (funext fun k => ?_)
        rw [mkL2_apply (summable_mul_of_bounded hc (r • a)), lp.coeFn_smul, lp.coeFn_smul,
          Pi.smul_apply, Pi.smul_apply, mkL2_apply (summable_mul_of_bounded hc a),
          RingHom.id_apply, mul_smul_comm] }
    C
    (fun a => by
      have hC : 0 ≤ C := (norm_nonneg _).trans (hc 0)
      have h1 : ‖mkL2 (fun k => c k * a k)‖ ^ 2 ≤ (C * ‖a‖) ^ 2 := by
        have hs := hasSum_norm_sq (mkL2 fun k => c k * a k)
        simp only [mkL2_apply (summable_mul_of_bounded hc a)] at hs
        rw [← hs.tsum_eq, mul_pow, ← (hasSum_norm_sq a).tsum_eq, ← tsum_mul_left]
        refine (summable_mul_of_bounded hc a).tsum_le_tsum (fun k => ?_)
          ((hasSum_norm_sq a).summable.mul_left _)
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc k) 2)
          (sq_nonneg _)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
        two_ne_zero).mp h1)

theorem diagCLM_apply (c : (Fin 2 → ℤ) → ℂ) (C : ℝ) (hc : ∀ k, ‖c k‖ ≤ C) (a : FreqL2)
    (k : Fin 2 → ℤ) : diagCLM c C hc a k = c k * a k :=
  mkL2_apply (summable_mul_of_bounded hc a) k

end AVRegularity.CleanupChain
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CleanupChain

/-! Uniqueness of Fourier coefficients: a continuous `ℤ²`-periodic function whose cell Fourier
coefficients all vanish is zero (Parseval, continuity on the open cell, periodicity). -/

theorem eq_zero_of_smoothFourierCoeff_eq_zero {u : Vec 2 → ℂ} (hu : Continuous u)
    (hper : AVenhance.IsZ2Periodic u) (h0 : ∀ k, smoothFourierCoeff u k = 0) (x : Vec 2) :
    u x = 0 := by
  have hI : ∫ y in unitCell 2, ‖u y‖ ^ 2 = 0 := by
    have hs := hasSum_sq_smoothFourierCoeff hu
    have e : (fun k => ‖smoothFourierCoeff u k‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext k
      rw [h0 k, norm_zero]
      ring
    rw [e] at hs
    exact hs.unique hasSum_zero
  have hae : (fun y => ‖u y‖ ^ 2) =ᵐ[volume.restrict (unitCell 2)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _)
      (Calculus.continuous_integrableOn_unitCell (hu.norm.pow 2))).mp hI
  have hae' : ∀ᵐ y ∂(volume.restrict (unitCell 2)), u y = 0 := hae.mono fun y hy => by
    have h2 : ‖u y‖ ^ 2 = 0 := hy
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  have hUsub : (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1) ⊆ unitCell 2 := by
    intro y hy
    have hy' : ∀ i, y i ∈ Set.Ioo (0 : ℝ) 1 := fun i => hy i (Set.mem_univ i)
    simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add]
    exact fun i => ⟨(hy' i).1, (hy' i).2.le⟩
  have hUo : IsOpen (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have haeU : u =ᵐ[volume.restrict (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1)] 0 :=
    ae_restrict_of_ae_restrict_of_subset hUsub hae'
  have hEqU : Set.EqOn u 0 (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq haeU hUo hu.continuousOn continuous_const.continuousOn
  have hcl : closure (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1) =
      Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    rw [closure_pi_set]
    simp only [closure_Ioo zero_ne_one]
  have hEqC : Set.EqOn u 0 (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) := by
    rw [← hcl]
    exact hEqU.closure hu continuous_const
  let n : Fin 2 → ℤ := fun i => ⌊x i⌋
  have hy : (fun i => Int.fract (x i)) ∈ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 :=
    fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hxe : x = (fun i => Int.fract (x i)) + AVenhance.latticeShift n := by
    funext i
    simp only [Pi.add_apply, AVenhance.latticeShift, n, Int.fract_add_floor]
  rw [hxe, hper n]
  exact hEqC hy

/-- Two continuous periodic functions with the same Fourier coefficients agree. -/
theorem eq_of_smoothFourierCoeff_eq {u w : Vec 2 → ℂ} (hu : Continuous u) (hw : Continuous w)
    (hpu : AVenhance.IsZ2Periodic u) (hpw : AVenhance.IsZ2Periodic w)
    (h : ∀ k, smoothFourierCoeff u k = smoothFourierCoeff w k) (x : Vec 2) : u x = w x := by
  have hd := eq_zero_of_smoothFourierCoeff_eq_zero (u := fun y => u y - w y) (hu.sub hw)
    (fun n y => by simp only [hpu n y, hpw n y]) (fun k => by
      rw [smoothFourierCoeff_sub hu hw k, h k, sub_self]) x
  exact sub_eq_zero.mp hd

end AVRegularity.CleanupChain
end
end

section
@[expose] public noncomputable section
open Filter Topology
namespace AVRegularity.CleanupChain

/-! Weighted series maps `a ↦ ∑ₖ α_k a_k T_k` on `ℓ²(ℤ²; ℂ)` with `∑ ‖α_k‖² ‖T_k‖² < ∞`:
Cauchy–Schwarz for series, the continuous linear map, its norm bound, and continuity in a parameter
of the family `T` in operator norm. -/

/-- Cauchy–Schwarz for nonnegative series. -/
theorem summable_mul_and_le {ι : Type*} {f g : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf2 : Summable fun i => f i ^ 2) (hg2 : Summable fun i => g i ^ 2) :
    Summable (fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ √(∑' i, f i ^ 2) * √(∑' i, g i ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf2' : Summable fun i => f i ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hf2
  have hg2' : Summable fun i => g i ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hg2
  refine ⟨Real.summable_mul_of_Lp_Lq_of_nonneg hpq hf hg hf2' hg2', ?_⟩
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf2' hg2'
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h

section Series

variable {G : Type*} [NormedAddCommGroup G]

/-- The weighted square sum `∑ (‖α_k‖ ‖T_k‖)²`. -/
def seriesNormSq (α : (Fin 2 → ℤ) → ℂ) (T : (Fin 2 → ℤ) → G) : ℝ :=
  ∑' k, (‖α k‖ * ‖T k‖) ^ 2

theorem summable_series_norm {α : (Fin 2 → ℤ) → ℂ} {T : (Fin 2 → ℤ) → G}
    (hT : Summable fun k => (‖α k‖ * ‖T k‖) ^ 2) (a : FreqL2) :
    Summable (fun k => ‖α k‖ * ‖T k‖ * ‖a k‖) ∧
      ∑' k, ‖α k‖ * ‖T k‖ * ‖a k‖ ≤ √(seriesNormSq α T) * ‖a‖ := by
  have ha := hasSum_norm_sq a
  have h := summable_mul_and_le (f := fun k => ‖α k‖ * ‖T k‖) (g := fun k => ‖a k‖)
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun _ => norm_nonneg _) hT
    ha.summable
  beta_reduce at h
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [ha.tsum_eq, Real.sqrt_sq (norm_nonneg _)]
  rfl

variable [NormedSpace ℂ G] [CompleteSpace G]

theorem summable_series {α : (Fin 2 → ℤ) → ℂ} {T : (Fin 2 → ℤ) → G}
    (hT : Summable fun k => (‖α k‖ * ‖T k‖) ^ 2) (a : FreqL2) :
    Summable fun k => (α k * a k) • T k :=
  Summable.of_norm_bounded (summable_series_norm hT a).1 fun k => by
    rw [norm_smul, norm_mul]
    exact le_of_eq (by ring)

variable [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]

/-- The series map `a ↦ ∑ₖ (α_k a_k) • T_k`. -/
def seriesCLM (α : (Fin 2 → ℤ) → ℂ) (T : (Fin 2 → ℤ) → G)
    (hT : Summable fun k => (‖α k‖ * ‖T k‖) ^ 2) : FreqL2 →L[ℝ] G :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' k, (α k * a k) • T k
      map_add' := fun a b => by
        simp only [lp.coeFn_add, Pi.add_apply, mul_add, add_smul]
        exact (summable_series hT a).tsum_add (summable_series hT b)
      map_smul' := fun r a => by
        simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        rw [← (summable_series hT a).tsum_const_smul r]
        congr 1
        funext k
        rw [mul_smul_comm, smul_assoc] }
    (√(seriesNormSq α T))
    (fun a => by
      refine (tsum_of_norm_bounded (summable_series_norm hT a).1.hasSum fun k => ?_).trans
        (summable_series_norm hT a).2
      rw [norm_smul, norm_mul]
      exact le_of_eq (by ring))

theorem seriesCLM_apply (α : (Fin 2 → ℤ) → ℂ) (T : (Fin 2 → ℤ) → G)
    (hT : Summable fun k => (‖α k‖ * ‖T k‖) ^ 2) (a : FreqL2) :
    seriesCLM α T hT a = ∑' k, (α k * a k) • T k := rfl

theorem norm_seriesCLM_le (α : (Fin 2 → ℤ) → ℂ) (T : (Fin 2 → ℤ) → G)
    (hT : Summable fun k => (‖α k‖ * ‖T k‖) ^ 2) :
    ‖seriesCLM α T hT‖ ≤ √(seriesNormSq α T) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

theorem seriesCLM_sub (α : (Fin 2 → ℤ) → ℂ) {T T' : (Fin 2 → ℤ) → G}
    (hT : Summable fun k => (‖α k‖ * ‖T k‖) ^ 2) (hT' : Summable fun k => (‖α k‖ * ‖T' k‖) ^ 2)
    (hTT' : Summable fun k => (‖α k‖ * ‖(T - T') k‖) ^ 2) :
    seriesCLM α T hT - seriesCLM α T' hT' = seriesCLM α (T - T') hTT' := by
  refine ContinuousLinearMap.ext fun a => ?_
  rw [_root_.sub_apply, seriesCLM_apply, seriesCLM_apply, seriesCLM_apply,
    ← (summable_series hT a).tsum_sub (summable_series hT' a)]
  congr 1
  funext k
  rw [Pi.sub_apply, smul_sub]

/-- Continuity in operator norm of a family of series maps whose terms are continuous and
dominated by a square-summable bound. -/
theorem continuous_seriesCLM {Z : Type*} [TopologicalSpace Z] (α : (Fin 2 → ℤ) → ℂ)
    (T : Z → (Fin 2 → ℤ) → G) (B : (Fin 2 → ℤ) → ℝ)
    (hTc : ∀ k, Continuous fun z => T z k) (hB : ∀ z k, ‖T z k‖ ≤ B k)
    (hBs : Summable fun k => (‖α k‖ * B k) ^ 2)
    (hT : ∀ z, Summable fun k => (‖α k‖ * ‖T z k‖) ^ 2) :
    Continuous fun z => seriesCLM α (T z) (hT z) := by
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  have hb : ∀ z k, (‖α k‖ * ‖T z k - T z₀ k‖) ^ 2 ≤ 4 * (‖α k‖ * B k) ^ 2 := fun z k => by
    have h1 : ‖T z k - T z₀ k‖ ≤ 2 * B k :=
      (norm_sub_le _ _).trans (by linarith [hB z k, hB z₀ k])
    calc (‖α k‖ * ‖T z k - T z₀ k‖) ^ 2 ≤ (‖α k‖ * (2 * B k)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) 2
      _ = 4 * (‖α k‖ * B k) ^ 2 := by ring
  have hdiff : ∀ z, Summable fun k => (‖α k‖ * ‖(T z - T z₀) k‖) ^ 2 := fun z =>
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => hb z k) (hBs.mul_left 4)
  have hΔc : Continuous fun z => ∑' k, (‖α k‖ * ‖T z k - T z₀ k‖) ^ 2 := by
    refine continuous_tsum (fun k => ?_) (hBs.mul_left 4) (fun k z => ?_)
    · exact (continuous_const.fun_mul ((hTc k).fun_sub continuous_const).norm).fun_pow 2
    · show ‖(‖α k‖ * ‖T z k - T z₀ k‖) ^ 2‖ ≤ 4 * (‖α k‖ * B k) ^ 2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hb z k
  have hΔ0 : (∑' k, (‖α k‖ * ‖T z₀ k - T z₀ k‖) ^ 2) = 0 := by simp
  have hle : ∀ z, ‖seriesCLM α (T z) (hT z) - seriesCLM α (T z₀) (hT z₀)‖ ≤
      √(∑' k, (‖α k‖ * ‖T z k - T z₀ k‖) ^ 2) := fun z => by
    rw [seriesCLM_sub α (hT z) (hT z₀) (hdiff z)]
    exact norm_seriesCLM_le _ _ _
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) hle ?_
  have h : Tendsto (fun z => √(∑' k, (‖α k‖ * ‖T z k - T z₀ k‖) ^ 2)) (𝓝 z₀)
      (𝓝 (√(∑' k, (‖α k‖ * ‖T z₀ k - T z₀ k‖) ^ 2))) :=
    (Real.continuous_sqrt.comp hΔc).tendsto z₀
  rw [hΔ0, Real.sqrt_zero] at h
  exact h

end Series

end AVRegularity.CleanupChain
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus Filter Topology
namespace AVRegularity.CleanupChain

/-! Slow regularity of coefficient sequences: if `h(X, z)` is `C^m` in the slow variable `X` with
jointly continuous slow jets (`IsSlowSmooth m h`), then `X ↦ coeffL2 (h X)` is `C^m` as a map into
`ℓ²(ℤ²; ℂ)`. The derivative is the coefficient sequence of the slow derivative. The estimate is
Parseval (`‖coeffL2 u‖ ≤ sup_{cell} |u|`) with the mean-value inequality and uniform continuity
on the compact cell. -/

theorem natCast_succ_ne_zero (m : ℕ) : (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero m

/-- Uniform continuity in the slow variable over the compact closed cell. -/
theorem eventually_unif_closedCell {G : Type*} [NormedAddCommGroup G] {F : Vec 2 → Vec 2 → G}
    (hF : Continuous fun p : Vec 2 × Vec 2 => F p.1 p.2) (X : Vec 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X' in 𝓝 X, ∀ z ∈ Calculus.closedUnitCell 2, ‖F X' z - F X z‖ < ε := by
  refine (Calculus.isCompact_closedUnitCell 2).eventually_forall_of_forall_eventually
    fun z _ => ?_
  have hc2 : Continuous fun q : Vec 2 × Vec 2 => F X q.2 :=
    hF.comp (continuous_const.prodMk continuous_snd)
  have h1 : ∀ᶠ q in 𝓝 (X, z), ‖F q.1 q.2 - F X z‖ < ε / 2 :=
    (Metric.tendsto_nhds.mp (hF.tendsto (X, z)) (ε / 2) (half_pos hε)).mono
      fun q hq => by rwa [dist_eq_norm] at hq
  have h2 : ∀ᶠ q in 𝓝 (X, z), ‖F X q.2 - F X z‖ < ε / 2 :=
    (Metric.tendsto_nhds.mp (hc2.tendsto (X, z)) (ε / 2) (half_pos hε)).mono
      fun q hq => by rwa [dist_eq_norm] at hq
  filter_upwards [h1, h2] with q hq1 hq2
  calc ‖F q.1 q.2 - F X q.2‖ = ‖(F q.1 q.2 - F X z) - (F X q.2 - F X z)‖ := by
        congr 1
        abel
    _ ≤ ‖F q.1 q.2 - F X z‖ + ‖F X q.2 - F X z‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hq1 hq2
    _ = ε := add_halves ε

theorem continuous_coeffL2 {h : Vec 2 → Vec 2 → ℂ}
    (hc : Continuous fun p : Vec 2 × Vec 2 => h p.1 p.2) :
    Continuous fun X => coeffL2 (h X) := by
  have hz : ∀ X, Continuous (h X) := fun X => hc.comp (continuous_const.prodMk continuous_id)
  refine continuous_iff_continuousAt.2 fun X => Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [eventually_unif_closedCell hc X (half_pos hε)] with X' hX'
  rw [dist_eq_norm, ← coeffL2_sub (hz X') (hz X)]
  refine lt_of_le_of_lt (norm_coeffL2_le (u := fun z => h X' z - h X z)
    ((hz X').fun_sub (hz X)) (half_pos hε).le fun z hz' => ?_) (half_lt_self hε)
  exact (hX' z (Calculus.unitCell_subset_closedUnitCell 2 hz')).le

/-- The slow derivative of a slow-`C¹` two-scale field is jointly continuous. -/
theorem continuous_fderiv_slow_of_isSlowSmooth {m : ℕ} {h : Vec 2 → Vec 2 → ℂ}
    (hh : IsSlowSmooth (m + 1) h) :
    Continuous fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => h X p.2) p.1 := by
  refine continuous_clm_apply.2 fun y => ?_
  have e : (fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => h X p.2) p.1 y) =
      fun p => ∑ i : Fin 2, y i • slowPartial i h p.1 p.2 := by
    funext p
    conv_lhs => rw [vec_eq_sum_basisVec y]
    rw [map_sum]
    simp only [map_smul, slowPartial]
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.fun_smul (hh.slowPartial i).continuous_uncurry

/-- The slow derivative `v ↦ ∑ᵢ vᵢ coeffL2 (∂_{Xᵢ} h(X, ·))`, as a candidate Fréchet derivative. -/
def slowDerivL2 (h : Vec 2 → Vec 2 → ℂ) (X : Vec 2) : Vec 2 →L[ℝ] FreqL2 :=
  ∑ i : Fin 2, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).smulRight
    (coeffL2 (slowPartial i h X))

theorem slowDerivL2_apply {h : Vec 2 → Vec 2 → ℂ}
    (hc : ∀ i : Fin 2, ∀ X, Continuous (slowPartial i h X)) (X v : Vec 2) :
    slowDerivL2 h X v = coeffL2 (fun z => fderiv ℝ (fun X' => h X' z) X v) := by
  rw [slowDerivL2, Fin.sum_univ_two, _root_.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.proj_apply, ← coeffL2_smul_add (hc 0 X) (hc 1 X)]
  congr 1
  funext z
  simp only [slowPartial]
  conv_rhs => rw [vec_eq_sum_basisVec v]
  rw [map_sum, Fin.sum_univ_two, map_smul, map_smul]

/-- The derivative of `X ↦ coeffL2 (h X)` is `slowDerivL2 h X`. -/
theorem hasFDerivAt_coeffL2 {m : ℕ} {h : Vec 2 → Vec 2 → ℂ} (hh : IsSlowSmooth (m + 1) h)
    (X : Vec 2) : HasFDerivAt (fun X => coeffL2 (h X)) (slowDerivL2 h X) X := by
  have hspc : ∀ i : Fin 2, ∀ X, Continuous (slowPartial i h X) := fun i X =>
    (hh.slowPartial i).continuous_fast X
  have hzc : ∀ X, Continuous (h X) := fun X => hh.continuous_fast X
  have hJ := continuous_fderiv_slow_of_isSlowSmooth hh
  have hfdc : ∀ X v, Continuous fun z => fderiv ℝ (fun X' => h X' z) X v := fun X v =>
    (hJ.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  have hdiff : ∀ z X, DifferentiableAt ℝ (fun X' => h X' z) X := fun z X =>
    (hh.1 z).differentiable (natCast_succ_ne_zero m) X
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp
    (eventually_unif_closedCell (F := fun a b => fderiv ℝ (fun X' => h X' b) a) hJ X hc)
  filter_upwards [Metric.ball_mem_nhds (0 : Vec 2) hδ] with v hv
  show ‖coeffL2 (h (X + v)) - coeffL2 (h X) - slowDerivL2 h X v‖ ≤ c * ‖v‖
  have hsub : Continuous fun z => h (X + v) z - h X z := (hzc (X + v)).fun_sub (hzc X)
  rw [slowDerivL2_apply hspc, ← coeffL2_sub (hzc (X + v)) (hzc X),
    ← coeffL2_sub (u := fun z => h (X + v) z - h X z) hsub (hfdc X v)]
  refine norm_coeffL2_le
    (u := fun z => h (X + v) z - h X z - fderiv ℝ (fun X' => h X' z) X v)
    (hsub.fun_sub (hfdc X v)) (mul_nonneg hc.le (norm_nonneg v)) fun z hz => ?_
  have hzK : z ∈ Calculus.closedUnitCell 2 := Calculus.unitCell_subset_closedUnitCell 2 hz
  have hyv : X + v ∈ Metric.ball X δ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    rwa [Metric.mem_ball, dist_zero_right] at hv
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ)
    (f := fun X' => h X' z) (φ := fderiv ℝ (fun X' => h X' z) X)
    (fun X' _ => hdiff z X') (fun X' hX' => (hδ' hX' z hzK).le) (convex_ball X δ)
    (Metric.mem_ball_self hδ) hyv
  rw [add_sub_cancel_left] at hmv
  exact hmv

/-- `X ↦ coeffL2 (h X)` is `C^m` into `ℓ²` for a slow-`C^m` field with jointly continuous slow
jets. -/
theorem contDiff_coeffL2 (m : ℕ) : ∀ h : Vec 2 → Vec 2 → ℂ, IsSlowSmooth m h →
    ContDiff ℝ (m : ℕ∞) (fun X => coeffL2 (h X)) := by
  induction m with
  | zero =>
    intro h hh
    simpa [contDiff_zero] using continuous_coeffL2 hh.continuous_uncurry
  | succ m ih =>
    intro h hh
    have hsp : ∀ i : Fin 2, IsSlowSmooth m (slowPartial i h) := fun i => hh.slowPartial i
    have hD : ∀ X, HasFDerivAt (fun X => coeffL2 (h X)) (slowDerivL2 h X) X :=
      hasFDerivAt_coeffL2 hh
    have hDc : ContDiff ℝ (m : ℕ∞) (slowDerivL2 h) := by
      unfold slowDerivL2
      exact ContDiff.sum fun i _ => contDiff_const.smulRight (ih _ (hsp i))
    have hfd : fderiv ℝ (fun X => coeffL2 (h X)) = slowDerivL2 h :=
      funext fun X => (hD X).fderiv
    rw [show (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = ((m : ℕ∞) : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_fderiv]
    refine ⟨fun X => (hD X).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact hDc

end AVRegularity.CleanupChain
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus
open scoped Real
namespace AVRegularity.CleanupChain

/-! The `H^s` data map of a box-smooth periodic field. The pure fast jets `∂_{zᵢ}^s G` have Fourier
coefficients `(2πi kᵢ)^s Ĝ_k`. Multiplying them by the unimodular symbols `(-i sign kᵢ)^s` and
adding gives the coefficients `ω_k Ĝ(X)_k`, with `ω_k = ∑ᵢ (2π|kᵢ|)^s`. As a map into `ℓ²(ℤ²; ℂ)`
this is `C^m` in the slow variable when `G` is box smooth of orders `(m, s)`. -/

/-- The pure fast jet `∂_{zᵢ}^s g`. -/
def pureJet (i : Fin 2) (s : ℕ) (g : Vec 2 → ℂ) (z : Vec 2) : ℂ :=
  iteratedFDeriv ℝ s g z (fun _ => basisVec i)

theorem continuous_pureJet {g : Vec 2 → ℂ} {s : ℕ} (hg : ContDiff ℝ (s : ℕ∞) g) (i : Fin 2) :
    Continuous (pureJet i s g) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2) ℂ
    (fun _ => basisVec i)).continuous.comp (hg.continuous_iteratedFDeriv (by exact_mod_cast le_rfl))

theorem pureJet_zero (i : Fin 2) (g : Vec 2 → ℂ) : pureJet i 0 g = g := by
  funext z
  simp [pureJet]

theorem pureJet_succ {g : Vec 2 → ℂ} {s : ℕ} (hg : ContDiff ℝ ((s + 1 : ℕ) : ℕ∞) g) (i : Fin 2)
    (z : Vec 2) : pureJet i (s + 1) g z = fderiv ℝ (pureJet i s g) z (basisVec i) := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ s g) z :=
    hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self s) z
  have hF : HasFDerivAt (pureJet i s g)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2) ℂ (fun _ => basisVec i)).comp
        (fderiv ℝ (iteratedFDeriv ℝ s g) z)) z :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2) ℂ
      (fun _ => basisVec i)).hasFDerivAt.comp z hd.hasFDerivAt
  rw [hF.fderiv]
  rfl

theorem pureJet_periodic {g : Vec 2 → ℂ} (hper : AVenhance.IsZ2Periodic g) (i : Fin 2) (n : ℕ) :
    IsZdPeriodic (pureJet i n g) := by
  have hper' : IsZdPeriodic g := (isZdPeriodic_iff_frozen g).2 hper
  intro c z
  show iteratedFDeriv ℝ n g (z + intVector c) (fun _ => basisVec i) =
    iteratedFDeriv ℝ n g z (fun _ => basisVec i)
  rw [← iteratedFDeriv_comp_add_right]
  have e : (fun y => g (y + intVector c)) = g := funext fun y => hper' c y
  rw [e]

/-- `∂_{zᵢ}^n g` has Fourier coefficients `(2πi kᵢ)^n ĝ_k`. -/
theorem smoothFourierCoeff_pureJet {g : Vec 2 → ℂ} {s : ℕ} (hg : ContDiff ℝ (s : ℕ∞) g)
    (hper : AVenhance.IsZ2Periodic g) (i : Fin 2) :
    ∀ n, n ≤ s → ∀ k, smoothFourierCoeff (pureJet i n g) k =
      (2 * π * Complex.I * (k i : ℂ)) ^ n * smoothFourierCoeff g k := by
  intro n
  induction n with
  | zero =>
    intro _ k
    rw [pureJet_zero, pow_zero, one_mul]
  | succ n ih =>
    intro hn k
    have hg1 : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) g := hg.of_le (by exact_mod_cast hn)
    have hC1 : ContDiff ℝ 1 (pureJet i n g) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Vec 2) ℂ
        (fun _ => basisVec i)).contDiff.comp
        (hg.iteratedFDeriv_right (m := 1) (i := n) (by exact_mod_cast (by omega : 1 + n ≤ s)))
    have e : pureJet i (n + 1) g = coordDeriv i (pureJet i n g) :=
      funext fun z => pureJet_succ hg1 i z
    rw [e, smoothFourierCoeff_coordDeriv i hC1 (pureJet_periodic hper i n) k,
      ih (by omega) k, pow_succ]
    ring

/-- The unimodular symbol `(-i sign kᵢ)^s`. -/
def signSym (s : ℕ) (i : Fin 2) (k : Fin 2 → ℤ) : ℂ :=
  (-Complex.I * ((Int.sign (k i) : ℤ) : ℂ)) ^ s

theorem norm_signSym_le (s : ℕ) (i : Fin 2) (k : Fin 2 → ℤ) : ‖signSym s i k‖ ≤ 1 := by
  rw [signSym, norm_pow]
  refine pow_le_one₀ (norm_nonneg _) ?_
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_intCast]
  rcases Int.sign_trichotomy (k i) with h | h | h <;> simp [h]

theorem signSym_mul (s : ℕ) (i : Fin 2) (k : Fin 2 → ℤ) :
    signSym s i k * (2 * π * Complex.I * (k i : ℂ)) ^ s =
      ((2 * π * |(k i : ℝ)| : ℝ) : ℂ) ^ s := by
  rw [signSym, ← mul_pow]
  congr 1
  have hs : ((Int.sign (k i) : ℤ) : ℂ) * (k i : ℂ) = ((|k i| : ℤ) : ℂ) := by
    rw [← Int.cast_mul, Int.sign_mul_self_eq_abs]
  have habs : ((|k i| : ℤ) : ℂ) = ((|(k i : ℝ)| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_intCast, Int.cast_abs]
  calc -Complex.I * ((Int.sign (k i) : ℤ) : ℂ) * (2 * π * Complex.I * (k i : ℂ))
      = 2 * π * (-(Complex.I * Complex.I)) * (((Int.sign (k i) : ℤ) : ℂ) * (k i : ℂ)) := by
        ring
    _ = 2 * π * ((|(k i : ℝ)| : ℝ) : ℂ) := by
        rw [Complex.I_mul_I, neg_neg, mul_one, hs, habs]
    _ = ((2 * π * |(k i : ℝ)| : ℝ) : ℂ) := by
        simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- `ω_k = ∑ᵢ (2π|kᵢ|)^s`. -/
def omegaW (s : ℕ) (k : Fin 2 → ℤ) : ℝ := ∑ i : Fin 2, (2 * π * |(k i : ℝ)|) ^ s

theorem one_le_omegaW (s : ℕ) {k : Fin 2 → ℤ} (hk : k ≠ 0) : 1 ≤ omegaW s k := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
  have h1 : (1 : ℝ) ≤ |(k j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  have h2 : (1 : ℝ) ≤ 2 * π * |(k j : ℝ)| := by
    have hπ : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 2 * π * |(k j : ℝ)| := mul_le_mul hπ h1 zero_le_one (by positivity)
  calc (1 : ℝ) ≤ (2 * π * |(k j : ℝ)|) ^ s := one_le_pow₀ h2
    _ ≤ omegaW s k :=
      Finset.single_le_sum (f := fun i : Fin 2 => (2 * π * |(k i : ℝ)|) ^ s)
        (fun i _ => by positivity) (Finset.mem_univ j)

/-- The `H^s` data map `X ↦ (ω_k Ĝ(X)_k)_k ∈ ℓ²`. -/
def dataL2 (s : ℕ) (G : Vec 2 → Vec 2 → ℂ) (X : Vec 2) : FreqL2 :=
  diagCLM (signSym s 0) 1 (norm_signSym_le s 0) (coeffL2 (pureJet 0 s (G X))) +
    diagCLM (signSym s 1) 1 (norm_signSym_le s 1) (coeffL2 (pureJet 1 s (G X)))

theorem dataL2_apply {s : ℕ} {G : Vec 2 → Vec 2 → ℂ} (hG : ∀ X, ContDiff ℝ (s : ℕ∞) (G X))
    (hper : ∀ X, AVenhance.IsZ2Periodic (G X)) (X : Vec 2) (k : Fin 2 → ℤ) :
    dataL2 s G X k = (omegaW s k : ℂ) * smoothFourierCoeff (G X) k := by
  unfold dataL2
  rw [lp.coeFn_add, Pi.add_apply, diagCLM_apply, diagCLM_apply,
    coeffL2_apply (continuous_pureJet (hG X) 0), coeffL2_apply (continuous_pureJet (hG X) 1),
    smoothFourierCoeff_pureJet (hG X) (hper X) 0 s le_rfl k,
    smoothFourierCoeff_pureJet (hG X) (hper X) 1 s le_rfl k,
    ← mul_assoc, ← mul_assoc, signSym_mul, signSym_mul]
  simp only [omegaW, Fin.sum_univ_two]
  push_cast
  ring

theorem isSlowSmooth_pureJet {m s : ℕ} {G : Vec 2 → Vec 2 → ℂ} (hG : IsBoxSmooth m s G)
    (i : Fin 2) : IsSlowSmooth m (fun X z => pureJet i s (G X) z) :=
  IsSlowSmooth.clm_comp (f := fun X z => iteratedFDeriv ℝ s (G X) z)
    ⟨hG.2.1 s le_rfl, fun a ha => hG.2.2 a s ha le_rfl⟩
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2) ℂ (fun _ => basisVec i))

theorem contDiff_dataL2 {m s : ℕ} {G : Vec 2 → Vec 2 → ℂ} (hG : IsBoxSmooth m s G) :
    ContDiff ℝ (m : ℕ∞) (dataL2 s G) := by
  have h0 := contDiff_coeffL2 m _ (isSlowSmooth_pureJet hG 0)
  have h1 := contDiff_coeffL2 m _ (isSlowSmooth_pureJet hG 1)
  exact ((diagCLM (signSym s 0) 1 (norm_signSym_le s 0)).contDiff.comp h0).add
    ((diagCLM (signSym s 1) 1 (norm_signSym_le s 1)).contDiff.comp h1)

end AVRegularity.CleanupChain
end
end
