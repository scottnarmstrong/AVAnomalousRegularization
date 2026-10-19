-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.CleanupChain.DataMap
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Jets.Lift

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance.Infra.Torus Filter Topology
open scoped Real
namespace AVRegularity.CleanupChain

/-! Fourier synthesis with a slow parameter. For a multiplier `α` with
`∑ₖ (‖α_k‖ (2π(1 + |k|₁))^b)² < ∞` and a `C^m` map `A : Vec 2 → ℓ²(ℤ²; ℂ)`, the field
`Φ(X, z) = ∑ₖ α_k A(X)_k e^{2πik·z}` is box smooth of slow order `m` and fast order `b`. Its fast
jets are continuous linear images `jetCLM z (A X)` of `A X`, continuous in `z` in operator norm.
`Φ(X, ·)` is `ℤ²`-periodic and has Fourier coefficients `α_k A(X)_k`. -/

/-- The derivative weight `2π (1 + |k|₁)`. -/
def freqW (k : Fin 2 → ℤ) : ℝ := 2 * π * (1 + freqL1 k)

theorem one_le_freqW (k : Fin 2 → ℤ) : 1 ≤ freqW k := by
  have hπ : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  have hL : (1 : ℝ) ≤ 1 + freqL1 k := by linarith [freqL1_nonneg k]
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ 2 * π * (1 + freqL1 k) := mul_le_mul hπ hL zero_le_one (by positivity)

theorem freqW_nonneg (k : Fin 2 → ℤ) : 0 ≤ freqW k := zero_le_one.trans (one_le_freqW k)

theorem norm_iteratedFDeriv_char_le (k : Fin 2 → ℤ) (c : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ c (torusCharacter (-k)) z‖ ≤ freqW k ^ c := by
  refine (norm_iteratedFDeriv_torusCharacter_le (-k) c z).trans
    (pow_le_pow_left₀ (norm_nonneg _) ?_ c)
  calc ‖charLin (-k)‖ ≤ 2 * π * freqL1 (-k) := norm_charLin_le _
    _ = 2 * π * freqL1 k := by rw [freqL1_neg]
    _ ≤ freqW k := by
        unfold freqW
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem norm_iteratedFDeriv_char_le' (k : Fin 2 → ℤ) {c b : ℕ} (hc : c ≤ b) (z : Vec 2) :
    ‖iteratedFDeriv ℝ c (torusCharacter (-k)) z‖ ≤ freqW k ^ b :=
  (norm_iteratedFDeriv_char_le k c z).trans (pow_le_pow_right₀ (one_le_freqW k) hc)

section Jets

variable {α : (Fin 2 → ℤ) → ℂ} {b : ℕ}

theorem summable_jet (hα : Summable fun k => (‖α k‖ * freqW k ^ b) ^ 2) {c : ℕ} (hc : c ≤ b)
    (z : Vec 2) :
    Summable fun k => (‖α k‖ * ‖iteratedFDeriv ℝ c (torusCharacter (-k)) z‖) ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun k => pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_char_le' k hc z) (norm_nonneg _)) 2) hα

/-- The `c`-th fast jet at `z` of the synthesis, as a continuous linear map of the coefficients. -/
def jetCLM (α : (Fin 2 → ℤ) → ℂ) {b : ℕ} (hα : Summable fun k => (‖α k‖ * freqW k ^ b) ^ 2)
    (c : ℕ) (hc : c ≤ b) (z : Vec 2) :
    FreqL2 →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin c => Vec 2) ℂ :=
  seriesCLM α (fun k => iteratedFDeriv ℝ c (torusCharacter (-k)) z) (summable_jet hα hc z)

theorem continuous_jetCLM (hα : Summable fun k => (‖α k‖ * freqW k ^ b) ^ 2) (c : ℕ)
    (hc : c ≤ b) : Continuous fun z => jetCLM α hα c hc z := by
  unfold jetCLM
  exact continuous_seriesCLM α (fun z k => iteratedFDeriv ℝ c (torusCharacter (-k)) z)
    (fun k => freqW k ^ b)
    (fun k => (torusCharacter_contDiff (-k)).continuous_iteratedFDeriv le_top)
    (fun z k => norm_iteratedFDeriv_char_le' k hc z) hα (fun z => summable_jet hα hc z)

end Jets

/-- The synthesis `z ↦ ∑ₖ (α_k a_k) e^{2πik·z}`. -/
def synth (α : (Fin 2 → ℤ) → ℂ) (a : FreqL2) (z : Vec 2) : ℂ :=
  ∑' k, (α k * a k) • torusCharacter (-k) z

section Synth

variable {α : (Fin 2 → ℤ) → ℂ} {b : ℕ}

theorem summable_synthBound (hα : Summable fun k => (‖α k‖ * freqW k ^ b) ^ 2) (a : FreqL2) :
    Summable fun k => ‖α k‖ * freqW k ^ b * ‖a k‖ := by
  have h := summable_mul_and_le (f := fun k => ‖α k‖ * freqW k ^ b) (g := fun k => ‖a k‖)
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg (freqW_nonneg k) b))
    (fun _ => norm_nonneg _) hα (hasSum_norm_sq a).summable
  exact h.1

theorem contDiff_synth_term (α : (Fin 2 → ℤ) → ℂ) (a : FreqL2) (N : ℕ∞) (k : Fin 2 → ℤ) :
    ContDiff ℝ N (fun z => (α k * a k) • torusCharacter (-k) z) :=
  ((torusCharacter_contDiff (-k)).of_le le_top).const_smul _

theorem norm_iteratedFDeriv_synth_term_le (a : FreqL2) {c : ℕ} (hc : c ≤ b)
    (k : Fin 2 → ℤ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ c (fun z => (α k * a k) • torusCharacter (-k) z) z‖ ≤
      ‖α k‖ * freqW k ^ b * ‖a k‖ := by
  rw [iteratedFDeriv_const_smul_apply' ((torusCharacter_contDiff (-k)).contDiffAt.of_le le_top),
    norm_smul, norm_mul]
  calc ‖α k‖ * ‖a k‖ * ‖iteratedFDeriv ℝ c (torusCharacter (-k)) z‖
      ≤ ‖α k‖ * ‖a k‖ * freqW k ^ b :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_char_le' k hc z)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖α k‖ * freqW k ^ b * ‖a k‖ := by ring

theorem contDiff_synth (hα : Summable fun k => (‖α k‖ * freqW k ^ b) ^ 2) (a : FreqL2) :
    ContDiff ℝ (b : ℕ∞) (synth α a) := by
  unfold synth
  exact contDiff_tsum (contDiff_synth_term α a b)
    (v := fun _ k => ‖α k‖ * freqW k ^ b * ‖a k‖) (fun _ _ => summable_synthBound hα a)
    (fun c k z hc => norm_iteratedFDeriv_synth_term_le a (by exact_mod_cast hc) k z)

theorem iteratedFDeriv_synth (hα : Summable fun k => (‖α k‖ * freqW k ^ b) ^ 2) (a : FreqL2)
    {c : ℕ} (hc : c ≤ b) (z : Vec 2) :
    iteratedFDeriv ℝ c (synth α a) z = jetCLM α hα c hc z a := by
  unfold synth
  rw [iteratedFDeriv_tsum_apply (contDiff_synth_term α a b)
    (v := fun _ k => ‖α k‖ * freqW k ^ b * ‖a k‖) (fun _ _ => summable_synthBound hα a)
    (fun c' k z' hc' => norm_iteratedFDeriv_synth_term_le a (by exact_mod_cast hc') k z')
    (by exact_mod_cast hc) z, jetCLM, seriesCLM_apply]
  congr 1
  funext k
  exact iteratedFDeriv_const_smul_apply'
    ((torusCharacter_contDiff (-k)).contDiffAt.of_le le_top)

/-- **Synthesis with a slow parameter is box smooth.** -/
theorem isBoxSmooth_synth (hα : Summable fun k => (‖α k‖ * freqW k ^ b) ^ 2) {m : ℕ}
    {A : Vec 2 → FreqL2} (hA : ContDiff ℝ (m : ℕ∞) A) :
    IsBoxSmooth m b (fun X z => synth α (A X) z) := by
  refine ⟨fun X => contDiff_synth hα (A X), fun c hc z => ?_, fun a' c ha hc => ?_⟩
  · show ContDiff ℝ (m : ℕ∞) (fun X => iteratedFDeriv ℝ c (synth α (A X)) z)
    have e : (fun X => iteratedFDeriv ℝ c (synth α (A X)) z) = (jetCLM α hα c hc z) ∘ A :=
      funext fun X => iteratedFDeriv_synth hα (A X) hc z
    rw [e]
    exact (jetCLM α hα c hc z).contDiff.comp hA
  · show Continuous fun p : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a' (fun X' => iteratedFDeriv ℝ c (synth α (A X')) p.2) p.1
    have e : (fun p : Vec 2 × Vec 2 =>
        iteratedFDeriv ℝ a' (fun X' => iteratedFDeriv ℝ c (synth α (A X')) p.2) p.1) =
        fun p => (jetCLM α hα c hc p.2).compContinuousMultilinearMap
          (iteratedFDeriv ℝ a' A p.1) := by
      funext p
      have h1 : (fun X' => iteratedFDeriv ℝ c (synth α (A X')) p.2) =
          (jetCLM α hα c hc p.2) ∘ A :=
        funext fun X' => iteratedFDeriv_synth hα (A X') hc p.2
      rw [h1]
      exact (jetCLM α hα c hc p.2).iteratedFDeriv_comp_left hA.contDiffAt
        (by exact_mod_cast ha)
    rw [e]
    have hpair : Continuous fun p : Vec 2 × Vec 2 =>
        ((jetCLM α hα c hc p.2, iteratedFDeriv ℝ a' A p.1) :
          (FreqL2 →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin c => Vec 2) ℂ) ×
            ContinuousMultilinearMap ℝ (fun _ : Fin a' => Vec 2) FreqL2) :=
      ((continuous_jetCLM hα c hc).comp continuous_snd).prodMk
        ((hA.continuous_iteratedFDeriv (by exact_mod_cast ha)).comp continuous_fst)
    exact (isBoundedBilinearMap_compMultilinear (𝕜 := ℝ) (F := FreqL2)
      (G := ContinuousMultilinearMap ℝ (fun _ : Fin c => Vec 2) ℂ)
      (E := fun _ : Fin a' => Vec 2)).continuous.comp hpair

theorem synth_periodic (α : (Fin 2 → ℤ) → ℂ) (a : FreqL2) :
    AVenhance.IsZ2Periodic (synth α a) := by
  intro n x
  unfold synth
  congr 1
  funext k
  rw [((isZdPeriodic_iff_frozen _).1 (torusCharacter_periodic (-k))) n x]

/-- The Fourier coefficients of the synthesis are `α_k a_k`. -/
theorem smoothFourierCoeff_synth (hα : Summable fun k => (‖α k‖ * freqW k ^ b) ^ 2)
    (a : FreqL2) (m : Fin 2 → ℤ) : smoothFourierCoeff (synth α a) m = α m * a m := by
  have hcont : ∀ k : Fin 2 → ℤ, Continuous fun x : Vec 2 =>
      α k * a k * (torusCharacter m x * torusCharacter (-k) x) := fun k =>
    continuous_const.fun_mul ((torusCharacter_contDiff m).continuous.fun_mul
      (torusCharacter_contDiff (-k)).continuous)
  have hCs : Summable fun k => ‖α k * a k‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (summable_synthBound hα a)
    rw [norm_mul]
    have h1 : (1 : ℝ) ≤ freqW k ^ b := one_le_pow₀ (one_le_freqW k)
    calc ‖α k‖ * ‖a k‖ = ‖α k‖ * 1 * ‖a k‖ := by ring
      _ ≤ ‖α k‖ * freqW k ^ b * ‖a k‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
            (norm_nonneg _)
  have hFi : ∀ k : Fin 2 → ℤ, Integrable (fun x : Vec 2 =>
      α k * a k * (torusCharacter m x * torusCharacter (-k) x)) (volume.restrict (unitCell 2)) :=
    fun k => Calculus.continuous_integrableOn_unitCell (hcont k)
  have hFn : Summable fun k : Fin 2 → ℤ => ∫ x in unitCell 2,
      ‖α k * a k * (torusCharacter m x * torusCharacter (-k) x)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_) hCs
    calc ∫ x in unitCell 2, ‖α k * a k * (torusCharacter m x * torusCharacter (-k) x)‖
        ≤ ∫ _x in unitCell 2, ‖α k * a k‖ := by
          refine setIntegral_mono_on (Calculus.continuous_integrableOn_unitCell (hcont k).norm)
            (Calculus.continuous_integrableOn_unitCell continuous_const)
            (measurableSet_unitCell 2) fun x _ => ?_
          rw [norm_mul, norm_mul (torusCharacter m x)]
          calc ‖α k * a k‖ * (‖torusCharacter m x‖ * ‖torusCharacter (-k) x‖)
              ≤ ‖α k * a k‖ * (1 * 1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul (norm_torusCharacter_le _ _)
                  (norm_torusCharacter_le _ _) (norm_nonneg _) zero_le_one) (norm_nonneg _)
            _ = ‖α k * a k‖ := by ring
      _ = ‖α k * a k‖ := integral_unitCell_const _
  have hsum := hasSum_integral_of_summable_integral_norm hFi hFn
  have hval : ∀ k : Fin 2 → ℤ, ∫ x in unitCell 2,
      α k * a k * (torusCharacter m x * torusCharacter (-k) x) =
        if k = m then α m * a m else 0 := by
    intro k
    rw [integral_const_mul, integral_unitCell_torusCharacter_mul]
    by_cases hk : k = m
    · subst hk
      simp
    · simp [hk, Ne.symm hk]
  have htsum : ∀ x : Vec 2, ∑' k, α k * a k * (torusCharacter m x * torusCharacter (-k) x) =
      torusCharacter m x * synth α a x := by
    intro x
    unfold synth
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [smul_eq_mul]
    ring
  have h1 : HasSum (fun k : Fin 2 → ℤ => ∫ x in unitCell 2,
      α k * a k * (torusCharacter m x * torusCharacter (-k) x)) (α m * a m) := by
    simp_rw [hval]
    exact hasSum_ite_eq m _
  unfold smoothFourierCoeff
  simp_rw [← htsum]
  exact hsum.unique h1

end Synth

end AVRegularity.CleanupChain
end

section
open MeasureTheory Homogenization AVenhance.Infra.Torus
open scoped Real
namespace AVRegularity.CleanupChain

/-! The multipliers of the cleanup chain on normalized coefficients `P_k = ω_k 4π²|k|² φ̂_k`.
- `alphaW s k = (ω_k 4π² |k|²)⁻¹` (`0` at `k = 0`) recovers `φ̂_k = α_k P_k`. It is square
  summable against the weight `(2π(1 + |k|₁))^s`, so the synthesis is box smooth of fast order `s`.
- `mulSym s i k = ω_k (2πi kᵢ) α_k` maps `P` to the normalized coefficients of `∂_{zᵢ} φ`. It is
  bounded by `1`. -/

/-- `α_k = (ω_k 4π² |k|²)⁻¹` for `k ≠ 0`, and `α_0 = 0`. -/
def alphaW (s : ℕ) (k : Fin 2 → ℤ) : ℂ :=
  if k = 0 then 0 else (((omegaW s k * (4 * π ^ 2 * freqSq k))⁻¹ : ℝ) : ℂ)

theorem alphaW_zero (s : ℕ) : alphaW s 0 = 0 := by
  rw [alphaW, ite_eq_left rfl]

theorem alphaW_of_ne (s : ℕ) {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    alphaW s k = (((omegaW s k * (4 * π ^ 2 * freqSq k))⁻¹ : ℝ) : ℂ) := by
  rw [alphaW, ite_eq_right hk]

theorem denom_pos (s : ℕ) {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    0 < omegaW s k * (4 * π ^ 2 * freqSq k) :=
  mul_pos (lt_of_lt_of_le one_pos (one_le_omegaW s hk))
    (mul_pos (by positivity) (lt_of_lt_of_le one_pos (one_le_freqSq hk)))

/-- `4π² |k|² ω_k α_k = 1` for `k ≠ 0`. -/
theorem alphaW_mul (s : ℕ) {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    ((4 * π ^ 2 * freqSq k : ℝ) : ℂ) * (omegaW s k : ℂ) * alphaW s k = 1 := by
  rw [alphaW_of_ne s hk, ← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_comm (4 * π ^ 2 * _),
    mul_inv_cancel₀ (denom_pos s hk).ne', Complex.ofReal_one]

theorem summable_alphaW (s : ℕ) : Summable fun k => (‖alphaW s k‖ * freqW k ^ s) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_)
    (summable_inv_one_add_freqL1_pow_four.mul_left ((2 * π) ^ (2 * s) * 2 ^ (2 * s + 2)))
  by_cases hk : k = 0
  · subst hk
    rw [alphaW_zero, norm_zero, zero_mul, zero_pow two_ne_zero]
    positivity
  · have hpos : 0 ≤ (omegaW s k * (4 * π ^ 2 * freqSq k))⁻¹ := (inv_pos.mpr (denom_pos s hk)).le
    have hL : 1 ≤ |(k 0 : ℝ)| + |(k 1 : ℝ)| := by
      rw [← freqL1_eq]
      exact one_le_freqL1 hk
    have hω : omegaW s k = (2 * π) ^ s * (|(k 0 : ℝ)| ^ s + |(k 1 : ℝ)| ^ s) := by
      simp only [omegaW, Fin.sum_univ_two, mul_pow]
      ring
    have hD := inv_sq_mul_le s _ _ (abs_nonneg (k 0 : ℝ)) (abs_nonneg (k 1 : ℝ)) hL
    rw [alphaW_of_ne s hk, Complex.norm_of_nonneg hpos, hω, freqSq_eq_abs]
    unfold freqW
    rw [freqL1_eq]
    set a := |(k 0 : ℝ)|
    set b := |(k 1 : ℝ)|
    set D := (2 * π) ^ s * (a ^ s + b ^ s) * (4 * π ^ 2 * (a ^ 2 + b ^ 2))
    calc (D⁻¹ * (2 * π * (1 + (a + b))) ^ s) ^ 2
        = (2 * π) ^ (2 * s) * ((D⁻¹) ^ 2 * (1 + (a + b)) ^ (2 * s)) := by
          rw [mul_pow D⁻¹, ← pow_mul, mul_pow (2 * π), mul_comm s 2]
          ring
      _ ≤ (2 * π) ^ (2 * s) * (2 ^ (2 * s + 2) * ((1 + (a + b)) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = (2 * π) ^ (2 * s) * 2 ^ (2 * s + 2) * ((1 + (a + b)) ^ 4)⁻¹ := by ring

/-- The symbol `ω_k (2πi kᵢ) α_k` of the cleanup step on normalized coefficients. -/
def mulSym (s : ℕ) (i : Fin 2) (k : Fin 2 → ℤ) : ℂ :=
  (omegaW s k : ℂ) * (2 * π * Complex.I * (k i : ℂ)) * alphaW s k

theorem norm_twoPiI_mul (m : ℤ) :
    ‖(2 * (π : ℂ) * Complex.I * (m : ℂ))‖ = 2 * π * |(m : ℝ)| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_I, Complex.norm_intCast]
  ring

theorem norm_mulSym_le (s : ℕ) (i : Fin 2) (k : Fin 2 → ℤ) : ‖mulSym s i k‖ ≤ 1 := by
  by_cases hk : k = 0
  · subst hk
    simp [mulSym, alphaW_zero]
  · have hD := denom_pos s hk
    have hω : 0 < omegaW s k := lt_of_lt_of_le one_pos (one_le_omegaW s hk)
    rw [mulSym, alphaW_of_ne s hk, norm_mul, norm_mul, Complex.norm_of_nonneg hω.le,
      norm_twoPiI_mul, Complex.norm_of_nonneg (inv_pos.mpr hD).le, ← div_eq_mul_inv,
      div_le_one hD]
    refine mul_le_mul_of_nonneg_left ?_ hω.le
    have h1 := abs_le_freqSq k i
    have h2 : 2 * π ≤ 4 * π ^ 2 := by
      calc 2 * π = 2 * π * 1 := by ring
        _ ≤ 2 * π * (2 * π) :=
            mul_le_mul_of_nonneg_left (by linarith [Real.two_le_pi]) (by positivity)
        _ = 4 * π ^ 2 := by ring
    calc 2 * π * |(k i : ℝ)| ≤ 2 * π * freqSq k :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 4 * π ^ 2 * freqSq k := mul_le_mul_of_nonneg_right h2 (freqSq_nonneg k)

/-- The cleanup step on normalized coefficients, `P ↦ (mulSym_k P_k)_k`. -/
def mulCLM (s : ℕ) (i : Fin 2) : FreqL2 →L[ℝ] FreqL2 :=
  diagCLM (mulSym s i) 1 (norm_mulSym_le s i)

theorem mulCLM_apply (s : ℕ) (i : Fin 2) (a : FreqL2) (k : Fin 2 → ℤ) :
    mulCLM s i a k = mulSym s i k * a k :=
  diagCLM_apply _ _ _ a k

/-! The periodic Poisson solver with a slow parameter, on normalized coefficients. The potential
is `φ(X, ·) = ∑ₖ α_k P(X)_k e_k`, with `α_k = (ω_k 4π²|k|²)⁻¹`.
- If `P(X)_k = -ω_k ĝ(X)_k` and `ĝ(X)_0 = 0`, then `Δ_z φ = div_z ∇_z φ = g`.
- `φ` is box smooth through `(n, q + 1)` and `∇_z φ` through `(n, q)` when `P` is `C^n`.
- `φ(X, ·)` is periodic with zero cell mean.
- `ω_k (∂_{zᵢ} φ)^_k = mulSym_k P_k`. -/

section
/-- The potential `φ(X, ·) = ∑ₖ α_k P(X)_k e_k`. -/
def potential (s : ℕ) (P : Vec 2 → FreqL2) (X z : Vec 2) : ℂ := synth (alphaW s) (P X) z

/-- The fast gradient `∇_z φ`. -/
def gradPot (s : ℕ) (P : Vec 2 → FreqL2) (X z : Vec 2) : Fin 2 → ℂ :=
  fun i => fderiv ℝ (potential s P X) z (basisVec i)

/-- A component of the fast gradient, `∂_{zᵢ} φ(X, ·)`. -/
def gradComp (s : ℕ) (P : Vec 2 → FreqL2) (X : Vec 2) (i : Fin 2) (z : Vec 2) : ℂ :=
  gradPot s P X z i

theorem smoothFourierCoeff_zero_eq_fieldCellMean (u : Vec 2 → ℂ) :
    smoothFourierCoeff u 0 = fieldCellMean u := by
  rw [FourierCalculus.smoothFourierCoeff_zero_eq_integral (n := 1)]
  exact integral_unitCell_eq_unitCube u

theorem fderiv_periodic {f : Vec 2 → ℂ} (hf : AVenhance.IsZ2Periodic f) (v : Vec 2) :
    AVenhance.IsZ2Periodic (fun z => fderiv ℝ f z v) := by
  intro n z
  show fderiv ℝ f (z + AVenhance.latticeShift n) v = fderiv ℝ f z v
  rw [← fderiv_comp_add_right]
  have e : (fun y => f (y + AVenhance.latticeShift n)) = f := funext fun y => hf n y
  rw [e]

section Potential

variable (s : ℕ) (P : Vec 2 → FreqL2) (X : Vec 2)

theorem potential_contDiff : ContDiff ℝ (s : ℕ∞) (potential s P X) :=
  contDiff_synth (summable_alphaW s) (P X)

theorem potential_periodic : AVenhance.IsZ2Periodic (potential s P X) :=
  synth_periodic _ _

theorem smoothFourierCoeff_potential (k : Fin 2 → ℤ) :
    smoothFourierCoeff (potential s P X) k = alphaW s k * P X k :=
  smoothFourierCoeff_synth (summable_alphaW s) (P X) k

theorem potential_mean : fieldCellMean (potential s P X) = 0 := by
  rw [← smoothFourierCoeff_zero_eq_fieldCellMean, smoothFourierCoeff_potential, alphaW_zero,
    zero_mul]

theorem gradPot_periodic : AVenhance.IsZ2Periodic (gradPot s P X) := fun n z =>
  funext fun i => fderiv_periodic (potential_periodic s P X) (basisVec i) n z

theorem gradComp_periodic (i : Fin 2) : AVenhance.IsZ2Periodic (gradComp s P X i) :=
  fderiv_periodic (potential_periodic s P X) (basisVec i)

theorem gradComp_contDiff {q : ℕ} (i : Fin 2) :
    ContDiff ℝ (q : ℕ∞) (gradComp (q + 1) P X i) :=
  ((potential_contDiff (q + 1) P X).fderiv_right (m := (q : ℕ∞))
    (by exact_mod_cast le_rfl)).clm_apply contDiff_const

theorem smoothFourierCoeff_gradComp (hs : 1 ≤ s) (i : Fin 2) (k : Fin 2 → ℤ) :
    smoothFourierCoeff (gradComp s P X i) k =
      (2 * π * Complex.I * (k i : ℂ)) * (alphaW s k * P X k) := by
  rw [← smoothFourierCoeff_potential s P X k]
  exact smoothFourierCoeff_coordDeriv i
    ((potential_contDiff s P X).of_le (by exact_mod_cast hs))
    ((isZdPeriodic_iff_frozen _).2 (potential_periodic s P X)) k

/-- `ω_k (∂_{zᵢ} φ)^_k = mulSym_k P_k`. -/
theorem omega_mul_coeff_gradComp (hs : 1 ≤ s) (i : Fin 2) (k : Fin 2 → ℤ) :
    (omegaW s k : ℂ) * smoothFourierCoeff (gradComp s P X i) k = mulCLM s i (P X) k := by
  rw [smoothFourierCoeff_gradComp s P X hs, mulCLM_apply, mulSym]
  ring

theorem smoothFourierCoeff_gradComp_zero (hs : 1 ≤ s) (i : Fin 2) :
    smoothFourierCoeff (gradComp s P X i) 0 = 0 := by
  rw [smoothFourierCoeff_gradComp s P X hs, alphaW_zero]
  ring

end Potential

theorem gradPot_isBoxSmooth {n q : ℕ} {P : Vec 2 → FreqL2} (hP : ContDiff ℝ (n : ℕ∞) P) :
    IsBoxSmooth n q (gradPot (q + 1) P) :=
  (isBoxSmooth_synth (summable_alphaW (q + 1)) hP).fderiv_fast.map_clm
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.apply ℝ ℂ (basisVec i))

theorem potential_isBoxSmooth {n s : ℕ} {P : Vec 2 → FreqL2} (hP : ContDiff ℝ (n : ℕ∞) P) :
    IsBoxSmooth n s (potential s P) :=
  isBoxSmooth_synth (summable_alphaW s) hP

theorem sum_sq_twoPiI (k : Fin 2 → ℤ) :
    (2 * (π : ℂ) * Complex.I * (k 0 : ℂ)) ^ 2 + (2 * (π : ℂ) * Complex.I * (k 1 : ℂ)) ^ 2 =
      -((4 * π ^ 2 * freqSq k : ℝ) : ℂ) := by
  have e : ((4 * π ^ 2 * freqSq k : ℝ) : ℂ) =
      4 * (π : ℂ) ^ 2 * ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2) := by
    simp only [freqSq, Fin.sum_univ_two, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_intCast]
  rw [e]
  linear_combination (4 * (π : ℂ) ^ 2 * ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2)) * Complex.I_sq

/-- **The Poisson identity.** If `P(X)_k = -ω_k ĝ_k` and `ĝ_0 = 0`, then `div_z ∇_z φ = g`. -/
theorem div_gradPot {q : ℕ} (hq : 1 ≤ q) (P : Vec 2 → FreqL2) (X : Vec 2) {g : Vec 2 → ℂ}
    (hgc : Continuous g) (hgp : AVenhance.IsZ2Periodic g)
    (hPg : ∀ k, P X k = -((omegaW (q + 1) k : ℂ) * smoothFourierCoeff g k))
    (hg0 : smoothFourierCoeff g 0 = 0) (z : Vec 2) :
    ∑ i : Fin 2, fderiv ℝ (fun z' => gradPot (q + 1) P X z' i) z (basisVec i) = g z := by
  have hψ : ∀ i : Fin 2, ContDiff ℝ 1 (gradComp (q + 1) P X i) := fun i =>
    (gradComp_contDiff P X i).of_le (by exact_mod_cast hq)
  have hψp : ∀ i : Fin 2, IsZdPeriodic (gradComp (q + 1) P X i) := fun i =>
    (isZdPeriodic_iff_frozen _).2 (gradComp_periodic (q + 1) P X i)
  have hdc : ∀ i : Fin 2, Continuous (coordDeriv i (gradComp (q + 1) P X i)) := fun i =>
    continuous_coordDeriv i (hψ i)
  have hdp : ∀ i : Fin 2, AVenhance.IsZ2Periodic (coordDeriv i (gradComp (q + 1) P X i)) :=
    fun i => fderiv_periodic (gradComp_periodic (q + 1) P X i) (basisVec i)
  have hcoef : ∀ (i : Fin 2) (k : Fin 2 → ℤ),
      smoothFourierCoeff (coordDeriv i (gradComp (q + 1) P X i)) k =
        (2 * π * Complex.I * (k i : ℂ)) *
          ((2 * π * Complex.I * (k i : ℂ)) * (alphaW (q + 1) k * P X k)) := by
    intro i k
    rw [smoothFourierCoeff_coordDeriv i (hψ i) (hψp i) k,
      smoothFourierCoeff_gradComp (q + 1) P X (by omega) i k]
  have hper : AVenhance.IsZ2Periodic (fun y => coordDeriv 0 (gradComp (q + 1) P X 0) y +
      coordDeriv 1 (gradComp (q + 1) P X 1) y) := fun n y => by
    simp only [(hdp 0) n y, (hdp 1) n y]
  have hcoeff : ∀ k, smoothFourierCoeff (fun y => coordDeriv 0 (gradComp (q + 1) P X 0) y +
      coordDeriv 1 (gradComp (q + 1) P X 1) y) k = smoothFourierCoeff g k := by
    intro k
    rw [smoothFourierCoeff_add (hdc 0) (hdc 1) k, hcoef 0 k, hcoef 1 k, hPg k]
    by_cases hk : k = 0
    · subst hk
      rw [alphaW_zero, hg0]
      ring
    · have h1 := alphaW_mul (q + 1) hk
      have h2 := sum_sq_twoPiI k
      linear_combination (-(alphaW (q + 1) k * (omegaW (q + 1) k : ℂ) *
        smoothFourierCoeff g k)) * h2 + smoothFourierCoeff g k * h1
  have key := eq_of_smoothFourierCoeff_eq
    (u := fun y => coordDeriv 0 (gradComp (q + 1) P X 0) y +
      coordDeriv 1 (gradComp (q + 1) P X 1) y) ((hdc 0).fun_add (hdc 1)) hgc hper hgp hcoeff z
  rw [Fin.sum_univ_two]
  exact key
end

/-! The cleanup chain on normalized coefficients, for scalar complex data `(f₀, F₀)`.
- `Pchain 0 = -D_{f₀}`, where `D_G(X)_k = ω_k Ĝ(X)_k` is the data map.
- `Pchain (j+1) = ∑ᵢ ∂_{Xᵢ} Rᵢ`, with `Rᵢ = [j = 0] D_{F₀ᵢ} + mulCLM i ∘ Pchain j` the normalized
  coefficients of `V_j`.
- The fields are `V_j = [j = 0] F₀ + ∇_z φ_j`, with `φ_j` synthesized from `Pchain j`.
- The sources are `g_0 = f₀` and `g_j = cleanupSource V j` for `j ≥ 1`. -/

section
/-- The `k`-th coordinate of the derivative of an `ℓ²`-valued map. -/
theorem fderiv_apply_freq {G : Vec 2 → FreqL2} {X : Vec 2} (hG : DifferentiableAt ℝ G X)
    (k : Fin 2 → ℤ) (v : Vec 2) : fderiv ℝ (fun X => G X k) X v = fderiv ℝ G X v k := by
  have h := (lp.evalCLM ℝ (fun _ : Fin 2 → ℤ => ℂ) 2 k).hasFDerivAt.comp X hG.hasFDerivAt
  exact DFunLike.congr_fun h.fderiv v

theorem differentiableAt_apply_freq {G : Vec 2 → FreqL2} {X : Vec 2}
    (hG : DifferentiableAt ℝ G X) (k : Fin 2 → ℤ) : DifferentiableAt ℝ (fun X => G X k) X :=
  ((lp.evalCLM ℝ (fun _ : Fin 2 → ℤ => ℂ) 2 k).hasFDerivAt.comp X hG.hasFDerivAt).differentiableAt

theorem smoothFourierCoeff_neg_add {a b : Vec 2 → ℂ} (ha : Continuous a) (hb : Continuous b)
    (k : Fin 2 → ℤ) :
    smoothFourierCoeff (fun z => -(a z + b z)) k =
      -(smoothFourierCoeff a k + smoothFourierCoeff b k) := by
  have e : (fun z => -(a z + b z)) = fun z => (-1 : ℂ) * (a z + b z) := by
    funext z
    ring
  rw [e, smoothFourierCoeff_const_mul, smoothFourierCoeff_add ha hb k]
  ring

section Defs

variable (s : ℕ) (f₀ : Vec 2 → Vec 2 → ℂ) (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ)

/-- The flux added at step `j`: `F₀` at `j = 0`, else `0`. -/
def Evec (j : ℕ) : Vec 2 → Vec 2 → Fin 2 → ℂ := if j = 0 then F₀ else fun _ _ => 0

/-- Normalized coefficients of the added flux: `D_{F₀ᵢ}` at `j = 0`, else `0`. -/
def Qmap (j : ℕ) (i : Fin 2) : Vec 2 → FreqL2 :=
  if j = 0 then dataL2 s (fun X z => F₀ X z i) else fun _ => 0

/-- Normalized coefficients of `V_j` from those of `φ_j`. -/
def Rmap (j : ℕ) (P : Vec 2 → FreqL2) (i : Fin 2) (X : Vec 2) : FreqL2 :=
  Qmap s F₀ j i X + mulCLM s i (P X)

/-- The normalized potential coefficients of the chain. -/
def Pchain : ℕ → Vec 2 → FreqL2
  | 0 => fun X => -dataL2 s f₀ X
  | j + 1 => fun X => ∑ i : Fin 2, fderiv ℝ (Rmap s F₀ j (Pchain j) i) X (basisVec i)

/-- The chain fields `V_j = [j = 0] F₀ + ∇_z φ_j`. -/
def Vchain (j : ℕ) : Vec 2 → Vec 2 → Fin 2 → ℂ :=
  fun X z => Evec F₀ j X z + gradPot s (Pchain s f₀ F₀ j) X z

/-- A component of a chain field, as a scalar two-scale field. -/
def Vcomp (j : ℕ) (i : Fin 2) : Vec 2 → Vec 2 → ℂ := fun X z => Vchain s f₀ F₀ j X z i

/-- The chain sources: `g_0 = f₀`, `g_j = cleanupSource V j` for `j ≥ 1`. -/
def gchain (j : ℕ) : Vec 2 → Vec 2 → ℂ :=
  if j = 0 then f₀ else cleanupSource (Vchain s f₀ F₀) j

end Defs

theorem Evec_zero (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ) : Evec F₀ 0 = F₀ := by
  rw [Evec, ite_eq_left rfl]

theorem Evec_succ (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ) (j : ℕ) :
    Evec F₀ (j + 1) = fun _ _ => 0 := by
  rw [Evec, ite_eq_right (Nat.add_one_ne_zero j)]

theorem Qmap_zero (s : ℕ) (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ) (i : Fin 2) :
    Qmap s F₀ 0 i = dataL2 s (fun X z => F₀ X z i) := by
  rw [Qmap, ite_eq_left rfl]

theorem Qmap_succ (s : ℕ) (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ) (j : ℕ) (i : Fin 2) :
    Qmap s F₀ (j + 1) i = fun _ => 0 := by
  rw [Qmap, ite_eq_right (Nat.add_one_ne_zero j)]

theorem gchain_zero (s : ℕ) (f₀ : Vec 2 → Vec 2 → ℂ) (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ) :
    gchain s f₀ F₀ 0 = f₀ := by
  rw [gchain, ite_eq_left rfl]

theorem gchain_succ_eq (s : ℕ) (f₀ : Vec 2 → Vec 2 → ℂ) (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ)
    (j : ℕ) : gchain s f₀ F₀ (j + 1) = cleanupSource (Vchain s f₀ F₀) (j + 1) := by
  rw [gchain, ite_eq_right (Nat.add_one_ne_zero j)]

theorem gchain_succ (s : ℕ) (f₀ : Vec 2 → Vec 2 → ℂ) (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ) (j : ℕ) :
    gchain s f₀ F₀ (j + 1) = fun X z =>
      -∑ i : Fin 2, slowPartial i (Vcomp s f₀ F₀ j i) X z :=
  (gchain_succ_eq s f₀ F₀ j).trans rfl

/-- `Vchain 0 = F₀ + ∇_z φ_0`. -/
theorem Vchain_zero (s : ℕ) (f₀ : Vec 2 → Vec 2 → ℂ) (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ) :
    Vchain s f₀ F₀ 0 = fun X z k => F₀ X z k + gradPot s (Pchain s f₀ F₀ 0) X z k := by
  funext X z k
  show Evec F₀ 0 X z k + gradPot s (Pchain s f₀ F₀ 0) X z k = _
  rw [Evec_zero]

/-- `Vchain j = ∇_z φ_j` for `j ≥ 1`. -/
theorem Vchain_succ (s : ℕ) (f₀ : Vec 2 → Vec 2 → ℂ) (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ) (j : ℕ) :
    Vchain s f₀ F₀ (j + 1) = gradPot s (Pchain s f₀ F₀ (j + 1)) := by
  funext X z k
  show Evec F₀ (j + 1) X z k + gradPot s (Pchain s f₀ F₀ (j + 1)) X z k = _
  rw [Evec_succ]
  exact zero_add _
end

/-! The induction step of the cleanup chain. `ChainInv j` says:
- `Pchain j` is `C^{N-j}` into `ℓ²`;
- `Pchain j = -ω ĝ_j` coefficientwise;
- `g_j` is continuous, periodic and centered.

The step goes through the fields `V_j`: box smooth through `(N - j, q)`, periodic and centered,
with normalized coefficients `ω_k (V_j)ᵢ^_k = Rᵢ(X)_k`. Slow derivatives of `ℓ²` maps commute with
coefficients (`hasFDerivAt_coeffL2`). -/

section
/-- The chain invariant at step `j`. -/
def ChainInv (q N : ℕ) (f₀ : Vec 2 → Vec 2 → ℂ) (F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ) (j : ℕ) :
    Prop :=
  ContDiff ℝ ((N - j : ℕ) : ℕ∞) (Pchain (q + 1) f₀ F₀ j) ∧
  (∀ X k, Pchain (q + 1) f₀ F₀ j X k =
    -((omegaW (q + 1) k : ℂ) * smoothFourierCoeff (gchain (q + 1) f₀ F₀ j X) k)) ∧
  (∀ X, smoothFourierCoeff (gchain (q + 1) f₀ F₀ j X) 0 = 0) ∧
  (∀ X, Continuous (gchain (q + 1) f₀ F₀ j X)) ∧
  (∀ X, AVenhance.IsZ2Periodic (gchain (q + 1) f₀ F₀ j X))

section Step

variable {q N : ℕ} {f₀ : Vec 2 → Vec 2 → ℂ} {F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ}

theorem chainInv_zero (hf : IsBoxSmooth N (q + 1) f₀) (hfp : ∀ X, AVenhance.IsZ2Periodic (f₀ X))
    (hfm : ∀ X, fieldCellMean (f₀ X) = 0) : ChainInv q N f₀ F₀ 0 := by
  refine ⟨?_, fun X k => ?_, fun X => ?_, fun X => ?_, fun X => ?_⟩
  · show ContDiff ℝ ((N - 0 : ℕ) : ℕ∞) (fun X => -dataL2 (q + 1) f₀ X)
    rw [Nat.sub_zero]
    exact (contDiff_dataL2 hf).neg
  · rw [gchain_zero]
    show (-dataL2 (q + 1) f₀ X) k = _
    rw [lp.coeFn_neg, Pi.neg_apply, dataL2_apply hf.1 hfp]
  · rw [gchain_zero, smoothFourierCoeff_zero_eq_fieldCellMean]
    exact hfm X
  · rw [gchain_zero]
    exact (hf.1 X).continuous
  · rw [gchain_zero]
    exact hfp X

theorem component_isBoxSmooth (hF : IsBoxSmooth N (q + 1) F₀) (i : Fin 2) :
    IsBoxSmooth N (q + 1) (fun X z => F₀ X z i) :=
  hF.map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) i)

theorem Evec_isBoxSmooth (hF : IsBoxSmooth N (q + 1) F₀) {n : ℕ} (hn : n ≤ N) (j : ℕ) :
    IsBoxSmooth n q (Evec F₀ j) := by
  unfold Evec
  split_ifs
  · exact hF.mono hn (by omega)
  · exact IsBoxSmooth.zero

theorem Evec_periodic (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X)) (j : ℕ) (X : Vec 2) :
    AVenhance.IsZ2Periodic (Evec F₀ j X) := by
  unfold Evec
  split_ifs
  · exact hFp X
  · exact fun _ _ => rfl

/-- Coefficient facts for a component of the added flux. -/
theorem Evec_comp (hF : IsBoxSmooth N (q + 1) F₀) (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0) (j : ℕ) (X : Vec 2)
    (i : Fin 2) :
    Continuous (fun z => Evec F₀ j X z i) ∧
    (∀ k, (omegaW (q + 1) k : ℂ) * smoothFourierCoeff (fun z => Evec F₀ j X z i) k =
      Qmap (q + 1) F₀ j i X k) ∧
    smoothFourierCoeff (fun z => Evec F₀ j X z i) 0 = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Evec_zero, Qmap_zero]
    refine ⟨(continuous_apply i).comp (hF.1 X).continuous, fun k => ?_, ?_⟩
    · rw [dataL2_apply (component_isBoxSmooth hF i).1
        (fun X n z => congrFun (hFp X n z) i) X k]
    · rw [smoothFourierCoeff_zero_eq_fieldCellMean]
      exact hFm X i
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Evec_succ, Qmap_succ]
    have h0 : ∀ k, smoothFourierCoeff (fun _ : Vec 2 => (0 : ℂ)) k = 0 := fun k => by
      simp [smoothFourierCoeff]
    refine ⟨continuous_const, fun k => ?_, h0 0⟩
    show (omegaW (q + 1) k : ℂ) * smoothFourierCoeff (fun _ : Vec 2 => (0 : ℂ)) k =
      (0 : FreqL2) k
    rw [h0 k, mul_zero, lp.coeFn_zero, Pi.zero_apply]

/-- The chain field `V_j` is box smooth through `(N - j, q)`. -/
theorem Vchain_isBoxSmooth (hF : IsBoxSmooth N (q + 1) F₀) {j : ℕ}
    (hinv : ChainInv q N f₀ F₀ j) : IsBoxSmooth (N - j) q (Vchain (q + 1) f₀ F₀ j) :=
  (Evec_isBoxSmooth hF (Nat.sub_le N j) j).add (gradPot_isBoxSmooth hinv.1)

theorem Vchain_periodic (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X)) (j : ℕ) (X : Vec 2) :
    AVenhance.IsZ2Periodic (Vchain (q + 1) f₀ F₀ j X) := by
  intro n z
  simp only [Vchain]
  rw [Evec_periodic hFp j X n z, gradPot_periodic _ _ X n z]

/-- Coefficient facts for a component of `V_j`. -/
theorem Vcomp_coeff (hq : 1 ≤ q) (hF : IsBoxSmooth N (q + 1) F₀)
    (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0) (j : ℕ) (X : Vec 2)
    (i : Fin 2) :
    (∀ k, (omegaW (q + 1) k : ℂ) * smoothFourierCoeff (Vcomp (q + 1) f₀ F₀ j i X) k =
      Rmap (q + 1) F₀ j (Pchain (q + 1) f₀ F₀ j) i X k) ∧
    smoothFourierCoeff (Vcomp (q + 1) f₀ F₀ j i X) 0 = 0 := by
  obtain ⟨hEc, hEk, hE0⟩ := Evec_comp hF hFp hFm j X i
  have hGc : Continuous (gradComp (q + 1) (Pchain (q + 1) f₀ F₀ j) X i) :=
    (gradComp_contDiff (Pchain (q + 1) f₀ F₀ j) X i).continuous
  have e : Vcomp (q + 1) f₀ F₀ j i X =
      fun z => Evec F₀ j X z i + gradComp (q + 1) (Pchain (q + 1) f₀ F₀ j) X i z := rfl
  refine ⟨fun k => ?_, ?_⟩
  · rw [e, smoothFourierCoeff_add hEc hGc k, mul_add, hEk k,
      omega_mul_coeff_gradComp (q + 1) _ X (by omega) i k, Rmap, lp.coeFn_add, Pi.add_apply]
  · rw [e, smoothFourierCoeff_add hEc hGc 0, hE0,
      smoothFourierCoeff_gradComp_zero (q + 1) _ X (by omega) i, add_zero]

theorem Qmap_contDiff (hF : IsBoxSmooth N (q + 1) F₀) {n : ℕ} (hn : n ≤ N) (j : ℕ) (i : Fin 2) :
    ContDiff ℝ (n : ℕ∞) (Qmap (q + 1) F₀ j i) := by
  unfold Qmap
  split_ifs
  · exact (contDiff_dataL2 (component_isBoxSmooth hF i)).of_le (by exact_mod_cast hn)
  · exact contDiff_const

theorem cleanupSource_comp_periodic (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X)) (j : ℕ)
    (i : Fin 2) (X : Vec 2) :
    AVenhance.IsZ2Periodic (slowPartial i (Vcomp (q + 1) f₀ F₀ j i) X) := by
  intro n z
  simp only [slowPartial]
  have e : (fun X' => Vcomp (q + 1) f₀ F₀ j i X' (z + AVenhance.latticeShift n)) =
      fun X' => Vcomp (q + 1) f₀ F₀ j i X' z := by
    funext X'
    exact congrFun (Vchain_periodic hFp j X' n z) i
  rw [e]

/-- **The induction step.** -/
theorem chainInv_succ (hq : 1 ≤ q) (hF : IsBoxSmooth N (q + 1) F₀)
    (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0) {j : ℕ} (hj : j + 1 ≤ N)
    (hinv : ChainInv q N f₀ F₀ j) : ChainInv q N f₀ F₀ (j + 1) := by
  have hVbox := Vchain_isBoxSmooth hF hinv
  obtain ⟨hP, -, -, -, -⟩ := hinv
  obtain ⟨n, hn⟩ : ∃ n, N - j = n + 1 := ⟨N - j - 1, by omega⟩
  have hNn : N - (j + 1) = n := by omega
  rw [hn] at hP hVbox
  -- the components of `V_j`
  have hhs : ∀ i : Fin 2, IsSlowSmooth (n + 1) (Vcomp (q + 1) f₀ F₀ j i) := fun i =>
    hVbox.isSlowSmooth.component i
  have hhc : ∀ (i : Fin 2) X, Continuous (Vcomp (q + 1) f₀ F₀ j i X) := fun i X =>
    (hhs i).continuous_fast X
  have hspc : ∀ (i i' : Fin 2) X, Continuous (slowPartial i' (Vcomp (q + 1) f₀ F₀ j i) X) :=
    fun i i' X => ((hhs i).slowPartial i').continuous_fast X
  have hC := fun X i => Vcomp_coeff (f₀ := f₀) hq hF hFp hFm j X i
  -- the normalized coefficients of `V_j`
  have hR : ∀ i : Fin 2,
      ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (Rmap (q + 1) F₀ j (Pchain (q + 1) f₀ F₀ j) i) := fun i =>
    (Qmap_contDiff hF (by omega) j i).add ((mulCLM (q + 1) i).contDiff.comp hP)
  have hRd : ∀ (i : Fin 2) X,
      DifferentiableAt ℝ (Rmap (q + 1) F₀ j (Pchain (q + 1) f₀ F₀ j) i) X := fun i X =>
    (hR i).differentiable (natCast_succ_ne_zero n) X
  -- slow derivatives of the coefficients
  have hslow : ∀ (i : Fin 2) X k,
      fderiv ℝ (Rmap (q + 1) F₀ j (Pchain (q + 1) f₀ F₀ j) i) X (basisVec i) k =
        (omegaW (q + 1) k : ℂ) *
          smoothFourierCoeff (slowPartial i (Vcomp (q + 1) f₀ F₀ j i) X) k := by
    intro i X k
    have hRk : (fun X => Rmap (q + 1) F₀ j (Pchain (q + 1) f₀ F₀ j) i X k) =
        fun X => (omegaW (q + 1) k : ℂ) * coeffL2 (Vcomp (q + 1) f₀ F₀ j i X) k := by
      funext X'
      rw [coeffL2_apply (hhc i X'), (hC X' i).1 k]
    have hD := hasFDerivAt_coeffL2 (hhs i) X
    have hfc : Continuous fun z => fderiv ℝ (fun X' => Vcomp (q + 1) f₀ F₀ j i X' z) X
        (basisVec i) := hspc i i X
    rw [← fderiv_apply_freq (hRd i X), hRk,
      fderiv_const_mul (differentiableAt_apply_freq hD.differentiableAt k),
      _root_.smul_apply, smul_eq_mul, fderiv_apply_freq hD.differentiableAt,
      hD.fderiv, slowDerivL2_apply (hspc i), coeffL2_apply hfc]
    rfl
  have hsp0 : ∀ (i : Fin 2) X,
      smoothFourierCoeff (slowPartial i (Vcomp (q + 1) f₀ F₀ j i) X) 0 = 0 := by
    intro i X
    have hD := hasFDerivAt_coeffL2 (hhs i) X
    have hz : (fun X => coeffL2 (Vcomp (q + 1) f₀ F₀ j i X) 0) = fun _ => 0 := by
      funext X'
      rw [coeffL2_apply (hhc i X'), (hC X' i).2]
    rw [← coeffL2_apply (hspc i i X)]
    show coeffL2 (fun z => fderiv ℝ (fun X' => Vcomp (q + 1) f₀ F₀ j i X' z) X (basisVec i)) 0 = 0
    rw [← slowDerivL2_apply (hspc i), ← hD.fderiv, ← fderiv_apply_freq hD.differentiableAt, hz]
    simp
  have hgcoef : ∀ X k, smoothFourierCoeff (gchain (q + 1) f₀ F₀ (j + 1) X) k =
      -(smoothFourierCoeff (slowPartial 0 (Vcomp (q + 1) f₀ F₀ j 0) X) k +
        smoothFourierCoeff (slowPartial 1 (Vcomp (q + 1) f₀ F₀ j 1) X) k) := by
    intro X k
    rw [gchain_succ]
    simp only [Fin.sum_univ_two]
    exact smoothFourierCoeff_neg_add (hspc 0 0 X) (hspc 1 1 X) k
  refine ⟨?_, fun X k => ?_, fun X => ?_, fun X => ?_, fun X => ?_⟩
  · rw [hNn]
    show ContDiff ℝ (n : ℕ∞) (fun X => ∑ i : Fin 2,
      fderiv ℝ (Rmap (q + 1) F₀ j (Pchain (q + 1) f₀ F₀ j) i) X (basisVec i))
    exact ContDiff.sum fun i _ => ((hR i).fderiv_right (m := (n : ℕ∞))
      (by exact_mod_cast le_rfl)).clm_apply contDiff_const
  · rw [hgcoef X k]
    show (∑ i : Fin 2, fderiv ℝ (Rmap (q + 1) F₀ j (Pchain (q + 1) f₀ F₀ j) i) X
      (basisVec i)) k = _
    rw [Fin.sum_univ_two, lp.coeFn_add, Pi.add_apply, hslow 0 X k, hslow 1 X k]
    ring
  · rw [hgcoef X 0, hsp0 0 X, hsp0 1 X]
    simp
  · rw [gchain_succ]
    exact (continuous_finsetSum _ fun i _ => hspc i i X).fun_neg
  · rw [gchain_succ]
    intro m z
    show -∑ i : Fin 2, slowPartial i (Vcomp (q + 1) f₀ F₀ j i) X
        (z + AVenhance.latticeShift m) =
      -∑ i : Fin 2, slowPartial i (Vcomp (q + 1) f₀ F₀ j i) X z
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact cleanupSource_comp_periodic hFp j i X m z

end Step
end

end AVRegularity.CleanupChain
end

section
open MeasureTheory Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CleanupChain

/-! The cleanup chain for scalar complex data. The invariant holds at every step `j ≤ N`. Each
`V_j = ∇_z φ_j` (with `F₀` added at `j = 0`) is a cell antidivergence of the source `g_j` at slow
order `sX`, provided `sX + j ≤ N = sX + A`. -/

section Scalar

variable {q N : ℕ} {f₀ : Vec 2 → Vec 2 → ℂ} {F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ}

theorem chainInv_all (hq : 1 ≤ q) (hf : IsBoxSmooth N (q + 1) f₀)
    (hfp : ∀ X, AVenhance.IsZ2Periodic (f₀ X)) (hfm : ∀ X, fieldCellMean (f₀ X) = 0)
    (hF : IsBoxSmooth N (q + 1) F₀) (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0) :
    ∀ j, j ≤ N → ChainInv q N f₀ F₀ j := by
  intro j
  induction j with
  | zero => exact fun _ => chainInv_zero hf hfp hfm
  | succ j ih => exact fun hj => chainInv_succ hq hF hFp hFm hj (ih (by omega))

/-- At step `j`, `∇_z φ_j` is a cell antidivergence of `g_j` at slow order `sX` if
`sX + j ≤ N`. -/
theorem isCellAntidivergence_of_chainInv (hq : 1 ≤ q) {sX j : ℕ} (hjN : sX + j ≤ N)
    (hinv : ChainInv q N f₀ F₀ j) :
    IsCellAntidivergence sX q (gchain (q + 1) f₀ F₀ j)
      (gradPot (q + 1) (Pchain (q + 1) f₀ F₀ j)) := by
  obtain ⟨hP, hPg, hg0, hgc, hgp⟩ := hinv
  have hP' : ContDiff ℝ (sX : ℕ∞) (Pchain (q + 1) f₀ F₀ j) :=
    hP.of_le (by exact_mod_cast (by omega : sX ≤ N - j))
  exact ⟨gradPot_isBoxSmooth hP', fun X => gradPot_periodic _ _ X,
    potential (q + 1) (Pchain (q + 1) f₀ F₀ j), potential_isBoxSmooth hP',
    fun X => potential_periodic _ _ X, fun X => potential_mean _ _ X, fun _ _ _ => rfl,
    fun X z => div_gradPot hq _ X (hgc X) (hgp X) (hPg X) (hg0 X) z⟩

end Scalar

/-- **The scalar cleanup chain.** For centered periodic scalar data, box smooth through
`(sX + A, sZ + 1)` with `1 ≤ sZ`, the chain `Vchain` is a cleanup chain. Every `V_j` with
`j < A` is box smooth of slow order `sX + 1`. -/
theorem scalar_cleanup_chain {sX sZ A : ℕ} (hsZ : 1 ≤ sZ) {f₀ : Vec 2 → Vec 2 → ℂ}
    {F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ} (hf : IsBoxSmooth (sX + A) (sZ + 1) f₀)
    (hfp : ∀ X, AVenhance.IsZ2Periodic (f₀ X)) (hfm : ∀ X, fieldCellMean (f₀ X) = 0)
    (hF : IsBoxSmooth (sX + A) (sZ + 1) F₀) (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0) :
    IsCleanupChain sX sZ A f₀ F₀ (Vchain (sZ + 1) f₀ F₀) ∧
      ∀ j, j < A → IsBoxSmooth (sX + 1) sZ (Vchain (sZ + 1) f₀ F₀ j) := by
  have hinv := chainInv_all hsZ hf hfp hfm hF hFp hFm
  refine ⟨⟨⟨gradPot (sZ + 1) (Pchain (sZ + 1) f₀ F₀ 0), ?_, Vchain_zero _ _ _⟩, ?_⟩, ?_⟩
  · have h := isCellAntidivergence_of_chainInv (sX := sX) hsZ (by omega) (hinv 0 (by omega))
    rwa [gchain_zero] at h
  · intro j hj1 hjA
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h := isCellAntidivergence_of_chainInv (sX := sX) hsZ (by omega)
      (hinv (j' + 1) (by omega))
    rw [Vchain_succ]
    rwa [gchain_succ_eq] at h
  · intro j hjA
    exact (Vchain_isBoxSmooth hF (hinv j (by omega))).mono (by omega) le_rfl

end AVRegularity.CleanupChain
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CleanupChain

/-! **Existence of the cleanup chain** for data in a finite-dimensional real inner product space
`E`. Expand in an orthonormal basis `(b_ι)`. Each component `⟪b_ι, ·⟫` (as complex scalar data)
gets the scalar chain. Reassemble with `w ↦ (Re w) b_ι`. Sums and continuous linear images of
cell antidivergences are cell antidivergences. The cleanup source commutes with the reassembly
because the scalar chains are slow-differentiable at every member used by a source. -/

/-- **The cleanup chain exists** for centered periodic data box smooth through `(sX + A, sZ + 1)`, `1 ≤ sZ`. -/
theorem exists_isCleanupChain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (sX sZ A : ℕ) (hsZ : 1 ≤ sZ)
    (f₀ : Vec 2 → Vec 2 → E) (F₀ : Vec 2 → Vec 2 → Fin 2 → E)
    (hf : IsBoxSmooth (sX + A) (sZ + 1) f₀) (hfp : ∀ X, AVenhance.IsZ2Periodic (f₀ X))
    (hfm : ∀ X, fieldCellMean (f₀ X) = 0)
    (hF : IsBoxSmooth (sX + A) (sZ + 1) F₀) (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0) :
    ∃ V : ℕ → Vec 2 → Vec 2 → Fin 2 → E, IsCleanupChain sX sZ A f₀ F₀ V := by
  set b := stdOrthonormalBasis ℝ E
  let L : Fin (Module.finrank ℝ E) → E →L[ℝ] ℂ := fun ι =>
    Complex.ofRealCLM.comp (innerSL ℝ (b ι))
  let M : Fin (Module.finrank ℝ E) → ℂ →L[ℝ] E := fun ι => Complex.reCLM.smulRight (b ι)
  have hML : ∀ e : E, ∑ ι, M ι (L ι e) = e := by
    intro e
    conv_rhs => rw [← b.sum_repr' e]
    refine Finset.sum_congr rfl fun ι _ => ?_
    show Complex.reCLM (Complex.ofRealCLM (innerSL ℝ (b ι) e)) • b ι = inner ℝ (b ι) e • b ι
    rw [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.ofReal_re, innerSL_apply_apply]
  -- the scalar data
  let fs : Fin (Module.finrank ℝ E) → Vec 2 → Vec 2 → ℂ := fun ι X z => L ι (f₀ X z)
  let Fs : Fin (Module.finrank ℝ E) → Vec 2 → Vec 2 → Fin 2 → ℂ := fun ι X z k => L ι (F₀ X z k)
  have hfs : ∀ ι, IsBoxSmooth (sX + A) (sZ + 1) (fs ι) := fun ι => hf.map_clm (L ι)
  have hFs : ∀ ι, IsBoxSmooth (sX + A) (sZ + 1) (Fs ι) := fun ι =>
    hF.map_clm (ContinuousLinearMap.pi fun k =>
      (L ι).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k))
  have hfsp : ∀ ι X, AVenhance.IsZ2Periodic (fs ι X) := fun ι X n z => by
    show L ι (f₀ X (z + AVenhance.latticeShift n)) = L ι (f₀ X z)
    rw [hfp X n z]
  have hFsp : ∀ ι X, AVenhance.IsZ2Periodic (Fs ι X) := fun ι X n z => by
    funext k
    show L ι (F₀ X (z + AVenhance.latticeShift n) k) = L ι (F₀ X z k)
    rw [hFp X n z]
  have hfsm : ∀ ι X, fieldCellMean (fs ι X) = 0 := fun ι X => by
    show ∫ z in AVenhance.unitCube, L ι (f₀ X z) = 0
    have h0 : ∫ z in AVenhance.unitCube, f₀ X z = 0 := hfm X
    rw [(L ι).integral_comp_comm (integrableOn_unitCube (hf.1 X).continuous), h0, map_zero]
  have hFsm : ∀ ι X (k : Fin 2), fieldCellMean (fun z => Fs ι X z k) = 0 := fun ι X k => by
    show ∫ z in AVenhance.unitCube, L ι (F₀ X z k) = 0
    have hc : Continuous fun z => F₀ X z k := (continuous_apply k).comp (hF.1 X).continuous
    have h0 : ∫ z in AVenhance.unitCube, F₀ X z k = 0 := hFm X k
    rw [(L ι).integral_comp_comm (integrableOn_unitCube hc), h0, map_zero]
  -- the scalar chains
  have hsc := fun ι => scalar_cleanup_chain hsZ (hfs ι) (hfsp ι) (hfsm ι) (hFs ι) (hFsp ι)
    (hFsm ι)
  let Vs : Fin (Module.finrank ℝ E) → ℕ → Vec 2 → Vec 2 → Fin 2 → ℂ := fun ι =>
    Vchain (sZ + 1) (fs ι) (Fs ι)
  choose W hW hV0 using fun ι => (hsc ι).1.1
  refine ⟨fun j X z k => ∑ ι, M ι (Vs ι j X z k), ⟨fun X z k => ∑ ι, M ι (W ι X z k), ?_, ?_⟩,
    fun j hj1 hjA => ?_⟩
  · have h := isCellAntidivergence_sum Finset.univ hsZ
      (f := fun ι X z => M ι (fs ι X z)) (V := fun ι X z k => M ι (W ι X z k))
      fun ι _ => (hW ι).clm_comp hsZ (M ι)
    beta_reduce at h
    have e : (fun X z => ∑ ι, M ι (fs ι X z)) = f₀ := by
      funext X z
      exact hML (f₀ X z)
    rwa [e] at h
  · funext X z k
    show ∑ ι, M ι (Vs ι 0 X z k) = F₀ X z k + ∑ ι, M ι (W ι X z k)
    have h0 : ∀ ι, Vs ι 0 X z k = Fs ι X z k + W ι X z k := fun ι =>
      congrFun (congrFun (congrFun (hV0 ι) X) z) k
    simp only [h0, map_add, Finset.sum_add_distrib]
    rw [show ∑ ι, M ι (Fs ι X z k) = F₀ X z k from hML (F₀ X z k)]
  · have h := isCellAntidivergence_sum Finset.univ hsZ
      (f := fun ι X z => M ι (cleanupSource (Vs ι) j X z))
      (V := fun ι X z k => M ι (Vs ι j X z k))
      fun ι _ => ((hsc ι).1.2 j hj1 hjA).clm_comp hsZ (M ι)
    have hd : ∀ ι X z (k : Fin 2), DifferentiableAt ℝ (fun X' => Vs ι (j - 1) X' z k) X :=
      fun ι X z k => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) k).contDiff.comp
        (((hsc ι).2 (j - 1) (by omega)).contDiff_slow z)).differentiable
        (by exact_mod_cast Nat.succ_ne_zero sX) X
    have e : cleanupSource (fun j X z k => ∑ ι, M ι (Vs ι j X z k)) j =
        fun X z => ∑ ι, M ι (cleanupSource (Vs ι) j X z) := by
      funext X z
      simp only [cleanupSource, slowPartial]
      have h1 : ∀ k : Fin 2,
          fderiv ℝ (fun X' => ∑ ι, M ι (Vs ι (j - 1) X' z k)) X (basisVec k) =
            ∑ ι, M ι (fderiv ℝ (fun X' => Vs ι (j - 1) X' z k) X (basisVec k)) := by
        intro k
        have hs := HasFDerivAt.fun_sum (u := Finset.univ)
          (A := fun ι X' => M ι (Vs ι (j - 1) X' z k))
          (A' := fun ι => (M ι).comp (fderiv ℝ (fun X' => Vs ι (j - 1) X' z k) X))
          fun ι _ => (M ι).hasFDerivAt.comp X (hd ι X z k).hasFDerivAt
        beta_reduce at hs
        simp only [hs.fderiv, _root_.sum_apply, ContinuousLinearMap.comp_apply]
      simp only [h1, map_neg, map_sum, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
    rw [e]
    exact h

end AVRegularity.CleanupChain
end
