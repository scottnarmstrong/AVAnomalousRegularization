-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
public import AVRegularity.CycleComparison.Residual.MixedTail.Energy
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
import AVRegularity.CycleComparison.Residual.BoundPointwise
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

section
@[expose] public section
namespace AVRegularity.CoarseFluxDiff

/-! Differentiated coarse flux: the real inequality closing the bound. -/

theorem sqrt_add_le_add_sqrt' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
  nlinarith

theorem sqrt_sq_mul {x y : ℝ} (hx : 0 ≤ x) : Real.sqrt (x ^ 2 * y) = x * Real.sqrt y := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hx]

/-- The combination of the flux and scalar bounds. -/
theorem final_real {ν B ρ e ℓ εc L C₀ Θh N cf cr indr c1 : ℝ} {A : ℕ} (hν : 0 < ν) (hB : 0 < B)
    (hρ : 0 < ρ) (he : 0 < e) (hℓ : ℓ = e / Real.sqrt ν) (hε : εc = ℓ * Real.sqrt B / ρ)
    (hC₀ : 0 ≤ C₀) (hΘ : 0 ≤ Θh) (hN : 0 ≤ N) (hcf : 0 ≤ cf)
    (hc1 : 0 ≤ c1) (hind : indr = 0 ∨ indr = 1) :
    (Real.sqrt ν)⁻¹ * Real.sqrt (c1 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf) +
        Real.sqrt (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cr) * Real.sqrt L ≤
      max (Real.sqrt c1) (max (C₀ * Real.sqrt (2 * N * cf)) (C₀ * Real.sqrt (N * cr))) *
        (indr * Real.sqrt (B / ν) + Θh * εc ^ 2 * (1 + Real.sqrt L / ℓ * (e / ρ) ^ A)) *
          (Real.sqrt B)⁻¹ := by
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hℓpos : 0 < ℓ := by rw [hℓ]; positivity
  have hεpos : 0 < εc := by rw [hε]; positivity
  have hϑ : 0 < e / ρ := by positivity
  set M := max (Real.sqrt c1) (max (C₀ * Real.sqrt (2 * N * cf)) (C₀ * Real.sqrt (N * cr))) with hM
  have hM1 : Real.sqrt c1 ≤ M := le_max_left _ _
  have hM2 : C₀ * Real.sqrt (2 * N * cf) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM3 : C₀ * Real.sqrt (N * cr) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans hM1
  have hθ : 0 ≤ C₀ * Θh := mul_nonneg hC₀ hΘ
  -- identities
  have hI1 : (Real.sqrt ν)⁻¹ * (e / ρ) = εc / Real.sqrt B := by
    rw [hε, hℓ]; field_simp
  have hI2 : ℓ * Real.sqrt B = ρ * εc := by
    rw [hε]; field_simp
  have hI3 : (Real.sqrt ν)⁻¹ = Real.sqrt (B / ν) / Real.sqrt B := by
    rw [Real.sqrt_div hB.le]; field_simp
  -- the flux part
  have hK1 : Real.sqrt (c1 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf) ≤
      Real.sqrt c1 * indr + (e / ρ) * εc * (C₀ * Θh) * Real.sqrt (2 * N * cf) := by
    have e1 : c1 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf =
        c1 * indr + ((e / ρ) * εc * (C₀ * Θh)) ^ 2 * (2 * N * cf) := by ring
    rw [e1]
    have hind0 : 0 ≤ c1 * indr := by rcases hind with h | h <;> simp [h, hc1]
    refine (sqrt_add_le_add_sqrt' hind0 (by positivity)).trans ?_
    rw [sqrt_sq_mul (by positivity)]
    refine add_le_add (le_of_eq ?_) le_rfl
    rcases hind with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hflux : (Real.sqrt ν)⁻¹ *
      Real.sqrt (c1 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf) ≤
      M * (indr * Real.sqrt (B / ν) + Θh * εc ^ 2) * (Real.sqrt B)⁻¹ := by
    have hind' : 0 ≤ indr := by rcases hind with h | h <;> simp [h]
    calc (Real.sqrt ν)⁻¹ * Real.sqrt (c1 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf)
        ≤ (Real.sqrt ν)⁻¹ * (Real.sqrt c1 * indr + (e / ρ) * εc * (C₀ * Θh) *
            Real.sqrt (2 * N * cf)) := by gcongr
      _ = Real.sqrt c1 * indr * (Real.sqrt (B / ν) / Real.sqrt B) +
          (εc / Real.sqrt B) * εc * (C₀ * Θh) * Real.sqrt (2 * N * cf) := by
          rw [← hI3, ← hI1]; ring
      _ = (Real.sqrt c1 * (indr * Real.sqrt (B / ν)) + (C₀ * Real.sqrt (2 * N * cf)) *
            (Θh * εc ^ 2)) * (Real.sqrt B)⁻¹ := by ring
      _ ≤ (M * (indr * Real.sqrt (B / ν)) + M * (Θh * εc ^ 2)) * (Real.sqrt B)⁻¹ := by
          gcongr
      _ = _ := by ring
  -- the scalar part
  have hK2 : Real.sqrt (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cr) =
      ρ⁻¹ * (e / ρ) ^ A * εc * (C₀ * Θh) * Real.sqrt (N * cr) := by
    have e1 : N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cr =
        (ρ⁻¹ * (e / ρ) ^ A * εc * (C₀ * Θh)) ^ 2 * (N * cr) := by ring
    rw [e1, sqrt_sq_mul (by positivity)]
  have hscal : Real.sqrt (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cr) *
      Real.sqrt L ≤ M * (Θh * εc ^ 2 * (Real.sqrt L / ℓ * (e / ρ) ^ A)) * (Real.sqrt B)⁻¹ := by
    rw [hK2]
    have hq : Θh * εc ^ 2 * (Real.sqrt L / ℓ * (e / ρ) ^ A) * (Real.sqrt B)⁻¹ =
        ρ⁻¹ * (e / ρ) ^ A * εc * Θh * Real.sqrt L := by
      have : ℓ * Real.sqrt B = ρ * εc := hI2
      field_simp
      have e2 : Θh * Real.sqrt L * ℓ * Real.sqrt B = Θh * Real.sqrt L * (ℓ * Real.sqrt B) := by ring
      rw [e2, this]
      ring
    calc ρ⁻¹ * (e / ρ) ^ A * εc * (C₀ * Θh) * Real.sqrt (N * cr) * Real.sqrt L
        = (C₀ * Real.sqrt (N * cr)) * (ρ⁻¹ * (e / ρ) ^ A * εc * Θh * Real.sqrt L) := by ring
      _ ≤ M * (ρ⁻¹ * (e / ρ) ^ A * εc * Θh * Real.sqrt L) := by gcongr
      _ = M * (Θh * εc ^ 2 * (Real.sqrt L / ℓ * (e / ρ) ^ A)) * (Real.sqrt B)⁻¹ := by
          rw [mul_assoc M, hq]
  calc _ ≤ M * (indr * Real.sqrt (B / ν) + Θh * εc ^ 2) * (Real.sqrt B)⁻¹ +
        M * (Θh * εc ^ 2 * (Real.sqrt L / ℓ * (e / ρ) ^ A)) * (Real.sqrt B)⁻¹ :=
        add_le_add hflux hscal
    _ = _ := by ring

end AVRegularity.CoarseFluxDiff
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CoarseFluxDiff

/-! Coarse flux bound: elementary squared-norm inequalities in `ℝ≥0∞` for finite weighted
combinations. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ennreal_sq_sum_le_card_mul_sum_sq (Finset.range 2) (fun i => if i = 0 then a else b)
  simpa [Finset.sum_range_succ] using h

/-- The squared norm of a weighted finite combination. -/
theorem enorm_sq_sum_smul_le (S : Finset ℕ) (c : ℝ) (d : ℕ → ℝ) (s : ℕ → E) :
    ‖c • ∑ n ∈ S, d n • s n‖ₑ ^ 2 ≤
      ∑ n ∈ S, ENNReal.ofReal (S.card * c ^ 2 * (d n) ^ 2) * ‖s n‖ₑ ^ 2 := by
  have h1 : ‖c • ∑ n ∈ S, d n • s n‖ₑ ≤ ∑ n ∈ S, ‖c * d n‖ₑ * ‖s n‖ₑ := by
    rw [enorm_smul]
    calc ‖c‖ₑ * ‖∑ n ∈ S, d n • s n‖ₑ ≤ ‖c‖ₑ * ∑ n ∈ S, ‖d n • s n‖ₑ := by
          gcongr; exact enorm_sum_le _ _
      _ = ∑ n ∈ S, ‖c * d n‖ₑ * ‖s n‖ₑ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [enorm_smul, enorm_mul, mul_assoc]
  calc ‖c • ∑ n ∈ S, d n • s n‖ₑ ^ 2 ≤ (∑ n ∈ S, ‖c * d n‖ₑ * ‖s n‖ₑ) ^ 2 := by gcongr
    _ ≤ (S.card : ℝ≥0∞) * ∑ n ∈ S, (‖c * d n‖ₑ * ‖s n‖ₑ) ^ 2 := by
        simpa using ennreal_sq_sum_le_card_mul_sum_sq S (fun n => ‖c * d n‖ₑ * ‖s n‖ₑ)
    _ = ∑ n ∈ S, ENNReal.ofReal (S.card * c ^ 2 * (d n) ^ 2) * ‖s n‖ₑ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        have e1 : ‖c * d n‖ₑ ^ 2 = ENNReal.ofReal ((c * d n) ^ 2) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
        have e2 : ENNReal.ofReal (S.card * c ^ 2 * (d n) ^ 2) =
            (S.card : ℝ≥0∞) * ENNReal.ofReal ((c * d n) ^ 2) := by
          rw [show (S.card : ℝ) * c ^ 2 * (d n) ^ 2 = S.card * (c * d n) ^ 2 by ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        rw [e2, mul_pow, e1]
        ring

/-- The squared norm of a term plus a weighted finite combination. -/
theorem enorm_sq_add_sum_smul_le (S : Finset ℕ) (a : E) (c : ℝ) (d : ℕ → ℝ) (s : ℕ → E) :
    ‖a + c • ∑ n ∈ S, d n • s n‖ₑ ^ 2 ≤
      2 * ‖a‖ₑ ^ 2 + ∑ n ∈ S, ENNReal.ofReal (2 * S.card * c ^ 2 * (d n) ^ 2) * ‖s n‖ₑ ^ 2 := by
  calc ‖a + c • ∑ n ∈ S, d n • s n‖ₑ ^ 2
      ≤ (‖a‖ₑ + ‖c • ∑ n ∈ S, d n • s n‖ₑ) ^ 2 := by gcongr; exact enorm_add_le _ _
    _ ≤ 2 * (‖a‖ₑ ^ 2 + ‖c • ∑ n ∈ S, d n • s n‖ₑ ^ 2) := add_sq_le _ _
    _ ≤ 2 * (‖a‖ₑ ^ 2 + ∑ n ∈ S, ENNReal.ofReal (S.card * c ^ 2 * (d n) ^ 2) * ‖s n‖ₑ ^ 2) := by
        gcongr; exact enorm_sq_sum_smul_le S c d s
    _ = _ := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 2
        ring

end AVRegularity.CoarseFluxDiff
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoarseFluxDiff

/-! Coarse flux bound: the factorial-norm analogues of the slow-cell jet bounds.  A positive slow
jet of the dilated field on the slow cell is controlled by the classical factorial norm. -/

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The zeroth term of the factorial norm. -/
theorem lintegral_sq_le_classicalFactorialSq (ρ : ℝ) (m : ℕ) (g : Vec 2 → F) :
    ∫⁻ x in AVenhance.unitCube, ‖g x‖ₑ ^ 2 ≤ classicalFactorialSq ρ m g := by
  unfold classicalFactorialSq
  refine le_trans ?_ (Finset.single_le_sum (f := fun j => ENNReal.ofReal (ρ ^ (2 * j) /
    ((j.factorial : ℝ)) ^ 2) * ∑ w : DerivativeWord2 j,
      ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2) (fun _ _ => bot_le)
    (Finset.mem_range.2 (Nat.succ_pos m)))
  simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, div_one,
    ENNReal.ofReal_one, one_mul]
  refine le_of_eq ?_
  rw [Finset.sum_eq_single (fun i => (Fin.elim0 i : Fin 2))]
  · rw [orderedDerivative_zero]
  · intro w _ hw; exact absurd (Subsingleton.elim _ _) hw
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The full derivative of order `j` is controlled by the factorial norm. -/
theorem lintegral_iteratedFDeriv_sq_le_classicalFactorialSq (m j : ℕ) (hjm : j ≤ m)
    {g : Vec 2 → F} (hg : ContDiff ℝ (m : ℕ∞) g) {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (ρ ^ (2 * j)) * ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ j g x‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 ^ j * ((j.factorial : ℝ)) ^ 2) * classicalFactorialSq ρ m g := by
  have hjm' : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
  have hg' : ContDiff ℝ (j : ℕ∞) g := hg.of_le (by exact_mod_cast hjm)
  have h1 := lintegral_iteratedFDeriv_sq_le_words hg'
  have h2 : ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∑ w : DerivativeWord2 j, ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2 ≤
      classicalFactorialSq ρ m g :=
    Finset.single_le_sum (f := fun j => ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∑ w : DerivativeWord2 j, ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2)
      (fun _ _ => bot_le) hjm'
  have hfac : (0 : ℝ) < ((j.factorial : ℝ)) ^ 2 := by positivity
  have hcoef : ρ ^ (2 * j) * 2 ^ j =
      (2 ^ j * ((j.factorial : ℝ)) ^ 2) * (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) := by
    field_simp
  calc ENNReal.ofReal (ρ ^ (2 * j)) * ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ j g x‖ₑ ^ 2
      ≤ ENNReal.ofReal (ρ ^ (2 * j)) * (ENNReal.ofReal (2 ^ j) *
          ∑ w : DerivativeWord2 j,
            ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2) := by gcongr
    _ = ENNReal.ofReal ((2 ^ j * ((j.factorial : ℝ)) ^ 2) *
          (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2)) *
          ∑ w : DerivativeWord2 j,
            ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← hcoef]
    _ = ENNReal.ofReal (2 ^ j * ((j.factorial : ℝ)) ^ 2) *
          (ENNReal.ofReal (ρ ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
          ∑ w : DerivativeWord2 j,
            ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w g x‖ₑ ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ _ := by gcongr

/-- A slow jet of the dilated field on the slow cell is controlled by the factorial norm. -/
theorem lintegral_slowCell_dilate_le_classicalFactorialSq (m j : ℕ) (hjm : j ≤ m)
    {g : Vec 2 → F} (hg : ContDiff ℝ (m : ℕ∞) g) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ X in slowCell ρ, ‖iteratedFDeriv ℝ j (fun X' => g (ρ • X')) X‖ₑ ^ 2
      ≤ ENNReal.ofReal (ρ⁻¹ ^ 2 * (2 ^ j * ((j.factorial : ℝ)) ^ 2)) *
        classicalFactorialSq ρ m g := by
  have hgq : ContDiff ℝ (j : ℕ∞) g := hg.of_le (by exact_mod_cast hjm)
  have hpt : ∀ X : Vec 2, ‖iteratedFDeriv ℝ j (fun X' => g (ρ • X')) X‖ₑ ^ 2 =
      ENNReal.ofReal (ρ ^ (2 * j)) * ‖iteratedFDeriv ℝ j g (ρ • X)‖ₑ ^ 2 := by
    intro X
    rw [enorm_sq_eq_ofReal', enorm_sq_eq_ofReal', iteratedFDeriv_comp_smul_norm j g hgq ρ X,
      ← ENNReal.ofReal_mul (by positivity), abs_of_pos hρ]
    congr 1
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_slowCell_comp_smul' (fun x => iteratedFDeriv ℝ j g x) hρ]
  have hJ := lintegral_iteratedFDeriv_sq_le_classicalFactorialSq m j hjm hg hρ
  calc ENNReal.ofReal (ρ ^ (2 * j)) * (ENNReal.ofReal (ρ⁻¹ ^ 2) *
        ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ j g x‖ₑ ^ 2)
      = ENNReal.ofReal (ρ⁻¹ ^ 2) * (ENNReal.ofReal (ρ ^ (2 * j)) *
          ∫⁻ x in AVenhance.unitCube, ‖iteratedFDeriv ℝ j g x‖ₑ ^ 2) := by ring
    _ ≤ ENNReal.ofReal (ρ⁻¹ ^ 2) * (ENNReal.ofReal (2 ^ j * ((j.factorial : ℝ)) ^ 2) *
          classicalFactorialSq ρ m g) := by gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
end

/-! Coarse flux bound: the coarse field `g(s,X) = ∑_k ∂_{X_k} (F_c(ℓ² s, ρ X))_k`, its regularity,
its slow jets in terms of the jets of `F_c`, and the slow-cell integral of the mass-weighted jet
density by the factorial norms of `F_c`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The coarse field `g(s,X) = ∑_k ∂_{X_k} (F_c(ℓ² s, ρ X))_k`. -/
def coarseField (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ : ℝ) : ℝ → Vec 2 → ∀ i, h i :=
  fun s X => ∑ k : Fin 2, fderiv ℝ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) X (basisVec k)

theorem contDiff_coarseField {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ : ℝ} {r : ℕ} (s : ℝ)
    (hF : ∀ k, ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * s) x k)) :
    ContDiff ℝ (r : ℕ∞) (coarseField Fc ℓ ρ s) := by
  unfold coarseField
  refine ContDiff.sum fun k _ => ?_
  have hG : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) :=
    (hF k).comp (contDiff_const_smul ρ)
  exact (hG.fderiv_right (by simp)).clm_apply contDiff_const

/-- The component of the coarse field. -/
theorem coarseField_apply (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ : ℝ) (s : ℝ) (u : ι)
    {r : ℕ} (hF : ∀ k, ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * s) x k)) :
    (fun X => coarseField Fc ℓ ρ s X u) = fun X => ∑ k : Fin 2,
      orderedDerivative (fun _ : Fin 1 => k) (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) X := by
  funext X
  simp only [coarseField, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hG : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) :=
    (hF k).comp (contDiff_const_smul ρ)
  have hd : DifferentiableAt ℝ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) X :=
    hG.differentiable (by simp) X
  have := fderiv_comp X (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).differentiableAt hd
  have h2 : (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) =
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) u) ∘ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) :=
    rfl
  simp only [orderedDerivative, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil]
  rw [h2, this, ContinuousLinearMap.fderiv]
  rfl

/-- The slow jets of the coarse field are controlled by those of `F_c`. -/
theorem norm_iteratedFDeriv_coarseField_le (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ : ℝ)
    (s : ℝ) (u : ι) {r q : ℕ} (hq : q ≤ r)
    (hF : ∀ k, ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * s) x k)) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ s X' u) X‖ ≤
      ∑ k : Fin 2, ‖iteratedFDeriv ℝ (q + 1)
        (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) X‖ := by
  rw [coarseField_apply Fc ℓ ρ s u hF]
  have hH : ∀ k : Fin 2, ContDiff ℝ ((q + 1 : ℕ) : ℕ∞)
      (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) := fun k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp
      ((hF k).comp (contDiff_const_smul ρ))).of_le (by exact_mod_cast Nat.succ_le_succ hq)
  refine (norm_iteratedFDeriv_sum_le' (p := q) _ (fun k _ => ?_) X).trans ?_
  · exact contDiff_orderedDerivative (p := q) (q := 1) (fun _ : Fin 1 => k)
      (by simpa using hH k)
  · refine Finset.sum_le_sum fun k _ => ?_
    exact norm_iteratedFDeriv_orderedDerivative_le (p := q) (q := 1) (fun _ : Fin 1 => k)
      (hH k) X

/-- The mass-weighted factorial norms of the flux at one time: the integrand of
`classicalFluxL2H`. -/
def fluxDensity (ρ : ℝ) (kres : ℕ) (π : ι → ℝ) (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (t : ℝ) :
    ℝ≥0∞ :=
  ∑ v : ι, ENNReal.ofReal (π v)⁻¹ * ∑ k : Fin 2, classicalFactorialSq ρ kres (fun x => Fc t x k v)

/-- The slow-cell integral of the mass-weighted jet density of the coarse field. -/
theorem lintegral_slowCell_coarseJet_le (π : ι → ℝ) (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (ℓ ρ s : ℝ) {kres q : ℕ} (hρ : 0 < ρ) (hq : q + 1 ≤ kres)
    (hF : ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * s) x k)) :
    ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ *
        ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ s X' u) X‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * (ρ⁻¹ ^ 2 * (2 ^ (q + 1) * (((q + 1).factorial : ℝ)) ^ 2))) *
        fluxDensity ρ kres π Fc (ℓ ^ 2 * s) := by
  have hF' : ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * s) x k) := hF
  have hu : ∀ (k : Fin 2) (u : ι), ContDiff ℝ (kres : ℕ∞) (fun x => Fc (ℓ ^ 2 * s) x k u) :=
    fun k u => ((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp
      ((hF k).of_le (by exact_mod_cast Nat.le_succ kres)))
  have hmeas : ∀ (k : Fin 2) (u : ι), Measurable fun X : Vec 2 =>
      ‖iteratedFDeriv ℝ (q + 1) (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) X‖ₑ ^ 2 := by
    intro k u
    have hH : ContDiff ℝ ((q + 1 : ℕ) : ℕ∞) (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) :=
      ((hu k u).comp (contDiff_const_smul ρ)).of_le (by exact_mod_cast hq)
    exact (hH.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)).enorm.measurable.pow_const 2
  have hpt : ∀ (u : ι) (X : Vec 2),
      ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ s X' u) X‖ₑ ^ 2 ≤
        2 * ∑ k : Fin 2, ‖iteratedFDeriv ℝ (q + 1)
          (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) X‖ₑ ^ 2 := by
    intro u X
    have h1 := norm_iteratedFDeriv_coarseField_le Fc ℓ ρ s u (r := kres) (q := q)
      (by omega) hF' X
    have h2 : ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ s X' u) X‖ₑ ≤
        ∑ k : Fin 2, ‖iteratedFDeriv ℝ (q + 1) (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) X‖ₑ := by
      rw [← ofReal_norm]
      refine (ENNReal.ofReal_le_ofReal h1).trans ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
      exact le_of_eq (Finset.sum_congr rfl fun k _ => ofReal_norm _)
    calc ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ s X' u) X‖ₑ ^ 2
        ≤ (∑ k : Fin 2, ‖iteratedFDeriv ℝ (q + 1)
            (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) X‖ₑ) ^ 2 := by gcongr
      _ ≤ _ := by
          simpa using ennreal_sq_sum_le_card_mul_sum_sq (Finset.univ : Finset (Fin 2))
            (fun k => ‖iteratedFDeriv ℝ (q + 1) (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) X‖ₑ)
  calc ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ *
        ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ s X' u) X‖ₑ ^ 2
      ≤ ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ * (2 * ∑ k : Fin 2,
          ‖iteratedFDeriv ℝ (q + 1) (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) X‖ₑ ^ 2) :=
        lintegral_mono fun X => Finset.sum_le_sum fun u _ => by gcongr; exact hpt u X
    _ = ∑ u, ENNReal.ofReal (π u)⁻¹ * (2 * ∑ k : Fin 2, ∫⁻ X in slowCell ρ,
          ‖iteratedFDeriv ℝ (q + 1) (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k u) X‖ₑ ^ 2) := by
        rw [lintegral_finsetSum _ fun u _ => Measurable.const_mul
          (Measurable.const_mul (Finset.measurable_sum _ fun k _ => hmeas k u) _) _]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ (by simp),
          lintegral_finsetSum _ fun k _ => hmeas k u]
    _ ≤ ∑ u, ENNReal.ofReal (π u)⁻¹ * (2 * ∑ k : Fin 2,
          ENNReal.ofReal (ρ⁻¹ ^ 2 * (2 ^ (q + 1) * (((q + 1).factorial : ℝ)) ^ 2)) *
            classicalFactorialSq ρ kres (fun x => Fc (ℓ ^ 2 * s) x k u)) := by
        refine Finset.sum_le_sum fun u _ => ?_
        gcongr with k
        exact lintegral_slowCell_dilate_le_classicalFactorialSq kres (q + 1) hq (hu k u) hρ
    _ = _ := by
        unfold fluxDensity
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.mul_sum]
        ring
end

end AVRegularity.CoarseFluxDiff
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoarseFluxDiff

/-! The statement of `Providers.cycle_residual_coarse_flux_differentiated`, restated verbatim (a
standalone copy of the statement). -/

/-- The statement for the canonical cleanup of the lifted coarse flux, for each word of length at
most `r` (verbatim copy of `Providers.cycle_residual_coarse_flux_differentiated`). -/
def Statement (Acl N D H kl Ll : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : Prop :=
  1 ≤ Acl →
    ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ rs E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ)
        (_hrs : 0 < rs) (_hrse : rs ≤ e) (_heρ : e ≤ ρ)
        (kres s0 : ℕ), kres = 4 * (N + D) + 2 * Acl + 16 → s0 = Acl + 2 →
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N (s0 + r) (kl + r) (Ll + r) qs qf CG Cw Cj b Θ →
        (∃ M : ℕ, e⁻¹ = (M : ℝ)) →
        ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (s0 + r + D + 2) (max (kl + r + 1) (Ll + r + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H →
        ∀ Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ t, ∀ k, ContDiff ℝ ((kres + r + 1 : ℕ) : ℕ∞) (fun x => Fc t x k)) →
          (∀ t, ∀ k, AVenhance.IsZ2Periodic (fun x => Fc t x k)) →
        ∀ Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ n, 1 ≤ n → n ≤ N → ∀ τ ∈ Set.Icc t₀ t₁,
            IsCleanupChain (s0 + r) (max (kl + r + 1) (Ll + r + 2)) Acl (liftApply n (Cc hh n) (fun s X => ∑ k : Fin 2, fderiv ℝ (fun X' => Fc (ℓ ^ 2 * s) (ρ • X') k) X (basisVec k)) τ) (fun _ _ _ => 0)
              (fun j => Vn n j τ)) →
        ∀ Z : ℝ, Z = Real.sqrt (ℓ ^ 2 * (t₁ - t₀)) / ℓ * (e / ρ) ^ Acl →
          ∀ j : ℕ, j ≤ r → ∀ β : DerivativeWord2 j,
          residualNorm ν π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁))
              (fun t x k => rs ^ j • orderedDerivative β (fun x' =>
                (if hh = 0 then Fc t x' k else 0)
                + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x' k) x)
              (fun t x => rs ^ j • orderedDerivative β (fun x' => ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
                εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn n) t x') x)
            ≤ ENNReal.ofReal (C * ((if hh = 0 then Real.sqrt (B / ν) else 0)
                + Θ ^ hh * εc ^ 2 * (1 + Z)) * (Real.sqrt B)⁻¹) *
              classicalFluxL2H ρ π (Set.Icc (ℓ ^ 2 * t₀) (ℓ ^ 2 * t₁)) (kres + r) Fc

end AVRegularity.CoarseFluxDiff
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoarseFluxDiff

/-! The bridge `mixedCellJet ≤ 2^i cellEnergyJet` under the separate box regularity
`IsBoxSmooth i b` (slow order `i`, fast order `b`) instead of the joint order `i + b`: the slow
`i`-jet is `C^b` in the fast variable because its coordinates on the basis tuples are
`∂_X^w F`, which are `C^b` box smooth fields by the Schwarz lemmas. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar multilinear coefficient `x ↦ ∏_k x_k(w_k)`. -/
def coordProd {i : ℕ} (w : DerivativeWord2 i) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin i) ℝ).compContinuousLinearMap
    (fun k => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (w k))

/-- A multilinear map on `(ℝ²)^i` is the sum of its values on basis tuples. -/
theorem cmlm_expand {i : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E) :
    f = ∑ w : DerivativeWord2 i, ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin i => Vec 2) E
      (coordProd w) (f (fun k => basisVec (w k))) := by
  classical
  ext x
  have hx : x = fun k => ∑ j : Fin 2, x k j • basisVec j := funext fun k => vec2_eq_sum_basisVec _
  have h1 : f x = ∑ r : DerivativeWord2 i, f (fun k => x k (r k) • basisVec (r k)) := by
    conv_lhs => rw [hx]
    exact f.toMultilinearMap.map_sum (fun k j => x k j • basisVec j)
  rw [h1, sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [f.map_smul_univ]
  simp [coordProd, ContinuousMultilinearMap.smulRightL, ContinuousMultilinearMap.mkPiAlgebra_apply]

/-- The slow `i`-jet is `C^b` in the fast variable, under `IsBoxSmooth i b`. -/
theorem contDiff_slowJet {i b : ℕ} {F : Vec 2 → Vec 2 → E} (hF : IsBoxSmooth i b F) (X : Vec 2) :
    ContDiff ℝ (b : ℕ∞) (fun z' => iteratedFDeriv ℝ i (fun X' => F X' z') X) := by
  have hFi : ∀ z', ContDiff ℝ (i : ℕ∞) (fun X' => F X' z') := fun z' => hF.contDiff_slow z'
  have hexp : (fun z' => iteratedFDeriv ℝ i (fun X' => F X' z') X) = fun z' =>
      ∑ w : DerivativeWord2 i, ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin i => Vec 2) E
        (coordProd w) (iteratedFDeriv ℝ i (fun X' => F X' z') X (fun k => basisVec (w k))) := by
    funext z'; exact cmlm_expand _
  rw [hexp]
  refine ContDiff.sum fun w _ => ?_
  refine ((ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin i => Vec 2) E)
    (coordProd w)).contDiff.comp ?_
  -- the coordinates are box smooth fields
  set w' : DerivativeWord2 i := fun k => w (Fin.rev k) with hw'
  have hbox : IsBoxSmooth 0 b (FastJets.slowL (List.ofFn w') F) :=
    FastJets.isBoxSmooth_slowL (sX := 0) (sZ := b) (List.ofFn w') (by simpa using hF)
  have hcoord : (fun z' => iteratedFDeriv ℝ i (fun X' => F X' z') X (fun k => basisVec (w k))) =
      fun z' => FastJets.slowL (List.ofFn w') F X z' := by
    funext z'
    have := congrFun (orderedDerivative_eq_iteratedFDeriv w' (hFi z')) X
    change _ = orderedDerivative w' (fun X' => F X' z') X
    rw [this]
    simp [hw', Fin.rev_rev]
  rw [hcoord]
  exact hbox.1 X

/-- Pointwise: the slow `i`-jet of the fast word is controlled by `2^i` times the `b`-th fast jet of
the slow `i`-jet. -/
theorem norm_slowJet_fastWord_le' {i b : ℕ} {F : Vec 2 → Vec 2 → E}
    (hF : IsBoxSmooth i b F) (δ : DerivativeWord2 b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ i (fun X' => orderedDerivative δ (F X') z) X‖ ≤
      2 ^ i * ‖iteratedFDeriv ℝ b (fun z' => iteratedFDeriv ℝ i (fun X' => F X' z') X) z‖ := by
  set J : Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E :=
    fun z' => iteratedFDeriv ℝ i (fun X' => F X' z') X with hJdef
  have hJ : ContDiff ℝ (b : ℕ∞) J := contDiff_slowJet hF X
  have hFi : ∀ z', ContDiff ℝ (i : ℕ∞) (fun X' => F X' z') := fun z' =>
    hF.contDiff_slow z'
  have hg : ContDiff ℝ (i : ℕ∞) (fun X' => orderedDerivative δ (F X') z) := by
    have h0 : IsBoxSmooth i 0 (FastJets.fastL (List.ofFn δ) F) :=
      FastJets.isBoxSmooth_fastL (sX := i) (sZ := 0) _ (by simpa using hF)
    exact h0.contDiff_slow z
  refine (norm_le_sum_basisVec _).trans ?_
  have hw : ∀ w' : DerivativeWord2 i,
      ‖iteratedFDeriv ℝ i (fun X' => orderedDerivative δ (F X') z) X (fun k => basisVec (w' k))‖ ≤
        ‖iteratedFDeriv ℝ b J z‖ := by
    intro w'
    set w : DerivativeWord2 i := fun k => w' (Fin.rev k) with hwdef
    have e1 : iteratedFDeriv ℝ i (fun X' => orderedDerivative δ (F X') z) X
        (fun k => basisVec (w' k)) = orderedDerivative w
          (fun X' => orderedDerivative δ (F X') z) X := by
      rw [orderedDerivative_eq_iteratedFDeriv w hg]
      simp [hwdef, Fin.rev_rev]
    rw [e1]
    have e2 : orderedDerivative w (fun X' => orderedDerivative δ (F X') z) X =
        FastJets.slowL (List.ofFn w) (FastJets.fastL (List.ofFn δ) F) X z := rfl
    have hcomm := MixedTail.fastL_slowL_comm (List.ofFn w) (List.ofFn δ) (F := F)
      (by simpa using hF)
    have e3 : FastJets.slowL (List.ofFn w) (FastJets.fastL (List.ofFn δ) F) X z =
        orderedDerivative δ (fun z' => orderedDerivative w (fun X' => F X' z') X) z := by
      have := congrFun (congrFun hcomm X) z
      rw [← this]
      rfl
    have e4 : ∀ z', orderedDerivative w (fun X' => F X' z') X =
        J z' (fun k => basisVec (w (Fin.rev k))) := fun z' => by
      rw [orderedDerivative_eq_iteratedFDeriv w (hFi z')]
    have e5 : orderedDerivative δ (fun z' => orderedDerivative w (fun X' => F X' z') X) z =
        orderedDerivative δ J z (fun k => basisVec (w (Fin.rev k))) := by
      simp_rw [e4]
      exact congrFun (orderedDerivative_clm_comp
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => Vec 2) E
          (fun k => basisVec (w (Fin.rev k)))) δ hJ) z
    rw [e2, e3, e5]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hn : ∏ k : Fin i, ‖(basisVec (w (Fin.rev k)) : Vec 2)‖ = 1 := by simp [norm_basisVec]
    rw [hn, mul_one]
    exact norm_orderedDerivative_le hJ δ z
  calc ∑ w' : DerivativeWord2 i,
        ‖iteratedFDeriv ℝ i (fun X' => orderedDerivative δ (F X') z) X (fun k => basisVec (w' k))‖
      ≤ ∑ _w' : DerivativeWord2 i, ‖iteratedFDeriv ℝ b J z‖ := Finset.sum_le_sum fun w' _ => hw w'
    _ = 2 ^ i * ‖iteratedFDeriv ℝ b J z‖ := by
        rw [Finset.sum_const, card_derivativeWord2]; simp

/-- The mixed cell jet is bounded by the energy jet, `b ≤ k`, with the constant `2^i`. -/
theorem mixedCellJet_le_cellEnergyJet' (I : Set ℝ) {i b k : ℕ} (hb : b ≤ k) (δ : DerivativeWord2 b)
    (f : ℝ → Vec 2 → Vec 2 → E) (hf : ∀ t ∈ I, IsBoxSmooth i b (f t)) :
    MixedTail.mixedCellJet I i δ f ≤ 2 ^ i * cellEnergyJet I k i f := by
  unfold MixedTail.mixedCellJet
  refine iSup₂_le fun t ht => iSup_le fun X => ?_
  have hFt := hf t ht
  set μ := volume.restrict AVenhance.unitCube with hμ
  set D : Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin b => Vec 2)
      (ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E) :=
    fun z => iteratedFDeriv ℝ b (fun z' => iteratedFDeriv ℝ i (fun X' => f t X' z') X) z with hD
  have hmeas : AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ i (fun X' => orderedDerivative δ (f t X') z) X) μ := by
    have h0 : IsBoxSmooth i 0 (FastJets.fastL (List.ofFn δ) (f t)) :=
      FastJets.isBoxSmooth_fastL (sX := i) (sZ := 0) _ (by simpa using hFt)
    have := (h0.isSlowSmooth.2 i le_rfl).comp (Continuous.prodMk_right X)
    exact this.aestronglyMeasurable
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (2 : ℝ) ^ i := ⟨_, rfl⟩
  set hh : Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E :=
    fun z => iteratedFDeriv ℝ i (fun X' => orderedDerivative δ (f t X') z) X with hhdef
  have hc0 : 0 < c := by rw [hc]; positivity
  have h5 : eLpNorm (c⁻¹ • hh) 2 μ ≤ eLpNorm D 2 μ := by
    refine eLpNorm_mono_enorm (hmeas.const_smul c⁻¹) fun z => ?_
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h6 := norm_slowJet_fastWord_le' hFt δ X z
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc0.le)]
    rw [← hc] at h6
    calc c⁻¹ * ‖hh z‖ ≤ c⁻¹ * (c * ‖D z‖) := by gcongr
      _ = ‖D z‖ := by field_simp
  have h5' := eLpNorm_const_smul (c⁻¹) hh 2 μ
  rw [h5'] at h5
  have h1 : eLpNorm hh 2 μ ≤ ‖c‖ₑ * eLpNorm D 2 μ := by
    have hcc : ‖c‖ₑ * ‖c⁻¹‖ₑ = 1 := by
      rw [← enorm_mul, mul_inv_cancel₀ hc0.ne']; simp
    calc eLpNorm hh 2 μ = ‖c‖ₑ * (‖c⁻¹‖ₑ * eLpNorm hh 2 μ) := by rw [← mul_assoc, hcc, one_mul]
      _ ≤ _ := by gcongr
  refine h1.trans ?_
  have h2 : eLpNorm D 2 μ ≤ cellEnergyJet I k i f := by
    have h3 : eLpNorm D 2 μ ≤ fieldEnergyNorm I (fun t' z =>
        iteratedFDeriv ℝ b (fun z' => iteratedFDeriv ℝ i (fun X' => f t' X' z') X) z) := by
      unfold fieldEnergyNorm
      refine le_trans ?_ le_self_add
      exact le_iSup₂_of_le t ht le_rfl
    refine h3.trans ?_
    unfold cellEnergyJet
    refine le_trans ?_ (Finset.single_le_sum (f := fun q => ⨆ X : Vec 2, fieldEnergyNorm I
      (fun t z => iteratedFDeriv ℝ q (fun z' => iteratedFDeriv ℝ i (fun X' => f t X' z') X) z))
      (fun _ _ => bot_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hb)))
    exact le_iSup (fun X : Vec 2 => fieldEnergyNorm I (fun t z =>
      iteratedFDeriv ℝ b (fun z' => iteratedFDeriv ℝ i (fun X' => f t X' z') X) z)) X
  have h4 : ‖c‖ₑ = (2 : ℝ≥0∞) ^ i := by
    rw [← ofReal_norm, hc]; simp
  rw [h4]
  gcongr

/-- The weighted block norm of the mixed jets is bounded by that of the energy jets. -/
theorem schurMixedJet_le_schurEnergyJet' {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]
    (π : ι → ℝ) (I : Set ℝ) {i b k : ℕ} (hb : b ≤ k) (δ : DerivativeWord2 b)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a v u, ∀ t ∈ I, IsBoxSmooth i b (fun X z => c a t X z v u)) :
    MixedTail.schurMixedJet π I i δ c ≤ 2 ^ i * schurEnergyJet π I k i c := by
  unfold MixedTail.schurMixedJet schurEnergyJet
  refine le_trans (schurSums_mono π fun v u => ?_) (MixedTail.schurSums_const_mul_le π _ _)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ =>
    mixedCellJet_le_cellEnergyJet' I hb δ _ (fun t ht => hc a v u t ht)
end

/-! Differentiated coarse flux: the `L²` norm of a weighted word derivative of the diagonal sample
of a box smooth vector field, in terms of the mixed jets `vecJetF`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sum_scalJetF_le_vecJetF {b : ℕ} (W : Vec 2 → Vec 2 → Fin 2 → E) (p : ℕ)
    (δ : DerivativeWord2 b) (X : Vec 2) :
    ∑ k : Fin 2, FastJets.scalJetF (fun X y => W X y k) p δ X ≤ FastJets.vecJetF W p δ X := by
  unfold FastJets.scalJetF FastJets.vecJetF
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun β _ => ?_
  exact sum_lintegral_le_lintegral_sum (μ := volume.restrict AVenhance.unitCube) Finset.univ
    (fun k y => ‖orderedDerivative β (fun X' => orderedDerivative δ (fun y' => W X' y' k) y) X‖ₑ ^ 2)

/-- Measurability of the squared weighted word derivative of a diagonal sample. -/
theorem measurable_sampled_word {j : ℕ} (β : DerivativeWord2 j) {W : Vec 2 → Vec 2 → E}
    {sX sZ : ℕ} (hW : IsBoxSmooth sX sZ W) (hX : j ≤ sX) (hZ : j ≤ sZ) (ρ e c : ℝ) :
    Measurable fun x : Vec 2 =>
      ‖c • orderedDerivative β (fun x' => W (ρ⁻¹ • x') (e⁻¹ • x')) x‖ₑ ^ 2 := by
  have hU : ContDiff ℝ (j : ℕ∞) (Function.uncurry W) := hW.contDiff_uncurry hX hZ
  have hg : ContDiff ℝ (j : ℕ∞) (fun x' : Vec 2 => W (ρ⁻¹ • x') (e⁻¹ • x')) :=
    hU.comp ((contDiff_const_smul _).prodMk (contDiff_const_smul _))
  have hc : Continuous (orderedDerivative β (fun x' => W (ρ⁻¹ • x') (e⁻¹ • x'))) :=
    (contDiff_orderedDerivative (p := 0) β (by simpa using hg)).continuous
  exact ((continuous_const.smul hc).enorm.measurable).pow_const 2

/-- **Word derivatives of the sampled vector field in terms of the mixed jets.** -/
theorem sampled_word_vec_le {j : ℕ} (β : DerivativeWord2 j) {W : Vec 2 → Vec 2 → Fin 2 → E}
    (hW : IsBoxSmooth (j + 2) j W) (hper : ∀ X, AVenhance.IsZ2Periodic (W X))
    {ρ e rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) (M : ℕ) (hM : e⁻¹ = (M : ℝ)) :
    ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖rs ^ j • orderedDerivative β (fun x' => W (ρ⁻¹ • x') (e⁻¹ • x') k) x‖ₑ ^ 2
      ≤ 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
        ∑ δ : DerivativeWord2 ab.2, ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
          FastJets.vecJetF W (ab.1 + m) δ X := by
  have hk : ∀ k : Fin 2, IsBoxSmooth (j + 2) j (fun X y => W X y k) := fun k =>
    hW.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k)
  have hperk : ∀ (k : Fin 2) X, AVenhance.IsZ2Periodic (fun y => W X y k) := fun k X n y =>
    congrFun (hper X n y) k
  have hmeas : ∀ k ∈ (Finset.univ : Finset (Fin 2)), Measurable fun x : Vec 2 =>
      ‖rs ^ j • orderedDerivative β (fun x' => W (ρ⁻¹ • x') (e⁻¹ • x') k) x‖ₑ ^ 2 := fun k _ =>
    measurable_sampled_word β (hk k) (by omega) le_rfl ρ e _
  rw [lintegral_finsetSum _ hmeas]
  calc ∑ k : Fin 2, ∫⁻ x in AVenhance.unitCube,
        ‖rs ^ j • orderedDerivative β (fun x' => W (ρ⁻¹ • x') (e⁻¹ • x') k) x‖ₑ ^ 2
      ≤ ∑ k : Fin 2, 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
          ∑ δ : DerivativeWord2 ab.2, ∑ m ∈ Finset.range 3, ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => W X y k) (ab.1 + m) δ X :=
        Finset.sum_le_sum fun k _ =>
          FastJets.lintegral_rs_odL_diag_sq_le β (hk k) (hperk k) hrs hrse heρ M hM
    _ = 4 ^ j * ENNReal.ofReal (4 * ρ ^ 2) * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal j,
          ∑ δ : DerivativeWord2 ab.2, ∑ m ∈ Finset.range 3, ∑ k : Fin 2, ∫⁻ X in slowCell ρ,
            FastJets.scalJetF (fun X y => W X y k) (ab.1 + m) δ X := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_comm]
    _ ≤ _ := by
        gcongr with ab _ δ _ m _
        refine (sum_lintegral_le_lintegral_sum (μ := volume.restrict (slowCell ρ))
          (Finset.univ : Finset (Fin 2))
          (fun k X => FastJets.scalJetF (fun X y => W X y k) (ab.1 + m) δ X)).trans ?_
        exact lintegral_mono fun X => sum_scalJetF_le_vecJetF W _ δ X
end

/-! Differentiated coarse flux: the zeroth-order coefficients vanish when the lift action
annihilates constants, the mixed jets of vanishing arrays, and the mixed jets of the lift
coefficients from the grading. -/

theorem orderedDerivative_const' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    (β : DerivativeWord2 j) (c0 : E) :
    orderedDerivative β (fun _ : Vec 2 => c0) = fun _ => if j = 0 then c0 else 0 := by
  induction j with
  | zero => rw [orderedDerivative_zero]; simp
  | succ j ih =>
    rw [orderedDerivative_succ, ih]
    funext x
    simp

theorem coeff_zero_of_const {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (c : LiftCoeff ι h) (n : ℕ)
    (t : ℝ) (X z : Vec 2)
    (H : ∀ c0 : ∀ i, h i, liftApply n c (fun _ _ => c0) t X z = 0) (α : DerivativeWord2 0)
    (v u : ι) : c 0 α t X z v u = 0 := by
  classical
  ext w
  have h1 := congrFun (H (Pi.single u w)) v
  simp only [liftApply, Pi.zero_apply] at h1
  have hm0 : ∀ m ∈ Finset.range (n + 1), m ≠ 0 → ∑ α' : DerivativeWord2 m, ∑ u' : ι,
      c m α' t X z v u' (orderedDerivative α' (fun _ : Vec 2 => (Pi.single u w : ∀ i, h i)) X u')
        = 0 := by
    intro m _ hm
    refine Finset.sum_eq_zero fun α' _ => Finset.sum_eq_zero fun u' _ => ?_
    simp [orderedDerivative_const', hm]
  rw [Finset.sum_eq_single 0 hm0 (fun h0 => absurd (Finset.mem_range.2 (Nat.succ_pos n)) h0)] at h1
  have hα : ∀ α' ∈ (Finset.univ : Finset (DerivativeWord2 0)), α' ≠ α → ∑ u' : ι,
      c 0 α' t X z v u' (orderedDerivative α' (fun _ : Vec 2 => (Pi.single u w : ∀ i, h i)) X u')
        = 0 := fun α' _ hα' => absurd (funext fun i => i.elim0) hα'
  rw [Finset.sum_eq_single α hα (fun h0 => absurd (Finset.mem_univ _) h0)] at h1
  rw [Finset.sum_eq_single u] at h1
  · simpa [orderedDerivative_const'] using h1
  · intro u' _ hu'
    simp [orderedDerivative_const', Pi.single_eq_of_ne hu']
  · simp

theorem mixedCellJet_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ}
    (i : ℕ) {b : ℕ} (δ : DerivativeWord2 b) {f : ℝ → Vec 2 → Vec 2 → E}
    (hf : ∀ t ∈ I, ∀ X z, f t X z = 0) : MixedTail.mixedCellJet I i δ f = 0 := by
  unfold MixedTail.mixedCellJet
  refine le_antisymm (iSup₂_le fun t ht => iSup_le fun X => ?_) bot_le
  have h0 : (fun z : Vec 2 => iteratedFDeriv ℝ i (fun X' => orderedDerivative δ (f t X') z) X) =
      0 := by
    funext z
    have h1 : (fun X' => orderedDerivative δ (f t X') z) = fun _ => (0 : E) := by
      funext X'
      have : f t X' = fun _ => (0 : E) := funext fun z' => hf t ht X' z'
      rw [this, orderedDerivative_const_zero]
    rw [h1]; simp [iteratedFDeriv_fun_zero]
  rw [h0]
  exact le_of_eq (eLpNorm_zero (ε := ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E))

theorem schurMixedJet_eq_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]
    (π : ι → ℝ) (I : Set ℝ) (i : ℕ) {b : ℕ} (δ : DerivativeWord2 b)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a, ∀ t ∈ I, ∀ X z v u, c a t X z v u = 0) : MixedTail.schurMixedJet π I i δ c = 0 := by
  unfold MixedTail.schurMixedJet schurSums
  have h0 : ∀ v u, ∑ a : κ, MixedTail.mixedCellJet I i δ (fun t X z => c a t X z v u) = 0 :=
    fun v u => Finset.sum_eq_zero fun a _ =>
      mixedCellJet_eq_zero i δ fun t ht X z => hc a t ht X z v u
  simp [h0]

/-- The mixed jets of the lift coefficients of one degree. -/
theorem mjet_bounds {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (I : Set ℝ)
    {A r k : ℕ} (hk : r ≤ k) (c : LiftCoeff ι h) (Cg Θ lam : ℝ) (hCg : 0 ≤ Cg) (hΘ : 0 ≤ Θ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hh n : ℕ)
    (hbox : ∀ m α v u, ∀ t ∈ I, IsBoxSmooth (A + 2 + r) r (fun X z => c m α t X z v u))
    (hc0 : ∀ α, ∀ t ∈ I, ∀ X z v u, c 0 α t X z v u = 0)
    (hcgt : ∀ m, n < m → ∀ α, ∀ t ∈ I, ∀ X z v u, c m α t X z v u = 0)
    (hgr : ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ A + 2 + r →
      schurEnergyJet π I k j (c m) ≤ ENNReal.ofReal (Cg * Θ ^ hh * lam ^ (n - m + j))) :
    (∀ b, b ≤ r → ∀ δ : DerivativeWord2 b, ∀ i, MixedTail.schurMixedJet π I i δ (c 0) = 0) ∧
    (∀ b, b ≤ r → ∀ δ : DerivativeWord2 b, ∀ i, i ≤ A + 2 + r → ∀ m,
      MixedTail.schurMixedJet π I i δ (c m) ≤
        ENNReal.ofReal (2 ^ (A + 2 + r) * Cg * Θ ^ hh)) := by
  refine ⟨fun b _ δ i => schurMixedJet_eq_zero π I i δ (c 0) hc0, ?_⟩
  intro b hb δ i hi m
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [schurMixedJet_eq_zero π I i δ (c 0) hc0]; exact bot_le
  by_cases hmn : n < m
  · rw [schurMixedJet_eq_zero π I i δ (c m) (hcgt m hmn)]; exact bot_le
  have hmn' : m ≤ n := not_lt.1 hmn
  have hbox' : ∀ α v u, ∀ t ∈ I, IsBoxSmooth i b (fun X z => c m α t X z v u) :=
    fun α v u t ht => (hbox m α v u t ht).mono hi hb
  refine (schurMixedJet_le_schurEnergyJet' π I (k := k) (by omega) δ (c m)
    (fun a v u t ht => hbox' a v u t ht)).trans ?_
  refine (mul_le_mul' le_rfl (hgr m hm0 hmn' i hi)).trans ?_
  have hlam : lam ^ (n - m + i) ≤ 1 := pow_le_one₀ hlam0 hlam1
  have h2 : (2 : ℝ) ^ i ≤ 2 ^ (A + 2 + r) := pow_le_pow_right₀ (by norm_num) hi
  have hΘh : 0 ≤ Θ ^ hh := pow_nonneg hΘ hh
  calc (2 : ℝ≥0∞) ^ i * ENNReal.ofReal (Cg * Θ ^ hh * lam ^ (n - m + i))
      = ENNReal.ofReal (2 ^ i * (Cg * Θ ^ hh * lam ^ (n - m + i))) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ i),
          ENNReal.ofReal_pow (by norm_num)]; simp
    _ ≤ ENNReal.ofReal (2 ^ (A + 2 + r) * Cg * Θ ^ hh) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (2 : ℝ) ^ i * (Cg * Θ ^ hh * lam ^ (n - m + i))
            ≤ 2 ^ i * (Cg * Θ ^ hh * 1) := by
              have hnn : 0 ≤ Cg * Θ ^ hh := mul_nonneg hCg hΘh
              gcongr
          _ = 2 ^ i * Cg * Θ ^ hh := by ring
          _ ≤ 2 ^ (A + 2 + r) * Cg * Θ ^ hh := by gcongr

/-! Differentiated coarse flux: the mass-weighted mixed slow jet of the fast word `δ` of one lift
action, in terms of the mixed cell jets of the coefficient array and the jets of the coarse field,
and its slow-cell integral in terms of the flux density at the physical time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The constant of `lift_scalJetF_le`. -/
def liftJetConst (n p : ℕ) : ℝ :=
  2 ^ p * tailJetConst n p * (((n + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ))

theorem liftJetConst_nonneg (n p : ℕ) : 0 ≤ liftJetConst n p := by
  unfold liftJetConst tailJetConst; positivity

/-- The mass-weighted mixed slow jet of a lift action. -/
theorem lift_scalJetF_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (n p : ℕ) {b : ℕ}
    (δ : DerivativeWord2 b) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ I)
    (hbox : ∀ m α v u, IsBoxSmooth p b (fun X y => c m α τ X y v u))
    (hjet0 : ∀ i, MixedTail.schurMixedJet π I i δ (c 0) = 0) (s : ℝ≥0∞)
    (hjet : ∀ i, i ≤ p → ∀ m, MixedTail.schurMixedJet π I i δ (c m) ≤ s)
    (ha : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (a τ)) (X : Vec 2) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * FastJets.scalJetF (fun X y => liftApply n c a τ X y v) p δ X
      ≤ ENNReal.ofReal (liftJetConst n p) * s ^ 2 *
          ∑ q ∈ Finset.Icc 1 (p + n),
            ∑ u, ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => a τ X' u) X‖ₑ ^ 2 := by
  have hbox0 : ∀ m α v u, IsBoxSmooth p 0 (fun X y => MixedTail.fastCoeff δ c m α τ X y v u) :=
    fun m α v u => FastJets.isBoxSmooth_fastL (sX := p) (sZ := 0) (List.ofFn δ)
      (F := fun X y => c m α τ X y v u) (by simpa using hbox m α v u)
  have hrew : ∀ X' y v, liftApply n (MixedTail.fastCoeff δ c) a τ X' y v =
      orderedDerivative δ (fun y' => liftApply n c a τ X' y' v) y := fun X' y v =>
    MixedTail.liftApply_fastCoeff δ n c a τ X' (fun m α v u => (hbox m α v u).1 X') y v
  have hsc : ∀ v y, ContDiff ℝ (p : ℕ∞) (fun X' => liftApply n (MixedTail.fastCoeff δ c) a τ X' y v) :=
    fun v y => contDiff_liftApply (MixedTail.fastCoeff δ c) a τ y v
      (fun m α u => ((hbox0 m α v u).isSlowSmooth).1 y) ha
  have h1 : ∀ v, FastJets.scalJetF (fun X y => liftApply n c a τ X y v) p δ X ≤
      2 ^ p * ∫⁻ y in AVenhance.unitCube, ‖iteratedFDeriv ℝ p
        (fun X' => orderedDerivative δ (fun y' => liftApply n c a τ X' y' v) y) X‖ₑ ^ 2 := by
    intro v
    have := scalJet_le_iteratedFDeriv
      (fun X y => orderedDerivative δ (fun y' => liftApply n c a τ X y' v) y)
      (fun y => by simpa only [hrew] using hsc v y) X
    exact this
  have hT2 := MixedTail.sum_mass_lintegral_iteratedFDeriv_fast_le π hπ I n p δ c a hτ hbox ha X
  have hcol := BoundTail.collapse_le n p (fun m i => MixedTail.schurMixedJet π I i δ (c m))
    (fun q => ∑ u, ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => a τ X' u) X‖ₑ ^ 2) s
    hjet0 (fun m i hi => hjet i hi m)
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * FastJets.scalJetF (fun X y => liftApply n c a τ X y v) p δ X
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (2 ^ p * ∫⁻ y in AVenhance.unitCube,
          ‖iteratedFDeriv ℝ p
            (fun X' => orderedDerivative δ (fun y' => liftApply n c a τ X' y' v) y) X‖ₑ ^ 2) :=
        Finset.sum_le_sum fun v _ => by gcongr; exact h1 v
    _ = 2 ^ p * ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ y in AVenhance.unitCube,
          ‖iteratedFDeriv ℝ p
            (fun X' => orderedDerivative δ (fun y' => liftApply n c a τ X' y' v) y) X‖ₑ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ 2 ^ p * (ENNReal.ofReal (tailJetConst n p) * ∑ m ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (p + 1), MixedTail.schurMixedJet π I i δ (c m) ^ 2 *
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2) := by gcongr
    _ ≤ 2 ^ p * (ENNReal.ofReal (tailJetConst n p) * (((n + 1 : ℕ) : ℝ≥0∞) *
          ((p + 1 : ℕ) : ℝ≥0∞) * s ^ 2 * ∑ q ∈ Finset.Icc 1 (p + n),
            ∑ u, ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => a τ X' u) X‖ₑ ^ 2)) := by
        gcongr
    _ = _ := by
        have ht : 0 ≤ tailJetConst n p := by unfold tailJetConst; positivity
        unfold liftJetConst
        rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) ht),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ p),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
        ring
end

/-! Differentiated coarse flux: the slow-cell integral of the mass-weighted mixed jet of one lift
action of the coarse field, in terms of the flux density at the physical time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The coarse jet weight `2 · 2^{q+1} ((q+1)!)²`. -/
def coarseConst (q : ℕ) : ℝ := 2 * (2 ^ (q + 1) * (((q + 1).factorial : ℝ)) ^ 2)

theorem coarseConst_nonneg (q : ℕ) : 0 ≤ coarseConst q := by unfold coarseConst; positivity

/-- The slow-cell integral of the scalar slow jet of one lift action of the coarse field. -/
theorem slowCell_scalJetF_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (n p kres : ℕ) {b : ℕ} (δ : DerivativeWord2 b)
    (hk : p + n + 1 ≤ kres) (c : LiftCoeff ι h) {τ : ℝ} (hτ : τ ∈ I)
    (hbox : ∀ m α v u, IsBoxSmooth p b (fun X y => c m α τ X y v u))
    (hjet0 : ∀ i, MixedTail.schurMixedJet π I i δ (c 0) = 0) (s : ℝ≥0∞)
    (hjet : ∀ i, i ≤ p → ∀ m, MixedTail.schurMixedJet π I i δ (c m) ≤ s)
    (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ : ℝ) (hρ : 0 < ρ)
    (hF : ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * τ) x k)) :
    ∫⁻ X in slowCell ρ, ∑ v, ENNReal.ofReal (π v)⁻¹ *
        FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X
      ≤ ENNReal.ofReal (ρ⁻¹ ^ 2 * (liftJetConst n p * ∑ q ∈ Finset.Icc 1 (p + n), coarseConst q)) *
          s ^ 2 * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
  have hF' : ∀ k, ContDiff ℝ ((p + n + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * τ) x k) := fun k =>
    (hF k).of_le (by exact_mod_cast (by omega : p + n + 1 ≤ kres + 1))
  have ha : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (coarseField Fc ℓ ρ τ) :=
    contDiff_coarseField τ hF'
  have hmeas : ∀ q ∈ Finset.Icc 1 (p + n), Measurable fun X : Vec 2 => ∑ u,
      ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ τ X' u) X‖ₑ ^ 2 := by
    intro q hq
    have hq' : q ≤ p + n := (Finset.mem_Icc.1 hq).2
    refine Finset.measurable_sum _ fun u _ => Measurable.const_mul ?_ _
    have hau : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (fun X' => coarseField Fc ℓ ρ τ X' u) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp ha
    exact ((hau.continuous_iteratedFDeriv (by exact_mod_cast hq')).enorm.measurable).pow_const 2
  have hpt := fun X => lift_scalJetF_le π hπ I n p δ c (coarseField Fc ℓ ρ) hτ hbox hjet0 s hjet ha X
  have hq : ∀ q ∈ Finset.Icc 1 (p + n), ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ *
      ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ τ X' u) X‖ₑ ^ 2 ≤
      ENNReal.ofReal (ρ⁻¹ ^ 2 * coarseConst q) * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
    intro q hqI
    obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.1 hqI
    refine (lintegral_slowCell_coarseJet_le π Fc ℓ ρ τ hρ (by omega) hF).trans ?_
    refine le_of_eq (congrArg (· * _) (congrArg ENNReal.ofReal ?_))
    unfold coarseConst; ring
  calc ∫⁻ X in slowCell ρ, ∑ v, ENNReal.ofReal (π v)⁻¹ *
        FastJets.scalJetF (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p δ X
      ≤ ∫⁻ X in slowCell ρ, ENNReal.ofReal (liftJetConst n p) * s ^ 2 *
          ∑ q ∈ Finset.Icc 1 (p + n), ∑ u, ENNReal.ofReal (π u)⁻¹ *
            ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ τ X' u) X‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (liftJetConst n p) * s ^ 2 *
          ∑ q ∈ Finset.Icc 1 (p + n), ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ *
            ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ τ X' u) X‖ₑ ^ 2 := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ hmeas), lintegral_finsetSum _ hmeas]
    _ ≤ ENNReal.ofReal (liftJetConst n p) * s ^ 2 *
          ∑ q ∈ Finset.Icc 1 (p + n), ENNReal.ofReal (ρ⁻¹ ^ 2 * coarseConst q) *
            fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
        gcongr with q hq'
        exact hq q hq'
    _ = _ := by
        have hSum : 0 ≤ ∑ q ∈ Finset.Icc 1 (p + n), coarseConst q :=
          Finset.sum_nonneg fun q _ => coarseConst_nonneg q
        have e : ENNReal.ofReal (ρ⁻¹ ^ 2 * (liftJetConst n p *
            ∑ q ∈ Finset.Icc 1 (p + n), coarseConst q)) = ENNReal.ofReal (ρ⁻¹ ^ 2) *
            (ENNReal.ofReal (liftJetConst n p) *
              ∑ q ∈ Finset.Icc 1 (p + n), ENNReal.ofReal (coarseConst q)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (liftJetConst_nonneg n p),
            ENNReal.ofReal_sum_of_nonneg fun q _ => coarseConst_nonneg q]
        rw [e, ← Finset.sum_mul]
        simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ρ⁻¹ ^ 2)]
        rw [← Finset.mul_sum]
        ring
end

end AVRegularity.CoarseFluxDiff
end
end
