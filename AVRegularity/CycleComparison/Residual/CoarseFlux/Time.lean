-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.BoundPointwise
public import AVRegularity.CycleComparison.Residual.ChainProject
public import AVRegularity.CycleComparison.Residual.TailJets.Main
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import AVRegularity.CycleComparison.Residual.TailJets

section
@[expose] public section
namespace AVRegularity.CoarseFluxBound

/-! Coarse flux bound: the elementary real inequality combining the identity, cleanup flux and
scalar parts into the bound `C [1_{h=0} √(B/ν) + Θ^h ε_c² (1+Z)] B^{-1/2}`. -/

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
theorem final_real {ν B ρ e ℓ εc L C₀ Θh N cf cr indr : ℝ} {A : ℕ} (hν : 0 < ν) (hB : 0 < B)
    (hρ : 0 < ρ) (he : 0 < e) (hℓ : ℓ = e / Real.sqrt ν) (hε : εc = ℓ * Real.sqrt B / ρ)
    (hC₀ : 0 ≤ C₀) (hΘ : 0 ≤ Θh) (hN : 0 ≤ N) (hcf : 0 ≤ cf)
    (hind : indr = 0 ∨ indr = 1) :
    (Real.sqrt ν)⁻¹ * Real.sqrt (2 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf) +
        Real.sqrt (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cr) * Real.sqrt L ≤
      max (Real.sqrt 2) (max (C₀ * Real.sqrt (2 * N * cf)) (C₀ * Real.sqrt (N * cr))) *
        (indr * Real.sqrt (B / ν) + Θh * εc ^ 2 * (1 + Real.sqrt L / ℓ * (e / ρ) ^ A)) *
          (Real.sqrt B)⁻¹ := by
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hℓpos : 0 < ℓ := by rw [hℓ]; positivity
  have hεpos : 0 < εc := by rw [hε]; positivity
  have hϑ : 0 < e / ρ := by positivity
  set M := max (Real.sqrt 2) (max (C₀ * Real.sqrt (2 * N * cf)) (C₀ * Real.sqrt (N * cr))) with hM
  have hM1 : Real.sqrt 2 ≤ M := le_max_left _ _
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
  have hK1 : Real.sqrt (2 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf) ≤
      Real.sqrt 2 * indr + (e / ρ) * εc * (C₀ * Θh) * Real.sqrt (2 * N * cf) := by
    have e1 : 2 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf =
        2 * indr + ((e / ρ) * εc * (C₀ * Θh)) ^ 2 * (2 * N * cf) := by ring
    rw [e1]
    have hind0 : 0 ≤ 2 * indr := by rcases hind with h | h <;> simp [h]
    refine (sqrt_add_le_add_sqrt' hind0 (by positivity)).trans ?_
    rw [sqrt_sq_mul (by positivity)]
    refine add_le_add (le_of_eq ?_) le_rfl
    rcases hind with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hflux : (Real.sqrt ν)⁻¹ *
      Real.sqrt (2 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf) ≤
      M * (indr * Real.sqrt (B / ν) + Θh * εc ^ 2) * (Real.sqrt B)⁻¹ := by
    have hind' : 0 ≤ indr := by rcases hind with h | h <;> simp [h]
    calc (Real.sqrt ν)⁻¹ * Real.sqrt (2 * indr + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * (C₀ * Θh) ^ 2 * cf)
        ≤ (Real.sqrt ν)⁻¹ * (Real.sqrt 2 * indr + (e / ρ) * εc * (C₀ * Θh) *
            Real.sqrt (2 * N * cf)) := by gcongr
      _ = Real.sqrt 2 * indr * (Real.sqrt (B / ν) / Real.sqrt B) +
          (εc / Real.sqrt B) * εc * (C₀ * Θh) * Real.sqrt (2 * N * cf) := by
          rw [← hI3, ← hI1]; ring
      _ = (Real.sqrt 2 * (indr * Real.sqrt (B / ν)) + (C₀ * Real.sqrt (2 * N * cf)) *
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

end AVRegularity.CoarseFluxBound
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CoarseFluxBound

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

end AVRegularity.CoarseFluxBound
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoarseFluxBound

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

/-! Coarse flux bound: the mass-weighted slow jet of one lift action `C_n a` in terms of the Schur
cell-`L²` jets of the coefficient array and the jets of the coarse field. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The constant of `lift_scalJet_le`. -/
def liftJetConst (n p : ℕ) : ℝ :=
  2 ^ p * tailJetConst n p * (((n + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ))

theorem liftJetConst_nonneg (n p : ℕ) : 0 ≤ liftJetConst n p := by
  unfold liftJetConst tailJetConst; positivity

/-- The mass-weighted scalar slow jet of a lift action. -/
theorem lift_scalJet_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (n p : ℕ)
    (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ I)
    (hbox : ∀ m α v u, IsBoxSmooth p 0 (fun X y => c m α τ X y v u))
    (hjet0 : ∀ i, schurCellL2Jet π I i (c 0) = 0) (s : ℝ≥0∞)
    (hjet : ∀ i, i ≤ p → ∀ m, schurCellL2Jet π I i (c m) ≤ s)
    (ha : ContDiff ℝ ((p + n : ℕ) : ℕ∞) (a τ)) (X : Vec 2) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * scalJet (fun X y => liftApply n c a τ X y v) p X
      ≤ ENNReal.ofReal (liftJetConst n p) * s ^ 2 *
          ∑ q ∈ Finset.Icc 1 (p + n),
            ∑ u, ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => a τ X' u) X‖ₑ ^ 2 := by
  have hsc : ∀ v y, ContDiff ℝ (p : ℕ∞) (fun X' => liftApply n c a τ X' y v) := fun v y =>
    contDiff_liftApply c a τ y v (fun m α u => ((hbox m α v u).isSlowSmooth).1 y) ha
  have h1 : ∀ v, scalJet (fun X y => liftApply n c a τ X y v) p X ≤
      2 ^ p * ∫⁻ y in AVenhance.unitCube, ‖iteratedFDeriv ℝ p
        (fun X' => liftApply n c a τ X' y v) X‖ₑ ^ 2 := fun v =>
    scalJet_le_iteratedFDeriv _ (fun y => hsc v y) X
  have hT2 := sum_mass_lintegral_iteratedFDeriv_liftApply_le π hπ I n p c a hτ hbox ha X
  have hcol := BoundTail.collapse_le n p (fun m i => schurCellL2Jet π I i (c m))
    (fun q => ∑ u, ENNReal.ofReal (π u)⁻¹ * ‖iteratedFDeriv ℝ q (fun X' => a τ X' u) X‖ₑ ^ 2) s
    hjet0 (fun m i hi => hjet i hi m)
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * scalJet (fun X y => liftApply n c a τ X y v) p X
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (2 ^ p * ∫⁻ y in AVenhance.unitCube,
          ‖iteratedFDeriv ℝ p (fun X' => liftApply n c a τ X' y v) X‖ₑ ^ 2) :=
        Finset.sum_le_sum fun v _ => by gcongr; exact h1 v
    _ = 2 ^ p * ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ y in AVenhance.unitCube,
          ‖iteratedFDeriv ℝ p (fun X' => liftApply n c a τ X' y v) X‖ₑ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ 2 ^ p * (ENNReal.ofReal (tailJetConst n p) * ∑ m ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (p + 1), schurCellL2Jet π I i (c m) ^ 2 *
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

/-! Coarse flux bound: the slow-cell integral of the mass-weighted slow jet of one lift action of
the coarse field, in terms of the flux density `∑_v π_v⁻¹ ∑_k ‖F_c‖²_{ρ,k}` at the physical time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- The coarse jet weight `2 · 2^{q+1} ((q+1)!)²`. -/
def coarseConst (q : ℕ) : ℝ := 2 * (2 ^ (q + 1) * (((q + 1).factorial : ℝ)) ^ 2)

theorem coarseConst_nonneg (q : ℕ) : 0 ≤ coarseConst q := by unfold coarseConst; positivity

/-- The slow-cell integral of the scalar slow jet of one lift action of the coarse field. -/
theorem slowCell_scalJet_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (n p kres : ℕ)
    (hk : p + n + 1 ≤ kres) (c : LiftCoeff ι h) {τ : ℝ} (hτ : τ ∈ I)
    (hbox : ∀ m α v u, IsBoxSmooth p 0 (fun X y => c m α τ X y v u))
    (hjet0 : ∀ i, schurCellL2Jet π I i (c 0) = 0) (s : ℝ≥0∞)
    (hjet : ∀ i, i ≤ p → ∀ m, schurCellL2Jet π I i (c m) ≤ s)
    (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ : ℝ) (hρ : 0 < ρ)
    (hF : ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * τ) x k)) :
    ∫⁻ X in slowCell ρ, ∑ v, ENNReal.ofReal (π v)⁻¹ *
        scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X
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
  have hpt := fun X => lift_scalJet_le π hπ I n p c (coarseField Fc ℓ ρ) hτ hbox hjet0 s hjet ha X
  have hq : ∀ q ∈ Finset.Icc 1 (p + n), ∫⁻ X in slowCell ρ, ∑ u, ENNReal.ofReal (π u)⁻¹ *
      ‖iteratedFDeriv ℝ q (fun X' => coarseField Fc ℓ ρ τ X' u) X‖ₑ ^ 2 ≤
      ENNReal.ofReal (ρ⁻¹ ^ 2 * coarseConst q) * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
    intro q hqI
    obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.1 hqI
    refine (lintegral_slowCell_coarseJet_le π Fc ℓ ρ τ hρ (by omega) hF).trans ?_
    refine le_of_eq (congrArg (· * _) (congrArg ENNReal.ofReal ?_))
    unfold coarseConst; ring
  calc ∫⁻ X in slowCell ρ, ∑ v, ENNReal.ofReal (π v)⁻¹ *
        scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X
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

/-! Coarse flux bound: the sampled cleanup flux and remainder of the cleanup chain of one lift
action of the coarse field, bounded by the flux density at the physical time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The per-degree weight `J_{n,p} = liftJetConst · ∑_q coarseConst`. -/
def jetWeight (n p : ℕ) : ℝ := liftJetConst n p * ∑ q ∈ Finset.Icc 1 (p + n), coarseConst q

theorem jetWeight_nonneg (n p : ℕ) : 0 ≤ jetWeight n p :=
  mul_nonneg (liftJetConst_nonneg n p) (Finset.sum_nonneg fun q _ => coarseConst_nonneg q)

/-- The constant of the sampled cleanup flux of one degree. -/
def fluxChainConst (n A : ℕ) : ℝ := 8 * (A : ℝ) ^ 2 * ∑ p ∈ Finset.range (A + 2), jetWeight n p

/-- The constant of the sampled cleanup remainder of one degree. -/
def remChainConst (n A : ℕ) : ℝ := 16 * ∑ p ∈ Finset.range (A + 3), jetWeight n p

theorem fluxChainConst_nonneg (n A : ℕ) : 0 ≤ fluxChainConst n A :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ => jetWeight_nonneg n p)

theorem remChainConst_nonneg (n A : ℕ) : 0 ≤ remChainConst n A :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => jetWeight_nonneg n p)

theorem vecJet_zero_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℕ) (X : Vec 2) :
    vecJet (fun (_ _ : Vec 2) (_ : Fin 2) => (0 : E)) p X = 0 := by
  unfold vecJet
  refine Finset.sum_eq_zero fun β _ => ?_
  simp [orderedDerivative_const_zero]

/-- The data of one degree at one cell time. -/
structure DegreeData (π : ι → ℝ) (I : Set ℝ) (A sZ n kres : ℕ) (c : LiftCoeff ι h)
    (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ e τ : ℝ) (s : ℝ≥0∞)
    (V : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) : Prop where
  mass_pos : ∀ v, 0 < π v
  τ_mem : τ ∈ I
  ρ_pos : 0 < ρ
  e_pos : 0 < e
  e_le : e ≤ ρ
  e_inv : ∃ M : ℕ, e⁻¹ = (M : ℝ)
  hA : 1 ≤ A
  hZ : 1 ≤ sZ
  order : A + 2 + n + 1 ≤ kres
  box : ∀ m α v u, IsBoxSmooth (A + 2) 0 (fun X y => c m α τ X y v u)
  jet0 : ∀ i, schurCellL2Jet π I i (c 0) = 0
  jet : ∀ i, i ≤ A + 2 → ∀ m, schurCellL2Jet π I i (c m) ≤ s
  smooth : ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * τ) x k)
  chain : IsCleanupChain (A + 2) sZ A (liftApply n c (coarseField Fc ℓ ρ) τ)
    (fun _ _ _ => 0) V

namespace DegreeData

variable {π : ι → ℝ} {I : Set ℝ} {A sZ n kres : ℕ} {c : LiftCoeff ι h}
  {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e τ : ℝ} {s : ℝ≥0∞}
  {V : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem slow_f (hd : DegreeData π I A sZ n kres c Fc ℓ ρ e τ s V) :
    IsSlowSmooth (A + 2) (liftApply n c (coarseField Fc ℓ ρ) τ) := by
  have hF' : ∀ k, ContDiff ℝ (((A + 2) + n + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * τ) x k) :=
    fun k => (hd.smooth k).of_le (by exact_mod_cast (by have := hd.order; omega))
  exact isSlowSmooth_liftApply n (A + 2) c (coarseField Fc ℓ ρ) τ
    (fun m α v u => (hd.box m α v u).isSlowSmooth)
    (contDiff_coarseField τ hF')

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The chain projected on one component. -/
theorem chain_component (hd : DegreeData π I A sZ n kres c Fc ℓ ρ e τ s V) (v : ι) :
    IsCleanupChain (A + 2) sZ A (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v)
      (fun _ _ _ => (0 : h v)) (fun j X y k => V j X y k v) :=
  IsCleanupChain.clm_comp (by omega) hd.hZ (IsSlowSmooth.zero) hd.chain
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)

/-- The sampled cleanup flux of one degree. -/
theorem flux_bound (hd : DegreeData π I A sZ n kres c Fc ℓ ρ e τ s V) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • V j (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2
      ≤ ENNReal.ofReal (fluxChainConst n A) * s ^ 2 * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
  obtain ⟨M, hM⟩ := hd.e_inv
  have hv : ∀ v, ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • V j (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2 ≤
      ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 2),
        ∫⁻ X in slowCell ρ, scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X := by
    intro v
    have hf0 : IsSlowSmooth (A + 2) (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) :=
      hd.slow_f.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
    have := cleanupFlux_density_le (E := h v) (F₀ := fun _ _ _ => (0 : h v)) hd.hZ
      (by omega : A + 1 ≤ A + 2) (IsSlowSmooth.zero) (fun X _ _ => rfl) hf0 (hd.chain_component v) hd.ρ_pos hd.e_pos hd.e_le
      M hM
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    refine lintegral_congr fun X => ?_
    unfold pairJet
    rw [vecJet_zero_fun, zero_add]
  have hp : ∀ p ∈ Finset.range (A + 2), ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
      scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X ≤
      ENNReal.ofReal (ρ⁻¹ ^ 2 * jetWeight n p) * s ^ 2 * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
    intro p hpm
    have hpA : p ≤ A + 2 := by have := Finset.mem_range.1 hpm; omega
    have hbox : ∀ m α v u, IsBoxSmooth p 0 (fun X y => c m α τ X y v u) := fun m α v u =>
      BoundTail.isBoxSmooth_slow_zero (hd.box m α v u) hpA
    have hbox' : ∀ m α v u, IsBoxSmooth (A + 2) 0 (fun X y => c m α τ X y v u) := hd.box
    have key := slowCell_scalJet_le π hd.mass_pos I n p kres (by have := hd.order; omega) c
      hd.τ_mem (fun m α v u => BoundTail.isBoxSmooth_slow_zero (hd.box m α v u) hpA) hd.jet0 s
      (fun i hi m => hd.jet i (by omega) m) Fc ℓ ρ hd.ρ_pos hd.smooth
    refine le_trans ?_ key
    simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact sum_lintegral_le_lintegral_sum _ _
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • V j (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) *
          ∑ p ∈ Finset.range (A + 2), ∫⁻ X in slowCell ρ,
            scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X) :=
        Finset.sum_le_sum fun v _ => by gcongr; exact hv v
    _ = ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 2), ∑ v,
          ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
            scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 2),
          ENNReal.ofReal (ρ⁻¹ ^ 2 * jetWeight n p) * s ^ 2 *
            fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
        gcongr with p hpm
        exact hp p hpm
    _ = _ := by
        have hρ2 : ρ ^ 2 * ρ⁻¹ ^ 2 = 1 := by
          have := hd.ρ_pos.ne'
          field_simp
        have e1 : ∀ p, ENNReal.ofReal (8 * (A : ℝ) ^ 2 * ρ ^ 2) *
            ENNReal.ofReal (ρ⁻¹ ^ 2 * jetWeight n p) =
            ENNReal.ofReal (8 * (A : ℝ) ^ 2 * jetWeight n p) := fun p => by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          calc 8 * (A : ℝ) ^ 2 * ρ ^ 2 * (ρ⁻¹ ^ 2 * jetWeight n p)
              = 8 * (A : ℝ) ^ 2 * (ρ ^ 2 * ρ⁻¹ ^ 2) * jetWeight n p := by ring
            _ = _ := by rw [hρ2, mul_one]
        have hsum : ENNReal.ofReal (fluxChainConst n A) =
            ∑ p ∈ Finset.range (A + 2), ENNReal.ofReal (8 * (A : ℝ) ^ 2 * jetWeight n p) := by
          unfold fluxChainConst
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun p _ =>
            mul_nonneg (by positivity) (jetWeight_nonneg n p)]
        rw [hsum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← e1 p]
        ring

/-- The sampled cleanup remainder of one degree. -/
theorem rem_bound (hd : DegreeData π I A sZ n kres c Fc ℓ ρ e τ s V) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖cleanupSource V A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (remChainConst n A) * s ^ 2 * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
  obtain ⟨M, hM⟩ := hd.e_inv
  have hslowV : ∀ j, j < A → IsSlowSmooth (A + 2) (V j) :=
    IsCleanupChain.isSlowSmooth (IsSlowSmooth.zero (F := Fin 2 → ∀ i, h i)) hd.chain
  have hv : ∀ v, ∫⁻ x in AVenhance.unitCube, ‖cleanupSource V A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2 ≤
      ENNReal.ofReal (16 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 3),
        ∫⁻ X in slowCell ρ, scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X := by
    intro v
    have hf0 : IsSlowSmooth (A + 2) (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) :=
      hd.slow_f.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
    have := cleanupRemainder_density_le (E := h v) (F₀ := fun _ _ _ => (0 : h v)) hd.hZ hd.hA
      le_rfl (IsSlowSmooth.zero) (fun X _ _ => rfl) hf0 (hd.chain_component v) hd.ρ_pos hd.e_pos
      hd.e_le M hM
    have hcomm := cleanupSource_clm_comp (sX := A + 2) (by omega)
      (V := V) (j := A) (hslowV (A - 1) (by have := hd.hA; omega)) (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · refine lintegral_congr fun x => ?_
      have := congrFun (congrFun hcomm (ρ⁻¹ • x)) (e⁻¹ • x)
      exact congrArg (fun w => ‖w‖ₑ ^ 2) this.symm
    · congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      refine lintegral_congr fun X => ?_
      unfold pairJet
      rw [vecJet_zero_fun, zero_add]
  have hp : ∀ p ∈ Finset.range (A + 3), ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
      scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X ≤
      ENNReal.ofReal (ρ⁻¹ ^ 2 * jetWeight n p) * s ^ 2 * fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
    intro p hpm
    have hpA : p ≤ A + 2 := by have := Finset.mem_range.1 hpm; omega
    have key := slowCell_scalJet_le π hd.mass_pos I n p kres (by have := hd.order; omega) c
      hd.τ_mem (fun m α v u => BoundTail.isBoxSmooth_slow_zero (hd.box m α v u) hpA) hd.jet0 s
      (fun i hi m => hd.jet i (by omega) m) Fc ℓ ρ hd.ρ_pos hd.smooth
    refine le_trans ?_ key
    simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact sum_lintegral_le_lintegral_sum _ _
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖cleanupSource V A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (16 * ρ ^ 2) *
          ∑ p ∈ Finset.range (A + 3), ∫⁻ X in slowCell ρ,
            scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X) :=
        Finset.sum_le_sum fun v _ => by gcongr; exact hv v
    _ = ENNReal.ofReal (16 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 3), ∑ v,
          ENNReal.ofReal (π v)⁻¹ * ∫⁻ X in slowCell ρ,
            scalJet (fun X y => liftApply n c (coarseField Fc ℓ ρ) τ X y v) p X := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ ENNReal.ofReal (16 * ρ ^ 2) * ∑ p ∈ Finset.range (A + 3),
          ENNReal.ofReal (ρ⁻¹ ^ 2 * jetWeight n p) * s ^ 2 *
            fluxDensity ρ kres π Fc (ℓ ^ 2 * τ) := by
        gcongr with p hpm
        exact hp p hpm
    _ = _ := by
        have hρ2 : ρ ^ 2 * ρ⁻¹ ^ 2 = 1 := by
          have := hd.ρ_pos.ne'
          field_simp
        have e1 : ∀ p, ENNReal.ofReal (16 * ρ ^ 2) *
            ENNReal.ofReal (ρ⁻¹ ^ 2 * jetWeight n p) =
            ENNReal.ofReal (16 * jetWeight n p) := fun p => by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          calc 16 * ρ ^ 2 * (ρ⁻¹ ^ 2 * jetWeight n p)
              = 16 * (ρ ^ 2 * ρ⁻¹ ^ 2) * jetWeight n p := by ring
            _ = _ := by rw [hρ2, mul_one]
        have hsum : ENNReal.ofReal (remChainConst n A) =
            ∑ p ∈ Finset.range (A + 3), ENNReal.ofReal (16 * jetWeight n p) := by
          unfold remChainConst
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun p _ =>
            mul_nonneg (by positivity) (jetWeight_nonneg n p)]
        rw [hsum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← e1 p]
        ring

end DegreeData
end

/-! Coarse flux bound: the pointwise-in-time bounds of the flux and scalar residual densities of
the coarse flux presentation by the flux density `∑_v π_v⁻¹ ∑_k ‖F_c‖²_{ρ,k}` at the same time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The degree data at one cell time for every degree `1 ≤ n ≤ N`. -/
structure TimeData (π : ι → ℝ) (I : Set ℝ) (A sZ N kres : ℕ) (c : ℕ → LiftCoeff ι h)
    (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ e εc τ : ℝ) (s : ℝ≥0∞)
    (V : ℕ → ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) : Prop where
  deg : ∀ n ∈ Finset.Icc 1 N, DegreeData π I A sZ n kres (c n) Fc ℓ ρ e τ s (V n)
  ε_nonneg : 0 ≤ εc
  ε_le : εc ≤ 1
  smooth : ∀ k, ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => Fc (ℓ ^ 2 * τ) x k)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- The continuity of the sampled cleanup flux term. -/
theorem continuous_cleanupTerm {sX A : ℕ} {W : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hW : ∀ j, j < A → IsSlowSmooth sX (W j)) {ρ e : ℝ} (k : Fin 2) (v : ι) :
    Continuous fun x : Vec 2 => ∑ j ∈ Finset.range A, (e / ρ) ^ j • W j (ρ⁻¹ • x) (e⁻¹ • x) k v := by
  refine continuous_finsetSum _ fun j hj => ?_
  refine Continuous.const_smul ?_ _
  have hc : Continuous fun x : Vec 2 => W j (ρ⁻¹ • x) (e⁻¹ • x) :=
    (hW j (Finset.mem_range.1 hj)).continuous_uncurry.comp
      ((continuous_const_smul _).prodMk (continuous_const_smul _))
  exact (continuous_apply v).comp ((continuous_apply k).comp hc)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem flux_eval (hh : ℕ) (Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (ℓ ρ e εc t τ : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (A N : ℕ)
    (x : Vec 2) (k : Fin 2) (v : ι) :
    ((if hh = 0 then Fc t x k else 0) + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
        εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x k) v =
      (if hh = 0 then Fc t x k v else 0) + (ρ⁻¹ * e) • ∑ n ∈ Finset.Icc 1 N, εc ^ n •
        ∑ j ∈ Finset.range A, (e / ρ) ^ j • Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v := by
  have : ∀ n, cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x k v =
      e • ∑ j ∈ Finset.range A, (e / ρ) ^ j • Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v := by
    intro n
    simp only [cleanupFlux, diagSample, hτt, Pi.smul_apply, Finset.sum_apply]
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, this]
  congr 1
  · split_ifs <;> simp
  · rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [smul_smul]
    congr 1
    ring

theorem ite_enorm_sq {E : Type*} [NormedAddCommGroup E] (p : Prop) [Decidable p] (a : E) :
    ‖(if p then a else 0)‖ₑ ^ 2 = if p then ‖a‖ₑ ^ 2 else 0 := by
  split_ifs <;> simp

theorem lintegral_bound_split (P : Prop) [Decidable P] (S : Finset ℕ) (a : Vec 2 → ℝ≥0∞)
    (ha : Measurable a) (w : ℕ → ℝ≥0∞) (b : ℕ → Vec 2 → ℝ≥0∞) (hb : ∀ n ∈ S, Measurable (b n))
    (U : Vec 2 → ℝ≥0∞)
    (hU : ∀ x, U x ≤ 2 * (if P then a x else 0) + ∑ n ∈ S, w n * b n x) :
    ∫⁻ x in AVenhance.unitCube, U x ≤
      2 * (if P then ∫⁻ x in AVenhance.unitCube, a x else 0) +
        ∑ n ∈ S, w n * ∫⁻ x in AVenhance.unitCube, b n x := by
  have hm1 : Measurable fun x => 2 * (if P then a x else 0) := by
    by_cases hP : P
    · simp only [hP, ite_true]; exact ha.const_mul _
    · simp only [hP, ite_false]; exact measurable_const
  calc ∫⁻ x in AVenhance.unitCube, U x
      ≤ ∫⁻ x in AVenhance.unitCube, (2 * (if P then a x else 0) + ∑ n ∈ S, w n * b n x) :=
        lintegral_mono hU
    _ = (∫⁻ x in AVenhance.unitCube, 2 * (if P then a x else 0)) +
          ∫⁻ x in AVenhance.unitCube, ∑ n ∈ S, w n * b n x := lintegral_add_left hm1 _
    _ = _ := by
        congr 1
        · rw [lintegral_const_mul' _ _ (by simp)]
          congr 1
          by_cases hP : P <;> simp [hP]
        · rw [lintegral_finsetSum _ fun n hn => (hb n hn).const_mul _]
          exact Finset.sum_congr rfl fun n hn => lintegral_const_mul _ (hb n hn)

/-- The pointwise-in-time bound of the flux residual density. -/
theorem flux_time_bound {π : ι → ℝ} {I : Set ℝ} {A sZ N kres : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : TimeData π I A sZ N kres c Fc ℓ ρ e εc τ s (fun n j => Vn n j τ)) (hh : ℕ) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hℓτ : ℓ ^ 2 * τ = t) (θ : ℝ) (hs : s = ENNReal.ofReal θ)
    (hθ : 0 ≤ θ) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖((if hh = 0 then Fc t x k else 0) + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
          εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x k) v‖ₑ ^ 2
      ≤ ENNReal.ofReal ((if hh = 0 then 2 else 0) + 2 * N * (e / ρ) ^ 2 * εc ^ 2 * θ ^ 2 *
          ∑ n ∈ Finset.Icc 1 N, fluxChainConst n A) * fluxDensity ρ kres π Fc t := by
  classical
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  have hpt : ∀ (v : ι) (x : Vec 2), ∑ k : Fin 2,
      ‖((if hh = 0 then Fc t x k else 0) + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
        εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x k) v‖ₑ ^ 2 ≤
      2 * (if hh = 0 then ∑ k : Fin 2, ‖Fc t x k v‖ₑ ^ 2 else 0) +
        ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) *
          ∑ k : Fin 2, ‖∑ j ∈ Finset.range A, (e / ρ) ^ j •
            Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2 := by
    intro v x
    calc ∑ k : Fin 2, ‖((if hh = 0 then Fc t x k else 0) + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
          εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x k) v‖ₑ ^ 2
        = ∑ k : Fin 2, ‖(if hh = 0 then Fc t x k v else 0) + (ρ⁻¹ * e) •
            ∑ n ∈ Finset.Icc 1 N, εc ^ n • ∑ j ∈ Finset.range A, (e / ρ) ^ j •
              Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [flux_eval hh Fc ℓ ρ e εc t τ hτt Vn A N x k v]
      _ ≤ ∑ k : Fin 2, (2 * ‖(if hh = 0 then Fc t x k v else 0)‖ₑ ^ 2 +
            ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * ((Finset.Icc 1 N).card : ℝ) *
              (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) * ‖∑ j ∈ Finset.range A, (e / ρ) ^ j •
                Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2) :=
          Finset.sum_le_sum fun k _ => enorm_sq_add_sum_smul_le (Finset.Icc 1 N) _ (ρ⁻¹ * e)
            (fun n => εc ^ n) (fun n => ∑ j ∈ Finset.range A, (e / ρ) ^ j •
              Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v)
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcard, Finset.sum_comm]
          congr 1
          · simp only [ite_enorm_sq]
            split_ifs <;> simp
          · refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
  have hslowV : ∀ n ∈ Finset.Icc 1 N, ∀ j, j < A → IsSlowSmooth (A + 2) (Vn n j τ) := fun n hn =>
    IsCleanupChain.isSlowSmooth (IsSlowSmooth.zero (F := Fin 2 → ∀ i, h i)) (hT.deg n hn).chain
  have hFc : ∀ (v : ι) (k : Fin 2), Continuous fun x => Fc t x k v := fun v k => by
    have := (hT.smooth k).continuous
    rw [hℓτ] at this
    exact (continuous_apply v).comp this
  have hfsq : ∀ (v : ι), ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖Fc t x k v‖ₑ ^ 2 ≤
      ∑ k : Fin 2, classicalFactorialSq ρ kres (fun x => Fc t x k v) := by
    intro v
    rw [lintegral_finsetSum _ fun k _ => ((hFc v k).enorm.measurable).pow_const 2]
    exact Finset.sum_le_sum fun k _ => lintegral_sq_le_classicalFactorialSq ρ kres _
  have hint : ∀ v : ι, ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖((if hh = 0 then Fc t x k else 0) + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
          εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x k) v‖ₑ ^ 2 ≤
      2 * (if hh = 0 then ∑ k : Fin 2, classicalFactorialSq ρ kres (fun x => Fc t x k v)
        else 0) + ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) *
          ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖∑ j ∈ Finset.range A, (e / ρ) ^ j •
            Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2 := by
    intro v
    refine (lintegral_bound_split (hh = 0) (Finset.Icc 1 N)
      (fun x => ∑ k : Fin 2, ‖Fc t x k v‖ₑ ^ 2)
      (Finset.measurable_sum _ fun k _ => ((hFc v k).enorm.measurable).pow_const 2)
      (fun n => ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2))
      (fun n x => ∑ k : Fin 2, ‖∑ j ∈ Finset.range A, (e / ρ) ^ j •
            Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2)
      (fun n hn => Finset.measurable_sum _ fun k _ =>
        ((continuous_cleanupTerm (hslowV n hn) k v).enorm.measurable).pow_const 2) _
      (hpt v)).trans ?_
    gcongr
    split_ifs
    · exact hfsq v
    · exact le_rfl
  set G : ℝ≥0∞ := fluxDensity ρ kres π Fc t with hG
  set ind : ℝ≥0∞ := if hh = 0 then 1 else 0 with hind
  have hite : ∀ X : ℝ≥0∞, (if hh = 0 then X else 0) = ind * X := fun X => by
    simp only [hind]; split_ifs <;> simp
  have hdeg : ∀ n ∈ Finset.Icc 1 N, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
      ∑ k : Fin 2, ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2
      ≤ ENNReal.ofReal (fluxChainConst n A) * ENNReal.ofReal (θ ^ 2) * G := by
    intro n hn
    have := (hT.deg n hn).flux_bound
    rw [hs, ← ENNReal.ofReal_pow hθ, hℓτ] at this
    exact this
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
        ‖((if hh = 0 then Fc t x k else 0) + ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N,
          εc ^ n • cleanupFlux (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x k) v‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (2 * (ind * ∑ k : Fin 2,
          classicalFactorialSq ρ kres (fun x => Fc t x k v)) + ∑ n ∈ Finset.Icc 1 N,
          ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) * ∫⁻ x in AVenhance.unitCube,
            ∑ k : Fin 2, ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2) := by
        refine Finset.sum_le_sum fun v _ => ?_
        gcongr
        exact (hint v).trans_eq (by rw [hite])
    _ = 2 * (ind * G) + ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * (εc ^ n) ^ 2) *
          ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2,
            ‖∑ j ∈ Finset.range A, (e / ρ) ^ j • Vn n j τ (ρ⁻¹ • x) (e⁻¹ • x) k v‖ₑ ^ 2 := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · simp only [hG, fluxDensity, Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring_nf
        · simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ 2 * (ind * G) + ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * εc ^ 2) *
          (ENNReal.ofReal (fluxChainConst n A) * ENNReal.ofReal (θ ^ 2) * G) := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun n hn => ?_)
        have hn1 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
        have h1 : εc ^ n ≤ εc := pow_le_of_le_one hT.ε_nonneg hT.ε_le hn1
        have h2 : (εc ^ n) ^ 2 ≤ εc ^ 2 := pow_le_pow_left₀ (pow_nonneg hT.ε_nonneg n) h1 2
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left h2 (by positivity))) (hdeg n hn)
    _ = _ := by
        have hK : ENNReal.ofReal ((if hh = 0 then 2 else 0) + 2 * N * (e / ρ) ^ 2 * εc ^ 2 *
            θ ^ 2 * ∑ n ∈ Finset.Icc 1 N, fluxChainConst n A) =
            2 * ind + ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (2 * N * (ρ⁻¹ * e) ^ 2 * εc ^ 2) *
              (ENNReal.ofReal (fluxChainConst n A) * ENNReal.ofReal (θ ^ 2)) := by
          have hnn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, fluxChainConst n A :=
            Finset.sum_nonneg fun n _ => fluxChainConst_nonneg n A
          rw [ENNReal.ofReal_add (by split_ifs <;> norm_num) (by positivity)]
          congr 1
          · simp only [hind]; split_ifs <;> simp
          · rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun n _ =>
              mul_nonneg (by positivity) (fluxChainConst_nonneg n A)]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [← ENNReal.ofReal_mul (fluxChainConst_nonneg n A), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [div_eq_inv_mul]; ring
        rw [hK, add_mul, Finset.sum_mul]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun n _ => by ring

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem continuous_remTerm {A : ℕ} {W : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hW : IsSlowSmooth (A + 2) (W (A - 1))) {ρ e : ℝ} (v : ι) :
    Continuous fun x : Vec 2 => cleanupSource W A (ρ⁻¹ • x) (e⁻¹ • x) v := by
  have hs : IsSlowSmooth (A + 1) (cleanupSource W A) := isSlowSmooth_cleanupSource hW
  have hc : Continuous fun x : Vec 2 => cleanupSource W A (ρ⁻¹ • x) (e⁻¹ • x) :=
    hs.continuous_uncurry.comp ((continuous_const_smul _).prodMk (continuous_const_smul _))
  exact (continuous_apply v).comp hc

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem rem_eval (ℓ ρ e εc t τ : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (A N : ℕ)
    (x : Vec 2) (v : ι) :
    (ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x) v =
      (ρ⁻¹ * (e / ρ) ^ A) • ∑ n ∈ Finset.Icc 1 N, εc ^ n •
        cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v := by
  have : ∀ n, cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x v =
      (e / ρ) ^ A • cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v := by
    intro n
    simp only [cleanupRemainder, diagSample, hτt, Pi.smul_apply]
  simp only [Pi.smul_apply, Finset.sum_apply, this]
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [smul_smul]
  congr 1
  ring

/-- The pointwise-in-time bound of the scalar residual density. -/
theorem rem_time_bound {π : ι → ℝ} {I : Set ℝ} {A sZ N kres : ℕ} {c : ℕ → LiftCoeff ι h}
    {Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {ℓ ρ e εc τ : ℝ} {s : ℝ≥0∞}
    {Vn : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hT : TimeData π I A sZ N kres c Fc ℓ ρ e εc τ s (fun n j => Vn n j τ)) (t : ℝ)
    (hτt : (ℓ ^ 2)⁻¹ * t = τ) (hℓτ : ℓ ^ 2 * τ = t) (θ : ℝ) (hs : s = ENNReal.ofReal θ)
    (hθ : 0 ≤ θ) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2 * θ ^ 2 *
          ∑ n ∈ Finset.Icc 1 N, remChainConst n A) * fluxDensity ρ kres π Fc t := by
  classical
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  have hslowV : ∀ n ∈ Finset.Icc 1 N, ∀ j, j < A → IsSlowSmooth (A + 2) (Vn n j τ) := fun n hn =>
    IsCleanupChain.isSlowSmooth (IsSlowSmooth.zero (F := Fin 2 → ∀ i, h i)) (hT.deg n hn).chain
  have hpt : ∀ (v : ι) (x : Vec 2),
      ‖(ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x) v‖ₑ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (εc ^ n) ^ 2) *
        ‖cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2 := by
    intro v x
    rw [rem_eval ℓ ρ e εc t τ hτt Vn A N x v]
    have := enorm_sq_sum_smul_le (Finset.Icc 1 N) (ρ⁻¹ * (e / ρ) ^ A) (fun n => εc ^ n)
      (fun n => cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v)
    rwa [hcard] at this
  have hmeas : ∀ (v : ι), ∀ n ∈ Finset.Icc 1 N, Measurable fun x : Vec 2 =>
      ‖cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2 := fun v n hn =>
    ((continuous_remTerm (hslowV n hn (A - 1) (by have := (hT.deg n hn).hA; omega))
      v).enorm.measurable).pow_const 2
  have hint : ∀ v : ι, ∫⁻ x in AVenhance.unitCube,
      ‖(ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x) v‖ₑ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (εc ^ n) ^ 2) *
        ∫⁻ x in AVenhance.unitCube,
          ‖cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2 := by
    intro v
    refine (lintegral_mono (hpt v)).trans (le_of_eq ?_)
    rw [lintegral_finsetSum _ fun n hn => (hmeas v n hn).const_mul _]
    exact Finset.sum_congr rfl fun n hn => lintegral_const_mul _ (hmeas v n hn)
  set G : ℝ≥0∞ := fluxDensity ρ kres π Fc t with hG
  have hdeg : ∀ n ∈ Finset.Icc 1 N, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
      ‖cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2
      ≤ ENNReal.ofReal (remChainConst n A) * ENNReal.ofReal (θ ^ 2) * G := by
    intro n hn
    have := (hT.deg n hn).rem_bound
    rw [hs, ← ENNReal.ofReal_pow hθ, hℓτ] at this
    exact this
  calc ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(ρ⁻¹ • ∑ n ∈ Finset.Icc 1 N, εc ^ n • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e A (Vn n) t x) v‖ₑ ^ 2
      ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
          ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (εc ^ n) ^ 2) *
            ∫⁻ x in AVenhance.unitCube,
              ‖cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2 :=
        Finset.sum_le_sum fun v _ => by gcongr; exact hint v
    _ = ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * (εc ^ n) ^ 2) *
          ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
            ‖cleanupSource (fun j => Vn n j τ) A (ρ⁻¹ • x) (e⁻¹ • x) v‖ₑ ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun v _ => by ring_nf
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (N * (ρ⁻¹ * (e / ρ) ^ A) ^ 2 * εc ^ 2) *
          (ENNReal.ofReal (remChainConst n A) * ENNReal.ofReal (θ ^ 2) * G) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
        have h1 : εc ^ n ≤ εc := pow_le_of_le_one hT.ε_nonneg hT.ε_le hn1
        have h2 : (εc ^ n) ^ 2 ≤ εc ^ 2 := pow_le_pow_left₀ (pow_nonneg hT.ε_nonneg n) h1 2
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left h2 (by positivity))) (hdeg n hn)
    _ = _ := by
        have hnn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, remChainConst n A :=
          Finset.sum_nonneg fun n _ => remChainConst_nonneg n A
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun n _ =>
          mul_nonneg (by positivity) (remChainConst_nonneg n A), Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        have e3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → ENNReal.ofReal a *
            (ENNReal.ofReal b * ENNReal.ofReal c * G) = ENNReal.ofReal (a * b * c) * G :=
          fun a b c ha hb hc => by
            rw [ENNReal.ofReal_mul (mul_nonneg ha hb), ENNReal.ofReal_mul ha]; ring
        rw [e3 _ _ _ (by positivity) (remChainConst_nonneg n A) (by positivity)]
        congr 2
        ring
end

end AVRegularity.CoarseFluxBound
end
end
