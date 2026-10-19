-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.TorusDist
public import AVenhance.Statements.Roots.UnitCube
public import AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Prod

/-! # Riesz rows of a positive Hölder-smoothing operator

Steps 1 and 2 of the proof of Lemma 8.4 of the paper. Let `P : L²(𝕋²) → (Vec 2 → ℝ)` be linear
with `|P f x| ≤ C ‖f‖` and `|P f x - P f y| ≤ C d(x,y)^s ‖f‖`, `L²(𝕋²) = Lp ℝ 2 (volume.restrict
unitCube)`. The rows are any family `k : Vec 2 → L²(𝕋²)` with `⟪k x, f⟫ = P f x`
(`exists_riesz_rows`, by the Riesz representation theorem). For them:

* `norm_row_le`, `norm_row_sub_le`: `‖k_x‖ ≤ C`, `‖k_x - k_y‖ ≤ C d(x,y)^s`; hence
  `continuous_rows` and the periodicity `rows_add_latticeShift`;
* positivity `rows_ae_nonneg`: `k_x ≥ 0` a.e.; `P 1 = 1` gives `∫ k_x = 1` and `‖k_x‖ ≥ 1`;
* `integral_rows_eq_const_one`: the Bochner mean `∫_{𝕋²} k_x dx = 1` in `L²`;
* for `H(x,y) = ⟪k_x, k_y⟫`: `integral_inner_rows_right`, `inner_rows_nonneg`,
  `half_le_inner_rows`;
* `inner_integral_smul_rows`: `P^* g = ∫ g(x) k_x dx`, that is
  `⟪∫ g(x) k_x dx, f⟫ = ∫ g · P f`;
* `integral_sq_sub_norm_sq_integral_smul_rows`, display (8.18) of the paper:
  `‖g‖² - ‖P^* g‖² = ½ ∬ H(x,y) |g(x) - g(y)|² dx dy`.

The adjoint formula and (8.18) are stated for continuous `g` (the case used, `g = P f`). -/

public section

open MeasureTheory Homogenization AVenhance
open scoped InnerProductSpace

namespace AVRegularity.Applications.Dissipation

/-- `L²(𝕋²)`, the carrier of the operator lemma. -/
local notation "L2T" => Lp ℝ 2 (volume.restrict unitCube : Measure (Vec 2))

private theorem volume_unitCube_rows : volume (unitCube : Set (Vec 2)) = 1 := by
  rw [unitCube, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- The unit cell is a probability space. -/
local instance rowsProbCube : IsProbabilityMeasure (volume.restrict unitCube : Measure (Vec 2)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitCube_rows⟩

/-! ### Integrability on the cell -/

private theorem closedCube_isCompact :
    IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
  isCompact_univ_pi fun _ => isCompact_Icc

private theorem unitCube_subset_closedCube :
    unitCube ⊆ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 :=
  Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self

/-- A continuous function with values in a normed space is integrable on the unit cell. -/
theorem integrable_unitCube_of_continuous_normed {E : Type*} [NormedAddCommGroup E]
    {f : Vec 2 → E} (hf : Continuous f) : Integrable f (volume.restrict unitCube) :=
  (hf.continuousOn.integrableOn_compact closedCube_isCompact).mono_set unitCube_subset_closedCube

/-- A continuous function on the product of two cells is integrable. -/
theorem integrable_unitCube_prod_of_continuous {F : Vec 2 × Vec 2 → ℝ} (hF : Continuous F) :
    Integrable F ((volume.restrict unitCube).prod (volume.restrict unitCube)) := by
  rw [Measure.prod_restrict]
  exact (hF.continuousOn.integrableOn_compact (closedCube_isCompact.prod closedCube_isCompact))
    |>.mono_set (Set.prod_mono unitCube_subset_closedCube unitCube_subset_closedCube)

/-! ### The torus distance -/

private theorem torusDist_nonneg_rows (x y : Vec 2) : 0 ≤ torusDist x y :=
  Real.iInf_nonneg fun _ => Real.sqrt_nonneg _

private theorem torusDist_bddBelow_rows (x y : Vec 2) :
    BddBelow (Set.range fun n : Fin 2 → ℤ => √(vecNormSq (x - y - latticeShift n))) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact Real.sqrt_nonneg _⟩

/-- The torus distance is at most the Euclidean distance. -/
theorem torusDist_le_sqrt_vecNormSq (x y : Vec 2) : torusDist x y ≤ √(vecNormSq (x - y)) := by
  have h := ciInf_le (torusDist_bddBelow_rows x y) 0
  have h0 : latticeShift (0 : Fin 2 → ℤ) = 0 := by funext i; simp [latticeShift]
  rw [h0, sub_zero] at h
  exact h

/-- Lattice translates are at torus distance zero. -/
theorem torusDist_add_latticeShift_self (x : Vec 2) (n : Fin 2 → ℤ) :
    torusDist (x + latticeShift n) x = 0 := by
  refine le_antisymm ?_ (torusDist_nonneg_rows _ _)
  have h := ciInf_le (torusDist_bddBelow_rows (x + latticeShift n) x) n
  have h0 : x + latticeShift n - x - latticeShift n = 0 := by abel
  rw [h0] at h
  refine h.trans_eq ?_
  simp [vecNormSq, vecDot]

/-! ### The Hölder bound and periodicity -/

variable {P : L2T →ₗ[ℝ] (Vec 2 → ℝ)}

/-- The `s`-Hölder bound in the torus distance makes every `P f` periodic. -/
theorem isZ2Periodic_of_torus_holder {s C : ℝ} (hs : 0 < s)
    (hhol : ∀ f x y, |P f x - P f y| ≤ C * torusDist x y ^ s * ‖f‖) (f : L2T) :
    IsZ2Periodic (P f) := by
  intro n x
  have h := hhol f (x + latticeShift n) x
  rw [torusDist_add_latticeShift_self, Real.zero_rpow hs.ne', mul_zero, zero_mul] at h
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

/-! ### Rows -/

/-- The Riesz rows `k_x ∈ L²(𝕋²)` of `P`, with `⟪k_x, f⟫ = P f x`. -/
theorem exists_riesz_rows {C : ℝ} (hsup : ∀ f x, |P f x| ≤ C * ‖f‖) :
    ∃ k : Vec 2 → L2T, ∀ x f, ⟪k x, f⟫_ℝ = P f x := by
  refine ⟨fun x => (InnerProductSpace.toDual ℝ L2T).symm
    (LinearMap.mkContinuous ((LinearMap.proj x).comp P) C fun f => ?_), fun x f => ?_⟩
  · simpa [Real.norm_eq_abs] using hsup f x
  · rw [InnerProductSpace.toDual_symm_apply]
    rfl

section Rows

variable {k : Vec 2 → L2T}

/-- `‖k_x‖ ≤ C`. -/
theorem norm_row_le (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ f x, |P f x| ≤ C * ‖f‖) (x : Vec 2) : ‖k x‖ ≤ C := by
  have h : ‖k x‖ ^ 2 ≤ C * ‖k x‖ := by
    rw [← real_inner_self_eq_norm_sq, hk]
    exact (le_abs_self _).trans (hsup _ _)
  nlinarith [norm_nonneg (k x)]

/-- `‖k_x - k_y‖ ≤ C d(x,y)^s`. -/
theorem norm_row_sub_le (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) {s C : ℝ} (hC : 0 ≤ C)
    (hhol : ∀ f x y, |P f x - P f y| ≤ C * torusDist x y ^ s * ‖f‖) (x y : Vec 2) :
    ‖k x - k y‖ ≤ C * torusDist x y ^ s := by
  have h : ‖k x - k y‖ ^ 2 ≤ C * torusDist x y ^ s * ‖k x - k y‖ := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, hk, hk]
    exact (le_abs_self _).trans (hhol _ _ _)
  have h0 : 0 ≤ C * torusDist x y ^ s :=
    mul_nonneg hC (Real.rpow_nonneg (torusDist_nonneg_rows _ _) _)
  nlinarith [norm_nonneg (k x - k y)]

/-- The rows are periodic: `k_{x+n} = k_x`. -/
theorem rows_add_latticeShift (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) {s C : ℝ} (hs : 0 < s)
    (hhol : ∀ f x y, |P f x - P f y| ≤ C * torusDist x y ^ s * ‖f‖) (x : Vec 2)
    (n : Fin 2 → ℤ) : k (x + latticeShift n) = k x :=
  ext_inner_right ℝ fun f => by rw [hk, hk, isZ2Periodic_of_torus_holder hs hhol f n x]

/-- `x ↦ k_x` is a continuous `L²`-valued map. -/
theorem continuous_rows (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (hhol : ∀ f x y, |P f x - P f y| ≤ C * torusDist x y ^ s * ‖f‖) : Continuous k := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hq : Continuous fun y : Vec 2 => vecNormSq (y - x₀) := by
    simp only [vecNormSq, vecDot, Pi.sub_apply]
    fun_prop
  have hc : Continuous fun y : Vec 2 => C * √(vecNormSq (y - x₀)) ^ s :=
    continuous_const.mul ((Real.continuous_sqrt.comp hq).rpow_const fun _ => Or.inr hs.le)
  have h0 : C * √(vecNormSq (x₀ - x₀)) ^ s = 0 := by
    simp [vecNormSq, vecDot, Real.zero_rpow hs.ne']
  have ht := hc.tendsto x₀
  rw [h0] at ht
  refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) ht
  exact (norm_row_sub_le hk hC hhol y x₀).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (torusDist_nonneg_rows _ _) (torusDist_le_sqrt_vecNormSq y x₀) hs.le) hC)

/-- Positivity of `P` makes every row nonnegative: `k_x ≥ 0` a.e. -/
theorem rows_ae_nonneg (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x)
    (hpos : ∀ f : L2T, (∀ᵐ x ∂(volume.restrict unitCube), 0 ≤ f x) → ∀ x, 0 ≤ P f x)
    (x : Vec 2) : ∀ᵐ y ∂(volume.restrict unitCube), 0 ≤ k x y := by
  have hneg := Lp.coeFn_negPart_eq_max (k x)
  have h1 : 0 ≤ ⟪k x, Lp.negPart (k x)⟫_ℝ := by
    rw [hk]
    exact hpos _ (hneg.mono fun y h => h ▸ le_max_right _ _) x
  have h2 : ⟪k x + Lp.negPart (k x), Lp.negPart (k x)⟫_ℝ = 0 := by
    rw [L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_add (k x) (Lp.negPart (k x)), hneg] with y hy1 hy2
    rw [hy1, Pi.add_apply, hy2, Real.inner_apply, Pi.zero_apply]
    rcases le_total 0 (k x y) with h | h
    · rw [max_eq_right (by linarith)]
      ring
    · rw [max_eq_left (by linarith)]
      ring
  rw [inner_add_left, real_inner_self_eq_norm_sq] at h2
  have hv : Lp.negPart (k x) = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg (Lp.negPart (k x))])
  have hvz : (Lp.negPart (k x) : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] 0 := by
    rw [hv]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [hneg, hvz] with y hy1 hy2
  rw [hy2, Pi.zero_apply] at hy1
  have := le_max_left (-k x y) 0
  linarith

/-- The constant `1` of `L²(𝕋²)` is a.e. `1`. -/
private theorem coeFn_const_one_rows :
    (Lp.const 2 (volume.restrict unitCube) (1 : ℝ) : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube]
      fun _ => 1 :=
  Lp.coeFn_const ..

/-- `P 1 = 1` reads `⟪k_x, 1⟫ = 1`. -/
theorem inner_row_const_one (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x)
    (hone : ∀ f : L2T, (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) →
      ∀ x, P f x = 1) (x : Vec 2) :
    ⟪k x, Lp.const 2 (volume.restrict unitCube) (1 : ℝ)⟫_ℝ = 1 := by
  rw [hk]
  exact hone _ coeFn_const_one_rows x

/-- `∫_{𝕋²} k_x = 1`. -/
theorem integral_row_eq_one (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x)
    (hone : ∀ f : L2T, (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) →
      ∀ x, P f x = 1) (x : Vec 2) : ∫ y in unitCube, k x y = 1 := by
  have h := inner_row_const_one hk hone x
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_const_one_rows] with y hy
  rw [hy, Real.inner_apply, mul_one]

/-- `‖k_x‖ ≥ 1`. -/
theorem one_le_norm_row (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x)
    (hone : ∀ f : L2T, (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) →
      ∀ x, P f x = 1) (x : Vec 2) : 1 ≤ ‖k x‖ := by
  have h1 : ‖Lp.const 2 (volume.restrict unitCube : Measure (Vec 2)) (1 : ℝ)‖ ≤ 1 := by
    refine (Lp.norm_const_le ..).trans ?_
    simp
  calc (1 : ℝ) = ⟪k x, Lp.const 2 (volume.restrict unitCube) (1 : ℝ)⟫_ℝ :=
        (inner_row_const_one hk hone x).symm
    _ ≤ ‖k x‖ * ‖Lp.const 2 (volume.restrict unitCube : Measure (Vec 2)) (1 : ℝ)‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖k x‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖k x‖ := mul_one _

/-- The Bochner mean of the rows is `1`: `∫_{𝕋²} k_x dx = 1` in `L²(𝕋²)`. -/
theorem integral_rows_eq_const_one (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) (hkc : Continuous k)
    (hmass : ∀ f : L2T, ∫ x in unitCube, P f x = ∫ x in unitCube, f x) :
    ∫ x in unitCube, k x = Lp.const 2 (volume.restrict unitCube) (1 : ℝ) := by
  refine ext_inner_left ℝ fun f => ?_
  rw [← integral_inner (integrable_unitCube_of_continuous_normed hkc) f]
  have hfun : (fun x => ⟪f, k x⟫_ℝ) = fun x => P f x := funext fun x => by
    rw [real_inner_comm, hk]
  rw [hfun, hmass, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_const_one_rows] with y hy
  rw [hy, Real.inner_apply, mul_one]

/-- `∫ H(x,y) dy = 1` for `H(x,y) = ⟪k_x, k_y⟫`. -/
theorem integral_inner_rows_right (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) (hkc : Continuous k)
    (hone : ∀ f : L2T, (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) →
      ∀ x, P f x = 1)
    (hmass : ∀ f : L2T, ∫ x in unitCube, P f x = ∫ x in unitCube, f x) (x : Vec 2) :
    ∫ y in unitCube, ⟪k x, k y⟫_ℝ = 1 := by
  rw [integral_inner (integrable_unitCube_of_continuous_normed hkc) (k x),
    integral_rows_eq_const_one hk hkc hmass]
  exact inner_row_const_one hk hone x

/-- `∫ H(x,y) dx = 1`. -/
theorem integral_inner_rows_left (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) (hkc : Continuous k)
    (hone : ∀ f : L2T, (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) →
      ∀ x, P f x = 1)
    (hmass : ∀ f : L2T, ∫ x in unitCube, P f x = ∫ x in unitCube, f x) (y : Vec 2) :
    ∫ x in unitCube, ⟪k x, k y⟫_ℝ = 1 := by
  simp_rw [real_inner_comm (k y)]
  exact integral_inner_rows_right hk hkc hone hmass y

/-- `H(x,y) = ⟪k_x, k_y⟫ ≥ 0`. -/
theorem inner_rows_nonneg (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x)
    (hpos : ∀ f : L2T, (∀ᵐ x ∂(volume.restrict unitCube), 0 ≤ f x) → ∀ x, 0 ≤ P f x)
    (x y : Vec 2) : 0 ≤ ⟪k x, k y⟫_ℝ := by
  rw [hk]
  exact hpos _ (rows_ae_nonneg hk hpos y) x

/-- `H(x,y) ≥ ½` as soon as `C d(x,y)^s ≤ 1`. -/
theorem half_le_inner_rows (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) {s C : ℝ} (hC : 0 ≤ C)
    (hone : ∀ f : L2T, (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) →
      ∀ x, P f x = 1)
    (hhol : ∀ f x y, |P f x - P f y| ≤ C * torusDist x y ^ s * ‖f‖) {x y : Vec 2}
    (hxy : C * torusDist x y ^ s ≤ 1) : 1 / 2 ≤ ⟪k x, k y⟫_ℝ := by
  have h1 := one_le_norm_row hk hone x
  have h2 := one_le_norm_row hk hone y
  have h3 := (norm_row_sub_le hk hC hhol x y).trans hxy
  have h4 := norm_sub_sq_real (k x) (k y)
  nlinarith [norm_nonneg (k x - k y)]

/-! ### The adjoint and the Dirichlet identity -/

/-- `P^* g = ∫ g(x) k_x dx`, i.e. `⟪∫ g(x) k_x dx, f⟫ = ∫ g · P f`. -/
theorem inner_integral_smul_rows (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) (hkc : Continuous k)
    {g : Vec 2 → ℝ} (hg : Continuous g) (f : L2T) :
    ⟪∫ x in unitCube, g x • k x, f⟫_ℝ = ∫ x in unitCube, g x * P f x := by
  rw [real_inner_comm, ← integral_inner (integrable_unitCube_of_continuous_normed
    (f := fun x => g x • k x) (hg.smul hkc)) f]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [real_inner_smul_right, real_inner_comm, hk]

/-- `‖P^* g‖² = ∫∫ g(x) H(x,y) g(y) dy dx`. -/
private theorem norm_sq_integral_smul_rows (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x) (hkc : Continuous k)
    {g : Vec 2 → ℝ} (hg : Continuous g) :
    ‖∫ x in unitCube, g x • k x‖ ^ 2 =
      ∫ x in unitCube, ∫ y in unitCube, g x * (⟪k x, k y⟫_ℝ * g y) := by
  rw [← real_inner_self_eq_norm_sq, inner_integral_smul_rows hk hkc hg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← hk, real_inner_comm, inner_integral_smul_rows hk hkc hg, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [← hk, real_inner_comm (k x)]
  ring

/-- Display (8.18) of the paper: `‖g‖² - ‖P^* g‖² = ½ ∬ H(x,y) |g(x) - g(y)|² dy dx`, `P^* g = ∫ g(x) k_x dx`. -/
theorem integral_sq_sub_norm_sq_integral_smul_rows (hk : ∀ x f, ⟪k x, f⟫_ℝ = P f x)
    (hkc : Continuous k)
    (hone : ∀ f : L2T, (f : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) →
      ∀ x, P f x = 1)
    (hmass : ∀ f : L2T, ∫ x in unitCube, P f x = ∫ x in unitCube, f x)
    {g : Vec 2 → ℝ} (hg : Continuous g) :
    (∫ x in unitCube, g x ^ 2) - ‖∫ x in unitCube, g x • k x‖ ^ 2 =
      1 / 2 * ∫ x in unitCube, ∫ y in unitCube, ⟪k x, k y⟫_ℝ * (g x - g y) ^ 2 := by
  have hH : Continuous fun p : Vec 2 × Vec 2 => ⟪k p.1, k p.2⟫_ℝ :=
    (hkc.comp continuous_fst).inner (hkc.comp continuous_snd)
  have hint1 : ∀ x, Integrable (fun y => ⟪k x, k y⟫_ℝ) (volume.restrict unitCube) := fun x =>
    integrable_unitCube_of_continuous_normed (f := fun y => ⟪k x, k y⟫_ℝ)
      (continuous_const.inner hkc)
  have hint2 : ∀ x, Integrable (fun y => g x * (⟪k x, k y⟫_ℝ * g y))
      (volume.restrict unitCube) := fun x =>
    integrable_unitCube_of_continuous_normed (f := fun y => g x * (⟪k x, k y⟫_ℝ * g y))
      (continuous_const.mul ((continuous_const.inner hkc).mul hg))
  have hint3 : ∀ x, Integrable (fun y => ⟪k x, k y⟫_ℝ * g y ^ 2) (volume.restrict unitCube) :=
    fun x => integrable_unitCube_of_continuous_normed (f := fun y => ⟪k x, k y⟫_ℝ * g y ^ 2)
      ((continuous_const.inner hkc).mul (hg.pow 2))
  have hP2 : Integrable (Function.uncurry fun x y => g x * (⟪k x, k y⟫_ℝ * g y))
      ((volume.restrict unitCube).prod (volume.restrict unitCube)) :=
    integrable_unitCube_prod_of_continuous
      ((hg.comp continuous_fst).mul (hH.mul (hg.comp continuous_snd)))
  have hP3 : Integrable (Function.uncurry fun x y => ⟪k x, k y⟫_ℝ * g y ^ 2)
      ((volume.restrict unitCube).prod (volume.restrict unitCube)) :=
    integrable_unitCube_prod_of_continuous (hH.mul ((hg.comp continuous_snd).pow 2))
  have hinner : ∀ x, ∫ y in unitCube, ⟪k x, k y⟫_ℝ * (g x - g y) ^ 2 =
      g x ^ 2 + ((∫ y in unitCube, ⟪k x, k y⟫_ℝ * g y ^ 2) +
        (-2) * ∫ y in unitCube, g x * (⟪k x, k y⟫_ℝ * g y)) := by
    intro x
    have hexp : (fun y => ⟪k x, k y⟫_ℝ * (g x - g y) ^ 2) = fun y =>
        g x ^ 2 * ⟪k x, k y⟫_ℝ + (⟪k x, k y⟫_ℝ * g y ^ 2 +
          (-2) * (g x * (⟪k x, k y⟫_ℝ * g y))) := by
      funext y; ring
    have i23 : Integrable (fun y => ⟪k x, k y⟫_ℝ * g y ^ 2 +
        (-2) * (g x * (⟪k x, k y⟫_ℝ * g y))) (volume.restrict unitCube) :=
      (hint3 x).add ((hint2 x).const_mul _)
    rw [hexp, integral_add ((hint1 x).const_mul _) i23,
      integral_add (hint3 x) ((hint2 x).const_mul _), integral_const_mul, integral_const_mul,
      integral_inner_rows_right hk hkc hone hmass x, mul_one]
  simp_rw [hinner]
  have j1 : Integrable (fun x => g x ^ 2) (volume.restrict unitCube) :=
    integrable_unitCube_of_continuous_normed (f := fun x => g x ^ 2) (hg.pow 2)
  have j3 : Integrable (fun x => ∫ y in unitCube, ⟪k x, k y⟫_ℝ * g y ^ 2)
      (volume.restrict unitCube) := hP3.integral_prod_left
  have j2 : Integrable (fun x => ∫ y in unitCube, g x * (⟪k x, k y⟫_ℝ * g y))
      (volume.restrict unitCube) := hP2.integral_prod_left
  have j23 : Integrable (fun x => (∫ y in unitCube, ⟪k x, k y⟫_ℝ * g y ^ 2) +
      (-2) * ∫ y in unitCube, g x * (⟪k x, k y⟫_ℝ * g y)) (volume.restrict unitCube) :=
    j3.add (j2.const_mul _)
  rw [integral_add j1 j23, integral_add j3 (j2.const_mul _), integral_const_mul,
    ← norm_sq_integral_smul_rows hk hkc hg, integral_integral_swap hP3]
  have hswap : ∫ y in unitCube, ∫ x in unitCube, ⟪k x, k y⟫_ℝ * g y ^ 2 =
      ∫ y in unitCube, g y ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [integral_mul_const, integral_inner_rows_left hk hkc hone hmass y, one_mul]
  rw [hswap]
  ring

end Rows

end AVRegularity.Applications.Dissipation

end
