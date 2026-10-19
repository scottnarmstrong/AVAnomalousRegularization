-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Statements.Roots.UnitCube
public import AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import AVenhance.Infra.Torus.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Chebyshev

/-! # A Poincaré inequality on the torus through small translates

Step 3 of the proof of Lemma 8.4 of the paper. For a mean-zero periodic `g`, averaging
`A_g(z) = ∫_{𝕋²} |g(x + z) - g(x)|² dx` over `z ∈ Q = [-1/2, 1/2]²` gives `2 ‖g‖₂²`;
telescoping `g(· + N w) - g` over `N` steps gives `A_g(N w) ≤ N² A_g(w)`, and the change of
variables `z = N w` gives the inequality.

The cell tools used here and in `OperatorLemma.lean`: continuous periodic functions are bounded
(`exists_abs_le_of_continuous_isZ2Periodic`), cell integrals of periodic functions are
translation invariant (`integral_unitCube_add_of_isZ2Periodic`) and equal their integrals over
the centred box `Q` (`integral_centredBox_eq_unitCube`). -/

public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity.Applications.Dissipation

/-! ### Cell tools -/

private theorem volume_unitCube_shift : volume (unitCube : Set (Vec 2)) = 1 := by
  rw [unitCube, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- The unit cell is a probability space. -/
local instance torusShiftProbCube : IsProbabilityMeasure (volume.restrict unitCube) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitCube_shift⟩

/-- A continuous `ℤ²`-periodic function is bounded. -/
theorem exists_abs_le_of_continuous_isZ2Periodic {g : Vec 2 → ℝ} (hg : Continuous g)
    (hgp : IsZ2Periodic g) : ∃ M : ℝ, ∀ x, |g x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc (a := (0 : ℝ)) (b := 1))
    |>.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨M, fun x => ?_⟩
  have hx : x + latticeShift (fun i => -⌊x i⌋) ∈ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    intro i _
    have hfr : x i + ((-⌊x i⌋ : ℤ) : ℝ) = Int.fract (x i) := by
      rw [Int.cast_neg, ← sub_eq_add_neg, Int.self_sub_floor]
    simp only [Pi.add_apply, latticeShift, hfr]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  rw [← hgp (fun i => -⌊x i⌋) x, ← Real.norm_eq_abs]
  exact hM _ hx

/-- A continuous function is integrable on the unit cell. -/
theorem integrable_unitCube_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict unitCube) :=
  (hf.continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set
    (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self)

private theorem mem_unitCellAt_add_iff_shift (a x : Vec 2) :
    x + a ∈ Infra.Torus.unitCellAt 2 a ↔ x ∈ Infra.Torus.unitCell 2 := by
  simp only [Infra.Torus.unitCell, Infra.Torus.unitCellAt, Set.mem_ofPred_eq, Pi.add_apply,
    Set.mem_Ioc, zero_add]
  constructor
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]

/-- Translation invariance of cell integrals of periodic functions. -/
theorem integral_unitCube_add_of_isZ2Periodic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Vec 2 → E} (hf : IsZ2Periodic f) (a : Vec 2) :
    ∫ x in unitCube, f (x + a) = ∫ x in unitCube, f x := by
  rw [← Infra.Torus.integral_unitCell_eq_unitCube, ← Infra.Torus.integral_unitCell_eq_unitCube]
  have h1 := integral_indicator (μ := (volume : Measure (Vec 2))) (f := f)
    (Infra.Torus.measurableSet_unitCellAt 2 a)
  have h2 := integral_indicator (μ := (volume : Measure (Vec 2))) (f := fun x => f (x + a))
    (Infra.Torus.measurableSet_unitCell 2)
  have h3 := integral_add_right_eq_self (μ := (volume : Measure (Vec 2)))
    ((Infra.Torus.unitCellAt 2 a).indicator f) a
  have h4 : ∫ x in Infra.Torus.unitCell 2, f (x + a) = ∫ x in Infra.Torus.unitCellAt 2 a, f x := by
    rw [← h1, ← h2, ← h3]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    by_cases hx : x ∈ Infra.Torus.unitCell 2
    · simp only [Set.indicator_of_mem hx,
        Set.indicator_of_mem ((mem_unitCellAt_add_iff_shift a x).2 hx)]
    · simp only [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun h => hx ((mem_unitCellAt_add_iff_shift a x).1 h))]
  rw [h4]
  exact Infra.Torus.integral_periodic_unitCellAt_eq ((Infra.Torus.isZdPeriodic_iff_frozen f).2 hf) a

/-- The centred closed box `Q = [-1/2, 1/2]²`. -/
private theorem centredBox_ae_eq :
    (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) =ᵐ[(volume : Measure (Vec 2))]
      Infra.Torus.unitCellAt 2 (fun _ => -(1 / 2)) := by
  have h : (Set.pi Set.univ fun _ : Fin 2 => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) =ᵐ[volume]
      Set.Icc (fun _ : Fin 2 => -(1 / 2 : ℝ)) (fun _ => 1 / 2) := by
    simpa [volume_pi] using
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin 2 => (volume : Measure ℝ))
        (f := fun _ : Fin 2 => -(1 / 2 : ℝ)) (g := fun _ : Fin 2 => (1 / 2 : ℝ)))
  have hcell : Infra.Torus.unitCellAt 2 (fun _ => -(1 / 2)) =
      Set.pi Set.univ fun _ : Fin 2 => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    ext x
    simp only [Infra.Torus.unitCellAt, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    norm_num
  rw [hcell, Set.pi_univ_Icc]
  exact h.symm

/-- The integral of a periodic function over the centred box `Q = [-1/2, 1/2]²` is its cell
integral. -/
theorem integral_centredBox_eq_unitCube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → E} (hf : IsZ2Periodic f) :
    ∫ w in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)), f w =
      ∫ x in unitCube, f x := by
  rw [setIntegral_congr_set centredBox_ae_eq,
    Infra.Torus.integral_periodic_unitCellAt_eq ((Infra.Torus.isZdPeriodic_iff_frozen f).2 hf),
    Infra.Torus.integral_unitCell_eq_unitCube]

/-! ### The torus inequality -/

/-- The increment energy `A_g(z) = ∫_{𝕋²} |g(x + z) - g(x)|² dx`. -/
private noncomputable def incrementEnergy (g : Vec 2 → ℝ) (z : Vec 2) : ℝ :=
  ∫ x in unitCube, (g (x + z) - g x) ^ 2

private theorem sq_sub_le_of_abs_le {g : Vec 2 → ℝ} {M : ℝ} (hM : ∀ x, |g x| ≤ M) (a b : Vec 2) :
    ‖(g a - g b) ^ 2‖ ≤ (2 * M) ^ 2 := by
  rw [Real.norm_eq_abs, abs_pow]
  have h : |g a - g b| ≤ 2 * M := (abs_sub _ _).trans (by linarith [hM a, hM b])
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

private theorem continuous_incrementEnergy {g : Vec 2 → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) : Continuous (incrementEnergy g) := by
  refine continuous_of_dominated (bound := fun _ => (2 * M) ^ 2) (fun z => ?_)
    (fun z => Filter.Eventually.of_forall fun x => sq_sub_le_of_abs_le hM _ _)
    (integrable_const _) (Filter.Eventually.of_forall fun x => ?_)
  · exact ((hg.comp (continuous_id.add continuous_const)).sub hg).pow 2 |>.aestronglyMeasurable
  · exact ((hg.comp (continuous_const.add continuous_id)).sub continuous_const).pow 2

private theorem incrementEnergy_periodic {g : Vec 2 → ℝ} (hgp : IsZ2Periodic g) :
    IsZ2Periodic (incrementEnergy g) := by
  intro n z
  unfold incrementEnergy
  congr 1
  funext x
  rw [← add_assoc, hgp]

private theorem incrementEnergy_nonneg (g : Vec 2 → ℝ) (z : Vec 2) : 0 ≤ incrementEnergy g z :=
  integral_nonneg fun _ => sq_nonneg _

/-- `∫_{𝕋²} A_g = 2 ‖g‖₂²` for a mean-zero `g`. -/
private theorem integral_incrementEnergy {g : Vec 2 → ℝ} (hg : Continuous g)
    (hgp : IsZ2Periodic g) (hmean : ∫ x in unitCube, g x = 0) :
    ∫ z in unitCube, incrementEnergy g z = 2 * ∫ x in unitCube, g x ^ 2 := by
  obtain ⟨M, hM⟩ := exists_abs_le_of_continuous_isZ2Periodic hg hgp
  have hF : Integrable (Function.uncurry fun z x => (g (x + z) - g x) ^ 2)
      ((volume.restrict unitCube).prod (volume.restrict unitCube)) := by
    refine Integrable.of_bound ?_ ((2 * M) ^ 2)
      (Filter.Eventually.of_forall fun p => sq_sub_le_of_abs_le hM _ _)
    exact ((hg.comp (continuous_snd.add continuous_fst)).sub (hg.comp continuous_snd)).pow 2
      |>.aestronglyMeasurable
  unfold incrementEnergy
  rw [integral_integral_swap hF]
  have hinner : ∀ x, ∫ z in unitCube, (g (x + z) - g x) ^ 2 =
      (∫ y in unitCube, g y ^ 2) + g x ^ 2 := by
    intro x
    have hsq : ∫ z in unitCube, g (x + z) ^ 2 = ∫ y in unitCube, g y ^ 2 := by
      simp_rw [add_comm x]
      exact integral_unitCube_add_of_isZ2Periodic (f := fun y => g y ^ 2)
        (fun n y => by simp only [hgp n y]) x
    have hlin : ∫ z in unitCube, g (x + z) = 0 := by
      simp_rw [add_comm x]
      rw [integral_unitCube_add_of_isZ2Periodic hgp x, hmean]
    have hc : Continuous fun z => g (x + z) := hg.comp (continuous_const.add continuous_id)
    have i1 : Integrable (fun z => g (x + z) ^ 2) (volume.restrict unitCube) :=
      integrable_unitCube_of_continuous (f := fun z => g (x + z) ^ 2) (hc.pow 2)
    have i2 : Integrable (fun z => -(2 * g x) * g (x + z)) (volume.restrict unitCube) :=
      (integrable_unitCube_of_continuous hc).const_mul _
    have i3 : Integrable (fun _ : Vec 2 => g x ^ 2) (volume.restrict unitCube) :=
      integrable_const _
    have i23 : Integrable (fun z => -(2 * g x) * g (x + z) + g x ^ 2)
        (volume.restrict unitCube) := i2.add i3
    have hexp : (fun z => (g (x + z) - g x) ^ 2) =
        fun z => g (x + z) ^ 2 + ((-(2 * g x)) * g (x + z) + g x ^ 2) := by
      funext z; ring
    rw [hexp, integral_add i1 i23, integral_add i2 i3, integral_const_mul, hlin, hsq]
    simp
  simp_rw [hinner]
  have j1 : Integrable (fun _ : Vec 2 => ∫ y in unitCube, g y ^ 2) (volume.restrict unitCube) :=
    integrable_const _
  have j2 : Integrable (fun y => g y ^ 2) (volume.restrict unitCube) :=
    integrable_unitCube_of_continuous (f := fun y => g y ^ 2) (hg.pow 2)
  rw [integral_add j1 j2]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- Telescoping: `A_g(N w) ≤ N² A_g(w)`. -/
private theorem incrementEnergy_smul_le {g : Vec 2 → ℝ} (hg : Continuous g)
    (hgp : IsZ2Periodic g) (N : ℕ) (w : Vec 2) :
    incrementEnergy g ((N : ℝ) • w) ≤ (N : ℝ) ^ 2 * incrementEnergy g w := by
  set a : ℕ → Vec 2 → ℝ := fun j x => g (x + ((j + 1 : ℕ) : ℝ) • w) - g (x + (j : ℝ) • w)
    with ha
  have ha_cont : ∀ j, Continuous (a j) := fun j =>
    (hg.comp (continuous_id.add continuous_const)).sub (hg.comp (continuous_id.add continuous_const))
  have htel : ∀ x, g (x + (N : ℝ) • w) - g x = ∑ j ∈ Finset.range N, a j x := by
    intro x
    have := Finset.sum_range_sub (fun j : ℕ => g (x + (j : ℝ) • w)) N
    simp only [Nat.cast_zero, zero_smul, add_zero] at this
    rw [← this]
  have hterm : ∀ j, ∫ x in unitCube, a j x ^ 2 = incrementEnergy g w := by
    intro j
    have hshift : ∀ x, a j x ^ 2 = (fun y => (g (y + w) - g y) ^ 2) (x + (j : ℝ) • w) := by
      intro x
      simp only [ha]
      congr 3
      push_cast
      rw [add_smul, one_smul, add_assoc]
    simp_rw [hshift]
    exact integral_unitCube_add_of_isZ2Periodic
      (f := fun y => (g (y + w) - g y) ^ 2) (fun n y => by
        simp only
        rw [add_right_comm, hgp, hgp]) _
  unfold incrementEnergy
  calc ∫ x in unitCube, (g (x + (N : ℝ) • w) - g x) ^ 2
      ≤ ∫ x in unitCube, (N : ℝ) * ∑ j ∈ Finset.range N, a j x ^ 2 := by
        refine integral_mono (integrable_unitCube_of_continuous
          (((hg.comp (continuous_id.add continuous_const)).sub hg).pow 2))
          ((integrable_unitCube_of_continuous (f := fun x => ∑ j ∈ Finset.range N, a j x ^ 2)
            (continuous_finsetSum _ fun j _ => (ha_cont j).pow 2)).const_mul _) fun x => ?_
        rw [htel x]
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun j => a j x)
    _ = (N : ℝ) ^ 2 * ∫ x in unitCube, (g (x + w) - g x) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ =>
          integrable_unitCube_of_continuous (f := fun x => a j x ^ 2) ((ha_cont j).pow 2)]
        simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        unfold incrementEnergy
        ring

private theorem mem_Icc_scale_iff {R t : ℝ} (hR : 0 < R) :
    t ∈ Set.Icc (-(1 / (2 * R))) (1 / (2 * R)) ↔ R * t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  have h1 : 1 / (2 * R) = (1 / 2) / R := by rw [div_div]
  rw [Set.mem_Icc, Set.mem_Icc, h1, ← neg_div, div_le_iff₀ hR, le_div_iff₀ hR, mul_comm t R]

/-- The change of variables `z = R w`, `w ∈ Q/R`. -/
private theorem integral_smallBox_comp_smul (A : Vec 2 → ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ w in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / (2 * R))) (1 / (2 * R))), A (R • w) =
      (R ^ 2)⁻¹ * ∫ z in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)), A z := by
  have hQ : MeasurableSet (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hQR : MeasurableSet
      (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-(1 / (2 * R))) (1 / (2 * R))) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  rw [← integral_indicator hQR, ← integral_indicator hQ]
  have hind : (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-(1 / (2 * R))) (1 / (2 * R))).indicator
      (fun w => A (R • w)) = fun w =>
      (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator A (R • w) := by
    funext w
    have hmem : w ∈ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / (2 * R))) (1 / (2 * R))) ↔
        R • w ∈ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply, smul_eq_mul,
        mem_Icc_scale_iff hR]
    by_cases hw : w ∈ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / (2 * R))) (1 / (2 * R)))
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hmem.1 hw)]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw (hmem.2 h))]
  rw [hind, Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul,
    abs_of_pos (inv_pos.2 (pow_pos hR 2))]

/-- **Torus inequality** (Step 3 of the proof of Lemma 8.4 of the paper). A continuous periodic mean-zero `g` is controlled
by its increments over the translates `w ∈ Q/N = [-1/(2N), 1/(2N)]²`:
`2 ‖g‖₂² ≤ N⁴ ∫_{Q/N} ∫_{𝕋²} |g(x + w) - g(x)|² dx dw`. -/
theorem integral_sq_le_of_small_translates {g : Vec 2 → ℝ} (hg : Continuous g)
    (hgp : IsZ2Periodic g) (hmean : ∫ x in unitCube, g x = 0) {N : ℕ} (hN : 1 ≤ N) :
    2 * ∫ x in unitCube, g x ^ 2 ≤
      (N : ℝ) ^ 4 * ∫ w in Set.pi Set.univ
          (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
        ∫ x in unitCube, (g (x + w) - g x) ^ 2 := by
  have hR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨M, hM⟩ := exists_abs_le_of_continuous_isZ2Periodic hg hgp
  have hAc := continuous_incrementEnergy hg hM
  have hint : IntegrableOn (incrementEnergy g) (Set.pi Set.univ
      fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))) :=
    hAc.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have h13 := integral_incrementEnergy hg hgp hmean
  rw [← integral_centredBox_eq_unitCube (incrementEnergy_periodic hgp)] at h13
  have hscale := integral_smallBox_comp_smul (incrementEnergy g) hR
  rw [← h13]
  change _ ≤ (N : ℝ) ^ 4 * ∫ w in _, incrementEnergy g w
  have hle : ∫ w in Set.pi Set.univ
        (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
        incrementEnergy g ((N : ℝ) • w) ≤
      ∫ w in Set.pi Set.univ
        (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
        (N : ℝ) ^ 2 * incrementEnergy g w :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => incrementEnergy_nonneg g _)
      (hint.const_mul _) (Filter.Eventually.of_forall fun w => incrementEnergy_smul_le hg hgp N w)
  rw [integral_const_mul] at hle
  have hR2 : (0 : ℝ) < (N : ℝ) ^ 2 := pow_pos hR 2
  calc ∫ z in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)), incrementEnergy g z
      = (N : ℝ) ^ 2 * ∫ w in Set.pi Set.univ
          (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
          incrementEnergy g ((N : ℝ) • w) := by
        rw [hscale, ← mul_assoc, mul_inv_cancel₀ hR2.ne', one_mul]
    _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 * ∫ w in Set.pi Set.univ
          (fun _ : Fin 2 => Set.Icc (-(1 / (2 * (N : ℝ)))) (1 / (2 * (N : ℝ)))),
          incrementEnergy g w) := mul_le_mul_of_nonneg_left hle hR2.le
    _ = _ := by ring

end AVRegularity.Applications.Dissipation

end
