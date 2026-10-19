-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
import AVRegularity.CycleEvolution.StrongUniqueness
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! The identity matrix satisfies the actual admissible cell metric predicate. -/

theorem cellIdentityMetric : IsCellMetric (fun _ _ => 1) := by
  refine ⟨measurable_const, ?_, ?_, ?_⟩
  · intro t x n
    rfl
  · intro t x
    exact Matrix.isSymm_one
  · intro t x ξ
    have h : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have he : (∑ i, ∑ j, ξ i * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ j) =
        ∑ i, ξ i ^ 2 := by
      simp only [Fin.sum_univ_two, Matrix.one_apply]
      norm_num
      ring
    rw [he]
    constructor <;> linarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Uniform coordinate-direction notation for the two-parameter norm-jet interface. -/

/-- The unit multi-index for a coordinate direction. -/
def cellJetDirection (j : Fin 2) : ℕ × ℕ := if j = 0 then (1, 0) else (0, 1)

/-- The real coordinate line through a slow parameter. -/
def cellParameterLine (Y : Fin 2 → ℝ) (j : Fin 2) (h : ℝ) : Fin 2 → ℝ :=
  Y + h • Pi.single j 1

/-- Adding a coordinate multi-index raises total order by exactly one. -/
theorem cellJetDirection_order (α : ℕ × ℕ) (j : Fin 2) :
    (α + cellJetDirection j).1 + (α + cellJetDirection j).2 = α.1 + α.2 + 1 := by
  fin_cases j <;> simp [cellJetDirection, Prod.add_def] <;> omega

/-- Both norm-jet derivatives have one uniform coordinate-indexed statement. -/
theorem normJetFamily_directional {X : Type*} [AddCommGroup X] [Module ℝ X]
    (N : X → ℝ≥0∞) (K : ℕ) (J : ℕ × ℕ → (Fin 2 → ℝ) → X)
    (hJ : IsNormJetFamily N K Set.univ J) (α : ℕ × ℕ)
    (hα : α.1 + α.2 < K) (Y : Fin 2 → ℝ) (j : Fin 2) :
    Tendsto (fun h : ℝ => N (h⁻¹ • (J α (cellParameterLine Y j h) - J α Y) -
      J (α + cellJetDirection j) Y)) (𝓝[≠] 0) (𝓝 0) := by
  fin_cases j
  · simpa [cellJetDirection, Prod.add_def, cellParameterLine] using
      (hJ.2 α hα Y (Set.mem_univ Y)).1
  · simpa [cellJetDirection, Prod.add_def, cellParameterLine] using
      (hJ.2 α hα Y (Set.mem_univ Y)).2

/-- A punctured coordinate line converges to its base point. -/
theorem cellParameterLine_tendsto (Y : Fin 2 → ℝ) (j : Fin 2) :
    Tendsto (cellParameterLine Y j) (𝓝[≠] (0 : ℝ)) (𝓝 Y) := by
  have h : Tendsto (cellParameterLine Y j) (𝓝 (0 : ℝ)) (𝓝 Y) := by
    change Tendsto (fun h : ℝ => Y + h • Pi.single j 1) (𝓝 0) (𝓝 Y)
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds.add (tendsto_id.smul tendsto_const_nhds) :
        Tendsto (fun h : ℝ => Y + h • Pi.single j (1 : ℝ)) (𝓝 0)
          (𝓝 (Y + (0 : ℝ) • Pi.single j (1 : ℝ))))
  exact h.mono_left nhdsWithin_le_nhds

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Actual pointwise cell series and their L2 classes under summable literal L2 bounds. -/

/-- A summable family of literal L2 norms has a pointwise ae convergent L2 sum with its norm bound. -/
theorem cellLpSeries_memLp_bound {J E X : Type*} [MeasurableSpace X] [Countable J]
    [NormedAddCommGroup E] [CompleteSpace E]
    (μ : Measure X) (f : J → X → E) (hs : (∑' j, eLpNorm (f j) 2 μ) < ⊤) :
    MemLp (fun x => ∑' j, f j x) 2 μ ∧
      eLpNorm (fun x => ∑' j, f j x) 2 μ ≤ ∑' j, eLpNorm (f j) 2 μ ∧
      ∀ᵐ x ∂μ, Summable (fun j => ‖f j x‖) := by
  have hf (j : J) : MemLp (f j) 2 μ := (ENNReal.le_tsum j).trans_lt hs
  let u := fun j => (hf j).toLp (f j)
  have hu : (∑' j, ‖u j‖ₑ) < ⊤ := by
    simpa only [u, Lp.enorm_toLp] using hs
  have hall : ∀ᵐ x ∂μ, ∀ j, u j x = f j x :=
    ae_all_iff.mpr (fun j => (hf j).coeFn_toLp)
  have hcoe : (⇑(∑' j, u j) : X → E) =ᵐ[μ] fun x => ∑' j, f j x := by
    filter_upwards [Lp.coeFn_tsum hu.ne, hall] with x hx hx'
    exact hx.trans (tsum_congr (fun j => hx' j))
  refine ⟨(memLp_congr_ae hcoe).mp (Lp.memLp (∑' j, u j)), ?_, ?_⟩
  · rw [← eLpNorm_congr_ae hcoe, ← Lp.enorm_def]
    have hb := enorm_tsum_le_tsum_enorm (f := u)
    simpa only [u, Lp.enorm_toLp] using hb
  · exact summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2) hs.ne


/-- A summable family of literal L2 norms has a pointwise ae convergent L2 sum with its norm bound. -/
theorem cellL2Series_memLp_bound {J E : Type*} [Countable J]
    [NormedAddCommGroup E] [CompleteSpace E]
    (f : J → Vec 2 → E) (hs : (∑' j, cellL2Norm (f j)) < ⊤) :
    MemLp (fun x => ∑' j, f j x) 2 (volume.restrict AVenhance.unitCube) ∧
      cellL2Norm (fun x => ∑' j, f j x) ≤ ∑' j, cellL2Norm (f j) ∧
      ∀ᵐ x ∂volume.restrict AVenhance.unitCube, Summable (fun j => ‖f j x‖) := by
  exact cellLpSeries_memLp_bound (volume.restrict AVenhance.unitCube) f hs

end AVRegularity.CycleEvolution
end
end

section
/-! Pointwise entry bounds derived from the cell ellipticity hypothesis. -/

@[expose] public section

open Homogenization

namespace AVRegularity.CycleEvolution

/-- Uniform ellipticity bounds every matrix entry, including the mixed entries. -/
theorem cellMetric_entry_bound {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (z : Vec 2) (i j : Fin 2) :
    |G t z i j| ≤ 2 := by
  have h0 := hG.2.2.2 t z ![1, 0]
  have h1 := hG.2.2.2 t z ![0, 1]
  have hp := hG.2.2.2 t z ![1, 1]
  have hm := hG.2.2.2 t z ![1, -1]
  have hs : G t z 1 0 = G t z 0 1 := (hG.2.2.1 t z).apply 0 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow, zero_pow (by decide : 2 ≠ 0),
    one_mul, zero_mul, mul_one, mul_zero, add_zero, zero_add] at h0 h1 hp hm
  norm_num at hm
  rcases h0 with ⟨h0l, h0u⟩
  rcases h1 with ⟨h1l, h1u⟩
  rcases hp with ⟨hpl, hpu⟩
  rcases hm with ⟨hml, hmu⟩
  have h00 : |G t z 0 0| ≤ 2 := abs_le.mpr ⟨by linarith, h0u⟩
  have h11 : |G t z 1 1| ≤ 2 := abs_le.mpr ⟨by linarith, h1u⟩
  have h01 : |G t z 0 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h10 : |G t z 1 0| ≤ 2 := hs ▸ h01
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- Entry measurability follows from joint matrix measurability. -/
theorem cellMetric_entry_measurable {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (i j : Fin 2) :
    Measurable (fun p : ℝ × Vec 2 => G p.1 p.2 i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hG.1)

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- Realification preserves the ellipticity lower bound for complex gradients. -/
theorem cellMetric_complex_coercive {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (z : Vec 2) (w : Fin 2 → ℂ) :
    (1 / 2) * ∑ i, ‖w i‖ ^ 2 ≤
      (∑ i, ∑ j, (G t z i j : ℂ) * w i * star (w j)).re := by
  have hr := (hG.2.2.2 t z (fun i => (w i).re)).1
  have hi := (hG.2.2.2 t z (fun i => (w i).im)).1
  have he (i : Fin 2) : ‖w i‖ ^ 2 = (w i).re ^ 2 + (w i).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  simp [Fin.sum_univ_two, Complex.mul_re, Complex.mul_im, he] at *
  nlinarith

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- The vector drift bound controls each directional coefficient. -/
theorem cellDrift_entry_bound {v : ℝ → Vec 2 → Vec 2} {V : ℝ}
    (hv : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2) (t : ℝ) (z : Vec 2) (i : Fin 2) :
    |v t z i| ≤ |V| := by
  have h := hv t z
  simp only [Fin.sum_univ_two] at h
  have hs : (v t z i) ^ 2 ≤ V ^ 2 := by
    fin_cases i
    · exact le_trans (le_add_of_nonneg_right (sq_nonneg _)) h
    · exact le_trans (le_add_of_nonneg_left (sq_nonneg _)) h
  exact (sq_le_sq).mp hs

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! The entrywise metric size is an extended seminorm on raw coefficient fields. -/

/-- Each matrix entry is bounded by the uniform metric size. -/
theorem cellMetricSupNorm_entry (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) (x : Vec 2) (i j : Fin 2) : ‖G t x i j‖ₑ ≤ cellMetricSupNorm G :=
  le_iSup_of_le t (le_iSup_of_le x (le_iSup_of_le i (le_iSup (fun j => ‖G t x i j‖ₑ) j)))

/-- The uniform metric size obeys the triangle inequality. -/
theorem cellMetricSupNorm_add (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    cellMetricSupNorm (G + H) ≤ cellMetricSupNorm G + cellMetricSupNorm H := by
  apply iSup_le
  intro t
  apply iSup_le
  intro x
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  exact (enorm_add_le (G t x i j) (H t x i j)).trans
    (add_le_add (cellMetricSupNorm_entry G t x i j) (cellMetricSupNorm_entry H t x i j))

/-- Scalar multiplication has the expected uniform bound. -/
theorem cellMetricSupNorm_smul (r : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    cellMetricSupNorm (r • G) ≤ ‖r‖ₑ * cellMetricSupNorm G := by
  apply iSup_le
  intro t
  apply iSup_le
  intro x
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  change ‖r • G t x i j‖ₑ ≤ _
  rw [enorm_smul]
  gcongr
  exact cellMetricSupNorm_entry G t x i j

/-- The uniform metric size is unchanged by negation. -/
theorem cellMetricSupNorm_neg (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    cellMetricSupNorm (-G) = cellMetricSupNorm G := by
  simp only [cellMetricSupNorm, Pi.neg_apply, Matrix.neg_apply, enorm_neg]

end AVRegularity.CycleEvolution
end
end

section
/-! Convert the stated cell source bounds to genuine product-space L² integrability. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity.CycleEvolution

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The square of the cell L² norm is the spatial norm-square integral. -/
theorem cellL2Norm_sq_eq_lintegral {f : Vec 2 → E}
    (hf : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube)) :
    cellL2Norm f ^ 2 = ∫⁻ x in AVenhance.unitCube, ‖f x‖ₑ ^ 2 := by
  simpa [cellL2Norm, ENNReal.rpow_two] using
    eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hf

/-- The source assumptions imply product-space L² membership. -/
theorem cellSource_memLp_product (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : Measurable (Function.uncurry f))
    (h2 : ∫⁻ t in I, cellL2Norm (f t) ^ 2 < ⊤) :
    MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  change eLpNorm (Function.uncurry f) 2 _ < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_prod _ (hf.enorm.pow_const 2).aemeasurable]
  have he : (fun t => ∫⁻ x in AVenhance.unitCube, ‖f t x‖ₑ ^ 2) =
      (fun t => cellL2Norm (f t) ^ 2) := by
    funext t
    exact (cellL2Norm_sq_eq_lintegral
      ((hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).symm
  change (∫⁻ t in I, ∫⁻ x in AVenhance.unitCube, ‖f t x‖ₑ ^ 2) < ⊤
  have hi : (∫⁻ t in I, ∫⁻ x in AVenhance.unitCube, ‖f t x‖ₑ ^ 2) =
      ∫⁻ t in I, cellL2Norm (f t) ^ 2 := lintegral_congr (fun t => congrFun he t)
  exact hi.le.trans_lt h2

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Almost every section of a product-space L² function lies in spatial L². -/
theorem cellSource_memLp_slices (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    ∀ᵐ t ∂volume.restrict I, MemLp (f t) 2 (volume.restrict AVenhance.unitCube) := by
  have hmeas := hf.aestronglyMeasurable.prodMk_left
  have hsq : Integrable (fun p : ℝ × Vec 2 => ‖f p.1 p.2‖ ^ (2 : ℕ))
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
    simpa [Function.uncurry_def, Real.rpow_two] using hf.integrable_norm_rpow (by norm_num) (by norm_num)
  have hsections := hsq.prod_right_ae
  filter_upwards [hmeas, hsections] with t hm hs
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hs

/-- A total spatial source class, zero only on exceptional non-L² slices. -/
def cellSourceSlice (f : ℝ → Vec 2 → E) (t : ℝ) :
    Lp E 2 (volume.restrict AVenhance.unitCube) := by
  classical
  exact if h : MemLp (f t) 2 (volume.restrict AVenhance.unitCube) then h.toLp (f t) else 0

omit [InnerProductSpace ℝ E] in
/-- On every L² slice the total source class represents the actual raw source. -/
theorem cellSourceSlice_ae (f : ℝ → Vec 2 → E) (t : ℝ)
    (hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube)) :
    cellSourceSlice f t =ᵐ[volume.restrict AVenhance.unitCube] f t := by
  classical
  simp only [cellSourceSlice, dite_eq_left hf]
  exact hf.coeFn_toLp

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute L1 bounds for the products appearing in weak cell integrands. -/

/-- Two jointly almost measurable L2 fields give the precise absolute product integral bound. -/
theorem cellL2_product_lintegral_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℂ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    (∫⁻ x, ‖f x * g x‖ₑ ∂μ) ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    hf.enorm hg.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  simpa only [Pi.mul_apply, enorm_mul, ENNReal.toReal_ofNat] using hh

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Pointwise bounds for the metric perturbation flux in the cell resolvent identity. -/

/-- A real matrix acting on a complex cell gradient. -/
def cellMetricFluxVector (A : Matrix (Fin 2) (Fin 2) ℝ)
    (w : PiLp 2 (fun _ : Fin 2 => ℂ)) : PiLp 2 (fun _ : Fin 2 => ℂ) :=
  WithLp.toLp 2 (fun i => ∑ j : Fin 2, (A i j : ℂ) * w j)

/-- Entrywise bounds give a universal operator bound in dimension two. -/
theorem cellMetricFluxVector_norm_le (A : Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B)
    (w : PiLp 2 (fun _ : Fin 2 => ℂ)) :
    ‖cellMetricFluxVector A w‖ ≤ 2 * B * ‖w‖ := by
  have hi (i : Fin 2) : ‖cellMetricFluxVector A w i‖ ≤ B * (‖w 0‖ + ‖w 1‖) := by
    change ‖∑ j : Fin 2, (A i j : ℂ) * w j‖ ≤ _
    calc
      _ ≤ ∑ j : Fin 2, ‖(A i j : ℂ) * w j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 2, B * ‖w j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
      _ = _ := by simp only [Fin.sum_univ_two]; ring
  have hs (i : Fin 2) : ‖cellMetricFluxVector A w i‖ ^ 2 ≤
      B ^ 2 * (‖w 0‖ + ‖w 1‖) ^ 2 := by
    have hh := sq_le_sq₀ (norm_nonneg (cellMetricFluxVector A w i))
      (mul_nonneg hB (add_nonneg (norm_nonneg (w 0)) (norm_nonneg (w 1))))
    simpa only [mul_pow] using hh.mpr (hi i)
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℂ) w
  have hz := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℂ) (cellMetricFluxVector A w)
  simp only [Fin.sum_univ_two] at hn hz
  have hc : (‖w 0‖ + ‖w 1‖) ^ 2 ≤ 2 * ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖w 0‖ - ‖w 1‖)]
  have hmul := mul_le_mul_of_nonneg_left hc (sq_nonneg B)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hB)
    (norm_nonneg w))).mp
  nlinarith [hs 0, hs 1]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Joint measurability of algebraic metric perturbations, evaluated entrywise. -/

/-- Joint matrix measurability gives joint entry measurability. -/
theorem cellMetric_measurable_entry
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : Measurable (Function.uncurry G)) (i j : Fin 2) :
    Measurable (fun p : ℝ × Vec 2 => G p.1 p.2 i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hG)

/-- Differences of jointly measurable metric fields are jointly measurable. -/
theorem cellMetric_measurable_sub
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : Measurable (Function.uncurry G)) (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (G - H)) :=
  Measurable.of_eval (fun i => Measurable.of_eval (fun j =>
    (cellMetric_measurable_entry G hG i j).sub (cellMetric_measurable_entry H hH i j)))

/-- Real scaling preserves joint metric measurability. -/
theorem cellMetric_measurable_smul (r : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : Measurable (Function.uncurry G)) :
    Measurable (Function.uncurry (r • G)) :=
  Measurable.of_eval (fun i => Measurable.of_eval (fun j =>
    (cellMetric_measurable_entry G hG i j).const_mul r))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Pointwise complex metric pairings and quantitative Young bounds. -/

/-- Realification of the spatial complex metric pairing. -/
def cellMetricPairing (A : Matrix (Fin 2) (Fin 2) ℝ) (a b : Fin 2 → ℂ) : ℝ :=
  (∑ j : Fin 2, ∑ k : Fin 2, (A j k : ℂ) * a j * star (b k)).re

/-- The metric pairing expands bilinearly in real Hilbert variables. -/
theorem cellMetricPairing_add (A : Matrix (Fin 2) (Fin 2) ℝ)
    (p a q b : Fin 2 → ℂ) :
    cellMetricPairing A (p + a) (q + b) =
      cellMetricPairing A p q + cellMetricPairing A p b +
        cellMetricPairing A a q + cellMetricPairing A a b := by
  simp only [cellMetricPairing, Pi.add_apply, star_add, mul_add, add_mul,
    Finset.sum_add_distrib, Complex.add_re]
  ring

/-- Entry bounds control the full complex pairing without coefficient continuity. -/
theorem cellMetricPairing_abs_le (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ j k, |A j k| ≤ 2) (a b : Fin 2 → ℂ) :
    |cellMetricPairing A a b| ≤ ∑ j : Fin 2, ∑ k : Fin 2, 2 * ‖a j‖ * ‖b k‖ := by
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_star]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hA j k) (norm_nonneg _)) (norm_nonneg _)

/-- A small gradient coefficient can absorb a metric cross term. -/
theorem cellMetricPairing_young (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ j k, |A j k| ≤ 2) (p b : Fin 2 → ℂ) :
    |cellMetricPairing A p b| ≤
      (1 / 16) * ∑ j, ‖p j‖ ^ 2 + 64 * ∑ k, ‖b k‖ ^ 2 := by
  apply (cellMetricPairing_abs_le A hA p b).trans
  simp only [Fin.sum_univ_two]
  nlinarith [sq_nonneg (‖p 0‖ / 8 - 4 * ‖b 0‖),
    sq_nonneg (‖p 0‖ / 8 - 4 * ‖b 1‖),
    sq_nonneg (‖p 1‖ / 8 - 4 * ‖b 0‖),
    sq_nonneg (‖p 1‖ / 8 - 4 * ‖b 1‖)]

/-- A symmetric metric pairing is symmetric after realification. -/
theorem cellMetricPairing_symm (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsSymm)
    (a b : Fin 2 → ℂ) : cellMetricPairing A a b = cellMetricPairing A b a := by
  have h01 := hA.apply 0 1
  simp [cellMetricPairing, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] at *
  rw [h01]
  ring

/-- A coarse quadratic bound for two lower-order perturbations. -/
theorem cellMetricPairing_quadratic (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ j k, |A j k| ≤ 2) (a b : Fin 2 → ℂ) :
    |cellMetricPairing A a b| ≤ 2 * (∑ j, ‖a j‖ ^ 2 + ∑ k, ‖b k‖ ^ 2) := by
  apply (cellMetricPairing_abs_le A hA a b).trans
  simp only [Fin.sum_univ_two]
  nlinarith [sq_nonneg (‖a 0‖ - ‖b 0‖), sq_nonneg (‖a 0‖ - ‖b 1‖),
    sq_nonneg (‖a 1‖ - ‖b 0‖), sq_nonneg (‖a 1‖ - ‖b 1‖)]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Finite raw cell energy integrals from product-space L² membership. -/

/-- Fubini identifies the time integral of the cell L² norm square with the product square integral. -/
theorem cellProduct_cellNormSq_lintegral {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    (∫⁻ t in I, cellL2Norm (f t) ^ 2) =
      ∫⁻ p : ℝ × Vec 2, ‖f p.1 p.2‖ₑ ^ 2 ∂
        (volume.restrict I).prod (volume.restrict AVenhance.unitCube) := by
  have hm : AEMeasurable (fun p : ℝ × Vec 2 => ‖f p.1 p.2‖ₑ ^ 2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
    simpa only [Function.uncurry_def] using hf.aestronglyMeasurable.enorm.pow_const 2
  rw [lintegral_prod _ hm]
  apply lintegral_congr_ae
  filter_upwards [cellSource_memLp_slices I f hf] with t ht
  exact cellL2Norm_sq_eq_lintegral ht.aestronglyMeasurable

/-- Product L² membership supplies the finite gradient/source energy integrals required there. -/
theorem cellProduct_cellNormSq_finite {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    (∫⁻ t in I, cellL2Norm (f t) ^ 2) < ⊤ := by
  rw [cellProduct_cellNormSq_lintegral I f hf]
  have he : eLpNorm (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) < ⊤ := hf
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)
    hf.aestronglyMeasurable] at he
  simpa only [Function.uncurry_def, ENNReal.toReal_ofNat, ENNReal.rpow_two] using he

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Product-space L2 energy is the time integral of the literal spatial L2 energy. -/

/-- The exact squared product L2 norm formula needs only joint almost measurability. -/
theorem cellProduct_eLpNorm_sq {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    eLpNorm (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) ^ 2 =
      ∫⁻ t in I, cellL2Norm (f t) ^ 2 := by
  rw [← ENNReal.rpow_two]
  have hp := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hf
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at hp
  rw [hp, lintegral_prod _ (hf.enorm.pow_const 2)]
  apply lintegral_congr_ae
  filter_upwards [hf.prodMk_left] with t ht
  simpa only [Function.uncurry_def, ENNReal.rpow_two] using
    (cellL2Norm_sq_eq_lintegral ht).symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Jointly measurable product L2 data have the exact finite raw cell forcing budget. -/

section
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

theorem cellSource_product_energy_lt_top (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hm : Measurable (Function.uncurry f))
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    (∫⁻ t in I, cellL2Norm (f t) ^ 2) < ⊤ := by
  have hi : (∫⁻ p : ℝ × Vec 2, ‖f p.1 p.2‖ₑ ^ 2
      ∂((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ENNReal) ≠ 0) (by simp : (2 : ENNReal) ≠ ⊤)
      hm.aestronglyMeasurable).mp hf
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two, Function.uncurry_def] using h
  change (∫⁻ p : ℝ × Vec 2, ‖Function.uncurry f p‖ₑ ^ 2
    ∂((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) < ⊤ at hi
  rw [lintegral_prod _ (hm.enorm.pow_const 2).aemeasurable] at hi
  simp only [Function.uncurry_def] at hi
  have he : (∫⁻ t in I, ∫⁻ x in AVenhance.unitCube, ‖f t x‖ₑ ^ 2) =
      ∫⁻ t in I, cellL2Norm (f t) ^ 2 := by
    apply lintegral_congr
    intro t
    exact (cellL2Norm_sq_eq_lintegral
      ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).symm
  exact he ▸ hi
end

/-! A genuine L² representative identifies the total raw source slice. -/

theorem cellSourceSlice_eq_of_ae (f : ℝ → Vec 2 → ℂ) (t : ℝ)
    (S : Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (hS : S =ᵐ[volume.restrict AVenhance.unitCube] f t) : cellSourceSlice f t = S := by
  have hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube) :=
    (memLp_congr_ae hS).mp (Lp.memLp S)
  apply Lp.ext
  exact (cellSourceSlice_ae f t hf).trans hS.symm

/-! Uniformly local cell norms depend only on joint almost-everywhere classes. -/

/-- Equality on the time-space product preserves every uniformly local window. -/
theorem cellUlNorm_congr_ae {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f g : ℝ → Vec 2 → E)
    (he : Function.uncurry f =ᵐ[(volume.restrict I).prod
      (volume.restrict AVenhance.unitCube)] Function.uncurry g) :
    cellUlNorm I f = cellUlNorm I g := by
  have hs : ∀ᵐ t ∂volume.restrict I,
      f t =ᵐ[volume.restrict AVenhance.unitCube] g t := Measure.ae_ae_of_ae_prod he
  unfold cellUlNorm
  congr 1
  funext a
  congr 1
  apply lintegral_congr_ae
  have hm : volume.restrict (Set.Icc a (a + 1) ∩ I) ≤ volume.restrict I :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  filter_upwards [ae_mono hm hs] with t ht
  rw [cellL2Norm, cellL2Norm, eLpNorm_congr_ae ht]

/-- A jointly almost strongly measurable field has a measurable representative of the same
uniformly local size, without assuming a finite global time-space integral. -/
theorem cellUl_measurable_representative {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    ∃ g : ℝ → Vec 2 → E,
      Measurable (Function.uncurry g) ∧
      Function.uncurry f =ᵐ[(volume.restrict I).prod
        (volume.restrict AVenhance.unitCube)] Function.uncurry g ∧
      cellUlNorm I g = cellUlNorm I f := by
  refine ⟨fun t x => hf.mk (Function.uncurry f) (t, x), hf.measurable_mk,
    hf.ae_eq_mk, ?_⟩
  exact (cellUlNorm_congr_ae I _ _ hf.ae_eq_mk).symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The uniformly local norm is bounded by the full-time energy budget. -/

theorem cellUlNorm_le_totalEnergy {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E) (A : ENNReal)
    (hA : (∫⁻ t in I, cellL2Norm (f t) ^ 2) ≤ A) :
    cellUlNorm I f ≤ A ^ (1 / 2 : ℝ) := by
  unfold cellUlNorm
  apply iSup_le
  intro a
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact (lintegral_mono_set inter_subset_right).trans hA

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Unit-window estimates supplied by the uniformly local cell source norm. -/

variable {E : Type*} [NormedAddCommGroup E]

/-- The squared integral on each unit window is bounded by the squared uniformly local norm. -/
theorem cellUl_window_integral_le (I : Set ℝ) (f : ℝ → Vec 2 → E) (a : ℝ) :
    (∫⁻ τ in Set.Icc a (a + 1) ∩ I, cellL2Norm (f τ) ^ 2) ≤ cellUlNorm I f ^ 2 := by
  have h : (∫⁻ τ in Set.Icc a (a + 1) ∩ I, cellL2Norm (f τ) ^ 2) ^ (1 / 2 : ℝ) ≤
      cellUlNorm I f := le_iSup (fun a : ℝ =>
        (∫⁻ τ in Set.Icc a (a + 1) ∩ I, cellL2Norm (f τ) ^ 2) ^ (1 / 2 : ℝ)) a
  have hsq := pow_le_pow_left₀ (bot_le : (0 : ℝ≥0∞) ≤ _) h 2
  simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, ENNReal.rpow_one] using hsq

/-- Finite uniformly local norm gives a finite squared integral on every unit window. -/
theorem cellUl_window_integral_lt_top (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hf : cellUlNorm I f < ⊤) (a : ℝ) :
    (∫⁻ τ in Set.Icc a (a + 1) ∩ I, cellL2Norm (f τ) ^ 2) < ⊤ :=
  (cellUl_window_integral_le I f a).trans_lt (ENNReal.pow_lt_top hf)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! The uniformly local cell norm vanishes on the literal zero field. -/

/-- Zero forcing has zero uniformly local norm on every time set. -/
theorem cellUlNorm_zero_field {E : Type*} [NormedAddCommGroup E] (I : Set ℝ) :
    cellUlNorm I (0 : ℝ → Vec 2 → E) = 0 := by
  simp [cellUlNorm, cellL2Norm]

/-! Exact real-part increment of a real two-variable quadratic polynomial. -/

theorem complex_real_quadratic_increment (a b c : ℂ)
    (ha : a.im = 0) (hb : b.im = 0) (hc : c.im = 0) (x y : Vec 2) :
    ((a * ((x 0 : ℂ) + Complex.I * (y 0 : ℂ)) ^ 2 +
       b * ((x 0 : ℂ) + Complex.I * (y 0 : ℂ)) * ((x 1 : ℂ) + Complex.I * (y 1 : ℂ)) +
       c * ((x 1 : ℂ) + Complex.I * (y 1 : ℂ)) ^ 2) -
      (a * (x 0 : ℂ) ^ 2 + b * (x 0 : ℂ) * (x 1 : ℂ) + c * (x 1 : ℂ) ^ 2)).re =
      -(a.re * y 0 ^ 2 + b.re * y 0 * y 1 + c.re * y 1 ^ 2) := by
  simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, ha, hb, hc]
  ring

theorem real_quadratic_abs_bound (a b c B : ℝ) (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) (y : Vec 2) :
    |a * y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2| ≤
      2 * B * (∑ j, y j ^ 2) := by
  have h0 : |a * y 0 ^ 2| ≤ B * y 0 ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (y 0))]
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  have h1 : |c * y 1 ^ 2| ≤ B * y 1 ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (y 1))]
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have hm : |b * y 0 * y 1| ≤ B * |y 0| * |y 1| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (abs_nonneg _)) (abs_nonneg _)
  have hcross : |y 0| * |y 1| ≤ (y 0 ^ 2 + y 1 ^ 2) / 2 := by
    nlinarith [sq_nonneg (|y 0| - |y 1|), sq_abs (y 0), sq_abs (y 1)]
  have hmc := mul_le_mul_of_nonneg_left hcross hB
  have hsum := abs_add_le (a * y 0 ^ 2 + b * y 0 * y 1) (c * y 1 ^ 2)
  have hsub := abs_add_le (a * y 0 ^ 2) (b * y 0 * y 1)
  simp only [Fin.sum_univ_two]
  nlinarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Finite triangular indices for the two-coordinate fibre coefficient recursion. -/

/-- Only a positive coordinate can supply the corresponding frequency factor. -/
def fibreCoefficientDirections (p : ℕ × ℕ) : Finset (Fin 2) :=
  Finset.univ.filter (fun j => if j = 0 then 0 < p.1 else 0 < p.2)

/-- The lower coefficient after removing one coordinate frequency factor. -/
def fibreCoefficientPrevious (p : ℕ × ℕ) (j : Fin 2) : ℕ × ℕ :=
  (p.1 - (cellJetDirection j).1, p.2 - (cellJetDirection j).2)

/-- The rectangle of all first indices in an unweighted two-variable coefficient convolution. -/
def fibreCoefficientPairs (p : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (p.1 + 1) ×ˢ Finset.range (p.2 + 1)

/-- The complementary second coefficient index. -/
def fibreCoefficientComplement (p a : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 - a.1, p.2 - a.2)

/-- Every active frequency direction lowers the total order by exactly one. -/
theorem fibreCoefficientPrevious_order {p : ℕ × ℕ} {j : Fin 2}
    (hj : j ∈ fibreCoefficientDirections p) :
    (fibreCoefficientPrevious p j).1 + (fibreCoefficientPrevious p j).2 + 1 = p.1 + p.2 := by
  have hh := Finset.mem_filter.mp hj
  fin_cases j <;> simp [fibreCoefficientPrevious, cellJetDirection] at hh ⊢ <;> omega

/-- Adding back the active coordinate direction recovers the original coefficient index. -/
theorem fibreCoefficientPrevious_recover {p : ℕ × ℕ} {j : Fin 2}
    (hj : j ∈ fibreCoefficientDirections p) :
    fibreCoefficientPrevious p j + cellJetDirection j = p := by
  have hh := Finset.mem_filter.mp hj
  fin_cases j <;> apply Prod.ext <;>
    simp [fibreCoefficientPrevious, cellJetDirection] at hh ⊢ <;> omega

/-- Both coefficient convolution indices are componentwise bounded by the original multi-index. -/
theorem fibreCoefficientPairs_bounds {p a : ℕ × ℕ} (ha : a ∈ fibreCoefficientPairs p) :
    a.1 ≤ p.1 ∧ a.2 ≤ p.2 := by
  simp only [fibreCoefficientPairs, Finset.mem_product, Finset.mem_range] at ha
  omega

/-- The coefficient convolution indices recover the original multi-index. -/
theorem fibreCoefficientPairs_recover {p a : ℕ × ℕ} (ha : a ∈ fibreCoefficientPairs p) :
    a + fibreCoefficientComplement p a = p := by
  have hh := fibreCoefficientPairs_bounds ha
  apply Prod.ext <;> simp only [Prod.add_def, fibreCoefficientComplement] <;> omega

/-- Both inputs of each quadratic source coefficient have strictly smaller order than its output. -/
theorem fibreCoefficientPairs_lower_orders {p a : ℕ × ℕ} {j : Fin 2}
    (hj : j ∈ fibreCoefficientDirections p)
    (ha : a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j)) :
    a.1 + a.2 < p.1 + p.2 ∧
      (fibreCoefficientComplement (fibreCoefficientPrevious p j) a).1 +
        (fibreCoefficientComplement (fibreCoefficientPrevious p j) a).2 < p.1 + p.2 := by
  have ho := fibreCoefficientPrevious_order hj
  have hb := fibreCoefficientPairs_bounds ha
  simp only [fibreCoefficientComplement]
  omega

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Exact real and imaginary frequency geometry for the literal two-coordinate fibre norm. -/

theorem fibreNorm_real_cast_sq (x : Vec 2) :
    fibreNorm (fun j => (x j : ℂ)) ^ 2 = ∑ j, x j ^ 2 := by
  rw [fibreNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem fibreNorm_complex_parts_sq (x y : Vec 2) :
    fibreNorm (fun j => (x j : ℂ) + Complex.I * (y j : ℂ)) ^ 2 =
      (∑ j, x j ^ 2) + ∑ j, y j ^ 2 := by
  rw [fibreNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Fin.sum_univ_two]
  ring

theorem fibreNorm_real_projection_le (x y : Vec 2) :
    fibreNorm (fun j => (x j : ℂ)) ≤ fibreNorm (fun j => (x j : ℂ) + Complex.I * (y j : ℂ)) := by
  have hx := fibreNorm_real_cast_sq x
  have hxy := fibreNorm_complex_parts_sq x y
  have hy : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [fibreNorm_nonneg (fun j => (x j : ℂ)),
    fibreNorm_nonneg (fun j => (x j : ℂ) + Complex.I * (y j : ℂ))]

theorem fibreNorm_imaginary_part_le (x y : Vec 2) :
    Real.sqrt (∑ j, y j ^ 2) ≤ fibreNorm (fun j => (x j : ℂ) + Complex.I * (y j : ℂ)) := by
  have hxy := fibreNorm_complex_parts_sq x y
  have hx : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy : Real.sqrt (∑ j, y j ^ 2) ^ 2 = ∑ j, y j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (y j)))
  nlinarith [Real.sqrt_nonneg (∑ j, y j ^ 2),
    fibreNorm_nonneg (fun j => (x j : ℂ) + Complex.I * (y j : ℂ))]

theorem fibreNorm_complex_real_difference (x y : Vec 2) :
    fibreNorm (fun j => ((x j : ℂ) + Complex.I * (y j : ℂ)) - (x j : ℂ)) =
      Real.sqrt (∑ j, y j ^ 2) := by
  simp only [add_sub_cancel_left, fibreNorm, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Literal gradient components are bounded by the finite-array gradient norm. -/

/-- Spatial L2 control of a raw gradient controls each raw first derivative. -/
theorem cellGradComp_cellL2Norm_le (D : RawJet2 1 ℂ) (j : Fin 2)
    (hm : AEStronglyMeasurable (cellGradComp D j) (volume.restrict AVenhance.unitCube)) :
    cellL2Norm (cellGradComp D j) ≤ cellL2Norm (cellGradient D) := by
  apply eLpNorm_mono_ae hm
  exact Filter.Eventually.of_forall (fun x => PiLp.norm_apply_le (cellGradient D x) j)

/-- Joint L2 control of a raw gradient controls each raw first derivative on any time set. -/
theorem cellGradComp_product_eLpNorm_le (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ) (j : Fin 2)
    (hm : AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellGradComp (D p.1) j p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    eLpNorm (fun p : ℝ × Vec 2 => cellGradComp (D p.1) j p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) ≤
    eLpNorm (fun p : ℝ × Vec 2 => cellGradient (D p.1) p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  apply eLpNorm_mono_ae hm
  exact Filter.Eventually.of_forall (fun p : ℝ × Vec 2 => PiLp.norm_apply_le (cellGradient (D p.1) p.2) j)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Product L² membership from the raw cell energy integral and joint measurability. -/

/-- A jointly strongly measurable field with finite cell energy is product-space L². -/
theorem cellJoint_memLp_of_cellNorm {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f : ℝ → Vec 2 → E)
    (hm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (h2 : ∫⁻ t in I, cellL2Norm (f t) ^ 2 < ⊤) :
    MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  change eLpNorm (Function.uncurry f) 2 _ < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp) hm]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_prod _ (hm.enorm.pow_const 2)]
  apply lt_of_eq_of_lt _ h2
  apply lintegral_congr_ae
  filter_upwards [hm.prodMk_left] with t ht
  exact (cellL2Norm_sq_eq_lintegral ht).symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute summation and integration of the fixed-test products in cell equations. -/

/-- Absolute L2 summability gives absolute L1 summability after multiplication by an L2 test. -/
theorem cellL2_product_series_lintegral_lt_top {J X : Type*} [Countable J] [MeasurableSpace X]
    (μ : Measure X) (f : J → X → ℂ) (g : X → ℂ)
    (hf : ∀ j, AEStronglyMeasurable (f j) μ) (hg : MemLp g 2 μ)
    (hs : (∑' j, eLpNorm (f j) 2 μ) < ⊤) :
    (∑' j, ∫⁻ x, ‖f j x * g x‖ₑ ∂μ) < ⊤ := by
  calc
    _ ≤ ∑' j, eLpNorm (f j) 2 μ * eLpNorm g 2 μ :=
      ENNReal.tsum_le_tsum (fun j => cellL2_product_lintegral_le μ (f j) g (hf j) hg.aestronglyMeasurable)
    _ = (∑' j, eLpNorm (f j) 2 μ) * eLpNorm g 2 μ := ENNReal.tsum_mul_right
    _ < ⊤ := ENNReal.mul_lt_top hs hg.eLpNorm_lt_top

/-- The fixed-test pairing of a literal L2 series equals the series of the actual pairings. -/
theorem cellL2_product_series_integral {J X : Type*} [Countable J] [MeasurableSpace X]
    (μ : Measure X) (f : J → X → ℂ) (g : X → ℂ)
    (hf : ∀ j, AEStronglyMeasurable (f j) μ) (hg : MemLp g 2 μ)
    (hs : (∑' j, eLpNorm (f j) 2 μ) < ⊤) :
    (∫ x, (∑' j, f j x) * g x ∂μ) = ∑' j, ∫ x, f j x * g x ∂μ := by
  have he : (fun x => (∑' j, f j x) * g x) = (fun x => ∑' j, f j x * g x) := by
    funext x
    exact tsum_mul_right.symm
  rw [he]
  exact integral_tsum (fun j => (hf j).mul hg.aestronglyMeasurable)
    (cellL2_product_series_lintegral_lt_top μ f g hf hg hs).ne

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Pointwise Gårding bound for complex Bloch diffusion. -/

/-- The lower-order Bloch perturbation in each spatial direction. -/
def cellBlochShift (θ : Fin 2 → ℂ) (u : ℂ) : Fin 2 → ℂ := fun j => Complex.I * θ j * u

/-- Exact squared norm of the Bloch perturbation. -/
theorem cellBlochShift_norm_sq (θ : Fin 2 → ℂ) (u : ℂ) :
    (∑ j, ‖cellBlochShift θ u j‖ ^ 2) = (∑ j, ‖θ j‖ ^ 2) * ‖u‖ ^ 2 := by
  simp only [cellBlochShift, norm_mul, Complex.norm_I, one_mul, mul_pow, Finset.sum_mul]

/-- Complex conjugation of the Bloch parameter preserves its squared size. -/
theorem cellBlochShift_star_norm_sq (θ : Fin 2 → ℂ) (u : ℂ) :
    (∑ j, ‖cellBlochShift (fun i => star (θ i)) u j‖ ^ 2) =
      (∑ j, ‖θ j‖ ^ 2) * ‖u‖ ^ 2 := by
  simp only [cellBlochShift_norm_sq, norm_star]

/-- Uniform diffusion Gårding inequality, including arbitrary complex Bloch shift. -/
theorem cellDiffusion_pointwise_garding
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (x : Vec 2) (θ p : Fin 2 → ℂ) (u : ℂ) :
    2 * (-cellMetricPairing (G t x) (p + cellBlochShift θ u)
      (p + cellBlochShift (fun i => star (θ i)) u)) +
      (3 / 4) * ∑ j, ‖p j‖ ^ 2 ≤ 264 * (∑ j, ‖θ j‖ ^ 2) * ‖u‖ ^ 2 := by
  have he := cellMetric_complex_coercive hG t x p
  change (1 / 2) * ∑ j, ‖p j‖ ^ 2 ≤ cellMetricPairing (G t x) p p at he
  have hb := cellMetric_entry_bound hG t x
  have h1 := cellMetricPairing_young (G t x) hb p
    (cellBlochShift (fun i => star (θ i)) u)
  have h2 := cellMetricPairing_young (G t x) hb p (cellBlochShift θ u)
  rw [cellMetricPairing_symm (G t x) (hG.2.2.1 t x) p (cellBlochShift θ u)] at h2
  have h3 := cellMetricPairing_quadratic (G t x) hb
    (cellBlochShift θ u) (cellBlochShift (fun i => star (θ i)) u)
  rw [cellBlochShift_star_norm_sq] at h1
  rw [cellBlochShift_norm_sq] at h2
  rw [cellBlochShift_norm_sq, cellBlochShift_star_norm_sq] at h3
  rw [cellMetricPairing_add]
  have h1l := (abs_le.mp h1).1
  have h2l := (abs_le.mp h2).1
  have h3l := (abs_le.mp h3).1
  linarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Admissibility of the time-reversed metric and opposite drift for the dual graph. -/

theorem cellMetric_timeReverse {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) : IsCellMetric (fun t x => G (-t) x) := by
  refine ⟨hG.1.comp ((measurable_neg.comp measurable_fst).prodMk measurable_snd),
    fun t => hG.2.1 (-t), fun t x => hG.2.2.1 (-t) x,
    fun t x ξ => hG.2.2.2 (-t) x ξ⟩

theorem cellDrift_timeReverse {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) : IsCellDrift (fun t x => -v (-t) x) := by
  refine ⟨(hv.1.comp ((measurable_neg.comp measurable_fst).prodMk measurable_snd)).neg,
    ?_, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hv.2.1
    exact ⟨M, fun t x => by simpa using hM (-t) x⟩
  · intro t n x
    exact congrArg Neg.neg (hv.2.2.1 (-t) n x)
  · intro t φ
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, integral_neg,
      hv.2.2.2 (-t) φ, neg_zero]

theorem cellDrift_timeReverse_scaled_bound {v : ℝ → Vec 2 → Vec 2} {η Cw : ℝ}
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ∀ t x, Real.sqrt η * Real.sqrt (∑ i, (-v (-t) x) i ^ 2) ≤ Cw := by
  intro t x
  simpa using hw (-t) x

theorem cellDrift_timeReverse_mean_zero {v : ℝ → Vec 2 → Vec 2}
    (hm : ∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0) :
    ∀ t (k : Fin 2), cellMean (fun x => ((-v (-t) x) k : ℂ)) = 0 := by
  intro t k
  simp only [cellMean, Pi.neg_apply, Complex.ofReal_neg, integral_neg]
  exact neg_eq_zero.mpr (hm (-t) k)

end AVRegularity.CycleEvolution
end
end
