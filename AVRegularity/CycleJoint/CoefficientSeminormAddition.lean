-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleWords.IsGeometryCover
public import AVRegularity.CycleWords.QuietDurationAlgebra
import AVRegularity.CycleJoint.WeightedLocalLpBound
import AVRegularity.CycleWords.CellAffineHomeomorph
import AVRegularity.Weighted.PlaneH1Readouts
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
import AVRegularity.CycleWords.LowerCarrierTimeIntegrability
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! The same weights certify every lower moment reserve. -/

def chartWeightsReserveRestriction
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {a S ϖ : ℝ} {zc : Vec 2} {n N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v a S ϖ zc N Cw) (hn : n ≤ N) :
    ChartWeights G v a S ϖ zc n Cw where
  W := W.W
  Phi := W.Phi
  lam := W.lam
  smooth := fun m hm => W.smooth m (hm.trans hn)
  pos := fun m hm => W.pos m (hm.trans hn)
  comparable := fun m hm => W.comparable m (hm.trans hn)
  defect := fun m hm => W.defect m (hm.trans hn)
  bound := fun m hm => W.bound m (hm.trans hn)
  lam_bound := fun m hm => W.lam_bound m (hm.trans hn)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Piola lowering preserves the positive molecular price when the sampling radius is below E. -/

theorem molecular_order_lowering_normalization (ν ρ E : ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ) (hE : 0 < E) (hρE : ρ ≤ E)
    (K low extra : ℕ) (M : ℝ≥0∞) :
    E⁻¹ ^ extra * M.toReal * (ν * ρ ^ low)⁻¹ *
      (((K + low).factorial : ℝ) / (K.factorial : ℝ)) ≤
        molecularRealPrice ν ρ K (low + extra) M := by
  have hK : (K.factorial : ℝ) ≠ 0 := by positivity
  have hF : 0 < ((K + (low + extra)).factorial : ℝ) := by positivity
  have hρp : ρ ^ low ≠ 0 := pow_ne_zero _ hρ.ne'
  have he : (ρ / E) ^ extra ≤ 1 :=
    pow_le_one₀ (div_nonneg hρ.le hE.le) ((div_le_one hE).mpr hρE)
  have hfac : ((K + low).factorial : ℝ) / ((K + (low + extra)).factorial : ℝ) ≤ 1 := by
    apply (div_le_one hF).mpr
    exact_mod_cast Nat.factorial_le (by omega : K + low ≤ K + (low + extra))
  have hprice : 0 ≤ molecularRealPrice ν ρ K (low + extra) M :=
    molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _
  calc
    _ = (ρ / E) ^ extra * molecularRealPrice ν ρ K (low + extra) M *
        (((K + low).factorial : ℝ) / ((K + (low + extra)).factorial : ℝ)) := by
      unfold molecularRealPrice
      rw [pow_add, div_pow, inv_pow]
      field_simp [hν.ne', hρ.ne', hE.ne']
    _ ≤ 1 * molecularRealPrice ν ρ K (low + extra) M * 1 := by gcongr
    _ = _ := by simp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Affine cell composition preserves every finite plane Lp class. -/

theorem plane_affine_quasiMeasurePreserving (e : ℝ) (he : e ≠ 0) (y : Vec 2) :
    Measure.QuasiMeasurePreserving (fun z : Vec 2 => y + e • z) volume volume := by
  refine ⟨by fun_prop, ?_⟩
  rw [CycleWords.map_cell_affine_volume e he y]
  exact Measure.smul_absolutelyContinuous

variable {E : Type*} [NormedAddCommGroup E]

theorem memLp_plane_affine {p : ℝ≥0∞} {f : Vec 2 → E}
    (hf : MemLp f p (volume : Measure (Vec 2)))
    (e : ℝ) (he : e ≠ 0) (y : Vec 2) :
    MemLp (fun z : Vec 2 => f (y + e • z)) p volume := by
  have hm := hf.smul_measure (c := ENNReal.ofReal |(e ^ 2)⁻¹|) ENNReal.ofReal_ne_top
  rw [← CycleWords.map_cell_affine_volume e he y] at hm
  exact hm.comp_of_map (by fun_prop)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Translation preserves the global weighted L2 norm used in local image estimates. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem translatedWeighted_eLpNorm_le (f : Vec 2 → E) (q : Vec 2 → ℝ)
    (U : Set (Vec 2)) (a : Vec 2) (c : ℝ) (hc : 0 ≤ c)
    (hf : AEStronglyMeasurable (fun x => f (x + a)) (volume.restrict U))
    (hqf : AEStronglyMeasurable (fun x => q x • f x) volume)
    (hq : ∀ᵐ x ∂volume.restrict U, 1 ≤ c * q (x + a)) :
    eLpNorm (fun x => f (x + a)) 2 (volume.restrict U) ≤
      ENNReal.ofReal c * eLpNorm (fun x => q x • f x) 2 volume := by
  have he := weightedLocal_eLpNorm_le (fun x => f (x + a)) (fun x => q (x + a))
    (volume.restrict U) c hc hf hq
  have hm : eLpNorm (fun x => q (x + a) • f (x + a)) 2 (volume.restrict U) ≤
      eLpNorm (fun x => q x • f x) 2 volume := by
    apply (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
    exact (eLpNorm_comp_measurePreserving hqf (measurePreserving_add_right volume a)).le
  exact he.trans (mul_le_mul (le_refl _) hm zero_le zero_le)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Exact Bochner change of variables for the spatial cell chart. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_plane_affine (e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (f : Vec 2 → E) :
    (∫ z : Vec 2, f (y + e • z)) = |(e ^ 2)⁻¹| • ∫ x : Vec 2, f x := by
  have h := integral_map_equiv (μ := (volume : Measure (Vec 2)))
    (CycleWords.cellAffineHomeomorph e he y).toMeasurableEquiv f
  change (∫ x : Vec 2, f x ∂Measure.map (fun z => y + e • z) volume) = _ at h
  rw [CycleWords.map_cell_affine_volume e he y, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)] at h
  exact h.symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Exact nonnegative integral prices for cell coordinates, including unbounded moment weights. -/

theorem lintegral_plane_affine (e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (f : Vec 2 → ℝ≥0∞) :
    (∫⁻ z : Vec 2, f (y + e • z)) =
      ENNReal.ofReal |(e ^ 2)⁻¹| * ∫⁻ x : Vec 2, f x := by
  have h := lintegral_map_equiv (μ := (volume : Measure (Vec 2))) f
    (CycleWords.cellAffineHomeomorph e he y).toMeasurableEquiv
  change (∫⁻ x : Vec 2, f x ∂Measure.map (fun z => y + e • z) volume) = _ at h
  rw [CycleWords.map_cell_affine_volume e he y, lintegral_smul_measure] at h
  exact h.symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite positive coefficient budgets survive assembly of smooth constituents. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientDerivativeArray_sum {ι : Type*} (s : Finset ι)
    (A : ι → Vec 2 → E →L[ℝ] F) (j : ℕ)
    (hA : ∀ i ∈ s, ContDiff ℝ (j : ℕ) (A i)) (x : Vec 2) :
    coefficientDerivativeArray (fun y => ∑ i ∈ s, A i y) j x =
      ∑ i ∈ s, coefficientDerivativeArray (A i) j x := by
  have hs : ContDiff ℝ (j : ℕ) (fun y => ∑ i ∈ s, A i y) := ContDiff.sum hA
  ext z w
  simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply, coefficientDerivativeArray_apply]
  rw [Weighted.orderedCoefficientDerivative_eq_iterated _ j hs]
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => (hA i hi).contDiffAt)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Weighted.orderedCoefficientDerivative_eq_iterated _ j (hA i hi)]

theorem coefficientSeminorm_sum_le {ι : Type*} (s : Finset ι)
    (A : ι → ℝ → Vec 2 → E →L[ℝ] F) (ρ : ℝ) (K : ℕ) (a b : ℝ)
    (hA : ∀ i ∈ s, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A i t)) :
    coefficientSeminorm ρ K a b (fun t x => ∑ i ∈ s, A i t x) ≤
      ∑ i ∈ s, coefficientSeminorm ρ K a b (A i) := by
  unfold coefficientSeminorm
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  have hjK : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  apply iSup_le
  intro x
  rw [coefficientDerivativeArray_sum s _ j
    (fun i hi => (hA i hi t ht).of_le (by exact_mod_cast hjK))]
  calc
    _ ≤ ∑ i ∈ s, (‖coefficientDerivativeArray (A i t) j x‖₊ : ℝ≥0∞) := by
      exact_mod_cast nnnorm_sum_le s (fun i => coefficientDerivativeArray (A i t) j x)
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      le_iSup_of_le t (le_iSup_of_le ht
        (le_iSup (fun y : Vec 2 => (‖coefficientDerivativeArray (A i t) j y‖₊ : ℝ≥0∞)) x)))

theorem coefficientSeminorm_sum_ne_top {ι : Type*} (s : Finset ι)
    (A : ι → ℝ → Vec 2 → E →L[ℝ] F) (ρ : ℝ) (K : ℕ) (a b : ℝ)
    (hA : ∀ i ∈ s, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A i t))
    (hfinite : ∀ i ∈ s, coefficientSeminorm ρ K a b (A i) ≠ ⊤) :
    coefficientSeminorm ρ K a b (fun t x => ∑ i ∈ s, A i t x) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr hfinite)
    (coefficientSeminorm_sum_le s A ρ K a b hA)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A prescribed curve of spatial L2 classes inherits its Bochner L2 class from a joint representative. -/

variable {T X E : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bochner_memLp_of_joint_representation (μ : Measure T) (ν : Measure X)
    [SFinite μ] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]
    (f : T × X → E) (hf : MemLp f 2 (μ.prod ν)) (u : T → Lp E 2 ν)
    (he : ∀ᵐ t ∂μ, (u t : X → E) =ᵐ[ν] fun x => f (t, x)) : MemLp u 2 μ := by
  let P := hf.toLp f
  let F := fun p : T × X => P p
  have hF : MemLp F 2 (μ.prod ν) := Lp.memLp P
  have hS := bochnerL2TotalSlice_memLp μ ν (Function.curry F) (Lp.stronglyMeasurable P) hF
  apply hS.ae_eq
  have hp : ∀ᵐ t ∂μ, (fun x => F (t, x)) =ᵐ[ν] fun x => f (t, x) :=
    Measure.ae_ae_of_ae_prod (show F =ᵐ[μ.prod ν] f from hf.coeFn_toLp)
  filter_upwards [hp, he, bochnerL2Product_memLp_slices μ ν (Function.curry F) hF]
    with t ht het hft
  apply Lp.ext
  exact (bochnerL2TotalSlice_ae ν (Function.curry F) t hft).trans (ht.trans het.symm)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Two actual smooth coefficient arrays retain finite coefficient reserves under addition. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientSeminorm_add_ne_top (A B : ℝ → Vec 2 → E →L[ℝ] F)
    (ρ : ℝ) (K : ℕ) (a b : ℝ)
    (hA : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (hB : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (B t))
    (hAf : coefficientSeminorm ρ K a b A ≠ ⊤)
    (hBf : coefficientSeminorm ρ K a b B ≠ ⊤) :
    coefficientSeminorm ρ K a b (fun t z => A t z + B t z) ≠ ⊤ := by
  let C : Fin 2 → ℝ → Vec 2 → E →L[ℝ] F := fun i => if i = 0 then A else B
  have hc : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ∀ t ∈ Set.Icc a b,
      ContDiff ℝ (K : ℕ) (C i t) := by
    intro i _ t ht
    fin_cases i
    · exact hA t ht
    · exact hB t ht
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 2)), coefficientSeminorm ρ K a b (C i) ≠ ⊤ := by
    intro i _
    fin_cases i
    · exact hAf
    · exact hBf
  simpa [C, Fin.sum_univ_two] using coefficientSeminorm_sum_ne_top Finset.univ C ρ K a b hc hf

end AVRegularity.CycleJointProofs
end
end
