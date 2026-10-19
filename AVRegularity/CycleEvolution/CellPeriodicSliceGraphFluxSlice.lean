-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellMetricJetFluxDerivative
import AVRegularity.CycleEvolution.FibreCoefficientConvolutionSum
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice

@[expose] public noncomputable section

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Finite shift sums of two-variable Taylor coefficients inject into two copies of the lower degree set. -/

/-- The two coordinate shifts count each lower coefficient at most twice. -/
theorem fibreCoefficient_shift_sum_le (K : ℕ) (a : ℕ × ℕ → ℝ≥0∞) :
    (∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
      a (fibreCoefficientPrevious p j)) ≤ 2 * ∑ q ∈ jetIndices K, a q := by
  classical
  let S := (jetIndices (K + 1)).sigma fibreCoefficientDirections
  let f : (Σ _ : ℕ × ℕ, Fin 2) → Fin 2 × (ℕ × ℕ) :=
    fun p => (p.2, fibreCoefficientPrevious p.1 p.2)
  have hf : Set.InjOn f (↑S : Set (Σ _ : ℕ × ℕ, Fin 2)) := by
    intro p hp q hq he
    have hp' := Finset.mem_sigma.mp hp
    have hq' := Finset.mem_sigma.mp hq
    have hj : p.2 = q.2 := congrArg Prod.fst he
    have hprev : fibreCoefficientPrevious p.1 p.2 = fibreCoefficientPrevious q.1 q.2 :=
      congrArg Prod.snd he
    have hindex : p.1 = q.1 := by
      rw [← fibreCoefficientPrevious_recover hp'.2, ← fibreCoefficientPrevious_recover hq'.2]
      rw [hprev, hj]
    cases p
    cases q
    dsimp at hindex hj
    cases hindex
    cases hj
    rfl
  have hsub : S.image f ⊆ Finset.univ ×ˢ jetIndices K := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq', hj⟩ := Finset.mem_sigma.mp hq
    have horder := fibreCoefficientPrevious_order hj
    have hqorder := (mem_jetIndices_iff (K + 1) q.1).mp hq'
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (mem_jetIndices_iff K _).mpr (by dsimp only [f]; omega)⟩
  calc
    _ = ∑ p ∈ S, a (f p).2 := by rw [Finset.sum_sigma]
    _ = ∑ p ∈ S.image f, a p.2 :=
      (Finset.sum_image (f := fun p : Fin 2 × (ℕ × ℕ) => a p.2) hf).symm
    _ ≤ ∑ p ∈ Finset.univ ×ˢ jetIndices K, a p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
    _ = _ := by rw [Finset.sum_product]; simp only [Fin.sum_univ_two]; rw [two_mul]

/-! The constant forcing occupies only the two coefficients of degree one. -/

/-- The constant part of the weighted source has at most two frequency factors. -/
theorem fibreCoefficient_weighted_constant_le (K : ℕ) (ρ : ℝ≥0∞) :
    (∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
      fibreCoefficientWeight ρ p * (if p = cellJetDirection j then 1 else 0)) ≤ 2 * ρ := by
  calc
    _ ≤ ∑ p ∈ jetIndices (K + 1), ∑ j : Fin 2,
        fibreCoefficientWeight ρ p * (if p = cellJetDirection j then 1 else 0) := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ j : Fin 2, ∑ p ∈ jetIndices (K + 1),
        fibreCoefficientWeight ρ p * (if p = cellJetDirection j then 1 else 0) :=
      Finset.sum_comm
    _ = ∑ _j : Fin 2, ρ := by
      apply Finset.sum_congr rfl
      intro j _
      have ho : (cellJetDirection j).1 + (cellJetDirection j).2 = 1 := by
        fin_cases j <;> simp [cellJetDirection]
      have hm : cellJetDirection j ∈ jetIndices (K + 1) :=
        (mem_jetIndices_iff _ _).mpr (by rw [ho]; omega)
      rw [Finset.sum_eq_single (cellJetDirection j)]
      · simp [fibreCoefficientWeight, ho]
      · intro p _ hp
        simp only [ite_eq_right hp, mul_zero]
      · exact fun h => (h hm).elim
    _ = _ := by simp

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The shifted transport form and its conjugate-frequency adjoint. -/

def cellComplexShiftedDriftForm (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : IsCellDrift v) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) : ℂ :=
  cellComplexDriftForm v V hv hb t u z + ∑ j : Fin 2,
    (Complex.I * θ j) * cellComplexPair
      (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (torusHkValueCLM u))
      (torusHkValueCLM z)

theorem cellComplexShiftedDriftForm_eq_sum {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexShiftedDriftForm v V hv hb θ t u z = ∑ j : Fin 2,
      cellComplexPair (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j
        (cellShiftedDerivativeCLM θ j u)) (torusHkValueCLM z) := by
  unfold cellComplexShiftedDriftForm
  rw [cellComplexDriftForm_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [cellShiftedDerivativeCLM, add_apply, ContinuousLinearMap.comp_apply, map_add,
    cellComplexPair_add_left, cellDriftEntryCLM_scalar, cellComplexPair_scalar_left]

theorem cellComplexShiftedDriftForm_adjoint {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexShiftedDriftForm v V hv hb θ t u z =
      -star (cellComplexShiftedDriftForm v V hv hb (fun j => star (θ j)) t z u) := by
  unfold cellComplexShiftedDriftForm
  rw [cellComplexDriftForm_skew hv V hb t u z, star_add, neg_add,
    star_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [star_mul, star_mul, star_star, show star Complex.I = -Complex.I from Complex.conj_I]
  rw [cellDriftEntryCLM_complex_adjoint, cellComplexPair_symm (torusHkValueCLM u)]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Integrable complex spatial expressions for every H¹ test of the cell equation. -/

/-- The complex cell spatial expression written with class representatives. -/
def cellComplexSpatial (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (x : Vec 2) : ℂ :=
  -(∑ j : Fin 2, ∑ k : Fin 2,
    cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM C.θ j u) x *
      star (cellShiftedDerivativeCLM (fun i => star (C.θ i)) k z x)) -
  (∑ j : Fin 2, cellDriftEntryCLM C V hv hb t j (cellShiftedDerivativeCLM C.θ j u) x *
    star (torusHkValueCLM z x)) +
  cellScalarCLM (C.κ t) (torusHkValueCLM u) x * star (torusHkValueCLM z x) +
  S x * star (torusHkValueCLM z x) - ∑ j : Fin 2,
    F j x * star (cellShiftedDerivativeCLM (fun i => star (C.θ i)) j z x)

/-- Every term is a product of two L² classes, so the literal complex expression is integrable. -/
theorem cellComplexSpatial_integrable (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    Integrable (cellComplexSpatial C hG V hv hb t u z S F) (volume.restrict AVenhance.unitCube) := by
  have hm := integrable_finsetSum' Finset.univ (fun j _ =>
    integrable_finsetSum' Finset.univ (fun k _ => cellComplex_pairing_integrable
      (cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM C.θ j u))
      (cellShiftedDerivativeCLM (fun i => star (C.θ i)) k z)))
  have hd := integrable_finsetSum' Finset.univ (fun j _ => cellComplex_pairing_integrable
    (cellDriftEntryCLM C V hv hb t j (cellShiftedDerivativeCLM C.θ j u)) (torusHkValueCLM z))
  have hp := cellComplex_pairing_integrable (cellScalarCLM (C.κ t) (torusHkValueCLM u)) (torusHkValueCLM z)
  have hs := cellComplex_pairing_integrable S (torusHkValueCLM z)
  have hf := integrable_finsetSum' Finset.univ (fun j _ => cellComplex_pairing_integrable (F j)
    (cellShiftedDerivativeCLM (fun i => star (C.θ i)) j z))
  have hi := ((hm.neg.sub hd).add hp).add hs |>.sub hf
  apply hi.congr
  filter_upwards with x
  simp only [cellComplexSpatial, Finset.sum_apply, Pi.neg_apply, Pi.sub_apply, Pi.add_apply]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Countable measurable time selection of local jointly measurable cell representatives. -/

/-- Choosing one local field on each measurable time piece preserves joint almost-everywhere measurability. -/
theorem cellJoint_selected_aestronglyMeasurable (μ : Measure ℝ) [SFinite μ] (k : ℝ → ℕ) (hk : Measurable k)
    (I : ℕ → Set ℝ) (hmem : ∀ t, t ∈ I (k t))
    (f : ℕ → ℝ → Vec 2 → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (Function.uncurry (f n))
      ((μ.restrict (I n)).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => f (k p.1) p.1 p.2)
      (μ.prod (volume.restrict AVenhance.unitCube)) := by
  let A : ℕ → Set (ℝ × Vec 2) := fun n => {p | k p.1 = n}
  have hm (n : ℕ) : MeasurableSet (A n) := (hk.comp measurable_fst) (measurableSet_singleton n)
  have hloc (n : ℕ) : AEStronglyMeasurable (fun p : ℝ × Vec 2 => f (k p.1) p.1 p.2)
      ((μ.prod (volume.restrict AVenhance.unitCube)).restrict (A n)) := by
    have hsub : A n ⊆ I n ×ˢ (univ : Set (Vec 2)) := by
      intro p hp
      have ht := hmem p.1
      rw [show k p.1 = n from hp] at ht
      exact ⟨ht, mem_univ _⟩
    have hμ : (μ.prod (volume.restrict AVenhance.unitCube)).restrict (A n) ≤
        (μ.restrict (I n)).prod (volume.restrict AVenhance.unitCube) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact Measure.restrict_mono hsub le_rfl
    apply ((hf n).mono_measure hμ).congr
    filter_upwards [ae_restrict_mem (hm n)] with p hp
    dsimp only [Function.uncurry_def]
    rw [show k p.1 = n from hp]
  have hcover : (⋃ n, A n) = univ := by
    apply eq_univ_of_forall
    intro p
    exact mem_iUnion.mpr ⟨k p.1, rfl⟩
  have hall := AEStronglyMeasurable.iUnion hloc
  rw [hcover, Measure.restrict_univ] at hall
  exact hall

/-- A measurable index selecting a compact time interval that contains the given time. -/
def cellLocalTimeIndex (t : ℝ) : ℕ := ⌊|t|⌋₊ + 1

/-- The time-selection index is measurable. -/
theorem cellLocalTimeIndex_measurable : Measurable cellLocalTimeIndex :=
  (measurable_id.abs.nat_floor).add_const 1

/-- Each time belongs to the compact interval selected by its index. -/
theorem cellLocalTimeIndex_mem (t : ℝ) :
    t ∈ Icc (-(cellLocalTimeIndex t : ℝ)) (cellLocalTimeIndex t) := by
  have h := Nat.lt_floor_add_one |t|
  have he : (cellLocalTimeIndex t : ℝ) = (⌊|t|⌋₊ : ℝ) + 1 := by
    simp only [cellLocalTimeIndex, Nat.cast_add, Nat.cast_one]
  rw [he]
  constructor
  · have := neg_abs_le t; linarith
  · have := le_abs_self t; linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Exact energy production and spectral coercivity of the unshifted cell generator. -/

/-- Zero Bloch shift is the genuine weak derivative operator. -/
theorem cellShiftedDerivative_zero (j : Fin 2) :
    cellShiftedDerivativeCLM 0 j = cellDerivativeCLM j := by
  simp only [cellShiftedDerivativeCLM, Pi.zero_apply, mul_zero, cellScalarCLM, map_zero,
    ContinuousLinearMap.zero_comp, add_zero]

/-- Before drift cancellation the generator is minus metric dissipation minus transport. -/
theorem cellUnshiftedGenerator_energy {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellGeneratorForm ⟨G, v, 0, 0⟩ hG V hv hb t u u =
      -cellMetricEnergy hG t u - cellDriftForm v V hv hb t u u := by
  simp only [cellGeneratorForm, cellDiffusionForm, cellDriftForm, cellMetricEnergy,
    cellShiftedDerivative_zero, Pi.zero_apply, star_zero, cellScalarCLM, map_zero,
    add_apply, sub_apply, neg_apply, sum_apply, pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply, zero_apply, inner_zero_left, add_zero]
  simp only [show (fun _ : Fin 2 => (0 : ℂ)) = 0 from rfl, cellShiftedDerivative_zero]
  rfl

/-- For the actual weak divergence-free drift the generator energy is exactly minus dissipation. -/
theorem cellUnshiftedGenerator_drift_neutral {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellGeneratorForm ⟨G, v, 0, 0⟩ hG V hv.1 hb t u u = -cellMetricEnergy hG t u := by
  rw [cellUnshiftedGenerator_energy, cellDriftForm_energy_zero hv V hb t u, sub_zero]

/-- Mean-zero generator dissipation has spectral gap 2π², uniformly in the drift size. -/
theorem cellUnshiftedGenerator_meanZero_gap {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0) :
    cellGeneratorForm ⟨G, v, 0, 0⟩ hG V hv.1 hb t u u ≤
      -(2 * Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2) := by
  rw [cellUnshiftedGenerator_drift_neutral hG hv]
  exact neg_le_neg (cellMetricEnergy_meanZero_gap hG t u hm)

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! The finite factorial majorant derived from the actual triangular cell norm recurrence. -/

/-- A binomial triangular norm recurrence yields the literal factorial estimate after half absorption. -/
theorem factorialJetMajorant (K : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (C : ℝ≥0∞) (A G E : ℕ × ℕ → ℝ≥0∞)
    (hE : ∀ α ∈ jetIndices K, E α < ⊤)
    (hrec : ∀ α ∈ jetIndices K, E α ≤ C *
      (A α + ∑ β ∈ cellJetFluxIndices α,
        (cellJetChoose α β : ℝ≥0∞) * G β * E (α.1 - β.1, α.2 - β.2)))
    (hsmall : C * factorialJetSum ((jetIndices K).erase 0) ρ G ≤ 1 / 2) :
    factorialJetSum (jetIndices K) ρ E ≤
      (2 * C) * factorialJetSum (jetIndices K) ρ A := by
  let w := fun α => ENNReal.ofReal (cellJetWeightReal ρ α)
  let V := factorialJetSum (jetIndices K) ρ E
  let B := factorialJetSum (jetIndices K) ρ A
  let H := factorialJetSum ((jetIndices K).erase 0) ρ G
  have hV : V < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro α hα
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hE α hα)
  have hb : V ≤ C * B + (1 / 2 : ℝ≥0∞) * V := by
    calc
      V ≤ ∑ α ∈ jetIndices K, w α * (C *
          (A α + ∑ β ∈ cellJetFluxIndices α,
            (cellJetChoose α β : ℝ≥0∞) * G β * E (α.1 - β.1, α.2 - β.2))) := by
        apply Finset.sum_le_sum
        intro α hα
        change w α * E α ≤ _
        gcongr
        exact hrec α hα
      _ = C * (B + ∑ α ∈ jetIndices K, w α *
          ∑ β ∈ cellJetFluxIndices α,
            (cellJetChoose α β : ℝ≥0∞) * G β * E (α.1 - β.1, α.2 - β.2)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, B, factorialJetSum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro α _ <;> ac_rfl
      _ ≤ C * (B + H * V) := by
        gcongr
        exact factorialJetConvolution_le_product hρ K G E
      _ = C * B + (C * H) * V := by ring
      _ ≤ C * B + (1 / 2 : ℝ≥0∞) * V := by gcongr
  have hh := ennreal_half_absorption V (C * B) hV hb
  simpa only [mul_assoc] using hh

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! The actual convergent row coefficient series equals its scalar normalization times its graph. -/

theorem fibreRowCoefficients_series_pointwise (k : ℕ × ℕ → ℝ → ℂ)
    (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2)
    (hk : Summable (fun p => ‖fibreMonomial ξ p * k p t‖))
    (ha : Summable (fun p => ‖fibreMonomial ξ p * a p t x‖)) :
    fibreSeriesFun (fibreRowCoefficients k a) ξ t x =
      fibreSeriesC k ξ t * (1 + fibreSeriesFun a ξ t x) := by
  have hc := fibreMonomial_convolution_summable ξ (fun p => k p t) (fun p => a p t x) hk ha
  have he := fibreMonomial_cauchy_product ξ (fun p => k p t) (fun p => a p t x) hk ha
  change (∑' p, fibreMonomial ξ p *
    (k p t + ∑ q ∈ fibreCoefficientPairs p, k q t * a (fibreCoefficientComplement p q) t x)) = _
  simp only [mul_add]
  rw [hk.of_norm.tsum_add hc, ← he]
  change (∑' p, fibreMonomial ξ p * k p t) +
      (∑' p, fibreMonomial ξ p * k p t) * (∑' p, fibreMonomial ξ p * a p t x) = _
  unfold fibreSeriesC fibreSeriesFun
  ring

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Transport is energy-neutral for real Bloch frequencies. -/

theorem cellComplexShiftedDriftForm_real_diagonal {v : ℝ → Vec 2 → Vec 2}
    (V : ℝ) (hv : IsCellDrift v) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j) (t : ℝ) (u : TorusHk 1 ℂ) :
    (cellComplexShiftedDriftForm v V hv hb θ t u u).re = 0 := by
  have he : (fun j => star (θ j)) = θ := funext hθ
  have hs := cellComplexShiftedDriftForm_adjoint hv V hb θ t u u
  rw [he] at hs
  have hr := congrArg Complex.re hs
  simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at hr
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The literal complex spatial integral equals the actual complex weak cell form. -/

/-- Spatial integration of the complex expression reads the exact generator and source forms. -/
theorem cellComplexSpatial_integral (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    (∫ x in AVenhance.unitCube, cellComplexSpatial C hG V hv hb t u z S F x) =
      cellComplexGenerator C hG V hv hb t u z + cellComplexSource C.θ S F z := by
  let m := fun j k x => cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM C.θ j u) x *
    star (cellShiftedDerivativeCLM (fun i => star (C.θ i)) k z x)
  let d := fun j x => cellDriftEntryCLM C V hv hb t j (cellShiftedDerivativeCLM C.θ j u) x *
    star (torusHkValueCLM z x)
  let p := fun x => cellScalarCLM (C.κ t) (torusHkValueCLM u) x * star (torusHkValueCLM z x)
  let s := fun x => S x * star (torusHkValueCLM z x)
  let f := fun j x => F j x * star (cellShiftedDerivativeCLM (fun i => star (C.θ i)) j z x)
  have hm (j k : Fin 2) : Integrable (m j k) (volume.restrict AVenhance.unitCube) :=
    cellComplex_pairing_integrable _ _
  have hd (j : Fin 2) : Integrable (d j) (volume.restrict AVenhance.unitCube) :=
    cellComplex_pairing_integrable _ _
  have hp : Integrable p (volume.restrict AVenhance.unitCube) := cellComplex_pairing_integrable _ _
  have hs : Integrable s (volume.restrict AVenhance.unitCube) := cellComplex_pairing_integrable _ _
  have hf (j : Fin 2) : Integrable (f j) (volume.restrict AVenhance.unitCube) :=
    cellComplex_pairing_integrable _ _
  have hms (j : Fin 2) : Integrable (fun x => ∑ k : Fin 2, m j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun k _ => hm j k)
  have hmss : Integrable (fun x => ∑ j : Fin 2, ∑ k : Fin 2, m j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hms j)
  have hds : Integrable (fun x => ∑ j : Fin 2, d j x) (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hd j)
  have hfs : Integrable (fun x => ∑ j : Fin 2, f j x) (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hf j)
  have h1 := integral_sub (((hmss.neg.sub hds).add hp).add hs) hfs
  have h2 := integral_add ((hmss.neg.sub hds).add hp) hs
  have h3 := integral_add (hmss.neg.sub hds) hp
  have h4 := integral_sub hmss.neg hds
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at h1 h2 h3 h4
  change (∫ x in AVenhance.unitCube,
    -(∑ j : Fin 2, ∑ k : Fin 2, m j k x) - (∑ j : Fin 2, d j x) + p x + s x -
      ∑ j : Fin 2, f j x) = _
  rw [h1, h2, h3, h4, integral_neg,
    integral_finsetSum Finset.univ (fun j _ => hms j),
    integral_finsetSum Finset.univ (fun j _ => hd j),
    integral_finsetSum Finset.univ (fun j _ => hf j)]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hm _ k)]
  dsimp only [cellComplexGenerator, cellComplexSource, cellComplexPair, m, d, p, s, f]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Norm convergence of the finite metric-jet source convolution. -/

/-- Coefficient and lower-state norm convergence imply norm convergence of the literal metric-jet flux. -/
theorem cellMetricJetFlux_tendsto {P : Type*} (l : Filter P)
    (Gj : ℕ × ℕ → P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (G0 : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → P → ℝ → RawJet2 1 ℂ)
    (c0 : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ)
    (hG : ∀ β ∈ cellJetFluxIndices α, ∀ p,
      cellMetricSupNorm (Gj β p) < ⊤ ∧ Measurable (Function.uncurry (Gj β p)))
    (hG0 : ∀ β ∈ cellJetFluxIndices α,
      cellMetricSupNorm (G0 β) < ⊤ ∧ Measurable (Function.uncurry (G0 β)))
    (hc0 : ∀ β ∈ cellJetFluxIndices α,
      cellEnergyNorm univ (c0 (α.1 - β.1, α.2 - β.2)) < ⊤)
    (hcm : ∀ β ∈ cellJetFluxIndices α, ∀ p a,
      AEStronglyMeasurable (fun z : ℝ × Vec 2 => cj (α.1 - β.1, α.2 - β.2) p z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hc0m : ∀ β ∈ cellJetFluxIndices α, ∀ a,
      AEStronglyMeasurable (fun z : ℝ × Vec 2 => c0 (α.1 - β.1, α.2 - β.2) z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hGc : ∀ β ∈ cellJetFluxIndices α,
      Tendsto (fun p => cellMetricSupNorm (Gj β p - G0 β)) l (𝓝 0))
    (hcc : ∀ β ∈ cellJetFluxIndices α,
      Tendsto (fun p => cellEnergyNorm univ
        (cj (α.1 - β.1, α.2 - β.2) p - c0 (α.1 - β.1, α.2 - β.2))) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm univ
      (cellMetricJetFlux (fun β => Gj β p) (fun β => cj β p) α - cellMetricJetFlux G0 c0 α))
      l (𝓝 0) := by
  let S := cellJetFluxIndices α
  let f := fun β p => (cellJetChoose α β : ℝ) •
    cellMetricFlux (Gj β p) (cj (α.1 - β.1, α.2 - β.2) p)
  let f0 := fun β => (cellJetChoose α β : ℝ) • cellMetricFlux (G0 β) (c0 (α.1 - β.1, α.2 - β.2))
  have hfm (β : ℕ × ℕ) (hβ : β ∈ S) (p : P) : AEStronglyMeasurable (Function.uncurry (f β p))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    (cellMetricFlux_aestronglyMeasurable univ (Gj β p)
      (cj (α.1 - β.1, α.2 - β.2) p) (hG β hβ p).2 (hcm β hβ p)).const_smul (cellJetChoose α β : ℝ)
  have hf0m (β : ℕ × ℕ) (hβ : β ∈ S) : AEStronglyMeasurable (Function.uncurry (f0 β))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    (cellMetricFlux_aestronglyMeasurable univ (G0 β)
      (c0 (α.1 - β.1, α.2 - β.2)) (hG0 β hβ).2 (hc0m β hβ)).const_smul (cellJetChoose α β : ℝ)
  have hf (β : ℕ × ℕ) (hβ : β ∈ S) :
      Tendsto (fun p => cellUlNorm univ (f β p - f0 β)) l (𝓝 0) := by
    apply cellUlNorm_smul_tendsto l (cellJetChoose α β : ℝ)
      (fun p => cellMetricFlux (Gj β p) (cj (α.1 - β.1, α.2 - β.2) p))
      (cellMetricFlux (G0 β) (c0 (α.1 - β.1, α.2 - β.2)))
    · intro p
      exact cellMetricFlux_aestronglyMeasurable univ _ _ (hG β hβ p).2 (hcm β hβ p)
    · exact cellMetricFlux_aestronglyMeasurable univ _ _ (hG0 β hβ).2 (hc0m β hβ)
    · exact cellMetricFlux_tendsto l (Gj β) (G0 β) (cj (α.1 - β.1, α.2 - β.2))
        (c0 (α.1 - β.1, α.2 - β.2)) (hG β hβ) (hG0 β hβ) (hc0 β hβ)
        (hcm β hβ) (hc0m β hβ) (hGc β hβ) (hcc β hβ)
  simpa only [cellMetricJetFlux_eq_sum, f, f0, S] using
    cellUlNorm_finset_sum_tendsto l S f f0 hfm hf0m hf

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual raw periodic slice gives the raw graph flux as spatial representative. -/

theorem cellH1Slice_graph_flux_ae (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ)
    (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) (j : Fin 2) :
    cellNormalizedGraphFluxClass G (fun k => (Real.sqrt η : ℂ) * ξ k)
      t (cellH1Slice D t) j =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => fibreGraphFlux η G ξ (cellValue D) t x j := by
  filter_upwards [cellNormalizedGraphFluxClass_ae η G ξ t (cellH1Slice D t) j,
    cellH1Slice_value_ae D t ht] with x hf hx
  rw [hf]
  simp only [fibreGraphFlux]
  rw [hx]

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The adjoint value embedding realizes every cell L² field as an H¹ Riesz dual field. -/

def cellPivotDualCLM : ComplexCellL2 →L[ℝ] TorusHk 1 ℂ := (torusHkValueCLM (E := ℂ) (K := 1)).adjoint

theorem cellPivotDual_complex_pair (u : ComplexCellL2) (z : TorusHk 1 ℂ) :
    cellDualComplexPair (cellPivotDualCLM u) z = cellComplexPair u (torusHkValueCLM z) := by
  apply Complex.ext
  · rw [cellDualComplexPair_re, cellComplexPair_re]
    change inner ℝ ((torusHkValueCLM (E := ℂ) (K := 1)).adjoint u) z = _
    exact ContinuousLinearMap.adjoint_inner_left (torusHkValueCLM (E := ℂ) (K := 1)) z u
  · rw [cellDualComplexPair_im, cellComplexPair_im]
    change inner ℝ ((torusHkValueCLM (E := ℂ) (K := 1)).adjoint u) (cellH1Scalar Complex.I z) = _
    rw [ContinuousLinearMap.adjoint_inner_left (torusHkValueCLM (E := ℂ) (K := 1)),
      cellH1Scalar_value]

theorem cellDualComplexPair_add_left (g h z : TorusHk 1 ℂ) :
    cellDualComplexPair (g + h) z = cellDualComplexPair g z + cellDualComplexPair h z := by
  apply Complex.ext
  · simp only [cellDualComplexPair_re, Complex.add_re, inner_add_left]
  · simp only [cellDualComplexPair_im, Complex.add_im, inner_add_left]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Fixed complex tests of genuine weak Hilbert solutions are absolutely continuous scalar curves. -/

theorem CellWeakHilbertCurve.complex_test_strongTime {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (z : TorusHk 1 ℂ) :
    StrongTimeRegularity a b (fun t => cellComplexPair (u t) (torusHkValueCLM z))
      (fun t => cellDualComplexPair (g t) z) := by
  have hp := cellDualComplexPair_intervalIntegrable
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩) (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
    hab g h.dual z
  apply complexStrongTime_of_primitive hab _ _ hp
  intro t ht
  have he := h.complex_increment a ⟨le_rfl, hab⟩ t ht ht.1 z
  exact (eq_add_of_sub_eq he).trans (add_comm _ _)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Complex scalar multiples remain genuine weak Hilbert curves on the realified cell carriers. -/

theorem CellWeakHilbertCurve.complex_smul {a b : ℝ} {u : ℝ → ComplexCellL2}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) (c : ℂ) :
    CellWeakHilbertCurve a b (fun t => cellScalarCLM c (u t))
      (fun t => cellH1Scalar c (slice t)) (fun t => cellH1Scalar c (g t)) := by
  have hm := h.map (cellScalarCLM c) (cellH1ScalarCLM c)
    (fun z => by rw [cellH1ScalarCLM_apply, cellH1Scalar_value])
    (fun z => by rw [cellScalarCLM_adjoint, cellH1ScalarCLM_adjoint,
      cellH1ScalarCLM_apply, cellH1Scalar_value])
  simpa only [cellH1ScalarCLM_apply] using hm

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! The prescribed factorial-growth radius satisfies the literal coefficient smallness condition. -/

/-- A factorial-growth coefficient family has a finite uniform geometric majorant. -/
theorem factorialJetSum_growth_bound (K : ℕ) (G : ℕ × ℕ → ℝ≥0∞)
    (ρ M a : ℝ) (hρ : 0 ≤ ρ) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hx : ρ * a ≤ 1 / 2)
    (hG : ∀ β : ℕ × ℕ, β.1 + β.2 ≤ K → G β ≤
      ENNReal.ofReal (M * ((β.1.factorial : ℝ) * (β.2.factorial : ℝ)) * a ^ (β.1 + β.2))) :
    factorialJetSum ((jetIndices K).erase 0) ρ G ≤ ENNReal.ofReal (8 * M * (ρ * a)) := by
  have hterm β (hb : β ∈ (jetIndices K).erase 0) :
      ENNReal.ofReal (cellJetWeightReal ρ β) * G β ≤
        ENNReal.ofReal (M * (ρ * a) ^ (β.1 + β.2)) := by
    calc
      _ ≤ ENNReal.ofReal (cellJetWeightReal ρ β) *
          ENNReal.ofReal (M * ((β.1.factorial : ℝ) * (β.2.factorial : ℝ)) * a ^ (β.1 + β.2)) := by
        gcongr
        exact hG β ((mem_jetIndices_iff K β).mp (Finset.mem_erase.mp hb).2)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (cellJetWeightReal_nonneg hρ β),
          cellJetWeightReal_factorial_growth]
  have hsum := Finset.sum_le_sum hterm
  have hn β (_ : β ∈ (jetIndices K).erase 0) : 0 ≤ M * (ρ * a) ^ (β.1 + β.2) := by positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hn, ← Finset.mul_sum] at hsum
  have hgeom := finiteGeometric_positive_triangle (mul_nonneg hρ ha) hx K
  have hb : M * (∑ β ∈ (jetIndices K).erase 0, (ρ * a) ^ (β.1 + β.2)) ≤ 8 * M * (ρ * a) := by
    calc
      _ ≤ M * (8 * (ρ * a)) := by gcongr
      _ = _ := by ring
  exact hsum.trans (ENNReal.ofReal_le_ofReal hb)

/-- The radius specified in the statement makes the coefficient factorial sum absorbable for every K. -/
theorem factorialJetRadius_small (K : ℕ) (G : ℕ × ℕ → ℝ≥0∞)
    (C M a : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (ha : 0 < a)
    (hG : ∀ β : ℕ × ℕ, β.1 + β.2 ≤ K → G β ≤
      ENNReal.ofReal (M * ((β.1.factorial : ℝ) * (β.2.factorial : ℝ)) * a ^ (β.1 + β.2))) :
    ENNReal.ofReal C * factorialJetSum ((jetIndices K).erase 0)
      ((16 * (1 + C * M) * a)⁻¹) G ≤ 1 / 2 := by
  obtain ⟨hr, _, hx, hb⟩ := factorialRadius_algebra C M a hC hM ha
  have hg := factorialJetSum_growth_bound K G _ M a hr.le hM ha.le hx hG
  calc
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (8 * M * ((16 * (1 + C * M) * a)⁻¹ * a)) := by gcongr
    _ = ENNReal.ofReal (C * (8 * M * ((16 * (1 + C * M) * a)⁻¹ * a))) :=
      (ENNReal.ofReal_mul hC).symm
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hb
    _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]; norm_num

/-! Weighted finite-prefix convolution bounds with fully specified coefficient majorants. -/

theorem fibreCoefficient_weighted_convolution_prefix_le (ρ : ℝ≥0∞)
    (D K : ℕ × ℕ → ℝ≥0∞) (N : ℕ) :
    (∑ p ∈ jetIndices N, fibreCoefficientWeight ρ p *
      ∑ a ∈ fibreCoefficientPairs p, D a * K (fibreCoefficientComplement p a)) ≤
      (∑ p ∈ jetIndices N, fibreCoefficientWeight ρ p * D p) *
        ∑ p ∈ jetIndices N, fibreCoefficientWeight ρ p * K p := by
  have he :
      (∑ p ∈ jetIndices N, fibreCoefficientWeight ρ p *
        ∑ a ∈ fibreCoefficientPairs p, D a * K (fibreCoefficientComplement p a)) =
      ∑ p ∈ jetIndices N, ∑ a ∈ fibreCoefficientPairs p,
        (fibreCoefficientWeight ρ a * D a) *
          (fibreCoefficientWeight ρ (fibreCoefficientComplement p a) *
            K (fibreCoefficientComplement p a)) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [fibreCoefficientWeight_convolution ρ ha]
    ring
  rw [he]
  exact fibreCoefficient_convolution_le_product N
    (fun p => fibreCoefficientWeight ρ p * D p)
    (fun p => fibreCoefficientWeight ρ p * K p)

/-! Weighted finite-prefix control of the linear coordinate shifts. -/

/-- The weighted linear shift contributes only two frequency factors times the lower prefix sum. -/
theorem fibreCoefficient_weighted_shift_le (K : ℕ) (ρ : ℝ≥0∞) (E : ℕ × ℕ → ℝ≥0∞) :
    (∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
      fibreCoefficientWeight ρ p * E (fibreCoefficientPrevious p j)) ≤
      (2 * ρ) * ∑ q ∈ jetIndices K, fibreCoefficientWeight ρ q * E q := by
  calc
    _ = ρ * (∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
        fibreCoefficientWeight ρ (fibreCoefficientPrevious p j) * E (fibreCoefficientPrevious p j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro j hj
      rw [fibreCoefficientWeight_previous ρ hj]
      ring
    _ ≤ ρ * (2 * ∑ q ∈ jetIndices K, fibreCoefficientWeight ρ q * E q) :=
      mul_le_mul' le_rfl (fibreCoefficient_shift_sum_le K (fun q => fibreCoefficientWeight ρ q * E q))
    _ = _ := by ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Strong temporal convergence of Fourier projections of arbitrary cell L² curves. -/

/-- Fourier projection converges strongly in the temporal L² carrier. -/
theorem cellBochnerFourier_tendsto (I : Set ℝ) (u : ℝ → ComplexCellL2)
    (hu : MemLp u 2 (volume.restrict I)) :
    Tendsto (fun N => ((cellVectorFourierProjection N).comp_memLp' hu).toLp
      (fun t => cellVectorFourierProjection N (u t))) atTop (𝓝 (hu.toLp u)) := by
  have htail (N : ℕ) (t : ℝ) :
      ‖cellVectorFourierProjection N (u t) - u t‖ ≤ 2 * ‖u t‖ := by
    exact (norm_sub_le _ _).trans
      ((add_le_add (cellVectorFourierProjection_norm_le N (u t)) le_rfl).trans_eq (by ring))
  have hmeas (N : ℕ) := (((cellVectorFourierProjection N).comp_memLp' hu).sub hu).aestronglyMeasurable
  have hlim (t : ℝ) : Tendsto
      (fun N => ‖cellVectorFourierProjection N (u t) - u t‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (((cellVectorFourierProjection_tendsto (u t)).sub
        (tendsto_const_nhds (x := u t))).norm.pow 2)
  have hi := tendsto_integral_of_dominated_convergence (fun t => 4 * ‖u t‖ ^ 2)
    (fun N => (hmeas N).norm.pow 2) (hu.norm.integrable_sq.const_mul 4)
    (fun N => Filter.Eventually.of_forall (fun t => by
      change ‖‖cellVectorFourierProjection N (u t) - u t‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ht := htail N t
      nlinarith [norm_nonneg (cellVectorFourierProjection N (u t) - u t), norm_nonneg (u t)]))
    (Filter.Eventually.of_forall hlim)
  have hs : Tendsto (fun N =>
      ‖((cellVectorFourierProjection N).comp_memLp' hu).toLp
        (fun t => cellVectorFourierProjection N (u t)) - hu.toLp u‖ ^ 2) atTop (𝓝 0) := by
    simpa only [← MemLp.toLp_sub, cellTimeL2_norm_sq_integral, integral_zero,
      Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Function.comp_def] using hi
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Derivative readouts agree with the actual weak solution's spatial derivatives. -/

theorem cellFiniteEnergyTimeDerivativeCLM_ae {a b : ℝ} (hab : a ≤ b) (j : Fin 2)
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice g) (z : CellFiniteEnergyCarrier a b)
    (hz : ∀ t : CellCompactTime a b, z.val.1 t = u t.val) :
    cellFiniteEnergyTimeDerivativeCLM hab j z =ᵐ[volume.restrict (Icc a b)]
      fun t => cellDerivativeCLM j (slice t) := by
  have hd := (cellComplexH1DerivativeCLM j).coeFn_compLpL
    (cellFiniteEnergyTimeStateCLM hab z)
  have hs := cellFiniteEnergyTimeStateCLM_ae hab u slice g h z hz
  filter_upwards [hd, hs] with t hd' hs'
  change (cellComplexH1DerivativeCLM j).compLpL 2 (volume.restrict (Icc a b))
    (cellFiniteEnergyTimeStateCLM hab z) t = cellDerivativeCLM j (slice t)
  rw [hd', cellComplexH1DerivativeCLM_eq, hs']

theorem cellFiniteEnergyTimeShiftedDerivativeCLM_ae {a b : ℝ} (hab : a ≤ b)
    (θ : Fin 2 → ℂ) (j : Fin 2)
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice g) (z : CellFiniteEnergyCarrier a b)
    (hz : ∀ t : CellCompactTime a b, z.val.1 t = u t.val) :
    cellFiniteEnergyTimeShiftedDerivativeCLM hab θ j z =ᵐ[volume.restrict (Icc a b)]
      fun t => cellShiftedDerivativeCLM θ j (slice t) := by
  have hd := cellFiniteEnergyTimeDerivativeCLM_ae hab j u slice g h z hz
  have hv := cellFiniteEnergyTimeValueCLM_ae hab u slice g h z hz
  have ha := Lp.coeFn_add (cellFiniteEnergyTimeDerivativeCLM hab j z)
    ((Complex.I * θ j) • cellFiniteEnergyTimeValueCLM hab z)
  have hm := Lp.coeFn_smul (Complex.I * θ j) (cellFiniteEnergyTimeValueCLM hab z)
  filter_upwards [hd, hv, ha, hm, h.agrees] with t hd' hv' ha' hm' hs'
  change (cellFiniteEnergyTimeDerivativeCLM hab j z +
    (Complex.I * θ j) • cellFiniteEnergyTimeValueCLM hab z) t = _
  rw [ha']
  simp only [Pi.add_apply]
  rw [hm', hd']
  simp only [Pi.smul_apply]
  rw [hv', hs']
  rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The exact literal complex cell right-hand side used by the public weak identity. -/

/-- The literal bilinear cell integrand, with the trial and test Bloch shifts. -/
def cellLiteralRHS (C : CellCoefficients) (t : ℝ)
    (u : Vec 2 → ℂ) (du : Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src : Vec 2 → ℂ) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (x : Vec 2) : ℂ :=
  -(∑ j : Fin 2, ∑ k : Fin 2, (C.G t x j k : ℂ) *
    (du j x + Complex.I * C.θ j * u x) * (dψ k x - Complex.I * C.θ k * ψ x)) -
  (∑ k : Fin 2, (C.v t x k : ℂ) * (du k x + Complex.I * C.θ k * u x) * ψ x) +
  C.κ t * u x * ψ x + src x * ψ x -
  ∑ k : Fin 2, F x k * (dψ k x - Complex.I * C.θ k * ψ x)

/-- Conjugating the shifted conjugate-test class gives the minus-shift test. -/
theorem cellConjugateTest_shift_ae (θ : Fin 2 → ℂ) (z : TorusHk 1 ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (hv : (torusHkValueCLM z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] star ψ)
    (hd : ∀ j, (cellDerivativeCLM j z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] star (dψ j))
    (j : Fin 2) :
    (fun x => star (cellShiftedDerivativeCLM (fun i => star (θ i)) j z x)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => dψ j x - Complex.I * θ j * ψ x := by
  filter_upwards [cellShiftedDerivativeCLM_ae (fun i => star (θ i)) j z, hv, hd j]
    with x hs hx hdx
  rw [hs, hx, hdx]
  simp only [Pi.star_apply, star_add, star_mul, Complex.star_def, Complex.conj_I, starRingEnd_self_apply]
  ring

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Weighted quadratic coefficient convolutions are controlled by the square of the lower prefix sum. -/

/-- The weighted nonlinear coefficient convolution has the square of its lower weighted prefix as a bound. -/
theorem fibreCoefficient_weighted_convolution_le (K : ℕ) (ρ : ℝ≥0∞) (E : ℕ × ℕ → ℝ≥0∞) :
    (∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
      ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
        fibreCoefficientWeight ρ p * E (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) * E a) ≤
      (2 * ρ) * (∑ q ∈ jetIndices K, fibreCoefficientWeight ρ q * E q) ^ 2 := by
  let w := fun q => fibreCoefficientWeight ρ q * E q
  calc
    _ = ρ * (∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
          w a * w (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro a ha
      rw [fibreCoefficientWeight_previous ρ hj, fibreCoefficientWeight_convolution ρ ha]
      dsimp only [w]
      ring
    _ ≤ ρ * (2 * ∑ p ∈ jetIndices K, ∑ a ∈ fibreCoefficientPairs p,
        w a * w (fibreCoefficientComplement p a)) :=
      mul_le_mul' le_rfl (fibreCoefficient_shift_sum_le K
        (fun p => ∑ a ∈ fibreCoefficientPairs p, w a * w (fibreCoefficientComplement p a)))
    _ ≤ ρ * (2 * ((∑ q ∈ jetIndices K, w q) * ∑ q ∈ jetIndices K, w q)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (fibreCoefficient_convolution_le_product K w w))
    _ = _ := by dsimp only [w]; ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Agreement of the complex Hilbert form integrand with the public literal weak integrand. -/

/-- A trial class, conjugate test class, and source classes read the exact raw cell integrand. -/
theorem cellComplexSpatial_literal_ae (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (rawu : Vec 2 → ℂ) (rawdu : Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src : Vec 2 → ℂ) (flux : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hu : (torusHkValueCLM u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] rawu)
    (hdu : ∀ j, (cellDerivativeCLM j u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] rawdu j)
    (hz : (torusHkValueCLM z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] star ψ)
    (hdz : ∀ j, (cellDerivativeCLM j z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] star (dψ j))
    (hS : (S : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] src)
    (hF : ∀ j, (F j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun x => flux x j) :
    cellComplexSpatial C hG V hv hb t u z S F =ᵐ[volume.restrict AVenhance.unitCube]
      cellLiteralRHS C t rawu rawdu ψ dψ src flux := by
  have hm := ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k =>
    cellMetricEntryCLM_ae hG t j k (cellShiftedDerivativeCLM C.θ j u)))
  have hd := ae_all_iff.mpr (fun j => cellDriftEntryCLM_ae C V hv hb t j (cellShiftedDerivativeCLM C.θ j u))
  have hshift := ae_all_iff.mpr (fun j => cellShiftedDerivativeCLM_ae C.θ j u)
  have htest := ae_all_iff.mpr (fun j => cellConjugateTest_shift_ae C.θ z ψ dψ hz hdz j)
  filter_upwards [hm, hd, hshift, htest, hu, hz, hS, ae_all_iff.mpr hF,
    ae_all_iff.mpr hdu, cellScalarCLM_ae (C.κ t) (torusHkValueCLM u)]
    with x hmx hdx hsx htx hux hzx hSx hFx hdux hpx
  have hstar : star (torusHkValueCLM z x) = ψ x := by
    rw [hzx]
    exact star_star _
  simp only [cellComplexSpatial, cellLiteralRHS, Fin.sum_univ_two,
    hmx, hdx, hsx, htx, hux, hstar, hSx, hFx, hdux, hpx]

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Common forcing cancels algebraically in the actual literal cell weak integrand. -/

/-- Subtracting two literal right-hand sides with common forcing gives the homogeneous difference. -/
theorem cellLiteralRHS_sub_same_source (C : CellCoefficients) (t : ℝ)
    (u w : Vec 2 → ℂ) (du dw : Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src : Vec 2 → ℂ) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (x : Vec 2) :
    cellLiteralRHS C t u du ψ dψ src F x - cellLiteralRHS C t w dw ψ dψ src F x =
      cellLiteralRHS C t (u - w) (du - dw) ψ dψ 0 0 x := by
  simp only [cellLiteralRHS, Fin.sum_univ_two, Pi.sub_apply, Pi.zero_apply, PiLp.zero_apply]
  ring

/-! Linear identities for the public cell weak integrand. -/

/-- The literal weak integrand is additive jointly in state and forcing. -/
theorem cellLiteralRHS_add (C : CellCoefficients) (t : ℝ)
    (u w : Vec 2 → ℂ) (du dw : Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src src' : Vec 2 → ℂ) (F F' : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (x : Vec 2) :
    cellLiteralRHS C t (u + w) (du + dw) ψ dψ (src + src') (F + F') x =
      cellLiteralRHS C t u du ψ dψ src F x + cellLiteralRHS C t w dw ψ dψ src' F' x := by
  simp only [cellLiteralRHS, Fin.sum_univ_two, Pi.add_apply, PiLp.add_apply]
  ring

/-- Real scaling commutes with the literal weak integrand. -/
theorem cellLiteralRHS_smul (C : CellCoefficients) (t r : ℝ)
    (u : Vec 2 → ℂ) (du : Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src : Vec 2 → ℂ) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (x : Vec 2) :
    cellLiteralRHS C t (r • u) (r • du) ψ dψ (r • src) (r • F) x =
      r • cellLiteralRHS C t u du ψ dψ src F x := by
  simp only [cellLiteralRHS, Fin.sum_univ_two, Pi.smul_apply, PiLp.smul_apply,
    Complex.real_smul]
  ring

end AVRegularity.CycleEvolution
end

section
open Homogenization
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! The literal weak cell integrand is a continuous linear functional of its trial data. -/

/-- Pointwise trial value, gradient, scalar forcing, and vector forcing. -/
abbrev CellRHSState := ℂ × (PiLp 2 (fun _ : Fin 2 => ℂ) × (ℂ × PiLp 2 (fun _ : Fin 2 => ℂ)))

/-- Projection onto the pointwise trial value. -/
def cellRHSValueCLM : CellRHSState →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ _ _

/-- Projection onto one pointwise trial derivative. -/
def cellRHSGradientCLM (j : Fin 2) : CellRHSState →L[ℂ] ℂ :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) j).comp
    ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))

/-- Projection onto the pointwise scalar forcing. -/
def cellRHSSourceCLM : CellRHSState →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))

/-- Projection onto one pointwise flux forcing component. -/
def cellRHSFluxCLM (j : Fin 2) : CellRHSState →L[ℂ] ℂ :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) j).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp
      ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)))

/-- The exact cell integrand as a linear functional on pointwise trial data. -/
def cellLiteralRHSCLM (C : CellCoefficients) (t : ℝ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ) (x : Vec 2) : CellRHSState →L[ℂ] ℂ :=
  -(∑ j : Fin 2, ∑ k : Fin 2,
    ((C.G t x j k : ℂ) * (dψ k x - Complex.I * C.θ k * ψ x)) •
      (cellRHSGradientCLM j + (Complex.I * C.θ j) • cellRHSValueCLM)) -
  (∑ k : Fin 2, ((C.v t x k : ℂ) * ψ x) •
    (cellRHSGradientCLM k + (Complex.I * C.θ k) • cellRHSValueCLM)) +
  (C.κ t * ψ x) • cellRHSValueCLM + ψ x • cellRHSSourceCLM -
  ∑ k : Fin 2, (dψ k x - Complex.I * C.θ k * ψ x) • cellRHSFluxCLM k

/-- The continuous linear functional evaluates to the literal cell integrand. -/
theorem cellLiteralRHSCLM_apply (C : CellCoefficients) (t : ℝ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ) (x : Vec 2) (z : CellRHSState) :
    cellLiteralRHSCLM C t ψ dψ x z =
      cellLiteralRHS C t (fun _ => z.1) (fun j _ => z.2.1 j) ψ dψ
        (fun _ => z.2.2.1) (fun _ => z.2.2.2) x := by
  simp [cellLiteralRHSCLM, cellLiteralRHS, cellRHSValueCLM, cellRHSGradientCLM,
    cellRHSSourceCLM, cellRHSFluxCLM, Fin.sum_univ_two, smul_eq_mul]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual L² flux slices of periodic graph jets. -/

theorem cellH1Slice_graph_flux_slice (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ)
    (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) (j : Fin 2) :
    cellSourceSlice (fun s x => fibreGraphFlux η G ξ (cellValue D) s x j) t =
      cellNormalizedGraphFluxClass G (fun k => (Real.sqrt η : ℂ) * ξ k)
        t (cellH1Slice D t) j := by
  apply cellSourceSlice_eq_of_ae
  exact cellH1Slice_graph_flux_ae η G ξ D t ht j

end AVRegularity.CycleEvolution
end
