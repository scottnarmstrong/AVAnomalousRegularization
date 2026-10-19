-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.CoefficientPairing
public import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Exact plane coefficient multiplication using the per-order seminorm suprema. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The carrier multiplier at one interval time, using the actual per-order seminorm suprema. -/
def planeMultiplyIntervalCoefficient (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K : ℕ) (A t))
    (w : PlaneHk Set.univ K E) : PlaneHk Set.univ K F :=
  w.mulCoefficient (A t) hC (fun l x =>
    coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t ht x)

omit [FiniteDimensional ℝ F] in
/-- The exact coefficient seminorm controls the factorial multiplier norm. -/
theorem planeMultiplyIntervalCoefficient_factorialNorm_le
    (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K : ℕ) (A t))
    (w : PlaneHk Set.univ K E) :
    Real.sqrt (factorialNormSq ρ (planeMultiplyIntervalCoefficient ρ hρ K a b A hA t ht hC w).val) ≤
      (coefficientSeminorm ρ K a b A).toReal * Real.sqrt (factorialNormSq ρ w.val) := by
  have hb := fun (l : Fin (K + 1)) (x : Vec 2) =>
    coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t ht x
  have h := w.mulCoefficient_factorialNorm_le hC hb hρ.le
  rw [coefficientSeminorm_eq_sum_real_budget ρ hρ K a b A hA] at h
  exact h

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Cell L² drift bounds, through the multiplication tensor estimate. -/

section
open AVRegularity.CoupledEnergy.Variational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {U : Set (Vec 2)}

/-- The Hilbert array of one positional drift contribution. -/
def driftMaskL2Array {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2)
    (D : RawJet2 (K + 1) E) (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict U)) (m : PositionMask j) :
    PiLp 2 (fun _ : DerivativeWord2 j => ComponentL2 (volume.restrict U) E) :=
  WithLp.toLp 2 fun w => (hT m w).toLp
    (driftMaskTerm hj v D m w)

omit [BorelSpace E] in
/-- No dimension factor is lost when integrating the pointwise drift-array estimate. -/
theorem driftMaskL2Array_normSq_le {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2)
    (D : RawJet2 (K + 1) E) (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict U))
    (hD : JetMemL2On U D) (hU : MeasurableSet U) (m : PositionMask j)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x ∈ U,
      ‖coefficientDerivativeArray (driftCoefficient v) (maskLeftLength j m) x‖ ≤ M) :
    ‖driftMaskL2Array hj v D hT m‖ ^ 2 ≤ M ^ 2 *
      derivativeNormSq (jetToL2 D hD)
        ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩ := by
  classical
  let r : Fin (K + 2) := ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩
  let T := fun w : DerivativeWord2 j => driftMaskTerm hj v D m w
  have hTm : ∀ w, MemLp (T w) 2 (volume.restrict U) :=
    hT m
  have hleft := integrable_finsetSum Finset.univ (fun w _ => integrable_normSq_of_memLp (hTm w))
  have hright := integrable_finsetSum Finset.univ
    (fun w _ => integrable_normSq_of_memLp (hD ⟨r, w⟩))
  calc
    ‖driftMaskL2Array hj v D hT m‖ ^ 2 =
        ∫ x in U, ∑ w : DerivativeWord2 j, ‖T w x‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      change (∑ w : DerivativeWord2 j, ‖(hTm w).toLp (T w)‖ ^ 2) = _
      simp_rw [normSq_toLp_eq_integral]
      exact (integral_finsetSum Finset.univ
        (fun w _ => integrable_normSq_of_memLp (hTm w))).symm
    _ ≤ ∫ x in U, M ^ 2 *
        ∑ w : DerivativeWord2 r.val, ‖D ⟨r, w⟩ x‖ ^ 2 := by
      apply integral_mono_ae hleft (hright.const_mul (M ^ 2))
      filter_upwards [ae_restrict_mem hU]
        with x hx
      exact driftMaskTerm_pointwise_sumSq_le hj v D m x hM (hb x hx)
    _ = M ^ 2 * derivativeNormSq (jetToL2 D hD) r := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun w _ => integrable_normSq_of_memLp (hD ⟨r, w⟩))]
      change M ^ 2 * (∑ w : DerivativeWord2 r.val,
        ∫ x in U, ‖D ⟨r, w⟩ x‖ ^ 2) =
        M ^ 2 * ∑ w : DerivativeWord2 r.val, ‖(hD ⟨r, w⟩).toLp (D ⟨r, w⟩)‖ ^ 2
      congr 1
      apply Finset.sum_congr rfl
      intro w _
      exact (normSq_toLp_eq_integral (hD ⟨r, w⟩)).symm

omit [BorelSpace E] in
/-- Unsquared version of the cell drift-array estimate. -/
theorem driftMaskL2Array_norm_le {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2)
    (D : RawJet2 (K + 1) E) (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict U))
    (hD : JetMemL2On U D) (hU : MeasurableSet U) (m : PositionMask j)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x ∈ U,
      ‖coefficientDerivativeArray (driftCoefficient v) (maskLeftLength j m) x‖ ≤ M) :
    ‖driftMaskL2Array hj v D hT m‖ ≤ M * Real.sqrt
      (derivativeNormSq (jetToL2 D hD)
        ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩) := by
  have hnonneg : 0 ≤ derivativeNormSq (jetToL2 D hD)
      ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩ :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hnonneg]
  exact driftMaskL2Array_normSq_le hj v D hT hD hU m hM hb
end

/-! Exact binomial recombination of nonprincipal drift masks, reusing the multiplier count. -/

section
open AVRegularity.CoupledEnergy.Variational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {U : Set (Vec 2)}

/-- The actual L² array of the drift terms with at least one velocity derivative. -/
def driftCommutatorL2Array {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2)
    (D : RawJet2 (K + 1) E) (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict U)) :
    PiLp 2 (fun _ : DerivativeWord2 j => ComponentL2 (volume.restrict U) E) :=
  ∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then driftMaskL2Array hj v D hT m else 0

/-- Removing the principal mask leaves exactly the nonzero binomial derivative orders. -/
theorem sum_nonprincipal_masks (j : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then
      f (maskLeftLength j m) (maskRightLength j m) else 0) =
    ∑ l ∈ (Finset.range (j + 1)).erase 0, (j.choose l : ℝ) * f l (j - l) := by
  classical
  rw [sum_positionMask_eq_choose j (fun l r => if 1 ≤ l then f l r else 0)]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have heq : (Finset.range (j + 1)).filter (fun l => 1 ≤ l) =
      (Finset.range (j + 1)).erase 0 := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    omega
  rw [heq]

omit [BorelSpace E] [CompleteSpace E] in
/-- Constant-one commutator norm bound with the precise binomial multiplicities. -/
theorem driftCommutatorL2Array_norm_le {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2)
    (D : RawJet2 (K + 1) E) (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict U))
    (hD : JetMemL2On U D) (hU : MeasurableSet U)
    (V : ℕ → ℝ) (hV : ∀ l, 0 ≤ V l)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x ∈ U,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤ V l) :
    ‖driftCommutatorL2Array hj v D hT‖ ≤
    ∑ l ∈ (Finset.range (j + 1)).erase 0, (j.choose l : ℝ) * V l *
      finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) (j - l + 1) := by
  let Y := finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r))
  calc
    ‖driftCommutatorL2Array hj v D hT‖ ≤
        ∑ m : PositionMask j, ‖if 1 ≤ maskLeftLength j m then
          driftMaskL2Array hj v D hT m else 0‖ := norm_sum_le _ _
    _ ≤ ∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then
        V (maskLeftLength j m) * Y (maskRightLength j m + 1) else 0 := by
      apply Finset.sum_le_sum
      intro m _
      by_cases hm : 1 ≤ maskLeftLength j m
      · simp only [ite_eq_left hm]
        dsimp only [Y]
        rw [finiteSequence_of_le _ (by have := maskRightLength_le j m; omega)]
        exact driftMaskL2Array_norm_le hj v D hT hD hU m (hV _)
          (hb _ hm ((maskLeftLength_le j m).trans hj))
      · simp only [ite_eq_right hm, norm_zero, le_refl]
    _ = _ := by
      rw [sum_nonprincipal_masks j (fun l r => V l * Y (r + 1))]
      simp only [Y, mul_assoc]


omit [BorelSpace E] [CompleteSpace E] in
/-- The tested nonprincipal drift tensor has the exact scalar commutator envelope. -/
theorem driftCommutatorL2Array_pairing_abs_le {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2)
    (D : RawJet2 (K + 1) E) (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict U))
    (hD : JetMemL2On U D) (hU : MeasurableSet U)
    (V : ℕ → ℝ) (hV : ∀ l, 0 ≤ V l)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x ∈ U,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤ V l) :
    |inner ℝ (driftCommutatorL2Array hj v D hT)
      (orderL2Array (jetToL2 D hD) ⟨j, by omega⟩)| ≤
    ∑ l ∈ (Finset.range (j + 1)).erase 0, (j.choose l : ℝ) * V l *
      finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) (j - l + 1) *
      finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) j := by
  let Q := orderL2Array (jetToL2 D hD) (⟨j, by omega⟩ : Fin (K + 2))
  have hq : ‖Q‖ = finiteSequence
      (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) j := by
    rw [finiteSequence_of_le _ (by omega)]
    exact orderL2Array_norm _ _
  have hpair := abs_real_inner_le_norm (driftCommutatorL2Array hj v D hT) Q
  have hm := mul_le_mul_of_nonneg_right
    (driftCommutatorL2Array_norm_le hj v D hT hD hU V hV hb) (norm_nonneg Q)
  rw [hq] at hpair
  rw [hq, Finset.sum_mul] at hm
  exact hpair.trans hm
end

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The time hypotheses of `coupled_energy_plane` make its mass forcing integrals well
defined. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJet_memLp {X : Type*} [MeasurableSpace X] {m : Measure X}
    {p : ENNReal} (K : ℕ) {f : X → PlaneHk Set.univ K E} (hf : MemLp f p m) :
    MemLp (fun t => (f t).val) p m :=
  (planeHkGraph (E := E) Set.univ K).toSubmodule.subtypeL.comp_memLp' hf

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] in
theorem planeMassNormSq_integrable {X : Type*} [MeasurableSpace X] {m : Measure X}
    (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ)
    (f : ∀ i, X → PlaneHk Set.univ (K i) (h i)) (hf : ∀ i, MemLp (f i) 2 m) :
    Integrable (fun t => massNormSq ρ π (fun i => (f i t).val)) m :=
  massNormSq_integrable ρ π hπ (fun i => planeJet_memLp (K i) (hf i))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] in
theorem planeMassNorm_integrable {X : Type*} [MeasurableSpace X] {m : Measure X}
    (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ)
    (f : ∀ i, X → PlaneHk Set.univ (K i) (h i)) (hf : ∀ i, Integrable (f i) m) :
    Integrable (fun t => Real.sqrt (massNormSq ρ π (fun i => (f i t).val))) m :=
  massNorm_integrable ρ π hπ (fun i => planeJet_memLp (K i) (memLp_one_iff_integrable.mpr (hf i)))

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The exact mass norm is a fixed continuous linear readout of the
finite family of genuine Sobolev carriers. -/

open AVRegularity.CoupledEnergy.Variational
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

def planeMassWeightedCarrierCLM (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) :
    (∀ i, PlaneHk Set.univ (K i) (E i)) →L[ℝ]
      PiLp 2 (fun i => JetL2 (volume.restrict (Set.univ : Set (Vec 2))) (K i) (E i)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun i =>
    JetL2 (volume.restrict (Set.univ : Set (Vec 2))) (K i) (E i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      ((Real.sqrt ((π i)⁻¹) • factorialWeightedJetCLM ρ (K i)).comp
        (planeHkGraph (E := E i) Set.univ (K i)).toSubmodule.subtypeL).comp (ContinuousLinearMap.proj i)))

omit [Fintype ι] in
@[simp] theorem planeMassWeightedCarrierCLM_apply (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (w : ∀ i, PlaneHk Set.univ (K i) (E i)) :
    planeMassWeightedCarrierCLM K ρ π w = massWeightedJet ρ π (fun i => (w i).val) := rfl

theorem planeMassWeightedCarrierCLM_normSq (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (w : ∀ i, PlaneHk Set.univ (K i) (E i)) :
    ‖planeMassWeightedCarrierCLM K ρ π w‖ ^ 2 = massNormSq ρ π (fun i => (w i).val) :=
  massWeightedJet_normSq ρ π hπ _

theorem planeMassWeightedCarrierCLM_norm (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (w : ∀ i, PlaneHk Set.univ (K i) (E i)) :
    ‖planeMassWeightedCarrierCLM K ρ π w‖ = Real.sqrt (massNormSq ρ π (fun i => (w i).val)) :=
  massWeightedJet_norm ρ π hπ _

end AVRegularity.CoupledEnergyPlane.Variational
end
