-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Variational.ScalarTensorOperator
public import AVRegularity.CoupledEnergy.Variational.TorusHighReadout
public import AVRegularity.Statements.Intermediate.CoupledEnergy.GradFactorialNormSq
import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePairing
import AVenhance.Infra.Classical.PeriodicCalculus
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Time integrability of literal source terms against genuine H¹ tests,
using the paper's L² flux and L¹ value forcing. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- An L¹ Sobolev source has an integrable literal value pairing. -/
theorem torusValueSource_test_integrable (K : ℕ) (a b : ℝ)
    (g : ℝ → TorusHk K E) (hg : Integrable g (volume.restrict (Set.Icc a b)))
    (φ : TorusHk 1 E) :
    Integrable (fun r => ∫ x in AVenhance.unitCube,
      inner ℝ (Galerkin.torusHkValueCLM (g r) x) (Galerkin.torusHkValueCLM φ x))
      (volume.restrict (Set.Icc a b)) := by
  have hgv := (Galerkin.torusHkValueCLM (E := E) (K := K)).integrable_comp hg
  simpa only [L2.inner_def] using hgv.inner_const (𝕜 := ℝ) (Galerkin.torusHkValueCLM φ)

/-- An L² Sobolev flux has an integrable literal pairing with the H¹ test gradient. -/
theorem torusFluxSource_test_integrable (K : ℕ) (a b : ℝ)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b))) (φ : TorusHk 1 E) :
    Integrable (fun r => ∫ x in AVenhance.unitCube,
      inner ℝ (Galerkin.torusHkValueCLM (F r) x) (torusH1GradientL2CLM (E := E) φ x))
      (volume.restrict (Set.Icc a b)) := by
  have hfv := (Galerkin.torusHkValueCLM (E := PiLp 2 (fun _ : Fin 2 => E)) (K := K)).integrable_comp
    (hF.integrable (by norm_num))
  simpa only [L2.inner_def] using hfv.inner_const (𝕜 := ℝ) (torusH1GradientL2CLM (E := E) φ)
end

/-! The physical two-coordinate gradient as a fixed ambient coupled readout. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- Assemble the two physical first derivatives into one vector-valued L² field. -/
def coupledHighGradientCLM (K : ι → ℕ) (i : ι) :
    CoupledHighHilbert (h := h) K →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ k : Fin 2, ((Galerkin.tensorEntryCLM (E := h i) k).compLpL 2
    (volume.restrict AVenhance.unitCube)).comp
      (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)

omit [Fintype ι] [∀ i, BorelSpace (h i)] in
/-- The gradient readout has exactly the two first-jet representatives. -/
theorem coupledHighGradientCLM_ae (K : ι → ℕ) (i : ι)
    (U : CoupledHighHilbert (h := h) K) :
    coupledHighGradientCLM (h := h) K i U =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => WithLp.toLp 2 (fun k : Fin 2 =>
        U i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x) := by
  change (∑ k : Fin 2, (Galerkin.tensorEntryCLM (E := h i) k).compLpL 2
    (volume.restrict AVenhance.unitCube)
      (U i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)) =ᵐ[_] _
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun k : Fin 2 =>
    (Galerkin.tensorEntryCLM (E := h i) k).compLpL 2
      (volume.restrict AVenhance.unitCube)
        (U i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩))
  have hterms : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ k : Fin 2,
      ((Galerkin.tensorEntryCLM (E := h i) k).compLpL 2
        (volume.restrict AVenhance.unitCube)
          (U i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)) x =
      Galerkin.tensorEntryCLM k
        (U i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x) := by
    rw [ae_all_iff]
    intro k
    exact ContinuousLinearMap.coeFn_compLpL _ _
  filter_upwards [hsum, hterms] with x hx hxt
  rw [hx]
  simp only [Finset.sum_apply]
  simp_rw [hxt]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [Galerkin.tensorEntryCLM, Galerkin.tensorEntryLinearMap]
end

/-! Full ordered derivative tensors in the periodic Sobolev carrier. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The full order-r derivative array, retaining its tensor Hilbert norm. -/
def torusDerivativeTensor {K r : ℕ} (w : TorusHk (K + r) E) :
    TorusHk K (PiLp 2 (fun _ : DerivativeWord2 r => E)) :=
  torusFamilyTensor (fun a : DerivativeWord2 r => derivativeTorusHk a w)

/-- Tensor assembly preserves the exact factorial square of the derivative array. -/
theorem torusDerivativeTensor_factorialNormSq {K r : ℕ} (ρ : ℝ) (w : TorusHk (K + r) E) :
    factorialNormSq ρ (torusDerivativeTensor w).val =
      ∑ a : DerivativeWord2 r, factorialNormSq ρ (derivativeJet a w.val) := by
  rw [torusDerivativeTensor, torusFamilyTensor_factorialNormSq]
  rfl

/-- The precise factorial reserve shift, without a tensor dimension factor. -/
theorem torusDerivativeTensor_factorialNorm_le {K r : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) (w : TorusHk (K + r) E) :
    Real.sqrt (factorialNormSq ρ (torusDerivativeTensor w).val) ≤
      derivativeReserveFactor ρ K r * Real.sqrt (factorialNormSq ρ w.val) := by
  rw [torusDerivativeTensor_factorialNormSq]
  exact derivativeArray_factorialNorm_le ρ hρ w.val

/-- The first derivative tensor has exactly the gradient factorial square. -/
theorem torusDerivativeTensor_one_factorialNormSq {K : ℕ} (ρ : ℝ) (w : TorusHk (K + 1) E) :
    factorialNormSq ρ (torusDerivativeTensor (r := 1) w).val = gradFactorialNormSq ρ w.val := by
  rw [torusDerivativeTensor_factorialNormSq, derivativeArray_factorialNormSq]
  change (∑ j : Fin (K + 1), factorialWeight ρ j.val * derivativeNormSq w.val (shiftedJetOrder j)) =
    ∑ j : Fin (K + 1), factorialWeight ρ j.val *
      derivativeNormSq w.val ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  apply Finset.sum_congr rfl
  intro j _
  have hi : shiftedJetOrder (r := 1) j = ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ :=
    Fin.ext (Nat.add_comm 1 j.val)
  rw [hi]
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVenhance.Infra.Torus AVenhance.Infra.Classical
namespace AVRegularity.CoupledEnergy.Variational

/-! Periodic spatial integration by parts for smooth Hilbert-valued finite Fourier tests. -/

/-- Every derivative of a smooth scalar periodic function has zero cell integral. -/
theorem periodic_partial_integral_zero (q : Vec 2 → ℝ) (hq : ContDiff ℝ 1 q)
    (hp : AVenhance.IsZ2Periodic q) (k : Fin 2) :
    (∫ x in AVenhance.unitCube, fderiv ℝ q x (basisVec k)) = 0 := by
  rw [← integral_unitCell_eq_unitCube]
  have h := integral_unitCell_coord_ibp_real k (f := fun _ => (1 : ℝ)) contDiff_const hq
    (fun _ _ => rfl) hp
  simpa [AVenhance.spaceGrad] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A periodic Hilbert-valued derivative can be moved onto a smooth periodic test exactly. -/
theorem periodic_hilbert_partial_ibp (u q : Vec 2 → E)
    (hu : ContDiff ℝ 1 u) (hq : ContDiff ℝ 1 q)
    (hp : AVenhance.IsZ2Periodic u) (hqp : AVenhance.IsZ2Periodic q) (k : Fin 2) :
    (∫ x in AVenhance.unitCube, inner ℝ (fderiv ℝ u x (basisVec k)) (q x)) =
      -∫ x in AVenhance.unitCube, inner ℝ (u x) (fderiv ℝ q x (basisVec k)) := by
  let f := fun x => inner ℝ (u x) (q x)
  have hf : ContDiff ℝ 1 f := hu.inner ℝ hq
  have hfp : AVenhance.IsZ2Periodic f := fun n x => by dsimp [f]; rw [hp n x, hqp n x]
  have hder : (fun x => fderiv ℝ f x (basisVec k)) =
      fun x => inner ℝ (u x) (fderiv ℝ q x (basisVec k)) +
        inner ℝ (fderiv ℝ u x (basisVec k)) (q x) := by
    funext x
    exact fderiv_inner_apply ℝ (hu.differentiable (by simp) x) (hq.differentiable (by simp) x) _
  have hdu : Continuous (fun x => fderiv ℝ u x (basisVec k)) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdq : Continuous (fun x => fderiv ℝ q x (basisVec k)) :=
    (hq.continuous_fderiv (by simp)).clm_apply continuous_const
  have hleft := Galerkin.continuous_cell_integrable _ (hu.continuous.inner hdq)
  have hright := Galerkin.continuous_cell_integrable _ (hdu.inner hq.continuous)
  have hzero := periodic_partial_integral_zero f hf hfp k
  rw [hder, integral_add hleft hright] at hzero
  linarith

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Exact reserve shifts relative to gradient dissipation, rather than the full value norm. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Reserve-preserving extraction of all derivatives of order `s+1`. -/
def torusGradientReserveTensor {K L : ℕ} (s : ℕ) (hKL : K + s ≤ L)
    (w : TorusHk (L + 1) E) : TorusHk K (PiLp 2 (fun _ : DerivativeWord2 (s + 1) => E)) :=
  torusDerivativeTensor (r := s + 1)
    (truncateTorusHk (by omega : K + (s + 1) ≤ L + 1) w)

private def reserveGradientOrder {K L : ℕ} (s : ℕ) (hKL : K + s ≤ L)
    (j : Fin (K + 1)) : Fin (L + 1) := ⟨s + j.val, by omega⟩

private theorem reserveGradientOrder_injective {K L : ℕ} (s : ℕ) (hKL : K + s ≤ L) :
    Function.Injective (reserveGradientOrder s hKL) := by
  intro j k h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

/-- The extracted tensor norm is a sum of precisely the corresponding gradient levels. -/
theorem torusGradientReserveTensor_factorialNormSq {K L : ℕ} (ρ : ℝ)
    (s : ℕ) (hKL : K + s ≤ L) (w : TorusHk (L + 1) E) :
    factorialNormSq ρ (torusGradientReserveTensor s hKL w).val =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        derivativeNormSq w.val ⟨s + j.val + 1, by omega⟩ := by
  rw [torusGradientReserveTensor, torusDerivativeTensor_factorialNormSq,
    derivativeArray_factorialNormSq]
  have htr (q : Fin (K + (s + 1) + 1)) :
      derivativeNormSq (truncateTorusHk (by omega : K + (s + 1) ≤ L + 1) w).val q =
        derivativeNormSq w.val ⟨q.val, by omega⟩ := rfl
  apply Finset.sum_congr rfl
  intro j _
  rw [htr]
  congr 1
  apply congrArg (derivativeNormSq w.val)
  apply Fin.ext
  change (s + 1) + j.val = s + j.val + 1
  omega

/-- The exact shift factor of the coupling bound, measured against dissipation. -/
theorem torusGradientReserveTensor_factorialNorm_le {K L : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (s : ℕ) (hKL : K + s ≤ L) (w : TorusHk (L + 1) E) :
    Real.sqrt (factorialNormSq ρ (torusGradientReserveTensor s hKL w).val) ≤
      derivativeReserveFactor ρ K s * Real.sqrt (gradFactorialNormSq ρ w.val) := by
  have hsquare : factorialNormSq ρ (torusGradientReserveTensor s hKL w).val ≤
      (derivativeReserveFactor ρ K s) ^ 2 * gradFactorialNormSq ρ w.val := by
    rw [torusGradientReserveTensor_factorialNormSq]
    calc
      (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        derivativeNormSq w.val ⟨s + j.val + 1, by omega⟩) ≤
          ∑ j : Fin (K + 1), (derivativeReserveFactor ρ K s) ^ 2 *
            (factorialWeight ρ (s + j.val) * derivativeNormSq w.val ⟨s + j.val + 1, by omega⟩) := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (derivativeNormSq_nonneg _ _)
        simpa only [factorialWeight, Nat.add_comm] using
          factorialWeight_reserve_le ρ hρ (Nat.le_of_lt_succ j.isLt) s
      _ ≤ (derivativeReserveFactor ρ K s) ^ 2 * gradFactorialNormSq ρ w.val := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact sum_comp_le_sum_nonneg (reserveGradientOrder s hKL)
          (reserveGradientOrder_injective s hKL)
          (fun j : Fin (L + 1) => factorialWeight ρ j.val *
            derivativeNormSq w.val ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
          (fun j => mul_nonneg (factorialWeight_nonneg ρ j.val) (derivativeNormSq_nonneg _ _))
  calc
    Real.sqrt (factorialNormSq ρ (torusGradientReserveTensor s hKL w).val) ≤
      Real.sqrt ((derivativeReserveFactor ρ K s) ^ 2 * gradFactorialNormSq ρ w.val) :=
        Real.sqrt_le_sqrt hsquare
    _ = derivativeReserveFactor ρ K s * Real.sqrt (gradFactorialNormSq ρ w.val) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq]
      unfold derivativeReserveFactor
      positivity
end

/-! Assemble the two gradient directions in the output fiber used by the coupling coefficients. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The actual two-direction gradient as a Sobolev carrier. -/
def torusGradientTensor {K : ℕ} (w : TorusHk (K + 1) E) :
    TorusHk K (PiLp 2 (fun _ : Fin 2 => E)) :=
  torusFamilyTensor (fun k : Fin 2 => derivativeTorusHk (fun _ : Fin 1 => k) w)

/-- The two-direction carrier has exactly the factorial gradient square. -/
theorem torusGradientTensor_factorialNormSq {K : ℕ} (ρ : ℝ) (w : TorusHk (K + 1) E) :
    factorialNormSq ρ (torusGradientTensor w).val = gradFactorialNormSq ρ w.val := by
  rw [torusGradientTensor, torusFamilyTensor_factorialNormSq,
    ← torusDerivativeTensor_one_factorialNormSq, torusDerivativeTensor_factorialNormSq]
  let e : DerivativeWord2 1 ≃ Fin 2 :=
    { toFun := fun a => a 0
      invFun := fun k _ => k
      left_inv := fun a => by funext t; fin_cases t; rfl
      right_inv := fun _ => rfl }
  exact (Fintype.sum_equiv e
    (fun a : DerivativeWord2 1 => factorialNormSq ρ (derivativeJet a w.val))
    (fun k : Fin 2 => factorialNormSq ρ (derivativeJet (fun _ : Fin 1 => k) w.val))
    (fun a => by
      have ha : a = fun _ : Fin 1 => e a := by
        funext t
        fin_cases t
        rfl
      exact congrArg (fun z : DerivativeWord2 1 => factorialNormSq ρ (derivativeJet z w.val)) ha)).symm
end

/-! Reserve-compatible tensor extraction at the literal derivative order. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Positive-order derivative tensor extraction, indexed at its literal derivative order. -/
def torusPositiveDerivativeTensor {K L : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (hKL : K + (m - 1) ≤ L) (w : TorusHk (L + 1) E) :
    TorusHk K (PiLp 2 (fun _ : DerivativeWord2 m => E)) := by
  cases m with
  | zero => omega
  | succ s => exact torusGradientReserveTensor s (by simpa using hKL) w

/-- The positive-order tensor has the gradient reserve bound. -/
theorem torusPositiveDerivativeTensor_factorialNorm_le {K L : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (hm : 1 ≤ m) (hKL : K + (m - 1) ≤ L)
    (w : TorusHk (L + 1) E) :
    Real.sqrt (factorialNormSq ρ (torusPositiveDerivativeTensor m hm hKL w).val) ≤
      derivativeReserveFactor ρ K (m - 1) * Real.sqrt (gradFactorialNormSq ρ w.val) := by
  cases m with
  | zero => omega
  | succ s => exact torusGradientReserveTensor_factorialNorm_le ρ hρ s (by simpa using hKL) w

/-- Admissibility of orders includes the exact reserve loss used by the tensor extraction. -/
theorem admissibleOrders_reserve {ι : Type*} (K : ι → ℕ) (D : ℕ)
    (i i' : ι) (d : admissibleOrders K D i i') :
    1 ≤ d.1 - 1 ∧ K i + ((d.1 - 1) - 1) ≤ K i' := by
  have hd := Finset.mem_filter.mp d.2
  have hb := Finset.mem_Icc.mp hd.1
  exact ⟨by omega, by omega⟩
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CoupledEnergy.Variational

/-! Fixed-time regularity of the drift mask terms for smooth Galerkin fields. -/

/-- The scalar drift coefficient inherits all spatial smoothness of the velocity. -/
theorem driftCoefficient_contDiff {n : WithTop ℕ∞} (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ n v) : ContDiff ℝ n (driftCoefficient v) := by
  apply ContDiff.sum
  intro k _
  exact (contDiff_pi.mp hv k).smul contDiff_const

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- All drift-mask terms of a smooth finite Galerkin jet are spatially continuous. -/
theorem driftMaskTerm_continuous {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (D : RawJet2 (K + 1) E) (hD : ∀ a, Continuous (D a))
    (m : PositionMask j) (w : DerivativeWord2 j) : Continuous (driftMaskTerm hj v D m w) := by
  let l := maskLeftLength j m
  let left := (maskWordEquiv 2 j m w).1
  have hC : ContDiff ℝ (l + 0 : ℕ) (driftCoefficient v) :=
    (driftCoefficient_contDiff v hv).of_le (by simp)
  have hcoef := (orderedCoefficientDerivative_contDiff (driftCoefficient v) l 0 hC left).continuous
  change Continuous (fun x => ∑ k : Fin 2,
    (orderedCoefficientDerivative (driftCoefficient v) l left x (PiLp.single 2 k 1)) •
      D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩,
        Fin.snoc (maskWordEquiv 2 j m w).2 k⟩ x)
  apply continuous_finsetSum
  intro k _
  exact (hcoef.clm_apply continuous_const).smul (hD _)

variable [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Smooth Galerkin drift terms are cell L², independently of their quantitative estimate. -/
theorem driftMaskTerm_memLp {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (D : RawJet2 (K + 1) E) (hD : ∀ a, Continuous (D a))
    (m : PositionMask j) (w : DerivativeWord2 j) :
    MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict AVenhance.unitCube) := by
  let : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using WeakAlgebra.weak_unitCube_volume_lt_top⟩
  have hc := driftMaskTerm_continuous hj v hv D hD m w
  obtain ⟨C, _, hC⟩ := Galerkin.continuous_unitCube_bound _ hc
  apply MemLp.of_bound hc.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem (by
    exact AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge.bridge_unitCube_measurable)] with x hx
  exact hC x hx

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Bundle the actual weak gradient as a continuous linear map.
This gives time L² membership and convergence of its Fourier residual. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

def torusGradientTensorCLM (K : ℕ) : TorusHk (K + 1) E →L[ℝ]
    TorusHk K (PiLp 2 (fun _ : Fin 2 => E)) :=
  ∑ k : Fin 2, (mapTorusHkCLM K (tensorEntryCLM k)).comp
    (derivativeTorusHk (fun _ : Fin 1 => k))

@[simp] theorem torusGradientTensorCLM_apply (K : ℕ) (w : TorusHk (K + 1) E) :
    torusGradientTensorCLM K w = torusGradientTensor w := by
  simp only [torusGradientTensorCLM, sum_apply,
    ContinuousLinearMap.comp_apply, mapTorusHkCLM_apply, torusGradientTensor, torusFamilyTensor]

theorem torusGradientTensor_carrier_memLp (K : ℕ) (a b : ℝ)
    (w : ℝ → TorusHk (K + 1) E) (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => torusGradientTensor (w t)) 2 (volume.restrict (Set.Icc a b)) := by
  simpa only [Function.comp_def, torusGradientTensorCLM_apply] using!
    (torusGradientTensorCLM (E := E) K).comp_memLp' hw

end AVRegularity.CoupledEnergy.Variational
end
