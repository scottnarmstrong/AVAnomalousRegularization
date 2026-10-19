-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.PlainSynthesis
public import AVRegularity.Statements.Intermediate.CoupledEnergy.GradFactorialNormSq
public import AVRegularity.CoupledEnergyPlane.Fourier.HilbertSobolevOperator
public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Assemble finite Sobolev families into a tensor carrier without losing a dimension factor. -/

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Assemble the fiber entries by their mutually orthogonal singleton injections. -/
def planeFamilyTensor {K : ℕ} (w : J → PlaneHk Set.univ K E) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : J => E)) :=
  ∑ a, mapPlaneHk (tensorEntryCLM a) (w a)

/-- Each assembled jet is the corresponding finite sum of L² singleton injections. -/
theorem planeFamilyTensor_jet {K : ℕ} (w : J → PlaneHk Set.univ K E) (j : JetIndex2 K) :
    (planeFamilyTensor w).val j =
      ∑ a, (tensorEntryCLM (E := E) a).compLpL 2 (volume.restrict Set.univ) ((w a).val j) := by
  simp [planeFamilyTensor, mapPlaneHk_component]

omit [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Distinct tensor injections are orthogonal in the cell Hilbert space. -/
theorem tensorEntryLp_inner (a b : J)
    (u v : ComponentL2 (volume.restrict Set.univ) E) :
    inner ℝ ((tensorEntryCLM a).compLpL 2 (volume.restrict Set.univ) u)
      ((tensorEntryCLM b).compLpL 2 (volume.restrict Set.univ) v) =
        if a = b then inner ℝ u v else 0 := by
  rw [L2.inner_def]
  have hpoint : (fun x => inner ℝ
      (((tensorEntryCLM a).compLpL 2 (volume.restrict Set.univ) u) x)
      (((tensorEntryCLM b).compLpL 2 (volume.restrict Set.univ) v) x)) =ᵐ[
      volume.restrict Set.univ] fun x => if a = b then inner ℝ (u x) (v x) else 0 := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM a) u,
      ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM b) v] with x hu hv
    rw [hu, hv]
    change inner ℝ (PiLp.single (β := fun _ : J => E) 2 a (u x))
      (PiLp.single (β := fun _ : J => E) 2 b (v x)) = _
    rw [PiLp.inner_apply]
    simp only [PiLp.ofLp_single, Pi.single_apply]
    change (∑ k : J, inner ℝ (if k = a then u x else 0) (if k = b then v x else 0)) = _
    have hs (k : J) : inner ℝ (if k = a then u x else 0) (if k = b then v x else 0) =
        if k = a then (if a = b then inner ℝ (u x) (v x) else 0) else 0 := by
      by_cases hka : k = a <;> by_cases hkb : k = b <;> simp_all
    simp_rw [hs]
    simp
  rw [integral_congr_ae hpoint]
  by_cases hab : a = b <;> simp [hab, L2.inner_def]

/-- The tensor norm has exactly the sum of entry norm squares. -/
theorem planeFamilyTensor_jet_normSq {K : ℕ} (w : J → PlaneHk Set.univ K E) (j : JetIndex2 K) :
    ‖(planeFamilyTensor w).val j‖ ^ 2 = ∑ a, ‖(w a).val j‖ ^ 2 := by
  rw [planeFamilyTensor_jet, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, tensorEntryLp_inner]
  simp

/-- The tensor factorial norm is exactly the sum of the entry factorial norm squares. -/
theorem planeFamilyTensor_factorialNormSq {K : ℕ} (ρ : ℝ) (w : J → PlaneHk Set.univ K E) :
    factorialNormSq ρ (planeFamilyTensor w).val = ∑ a, factorialNormSq ρ (w a).val := by
  unfold factorialNormSq derivativeNormSq
  simp_rw [planeFamilyTensor_jet_normSq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm, Finset.mul_sum]

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Full ordered derivative tensors in the periodic Sobolev carrier. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The full order-r derivative array, retaining its tensor Hilbert norm. -/
def planeDerivativeTensor {K r : ℕ} (w : PlaneHk Set.univ (K + r) E) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : DerivativeWord2 r => E)) :=
  planeFamilyTensor (fun a : DerivativeWord2 r => derivativePlaneHk a w)

/-- Tensor assembly preserves the exact factorial square of the derivative array. -/
theorem planeDerivativeTensor_factorialNormSq {K r : ℕ} (ρ : ℝ) (w : PlaneHk Set.univ (K + r) E) :
    factorialNormSq ρ (planeDerivativeTensor w).val =
      ∑ a : DerivativeWord2 r, factorialNormSq ρ (derivativeJet a w.val) := by
  rw [planeDerivativeTensor, planeFamilyTensor_factorialNormSq]
  rfl

/-- The first derivative tensor has exactly the gradient factorial square. -/
theorem planeDerivativeTensor_one_factorialNormSq {K : ℕ} (ρ : ℝ) (w : PlaneHk Set.univ (K + 1) E) :
    factorialNormSq ρ (planeDerivativeTensor (r := 1) w).val = gradFactorialNormSq ρ w.val := by
  rw [planeDerivativeTensor_factorialNormSq, derivativeArray_factorialNormSq]
  change (∑ j : Fin (K + 1), factorialWeight ρ j.val * derivativeNormSq w.val (shiftedJetOrder j)) =
    ∑ j : Fin (K + 1), factorialWeight ρ j.val *
      derivativeNormSq w.val ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  apply Finset.sum_congr rfl
  intro j _
  have hi : shiftedJetOrder (r := 1) j = ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ :=
    Fin.ext (Nat.add_comm 1 j.val)
  rw [hi]
end

/-! Exact reserve shifts relative to gradient dissipation, rather than the full value norm. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Reserve-preserving extraction of all derivatives of order `s+1`. -/
def planeGradientReserveTensor {K L : ℕ} (s : ℕ) (hKL : K + s ≤ L)
    (w : PlaneHk Set.univ (L + 1) E) : PlaneHk Set.univ K (PiLp 2 (fun _ : DerivativeWord2 (s + 1) => E)) :=
  planeDerivativeTensor (r := s + 1)
    (truncatePlaneHk (by omega : K + (s + 1) ≤ L + 1) w)

private def reserveGradientOrder {K L : ℕ} (s : ℕ) (hKL : K + s ≤ L)
    (j : Fin (K + 1)) : Fin (L + 1) := ⟨s + j.val, by omega⟩

private theorem reserveGradientOrder_injective {K L : ℕ} (s : ℕ) (hKL : K + s ≤ L) :
    Function.Injective (reserveGradientOrder s hKL) := by
  intro j k h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

/-- The extracted tensor norm is a sum of precisely the corresponding gradient levels. -/
theorem planeGradientReserveTensor_factorialNormSq {K L : ℕ} (ρ : ℝ)
    (s : ℕ) (hKL : K + s ≤ L) (w : PlaneHk Set.univ (L + 1) E) :
    factorialNormSq ρ (planeGradientReserveTensor s hKL w).val =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        derivativeNormSq w.val ⟨s + j.val + 1, by omega⟩ := by
  rw [planeGradientReserveTensor, planeDerivativeTensor_factorialNormSq,
    derivativeArray_factorialNormSq]
  have htr (q : Fin (K + (s + 1) + 1)) :
      derivativeNormSq (truncatePlaneHk (by omega : K + (s + 1) ≤ L + 1) w).val q =
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
theorem planeGradientReserveTensor_factorialNorm_le {K L : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (s : ℕ) (hKL : K + s ≤ L) (w : PlaneHk Set.univ (L + 1) E) :
    Real.sqrt (factorialNormSq ρ (planeGradientReserveTensor s hKL w).val) ≤
      derivativeReserveFactor ρ K s * Real.sqrt (gradFactorialNormSq ρ w.val) := by
  have hsquare : factorialNormSq ρ (planeGradientReserveTensor s hKL w).val ≤
      (derivativeReserveFactor ρ K s) ^ 2 * gradFactorialNormSq ρ w.val := by
    rw [planeGradientReserveTensor_factorialNormSq]
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
    Real.sqrt (factorialNormSq ρ (planeGradientReserveTensor s hKL w).val) ≤
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
def planeGradientTensor {K : ℕ} (w : PlaneHk Set.univ (K + 1) E) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) :=
  planeFamilyTensor (fun k : Fin 2 => derivativePlaneHk (fun _ : Fin 1 => k) w)

/-- The two-direction carrier has exactly the factorial gradient square. -/
theorem planeGradientTensor_factorialNormSq {K : ℕ} (ρ : ℝ) (w : PlaneHk Set.univ (K + 1) E) :
    factorialNormSq ρ (planeGradientTensor w).val = gradFactorialNormSq ρ w.val := by
  rw [planeGradientTensor, planeFamilyTensor_factorialNormSq,
    ← planeDerivativeTensor_one_factorialNormSq, planeDerivativeTensor_factorialNormSq]
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

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology ENNReal
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Native H¹ spatial tests separate raw plane L² time representatives almost everywhere. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeL2_ae_eq_of_H1_tests {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (f g : T → Lp E 2 (volume : Measure (Vec 2)))
    (htest : ∀ ψ : PlaneHk Set.univ 1 E,
      (fun t => inner ℝ (f t) (planeHkValueOperator 1 ψ)) =ᵐ[μ]
        fun t => inner ℝ (g t) (planeHkValueOperator 1 ψ)) :
    f =ᵐ[μ] g := by
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) :=
    by
      let : TopologicalSpace.SeparableSpace E := inferInstance
      let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
      let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
      exact Lp.SecondCountableTopology
  have hz : (fun t => f t - g t) =ᵐ[μ] 0 := by
    apply ae_eq_zero_of_forall_inner (𝕜 := ℝ)
    intro z
    have hN : ∀ᵐ t ∂μ, ∀ N : ℕ, inner ℝ (f t)
        (planeHkValueOperator 1 (hilbertBandHk N 1 z)) =
      inner ℝ (g t) (planeHkValueOperator 1 (hilbertBandHk N 1 z)) :=
      ae_all_iff.mpr (fun N => htest (hilbertBandHk N 1 z))
    filter_upwards [hN] with t ht
    have hp := (tendsto_hilbertProjection z).inner (𝕜 := ℝ)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f t - g t) atTop (𝓝 (f t - g t)))
    have hzero : ∀ N, inner ℝ (hilbertProjection N z) (f t - g t) = 0 := by
      intro N
      rw [inner_sub_right, ← real_inner_comm (hilbertProjection N z) (f t),
        ← real_inner_comm (hilbertProjection N z) (g t)]
      have hh := ht N
      simpa only [planeHkValueOperator_apply, hilbertBandHk_value,
        AVRegularity.Analysis.Convolution.univToPlane_planeToUniv] using sub_eq_zero.mpr hh
    simpa only [Pi.zero_apply] using (tendsto_nhds_unique hp
      (by simpa only [hzero] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))))
  filter_upwards [hz] with t ht
  exact sub_eq_zero.mp ht

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The literal plane representatives have the exact integrable Hilbert value pairings. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeRawValue_ae {K : ℕ} (u : PlaneHk Set.univ K E) :
    u.toFunction.jet (valueIndex2 K) =ᵐ[volume]
      planeHkValueOperator (E := E) K u := by
  exact (univToPlane_ae (u.val (valueIndex2 K))).symm

omit [FiniteDimensional ℝ E] in
theorem planeRawValue_pairing_integrable_and_integral {K L : ℕ}
    (u : PlaneHk Set.univ K E) (φ : PlaneHk Set.univ L E) :
    Integrable (fun x => inner ℝ (u.toFunction.jet (valueIndex2 K) x)
      (φ.toFunction.jet (valueIndex2 L) x)) volume ∧
    (∫ x, inner ℝ (u.toFunction.jet (valueIndex2 K) x)
      (φ.toFunction.jet (valueIndex2 L) x)) =
      inner ℝ (planeHkValueOperator (E := E) K u) (planeHkValueOperator (E := E) L φ) := by
  have he : (fun x => inner ℝ (u.toFunction.jet (valueIndex2 K) x)
      (φ.toFunction.jet (valueIndex2 L) x)) =ᵐ[volume]
      fun x => inner ℝ (planeHkValueOperator (E := E) K u x)
        (planeHkValueOperator (E := E) L φ x) := by
    filter_upwards [planeRawValue_ae u, planeRawValue_ae φ] with x hu hp
    rw [hu, hp]
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) _ _).congr he.symm, ?_⟩
  rw [integral_congr_ae he, L2.inner_def]

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Reserve-compatible tensor extraction at the literal derivative order of the statement. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Positive-order derivative tensor extraction, indexed at its literal derivative order. -/
def planePositiveDerivativeTensor {K L : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (hKL : K + (m - 1) ≤ L) (w : PlaneHk Set.univ (L + 1) E) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : DerivativeWord2 m => E)) := by
  cases m with
  | zero => omega
  | succ s => exact planeGradientReserveTensor s (by simpa using hKL) w

/-- The positive-order tensor has the gradient reserve bound of the coupling. -/
theorem planePositiveDerivativeTensor_factorialNorm_le {K L : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (hm : 1 ≤ m) (hKL : K + (m - 1) ≤ L)
    (w : PlaneHk Set.univ (L + 1) E) :
    Real.sqrt (factorialNormSq ρ (planePositiveDerivativeTensor m hm hKL w).val) ≤
      derivativeReserveFactor ρ K (m - 1) * Real.sqrt (gradFactorialNormSq ρ w.val) := by
  cases m with
  | zero => omega
  | succ s => exact planeGradientReserveTensor_factorialNorm_le ρ hρ s (by simpa using hKL) w

/-- Admissibility of the orders (`admissibleOrders`) includes the exact reserve loss used by the
tensor extraction. -/
theorem admissibleOrders_reserve {ι : Type*} (K : ι → ℕ) (D : ℕ)
    (i i' : ι) (d : admissibleOrders K D i i') :
    1 ≤ d.1 - 1 ∧ K i + ((d.1 - 1) - 1) ≤ K i' := by
  have hd := Finset.mem_filter.mp d.2
  have hb := Finset.mem_Icc.mp hd.1
  exact ⟨by omega, by omega⟩

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual two-direction Sobolev gradient is a fixed bounded linear operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

def planeGradientTensorOperator (K : ℕ) : PlaneHk Set.univ (K + 1) E →L[ℝ]
    PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) :=
  ∑ k : Fin 2, (mapPlaneHkOperator K (tensorEntryCLM (E := E) k)).comp
    (derivativePlaneHk (fun _ : Fin 1 => k))

@[simp] theorem planeGradientTensorOperator_apply (K : ℕ)
    (q : PlaneHk Set.univ (K + 1) E) :
    planeGradientTensorOperator K q = planeGradientTensor q := by
  simp only [planeGradientTensorOperator, sum_apply, ContinuousLinearMap.comp_apply,
    mapPlaneHkOperator_apply, planeGradientTensor, planeFamilyTensor]

end AVRegularity.CoupledEnergyPlane.Variational
end
