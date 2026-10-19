-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Variational.GradientTensorCLM
public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM
public import AVRegularity.CoupledEnergyPlane.Variational.GradientTensorOperator

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Plane drift masks are genuinely L² using bounded velocity jets and the input weak jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {U : Set (Vec 2)}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem driftMaskTerm_memLp_of_coefficientBound {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D)
    (m : PositionMask j) (w : DerivativeWord2 j) (M : ℝ)
    (hb : ∀ x, ‖coefficientDerivativeArray (driftCoefficient v) (maskLeftLength j m) x‖ ≤ M) :
    MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict U) := by
  let l := maskLeftLength j m
  let left := (maskWordEquiv 2 j m w).1
  have hC : ContDiff ℝ (l + 0 : ℕ) (driftCoefficient v) :=
    (driftCoefficient_contDiff v hv).of_le (by simp)
  have hc := (orderedCoefficientDerivative_contDiff (driftCoefficient v) l 0 hC left).continuous
  change MemLp (fun x => ∑ k : Fin 2,
    (orderedCoefficientDerivative (driftCoefficient v) l left x (PiLp.single 2 k 1)) •
      D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩,
        Fin.snoc (maskWordEquiv 2 j m w).2 k⟩ x) 2 (volume.restrict U)
  apply memLp_finsetSum
  intro k _
  have hcoef : MemLp (fun x =>
      orderedCoefficientDerivative (driftCoefficient v) l left x (PiLp.single 2 k 1))
      ⊤ (volume.restrict U) := by
    apply memLp_top_of_bound (hc.clm_apply continuous_const).aestronglyMeasurable M
    apply Filter.Eventually.of_forall
    intro x
    have h := (coefficientDerivativeArray (driftCoefficient v) l x).le_opNorm (PiLp.single 2 k 1)
    have he : coefficientDerivativeArray (driftCoefficient v) l x (PiLp.single 2 k 1) left =
        orderedCoefficientDerivative (driftCoefficient v) l left x (PiLp.single 2 k 1) := rfl
    rw [← he]
    apply (PiLp.norm_apply_le _ left).trans
    have hs : ‖(PiLp.single 2 k (1 : ℝ) : PiLp 2 (fun _ : Fin 2 => ℝ))‖ = 1 := by simp
    rw [hs, mul_one] at h
    exact h.trans (hb x)
  exact hcoef.smul (hD _)

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The literal raw spatial form used in the weak-solution class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def planeRawCouplingFlux (K : ι → ℕ) (D : ℕ) (r : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ i', ∑ d : admissibleOrders K D i i', A i i' d r x
    (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
      (w i').toFunction.jet ⟨⟨d.1 - 1, by have hd := admissibleOrders_reserve K D i i' d; omega⟩, word⟩ x))

def planeRawSpatialRhs (K : ι → ℕ) (D : ℕ) (ν r : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) (φ : PlaneHk Set.univ 1 (h i)) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, v r x k * inner ℝ ((w i).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x) (φ.toFunction.jet (valueIndex2 1) x)) -
    ν * ∑ k : Fin 2, inner ℝ ((w i).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) -
    (∑ k : Fin 2, inner ℝ (planeRawCouplingFlux K D r A w i x k +
      (F i r).toFunction.jet (valueIndex2 (K i)) x k)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) +
    inner ℝ ((g i r).toFunction.jet (valueIndex2 (K i)) x) (φ.toFunction.jet (valueIndex2 1) x)

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Literal value representatives of the assembled derivative tensors. -/

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The assembled carrier has exactly the finite vector of the component value representatives. -/
theorem planeFamilyTensor_value_ae {K : ℕ} (w : J → PlaneHk Set.univ K E) :
    (planeFamilyTensor w).val (valueIndex2 K) =ᵐ[volume.restrict Set.univ]
      fun x => (WithLp.toLp 2 (fun j => (w j).val (valueIndex2 K) x) : PiLp 2 (fun _ : J => E)) := by
  rw [planeFamilyTensor_jet]
  have hs := Lp.coeFn_finsetSum Finset.univ (fun j : J =>
    (tensorEntryCLM (J := J) (E := E) j).compLpL 2 (volume.restrict Set.univ)
      ((w j).val (valueIndex2 K)))
  have ht : ∀ᵐ x ∂volume.restrict Set.univ, ∀ j : J,
      ((tensorEntryCLM (J := J) (E := E) j).compLpL 2 (volume.restrict Set.univ)
        ((w j).val (valueIndex2 K))) x = tensorEntryCLM (J := J) (E := E) j ((w j).val (valueIndex2 K) x) :=
    ae_all_iff.mpr (fun j => ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM (J := J) (E := E) j) _)
  filter_upwards [hs, ht] with x hx hterms
  rw [hx, Finset.sum_apply]
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [hterms]
  change (∑ k : J, PiLp.single 2 k ((w k).val (valueIndex2 K) x) j) = _
  simp

variable {K r : ℕ}

/-- The value of an ordered derivative tensor is the complete original order-r jet array. -/
theorem planeDerivativeTensor_value_ae (w : PlaneHk Set.univ (K + r) E) :
    (planeDerivativeTensor w).val (valueIndex2 K) =ᵐ[volume.restrict Set.univ]
      fun x => WithLp.toLp 2 (fun a : DerivativeWord2 r => w.val ⟨⟨r, by omega⟩, a⟩ x) := by
  have ht := planeFamilyTensor_value_ae (fun a : DerivativeWord2 r => derivativePlaneHk a w)
  have hval (a : DerivativeWord2 r) :
      (derivativePlaneHk a w).val (valueIndex2 K) = w.val ⟨⟨r, by omega⟩, a⟩ := by
    rw [derivativePlaneHk_apply]
    have hi : prefixJetIndex a (valueIndex2 K) = (⟨⟨r, by omega⟩, a⟩ : JetIndex2 (K + r)) := by
      simp [prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
    rw [hi]
  simpa only [planeDerivativeTensor, hval] using ht

/-- Reserve-compatible positive tensors retain the literal original derivative array at value order. -/
theorem planePositiveDerivativeTensor_value_ae {K L : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (hKL : K + (m - 1) ≤ L) (w : PlaneHk Set.univ (L + 1) E) :
    (planePositiveDerivativeTensor m hm hKL w).val (valueIndex2 K) =ᵐ[
      volume.restrict Set.univ] fun x =>
      (WithLp.toLp 2 (fun a : DerivativeWord2 m => w.val ⟨⟨m, by omega⟩, a⟩ x) :
        PiLp 2 (fun _ : DerivativeWord2 m => E)) := by
  cases m with
  | zero => omega
  | succ s =>
    have ht := planeDerivativeTensor_value_ae
      (truncatePlaneHk (by omega : K + (s + 1) ≤ L + 1) w)
    simpa only [planePositiveDerivativeTensor, planeGradientReserveTensor,
      truncatePlaneHk_apply, truncateJetIndex] using ht

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The true reserved derivative tensors are fixed bounded Sobolev operators. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

def planeDerivativeTensorOperator (K r : ℕ) :
    PlaneHk Set.univ (K + r) E →L[ℝ] PlaneHk Set.univ K (PiLp 2 (fun _ : DerivativeWord2 r => E)) :=
  ∑ a : DerivativeWord2 r, (mapPlaneHkOperator K (AVRegularity.CoupledEnergy.Galerkin.tensorEntryCLM (E := E) a)).comp
    (derivativePlaneHk a)

@[simp] theorem planeDerivativeTensorOperator_apply (K r : ℕ)
    (q : PlaneHk Set.univ (K + r) E) :
    planeDerivativeTensorOperator K r q = planeDerivativeTensor q := by
  simp only [planeDerivativeTensorOperator, sum_apply, ContinuousLinearMap.comp_apply,
    mapPlaneHkOperator_apply, planeDerivativeTensor, planeFamilyTensor]

def planePositiveDerivativeTensorOperator {K L : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (hKL : K + (m - 1) ≤ L) : PlaneHk Set.univ (L + 1) E →L[ℝ]
      PlaneHk Set.univ K (PiLp 2 (fun _ : DerivativeWord2 m => E)) := by
  cases m with
  | zero => omega
  | succ s =>
      have hh : K + (s + 1) ≤ L + 1 := by omega
      let T : PlaneHk Set.univ (L + 1) E →L[ℝ] PlaneHk Set.univ (K + (s + 1)) E :=
        truncatePlaneHk hh
      exact (planeDerivativeTensorOperator (E := E) K (s + 1)).comp T

@[simp] theorem planePositiveDerivativeTensorOperator_apply {K L : ℕ}
    (m : ℕ) (hm : 1 ≤ m) (hKL : K + (m - 1) ≤ L)
    (q : PlaneHk Set.univ (L + 1) E) :
    planePositiveDerivativeTensorOperator m hm hKL q = planePositiveDerivativeTensor m hm hKL q := by
  cases m with
  | zero => omega
  | succ s => simp only [planePositiveDerivativeTensorOperator, ContinuousLinearMap.comp_apply,
      planeDerivativeTensorOperator_apply, planePositiveDerivativeTensor, planeGradientReserveTensor]

end AVRegularity.CoupledEnergyPlane.Variational
end
