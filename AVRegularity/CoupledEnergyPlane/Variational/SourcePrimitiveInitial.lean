-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Variational.PrincipalMask
import AVRegularity.CoupledEnergyPlane.Transport.CarrierTransport
public import AVRegularity.CoupledEnergyPlane.Variational.ProductPlaneHkOperator
import AVRegularity.CoupledEnergyPlane.Variational.DerivativeTensorOperator
import AVRegularity.CoupledEnergyPlane.Fourier.LaplacianProjection
public import AVRegularity.CoupledEnergyPlane.HigherReadout
import AVenhance.Infra.ODE.Linear.Energy
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Spatial bounded multiplication is exactly the value of the constructed weak product carrier. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem planeCoefficientOperator_eq_productValue {K : ℕ}
    (q : PlaneHk Set.univ K E) (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {A : Fin (K + 1) → ℝ} (hA : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M) :
    planeCoefficientOperator C hC.continuous hM hb (planeHkValueOperator K q) =
      planeHkValueOperator K (q.mulCoefficient C hC hA) := by
  have hp : (q.mulCoefficient C hC hA).val (valueIndex2 K) =ᵐ[volume.restrict Set.univ]
      multiplicationRawJet C q.toFunction.jet (valueIndex2 K) := by
    unfold PlaneHk.mulCoefficient
    exact jetToL2_ae _ _ _
  have he : multiplicationRawJet C q.toFunction.jet (valueIndex2 K) =
      fun x => C x (q.toFunction.jet (valueIndex2 K) x) := by
    funext x
    exact multiplicationRawJet_value C q.toFunction.jet x
  rw [he] at hp
  change (q.mulCoefficient C hC hA).val (valueIndex2 K) =ᵐ[volume.restrict Set.univ]
    fun x => C x (q.val (valueIndex2 K) x) at hp
  simp only [Measure.restrict_univ] at hp
  simp only [planeHkValueOperator_apply]
  apply Lp.ext
  filter_upwards [planeCoefficientOperator_ae C hC.continuous hM hb
      (univToPlane (q.val (valueIndex2 K))), univToPlane_ae (q.val (valueIndex2 K)),
    univToPlane_ae ((q.mulCoefficient C hC hA).val (valueIndex2 K)), hp] with x ho hq hm hp
  rw [ho, hq, hm, hp]

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Literal admissible coupling fluxes, with the exact coefficient budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- One actual coupling flux at reserve `K i`, for an admissible order. -/
def planeCoupledFluxTerm (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (w : PlaneHk Set.univ (K i' + 1) (h i')) :
    PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  planeMultiplyIntervalCoefficient ρ hρ (K i) a b A hA t ht hC
    (planePositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
      (admissibleOrders_reserve K D i i' d).2 w)

omit [Fintype ι] in
/-- Each literal admissible coupling consumes only its declared reserve and coefficient budget. -/
theorem planeCoupledFluxTerm_factorialNorm_le (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (w : PlaneHk Set.univ (K i' + 1) (h i')) :
    Real.sqrt (factorialNormSq ρ (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC w).val) ≤
      ((coefficientSeminorm ρ (K i) a b A).toReal * derivativeReserveFactor ρ (K i) (d.1 - 2)) *
        Real.sqrt (gradFactorialNormSq ρ w.val) := by
  have hm := planeMultiplyIntervalCoefficient_factorialNorm_le ρ hρ (K i) a b A hA t ht hC
    (planePositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
      (admissibleOrders_reserve K D i i' d).2 w)
  have hs := planePositiveDerivativeTensor_factorialNorm_le ρ hρ (d.1 - 1)
    (admissibleOrders_reserve K D i i' d).1 (admissibleOrders_reserve K D i i' d).2 w
  conv_rhs at hs => rw [Nat.sub_sub]
  exact hm.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hs ENNReal.toReal_nonneg)

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Transport
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Principal mask arrays have zero pairing against the corresponding genuine weak Sobolev order. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem driftMaskL2Array_principal_inner_zero {K : ℕ}
    (p : PlaneHk Set.univ (K + 1) E) (j : Fin (K + 1))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hb : ∃ M : ℝ, ∀ x, ‖v x‖ ≤ M)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ v x (basisVec i) i = 0)
    (hT : ∀ (m : PositionMask j.val) (w : DerivativeWord2 j.val),
      MemLp (driftMaskTerm (Nat.le_of_lt_succ j.isLt) v p.toFunction.jet m w)
        2 (volume.restrict Set.univ))
    (m : PositionMask j.val) (hm : maskLeftLength j.val m = 0) :
    inner ℝ (driftMaskL2Array (Nat.le_of_lt_succ j.isLt) v p.toFunction.jet hT m)
      (orderL2Array p.val ⟨j.val, by omega⟩) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro w _
  simp only [L2.inner_def, Measure.restrict_univ]
  change (∫ x, inner ℝ
    ((hT m w).toLp (driftMaskTerm (Nat.le_of_lt_succ j.isLt) v p.toFunction.jet m w) x)
    (p.val (lowerIndex2 j w) x)) = 0
  have he : (fun x => inner ℝ
      ((hT m w).toLp (driftMaskTerm (Nat.le_of_lt_succ j.isLt) v p.toFunction.jet m w) x)
      (p.val (lowerIndex2 j w) x)) =ᵐ[volume]
      fun x => inner ℝ (∑ i : Fin 2, v x i • p.val (nextIndex2 j w i) x)
        (p.val (lowerIndex2 j w) x) := by
    have ht := (hT m w).coeFn_toLp
    simp only [Measure.restrict_univ] at ht
    filter_upwards [ht] with x hx
    rw [hx, driftMaskTerm_principal (Nat.le_of_lt_succ j.isLt) p.toFunction.jet v m hm w x]
    rfl
  rw [integral_congr_ae he]
  exact planeHk_principal_transport_zero p j w v hv hb hdiv

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Strong convergence of genuine Sobolev cutoff residuals and their bounded images. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeSobolevTimeResidual {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (N K : ℕ) (U : Lp (PlaneHk Set.univ K E) 2 μ) : Lp (PlaneHk Set.univ K E) 2 μ :=
  U - (planeHkCutoff (E := E) N K).compLpL 2 μ U

theorem planeSobolevTimeResidual_ae {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (N K : ℕ) (U : Lp (PlaneHk Set.univ K E) 2 μ) :
    planeSobolevTimeResidual μ N K U =ᵐ[μ] fun t => U t - planeHkCutoff N K (U t) := by
  filter_upwards [Lp.coeFn_sub U ((planeHkCutoff (E := E) N K).compLpL 2 μ U),
    ContinuousLinearMap.coeFn_compLpL (planeHkCutoff (E := E) N K) U] with t hs hc
  exact hs.trans (congrArg (fun z => U t - z) hc)

theorem tendsto_planeSobolevTimeResidual {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (K : ℕ) (U : Lp (PlaneHk Set.univ K E) 2 μ) :
    Tendsto (fun N => planeSobolevTimeResidual μ N K U) atTop (𝓝 0) := by
  simpa only [planeSobolevTimeResidual, sub_self] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => U) atTop (𝓝 U)).sub
      (tendsto_planeHkCutoff_time μ K U))

theorem tendsto_planeSobolevTimeResidual_image {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : ℕ) (U : Lp (PlaneHk Set.univ K E) 2 μ)
    {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    (L : Lp (PlaneHk Set.univ K E) 2 μ →L[ℝ] J) :
    Tendsto (fun N => L (planeSobolevTimeResidual μ N K U)) atTop (𝓝 0) := by
  have ht := (L.continuous.tendsto (0 : Lp (PlaneHk Set.univ K E) 2 μ)).comp
    (tendsto_planeSobolevTimeResidual μ K U)
  rw [L.map_zero] at ht
  exact ht

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Identifying a true transport jet with its complete mask array removes exactly the principal energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem orderL2Array_eq_masks_of_ae {K j : ℕ} (hj : j ≤ K)
    (D : RawJet2 (K + 1) E) (v : Vec 2 → Vec 2)
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict Set.univ))
    (Q : JetL2 (volume.restrict Set.univ) K E)
    (hQ : ∀ w : DerivativeWord2 j, Q ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ =ᵐ[volume]
      fun x => ∑ m : PositionMask j, driftMaskTerm hj v D m w x) :
    orderL2Array Q ⟨j, Nat.lt_succ_of_le hj⟩ = ∑ m : PositionMask j, driftMaskL2Array hj v D hT m := by
  apply PiLp.ext
  intro w
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  change Q ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ =
    ∑ m : PositionMask j, (hT m w).toLp (driftMaskTerm hj v D m w)
  apply Lp.ext
  have hs := Lp.coeFn_finsetSum Finset.univ
    (fun m : PositionMask j => (hT m w).toLp (driftMaskTerm hj v D m w))
  have ht := ae_all_iff.mpr (fun m : PositionMask j => (hT m w).coeFn_toLp)
  simp only [Measure.restrict_univ] at hs ht ⊢
  filter_upwards [hQ w, hs, ht] with x hq hs ht
  rw [hq, hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun m _ => (ht m).symm)

theorem transportOrder_inner_eq_commutator_of_ae_masks {K : ℕ}
    (p : PlaneHk Set.univ (K + 1) E) (j : Fin (K + 1))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hb : ∃ M : ℝ, ∀ x, ‖v x‖ ≤ M)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ v x (basisVec i) i = 0)
    (hT : ∀ (m : PositionMask j.val) (w : DerivativeWord2 j.val),
      MemLp (driftMaskTerm (Nat.le_of_lt_succ j.isLt) v p.toFunction.jet m w)
        2 (volume.restrict Set.univ))
    (Q : JetL2 (volume.restrict Set.univ) K E)
    (hQ : ∀ w : DerivativeWord2 j.val, Q ⟨j, w⟩ =ᵐ[volume]
      fun x => ∑ m : PositionMask j.val,
        driftMaskTerm (Nat.le_of_lt_succ j.isLt) v p.toFunction.jet m w x) :
    inner ℝ (orderL2Array Q j) (orderL2Array p.val ⟨j.val, by omega⟩) =
      inner ℝ (driftCommutatorL2Array (Nat.le_of_lt_succ j.isLt) v p.toFunction.jet hT)
        (orderL2Array p.val ⟨j.val, by omega⟩) := by
  rw [orderL2Array_eq_masks_of_ae (Nat.le_of_lt_succ j.isLt) p.toFunction.jet v hT Q hQ]
  simp only [driftCommutatorL2Array, sum_inner]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : 1 ≤ maskLeftLength j.val m
  · rw [ite_eq_left hm]
  · rw [ite_eq_right hm, inner_zero_left]
    exact driftMaskL2Array_principal_inner_zero p j v hv hb hdiv hT m (by omega)

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Finite assembly of bounded images of actual Sobolev cutoff residuals. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
variable {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]

def assemblePlaneResidualFlux (μ : Measure ℝ) (K : ι → ℕ)
    {D : ι → Type*} [∀ i, Fintype (D i)]
    (C : ∀ i, D i → Lp (PlaneHk Set.univ (K i) (h i)) 2 μ →L[ℝ] Lp J 2 μ)
    (U : ∀ i, Lp (PlaneHk Set.univ (K i) (h i)) 2 μ) (F : Lp J 2 μ) (N : ℕ) : Lp J 2 μ :=
  assembleTimeFlux μ 0 0 (fun i d => C i d (planeSobolevTimeResidual μ N (K i) (U i))) F

theorem tendsto_assemblePlaneResidualFlux (μ : Measure ℝ) (K : ι → ℕ)
    {D : ι → Type*} [∀ i, Fintype (D i)]
    (C : ∀ i, D i → Lp (PlaneHk Set.univ (K i) (h i)) 2 μ →L[ℝ] Lp J 2 μ)
    (U : ∀ i, Lp (PlaneHk Set.univ (K i) (h i)) 2 μ) (F : Lp J 2 μ) :
    Tendsto (fun N => assemblePlaneResidualFlux μ K C U F N) atTop (𝓝 F) := by
  apply assembleTimeFlux_zero_tendsto (J := J) (I := ι) (D := D)
  intro i d
  exact tendsto_planeSobolevTimeResidual_image (E := h i) μ (K i) (U i) (C i d)

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Each literal finite Leibniz multiplier is strongly measurable on fixed spatial inputs. -/

variable {T E F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem productMaskOperator_stronglyMeasurable {K : ℕ}
    (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (B : Fin (K + 1) → ℝ) (hB : ∀ l, 0 ≤ B l)
    (hb : ∀ t l x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ B l)
    (α : JetIndex2 K) (m : PositionMask α.1.val)
    (U : Lp E 2 (volume : Measure (Vec 2))) :
    StronglyMeasurable (fun t => productMaskOperator (C t) (hc t) (hb t) α m U) := by
  let l : Fin (K + 1) := ⟨maskLeftLength α.1.val m,
    Nat.lt_succ_of_le ((maskLeftLength_le α.1.val m).trans (Nat.le_of_lt_succ α.1.isLt))⟩
  have hcm (t : T) : Continuous
      (orderedCoefficientDerivative (C t) l.val (maskWordEquiv 2 α.1.val m α.2).1) :=
    (orderedCoefficientDerivative_contDiff (C t) l.val 0
      (by simpa only [Nat.add_zero] using (hc t).of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt))
      (maskWordEquiv 2 α.1.val m α.2).1).continuous
  have hj : Measurable (Function.uncurry (fun t =>
      orderedCoefficientDerivative (C t) l.val (maskWordEquiv 2 α.1.val m α.2).1)) :=
    orderedCoefficientDerivative_measurable C hC K l.val hc
      (Nat.le_of_lt_succ l.isLt) (maskWordEquiv 2 α.1.val m α.2).1
  have hb' (t : T) (x : Vec 2) :
      ‖orderedCoefficientDerivative (C t) l.val (maskWordEquiv 2 α.1.val m α.2).1 x‖ ≤ B l :=
    (orderedCoefficientDerivative_norm_le_array (C t) l.val
      (maskWordEquiv 2 α.1.val m α.2).1 x).trans (hb t l x)
  have hs := planeCoefficientOperator_stronglyMeasurable
    (fun t => orderedCoefficientDerivative (C t) l.val (maskWordEquiv 2 α.1.val m α.2).1)
    hcm hj (hB l) hb' U
  convert hs using 1
  ext t
  rfl

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Uniform unweighted Sobolev operator bounds from the actual finite coefficient jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def productJetBound {K : ℕ} (B : Fin (K + 1) → ℝ) (α : JetIndex2 K) : ℝ :=
  ∑ m : PositionMask α.1.val, B ⟨maskLeftLength α.1.val m,
    Nat.lt_succ_of_le ((maskLeftLength_le α.1.val m).trans (Nat.le_of_lt_succ α.1.isLt))⟩

def productSobolevBound {K : ℕ} (B : Fin (K + 1) → ℝ) : ℝ :=
  Real.sqrt (∑ α : JetIndex2 K, productJetBound B α ^ 2)

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E]
  [BorelSpace F] [CompleteSpace F] in
theorem productMaskOperator_norm_le {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (hc : ContDiff ℝ (K : ℕ) C) {B : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l)
    (α : JetIndex2 K) (m : PositionMask α.1.val) :
    ‖productMaskOperator C hc hb α m‖ ≤ B ⟨maskLeftLength α.1.val m,
      Nat.lt_succ_of_le ((maskLeftLength_le α.1.val m).trans (Nat.le_of_lt_succ α.1.isLt))⟩ := by
  unfold productMaskOperator
  exact planeCoefficientOperator_norm_le _ _ _ _

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E]
  [BorelSpace F] [CompleteSpace F] in
theorem productJetOperator_apply_norm_le {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (hc : ContDiff ℝ (K : ℕ) C) {B : Fin (K + 1) → ℝ} (hB : ∀ l, 0 ≤ B l)
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l)
    (α : JetIndex2 K) (D : JetL2 (volume.restrict Set.univ) K E) :
    ‖productJetOperator C hc hb α D‖ ≤ productJetBound B α * ‖D‖ := by
  simp only [productJetOperator, sum_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  apply (norm_sum_le _ _).trans
  rw [productJetBound, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m _
  have hn := (productMaskOperator C hc hb α m).le_opNorm
    (univToPlane (D (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2)))
  have hb' := productMaskOperator_norm_le C hc hb α m
  have hd : ‖univToPlane (D (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2))‖ ≤ ‖D‖ := by
    rw [univToPlane.norm_map]
    exact PiLp.norm_apply_le _ _
  exact hn.trans (mul_le_mul hb' hd (norm_nonneg _) (hB _))

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E]
  [BorelSpace F] [CompleteSpace F] in
theorem productAmbientJetOperator_apply_norm_le {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (hc : ContDiff ℝ (K : ℕ) C) {B : Fin (K + 1) → ℝ} (hB : ∀ l, 0 ≤ B l)
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l)
    (D : JetL2 (volume.restrict Set.univ) K E) :
    ‖productAmbientJetOperator C hc hb D‖ ≤ productSobolevBound B * ‖D‖ := by
  unfold productSobolevBound
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro α _
  change ‖planeToUniv (productJetOperator C hc hb α D)‖ ^ 2 ≤ _
  rw [planeToUniv.norm_map]
  have hp := productJetOperator_apply_norm_le C hc hB hb α D
  have hn : 0 ≤ productJetBound B α := Finset.sum_nonneg (fun _ _ => hB _)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg D))).mpr hp
  simpa only [mul_pow] using hs


theorem productPlaneHkOperator_norm_le {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (hc : ContDiff ℝ (K : ℕ) C) {B : Fin (K + 1) → ℝ} (hB : ∀ l, 0 ≤ B l)
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l) :
    ‖productPlaneHkOperator C hc hb‖ ≤ productSobolevBound B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro q
  change ‖productAmbientJetOperator C hc hb q.val‖ ≤ productSobolevBound B * ‖q.val‖
  exact productAmbientJetOperator_apply_norm_le C hc hB hb q.val

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The exact plane flux budget is continuous in the strong time L² topology. -/

open AVRegularity.CoupledEnergy.Variational
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)] [∀ i, FiniteDimensional ℝ (E i)]

theorem planeMassGradNormSq_integral_split (μ : Measure T) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (f : ∀ i, T → PlaneHk Set.univ (K i + 1) (E i)) (hf : ∀ i, MemLp (f i) 2 μ) :
    (∫ t, massGradNormSq ρ π (fun i => (f i t).val) ∂μ) =
      ∑ i, (π i)⁻¹ * ∫ t, gradFactorialNormSq ρ (f i t).val ∂μ := by
  have he (t : T) : massGradNormSq ρ π (fun i => (f i t).val) =
      massNormSq ρ π (fun i => (planeGradientTensor (f i t)).val) := by
    change (∑ i, (π i)⁻¹ * gradFactorialNormSq ρ (f i t).val) = _
    simp only [massNormSq, planeGradientTensor_factorialNormSq]
  simp_rw [he]
  rw [planeMassNormSq_integral_split μ K ρ π (fun i t => planeGradientTensor (f i t))
    (fun i => by simpa only [Function.comp_def, planeGradientTensorOperator_apply] using
      (planeGradientTensorOperator (E := E i) (K i)).comp_memLp' (hf i))]
  simp only [planeGradientTensor_factorialNormSq]

theorem planeMassGradNormSq_timeLp_tendsto (μ : Measure T) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (U : ℕ → ∀ i, Lp (PlaneHk Set.univ (K i + 1) (E i)) 2 μ)
    (V : ∀ i, Lp (PlaneHk Set.univ (K i + 1) (E i)) 2 μ)
    (hU : ∀ i, Tendsto (fun N => U N i) atTop (𝓝 (V i))) :
    Tendsto (fun N => ∫ t, massGradNormSq ρ π (fun i => (U N i t).val) ∂μ)
      atTop (𝓝 (∫ t, massGradNormSq ρ π (fun i => (V i t).val) ∂μ)) := by
  let L (i : ι) : PlaneHk Set.univ (K i + 1) (E i) →L[ℝ]
      JetL2 (volume.restrict (Set.univ : Set (Vec 2))) (K i) (PiLp 2 (fun _ : Fin 2 => E i)) :=
    (factorialWeightedJetCLM (E := PiLp 2 (fun _ : Fin 2 => E i)) (μ := volume.restrict Set.univ) ρ (K i)).comp
      ((planeHkGraph (E := PiLp 2 (fun _ : Fin 2 => E i)) Set.univ (K i)).toSubmodule.subtypeL.comp
        (planeGradientTensorOperator (E := E i) (K i)))
  have he (i : ι) (x : PlaneHk Set.univ (K i + 1) (E i)) :
      ‖L i x‖ ^ 2 = gradFactorialNormSq ρ x.val := by
    rw [← planeGradientTensor_factorialNormSq ρ x]
    change ‖factorialWeightedJet ρ ((planeGradientTensorOperator (E := E i) (K i) x).val)‖ ^ 2 = _
    rw [planeGradientTensorOperator_apply]
    exact factorialWeightedJet_normSq ρ (planeGradientTensor x).val
  have hi (i : ι) : Tendsto (fun N => ∫ t, gradFactorialNormSq ρ (U N i t).val ∂μ)
      atTop (𝓝 (∫ t, gradFactorialNormSq ρ (V i t).val ∂μ)) := by
    simpa only [he] using timeLp_readout_integral_norm_square_tendsto μ (L i)
      (fun N => U N i) (V i) (hU i)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => (hi i).const_mul ((π i)⁻¹))
  simpa only [← planeMassGradNormSq_integral_split μ K ρ π _ (fun i => Lp.memLp (U _ i)),
    ← planeMassGradNormSq_integral_split μ K ρ π _ (fun i => Lp.memLp (V i))] using hs

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Topology
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual Sobolev product operators are strongly measurable on every fixed weak carrier. -/

variable {T E F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem productPlaneHkOperator_stronglyMeasurable {K : ℕ}
    (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (B : Fin (K + 1) → ℝ) (hB : ∀ l, 0 ≤ B l)
    (hb : ∀ t l x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ B l)
    (q : PlaneHk Set.univ K E) :
    StronglyMeasurable (fun t => productPlaneHkOperator (C t) (hc t) (hb t) q) := by
  simp only [productPlaneHkOperator_apply]
  apply (Embedding.comp_stronglyMeasurable_iff
    (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : PlaneHk Set.univ K F →
      JetL2 (volume.restrict Set.univ) K F))).mp
  let : SecondCountableTopology (ComponentL2 (volume.restrict Set.univ) F) :=
    planeL2SecondCountableTopology
  borelize ↥(ComponentL2 (volume.restrict Set.univ) F)
  have hjet (α : JetIndex2 K) : StronglyMeasurable
      (fun t => (q.mulCoefficient (C t) (hc t) (hb t)).val α) := by
    have hsum : StronglyMeasurable (fun t => productJetReadout q (C t) (hc t) (hb t) α) :=
      Finset.stronglyMeasurable_fun_sum Finset.univ (fun m _ =>
        productMaskOperator_stronglyMeasurable C hC hc B hB hb α m
          (univToPlane (q.val (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2))))
    have hs := planeToUniv.continuous.comp_stronglyMeasurable hsum
    have he : (fun t => planeToUniv (productJetReadout q (C t) (hc t) (hb t) α)) =
        fun t => (q.mulCoefficient (C t) (hc t) (hb t)).val α := by
      funext t
      rw [productJetReadout_eq_productJet, planeToUniv_univToPlane]
    rw [he] at hs
    exact hs
  have hm : Measurable (fun t => fun α : JetIndex2 K =>
      (q.mulCoefficient (C t) (hc t) (hb t)).val α) :=
    Measurable.of_eval (fun α => (hjet α).measurable)
  have hs := (PiLp.continuous_toLp 2
    (fun _ : JetIndex2 K => ComponentL2 (volume.restrict Set.univ) F)).comp_stronglyMeasurable
      hm.stronglyMeasurable
  convert hs using 1

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Schur absorption for the actual differentiated coupling fluxes. -/

open AVRegularity.CoupledEnergy.Variational

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- Pairing one actual coupling flux with the target gradient costs exactly its reserve budget. -/
theorem planeCoupledFluxTerm_pairing_abs_le (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (wi : PlaneHk Set.univ (K i + 1) (h i)) (wj : PlaneHk Set.univ (K i' + 1) (h i')) :
    |inner ℝ
      (factorialWeightedJet ρ (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC wj).val)
      (factorialWeightedJet ρ (planeGradientTensor wi).val)| ≤
    ((coefficientSeminorm ρ (K i) a b A).toReal * derivativeReserveFactor ρ (K i) (d.1 - 2)) *
      Real.sqrt (gradFactorialNormSq ρ wj.val) * Real.sqrt (gradFactorialNormSq ρ wi.val) := by
  have hc := abs_real_inner_le_norm
    (factorialWeightedJet ρ (planeCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC wj).val)
    (factorialWeightedJet ρ (planeGradientTensor wi).val)
  simp only [factorialWeightedJet_norm, planeGradientTensor_factorialNormSq] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (planeCoupledFluxTerm_factorialNorm_le ρ hρ K D a b i i' d A hA t ht hC wj)
      (Real.sqrt_nonneg _))

/-- The sum of absolute differentiated coupling pairings is absorbed by ν/8 of dissipation. -/
theorem planeCoupledFlux_schurEnergy_abs_sum_le (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) :
    (∑ i, ∑ i', ∑ d : admissibleOrders K D i i', (π i)⁻¹ * |inner ℝ
      (factorialWeightedJet ρ (planeCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d)
        (hA i i' d) t ht (hC i i' d) (w i')).val)
      (factorialWeightedJet ρ (planeGradientTensor (w i)).val)|) ≤
      (ν / 8) * massGradNormSq ρ π (fun i => (w i).val) := by
  let Y := fun i => Real.sqrt (gradFactorialNormSq ρ (w i).val)
  have hbound : (∑ i, ∑ i', ∑ d : admissibleOrders K D i i', (π i)⁻¹ * |inner ℝ
      (factorialWeightedJet ρ (planeCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d)
        (hA i i' d) t ht (hC i i' d) (w i')).val)
      (factorialWeightedJet ρ (planeGradientTensor (w i)).val)|) ≤
      ∑ i, ∑ i', (π i)⁻¹ * couplingReserveBudget ρ K D a b A i i' * Y i * Y i' := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro i' _
    unfold couplingReserveBudget
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d _
    have hb := planeCoupledFluxTerm_pairing_abs_le ρ hρ K D a b i i' d (A i i' d)
        (hA i i' d) t ht (hC i i' d) (w i) (w i')
    have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (hπ i).le)
    simpa only [Y, mul_assoc, mul_comm, mul_left_comm] using hm
  have hs := couplingReserveBudget_quadratic_le ν ρ hν hρ π hπ K D a b A hschur Y
  refine hbound.trans (hs.trans_eq ?_)
  congr 1
  unfold massGradNormSq
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Real.sq_sqrt
  rw [← planeGradientTensor_factorialNormSq ρ (w i)]
  exact factorialNormSq_nonneg _ _

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual finite Sobolev product is one bounded operator on Bochner L². -/

variable {T E F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def productPlaneHkTimeCLM {K : ℕ} (μ : Measure T)
    (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (B : Fin (K + 1) → ℝ) (hB : ∀ l, 0 ≤ B l)
    (hb : ∀ t l x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ B l) :
    Lp (PlaneHk Set.univ K E) 2 μ →L[ℝ] Lp (PlaneHk Set.univ K F) 2 μ := by
  let : TopologicalSpace.SeparableSpace (PlaneHk Set.univ K E) := planeHkSeparableSpace K
  let : SecondCountableTopology (PlaneHk Set.univ K E) := inferInstance
  borelize (PlaneHk Set.univ K E)
  exact timeOperatorCLM μ (fun t => productPlaneHkOperator (C t) (hc t) (hb t))
    (productPlaneHkOperator_stronglyMeasurable C hC hc B hB hb)
    (productSobolevBound B) (Real.sqrt_nonneg _)
    (fun t => productPlaneHkOperator_norm_le (C t) (hc t) hB (hb t))

theorem productPlaneHkTimeCLM_ae {K : ℕ} (μ : Measure T)
    (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (B : Fin (K + 1) → ℝ) (hB : ∀ l, 0 ≤ B l)
    (hb : ∀ t l x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ B l)
    (U : Lp (PlaneHk Set.univ K E) 2 μ) :
    productPlaneHkTimeCLM μ C hC hc B hB hb U =ᵐ[μ]
      fun t => (U t).mulCoefficient (C t) (hc t) (hb t) := by
  let : TopologicalSpace.SeparableSpace (PlaneHk Set.univ K E) := planeHkSeparableSpace K
  let : SecondCountableTopology (PlaneHk Set.univ K E) := inferInstance
  borelize (PlaneHk Set.univ K E)
  have he := timeOperatorValue_ae μ (fun t => productPlaneHkOperator (C t) (hc t) (hb t))
    (productPlaneHkOperator_stronglyMeasurable C hC hc B hB hb)
    (productSobolevBound B) (Real.sqrt_nonneg _)
    (fun t => productPlaneHkOperator_norm_le (C t) (hc t) hB (hb t)) U
  simp only [productPlaneHkOperator_apply] at he
  convert he using 1
  rfl

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The true gradient value is the finite tensor of the genuine first weak jets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeGradientTensor_value_formula {K : ℕ} (q : PlaneHk Set.univ (K + 1) E) :
    planeHkValueOperator K (planeGradientTensor q) =
      ∑ k : Fin 2, (tensorEntryCLM (E := E) k).compLpL 2 volume
        (univToPlane (q.val ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩)) := by
  simp only [planeHkValueOperator_apply, planeGradientTensor, planeFamilyTensor_jet,
    derivativePlaneHk_apply, map_sum, univToPlane_fiberMap]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have hi : prefixJetIndex (fun _ : Fin 1 => k) (valueIndex2 K) =
      (⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ : Fin 1 => k⟩ : JetIndex2 (K + 1)) := by
    simp [prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
  rw [hi]
end

/-! Values of the reserved derivative tensors are the literal higher weak jets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeDerivativeTensor_value_formula {K r : ℕ}
    (q : PlaneHk Set.univ (K + r) E) :
    planeHkValueOperator K (planeDerivativeTensor q) =
      ∑ a : DerivativeWord2 r, (tensorEntryCLM (E := E) a).compLpL 2 volume
        (univToPlane (q.val ⟨⟨r, by omega⟩, a⟩)) := by
  simp only [planeHkValueOperator_apply, planeDerivativeTensor, planeFamilyTensor_jet,
    derivativePlaneHk_apply, map_sum, univToPlane_fiberMap]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have hi : prefixJetIndex a (valueIndex2 K) =
      (⟨⟨r, by omega⟩, a⟩ : JetIndex2 (K + r)) := by
    simp [prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
  rw [hi]

theorem planePositiveDerivativeTensor_value_formula {K L : ℕ}
    (m : ℕ) (hm : 1 ≤ m) (hKL : K + (m - 1) ≤ L)
    (q : PlaneHk Set.univ (L + 1) E) :
    planeHkValueOperator K (planePositiveDerivativeTensor m hm hKL q) =
      ∑ a : DerivativeWord2 m, (tensorEntryCLM (E := E) a).compLpL 2 volume
        (univToPlane (q.val ⟨⟨m, by omega⟩, a⟩)) := by
  cases m with
  | zero => omega
  | succ s =>
      change planeHkValueOperator K
        (planeDerivativeTensor (r := s + 1)
          (truncatePlaneHk (by omega : K + (s + 1) ≤ L + 1) q)) = _
      rw [planeDerivativeTensor_value_formula]
      rfl
end

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The genuine gradient carrier agrees with the literal first weak jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeGradientTensor_raw_value_ae {K : ℕ} (q : PlaneHk Set.univ (K + 1) E) :
    planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => E)) K (planeGradientTensor (E := E) q)
      =ᵐ[volume] fun x => WithLp.toLp 2 (fun k : Fin 2 =>
        q.toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x) := by
  have ht := planeFamilyTensor_value_ae (fun k : Fin 2 =>
    derivativePlaneHk (fun _ : Fin 1 => k) q)
  have hval (k : Fin 2) :
      (derivativePlaneHk (fun _ : Fin 1 => k) q).val (valueIndex2 K) =
        q.val ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ := by
    rw [derivativePlaneHk_apply]
    have hi : prefixJetIndex (fun _ : Fin 1 => k) (valueIndex2 K) =
        (⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ : JetIndex2 (K + 1)) := by
      simp only [prefixJetIndex, valueIndex2, valueIndex]
      congr 1
      funext a
      fin_cases a
      rfl
    rw [hi]
  simp only [hval, Measure.restrict_univ] at ht
  exact (univToPlane_ae ((planeGradientTensor (E := E) q).val (valueIndex2 K))).trans ht

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! A projected value readout determines the entire bounded-frequency Sobolev carrier. -/

variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem hilbertBandHk_time_alignment_ae (μ : Measure T) (N K : ℕ)
    (U : Lp (PlaneHk Set.univ K E) 2 μ) (q : T → Lp E 2 (volume : Measure (Vec 2)))
    (hq : q =ᵐ[μ] fun t => hilbertProjection (E := E) N (planeHkValueOperator (E := E) K (U t))) :
    (fun t => hilbertBandHk N K (q t)) =ᵐ[μ]
      ((planeHkCutoff (E := E) N K).compLpL 2 μ U : T → PlaneHk Set.univ K E) := by
  filter_upwards [hq, ContinuousLinearMap.coeFn_compLpL (planeHkCutoff (E := E) N K) U]
    with t hq hc
  rw [hq, hc]
  exact hilbertBandHk_projection (E := E) N K (planeHkValueOperator (E := E) K (U t))

end AVRegularity.CoupledEnergyPlane.Variational
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Exact gradient-energy convergence for band curves aligned with genuine time Sobolev carriers. -/

variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem bandCurve_gradient_integral_tendsto_of_alignment (μ : Measure T) (K : ι → ℕ)
    (ρ : ℝ) (π : ι → ℝ)
    (U : ∀ i, Lp (PlaneHk Set.univ (K i + 1) (E i)) 2 μ)
    (q : ℕ → T → ProjectedFamily E)
    (hq : ∀ N i, (fun t => q N t i) =ᵐ[μ] fun t =>
      hilbertProjection (E := E i) N (planeHkValueOperator (E := E i) (K i + 1) (U i t))) :
    Tendsto (fun N => ∫ t, massGradNormSq ρ π
      (fun i => (hilbertBandHk N (K i + 1) (q N t i)).val) ∂μ)
      atTop (𝓝 (∫ t, massGradNormSq ρ π (fun i => (U i t).val) ∂μ)) := by
  let V := fun N i => (planeHkCutoff (E := E i) N (K i + 1)).compLpL 2 μ (U i)
  have he := planeMassGradNormSq_timeLp_tendsto μ K ρ π V U
    (fun i => tendsto_planeHkCutoff_time μ (K i + 1) (U i))
  have hi (N : ℕ) : (∫ t, massGradNormSq ρ π
      (fun i => (hilbertBandHk N (K i + 1) (q N t i)).val) ∂μ) =
        ∫ t, massGradNormSq ρ π (fun i => (V N i t).val) ∂μ := by
    have ha := ae_all_iff.mpr (fun i => hilbertBandHk_time_alignment_ae μ N (K i + 1)
      (U i) (fun t => q N t i) (hq N i))
    apply integral_congr_ae
    filter_upwards [ha] with t ht
    exact congrArg (massGradNormSq ρ π) (funext (fun i => congrArg Subtype.val (ht i)))
  simpa only [← hi] using he

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.ODE
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Sobolev-valued frequency primitives of genuine value and divergence sources. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance bandPrimitiveAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance bandPrimitiveTopAdd (K : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ K E) :=
  inferInstance
local instance bandPrimitiveTensorAdd (K : ℕ) :
    AddCommGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance
local instance bandPrimitiveTensorTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance

def planeBandDivergenceCLM (N K : ℕ) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] PlaneHk Set.univ K E :=
  (hilbertBandHkOperator (E := E) N K).comp
    ((bandDivergenceOperator (E := E) N).comp (planeHkValueOperator K))

def planeBandSobolevRhs (N K : ℕ)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (H : ℝ → PlaneHk Set.univ K E) (t : ℝ) : PlaneHk Set.univ K E :=
  planeBandDivergenceCLM (E := E) N K (S t) + planeHkCutoff (E := E) N K (H t)

theorem planeBandSobolevRhs_integrable (N K : ℕ) (a b : ℝ)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (H : ℝ → PlaneHk Set.univ K E)
    (hH : Integrable H (volume.restrict (Set.Icc a b))) :
    Integrable (planeBandSobolevRhs N K S H) (volume.restrict (Set.Icc a b)) :=
  ((planeBandDivergenceCLM (E := E) N K).integrable_comp (hS.integrable (by norm_num))).add
    ((planeHkCutoff (E := E) N K).integrable_comp hH)

def planeBandSobolevPrimitive {a b : ℝ} (hab : a ≤ b) (N K : ℕ)
    (f : PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (H : ℝ → PlaneHk Set.univ K E)
    (hH : Integrable H (volume.restrict (Set.Icc a b))) :
    C(Set.Icc a b, PlaneHk Set.univ K E) :=
  ⟨fun t => planeHkCutoff N K f + ∫ s in a..t.1, planeBandSobolevRhs N K S H s, by
    change Continuous (Set.domRestrict (Set.Icc a b) (fun t : ℝ =>
      planeHkCutoff N K f + ∫ s in a..t, planeBandSobolevRhs N K S H s))
    apply continuousOn_iff_continuous_domRestrict.mp
    have hi : IntervalIntegrable (planeBandSobolevRhs N K S H) volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (planeBandSobolevRhs_integrable N K a b S hS H hH)
    have hc := continuousOn_intervalPrimitive hi
    rw [Set.uIcc_of_le hab] at hc
    exact continuousOn_const.add hc⟩
end

/-! The exact Hilbert energy chain rule for two actual Sobolev frequency primitives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance bandEnergyAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance bandEnergyTopAdd (K : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ K E) :=
  inferInstance

theorem planeBandSobolevPrimitive_energy {a b : ℝ} (hab : a ≤ b) (N M K : ℕ)
    (f : PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (H : ℝ → PlaneHk Set.univ K E)
    (hH : Integrable H (volume.restrict (Set.Icc a b)))
    (t : Set.Icc a b) :
    ‖planeBandSobolevPrimitive hab N K f S hS H hH t -
      planeBandSobolevPrimitive hab M K f S hS H hH t‖ ^ 2 -
        ‖planeHkCutoff N K f - planeHkCutoff M K f‖ ^ 2 =
      ∫ s in a..t.1, 2 * inner ℝ
        (extendCurve hab (planeBandSobolevPrimitive hab N K f S hS H hH) s -
          extendCurve hab (planeBandSobolevPrimitive hab M K f S hS H hH) s)
        (planeBandSobolevRhs N K S H s - planeBandSobolevRhs M K S H s) := by
  let y : ℝ → PlaneHk Set.univ K E := fun s =>
    (planeHkCutoff N K f + ∫ r in a..s, planeBandSobolevRhs N K S H r) -
      (planeHkCutoff M K f + ∫ r in a..s, planeBandSobolevRhs M K S H r)
  let q : ℝ → PlaneHk Set.univ K E := fun s =>
    planeBandSobolevRhs N K S H s - planeBandSobolevRhs M K S H s
  have hi (L : ℕ) : IntervalIntegrable (planeBandSobolevRhs L K S H) volume a t.1 := by
    have hs : Set.Icc a t.1 ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl t.property.2
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).mpr
      ((planeBandSobolevRhs_integrable L K a b S hS H hH).mono_measure
        (Measure.restrict_mono hs le_rfl))
  have hp : IsLinearIntegralSolution (fun _ => (0 : PlaneHk Set.univ K E →L[ℝ]
      PlaneHk Set.univ K E)) q (planeHkCutoff N K f - planeHkCutoff M K f) a t.1 y := by
    intro s hs
    have his (L : ℕ) : IntervalIntegrable (planeBandSobolevRhs L K S H) volume a s :=
      (hi L).mono_set (by
        rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le t.property.1]
        exact Set.Icc_subset_Icc le_rfl hs.2)
    simp only [linearRhs, zero_apply, zero_add]
    dsimp only [y, q]
    rw [intervalIntegral.integral_sub (his N) (his M)]
    abel
  have hrhs : IntervalIntegrable
      (linearRhs (fun _ => (0 : PlaneHk Set.univ K E →L[ℝ] PlaneHk Set.univ K E)) q y)
      volume a t.1 := by
    change IntervalIntegrable (fun s => (0 : PlaneHk Set.univ K E) + q s) volume a t.1
    simpa only [zero_add, q, Pi.sub_apply]
      using (hi N).sub (hi M)
  have he := hp.energy_identity t.property.1 hrhs
  have hy (s : ℝ) (hs : s ∈ Set.Icc a t.1) : y s =
      extendCurve hab (planeBandSobolevPrimitive hab N K f S hS H hH) s -
        extendCurve hab (planeBandSobolevPrimitive hab M K f S hS H hH) s := by
    have hs' : s ∈ Set.Icc a b := ⟨hs.1, hs.2.trans t.property.2⟩
    rw [extendCurve_eq_of_mem hab _ hs', extendCurve_eq_of_mem hab _ hs']
    rfl
  have hint : (∫ s in a..t.1, 2 * inner ℝ (y s) (q s)) =
      ∫ s in a..t.1, 2 * inner ℝ
        (extendCurve hab (planeBandSobolevPrimitive hab N K f S hS H hH) s -
          extendCurve hab (planeBandSobolevPrimitive hab M K f S hS H hH) s) (q s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    change 2 * inner ℝ (y s) (q s) = _
    rw [hy s (by simpa only [Set.uIcc_of_le t.property.1] using hs)]
  simp only [zero_apply, zero_add] at he
  rw [hint] at he
  simpa only [y, q, planeBandSobolevPrimitive, ContinuousMap.coe_mk,
    intervalIntegral.integral_same, add_zero] using he.symm
end

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The actual cutoff transport product has exactly the drift-mask expansion bounded above. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandDrift_multiplicationTerm_ae {K j : ℕ} (hj : j ≤ K)
    (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2)))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (m : PositionMask j) (w : DerivativeWord2 j) :
    multiplicationTerm hj (driftFiberCoefficient v)
      (planeGradientTensor (hilbertBandHk N (K + 1) u)).toFunction.jet m w =ᵐ[volume]
      driftMaskTerm hj v (hilbertBandHk N (K + 1) u).toFunction.jet m w := by
  let α : JetIndex2 K :=
    ⟨⟨maskRightLength j m, Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩,
      (maskWordEquiv 2 j m w).2⟩
  filter_upwards [planeGradientTensor_band_raw_ae N K u α] with x hx
  unfold multiplicationTerm driftFiberCoefficient
  rw [orderedCoefficientDerivative_linearMap (scalarRowFiberMap (E := E))
    (driftCoefficient v) (driftCoefficient_contDiff v hv), scalarRowFiberMap_apply]
  change (∑ k : Fin 2, orderedCoefficientDerivative (driftCoefficient v)
    (maskLeftLength j m) (maskWordEquiv 2 j m w).1 x (PiLp.single 2 k 1) •
    (planeGradientTensor (hilbertBandHk N (K + 1) u)).val α x k) = _
  rw [hx]
  rfl

theorem bandDrift_multiplicationRawJet_ae (N K : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2)))
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (α : JetIndex2 K) :
    multiplicationRawJet (driftFiberCoefficient v)
      (planeGradientTensor (hilbertBandHk N (K + 1) u)).toFunction.jet α =ᵐ[volume]
      fun x => ∑ m : PositionMask α.1.val,
        driftMaskTerm (Nat.le_of_lt_succ α.1.isLt) v
          (hilbertBandHk N (K + 1) u).toFunction.jet m α.2 x := by
  have hh := ae_all_iff.mpr (fun m => bandDrift_multiplicationTerm_ae
    (Nat.le_of_lt_succ α.1.isLt) N u v hv m α.2)
  filter_upwards [hh] with x hx
  unfold multiplicationRawJet
  exact Finset.sum_congr rfl (fun m _ => hx m)

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The finite seminorm of the statement supplies the actual interval Sobolev product operator
on time L². -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def intervalProductTimeCLM {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2)) :
    Lp (PlaneHk Set.univ K E) 2 (volume.restrict (Set.Icc a b)) →L[ℝ]
      Lp (PlaneHk Set.univ K F) 2 (volume.restrict (Set.Icc a b)) :=
  productPlaneHkTimeCLM (volume.restrict (Set.Icc a b))
    (fun t => A (clampPoint a b hab t))
    (hAm.comp (((continuous_clampPoint a b hab).measurable.comp measurable_fst).prodMk measurable_snd))
    (fun t => hc _ (clampPoint a b hab t).property)
    (fun l => (coefficientOrderSup a b A l.val).toReal) (fun _ => ENNReal.toReal_nonneg)
    (fun t l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) _ (clampPoint a b hab t).property x)

theorem intervalProductTimeCLM_ae {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (hc : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (hAm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (U : Lp (PlaneHk Set.univ K E) 2 (volume.restrict (Set.Icc a b))) :
    intervalProductTimeCLM hab ρ hρ K A hA hc hAm U =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => planeMultiplyIntervalCoefficient ρ hρ K a b A hA
        (clampPoint a b hab t) (clampPoint a b hab t).property
        (hc _ (clampPoint a b hab t).property) (U t) := by
  exact productPlaneHkTimeCLM_ae _ _ _ _ _ _ _ U

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Genuine source primitives with a higher Sobolev time carrier have a continuous lower representative. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance sourcePrimitiveInitialAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance sourcePrimitiveInitialTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K E) := inferInstance
local instance sourcePrimitiveInitialTensorAdd (K : ℕ) :
    AddCommGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance
local instance sourcePrimitiveInitialTensorTopAdd (K : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) := inferInstance

theorem planeBandSobolevPrimitive_initial {a b : ℝ} (hab : a ≤ b) (N K : ℕ)
    (f : PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (H : ℝ → PlaneHk Set.univ K E) (hH : Integrable H (volume.restrict (Set.Icc a b))) :
    planeBandSobolevPrimitive hab N K f S hS H hH ⟨a, le_rfl, hab⟩ =
      planeHkCutoff (E := E) N K f := by
  change planeHkCutoff (E := E) N K f + (∫ s in a..a, planeBandSobolevRhs N K S H s) = _
  rw [intervalIntegral.integral_same, add_zero]

theorem sourcePrimitive_limit_initial {a b : ℝ} (hab : a ≤ b) (K : ℕ)
    (f : PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (H : ℝ → PlaneHk Set.univ K E) (hH : Integrable H (volume.restrict (Set.Icc a b)))
    (U : C(Set.Icc a b, PlaneHk Set.univ K E))
    (hU : Tendsto (fun N => planeBandSobolevPrimitive hab N K f S hS H hH) atTop (𝓝 U)) :
    U ⟨a, le_rfl, hab⟩ = f := by
  have hp := (continuous_eval_const ⟨a, le_rfl, hab⟩).tendsto U |>.comp hU
  have he : (fun N => planeBandSobolevPrimitive hab N K f S hS H hH ⟨a, le_rfl, hab⟩) =
      fun N => planeHkCutoff (E := E) N K f := by
    funext N
    exact planeBandSobolevPrimitive_initial hab N K f S hS H hH
  change Tendsto (fun N => planeBandSobolevPrimitive hab N K f S hS H hH ⟨a, le_rfl, hab⟩) atTop (𝓝 (U ⟨a, le_rfl, hab⟩)) at hp
  rw [he] at hp
  exact tendsto_nhds_unique hp (tendsto_planeHkCutoff K f)

end AVRegularity.CoupledEnergyPlane.Variational
end
end
end
