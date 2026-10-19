-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Variational.SourcePrimitiveInitial
public import AVRegularity.Weighted.ParameterCoefficientJetMeasurable
import AVRegularity.CoupledEnergyPlane.SourceCarrierResidualRhs
import AVRegularity.CoupledEnergyPlane.PlaneWeakSolutionUniqueness
import AVRegularity.Weighted.WordPredecessorFluxIdentity
import AVRegularity.CoupledEnergy.CouplingBounds
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.Weighted.PlaneGalerkin

/-! Finite carrier sums commute with the actual factorial energy pairing. -/

variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem carrier_factorialPairing_sum {K : ℕ} (ρ : ℝ) (s : Finset J)
    (P : J → PlaneHk Set.univ K E) (Q : PlaneHk Set.univ K E) :
    factorialPairing ρ (∑ j ∈ s, P j).val Q.val =
      ∑ j ∈ s, factorialPairing ρ (P j).val Q.val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [factorialPairing]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    change factorialPairing ρ ((P a).val + (∑ j ∈ s, P j).val) Q.val = _
    rw [factorialPairing_add_left, ih]

end AVRegularity.Weighted.PlaneGalerkin
end

section
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The full metric flux equals the identity gradient plus the native metric deviation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem finiteMetricFlux_identity_split (G : Matrix (Fin 2) (Fin 2) ℝ)
    (u : PiLp 2 (fun _ : Fin 2 => E)) :
    finiteMetricFlux G u = u + finiteMetricFlux (G - 1) u := by
  apply PiLp.ext
  intro k
  change (∑ j : Fin 2, G k j • u j) = u k + ∑ j : Fin 2, (G - 1) k j • u j
  simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have hi : (∑ j : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℝ) k j • u j) = u k := by
    simp [Matrix.one_apply]
  rw [hi]
  abel

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The metric principal flux retains coercivity after pairing its true commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem metric_flux_pairing_lower
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g) (t : ℝ) (x : Vec 2)
    (du R : PiLp 2 (fun _ : Fin 2 => E)) :
    (1 / 2 : ℝ) * ‖du‖ ^ 2 - ‖R‖ ^ 2 ≤
      inner ℝ (finiteMetricFlux (G t x) du + R) du := by
  have hp : (3 / 4 : ℝ) * ‖du‖ ^ 2 ≤ inner ℝ (finiteMetricFlux (G t x) du) du := by
    have hh := nearIdentity_hilbert_quadratic_lower G g hg4 hG t x (fun k => du k)
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [PiLp.inner_apply, finiteMetricFlux, sum_inner, real_inner_smul_left]
    simpa only [real_inner_comm] using hh
  have hr := neg_abs_le (inner ℝ R du)
  have hb := abs_real_inner_le_norm R du
  rw [inner_add_left]
  nlinarith only [hp, hr, hb, sq_nonneg (‖R‖ - ‖du‖ / 2)]

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization MeasureTheory Filter
namespace AVRegularity.Weighted.PlaneGalerkin

/-! Integrate metric coercivity using the actual spatial L2 carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem metric_pairing_integral_lower (μ : Measure (Vec 2))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g) (t : ℝ)
    (du Q : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 μ)
    (R : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (hR : MemLp R 2 μ)
    (hq : Q =ᵐ[μ] fun x => finiteMetricFlux (G t x) (du x) + R x) :
    (1 / 2 : ℝ) * ‖du‖ ^ 2 - (∫ x, ‖R x‖ ^ 2 ∂μ) ≤ inner ℝ Q du := by
  have hiD : Integrable (fun x => ‖du x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) du du
  have hiR : Integrable (fun x => ‖R x‖ ^ 2) μ := hR.norm.integrable_sq
  have hh : (∫ x, (1 / 2 : ℝ) * ‖du x‖ ^ 2 - ‖R x‖ ^ 2 ∂μ) ≤
      ∫ x, inner ℝ (Q x) (du x) ∂μ := by
    apply integral_mono_ae ((hiD.const_mul _).sub hiR) (L2.integrable_inner Q du)
    filter_upwards [hq] with x hx
    rw [hx]
    exact metric_flux_pairing_lower G g hg4 hGnear t x (du x) (R x)
  rw [integral_sub (hiD.const_mul _) hiR, integral_const_mul] at hh
  have hn : ‖du‖ ^ 2 = ∫ x, ‖du x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [← hn, ← L2.inner_def] at hh
  exact hh

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance coupledSumTensorAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

def coupledCarrierSum (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (W : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) : PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ i' : ι, ∑ d : admissibleOrders K D i i',
    planeCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d) (hA i i' d) t ht (hC i i' d) (W i')

theorem coupledCarrierSum_value_ae (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (W : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) :
    planeHkValueOperator (K i) (coupledCarrierSum ρ hρ K D a b A hA t ht hC W i)
      =ᵐ[volume] fun x => ∑ i' : ι, ∑ d : admissibleOrders K D i i',
        A i i' d t x (WithLp.toLp 2 (fun word : DerivativeWord2 (d.val - 1) =>
          (W i').toFunction.jet ⟨⟨d.val - 1, by
            have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i i' d; omega⟩, word⟩ x)) := by
  unfold coupledCarrierSum
  rw [map_sum]
  apply lp_finite_sum_readout
  intro i'
  rw [map_sum]
  apply lp_finite_sum_readout
  intro d
  exact planeCoupledFluxTerm_raw_value_ae ρ hρ K D a b i i' d
    (A i i' d) (hA i i' d) t ht (hC i i' d) (W i')

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem projectedCoupling_pairing_sum (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (M : ∀ i i', admissibleOrders K D i i' → ℝ)
    (hM : ∀ i i' d, 0 ≤ M i i' d) (hb : ∀ i i' d x, ‖A i i' d t x‖ ≤ M i i' d)
    (N : ℕ) (u : ∀ i, Lp (h i) 2 (volume : Measure (Vec 2))) (i : ι) :
    (∑ i' : ι, ∑ d : admissibleOrders K D i i', factorialPairing ρ
      (hilbertBandHk N (K i) (bandDivergenceOperator (E := h i) N
        (planeCoefficientOperator (A i i' d t) (hC i i' d).continuous
          (hM i i' d) (hb i i' d) (bandTensorOperator (E := h i') N (d.val - 1) (u i'))))).val
      (hilbertBandHk N (K i) (u i)).val) =
    -factorialPairing ρ
      (coupledCarrierSum ρ hρ K D a b A hA t ht hC
        (fun i => hilbertBandHk N (K i + 1) (u i)) i).val
      (planeGradientTensor (hilbertBandHk N (K i + 1) (u i))).val := by
  have he (i' : ι) (d : admissibleOrders K D i i') :=
    projectedCoupling_factorialPairing ρ hρ K D a b i i' d (A i i' d)
      (hA i i' d) t ht (hC i i' d) (M i i' d) (hM i i' d)
      (hb i i' d) N (u i') (u i)
  simp_rw [he]
  simp only [coupledCarrierSum, carrier_factorialPairing_sum, Finset.sum_neg_distrib]

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance scalarCoupledTensorAdd (i : Fin 1 × ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i.2))) := inferInstance

def scalarCoupledCarrier (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (W : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2)) (i : Fin 1 × ι) :
    PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)) :=
  coupledCarrierSum (ι := Fin 1 × ι) (h := fun p => h p.2) ρ hρ (fun p => κ p.1 p.2) 2 a b
    (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hA t ht hC W i

theorem scalarCoupledCarrier_value_ae (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (W : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2)) (i : Fin 1 × ι) :
    planeHkValueOperator (κ i.1 i.2) (scalarCoupledCarrier ρ hρ κ a b G hA t ht hC W i)
      =ᵐ[volume] scalarChainFlux G κ W i t := by
  exact coupledCarrierSum_value_ae (ι := Fin 1 × ι) (h := fun p => h p.2)
    ρ hρ (fun p => κ p.1 p.2) 2 a b
    (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hA t ht hC W i

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance scalarMetricTensorAdd (i : Fin 1 × ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i.2))) := inferInstance

theorem scalarCoupledCarrier_metric_identity (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (W : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2)) (i : Fin 1 × ι)
    (hG : ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (M : Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ l : Fin (κ i.1 i.2 + 1), ∀ x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ M l) :
    planeMetricGradientCarrier (G t) hG M hb (W i) =
      planeGradientTensor (W i) + scalarCoupledCarrier ρ hρ κ a b G hA t ht hC W i := by
  apply PlaneHk.ext_value isOpen_univ
  apply univToPlane.injective
  change planeHkValueOperator (κ i.1 i.2) (planeMetricGradientCarrier (G t) hG M hb (W i)) =
    planeHkValueOperator (κ i.1 i.2)
      (planeGradientTensor (W i) + scalarCoupledCarrier ρ hρ κ a b G hA t ht hC W i)
  rw [map_add]
  apply Lp.ext
  have hm := planeMetricGradientCarrier_value_ae (G t) hG M hb (W i)
  simp only [Measure.restrict_univ] at hm
  have hmv := univToPlane_ae
    ((planeMetricGradientCarrier (G t) hG M hb (W i)).val (valueIndex2 (κ i.1 i.2)))
  have hgv := univToPlane_ae ((planeGradientTensor (W i)).val (valueIndex2 (κ i.1 i.2)))
  have hgrad := planeGradientTensor_raw_value_ae (W i)
  have hq := scalarCoupledCarrier_value_ae ρ hρ κ a b G hA t ht hC W i
  have hadd := Lp.coeFn_add
    (planeHkValueOperator (κ i.1 i.2) (planeGradientTensor (W i)))
    (planeHkValueOperator (κ i.1 i.2) (scalarCoupledCarrier ρ hρ κ a b G hA t ht hC W i))
  filter_upwards [hm, hmv, hgv, hgrad, hq, hadd] with x hm hmv hgv hg hq ha
  change univToPlane ((planeMetricGradientCarrier (G t) hG M hb (W i)).val
    (valueIndex2 (κ i.1 i.2))) x = _
  rw [hmv, hm, ← hgv, ha]
  change finiteMetricFlux (G t x)
    (planeHkValueOperator (κ i.1 i.2) (planeGradientTensor (W i)) x) =
      planeHkValueOperator (κ i.1 i.2) (planeGradientTensor (W i)) x +
        planeHkValueOperator (κ i.1 i.2) (scalarCoupledCarrier ρ hρ κ a b G hA t ht hC W i) x
  rw [hg, hq]
  apply PiLp.ext
  intro k
  have hsplit := finiteMetricFlux_identity_split (G t x)
    (WithLp.toLp 2 (fun j : Fin 2 => (W i).toFunction.jet ⟨⟨1, by omega⟩, fun _ => j⟩ x))
  have hsplitk := congrArg (fun z : PiLp 2 (fun _ : Fin 2 => h i.2) => z k) hsplit
  simp only [WithLp.ofLp_add, Pi.add_apply] at hsplitk ⊢
  rw [scalarChainFlux_eq G κ W i t x k]
  exact hsplitk

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarCoupledCarrier_pairing_identity (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (W : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2)) (i : Fin 1 × ι)
    (hG : ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (M : Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ l : Fin (κ i.1 i.2 + 1), ∀ x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ M l) :
    -gradFactorialNormSq ρ (W i).val -
      factorialPairing ρ (scalarCoupledCarrier ρ hρ κ a b G hA t ht hC W i).val
        (planeGradientTensor (W i)).val =
    -factorialPairing ρ (planeMetricGradientCarrier (G t) hG M hb (W i)).val
      (planeGradientTensor (W i)).val := by
  rw [scalarCoupledCarrier_metric_identity ρ hρ κ a b G hA t ht hC W i hG M hb]
  change _ = -factorialPairing ρ
    ((planeGradientTensor (W i)).val + (scalarCoupledCarrier ρ hρ κ a b G hA t ht hC W i).val)
      (planeGradientTensor (W i)).val
  rw [factorialPairing_add_left, factorialPairing_self, planeGradientTensor_factorialNormSq]
  ring
end

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarSourceProjectedOperator_row_energy (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (N : ℕ) (u : ProjectedFamily (fun p : Fin 1 × ι => h p.2))
    (t : Set.Icc a b) (i : Fin 1 × ι)
    (hG : ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (M : Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ l : Fin (κ i.1 i.2 + 1), ∀ x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ M l) :
    let C := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv
      (fun p : Fin 1 × ι => κ p.1 p.2) 2
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hC hA
    factorialPairing ρ
      (hilbertBandHk N (κ i.1 i.2) (projectedOperator C N 1 t u i)).val
      (hilbertBandHk N (κ i.1 i.2) (u i)).val =
    -factorialPairing ρ
      (hilbertBandHk N (κ i.1 i.2) (hilbertProjection N
        (planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
          (C.drift_bound_nonneg i) (C.drift_le i t)
          (bandGradientOperator (E := h i.2) N (u i))))).val
      (hilbertBandHk N (κ i.1 i.2) (u i)).val -
    factorialPairing ρ
      (planeMetricGradientCarrier (G t) hG M hb
        (hilbertBandHk N (κ i.1 i.2 + 1) (u i))).val
      (planeGradientTensor (hilbertBandHk N (κ i.1 i.2 + 1) (u i))).val := by
  dsimp only
  rw [projectedOperator_row_energy
    (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv
      (fun p : Fin 1 × ι => κ p.1 p.2) 2
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hC hA) N 1 ρ t u i,
    one_mul]
  have he := projectedCoupling_pairing_sum (ι := Fin 1 × ι) (h := fun p => h p.2)
    ρ hρ (fun p => κ p.1 p.2) 2 a b
    (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hA t t.property
    (fun i i' d => hC i i' d t t.property)
    (fun i i' d => (coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d)).toReal)
    (fun _ _ _ => ENNReal.toReal_nonneg)
    (fun i i' d x => sourceCoefficient_norm_le ρ hρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d)
      (hA i i' d) t t.property x) N (fun i => u i) i
  change _ - _ + _ = _
  dsimp only [sourceProjectedCoefficients]
  rw [he]
  have hm := scalarCoupledCarrier_pairing_identity ρ hρ κ a b G hA t t.property
    (fun i i' d => hC i i' d t t.property)
    (fun i => hilbertBandHk N (κ i.1 i.2 + 1) (u i)) i hG M hb
  dsimp only [scalarCoupledCarrier] at hm
  linarith only [hm]
end

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The genuine metric Sobolev carrier satisfies the wordwise coercive pairing estimate. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem metric_word_pairing_lower {K : ℕ}
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g) (t : ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G t x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ l : Fin (K + 1), ∀ x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ M l)
    (W : PlaneHk Set.univ (K + 1) E) (j : Fin (K + 1)) (w : DerivativeWord2 j.val) :
    (1 / 2 : ℝ) * ‖(planeGradientTensor W).val ⟨j, w⟩‖ ^ 2 -
      (∫ x, ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) (G t) W.toFunction.jet w x‖ ^ 2
        ∂volume.restrict Set.univ) ≤
      inner ℝ ((planeMetricGradientCarrier (G t) hG M hb W).val ⟨j, w⟩)
        ((planeGradientTensor W).val ⟨j, w⟩) := by
  let du := (planeGradientTensor W).val ⟨j, w⟩
  let Q := (planeMetricGradientCarrier (G t) hG M hb W).val ⟨j, w⟩
  let R := metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) (G t) W.toFunction.jet w
  have hr := metricRawCommutator_memLp (G t) hG M hb W.toFunction.jet W.toFunction.memL2 ⟨j, w⟩
  have hD : ∀ᵐ x ∂volume.restrict Set.univ, du x =
      WithLp.toLp 2 (fun k : Fin 2 => W.toFunction.jet
        ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) :=
    planeGradientTensor_jet_ae W j w
  have hQ := planeMetricGradientCarrier_principal_commutator_ae (G t) hG M hb W j w
  apply metric_pairing_integral_lower (volume.restrict Set.univ) G g hg4 hGnear t du Q R hr
  filter_upwards [hD, hQ] with x hd hq
  exact hq.trans (by rw [hd])

end AVRegularity.Weighted.PlaneGalerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The uniform Galerkin energy bound controls the genuine lower weak Sobolev carrier almost everywhere. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weightedLimitPackAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weightedLimitPackTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem exists_planeWeakSolution_of_nativeGalerkinLimit {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hrange : ∀ N t, familyProjection N (u N t) = u N t)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C : ℝ)
    (hmass : ∀ N t, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤ C)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    :
    ∃ (U : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane ν a b v D K A f F g U w := by
  classical
  have hrep (i : ι) := exists_sourceContinuousSobolevRepresentative hab ρ hρ v hv V hV hbv
    K D A hAc hAf hvm hAm ν f F hF g hg u heq φ hφ W R hu hw
    hrange π hπ C hmass hW Kmax hK strain B lam hstrain hB hlam hjets i
  choose U _hconv hinit hUa using hrep
  refine ⟨fun i => extendCurve hab (U i), weakHighCarrier K a b W, ?_⟩
  apply AVRegularity.CoupledEnergyPlane.sourceNativeEquation_pack_weakSolution hab ρ hρ
    v hv V hV hbv K D A hAc hAf hvm hAm Kmax hK strain B lam hstrain
    hB hlam hjets W hW ν F hF g hg f U hinit hUa
  dsimp only
  intro i t ψ
  exact AVRegularity.CoupledEnergyPlane.sourceContinuousCarrier_native_equation hab ρ hρ v hv V hV hbv
    K D A hAc hAf hvm hAm ν f F hF g hg u heq φ hφ W R hu hw
    hrange π hπ C hmass hW i (U i) (hinit i) (hUa i) t ψ

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! Full factorial coercivity of the true metric-gradient carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem metric_factorial_pairing_lower {K : ℕ}
    (ρ δ g : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g) (t : ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ)
    (hbfull : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (W : PlaneHk Set.univ (K + 1) E) :
    (1 / 2 - (metricRadiusConstant K CG * g * (ρ * δ)) ^ 2) * gradFactorialNormSq ρ W.val ≤
      factorialPairing ρ
        (planeMetricGradientCarrier (G t) hG (fun l => metricEntryEnvelope CG g δ l.val) hbfull W).val
        (planeGradientTensor W).val := by
  let source := ∑ j : Fin (K + 1), factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 j.val, ∫ x,
      ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) (G t) W.toFunction.jet w x‖ ^ 2
        ∂volume.restrict Set.univ
  have hword : (1 / 2 : ℝ) * factorialNormSq ρ (planeGradientTensor W).val - source ≤
      factorialPairing ρ
        (planeMetricGradientCarrier (G t) hG (fun l => metricEntryEnvelope CG g δ l.val) hbfull W).val
        (planeGradientTensor W).val := by
    have hh : (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        ∑ w : DerivativeWord2 j.val,
          ((1 / 2 : ℝ) * ‖(planeGradientTensor W).val ⟨j, w⟩‖ ^ 2 -
            ∫ x, ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) (G t) W.toFunction.jet w x‖ ^ 2
              ∂volume.restrict Set.univ)) ≤ factorialPairing ρ
          (planeMetricGradientCarrier (G t) hG (fun l => metricEntryEnvelope CG g δ l.val) hbfull W).val
          (planeGradientTensor W).val := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg _ _)
      apply Finset.sum_le_sum
      intro w _
      exact metric_word_pairing_lower G g hg4 hGnear t hG _ hbfull W j w
    have he : (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        ∑ w : DerivativeWord2 j.val,
          ((1 / 2 : ℝ) * ‖(planeGradientTensor W).val ⟨j, w⟩‖ ^ 2 -
            ∫ x, ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) (G t) W.toFunction.jet w x‖ ^ 2
              ∂volume.restrict Set.univ)) =
        (1 / 2 : ℝ) * factorialNormSq ρ (planeGradientTensor W).val - source := by
      dsimp only [source]
      simp only [Finset.sum_sub_distrib, mul_sub]
      congr 1
      unfold factorialNormSq derivativeNormSq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]
      ring
    exact he ▸ hh
  have hs := weightedMetricFluxSource_energy_le (U := Set.univ) ρ δ g hρ hδ hg hscale
    (G t) hG CG hbfull hb (fun _ => 1) continuous_const (fun _ => by norm_num)
    1 (fun _ => le_rfl) W.toFunction.jet W.toFunction.memL2
  simp only [one_mul, Measure.restrict_univ] at hs
  have hprod := rawWeightedGradient_integral_sum ρ (fun _ => 1) aestronglyMeasurable_const
    (M := 1) (Filter.Eventually.of_forall (fun _ => by norm_num)) W.toFunction.jet W.toFunction.memL2
  simp only [one_mul] at hprod
  rw [hprod, rawWeightedGradientEnergy_one] at hs
  rw [planeGradientTensor_factorialNormSq] at hword
  have hs' : source ≤ (metricRadiusConstant K CG * g * (ρ * δ)) ^ 2 * gradFactorialNormSq ρ W.val := by
    simpa only [source, Measure.restrict_univ] using hs
  nlinarith only [hword, hs']

end AVRegularity.Weighted.PlaneGalerkin
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarSourceProjectedOperator_row_energy_le (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (N : ℕ) (u : ProjectedFamily (fun p : Fin 1 × ι => h p.2))
    (t : Set.Icc a b) (i : Fin 1 × ι)
    (hG : ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hg4 : g ≤ 1 / 4) (hnear : IsMetricNearIdentity G g) (hscale : ρ * δ ≤ 1)
    (hbfull : ∀ (l : Fin (κ i.1 i.2 + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ l, 1 ≤ l → l ≤ κ i.1 i.2 → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (hprice : (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16)
    (Kmax : ℕ) (hK : κ i.1 i.2 ≤ Kmax)
    (strain B lam : ℝ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    let C := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv
      (fun p : Fin 1 × ι => κ p.1 p.2) 2
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hC hA
    factorialPairing ρ
      (hilbertBandHk N (κ i.1 i.2) (projectedOperator C N 1 t u i)).val
      (hilbertBandHk N (κ i.1 i.2) (u i)).val ≤
      -(3 / 16) * gradFactorialNormSq ρ (hilbertBandHk N (κ i.1 i.2 + 1) (u i)).val := by
  dsimp only
  rw [scalarSourceProjectedOperator_row_energy ρ hρ κ a b G hA hC v hv V hV hbv N u t i
    hG (fun l => metricEntryEnvelope CG g δ l.val) hbfull]
  have hd := projectedDrift_factorialPairing_abs_le hK N (u i)
    ρ strain B lam 1 hρ hstrain0 hB hlam (by norm_num) hsmall
    (by simpa using hstrain) (v t) (hv t t.property) V hV (hbv t t.property) hdiv hjets
  have hm := metric_factorial_pairing_lower ρ δ g hρ.le hδ hg hscale G hg4 hnear t hG CG
    hbfull hb (hilbertBandHk N (κ i.1 i.2 + 1) (u i))
  have hn : 0 ≤ gradFactorialNormSq ρ (hilbertBandHk N (κ i.1 i.2 + 1) (u i)).val :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (factorialWeight_nonneg ρ j.val)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hp := mul_le_mul_of_nonneg_right hprice hn
  dsimp only [sourceProjectedCoefficients] at ⊢
  have hneg := neg_le_abs (factorialPairing ρ
      (hilbertBandHk N (κ i.1 i.2) (hilbertProjection N
        (planeCoefficientOperator (driftFiberCoefficient (E := h i.2) (v t))
          (driftFiberCoefficient_contDiff (E := h i.2) (v t) (hv t t.property)).continuous
          (mul_nonneg (by norm_num) hV)
          (fun x => (driftFiberCoefficient_norm_le (E := h i.2) (v t) x).trans
            (mul_le_mul_of_nonneg_left (hbv t t.property x) (by norm_num)))
          (bandGradientOperator (E := h i.2) N (u i))))).val
      (hilbertBandHk N (κ i.1 i.2) (u i)).val)
  nlinarith only [hd, hm, hp, hneg]
end

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarSourceProjectedOperator_massEnergy_le (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (N : ℕ) (u : ProjectedFamily (fun p : Fin 1 × ι => h p.2))
    (t : Set.Icc a b)
    (hG : ∀ i : Fin 1 × ι, ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hg4 : g ≤ 1 / 4) (hnear : IsMetricNearIdentity G g) (hscale : ρ * δ ≤ 1)
    (hbfull : ∀ i : Fin 1 × ι, ∀ (l : Fin (κ i.1 i.2 + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ i : Fin 1 × ι, ∀ l, 1 ≤ l → l ≤ κ i.1 i.2 → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (hprice : ∀ i : Fin 1 × ι, (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16)
    (Kmax : ℕ) (hK : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (strain B lam : ℝ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (π : Fin 1 × ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) :
    let C := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv
      (fun p : Fin 1 × ι => κ p.1 p.2) 2
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hC hA
    (∑ i, (π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N (κ i.1 i.2) (projectedOperator C N 1 t u i)).val
      (hilbertBandHk N (κ i.1 i.2) (u i)).val) ≤
      -(3 / 16) * massGradNormSq ρ π
        (fun i => (hilbertBandHk N (κ i.1 i.2 + 1) (u i)).val) := by
  dsimp only
  unfold massGradNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he := scalarSourceProjectedOperator_row_energy_le ρ hρ κ a b G hA hC v hv V hV hbv
    N u t i (hG i) CG g δ hg hδ hg4 hnear hscale (hbfull i) (hb i) (hprice i)
    Kmax (hK i) strain B lam hstrain0 hB hlam hsmall hstrain hdiv hjets
  convert mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (hπ i).le) using 1
  ring
end

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarSourceProjectedRhs_massEnergy_le (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (N : ℕ) (u : ProjectedFamily (fun p : Fin 1 × ι => h p.2))
    (t : Set.Icc a b)
    (hG : ∀ i : Fin 1 × ι, ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hg4 : g ≤ 1 / 4) (hnear : IsMetricNearIdentity G g) (hscale : ρ * δ ≤ 1)
    (hbfull : ∀ i : Fin 1 × ι, ∀ (l : Fin (κ i.1 i.2 + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ i : Fin 1 × ι, ∀ l, 1 ≤ l → l ≤ κ i.1 i.2 → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (hprice : ∀ i : Fin 1 × ι, (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16)
    (Kmax : ℕ) (hK : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (strain B lam : ℝ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (π : Fin 1 × ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (F : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (q : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2)) :
    let C := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv
      (fun p : Fin 1 × ι => κ p.1 p.2) 2
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hC hA
    (∑ i, (π i)⁻¹ * factorialPairing ρ
      (hilbertBandHk N (κ i.1 i.2)
        ((projectedOperator C N 1 t u +
          projectedSource N (fun i _ => F i) (fun i _ => q i) t) i)).val
      (hilbertBandHk N (κ i.1 i.2) (u i)).val) ≤
      -(1 / 8) * massGradNormSq ρ π
        (fun i => (hilbertBandHk N (κ i.1 i.2 + 1) (u i)).val) +
      Real.sqrt (massNormSq ρ π (fun i => (q i).val)) *
        Real.sqrt (massNormSq ρ π (fun i => (hilbertBandHk N (κ i.1 i.2) (u i)).val)) +
      8 * massNormSq ρ π (fun i => (F i).val) := by
  dsimp only
  have ho := scalarSourceProjectedOperator_massEnergy_le ρ hρ κ a b G hA hC v hv V hV hbv
    N u t hG CG g δ hg hδ hg4 hnear hscale hbfull hb hprice Kmax hK
    strain B lam hstrain0 hB hlam hsmall hstrain π hπ hdiv hjets
  have hf := projectedFlux_massPairing_young_le N (fun p : Fin 1 × ι => κ p.1 p.2)
    ρ (1 / 4) (by norm_num) π hπ F (fun i => u i)
  have hq := projectedSource_massPairing_abs_le N (fun p : Fin 1 × ι => κ p.1 p.2)
    ρ π hπ q (fun i => u i)
  have hn := massGradNormSq_nonneg ρ π hπ
    (fun i => (hilbertBandHk N (κ i.1 i.2 + 1) (u i)).val)
  simp only [WithLp.ofLp_add, Pi.add_apply, projectedSource,
    bandPairing_add, mul_add, Finset.sum_add_distrib]
  have hf' := le_abs_self (∑ i, (π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N (κ i.1 i.2) (bandDivergenceOperator (E := h i.2) N
      (planeHkValueOperator (κ i.1 i.2) (F i)))).val
    (hilbertBandHk N (κ i.1 i.2) (u i)).val)
  have hq' := le_abs_self (∑ i, (π i)⁻¹ * factorialPairing ρ
    (hilbertBandHk N (κ i.1 i.2) (hilbertProjection N
      (planeHkValueOperator (κ i.1 i.2) (q i)))).val
    (hilbertBandHk N (κ i.1 i.2) (u i)).val)
  dsimp only at ho
  linarith only [ho, hf, hq, hf', hq', hn]
end

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarSourceProjectedEnergy_deriv_le_of_hasDerivAt (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (N : ℕ) (u : ℝ → ProjectedFamily (fun p : Fin 1 × ι => h p.2))
    (t : Set.Icc a b)
    (hG : ∀ i : Fin 1 × ι, ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hg4 : g ≤ 1 / 4) (hnear : IsMetricNearIdentity G g) (hscale : ρ * δ ≤ 1)
    (hbfull : ∀ i : Fin 1 × ι, ∀ (l : Fin (κ i.1 i.2 + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ i : Fin 1 × ι, ∀ l, 1 ≤ l → l ≤ κ i.1 i.2 → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (hprice : ∀ i : Fin 1 × ι, (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16)
    (Kmax : ℕ) (hK : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (strain B lam : ℝ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (π : Fin 1 × ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (F : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (q : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hu : HasDerivAt u
      (projectedOperator
        (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv
          (fun p : Fin 1 × ι => κ p.1 p.2) 2
          (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hC hA)
        N 1 t (u t) + projectedSource N (fun i _ => F i) (fun i _ => q i) t) t) :
    deriv (fun s => massNormSq ρ π
      (fun i => (hilbertBandHk N (κ i.1 i.2) (u s i)).val)) t +
      (1 / 4) * massGradNormSq ρ π
        (fun i => (hilbertBandHk N (κ i.1 i.2 + 1) (u t i)).val) ≤
      2 * Real.sqrt (massNormSq ρ π (fun i => (q i).val)) *
        Real.sqrt (massNormSq ρ π (fun i => (hilbertBandHk N (κ i.1 i.2) (u t i)).val)) +
      16 * massNormSq ρ π (fun i => (F i).val) := by
  rw [(hasDerivAt_massBandEnergy N (fun p : Fin 1 × ι => κ p.1 p.2) ρ π hπ hu).deriv]
  have he := scalarSourceProjectedRhs_massEnergy_le ρ hρ κ a b G hA hC v hv V hV hbv
    N (u t) t hG CG g δ hg hδ hg4 hnear hscale hbfull hb hprice Kmax hK
    strain B lam hstrain0 hB hlam hsmall hstrain π hπ hdiv hjets F q
  linear_combination 2 * he
end

end AVRegularity.Weighted.PlaneGalerkin
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted.PlaneGalerkin

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarSourceProjectedEnergy_uniform_of_timeRegularity (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (N : ℕ) (u : C(Set.Icc a b, ProjectedFamily (fun p : Fin 1 × ι => h p.2)))
    (hG : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hg4 : g ≤ 1 / 4) (hnear : IsMetricNearIdentity G g) (hscale : ρ * δ ≤ 1)
    (hbfull : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ (l : Fin (κ i.1 i.2 + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ l, 1 ≤ l → l ≤ κ i.1 i.2 → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (hprice : ∀ i : Fin 1 × ι, (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16)
    (Kmax : ℕ) (hK : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (strain B lam : ℝ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (π : Fin 1 × ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (q : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hq : ∀ i, Integrable (q i) (volume.restrict (Set.Icc a b)))
    (hac : AbsolutelyContinuousOnInterval (extendCurve hab u) a b)
    (hd : ∀ᵐ t ∂volume, t ∈ Set.Icc a b → HasDerivAt (extendCurve hab u)
      (projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv
          (fun p : Fin 1 × ι => κ p.1 p.2) 2
          (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hC hA).reindex
            (clampPoint a b hab)) N 1 t (extendCurve hab u t) + projectedSource N F q t) t) :
    ∃ S : ℝ, 0 ≤ S ∧
      (∀ t : Set.Icc a b, massNormSq ρ π
        (fun i => (hilbertBandHk N (κ i.1 i.2) (u t i)).val) ≤ S ^ 2) ∧
      S ^ 2 + (1 / 8) * (∫ s in a..b, massGradNormSq ρ π
        (fun i => (hilbertBandHk N (κ i.1 i.2 + 1) (extendCurve hab u s i)).val)) ≤
      2 * massNormSq ρ π (fun i => (hilbertBandHk N (κ i.1 i.2) (u ⟨a, le_rfl, hab⟩ i)).val) +
        32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
          10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2 := by
  let K := fun p : Fin 1 × ι => κ p.1 p.2
  let D := 2
  let A := planeChainCoefficient (geometryScalarData (h := h) 2 G) κ
  let E := fun s => massNormSq ρ π
    (fun i => (hilbertBandHk N (K i) (extendCurve hab u s i)).val)
  let R := fun s => massGradNormSq ρ π
    (fun i => (hilbertBandHk N (K i + 1) (extendCurve hab u s i)).val)
  let Q := fun s => Real.sqrt (massNormSq ρ π (fun i => (q i s).val))
  let Fsq := fun s => massNormSq ρ π (fun i => (F i s).val)
  have hE : AbsolutelyContinuousOnInterval E a b :=
    massBandEnergy_absolutelyContinuous N K ρ π hπ hac
  have hR : IntervalIntegrable R volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (((continuous_massBandGradient N K ρ π).comp (continuous_extendCurve hab u)).integrableOn_Icc)
  have hQ : IntervalIntegrable Q volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (planeMassNorm_integrable ρ π hπ K q hq)
  have hFsq : IntervalIntegrable Fsq volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (planeMassNormSq_integrable ρ π hπ K F hF)
  have hi : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv E t + (1 / 4) * R t ≤ 2 * Q t * Real.sqrt (E t) + 16 * Fsq t := by
    have hd' := hd.filter_mono (ae_mono (Measure.restrict_le_self (s := Set.Icc a b)))
    filter_upwards [hd', ae_restrict_mem measurableSet_Icc] with t ht htm
    have hcl : clampPoint a b hab t = ⟨t, htm⟩ := by
      apply Subtype.ext
      simp only [clampPoint, max_eq_right htm.1, min_eq_right htm.2]
    have hp : projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA).reindex
          (clampPoint a b hab)) N 1 t =
      projectedOperator (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hC hA)
        N 1 ⟨t, htm⟩ := by
      apply ContinuousLinearMap.ext
      intro z
      apply PiLp.ext
      intro i
      simp only [projectedOperator_component, ProjectedCoefficients.reindex, hcl]
    have hdt := ht htm
    rw [hp] at hdt
    exact scalarSourceProjectedEnergy_deriv_le_of_hasDerivAt ρ hρ κ a b G hA hC v hv V hV hbv
      N (extendCurve hab u) ⟨t, htm⟩ (hG t htm) CG g δ hg hδ hg4 hnear hscale
      (hbfull t htm) (hb t htm) hprice Kmax hK strain B lam hstrain0 hB hlam
      hsmall hstrain π hπ (hdiv t htm) (hjets t htm) (fun i => F i t) (fun i => q i t) hdt

  obtain ⟨S, hS, hbnd, he⟩ := coupledTimeEnergy_uniform_of_deriv_le hab (show (0 : ℝ) < 1 / 4 by norm_num) hE
    (fun _ _ => massNormSq_nonneg ρ π hπ _)
    (fun _ _ => massGradNormSq_nonneg ρ π hπ _)
    (fun _ _ => Real.sqrt_nonneg _)
    (fun _ _ => massNormSq_nonneg ρ π hπ _) hR hQ hFsq (by simpa only [show (4 : ℝ) / (1 / 4) = 16 by norm_num] using hi)
  refine ⟨S, hS, ?_, ?_⟩
  · intro t
    simpa only [E, extendCurve_eq_of_mem hab u t.property] using hbnd t t.property
  · simpa only [E, R, Q, Fsq, K,
      show (1 : ℝ) / 4 / 2 = 1 / 8 by norm_num,
      show (8 : ℝ) / (1 / 4) = 32 by norm_num, extendCurve_eq_of_mem hab u
      (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)] using he
end

/-! The sum of the committed native scalar coupling carriers has the literal metric deviation flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_scalarSourceProjectedEvolution_with_uniformEnergy (ρ : ℝ) (hρ : 0 < ρ) (κ : Fin 1 → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (κ i.1 i.2) a b
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t))
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (N : ℕ)
    (hG : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ k a, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k a))
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ)
    (hg4 : g ≤ 1 / 4) (hnear : IsMetricNearIdentity G g) (hscale : ρ * δ ≤ 1)
    (hbfull : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ (l : Fin (κ i.1 i.2 + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ t ∈ Set.Icc a b, ∀ i : Fin 1 × ι, ∀ l, 1 ≤ l → l ≤ κ i.1 i.2 → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G t y k a) x‖ ≤ CG l * g * δ ^ l)
    (hprice : ∀ i : Fin 1 × ι, (metricRadiusConstant (κ i.1 i.2) CG * g * (ρ * δ)) ^ 2 ≤ 1 / 16)
    (Kmax : ℕ) (hK : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (strain B lam : ℝ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ 1 / 8)
    (π : Fin 1 × ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (q : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hq : ∀ i, Integrable (q i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 =>
      planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i j d p.1 p.2)) :
    ∃ u : C(Set.Icc a b, ProjectedFamily (fun p : Fin 1 × ι => h p.2)),
      (∀ t : Set.Icc a b, u t = projectedInitial N f + ∫ s in a..t.1,
        projectedOperator
          ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv (fun p : Fin 1 × ι => κ p.1 p.2) 2
            (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) hC hA).reindex
            (clampPoint a b hab)) N 1 s (extendCurve hab u s) + projectedSource N F q s) ∧
      (∀ t : Set.Icc a b, familyProjection N (u t) = u t) ∧
      ∃ S : ℝ, 0 ≤ S ∧
        (∀ t : Set.Icc a b, massNormSq ρ π
          (fun i => (hilbertBandHk N (κ i.1 i.2) (u t i)).val) ≤ S ^ 2) ∧
        S ^ 2 + (1 / 8) * (∫ s in a..b, massGradNormSq ρ π
          (fun i => (hilbertBandHk N (κ i.1 i.2 + 1) (extendCurve hab u s i)).val)) ≤
        2 * massNormSq ρ π (fun i => (f i).val) +
          32 * (∫ s in a..b, massNormSq ρ π (fun i => (F i s).val)) +
            10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (q i s).val))) ^ 2 := by
  let K := fun p : Fin 1 × ι => κ p.1 p.2
  let A := planeChainCoefficient (geometryScalarData (h := h) 2 G) κ
  let C := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K 2 A hC hA
  have hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K 2 A hC hA hAm
  obtain ⟨u, heq, hrange, hac, hd⟩ :=
    exists_projectedPlaneEvolution_with_timeRegularity hab C hc N 1 f F hF q hq
  obtain ⟨S, hS, hbound, henergy⟩ := scalarSourceProjectedEnergy_uniform_of_timeRegularity
    ρ hρ κ a b hab G hA hC v hv V hV hbv N u hG CG g δ hg hδ hg4 hnear hscale
    hbfull hb hprice Kmax hK strain B lam hstrain0 hB hlam hsmall hstrain π hπ
    hdiv hjets F q hF hq hac hd
  refine ⟨u, heq, hrange, S, hS, hbound, ?_⟩
  have hi : u ⟨a, le_rfl, hab⟩ = projectedInitial N f := by
    simpa only [intervalIntegral.integral_same, add_zero] using heq ⟨a, le_rfl, hab⟩
  rw [hi] at henergy
  have hb := projectedInitial_massNormSq_le N K ρ π hπ f
  linarith
end

end AVRegularity.Weighted.PlaneGalerkin
end
end
