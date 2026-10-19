-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.WeightedGradientLiftComparison
public import AVRegularity.CycleJoint.ScalarPlaneChainNativeResidualOrderAssembly
public import AVRegularity.CycleWords.WeightedSmoothPullbackSequence
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVRegularity.CycleWords.CellComplexH1Separability
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The polynomial moment is uniformly bounded on the actual mesh patch. -/

def spatialPatchCenter (N : ℕ) (k : Fin 2 → ℤ) : Vec 2 := fun i => (k i : ℝ) / (N : ℝ)

theorem spatialPatch_scaled_coordinate_bound {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (k : Fin 2 → ℤ) (x : Vec 2)
    (hx : x ∈ tsupport (spatialPatchCutoff ζ N k)) (ϖ R : ℝ)
    (hϖ : 0 ≤ ϖ) (hR : 0 ≤ R) (hscale : ϖ / (N : ℝ) ≤ R) (i : Fin 2) :
    |ϖ * (x i - spatialPatchCenter N k i)| ≤ R := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he : ϖ * (x i - spatialPatchCenter N k i) =
      (ϖ / (N : ℝ)) * ((N : ℝ) * x i - (k i : ℝ)) := by
    unfold spatialPatchCenter
    field_simp
  rw [he, abs_mul, abs_of_nonneg (div_nonneg hϖ hNp.le)]
  have hc : |(N : ℝ) * x i - (k i : ℝ)| ≤ 1 :=
    (spatialPatchCutoff_tsupport_coordinate hζ N k x hx i).trans (by norm_num)
  exact (mul_le_mul hscale hc (abs_nonneg _) hR).trans_eq (mul_one R)

theorem spatialPatch_polynomial_moment_bound {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (k : Fin 2 → ℤ) (x : Vec 2)
    (hx : x ∈ tsupport (spatialPatchCutoff ζ N k)) (n : ℕ) (ϖ R : ℝ)
    (hϖ : 0 ≤ ϖ) (hR : 0 ≤ R) (hscale : ϖ / (N : ℝ) ≤ R) :
    planeMomentPolynomial n ϖ (spatialPatchCenter N k) x ≤ (1 + 2 * R ^ 2) ^ n :=
  planeMomentPolynomial_le_coordinate_bound n ϖ R hR _ x
    (spatialPatch_scaled_coordinate_bound hζ N hN k x hx ϖ R hϖ hR hscale)

end AVRegularity.CycleJointProofs
end
end

section
public section
open Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Polynomial moments on a pulled-back patch centered at the inverse image of
its physical center. The price is uniform in the patch location. -/

theorem spatialPatch_pullback_polynomial_moment_bound
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (k : Fin 2 → ℤ) (X : Vec 2 ≃ₜ Vec 2) (L : NNReal)
    (hL : LipschitzWith L X.symm) (x : Vec 2)
    (hx : X x ∈ tsupport (spatialPatchCutoff ζ N k))
    (n : ℕ) (ϖ R : ℝ) (hϖ : 0 ≤ ϖ) (hR : 0 ≤ R)
    (hscale : ϖ / (N : ℝ) ≤ R) :
    planeMomentPolynomial n ϖ (X.symm (spatialPatchCenter N k)) x ≤
      (1 + 2 * ((L : ℝ) * R) ^ 2) ^ n := by
  have hp : ‖ϖ • (X x - spatialPatchCenter N k)‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    change ‖ϖ * (X x i - spatialPatchCenter N k i)‖ ≤ R
    rw [Real.norm_eq_abs]
    exact spatialPatch_scaled_coordinate_bound hζ N hN k (X x) hx ϖ R hϖ hR hscale i
  have hl := hL.norm_sub_le (X x) (spatialPatchCenter N k)
  rw [X.symm_apply_apply] at hl
  have hb : ‖ϖ • (x - X.symm (spatialPatchCenter N k))‖ ≤ (L : ℝ) * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hϖ]
    calc
      _ ≤ ϖ * ((L : ℝ) * ‖X x - spatialPatchCenter N k‖) :=
        mul_le_mul_of_nonneg_left hl hϖ
      _ = (L : ℝ) * ‖ϖ • (X x - spatialPatchCenter N k)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hϖ, mul_left_comm]
      _ ≤ (L : ℝ) * R := mul_le_mul_of_nonneg_left hp L.coe_nonneg
  apply planeMomentPolynomial_le_coordinate_bound n ϖ ((L : ℝ) * R)
    (mul_nonneg L.coe_nonneg hR) _ x
  intro i
  have hi := norm_le_pi_norm (ϖ • (x - X.symm (spatialPatchCenter N k))) i
  change ‖ϖ * (x i - X.symm (spatialPatchCenter N k) i)‖ ≤ _ at hi
  rw [Real.norm_eq_abs] at hi
  exact hi.trans hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Treat the actual homogeneous coupling row as external forcing in an identity scalar chain. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The genuine coupling row gives the exact external flux required by the weighted scalar theorem. -/
theorem planeHomogeneous_scalar_chain_solution {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w) :
    IsCoupledWeakSolutionPlane 1 a b v 2 (fun p : Fin 1 × ι => K p.2)
      (planeChainCoefficient
        (geometryScalarData (h := h) 2 (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)))
        (fun _ i => K i))
      (fun p => f p.2)
      (fun p => planeCouplingFluxRow hab ρ hρ K D A hA hc w p.2)
      (fun _ _ => 0) (fun p => u p.2) (fun p => w p.2) := by
  refine ⟨(fun p => hs.1 p.2), (fun p => hs.2.1 p.2),
    (fun p => hs.2.2.1 p.2), (fun p => hs.2.2.2.1 p.2), ?_⟩
  intro p t ht φ
  have hold := hs.2.2.2.2 p.2 t ht φ
  simp only [Measure.restrict_univ] at hold ⊢
  simp only [planeChainCoefficient_identity, zero_apply,
    Finset.sum_const_zero]
  apply coupledWeakIdentity_flux_reallocation volume 1 a t v _ _ _ _ _ _ 0 _ _ _ _ hold
  intro r hr
  have hrab : r ∈ Set.Icc a b := ⟨hr.1.le, hr.2.trans ht.2⟩
  let Q := planeCouplingFluxRow hab ρ hρ K D A hA hc w p.2 r
  have hread : Q.toFunction.jet (valueIndex2 (K p.2)) =ᵐ[volume]
      planeRawCouplingFlux K D r A (fun i => w i r) p.2 := by
    have hq := (univToPlane_ae (Q.val (valueIndex2 (K p.2)))).symm
    apply hq.trans
    exact planeCouplingFluxRow_raw_value_ae hab ρ hρ K D A hA hc w p.2 r hrab
  filter_upwards [hread, planeZero_rawJet_ae
    (E := PiLp 2 (fun _ : Fin 2 => h p.2)) (K p.2) (valueIndex2 (K p.2))]
    with x hx hz
  simp only [hz, Pi.zero_apply, add_zero, zero_add]
  exact hx.symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Fixed-time covariance of the genuine native plane weak dual under a material chart. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem integral_sum_inner_comm (G H : Fin 2 → Vec 2 → E) :
    (∫ x, ∑ k : Fin 2, inner ℝ (G k x) (H k x)) =
      ∫ x, ∑ k : Fin 2, inner ℝ (H k x) (G k x) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    Finset.sum_congr rfl (fun k _ => real_inner_comm _ _)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem vecDot_inner_comm (v : Vec 2) (G : Fin 2 → E) (e : E) :
    vecDot v (fun k => inner ℝ e (G k)) = vecDot v (fun k => inner ℝ (G k) e) := by
  apply congrArg (vecDot v)
  funext k
  exact real_inner_comm _ _

theorem planeMaterialDual_pairing {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hvc : ∀ k, Continuous (fun x => v t x k))
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v t x k| ≤ Mv)
    (hcc : ∀ k, Continuous (fun y => chartVector hφ s v t y k))
    {Mc : ℝ} (hMc : 0 ≤ Mc) (hcb : ∀ k y, |chartVector hφ s v t y k| ≤ Mc)
    (hGc : ∀ k j, Continuous (fun y => (ν • chartMetric hφ s t y) k j))
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j y, |(ν • chartMetric hφ s t y) k j| ≤ MG)
    (u z : PlaneHk univ 1 E) (F : PlaneFluxL2 E) :
    inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport (chartVector hφ s v t) hcc hMc hcb)
      (planeScalarDiffusion (fun y => ν • chartMetric hφ s t y) hGc hMG hGb)
      (planeH1ChartPull hφ t s u) (planeFluxChartPull hφ t s F))
      (planeH1ChartPull hφ t s z) =
    inner ℝ (planeWeakDualRepresentative (planeScalarTransport (v t) hvc hMv hvb)
      (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) u F) z := by
  have ht := planeH1ChartPull_transport_pairing hφ t s v u z
  simp_rw [vecDot_inner_comm] at ht
  have hf : (∫ y, ∑ k : Fin 2, inner ℝ (planeFluxChartPull hφ t s F k y)
      (planeH1GradientOperator (planeH1ChartPull hφ t s z) k y)) =
      ∫ x, ∑ k : Fin 2, inner ℝ (F k x) (planeH1GradientOperator z k x) := by
    rw [integral_sum_inner_comm (fun k => (planeFluxChartPull hφ t s F k : Vec 2 → E))
      (fun k => (planeH1GradientOperator (planeH1ChartPull hφ t s z) k : Vec 2 → E)),
      planeH1ChartPull_flux_pairing, integral_sum_inner_comm]
  rw [planeScalarDual_split_pairing, planeViscousDual_split_pairing,
    planeH1ChartPull_diffusion_pairing, hf]
  congr 2
  exact congrArg Neg.neg ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A fixed remainder constant depends only on the two integer jet orders. -/

def centeredSlowRemainderJetPrice (K J : ℕ) : ℝ :=
  Classical.choose (centeredSlow_remainder_jet_budget K J)

theorem centeredSlowRemainderJetPrice_nonneg (K J : ℕ) :
    0 ≤ centeredSlowRemainderJetPrice K J :=
  (Classical.choose_spec (centeredSlow_remainder_jet_budget K J)).1

theorem centeredSlowRemainderJetPrice_bound (K J : ℕ) :
    ∀ (f : Vec 2 → Vec 2 → ℝ),
      ContDiff ℝ (J + (K + 1) : ℕ) (Function.uncurry f) →
      ∀ (ϖ ρ δ ζ B : ℝ), 0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → 0 ≤ B → δ = ζ * ϖ →
      (∀ a b : ℕ, a + b ≤ J → ∀ X z,
        ρ ^ (a + b) * |δ| ^ a *
          ‖iteratedFDeriv ℝ (K + 1 + a) (fun X' => iteratedFDeriv ℝ b (f X') z) X‖ ≤ B) →
      ∀ X0 j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z =>
          f (X0 + δ • z) z - taylorSlow 0 K (fun X' => f X' z) X0 (δ • z)) z‖ ≤
          centeredSlowRemainderJetPrice K J * B * ζ ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1) := by
  exact (Classical.choose_spec (centeredSlow_remainder_jet_budget K J)).2

def centeredSlowRemainderBoundedJetPrice (K Jmax : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Jmax + 1), centeredSlowRemainderJetPrice K j

theorem centeredSlowRemainderBoundedJetPrice_nonneg (K Jmax : ℕ) :
    0 ≤ centeredSlowRemainderBoundedJetPrice K Jmax := by
  exact Finset.sum_nonneg (fun j _ => centeredSlowRemainderJetPrice_nonneg K j)

theorem centeredSlowRemainderJetPrice_le_bounded (K : ℕ) {j Jmax : ℕ} (hj : j ≤ Jmax) :
    centeredSlowRemainderJetPrice K j ≤ centeredSlowRemainderBoundedJetPrice K Jmax := by
  exact Finset.single_le_sum (fun k _ => centeredSlowRemainderJetPrice_nonneg K k)
    (Finset.mem_range.mpr (by omega))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Native source readouts replace external forcings in every level of an actual word chain. -/

theorem planeValue_eq_rawValue {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (U : PlaneHk Set.univ K E) : planeValue U = U.toFunction.jet (valueIndex2 K) := by
  have hz : (⟨⟨0, Nat.lt_succ_of_le (Nat.zero_le K)⟩,
      fun j : Fin 0 => (j.elim0 : Fin 2)⟩ : JetIndex2 K) = valueIndex2 K := by
    apply Sigma.ext
    · exact Fin.ext rfl
    · apply heq_of_eq
      funext j
      exact j.elim0
  unfold planeValue
  rw [planeJetOrder_eq_stored (Nat.zero_le K), hz]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The exact geometry factorial norm transfers to cell coordinates with its plane volume factor. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem weightedFactorialNormSq_affine (n : ℕ) (ϖ ρ e : ℝ) (he : e ≠ 0)
    (y zc : Vec 2) (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n (ϖ * e) (e⁻¹ • (zc - y)) (ρ / e) K (planeCarrierAffine e he y U) =
      ENNReal.ofReal |(e ^ 2)⁻¹| * weightedFactorialNormSq n ϖ zc ρ K U := by
  unfold weightedFactorialNormSq
  change (∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (factorialWeight (ρ / e) j) *
      ∫⁻ z, ENNReal.ofReal (planeMomentPolynomial n (ϖ * e) (e⁻¹ • (zc - y)) z *
        ∑ w : DerivativeWord2 j, ‖planeJetOrder (planeCarrierAffine e he y U) j w z‖ ^ 2)) =
      ENNReal.ofReal |(e ^ 2)⁻¹| *
        ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (factorialWeight ρ j) *
          ∫⁻ x, ENNReal.ofReal (planeMomentPolynomial n ϖ zc x *
            ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w x‖ ^ 2)
  simp_rw [planeMomentPolynomial_affine n ϖ e he y zc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [planeCarrierAffine_order_energy e he y (planeMomentPolynomial n ϖ zc) U hjK,
    ← mul_assoc, ← ENNReal.ofReal_mul (factorialWeight_nonneg _ _)]
  have hp : factorialWeight (ρ / e) j * (‖e ^ j‖ ^ 2 * |(e ^ 2)⁻¹|) =
      |(e ^ 2)⁻¹| * factorialWeight ρ j := by
    rw [← mul_assoc, factorialWeight_affine ρ e he]
    ring
  rw [hp, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Scalar moments commute with the energy of a finite Sobolev tensor. -/

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The weighted factorial energy of an assembled tensor is the sum of component energies. -/
theorem planeFamilyTensor_weighted_factorialEnergy {K : ℕ} (ρ : ℝ)
    (q : Vec 2 → ℝ) (hq : Continuous q) (w : J → PlaneHk Set.univ K E) :
    storedChartFactorialEnergy ρ (fun x => q x ^ 2) (planeFamilyTensor w) =
      ∑ j : J, storedChartFactorialEnergy ρ (fun x => q x ^ 2) (w j) := by
  have he (β : JetIndex2 K) :
      chartScalarEnergy (fun x => q x ^ 2)
        (planeJetReadoutOperator K β (planeFamilyTensor w)) =
        ∑ j : J, chartScalarEnergy (fun x => q x ^ 2)
          (planeJetReadoutOperator K β (w j)) := by
    apply chartScalarEnergy_tensor_readout q hq
    have ht := planeFamilyTensor_jet_ae w β
    simp only [Measure.restrict_univ] at ht
    have hw := ae_all_iff.mpr (fun j : J => univToPlane_ae ((w j).val β))
    filter_upwards [univToPlane_ae ((planeFamilyTensor w).val β), ht, hw]
      with x hx htx hwx
    simp only [planeJetReadoutOperator_apply]
    rw [hx, htx]
    congr 1
    funext j
    exact (hwx j).symm
  unfold storedChartFactorialEnergy
  simp_rw [he, Finset.mul_sum]
  exact Finset.sum_comm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! On its full certified geometry, each piece's common-reference transition is the fixed map between its two anchors. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

theorem preparation_reference_material_stationary
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (p : P') (hp : ((F.piece p).output ∩ Set.Icc a b).Nonempty)
    (s t : ℝ) (ht : t ∈ (F.piece p).geometry) (y : Vec 2) :
    pieceReferenceMaterial F hφ s p t y = streamFlow φ hφ s y (F.piece p).anchor := by
  change streamFlow φ hφ s ((F.piece p).material t y) t = _
  rw [preparation_material_eq_streamFlow hc p hp t ht]
  exact Infra.Flow.flow_group_law _ hφ.vel_lipschitz
    (flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz) y (F.piece p).anchor t s

theorem preparation_reference_inverse_material_stationary
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (p : P') (hp : ((F.piece p).output ∩ Set.Icc a b).Nonempty)
    (s t : ℝ) (ht : t ∈ (F.piece p).geometry) (y : Vec 2) :
    (pieceReferenceMaterial F hφ s p t).symm y =
      streamFlow φ hφ (F.piece p).anchor y s := by
  apply (pieceReferenceMaterial F hφ s p t).injective
  rw [Homeomorph.apply_symm_apply, preparation_reference_material_stationary hc p hp s t ht]
  have hh := Infra.Flow.flow_group_law _ hφ.vel_lipschitz
    (flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz) y s (F.piece p).anchor s
  exact ((hh.trans ((flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz).1 y s))).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Exact centred polynomial energies for the initial datum in cell coordinates. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem weightedFactorialNormSq_affine_centered (n : ℕ) (ϖ ρ e : ℝ)
    (he : e ≠ 0) (yc : Vec 2) (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ 0 (ρ / e) K (planeCarrierAffine e he yc U) =
      ENNReal.ofReal |(e ^ 2)⁻¹| * weightedFactorialNormSq n (ϖ / e) yc ρ K U := by
  have hh := weightedFactorialNormSq_affine n (ϖ / e) ρ e he yc yc U
  simpa only [div_mul_cancel₀ _ he, sub_self, smul_zero] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The reference-to-piece anchor maps lie entirely inside the certified padded flow domain. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
  (p : P') (hp : ((F.piece p).output ∩ Set.Icc a b).Nonempty)

include hc hp

theorem preparation_piece_anchor_mem_geometry : (F.piece p).anchor ∈ (F.piece p).geometry := by
  have hactive := hp
  obtain ⟨t, ht, _⟩ := hactive
  exact hc.schedule.anchor_segments p hp t ((F.piece p).output_subset ht) Set.left_mem_uIcc

theorem preparation_reference_anchor_endpoints (hT : 0 ≤ ocTauPP α q Λ m) :
    (F.piece p).anchor ∈ preparationPaddedWindow a b Cpad (ocTauPP α q Λ m) ∧
      ((l₀ : ℝ) * ocTauPP α q Λ m) ∈ preparationPaddedWindow a b Cpad (ocTauPP α q Λ m) ∧
      |(F.piece p).anchor - (l₀ : ℝ) * ocTauPP α q Λ m| ≤ 2 * Cage * ocTauPP α q Λ m := by
  have hg := preparation_piece_anchor_mem_geometry hc p hp
  refine ⟨hc.schedule.geometry_padded p hp hg, hc.schedule.reference_mem, ?_⟩
  have hh := hc.schedule.reference_age p hp _ hg
  have hn : 0 ≤ Cage * ocTauPP α q Λ m := mul_nonneg hc.schedule.age_pos.le hT
  linarith
end

/-! The actual common-reference inverse Piola Jacobian is a fixed natural anchor-to-anchor Jacobian. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

theorem preparation_reference_inverseJacobian_eq_natural
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (p : P') (hp : ((F.piece p).output ∩ Set.Icc a b).Nonempty)
    (s t : ℝ) (ht : t ∈ (F.piece p).geometry) :
    chartInvJacobian ⇑(pieceReferenceMaterial F hφ s p t).symm =
      naturalPreparationJacobian hφ (F.piece p).anchor s := by
  funext x
  rw [chartInvJacobian_homeomorph_symm (pieceReferenceMaterial F hφ s p t)
    ((pieceReferenceMaterial_smooth F hφ s p t).differentiable (by simp))
    ((pieceReferenceMaterial_symm_smooth F hφ s p t).differentiable (by simp))]
  have hforward : ⇑(pieceReferenceMaterial F hφ s p t) =
      fun y => streamFlow φ hφ s y (F.piece p).anchor :=
    funext (preparation_reference_material_stationary hc p hp s t ht)
  have hinverse : ⇑(pieceReferenceMaterial F hφ s p t).symm =
      fun y => streamFlow φ hφ (F.piece p).anchor y s :=
    funext (preparation_reference_inverse_material_stationary hc p hp s t ht)
  rw [hforward, hinverse]
  rfl
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The initial plane dilation Jacobian cancels the squared physical return price,
uniformly over the component family and without a finiteness assumption on its energy. -/

theorem planeAffine_return_volume_price (C e : ℝ) (he : e ≠ 0) :
    ENNReal.ofReal ((C * |e|) ^ 2) * ENNReal.ofReal |(e ^ 2)⁻¹| =
      ENNReal.ofReal (C ^ 2) := by
  rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_pow, sq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg e)), mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero 2 he), mul_one]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

 theorem weightedFactorialNormSq_family_affine_centered (π : ι → ℝ) (K : ι → ℕ)
    (n : ℕ) (ϖ ρ e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : ∀ i, PlaneHk Set.univ (K i) (h i)) :
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K i)
      (planeCarrierAffine e he yc (U i))) =
      ENNReal.ofReal |(e ^ 2)⁻¹| *
        ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n (ϖ / e) yc ρ (K i) (U i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedFactorialNormSq_affine_centered]
  exact mul_left_comm _ _ _

theorem planeAffine_family_initial_return_price (π : ι → ℝ) (K : ι → ℕ)
    (n : ℕ) (C ϖ ρ e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : ∀ i, PlaneHk Set.univ (K i) (h i)) :
    ENNReal.ofReal ((C * |e|) ^ 2) *
      (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K i)
        (planeCarrierAffine e he yc (U i))) =
      ENNReal.ofReal (C ^ 2) *
        ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n (ϖ / e) yc ρ (K i) (U i) := by
  rw [weightedFactorialNormSq_family_affine_centered, ← mul_assoc,
    planeAffine_return_volume_price C e he]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
open AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Native subwindows retain the full future-memory polynomial weights and uniform comparison constants. -/

def adjointSubwindowChartWeights {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (hellT : ocEll q Λ m ν ^ 2 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m)
    (hdur : Real.sqrt T * ocEll q Λ m ν / ocTau α q Λ m *
      Real.exp (-Real.pi ^ 2 * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) ≤ 1)
    (yc : Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => G p.1 p.2 k j))
    (hGsym : ∀ t z, (G t z).IsSymm) (g : ℝ) (hg : g ≤ 1 / 4)
    (t₀ S : ℝ) (hS : 0 < S) (hST : S ≤ T / ocEll q Λ m ν ^ 2)
    (hGn : IsMetricNearIdentityOn (Set.Icc t₀ (t₀ + S)) G g) (M : ℕ) :
    ChartWeights G (ocCellDrift α q Λ ζ m ν yc) t₀ S
      (ocEpsilon q Λ m / Real.sqrt (B * T)) 0 M (adjointWeightConstant C K) := by
  let W := adjointCellPolynomialWeight α q Λ ζ m ν B T yc
  have hWp : ∀ n t z, 0 < W n t z := fun n t z =>
    adjointCellPolynomialWeight_pos α q Λ ζ m ν B T yc n t z
  have hWs : ∀ n, ContDiff ℝ 2 (fun p : ℝ × Vec 2 => W n p.1 p.2) := fun n =>
    adjointCellPolynomialWeight_joint_contDiff hΛ hζ ν B T yc n 2
  have hGs : ∀ t k j, Differentiable ℝ (fun z => G t z k j) := fun t k j =>
    ((hG k j).comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)
  have hellp : 0 < ocEll q Λ m ν ^ 2 := by
    have hep := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    unfold ocEll
    positivity
  refine {
    W := W
    Phi := fun n t z k => metricCorrectionFlux (W n t) (G t) z k
    lam := fun n => adjointWeightRate C K n * (ocEll q Λ m ν ^ 2 / T)
    smooth := ?_
    pos := ?_
    comparable := ?_
    defect := ?_
    bound := ?_
    lam_bound := ?_ }
  · intro n _
    exact ⟨hWs n, metricCorrectionFlux_joint_contDiff (W n) (hWs n) G hG⟩
  · intro n _ t z
    exact hWp n t z
  · intro n _ t _ z
    have hh := adjointCellPolynomialWeight_comparable hΛ hζ hν hB hT hC he
      (by simpa only [CycleReference.ocEll_sq_eq hν] using hellT) yc n t z
    have hcomp := adjointWeightConstant_comparison hC hK n
    have hp := adjointWeightComparison_pos C n
    have hU : 0 ≤ (1 + (ocEpsilon q Λ m / Real.sqrt (B * T)) ^ 2 *
        (z 0 ^ 2 + z 1 ^ 2)) ^ n := by positivity
    have hew := weight_comparison_enlarge hU hp hcomp
      (show (adjointWeightComparison C n)⁻¹ * _ ≤ W n t z from hh.1)
      (show W n t z ≤ adjointWeightComparison C n * _ from hh.2)
    simpa only [Pi.zero_apply, sub_zero] using hew
  · intro n _ t _ z
    exact adjointPolynomial_metric_defect hΛ hζ hν hB hT hC he K hK hb hdur yc G hGs n t z
  · intro n _ t ht z
    exact adjointPolynomial_metric_gradient hΛ hζ hν hB hT hC hK he yc G n t z
      (fun i j => nearIdentityOn_entry_abs_le G hg hGn ht z (hGsym t z) i j)
  · intro n _
    refine ⟨mul_nonneg (adjointWeightRate_nonneg hC hK n) (div_pos hellp hT).le, ?_⟩
    have hi : adjointWeightRate C K n * (ocEll q Λ m ν ^ 2 / T) =
        adjointWeightRate C K n / (T / ocEll q Λ m ν ^ 2) := by field_simp
    rw [hi]
    have hc0 : 0 ≤ adjointWeightConstant C K n :=
      (adjointWeightRate_nonneg hC hK n).trans (adjointWeightConstant_rate hC hK n)
    exact (div_le_div_of_nonneg_right (adjointWeightConstant_rate hC hK n)
      (div_pos hT hellp).le).trans (div_le_div_of_nonneg_left hc0 hS hST)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Flux readouts which superpose almost everywhere determine genuine native forcing superposition. -/

variable {X E : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeForcing_ae_linear_readout_superposition (μ : Measure ℝ)
    (H : X → ℝ → Vec 2 → E) (V : X → ℝ → PlaneHk Set.univ K E)
    (haddH : ∀ x y, ∀ᵐ t ∂μ, H (x + y) t =ᵐ[volume]
      fun z => H x t z + H y t z)
    (hsmulH : ∀ (c : ℝ) x, ∀ᵐ t ∂μ, H (c • x) t =ᵐ[volume]
      fun z => c • H x t z)
    (hread : ∀ x, ∀ᵐ t ∂μ, planeValue (V x t) =ᵐ[volume] H x t) :
    (∀ x y, V (x + y) =ᵐ[μ] fun t => V x t + V y t) ∧
      ∀ (c : ℝ) x, V (c • x) =ᵐ[μ] fun t => c • V x t := by
  constructor
  · intro x y
    filter_upwards [hread (x + y), hread x, hread y, haddH x y] with t ht htx hty htH
    apply planeHk_eq_of_planeValue_ae
    have hadd : planeValue (V x t + V y t) =ᵐ[volume]
        fun z => planeValue (V x t) z + planeValue (V y t) z := by
      simpa only [planeValue_eq_rawValue] using
        planeCarrier_jet_add_ae (V x t) (V y t) (valueIndex2 K)
    filter_upwards [ht, htx, hty, hadd, htH] with z hz hzx hzy hza hzH
    rw [hz, hza, hzx, hzy]
    exact hzH
  · intro c x
    filter_upwards [hread (c • x), hread x, hsmulH c x] with t ht htx htH
    apply planeHk_eq_of_planeValue_ae
    have hsmul : planeValue (c • V x t) =ᵐ[volume]
        fun z => c • planeValue (V x t) z := by
      simpa only [planeValue_eq_rawValue] using
        planeCarrier_jet_smul_ae c (V x t) (valueIndex2 K)
    filter_upwards [ht, htx, hsmul, htH] with z hz hzx hzs hzH
    rw [hz, hzs, hzx]
    exact hzH

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Scalar moments retain the exact finite factorial reserve cost of derivative tensors. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A weighted derivative tensor has the same finite factorial reserve price as its raw jet array. -/
theorem planeDerivativeTensor_weighted_factorialEnergy_le {K r : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) (q : Vec 2 → ℝ) (hq : Continuous q)
    (U : PlaneHk Set.univ (K + r) E)
    (hD : JetMemL2On Set.univ (fun β x => q x • U.toFunction.jet β x)) :
    storedChartFactorialEnergy ρ (fun x => q x ^ 2) (planeDerivativeTensor (K := K) (r := r) U) ≤
      ENNReal.ofReal ((derivativeReserveFactor ρ K r) ^ 2) *
        storedChartFactorialEnergy ρ (fun x => q x ^ 2) U := by
  let J := jetToL2 (fun β x => q x • U.toFunction.jet β x) hD
  have hDa (a : DerivativeWord2 r) :
      JetMemL2On Set.univ (fun β x => q x • (derivativePlaneHk (K := K) a U).toFunction.jet β x) := by
    intro β
    exact hD (prefixJetIndex a β)
  have hJ (a : DerivativeWord2 r) :
      jetToL2 (fun β x => q x • (derivativePlaneHk (K := K) a U).toFunction.jet β x) (hDa a) =
        derivativeJet a J := by
    rfl
  have he : storedChartFactorialEnergy ρ (fun x => q x ^ 2)
      (planeDerivativeTensor (K := K) (r := r) U) =
      ENNReal.ofReal (∑ a : DerivativeWord2 r, factorialNormSq ρ (derivativeJet a J)) := by
    rw [planeDerivativeTensor, planeFamilyTensor_weighted_factorialEnergy ρ q hq,
      ENNReal.ofReal_sum_of_nonneg (fun a _ => factorialNormSq_nonneg ρ (derivativeJet a J))]
    apply Finset.sum_congr rfl
    intro a _
    rw [storedChartFactorialEnergy_weighted_jet_readout ρ q _ (hDa a), hJ a]
  rw [he, storedChartFactorialEnergy_weighted_jet_readout ρ q U hD,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    (derivativeArray_factorialNormSq_le (K := K) (r := r) ρ hρ J)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The forced coupled error retains its genuine scalar metric equation and total external source flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The genuine coupling row gives the exact external flux required by the weighted scalar theorem. -/
theorem planeForced_metric_source_order_two_chain {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ) (hD : 2 ≤ D) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v D K
      (fun i j d r x => planeDiagonalGradientCoefficient K D (fun _ t z => G t z - 1) i j d r x + A i j d r x) f F (fun _ _ => 0) u w) :
    IsPlaneChainFrom (geometryScalarData 2 G) (fun _ i => K i) a b v
      (fun _ i => f i)
      (fun _ i t => F i t + planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)
      (fun _ i => u i) (fun _ i => w i) := by
  have hsplit := planeForced_split_flux_solution hab 1 ρ hρ K D v A
    (planeDiagonalGradientCoefficient K D (fun _ t z => G t z - 1))
    hA hc f F (fun _ _ => 0) u w hs
  have hone := planeWeakSolution_oneLevel K D 1 a b v
    (planeDiagonalGradientCoefficient K D (fun _ t z => G t z - 1)) f
    (fun i t => F i t + planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)
    (fun _ _ => 0) u w hsplit
  have hcoeff : planeOneLevelCoefficient K D
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t z => G t z - 1)) =
      planeChainCoefficient (geometryScalarData D G) (fun _ => K) := by
    funext p p' d t z
    exact planeDiagonalGradientCoefficient_eq_scalar_chain K D G p p' d t z
  rw [hcoeff] at hone
  exact AVRegularity.CycleWords.geometryScalarSolution_order_two D hD G (fun _ i => K i)
    a b v (fun _ i => f i)
    (fun _ i t => F i t + planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)
    (fun _ i => u i) (fun _ i => w i) hone

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The exact homogeneous coupled plane solution has its viscous weak Hilbert time curve. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {a b : ℝ} (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))

/-- The homogeneous coupled plane solution supplies its literal viscous weak Hilbert curve. -/
theorem planeHomogeneous_coupledWeakHilbertCurve
    (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hvc : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hsln : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι) :
    PlaneWeakHilbertCurve a b (coupledPlaneL2Trace u i) (coupledPlaneH1Slice w i)
      (fun t => planeWeakDualRepresentative
        (planeIntervalTransport a b hab v hvc M hvb t)
        (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 (h i)))
        (coupledPlaneH1Slice w i t)
        (planeFluxValueOperator (E := h i) (K i)
          (planeCouplingFluxRow hab ρ hρ K D A hA hc w i t))) := by
  apply coupledWeakSolution_planeWeakHilbertCurve hsln i
  · apply planeViscousDual_memLp
    · exact hvm
    · exact (coupledWeakSolution_h1_trace_data hsln i).2.1
    · exact planeFluxValueOperator_memLp (K i) _
        (planeCouplingFluxRow_memLp hab ρ hρ K D A hA hc w hAm hsln.2.1 i)
  · intro s hs t ht hst φ
    rw [planeHomogeneous_trace_increment hab K D v A f u w hsln i hs ht φ]
    apply intervalIntegral.integral_congr
    intro r hr
    have hrab : r ∈ Set.Icc a b :=
      Set.Icc_subset_Icc hs.1 ht.2 (by simpa only [Set.uIcc_of_le hst] using hr)
    have hp := planeViscousDual_pair_eq_raw ν (K i)
      (planeIntervalCoefficient a b hab v r)
      (planeIntervalVelocity_continuous a b hab v hvc r) (le_max_right M 0)
      (planeIntervalVelocity_bound a b hab v M hvb r) (w i r) φ
      (planeFluxValueOperator (E := h i) (K i)
        (planeCouplingFluxRow hab ρ hρ K D A hA hc w i r))
      (planeRawCouplingFlux K D r A (fun i => w i r) i)
      (planeCouplingFluxRow_component_ae hab ρ hρ K D A hA hc w i r hrab)
    simpa only [planeIntervalCoefficient_of_mem a b hab v r hrab,
      planeWeakSpatialRhs, coupledPlaneH1Slice, planeIntervalTransport] using hp.symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Finite weighted lift energy controls every admissible positive derivative tensor. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A positive derivative tensor has a finite reserve bound against the full weighted lift. -/
theorem planePositiveDerivativeTensor_weighted_factorialEnergy_le {K L : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (hm : 1 ≤ m) (hKL : K + (m - 1) ≤ L)
    (w : PlaneHk Set.univ (L + 1) E) (q : Vec 2 → ℝ) (hq : Continuous q)
    (hD : JetMemL2On Set.univ (fun β x => q x • w.toFunction.jet β x)) :
    storedChartFactorialEnergy ρ (fun x => q x ^ 2)
        (planePositiveDerivativeTensor m hm hKL w) ≤
      ENNReal.ofReal ((derivativeReserveFactor ρ K m) ^ 2) *
        storedChartFactorialEnergy ρ (fun x => q x ^ 2) w := by
  cases m with
  | zero => omega
  | succ s =>
    have hT : K + (s + 1) ≤ L + 1 := by omega
    have hDt : JetMemL2On Set.univ
        (fun β x => q x • (truncatePlaneHk hT w).toFunction.jet β x) :=
      fun β => hD (truncateJetIndex hT β)
    exact (planeDerivativeTensor_weighted_factorialEnergy_le ρ hρ q hq
      (truncatePlaneHk hT w) hDt).trans
      (mul_le_mul (le_refl _) (storedChartFactorialEnergy_weighted_truncate_le hT ρ q w hD)
        zero_le zero_le)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! The natural-flow remainder chart price depends only on fixed jet orders
and the supplied chart constants, before the family and physical scales. -/

def naturalRemainderChartPrice (Ks Kmax Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  (Kmax.factorial : ℝ) *
    (1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|) ^ Kmax *
    (Kmax + 1 : ℕ) * centeredSlowRemainderBoundedJetPrice Ks Kmax *
    (3 + max (Cchart 0) 0) ^ (Ks + 1)

theorem naturalRemainderChartPrice_nonneg (Ks Kmax Jchart : ℕ) (Cchart : ℕ → ℝ) :
    0 ≤ naturalRemainderChartPrice Ks Kmax Jchart Cchart := by
  unfold naturalRemainderChartPrice
  have hC := centeredSlowRemainderBoundedJetPrice_nonneg Ks Kmax
  positivity

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Exact weighted identification of the actual piece array with its natural-flow formula. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem weighted_reference_piece_operator_eq_natural
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (p : P') (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (s : ℝ) (t : Set.Icc tS tZ) (x : Vec 2) :
    F.weight p t • (nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (chartInvJacobian ⇑(pieceReferenceMaterial F hφ s p t).symm)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I t
          ((pieceReferenceMaterial F hφ s p t).symm x) (e⁻¹ • (pieceReferenceMaterial F hφ s p t).symm x)) r A x a)) =
    F.weight p t • (nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor s)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I t
          (streamFlow φ hφ (F.piece p).anchor x s)
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor x s)) r A x a)) := by
  by_cases hw : F.weight p t = 0
  · rw [hw]
    ext z k
    simp
  · have ht : (t : ℝ) ∈ (F.piece p).output := by
      by_contra hout
      exact hw (F.weight_zero p t hout)
    have hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty := ⟨t, ht, t.property⟩
    rw [preparation_reference_inverseJacobian_eq_natural hc p hp s t ((F.piece p).output_subset ht),
      show ⇑(pieceReferenceMaterial F hφ s p t).symm =
        (fun x => streamFlow φ hφ (F.piece p).anchor x s) from
        funext (preparation_reference_inverse_material_stationary hc p hp s t
          ((F.piece p).output_subset ht))]
end

/-! Actual constituent coefficients inherit positive active-piece budgets without counting pieces. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem reference_constituentPhysical_eq_natural (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (d : ℕ) (s : ℝ) (t : Set.Icc tS tZ) :
    constituentPhysical (referenceChartedFamily F hφ s) ν e E actual v u γ d t =
      fun y => ∑ᶠ p, F.weight p t • nativeArrayAssembly (d - 1) (F.identity v u γ).map
        (fun a A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor s)
          (F.identity v u γ).maxOrder
          (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
            (streamFlow φ hφ (F.piece p).anchor y s)
            (e⁻¹ • streamFlow φ hφ (F.piece p).anchor y s)) (d - 1) A y a) := by
  funext y
  unfold constituentPhysical
  dsimp only [referenceChartedFamily]
  apply finsum_congr
  intro p
  change F.weight p t • (nativeArrayAssembly (d - 1) (F.identity v u γ).map
    (fun a A => transportedCoeff (chartInvJacobian ⇑(pieceReferenceMaterial F hφ s p t).symm)
      (F.identity v u γ).maxOrder
      (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
        ((pieceReferenceMaterial F hφ s p t).symm y)
        (e⁻¹ • (pieceReferenceMaterial F hφ s p t).symm y)) (d - 1) A y a)) = _
  rw [weighted_reference_piece_operator_eq_natural F hc ν e E p (actual p) v u γ (d - 1) s t y]
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The genuine weak curve's material L2 trace is continuous and agrees with its native chart H1 state. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_chart_trace_continuous {a b : ℝ}
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E} (h : PlaneWeakHilbertCurve a b u slice dual)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ) :
    ContinuousOn (fun t => planeL2FlowPull hφ t s (u t)) (Icc a b) :=
  planeL2FlowPull_continuousOn hφ s (Icc a b) u h.trace

theorem planeWeakCurve_chart_state_agrees {a b : ℝ}
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E} (h : PlaneWeakHilbertCurve a b u slice dual)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc a b), planeL2FlowPull hφ t s (u t) =
      planeHkValueOperator 1 (planeH1ChartPull hφ t s (slice t)) := by
  filter_upwards [h.agrees] with t ht
  rw [ht, planeH1ChartPull_value_eq]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Real scaling of native plane carriers has the exact quadratic price in polynomial factorial energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem chartScalarEnergy_smul (q : Vec 2 → ℝ) (c : ℝ)
    (U : Lp E 2 (volume : Measure (Vec 2))) :
    chartScalarEnergy q (c • U) = ENNReal.ofReal (c ^ 2) * chartScalarEnergy q U := by
  unfold chartScalarEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_smul c U] with x hx
  rw [hx, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have he : q x * (c ^ 2 * ‖U x‖ ^ 2) = c ^ 2 * (q x * ‖U x‖ ^ 2) := by ring
  rw [he, ENNReal.ofReal_mul (sq_nonneg c)]

theorem storedChartFactorialEnergy_smul {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (c : ℝ) (U : PlaneHk Set.univ K E) :
    storedChartFactorialEnergy ρ q (c • U) =
      ENNReal.ofReal (c ^ 2) * storedChartFactorialEnergy ρ q U := by
  unfold storedChartFactorialEnergy
  simp_rw [map_smul, chartScalarEnergy_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ac_rfl

theorem weightedFactorialNormSq_smul {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ c : ℝ) (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc ρ K (c • U) =
      ENNReal.ofReal (c ^ 2) * weightedFactorialNormSq n ϖ zc ρ K U := by
  rw [weightedFactorialNormSq_stored_readout, weightedFactorialNormSq_stored_readout,
    storedChartFactorialEnergy_smul]

theorem integrated_weightedFactorialNormSq_smul_ne_top {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ c : ℝ) (μ : Measure ℝ)
    (U : ℝ → PlaneHk Set.univ K E)
    (he : (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (U t) ∂μ) ≠ ⊤) :
    (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (c • U t) ∂μ) ≠ ⊤ := by
  simp_rw [weightedFactorialNormSq_smul]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top he

end AVRegularity.CycleJointProofs
end
end
