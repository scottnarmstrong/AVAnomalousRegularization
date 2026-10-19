-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.CellTransverseBilinearProjection
import AVRegularity.CycleReference.ChartCorrectionIntegrability
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Gluing the actual error with zero initial datum and bounded remainder forcing. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem nativeError_renewal_mass_budget {P N J : ℕ} (hP : P ≤ N)
    (π : ι → ℝ) (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (a b : Fin P → ℝ)
    (f : ∀ (_ : Fin P) x, PlaneHk Set.univ (K x) (h x))
    (fZ : ∀ (_ : Fin P) (_ : Fin (J + 1)) x, PlaneHk Set.univ (K x) (h x))
    (U : ∀ (_ : Fin P) x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Uw : ∀ (_ : Fin P) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (Z : ∀ (_ : Fin P) (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Zw : ∀ (_ : Fin P) (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (A L B F : ℝ≥0∞) (hB : 1 ≤ B) (hAB : A ≤ B) (hALB : A * L + A ≤ B)
    (hfzero : ∀ i : Fin P, i.val = 0 → ∀ x, nativeErrorDatum (f i x) (fun j => fZ i j x) = 0)
    (hjoin : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ x,
      weightedFactorialNormSq n ϖ 0 ρ (K x) (nativeErrorDatum (f i' x) (fun j => fZ i' j x)) ≤
      L * nativeComponentEnergy n ϖ ρ (a i) (b i)
        (nativeErrorCurve (U i x) (fun j => Z i j x))
        (nativeErrorCurve (Uw i x) (fun j => Zw i j x)))
    (hpiece : ∀ i : Fin P,
      (∑ x, ENNReal.ofReal ((π x)⁻¹) * nativeComponentEnergy n ϖ ρ (a i) (b i)
        (nativeErrorCurve (U i x) (fun j => Z i j x))
        (nativeErrorCurve (Uw i x) (fun j => Zw i j x))) ≤
      A * ((∑ x, ENNReal.ofReal ((π x)⁻¹) * weightedFactorialNormSq n ϖ 0 ρ (K x)
        (nativeErrorDatum (f i x) (fun j => fZ i j x))) + F)) :
    ∀ i : Fin P,
      (∑ x, ENNReal.ofReal ((π x)⁻¹) * nativeComponentEnergy n ϖ ρ (a i) (b i)
        (nativeErrorCurve (U i x) (fun j => Z i j x))
        (nativeErrorCurve (Uw i x) (fun j => Zw i j x))) ≤ B ^ N * F := by
  classical
  let E := fun i : Fin P => ∑ x, ENNReal.ofReal ((π x)⁻¹) * nativeComponentEnergy n ϖ ρ (a i) (b i)
    (nativeErrorCurve (U i x) (fun j => Z i j x))
    (nativeErrorCurve (Uw i x) (fun j => Zw i j x))
  have hz : ∀ i : Fin P, i.val = 0 → E i ≤ A * (0 + F) := by
    intro i hi
    have hp := hpiece i
    simpa only [hfzero i hi, Weighted.weightedFactorialNormSq_zero_carrier,
      mul_zero, Finset.sum_const_zero] using hp
  have hs : ∀ i i' : Fin P, i'.val = i.val + 1 → E i' ≤ A * (L * E i + F) := by
    intro i i' hi
    have hj := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
      mul_le_mul_right (hjoin i i' hi x) (ENNReal.ofReal ((π x)⁻¹)))
    have hj' : (∑ x, ENNReal.ofReal ((π x)⁻¹) * weightedFactorialNormSq n ϖ 0 ρ (K x)
        (nativeErrorDatum (f i' x) (fun j => fZ i' j x))) ≤ L * E i := by
      simpa only [E, mul_left_comm, Finset.mul_sum] using hj
    exact (hpiece i').trans (mul_le_mul_right (add_le_add hj' le_rfl) A)
  simpa only [zero_add] using finite_renewal_budget hP E 0 F A L B hB hAB hALB hz hs

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Scalar forcing in a transverse energy estimate retains full diffusion coercivity. -/

theorem cellSourceFunctional_scalar_only (θ : Fin 2 → ℂ)
    (src : ComplexCellL2) (u : TorusHk 1 ℂ) :
    cellSourceFunctional θ src 0 u = inner ℝ src (torusHkValueCLM u) := by
  simp only [cellSourceFunctional, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Pi.zero_apply, inner_zero_left, Finset.sum_const_zero, sub_zero]

theorem cellSourceFunctional_scalar_energy_le (θ : Fin 2 → ℂ)
    (src : ComplexCellL2) (u : TorusHk 1 ℂ) :
    2 * cellSourceFunctional θ src 0 u ≤ ‖src‖ ^ 2 + ‖torusHkValueCLM u‖ ^ 2 := by
  rw [cellSourceFunctional_scalar_only]
  have h := (le_abs_self _).trans (abs_real_inner_le_norm src (torusHkValueCLM u))
  nlinarith only [h, sq_nonneg (‖src‖ - ‖torusHkValueCLM u‖)]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleWords

/-! Literal letter forcing is unchanged when every nonempty source jet is retained. -/

variable {ι σ : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem letterFullOrderFlux_truncate (L : CycleLetter ι h D)
    (κ κ' : σ → ℕ) (hκ : ∀ p, κ' p ≤ κ p) (b : ι → σ) (v : ι)
    (hr : ∀ u (o : Finset.Icc 2 D), L.edge v u o ≠ [] → o.1 - 1 ≤ κ' (b u) + 1)
    (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (t : ℝ) (z : Vec 2) :
    letterFullOrderFlux L κ' b v lo X₀ δ
      (fun u => truncatePlaneHk (Nat.succ_le_succ (hκ (b u))) (W u)) t z =
      letterFullOrderFlux L κ b v lo X₀ δ W t z := by
  classical
  unfold letterFullOrderFlux
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro o ho
  simp only [dite_eq_left ho]
  by_cases hz : L.edge v u ⟨o, ho⟩ = []
  · simp only [hz, slowEvalCoefficient, List.map_nil, List.sum_nil, zero_apply]
  · have he (w : DerivativeWord2 (o - 1)) :=
      congrFun (planeJetOrder_truncate (Nat.succ_le_succ (hκ (b u)))
        (hr u ⟨o, ho⟩ hz) (W u) w) z
    simp_rw [he]

theorem letterAdmissibleFlux_truncate (L : CycleLetter ι h D)
    (κ κ' : σ → ℕ) (hκ : ∀ p, κ' p ≤ κ p) (a : σ) (b : ι → σ) (v : ι)
    (hc : ∀ u (o : Finset.Icc 2 D), L.edge v u o ≠ [] → κ a + o.1 ≤ κ (b u) + 2)
    (hc' : ∀ u (o : Finset.Icc 2 D), L.edge v u o ≠ [] → κ' a + o.1 ≤ κ' (b u) + 2)
    (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (t : ℝ) (z : Vec 2) :
    Weighted.letterAdmissibleFlux L κ' a b v lo X₀ δ
      (fun u => truncatePlaneHk (Nat.succ_le_succ (hκ (b u))) (W u)) t z =
      Weighted.letterAdmissibleFlux L κ a b v lo X₀ δ W t z := by
  rw [letterAdmissibleFlux_eq_fullOrderFlux L κ' a b v hc',
    letterAdmissibleFlux_eq_fullOrderFlux L κ a b v hc]
  apply letterFullOrderFlux_truncate L κ κ' hκ b v
  intro u o hn
  have hh := hc' u o hn
  have ho := (Finset.mem_Icc.mp o.2).1
  omega

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The original normalized generator has a drift-independent energy bound on every native state. -/

theorem cellNormalizedGenerator_sharp_garding
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    2 * cellGeneratorForm ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG V hv.1 hb t u u + (3 / 4) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤
      (264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) +
        2 * (Cw * fibreNorm ξ + ‖κ t‖)) * ‖torusHkValueCLM u‖ ^ 2 := by
  let p := torusHkValueCLM u
  have hd := cellDiffusionForm_sharp_garding
    ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG t u
  have hc : |inner ℝ (cellScalarCLM Complex.I
      (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t p)) p| ≤
      Cw * fibreNorm ξ * ‖p‖ ^ 2 := by
    have h := abs_real_inner_le_norm
      (cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t p)) p
    rw [cellScalarCLM_norm, Complex.norm_I, one_mul] at h
    exact h.trans ((mul_le_mul_of_nonneg_right
      (cellFibreDriftCouplingCLM_apply_norm_le η Cw hCw hv hw ξ t p)
      (norm_nonneg p)).trans_eq (by ring))
  have hk : |inner ℝ (cellScalarCLM (κ t) p) p| ≤ ‖κ t‖ * ‖p‖ ^ 2 := by
    exact (abs_real_inner_le_norm _ _).trans_eq (by rw [cellScalarCLM_norm]; ring)
  rw [cellNormalizedGenerator_diagonal η Cw hCw G hG hv hw V hb]
  have hc' := neg_le_abs (inner ℝ (cellScalarCLM Complex.I
    (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t p)) p)
  have hk' := le_abs_self (inner ℝ (cellScalarCLM (κ t) p) p)
  change 2 * (_ - _ + _) + _ ≤ _
  dsimp only [p] at hc hk hc' hk'
  nlinarith only [hd, hc, hk, hc', hk']

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleWords

/-! Literal scalar and gradient densities integrate to the polynomial factorial norms. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem planeGradientTensor_factorialDensity_ae {K : ℕ} (ρ : ℝ)
    (U : PlaneHk Set.univ (K + 1) E) :
    planeFactorialDensity ρ (planeGradientTensor U) =ᵐ[volume] planeGradFactorialDensity ρ U := by
  have hh : ∀ᵐ x ∂volume, ∀ j : Fin (K + 1), ∀ w : DerivativeWord2 j.val,
      planeJetOrder (planeGradientTensor U) j.val w x =
        WithLp.toLp 2 (fun k : Fin 2 => planeJetOrder U (j.val + 1) (Fin.snoc w k) x) :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun w =>
      planeGradientTensor_word_readout U j.val (Nat.le_of_lt_succ j.isLt) w))
  filter_upwards [hh] with x hx
  rw [planeFactorialDensity_orders_eq]
  unfold planeGradFactorialDensity
  apply Finset.sum_congr rfl
  intro j hj
  have hjs : j < K + 1 := Finset.mem_range.mp hj
  simp_rw [hx ⟨j, hjs⟩, PiLp.norm_sq_eq_of_L2]
  congr 1
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (fun p : Fin 2 × DerivativeWord2 j =>
    ‖planeJetOrder U (j + 1) (Fin.snoc p.2 p.1) x‖ ^ 2)]
  exact Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (j + 1) => Fin 2))
    (fun p : Fin 2 × DerivativeWord2 j => ‖planeJetOrder U (j + 1) (Fin.snoc p.2 p.1) x‖ ^ 2)
    (fun w : DerivativeWord2 (j + 1) => ‖planeJetOrder U (j + 1) w x‖ ^ 2)
    (fun _ => rfl)

omit [FiniteDimensional ℝ E] in
theorem weightedFactorialNormSq_density {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc ρ K U =
      ∫⁻ x, ENNReal.ofReal (Weighted.planeMomentPolynomial n ϖ zc x *
        planeFactorialDensity ρ U x) := by
  rw [Weighted.weightedFactorialNormSq_stored_readout]
  apply storedChartFactorialEnergy_density
  · have hc : Continuous (Weighted.planeMomentPolynomial n ϖ zc) := by
      unfold Weighted.planeMomentPolynomial
      fun_prop
    exact hc.aemeasurable
  · intro x
    unfold Weighted.planeMomentPolynomial
    positivity

theorem weightedGradFactorialNormSq_density {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (U : PlaneHk Set.univ (K + 1) E) :
    weightedGradFactorialNormSq n ϖ zc ρ K U =
      ∫⁻ x, ENNReal.ofReal (Weighted.planeMomentPolynomial n ϖ zc x *
        planeGradFactorialDensity ρ U x) := by
  rw [← planeGradientTensor_weightedFactorialNormSq n ϖ zc ρ U,
    weightedFactorialNormSq_density]
  apply lintegral_congr_ae
  filter_upwards [planeGradientTensor_factorialDensity_ae ρ U] with x hx
  rw [hx]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Literal scalar source products pay their exact reserve in the pointwise factorial density. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem scalarDerivativeProduct_readout_density_le {K L r : ℕ}
    (hKL : K + r ≤ L + 1) (hr : 1 ≤ r) (I : DerivativeWord2 r)
    (U : PlaneHk Set.univ (L + 1) E) (V : PlaneHk Set.univ K F)
    (c : Vec 2 → ℝ) (hc : ContDiff ℝ (K : ℕ) c) (T : E →L[ℝ] F)
    (ρ A : ℝ) (hρ : 0 < ρ) (q : Vec 2 → ℝ)
    (hb : ∀ j ≤ K, ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j c x‖ ≤ A * q x)
    (hv : ∀ a, Weighted.planeJetReadoutOperator K a V =ᵐ[volume]
      multiplicationRawJet (fun x => c x • T)
        (Weighted.derivativeSourceOperator hKL I U).toFunction.jet a) :
    ∀ᵐ x ∂volume, planeFactorialDensity ρ V x ≤
      multiplicationDensityBudget K * (A * ‖T‖ * derivativeReserveFactor ρ K (r - 1)) ^ 2 *
        q x ^ 2 * planeGradFactorialDensity ρ U x := by
  have hcb (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) (x : Vec 2) :
      ρ ^ j * ‖orderedCoefficientDerivative (fun y => c y • T) j w x‖ ≤ (A * ‖T‖) * q x := by
    have hh := normalized_scalar_operator_word_le c j (hc.of_le (by exact_mod_cast hj)) T
      ρ (A * q x) hρ.le x (hb j hj x) w
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  filter_upwards [productReadout_density_le (Weighted.derivativeSourceOperator hKL I U) V
    (fun x => c x • T) ρ (A * ‖T‖) hρ.le q hcb hv] with x hx
  have hh := mul_le_mul_of_nonneg_left
    (derivativeSourceOperator_density_le hKL hr I ρ hρ U x)
    (show 0 ≤ multiplicationDensityBudget K * (A * ‖T‖) ^ 2 * q x ^ 2 by
      exact mul_nonneg (mul_nonneg (multiplicationDensityBudget_nonneg K) (sq_nonneg _)) (sq_nonneg _))
  have he : multiplicationDensityBudget K * (A * ‖T‖) ^ 2 * q x ^ 2 *
      ((derivativeReserveFactor ρ K (r - 1)) ^ 2 * planeGradFactorialDensity ρ U x) =
      multiplicationDensityBudget K * (A * ‖T‖ * derivativeReserveFactor ρ K (r - 1)) ^ 2 *
        q x ^ 2 * planeGradFactorialDensity ρ U x := by ring
  exact hx.trans (hh.trans_eq he)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The full finite normalized equation gains its first reserve with drift-independent growth. -/

theorem zerothGradientEnergy_absorb {P E H D C : ℝ} (hD : 0 ≤ D)
    (hH : H = E + D) (he : P + (3 / 4) * D ≤ C * E) :
    P + (1 / 2) * H ≤ (C + 1 / 2) * E := by
  nlinarith

def cellFullZerothGrowth (η Cw : ℝ) (ξ : Fin 2 → ℂ) (k : ℝ) : ℝ :=
  264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 2 * (Cw * fibreNorm ξ + k) + 1 / 2

theorem cellFullZerothGrowth_nonneg (η Cw : ℝ) (hCw : 0 ≤ Cw) (ξ : Fin 2 → ℂ)
    (k : ℝ) (hk : 0 ≤ k) : 0 ≤ cellFullZerothGrowth η Cw ξ k := by
  unfold cellFullZerothGrowth
  exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hCw (fibreNorm_nonneg ξ)) hk))) (by norm_num)

theorem cellFullGalerkin_zeroth_adjacent_energy (N : ℕ)
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (cellGalerkinValue N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG V hv.1 hb t) u))
      (cellGalerkinValue N u) + (1 / 2) * ‖u.val‖ ^ 2 ≤
      cellFullZerothGrowth η Cw ξ k * ‖cellGalerkinValue N u‖ ^ 2 := by
  have he := cellNormalizedGenerator_sharp_garding η Cw hCw G hG hv hw V hb ξ κ t u.val
  have hprice := mul_le_mul_of_nonneg_right
    (show 264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 2 * (Cw * fibreNorm ξ + ‖κ t‖) ≤
      264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 2 * (Cw * fibreNorm ξ + k) by linarith only [hk])
    (sq_nonneg ‖cellGalerkinValue N u‖)
  have hd : 0 ≤ ∑ j : Fin 2, ‖cellDerivativeCLM j u.val‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := zerothGradientEnergy_absorb hd (cellH1_norm_sq u.val) (he.trans hprice)
  have hp := cellGalerkinOperator_pairing N
    (cellGeneratorB ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG V hv.1 hb t) u u
  have hp' : inner ℝ (cellGalerkinValue N (cellGalerkinOperator N
      (cellGeneratorB ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG V hv.1 hb t) u))
      (cellGalerkinValue N u) =
      cellGeneratorForm ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG V hv.1 hb t u.val u.val := hp
  exact (congrArg (fun p : ℝ => 2 * p + (1 / 2) * ‖u.val‖ ^ 2) hp').le.trans hs

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Inverse-mass factorial sums are the integrals of their literal weighted densities. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

omit [Fintype ι] in
theorem planeFactorialDensity_aemeasurable (K : ι → ℕ) (ρ : ℝ)
    (U : ∀ v, PlaneHk Set.univ (K v) (E v)) (v : ι) :
    AEMeasurable (planeFactorialDensity ρ (U v)) volume := by
  unfold planeFactorialDensity
  apply Finset.aemeasurable_fun_sum
  intro a _
  exact aemeasurable_const.mul
    ((planeJetOrder_memLp (Nat.le_of_lt_succ a.1.isLt) (U v) a.2).aestronglyMeasurable.norm.aemeasurable.pow_const 2)

theorem storedChartFactorialEnergy_mass_density (π : ι → ℝ) (hπ : ∀ v, 0 ≤ π v)
    (K : ι → ℕ) (ρ : ℝ) (q : Vec 2 → ℝ) (hqm : AEMeasurable q volume)
    (hq : ∀ x, 0 ≤ q x) (U : ∀ v, PlaneHk Set.univ (K v) (E v)) :
    (∑ v, ENNReal.ofReal ((π v)⁻¹) * Weighted.storedChartFactorialEnergy ρ q (U v)) =
      ∫⁻ x, ENNReal.ofReal (q x * ∑ v, (π v)⁻¹ * planeFactorialDensity ρ (U v) x) := by
  classical
  simp_rw [storedChartFactorialEnergy_density ρ q hqm hq]
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← lintegral_finsetSum' Finset.univ
    (f := fun v x => ENNReal.ofReal ((π v)⁻¹) * ENNReal.ofReal (q x * planeFactorialDensity ρ (U v) x))
    (fun v _ => aemeasurable_const.mul
      ((hqm.mul (planeFactorialDensity_aemeasurable K ρ U v)).ennreal_ofReal))]
  apply lintegral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun v _ =>
    mul_nonneg (hq x) (mul_nonneg (inv_nonneg.mpr (hπ v)) (planeFactorialDensity_nonneg ρ (U v) x)))]
  apply Finset.sum_congr rfl
  intro v _
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hπ v))]
  congr 1
  ring

theorem weightedFactorialNormSq_mass_density (π : ι → ℝ) (hπ : ∀ v, 0 ≤ π v)
    (K : ι → ℕ) (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ)
    (U : ∀ v, PlaneHk Set.univ (K v) (E v)) :
    (∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K v) (U v)) =
      ∫⁻ x, ENNReal.ofReal (Weighted.planeMomentPolynomial n ϖ zc x *
        ∑ v, (π v)⁻¹ * planeFactorialDensity ρ (U v) x) := by
  simp_rw [Weighted.weightedFactorialNormSq_stored_readout]
  apply storedChartFactorialEnergy_mass_density π hπ K ρ
  · have hc : Continuous (Weighted.planeMomentPolynomial n ϖ zc) := by
      unfold Weighted.planeMomentPolynomial
      fun_prop
    exact hc.aemeasurable
  · intro x
    unfold Weighted.planeMomentPolynomial
    positivity

variable [∀ i, FiniteDimensional ℝ (E i)]

theorem weightedGradFactorialNormSq_mass_density (π : ι → ℝ) (hπ : ∀ v, 0 ≤ π v)
    (K : ι → ℕ) (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ)
    (U : ∀ v, PlaneHk Set.univ (K v + 1) (E v)) :
    (∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedGradFactorialNormSq n ϖ zc ρ (K v) (U v)) =
      ∫⁻ x, ENNReal.ofReal (Weighted.planeMomentPolynomial n ϖ zc x *
        ∑ v, (π v)⁻¹ * planeGradFactorialDensity ρ (U v) x) := by
  simp_rw [← planeGradientTensor_weightedFactorialNormSq n ϖ zc ρ]
  rw [weightedFactorialNormSq_mass_density π hπ K n ϖ zc ρ]
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun v => planeGradientTensor_factorialDensity_ae ρ (U v))] with x hx
  simp_rw [hx]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Full normalized finite L2 traces propagate without an unscaled drift price. -/

theorem positiveDissipation_drop {P D C E : ℝ} (hD : 0 ≤ D)
    (he : P + (1 / 2) * D ≤ C * E) : P ≤ C * E := by linarith

theorem cellFullGalerkin_zeroth_propagation (N : ℕ)
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG V hv.1 hb t) (y t))) :
    ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤
      ‖cellGalerkinValue N (y a)‖ ^ 2 * Real.exp (cellFullZerothGrowth η Cw ξ k * (t - a)) := by
  have hC := cellFullZerothGrowth_nonneg η Cw hCw ξ k ((norm_nonneg _).trans (hk a))
  have he := (hy.map (cellGalerkinValue N)).norm_sq_le_gronwall hab
    (cellFullZerothGrowth η Cw ξ k) hC 0 intervalIntegrable_const
    (Filter.Eventually.of_forall (fun _ => by simp only [Pi.zero_apply, le_refl])) (by
      apply Filter.Eventually.of_forall
      intro t
      simp only [Pi.zero_apply, add_zero]
      rw [real_inner_comm]
      exact positiveDissipation_drop (sq_nonneg _) (cellFullGalerkin_zeroth_adjacent_energy N η Cw hCw G hG hv hw V hb ξ κ t k (hk t) (y t)))
  simpa only [Pi.zero_apply, intervalIntegral.integral_zero, add_zero] using he

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The native forcing addition estimate is valid for the literal polynomial
weighted energies, including infinite values. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem native_norm_add_sq_le (u v : E) : ‖u + v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hh := pow_le_pow_left₀ (norm_nonneg (u + v)) (norm_add_le u v) 2
  have hs := sq_nonneg (‖u‖ - ‖v‖)
  nlinarith only [hh, hs]

theorem planeFactorialDensity_add_le {K : ℕ} (ρ : ℝ) (U V : PlaneHk Set.univ K E) :
    ∀ᵐ z ∂volume, planeFactorialDensity ρ (U + V) z ≤
      2 * (planeFactorialDensity ρ U z + planeFactorialDensity ρ V z) := by
  filter_upwards [ae_all_iff.mpr (fun a : JetIndex2 K =>
    planeJetOrder_add_ae (Nat.le_of_lt_succ a.1.isLt) U V a.2)] with z hz
  unfold planeFactorialDensity
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [hz a]
  have hh := mul_le_mul_of_nonneg_left (native_norm_add_sq_le
    (planeJetOrder U a.1.val a.2 z) (planeJetOrder V a.1.val a.2 z))
    (factorialWeight_nonneg ρ a.1.val)
  convert hh using 1
  ring

theorem nativeFactorialDensity_aemeasurable {K : ℕ} (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    AEMeasurable (planeFactorialDensity ρ U) volume := by
  unfold planeFactorialDensity
  apply Finset.aemeasurable_fun_sum
  intro a _
  exact aemeasurable_const.mul
    ((planeJetOrder_memLp (Nat.le_of_lt_succ a.1.isLt) U a.2).aestronglyMeasurable.norm.aemeasurable.pow_const 2)

theorem weightedFactorialNormSq_add_le {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (U V : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc ρ K (U + V) ≤
      2 * (weightedFactorialNormSq n ϖ zc ρ K U + weightedFactorialNormSq n ϖ zc ρ K V) := by
  have hm : AEMeasurable (Weighted.planeMomentPolynomial n ϖ zc) volume := by
    have hc : Continuous (Weighted.planeMomentPolynomial n ϖ zc) := by
      unfold Weighted.planeMomentPolynomial
      fun_prop
    exact hc.aemeasurable
  have hp (z : Vec 2) : 0 ≤ Weighted.planeMomentPolynomial n ϖ zc z := by
    unfold Weighted.planeMomentPolynomial
    positivity
  have hqU : AEMeasurable (fun z => ENNReal.ofReal
      (Weighted.planeMomentPolynomial n ϖ zc z * planeFactorialDensity ρ U z)) volume :=
    (hm.mul (nativeFactorialDensity_aemeasurable ρ U)).ennreal_ofReal
  simp_rw [weightedFactorialNormSq_density]
  rw [← lintegral_add_left' hqU _, ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply lintegral_mono_ae
  filter_upwards [planeFactorialDensity_add_le ρ U V] with z hz
  rw [← ENNReal.ofReal_add (mul_nonneg (hp z) (planeFactorialDensity_nonneg ρ U z))
    (mul_nonneg (hp z) (planeFactorialDensity_nonneg ρ V z))]
  conv_rhs => lhs; rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left hz (hp z)
  convert hh using 1
  ring

theorem integrated_weightedFactorialNormSq_add_le [FiniteDimensional ℝ E] {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U V : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ) :
    (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (U t + V t) ∂μ) ≤
      2 * ((∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (U t) ∂μ) +
        ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (V t) ∂μ) := by
  have hm := Weighted.weightedFactorialNormSq_time_aemeasurable n ϖ zc ρ μ U hU
  rw [← lintegral_add_left' hm _, ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  exact lintegral_mono (fun t => weightedFactorialNormSq_add_le n ϖ zc ρ (U t) (V t))

theorem integrated_weightedFactorialNormSq_add_ne_top [FiniteDimensional ℝ E] {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U V : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (heU : (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (U t) ∂μ) ≠ ⊤)
    (heV : (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (V t) ∂μ) ≠ ⊤) :
    (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (U t + V t) ∂μ) ≠ ⊤ := by
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨heU, heV⟩))
    (integrated_weightedFactorialNormSq_add_le n ϖ zc ρ μ U V hU)
end

/-! Native negation preserves the literal polynomial factorial energy. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetOrder_neg_ae {K j : ℕ} (hj : j ≤ K)
    (U : PlaneHk Set.univ K E) (w : DerivativeWord2 j) :
    planeJetOrder (-U) j w =ᵐ[volume] (fun z => -planeJetOrder U j w z) := by
  filter_upwards [planeJetOrder_sub_ae hj (0 : PlaneHk Set.univ K E) U w,
    planeJetOrder_zero_ae (E := E) hj w] with z hz hzero
  simpa only [zero_sub, hzero] using hz

theorem planeFactorialDensity_neg_ae {K : ℕ} (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    planeFactorialDensity ρ (-U) =ᵐ[volume] planeFactorialDensity ρ U := by
  filter_upwards [ae_all_iff.mpr (fun a : JetIndex2 K =>
    planeJetOrder_neg_ae (Nat.le_of_lt_succ a.1.isLt) U a.2)] with z hz
  simp only [planeFactorialDensity, hz, norm_neg]

theorem weightedFactorialNormSq_neg {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc ρ K (-U) = weightedFactorialNormSq n ϖ zc ρ K U := by
  rw [weightedFactorialNormSq_density, weightedFactorialNormSq_density]
  apply lintegral_congr_ae
  filter_upwards [planeFactorialDensity_neg_ae ρ U] with z hz
  rw [hz]

theorem weightedFactorialNormSq_sub_le {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (U V : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc ρ K (U - V) ≤
      2 * (weightedFactorialNormSq n ϖ zc ρ K U + weightedFactorialNormSq n ϖ zc ρ K V) := by
  simpa only [sub_eq_add_neg, weightedFactorialNormSq_neg] using
    weightedFactorialNormSq_add_le n ϖ zc ρ U (-V)
end

/-! Native weighted Sobolev energy transfer under smooth spatial renewal. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeSobolev_weighted_pullback {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (W W' : Vec 2 → ℝ) (hWm : AEMeasurable W volume) (hW'm : AEMeasurable W' volume)
    (hW0 : ∀ z, 0 ≤ W z) (hW'0 : ∀ z, 0 ≤ W' z)
    (C : ℝ) (hC : 0 ≤ C) (hW : ∀ z, W' z ≤ C * W (X z)) :
    Weighted.storedChartFactorialEnergy r W' V ≤
      ENNReal.ofReal (pullbackSquareBudget B K * C) *
        Weighted.storedChartFactorialEnergy r W U := by
  have hB : 0 ≤ pullbackSquareBudget B K := by
    unfold pullbackSquareBudget pullbackSquareOrderBudget
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  rw [storedChartFactorialEnergy_density r W' hW'm hW'0,
    storedChartFactorialEnergy_density r W hWm hW0, ENNReal.ofReal_mul hB, mul_assoc]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (pullbackSquareBudget B K *
        (W' z * planeFactorialDensity r U (X z))) := by
      apply lintegral_mono_ae
      filter_upwards [planeSobolev_pullback_density_bound U V X hX hμ B hb hv r hr hr1] with z hz
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hz (hW'0 z)
    _ = ENNReal.ofReal (pullbackSquareBudget B K) *
        ∫⁻ z, ENNReal.ofReal (W' z * planeFactorialDensity r U (X z)) := by
      simp_rw [ENNReal.ofReal_mul hB]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right
      (weighted_pullback_nonnegative_integral_le X hμ W W' (planeFactorialDensity r U)
        (planeFactorialDensity_nonneg r U) C hC hW) _
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! Polynomially growing smooth charts transport actual weighted native Sobolev data. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weighted_plane_pullback_exists {K : ℕ} (U : PlaneHk Set.univ K E)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (qout qin P : Vec 2 → ℝ) (hqout : Continuous qout) (hqin : Continuous qin)
    (hout : ∀ z, 1 ≤ qout z) (hin : ∀ z, 1 ≤ qin z)
    (B : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ z, 1 ≤ P z) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) z‖ ≤ B j * P z)
    (hweight : ∀ z, qout z * P z ^ K ≤ L * qin (X z))
    (hw : JetMemL2On Set.univ (fun a x => qin x • U.toFunction.jet a x)) :
    ∃ V : PlaneHk Set.univ K E, planeValue V =ᵐ[volume] planeValue U ∘ X ∧
      ∀ a : JetIndex2 K, MemLp (fun x => qout x • V.toFunction.jet a x) 2 volume := by
  obtain ⟨UN, fN, hs, hv, hj⟩ := exists_weighted_compact_smooth_approximation U qin hqin hw
  choose hm hm0 ht using hj
  let RN (n : ℕ) : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))) :=
    WithLp.toLp 2 (fun a => (hm a n).toLp (fun x => qin x • (UN n).toFunction.jet a x))
  let R : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))) :=
    WithLp.toLp 2 (fun a => (hm0 a).toLp (fun x => qin x • U.toFunction.jet a x))
  have hRN (n : ℕ) (a : JetIndex2 K) :
      RN n a =ᵐ[volume] (fun x => qin x • (UN n).toFunction.jet a x) := (hm a n).coeFn_toLp
  have hR (a : JetIndex2 K) : R a =ᵐ[volume] (fun x => qin x • U.toFunction.jet a x) :=
    (hm0 a).coeFn_toLp
  have htR : Tendsto RN atTop (𝓝 R) := by
    have htpi := tendsto_pi_nhds.mpr ht
    exact ((PiLp.continuous_toLp 2
      (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2)))).tendsto _).comp htpi
  have htU := weightedJetArray_tendsto_native UN U qin hin RN R hRN hR htR
  exact weighted_smooth_pullback_sequence_limit U UN fN htU hs hv X hX hμ qout qin P hqout
    hout (fun z => zero_le_one.trans (hin z)) B L hL hP hB hb hweight RN hRN htR.cauchySeq

theorem weighted_plane_pullback_memLp {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X)
    (qout qin P : Vec 2 → ℝ) (hqout : Continuous qout) (hqin : Continuous qin)
    (hout : ∀ z, 1 ≤ qout z) (hin : ∀ z, 1 ≤ qin z)
    (B : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ z, 1 ≤ P z) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) z‖ ≤ B j * P z)
    (hweight : ∀ z, qout z * P z ^ K ≤ L * qin (X z))
    (hw : JetMemL2On Set.univ (fun a x => qin x • U.toFunction.jet a x)) :
    ∀ a : JetIndex2 K, MemLp (fun x => qout x • V.toFunction.jet a x) 2 volume := by
  obtain ⟨W, hwv, hm⟩ := weighted_plane_pullback_exists U X hX hμ qout qin P hqout hqin
    hout hin B L hL hP hB hb hweight hw
  have he : W = V := planeHk_eq_of_planeValue_ae (hwv.trans hv.symm)
  simpa only [he] using hm

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The actual unscaled transport entry acts on every reserved native carrier. -/

 def interiorPulseDriftEntryNativeCLM (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k))
    (i : Fin 2) (t : ℝ) : TorusHk K ℂ →L[ℝ] TorusHk K ℂ :=
  KernelEnergy.torusMultiplierCLM (interiorPulseDriftEntryCoefficient α q Λ m ζ ν y₀ k i t)
    (interiorPulseDriftEntryCoefficient_contDiff ν y₀ hk i t K)
    (interiorPulseDriftEntryCoefficient_periodic α q Λ m ζ ν y₀ k hv i t)
    (fun l => interiorPulseDriftEntryJetPrice α q Λ m ν l.val)
    (fun l x => interiorPulseDriftEntryCoefficient_array_bound hΛ hζ ν y₀ hk i t l.val x)
    1 (by norm_num)

 def interiorPulseDriftEntryNativePrice (α q : ℝ) (Λ m : ℕ) (ν : ℝ) (K : ℕ) : ℝ :=
  (∑ l : Fin (K + 1), factorialRootWeight 1 l.val *
      interiorPulseDriftEntryJetPrice α q Λ m ν l.val) *
    Real.sqrt (factorialWeightMax 1 K) / Real.sqrt (factorialWeightMin 1 K)

 theorem interiorPulseDriftEntryNativeCLM_norm_bound (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k))
    (i : Fin 2) (t : ℝ) (U : TorusHk K ℂ) :
    ‖interiorPulseDriftEntryNativeCLM K hΛ hζ ν y₀ hk hv i t U‖ ≤
      interiorPulseDriftEntryNativePrice α q Λ m ν K * ‖U‖ :=
  KernelEnergy.torusMultiplier_norm_bound _ _ _ _ _ 1 (by norm_num) U

 theorem interiorPulseDriftEntryNativeCLM_value (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ k t x j ^ 2 ≤ V ^ 2)
    (i : Fin 2) (t : ℝ) (U : TorusHk K ℂ) :
    torusHkValueCLM (interiorPulseDriftEntryNativeCLM K hΛ hζ ν y₀ hk hv i t U) =
      cellDriftEntryCLM ⟨0, interiorSinglePulseDrift α q Λ ζ m ν y₀ k, 0, 0⟩ V hv.1 hb t i
        (torusHkValueCLM U) := by
  apply Lp.ext
  have hl := torusMulCoefficient_value_ae U
    (interiorPulseDriftEntryCoefficient α q Λ m ζ ν y₀ k i t)
    (interiorPulseDriftEntryCoefficient_contDiff ν y₀ hk i t K)
    (interiorPulseDriftEntryCoefficient_periodic α q Λ m ζ ν y₀ k hv i t)
    (fun l x => interiorPulseDriftEntryCoefficient_array_bound hΛ hζ ν y₀ hk i t l.val x)
  have hr := cellDriftEntryCLM_ae ⟨0, interiorSinglePulseDrift α q Λ ζ m ν y₀ k, 0, 0⟩ V hv.1 hb t i
    (torusHkValueCLM U)
  filter_upwards [hl, hr] with x hl hr
  exact hl.trans hr.symm

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Adding an actual L2 scalar source adds its pivot Riesz derivative. -/

theorem cellDualDerivative_add_scalar_source
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (src f : ComplexCellL2) :
    cellDualDerivative C hG V hv hb t u (src + f) 0 =
      cellDualDerivative C hG V hv hb t u src 0 + cellPivotDualCLM f := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_add_left, cellDualDerivative_pairing, cellDualDerivative_pairing,
    cellSourceFunctional_scalar_only, cellSourceFunctional_scalar_only, inner_add_left]
  change _ = _ + inner ℝ ((torusHkValueCLM (E := ℂ) (K := 1)).adjoint f) z
  rw [ContinuousLinearMap.adjoint_inner_left, add_assoc]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The geometry cover supplies the actual and frozen metrics for the constructed adjoint weights. -/

def geometryCover_adjointChartWeights {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream (Φ (m - 1)))
    {ν B T ta ρs g g0 a B₀ lam Cb CT : ℝ} {qJ Kmax : ℕ} {CG : ℕ → ℝ}
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsGeometryCover α q Λ m ζ Φ hφ ν B T ta ρs g g0 a B₀ lam Cb CT qJ Kmax CG l₀ P y₀)
    (hg0 : g0 ≤ 1 / 4) {C : ℝ} (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m)
    (i : Fin P) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) ∨
      G = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0) (N : ℕ) :
    ChartWeights G (ocCellDrift α q Λ ζ m ν
      (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
      (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
      (ocEpsilon q Λ m / Real.sqrt (B * T)) 0 N (adjointWeightConstant C K) := by
  let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i
  have hGs : ∀ j k : Fin 2, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => G p.1 p.2 j k) :=
    fun j k => cellMetricChoice_joint_contDiff α q Λ m hφ (l₀ + i) ν yc G hG j k
  have hsym : ∀ t z, (G t z).IsSymm :=
    cellMetricChoice_symmetric α q Λ m hφ (l₀ + i) ν yc G hG
  have hnear : IsMetricNearIdentityOn
      (Set.Icc (ta / ocEll q Λ m ν ^ 2) (ta / ocEll q Λ m ν ^ 2 + T / ocEll q Λ m ν ^ 2)) G g := by
    rw [← add_div]
    exact cellMetricChoice_nearIdentityOn α q Λ m hφ (l₀ + i) ν yc G hG _ g (cov.metric_near i)
  exact adjointChartWeights hΛ hζ cov.pos.1 cov.pos.2.1 cov.pos.2.2.1 hC he cov.ellT K hK hb
    (by simpa only [neg_mul] using cov.dur) yc G hGs hsym g (cov.g_range.2.trans hg0)
    (ta / ocEll q Λ m ν ^ 2) hnear N

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
namespace AVRegularity.CycleWords

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_storedWord_clipped_value_energy_bound {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (Mv : ℝ) (hMv : 0 ≤ Mv) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (hCell : IsCellMetric G)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (Q : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hH : MemLp H 2 (volume.restrict (Icc a b)))
    (hQ : MemLp Q 2 (volume.restrict (Icc a b))) (α : JetIndex2 K)
    (hcurve : PlaneWeakHilbertCurve a b
      (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t))))
    (B : ℝ) (hB : 0 < B) :
    let u := fun t => planeJetReadoutOperator K α (U t)
    let slice := fun t => planeWordH1SliceOperator K α (W t)
    let T := planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
    let D := cellMetricIntervalDiffusion a b hab G
      (fun t ht k j => (hG t ht k j).continuous) hCell
    let F := fun t => planeJetFluxOperator K α (Q t) - D t (planeH1GradientOperator (slice t))
    let R := fun t => planeJetReadoutOperator K α (H t) + T t (planeH1GradientOperator (slice t))
    ∀ t ∈ Icc a b,
      (∫ x, clipWeight B (C.W m t x) * ‖u t x‖ ^ 2) +
      (∫ s in a..t, ∫ x, (1 / 2) * clipWeight B (C.W m s x) *
        ‖(WithLp.toLp 2 (fun k => planeH1GradientOperator (slice s) k x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
      ((∫ x, clipWeight B (C.W m a x) * ‖u a x‖ ^ 2) +
        8 * (∫ s in a..b, ∫ x, clipWeight B (C.W m s x) *
          ‖(WithLp.toLp 2 (fun k => F s k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
        2 * (∫ s in a..b, ∫ x, clipWeight B (C.W m s x) * (‖R s x‖ * ‖u s x‖))) *
        Real.exp (18 * C.lam m * (t - a)) := by
  dsimp only
  have hacts := cellMetric_planeIntervalActions_memLp a b hab v (fun t ht => (hv t ht).continuous)
    hvm Mv hvb G (fun t ht k j => (hG t ht k j).continuous) hGm
    hCell (fun t => planeWordH1SliceOperator K α (W t)) hcurve.state
  have hres := orderedSourceResidual_memLp H Q hH hQ α _ _ hacts.1 hacts.2
  exact cellMetric_planeWeak_clipped_value_energy_gronwall a b hab v hv hdiv Mv hMv hvb G hG hCell hGs t₀ S ϖ zc N m Cw C hm ha hb _ _ _ _
    (planeSourceCurve_scalar_residual _ _ _ _ _ _ hcurve) B hB hres.2 hres.1

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual universal transport prices also bound every single-pulse native multiplier. -/

 theorem interiorPulseDriftEntryJetPrice_polynomial
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (n : ℕ) :
    interiorPulseDriftEntryJetPrice α q Λ m ν n ≤
      constructedEntryUniversalJetPrice n * peFactor (ν / ocMeanFlux α q Λ ζ m ν) := by
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (constructed_amplitude_polynomial_price hΛ hζ hν hr)
      (by positivity : 0 ≤ (2 * Real.pi) ^ n))
    (by positivity : 0 ≤ (Fintype.card (DerivativeWord2 n) : ℝ) * ‖realScalarMultiplierMap‖)
  exact h.trans_eq (by
    unfold constructedEntryUniversalJetPrice constructedSpatialJetPrice
    simp only [pow_zero, mul_one]
    ring)

 theorem interiorPulseDriftEntryNativePrice_polynomial
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (K : ℕ) :
    interiorPulseDriftEntryNativePrice α q Λ m ν K ≤
      constructedEntryUniversalNativePrice K * peFactor (ν / ocMeanFlux α q Λ ζ m ν) := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (K + 1))))
    (fun l _ => mul_le_mul_of_nonneg_left
      (interiorPulseDriftEntryJetPrice_polynomial hΛ hζ hν hr l.val)
      (by unfold factorialRootWeight; positivity : 0 ≤ factorialRootWeight 1 l.val))
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (factorialWeightMax 1 K)))
    (Real.sqrt_nonneg (factorialWeightMin 1 K))
  exact h.trans_eq (by
    unfold constructedEntryUniversalNativePrice
    simp only [← mul_assoc, ← Finset.sum_mul]
    ring)

 theorem interiorPulseDriftEntryNativeCLM_polynomial_bound (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k))
    (i : Fin 2) (t : ℝ) (U : TorusHk K ℂ) :
    ‖interiorPulseDriftEntryNativeCLM K hΛ hζ ν y₀ hk hv i t U‖ ≤
      (constructedEntryUniversalNativePrice K * peFactor (ν / ocMeanFlux α q Λ ζ m ν)) * ‖U‖ :=
  (interiorPulseDriftEntryNativeCLM_norm_bound K hΛ hζ ν y₀ hk hv i t U).trans
    (mul_le_mul_of_nonneg_right (interiorPulseDriftEntryNativePrice_polynomial hΛ hζ hν hr K) (norm_nonneg U))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleWords

/-! Construction-uniform weights for every actual and frozen geometry chart. -/

theorem geometryCover_uniform_adjoint_weights {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Cw : ℕ → ℝ, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ) (M : ℕ) (κ : ℕ → ℝ),
      IsOCBandChain α q Λ ζ M κ →
    ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ (ν B : ℝ), κ m = ν → κ (m - 1) = B →
    ∀ (hφ : IsAdmissibleStream (Φ (m - 1)))
      (T ta ρs g g0 a B₀ lam Cb CT : ℝ) (qJ Kmax : ℕ) (CG : ℕ → ℝ)
      (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2),
      IsGeometryCover α q Λ m ζ Φ hφ ν B T ta ρs g g0 a B₀ lam Cb CT qJ Kmax CG l₀ P y₀ →
      g0 ≤ 1 / 4 →
    ∀ (i : Fin P) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ),
      (G = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) ∨
       G = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0) →
    ∀ N : ℕ, Nonempty (ChartWeights G (ocCellDrift α q Λ ζ m ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
      (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
      (ocEpsilon q Λ m / Real.sqrt (B * T)) 0 N Cw) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, he⟩ := bandChain_enhancement_bound hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨K, hK, hb⟩ := cutoff_derivative_uniform_bound
  refine ⟨adjointWeightConstant C K, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ Φ M κ hκ m hm hmM ν B hν hB hφ T ta ρs g g0 a B₀ lam Cb CT
    qJ Kmax CG l₀ P y₀ cov hg0 i G hG N
  have hΛ1 : 1 ≤ Λ := by omega
  have hen := he Λ hΛ M (by omega) κ hκ m hm hmM
  rw [hν, hB] at hen
  exact ⟨geometryCover_adjointChartWeights hΛ1 hζ hφ cov hg0
    (le_trans (by norm_num) hC) hen K hK.le (hb α q Λ m hΛ1) i G hG N⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual preceding word source is the committed admissible Taylor-letter flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainPreviousFlux_eq_weighted (letters : Fin N → CycleLetter ι h D)
    (X0 : Vec 2) (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) :
    wordChainPreviousFlux letters X0 δ κ U i t z =
      Weighted.wordPredecessorFlux letters κ X0 δ U i t z := rfl

theorem wordChainPreviousFlux_succ (letters : Fin N → CycleLetter ι h D)
    (X0 : Vec 2) (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (j : Fin N) (x : ι) (t : ℝ) (z : Vec 2) :
    wordChainPreviousFlux letters X0 δ κ U (j.succ, x) t z =
      Weighted.letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
        (j.succ, x) (fun u => (j.castSucc, u)) x (if (letters j).positive then 1 else 0)
        X0 δ (fun u => U (j.castSucc, u)) t z := by
  rw [wordChainPreviousFlux_eq_weighted]
  exact Weighted.wordPredecessorFlux_succ letters κ X0 δ U j x t z

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier Set
namespace AVRegularity.CycleWords

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_storedWord_residual_time_integrable {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (Mv : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (hCell : IsCellMetric G)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (Q : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hH : MemLp H 2 (volume.restrict (Icc a b)))
    (hQ : MemLp Q 2 (volume.restrict (Icc a b))) 
    (hcurve : ∀ α : JetIndex2 K, PlaneWeakHilbertCurve a b
      (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t))))
    (B : ℝ) (hB : 0 < B) (α : JetIndex2 K) :
    let slice := fun t => planeWordH1SliceOperator K α (W t)
    let T := planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
    let D := cellMetricIntervalDiffusion a b hab G
      (fun t ht k j => (hG t ht k j).continuous) hCell
    let L := fun t => planeJetFluxOperator K α (Q t) - D t (planeH1GradientOperator (slice t))
    let R := fun t => planeJetReadoutOperator K α (H t) + T t (planeH1GradientOperator (slice t))
    Integrable (fun t => ∫ x, clipWeight B (C.W m t x) *
      ‖(WithLp.toLp 2 (fun k : Fin 2 => L t k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)
      (volume.restrict (Icc a b)) ∧
    Integrable (fun t => ∫ x, clipWeight B (C.W m t x) *
      (‖R t x‖ * ‖planeJetReadoutOperator K α (U t) x‖))
      (volume.restrict (Icc a b)) := by
  dsimp only
  have hc := hcurve α
  have hacts := cellMetric_planeIntervalActions_memLp a b hab v (fun t ht => (hv t ht).continuous)
    hvm Mv hvb G (fun t ht k j => (hG t ht k j).continuous) hGm
    hCell (fun t => planeWordH1SliceOperator K α (W t)) hc.state
  have hres := orderedSourceResidual_memLp H Q hH hQ α _ _ hacts.1 hacts.2
  have hu : MemLp (fun t => planeJetReadoutOperator K α (U t)) 2
      (volume.restrict (Icc a b)) :=
    (memLp_congr_ae hc.agrees).2 ((planeHkValueOperator (E := E) 1).comp_memLp' hc.state)
  obtain ⟨hqc, hqm, hqb⟩ := chartWeights_clipped_time_coefficient C m hm B hB
  exact ⟨chartWeights_clipped_finite_time_integrable (E := E) C m hm B hB _ _ hres.2,
    weighted_spatial_value_product_time_integrable _ hqc hqm hB.le hqb _ _ hres.1 hu⟩

end AVRegularity.CycleWords
end
end
