-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.External.FourierCarrierParseval
import AVRegularity.EntryWeak.SourceParameterPeriodicity
import AVRegularity.CycleJoint.TransitionAffineSampling
public import AVRegularity.Definitions.Iteration.CascadeStatement
public import AVRegularity.EntryWeak.ScheduledAnchorDistance
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
namespace AVRegularity.IterationPassage

/-! The half-order interpolation constant and the paid physical accuracy are scalar algebra. -/

theorem sqrt_product_paid (K C₀ C₁ x A : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hx : 0 ≤ x) (hA : 0 ≤ A) :
    K * Real.sqrt (C₀ * x * A) * Real.sqrt (C₁ * A) =
      (K * Real.sqrt C₀ * Real.sqrt C₁) * Real.sqrt x * A := by
  rw [Real.sqrt_mul (mul_nonneg hC₀ hx), Real.sqrt_mul hC₀, Real.sqrt_mul hC₁]
  calc
    _ = ((K * Real.sqrt C₀ * Real.sqrt C₁) * Real.sqrt x) * (Real.sqrt A * Real.sqrt A) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hA]

theorem sqrt_rpow_paid (E Q : ℝ) (hE : 0 ≤ E) :
    Real.sqrt (E ^ Q) = E ^ (Q / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hE]
  congr 1
  ring

/-! Positive mass weights preserve interpolation without counting components. -/

theorem weighted_product_sum_le {ι : Type*} [Fintype ι]
    (μ a b : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∑ i, μ i * a i * b i ≤
      Real.sqrt (∑ i, μ i * a i ^ 2) * Real.sqrt (∑ i, μ i * b i ^ 2) := by
  have hs : (∑ i, μ i * a i * b i) ^ 2 ≤
      (∑ i, μ i * a i ^ 2) * ∑ i, μ i * b i ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => mul_nonneg (hμ i) (sq_nonneg _))
      (fun i _ => mul_nonneg (hμ i) (sq_nonneg _))
    intro i _
    exact le_of_eq (by ring)
  have hn : 0 ≤ ∑ i, μ i * a i * b i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hμ i) (ha i)) (hb i)
  have hh := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq hn, Real.sqrt_mul
    (Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _))] at hh
  exact hh

end AVRegularity.IterationPassage
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.IterationPassage

/-! Subtraction and restriction retain the value class of the actual physical error. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torus_sub_value_ae {K : ℕ} (f g : TorusHk K E) :
    (f - g).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => f.toFunction.jet (valueIndex2 K) x - g.toFunction.jet (valueIndex2 K) x := by
  filter_upwards [periodicJetRepresentative_ae (f - g).val (valueIndex2 K),
    periodicJetRepresentative_ae f.val (valueIndex2 K),
    periodicJetRepresentative_ae g.val (valueIndex2 K),
    Lp.coeFn_sub (f.val (valueIndex2 K)) (g.val (valueIndex2 K))] with x hsub hf hg hLp
  change periodicJetRepresentative (f - g).val (valueIndex2 K) x =
    periodicJetRepresentative f.val (valueIndex2 K) x - periodicJetRepresentative g.val (valueIndex2 K) x
  rw [hf, hg, hsub]
  exact hLp

theorem torus_truncate_value_ae {K L : ℕ} (hKL : K ≤ L) (f : TorusHk L E) :
    (truncateTorusHk hKL f).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      f.toFunction.jet (valueIndex2 L) := by
  filter_upwards [periodicJetRepresentative_ae (truncateTorusHk hKL f).val (valueIndex2 K),
    periodicJetRepresentative_ae f.val (valueIndex2 L)] with x hlo hhi
  exact hlo.trans hhi.symm

theorem actual_error_carrier_value {K L : ℕ} (hKL : K ≤ L) (f g : TorusHk L E)
    (u v : Vec 2 → E)
    (hf : f.toFunction.jet (valueIndex2 L) =ᵐ[volume.restrict AVenhance.unitCube] u)
    (hg : g.toFunction.jet (valueIndex2 L) =ᵐ[volume.restrict AVenhance.unitCube] v) :
    (truncateTorusHk hKL (f - g)).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => u x - v x := by
  apply (torus_truncate_value_ae hKL (f - g)).trans
  apply (torus_sub_value_ae f g).trans
  filter_upwards [hf, hg] with x hfx hgx
  rw [hfx, hgx]
end

/-! Exact cancellation of the radius in the half-order factorial comparison. -/

section
def doubledFactorialCost (j : ℕ) : ℝ := ((j + j).factorial : ℝ) / (j.factorial : ℝ) ^ 2

theorem doubledFactorialCost_nonneg (j : ℕ) : 0 ≤ doubledFactorialCost j := by
  unfold doubledFactorialCost
  positivity

theorem factorialWeight_eq_double_root (ρ : ℝ) (j : ℕ) :
    factorialWeight ρ j = doubledFactorialCost j * factorialRootWeight ρ (j + j) := by
  unfold factorialWeight doubledFactorialCost factorialRootWeight
  rw [show 2 * j = j + j by omega]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {μ : Measure (Vec 2)} {K : ℕ}

theorem factorial_component_sq_le (ρ : ℝ) (D : JetL2 μ K E) (a : JetIndex2 K) :
    factorialWeight ρ a.1.val * ‖D a‖ ^ 2 ≤ factorialNormSq ρ D := by
  have hi : ‖D a‖ ^ 2 ≤ derivativeNormSq D a.1 :=
    Finset.single_le_sum (fun w _ => sq_nonneg ‖D ⟨a.1, w⟩‖) (Finset.mem_univ a.2)
  exact (mul_le_mul_of_nonneg_left hi (factorialWeight_nonneg ρ _)).trans
    (Finset.single_le_sum (fun j _ => mul_nonneg (factorialWeight_nonneg ρ _) (derivativeNormSq_nonneg D j))
      (Finset.mem_univ a.1))

theorem factorial_root_component_le (ρ : ℝ) (hρ : 0 ≤ ρ) (D : JetL2 μ K E) (a : JetIndex2 K) :
    factorialRootWeight ρ a.1.val * ‖D a‖ ≤ Real.sqrt (factorialNormSq ρ D) := by
  have hs : (factorialRootWeight ρ a.1.val * ‖D a‖) ^ 2 ≤
      (Real.sqrt (factorialNormSq ρ D)) ^ 2 := by
    rw [mul_pow, factorialRootWeight_sq, Real.sq_sqrt (factorialNormSq_nonneg _ _)]
    exact factorial_component_sq_le ρ D a
  exact (sq_le_sq₀ (by unfold factorialRootWeight; positivity) (Real.sqrt_nonneg _)).mp hs
end

end AVRegularity.IterationPassage
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVenhance.Infra.Heat
namespace AVRegularity.IterationPassage

/-! Exact Parseval norms for the existing real ordered-jet Fourier rows. -/

local instance fourierJetNormUnitAddCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance fourierJetNormUnitAddCircleHaarMeasure : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance fourierJetNormUnitAddCircleProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem realJetFourier_norm_eq (K : ℕ) (f : TorusHk K ℝ) (a : JetIndex2 K) :
    ‖realJetFourier K f a‖ = ‖f.val a‖ := by
  have hp := AVRegularity.External.torusJetComponentParseval f a
  have hn := lp.norm_rpow_eq_tsum (show 0 < (2 : ENNReal).toReal by norm_num)
    (realJetFourier K f a)
  have he (k : Frequency) : ‖realJetFourier K f a k‖ ^ 2 =
      ‖UnitAddTorus.mFourierCoeff (AVRegularity.External.torusJetComponentL2 f a) k‖ ^ 2 :=
    congrArg (fun z : ℂ => ‖z‖ ^ 2) (UnitAddTorus.mFourierBasis_repr _ k)
  have hs : ‖realJetFourier K f a‖ ^ 2 = ‖f.val a‖ ^ 2 := by
    calc
      _ = ∑' k : Frequency, ‖realJetFourier K f a k‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hn
      _ = _ := (tsum_congr he).trans hp.tsum_eq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

end AVRegularity.IterationPassage
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVenhance.Infra.Heat
namespace AVRegularity.IterationPassage

/-! Cauchy--Schwarz between the value and doubled derivative controls each actual weak jet. -/

local instance orderedJetInterpolationUnitAddCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance orderedJetInterpolationUnitAddCircleHaarMeasure : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance orderedJetInterpolationUnitAddCircleProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem realJetFourier_double_word_norm (K j : ℕ) (hj : j + j ≤ K)
    (f : TorusHk K ℝ) (w : DerivativeWord2 j) (k : Frequency) :
    ‖realJetFourier K f ⟨⟨j, by omega⟩, w⟩ k‖ ^ 2 =
      ‖realJetFourier K f (valueIndex2 K) k‖ *
        ‖realJetFourier K f ⟨⟨j + j, by omega⟩, Fin.append w w⟩ k‖ := by
  rw [realJetFourier_word_norm K f j (by omega), realJetFourier_word_norm K f (j + j) hj]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, pow_add]
  ring

theorem ordered_jet_half_interpolation (K j : ℕ) (hj : j + j ≤ K)
    (f : TorusHk K ℝ) (w : DerivativeWord2 j) :
    ‖f.val ⟨⟨j, by omega⟩, w⟩‖ ^ 2 ≤ ‖f.val (valueIndex2 K)‖ *
      ‖f.val ⟨⟨j + j, by omega⟩, Fin.append w w⟩‖ := by
  let a : JetIndex2 K := ⟨⟨j, by omega⟩, w⟩
  let d : JetIndex2 K := ⟨⟨j + j, by omega⟩, Fin.append w w⟩
  have hparse := AVRegularity.External.torusJetComponentParseval f a
  have he : (fun k : Frequency =>
      ‖UnitAddTorus.mFourierCoeff (AVRegularity.External.torusJetComponentL2 f a) k‖ ^ 2) =
      fun k => ‖realJetFourier K f (valueIndex2 K) k‖ * ‖realJetFourier K f d k‖ := by
    funext k
    rw [← UnitAddTorus.mFourierBasis_repr]
    exact realJetFourier_double_word_norm K j hj f w k
  rw [he] at hparse
  have hc := lp.tsum_mul_le_mul_norm'
    (show (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal by
      simpa using Real.HolderConjugate.two_two)
    (realJetFourier K f (valueIndex2 K)) (realJetFourier K f d)
  rw [hparse.tsum_eq, realJetFourier_norm_eq, realJetFourier_norm_eq] at hc
  exact hc

end AVRegularity.IterationPassage
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.IterationPassage

/-! Radius-independent half-order interpolation for the actual scalar torus factorial norm. -/

def factorialHalfCost (J : ℕ) : ℝ :=
  ∑ j : Fin (J + 1), ∑ _w : DerivativeWord2 j.val, doubledFactorialCost j.val

theorem factorialHalfCost_nonneg (J : ℕ) : 0 ≤ factorialHalfCost J :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => doubledFactorialCost_nonneg j.val

theorem factorial_ordered_half_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (K j : ℕ) (hj : j + j ≤ K)
    (f : TorusHk K ℝ) (w : DerivativeWord2 j) :
    factorialWeight ρ j * ‖f.val ⟨⟨j, by omega⟩, w⟩‖ ^ 2 ≤
      doubledFactorialCost j * ‖f.val (valueIndex2 K)‖ * Real.sqrt (factorialNormSq ρ f.val) := by
  have hi := ordered_jet_half_interpolation K j hj f w
  have hw := factorial_root_component_le ρ hρ f.val
    (⟨⟨j + j, by omega⟩, Fin.append w w⟩ : JetIndex2 K)
  calc
    _ ≤ factorialWeight ρ j * (‖f.val (valueIndex2 K)‖ *
        ‖f.val ⟨⟨j + j, by omega⟩, Fin.append w w⟩‖) :=
      mul_le_mul_of_nonneg_left hi (factorialWeight_nonneg ρ j)
    _ = (doubledFactorialCost j * ‖f.val (valueIndex2 K)‖) *
        (factorialRootWeight ρ (j + j) * ‖f.val ⟨⟨j + j, by omega⟩, Fin.append w w⟩‖) := by
      rw [factorialWeight_eq_double_root]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw
      (mul_nonneg (doubledFactorialCost_nonneg j) (norm_nonneg _))

theorem factorial_half_square_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (J : ℕ) (f : TorusHk (2 * J) ℝ) :
    factorialNormSq ρ (truncateTorusHk (show J ≤ 2 * J by omega) f).val ≤
      factorialHalfCost J * ‖f.val (valueIndex2 (2 * J))‖ * Real.sqrt (factorialNormSq ρ f.val) := by
  unfold factorialNormSq derivativeNormSq
  calc
    _ ≤ ∑ j : Fin (J + 1), ∑ _w : DerivativeWord2 j.val,
        doubledFactorialCost j.val * ‖f.val (valueIndex2 (2 * J))‖ *
          Real.sqrt (factorialNormSq ρ f.val) := by
      apply Finset.sum_le_sum
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro w _
      exact factorial_ordered_half_bound ρ hρ (2 * J) j.val (by have := j.isLt; omega) f w
    _ = _ := by
      simp only [factorialHalfCost, Finset.sum_mul]
      rfl

/-! Half-order interpolation in the literal mass-weighted factorial norm. -/

section
variable {ι : Type*} [Fintype ι]

theorem factorial_truncate_zero_eq (ρ : ℝ) {K : ℕ} (f : TorusHk K ℝ) :
    factorialNormSq ρ (truncateTorusHk (Nat.zero_le K) f).val = ‖f.val (valueIndex2 K)‖ ^ 2 := by
  rw [AVRegularity.CycleJointProofs.factorialNormSq_order_zero_measure,
    AVRegularity.CycleJointProofs.zeroOrderJet_norm_sq]
  rfl

theorem mass_factorial_half_square_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (J : ℕ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (f : ι → TorusHk (2 * J) ℝ) :
    massNormSq ρ π (fun i => (truncateTorusHk (show J ≤ 2 * J by omega) (f i)).val) ≤
      factorialHalfCost J *
        Real.sqrt (massNormSq 1 π (fun i => (truncateTorusHk (Nat.zero_le (2 * J)) (f i)).val)) *
        Real.sqrt (massNormSq ρ π (fun i => (f i).val)) := by
  have hw i : 0 ≤ (π i)⁻¹ := (inv_pos.mpr (hπ i)).le
  have hc := weighted_product_sum_le (fun i => (π i)⁻¹)
    (fun i => ‖(f i).val (valueIndex2 (2 * J))‖) (fun i => Real.sqrt (factorialNormSq ρ (f i).val))
    hw (fun _ => norm_nonneg _) (fun _ => Real.sqrt_nonneg _)
  simp only [Real.sq_sqrt (factorialNormSq_nonneg _ _)] at hc
  have he : (∑ i, (π i)⁻¹ * ‖(f i).val (valueIndex2 (2 * J))‖ ^ 2) =
      massNormSq 1 π (fun i => (truncateTorusHk (Nat.zero_le (2 * J)) (f i)).val) := by
    simp only [massNormSq, factorial_truncate_zero_eq]
  rw [he] at hc
  calc
    _ ≤ ∑ i, (π i)⁻¹ * (factorialHalfCost J * ‖(f i).val (valueIndex2 (2 * J))‖ *
        Real.sqrt (factorialNormSq ρ (f i).val)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (factorial_half_square_bound ρ hρ J (f i)) (hw i)
    _ = factorialHalfCost J * ∑ i, (π i)⁻¹ * ‖(f i).val (valueIndex2 (2 * J))‖ *
        Real.sqrt (factorialNormSq ρ (f i).val) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
      simpa only [massNormSq, mul_assoc] using mul_le_mul_of_nonneg_left hc (factorialHalfCost_nonneg J)

theorem mass_factorial_half_interpolation (ρ : ℝ) (hρ : 0 ≤ ρ) (J : ℕ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (f : ι → TorusHk (2 * J) ℝ) :
    Real.sqrt (massNormSq ρ π (fun i => (truncateTorusHk (show J ≤ 2 * J by omega) (f i)).val)) ≤
      Real.sqrt (factorialHalfCost J) *
        Real.sqrt (Real.sqrt (massNormSq 1 π (fun i => (truncateTorusHk (Nat.zero_le (2 * J)) (f i)).val))) *
        Real.sqrt (Real.sqrt (massNormSq ρ π (fun i => (f i).val))) := by
  have hi := Real.sqrt_le_sqrt (mass_factorial_half_square_bound ρ hρ J π hπ f)
  rw [Real.sqrt_mul (mul_nonneg (factorialHalfCost_nonneg J) (Real.sqrt_nonneg _)),
    Real.sqrt_mul (factorialHalfCost_nonneg J)] at hi
  exact hi
end

/-! The half-order bound uses exactly the passage's unmarked weightedNorm. -/

theorem weightedNorm_half_interpolation {S : Finset Comp} (ρ : ℝ) (hρ : 0 ≤ ρ) (J : ℕ)
    (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (f : ∀ _v : CompIn S, TorusHk (2 * J) ℝ) :
    weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) (fun v => truncateTorusHk (show J ≤ 2 * J by omega) (f v)) ≤
      Real.sqrt (factorialHalfCost J) *
        Real.sqrt (weightedNorm (hr := fun _ => ℝ) 1 π (fun _ => 1) (fun v => truncateTorusHk (Nat.zero_le (2 * J)) (f v))) *
        Real.sqrt (weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) f) := by
  simpa only [weightedNorm, one_pow, div_one] using mass_factorial_half_interpolation ρ hρ J π hπ f

theorem weightedNorm_sub_le {S : Finset Comp} {K : ℕ} (ρ : ℝ)
    (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (f g : ∀ _v : CompIn S, TorusHk K ℝ) :
    weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) (f - g) ≤
      weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) f + weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) g := by
  simp only [weightedNorm, one_pow, div_one]
  rw [← CoupledEnergy.Variational.massWeightedCarrierCLM_norm (fun _ => K) ρ π hπ (f - g), map_sub,
    ← CoupledEnergy.Variational.massWeightedCarrierCLM_norm (fun _ => K) ρ π hπ f,
    ← CoupledEnergy.Variational.massWeightedCarrierCLM_norm (fun _ => K) ρ π hπ g]
  exact norm_sub_le _ _

/-! A paid order-zero error and genuine high carriers yield the half-order physical error. -/

def paidErrorJetConstant (J : ℕ) (C₀ C₁ : ℝ) : ℝ :=
  Real.sqrt (factorialHalfCost J) * Real.sqrt C₀ * Real.sqrt C₁

theorem paidErrorJetConstant_nonneg (J : ℕ) (C₀ C₁ : ℝ) :
    0 ≤ paidErrorJetConstant J C₀ C₁ := by unfold paidErrorJetConstant; positivity

theorem weighted_error_half_bound {S : Finset Comp} (ρ : ℝ) (hρ : 0 ≤ ρ) (J : ℕ)
    (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (f g : CompIn S → TorusHk (2 * J) ℝ) (C₀ C₁ E Q A : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hlo : weightedNorm (hr := fun _ => ℝ) 1 π (fun _ => 1)
      (fun v => truncateTorusHk (Nat.zero_le (2 * J)) (f v - g v)) ≤ C₀ * E ^ Q * A)
    (hhi : weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) f + weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) g ≤ C₁ * A) :
    weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1)
      (fun v => truncateTorusHk (show J ≤ 2 * J by omega) (f v - g v)) ≤
      paidErrorJetConstant J C₀ C₁ * E ^ (Q / 2) * A := by
  have hdiff := (weightedNorm_sub_le ρ π hπ f g).trans hhi
  have hb := weightedNorm_half_interpolation ρ hρ J π hπ (f - g)
  have hpaid : Real.sqrt (factorialHalfCost J) * Real.sqrt (C₀ * E ^ Q * A) * Real.sqrt (C₁ * A) =
      paidErrorJetConstant J C₀ C₁ * E ^ (Q / 2) * A := by
    rw [sqrt_product_paid _ C₀ C₁ (E ^ Q) A hC₀ hC₁ (Real.rpow_nonneg hE _) hA,
      sqrt_rpow_paid E Q hE]
    rfl
  apply hb.trans
  rw [← hpaid]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlo) (Real.sqrt_nonneg _))
    (Real.sqrt_le_sqrt hdiff) (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-! Conditional passage assembly from the external buffer, full-lift and comparison outputs. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem passage_jet_clauses_of_actual_bounds
    (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀) (m p N depth K : ℕ)
    (η₀ Q c₀ A tp tf C₀ C₁ : ℝ)
    (hρ : 0 ≤ rhoStar D c₀ m) (hE : 0 ≤ D.eps (m - 1)) (hA : 0 ≤ A)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hπ : ∀ v, 0 < G.mass law v)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root)
    (XU XH : ℝ → ∀ v : CompIn G.comps, TorusHk (2 * (K + 2)) (ScalarH v.1.root))
    (hU : ∀ t ∈ Set.Icc tp tf, ∀ v,
      (XU t v).toFunction.jet (valueIndex2 (2 * (K + 2))) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => aU t x v)
    (hH : ∀ t ∈ Set.Icc tp tf, ∀ v,
      (XH t v).toFunction.jet (valueIndex2 (2 * (K + 2))) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => passageLift D m N depth CcT
          (fieldCov D m p (fieldReadout m (D.eps (m - 1)) η₀ aY)) t x v)
    (hhi : ∀ t ∈ Set.Icc tp tf,
      weightedNorm (hr := fun _ => ℝ) (rhoStar D c₀ m) (G.mass law) (fun _ => 1) (XU t) +
        weightedNorm (hr := fun _ => ℝ) (rhoStar D c₀ m) (G.mass law) (fun _ => 1) (XH t) ≤ C₁ * A)
    (hlo : ∀ t ∈ Set.Icc tp tf,
      weightedNorm (hr := fun _ => ℝ) 1 (G.mass law) (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le _) (XU t v - XH t v)) ≤
        C₀ * D.eps (m - 1) ^ Q * A) :
    PassageJetClauses law G Gr m p N depth K η₀ Q
      (C₁ + paidErrorJetConstant (K + 2) C₀ C₁) c₀ A tp tf CcT aU aY := by
  intro t ht
  constructor
  · refine ⟨XU t, XH t, hU t ht, hH t ht, ?_⟩
    exact (hhi t ht).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (paidErrorJetConstant_nonneg _ _ _)) hA)
  · refine ⟨fun v => truncateTorusHk (show K + 2 ≤ 2 * (K + 2) by omega) (XU t v - XH t v), ?_, ?_⟩
    · intro v
      exact actual_error_carrier_value _ (XU t v) (XH t v) _ _ (hU t ht v) (hH t ht v)
    · have hi := weighted_error_half_bound (rhoStar D c₀ m) hρ (K + 2) (G.mass law) hπ
        (XU t) (XH t) C₀ C₁ (D.eps (m - 1)) Q A hC₀ hC₁ hE hA (hlo t ht) (hhi t ht)
      apply hi.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (Real.rpow_nonneg hE _)) hA
end

end AVRegularity.IterationPassage
end
