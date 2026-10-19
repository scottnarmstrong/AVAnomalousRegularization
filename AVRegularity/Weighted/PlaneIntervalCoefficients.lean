-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.PlaneH1Readouts
public import AVRegularity.Definitions.CycleWords.CoreScalarPackage
import AVRegularity.CoupledEnergyPlane.Variational.ProductPlaneHkOperator
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity
public import AVRegularity.CoupledEnergyPlane.Variational.MassWeightedCarrierCLM
public import AVRegularity.Statements.Intermediate.CycleComparison.IsBoxSmooth
import AVRegularity.CoupledEnergy.CouplingBounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The gradient energy is exactly the norm square of its factorial sequence. -/

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

def gradientFactorialSequence {K : ℕ} {U : Set (Vec 2)} (ρ : ℝ)
    (D : JetL2 (volume.restrict U) (K + 1) E) :
    PiLp 2 (fun _ : Fin (K + 1) => ℝ) :=
  WithLp.toLp 2 (fun j => factorialRootWeight ρ j.val *
    Real.sqrt (derivativeNormSq D ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))

theorem gradientFactorialSequence_normSq {K : ℕ} {U : Set (Vec 2)} (ρ : ℝ)
    (D : JetL2 (volume.restrict U) (K + 1) E) :
    ‖gradientFactorialSequence ρ D‖ ^ 2 = gradFactorialNormSq ρ D := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold gradFactorialNormSq
  apply Finset.sum_congr rfl
  intro j _
  change ‖factorialRootWeight ρ j.val * Real.sqrt (derivativeNormSq D _)‖ ^ 2 = _
  rw [Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (derivativeNormSq_nonneg D _), factorialRootWeight_sq]
  rfl

theorem gradientFactorialSequence_norm {K : ℕ} {U : Set (Vec 2)} (ρ : ℝ)
    (D : JetL2 (volume.restrict U) (K + 1) E) :
    ‖gradientFactorialSequence ρ D‖ = Real.sqrt (gradFactorialNormSq ρ D) := by
  rw [← gradientFactorialSequence_normSq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Exact factorial reweighting of a finite positive-order commutator convolution. -/

theorem nonprincipal_factorial_convolution_eq {K : ℕ} (ρ : ℝ)
    (A Y : Fin (K + 1) → ℝ) (hA0 : A 0 = 0) (j : Fin (K + 1)) :
    factorialRootWeight ρ j.val *
      (∑ l ∈ (Finset.range (j.val + 1)).erase 0,
        (j.val.choose l : ℝ) * finiteSequence A l * finiteSequence Y (j.val - l)) =
      finiteConvolution (fun l => factorialRootWeight ρ l.val * A l)
        (WithLp.toLp 2 (fun r => factorialRootWeight ρ r.val * Y r)) j := by
  rw [finiteConvolution_eq_sum_range, Finset.mul_sum]
  have hz : finiteSequence (fun l => factorialRootWeight ρ l.val * A l) 0 = 0 := by
    rw [finiteSequence_of_le _ (Nat.zero_le K)]
    simp [hA0]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr (Nat.succ_pos j.val)), hz, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro l hl
  have hlj : l ≤ j.val := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_of_mem_erase hl))
  have hlK : l ≤ K := hlj.trans (Nat.le_of_lt_succ j.isLt)
  have hrK : j.val - l ≤ K := (Nat.sub_le _ _).trans (Nat.le_of_lt_succ j.isLt)
  rw [finiteSequence_of_le A hlK, finiteSequence_of_le Y hrK,
    finiteSequence_of_le _ hlK, finiteSequence_of_le _ hrK]
  change factorialRootWeight ρ j.val * ((j.val.choose l : ℝ) *
    A ⟨l, _⟩ * Y ⟨j.val - l, _⟩) =
    (factorialRootWeight ρ l * A ⟨l, _⟩) *
      (factorialRootWeight ρ (j.val - l) * Y ⟨j.val - l, _⟩)
  rw [← mul_assoc, ← mul_assoc, factorialRootWeight_mul_choose ρ hlj]
  ring

theorem nonprincipal_factorial_norm_le {K : ℕ} (ρ : ℝ) (hρ : 0 ≤ ρ)
    (A Y S : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l) (hA0 : A 0 = 0)
    (hS : ∀ j, 0 ≤ S j)
    (hb : ∀ j, S j ≤ ∑ l ∈ (Finset.range (j.val + 1)).erase 0,
      (j.val.choose l : ℝ) * finiteSequence A l * finiteSequence Y (j.val - l)) :
    ‖WithLp.toLp 2 (fun j => factorialRootWeight ρ j.val * S j)‖ ≤
      (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l) *
        ‖WithLp.toLp 2 (fun j => factorialRootWeight ρ j.val * Y j)‖ := by
  let c := fun l : Fin (K + 1) => factorialRootWeight ρ l.val * A l
  let a : PiLp 2 (fun _ : Fin (K + 1) => ℝ) :=
    WithLp.toLp 2 (fun j => factorialRootWeight ρ j.val * Y j)
  have hw (j : Fin (K + 1)) : 0 ≤ factorialRootWeight ρ j.val :=
    div_nonneg (pow_nonneg hρ _) (Nat.cast_nonneg _)
  have hc : ∀ l, 0 ≤ c l := fun l => mul_nonneg (hw l) (hA l)
  have hle (j : Fin (K + 1)) : factorialRootWeight ρ j.val * S j ≤ finiteConvolution c a j := by
    calc
      _ ≤ factorialRootWeight ρ j.val * _ := mul_le_mul_of_nonneg_left (hb j) (hw j)
      _ = _ := nonprincipal_factorial_convolution_eq ρ A Y hA0 j
  exact (finiteSequence_norm_mono _ _ (fun j => mul_nonneg (hw j) (hS j)) hle).trans
    (finiteConvolution_norm_le c hc a)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Reserved jets of a literal nonzero letter constituent have finite essential time envelopes. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem letter_coefficient_jetSupOn_ne_top (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (dom : Set (ℝ × Vec 2)) (J H : ℕ)
    (hL : IsCycleLetter π L dom J H)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (hk : ((L.edge v u o).get k).map ≠ 0)
    (w : DerivativeWord2 (o.1 - 1)) (r q : ℕ) (hr : r ≤ L.slow) (hq : q ≤ J) :
    jetSupOn dom r q (((L.edge v u o).get k).coeff w) ≠ ⊤ := by
  let F := ChartedFamily.ofFiber L.edge
  have hh := analyticEnvelope_reserved_jet_ne_top F π hπ (fun _ _ => dom)
    L.slow J L.majorant hL.analytic v u ⟨o, k⟩
    (by simpa only [F, ChartedFamily.ofFiber] using hk) o.1
    (by exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp o.2).1, le_rfl⟩) w r q hr hq
  exact ne_top_of_le_ne_top hh (ofFiber_jetSupOn_le_jetSupFam L.edge dom v u o k w r q)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! One finite bound controls every reserved mixed jet of a constituent at almost every time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem letter_coefficient_ae_mixed_bound (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (I : Set ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (I ×ˢ Set.univ) J H)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (hk : ((L.edge v u o).get k).map ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ t ∂volume, t ∈ I →
      ∀ (w : DerivativeWord2 (o.1 - 1)) (r q : ℕ), r ≤ L.slow → q ≤ J →
      ∀ X z, ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ q
        (((L.edge v u o).get k).coeff w t X') z) X‖ ≤ B := by
  classical
  let b := fun (w : DerivativeWord2 (o.1 - 1)) (r : Fin (L.slow + 1)) (q : Fin (J + 1)) =>
    (jetSupOn (I ×ˢ Set.univ) r.val q.val (((L.edge v u o).get k).coeff w)).toReal
  let B := ∑ w, ∑ r, ∑ q, b w r q
  have hb0 : ∀ w r q, 0 ≤ b w r q := fun _ _ _ => ENNReal.toReal_nonneg
  refine ⟨B, Finset.sum_nonneg (fun w _ => Finset.sum_nonneg
    (fun r _ => Finset.sum_nonneg (fun q _ => hb0 w r q))), ?_⟩
  have hh (w : DerivativeWord2 (o.1 - 1)) (r : Fin (L.slow + 1)) (q : Fin (J + 1)) :=
    jetSupOn_ae_norm_bound (I ×ˢ Set.univ) r.val q.val
      (((L.edge v u o).get k).coeff w)
      (letter_coefficient_jetSupOn_ne_top π hπ L _ J H hL v u o k hk w r.val q.val
        (Nat.le_of_lt_succ r.isLt) (Nat.le_of_lt_succ q.isLt))
  filter_upwards [ae_all_iff.mpr (fun w => ae_all_iff.mpr
    (fun r => ae_all_iff.mpr (fun q => hh w r q)))] with t ht
  intro hti w r q hr hq X z
  let ri : Fin (L.slow + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
  let qi : Fin (J + 1) := ⟨q, Nat.lt_succ_of_le hq⟩
  have hle : b w ri qi ≤ B := by
    exact (Finset.single_le_sum (f := b w ri) (fun q _ => hb0 w ri q)
      (Finset.mem_univ qi)).trans ((Finset.single_le_sum
      (f := fun r => ∑ q, b w r q) (fun r _ => Finset.sum_nonneg (fun q _ => hb0 w r q))
      (Finset.mem_univ ri)).trans (Finset.single_le_sum
      (f := fun w => ∑ r, ∑ q, b w r q)
      (fun w _ => Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun q _ => hb0 w r q)))
      (Finset.mem_univ w)))
  exact (ht w ri qi X ⟨hti, Set.mem_univ X⟩ z).trans hle
end

/-! The constructed coefficient product has its literal pointwise value readout. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem planeCoefficientCarrier_jet_ae {K : ℕ}
    (q : PlaneHk Set.univ K E) (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) {A : Fin (K + 1) → ℝ}
    (hA : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (j : JetIndex2 K) :
    (q.mulCoefficient C hC hA).val j =ᵐ[volume.restrict Set.univ]
      multiplicationRawJet C q.toFunction.jet j := by
  unfold PlaneHk.mulCoefficient
  exact jetToL2_ae _ _ _

theorem planeCoefficientCarrier_value_ae {K : ℕ}
    (q : PlaneHk Set.univ K E) (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) {A : Fin (K + 1) → ℝ}
    (hA : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    (q.mulCoefficient C hC hA).val (valueIndex2 K) =ᵐ[volume.restrict Set.univ]
      fun x => C x (q.val (valueIndex2 K) x) := by
  have hp : (q.mulCoefficient C hC hA).val (valueIndex2 K) =ᵐ[volume.restrict Set.univ]
      multiplicationRawJet C q.toFunction.jet (valueIndex2 K) := by
    unfold PlaneHk.mulCoefficient
    exact jetToL2_ae _ _ _
  have he : multiplicationRawJet C q.toFunction.jet (valueIndex2 K) =
      fun x => C x (q.toFunction.jet (valueIndex2 K) x) := by
    funext x
    exact multiplicationRawJet_value C q.toFunction.jet x
  rw [he] at hp
  exact hp
end

/-! Polynomially growing coefficients act on actual weighted weak Sobolev jets. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem memLp_growing_operator_mul {U : Set (Vec 2)}
    (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C) (u : Vec 2 → E)
    (hu : MemLp u 2 (volume.restrict U)) (q : Vec 2 → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hw : MemLp (fun x => q x • u x) 2 (volume.restrict U))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ x, ‖C x‖ ≤ A * q x) :
    MemLp (fun x => C x (u x)) 2 (volume.restrict U) := by
  apply (hw.const_smul A).of_le
  · exact (ContinuousLinearMap.apply ℝ F).flip.aestronglyMeasurable_comp₂
      hC.aestronglyMeasurable hu.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    calc
      ‖C x (u x)‖ ≤ ‖C x‖ * ‖u x‖ := (C x).le_opNorm _
      _ ≤ (A * q x) * ‖u x‖ := mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
      _ = ‖A • (q x • u x)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hA, Real.norm_of_nonneg (hq x)]
        ring

theorem multiplicationRawJet_memL2_growing {K : ℕ} {U : Set (Vec 2)}
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (D : RawJet2 K E) (hD : JetMemL2On U D)
    (q : Vec 2 → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hw : ∀ α, MemLp (fun x => q x • D α x) 2 (volume.restrict U))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l * q x) :
    JetMemL2On U (multiplicationRawJet C D) := by
  intro α
  apply memLp_finsetSum Finset.univ
  intro m _
  let l : Fin (K + 1) := ⟨maskLeftLength α.1.val m,
    Nat.lt_succ_of_le ((maskLeftLength_le α.1.val m).trans (Nat.le_of_lt_succ α.1.isLt))⟩
  have hCl : ContDiff ℝ (Nat.cast l.val : WithTop ℕ∞) C :=
    hC.of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt)
  exact memLp_growing_operator_mul
    (orderedCoefficientDerivative C l.val (maskWordEquiv 2 α.1.val m α.2).1)
    (orderedCoefficientDerivative_contDiff C l.val 0
      (by simpa only [Nat.add_zero] using hCl) _).continuous
    (D (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2))
    (hD _) q hq (hw _) (A l) (hA l)
    (fun x => (orderedCoefficientDerivative_norm_le_array C l.val _ x).trans (hb l x))

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def multiplyGrowingPlaneHk {K : ℕ} (W : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (q : Vec 2 → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hw : ∀ α, MemLp (fun x => q x • W.toFunction.jet α x) 2 (volume.restrict Set.univ))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l * q x) :
    PlaneHk Set.univ K F :=
  (⟨multiplicationRawJet C W.toFunction.jet,
    multiplicationRawJet_memL2_growing C hC W.toFunction.jet W.toFunction.memL2 q hq hw A hA hb,
    multiplicationRawJet_hasOrderedWeakJetOn hC W.toFunction.hasWeakJet
      (jet_scalar_locallyIntegrable W.toFunction.memL2)⟩ : PlaneHkFunction Set.univ K F).toHk
end

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The existing factorial multiplier estimate gives a true `H¹` operator norm bound. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- At order one and radius one the factorial norm is exactly the ambient Sobolev Hilbert norm. -/
theorem planeH1_factorialNormSq_one (u : PlaneHk Set.univ 1 E) :
    factorialNormSq 1 u.val = ‖u‖ ^ 2 := by
  change factorialNormSq 1 u.val = ‖u.val‖ ^ 2
  rw [jet_norm_sq_eq_sum]
  unfold factorialNormSq
  apply Finset.sum_congr rfl
  intro j _
  have hw : factorialWeight 1 j.val = 1 := by
    fin_cases j <;> simp [factorialWeight]
  rw [hw, one_mul]

/-- Bounded order-zero and order-one coefficient jets give a dimension-free `H¹` multiplier bound. -/
theorem planeH1_mulCoefficient_norm_le
    (C : Vec 2 → E →L[ℝ] E) (hC : ContDiff ℝ 1 C)
    (A : Fin 2 → ℝ) (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (u : PlaneHk Set.univ 1 E) :
    ‖u.mulCoefficient C hC hb‖ ≤ (A 0 + A 1) * ‖u‖ := by
  have h := u.mulCoefficient_factorialNorm_le hC hb (ρ := 1) (by norm_num)
  rw [planeH1_factorialNormSq_one, planeH1_factorialNormSq_one,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  have hw : (∑ l : Fin 2, factorialRootWeight 1 l.val * A l) = A 0 + A 1 := by
    simp [Fin.sum_univ_two, factorialRootWeight]
  rw [hw] at h
  exact h

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! Factorial absorption also controls the norm product of the actual drift source and stored word. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {U : Set (Vec 2)}

omit [BorelSpace E] [CompleteSpace E] in
theorem driftCommutator_norm_product_absorption {K Kmax : ℕ} (hK : K ≤ Kmax)
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : RawJet2 (K + 1) E) (hT : ∀ (j : Fin (K + 1)) (m : PositionMask j.val) (w : DerivativeWord2 j.val),
      MemLp (driftMaskTerm (Nat.le_of_lt_succ j.isLt) v D m w) 2 (volume.restrict U))
    (hD : JetMemL2On U D) (hU : MeasurableSet U) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (‖driftCommutatorL2Array (Nat.le_of_lt_succ j.isLt) v D (hT j)‖ *
        ‖orderL2Array (jetToL2 D hD) ⟨j.val, by omega⟩‖)) ≤
      (ν / 4) * gradFactorialNormSq ρ (jetToL2 D hD) := by
  let V := fun l : ℕ => a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)
  let Y := finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r))
  have hV : ∀ l, 0 ≤ V l := by
    intro l
    dsimp [V]
    exact mul_nonneg (mul_nonneg (mul_nonneg ha (pow_nonneg (by linarith) _))
      (Nat.cast_nonneg _)) (zpow_nonneg hlam.le _)
  have hY : ∀ j, 0 ≤ Y j := by
    intro j
    unfold Y finiteSequence
    split_ifs <;> positivity
  have hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x ∈ U,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤ V l :=
    fun l hl hlK x _ => hjets l hl (hlK.trans hK) x
  have hscalar := CoupledEnergy.coupledDriftCommutatorAbsorption hρ.le ha hB hlam hν
    hsmall hstrain hK V Y (fun _ _ _ => le_rfl) hY
  rw [← Fin.sum_univ_eq_sum_range] at hscalar
  have hgradient := finiteDerivativeSequence_gradient_square ρ (jetToL2 D hD)
  dsimp only [Y] at hscalar
  rw [hgradient] at hscalar
  refine le_trans ?_ hscalar
  apply Finset.sum_le_sum
  intro j _
  rw [analyticFactorialWeight_sq]
  apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg ρ _)
  have hm := mul_le_mul_of_nonneg_right
    (driftCommutatorL2Array_norm_le (Nat.le_of_lt_succ j.isLt) v D (hT j) hD hU V hV hb)
    (norm_nonneg (orderL2Array (jetToL2 D hD) ⟨j.val, by omega⟩))
  rw [orderL2Array_norm, ← finiteSequence_of_le (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r))
      (by omega : j.val ≤ K + 1),
    Finset.sum_mul] at hm
  rw [orderL2Array_norm, ← finiteSequence_of_le
    (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) (by omega : j.val ≤ K + 1)]
  exact hm

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Read the literal constituent regularity from the one-chart letter envelope. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem letter_coefficient_joint_contDiff (π : ι → ℝ) (L : CycleLetter ι h D)
    (a b : ℝ) (J H : ℕ) (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (w : DerivativeWord2 (o.1 - 1)) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (L.slow + J : ℕ)
      (fun p : Vec 2 × Vec 2 => ((L.edge v u o).get k).coeff w t p.1 p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  rintro ⟨X, z⟩
  have hh := hL.analytic.1 () () v u ⟨o, k⟩ o.1 w (t, X) ⟨ht, Set.mem_univ X⟩ z
  simpa only [ChartedFamily.ofFiber, dite_true, inv_one, one_smul] using hh

theorem letter_coefficient_boxSmooth (π : ι → ℝ) (L : CycleLetter ι h D)
    (a b : ℝ) (J H : ℕ) (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (w : DerivativeWord2 (o.1 - 1)) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth L.slow J (((L.edge v u o).get k).coeff w t) :=
  isBoxSmooth_of_joint_contDiff L.slow J _
    (letter_coefficient_joint_contDiff π L a b J H hL v u o k w t ht)

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Bounded rational truncations of positive weights, used to justify weighted energy tests. -/

section
open Homogenization

noncomputable section

/-- The bounded truncation `B s / (B + s)` of a positive weight `s`. -/
def clipWeight (B s : ℝ) : ℝ := B * s / (B + s)

/-- The derivative of `clipWeight B` at a positive argument. -/
def clipWeightDeriv (B s : ℝ) : ℝ := B ^ 2 / (B + s) ^ 2

/-- The second derivative of `clipWeight B` at a positive argument. -/
def clipWeightSecondDeriv (B s : ℝ) : ℝ := -(2 * B ^ 2 / (B + s) ^ 3)

/-- The explicit first derivative used when composing a clipped weight with a smooth weight. -/
theorem hasDerivAt_clipWeight {B s : ℝ} (hB : 0 < B) (hs : 0 < s) :
    HasDerivAt (clipWeight B) (clipWeightDeriv B s) s := by
  have hnum : HasDerivAt (fun x : ℝ => B * x) B s := hasDerivAt_const_mul (x := s) B
  have hden : HasDerivAt (fun x : ℝ => B + x) 1 s :=
    (hasDerivAt_id s).const_add B
  have hquot := hnum.div hden (ne_of_gt (add_pos hB hs))
  change HasDerivAt (fun x : ℝ => B * x / (B + x))
    (B ^ 2 / (B + s) ^ 2) s
  have hformula : B ^ 2 / (B + s) ^ 2 =
      (B * (B + s) - B * s * 1) / (B + s) ^ 2 := by
    field_simp [ne_of_gt (add_pos hB hs)]
    ring
  rw [hformula]
  exact hquot

/-- The explicit second derivative used in the clipped-weight chain rule. -/
theorem hasDerivAt_clipWeightDeriv {B s : ℝ} (hB : 0 < B) (hs : 0 < s) :
    HasDerivAt (clipWeightDeriv B) (clipWeightSecondDeriv B s) s := by
  have hden : HasDerivAt (fun x : ℝ => B + x) 1 s :=
    (hasDerivAt_id s).const_add B
  have hdenSq := hden.pow 2
  have hnum : HasDerivAt (fun _ : ℝ => B ^ 2) 0 s := hasDerivAt_const s (B ^ 2)
  have hquot := hnum.div hdenSq (pow_ne_zero 2 (ne_of_gt (add_pos hB hs)))
  change HasDerivAt (fun x : ℝ => B ^ 2 / (B + x) ^ 2)
    (-(2 * B ^ 2 / (B + s) ^ 3)) s
  have hformula : -(2 * B ^ 2 / (B + s) ^ 3) =
      (0 * (B + s) ^ 2 - B ^ 2 * (2 * (B + s) ^ (2 - 1) * 1)) /
        ((B + s) ^ 2) ^ 2 := by
    norm_num
    field_simp [ne_of_gt (add_pos hB hs)]
  rw [hformula]
  exact hquot

theorem clipWeight_pos {B s : ℝ} (hB : 0 < B) (hs : 0 < s) : 0 < clipWeight B s := by
  exact div_pos (mul_pos hB hs) (add_pos hB hs)

theorem clipWeightDeriv_nonneg {B s : ℝ} (hB : 0 < B) (hs : 0 < s) :
    0 ≤ clipWeightDeriv B s := by
  unfold clipWeightDeriv
  positivity

theorem clipWeightSecondDeriv_nonpos {B s : ℝ} (hB : 0 < B) (hs : 0 < s) :
    clipWeightSecondDeriv B s ≤ 0 := by
  unfold clipWeightSecondDeriv
  exact neg_nonpos.mpr (by positivity)

theorem clipWeight_le_bound {B s : ℝ} (hB : 0 < B) (hs : 0 < s) :
    clipWeight B s ≤ B := by
  rw [clipWeight, div_le_iff₀ (add_pos hB hs)]
  nlinarith

theorem clipWeight_le_value {B s : ℝ} (hB : 0 < B) (hs : 0 < s) :
    clipWeight B s ≤ s := by
  rw [clipWeight, div_le_iff₀ (add_pos hB hs)]
  nlinarith

/-- The scaled first-derivative bound used in the chain rule for a clipped weight. -/
theorem clipWeight_scaled_deriv_le {B s : ℝ} (hB : 0 < B) (hs : 0 < s) :
    s * clipWeightDeriv B s ≤ clipWeight B s := by
  rw [clipWeightDeriv, clipWeight]
  have hden : B + s ≠ 0 := ne_of_gt (add_pos hB hs)
  field_simp [hden]
  nlinarith

/-- The scaled second-derivative bound from the bounded-weight energy argument. -/
theorem clipWeight_scaled_secondDeriv_abs_le {B s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    s ^ 2 * |clipWeightSecondDeriv B s| ≤ 2 * clipWeight B s := by
  rw [clipWeightSecondDeriv, abs_neg, abs_of_pos (div_pos
    (mul_pos (by norm_num) (sq_pos_of_pos hB)) (pow_pos (add_pos hB hs) 3)),
    clipWeight]
  have hden : B + s ≠ 0 := ne_of_gt (add_pos hB hs)
  field_simp [hden]
  nlinarith [sq_nonneg (B - s), mul_pos hB hs]

/-- Differentiating the bounded truncation after a smooth scalar weight. -/
theorem hasFDerivAt_clipWeight_comp {d : ℕ} (B : ℝ) {w : Vec d → ℝ}
    {x : Vec d} (hB : 0 < B) (hw : 0 < w x)
    (hwd : HasFDerivAt w (fderiv ℝ w x) x) :
    HasFDerivAt (fun y => clipWeight B (w y))
      (clipWeightDeriv B (w x) • fderiv ℝ w x) x := by
  have hclip := (hasDerivAt_clipWeight hB hw).hasFDerivAt
  have hcomp := hclip.comp x hwd
  convert hcomp using 1
  · rfl
  · ext y
    simp [ContinuousLinearMap.comp_apply]
    ring

theorem clipWeight_comp_fderiv {d : ℕ} (B : ℝ) {w : Vec d → ℝ}
    {x : Vec d} (hB : 0 < B) (hw : 0 < w x)
    (hwd : HasFDerivAt w (fderiv ℝ w x) x) :
    fderiv ℝ (fun y => clipWeight B (w y)) x =
      clipWeightDeriv B (w x) • fderiv ℝ w x := by
  exact (hasFDerivAt_clipWeight_comp B hB hw hwd).fderiv

/-- Differentiating the first derivative coefficient after composing it with a
positive smooth weight. -/
theorem hasFDerivAt_clipWeightDeriv_comp {d : ℕ} (B : ℝ) {w : Vec d → ℝ}
    {x : Vec d} (hB : 0 < B) (hw : 0 < w x)
    (hwd : HasFDerivAt w (fderiv ℝ w x) x) :
    HasFDerivAt (fun y => clipWeightDeriv B (w y))
      (clipWeightSecondDeriv B (w x) • fderiv ℝ w x) x := by
  have hclip := (hasDerivAt_clipWeightDeriv hB hw).hasFDerivAt
  have hcomp := hclip.comp x hwd
  convert hcomp using 1
  · rfl
  · ext y
    simp [ContinuousLinearMap.comp_apply]
    ring

/-- The clipped derivative coefficient preserves relative square bounds. -/
theorem clipWeight_scaled_mul_sq_le {B s x : ℝ} (hB : 0 < B) (hs : 0 < s) :
    (clipWeightDeriv B s * x) ^ 2 / (clipWeight B s) ^ 2 ≤ x ^ 2 / s ^ 2 := by
  have hratio : s * clipWeightDeriv B s ≤ clipWeight B s :=
    clipWeight_scaled_deriv_le hB hs
  have hclip0 : 0 < clipWeight B s := clipWeight_pos hB hs
  have hder0 : 0 ≤ clipWeightDeriv B s := by
    unfold clipWeightDeriv
    positivity
  have hprod0 : 0 ≤ clipWeightDeriv B s * s := mul_nonneg hder0 hs.le
  have hratio' : clipWeightDeriv B s * s ≤ clipWeight B s := by nlinarith [hratio]
  have hratioSq :
      (clipWeightDeriv B s * s) ^ 2 ≤ (clipWeight B s) ^ 2 := by
    exact pow_le_pow_left₀ hprod0 hratio' 2
  rw [div_le_div_iff₀ (sq_pos_of_pos hclip0) (sq_pos_of_pos hs)]
  have h := mul_le_mul_of_nonneg_right hratioSq (sq_nonneg x)
  nlinarith [h]

/-- The same relative square estimate after summing a finite vector. -/
theorem clipWeight_scaled_vec_sq_le {d : ℕ} (B s : ℝ) (hB : 0 < B)
    (hs : 0 < s) (q : Fin d → ℝ) :
    (∑ i, (clipWeightDeriv B s * q i) ^ 2) / (clipWeight B s) ^ 2 ≤
      (∑ i, (q i) ^ 2) / s ^ 2 := by
  rw [Finset.sum_div, Finset.sum_div]
  exact Finset.sum_le_sum fun i _ => clipWeight_scaled_mul_sq_le hB hs

end
end

/-! Scalar estimates for the correction terms created by bounded weight clipping. -/

/-- The cross term of two finite vectors is controlled by their combined square energy. -/
theorem finiteDot_abs_le_half_sq (x y : Fin 2 → ℝ) :
    2 * |∑ i : Fin 2, x i * y i| ≤ ∑ i, (x i) ^ 2 + ∑ i, (y i) ^ 2 := by
  have hterm : ∀ i : Fin 2, 2 * |x i * y i| ≤ (x i) ^ 2 + (y i) ^ 2 := by
    intro i
    rw [abs_mul]
    nlinarith [sq_nonneg (|x i| - |y i|), sq_abs (x i), sq_abs (y i)]
  calc
    2 * |∑ i : Fin 2, x i * y i| ≤ 2 * ∑ i, |x i * y i| := by
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = ∑ i, 2 * |x i * y i| := by rw [Finset.mul_sum]
    _ ≤ ∑ i, ((x i) ^ 2 + (y i) ^ 2) := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, (x i) ^ 2) + ∑ i, (y i) ^ 2 := by rw [Finset.sum_add_distrib]

/-- The second-derivative correction in the clipped-weight defect is absorbed
by the logarithmic gradient and flux bounds. -/
theorem clipWeight_second_cross_le {B s lam : ℝ} (hB : 0 < B) (hs : 0 < s)
    (hlam : 0 ≤ lam) (x y : Fin 2 → ℝ)
    (hbound : (∑ i, (x i) ^ 2) / s ^ 2 + (∑ i, (y i) ^ 2) / s ^ 2 ≤ lam) :
    |clipWeightSecondDeriv B s| * |∑ i, x i * y i| ≤ lam * clipWeight B s := by
  let X : ℝ := ∑ i : Fin 2, (x i) ^ 2
  let Y : ℝ := ∑ i : Fin 2, (y i) ^ 2
  have hXY : X + Y ≤ lam * s ^ 2 := by
    have hfrac : (X + Y) / s ^ 2 ≤ lam := by
      simpa [X, Y, add_div] using hbound
    exact (div_le_iff₀ (sq_pos_of_pos hs)).mp hfrac
  have hdot := finiteDot_abs_le_half_sq x y
  have hsecond := clipWeight_scaled_secondDeriv_abs_le hB hs
  have hmul :
      2 * |clipWeightSecondDeriv B s| * |∑ i, x i * y i| ≤
        |clipWeightSecondDeriv B s| * (X + Y) := by
    dsimp [X, Y] at hdot ⊢
    nlinarith [mul_le_mul_of_nonneg_left hdot (abs_nonneg (clipWeightSecondDeriv B s))]
  have henergy : |clipWeightSecondDeriv B s| * (X + Y) ≤
      2 * lam * clipWeight B s := by
    have hcoeff := mul_le_mul_of_nonneg_right hXY
      (abs_nonneg (clipWeightSecondDeriv B s))
    have hclip := mul_le_mul_of_nonneg_left hsecond hlam
    dsimp [X, Y] at hcoeff ⊢
    nlinarith [hcoeff, hclip]
  nlinarith [hmul, henergy]

/-- Algebraic composition step for the clipped weight inequality. The spatial
second derivative contributes a nonpositive elliptic term, while its flux
cross term is absorbed by the chart defect budget. -/
theorem clippedOperator_defect_bound {lam W ψ a b L divPhi qG qPhi : ℝ}
    (hlam : 0 ≤ lam) (ha : 0 ≤ a) (hscale : a * W ≤ ψ)
    (hbase : L ≤ lam * W + divPhi) (helliptic : b * qG ≤ 0)
    (hcross : |b| * |qPhi| ≤ lam * ψ) :
    a * L + b * qG ≤ 2 * lam * ψ + a * divPhi + b * qPhi := by
  have hmul := mul_le_mul_of_nonneg_left hbase ha
  have hscale' : lam * (a * W) ≤ lam * ψ :=
    mul_le_mul_of_nonneg_left hscale hlam
  have hcross' : -b * qPhi ≤ lam * ψ := by
    calc
      -b * qPhi = -(b * qPhi) := by ring
      _ ≤ |b * qPhi| := neg_le_abs _
      _ = |b| * |qPhi| := abs_mul b qPhi
      _ ≤ lam * ψ := hcross
  nlinarith [hmul, hscale', hcross']

end AVRegularity.Weighted
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Weighted

/-! Spatial product and chain rules for the clipped elliptic flux. -/

noncomputable section

/-- One row of the metric flux of a scalar field. -/
def weightFluxRow (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (w : Vec 2 → ℝ)
    (i : Fin 2) : Vec 2 → ℝ :=
  fun z => ∑ j : Fin 2, G z i j * fderiv ℝ w z (basisVec j)

/-- One row of the metric flux after composing the field with `clipWeight`. -/
def clippedWeightFluxRow (B : ℝ) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : Vec 2 → ℝ) (i : Fin 2) : Vec 2 → ℝ :=
  fun z => ∑ j : Fin 2, G z i j *
    fderiv ℝ (fun y => clipWeight B (w y)) z (basisVec j)

/-- The divergence row of a clipped metric flux is the scaled old divergence
plus the second-derivative chain correction. -/
theorem clippedWeightFluxRow_fderiv
    (B : ℝ) (hB : 0 < B) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : Vec 2 → ℝ) (i : Fin 2) (z : Vec 2)
    (hw : ∀ y, 0 < w y)
    (hwd : ∀ y, HasFDerivAt w (fderiv ℝ w y) y)
    (hfluxd : HasFDerivAt (weightFluxRow G w i)
      (fderiv ℝ (weightFluxRow G w i) z) z) :
    fderiv ℝ (clippedWeightFluxRow B G w i) z (basisVec i) =
      clipWeightDeriv B (w z) *
        fderiv ℝ (weightFluxRow G w i) z (basisVec i) +
      clipWeightSecondDeriv B (w z) *
        fderiv ℝ w z (basisVec i) * weightFluxRow G w i z := by
  have hfluxEq : clippedWeightFluxRow B G w i =
      fun y => clipWeightDeriv B (w y) * weightFluxRow G w i y := by
    funext y
    simp only [clippedWeightFluxRow, weightFluxRow]
    calc
      (∑ j : Fin 2, G y i j *
          fderiv ℝ (fun x => clipWeight B (w x)) y (basisVec j)) =
          ∑ j : Fin 2, G y i j *
            (clipWeightDeriv B (w y) * fderiv ℝ w y (basisVec j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [clipWeight_comp_fderiv B hB (hw y) (hwd y)]
        simp only [smul_apply]
        ring
      _ = clipWeightDeriv B (w y) *
          ∑ j : Fin 2, G y i j * fderiv ℝ w y (basisVec j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hcoeff := hasFDerivAt_clipWeightDeriv_comp B hB (hw z) (hwd z)
  have hmul := hcoeff.mul hfluxd
  rw [hfluxEq]
  change fderiv ℝ ((fun y => clipWeightDeriv B (w y)) * weightFluxRow G w i) z
      (basisVec i) = _
  rw [hmul.fderiv]
  simp only [add_apply, smul_apply]
  ring

/-- Divergence of the metric flux of a scalar field. -/
def weightMetricDivergence (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : Vec 2 → ℝ) (z : Vec 2) : ℝ :=
  ∑ i : Fin 2, fderiv ℝ (weightFluxRow G w i) z (basisVec i)

/-- Divergence of the metric flux after the bounded weight composition. -/
def clippedWeightMetricDivergence (B : ℝ) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : Vec 2 → ℝ) (z : Vec 2) : ℝ :=
  ∑ i : Fin 2, fderiv ℝ (clippedWeightFluxRow B G w i) z (basisVec i)

/-- The full divergence chain rule for the clipped metric flux. -/
theorem clippedWeightMetricDivergence_eq
    (B : ℝ) (hB : 0 < B) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : Vec 2 → ℝ) (z : Vec 2)
    (hw : ∀ y, 0 < w y)
    (hwd : ∀ y, HasFDerivAt w (fderiv ℝ w y) y)
    (hfluxd : ∀ i : Fin 2, HasFDerivAt (weightFluxRow G w i)
      (fderiv ℝ (weightFluxRow G w i) z) z) :
    clippedWeightMetricDivergence B G w z =
      clipWeightDeriv B (w z) * weightMetricDivergence G w z +
        clipWeightSecondDeriv B (w z) *
          ∑ i : Fin 2, fderiv ℝ w z (basisVec i) * weightFluxRow G w i z := by
  unfold clippedWeightMetricDivergence weightMetricDivergence
  calc
    (∑ i : Fin 2,
      fderiv ℝ (clippedWeightFluxRow B G w i) z (basisVec i)) =
      ∑ i : Fin 2,
        (clipWeightDeriv B (w z) *
          fderiv ℝ (weightFluxRow G w i) z (basisVec i) +
        clipWeightSecondDeriv B (w z) *
          fderiv ℝ w z (basisVec i) * weightFluxRow G w i z) := by
      apply Finset.sum_congr rfl
      intro i _
      exact clippedWeightFluxRow_fderiv B hB G w i z hw hwd (hfluxd i)
    _ = clipWeightDeriv B (w z) *
          ∑ i : Fin 2, fderiv ℝ (weightFluxRow G w i) z (basisVec i) +
        clipWeightSecondDeriv B (w z) *
          ∑ i : Fin 2, fderiv ℝ w z (basisVec i) * weightFluxRow G w i z := by
      rw [Finset.sum_add_distrib]
      have hfact :
          (∑ i : Fin 2, clipWeightSecondDeriv B (w z) *
            fderiv ℝ w z (basisVec i) * weightFluxRow G w i z) =
          clipWeightSecondDeriv B (w z) *
            ∑ i : Fin 2, fderiv ℝ w z (basisVec i) * weightFluxRow G w i z := by
        calc
          _ = ∑ i : Fin 2, clipWeightSecondDeriv B (w z) *
              (fderiv ℝ w z (basisVec i) * weightFluxRow G w i z) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by rw [Finset.mul_sum]
      rw [← Finset.mul_sum, hfact]

end

end AVRegularity.Weighted
end
end

section
@[expose] public section
open Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Monotone exhaustion of a positive chart weight by its bounded clips. -/

/-- The rational clip is increasing in its clipping parameter. -/
theorem clipWeight_mono_parameter {B₁ B₂ s : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₁₂ : B₁ ≤ B₂) (hs : 0 < s) :
    clipWeight B₁ s ≤ clipWeight B₂ s := by
  unfold clipWeight
  apply (div_le_div_iff₀ (add_pos_of_nonneg_of_pos hB₁ hs)
    (add_pos_of_nonneg_of_pos (le_trans hB₁ hB₁₂) hs)).2
  have hmul : 0 ≤ (B₂ - B₁) * s ^ 2 := mul_nonneg (sub_nonneg.mpr hB₁₂) (sq_nonneg s)
  nlinarith [hmul]

/-- Integer clips converge pointwise to the original positive weight. -/
theorem clipWeight_nat_tendsto (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => clipWeight ((n : ℝ) + 1) s) atTop (𝓝 s) := by
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1) + s) atTop atTop := by
    have hc : Tendsto (fun _ : ℕ => 1 + s) atTop (𝓝 (1 + s)) := tendsto_const_nhds
    have h := hc.add_atTop tendsto_natCast_atTop_atTop
    simpa [add_comm, add_left_comm, add_assoc] using h
  have htail : Tendsto (fun n : ℕ => s ^ 2 / (((n : ℝ) + 1) + s)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hformula (n : ℕ) : clipWeight ((n : ℝ) + 1) s =
      s - s ^ 2 / (((n : ℝ) + 1) + s) := by
    unfold clipWeight
    have hpos : (((n : ℝ) + 1) + s) ≠ 0 := ne_of_gt (by positivity)
    field_simp [hpos]
    ring
  simpa [Function.comp_def, hformula] using
    (tendsto_const_nhds.sub htail :
      Tendsto (fun n : ℕ => s - s ^ 2 / (((n : ℝ) + 1) + s)) atTop (𝓝 (s - 0)))

/-- The integer clip sequence is monotone for every positive weight. -/
theorem clipWeight_nat_monotone (s : ℝ) (hs : 0 < s) :
    Monotone (fun n : ℕ => clipWeight ((n : ℝ) + 1) s) := by
  intro n m hnm
  apply clipWeight_mono_parameter (by positivity) _ hs
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  simpa [add_comm] using add_le_add_right hcast (1 : ℝ)

end AVRegularity.Weighted
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Weighted

/-! Quadratic-form ellipticity consequences of the near-identity bound `IsMetricNearIdentity`. -/

/-- Symmetry turns the near-identity quadratic bound into uniform bounds on every matrix entry. -/
theorem nearIdentity_entry_abs_le
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (t : ℝ) (z : Vec 2) (hsym : (G t z).IsSymm) (i j : Fin 2) :
    |G t z i j| ≤ 5 / 4 := by
  have hsym' : G t z 1 0 = G t z 0 1 := by
    change (G t z).transpose = G t z at hsym
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hsym
  have h00 := hG t z ![1, 0]
  have h11 := hG t z ![0, 1]
  have hp := hG t z ![1, 1]
  have hm := hG t z ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h11 hp hm
  norm_num at h00 h11 hp hm
  rw [hsym'] at hp hm
  rw [abs_le] at h00 h11 hp hm ⊢
  fin_cases i <;> fin_cases j
  · change -(5 / 4 : ℝ) ≤ G t z 0 0 ∧ G t z 0 0 ≤ 5 / 4
    constructor <;> linarith
  · change -(5 / 4 : ℝ) ≤ G t z 0 1 ∧ G t z 0 1 ≤ 5 / 4
    constructor <;> linarith
  · change -(5 / 4 : ℝ) ≤ G t z 1 0 ∧ G t z 1 0 ≤ 5 / 4
    rw [hsym']
    constructor <;> linarith
  · change -(5 / 4 : ℝ) ≤ G t z 1 1 ∧ G t z 1 1 ≤ 5 / 4
    constructor <;> linarith

/-- A metric within `g` of the identity has the expected two-sided quadratic
form bounds. -/
theorem nearIdentity_quadratic_bounds
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (t : ℝ) (z : Vec 2) (ξ : Vec 2) :
    (3 / 4 : ℝ) * (∑ i : Fin 2, ξ i ^ 2) ≤
        ∑ i, ∑ j, ξ i * G t z i j * ξ j ∧
      (∑ i, ∑ j, ξ i * G t z i j * ξ j) ≤
        (5 / 4 : ℝ) * (∑ i : Fin 2, ξ i ^ 2) := by
  let q : ℝ := ∑ i, ∑ j, ξ i * G t z i j * ξ j
  let e : ℝ := ∑ i : Fin 2, ξ i ^ 2
  have hone : (∑ i, ∑ j, ξ i * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ j) = e := by
    simp [e, Matrix.one_apply]
    ring
  have hsub :
      (∑ i : Fin 2, ∑ j : Fin 2, ξ i * (G t z - 1) i j * ξ j) = q - e := by
    calc
      (∑ i : Fin 2, ∑ j : Fin 2, ξ i * (G t z - 1) i j * ξ j) =
          ∑ i, ∑ j, (ξ i * G t z i j * ξ j -
            ξ i * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [Matrix.sub_apply]
        ring
      _ = (∑ i, ∑ j, ξ i * G t z i j * ξ j) -
          (∑ i, ∑ j, ξ i * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ j) := by
        simp_rw [Finset.sum_sub_distrib]
      _ = q - e := by rw [hone]
  have hnear := hG t z ξ
  rw [abs_le] at hnear
  have hlow : - (g * e) ≤ q - e := by
    simpa only [e, q, hsub] using hnear.1
  have hupp : q - e ≤ g * e := by
    simpa only [e, q, hsub] using hnear.2
  have he : 0 ≤ e := by
    dsimp [e]
    positivity
  constructor
  · change (3 / 4 : ℝ) * e ≤ q
    nlinarith [mul_nonneg (sub_nonneg.mpr hg4) he]
  · change q ≤ (5 / 4 : ℝ) * e
    nlinarith [mul_nonneg (sub_nonneg.mpr hg4) he]

end AVRegularity.Weighted
end
end

section
@[expose] public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace AVRegularity.Weighted

/-! Monotone convergence for the nonnegative quadratic densities used in clipped tests. -/

/-- Integrals against the bounded rational clips increase to the integral against the
unclipped positive weight. -/
theorem lintegral_clipWeight_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (w f : α → ℝ) (hw : ∀ x, 0 < w x) (hf : AEMeasurable f μ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hclip : ∀ n : ℕ, Measurable (fun x => clipWeight ((n : ℝ) + 1) (w x))) :
    Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal
      (clipWeight ((n : ℝ) + 1) (w x) * f x) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (w x * f x) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable ((hclip n).aemeasurable.mul hf)
  · filter_upwards [] with x n m hnm
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (clipWeight_nat_monotone (w x) (hw x) hnm) (hf_nonneg x)
  · filter_upwards [] with x
    have hweight := clipWeight_nat_tendsto (w x) (hw x)
    have hproduct : Tendsto
        (fun n : ℕ => clipWeight ((n : ℝ) + 1) (w x) * f x) atTop
        (𝓝 (w x * f x)) := by
      simpa using hweight.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hproduct

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! Spatial cutoff flux formulas; no bound on derivatives of the metric is used. -/

theorem cutoff_weight_fderiv (χ q : Vec 2 → ℝ)
    (hχ : Differentiable ℝ χ) (hq : Differentiable ℝ q) (x : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun y => χ y ^ 2 * q y) x (basisVec i) =
      χ x ^ 2 * fderiv ℝ q x (basisVec i) +
        2 * χ x * fderiv ℝ χ x (basisVec i) * q x := by
  have h := ((hχ x).hasFDerivAt.pow 2).mul (hq x).hasFDerivAt
  change fderiv ℝ ((fun y => χ y ^ 2) * q) x (basisVec i) = _
  rw [h.fderiv]
  norm_num [add_apply, smul_apply, smul_eq_mul]
  ring

theorem cutoff_flux_divergence (χ : Vec 2 → ℝ) (hχ : Differentiable ℝ χ)
    (A : Fin 2 → Vec 2 → ℝ) (hA : ∀ i, Differentiable ℝ (A i)) (x : Vec 2) :
    (∑ i : Fin 2, fderiv ℝ (fun y => χ y ^ 2 * A i y) x (basisVec i)) =
      χ x ^ 2 * (∑ i : Fin 2, fderiv ℝ (A i) x (basisVec i)) +
        2 * χ x * (∑ i : Fin 2, fderiv ℝ χ x (basisVec i) * A i x) := by
  simp_rw [cutoff_weight_fderiv χ (A _) hχ (hA _) x]
  simp only [Fin.sum_univ_two]
  ring

theorem cutoff_weight_flux_split (χ q : Vec 2 → ℝ)
    (hχ : Differentiable ℝ χ) (hq : Differentiable ℝ q)
    (v : Vec 2 → Vec 2) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (Φ : Fin 2 → Vec 2 → ℝ) (x : Vec 2) (i : Fin 2) :
    (χ x ^ 2 * q x) * v x i +
        (∑ j : Fin 2, G x i j * fderiv ℝ (fun y => χ y ^ 2 * q y) x (basisVec j)) =
      χ x ^ 2 * (q x * v x i +
        (∑ j : Fin 2, G x i j * fderiv ℝ q x (basisVec j)) - Φ i x) +
      (χ x ^ 2 * Φ i x +
        2 * χ x * q x * ∑ j : Fin 2, G x i j * fderiv ℝ χ x (basisVec j)) := by
  simp_rw [cutoff_weight_fderiv χ q hχ hq x]
  simp only [Fin.sum_univ_two]
  ring

theorem cutoff_defect_le (χ : Vec 2 → ℝ) (hχ : Differentiable ℝ χ)
    (A : Fin 2 → Vec 2 → ℝ) (hA : ∀ i, Differentiable ℝ (A i)) (x : Vec 2)
    (dt q L : ℝ) (h : dt + (∑ i : Fin 2, fderiv ℝ (A i) x (basisVec i)) ≤ L * q) :
    χ x ^ 2 * dt +
      (∑ i : Fin 2, fderiv ℝ (fun y => χ y ^ 2 * A i y) x (basisVec i)) ≤
      L * χ x ^ 2 * q +
        2 * χ x * (∑ i : Fin 2, fderiv ℝ χ x (basisVec i) * A i x) := by
  rw [cutoff_flux_divergence χ hχ A hA x]
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (χ x))
  nlinarith only [hh]

/-! The metric hypotheses (near identity, with jet bounds) supply every coefficient entry budget,
including order zero. -/

def metricEntryEnvelope (CG : ℕ → ℝ) (g δ : ℝ) (l : ℕ) : ℝ :=
  if l = 0 then 5 / 4 else |CG l| * g * δ ^ l

theorem metricEntryEnvelope_bound {K Kmax : ℕ} (hK : K ≤ Kmax)
    {a b : ℝ} (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (CG : ℕ → ℝ) (g δ : ℝ) (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hg4 : g ≤ 1 / 4)
    (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ x j, 1 ≤ j → j ≤ Kmax → ∀ k q,
      ‖iteratedFDeriv ℝ j (fun y => G t y k q) x‖ ≤ CG j * g * δ ^ j)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (l : Fin (K + 1)) (x : Vec 2) (k q : Fin 2) :
    ‖iteratedFDeriv ℝ l.val (fun y => G t y k q) x‖ ≤ metricEntryEnvelope CG g δ l.val := by
  by_cases hl : l.val = 0
  · rw [show metricEntryEnvelope CG g δ l.val = 5 / 4 by simp [metricEntryEnvelope, hl]]
    calc
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k q) x‖ = |G t x k q| := by
        rw [hl, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      _ ≤ _ := nearIdentity_entry_abs_le G g hg4 hGnear t x (hGs t ht x) k q
  · simp only [metricEntryEnvelope, hl, ite_false]
    exact (hjets t ht x l.val (by omega) ((Nat.le_of_lt_succ l.isLt).trans hK) k q).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hg)
        (pow_nonneg hδ _))

/-! The metric quadratic-form bound applies to arbitrary finite Hilbert fibers. -/

/-- Finite Hilbert fiber expansion preserves the metric's exact coercivity constant. -/
theorem nearIdentity_hilbert_quadratic_lower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (t : ℝ) (z : Vec 2) (u : Fin 2 → E) :
    (3 / 4 : ℝ) * (∑ k : Fin 2, ‖u k‖ ^ 2) ≤
      ∑ k : Fin 2, ∑ j : Fin 2, G t z k j * inner ℝ (u k) (u j) := by
  let b := stdOrthonormalBasis ℝ E
  have he (k : Fin 2) : ‖u k‖ ^ 2 =
      ∑ a : Fin (Module.finrank ℝ E), inner ℝ (b a) (u k) ^ 2 :=
    (b.sum_sq_inner_right (u k)).symm
  have hp (k j : Fin 2) : inner ℝ (u k) (u j) =
      ∑ a : Fin (Module.finrank ℝ E), inner ℝ (b a) (u k) * inner ℝ (b a) (u j) := by
    rw [← b.sum_inner_mul_inner]
    simp only [real_inner_comm (u k)]
  have hE : (3 / 4 : ℝ) * (∑ k : Fin 2, ‖u k‖ ^ 2) =
      ∑ a : Fin (Module.finrank ℝ E), (3 / 4 : ℝ) *
        (∑ k : Fin 2, inner ℝ (b a) (u k) ^ 2) := by
    simp_rw [he, Finset.mul_sum]
    exact Finset.sum_comm
  have hQ : (∑ k : Fin 2, ∑ j : Fin 2, G t z k j * inner ℝ (u k) (u j)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ k : Fin 2, ∑ j : Fin 2,
        G t z k j * (inner ℝ (b a) (u k) * inner ℝ (b a) (u j)) := by
    simp_rw [hp, Finset.mul_sum]
    calc
      (∑ k : Fin 2, ∑ j : Fin 2, ∑ a : Fin (Module.finrank ℝ E),
          G t z k j * (inner ℝ (b a) (u k) * inner ℝ (b a) (u j))) =
          ∑ k : Fin 2, ∑ a : Fin (Module.finrank ℝ E), ∑ j : Fin 2,
            G t z k j * (inner ℝ (b a) (u k) * inner ℝ (b a) (u j)) := by
              apply Finset.sum_congr rfl
              intro k _
              exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hE, hQ]
  apply Finset.sum_le_sum
  intro a _
  have h := (nearIdentity_quadratic_bounds G g hg4 hG t z
    (fun k => inner ℝ (b a) (u k))).1
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

end AVRegularity.Weighted
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Time clamping extends exactly the given measurable plane metric and velocity. -/

/-- Extend an interval coefficient by clamping its time argument to the same interval. -/
def planeIntervalCoefficient {F : Type*} (a b : ℝ) (hab : a ≤ b)
    (C : ℝ → Vec 2 → F) : ℝ → Vec 2 → F :=
  fun t => C (Set.projIcc a b hab t)

@[simp] theorem planeIntervalCoefficient_of_mem {F : Type*} (a b : ℝ) (hab : a ≤ b)
    (C : ℝ → Vec 2 → F) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    planeIntervalCoefficient a b hab C t = C t := by
  simp only [planeIntervalCoefficient, Set.projIcc_of_mem hab ht]

/-- Joint measurability on the actual interval suffices for the clamped extension. -/
theorem planeIntervalCoefficient_measurable {F : Type*} [MeasurableSpace F]
    (a b : ℝ) (hab : a ≤ b) (C : ℝ → Vec 2 → F)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2)) :
    Measurable (Function.uncurry (planeIntervalCoefficient a b hab C)) :=
  hC.comp (((continuous_projIcc (a := a) (b := b) (h := hab)).measurable.comp
    measurable_fst).prodMk measurable_snd)

/-- Each velocity component inherits the spatial continuity of the prescribed velocity. -/
theorem planeIntervalVelocity_continuous (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (t : ℝ) (k : Fin 2) :
    Continuous (fun z => planeIntervalCoefficient a b hab v t z k) :=
  (continuous_apply k).comp (hv _ (Set.projIcc a b hab t).property)

/-- Clamping preserves every metric entry's spatial continuity. -/
theorem planeIntervalMetric_continuous (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun z => G t z k j))
    (t : ℝ) (k j : Fin 2) :
    Continuous (fun z => planeIntervalCoefficient a b hab G t z k j) :=
  hG _ (Set.projIcc a b hab t).property k j

/-- The qualitative bounded velocity supplies bounded scalar multiplier components. -/
theorem planeIntervalVelocity_bound (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (M : ℝ)
    (hv : ∀ t ∈ Set.Icc a b, ∀ z, ‖v t z‖ ≤ M) (t : ℝ) (k : Fin 2) (z : Vec 2) :
    |planeIntervalCoefficient a b hab v t z k| ≤ max M 0 := by
  have h := norm_le_pi_norm (v (Set.projIcc a b hab t) z) k
  change |v (Set.projIcc a b hab t) z k| ≤ max M 0
  have hcomp : |v (Set.projIcc a b hab t) z k| ≤ ‖v (Set.projIcc a b hab t) z‖ := by
    simpa only [Real.norm_eq_abs] using h
  exact hcomp.trans
    ((hv _ (Set.projIcc a b hab t).property z).trans (le_max_left _ _))

/-- The actual near-identity symmetric metric supplies a uniform bound after clamping. -/
theorem planeIntervalMetric_bound (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (hsym : ∀ t ∈ Set.Icc a b, ∀ z, (G t z).IsSymm)
    (t : ℝ) (k j : Fin 2) (z : Vec 2) :
    |planeIntervalCoefficient a b hab G t z k j| ≤ 5 / 4 :=
  nearIdentity_entry_abs_le G g hg4 hG _ z
    (hsym _ (Set.projIcc a b hab t).property z) k j

end AVRegularity.Weighted
end
end
