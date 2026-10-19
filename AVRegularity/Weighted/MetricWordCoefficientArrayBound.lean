-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.SlowBasisProjectionBound
import AVRegularity.Weighted.PlaneH1Readouts
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

section
section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.KernelEnergy
namespace AVRegularity.Weighted

/-! Jointly measurable metric entries give the literal measurable fiber coefficient. -/

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace T]

theorem metricFiberCoefficient_measurable
    (G : T → Matrix (Fin 2) (Fin 2) ℝ) (hG : Measurable G) :
    Measurable (fun t => metricFiberCoefficient (E := E) (G t)) := by
  unfold metricFiberCoefficient
  have : IsBoundedSMul ℝ ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => E)) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E)))
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro a _
  exact ((measurable_pi_apply a).comp ((measurable_pi_apply k).comp hG)).smul_const _

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! Actual metric commutator sources are L2 at the finite regularity of the statement. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem metricMaskTerm_memLp {K j : ℕ} {U : Set (Vec 2)} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D)
    (m : PositionMask j) (w : DerivativeWord2 j) (M : ℝ)
    (hb : ∀ x k a, |orderedScalarDerivative (fun y => G y k a)
      (maskLeftLength j m) (maskWordEquiv 2 j m w).1 x| ≤ M) :
    MemLp (metricMaskTerm hj G D m w) 2 (volume.restrict U) := by
  apply memLp_piLp_iff.mpr
  intro k
  change MemLp (fun x => ∑ a : Fin 2,
    orderedScalarDerivative (fun y => G y k a) (maskLeftLength j m)
      (maskWordEquiv 2 j m w).1 x •
    D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩,
      Fin.snoc (maskWordEquiv 2 j m w).2 a⟩ x) 2 (volume.restrict U)
  apply memLp_finsetSum
  intro a _
  have hc : Continuous (orderedScalarDerivative (fun y => G y k a)
      (maskLeftLength j m) (maskWordEquiv 2 j m w).1) := by
    apply (orderedScalarDerivative_contDiff _ (maskLeftLength j m) 0 _ _).continuous
    exact (hG k a).of_le (by
      have hh := (maskLeftLength_le j m).trans hj
      simpa only [Nat.add_zero] using (show (maskLeftLength j m : WithTop ℕ∞) ≤ (K : WithTop ℕ∞) from by exact_mod_cast hh))
  have hcoef := memLp_top_of_bound (μ := volume.restrict U) hc.aestronglyMeasurable M
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x k a))
  exact hcoef.smul (hD _)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Weighted

/-! The literal word coefficient separates into its diagonal metric and predecessor letter. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D N : ℕ}

theorem metricFlux_zero {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1) :
    metricFlux (h := h) (0 : Matrix (Fin 2) (Fin 2) ℝ) m hab hm = 0 := by
  subst b
  subst m
  ext g k
  simp [metricFlux, PiLp.continuousLinearEquiv_symm_apply]

def wordDiagonalCoefficient (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (i i' : Fin (N + 1) × ι)
    (d : admissibleOrders (fun p => κ p.1 p.2) D i i') (t : ℝ) :
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i'.2)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i.2) :=
  if i.1 = i'.1 then
    if hv : i.2 = i'.2 ∧ d.1 = 2 then metricFlux (G t - 1) (d.1 - 1) hv.1 (by omega) else 0
  else 0

def wordPredecessorCoefficient (letters : Fin N → CycleLetter ι h D)
    (κ : Fin (N + 1) → ι → ℕ) (X₀ : Vec 2) (δ : ℝ)
    (i i' : Fin (N + 1) × ι)
    (d : admissibleOrders (fun p => κ p.1 p.2) D i i') (t : ℝ) (z : Vec 2) :
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i'.2)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i.2) :=
  if hs : i.1.val = i'.1.val + 1 then
    slowEvalCoefficient
      (fun f z => taylorSlow (if (letters ⟨i'.1.val, by omega⟩).positive then 1 else 0)
        (letters ⟨i'.1.val, by omega⟩).slow f X₀ (δ • z))
      ((letters ⟨i'.1.val, by omega⟩).edge i.2 i'.2 ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z
  else 0

theorem wordChainCoefficient_split [Fintype ι] (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (κ : Fin (N + 1) → ι → ℕ) (X₀ : Vec 2) (δ : ℝ)
    (i i' : Fin (N + 1) × ι) (d : admissibleOrders (fun p => κ p.1 p.2) D i i')
    (t : ℝ) (z : Vec 2) :
    planeChainCoefficient (wordChainData G letters X₀ δ) κ i i' d t z =
      wordDiagonalCoefficient G κ i i' d t + wordPredecessorCoefficient letters κ X₀ δ i i' d t z := by
  simp only [planeChainCoefficient, wordChainData, slowEvalCoefficient, List.map_nil,
    List.sum_nil, add_zero, wordDiagonalCoefficient, wordPredecessorCoefficient]
  split_ifs <;> simp only [metricFlux_zero, zero_add]

end AVRegularity.Weighted
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.KernelEnergy
namespace AVRegularity.Weighted

/-! Multiplication by a bounded clipped chart weight preserves the plane `H¹`
test carrier. -/

noncomputable section

/-- The order-one Leibniz jet of an operator coefficient has its two usual
terms: coefficient times derivative, plus coefficient derivative times value. -/
theorem multiplicationRawJet_first_snoc {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : ℕ} (hK : 1 ≤ K) (C : Vec 2 → E →L[ℝ] F)
    (D : RawJet2 K E) (i : Fin 2) (z : Vec 2) :
    multiplicationRawJet C D
        (⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩ : JetIndex2 K) z =
      C z (D ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩ z) +
        fderiv ℝ C z (basisVec i) (D (valueIndex2 K) z) := by
  classical
  let w₀ : DerivativeWord2 0 := Fin.elim0
  let hK0 : 0 < K := by omega
  have hword : Fin.snoc w₀ i = (fun _ : Fin 1 => i) := by
    funext j
    fin_cases j
    rfl
  change (∑ p : PositionMask 0 × Bool,
      multiplicationTerm (Nat.le_of_lt_succ (by omega : 1 < K + 1)) C D p
        (Fin.snoc w₀ i) z) = _
  rw [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
  have hfalse : multiplicationTerm (Nat.le_of_lt_succ (by omega : 1 < K + 1))
      C D (PUnit.unit, false) (Fin.snoc w₀ i) z =
      C z (D ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩ z) := by
    rw [multiplicationTerm_snoc_false hK0 C D PUnit.unit w₀ i z]
    simp [maskWordEquiv, maskLeftLength, maskRightLength,
      orderedCoefficientDerivative, nextIndex2, nextIndex]
    rw [hword]
  have htrue : multiplicationTerm (Nat.le_of_lt_succ (by omega : 1 < K + 1))
      C D (PUnit.unit, true) (Fin.snoc w₀ i) z =
      fderiv ℝ C z (basisVec i) (D (valueIndex2 K) z) := by
    rw [multiplicationTerm_snoc_true hK0 C D PUnit.unit w₀ i z]
    simp [maskWordEquiv, maskLeftLength, maskRightLength,
      orderedCoefficientDerivative, lowerIndex2, lowerIndex, valueIndex2, valueIndex]
  simpa [w₀, add_comm] using congrArg₂ (· + ·) htrue hfalse

end

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Integrate the actual metric mask bound without a Hilbert fiber dimension cost. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
variable {U : Set (Vec 2)}

def metricMaskL2Array {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (metricMaskTerm hj G D m w) 2 (volume.restrict U)) (m : PositionMask j) :
    PiLp 2 (fun _ : DerivativeWord2 j => ComponentL2 (volume.restrict U)
      (PiLp 2 (fun _ : Fin 2 => E))) :=
  WithLp.toLp 2 fun w => (hT m w).toLp (metricMaskTerm hj G D m w)

theorem metricMaskL2Array_normSq_le {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (metricMaskTerm hj G D m w) 2 (volume.restrict U))
    (hD : JetMemL2On U D) (m : PositionMask j) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x w k a, |orderedScalarDerivative (fun y => G y k a)
      (maskLeftLength j m) w x| ≤ M) :
    ‖metricMaskL2Array hj G D hT m‖ ^ 2 ≤
      (Fintype.card (DerivativeWord2 (maskLeftLength j m)) : ℝ) * (4 * M) ^ 2 *
        derivativeNormSq (jetToL2 D hD)
          ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩ := by
  let r : Fin (K + 2) := ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩
  let A : ℝ := (Fintype.card (DerivativeWord2 (maskLeftLength j m)) : ℝ) * (4 * M) ^ 2
  let T := fun w : DerivativeWord2 j => metricMaskTerm hj G D m w
  have hTm : ∀ w, MemLp (T w) 2 (volume.restrict U) := hT m
  have hleft := integrable_finsetSum Finset.univ (fun w _ => integrable_normSq_of_memLp (hTm w))
  have hright := integrable_finsetSum Finset.univ
    (fun w _ => integrable_normSq_of_memLp (hD ⟨r, w⟩))
  calc
    ‖metricMaskL2Array hj G D hT m‖ ^ 2 = ∫ x in U, ∑ w : DerivativeWord2 j, ‖T w x‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      change (∑ w : DerivativeWord2 j, ‖(hTm w).toLp (T w)‖ ^ 2) = _
      simp_rw [normSq_toLp_eq_integral]
      exact (integral_finsetSum Finset.univ (fun w _ => integrable_normSq_of_memLp (hTm w))).symm
    _ ≤ ∫ x in U, A * ∑ w : DerivativeWord2 r.val, ‖D ⟨r, w⟩ x‖ ^ 2 := by
      apply integral_mono hleft (hright.const_mul A)
      intro x
      exact metricMaskTerm_pointwise_sumSq_le hj G D m x hM (hb x)
    _ = A * derivativeNormSq (jetToL2 D hD) r := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun w _ => integrable_normSq_of_memLp (hD ⟨r, w⟩))]
      change A * (∑ w : DerivativeWord2 r.val, ∫ x in U, ‖D ⟨r, w⟩ x‖ ^ 2) =
        A * ∑ w : DerivativeWord2 r.val, ‖(hD ⟨r, w⟩).toLp (D ⟨r, w⟩)‖ ^ 2
      congr 1
      apply Finset.sum_congr rfl
      intro w _
      exact (normSq_toLp_eq_integral (hD ⟨r, w⟩)).symm

theorem metricMaskL2Array_norm_le {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (metricMaskTerm hj G D m w) 2 (volume.restrict U))
    (hD : JetMemL2On U D) (m : PositionMask j) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x w k a, |orderedScalarDerivative (fun y => G y k a)
      (maskLeftLength j m) w x| ≤ M) :
    ‖metricMaskL2Array hj G D hT m‖ ≤
      Real.sqrt (Fintype.card (DerivativeWord2 (maskLeftLength j m)) : ℝ) * (4 * M) *
        Real.sqrt (derivativeNormSq (jetToL2 D hD)
          ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩) := by
  have hn : 0 ≤ derivativeNormSq (jetToL2 D hD)
      ⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩ :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hn]
  exact metricMaskL2Array_normSq_le hj G D hT hD m hM hb

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! The unique metric mask without coefficient derivatives is the principal diffusion. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem metricMaskTerm_principal {K j : ℕ} (hj : j ≤ K)
    (D : RawJet2 (K + 1) E) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (m : PositionMask j) (hm : maskLeftLength j m = 0)
    (w : DerivativeWord2 j) (x : Vec 2) :
    metricMaskTerm hj G D m w x = finiteMetricFlux (G x)
      (WithLp.toLp 2 (fun k : Fin 2 => D ⟨⟨j + 1, by omega⟩, Fin.snoc w k⟩ x)) := by
  have hc (c : Vec 2 → ℝ) (r : ℕ) (hr : r = 0) (a : DerivativeWord2 r) :
      orderedScalarDerivative c r a = c := by
    subst r
    rfl
  unfold metricMaskTerm
  simp_rw [hc _ _ hm]
  congr 1
  apply PiLp.ext
  intro k
  have hw := zero_left_mask_word
    (fun r a => if hr : r ≤ K then D ⟨⟨r + 1, by omega⟩, Fin.snoc a k⟩ x else 0)
    j m hm w
  simp only [dite_eq_left ((maskRightLength_le j m).trans hj), dite_eq_left hj] at hw
  exact hw

theorem metricMaskTerm_principal_sum {K j : ℕ} (hj : j ≤ K)
    (D : RawJet2 (K + 1) E) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : DerivativeWord2 j) (x : Vec 2) :
    (∑ m : PositionMask j, if maskLeftLength j m = 0 then metricMaskTerm hj G D m w x else 0) =
      finiteMetricFlux (G x)
        (WithLp.toLp 2 (fun k : Fin 2 => D ⟨⟨j + 1, by omega⟩, Fin.snoc w k⟩ x)) := by
  have he (m : PositionMask j) :
      (if maskLeftLength j m = 0 then metricMaskTerm hj G D m w x else 0) =
      if maskLeftLength j m = 0 then finiteMetricFlux (G x)
        (WithLp.toLp 2 (fun k : Fin 2 => D ⟨⟨j + 1, by omega⟩, Fin.snoc w k⟩ x)) else 0 := by
    split_ifs with hm
    · exact metricMaskTerm_principal hj D G m hm w x
    · rfl
  simp_rw [he]
  exact sum_zero_left_masks j _

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Literal diagonal and predecessor coupling fluxes of the finite word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

def wordCouplingInput (κ : Fin (N + 1) → ι → ℕ) (i i' : Fin (N + 1) × ι)
    (d : admissibleOrders (fun p => κ p.1 p.2) D i i')
    (W : PlaneHk Set.univ (κ i'.1 i'.2 + 1) (h i'.2)) (z : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i'.2) :=
  WithLp.toLp 2 (fun word => W.toFunction.jet
    ⟨⟨d.1 - 1, by
      have hh := Finset.mem_filter.mp d.2
      have ho := Finset.mem_Icc.mp hh.1
      have hs := hh.2
      change κ i.1 i.2 + d.1 ≤ κ i'.1 i'.2 + 2 at hs
      omega⟩, word⟩ z)

def wordDiagonalFlux (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (κ : Fin (N + 1) → ι → ℕ)
    (W : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i.2) :=
  ∑ i', ∑ d : admissibleOrders (fun p => κ p.1 p.2) D i i',
    wordDiagonalCoefficient G κ i i' d t (wordCouplingInput κ i i' d (W i') z)

def wordPredecessorFlux (letters : Fin N → CycleLetter ι h D)
    (κ : Fin (N + 1) → ι → ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i.2) :=
  ∑ i', ∑ d : admissibleOrders (fun p => κ p.1 p.2) D i i',
    wordPredecessorCoefficient letters κ X₀ δ i i' d t z (wordCouplingInput κ i i' d (W i') z)

def wordChainRawFlux (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (κ : Fin (N + 1) → ι → ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i.2) :=
  ∑ i', ∑ d : admissibleOrders (fun p => κ p.1 p.2) D i i',
    planeChainCoefficient (wordChainData G letters X₀ δ) κ i i' d t z
      (wordCouplingInput κ i i' d (W i') z)

theorem wordChainRawFlux_split (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (κ : Fin (N + 1) → ι → ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) :
    wordChainRawFlux G letters κ X₀ δ W i t z =
      wordDiagonalFlux (D := D) G κ W i t z + wordPredecessorFlux letters κ X₀ δ W i t z := by
  simp only [wordChainRawFlux, wordChainCoefficient_split, add_apply,
    Finset.sum_add_distrib, wordDiagonalFlux, wordPredecessorFlux]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The complete nonprincipal metric source is square integrable on the true plane graph. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem metricCommutatorTerm_memLp {K j : ℕ} {U : Set (Vec 2)} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : ℕ → ℝ)
    (hb : ∀ l, l ≤ K → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G y k a) x‖ ≤ M l)
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D)
    (w : DerivativeWord2 j) :
    MemLp (metricCommutatorTerm hj G D w) 2 (volume.restrict U) := by
  unfold metricCommutatorTerm
  apply memLp_finsetSum
  intro m _
  by_cases hm : 1 ≤ maskLeftLength j m
  · simp only [ite_eq_left hm]
    apply metricMaskTerm_memLp hj G hG D hD m w (M (maskLeftLength j m))
    intro x k a
    simpa only [Real.norm_eq_abs] using
      (orderedScalarDerivative_norm_le (fun y => G y k a) (maskLeftLength j m)
        ((hG k a).of_le (by exact_mod_cast (maskLeftLength_le j m).trans hj))
        (maskWordEquiv 2 j m w).1 x).trans
          (hb _ ((maskLeftLength_le j m).trans hj) x k a)
  · simp only [ite_eq_right hm]
    exact MemLp.zero

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The diagonal part of the native word flux is exactly the scalar metric deviation flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordDiagonalFlux_eq (hD : 2 ≤ D) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (κ : Fin (N + 1) → ι → ℕ)
    (W : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) (k : Fin 2) :
    wordDiagonalFlux (D := D) G κ W i t z k = ∑ j : Fin 2, (G t - 1) k j •
      (W i).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => j⟩ z := by
  classical
  unfold wordDiagonalFlux
  rw [Finset.sum_eq_single i]
  · have hd2 : 2 ∈ admissibleOrders (fun p => κ p.1 p.2) D i i := by
      simp [admissibleOrders, hD]
    let d2 : admissibleOrders (fun p => κ p.1 p.2) D i i := ⟨2, hd2⟩
    rw [Finset.sum_eq_single d2]
    · simp [wordDiagonalCoefficient, d2, metricFlux, wordCouplingInput]
    · intro d _ hne
      have hd : d.1 ≠ 2 := fun h => hne (Subtype.ext h)
      simp [wordDiagonalCoefficient, hd]
    · intro hn
      exact (hn (Finset.mem_univ d2)).elim
  · intro i' _ hne
    apply Finset.sum_eq_zero
    intro d _
    by_cases hl : i.1 = i'.1
    · have hc : i.2 ≠ i'.2 := fun he => hne (Prod.ext hl.symm he.symm)
      simp [wordDiagonalCoefficient, hl, hc]
    · simp [wordDiagonalCoefficient, hl]
  · intro hn
    exact (hn (Finset.mem_univ i)).elim

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! The actual truncated slow polynomial retains all reserved fast derivatives. -/

theorem taylorSlow_spatial_contDiff (lo Ks J : ℕ)
    (f : Vec 2 → Vec 2 → ℝ)
    (hf : ContDiff ℝ (Ks + J : ℕ) (Function.uncurry f))
    (X₀ : Vec 2) (δ : ℝ) :
    ContDiff ℝ (J : ℕ) (fun z => taylorSlow lo Ks (fun X => f X z) X₀ (δ • z)) := by
  unfold taylorSlow
  apply ContDiff.sum
  intro r hr
  have hrK := (Finset.mem_Icc.mp hr).2
  have hh := joint_partialIteratedFDeriv_left_contDiff J r (Function.uncurry f)
    (hf.of_le (by exact_mod_cast (show J + r ≤ Ks + J by omega)))
  have ha : ContDiff ℝ (J : ℕ)
      (fun z => iteratedFDeriv ℝ r (fun X => f X z) X₀) :=
    hh.comp (contDiff_const.prodMk contDiff_id)
  exact contDiff_const.mul (multilinear_diagonal_contDiff J _ ha δ)

/-! The compact chart test's pointwise energy inequality for the actual metric. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def cutoffEnergyResidual
    (G : Matrix (Fin 2) (Fin 2) ℝ) (v p Φ h : PiLp 2 (fun _ : Fin 2 => ℝ))
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E) (χ q : ℝ) : ℝ :=
    2 * χ * inner ℝ h (q • v + finiteMetricFlux G p - Φ) * ‖u‖ ^ 2 -
      2 * χ ^ 2 * inner ℝ du (scalarHilbertTensor Φ u) -
      4 * χ * q * inner ℝ du (scalarHilbertTensor (finiteMetricFlux G h) u) -
      2 * χ ^ 2 * q * inner ℝ F du -
      2 * χ ^ 2 * inner ℝ F (scalarHilbertTensor p u) -
      4 * χ * q * inner ℝ F (scalarHilbertTensor h u)

theorem cutoff_chart_metric_pointwise
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (t : ℝ) (x : Vec 2) (hGs : (G t x).IsSymm)
    (v p Φ h : PiLp 2 (fun _ : Fin 2 => ℝ))
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E)
    {q lam M χ η : ℝ} (hq : 0 ≤ q) (hlam : 0 ≤ lam) (hM : 0 ≤ M)
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hη : 0 ≤ η)
    (hv : ‖v‖ ≤ 2 * M) (hp : ‖p‖ ≤ Real.sqrt lam * q)
    (hΦ : ‖Φ‖ ≤ Real.sqrt lam * q) (hh : ‖h‖ ≤ 2 * η) :
    2 * lam * χ ^ 2 * q * ‖u‖ ^ 2 + cutoffEnergyResidual (G t x) v p Φ h du F u χ q -
      2 * χ ^ 2 * q * (∑ k : Fin 2, ∑ j : Fin 2,
        G t x k j * inner ℝ (du k) (du j)) + χ ^ 2 * q * ‖du‖ ^ 2 ≤
    18 * lam * χ ^ 2 * q * ‖u‖ ^ 2 + 8 * q * ‖F‖ ^ 2 +
      (4096 * η ^ 2 + 16 * M * η) * q * ‖u‖ ^ 2 := by
  have hGb : ∀ i j, |G t x i j| ≤ 5 / 4 :=
    nearIdentity_entry_abs_le G g hg4 hG t x hGs
  have hQ : (3 / 4 : ℝ) * ‖du‖ ^ 2 ≤
      ∑ k : Fin 2, ∑ j : Fin 2, G t x k j * inner ℝ (du k) (du j) := by
    rw [PiLp.norm_sq_eq_of_L2 _ du]
    exact nearIdentity_hilbert_quadratic_lower G g hg4 hG t x du
  exact cutoff_pointwise_energy_absorption hχ hχ1 hη hM hq (Real.sq_sqrt hlam) hQ
    (cutoff_residual_bound (G t x) hGb v p Φ h du F u hq (Real.sqrt_nonneg _) hM
      hχ hη hv hp hΦ hh)
end

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! Exact binomial recombination of the genuine metric commutator source. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
variable {U : Set (Vec 2)}

def metricCommutatorL2Array {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (metricMaskTerm hj G D m w) 2 (volume.restrict U)) :
    PiLp 2 (fun _ : DerivativeWord2 j => ComponentL2 (volume.restrict U)
      (PiLp 2 (fun _ : Fin 2 => E))) :=
  ∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then metricMaskL2Array hj G D hT m else 0

def metricMaskPrice (M : ℕ → ℝ) (l : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (DerivativeWord2 l) : ℝ) * (4 * M l)

theorem metricCommutatorL2Array_norm_le {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (metricMaskTerm hj G D m w) 2 (volume.restrict U))
    (hD : JetMemL2On U D) (M : ℕ → ℝ) (hM : ∀ l, 0 ≤ M l)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x w k a,
      |orderedScalarDerivative (fun y => G y k a) l w x| ≤ M l) :
    ‖metricCommutatorL2Array hj G D hT‖ ≤
      ∑ l ∈ (Finset.range (j + 1)).erase 0, (j.choose l : ℝ) * metricMaskPrice M l *
        finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) (j - l + 1) := by
  let Y := finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r))
  calc
    ‖metricCommutatorL2Array hj G D hT‖ ≤ ∑ m : PositionMask j,
        ‖if 1 ≤ maskLeftLength j m then metricMaskL2Array hj G D hT m else 0‖ := norm_sum_le _ _
    _ ≤ ∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then
        metricMaskPrice M (maskLeftLength j m) * Y (maskRightLength j m + 1) else 0 := by
      apply Finset.sum_le_sum
      intro m _
      by_cases hm : 1 ≤ maskLeftLength j m
      · simp only [ite_eq_left hm]
        dsimp only [Y]
        rw [finiteSequence_of_le _ (by have := maskRightLength_le j m; omega)]
        exact metricMaskL2Array_norm_le hj G D hT hD m (hM _)
          (hb _ hm ((maskLeftLength_le j m).trans hj))
      · simp only [ite_eq_right hm, norm_zero, le_refl]
    _ = _ := by
      rw [sum_nonprincipal_masks j (fun l r => metricMaskPrice M l * Y (r + 1))]
      simp only [Y, mul_assoc]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.KernelEnergy
namespace AVRegularity.Weighted

/-! The literal ordered metric coefficient derivatives are its entrywise scalar derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem metricFiberCoefficient_orderedDerivative
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (l : ℕ)
    (hG : ∀ k a, ContDiff ℝ (l : ℕ) (fun x => G x k a))
    (w : DerivativeWord2 l) (x : Vec 2) :
    orderedCoefficientDerivative (fun y => metricFiberCoefficient (E := E) (G y)) l w x =
      metricFiberCoefficient (fun k a => orderedScalarDerivative (fun y => G y k a) l w x) := by
  let T := fun k a : Fin 2 =>
    (tensorEntryCLM (E := E) k).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) a)
  have : IsBoundedSMul ℝ ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => E)) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E)))
  have hc (k a : Fin 2) : ContDiff ℝ (l : ℕ) (fun y => G y k a • T k a) :=
    (hG k a).smul_const _
  have hout (k : Fin 2) : ContDiff ℝ (l : ℕ) (fun y => ∑ a : Fin 2, G y k a • T k a) :=
    ContDiff.sum (fun a _ => hc k a)
  change orderedCoefficientDerivative (fun y => ∑ k : Fin 2, ∑ a : Fin 2,
    G y k a • T k a) l w x = ∑ k : Fin 2, ∑ a : Fin 2,
      orderedScalarDerivative (fun y => G y k a) l w x • T k a
  rw [orderedCoefficientDerivative_finset_sum Finset.univ _ l (fun k _ => hout k) w]
  dsimp only
  apply Finset.sum_congr rfl
  intro k _
  rw [orderedCoefficientDerivative_finset_sum Finset.univ _ l (fun a _ => hc k a) w]
  dsimp only
  apply Finset.sum_congr rfl
  intro a _
  exact congrFun (orderedCoefficientDerivative_smul_const
    (fun y => G y k a) l (hG k a) (T k a) w) x

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Entry envelopes supply each actual stored metric commutator's spatial source class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem metricRawCommutator_memLp {K : ℕ} {U : Set (Vec 2)}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D) (α : JetIndex2 K) :
    MemLp (metricCommutatorTerm (Nat.le_of_lt_succ α.1.isLt) G D α.2)
      2 (volume.restrict U) := by
  exact metricCommutatorTerm_memLp (Nat.le_of_lt_succ α.1.isLt) G hG
    (fun l => if hl : l ≤ K then M ⟨l, by omega⟩ else 0)
    (fun l hl x k a => by simpa only [dite_eq_left hl] using hb ⟨l, by omega⟩ x k a)
    D hD α.2

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The scalar chain's literal coefficient arrays inherit spatial regularity from the metric. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem scalarChainCoefficient_contDiff
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (i i' : Fin 1 × ι) (d : admissibleOrders (fun p => κ p.1 p.2) 2 i i')
    (t : ℝ) (hG : ∀ k j, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j)) :
    ContDiff ℝ (κ i.1 i.2 : ℕ)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t) := by
  classical
  by_cases he : i = i'
  · subst i'
    have heq : planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i d t =
        fun x => metricFlux (h := h) (G t x - 1) (d.val - 1) (a := i.2) rfl
          (by have hd := scalarChain_order_eq_two κ i i d; omega) := by
      funext x
      exact scalarChainCoefficient_diagonal G κ i d t x
    rw [heq]
    apply metricFlux_contDiff
    intro k j
    exact (hG k j).sub contDiff_const
  · have hc : i.2 ≠ i'.2 := by
      intro hc
      exact he (Prod.ext (Subsingleton.elim _ _) hc)
    have heq : planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t =
        fun _ => 0 := by
      funext x
      exact scalarChainCoefficient_offDiagonal G κ i i' hc d t x
    rw [heq]
    exact contDiff_const

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Weighted

/-! The flux and source terms of the compact test expand to its bounded residual. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalarHilbertTensor_add (a b : PiLp 2 (fun _ : Fin 2 => ℝ)) (u : E) :
    scalarHilbertTensor (a + b) u = scalarHilbertTensor a u + scalarHilbertTensor b u := by
  apply PiLp.ext
  intro i
  change (a i + b i) • u = a i • u + b i • u
  exact add_smul _ _ _

theorem scalarHilbertTensor_smul (c : ℝ) (a : PiLp 2 (fun _ : Fin 2 => ℝ)) (u : E) :
    scalarHilbertTensor (c • a) u = c • scalarHilbertTensor a u := by
  apply PiLp.ext
  intro i
  change (c * a i) • u = c • (a i • u)
  exact mul_smul _ _ _

theorem cutoff_residual_eq
    (G : Matrix (Fin 2) (Fin 2) ℝ) (v p Φ h : PiLp 2 (fun _ : Fin 2 => ℝ))
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E) (χ q : ℝ) :
    2 * χ * inner ℝ h (q • v + finiteMetricFlux G p - Φ) * ‖u‖ ^ 2 -
      2 * inner ℝ du (scalarHilbertTensor
        (χ ^ 2 • Φ + (2 * χ * q) • finiteMetricFlux G h) u) -
      2 * inner ℝ F ((χ ^ 2 * q) • du + χ ^ 2 • scalarHilbertTensor p u +
        (2 * χ * q) • scalarHilbertTensor h u) =
      cutoffEnergyResidual G v p Φ h du F u χ q := by
  rw [scalarHilbertTensor_add, scalarHilbertTensor_smul, scalarHilbertTensor_smul]
  simp only [inner_add_right, real_inner_smul_right, cutoffEnergyResidual]
  ring

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Finite metric entry bounds control the actual coefficient operator array. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem finitePiLp_norm_le_sum {J F : Type*} [Fintype J] [DecidableEq J]
    [NormedAddCommGroup F] (A : PiLp 2 (fun _ : J => F)) :
    ‖A‖ ≤ ∑ w : J, ‖A w‖ := by
  have he : A = ∑ w : J, PiLp.single 2 w (A w) := by
    apply PiLp.ext
    intro w
    simp
  rw [he]
  exact (norm_sum_le _ _).trans_eq (by simp)

theorem metricFiberCoefficient_array_norm_le
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (j : ℕ)
    (hG : ∀ k a, ContDiff ℝ (j : ℕ) (fun x => G x k a))
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ w : DerivativeWord2 j, ∀ x k a,
      |orderedScalarDerivative (fun y => G y k a) j w x| ≤ M) (x : Vec 2) :
    ‖coefficientDerivativeArray (fun y => metricFiberCoefficient (E := E) (G y)) j x‖ ≤
      (Fintype.card (DerivativeWord2 j) : ℝ) * (4 * M) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  let A := coefficientDerivativeArray (fun y => metricFiberCoefficient (E := E) (G y)) j x z
  calc
    ‖A‖ ≤ ∑ w : DerivativeWord2 j, ‖A w‖ := finitePiLp_norm_le_sum A
    _ ≤ ∑ _w : DerivativeWord2 j, (4 * M) * ‖z‖ := by
      apply Finset.sum_le_sum
      intro w _
      change ‖orderedCoefficientDerivative (fun y => metricFiberCoefficient (E := E) (G y)) j w x z‖ ≤ _
      rw [metricFiberCoefficient_orderedDerivative G j hG w x]
      exact (ContinuousLinearMap.le_opNorm (metricFiberCoefficient (E := E)
        (fun k a => orderedScalarDerivative (fun y => G y k a) j w x)) z).trans
        (mul_le_mul_of_nonneg_right (metricFiberCoefficient_norm_le (E := E) _ hM (hb w x))
          (norm_nonneg z))
    _ = _ := by simp; ring

theorem metricFiberCoefficient_array_bound_entries {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (l : Fin (K + 1)) (x : Vec 2) :
    ‖coefficientDerivativeArray (fun y => metricFiberCoefficient (E := E) (G y)) l.val x‖ ≤
      (Fintype.card (DerivativeWord2 l.val) : ℝ) * (4 * M l) := by
  exact metricFiberCoefficient_array_norm_le G l.val
    (fun k a => (hG k a).of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt))
    ((norm_nonneg (iteratedFDeriv ℝ l.val (fun y => G y 0 0) 0)).trans (hb l 0 0 0))
    (fun w y k a => by
      simpa only [Real.norm_eq_abs] using
        (orderedScalarDerivative_norm_le (fun z => G z k a) l.val
          ((hG k a).of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt)) w y).trans
            (hb l y k a)) x
end

/-! A finite radius reserve makes every positive-order metric coefficient price small. -/

def metricRadiusConstant (K : ℕ) (CG : ℕ → ℝ) : ℝ :=
  ∑ l : Fin (K + 1), if l.val = 0 then 0 else
    Real.sqrt (Fintype.card (DerivativeWord2 l.val) : ℝ) * 4 * |CG l.val| /
      (l.val.factorial : ℝ)

theorem metricRadiusConstant_nonneg (K : ℕ) (CG : ℕ → ℝ) :
    0 ≤ metricRadiusConstant K CG := by
  apply Finset.sum_nonneg
  intro l _
  split_ifs <;> positivity

theorem metric_positive_jet_price_le (K : ℕ) (CG : ℕ → ℝ)
    (ρ δ g : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1) :
    (∑ l : Fin (K + 1), factorialRootWeight ρ l.val *
      (if l.val = 0 then 0 else metricMaskPrice (fun j => |CG j| * g * δ ^ j) l.val)) ≤
      metricRadiusConstant K CG * g * (ρ * δ) := by
  unfold metricRadiusConstant
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l _
  by_cases hl : l.val = 0
  · simp [hl]
  · simp only [hl, ite_false]
    have hp : (ρ * δ) ^ l.val ≤ ρ * δ := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hl
      rw [hk, pow_succ]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pow_le_one₀ (mul_nonneg hρ hδ) hscale : (ρ * δ) ^ k ≤ 1) (mul_nonneg hρ hδ)
    have hc : 0 ≤ (Real.sqrt (Fintype.card (DerivativeWord2 l.val) : ℝ) * 4 *
        |CG l.val| / (l.val.factorial : ℝ)) * g := by positivity
    calc
      factorialRootWeight ρ l.val * metricMaskPrice (fun j => |CG j| * g * δ ^ j) l.val =
          (Real.sqrt (Fintype.card (DerivativeWord2 l.val) : ℝ) * 4 * |CG l.val| /
            (l.val.factorial : ℝ)) * g * (ρ * δ) ^ l.val := by
        unfold factorialRootWeight metricMaskPrice
        rw [mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hc

/-! The scalar chain's literal coefficient arrays inherit spatial regularity from the metric. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

theorem scalarChainCoefficient_measurable
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (ta tb : ℝ) (hG : Measurable (fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2))
    (i i' : Fin 1 × ι) (d : admissibleOrders (fun p => κ p.1 p.2) 2 i i') :
    Measurable (fun p : Set.Icc ta tb × Vec 2 =>
      planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d p.1 p.2) := by
  classical
  by_cases he : i = i'
  · subst i'
    have heq : (fun p : Set.Icc ta tb × Vec 2 =>
        planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i d p.1 p.2) =
        fun p => metricFlux (h := h) (G p.1 p.2 - 1) (d.val - 1) (a := i.2) rfl
          (by have hd := scalarChain_order_eq_two κ i i d; omega) := by
      funext p
      exact scalarChainCoefficient_diagonal G κ i d p.1 p.2
    rw [heq]
    have hdev : Measurable (fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2 - 1) := by
      apply measurable_pi_iff.mpr
      intro k
      apply measurable_pi_iff.mpr
      intro j
      exact ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hG)).sub measurable_const
    exact metricFlux_measurable _ hdev (d.val - 1) rfl
      (by have hd := scalarChain_order_eq_two κ i i d; omega)
  · have hc : i.2 ≠ i'.2 := by
      intro hc
      exact he (Prod.ext (Subsingleton.elim _ _) hc)
    have heq : (fun p : Set.Icc ta tb × Vec 2 =>
        planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d p.1 p.2) =
        fun _ => 0 := by
      funext p
      exact scalarChainCoefficient_offDiagonal G κ i i' hc d p.1 p.2
    rw [heq]
    exact measurable_const
end

/-! A single maximal-slot metric budget controls every smaller component slot. -/

theorem metricRadiusConstant_mono {K L : ℕ} (hKL : K ≤ L) (CG : ℕ → ℝ) :
    metricRadiusConstant K CG ≤ metricRadiusConstant L CG := by
  let f : ℕ → ℝ := fun l => if l = 0 then 0 else
    Real.sqrt (Fintype.card (DerivativeWord2 l) : ℝ) * 4 * |CG l| / (l.factorial : ℝ)
  change (∑ l : Fin (K + 1), f l.val) ≤ ∑ l : Fin (L + 1), f l.val
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hKL))
  intro j _ _
  dsimp only [f]
  split_ifs <;> positivity

/-! A scalar coefficient times a fixed Hilbert map has a finite array norm bound. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem scalar_operator_array_norm_le (c : Vec 2 → ℝ) (j : ℕ)
    (hc : ContDiff ℝ (j : ℕ) c) (T : E →L[ℝ] F) (x : Vec 2) :
    ‖coefficientDerivativeArray (fun y => c y • T) j x‖ ≤
      (Fintype.card (DerivativeWord2 j) : ℝ) * (‖iteratedFDeriv ℝ j c x‖ * ‖T‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    _ ≤ ∑ w : DerivativeWord2 j,
        ‖coefficientDerivativeArray (fun y => c y • T) j x z w‖ := finitePiLp_norm_le_sum _
    _ ≤ ∑ _w : DerivativeWord2 j, (‖iteratedFDeriv ℝ j c x‖ * ‖T‖) * ‖z‖ := by
      apply Finset.sum_le_sum
      intro w _
      change ‖orderedCoefficientDerivative (fun y => c y • T) j w x z‖ ≤ _
      rw [congrFun (orderedCoefficientDerivative_smul_const c j hc T w) x]
      simp only [smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul (orderedScalarDerivative_norm_le c j hc w x)
        (ContinuousLinearMap.le_opNorm T z) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The actual metric commutator factorial norm is controlled by gradient energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
variable {U : Set (Vec 2)}

theorem metricCommutator_factorial_norm_le {K : ℕ}
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D)
    (hT : ∀ (j : Fin (K + 1)) (m : PositionMask j.val) (w : DerivativeWord2 j.val),
      MemLp (metricMaskTerm (Nat.le_of_lt_succ j.isLt) G D m w) 2 (volume.restrict U))
    (M : ℕ → ℝ) (hM : ∀ l, 0 ≤ M l)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x w k a,
      |orderedScalarDerivative (fun y => G y k a) l w x| ≤ M l) :
    ‖WithLp.toLp 2 (fun j : Fin (K + 1) => factorialRootWeight ρ j.val *
      ‖metricCommutatorL2Array (Nat.le_of_lt_succ j.isLt) G D (hT j)‖)‖ ≤
      (∑ l : Fin (K + 1), factorialRootWeight ρ l.val *
        (if l.val = 0 then 0 else metricMaskPrice M l.val)) *
      Real.sqrt (gradFactorialNormSq ρ (jetToL2 D hD)) := by
  let A := fun l : Fin (K + 1) => if l.val = 0 then 0 else metricMaskPrice M l.val
  let Y := fun r : Fin (K + 1) => Real.sqrt
    (derivativeNormSq (jetToL2 D hD) ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩)
  let S := fun j : Fin (K + 1) =>
    ‖metricCommutatorL2Array (Nat.le_of_lt_succ j.isLt) G D (hT j)‖
  have hA : ∀ l, 0 ≤ A l := by
    intro l
    dsimp only [A]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (hM _))
  have hA0 : A 0 = 0 := by simp [A]
  have hbound (j : Fin (K + 1)) : S j ≤
      ∑ l ∈ (Finset.range (j.val + 1)).erase 0,
        (j.val.choose l : ℝ) * finiteSequence A l * finiteSequence Y (j.val - l) := by
    refine (metricCommutatorL2Array_norm_le (Nat.le_of_lt_succ j.isLt)
      G D (hT j) hD M hM hb).trans_eq ?_
    apply Finset.sum_congr rfl
    intro l hl
    have hl0 : l ≠ 0 := (Finset.mem_erase.mp hl).1
    have hlj : l ≤ j.val := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hl).2)
    have hlK : l ≤ K := hlj.trans (Nat.le_of_lt_succ j.isLt)
    have hrK : j.val - l ≤ K := (Nat.sub_le _ _).trans (Nat.le_of_lt_succ j.isLt)
    rw [finiteSequence_of_le A hlK, finiteSequence_of_le Y hrK,
      finiteSequence_of_le _ (by omega : j.val - l + 1 ≤ K + 1)]
    simp only [A, hl0, ite_false, Y]
  have h := nonprincipal_factorial_norm_le ρ hρ A Y S hA hA0
    (fun j => norm_nonneg _) hbound
  rw [show WithLp.toLp 2 (fun j => factorialRootWeight ρ j.val * Y j) =
      gradientFactorialSequence ρ (jetToL2 D hD) from rfl,
    gradientFactorialSequence_norm] at h
  exact h

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Stored metric word coefficients inherit the entrywise derivative envelopes. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem metricFlux_orderedDerivative (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (l : ℕ)
    (hM : ∀ k j, ContDiff ℝ (l : ℕ) (fun x => M x k j))
    {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1)
    (w : DerivativeWord2 l) (x : Vec 2) :
    orderedCoefficientDerivative (fun y => metricFlux (h := h) (M y) m hab hm) l w x =
      ∑ k : Fin 2, ∑ j : Fin 2,
        orderedScalarDerivative (fun y => M y k j) l w x • metricWordEntry (h := h) m hab hm k j := by
  have : IsBoundedSMul ℝ ((PiLp 2 (fun _ : DerivativeWord2 m => h b)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h a)) := NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
        (E := ((PiLp 2 (fun _ : DerivativeWord2 m => h b)) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => h a)))
  let T := fun k j => metricWordEntry (h := h) m hab hm k j
  have hc (k j : Fin 2) : ContDiff ℝ (l : ℕ) (fun y => M y k j • T k j) :=
    (hM k j).smul_const _
  have hout (k : Fin 2) : ContDiff ℝ (l : ℕ) (fun y => ∑ j : Fin 2, M y k j • T k j) :=
    ContDiff.sum (fun j _ => hc k j)
  simp_rw [metricFlux_entry_expansion]
  rw [orderedCoefficientDerivative_finset_sum Finset.univ _ l (fun k _ => hout k) w]
  dsimp only
  apply Finset.sum_congr rfl
  intro k _
  rw [orderedCoefficientDerivative_finset_sum Finset.univ _ l (fun j _ => hc k j) w]
  dsimp only
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (orderedCoefficientDerivative_smul_const
    (fun y => M y k j) l (hM k j) (T k j) w) x

end AVRegularity.Weighted
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Squared source energy bound for the actual factorial metric commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
variable {U : Set (Vec 2)}

theorem metricCommutator_factorial_energy_le {K : ℕ}
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D)
    (hT : ∀ (j : Fin (K + 1)) (m : PositionMask j.val) (w : DerivativeWord2 j.val),
      MemLp (metricMaskTerm (Nat.le_of_lt_succ j.isLt) G D m w) 2 (volume.restrict U))
    (M : ℕ → ℝ) (hM : ∀ l, 0 ≤ M l)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x w k a,
      |orderedScalarDerivative (fun y => G y k a) l w x| ≤ M l) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      ‖metricCommutatorL2Array (Nat.le_of_lt_succ j.isLt) G D (hT j)‖ ^ 2) ≤
      (∑ l : Fin (K + 1), factorialRootWeight ρ l.val *
        (if l.val = 0 then 0 else metricMaskPrice M l.val)) ^ 2 *
        gradFactorialNormSq ρ (jetToL2 D hD) := by
  let X : PiLp 2 (fun _ : Fin (K + 1) => ℝ) := WithLp.toLp 2
    (fun j => factorialRootWeight ρ j.val *
      ‖metricCommutatorL2Array (Nat.le_of_lt_succ j.isLt) G D (hT j)‖)
  have hx : ‖X‖ ^ 2 = ∑ j : Fin (K + 1), factorialWeight ρ j.val *
      ‖metricCommutatorL2Array (Nat.le_of_lt_succ j.isLt) G D (hT j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro j _
    change ‖factorialRootWeight ρ j.val * _‖ ^ 2 = _
    rw [Real.norm_eq_abs, sq_abs, mul_pow, factorialRootWeight_sq]
  have hh := metricCommutator_factorial_norm_le ρ hρ G D hD hT M hM hb
  have hgrad : 0 ≤ gradFactorialNormSq ρ (jetToL2 D hD) := by
    rw [← gradientFactorialSequence_normSq]
    exact sq_nonneg _
  have hh2 := pow_le_pow_left₀ (norm_nonneg X) hh 2
  rw [hx, mul_pow, Real.sq_sqrt (hgrad)] at hh2
  exact hh2

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Uniform entry bounds give a finite envelope for every stored coefficient derivative array. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem metricFlux_array_norm_le (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (l : ℕ)
    (hM : ∀ k j, ContDiff ℝ (l : ℕ) (fun x => M x k j))
    {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ w : DerivativeWord2 l, ∀ x k j,
      |orderedScalarDerivative (fun y => M y k j) l w x| ≤ R) (x : Vec 2) :
    ‖coefficientDerivativeArray (fun y => metricFlux (h := h) (M y) m hab hm) l x‖ ≤
      (Fintype.card (DerivativeWord2 l) : ℝ) *
        (R * (∑ k : Fin 2, ∑ j : Fin 2, ‖metricWordEntry (h := h) m hab hm k j‖)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  let A := coefficientDerivativeArray (fun y => metricFlux (h := h) (M y) m hab hm) l x z
  calc
    ‖A‖ ≤ ∑ w : DerivativeWord2 l, ‖A w‖ := finitePiLp_norm_le_sum A
    _ ≤ ∑ _w : DerivativeWord2 l,
        (R * (∑ k : Fin 2, ∑ j : Fin 2, ‖metricWordEntry (h := h) m hab hm k j‖)) * ‖z‖ := by
      apply Finset.sum_le_sum
      intro w _
      change ‖orderedCoefficientDerivative (fun y => metricFlux (h := h) (M y) m hab hm) l w x z‖ ≤ _
      rw [metricFlux_orderedDerivative M l hM m hab hm w x]
      simp only [sum_apply, smul_apply]
      calc
        ‖∑ k : Fin 2, ∑ j : Fin 2,
            orderedScalarDerivative (fun y => M y k j) l w x • metricWordEntry (h := h) m hab hm k j z‖
          ≤ ∑ k : Fin 2, ∑ j : Fin 2,
            ‖orderedScalarDerivative (fun y => M y k j) l w x • metricWordEntry (h := h) m hab hm k j z‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
        _ ≤ ∑ k : Fin 2, ∑ j : Fin 2, R * ‖metricWordEntry (h := h) m hab hm k j‖ * ‖z‖ := by
          apply Finset.sum_le_sum
          intro k _
          apply Finset.sum_le_sum
          intro j _
          rw [norm_smul, Real.norm_eq_abs, mul_assoc]
          exact mul_le_mul (hb w x k j) (ContinuousLinearMap.le_opNorm _ z)
            (norm_nonneg _) hR
        _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end AVRegularity.Weighted
end
end
