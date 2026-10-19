-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Variational.TorusLowTestLimit
public import AVRegularity.CoupledEnergy.Variational.FactorialPairing
import AVRegularity.CoupledEnergy.CouplingBounds
public import AVRegularity.Analysis.Factorial.Drift
import AVRegularity.CoupledEnergy.Variational.WeightedJetMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Exact binomial recombination of nonprincipal drift masks, reusing the multiplier count. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The actual L² array of the drift terms with at least one velocity derivative. -/
def driftCommutatorL2Array {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (D : RawJet2 (K + 1) E) (hc : ∀ a, Continuous (D a)) :
    PiLp 2 (fun _ : DerivativeWord2 j => ComponentL2 (volume.restrict AVenhance.unitCube) E) :=
  ∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then driftMaskL2Array hj v hv D hc m else 0

/-- Removing the principal mask leaves exactly the nonzero binomial derivative orders. -/
theorem sum_nonprincipal_masks (j : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then
      f (maskLeftLength j m) (maskRightLength j m) else 0) =
    ∑ l ∈ (Finset.range (j + 1)).erase 0, (j.choose l : ℝ) * f l (j - l) := by
  classical
  rw [sum_positionMask_eq_choose j (fun l r => if 1 ≤ l then f l r else 0)]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have heq : (Finset.range (j + 1)).filter (fun l => 1 ≤ l) =
      (Finset.range (j + 1)).erase 0 := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    omega
  rw [heq]

omit [BorelSpace E] [CompleteSpace E] in
/-- Constant-one commutator norm bound with the precise binomial multiplicities. -/
theorem driftCommutatorL2Array_norm_le {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (D : RawJet2 (K + 1) E) (hc : ∀ a, Continuous (D a))
    (hD : JetMemL2On AVenhance.unitCube D)
    (V : ℕ → ℝ) (hV : ∀ l, 0 ≤ V l)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x ∈ AVenhance.unitCube,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤ V l) :
    ‖driftCommutatorL2Array hj v hv D hc‖ ≤
    ∑ l ∈ (Finset.range (j + 1)).erase 0, (j.choose l : ℝ) * V l *
      finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) (j - l + 1) := by
  let Y := finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r))
  calc
    ‖driftCommutatorL2Array hj v hv D hc‖ ≤
        ∑ m : PositionMask j, ‖if 1 ≤ maskLeftLength j m then
          driftMaskL2Array hj v hv D hc m else 0‖ := norm_sum_le _ _
    _ ≤ ∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then
        V (maskLeftLength j m) * Y (maskRightLength j m + 1) else 0 := by
      apply Finset.sum_le_sum
      intro m _
      by_cases hm : 1 ≤ maskLeftLength j m
      · simp only [ite_eq_left hm]
        dsimp only [Y]
        rw [finiteSequence_of_le _ (by have := maskRightLength_le j m; omega)]
        exact driftMaskL2Array_norm_le hj v hv D hc hD m (hV _)
          (hb _ hm ((maskLeftLength_le j m).trans hj))
      · simp only [ite_eq_right hm, norm_zero, le_refl]
    _ = _ := by
      rw [sum_nonprincipal_masks j (fun l r => V l * Y (r + 1))]
      simp only [Y, mul_assoc]


omit [BorelSpace E] [CompleteSpace E] in
/-- The tested nonprincipal drift tensor has the exact scalar commutator envelope. -/
theorem driftCommutatorL2Array_pairing_abs_le {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (D : RawJet2 (K + 1) E) (hc : ∀ a, Continuous (D a))
    (hD : JetMemL2On AVenhance.unitCube D)
    (V : ℕ → ℝ) (hV : ∀ l, 0 ≤ V l)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x ∈ AVenhance.unitCube,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤ V l) :
    |inner ℝ (driftCommutatorL2Array hj v hv D hc)
      (orderL2Array (jetToL2 D hD) ⟨j, by omega⟩)| ≤
    ∑ l ∈ (Finset.range (j + 1)).erase 0, (j.choose l : ℝ) * V l *
      finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) (j - l + 1) *
      finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) j := by
  let Q := orderL2Array (jetToL2 D hD) (⟨j, by omega⟩ : Fin (K + 2))
  have hq : ‖Q‖ = finiteSequence
      (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) j := by
    rw [finiteSequence_of_le _ (by omega)]
    exact orderL2Array_norm _ _
  have hpair := abs_real_inner_le_norm (driftCommutatorL2Array hj v hv D hc) Q
  have hm := mul_le_mul_of_nonneg_right
    (driftCommutatorL2Array_norm_le hj v hv D hc hD V hV hb) (norm_nonneg Q)
  rw [hq] at hpair
  rw [hq, Finset.sum_mul] at hm
  exact hpair.trans hm

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Exact subtraction identities for the weak gradient and reserve tensors. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem torusFamilyTensor_sub {J : Type*} [Fintype J] [DecidableEq J] {K : ℕ}
    (w z : J → TorusHk K E) :
    torusFamilyTensor (fun j => w j - z j) = torusFamilyTensor w - torusFamilyTensor z := by
  unfold torusFamilyTensor
  simp_rw [← mapTorusHkCLM_apply, map_sub]
  rw [Finset.sum_sub_distrib]

theorem torusDerivativeTensor_sub {K r : ℕ} (w z : TorusHk (K + r) E) :
    torusDerivativeTensor (w - z) = torusDerivativeTensor w - torusDerivativeTensor z := by
  simp only [torusDerivativeTensor, map_sub]
  exact torusFamilyTensor_sub _ _

theorem torusGradientTensor_sub {K : ℕ} (w z : TorusHk (K + 1) E) :
    torusGradientTensor (w - z) = torusGradientTensor w - torusGradientTensor z := by
  simp only [torusGradientTensor, map_sub]
  exact torusFamilyTensor_sub _ _

theorem torusGradientReserveTensor_sub {K L : ℕ} (s : ℕ) (hKL : K + s ≤ L)
    (w z : TorusHk (L + 1) E) :
    torusGradientReserveTensor s hKL (w - z) =
      torusGradientReserveTensor s hKL w - torusGradientReserveTensor s hKL z := by
  simp only [torusGradientReserveTensor, map_sub, torusDerivativeTensor_sub]

theorem torusPositiveDerivativeTensor_sub {K L : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (hKL : K + (m - 1) ≤ L) (w z : TorusHk (L + 1) E) :
    torusPositiveDerivativeTensor m hm hKL (w - z) =
      torusPositiveDerivativeTensor m hm hKL w - torusPositiveDerivativeTensor m hm hKL z := by
  cases m with
  | zero => omega
  | succ s => exact torusGradientReserveTensor_sub s (by simpa using hKL) w z

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Bundle the higher Sobolev family of any weak solution into the
plain ambient Bochner space used by native component tests. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem coupledCarrierHighJets_memLp (K : ι → ℕ) (a b : ℝ)
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun r => coupledCarrierHighJets K (fun i => w i r)) 2 (volume.restrict (Set.Icc a b)) := by
  have hi (i : ι) := (torusHkGraph (E := h i) (K i + 1)).toSubmodule.subtypeL.comp_memLp' (hw i)
  have hp : MemLp (fun r i => (w i r).val) 2 (volume.restrict (Set.Icc a b)) :=
    memLp_pi_iff.mpr hi
  simpa only [Function.comp_def, coupledCarrierHighJets] using!
    (PiLp.continuousLinearEquiv 2 ℝ (fun i =>
      JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i))).symm.toContinuousLinearMap.comp_memLp' hp

def coupledCarrierHighTime (K : ι → ℕ) (a b : ℝ)
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    CoupledHighTime (h := h) K a b :=
  (coupledCarrierHighJets_memLp K a b w hw).toLp (fun r => coupledCarrierHighJets K (fun i => w i r))

theorem coupledCarrierHighTime_ae (K : ι → ℕ) (a b : ℝ)
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i,
      (w i r).val = coupledCarrierHighTime K a b w hw r i := by
  filter_upwards [(coupledCarrierHighJets_memLp K a b w hw).coeFn_toLp] with r hr
  intro i
  exact (congrArg (fun U : CoupledHighHilbert (h := h) K => U i) hr).symm


theorem coupledCarrierHighTime_graphReadout_ae (K : ι → ℕ) (a b : ℝ)
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) :
    ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ i,
      coupledHighGraphReadout K i (coupledCarrierHighTime K a b w hw r) = w i r := by
  filter_upwards [coupledCarrierHighTime_ae K a b w hw] with r hr
  intro i
  apply Subtype.ext
  have hg : coupledCarrierHighTime K a b w hw r i ∈ torusHkGraph (E := h i) (K i + 1) := by
    rw [← hr i]
    exact (w i r).property
  exact (coupledHighGraphReadout_val K i _ hg).trans (hr i).symm


theorem coupledCarrierHighTime_sub (K : ι → ℕ) (a b : ℝ)
    (w z : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (hz : ∀ i, MemLp (z i) 2 (volume.restrict (Set.Icc a b)))
    (hd : ∀ i, MemLp (fun t => w i t - z i t) 2 (volume.restrict (Set.Icc a b))) :
    coupledCarrierHighTime K a b (fun i t => w i t - z i t) hd =
      coupledCarrierHighTime K a b w hw - coupledCarrierHighTime K a b z hz := by
  apply Lp.ext
  filter_upwards [coupledCarrierHighTime_ae K a b (fun i t => w i t - z i t) hd,
    coupledCarrierHighTime_ae K a b w hw, coupledCarrierHighTime_ae K a b z hz,
    Lp.coeFn_sub (coupledCarrierHighTime K a b w hw) (coupledCarrierHighTime K a b z hz)]
      with t hdiff hw' hz' hsub
  rw [hsub, Pi.sub_apply]
  apply PiLp.ext
  intro i
  rw [← hdiff i]
  change (w i t).val - (z i t).val = _
  rw [hw' i, hz' i]
  rfl

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Literal admissible coupling fluxes, with the exact coefficient budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- One actual coupling flux at reserve `K i`, for an admissible order. -/
def torusCoupledFluxTerm (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t)) (w : TorusHk (K i' + 1) (h i')) :
    TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  torusMultiplyIntervalCoefficient ρ hρ (K i) a b A hA t ht hC hp
    (torusPositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
      (admissibleOrders_reserve K D i i' d).2 w)

omit [Fintype ι] in
/-- Each literal admissible coupling consumes only its declared reserve and coefficient budget. -/
theorem torusCoupledFluxTerm_factorialNorm_le (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t)) (w : TorusHk (K i' + 1) (h i')) :
    Real.sqrt (factorialNormSq ρ (torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp w).val) ≤
      ((coefficientSeminorm ρ (K i) a b A).toReal * derivativeReserveFactor ρ (K i) (d.1 - 2)) *
        Real.sqrt (gradFactorialNormSq ρ w.val) := by
  have hm := torusMultiplyIntervalCoefficient_factorialNorm_le ρ hρ (K i) a b A hA t ht hC hp
    (torusPositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
      (admissibleOrders_reserve K D i i' d).2 w)
  have hs := torusPositiveDerivativeTensor_factorialNorm_le ρ hρ (d.1 - 1)
    (admissibleOrders_reserve K D i i' d).1 (admissibleOrders_reserve K D i i' d).2 w
  conv_rhs at hs => rw [Nat.sub_sub]
  exact hm.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hs ENNReal.toReal_nonneg)

end AVRegularity.CoupledEnergy.Variational
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Factorial absorption of the actual nonprincipal drift-mask pairings. -/

/-- The source's unsquared factorial weight squares to the Sobolev energy weight. -/
theorem analyticFactorialWeight_sq (ρ : ℝ) (j : ℕ) :
    Analysis.Factorial.factorialWeight ρ j ^ 2 = factorialWeight ρ j := by
  unfold Analysis.Factorial.factorialWeight factorialWeight
  rw [div_pow, ← pow_mul, Nat.mul_comm j 2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The derivative sequence of the scalar absorption theorem has exactly the gradient square. -/
theorem finiteDerivativeSequence_gradient_square {K : ℕ} (ρ : ℝ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) (K + 1) E) :
    (∑ k ∈ Finset.range (K + 1),
      (Analysis.Factorial.factorialWeight ρ k *
        finiteSequence (fun r => Real.sqrt (derivativeNormSq D r)) (k + 1)) ^ 2) =
      gradFactorialNormSq ρ D := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [finiteSequence_of_le _ (by omega), mul_pow,
    Real.sq_sqrt (derivativeNormSq_nonneg D _), analyticFactorialWeight_sq]
  rfl

omit [BorelSpace E] [CompleteSpace E] in
/-- The velocity envelope absorbs the actual tested commutator in ν/4 of the gradient energy. -/
theorem driftCommutatorL2Array_energy_le {K Kmax : ℕ} (hK : K ≤ Kmax)
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : RawJet2 (K + 1) E) (hc : ∀ z, Continuous (D z))
    (hD : JetMemL2On AVenhance.unitCube D) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val * inner ℝ
      (driftCommutatorL2Array (Nat.le_of_lt_succ j.isLt) v hv D hc)
      (orderL2Array (jetToL2 D hD) ⟨j.val, by omega⟩)) ≤
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
  have hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x ∈ AVenhance.unitCube,
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
  exact (le_abs_self _).trans
    (driftCommutatorL2Array_pairing_abs_le (Nat.le_of_lt_succ j.isLt) v hv D hc hD V hV hb)

omit [BorelSpace E] [CompleteSpace E] in
/-- The velocity envelope absorbs the sum of absolute tested commutator pairings in ν/4 of the
gradient energy. -/
theorem driftCommutatorL2Array_energy_abs_sum_le {K Kmax : ℕ} (hK : K ≤ Kmax)
    (ρ a B lam ν : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : RawJet2 (K + 1) E) (hc : ∀ z, Continuous (D z))
    (hD : JetMemL2On AVenhance.unitCube D) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val * |inner ℝ
      (driftCommutatorL2Array (Nat.le_of_lt_succ j.isLt) v hv D hc)
      (orderL2Array (jetToL2 D hD) ⟨j.val, by omega⟩)|) ≤
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
  have hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x ∈ AVenhance.unitCube,
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
  exact driftCommutatorL2Array_pairing_abs_le (Nat.le_of_lt_succ j.isLt) v hv D hc hD V hV hb

end AVRegularity.CoupledEnergy.Variational
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The Hilbert-valued drift coefficient and its exact scalar derivative-array norm bound. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A scalar linear row extended identically to each fiber coordinate. -/
def scalarRowFiberMap : (PiLp 2 (fun _ : Fin 2 => ℝ) →L[ℝ] ℝ) →L[ℝ]
    (PiLp 2 (fun _ : Fin 2 => E) →L[ℝ] E) :=
  ∑ k : Fin 2, (ContinuousLinearMap.apply ℝ ℝ (PiLp.single 2 k 1)).smulRight
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k)

omit [FiniteDimensional ℝ E] in
/-- The extended scalar row is its usual coefficient contraction. -/
theorem scalarRowFiberMap_apply (T : PiLp 2 (fun _ : Fin 2 => ℝ) →L[ℝ] ℝ)
    (U : PiLp 2 (fun _ : Fin 2 => E)) :
    scalarRowFiberMap (E := E) T U = ∑ k : Fin 2, T (PiLp.single 2 k 1) • U k := by
  simp [scalarRowFiberMap]

/-- The spatial drift coefficient acting on an actual Hilbert-valued gradient. -/
def driftFiberCoefficient (v : Vec 2 → Vec 2) :
    Vec 2 → PiLp 2 (fun _ : Fin 2 => E) →L[ℝ] E :=
  fun x => scalarRowFiberMap (driftCoefficient v x)

omit [FiniteDimensional ℝ E] in
/-- The lifted drift is exactly the velocity-gradient contraction in the PDE. -/
theorem driftFiberCoefficient_apply (v : Vec 2 → Vec 2) (x : Vec 2)
    (U : PiLp 2 (fun _ : Fin 2 => E)) :
    driftFiberCoefficient v x U = ∑ k : Fin 2, v x k • U k := by
  rw [driftFiberCoefficient, scalarRowFiberMap_apply]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  fin_cases k <;> simp [driftCoefficient]

omit [FiniteDimensional ℝ E] in
/-- Spatial smoothness of the velocity passes to the Hilbert-valued drift coefficient. -/
theorem driftFiberCoefficient_contDiff (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (driftFiberCoefficient (E := E) v) := by
  unfold driftFiberCoefficient scalarRowFiberMap
  simp only [sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have : IsBoundedSMul ℝ ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] E) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] E))
  apply ContDiff.sum
  intro k _
  exact ((driftCoefficient_contDiff v hv).clm_apply contDiff_const).smul contDiff_const

omit [FiniteDimensional ℝ E] in
/-- The complete ordered drift array is the dimension-free scalar tensor extension. -/
theorem driftFiberCoefficient_array_eq (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (j : ℕ) (x : Vec 2) :
    coefficientDerivativeArray (driftFiberCoefficient (E := E) v) j x =
      scalarTensorOperator (coefficientDerivativeArray (driftCoefficient v) j x) := by
  apply ContinuousLinearMap.ext
  intro U
  apply PiLp.ext
  intro w
  unfold driftFiberCoefficient
  rw [coefficientDerivativeArray_apply,
    orderedCoefficientDerivative_linearMap (scalarRowFiberMap (E := E)) (driftCoefficient v)
      (driftCoefficient_contDiff v hv), scalarRowFiberMap_apply]
  rw [scalarTensorOperator_apply]
  rfl

/-- The exact scalar coefficient-array norm also bounds the fiber drift-array norm. -/
theorem driftFiberCoefficient_array_norm_le (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (j : ℕ) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftFiberCoefficient (E := E) v) j x‖ ≤
      ‖coefficientDerivativeArray (driftCoefficient v) j x‖ := by
  rw [driftFiberCoefficient_array_eq v hv]
  exact scalarTensorOperator_norm_le _

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Ordinary graph norm control of each actual admissible coupling flux. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusCoupledFluxTerm_norm_le (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t)) (w : TorusHk (K i' + 1) (h i')) :
    ‖torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp w‖ ≤
      (((coefficientSeminorm ρ (K i) a b A).toReal * derivativeReserveFactor ρ (K i) (d.1 - 2)) *
        Real.sqrt (factorialWeightMax ρ (K i')) / Real.sqrt (factorialWeightMin ρ (K i))) * ‖w‖ := by
  let L := (coefficientSeminorm ρ (K i) a b A).toReal * derivativeReserveFactor ρ (K i) (d.1 - 2)
  have hL : 0 ≤ L := by unfold L derivativeReserveFactor; positivity
  have hn := jetNorm_le_factorialRoot ρ hρ
    (torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp w).val
  have hf := torusCoupledFluxTerm_factorialNorm_le ρ hρ K D a b i i' d A hA t ht hC hp w
  have hg := gradFactorialRoot_le_jetNorm ρ w.val
  calc
    _ ≤ Real.sqrt (factorialNormSq ρ
        (torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp w).val) /
        Real.sqrt (factorialWeightMin ρ (K i)) := hn
    _ ≤ (L * Real.sqrt (gradFactorialNormSq ρ w.val)) / Real.sqrt (factorialWeightMin ρ (K i)) :=
      div_le_div_of_nonneg_right hf (Real.sqrt_nonneg _)
    _ ≤ (L * (Real.sqrt (factorialWeightMax ρ (K i')) * ‖w.val‖)) /
        Real.sqrt (factorialWeightMin ρ (K i)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg hL) (Real.sqrt_nonneg _)
    _ = _ := by change _ = (L * _ / _) * ‖w.val‖; ring
end

/-! The actual coupling flux carrier has the literal derivative tensor
representative appearing in the integrated weak equation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
theorem torusCoupledFluxTerm_value_ae (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t)) (w : TorusHk (K i' + 1) (h i')) :
    (torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp w).val (valueIndex2 (K i)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => A t x
        (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
          w.val ⟨⟨d.1 - 1, by
            have := admissibleOrders_reserve K D i i' d
            omega⟩, word⟩ x)) := by
  let T := torusPositiveDerivativeTensor (d.1 - 1) (admissibleOrders_reserve K D i i' d).1
    (admissibleOrders_reserve K D i i' d).2 w
  have hb := fun (l : Fin (K i + 1)) (x : Vec 2) =>
    coefficientOrderSup_derivative_bound ρ hρ (K i) a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t ht x
  have hm := torusMulCoefficient_value_ae T (A t) hC hp hb
  have htensor := torusPositiveDerivativeTensor_value_ae (d.1 - 1)
    (admissibleOrders_reserve K D i i' d).1 (admissibleOrders_reserve K D i i' d).2 w
  filter_upwards [hm, htensor] with x hx htx
  unfold torusCoupledFluxTerm torusMultiplyIntervalCoefficient
  rw [hx, htx]
end

end AVRegularity.CoupledEnergy.Variational
end
