-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Variational.MassWeightedCarrierCLM
import AVRegularity.CoupledEnergyPlane.Variational.PrincipalMask
import AVRegularity.CoupledEnergy.CouplingBounds
public import AVRegularity.Analysis.Factorial.Drift
public import AVRegularity.CoupledEnergyPlane.LowerReadout

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Exact mass forcing energies are continuous under componentwise strong
time L² residuals in the genuine Sobolev carriers. -/

section
open AVRegularity.CoupledEnergy.Variational
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem planeMassNormSq_integral_split (μ : Measure T) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (f : ∀ i, T → PlaneHk Set.univ (K i) (E i)) (hf : ∀ i, MemLp (f i) 2 μ) :
    (∫ t, massNormSq ρ π (fun i => (f i t).val) ∂μ) =
      ∑ i, (π i)⁻¹ * ∫ t, factorialNormSq ρ (f i t).val ∂μ := by
  change (∫ t, ∑ i, (π i)⁻¹ * factorialNormSq ρ (f i t).val ∂μ) = _
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (factorialNormSq_integrable ρ (K i) (planeJet_memLp (K i) (hf i))).const_mul ((π i)⁻¹))]
  simp_rw [integral_const_mul]
end

/-! The exact plane flux budget is continuous in the strong time L² topology. -/

section
open AVRegularity.CoupledEnergy.Variational
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem planeMassNormSq_timeLp_tendsto (μ : Measure T) (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (U : ℕ → ∀ i, Lp (PlaneHk Set.univ (K i) (E i)) 2 μ)
    (V : ∀ i, Lp (PlaneHk Set.univ (K i) (E i)) 2 μ)
    (hU : ∀ i, Tendsto (fun N => U N i) atTop (𝓝 (V i))) :
    Tendsto (fun N => ∫ t, massNormSq ρ π (fun i => (U N i t).val) ∂μ)
      atTop (𝓝 (∫ t, massNormSq ρ π (fun i => (V i t).val) ∂μ)) := by
  let L (i : ι) : PlaneHk Set.univ (K i) (E i) →L[ℝ]
      JetL2 (volume.restrict (Set.univ : Set (Vec 2))) (K i) (E i) :=
    (factorialWeightedJetCLM (E := E i) (μ := volume.restrict Set.univ) ρ (K i)).comp
      (planeHkGraph (E := E i) Set.univ (K i)).toSubmodule.subtypeL
  have he (i : ι) (x : PlaneHk Set.univ (K i) (E i)) :
      ‖L i x‖ ^ 2 = factorialNormSq ρ x.val := factorialWeightedJet_normSq ρ x.val
  have hi (i : ι) : Tendsto (fun N => ∫ t, factorialNormSq ρ (U N i t).val ∂μ)
      atTop (𝓝 (∫ t, factorialNormSq ρ (V i t).val ∂μ)) := by
    simpa only [he] using timeLp_readout_integral_norm_square_tendsto μ (L i)
      (fun N => U N i) (V i) (hU i)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => (hi i).const_mul ((π i)⁻¹))
  simpa only [← planeMassNormSq_integral_split μ K ρ π _ (fun i => Lp.memLp (U _ i)),
    ← planeMassNormSq_integral_split μ K ρ π _ (fun i => Lp.memLp (V i))] using hs
end

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Factorial absorption of the actual nonprincipal drift-mask pairings. -/

open AVRegularity.CoupledEnergy.Variational

/-- The source's unsquared factorial weight squares to the Sobolev energy weight. -/
theorem analyticFactorialWeight_sq (ρ : ℝ) (j : ℕ) :
    Analysis.Factorial.factorialWeight ρ j ^ 2 = factorialWeight ρ j := by
  unfold Analysis.Factorial.factorialWeight factorialWeight
  rw [div_pow, ← pow_mul, Nat.mul_comm j 2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {U : Set (Vec 2)}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The derivative sequence used by the scalar absorption theorem has exactly the gradient
square. -/
theorem finiteDerivativeSequence_gradient_square {K : ℕ} (ρ : ℝ)
    (D : JetL2 (volume.restrict U) (K + 1) E) :
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
/-- The velocity envelope of the statement absorbs the actual tested commutator in ν/4 of the
gradient energy. -/
theorem driftCommutatorL2Array_energy_le {K Kmax : ℕ} (hK : K ≤ Kmax)
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
    (∑ j : Fin (K + 1), factorialWeight ρ j.val * inner ℝ
      (driftCommutatorL2Array (Nat.le_of_lt_succ j.isLt) v D (hT j))
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
  exact (le_abs_self _).trans
    (driftCommutatorL2Array_pairing_abs_le (Nat.le_of_lt_succ j.isLt) v D (hT j) hD hU V hV hb)

omit [BorelSpace E] [CompleteSpace E] in
/-- The velocity envelope of the statement absorbs the sum of absolute tested commutator
pairings in ν/4 of the gradient energy. -/
theorem driftCommutatorL2Array_energy_abs_sum_le {K Kmax : ℕ} (hK : K ≤ Kmax)
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
    (∑ j : Fin (K + 1), factorialWeight ρ j.val * |inner ℝ
      (driftCommutatorL2Array (Nat.le_of_lt_succ j.isLt) v D (hT j))
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
  exact driftCommutatorL2Array_pairing_abs_le (Nat.le_of_lt_succ j.isLt) v D (hT j) hD hU V hV hb

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Spatial integrability of literal bounded coefficient pairings. No
spatial representative is assumed pointwise smooth. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem planeStaticCoefficient_pairing_integrable (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume : Measure (Vec 2)))
    (z : Lp F 2 (volume : Measure (Vec 2))) :
    Integrable (fun x => inner ℝ (C x (u x)) (z x)) volume := by
  apply (L2.integrable_inner (𝕜 := ℝ) (planeCoefficientOperator C hc hM hb u) z).congr
  filter_upwards [planeCoefficientOperator_ae C hc hM hb u] with x hx
  rw [hx]

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Every true weak-product jet is a finite sum of genuine bounded spatial multipliers. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def productMaskOperator {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) {B : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l)
    (α : JetIndex2 K) (m : PositionMask α.1.val) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp F 2 (volume : Measure (Vec 2)) := by
  let l : Fin (K + 1) := ⟨maskLeftLength α.1.val m,
    Nat.lt_succ_of_le ((maskLeftLength_le α.1.val m).trans (Nat.le_of_lt_succ α.1.isLt))⟩
  have hc : Continuous (orderedCoefficientDerivative C l.val (maskWordEquiv 2 α.1.val m α.2).1) :=
    (orderedCoefficientDerivative_contDiff C l.val 0
      (by simpa only [Nat.add_zero] using hC.of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt))
      (maskWordEquiv 2 α.1.val m α.2).1).continuous
  have hn : 0 ≤ B l := (norm_nonneg
    (orderedCoefficientDerivative C l.val (maskWordEquiv 2 α.1.val m α.2).1 0)).trans
      ((orderedCoefficientDerivative_norm_le_array C l.val
        (maskWordEquiv 2 α.1.val m α.2).1 0).trans (hb l 0))
  exact planeCoefficientOperator (M := B l) _ hc hn
    (fun x => (orderedCoefficientDerivative_norm_le_array C l.val
      (maskWordEquiv 2 α.1.val m α.2).1 x).trans (hb l x))

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E]
  [BorelSpace F] [CompleteSpace F] in
theorem productMaskOperator_ae {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) {B : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l)
    (α : JetIndex2 K) (m : PositionMask α.1.val)
    (U : Lp E 2 (volume : Measure (Vec 2))) :
    productMaskOperator C hC hb α m U =ᵐ[volume] fun x =>
      orderedCoefficientDerivative C (maskLeftLength α.1.val m)
        (maskWordEquiv 2 α.1.val m α.2).1 x (U x) := by
  unfold productMaskOperator
  exact planeCoefficientOperator_ae _ _ _ _ U

def productJetReadout {K : ℕ} (q : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {B : Fin (K + 1) → ℝ} (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l)
    (α : JetIndex2 K) : Lp F 2 (volume : Measure (Vec 2)) :=
  ∑ m : PositionMask α.1.val, productMaskOperator C hC hb α m
    (univToPlane (q.val (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2)))

theorem productJetReadout_eq_productJet {K : ℕ} (q : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {B : Fin (K + 1) → ℝ} (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l)
    (α : JetIndex2 K) :
    productJetReadout q C hC hb α = univToPlane ((q.mulCoefficient C hC hb).val α) := by
  have hp : (q.mulCoefficient C hC hb).val α =ᵐ[volume.restrict Set.univ]
      multiplicationRawJet C q.toFunction.jet α := by
    unfold PlaneHk.mulCoefficient
    exact jetToL2_ae _ _ _
  change (q.mulCoefficient C hC hb).val α =ᵐ[volume.restrict Set.univ]
    fun x => ∑ m : PositionMask α.1.val,
      orderedCoefficientDerivative C (maskLeftLength α.1.val m)
        (maskWordEquiv 2 α.1.val m α.2).1 x
        (q.val (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2) x) at hp
  simp only [Measure.restrict_univ] at hp
  let term := fun m : PositionMask α.1.val => productMaskOperator C hC hb α m
    (univToPlane (q.val (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2)))
  have hm (m : PositionMask α.1.val) : term m =ᵐ[volume] fun x =>
      orderedCoefficientDerivative C (maskLeftLength α.1.val m)
        (maskWordEquiv 2 α.1.val m α.2).1 x
        (q.val (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2) x) := by
    have he := productMaskOperator_ae C hC hb α m
      (univToPlane (q.val (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2)))
    change term m =ᵐ[volume] _ at he
    filter_upwards [he, univToPlane_ae
      (q.val (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2))] with x hx hq
    rw [hx, hq]
  apply Lp.ext
  filter_upwards [Lp.coeFn_finsetSum Finset.univ term, ae_all_iff.mpr hm,
    univToPlane_ae ((q.mulCoefficient C hC hb).val α), hp] with x hs hm hout hp
  change (∑ m, term m) x = _
  rw [hs, Finset.sum_apply, hout, hp]
  exact Finset.sum_congr rfl (fun m _ => hm m)
end

/-! The true finite Sobolev product acts linearly through its complete weak-jet readout. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def productJetOperator {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) {B : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l)
    (α : JetIndex2 K) : JetL2 (volume.restrict Set.univ) K E →L[ℝ]
      Lp F 2 (volume : Measure (Vec 2)) :=
  ∑ m : PositionMask α.1.val, (productMaskOperator C hC hb α m).comp
    (univToPlane.toContinuousLinearMap.comp
      (PiLp.proj (𝕜 := ℝ) 2
        (fun _ : JetIndex2 K => ComponentL2 (volume.restrict Set.univ) E)
        (maskJetIndex (Nat.le_of_lt_succ α.1.isLt) m α.2)))

omit [FiniteDimensional ℝ E] [BorelSpace F] [CompleteSpace F] in
theorem productJetOperator_apply {K : ℕ} (q : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {B : Fin (K + 1) → ℝ} (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l)
    (α : JetIndex2 K) : productJetOperator C hC hb α q.val = productJetReadout q C hC hb α := by
  simp only [productJetOperator, sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, productJetReadout]
  rfl

def productAmbientJetOperator {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) {B : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l) :
    JetL2 (volume.restrict Set.univ) K E →L[ℝ] JetL2 (volume.restrict Set.univ) K F :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex2 K => ComponentL2 (volume.restrict Set.univ) F)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun α =>
        planeToUniv.toContinuousLinearMap.comp (productJetOperator C hC hb α)))

theorem productAmbientJetOperator_eq_product {K : ℕ} (q : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {B : Fin (K + 1) → ℝ} (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l) :
    productAmbientJetOperator C hC hb q.val = (q.mulCoefficient C hC hb).val := by
  apply PiLp.ext
  intro α
  change planeToUniv (productJetOperator C hC hb α q.val) = _
  rw [productJetOperator_apply, productJetReadout_eq_productJet, planeToUniv_univToPlane]
end

end AVRegularity.CoupledEnergyPlane.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! The true Sobolev coefficient product is a bounded linear operator on the plane weak graph. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def productPlaneHkOperator {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) {B : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l) :
    PlaneHk Set.univ K E →L[ℝ] PlaneHk Set.univ K F :=
  ((productAmbientJetOperator C hC hb).comp
    (planeHkGraph (E := E) Set.univ K).toSubmodule.subtypeL).codRestrict
      (planeHkGraph (E := F) Set.univ K).toSubmodule (fun (q : PlaneHk Set.univ K E) => by
        change productAmbientJetOperator C hC hb q.val ∈ planeHkGraph (E := F) Set.univ K
        rw [productAmbientJetOperator_eq_product]
        exact (q.mulCoefficient C hC hb).property)

@[simp] theorem productPlaneHkOperator_apply {K : ℕ} (q : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {B : Fin (K + 1) → ℝ} (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ B l) :
    productPlaneHkOperator C hC hb q = q.mulCoefficient C hC hb := by
  apply Subtype.ext
  exact productAmbientJetOperator_eq_product q C hC hb

end AVRegularity.CoupledEnergyPlane.Variational
end
