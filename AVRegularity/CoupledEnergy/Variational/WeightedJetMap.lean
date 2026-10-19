-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Variational.FactorialPairing
import AVRegularity.CoupledEnergy.Galerkin.CoefficientPairing
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Convert the existing factorial multiplication and reserve estimates to
ordinary Sobolev graph norm bounds for Bochner measurability arguments. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem jetNorm_le_factorialRoot {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) :
    ‖D‖ ≤ Real.sqrt (factorialNormSq ρ D) / Real.sqrt (factorialWeightMin ρ K) := by
  have hm := factorialWeightMin_pos ρ hρ (K := K)
  have hs := Real.sqrt_le_sqrt (factorialNormSq_lower ρ D)
  rw [Real.sqrt_mul hm.le, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hm), mul_comm]
  exact hs

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem gradFactorialNormSq_le_jetNormSq {K : ℕ} (ρ : ℝ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) (K + 1) E) :
    gradFactorialNormSq ρ D ≤ factorialWeightMax ρ K * ‖D‖ ^ 2 := by
  change (∑ j : Fin (K + 1), factorialWeight ρ j.val * derivativeNormSq D j.succ) ≤ _
  have hm : 0 ≤ factorialWeightMax ρ K :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (K + 1)))
  calc
    _ ≤ ∑ j : Fin (K + 1), factorialWeightMax ρ K * derivativeNormSq D j.succ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (factorialWeight_le_max ρ j) (derivativeNormSq_nonneg D _)
    _ = factorialWeightMax ρ K * ∑ j : Fin (K + 1), derivativeNormSq D j.succ := by
      rw [Finset.mul_sum]
    _ ≤ factorialWeightMax ρ K * ∑ j : Fin (K + 2), derivativeNormSq D j :=
      mul_le_mul_of_nonneg_left
        (sum_comp_le_sum_nonneg Fin.succ (Fin.succ_injective (K + 1)) (derivativeNormSq D)
          (derivativeNormSq_nonneg D)) hm
    _ = _ := by rw [jet_norm_sq_eq_sum]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem gradFactorialRoot_le_jetNorm {K : ℕ} (ρ : ℝ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) (K + 1) E) :
    Real.sqrt (gradFactorialNormSq ρ D) ≤ Real.sqrt (factorialWeightMax ρ K) * ‖D‖ := by
  have hm : 0 ≤ factorialWeightMax ρ K :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (K + 1)))
  have hs := Real.sqrt_le_sqrt (gradFactorialNormSq_le_jetNormSq ρ D)
  simpa only [Real.sqrt_mul hm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs
end

/-! Linearity of the actual weak coefficient multiplier, proved by uniqueness
of periodic weak derivatives from the value class. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem torusMulCoefficient_sub {K : ℕ} (w z : TorusHk K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (hp : AVenhance.IsZ2Periodic C) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    (w - z).mulCoefficient C hC hp hb =
      w.mulCoefficient C hC hp hb - z.mulCoefficient C hC hp hb := by
  apply TorusHk.ext_value
  apply Lp.ext
  have hs : (w - z).val (valueIndex2 K) =
      w.val (valueIndex2 K) - z.val (valueIndex2 K) := rfl
  have ht : (w.mulCoefficient C hC hp hb - z.mulCoefficient C hC hp hb).val
      (valueIndex2 K) = (w.mulCoefficient C hC hp hb).val (valueIndex2 K) -
        (z.mulCoefficient C hC hp hb).val (valueIndex2 K) := rfl
  rw [ht]
  filter_upwards [torusMulCoefficient_value_ae (w - z) C hC hp hb,
    torusMulCoefficient_value_ae w C hC hp hb,
    torusMulCoefficient_value_ae z C hC hp hb,
    Lp.coeFn_sub (w.val (valueIndex2 K)) (z.val (valueIndex2 K)),
    Lp.coeFn_sub ((w.mulCoefficient C hC hp hb).val (valueIndex2 K))
      ((z.mulCoefficient C hC hp hb).val (valueIndex2 K))] with x hx hw hz hsx htx
  rw [hx, hs, hsx, htx]
  simp only [Pi.sub_apply]
  rw [hw, hz]
  exact (C x).map_sub _ _
end

/-! Spatial integrability of literal bounded coefficient pairings. No
spatial representative is assumed pointwise smooth. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem staticCoefficient_pairing_integrable (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : ComponentL2 (volume.restrict AVenhance.unitCube) E)
    (z : ComponentL2 (volume.restrict AVenhance.unitCube) F) :
    Integrable (fun x => inner ℝ (C x (u x)) (z x)) (volume.restrict AVenhance.unitCube) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (Galerkin.boundedCoefficientL2 C hc M hM hb u) z).congr
  filter_upwards [Galerkin.boundedCoefficientL2_ae C hc M hM hb u] with x hx
  rw [hx]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]

omit [BorelSpace H] [CompleteSpace H] in
theorem boundedScalar_inner_integrable (c : Vec 2 → ℝ) (hc : Continuous c)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖c x‖ ≤ M)
    (u z : ComponentL2 (volume.restrict AVenhance.unitCube) H) :
    Integrable (fun x => c x * inner ℝ (u x) (z x)) (volume.restrict AVenhance.unitCube) := by
  let C : Vec 2 → H →L[ℝ] H := fun x => c x • ContinuousLinearMap.id ℝ H
  have hC : Continuous C := hc.smul continuous_const
  have hCb (x : Vec 2) : ‖C x‖ ≤ M := by
    calc
      _ = ‖c x‖ * ‖ContinuousLinearMap.id ℝ H‖ := norm_smul _ _
      _ ≤ ‖c x‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ ≤ M := by simpa only [mul_one] using hb x
  have hi := staticCoefficient_pairing_integrable C hC M hM hCb u z
  simpa only [C, smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left] using hi
end

/-! Exact Hilbert pairings of finite fiber tensors and factorial weighted jets. -/

section
variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

omit [DecidableEq J] in
/-- Cell L² tensor pairings are exactly the sum of component L² pairings. -/
theorem tensorL2_inner_eq_sum (U V : ComponentL2 (volume.restrict AVenhance.unitCube)
    (PiLp 2 (fun _ : J => E))) :
    inner ℝ U V = ∑ j : J, inner ℝ
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : J => E) j).compLpL 2 (volume.restrict AVenhance.unitCube) U)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : J => E) j).compLpL 2 (volume.restrict AVenhance.unitCube) V) := by
  simp only [L2.inner_def]
  rw [← integral_finsetSum Finset.univ (fun j _ => L2.integrable_inner (𝕜 := ℝ)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : J => E) j).compLpL 2 (volume.restrict AVenhance.unitCube) U)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : J => E) j).compLpL 2 (volume.restrict AVenhance.unitCube) V))]
  have hu : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j : J,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : J => E) j).compLpL 2 (volume.restrict AVenhance.unitCube) U) x =
        U x j := ae_all_iff.mpr (fun j => ContinuousLinearMap.coeFn_compLpL _ U)
  have hv : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j : J,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : J => E) j).compLpL 2 (volume.restrict AVenhance.unitCube) V) x =
        V x j := ae_all_iff.mpr (fun j => ContinuousLinearMap.coeFn_compLpL _ V)
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun j _ => by rw [hx j, hy j])

variable {μ : Measure (Vec 2)} {K : ℕ}

/-- The weighted Hilbert inner product is the exact factorial energy pairing. -/
theorem factorialWeightedJet_inner (ρ : ℝ) (D Q : JetL2 μ K E) :
    inner ℝ (factorialWeightedJet ρ D) (factorialWeightedJet ρ Q) =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val * ∑ w : DerivativeWord2 j.val,
        inner ℝ (D ⟨j, w⟩) (Q ⟨j, w⟩) := by
  rw [PiLp.inner_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  change inner ℝ (factorialRootWeight ρ j.val • D ⟨j, w⟩)
    (factorialRootWeight ρ j.val • Q ⟨j, w⟩) = _
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    ← pow_two, factorialRootWeight_sq]

/-- Constant scalar multiplication commutes with factorial jet reweighting. -/
theorem factorialWeightedJet_smul (ρ z : ℝ) (D : JetL2 μ K E) :
    factorialWeightedJet ρ (z • D) = z • factorialWeightedJet ρ D := by
  apply PiLp.ext
  intro a
  change factorialRootWeight ρ a.1.val • (z • D a) = z • (factorialRootWeight ρ a.1.val • D a)
  exact smul_comm _ _ _

/-- Additive inverse commutes with factorial jet reweighting. -/
theorem factorialWeightedJet_neg (ρ : ℝ) (D : JetL2 μ K E) :
    factorialWeightedJet ρ (-D) = -factorialWeightedJet ρ D := by
  apply PiLp.ext
  intro a
  change factorialRootWeight ρ a.1.val • (-D a) = -(factorialRootWeight ρ a.1.val • D a)
  exact smul_neg _ _
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoupledEnergy.Variational

/-! Fixed factorial jet readouts and their time integrability. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] {μ : Measure (Vec 2)}

/-- Factorial reweighting is a fixed continuous linear map on the finite jet array. -/
def factorialWeightedJetCLM (ρ : ℝ) (K : ℕ) : JetL2 μ K E →L[ℝ] JetL2 μ K E :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : JetIndex2 K => ComponentL2 μ E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => factorialRootWeight ρ j.1.val •
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K => ComponentL2 μ E) j))

@[simp] theorem factorialWeightedJetCLM_apply (ρ : ℝ) (K : ℕ) (D : JetL2 μ K E) :
    factorialWeightedJetCLM ρ K D = factorialWeightedJet ρ D := rfl

/-- Time L² control of jets gives integrability of the exact factorial square. -/
theorem factorialNormSq_integrable {X : Type*} [MeasurableSpace X] {m : Measure X}
    (ρ : ℝ) (K : ℕ) {f : X → JetL2 μ K E} (hf : MemLp f 2 m) :
    Integrable (fun t => factorialNormSq ρ (f t)) m := by
  have hc := ((factorialWeightedJetCLM (E := E) (μ := μ) ρ K).comp_memLp' hf).norm.integrable_sq
  simpa only [Function.comp_apply, factorialWeightedJetCLM_apply, factorialWeightedJet_normSq] using hc

/-- A time Sobolev hypothesis controls the ambient ordered-jet readout by a fixed map. -/
theorem torusJet_memLp [BorelSpace E] [CompleteSpace E]
    {X : Type*} [MeasurableSpace X] {m : Measure X} (K : ℕ) {p : ℝ≥0∞}
    {f : X → TorusHk K E} (hf : MemLp f p m) :
    MemLp (fun t => (f t).val) p m :=
  (torusHkGraph (E := E) K).toSubmodule.subtypeL.comp_memLp' hf

end AVRegularity.CoupledEnergy.Variational
end
