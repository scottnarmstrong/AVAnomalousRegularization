-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
public import AVRegularity.CoupledEnergy.Variational.WeightedJetMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Component coercivity from the exact factorial mass energy and dissipation. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  {μ : Measure (Vec 2)} {K : ι → ℕ}

omit [∀ i, InnerProductSpace ℝ (E i)] in
/-- Every component energy is bounded by its positive mass times the total mass energy. -/
theorem componentFactorial_le_mass (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D : ∀ i, JetL2 μ (K i) (E i)) (i : ι) :
    factorialNormSq ρ (D i) ≤ π i * massNormSq ρ π D := by
  classical
  have hs : (π i)⁻¹ * factorialNormSq ρ (D i) ≤ massNormSq ρ π D :=
    Finset.single_le_sum (fun j _ => mul_nonneg (inv_nonneg.mpr (hπ j).le)
      (factorialNormSq_nonneg ρ (D j))) (Finset.mem_univ i)
  have hm := mul_le_mul_of_nonneg_left hs (hπ i).le
  simpa only [← mul_assoc, mul_inv_cancel₀ (hπ i).ne', one_mul] using hm

omit [∀ i, InnerProductSpace ℝ (E i)] in
/-- Every component gradient energy is bounded by its mass times total dissipation. -/
theorem componentGradFactorial_le_mass (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D : ∀ i, JetL2 μ (K i + 1) (E i)) (i : ι) :
    gradFactorialNormSq ρ (D i) ≤ π i * massGradNormSq ρ π D := by
  classical
  have hn (j : ι) : 0 ≤ gradFactorialNormSq ρ (D j) :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (factorialWeight_nonneg ρ r.val)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hs : (π i)⁻¹ * gradFactorialNormSq ρ (D i) ≤ massGradNormSq ρ π D :=
    Finset.single_le_sum (fun j _ => mul_nonneg (inv_nonneg.mpr (hπ j).le) (hn j)) (Finset.mem_univ i)
  have hm := mul_le_mul_of_nonneg_left hs (hπ i).le
  simpa only [← mul_assoc, mul_inv_cancel₀ (hπ i).ne', one_mul] using hm

/-- The exact mass energy and gradient energy control each entire higher-order jet. -/
theorem componentJetNormSq_le_mass (ρ : ℝ) (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D : ∀ i, JetL2 μ (K i + 1) (E i)) (i : ι) :
    ‖D i‖ ^ 2 ≤ π i * massNormSq ρ π (fun j => truncateJet (Nat.le_succ (K j)) (D j)) +
      (π i / factorialWeightMin ρ (K i)) * massGradNormSq ρ π D := by
  have hl := componentFactorial_le_mass ρ π hπ (fun j => truncateJet (Nat.le_succ (K j)) (D j)) i
  have hg := componentGradFactorial_le_mass ρ π hπ D i
  calc
    ‖D i‖ ^ 2 ≤ factorialNormSq ρ (truncateJet (Nat.le_succ (K i)) (D i)) +
        gradFactorialNormSq ρ (D i) / factorialWeightMin ρ (K i) :=
      jetNormSq_le_factorial_add_grad ρ hρ (D i)
    _ ≤ π i * massNormSq ρ π (fun j => truncateJet (Nat.le_succ (K j)) (D j)) +
        (π i * massGradNormSq ρ π D) / factorialWeightMin ρ (K i) :=
      add_le_add hl (div_le_div_of_nonneg_right hg (factorialWeightMin_pos ρ hρ).le)
    _ = _ := by ring

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CoupledEnergy.Variational

/-! Exact mass-weighted forcing norms from finite Hilbert jet readouts. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] {μ : Measure (Vec 2)} {K : ι → ℕ}

/-- The factorial mass square is the squared norm of this finite Hilbert array. -/
def massWeightedJet (ρ : ℝ) (π : ι → ℝ) (D : ∀ i, JetL2 μ (K i) (E i)) :
    PiLp 2 (fun i => JetL2 μ (K i) (E i)) :=
  WithLp.toLp 2 (fun i => Real.sqrt ((π i)⁻¹) • factorialWeightedJet ρ (D i))

theorem massWeightedJet_normSq (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D : ∀ i, JetL2 μ (K i) (E i)) : ‖massWeightedJet ρ π D‖ ^ 2 = massNormSq ρ π D := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i, ‖Real.sqrt ((π i)⁻¹) • factorialWeightedJet ρ (D i)‖ ^ 2) = _
  unfold massNormSq
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (inv_nonneg.mpr (hπ i).le), factorialWeightedJet_normSq]

theorem massWeightedJet_norm (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D : ∀ i, JetL2 μ (K i) (E i)) :
    ‖massWeightedJet ρ π D‖ = Real.sqrt (massNormSq ρ π D) := by
  rw [← massWeightedJet_normSq ρ π hπ D, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Componentwise time integrability survives the finite mass-weighted readout. -/
theorem massWeightedJet_memLp {X : Type*} [MeasurableSpace X] {m : Measure X}
    (ρ : ℝ) (π : ι → ℝ) {p : ℝ≥0∞} {f : ∀ i, X → JetL2 μ (K i) (E i)}
    (hf : ∀ i, MemLp (f i) p m) :
    MemLp (fun t => massWeightedJet ρ π (fun i => f i t)) p m := by
  have hi (i : ι) : MemLp (fun t => Real.sqrt ((π i)⁻¹) • factorialWeightedJet ρ (f i t)) p m := by
    simpa only [Pi.smul_apply, Function.comp_apply, factorialWeightedJetCLM_apply] using!
      ((factorialWeightedJetCLM (E := E i) (μ := μ) ρ (K i)).comp_memLp' (hf i)).const_smul
        (Real.sqrt ((π i)⁻¹))
  have hpi := memLp_pi_iff.mpr hi
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun i => JetL2 μ (K i) (E i))).symm.toContinuousLinearMap.comp_memLp' hpi

/-- The L² flux hypothesis gives integrability of the exact mass forcing square. -/
theorem massNormSq_integrable {X : Type*} [MeasurableSpace X] {m : Measure X}
    (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    {f : ∀ i, X → JetL2 μ (K i) (E i)} (hf : ∀ i, MemLp (f i) 2 m) :
    Integrable (fun t => massNormSq ρ π (fun i => f i t)) m := by
  simpa only [massWeightedJet_normSq ρ π hπ] using
    (massWeightedJet_memLp ρ π hf).norm.integrable_sq

/-- The L¹ value-source hypothesis gives integrability of its exact mass norm. -/
theorem massNorm_integrable {X : Type*} [MeasurableSpace X] {m : Measure X}
    (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    {f : ∀ i, X → JetL2 μ (K i) (E i)} (hf : ∀ i, MemLp (f i) 1 m) :
    Integrable (fun t => Real.sqrt (massNormSq ρ π (fun i => f i t))) m := by
  simpa only [massWeightedJet_norm ρ π hπ] using
    (memLp_one_iff_integrable.mp (massWeightedJet_memLp ρ π hf)).norm

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Mass-weighted Hilbert Cauchy-Schwarz, using the square-root normalization from Schur.Finite. -/

/-- Finite weighted products have the exact constant-one Cauchy-Schwarz bound. -/
theorem weighted_sum_mul_le {ι : Type*} [Fintype ι] (ω x y : ι → ℝ)
    (hω : ∀ i, 0 ≤ ω i) :
    (∑ i, ω i * x i * y i) ≤
      Real.sqrt (∑ i, ω i * x i ^ 2) * Real.sqrt (∑ i, ω i * y i ^ 2) := by
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => Real.sqrt (ω i) * x i) (fun i => Real.sqrt (ω i) * y i)
  have hmul (i : ι) : (Real.sqrt (ω i) * x i) * (Real.sqrt (ω i) * y i) =
      ω i * x i * y i := by
    calc
      _ = (Real.sqrt (ω i)) ^ 2 * x i * y i := by ring
      _ = _ := by rw [Real.sq_sqrt (hω i)]
  simp only [hmul, mul_pow, Real.sq_sqrt (hω _)] at hc
  exact hc

/-- Arbitrary component Hilbert spaces obey the same exact mass-weighted pairing bound. -/
theorem weightedHilbertPairing_abs_le {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    (ω : ι → ℝ) (hω : ∀ i, 0 ≤ ω i) (D Q : ∀ i, H i) :
    |∑ i, ω i * inner ℝ (D i) (Q i)| ≤
      Real.sqrt (∑ i, ω i * ‖D i‖ ^ 2) * Real.sqrt (∑ i, ω i * ‖Q i‖ ^ 2) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_mul, abs_of_nonneg (hω _)]
  refine le_trans ?_ (weighted_sum_mul_le ω (fun i => ‖D i‖) (fun i => ‖Q i‖) hω)
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (D i) (Q i)) (hω i)).trans_eq
    (mul_assoc _ _ _).symm

/-- The native factorial jet family has the literal mass norm on both sides. -/
theorem massFactorialPairing_abs_le {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, MeasurableSpace (E i)] {μ : Measure (Vec 2)} {K : ι → ℕ}
    (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D Q : ∀ i, JetL2 μ (K i) (E i)) :
    |∑ i, (π i)⁻¹ * inner ℝ (factorialWeightedJet ρ (D i)) (factorialWeightedJet ρ (Q i))| ≤
      Real.sqrt (massNormSq ρ π D) * Real.sqrt (massNormSq ρ π Q) := by
  have hc := weightedHilbertPairing_abs_le (fun i => (π i)⁻¹)
    (fun i => inv_nonneg.mpr (hπ i).le) (fun i => factorialWeightedJet ρ (D i))
    (fun i => factorialWeightedJet ρ (Q i))
  simpa only [factorialWeightedJet_normSq, massNormSq] using hc

/-- The mass square is nonnegative for positive component masses. -/
theorem massNormSq_nonneg {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)]
    {μ : Measure (Vec 2)} {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D : ∀ i, JetL2 μ (K i) (E i)) : 0 ≤ massNormSq ρ π D :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (inv_nonneg.mpr (hπ i).le) (factorialNormSq_nonneg ρ (D i)))

/-- The mass gradient square is nonnegative for positive component masses. -/
theorem massGradNormSq_nonneg {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)]
    {μ : Measure (Vec 2)} {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D : ∀ i, JetL2 μ (K i + 1) (E i)) : 0 ≤ massGradNormSq ρ π D := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (inv_nonneg.mpr (hπ i).le)
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (factorialWeight_nonneg ρ j.val)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-! The exact mass norm is a fixed continuous linear readout of the
finite family of genuine Sobolev carriers. -/

section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

def massWeightedCarrierCLM (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) :
    (∀ i, TorusHk (K i) (E i)) →L[ℝ]
      PiLp 2 (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i) (E i)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun i =>
    JetL2 (volume.restrict AVenhance.unitCube) (K i) (E i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      ((Real.sqrt ((π i)⁻¹) • factorialWeightedJetCLM ρ (K i)).comp
        (torusHkGraph (E := E i) (K i)).toSubmodule.subtypeL).comp (ContinuousLinearMap.proj i)))

omit [Fintype ι] in
@[simp] theorem massWeightedCarrierCLM_apply (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (w : ∀ i, TorusHk (K i) (E i)) :
    massWeightedCarrierCLM K ρ π w = massWeightedJet ρ π (fun i => (w i).val) := rfl

theorem massWeightedCarrierCLM_normSq (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (w : ∀ i, TorusHk (K i) (E i)) :
    ‖massWeightedCarrierCLM K ρ π w‖ ^ 2 = massNormSq ρ π (fun i => (w i).val) :=
  massWeightedJet_normSq ρ π hπ _

theorem massWeightedCarrierCLM_norm (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (w : ∀ i, TorusHk (K i) (E i)) :
    ‖massWeightedCarrierCLM K ρ π w‖ = Real.sqrt (massNormSq ρ π (fun i => (w i).val)) :=
  massWeightedJet_norm ρ π hπ _
end

end AVRegularity.CoupledEnergy.Variational
end
