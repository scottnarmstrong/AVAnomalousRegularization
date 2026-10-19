-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.GradFactorialNormSq
import AVRegularity.CoupledEnergy.Variational.TorusTimeGraph
public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM
public import AVRegularity.Sobolev.Multiply.Carrier
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The energy and dissipation control the complete higher-order Hilbert jet norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {μ : Measure (Vec 2)} {K : ℕ}

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The zeroth derivative tensor is one nonnegative summand of the factorial energy. -/
theorem derivativeNormSq_zero_le_factorial (ρ : ℝ) (D : JetL2 μ K E) :
    derivativeNormSq D (0 : Fin (K + 1)) ≤ factorialNormSq ρ D := by
  have hs := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (K + 1)))) =>
      mul_nonneg (factorialWeight_nonneg ρ j.val) (derivativeNormSq_nonneg D j))
    (Finset.mem_univ (0 : Fin (K + 1)))
  simpa only [factorialWeight, Fin.val_zero, Nat.mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_pow, div_one, one_mul, factorialNormSq] using hs

omit [BorelSpace E] [CompleteSpace E] in
/-- The full unweighted higher-order graph norm is controlled by value and gradient energy. -/
theorem jetNormSq_le_factorial_add_grad (ρ : ℝ) (hρ : 0 < ρ) (D : JetL2 μ (K + 1) E) :
    ‖D‖ ^ 2 ≤ factorialNormSq ρ (truncateJet (Nat.le_succ K) D) +
      gradFactorialNormSq ρ D / factorialWeightMin ρ K := by
  have hm : 0 < factorialWeightMin ρ K := factorialWeightMin_pos ρ hρ
  have hd : (∑ j : Fin (K + 1), derivativeNormSq D j.succ) ≤
      gradFactorialNormSq ρ D / factorialWeightMin ρ K := by
    rw [le_div_iff₀ hm, mul_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (factorialWeightMin_le ρ j) (derivativeNormSq_nonneg D j.succ)
  have hv := derivativeNormSq_zero_le_factorial ρ (truncateJet (Nat.le_succ K) D)
  have hzero : derivativeNormSq (truncateJet (Nat.le_succ K) D) (0 : Fin (K + 1)) =
      derivativeNormSq D (0 : Fin (K + 2)) := rfl
  rw [hzero] at hv
  rw [jet_norm_sq_eq_sum, Fin.sum_univ_succ]
  exact add_le_add hv hd

end AVRegularity.CoupledEnergy.Variational
end

section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Recover the periodic Sobolev graph after ambient spacetime weak compactness. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Recover one genuine Sobolev carrier by a fixed projection readout after weak compactness. -/
def coupledHighGraphReadout (K : ι → ℕ) (i : ι) :
    CoupledHighHilbert (h := h) K →L[ℝ] TorusHk (K i + 1) (h i) :=
  (closedSubmoduleReadout (torusHkGraph (E := h i) (K i + 1))).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun j => JetL2 (volume.restrict AVenhance.unitCube) (K j + 1) (h j)) i)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in

/-- Carrier recovery preserves every ambient jet wherever the graph constraint holds. -/
theorem coupledHighGraphReadout_val (K : ι → ℕ) (i : ι) (D : CoupledHighHilbert (h := h) K)
    (hD : D i ∈ torusHkGraph (E := h i) (K i + 1)) :
    (coupledHighGraphReadout K i D).val = D i := by
  change (torusHkGraph (E := h i) (K i + 1)).toSubmodule.starProjection (D i) = D i
  exact Submodule.starProjection_eq_self_iff.mpr hD

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The recovered higher-order component is a genuine time L² Sobolev path. -/
theorem highTimeGraphReadout_memLp (K : ι → ℕ) (a b : ℝ)
    (U : CoupledHighTime (h := h) K a b) (i : ι) :
    MemLp (fun t => coupledHighGraphReadout K i (U t)) 2 (volume.restrict (Set.Icc a b)) := by
  let : ∀ j, Module ℝ (JetL2 (volume.restrict AVenhance.unitCube) (K j + 1) (h j)) := fun j => inferInstance
  let : Module ℝ (CoupledHighHilbert (h := h) K) := inferInstance
  let : NormedSpace ℝ (CoupledHighHilbert (h := h) K) := inferInstance
  have hc : MemLp (fun t => U t i) 2 (volume.restrict (Set.Icc a b)) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun j => JetL2 (volume.restrict AVenhance.unitCube) (K j + 1) (h j)) i).comp_memLp' (Lp.memLp U)
  exact closedSubmoduleReadout_memLp (torusHkGraph (E := h i) (K i + 1)) hc

omit [∀ i, FiniteDimensional ℝ (h i)] in

/-- Every ambient weak graph limit agrees almost everywhere with its recovered carrier field. -/
theorem highTimeGraphReadout_val_ae (K : ι → ℕ) (a b : ℝ)
    {u : ℕ → CoupledHighTime (h := h) K a b} {U : CoupledHighTime (h := h) K a b}
    (hlim : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (u n)) atTop (𝓝 (ell U)))
    (hu : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      ∀ i, u n t i ∈ torusHkGraph (E := h i) (K i + 1)) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i, (coupledHighGraphReadout K i (U t)).val = U t i := by
  filter_upwards [highTime_graph_of_weak_limit K a b hlim hu] with t ht
  exact fun i => coupledHighGraphReadout_val K i (U t) (ht i)

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The value representative of the actual weak-jet coefficient multiplier. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The Sobolev multiplier's value is precisely the pointwise coefficient action. -/
theorem torusMulCoefficient_value_ae {K : ℕ} (w : TorusHk K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (hp : AVenhance.IsZ2Periodic C) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    (w.mulCoefficient C hC hp hb).val (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => C x (w.val (valueIndex2 K) x) := by
  have hm := torusJetToL2_ae (multiplicationRawJet C w.toFunction.jet)
    (multiplicationRawJet_memL2On hC w.toFunction.hasPeriodicWeakJet.2.1 hb) (valueIndex2 K)
  have hw := periodicJetRepresentative_ae w.val (valueIndex2 K)
  filter_upwards [hm, hw] with x hx hy
  rw [multiplicationRawJet_value] at hx
  exact hx.trans (congrArg (C x) hy)
end

/-! Linear factorial reweighting and its exact Hilbert pairings. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
variable {μ : Measure (Vec 2)} {K : ℕ}

/-- The actual weighted jet, keeping each L² component rather than taking its norm. -/
def factorialWeightedJet (ρ : ℝ) (D : JetL2 μ K E) : JetL2 μ K E :=
  WithLp.toLp 2 fun j => factorialRootWeight ρ j.1.val • D j

/-- This linear reweighting realizes the exact factorial square. -/
theorem factorialWeightedJet_normSq (ρ : ℝ) (D : JetL2 μ K E) :
    ‖factorialWeightedJet ρ D‖ ^ 2 = factorialNormSq ρ D := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : JetIndex2 K, ‖factorialRootWeight ρ j.1.val • D j‖ ^ 2) = _
  rw [Fintype.sum_sigma]
  unfold factorialNormSq derivativeNormSq
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, factorialRootWeight_sq]

/-- The weighted jet norm is the precise factorial norm of the coupled energy estimate. -/
theorem factorialWeightedJet_norm (ρ : ℝ) (D : JetL2 μ K E) :
    ‖factorialWeightedJet ρ D‖ = Real.sqrt (factorialNormSq ρ D) := by
  rw [← factorialWeightedJet_normSq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

@[simp] theorem factorialWeightedJet_add (ρ : ℝ) (D Q : JetL2 μ K E) :
    factorialWeightedJet ρ (D + Q) = factorialWeightedJet ρ D + factorialWeightedJet ρ Q := by
  apply PiLp.ext
  intro j
  exact smul_add _ _ _

@[simp] theorem factorialWeightedJet_sum {J : Type*} (ρ : ℝ) (s : Finset J)
    (D : J → JetL2 μ K E) :
    factorialWeightedJet ρ (∑ j ∈ s, D j) = ∑ j ∈ s, factorialWeightedJet ρ (D j) := by
  apply PiLp.ext
  intro a
  simp [factorialWeightedJet, Finset.smul_sum]

/-- The factorial norm satisfies its exact finite triangle inequality. -/
theorem factorialNorm_sum_le {J : Type*} (ρ : ℝ) (s : Finset J) (D : J → JetL2 μ K E) :
    Real.sqrt (factorialNormSq ρ (∑ j ∈ s, D j)) ≤
      ∑ j ∈ s, Real.sqrt (factorialNormSq ρ (D j)) := by
  simp_rw [← factorialWeightedJet_norm]
  rw [factorialWeightedJet_sum]
  exact norm_sum_le _ _

/-- The differentiated forcing pairing has its exact Cauchy-Schwarz bound. -/
theorem factorialPairing_abs_le (ρ : ℝ) (D Q : JetL2 μ K E) :
    |∑ j : Fin (K + 1), factorialWeight ρ j.val * ∑ w : DerivativeWord2 j.val,
        inner ℝ (D ⟨j, w⟩) (Q ⟨j, w⟩)| ≤
      Real.sqrt (factorialNormSq ρ D) * Real.sqrt (factorialNormSq ρ Q) := by
  have heq : inner ℝ (factorialWeightedJet ρ D) (factorialWeightedJet ρ Q) =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val * ∑ w : DerivativeWord2 j.val,
        inner ℝ (D ⟨j, w⟩) (Q ⟨j, w⟩) := by
    rw [PiLp.inner_apply]
    change (∑ j : JetIndex2 K, inner ℝ (factorialRootWeight ρ j.1.val • D j)
      (factorialRootWeight ρ j.1.val • Q j)) = _
    rw [Fintype.sum_sigma]
    simp only [real_inner_smul_left, real_inner_smul_right]
    simp_rw [← mul_assoc, ← pow_two, factorialRootWeight_sq]
    simp only [Finset.mul_sum]
  rw [← heq]
  simpa only [factorialWeightedJet_norm] using
    abs_real_inner_le_norm (factorialWeightedJet ρ D) (factorialWeightedJet ρ Q)
end

end AVRegularity.CoupledEnergy.Variational
end
