-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledEnergyTorus
public import AVRegularity.Statements.Intermediate.CycleOutput.ObsErrorNorm
import AVRegularity.CycleComparison.Error.WeakSolution
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.Families.TorusCompatible.WeakStage
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurMatrix
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.CycleReference.OcChart
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsSmoothOn
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.IsSampledEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Error

/-! The physical energy error of a forced triangular system: component energy, the factorial
shift and the forward envelope give `x_v ≤ C d_v + C ∑_u b_{vu} x_u`, and substitution in
topological order terminates at depth `H`. For a triangular coefficient (rank `r ≤ H`,
coefficients only from lower to higher rank) whose Schur matrix is dominated by a matrix with row
and column sums at most `S`, the masses `π_v L^{2r_v}` with `L = 8S + 1` satisfy the Schur
condition of the coupled energy estimate (`coupled_energy_torus`); converting back to the masses
`π` costs `L^H`. The error norm `obsErrorNorm` (plain `L²_π` and gradient) of every solution is
then at most `8 L^H` times the initial, flux and source norms in the slot norms `ρ, K`. -/

section Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- Truncation does not increase the factorial norm. -/
theorem factorialNormSq_truncateTorusHk_le {K M : ℕ} (hKM : K ≤ M) (ρ : ℝ) (U : TorusHk M E) :
    factorialNormSq ρ (truncateTorusHk hKM U).val ≤ factorialNormSq ρ U.val := by
  unfold factorialNormSq
  have hterm : ∀ j : Fin (K + 1),
      factorialWeight ρ j.val * derivativeNormSq (truncateTorusHk hKM U).val j =
        factorialWeight ρ (Fin.castLE (Nat.succ_le_succ hKM) j).val *
          derivativeNormSq U.val (Fin.castLE (Nat.succ_le_succ hKM) j) := fun _ => rfl
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  calc ∑ j : Fin (K + 1), factorialWeight ρ (Fin.castLE (Nat.succ_le_succ hKM) j).val *
        derivativeNormSq U.val (Fin.castLE (Nat.succ_le_succ hKM) j)
      = ∑ j ∈ Finset.univ.map (Fin.castLEEmb (Nat.succ_le_succ hKM)),
          factorialWeight ρ j.val * derivativeNormSq U.val j := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j : Fin (M + 1), factorialWeight ρ j.val * derivativeNormSq U.val j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => mul_nonneg (factorialWeight_nonneg ρ _) (derivativeNormSq_nonneg _ _))

/-- Truncation does not increase the gradient factorial norm. -/
theorem gradFactorialNormSq_truncateTorusHk_le {K M : ℕ} (hKM : K ≤ M) (ρ : ℝ)
    (U : TorusHk (M + 1) E) :
    gradFactorialNormSq ρ (truncateTorusHk (Nat.succ_le_succ hKM) U).val ≤
      gradFactorialNormSq ρ U.val := by
  unfold gradFactorialNormSq
  have hterm : ∀ j : Fin (K + 1),
      factorialWeight ρ j.val * ∑ w : DerivativeWord2 (j.val + 1),
          ‖(truncateTorusHk (Nat.succ_le_succ hKM) U).val
            ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩‖ ^ 2 =
        factorialWeight ρ (Fin.castLE (Nat.succ_le_succ hKM) j).val *
          ∑ w : DerivativeWord2 ((Fin.castLE (Nat.succ_le_succ hKM) j).val + 1),
            ‖U.val ⟨⟨(Fin.castLE (Nat.succ_le_succ hKM) j).val + 1,
              Nat.succ_lt_succ (Fin.castLE (Nat.succ_le_succ hKM) j).isLt⟩, w⟩‖ ^ 2 :=
    fun _ => rfl
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  calc ∑ j : Fin (K + 1), factorialWeight ρ (Fin.castLE (Nat.succ_le_succ hKM) j).val *
          ∑ w : DerivativeWord2 ((Fin.castLE (Nat.succ_le_succ hKM) j).val + 1),
            ‖U.val ⟨⟨(Fin.castLE (Nat.succ_le_succ hKM) j).val + 1,
              Nat.succ_lt_succ (Fin.castLE (Nat.succ_le_succ hKM) j).isLt⟩, w⟩‖ ^ 2
      = ∑ j ∈ Finset.univ.map (Fin.castLEEmb (Nat.succ_le_succ hKM)),
          factorialWeight ρ j.val * ∑ w : DerivativeWord2 (j.val + 1),
            ‖U.val ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩‖ ^ 2 := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j : Fin (M + 1), factorialWeight ρ j.val * ∑ w : DerivativeWord2 (j.val + 1),
          ‖U.val ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => mul_nonneg (factorialWeight_nonneg ρ _)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _))

variable {μ : Measure (Vec 2)}

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- At order zero the factorial norm does not depend on the radius. -/
theorem factorialNormSq_order_zero (ρ ρ' : ℝ) (D : JetL2 μ 0 E) :
    factorialNormSq ρ D = factorialNormSq ρ' D := by
  unfold factorialNormSq
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp [factorialWeight]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- At order zero the gradient factorial norm does not depend on the radius. -/
theorem gradFactorialNormSq_order_zero (ρ ρ' : ℝ) (D : JetL2 μ (0 + 1) E) :
    gradFactorialNormSq ρ D = gradFactorialNormSq ρ' D := by
  unfold gradFactorialNormSq
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp [factorialWeight]

end Truncation

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The plain mass norm of the truncation is at most the slot mass norm. -/
theorem massNormSq_zero_le (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {K : ι → ℕ}
    (U : ∀ i, TorusHk (K i) (h i)) :
    massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun i => (truncateTorusHk (Nat.zero_le _) (U i)).val) ≤
      massNormSq (E := h) (K := K) ρ π (fun i => (U i).val) := by
  unfold massNormSq
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (hπ i).le)
  rw [factorialNormSq_order_zero 1 ρ]
  exact factorialNormSq_truncateTorusHk_le (Nat.zero_le _) ρ (U i)

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The plain gradient mass norm of the truncation is at most the slot gradient mass norm. -/
theorem massGradNormSq_zero_le (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {K : ι → ℕ}
    (W : ∀ i, TorusHk (K i + 1) (h i)) :
    massGradNormSq (E := h) (K := fun _ => 0) 1 π
        (fun i => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W i)).val) ≤
      massGradNormSq (E := h) (K := K) ρ π (fun i => (W i).val) := by
  unfold massGradNormSq
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (hπ i).le)
  rw [gradFactorialNormSq_order_zero 1 ρ]
  exact gradFactorialNormSq_truncateTorusHk_le (Nat.zero_le _) ρ (W i)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem integrable_massGradNormSq (ρ : ℝ) (π : ι → ℝ) {K : ι → ℕ} {t₀ t₁ : ℝ}
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc t₀ t₁))) :
    Integrable (fun s => massGradNormSq (E := h) (K := K) ρ π (fun i => (w i s).val))
      (volume.restrict (Set.Icc t₀ t₁)) := by
  unfold massGradNormSq
  exact integrable_finsetSum _ fun i _ =>
    (Coarse.integrable_gradFactorialNormSq_torus (hw i)).const_mul _

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem integrable_massNormSq {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, CompleteSpace (E i)] (ρ : ℝ) (π : ι → ℝ) {K : ι → ℕ} {t₀ t₁ : ℝ}
    (F : ∀ i, ℝ → TorusHk (K i) (E i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc t₀ t₁))) :
    Integrable (fun s => massNormSq (E := E) (K := K) ρ π (fun i => (F i s).val))
      (volume.restrict (Set.Icc t₀ t₁)) := by
  unfold massNormSq
  exact integrable_finsetSum _ fun i _ =>
    (Coarse.integrable_factorialNormSq_torus (hF i)).const_mul _

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The square root of the slot mass norm of an integrable source is integrable. -/
theorem integrable_sqrt_massNormSq (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) {K : ι → ℕ}
    {t₀ t₁ : ℝ} (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc t₀ t₁))) :
    Integrable (fun s => Real.sqrt (massNormSq (E := h) (K := K) ρ π (fun i => (g i s).val)))
      (volume.restrict (Set.Icc t₀ t₁)) := by
  have hmeas : AEStronglyMeasurable
      (fun s => massNormSq (E := h) (K := K) ρ π (fun i => (g i s).val))
      (volume.restrict (Set.Icc t₀ t₁)) := by
    unfold massNormSq
    exact Finset.aestronglyMeasurable_fun_sum
      (f := fun i s => (π i)⁻¹ * factorialNormSq ρ (g i s).val) Finset.univ fun i _ =>
      (((Coarse.continuous_factorialNormSq ρ (K i)).comp
        continuous_subtype_val).comp_aestronglyMeasurable (hg i).aestronglyMeasurable).const_mul _
  have hbound : Integrable (fun s => ∑ i, Real.sqrt ((π i)⁻¹ * factorialWeightMax ρ (K i)) *
      ‖g i s‖) (volume.restrict (Set.Icc t₀ t₁)) :=
    integrable_finsetSum _ fun i _ => ((hg i).norm).const_mul _
  refine hbound.mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hterm : ∀ i, 0 ≤ Real.sqrt ((π i)⁻¹ * factorialWeightMax ρ (K i)) * ‖g i s‖ :=
    fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => hterm i)]
  refine le_trans ?_ (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hterm i)
  unfold massNormSq
  refine Finset.sum_le_sum fun i _ => ?_
  have hw : 0 ≤ (π i)⁻¹ * factorialWeightMax ρ (K i) :=
    mul_nonneg (inv_nonneg.2 (hπ i).le)
      ((factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ ⟨0, Nat.succ_pos _⟩))
  rw [mul_pow, Real.sq_sqrt hw, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (hπ i).le)
  have hn : ‖(g i s).val‖ = ‖g i s‖ := rfl
  rw [← hn]
  exact factorialNormSq_upper ρ (g i s).val

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The error norm from the slot bounds.** -/
theorem obsErrorNorm_le_of_bounds (ν : ℝ) (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (K : ι → ℕ) (t₀ t₁ : ℝ) (u : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc t₀ t₁))) (ρ X Y : ℝ) (hY : 0 ≤ Y)
    (hval : ∀ t ∈ Set.Icc t₀ t₁, massNormSq (E := h) (K := K) ρ π (fun i => (u i t).val) ≤ X)
    (hgrad : ∫ s in Set.Icc t₀ t₁,
      massGradNormSq (E := h) (K := K) ρ π (fun i => (w i s).val) ≤ Y) :
    obsErrorNorm ν π K t₀ t₁ u w ≤ ENNReal.ofReal (Real.sqrt X + Real.sqrt (ν * Y)) := by
  unfold obsErrorNorm
  rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  refine add_le_add ?_ ?_
  · refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    exact (massNormSq_zero_le ρ π hπ (fun i => u i t)).trans (hval t ht)
  · have hint := integrable_massGradNormSq ρ π w hw
    have hl : ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (massGradNormSq (E := h) (K := fun _ => 0)
        1 π (fun i => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (w i s)).val)) ≤
        ENNReal.ofReal Y := by
      calc ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (massGradNormSq (E := h) (K := fun _ => 0)
            1 π (fun i => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (w i s)).val))
          ≤ ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal
              (massGradNormSq (E := h) (K := K) ρ π (fun i => (w i s).val)) :=
            lintegral_mono fun s => ENNReal.ofReal_le_ofReal
              (massGradNormSq_zero_le ρ π hπ (fun i => w i s))
        _ = ENNReal.ofReal (∫ s in Set.Icc t₀ t₁,
              massGradNormSq (E := h) (K := K) ρ π (fun i => (w i s).val)) :=
            (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun s =>
              Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.2 (hπ i).le)
                (Coarse.gradFactorialNormSq_nonneg ρ _))).symm
        _ ≤ ENNReal.ofReal Y := ENNReal.ofReal_le_ofReal hgrad
    calc ENNReal.ofReal (Real.sqrt ν) *
          (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (massGradNormSq (E := h) (K := fun _ => 0)
            1 π (fun i => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _))
              (w i s)).val))) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (Real.sqrt ν) * ENNReal.ofReal Y ^ (1 / 2 : ℝ) :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hl (by norm_num))
      _ = ENNReal.ofReal (Real.sqrt (ν * Y)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hY (by norm_num), ← Real.sqrt_eq_rpow,
            ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.sqrt_mul hν.le]

/-- **Energy error of a forced triangular system.** -/
theorem forced_error_energy (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (ρ : ℝ) (hρ : 0 < ρ)
    (ν : ℝ) (hν : 0 < ν) (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖v t x‖ ≤ C)
    (hv_meas : Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => v p.1 p.2)
    (hv_smooth : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hv_div : ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hv_per : ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (v t))
    (a B₀ lam : ℝ) (ha : 0 ≤ a) (hB₀ : 1 ≤ B₀) (hlam : 0 < lam) (Kmax : ℕ)
    (hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hB : B₀ * ρ / lam ≤ 1 / 2) (hab : a * B₀ * ρ ^ 2 ≤ ν / 8)
    (D : ℕ) (hD : 2 ≤ D)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (hK : ∀ i, K i ≤ Kmax)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hA_meas : ∀ i i' d, Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => A i i' d p.1 p.2)
    (hA_smooth : ∀ i i' d, ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hA_per : ∀ i i' d, ∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (A i i' d t))
    (hA_fin : ∀ i i' d, coefficientSeminorm ρ (K i) t₀ t₁ (A i i' d) ≠ ⊤)
    (r : ι → ℕ) (H : ℕ) (hrH : ∀ i, r i ≤ H)
    (hr : ∀ i i', ¬ r i' < r i → ∀ d, A i i' d = 0)
    (c : ι → ι → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hc : ∀ i i', schurMatrix ν ρ π K D t₀ t₁ A i i' ≤ c i i')
    (hrow : ∀ i, ∑ i', c i i' ≤ S) (hcol : ∀ i', ∑ i, c i i' ≤ S)
    (f : ∀ i, TorusHk (K i) (h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc t₀ t₁)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc t₀ t₁)))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionTorus ν t₀ t₁ v D K A f F g u w) :
    obsErrorNorm ν π K t₀ t₁ u w ≤ ENNReal.ofReal (8 * (8 * S + 1) ^ H *
      (Real.sqrt (massNormSq (E := h) (K := K) ρ π (fun i => (f i).val)) +
        Real.sqrt (ν⁻¹ * ∫ s in Set.Icc t₀ t₁,
          massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := K) ρ π
            (fun i => (F i s).val)) +
        ∫ s in Set.Icc t₀ t₁,
          Real.sqrt (massNormSq (E := h) (K := K) ρ π (fun i => (g i s).val)))) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 8 * S + 1 := ⟨_, rfl⟩
  rw [← hLdef]
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hL0 : 0 < L := by linarith
  have hπ' : ∀ i, 0 < rankScaledMass π r L i := rankScaledMass_pos hπ hL0
  have hschur := schurCondition_rankScaledMass ν ρ hν hρ π hπ K D t₀ t₁ A hA_fin r hr L hL1
    c S hc hrow hcol (by rw [hLdef]; linarith)
  have hE := (coupled_energy_torus t₀ t₁ ht ρ hρ ν hν v hv_bdd hv_meas hv_smooth hv_div hv_per
    a B₀ lam ha hB₀ hlam Kmax hjets hB hab D hD (rankScaledMass π r L) hπ' K hK A hA_meas
    hA_smooth hA_per hA_fin hschur f F hF g hg).2.2 u w hsol
  -- the real quantities, kept opaque
  generalize hmf : massNormSq (E := h) (K := K) ρ π (fun i => (f i).val) = mf at *
  generalize hmf' : massNormSq (E := h) (K := K) ρ (rankScaledMass π r L)
    (fun i => (f i).val) = mf' at hE
  have hmf0 : 0 ≤ mf := hmf ▸ CoupledEnergy.Variational.massNormSq_nonneg ρ π hπ _
  have hmf'le : mf' ≤ mf := by
    rw [← hmf, ← hmf']; exact massNormSq_rankScaledMass_le ρ π hπ r L hL1 _
  have hFint := integrable_massNormSq ρ π F hF
  have hFle : ∫ s in Set.Icc t₀ t₁, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
      (K := K) ρ (rankScaledMass π r L) (fun i => (F i s).val) ≤
      ∫ s in Set.Icc t₀ t₁, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
        (K := K) ρ π (fun i => (F i s).val) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun s =>
      CoupledEnergy.Variational.massNormSq_nonneg ρ _ (fun i => hπ' i) _) hFint
      (Filter.Eventually.of_forall fun s => massNormSq_rankScaledMass_le ρ π hπ r L hL1 _)
  have hFnn : 0 ≤ ∫ s in Set.Icc t₀ t₁, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
      (K := K) ρ (rankScaledMass π r L) (fun i => (F i s).val) :=
    integral_nonneg fun s => CoupledEnergy.Variational.massNormSq_nonneg ρ _ (fun i => hπ' i) _
  generalize hIF : ∫ s in Set.Icc t₀ t₁, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
      (K := K) ρ π (fun i => (F i s).val) = IF at *
  generalize hIF' : ∫ s in Set.Icc t₀ t₁,
      massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
      (K := K) ρ (rankScaledMass π r L) (fun i => (F i s).val) = IF' at hE hFle hFnn
  have hgint := integrable_sqrt_massNormSq ρ π hπ g hg
  have hgle : ∫ s in Set.Icc t₀ t₁, Real.sqrt (massNormSq (E := h) (K := K) ρ
      (rankScaledMass π r L) (fun i => (g i s).val)) ≤
      ∫ s in Set.Icc t₀ t₁, Real.sqrt (massNormSq (E := h) (K := K) ρ π
        (fun i => (g i s).val)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => Real.sqrt_nonneg _) hgint
      (Filter.Eventually.of_forall fun s =>
        Real.sqrt_le_sqrt (massNormSq_rankScaledMass_le ρ π hπ r L hL1 _))
  have hgnn : 0 ≤ ∫ s in Set.Icc t₀ t₁, Real.sqrt (massNormSq (E := h) (K := K) ρ
      (rankScaledMass π r L) (fun i => (g i s).val)) :=
    integral_nonneg fun s => Real.sqrt_nonneg _
  generalize hIg : ∫ s in Set.Icc t₀ t₁, Real.sqrt (massNormSq (E := h) (K := K) ρ π
      (fun i => (g i s).val)) = Ig at *
  generalize hIg' : ∫ s in Set.Icc t₀ t₁, Real.sqrt (massNormSq (E := h) (K := K) ρ
      (rankScaledMass π r L) (fun i => (g i s).val)) = Ig' at hE hgle hgnn
  -- the bound of the rescaled energy
  obtain ⟨R', hR'def⟩ : ∃ R' : ℝ, R' = 2 * mf' + 8 / ν * IF' + 10 * Ig' ^ 2 := ⟨_, rfl⟩
  rw [← hR'def] at hE
  have hIF0 : 0 ≤ IF := hFnn.trans hFle
  have hIg0 : 0 ≤ Ig := hgnn.trans hgle
  have hR'le : R' ≤ 10 * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig) ^ 2 := by
    have h1 : 2 * mf' ≤ 2 * (Real.sqrt mf) ^ 2 := by
      rw [Real.sq_sqrt hmf0]; linarith
    have h2 : 8 / ν * IF' ≤ 8 * (Real.sqrt (ν⁻¹ * IF)) ^ 2 := by
      rw [Real.sq_sqrt (mul_nonneg (inv_nonneg.2 hν.le) hIF0), div_eq_mul_inv, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFle (inv_nonneg.2 hν.le))
        (by norm_num)
    have h3 : 10 * Ig' ^ 2 ≤ 10 * Ig ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgnn hgle 2) (by norm_num)
    have ha0 := Real.sqrt_nonneg mf
    have hb0 := Real.sqrt_nonneg (ν⁻¹ * IF)
    rw [hR'def]
    nlinarith [mul_nonneg ha0 hb0, mul_nonneg ha0 hIg0, mul_nonneg hb0 hIg0]
  -- the rescaled gradient integral
  have hwint' := integrable_massGradNormSq ρ (rankScaledMass π r L) w hsol.2.1
  have hLH : 0 ≤ L ^ (2 * H) := pow_nonneg hL0.le _
  have hgradπ : ∫ s in Set.Icc t₀ t₁,
      massGradNormSq (E := h) (K := K) ρ π (fun i => (w i s).val) ≤
      L ^ (2 * H) * ∫ s in Set.Icc t₀ t₁, massGradNormSq (E := h) (K := K) ρ
        (rankScaledMass π r L) (fun i => (w i s).val) := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun s =>
      CoupledEnergy.Variational.massGradNormSq_nonneg ρ π hπ _) (hwint'.const_mul _)
      (Filter.Eventually.of_forall fun s =>
        massGradNormSq_le_rankScaledMass ρ π hπ r L hL1 H hrH _)
  have hG'nn : 0 ≤ ∫ s in Set.Icc t₀ t₁, massGradNormSq (E := h) (K := K) ρ
      (rankScaledMass π r L) (fun i => (w i s).val) :=
    integral_nonneg fun s => CoupledEnergy.Variational.massGradNormSq_nonneg ρ _
      (fun i => hπ' i) _
  generalize hG' : ∫ s in Set.Icc t₀ t₁, massGradNormSq (E := h) (K := K) ρ
      (rankScaledMass π r L) (fun i => (w i s).val) = G' at hE hG'nn hgradπ
  have hνG : 0 ≤ ν / 2 * G' := mul_nonneg (div_nonneg hν.le (by norm_num)) hG'nn
  have hE0 := hE t₀ ⟨le_rfl, ht⟩
  have hu0 := CoupledEnergy.Variational.massNormSq_nonneg ρ _ (fun i => hπ' i)
    (fun i => (u i t₀).val)
  have hR'nn : 0 ≤ R' := by linarith
  have hG'le : G' ≤ 2 / ν * R' := by
    have h1 : ν / 2 * G' ≤ R' := by linarith
    calc G' = 2 / ν * (ν / 2 * G') := by field_simp
      _ ≤ 2 / ν * R' := mul_le_mul_of_nonneg_left h1 (div_nonneg (by norm_num) hν.le)
  have hval : ∀ t ∈ Set.Icc t₀ t₁,
      massNormSq (E := h) (K := K) ρ π (fun i => (u i t).val) ≤ L ^ (2 * H) * R' := by
    intro t ht'
    have h1 := massNormSq_le_rankScaledMass ρ π hπ r L hL1 H hrH (fun i => (u i t).val)
    have h2 := hE t ht'
    have h4 : massNormSq (E := h) (K := K) ρ (rankScaledMass π r L)
        (fun i => (u i t).val) ≤ R' := by linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h4 hLH)
  have hgrad : ∫ s in Set.Icc t₀ t₁,
      massGradNormSq (E := h) (K := K) ρ π (fun i => (w i s).val) ≤
      L ^ (2 * H) * (2 / ν * R') :=
    hgradπ.trans (mul_le_mul_of_nonneg_left hG'le hLH)
  have hY : 0 ≤ L ^ (2 * H) * (2 / ν * R') :=
    mul_nonneg hLH (mul_nonneg (div_nonneg (by norm_num) hν.le) hR'nn)
  refine (obsErrorNorm_le_of_bounds ν hν π hπ K t₀ t₁ u w hsol.2.1 ρ _ _ hY hval hgrad).trans
    (ENNReal.ofReal_le_ofReal ?_)
  -- the real inequality
  have hsq : Real.sqrt (L ^ (2 * H)) = L ^ H := by
    rw [pow_mul, pow_right_comm, Real.sqrt_sq (pow_nonneg hL0.le _)]
  have e1 : Real.sqrt (L ^ (2 * H) * R') = L ^ H * Real.sqrt R' := by
    rw [Real.sqrt_mul hLH, hsq]
  have e2 : Real.sqrt (ν * (L ^ (2 * H) * (2 / ν * R'))) =
      L ^ H * (Real.sqrt 2 * Real.sqrt R') := by
    have : ν * (L ^ (2 * H) * (2 / ν * R')) = L ^ (2 * H) * (2 * R') := by
      field_simp
    rw [this, Real.sqrt_mul hLH, hsq, Real.sqrt_mul (by norm_num)]
  rw [e1, e2]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs10 : Real.sqrt 10 ≤ 16 / 5 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hR'sq : Real.sqrt R' ≤ Real.sqrt 10 * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig) := by
    have hsum : 0 ≤ Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig :=
      add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hIg0
    calc Real.sqrt R' ≤ Real.sqrt (10 * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig) ^ 2) :=
          Real.sqrt_le_sqrt hR'le
      _ = Real.sqrt 10 * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hsum]
  have hLHn : 0 ≤ L ^ H := pow_nonneg hL0.le _
  have hsR : 0 ≤ Real.sqrt R' := Real.sqrt_nonneg _
  have hs2n : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs10n : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg _
  have hsum : 0 ≤ Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig :=
    add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hIg0
  have key : (1 + Real.sqrt 2) * Real.sqrt R' ≤
      8 * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig) := by
    calc (1 + Real.sqrt 2) * Real.sqrt R'
        ≤ (5 / 2) * (Real.sqrt 10 * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig)) :=
          mul_le_mul (by linarith) hR'sq hsR (by norm_num)
      _ ≤ (5 / 2) * (16 / 5 * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs10 hsum) (by norm_num)
      _ = 8 * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig) := by ring
  calc L ^ H * Real.sqrt R' + L ^ H * (Real.sqrt 2 * Real.sqrt R')
      = L ^ H * ((1 + Real.sqrt 2) * Real.sqrt R') := by ring
    _ ≤ L ^ H * (8 * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig)) :=
        mul_le_mul_of_nonneg_left key hLHn
    _ = 8 * L ^ H * (Real.sqrt mf + Real.sqrt (ν⁻¹ * IF) + Ig) := by ring

end AVRegularity.CycleComparison.Error
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.CycleComparison.Error

/-! **The actual source on the error** (in the comparison proposition `cycle_comparison`): if
`û` solves the actual equation on the observation window `[t_p, t₁]` with a residual
presentation `(R, q)` and starts at the model `û(t_p) = 𝑷f`, then `e = u - û` solves
`L_f e_v = ∑ 𝒮_{vu} e_u - div R_v - q_v` from `u(t_p) - 𝑷f`; component energy with the forward
envelope and the triangular (depth `H`) structure of the edges bounds
`‖e‖_{L^∞L²_π} + √ν ‖∇e‖_{L²L²_π}` by a constant depending only on the forward constant, the
envelope sum and `H`, times the preparation discrepancy plus the residual norms in the slots
`K_v`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The slot mass norm of `0 - X` is that of `X`. -/
theorem massNormSq_zero_sub {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, CompleteSpace (E i)] {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (X : ∀ i, TorusHk (K i) (E i)) :
    massNormSq (E := E) (K := K) ρ π (fun i => (0 - X i).val) =
      massNormSq (E := E) (K := K) ρ π (fun i => (X i).val) := by
  unfold massNormSq factorialNormSq derivativeNormSq
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  beta_reduce
  have hneg : (0 - X i).val = -(X i).val := by rw [zero_sub]; rfl
  rw [hneg, WithLp.ofLp_neg, Pi.neg_apply, norm_neg]

/-- **The error clause of the comparison.** -/
theorem comparison_error_bound {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (H Kmax : ℕ) (hD : 2 ≤ D) (Cfw Cth : ℝ) (hCfw : 0 ≤ Cfw) (hCth : 0 ≤ Cth)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (hK : ∀ v, K v ≤ Kmax)
    (ν : ℝ) (hν : 0 < ν) (b : ℝ → Vec 2 → Vec 2) (tS tp t₁ : ℝ) (htS : tS ≤ tp) (htp : tp ≤ t₁)
    (hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc tp t₁, ∀ x, ‖b t x‖ ≤ C)
    (hv_meas : Measurable fun p : Set.Icc tp t₁ × Vec 2 => b p.1 p.2)
    (hv_smooth : ∀ t ∈ Set.Icc tp t₁, ContDiff ℝ (⊤ : ℕ∞) (b t))
    (hv_div : ∀ t ∈ Set.Icc tp t₁, ∀ x, ∑ k : Fin 2, fderiv ℝ (b t) x (basisVec k) k = 0)
    (hv_per : ∀ t ∈ Set.Icc tp t₁, AVenhance.IsZ2Periodic (b t))
    (a₂ B₂ lam₂ ρs : ℝ) (ha₂ : 0 ≤ a₂) (hB₂ : 1 ≤ B₂) (hlam₂ : 0 < lam₂) (hρs : 0 < ρs)
    (hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc tp t₁, ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (b t)) l x‖ ≤
        a₂ * B₂ ^ l * (l.factorial : ℝ) * lam₂ ^ ((1 : ℤ) - l))
    (hB₂ρ : B₂ * ρs / lam₂ ≤ 1 / 2) (hab : a₂ * B₂ * ρs ^ 2 ≤ ν / 8)
    (F : ChartedFamily ι h D P Ctx) (actual : ∀ p, Ctx p) (hdepth : F.HasDepthAtMost H)
    (e E : ℝ) (he : ∃ N : ℕ, e⁻¹ = N) (htorus : IsTorusCompatible F actual E)
    (n : ι → ℕ) (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tp t₁)) E n)
    (hmeas : F.IsTimeMeasurable)
    (hwin : ∀ p, (∀ t ∈ Set.Icc tp t₁, F.weight p t = 0) ∨
      (Continuous (F.weight p) ∧
        ∃ l : ℤ, ∀ t, ⇑((F.piece p).material t) = ocChart α q Λ m φ hφ l t))
    (A : ι → ι → ℝ) (hA : ∀ v u, 0 ≤ Real.sqrt (π u / π v) * A v u)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ Cth)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ Cth)
    (hfwd : IsSampledEnvelope F π K actual tp t₁ ν e E ρs Cfw
      (fun v u => Real.sqrt (π u / π v) * A v u))
    (P0 : ∀ v, TorusHk (K v) (h v)) (f : ∀ v, TorusHk (K v) (h v))
    (u : ∀ v, ℝ → TorusHk (K v) (h v)) (w : ∀ v, ℝ → TorusHk (K v + 1) (h v))
    (hsol : IsCoupledWeakSolutionTorus ν tS t₁ b D K (edgeCoefficient F ν e E actual K) f
      (fun _ _ => 0) (fun _ _ => 0) u w)
    (X0 : ℝ)
    (hinit : Real.sqrt (massNormSq (E := h) (K := K) ρs π (fun v => (u v tp - P0 v).val)) ≤ X0)
    (û : ∀ v, ℝ → TorusHk (K v) (h v)) (ŵ : ∀ v, ℝ → TorusHk (K v + 1) (h v))
    (R : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (qr : ∀ v, ℝ → TorusHk (K v) (h v))
    (hhat : IsCoupledWeakSolutionTorus ν tp t₁ b D K (edgeCoefficient F ν e E actual K)
      (fun v => û v tp) R qr û ŵ)
    (hstart : ∀ v, û v tp = P0 v)
    (hR : ∀ v, MemLp (R v) 2 (volume.restrict (Set.Icc tp t₁)))
    (hq : ∀ v, Integrable (qr v) (volume.restrict (Set.Icc tp t₁)))
    (X1 : ℝ)
    (hR1 : ν⁻¹ * ∫ s in Set.Icc tp t₁,
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K) ρs π
          (fun v => (R v s).val) ≤ X1 ^ 2)
    (hq1 : ∫ s in Set.Icc tp t₁,
        Real.sqrt (massNormSq (E := h) (K := K) ρs π (fun v => (qr v s).val)) ≤ X1) :
    obsErrorNorm ν π K tp t₁ (fun v t => u v t - û v t) (fun v t => w v t - ŵ v t) ≤
      ENNReal.ofReal (8 * (8 * (Cfw * Cth) + 1) ^ H * (X0 + 2 * X1)) := by
  have hsol' := isCoupledWeakSolutionTorus_restrict_right htS htp hsol
  have hdiff := isCoupledWeakSolutionTorus_sub hsol' hhat
  have hFm := fun v => CoupledEnergy.Variational.timeMemLp_pointwise_sub
    (volume.restrict (Set.Icc tp t₁)) 2 (fun _ => 0) (R v)
    (CoupledEnergy.Variational.timeMemLp_zero _ 2) (hR v)
  have hgm := fun v => CoupledEnergy.Variational.timeIntegrable_pointwise_sub
    (volume.restrict (Set.Icc tp t₁)) (fun _ => 0) (qr v)
    (CoupledEnergy.Variational.timeIntegrable_zero _) (hq v)
  have hsch := fun v u' => sampled_edgeCoefficient_schur F π hπ K actual tp t₁ ν e E ρs Cfw hν hρs
    hCfw (fun v u => Real.sqrt (π u / π v) * A v u)
    hA hfwd v u'
  have hE := forced_error_energy tp t₁ htp ρs hρs ν hν b hv_bdd hv_meas hv_smooth hv_div hv_per
    a₂ B₂ lam₂ ha₂ hB₂ hlam₂ Kmax hjets hB₂ρ hab D hD π hπ K hK
    (edgeCoefficient F ν e E actual K)
    (fun i i' d => physicalCoefficient_window_measurable α q Λ m φ hφ F ν e E tp t₁ n hs hmeas
      hwin actual i i' d.1)
    (fun i i' d t ht => by
      change ContDiff ℝ (K i : ℕ) (fun x => ∑ γ : F.Γ i i',
        constituentPhysical F ν e E actual i i' γ d.1 t x)
      exact ContDiff.sum fun γ _ => hfwd.1 i i' γ d.1 t ht)
    (fun i i' d t _ => htorus.edgeCoefficient_periodic ν e he K i i' d t)
    (fun i i' d => (hsch i i').1 d)
    (CycleJointProofs.sourceDepthRank F H) H (CycleJointProofs.sourceDepthRank_le F H)
    (fun i i' hh d => CycleJointProofs.physicalCoefficient_zero_of_rank F H hdepth ν e E actual
      i i' d.1 hh)
    (fun v u' => Cfw * (Real.sqrt (π u' / π v) * A v u')) (Cfw * Cth) (mul_nonneg hCfw hCth)
    (fun v u' => (hsch v u').2)
    (fun v => by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hrow v) hCfw)
    (fun u' => by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hcol u') hCfw)
    _ _ hFm _ hgm _ _ hdiff
  refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
  have hX1 : 0 ≤ X1 := (integral_nonneg fun s => Real.sqrt_nonneg _).trans hq1
  have h1 : Real.sqrt (massNormSq (E := h) (K := K) ρs π
      (fun i => (u i tp - û i tp).val)) ≤ X0 := by
    simpa only [hstart] using hinit
  have h2 : Real.sqrt (ν⁻¹ * ∫ s in Set.Icc tp t₁,
      massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := K) ρs π
        (fun i => ((fun _ _ => (0 : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))) i s -
          R i s).val)) ≤ X1 := by
    simp only [massNormSq_zero_sub]
    rw [Real.sqrt_le_left hX1]
    exact hR1
  have h3 : ∫ s in Set.Icc tp t₁, Real.sqrt (massNormSq (E := h) (K := K) ρs π
      (fun i => ((fun _ _ => (0 : TorusHk (K i) (h i))) i s - qr i s).val)) ≤ X1 := by
    simp only [massNormSq_zero_sub]
    exact hq1
  have hLH : 0 ≤ 8 * (8 * (Cfw * Cth) + 1) ^ H :=
    mul_nonneg (by norm_num) (pow_nonneg (by nlinarith [mul_nonneg hCfw hCth]) _)
  exact mul_le_mul_of_nonneg_left (by linarith) hLH

end AVRegularity.CycleComparison.Error
end
