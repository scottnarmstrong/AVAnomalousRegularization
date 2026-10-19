-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.Tested
public import AVRegularity.Statements.Intermediate.CycleComparison.TorusJetOrder
import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.ComponentStrong
public import AVRegularity.Construction.Preservation.Buffer.KernelMaterialIncrement
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence
import Mathlib.Algebra.Order.Star.Real

section
/-! **From word-by-word residual norms to mass norms**. If every derivative word
`β` of order `j ≤ k` has residual norm (weight `ρ^j`) at most `X`, the forcing `(F, g)` satisfies
`∫ ‖F‖²_{ρ,k;π} ≤ W ν X²` and `∫ ‖g‖_{ρ,k;π} ≤ W X`, `W = ∑_{j ≤ k} 2^j` the number of words.
The factorial weight `ρ^{2j}/(j!)²` is at most the residual's `ρ^{2j}`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.EntryTerminal.ForcedEnergy

section Densities
variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)] {k : ℕ}

/-- The squared `L²` norm of the word `β` of order `j` of a torus Sobolev element is the lower
integral over the cell of the squared norm of its jet function. -/
theorem ofReal_jet_norm_sq_eq_lintegral {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ} (U : TorusHk K F)
    (a : JetIndex2 K) :
    ENNReal.ofReal (‖U.val a‖ ^ 2) =
      ∫⁻ x in AVenhance.unitCube, ‖U.toFunction.jet a x‖ₑ ^ 2 := by
  have hae := AVRegularity.KernelEnergy.torusHk_toFunction_jet_ae U a
  have hm : MemLp (U.toFunction.jet a) 2 (volume.restrict AVenhance.unitCube) :=
    (Lp.memLp (U.val a)).ae_eq hae.symm
  have hn : ‖U.val a‖ =
      (eLpNorm (U.toFunction.jet a) 2 (volume.restrict AVenhance.unitCube)).toReal := by
    rw [eLpNorm_congr_ae hae, ← Lp.norm_def]
  rw [hn]
  exact AVRegularity.CycleComparison.Reconstruction.ofReal_eLpNorm_sq_cell hm

/-- The real word density `ρ^{2j} ∑_v π_v⁻¹ ‖∂^β D_v‖²_{L²}`. -/
def wordDensity (ρ : ℝ) (π : ι → ℝ) (D : ∀ v, TorusHk k (E v)) (j : Fin (k + 1))
    (β : DerivativeWord2 j.val) : ℝ :=
  ρ ^ (2 * j.val) * ∑ v, (π v)⁻¹ * ‖(D v).val ⟨j, β⟩‖ ^ 2

theorem wordDensity_nonneg (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (D : ∀ v, TorusHk k (E v))
    (j : Fin (k + 1)) (β : DerivativeWord2 j.val) : 0 ≤ wordDensity ρ π D j β := by
  unfold wordDensity
  refine mul_nonneg ?_ (Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le) (sq_nonneg _))
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

/-- The mass norm is at most the sum of the word densities. -/
theorem massNormSq_le_sum_wordDensity (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (D : ∀ v, TorusHk k (E v)) :
    massNormSq (E := E) (K := fun _ => k) ρ π (fun v => (D v).val) ≤
      ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val, wordDensity ρ π D j β := by
  have hmass : massNormSq (E := E) (K := fun _ => k) ρ π (fun v => (D v).val) =
      ∑ v, (π v)⁻¹ * factorialNormSq ρ (D v).val := rfl
  rw [hmass]
  have hexp : ∀ v, (π v)⁻¹ * factorialNormSq ρ (D v).val =
      ∑ j : Fin (k + 1), factorialWeight ρ j.val * ∑ β : DerivativeWord2 j.val,
        (π v)⁻¹ * ‖(D v).val ⟨j, β⟩‖ ^ 2 := by
    intro v
    unfold factorialNormSq derivativeNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  have hsw : ∑ v, factorialWeight ρ j.val * ∑ β : DerivativeWord2 j.val,
        (π v)⁻¹ * ‖(D v).val ⟨j, β⟩‖ ^ 2 =
      factorialWeight ρ j.val * ∑ β : DerivativeWord2 j.val, ∑ v, (π v)⁻¹ * ‖(D v).val ⟨j, β⟩‖ ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hsw]
  have hfw : factorialWeight ρ j.val ≤ ρ ^ (2 * j.val) := by
    unfold factorialWeight
    have h1 : (1 : ℝ) ≤ (j.val.factorial : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (j.val.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
      nlinarith
    have h0 : 0 ≤ ρ ^ (2 * j.val) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
    exact div_le_self h0 h1
  have hs0 : 0 ≤ ∑ β : DerivativeWord2 j.val, ∑ v, (π v)⁻¹ * ‖(D v).val ⟨j, β⟩‖ ^ 2 :=
    Finset.sum_nonneg fun β _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (inv_nonneg.2 (hπ v).le) (sq_nonneg _)
  calc _ ≤ ρ ^ (2 * j.val) * ∑ β : DerivativeWord2 j.val, ∑ v, (π v)⁻¹ * ‖(D v).val ⟨j, β⟩‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hfw hs0
    _ = _ := by
        unfold wordDensity
        rw [Finset.mul_sum]

end Densities


section ResidualDensity
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {k : ℕ}

theorem torusJetOrder_fin {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ} (W : TorusHk K F)
    (j : Fin (K + 1)) (β : DerivativeWord2 j.val) (x : Vec 2) :
    torusJetOrder W j.val β x = W.toFunction.jet ⟨j, β⟩ x := by
  simp only [torusJetOrder, Nat.lt_succ_iff.mp j.2, ↓reduceDIte]

theorem enorm_pow_sq (ρ : ℝ) (j : ℕ) : ‖ρ ^ j‖ₑ ^ 2 = ENNReal.ofReal (ρ ^ (2 * j)) := by
  rw [AVRegularity.CycleComparison.Reconstruction.enorm_sq_eq_ofReal_sq, Real.norm_eq_abs, sq_abs,
    ← pow_mul, mul_comm]

theorem rho_pow_two_nonneg (ρ : ℝ) (j : ℕ) : 0 ≤ ρ ^ (2 * j) := by
  rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _

/-- The scaled word has lower integral `ρ^{2j} ‖W_{jβ}‖²` over the cell (value part). -/
theorem lintegral_scaled_word_value {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] (ρ : ℝ) (W : TorusHk k F)
    (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
    ∫⁻ x in AVenhance.unitCube, ‖ρ ^ j.val • torusJetOrder W j.val β x‖ₑ ^ 2 =
      ENNReal.ofReal (ρ ^ (2 * j.val) * ‖W.val ⟨j, β⟩‖ ^ 2) := by
  have h1 : ∀ x, ‖ρ ^ j.val • torusJetOrder W j.val β x‖ₑ ^ 2 =
      ENNReal.ofReal (ρ ^ (2 * j.val)) * ‖W.toFunction.jet ⟨j, β⟩ x‖ₑ ^ 2 := by
    intro x
    rw [torusJetOrder_fin, enorm_smul, mul_pow, enorm_pow_sq]
  rw [lintegral_congr h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_jet_norm_sq_eq_lintegral, ← ENNReal.ofReal_mul (rho_pow_two_nonneg ρ _)]

/-- The scaled word has lower integral `ρ^{2j} ‖W_{jβ}‖²` over the cell (flux part, summed over
the two directions). -/
theorem lintegral_scaled_word_flux {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] (ρ : ℝ)
    (W : TorusHk k (PiLp 2 (fun _ : Fin 2 => F)))
    (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
    ∫⁻ x in AVenhance.unitCube, ∑ i : Fin 2, ‖ρ ^ j.val • (torusJetOrder W j.val β x) i‖ₑ ^ 2 =
      ENNReal.ofReal (ρ ^ (2 * j.val) * ‖W.val ⟨j, β⟩‖ ^ 2) := by
  have h1 : ∀ x, ∑ i : Fin 2, ‖ρ ^ j.val • (torusJetOrder W j.val β x) i‖ₑ ^ 2 =
      ENNReal.ofReal (ρ ^ (2 * j.val)) * ‖W.toFunction.jet ⟨j, β⟩ x‖ₑ ^ 2 := by
    intro x
    simp_rw [enorm_smul, mul_pow, enorm_pow_sq]
    rw [← Finset.mul_sum, AVRegularity.CycleComparison.Reconstruction.sum_enorm_sq_pair, torusJetOrder_fin]
  rw [lintegral_congr h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_jet_norm_sq_eq_lintegral, ← ENNReal.ofReal_mul (rho_pow_two_nonneg ρ _)]

end ResidualDensity

section Integrals
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {k : ℕ}

theorem jetNormSq_continuous {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ} (a : JetIndex2 K) :
    Continuous (fun x : TorusHk K F => ‖x.val a‖ ^ 2) := by
  have h1 : Continuous (fun x : TorusHk K F => x.val) := continuous_subtype_val
  have h2 : Continuous (fun y : JetL2 (volume.restrict AVenhance.unitCube) K F => y a) := by
    exact (continuous_apply a).comp (PiLp.continuous_ofLp 2 _)
  exact (h2.comp h1).norm.pow 2

theorem wordDensity_aemeasurable {μ : Measure ℝ} (ρ : ℝ) (π : ι → ℝ) {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]
    (D : ∀ v, ℝ → TorusHk k (E v)) (hD : ∀ v, AEStronglyMeasurable (D v) μ) (j : Fin (k + 1))
    (β : DerivativeWord2 j.val) :
    AEMeasurable (fun s => wordDensity ρ π (fun v => D v s) j β) μ := by
  unfold wordDensity
  refine AEMeasurable.const_mul ?_ _
  refine Finset.aemeasurable_fun_sum Finset.univ fun v _ => ?_
  refine AEMeasurable.const_mul ?_ _
  exact ((jetNormSq_continuous (F := E v) (⟨j, β⟩ : JetIndex2 k)).comp_aestronglyMeasurable (hD v)).aemeasurable

theorem sum_residual_density_gen (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (j : Fin (k + 1))
    (n : ι → ℝ) (hn : ∀ v, 0 ≤ n v) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ENNReal.ofReal (ρ ^ (2 * j.val) * n v) =
      ENNReal.ofReal (ρ ^ (2 * j.val) * ∑ v, (π v)⁻¹ * n v) := by
  rw [ENNReal.ofReal_mul (rho_pow_two_nonneg ρ _),
    ENNReal.ofReal_sum_of_nonneg (fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le) (hn v)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le), ← ENNReal.ofReal_mul (rho_pow_two_nonneg ρ _)]
  congr 1
  ring

/-- The residual density of the flux, summed over the components. -/
theorem sum_residual_density_flux (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (W : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (j : Fin (k + 1))
    (β : DerivativeWord2 j.val) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ i : Fin 2, ‖ρ ^ j.val • (torusJetOrder (W v) j.val β x) i‖ₑ ^ 2 =
      ENNReal.ofReal (wordDensity ρ π W j β) := by
  simp_rw [lintegral_scaled_word_flux]
  exact sum_residual_density_gen ρ π hπ j (fun v => ‖(W v).val ⟨j, β⟩‖ ^ 2) (fun v => sq_nonneg _)

omit [∀ (i : ι), FiniteDimensional ℝ (h i)] in
/-- The residual density of the value forcing, summed over the components. -/
theorem sum_residual_density_value (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (W : ∀ v, TorusHk k (h v)) (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ ^ j.val • torusJetOrder (W v) j.val β x‖ₑ ^ 2 =
      ENNReal.ofReal (wordDensity ρ π W j β) := by
  simp_rw [lintegral_scaled_word_value]
  exact sum_residual_density_gen ρ π hπ j (fun v => ‖(W v).val ⟨j, β⟩‖ ^ 2) (fun v => sq_nonneg _)

end Integrals

section WordSums

/-- The number of derivative words of order at most `k`. -/
def wordCount (k : ℕ) : ℝ := ∑ j : Fin (k + 1), (2 : ℝ) ^ j.val

theorem wordCount_nonneg (k : ℕ) : 0 ≤ wordCount k :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (by norm_num) _

theorem one_le_wordCount (k : ℕ) : 1 ≤ wordCount k := by
  unfold wordCount
  have h0 : (2 : ℝ) ^ (0 : Fin (k + 1)).val ≤ ∑ j : Fin (k + 1), (2 : ℝ) ^ j.val :=
    Finset.single_le_sum (f := fun j : Fin (k + 1) => (2 : ℝ) ^ j.val)
      (fun _ _ => pow_nonneg (by norm_num) _) (Finset.mem_univ 0)
  simpa using h0

theorem sum_words_const (k : ℕ) (c : ℝ) :
    ∑ j : Fin (k + 1), ∑ _β : DerivativeWord2 j.val, c = wordCount k * c := by
  unfold wordCount
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, Finset.card_univ, AVRegularity.CycleComparison.Coarse.card_derivativeWord2,
    nsmul_eq_mul]
  push_cast
  ring

/-- From `ofReal(√ν)⁻¹ L^{1/2} ≤ X` to `L ≤ ν X²`. -/
theorem lintegral_le_of_inv_sqrt_mul_rpow_le {ν X : ℝ} (hν : 0 < ν) (hX : 0 ≤ X) {L : ℝ≥0∞}
    (h : ENNReal.ofReal (Real.sqrt ν)⁻¹ * L ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal X) :
    L ≤ ENNReal.ofReal (ν * X ^ 2) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have h1 : L ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt ν * X) := by
    have h2 := mul_le_mul_right h (ENNReal.ofReal (Real.sqrt ν))
    rw [← mul_assoc, ← ENNReal.ofReal_mul hs.le, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one,
      one_mul, ← ENNReal.ofReal_mul hs.le] at h2
    exact h2
  have h3 := ENNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hs.le hX) (by norm_num)] at h3
  convert h3 using 2
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow, Real.sq_sqrt hν.le]

end WordSums

section MainIntegrals
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {k : ℕ}

/-- The flux forcing, word by word: the time integral of the mass norm is at most
`W ν X²` when every word has residual `L²` part at most `ν X²`. -/
theorem integral_massNormSq_le_of_words (ρ ν X : ℝ) (a b : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (hν : 0 < ν) (F : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hF : ∀ v, MemLp (F v) 2 (volume.restrict (Set.Icc a b)))
    (hres : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc a b, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ i : Fin 2, ‖ρ ^ j.val • (torusJetOrder (F v t) j.val β x) i‖ₑ ^ 2 ≤
        ENNReal.ofReal (ν * X ^ 2)) :
    ∫ s in Set.Icc a b, massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k)
      ρ π (fun v => (F v s).val) ≤ wordCount k * (ν * X ^ 2) := by
  have hint := AVRegularity.CoupledEnergy.Variational.massNormSq_integrable (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k) ρ π hπ
    (fun v => AVRegularity.CoupledEnergy.Variational.torusJet_memLp k (hF v))
  have hX : 0 ≤ wordCount k * (ν * X ^ 2) := mul_nonneg (wordCount_nonneg k) (mul_nonneg hν.le (sq_nonneg X))
  have hmeas (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
      AEMeasurable (fun s => ENNReal.ofReal (wordDensity ρ π (fun v => F v s) j β))
        (volume.restrict (Set.Icc a b)) :=
    (wordDensity_aemeasurable ρ π F (fun v => (hF v).aestronglyMeasurable) j β).ennreal_ofReal
  have hdens (s : ℝ) (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
      ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ i : Fin 2, ‖ρ ^ j.val • (torusJetOrder (F v s) j.val β x) i‖ₑ ^ 2 =
      ENNReal.ofReal (wordDensity ρ π (fun v => F v s) j β) :=
    sum_residual_density_flux ρ π hπ (fun v => F v s) j β
  have hw (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
      ∫⁻ s in Set.Icc a b, ENNReal.ofReal (wordDensity ρ π (fun v => F v s) j β) ≤
        ENNReal.ofReal (ν * X ^ 2) := by
    refine le_trans (le_of_eq ?_) (hres j β)
    exact lintegral_congr fun s => (hdens s j β).symm
  rw [← ENNReal.ofReal_le_ofReal_iff hX,
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun s => AVRegularity.CoupledEnergy.Variational.massNormSq_nonneg ρ π hπ _)]
  calc ∫⁻ s in Set.Icc a b, ENNReal.ofReal (massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => k)
          ρ π (fun v => (F v s).val))
      ≤ ∫⁻ s in Set.Icc a b, ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
          ENNReal.ofReal (wordDensity ρ π (fun v => F v s) j β) := by
        refine lintegral_mono fun s => ?_
        have hsum : ENNReal.ofReal (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
            wordDensity ρ π (fun v => F v s) j β) = ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
            ENNReal.ofReal (wordDensity ρ π (fun v => F v s) j β) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun β _ =>
            wordDensity_nonneg ρ π hπ _ j β)]
          exact Finset.sum_congr rfl fun j _ =>
            ENNReal.ofReal_sum_of_nonneg (fun β _ => wordDensity_nonneg ρ π hπ _ j β)
        exact (ENNReal.ofReal_le_ofReal (massNormSq_le_sum_wordDensity ρ π hπ _)).trans hsum.le
    _ = ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
          ∫⁻ s in Set.Icc a b, ENNReal.ofReal (wordDensity ρ π (fun v => F v s) j β) := by
        rw [lintegral_finsetSum']
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_finsetSum']
          exact fun β _ => hmeas j β
        · exact fun j _ => Finset.aemeasurable_fun_sum _ fun β _ => hmeas j β
    _ ≤ ∑ j : Fin (k + 1), ∑ _β : DerivativeWord2 j.val, ENNReal.ofReal (ν * X ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun β _ => hw j β
    _ = ENNReal.ofReal (wordCount k * (ν * X ^ 2)) := by
        rw [← sum_words_const, ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg]
          exact fun β _ => mul_nonneg hν.le (sq_nonneg X)
        · exact fun j _ => Finset.sum_nonneg fun β _ => mul_nonneg hν.le (sq_nonneg X)

end MainIntegrals

section MainIntegralsValue
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {k : ℕ}

omit [∀ (i : ι), FiniteDimensional ℝ (h i)] in
/-- The value forcing, word by word: the time integral of the mass norm is at most `W X` when
every word has residual `L¹` part at most `X`. -/
theorem integral_sqrt_massNormSq_le_of_words (ρ X : ℝ) (a b : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (hX : 0 ≤ X) (g : ∀ v, ℝ → TorusHk k (h v))
    (hg : ∀ v, Integrable (g v) (volume.restrict (Set.Icc a b)))
    (hres : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc a b, (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ ^ j.val • torusJetOrder (g v t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal X) :
    ∫ s in Set.Icc a b, Real.sqrt (massNormSq (E := h) (K := fun _ => k)
      ρ π (fun v => (g v s).val)) ≤ wordCount k * X := by
  have hint := AVRegularity.CoupledEnergy.Variational.massNorm_integrable (E := h) (K := fun _ => k) ρ π hπ
    (fun v => AVRegularity.CoupledEnergy.Variational.torusJet_memLp k (memLp_one_iff_integrable.mpr (hg v)))
  have hXW : 0 ≤ wordCount k * X := mul_nonneg (wordCount_nonneg k) hX
  have hmeas (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
      AEMeasurable (fun s => ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => g v s) j β)))
        (volume.restrict (Set.Icc a b)) :=
    ((wordDensity_aemeasurable ρ π g (fun v => (hg v).aestronglyMeasurable) j β).sqrt).ennreal_ofReal
  have hdens (s : ℝ) (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
      (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ ^ j.val • torusJetOrder (g v s) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => g v s) j β)) := by
    rw [sum_residual_density_value ρ π hπ (fun v => g v s) j β,
      ENNReal.ofReal_rpow_of_nonneg (wordDensity_nonneg ρ π hπ _ j β) (by norm_num),
      Real.sqrt_eq_rpow]
  have hw (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
      ∫⁻ s in Set.Icc a b, ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => g v s) j β)) ≤
        ENNReal.ofReal X := by
    refine le_trans (le_of_eq ?_) (hres j β)
    exact lintegral_congr fun s => (hdens s j β).symm
  have hpt (s : ℝ) : Real.sqrt (massNormSq (E := h) (K := fun _ => k) ρ π (fun v => (g v s).val)) ≤
      ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
        Real.sqrt (wordDensity ρ π (fun v => g v s) j β) := by
    have hm := massNormSq_le_sum_wordDensity ρ π hπ (fun v => g v s)
    have hr (j : Fin (k + 1)) (β : DerivativeWord2 j.val) : 0 ≤ Real.sqrt (wordDensity ρ π (fun v => g v s) j β) :=
      Real.sqrt_nonneg _
    have hsq : ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val, wordDensity ρ π (fun v => g v s) j β ≤
        (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
          Real.sqrt (wordDensity ρ π (fun v => g v s) j β)) ^ 2 := by
      calc _ = ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
              Real.sqrt (wordDensity ρ π (fun v => g v s) j β) ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun β _ => ?_
            rw [Real.sq_sqrt (wordDensity_nonneg ρ π hπ _ j β)]
        _ ≤ ∑ j : Fin (k + 1), (∑ β : DerivativeWord2 j.val,
              Real.sqrt (wordDensity ρ π (fun v => g v s) j β)) ^ 2 :=
            Finset.sum_le_sum fun j _ => Finset.sum_sq_le_sq_sum_of_nonneg fun β _ => hr j β
        _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => Finset.sum_nonneg fun β _ => hr j β
    refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun β _ => hr j β, ?_⟩
    exact hm.trans hsq
  rw [← ENNReal.ofReal_le_ofReal_iff hXW,
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun s => Real.sqrt_nonneg _)]
  calc ∫⁻ s in Set.Icc a b, ENNReal.ofReal (Real.sqrt (massNormSq (E := h) (K := fun _ => k)
          ρ π (fun v => (g v s).val)))
      ≤ ∫⁻ s in Set.Icc a b, ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
          ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => g v s) j β)) := by
        refine lintegral_mono fun s => ?_
        have hsum : ENNReal.ofReal (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
            Real.sqrt (wordDensity ρ π (fun v => g v s) j β)) = ∑ j : Fin (k + 1),
            ∑ β : DerivativeWord2 j.val,
            ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => g v s) j β)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun β _ => Real.sqrt_nonneg _)]
          exact Finset.sum_congr rfl fun j _ =>
            ENNReal.ofReal_sum_of_nonneg (fun β _ => Real.sqrt_nonneg _)
        exact (ENNReal.ofReal_le_ofReal (hpt s)).trans hsum.le
    _ = ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
          ∫⁻ s in Set.Icc a b, ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => g v s) j β)) := by
        rw [lintegral_finsetSum']
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_finsetSum']
          exact fun β _ => hmeas j β
        · exact fun j _ => Finset.aemeasurable_fun_sum _ fun β _ => hmeas j β
    _ ≤ ∑ j : Fin (k + 1), ∑ _β : DerivativeWord2 j.val, ENNReal.ofReal X :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun β _ => hw j β
    _ = ENNReal.ofReal (wordCount k * X) := by
        rw [← sum_words_const, ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg]
          exact fun β _ => hX
        · exact fun j _ => Finset.sum_nonneg fun β _ => hX

end MainIntegralsValue

end AVRegularity.EntryTerminal.ForcedEnergy

namespace AVRegularity.KernelEnergy.TorusKernelOperator
open AVRegularity.EntryTerminal.ForcedEnergy
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

/-- The arithmetic of the forced estimate: with `W ≥ 1` the number of words. -/
theorem forced_arith {E0 FF GG W X ν : ℝ} (hE0 : 0 ≤ E0) (hGG : 0 ≤ GG) (hW : 1 ≤ W) (hX : 0 ≤ X)
    (hν : 0 < ν) (hFF : FF ≤ W * (ν * X ^ 2)) (hG : GG ≤ W * X) :
    Real.sqrt (8 * E0 + (24 / ν) * FF + 28 * GG ^ 2) ≤ (3 + 8 * W) * (Real.sqrt E0 + X) := by
  have hs := Real.sq_sqrt hE0
  have hs0 := Real.sqrt_nonneg E0
  have hF1 : (24 / ν) * FF ≤ 24 * W * X ^ 2 := by
    calc (24 / ν) * FF ≤ (24 / ν) * (W * (ν * X ^ 2)) :=
          mul_le_mul_of_nonneg_left hFF (by positivity)
      _ = 24 * W * X ^ 2 := by field_simp
  have hG2 : GG ^ 2 ≤ (W * X) ^ 2 := pow_le_pow_left₀ hGG hG 2
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hc : (3 + 8 * W) ^ 2 ≥ 9 := by nlinarith
  have hX2 := sq_nonneg X
  have hWX : 0 ≤ W * X := by positivity
  nlinarith [mul_nonneg hs0 hX, mul_nonneg (sub_nonneg.2 hc) hE0, mul_nonneg (sq_nonneg (3 + 8 * W)) hX2,
    mul_nonneg (by linarith : (0 : ℝ) ≤ W) hX2, mul_nonneg (mul_self_nonneg W) hX2]

include P in
/-- **Forced strong energy from word-wise residual norms**. -/
theorem kernelForcedWeakSolution_strongEnergy_of_words (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (X : ℝ) (hX : 0 ≤ X)
    (hFw : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc a b, ∑ i, ENNReal.ofReal (P.π i)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ r : Fin 2, ‖ρ ^ j.val • (torusJetOrder (F i t) j.val β x) r‖ₑ ^ 2 ≤
        ENNReal.ofReal (ν * X ^ 2))
    (hgw : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc a b, (∑ i, ENNReal.ofReal (P.π i)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ ^ j.val • torusJetOrder (g i t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal X)
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w) :
    AVRegularity.strongEnergy ρ ν P.π a b u w ≤
      ENNReal.ofReal ((3 + 8 * wordCount k) *
        (Real.sqrt (massNormSq ρ P.π (fun i => (f i).val)) + X)) := by
  have hν := P.diffusivity_pos
  have h1 := P.kernelForcedWeakSolution_forced_strongEnergy v hv hvp F g αv B lam hα hB hlam hsmall
    hstrain hd hjets hv_meas V hV hvb T hT w u f hF hg hsol
  have hFF := integral_massNormSq_le_of_words ρ ν X a b P.π P.hπ hν F hF hFw
  have hGG := integral_sqrt_massNormSq_le_of_words ρ X a b P.π P.hπ hX g hg hgw
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  exact forced_arith (massNormSq_nonneg ρ P.π P.hπ _)
    (integral_nonneg fun s => Real.sqrt_nonneg _) (one_le_wordCount k) hX hν hFF hGG

end AVRegularity.KernelEnergy.TorusKernelOperator
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.EntryTerminal.ForcedEnergy

/-! Integrability of the forcing from its word densities, and monotonicity of the word densities in
the radius. The residual bound of the statement is at the radius `r_*`; the
estimate is run at a smaller radius, where every density is smaller. -/

section Mono
variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)] {k : ℕ}

theorem wordDensity_mono (ρ ρ' : ℝ) (hρ : 0 ≤ ρ) (hρρ' : ρ ≤ ρ') (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (D : ∀ v, TorusHk k (E v)) (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
    wordDensity ρ π D j β ≤ wordDensity ρ' π D j β := by
  unfold wordDensity
  have hs : 0 ≤ ∑ v, (π v)⁻¹ * ‖(D v).val ⟨j, β⟩‖ ^ 2 :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le) (sq_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ hs
  rw [pow_mul, pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ hρ hρρ' 2) _

theorem norm_sq_le_sum_wordDensity (ρ : ℝ) (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (D : ∀ v, TorusHk k (E v)) (v : ι) :
    ‖D v‖ ^ 2 ≤ (π v / factorialWeightMin ρ k) *
      ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val, wordDensity ρ π D j β := by
  have hmin := factorialWeightMin_pos ρ hρ (K := k)
  have h1 : factorialWeightMin ρ k * ‖D v‖ ^ 2 ≤ factorialNormSq ρ (D v).val :=
    factorialNormSq_lower ρ (D v).val
  have h2 := AVRegularity.CoupledEnergy.Variational.componentFactorial_le_mass (E := E)
    (K := fun _ => k) ρ π hπ (fun v => (D v).val) v
  have h3 := massNormSq_le_sum_wordDensity ρ π hπ D
  rw [div_mul_eq_mul_div, le_div_iff₀ hmin]
  calc ‖D v‖ ^ 2 * factorialWeightMin ρ k = factorialWeightMin ρ k * ‖D v‖ ^ 2 := by ring
    _ ≤ π v * massNormSq (E := E) (K := fun _ => k) ρ π (fun v => (D v).val) := h1.trans h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (hπ v).le

end Mono

section Integ
variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)] {k : ℕ}

theorem lintegral_ofReal_sum_wordDensity_le {μ : Measure ℝ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (D : ∀ v, ℝ → TorusHk k (E v)) (hD : ∀ v, AEStronglyMeasurable (D v) μ) (Y : ℝ)
    (hY : 0 ≤ Y)
    (hwd : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t, ENNReal.ofReal (wordDensity ρ π (fun v => D v t) j β) ∂μ ≤ ENNReal.ofReal Y) :
    ∫⁻ t, ENNReal.ofReal (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
      wordDensity ρ π (fun v => D v t) j β) ∂μ ≤ ENNReal.ofReal (wordCount k * Y) := by
  have hmeas (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
      AEMeasurable (fun s => ENNReal.ofReal (wordDensity ρ π (fun v => D v s) j β)) μ :=
    (wordDensity_aemeasurable ρ π D hD j β).ennreal_ofReal
  have hsum (t : ℝ) : ENNReal.ofReal (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
      wordDensity ρ π (fun v => D v t) j β) = ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
      ENNReal.ofReal (wordDensity ρ π (fun v => D v t) j β) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun β _ =>
      wordDensity_nonneg ρ π hπ _ j β)]
    exact Finset.sum_congr rfl fun j _ =>
      ENNReal.ofReal_sum_of_nonneg (fun β _ => wordDensity_nonneg ρ π hπ _ j β)
  simp_rw [hsum]
  calc _ = ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
          ∫⁻ s, ENNReal.ofReal (wordDensity ρ π (fun v => D v s) j β) ∂μ := by
        rw [lintegral_finsetSum']
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_finsetSum']
          exact fun β _ => hmeas j β
        · exact fun j _ => Finset.aemeasurable_fun_sum _ fun β _ => hmeas j β
    _ ≤ ∑ j : Fin (k + 1), ∑ _β : DerivativeWord2 j.val, ENNReal.ofReal Y :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun β _ => hwd j β
    _ = ENNReal.ofReal (wordCount k * Y) := by
        rw [← sum_words_const, ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg]
          exact fun β _ => hY
        · exact fun j _ => Finset.sum_nonneg fun β _ => hY

theorem lintegral_ofReal_sum_sqrt_wordDensity_le {μ : Measure ℝ} (ρ : ℝ) (π : ι → ℝ)
    (_hπ : ∀ v, 0 < π v)
    (D : ∀ v, ℝ → TorusHk k (E v)) (hD : ∀ v, AEStronglyMeasurable (D v) μ) (Y : ℝ)
    (hY : 0 ≤ Y)
    (hwd : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t, ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => D v t) j β)) ∂μ ≤
        ENNReal.ofReal Y) :
    ∫⁻ t, ENNReal.ofReal (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
      Real.sqrt (wordDensity ρ π (fun v => D v t) j β)) ∂μ ≤ ENNReal.ofReal (wordCount k * Y) := by
  have hmeas (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
      AEMeasurable (fun s => ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => D v s) j β))) μ :=
    ((wordDensity_aemeasurable ρ π D hD j β).sqrt).ennreal_ofReal
  have hsum (t : ℝ) : ENNReal.ofReal (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
      Real.sqrt (wordDensity ρ π (fun v => D v t) j β)) = ∑ j : Fin (k + 1),
      ∑ β : DerivativeWord2 j.val, ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => D v t) j β)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun β _ => Real.sqrt_nonneg _)]
    exact Finset.sum_congr rfl fun j _ =>
      ENNReal.ofReal_sum_of_nonneg (fun β _ => Real.sqrt_nonneg _)
  simp_rw [hsum]
  calc _ = ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
          ∫⁻ s, ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => D v s) j β)) ∂μ := by
        rw [lintegral_finsetSum']
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_finsetSum']
          exact fun β _ => hmeas j β
        · exact fun j _ => Finset.aemeasurable_fun_sum _ fun β _ => hmeas j β
    _ ≤ ∑ j : Fin (k + 1), ∑ _β : DerivativeWord2 j.val, ENNReal.ofReal Y :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun β _ => hwd j β
    _ = ENNReal.ofReal (wordCount k * Y) := by
        rw [← sum_words_const, ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg]
          exact fun β _ => hY
        · exact fun j _ => Finset.sum_nonneg fun β _ => hY

/-- Square integrability of the forcing from the integrals of its word densities. -/
theorem memLp_two_of_wordDensity {μ : Measure ℝ} (ρ : ℝ) (hρ : 0 < ρ) (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v)
    (D : ∀ v, ℝ → TorusHk k (E v)) (hD : ∀ v, AEStronglyMeasurable (D v) μ) (Y : ℝ)
    (hY : 0 ≤ Y)
    (hwd : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t, ENNReal.ofReal (wordDensity ρ π (fun v => D v t) j β) ∂μ ≤ ENNReal.ofReal Y)
    (v : ι) : MemLp (D v) 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm (hD v)]
  refine ⟨((hD v).norm.pow 2 : AEStronglyMeasurable _ μ), ?_⟩
  set c := π v / factorialWeightMin ρ k with hc
  have hc0 : 0 ≤ c := div_nonneg (hπ v).le (factorialWeightMin_pos ρ hρ).le
  have h1 := lintegral_ofReal_sum_wordDensity_le ρ π hπ D hD Y hY hwd
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t => sq_nonneg _)]
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := c))
    (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top))
  calc _ ≤ ∫⁻ t, ENNReal.ofReal c * ENNReal.ofReal (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
          wordDensity ρ π (fun v => D v t) j β) ∂μ := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul hc0]
        exact ENNReal.ofReal_le_ofReal (norm_sq_le_sum_wordDensity ρ hρ π hπ (fun v => D v t) v)
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Integrability of the forcing from the integrals of the square roots of its word densities. -/
theorem integrable_of_sqrt_wordDensity {μ : Measure ℝ} (ρ : ℝ) (hρ : 0 < ρ) (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v)
    (D : ∀ v, ℝ → TorusHk k (E v)) (hD : ∀ v, AEStronglyMeasurable (D v) μ) (Y : ℝ)
    (hY : 0 ≤ Y)
    (hwd : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t, ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => D v t) j β)) ∂μ ≤
        ENNReal.ofReal Y)
    (v : ι) : Integrable (D v) μ := by
  refine ⟨hD v, ?_⟩
  set c := Real.sqrt (π v / factorialWeightMin ρ k) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have h1 := lintegral_ofReal_sum_sqrt_wordDensity_le ρ π hπ D hD Y hY hwd
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := c))
    (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top))
  calc _ ≤ ∫⁻ t, ENNReal.ofReal c * ENNReal.ofReal (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
          Real.sqrt (wordDensity ρ π (fun v => D v t) j β)) ∂μ := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul hc0]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 := norm_sq_le_sum_wordDensity ρ hρ π hπ (fun v => D v t) v
        have h3 : Real.sqrt (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
            wordDensity ρ π (fun v => D v t) j β) ≤ ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
            Real.sqrt (wordDensity ρ π (fun v => D v t) j β) := by
          have hr (j : Fin (k + 1)) (β : DerivativeWord2 j.val) :
              0 ≤ Real.sqrt (wordDensity ρ π (fun v => D v t) j β) := Real.sqrt_nonneg _
          refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun β _ => hr j β, ?_⟩
          calc _ = ∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
                  Real.sqrt (wordDensity ρ π (fun v => D v t) j β) ^ 2 := by
                refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun β _ => ?_
                rw [Real.sq_sqrt (wordDensity_nonneg ρ π hπ _ j β)]
            _ ≤ ∑ j : Fin (k + 1), (∑ β : DerivativeWord2 j.val,
                  Real.sqrt (wordDensity ρ π (fun v => D v t) j β)) ^ 2 :=
                Finset.sum_le_sum fun j _ => Finset.sum_sq_le_sq_sum_of_nonneg fun β _ => hr j β
            _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => Finset.sum_nonneg fun β _ => hr j β
        have h4 : ‖D v t‖ ≤ c * Real.sqrt (∑ j : Fin (k + 1), ∑ β : DerivativeWord2 j.val,
            wordDensity ρ π (fun v => D v t) j β) := by
          rw [hc, ← Real.sqrt_mul (div_nonneg (hπ v).le (factorialWeightMin_pos ρ hρ).le)]
          exact Real.le_sqrt_of_sq_le h2
        exact h4.trans (mul_le_mul_of_nonneg_left h3 hc0)
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Integ

end AVRegularity.EntryTerminal.ForcedEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryTerminal.ForcedEnergy

/-! The kernel operator of a stage with a nonnegative producer reserve at an arbitrary radius
`ρ ≤ ε_{i-1}`. Compared with `nativeInvariantKernelOperator` the cascade
hypotheses are replaced by the single premise `0 ≤ compReserve k v.1`, the radius is free and the
Schur bound at the radius `ρ` is a hypothesis. -/

open AVRegularity.Construction.Preservation.Buffer KernelEnergy
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

def reserveKernelOperator
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts)
    (a b S θ : ℝ) (G : GenStage D hr Dm bw j₀)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k a b S θ G)
    (hres : ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1))
    (hab : a ≤ b) (hν : 0 < D.kap G.level)
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ D.eps (G.level - 1)) (hD : 2 ≤ Dm)
    (hθ : θ ≤ 1 / 8) (n : ℕ) (hn : n ≤ k.Ks)
    (hsch : SchurBound θ (kernelSchurMatrix (ι := CompIn G.comps) (h := fun v => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) (D.kap G.level) ρ
      (fun v => G.mass law v / (fun _ => (1 : ℝ)) v ^ 2) n Dm a b k.cker
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1))) :
    TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root)
      a b ρ (D.kap G.level) n Dm := by
  rcases hI with ⟨hnat, _htags, _hgen, hshift, hpar, hcert, henv, _hledger,
    hkernel, _hschur, _hquiet⟩
  have hs := (henv (fun _ => n) (fun _ => hn)).1.molecular.1
  refine {
    htime := hab
    radius_pos := hρ
    diffusivity_pos := hν
    order_ge_two := hD
    π := fun v => G.mass law v / (fun _ => (1 : ℝ)) v ^ 2
    hπ := fun v => div_pos (birth_compMass_pos hq hΛ law v.1) (pow_pos zero_lt_one 2)
    B := fun v u γ d => G.physCoeff v u γ d.1
    hB_meas := ?_
    hB_smooth := ?_
    hB_per := ?_
    hB_fin := ?_
    C := fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root)
    S := G.sysS P seedK freshK φ₀ hφ₀
    c := k.cker
    r := fun v u γ => (G.kernelOf P seedK freshK v u γ).width
    hr := ?_
    hS := fun v u γ => (hkernel v u γ).2.2.2.2 _ hρ n hn
    θ := θ
    hθ := hθ
    hschur := hsch }
  · intro v u γ d
    exact native_physCoeff_joint_measurable hnat hcert (by omega) hi hj a b k.mEnv
      (fun _ => n + k.Jm) hs v u γ d.1
  · intro v u γ d t ht
    exact (native_physCoeff_spatial_smooth hnat hi hj a b k.mEnv hε.ne'
      (fun _ => n + k.Jm) hs v u γ d.1 t ht).of_le (by exact_mod_cast Nat.le_add_right n k.Jm)
  · intro v u γ d t _
    exact native_physCoeff_periodic hnat hshift v u γ d.1 t
  · intro v u γ d
    exact native_physCoeff_coefficientSeminorm_finite hcert hpar hnat hi hj hb hε
      a b k.mEnv (fun _ => n + k.Jm) hs v u γ
      (hres v)
      ((compReserve_le_one k v.1).trans (by norm_num))
      _ hρ hρε n d.1 (Nat.le_add_right n k.Jm)
  · intro v u γ
    rw [(hkernel v u γ).2.1]
    exact (G.fam.identity v u γ).record.width_pos

theorem reserveKernelOperator_data
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts)
    (a b S θ : ℝ) (G : GenStage D hr Dm bw j₀)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k a b S θ G)
    (hres : ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < bw) (hε : 0 < D.eps (G.level - 1))
    (hab : a ≤ b) (hν : 0 < D.kap G.level)
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ D.eps (G.level - 1)) (hD : 2 ≤ Dm)
    (hθ : θ ≤ 1 / 8) (n : ℕ) (hn : n ≤ k.Ks) (hsch) :
    let R := reserveKernelOperator law P seedK freshK φ₀ hφ₀ M k a b S θ G hI hres hq hΛ hi hj hb hε
      hab hν ρ hρ hρε hD hθ n hn hsch
    R.π = G.mass law ∧
    R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1) ∧
    R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) => ContinuousLinearMap.id ℝ (hr u.1.root)) ∧
    R.S = G.sysS P seedK freshK φ₀ hφ₀ := by
  refine ⟨?_, rfl, rfl, rfl⟩
  funext v
  simp [reserveKernelOperator]

end AVRegularity.EntryTerminal.ForcedEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryTerminal.ForcedEnergy

/-! The forced strong energy of a native stage solution: the regularized system
with forcing `(F, g)` is the forced coupled weak solution of its kernel operator, and the
component estimate of Part 1 applies. -/

open AVRegularity.Construction.Preservation
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_forced_weak (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν k Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (F : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (g : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f F g U W Y) :
    IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => k)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (fun v t => F v t + R.carrierFlux W v t) g U W := by
  have hs : IsKernelWeakSolutionTorus ν a b (streamVel φ) k Dm R.B R.C R.S f F g U W Y := by
    simpa only [hB, hC, hS, GenStage.IsRegSolution] using hsol
  obtain ⟨hv, _hp, _hd, ⟨V, hV⟩, _hm⟩ := Buffer.stream_kernel_drift_data hφ a b
  exact R.kernelWeakSolution_forcedWeakSolution (streamVel φ) hv (max V 0)
    (le_max_right _ _) (fun t ht x => (hV t ht x).trans (le_max_left _ _))
    f F g U W Y hs

theorem native_reg_solution_forced_strongEnergy (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν k Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (F : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (g : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f F g U W Y)
    (hFm : ∀ v, MemLp (F v) 2 (volume.restrict (Set.Icc a b)))
    (hgm : ∀ v, Integrable (g v) (volume.restrict (Set.Icc a b)))
    (X : ℝ) (hX : 0 ≤ X)
    (hFw : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc a b, ∑ i, ENNReal.ofReal (R.π i)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ r : Fin 2, ‖ρ ^ j.val • (torusJetOrder (F i t) j.val β x) r‖ₑ ^ 2 ≤
        ENNReal.ofReal (ν * X ^ 2))
    (hgw : ∀ j : Fin (k + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc a b, (∑ i, ENNReal.ofReal (R.π i)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ ^ j.val • torusJetOrder (g i t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal X) :
    AVRegularity.strongEnergy ρ ν R.π a b U W ≤
      ENNReal.ofReal ((3 + 8 * wordCount k) *
        (Real.sqrt (massNormSq ρ R.π (fun i => (f i).val)) + X)) := by
  have hforced := native_reg_solution_forced_weak P seedK freshK φ₀ hφ₀ G R hB hC hS hφ
    f F g U W Y hsol
  obtain ⟨hv, hp, hd, ⟨V, hV⟩, hm⟩ := Buffer.stream_kernel_drift_data hφ a b
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hbV : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ max V 0 :=
    fun t ht x => (hV t ht x).trans (le_max_left _ _)
  exact R.kernelForcedWeakSolution_strongEnergy_of_words (streamVel φ) hv hp F g α B lam hα hBdrift
    hlam hsmall hstrain hd hjets hm (max V 0) hV0 hbV
    (fun _ => driftCarrierBudget k (max V 0) α B lam)
    (fun t ht _ => driftCarrierBudget_bounds k (streamVel φ t) (max V 0) α B lam hV0
      (hbV t ht) (hjets t ht)) W U f hFm hgm X hX hFw hgw hforced

end AVRegularity.EntryTerminal.ForcedEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.EntryTerminal.ForcedEnergy

/-! **The forced strong energy of a stage with a nonnegative reserve**. The
stage invariant gives the kernel operator at the radius `R = ρ_⋆`; the Schur bound passes to every
smaller radius `ρ`; the forced estimate of Part 1 is run at `ρ`, with the residual bounds that hold
at `R` (every word density is monotone in the radius). -/

open AVRegularity.Construction.Preservation AVRegularity.Construction.Preservation.Buffer
  KernelEnergy

section Shapes
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {k : ℕ}

theorem flux_shape_le (I : Set ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (ρ ρ' : ℝ) (hρ : 0 ≤ ρ)
    (hρρ' : ρ ≤ ρ') (F : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (Y : ℝ≥0∞) (j : Fin (k + 1)) (β : DerivativeWord2 j.val)
    (H : ∫⁻ t in I, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ r : Fin 2, ‖ρ' ^ j.val • (torusJetOrder (F v t) j.val β x) r‖ₑ ^ 2 ≤ Y) :
    ∫⁻ t in I, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ r : Fin 2, ‖ρ ^ j.val • (torusJetOrder (F v t) j.val β x) r‖ₑ ^ 2 ≤ Y := by
  refine le_trans (lintegral_mono fun t => ?_) H
  rw [sum_residual_density_flux ρ π hπ (fun v => F v t) j β,
    sum_residual_density_flux ρ' π hπ (fun v => F v t) j β]
  exact ENNReal.ofReal_le_ofReal (wordDensity_mono ρ ρ' hρ hρρ' π hπ _ j β)

omit [∀ (i : ι), FiniteDimensional ℝ (h i)] in
theorem value_shape_le (I : Set ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (ρ ρ' : ℝ) (hρ : 0 ≤ ρ)
    (hρρ' : ρ ≤ ρ') (g : ∀ v, ℝ → TorusHk k (h v))
    (Y : ℝ≥0∞) (j : Fin (k + 1)) (β : DerivativeWord2 j.val)
    (H : ∫⁻ t in I, (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ' ^ j.val • torusJetOrder (g v t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ Y) :
    ∫⁻ t in I, (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ ^ j.val • torusJetOrder (g v t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ Y := by
  refine le_trans (lintegral_mono fun t => ?_) H
  rw [sum_residual_density_value ρ π hπ (fun v => g v t) j β,
    sum_residual_density_value ρ' π hπ (fun v => g v t) j β,
    ENNReal.ofReal_rpow_of_nonneg (wordDensity_nonneg ρ π hπ _ j β) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (wordDensity_nonneg ρ' π hπ _ j β) (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (wordDensity_nonneg ρ π hπ _ j β)
    (wordDensity_mono ρ ρ' hρ hρρ' π hπ _ j β) (by norm_num))

theorem wd_of_flux_shape (I : Set ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (ρ : ℝ)
    (F : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (Y : ℝ≥0∞) (j : Fin (k + 1))
    (β : DerivativeWord2 j.val)
    (H : ∫⁻ t in I, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ r : Fin 2, ‖ρ ^ j.val • (torusJetOrder (F v t) j.val β x) r‖ₑ ^ 2 ≤ Y) :
    ∫⁻ t in I, ENNReal.ofReal (wordDensity ρ π (fun v => F v t) j β) ≤ Y := by
  refine le_trans (le_of_eq (lintegral_congr fun t => ?_)) H
  rw [sum_residual_density_flux ρ π hπ (fun v => F v t) j β]

omit [∀ (i : ι), FiniteDimensional ℝ (h i)] in
theorem sqrt_wd_of_value_shape (I : Set ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (ρ : ℝ)
    (g : ∀ v, ℝ → TorusHk k (h v)) (Y : ℝ≥0∞) (j : Fin (k + 1)) (β : DerivativeWord2 j.val)
    (H : ∫⁻ t in I, (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖ρ ^ j.val • torusJetOrder (g v t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ Y) :
    ∫⁻ t in I, ENNReal.ofReal (Real.sqrt (wordDensity ρ π (fun v => g v t) j β)) ≤ Y := by
  refine le_trans (le_of_eq (lintegral_congr fun t => ?_)) H
  rw [sum_residual_density_value ρ π hπ (fun v => g v t) j β,
    ENNReal.ofReal_rpow_of_nonneg (wordDensity_nonneg ρ π hπ _ j β) (by norm_num),
    Real.sqrt_eq_rpow]

end Shapes

section SchurMono
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)]

omit [Fintype ι] in
/-- The kernel Schur matrix decreases with the radius. -/
theorem kernelSchurMatrix_radius_mono (ν ρ R : ℝ) (hν : 0 < ν) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (π : ι → ℝ) (k D : ℕ) (t₀ t₁ : ℝ) (c : ℕ → ℝ) (r : ∀ i j, Γ i j → ℝ)
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hc : ∀ i j (_α : Γ i j) (d : ↥(Finset.Icc 2 D)), 0 ≤ c (d.1 - 2))
    (hr : ∀ i j (α : Γ i j), 0 < r i j α)
    (hfin : ∀ i j α d, coefficientSeminorm R k t₀ t₁ (B i j α d) ≠ ⊤) (i j : ι) :
    kernelSchurMatrix ν ρ π k D t₀ t₁ c r C B i j ≤ kernelSchurMatrix ν R π k D t₀ t₁ c r C B i j := by
  unfold kernelSchurMatrix
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine Finset.sum_le_sum fun α _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine Finset.sum_le_sum fun d _ => ?_
  have hden : 0 < ν * r i j α ^ (d.1 - 2) := mul_pos hν (pow_pos (hr i j α) _)
  refine div_le_div_of_nonneg_right ?_ hden.le
  refine mul_le_mul_of_nonneg_right ?_ (hc i j α d)
  exact ENNReal.toReal_mono (hfin i j α d)
    (AVRegularity.CycleJointProofs.coefficientSeminorm_radius_mono ρ R hρ hρR k t₀ t₁ _)

end SchurMono

section Stage
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem stage_forced_energy (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (k : InvConsts)
    (tA tB S θ : ℝ) (G : GenStage D hr Dm bw j₀)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k tA tB S θ G)
    (hres : ∀ v : CompIn G.comps, 0 ≤ compReserve k v.1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (hab : tA ≤ tB) (hν : 0 < D.kap G.level)
    (R : ℝ) (hR : 0 < R) (hRε : R ≤ D.eps (G.level - 1)) (hRrho : R = rhoStar D k.c₀ G.level)
    (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R) (hD : 2 ≤ Dm) (hθ : θ ≤ 1 / 8) (n : ℕ) (hn : n ≤ k.Ks)
    (t0 : ℝ) (ht0A : tA ≤ t0) (ht0B : t0 ≤ tB)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (αd lam : ℝ) (hα : 0 ≤ αd) (hlam : 0 < lam)
    (hsmall : 1024 * ρ / lam ≤ 1 / 2) (hstrain : αd * 1024 * ρ ^ 2 ≤ D.kap G.level / 8)
    (hjets : ∀ t ∈ Set.Icc t0 tB, ∀ l, 1 ≤ l → l ≤ n → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        αd * 1024 ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ v : CompIn G.comps, TorusHk n (hr v.1.root))
    (F : ∀ v : CompIn G.comps, ℝ → TorusHk n (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))
    (g : ∀ v : CompIn G.comps, ℝ → TorusHk n (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk n (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (n + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (n + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.kap G.level) (streamVel φ) n t0 tB f F g U W Y)
    (hFm : ∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc t0 tB)))
    (hgm : ∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc t0 tB)))
    (X : ℝ) (hX : 0 ≤ X)
    (hFw : ∀ j : Fin (n + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc t0 tB, ∑ v, ENNReal.ofReal (G.mass law v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ r : Fin 2, ‖R ^ j.val • (torusJetOrder (F v t) j.val β x) r‖ₑ ^ 2 ≤
        ENNReal.ofReal (D.kap G.level * X ^ 2))
    (hgw : ∀ j : Fin (n + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in Set.Icc t0 tB, (∑ v, ENNReal.ofReal (G.mass law v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖R ^ j.val • torusJetOrder (g v t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal X) :
    AVRegularity.strongEnergy ρ (D.kap G.level) (G.mass law) t0 tB U W ≤
      ENNReal.ofReal ((3 + 8 * wordCount n) *
        (Real.sqrt (massNormSq ρ (G.mass law) (fun v => (f v).val)) + X)) := by
  have hmass : ∀ v : CompIn G.comps, 0 < G.mass law v := fun v => birth_compMass_pos hq hΛ law v.1
  have hI' := hI
  rcases hI' with ⟨_, _, _, _, _, _, _, _, hkernel, hschur, _⟩
  have hschR := hschur n hn (fun _ => 1) (Or.inl rfl)
  rw [← hRrho] at hschR
  let R0 := reserveKernelOperator law P seedK freshK φ₀ hφ₀ M k tA tB S θ G hI hres hq hΛ hi hj hb hε
    hab hν R hR hRε hD hθ n hn hschR
  have hfin : ∀ v u (γ : G.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)),
      coefficientSeminorm R n tA tB (G.physCoeff v u γ d.1) ≠ ⊤ := fun v u γ d => R0.hB_fin v u γ d
  have hc : ∀ v u (γ : G.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)), 0 ≤ k.cker (d.1 - 2) := by
    intro v u γ d
    have hd := Finset.mem_Icc.1 d.2
    exact ((hkernel v u γ).2.2.2.2 R hR n hn).2.2.1 (d.1 - 2) (by omega)
  have hrpos : ∀ v u (γ : G.fam.Γ v u), 0 < (G.kernelOf P seedK freshK v u γ).width := by
    intro v u γ
    rw [((hkernel v u γ).2.1)]
    exact (G.fam.identity v u γ).record.width_pos
  have hschρ : SchurBound θ (kernelSchurMatrix (ι := CompIn G.comps) (h := fun v => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) (D.kap G.level) ρ
      (fun v => G.mass law v / (fun _ => (1 : ℝ)) v ^ 2) n Dm tA tB k.cker
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1)) := by
    have hmono := kernelSchurMatrix_radius_mono (ι := CompIn G.comps) (h := fun v => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) (D.kap G.level) ρ R hν hρ.le hρR
      (fun v => G.mass law v / (fun _ => (1 : ℝ)) v ^ 2) n Dm tA tB k.cker
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1) (fun i j α d => hc i j α d) hrpos hfin
    exact ⟨fun i => (Finset.sum_le_sum fun j _ => hmono i j).trans (hschR.1 i),
      fun j => (Finset.sum_le_sum fun i _ => hmono i j).trans (hschR.2 j)⟩
  have hρε : ρ ≤ D.eps (G.level - 1) := hρR.trans hRε
  let R1 := reserveKernelOperator law P seedK freshK φ₀ hφ₀ M k tA tB S θ G hI hres hq hΛ hi hj hb hε
    hab hν ρ hρ hρε hD hθ n hn hschρ
  have hdata := reserveKernelOperator_data law P seedK freshK φ₀ hφ₀ M k tA tB S θ G hI hres hq hΛ hi
    hj hb hε hab hν ρ hρ hρε hD hθ n hn hschρ
  let R2 := kernelOperator_time_restrict R1 (Set.Icc_subset_Icc ht0A le_rfl) ht0B
  have hπ2 : R2.π = G.mass law := hdata.1
  have hB2 : R2.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)) =>
      G.physCoeff v u γ d.1) := rfl
  have hC2 : R2.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)) := rfl
  have hS2 : R2.S = G.sysS P seedK freshK φ₀ hφ₀ := rfl
  have hFρ := fun j β => flux_shape_le (Set.Icc t0 tB) (G.mass law) hmass ρ R hρ.le hρR F
    (ENNReal.ofReal (D.kap G.level * X ^ 2)) j β (hFw j β)
  have hgρ := fun j β => value_shape_le (Set.Icc t0 tB) (G.mass law) hmass ρ R hρ.le hρR g
    (ENNReal.ofReal X) j β (hgw j β)
  have hY : 0 ≤ D.kap G.level * X ^ 2 := mul_nonneg hν.le (sq_nonneg X)
  have hFmem := memLp_two_of_wordDensity (μ := volume.restrict (Set.Icc t0 tB)) ρ hρ (G.mass law) hmass
    F hFm _ hY (fun j β => wd_of_flux_shape _ (G.mass law) hmass ρ F _ j β (hFρ j β))
  have hgint := integrable_of_sqrt_wordDensity (μ := volume.restrict (Set.Icc t0 tB)) ρ hρ (G.mass law)
    hmass g hgm X hX (fun j β => sqrt_wd_of_value_shape _ (G.mass law) hmass ρ g _ j β (hgρ j β))
  have hmain := native_reg_solution_forced_strongEnergy P seedK freshK φ₀ hφ₀ G R2 hB2 hC2 hS2 hφ
    αd 1024 lam hα (by norm_num) hlam hsmall hstrain hjets f F g U W Y hsol hFmem hgint X hX
    (by simp only [hπ2]; exact hFρ) (by simp only [hπ2]; exact hgρ)
  simpa only [hπ2] using hmain

end Stage

end AVRegularity.EntryTerminal.ForcedEnergy
end
end
