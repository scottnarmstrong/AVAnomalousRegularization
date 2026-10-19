-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.WeakMass
public import AVRegularity.CycleComparison.Lift.FourierParameterJetContinuity
public import AVRegularity.CycleComparison.Lift.TransverseModeFactor
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public noncomputable section

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The scalar transverse damping acts on a finite coefficient carrier by a single explicit scalar matrix. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def transverseModeVectorODEData (rate : ℝ) (g : ℝ → ℝ) (f : ℝ → E)
    (a b : ℝ) (hab : a ≤ b) (M : ℝ) (hM : 0 ≤ M) (hg : AEStronglyMeasurable g volume)
    (hgb : ∀ t, |g t| ≤ M) (hf : IntervalIntegrable f volume a b) :
    CoupledEnergy.Galerkin.FiniteGalerkinODEData (V := E) a b hab where
  operator := fun t => (-rate * g t) • ContinuousLinearMap.id ℝ E
  forcing := f
  initial := 0
  operatorBound := |rate| * M
  operatorBound_nonneg := mul_nonneg (abs_nonneg _) hM
  operator_aestronglyMeasurable := (hg.const_mul (-rate)).smul aestronglyMeasurable_const
  operator_norm_le := fun t => by
    calc
      ‖(-rate * g t) • ContinuousLinearMap.id ℝ E‖ =
          (|rate| * |g t|) * ‖ContinuousLinearMap.id ℝ E‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg]
      _ ≤ |rate| * |g t| := mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
      _ ≤ |rate| * M := mul_le_mul_of_nonneg_left (hgb t) (abs_nonneg rate)
  forcing_intervalIntegrable := hf

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A transverse profile reduces the cell operator to scalar diffusion in its sole fast coordinate. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_profile_basis (f : ℝ → E) (hf : Differentiable ℝ f)
    (p i : Fin 2) (z : Vec 2) :
    fderiv ℝ (fun y : Vec 2 => f (y p)) z (basisVec i) =
      (if i = p then deriv f (z p) else 0) := by
  let pr : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj p
  have he : (fun y : Vec 2 => f (y p)) = f ∘ pr := rfl
  rw [he, fderiv_comp z (hf (z p)) pr.differentiableAt, pr.fderiv]
  simp [pr, fderiv_eq_smul_deriv, basisVec_apply, eq_comm]

theorem fderiv_profile_twice_basis (f : ℝ → E) (hf : ContDiff ℝ 2 f)
    (p i j : Fin 2) (z : Vec 2) :
    fderiv ℝ (fun y : Vec 2 => fderiv ℝ (fun w : Vec 2 => f (w p)) y (basisVec j)) z
      (basisVec i) = if i = p ∧ j = p then deriv (deriv f) (z p) else 0 := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have he : (fun y : Vec 2 => fderiv ℝ (fun w : Vec 2 => f (w p)) y (basisVec j)) =
      fun y => if j = p then deriv f (y p) else 0 := by
    funext y
    exact fderiv_profile_basis f hdf p j y
  rw [he]
  by_cases hj : j = p
  · simp only [hj, ite_true, and_true]
    exact fderiv_profile_basis (deriv f) hd p i z
  · simp [hj, fderiv_fun_const]

theorem cellOperator_transverse_profile (G : Fin 2 → Fin 2 → ℝ) (V : ℝ → ℝ)
    (par : Fin 2) (f : ℝ → E) (hf : ContDiff ℝ 2 f) (z : Vec 2) :
    cellOperator G (fun y => V (y par.rev) • basisVec par)
      (fun y => f (y par.rev)) z =
      -(G par.rev par.rev • deriv (deriv f) (z par.rev)) := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  simp only [cellOperator]
  simp_rw [fderiv_profile_twice_basis f hf]
  simp only [fderiv_profile_basis f hdf]
  fin_cases par <;> simp [basisVec_apply]

end AVRegularity.CycleComparison.Lift
end

section
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! A Wiener sum supported on transverse frequencies is exactly the one-dimensional sum. -/

theorem frequency_max_eq_parallel_transverse (par : Fin 2) (k : Fin 2 → ℤ) :
    max |(k 0 : ℝ)| |(k 1 : ℝ)| = max |(k par : ℝ)| |(k par.rev : ℝ)| := by
  fin_cases par <;> simp [max_comm]

theorem transverse_wiener_tsum (par : Fin 2) (L : ℕ) (B : ℤ → ℝ≥0∞) :
    (∑' k : Fin 2 → ℤ, ENNReal.ofReal ((1 + max |(k 0 : ℝ)| |(k 1 : ℝ)|) ^ L) *
      (if k par = 0 then B (k par.rev) else 0)) =
      ∑' m : ℤ, ENNReal.ofReal ((1 + |(m : ℝ)|) ^ L) * B m := by
  rw [← (transverseFrequencyEquiv par).symm.tsum_eq]
  simp_rw [frequency_max_eq_parallel_transverse par,
    transverseFrequencyEquiv_symm_parallel, transverseFrequencyEquiv_symm_transverse]
  rw [ENNReal.tsum_prod']
  have he (a : ℤ) : (∑' b : ℤ,
      ENNReal.ofReal ((1 + max |(a : ℝ)| |(b : ℝ)|) ^ L) * (if a = 0 then B b else 0)) =
      if a = 0 then ∑' b : ℤ, ENNReal.ofReal ((1 + |(b : ℝ)|) ^ L) * B b else 0 := by
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha]
  simp_rw [he]
  simp

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Polynomial metric-derivative factors leave a uniform reciprocal-rate time bound. -/

theorem weighted_decayKernel_pointwise (n : ℕ) (C rate κ τ : ℝ)
    (hC : 0 ≤ C) (hrate : 0 ≤ rate) (hκ : 0 < κ) (hτ : 0 ≤ τ) :
    (max 1 (C * rate * τ)) ^ n * Real.exp (-(rate * κ) * τ) ≤
      (1 + n.factorial * (2 * C / κ) ^ n) * Real.exp (-(rate * κ / 2) * τ) := by
  have hh := max_pow_mul_exp_double_neg_le n (2 * C / κ) (rate * κ * τ / 2)
    (div_nonneg (mul_nonneg (by norm_num) hC) hκ.le)
    (div_nonneg (mul_nonneg (mul_nonneg hrate hκ.le) hτ) (by norm_num))
  have ha : (2 * C / κ) * (rate * κ * τ / 2) = C * rate * τ := by
    field_simp
  have hb : -2 * (rate * κ * τ / 2) = -(rate * κ) * τ := by ring
  have hc : -(rate * κ * τ / 2) = -(rate * κ / 2) * τ := by ring
  simpa only [ha, hb, hc] using hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! In two dimensions a single coordinate multiplicity determines a symmetric word. -/

def wordZeroMultiplicity {m : ℕ} (α : DerivativeWord2 m) : ℕ :=
  Fintype.card {i : Fin m // α i = 0}

theorem wordZeroMultiplicity_le {m : ℕ} (α : DerivativeWord2 m) :
    wordZeroMultiplicity α ≤ m := by
  simpa only [wordZeroMultiplicity, Fintype.card_fin] using
    Fintype.card_subtype_le (fun i : Fin m => α i = 0)

theorem word_fiber_card_eq_of_zeroMultiplicity {m : ℕ} (α β : DerivativeWord2 m)
    (hc : wordZeroMultiplicity α = wordZeroMultiplicity β) (j : Fin 2) :
    Fintype.card {i : Fin m // α i = j} = Fintype.card {i : Fin m // β i = j} := by
  classical
  fin_cases j
  · exact hc
  · have ha : (fun i : Fin m => α i = 1) = fun i => ¬α i = 0 := by
      funext i
      simp only [eq_iff_iff]
      omega
    have hb : (fun i : Fin m => β i = 1) = fun i => ¬β i = 0 := by
      funext i
      simp only [eq_iff_iff]
      omega
    change Fintype.card (Subtype (fun i : Fin m => α i = 1)) =
      Fintype.card (Subtype (fun i : Fin m => β i = 1))
    simp only [ha, hb, Fintype.card_subtype_compl]
    exact congrArg (fun k => Fintype.card (Fin m) - k) hc

theorem wordSymbol_coordinate_power {m : ℕ} (α : DerivativeWord2 m) (ε : ℝ) :
    ((List.ofFn α).map (fun j => if j = 0 then ε else 1)).prod =
      ε ^ wordZeroMultiplicity α := by
  classical
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_def]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one,
    wordZeroMultiplicity, Fintype.card_subtype]

/-! Equal coordinate multiplicities identify ordered words up to permutation. -/

theorem derivativeWord_permutation_of_fiber_card {m : ℕ} (α β : DerivativeWord2 m)
    (hc : ∀ j, Fintype.card {i : Fin m // α i = j} =
      Fintype.card {i : Fin m // β i = j}) :
    ∃ σ : Equiv.Perm (Fin m), α ∘ σ = β := by
  classical
  let e : ∀ j, {i : Fin m // β i = j} ≃ {i : Fin m // α i = j} :=
    fun j => Fintype.equivOfCardEq (hc j).symm
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map e i

theorem symmetric_word_value_of_fiber_card {m : ℕ} {E : Type*}
    (c : DerivativeWord2 m → E)
    (hs : ∀ α (σ : Equiv.Perm (Fin m)), c (α ∘ σ) = c α)
    (α β : DerivativeWord2 m)
    (hc : ∀ j, Fintype.card {i : Fin m // α i = j} =
      Fintype.card {i : Fin m // β i = j}) : c α = c β := by
  obtain ⟨σ, hσ⟩ := derivativeWord_permutation_of_fiber_card α β hc
  rw [← hσ, hs]

/-! Scaling an exponential test direction makes each tested word homogeneous in its order. -/

theorem wordSymbol_smul {m : ℕ} (α : DerivativeWord2 m)
    (A : Vec 2 →L[ℝ] ℝ) (ε : ℝ) :
    ((List.ofFn α).map (fun j => (ε • A) (basisVec j))).prod =
      ε ^ m * ((List.ofFn α).map (fun j => A (basisVec j))).prod := by
  simp only [smul_apply, smul_eq_mul, List.map_ofFn, List.prod_ofFn, Function.comp_def,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! The common matrix-power entry factors out of the literal three-part source budget. -/

theorem ambientUncenteredScalarBudget_factor (D hh n : ℕ) (hn : 1 ≤ n)
    (B : ℕ → ℕ → ℝ) (K₁ K₂ : ℝ) (Ks : ℕ → ℝ) (z : ℝ) :
    K₁ * B hh (n - 1) * z +
      (if 2 ≤ n then K₂ * B hh (n - 2) * z else 0) +
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
        Ks j * B (hh - 1) (n - j) * z) =
      ambientUncenteredScalarBudget D hh n B K₁ K₂ Ks * z := by
  have h₂ : (if 2 ≤ n then K₂ * B hh (n - 2) * z else 0) =
      (if 2 ≤ n then K₂ * B hh (n - 2) else 0) * z := by
    split_ifs
    · rfl
    · exact (zero_mul z).symm
  have hS : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      Ks j * B (hh - 1) (n - j) * z) =
      (if 1 ≤ hh then ∑ j ∈ Finset.range (min D n + 1),
        Ks j * B (hh - 1) (n - j) else 0) * z := by
    by_cases hh0 : hh = 0
    · subst hh
      simp
    · rw [ite_eq_right hh0, ite_eq_left (by omega : 1 ≤ hh), Finset.sum_mul]
  rw [h₂, hS]
  unfold ambientUncenteredScalarBudget
  rw [ite_eq_left hn]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A constant field has only its value jet, so every positive slow or fast derivative costs zero. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_constant_graded_le (r q : ℕ) (c : E) (C lam : ℝ)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hc : ‖c‖ ≤ C) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun _ : Vec 2 => iteratedFDeriv ℝ q
      (fun _ : Vec 2 => c) z) X‖ ≤ C * lam ^ r := by
  apply (norm_mixed_slow_field_le r q (fun _ : Vec 2 => c) X z).trans
  cases r with
  | zero => simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hc
  | succ r =>
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
    exact mul_nonneg hC (pow_nonneg hlam _)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A polynomial direction probes the two coordinate multiplicities of a derivative word. -/

def coordinateSymbolDirection (ε : ℝ) : Vec 2 →L[ℝ] ℝ :=
  ε • ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1

theorem coordinateSymbolDirection_basis (ε : ℝ) (j : Fin 2) :
    coordinateSymbolDirection ε (basisVec j) = if j = 0 then ε else 1 := by
  fin_cases j <;> simp [coordinateSymbolDirection, basisVec]

theorem wordSymbol_coordinateDirection {m : ℕ} (α : DerivativeWord2 m) (ε : ℝ) :
    ((List.ofFn α).map (fun j => coordinateSymbolDirection ε (basisVec j))).prod =
      ε ^ wordZeroMultiplicity α := by
  simp only [coordinateSymbolDirection_basis]
  exact wordSymbol_coordinate_power α ε

/-! Affine coordinate tests isolate the first-order coefficient entries. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_one (α : DerivativeWord2 1) (f : Vec 2 → E) :
    orderedDerivative α f = fun X => fderiv ℝ f X (basisVec (α 0)) := by
  simp [orderedDerivative, List.ofFn_succ]

theorem orderedDerivative_one_affine (α : DerivativeWord2 1) (q : Fin 2)
    (X : Vec 2) (ξ : E) :
    orderedDerivative α (fun Y : Vec 2 => (Y q - X q) • ξ) =
      fun _ => if α 0 = q then ξ else 0 := by
  let A : Vec 2 →L[ℝ] E := (ContinuousLinearMap.proj q).smulRight ξ
  have he : (fun Y : Vec 2 => (Y q - X q) • ξ) = fun Y => A Y - (X q) • ξ := by
    funext Y
    simp [A, sub_smul]
  rw [orderedDerivative_one, he]
  funext Y
  rw [fderiv_sub_const]
  rw [A.fderiv]
  simp [A, basisVec_apply, eq_comm]
end

/-! Ordered derivatives of a directional eigenfunction are products of its eigenvalues. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem directional_fold_eigenfunction (f : Vec 2 → E) (hf : Differentiable ℝ f)
    (q : Fin 2 → ℝ) (hq : ∀ j X, fderiv ℝ f X (basisVec j) = q j • f X)
    (w : List (Fin 2)) (c : ℝ) :
    w.foldl (fun g j => fun X => fderiv ℝ g X (basisVec j)) (fun X => c • f X) =
      fun X => (c * (w.map q).prod) • f X := by
  induction w generalizing c with
  | nil => simp
  | cons j w ih =>
    rw [List.foldl_cons]
    have he : (fun X => fderiv ℝ (fun Y => c • f Y) X (basisVec j)) =
        fun X => (c * q j) • f X := by
      funext X
      rw [fderiv_fun_const_smul (hf X), smul_apply, hq, smul_smul]
    rw [he, ih]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

theorem orderedDerivative_eigenfunction {m : ℕ} (α : DerivativeWord2 m)
    (f : Vec 2 → E) (hf : Differentiable ℝ f) (q : Fin 2 → ℝ)
    (hq : ∀ j X, fderiv ℝ f X (basisVec j) = q j • f X) :
    orderedDerivative α f = fun X => ((List.ofFn α).map q).prod • f X := by
  have he := directional_fold_eigenfunction f hf q hq (List.ofFn α) 1
  simpa only [one_smul, one_mul, orderedDerivative] using he
end

/-! First tested-order words are exactly the two coordinate derivatives. -/

def firstWordEquiv : DerivativeWord2 1 ≃ Fin 2 where
  toFun α := α 0
  invFun j := fun _ => j
  left_inv α := by
    funext i
    apply congrArg α
    apply Fin.ext
    have hi := i.isLt
    omega
  right_inv j := rfl

theorem orderedDerivative_first_word {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : DerivativeWord2 1) (f : Vec 2 → E) :
    orderedDerivative α f = fun X => fderiv ℝ f X (basisVec (α 0)) := by
  simp only [orderedDerivative, List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil]

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! A single integrated perturbation factor leaves an integrable exponential majorant. -/

theorem linear_weighted_decayKernel_le (rate κ τ : ℝ)
    (hrate : 0 ≤ rate) (hκ : 0 < κ) (hτ : 0 ≤ τ) :
    (rate * τ) * Real.exp (-(rate * κ) * τ) ≤
      (1 + 2 / κ) * Real.exp (-(rate * κ / 2) * τ) := by
  have he := weighted_decayKernel_pointwise 1 1 rate κ τ zero_le_one hrate hκ hτ
  simp only [one_mul, pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at he
  exact (mul_le_mul_of_nonneg_right (le_max_right 1 (rate * τ)) (Real.exp_pos _).le).trans he

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Finite linear combinations commute with the centered periodic primitive. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem centeredIntervalPrimitive_zero (r : ℝ) :
    centeredIntervalPrimitive (0 : ℝ → E) r = 0 := by
  simp [centeredIntervalPrimitive]

theorem centeredIntervalPrimitive_add (f g : ℝ → E)
    (hf : Continuous f) (hg : Continuous g) (r : ℝ) :
    centeredIntervalPrimitive (fun y => f y + g y) r =
      centeredIntervalPrimitive f r + centeredIntervalPrimitive g r := by
  have he (s : ℝ) : (∫ y in (0 : ℝ)..s, f y + g y) =
      (∫ y in (0 : ℝ)..s, f y) + ∫ y in (0 : ℝ)..s, g y :=
    intervalIntegral.integral_add (hf.intervalIntegrable 0 s) (hg.intervalIntegrable 0 s)
  unfold centeredIntervalPrimitive
  simp_rw [he]
  rw [intervalIntegral.integral_add
    ((intervalPrimitive_continuous f hf).intervalIntegrable 0 1)
    ((intervalPrimitive_continuous g hg).intervalIntegrable 0 1)]
  abel

theorem centeredIntervalPrimitive_finset_sum {J : Type*} (s : Finset J)
    (f : J → ℝ → E) (hf : ∀ j ∈ s, Continuous (f j)) (r : ℝ) :
    centeredIntervalPrimitive (fun y => ∑ j ∈ s, f j y) r =
      ∑ j ∈ s, centeredIntervalPrimitive (f j) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [centeredIntervalPrimitive]
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [centeredIntervalPrimitive_add (f j) (fun y => ∑ i ∈ s, f i y)
      (hf j (Finset.mem_insert_self j s))
      (continuous_finsetSum s (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Finite profile jets give explicit inverse-frequency decay, uniformly in any external parameters. -/

theorem unitProfileFourierCoeff_iteratedDeriv (j : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ j f) (hp : Function.Periodic f 1) (n : ℤ) (hn : n ≠ 0) :
    unitProfileFourierCoeff (iteratedDeriv j f) n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ j * unitProfileFourierCoeff f n := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : ContDiff ℝ j f := hf.of_le (by exact_mod_cast Nat.le_succ j)
    have h1 : ContDiff ℝ 1 (iteratedDeriv j f) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hf).2
    rw [iteratedDeriv_succ, unitProfileFourierCoeff_deriv _ h1
      (profile_iteratedDeriv_periodic f 1 hp j) n hn, ih hj, pow_succ]
    ring

theorem unitProfileFourierCoeff_frequency_weight_bound (j : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ j f) (hp : Function.Periodic f 1) (n : ℤ) (hn : n ≠ 0)
    (C : ℝ) (hC : ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv j f x‖ ≤ C) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ ^ j * ‖unitProfileFourierCoeff f n‖ ≤ C := by
  have he := unitProfileFourierCoeff_norm_le (iteratedDeriv j f) n C hC
  rwa [unitProfileFourierCoeff_iteratedDeriv j f hf hp n hn, norm_mul, norm_pow] at he

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Absolute summability of the finite Fourier jets produces the required classical fast regularity. -/

theorem profileFourierSeries_contDiff (q : ℕ) (c : ℤ → ℂ)
    (hc : ∀ j : ℕ, j ≤ q → Summable (fun n => profileFourierFrequency n ^ j * c n)) :
    ContDiff ℝ q (profileFourierSeries c) := by
  induction q generalizing c with
  | zero =>
    apply contDiff_zero.mpr
    exact profileFourierSeries_continuous c (by simpa using hc 0 le_rfl)
  | succ q ih =>
    have h0 : Summable c := by simpa using hc 0 (Nat.zero_le _)
    have h1 : Summable (fun n => profileFourierFrequency n * c n) := by
      simpa using hc 1 (Nat.succ_le_succ (Nat.zero_le _))
    have hd : deriv (profileFourierSeries c) =
        profileFourierSeries (fun n => profileFourierFrequency n * c n) := by
      funext x
      exact (profileFourierSeries_hasDerivAt c h0 h1 x).deriv
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨(fun x => (profileFourierSeries_hasDerivAt c h0 h1 x).differentiableAt), ?_, ?_⟩
    · simp
    · rw [hd]
      apply ih
      intro j hj
      apply (hc (j + 1) (Nat.succ_le_succ hj)).congr
      intro n
      simp only [pow_succ, mul_assoc]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Physical flux coefficients restore one spatial factor per divergence order. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def scaledMeanCoefficient (c ρ : ℝ) (τ : ℝ → ℝ) (b : MeanCoeff ι h) : MeanCoeff ι h :=
  fun d α t x k v u => (c * ρ ^ d) • b d α (τ t) (ρ⁻¹ • x) k v u

omit [Fintype ι] in
theorem scaledMeanCoefficient_perm (c ρ : ℝ) (τ : ℝ → ℝ) (b : MeanCoeff ι h)
    (hb : ∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))), b d (α ∘ σ) = b d α)
    (d : ℕ) (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))) :
    scaledMeanCoefficient c ρ τ b d (α ∘ σ) = scaledMeanCoefficient c ρ τ b d α := by
  unfold scaledMeanCoefficient
  rw [hb]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Changing space and time variables preserves the uniform jet bound with the spatial scale. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slowJet_dilation_smul_le (I J : Set ℝ) (τ : ℝ → ℝ) (hτ : ∀ t ∈ J, τ t ∈ I)
    (j : ℕ) (a c : ℝ) (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t ∈ I, ∀ z, ContDiff ℝ (j : ℕ∞) (fun X => f t X z)) :
    slowJet J j (fun t X z => c • f (τ t) (a • X) z) ≤
      ENNReal.ofReal (|c| * |a| ^ j) * slowJet I j f := by
  unfold slowJet
  refine iSup_le fun t => iSup_le fun ht => iSup_le fun X => iSup_le fun z => ?_
  rw [← ofReal_norm, norm_iteratedFDeriv_dilation_smul j a c _ (hf (τ t) (hτ t ht) z) X]
  rw [ENNReal.ofReal_mul (mul_nonneg (abs_nonneg c) (pow_nonneg (abs_nonneg a) j))]
  apply mul_le_mul' le_rfl
  rw [ofReal_norm]
  exact le_iSup_of_le (τ t) (le_iSup_of_le (hτ t ht)
    (le_iSup_of_le (a • X) (le_iSup (fun z =>
      ‖iteratedFDeriv ℝ j (fun Y => f (τ t) Y z) (a • X)‖ₑ) z)))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! The exact metric difference kernel is an interpolation average with one perturbation factor. -/

theorem transverseModeKernel_metric_difference_integral (rate : ℝ) (g : ℝ → ℝ)
    (s t : ℝ) (hi : IntervalIntegrable g volume s t) :
    transverseModeKernel rate g s t - transverseModeKernel rate (fun _ => 1) s t =
      ∫ θ in (0 : ℝ)..1,
        transverseModeKernel rate (fun r => (1 - θ) + θ * g r) s t *
          (-rate * ∫ r in s..t, g r - 1) := by
  let I := ∫ r in s..t, g r
  have hdiff : (∫ r in s..t, g r - 1) = I - (t - s) := by
    rw [intervalIntegral.integral_sub hi (intervalIntegrable_const (μ := volume))]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, I]
  have hmix (θ : ℝ) : (∫ r in s..t, (1 - θ) + θ * g r) =
      (1 - θ) * (t - s) + θ * I := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const (μ := volume)) (hi.const_mul θ),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul, I]
    ring
  have he := exponential_difference_integral (-rate * (t - s)) (-rate * (I - (t - s)))
  have ha : -rate * (t - s) + -rate * (I - (t - s)) = -rate * I := by ring
  rw [ha] at he
  simp only [transverseModeKernel, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  change Real.exp (-rate * I) - Real.exp (-rate * (t - s)) = _
  rw [he]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [hmix, hdiff]
  congr 1
  congr 1
  ring

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Integrability and reciprocal-rate mass of the measurable transverse mode propagator. -/

theorem transverseModeKernel_continuousOn_left (rate : ℝ) (g : ℝ → ℝ)
    (a t : ℝ) (hi : IntegrableOn g (uIcc a t)) :
    ContinuousOn (fun s => transverseModeKernel rate g s t) (uIcc a t) := by
  exact Real.continuous_exp.comp_continuousOn
    ((intervalIntegral.continuousOn_primitive_interval_left hi).const_mul (-rate))

theorem transverseModeKernel_intervalIntegrable (rate : ℝ) (g : ℝ → ℝ)
    (a t : ℝ) (hi : IntegrableOn g (uIcc a t)) :
    IntervalIntegrable (fun s => transverseModeKernel rate g s t) volume a t :=
  (transverseModeKernel_continuousOn_left rate g a t hi).intervalIntegrable

theorem integral_transverseModeKernel_le (rate κ : ℝ) (hrate : 0 < rate) (hκ : 0 < κ)
    (g : ℝ → ℝ) (a t : ℝ) (hat : a ≤ t) (hi : IntegrableOn g (Icc a t))
    (hg : ∀ r ∈ Icc a t, κ ≤ g r) :
    (∫ s in a..t, transverseModeKernel rate g s t) ≤ 1 / (rate * κ) := by
  have hi' : IntegrableOn g (uIcc a t) := by simpa [uIcc_of_le hat] using hi
  have he := intervalIntegral.integral_mono_on hat
    (transverseModeKernel_intervalIntegrable rate g a t hi')
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-(rate * κ) * (t - s)))).intervalIntegrable a t)
    (fun s hs => transverseModeKernel_le_exp rate κ hrate.le g s t hs.2
      ((by simpa [uIcc_of_le hs.2] using
        hi.mono_set (Icc_subset_Icc hs.1 le_rfl)) : IntegrableOn g (uIcc s t)).intervalIntegrable
      (fun r hr => hg r ⟨hs.1.trans hr.1, hr.2⟩))
  exact he.trans (integral_decayKernel_le (rate * κ) (mul_pos hrate hκ) a t)

/-! The transverse mode kernel solves the homogeneous ODE even for measurable time coefficients. -/

theorem transverseModeKernel_absolutelyContinuous_right (rate : ℝ) (g : ℝ → ℝ)
    (a b s : ℝ) (hi : IntervalIntegrable g volume a b) (hs : s ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t => transverseModeKernel rate g s t) a b :=
  absolutelyContinuousOnInterval_exp
    ((hi.absolutelyContinuousOnInterval_intervalIntegral hs).const_mul (-rate))

theorem transverseModeKernel_ae_hasDerivAt_right (rate : ℝ) (g : ℝ → ℝ)
    (a b s : ℝ) (hi : IntervalIntegrable g volume a b) (hs : s ∈ uIcc a b) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt (fun r => transverseModeKernel rate g s r)
      (-rate * g t * transverseModeKernel rate g s t) t := by
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht htab
  simpa only [transverseModeKernel, mul_assoc, mul_comm, mul_left_comm] using
    ((ht htab s hs).const_mul (-rate)).exp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Any drift tangent to a transverse profile drops out of its classical cell operator. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellOperator_transverse_profile_tangent_drift (G : Fin 2 → Fin 2 → ℝ)
    (v : Vec 2 → Vec 2) (par : Fin 2) (hv : ∀ z, v z par.rev = 0)
    (f : ℝ → E) (hf : ContDiff ℝ 2 f) (z : Vec 2) :
    cellOperator G v (fun y => f (y par.rev)) z =
      -(G par.rev par.rev • iteratedDeriv 2 f (z par.rev)) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hsum : (∑ k : Fin 2, v z k • fderiv ℝ (fun y => f (y par.rev)) z (basisVec k)) = 0 := by
    simp_rw [fderiv_profile_basis f hd par.rev]
    rw [Finset.sum_eq_single par.rev]
    · simp [hv]
    · intro k _ hk
      simp [hk]
    · simp
  have he := cellOperator_transverse_profile G (fun _ => 0) par f hf z
  simp only [cellOperator, zero_smul, Pi.zero_apply, Finset.sum_const_zero, zero_sub] at he
  change _ - _ = _
  rw [hsum, zero_sub]
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Clamped Duhamel time sections remain measurable for measurable source data. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem clamped_duhamel_measurable (g : ℝ → Vec 2 → ℝ)
    (f : ℝ → Vec 2 → E) (hf : ∀ X, Measurable (fun t => f t X))
    (rate a b : ℝ) (hab : a ≤ b)
    (hi : ∀ X, IntegrableOn (fun t => g t X) (Icc a b)) (X : Vec 2) :
    Measurable (fun s => transverseModeKernel rate (fun t => g t X)
      (projIcc a b hab s) b • f (projIcc a b hab s) X) := by
  have hproj := (continuous_projIcc (a := a) (b := b) (h := hab)).subtype_val
  have hi' : IntegrableOn (fun t => g t X) (uIcc a b) := by
    simpa [uIcc_of_le hab] using hi X
  have hk := (transverseModeKernel_continuousOn_left rate (fun t => g t X) a b hi').comp_continuous
    hproj (fun s => by rw [uIcc_of_le hab]; exact (projIcc a b hab s).2)
  exact hk.measurable.smul ((hf X).comp hproj.measurable)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Exponential coarse tests give the finite symbol of an ordered differential operator. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_exp_linear_smul {m : ℕ} (α : DerivativeWord2 m)
    (A : Vec 2 →L[ℝ] ℝ) (ξ : E) :
    orderedDerivative α (fun X => Real.exp (A X) • ξ) =
      fun X => (((List.ofFn α).map (fun j => A (basisVec j))).prod * Real.exp (A X)) • ξ := by
  have hf : Differentiable ℝ (fun X => Real.exp (A X) • ξ) := by
    exact A.differentiable.exp.smul_const ξ
  have hq : ∀ j X, fderiv ℝ (fun Y => Real.exp (A Y) • ξ) X (basisVec j) =
      A (basisVec j) • (Real.exp (A X) • ξ) := by
    intro j X
    have hd := (A.hasFDerivAt (x := X)).exp.smul_const ξ
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
      smul_eq_mul, mul_comm (Real.exp (A X)), smul_smul]
  simpa only [smul_smul] using
    orderedDerivative_eigenfunction α _ hf (fun j => A (basisVec j)) hq
end

/-! The diagonal molecular metric flux is a first tested-order block operator. -/

section
variable {ι : Type*} [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def metricFluxCoefficient (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (k : Fin 2) : LiftCoeff ι h := fun m =>
  match m with
  | 1 => fun α t X _ v u => (-η * G t X k (α 0)) • blockIdentityEntry h v u
  | _ => fun _ _ _ _ _ _ => 0

theorem metricFluxCoefficient_one (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (k : Fin 2) (α : DerivativeWord2 1) (t : ℝ) (X z : Vec 2) (v u : ι) :
    metricFluxCoefficient η G k 1 α t X z v u =
      (-η * G t X k (α 0)) • blockIdentityEntry h v u := rfl

theorem metricFluxCoefficient_zero (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (k : Fin 2) (α : DerivativeWord2 0) (t : ℝ) (X z : Vec 2) (v u : ι) :
    metricFluxCoefficient (h := h) η G k 0 α t X z v u = 0 := rfl

theorem metricFluxCoefficient_perm (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (k : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    metricFluxCoefficient (h := h) η G k m (α ∘ σ) = metricFluxCoefficient η G k m α := by
  cases m with
  | zero => rfl
  | succ m =>
    cases m with
    | zero =>
      have hs : α ∘ σ = α := by
        funext i
        apply congrArg α
        apply Fin.ext
        have hi := i.isLt
        have hσ := (σ i).isLt
        omega
      rw [hs]
    | succ m => rfl
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Scalar dual estimates recover mixed jet norms with constant one. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixed_jet_norm_le_from_real_duals (p q : ℕ) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p q f) (X z : Vec 2) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ l : E →L[ℝ] ℝ,
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun y => l (f Y y)) z) X‖ ≤ C * ‖l‖) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ ≤ C := by
  apply mixed_multilinear_norm_le_from_real_duals _ C hC
  intro l
  let A := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin q => Vec 2) E ℝ l
  have he : (fun Y => iteratedFDeriv ℝ q (fun y => l (f Y y)) z) =
      A ∘ (fun Y => iteratedFDeriv ℝ q (f Y) z) := by
    funext Y
    exact l.iteratedFDeriv_comp_left (hf.1 Y).contDiffAt le_rfl
  have hh := hb l
  rw [he, A.iteratedFDeriv_comp_left (hf.2.1 q le_rfl z).contDiffAt le_rfl] at hh
  exact hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ordered derivatives commute with the explicit finite coefficient synthesis map. -/

section
variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_finite_synthesis {m : ℕ} (α : DerivativeWord2 m)
    (w : J → ℝ) (f : J → Vec 2 → E) (hf : ∀ j, ContDiff ℝ (m : ℕ∞) (f j)) (X : Vec 2) :
    orderedDerivative α (fun Y => ∑ j, w j • f j Y) X =
      ∑ j, w j • orderedDerivative α (f j) X := by
  let F : Vec 2 → J → E := fun Y j => f j Y
  let L : (J → E) →L[ℝ] E := ∑ j, w j • ContinuousLinearMap.proj j
  have hF : ContDiff ℝ (m : ℕ∞) F := contDiff_pi.mpr hf
  have hL (u : J → E) : L u = ∑ j, w j • u j := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply]
  have hcomp : (fun Y => L (F Y)) = fun Y => ∑ j, w j • f j Y := funext (fun Y => hL (F Y))
  rw [← hcomp, orderedDerivative_clm_comp L α hF]
  dsimp only
  rw [hL]
  apply Finset.sum_congr rfl
  intro j _
  have he := congrFun (orderedDerivative_clm_comp
    (ContinuousLinearMap.proj j : (J → E) →L[ℝ] E) α hF) X
  exact congrArg (fun u => w j • u) he.symm
end

/-! Spatial dilation preserves the qualitative regularity of the physical flux arrays. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
theorem scaledMeanCoefficient_contDiff (c ρ : ℝ) (τ : ℝ → ℝ) (b : MeanCoeff ι h)
    (p d : ℕ) (α : DerivativeWord2 (d - 1)) (t : ℝ) (k : Fin 2) (v u : ι)
    (hb : ContDiff ℝ (p : ℕ∞) (fun X => b d α (τ t) X k v u)) :
    ContDiff ℝ (p : ℕ∞) (fun x => scaledMeanCoefficient c ρ τ b d α t x k v u) :=
  (hb.comp (contDiff_const_smul ρ⁻¹)).const_smul (c * ρ ^ d)
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Zero cell-norm arrays. -/

/-- The cell jet of the zero field. -/
theorem cellL2Jet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ) (i : ℕ) :
    cellL2Jet I i (fun (_ : ℝ) (_ _ : Vec 2) => (0 : E)) = 0 := by
  unfold cellL2Jet
  refine le_antisymm (iSup₂_le fun t _ => iSup_le fun X => ?_) bot_le
  refine le_of_eq ?_
  have h0 : (fun z : Vec 2 => iteratedFDeriv ℝ i (fun _ : Vec 2 => (0 : E)) X) = 0 := by
    funext z; simp [iteratedFDeriv_fun_zero]
  rw [h0]
  exact eLpNorm_zero (ε := ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E)

/-- The Schur jet of an array that vanishes identically. -/
theorem schurCellL2Jet_eq_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]
    (π : ι → ℝ) (I : Set ℝ) (i : ℕ) (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v)
    (hc : ∀ a t X z v u, c a t X z v u = 0) : schurCellL2Jet π I i c = 0 := by
  have h0 : ∀ a v u, (fun t X z => c a t X z v u) = fun _ _ _ => 0 := by
    intro a v u; funext t X z; exact hc a t X z v u
  unfold schurCellL2Jet schurSums
  simp only [h0, cellL2Jet_zero]
  simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A symmetric array is constant on each coordinate-count orbit. -/

section
variable {E : Type*} [AddCommMonoid E]

theorem symmetric_word_orbit_sum {m : ℕ} (c : DerivativeWord2 m → E)
    (hs : ∀ β (σ : Equiv.Perm (Fin m)), c (β ∘ σ) = c β) (α : DerivativeWord2 m) :
    (∑ β : DerivativeWord2 m, if wordZeroMultiplicity β = wordZeroMultiplicity α then c β else 0) =
      Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} • c α := by
  classical
  have he : (∑ β : DerivativeWord2 m,
      if wordZeroMultiplicity β = wordZeroMultiplicity α then c β else 0) =
      ∑ β : DerivativeWord2 m,
      if wordZeroMultiplicity β = wordZeroMultiplicity α then c α else 0 := by
    apply Finset.sum_congr rfl
    intro β _
    by_cases hb : wordZeroMultiplicity β = wordZeroMultiplicity α
    · rw [ite_eq_left hb, ite_eq_left hb]
      exact symmetric_word_value_of_fiber_card c hs β α
        (word_fiber_card_eq_of_zeroMultiplicity β α hb)
    · simp only [hb, ite_false]
  rw [he, ← Finset.sum_filter]
  simp only [Finset.sum_const, Fintype.card_subtype]
end

/-! A scalar polynomial derivative recovers the symmetric coefficient on each word orbit. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem symmetric_word_polynomial_derivative {m : ℕ} (c : DerivativeWord2 m → E)
    (hs : ∀ α (σ : Equiv.Perm (Fin m)), c (α ∘ σ) = c α) (α : DerivativeWord2 m) :
    iteratedDeriv (wordZeroMultiplicity α)
      (fun ε : ℝ => ∑ β : DerivativeWord2 m, ε ^ wordZeroMultiplicity β • c β) 0 =
    (wordZeroMultiplicity α).factorial •
      (Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} •
        c α) := by
  classical
  let r := wordZeroMultiplicity α
  have hd : ∀ β ∈ (Finset.univ : Finset (DerivativeWord2 m)),
      ContDiffAt ℝ (r : WithTop ℕ∞) (fun ε : ℝ => ε ^ wordZeroMultiplicity β • c β) 0 :=
    fun β _ => ((contDiff_id.pow _).smul contDiff_const).contDiffAt
  rw [iteratedDeriv_fun_sum hd]
  have he (β : DerivativeWord2 m) :
      iteratedDeriv r (fun ε : ℝ => ε ^ wordZeroMultiplicity β • c β) 0 =
      if wordZeroMultiplicity β = r then (r.factorial : ℝ) • c α else 0 := by
    rw [iteratedDeriv_smul_const (contDiff_id.pow _).contDiffAt (c β),
      iteratedDeriv_fun_pow_zero]
    by_cases hb : wordZeroMultiplicity β = r
    · have hc : c β = c α := symmetric_word_value_of_fiber_card c hs β α
        (word_fiber_card_eq_of_zeroMultiplicity β α hb)
      simp only [hb, ite_true, hc]
    · simp only [hb, ite_false, Ne.symm hb, Nat.cast_zero, zero_smul]
  rw [Finset.sum_congr rfl (fun β _ => he β)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, Fintype.card_subtype]
  simp only [Nat.cast_smul_eq_nsmul]
  rw [smul_comm]
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The finite-past Duhamel response gains the reciprocal transverse damping rate. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def transverseModeResponse (rate : ℝ) (g : ℝ → ℝ) (f : ℝ → E) (a t : ℝ) : E :=
  ∫ s in a..t, transverseModeKernel rate g s t • f s

theorem transverseModeResponse_norm_le (rate κ : ℝ) (hrate : 0 < rate) (hκ : 0 < κ)
    (g : ℝ → ℝ) (f : ℝ → E) (a t : ℝ) (hat : a ≤ t)
    (hi : IntegrableOn g (Icc a t)) (hg : ∀ r ∈ Icc a t, κ ≤ g r)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ s ∈ Icc a t, ‖f s‖ ≤ C) :
    ‖transverseModeResponse rate g f a t‖ ≤ C / (rate * κ) := by
  have hi' : IntegrableOn g (uIcc a t) := by simpa [uIcc_of_le hat] using hi
  have hk := transverseModeKernel_intervalIntegrable rate g a t hi'
  have hb : ∀ᵐ s ∂volume, s ∈ Ioc a t →
      ‖transverseModeKernel rate g s t • f s‖ ≤ C * transverseModeKernel rate g s t := by
    exact Filter.Eventually.of_forall fun s hs => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (transverseModeKernel_pos rate g s t)]
      exact (mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2⟩)
        (transverseModeKernel_pos rate g s t).le).trans_eq (mul_comm _ _)
  have hb' := intervalIntegral.norm_integral_le_of_norm_le hat hb (hk.const_mul C)
  unfold transverseModeResponse
  calc
    ‖∫ s in a..t, transverseModeKernel rate g s t • f s‖
        ≤ ∫ s in a..t, C * transverseModeKernel rate g s t := hb'
    _ = C * ∫ s in a..t, transverseModeKernel rate g s t :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ C * (1 / (rate * κ)) := mul_le_mul_of_nonneg_left
      (integral_transverseModeKernel_le rate κ hrate hκ g a t hat hi hg) hC
    _ = C / (rate * κ) := by ring
end

/-! A scalar mode's integrating factor gives the exact forced finite-past identity. -/

theorem transverseMode_weighted_identity (rate : ℝ) (g f u : ℝ → ℝ) (a b : ℝ)
    (hi : IntervalIntegrable g volume a b) (hu : AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt u (-rate * g t * u t + f t) t) :
    transverseModeKernel (-rate) g a b * u b - u a =
      ∫ t in a..b, transverseModeKernel (-rate) g a t * f t := by
  let w := fun t => transverseModeKernel (-rate) g a t
  have hw := transverseModeKernel_absolutelyContinuous_right (-rate) g a b a hi left_mem_uIcc
  have he := hw.integral_deriv_mul_eq_sub hu
  have hwa : w a = 1 := by simp [w]
  change (∫ t in a..b, deriv w t * u t + w t * deriv u t) = w b * u b - w a * u a at he
  rw [hwa, one_mul] at he
  apply he.symm.trans
  apply intervalIntegral.integral_congr_ae_restrict
  have hdu := hd.filter_mono (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  have hdw := (transverseModeKernel_ae_hasDerivAt_right (-rate) g a b a hi left_mem_uIcc).filter_mono
    (ae_mono (Measure.restrict_le_self : volume.restrict (uIoc a b) ≤ volume))
  filter_upwards [hdu, hdw, ae_restrict_mem measurableSet_uIoc] with t hut hwt ht
  rw [hut.deriv, (hwt (uIoc_subset_uIcc ht)).deriv]
  dsimp only [w]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Parallel fast invariance is preserved by partials without additional differentiability premises. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transverse_slowPartial (par k : Fin 2) (I : Set ℝ)
    (f : ℝ → Vec 2 → Vec 2 → E) (hf : IsTransverseOn par I f) :
    IsTransverseOn par I (fun t => slowPartial k (f t)) := by
  intro t ht X z s
  have he : (fun Y => f t Y (z + s • basisVec par)) = fun Y => f t Y z :=
    funext (fun Y => hf t ht Y z s)
  change fderiv ℝ (fun Y => f t Y (z + s • basisVec par)) X (basisVec k) = _
  rw [he]
  rfl

theorem transverse_fastPartial (par k : Fin 2) (I : Set ℝ)
    (f : ℝ → Vec 2 → Vec 2 → E) (hf : IsTransverseOn par I f) :
    IsTransverseOn par I (fun t => fastPartial k (f t)) := by
  intro t ht X z s
  have he : (fun y => f t X (y + s • basisVec par)) = f t X :=
    funext (fun y => hf t ht X y s)
  have hh := fderiv_comp_add_right (𝕜 := ℝ) (f := f t X) (x := z) (s • basisVec par)
  rw [he] at hh
  change fderiv ℝ (f t X) (z + s • basisVec par) (basisVec k) = _
  rw [← hh]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem transverse_profile_representation (par : Fin 2) (I : Set ℝ)
    (f : ℝ → Vec 2 → Vec 2 → E) (hf : IsTransverseOn par I f)
    (t : ℝ) (ht : t ∈ I) (X z : Vec 2) :
    f t X z = f t X (z par.rev • basisVec par.rev) := by
  have he : z par.rev • basisVec par.rev + z par • basisVec par = z := by
    fin_cases par <;> ext k <;> fin_cases k <;> simp [basisVec_apply]
  have hh := hf t ht X (z par.rev • basisVec par.rev) (z par)
  rw [he] at hh
  exact hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Fixed interpolation extracts a coordinate-count orbit without differentiating a parameter. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem word_polynomial_finite_extraction {m : ℕ} (r : ℕ) (hr : r ≤ m)
    (c : DerivativeWord2 m → E) :
    (∑ j : Fin (m + 1), polynomialExtractionWeight m r j •
      ∑ β : DerivativeWord2 m, (j : ℝ) ^ wordZeroMultiplicity β • c β) =
      ∑ β : DerivativeWord2 m, if wordZeroMultiplicity β = r then c β else 0 := by
  classical
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  have hp (ε : ℝ) : (∑ i ∈ Finset.range (m + 1), ε ^ i •
      (if i = wordZeroMultiplicity β then c β else 0)) =
      ε ^ wordZeroMultiplicity β • c β := by
    simp only [smul_ite, smul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range, Nat.lt_succ_iff, wordZeroMultiplicity_le, ite_true]
  have he := finite_polynomial_coefficient_interpolation m r hr
    (fun i => if i = wordZeroMultiplicity β then c β else 0)
  simpa only [hp, eq_comm] using he

end AVRegularity.CycleComparison.Lift
end
