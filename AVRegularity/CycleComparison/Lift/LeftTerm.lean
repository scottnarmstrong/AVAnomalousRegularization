-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.WordPolynomialFiniteExtraction
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The lift operator at a time only uses the coarse input at that time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_input_congr_at_time (n : ℕ) (c : LiftCoeff ι h)
    (a b : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (he : a t = b t) :
    liftApply n c a t = liftApply n c b t := by
  funext X z v
  simp only [liftApply, he]
end

/-! The first-order metric flux retains the available slow coefficient regularity. -/

section
variable {ι : Type*} [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem metricFluxCoefficient_contDiff (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (p : ℕ) (t : ℝ) (hG : ∀ i j, ContDiff ℝ (p : ℕ∞) (fun X => G t X i j))
    (k : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (z : Vec 2) (v u : ι) :
    ContDiff ℝ (p : ℕ∞) (fun X => metricFluxCoefficient (h := h) η G k m α t X z v u) := by
  cases m with
  | zero => exact contDiff_const
  | succ m =>
    cases m with
    | zero => exact (contDiff_const.mul (hG k (α 0))).smul contDiff_const
    | succ m => exact contDiff_const
end

/-! Normalizing by the nonzero word-orbit cardinality extracts each symmetric left coefficient. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem wordOrbit_card_pos {m : ℕ} (α : DerivativeWord2 m) :
    0 < Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨α, rfl⟩⟩

theorem symmetric_word_coefficient_extraction {m : ℕ} (c : DerivativeWord2 m → E)
    (hs : ∀ α (σ : Equiv.Perm (Fin m)), c (α ∘ σ) = c α) (α : DerivativeWord2 m) :
    (((wordZeroMultiplicity α).factorial *
      Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℕ) : ℝ)⁻¹ •
      iteratedDeriv (wordZeroMultiplicity α)
        (fun ε : ℝ => ∑ β : DerivativeWord2 m, ε ^ wordZeroMultiplicity β • c β) 0 = c α := by
  rw [symmetric_word_polynomial_derivative c hs α]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_smul, smul_smul, Nat.cast_mul]
  rw [mul_assoc, inv_mul_cancel₀, one_smul]
  exact mul_ne_zero (by exact_mod_cast (wordZeroMultiplicity α).factorial_ne_zero)
    (by exact_mod_cast (Nat.ne_of_gt (wordOrbit_card_pos α)))
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Rectangular smoothness and time-measurable values give measurable mixed coordinate words. -/

variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem boxSmooth_fast_word_slow_contDiff (p q s : ℕ) (hs : s ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (β : DerivativeWord2 s) (z : Vec 2) :
    ContDiff ℝ (p : ℕ∞) (fun X => orderedDerivative β (f X) z) := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2) E
    (fun k => basisVec (β (Fin.rev k)))
  have he : (fun X => orderedDerivative β (f X) z) =
      fun X => L (iteratedFDeriv ℝ s (f X) z) := by
    funext X
    rw [AVRegularity.Sampling.orderedDerivative_eq_iteratedFDeriv β (f X)
      ((hf.1 X).of_le (by exact_mod_cast hs))]
    rfl
  rw [he]
  exact L.contDiff.comp (hf.2.1 s hs z)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Uncentered affine tests recover first coefficients once the zeroth coefficient is zero. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_one_linear_single_of_zero_order (c : LiftCoeff ι h)
    (α : DerivativeWord2 1) (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u)
    (hc0 : ∀ β : DerivativeWord2 0, ∀ j, c 0 β t X z v j = 0) :
    liftApply 1 c (fun _ Y => Y (α 0) • Pi.single u ξ) t X z v =
      c 1 α t X z v u ξ := by
  classical
  let F := fun Y : Vec 2 => Y (α 0) • Pi.single u ξ
  have hone (β : DerivativeWord2 1) :
      orderedDerivative β F X = if β 0 = α 0 then Pi.single u ξ else 0 := by
    simpa only [Pi.zero_apply, sub_zero] using!
      congrFun (orderedDerivative_one_affine β (α 0) (0 : Vec 2) (Pi.single u ξ)) X
  change (∑ m ∈ Finset.range (1 + 1), ∑ β : DerivativeWord2 m, ∑ j : ι,
    c m β t X z v j (orderedDerivative β F X j)) = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, hc0, zero_apply, Finset.sum_const_zero]
  rw [Finset.sum_eq_single α]
  · simp only [hone, ite_true]
    rw [Finset.sum_eq_single u]
    · simp
    · intro j _ hju
      rw [Pi.single_eq_of_ne hju ξ, map_zero]
    · simp
  · intro β _ hβ
    have hn : β 0 ≠ α 0 := by
      intro he
      apply hβ
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using he
    simp [hone, hn]
  · simp
end

/-! Exponential coarse inputs expose the finite polynomial symbol of the literal lift. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_exponential_single (n : ℕ) (c : LiftCoeff ι h)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u) :
    liftApply n c (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z v =
      Real.exp (A X) • ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
        ((List.ofFn α).map (fun j => A (basisVec j))).prod • c m α t X z v u ξ := by
  classical
  unfold liftApply
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [orderedDerivative_exp_linear_smul]
  rw [Finset.sum_eq_single u]
  · simp only [Pi.smul_apply, Pi.single_eq_same, map_smul, smul_smul]
    rw [mul_comm]
  · intro j _ hju
    simp only [Pi.smul_apply, Pi.single_eq_of_ne hju, smul_zero, map_zero]
  · simp
end

/-! Copy-adapt the ordered-word calculus to differentiate a left coefficient acting on a coarse jet. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem left_term_slowPartial {m : ℕ} (α : DerivativeWord2 m) (k : Fin 2)
    (c : Vec 2 → Vec 2 → E →L[ℝ] F)
    (hc : ∀ z, ContDiff ℝ 1 (fun X => c X z)) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    slowPartial k (fun X z => c X z (orderedDerivative α f X)) = fun X z =>
      slowPartial k c X z (orderedDerivative α f X) +
        c X z (orderedDerivative (Fin.snoc α k) f X) := by
  funext X z
  have hd : DifferentiableAt ℝ (fun Y => c Y z) X :=
    ((hc z).differentiable one_ne_zero) X
  have hg : DifferentiableAt ℝ (orderedDerivative α f) X :=
    ((Sampling.contDiff_orderedDerivative 1 α f (hf.of_le (by simp))).differentiable one_ne_zero) X
  rw [slowPartial, fderiv_clm_apply hd hg, Sampling.orderedDerivative_snoc]
  change c X z (fderiv ℝ (orderedDerivative α f) X (basisVec k)) +
    (fderiv ℝ (fun Y => c Y z) X (basisVec k)) (orderedDerivative α f X) = _
  exact add_comm _ _

theorem left_term_fastPartial {m : ℕ} (α : DerivativeWord2 m) (k : Fin 2)
    (c : Vec 2 → Vec 2 → E →L[ℝ] F)
    (hc : ∀ X, ContDiff ℝ 1 (c X)) (f : Vec 2 → E) :
    fastPartial k (fun X z => c X z (orderedDerivative α f X)) = fun X z =>
      fastPartial k c X z (orderedDerivative α f X) := by
  funext X z
  have hd : DifferentiableAt ℝ (c X) z :=
    ((hc X).differentiable one_ne_zero) z
  change fderiv ℝ (fun y => c X y (orderedDerivative α f X)) z (basisVec k) = _
  have he := ((ContinuousLinearMap.apply ℝ F (orderedDerivative α f X)).hasFDerivAt.comp z
    hd.hasFDerivAt).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.comp_apply, fastPartial] using
      congrArg (fun L : Vec 2 →L[ℝ] F => L (basisVec k)) he
end

/-! Finite left-coefficient terms encode the literal differential action before symmetrization. -/

section
variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure LeftTerm where
  order : ℕ
  word : DerivativeWord2 order
  coeff : Vec 2 → Vec 2 → E →L[ℝ] F

variable {E F}

def LeftTerm.apply (c : LeftTerm E F) (f : Vec 2 → E) : Vec 2 → Vec 2 → F :=
  fun X z => c.coeff X z (orderedDerivative c.word f X)

def LeftTerm.smul (c : LeftTerm E F) (a : ℝ) : LeftTerm E F :=
  ⟨c.order, c.word, fun X z => a • c.coeff X z⟩

def LeftTerm.fastDerivative (c : LeftTerm E F) (k : Fin 2) : LeftTerm E F :=
  ⟨c.order, c.word, fastPartial k c.coeff⟩

def LeftTerm.slowCoefficientDerivative (c : LeftTerm E F) (k : Fin 2) : LeftTerm E F :=
  ⟨c.order, c.word, slowPartial k c.coeff⟩

def LeftTerm.slowInputDerivative (c : LeftTerm E F) (k : Fin 2) : LeftTerm E F :=
  ⟨c.order + 1, Fin.snoc c.word k, c.coeff⟩

def leftTermsApply (l : List (LeftTerm E F)) (f : Vec 2 → E) : Vec 2 → Vec 2 → F :=
  fun X z => (l.map (fun c => c.apply f X z)).sum

theorem LeftTerm.smul_apply (c : LeftTerm E F) (a : ℝ) (f : Vec 2 → E) :
    (c.smul a).apply f = fun X z => a • c.apply f X z := rfl

theorem LeftTerm.fastDerivative_apply (c : LeftTerm E F) (k : Fin 2)
    (hc : ∀ X, ContDiff ℝ 1 (c.coeff X)) (f : Vec 2 → E) :
    (c.fastDerivative k).apply f = fastPartial k (c.apply f) :=
  (left_term_fastPartial c.word k c.coeff hc f).symm

theorem LeftTerm.slowDerivative_apply (c : LeftTerm E F) (k : Fin 2)
    (hc : ∀ z, ContDiff ℝ 1 (fun X => c.coeff X z)) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    slowPartial k (c.apply f) = fun X z =>
      (c.slowCoefficientDerivative k).apply f X z + (c.slowInputDerivative k).apply f X z :=
  left_term_slowPartial c.word k c.coeff hc f hf
end

end AVRegularity.CycleComparison.Lift
end
