-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.CovariantPolynomialMean
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
public import AVRegularity.CycleComparison.Lift.NormalizedCellB1ScaledDriftMixedGrading
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleEvolution.CellWeakForcedGapEnergy
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The top covariant coefficient is the ordinary ordered slow derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def slowListDerivative (w : List (Fin 2)) (f : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  w.foldl (fun F k => slowPartial k F) f

theorem slowListDerivative_append_singleton (w : List (Fin 2)) (k : Fin 2)
    (f : Vec 2 → Vec 2 → E) :
    slowListDerivative (w ++ [k]) f = slowPartial k (slowListDerivative w f) := by
  simp only [slowListDerivative, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem covariantListCoefficients_top (w : List (Fin 2)) (f : Vec 2 → Vec 2 → E) :
    covariantListCoefficients 1 w f w.length = slowListDerivative w f := by
  induction w using List.reverseRecOn with
  | nil => simp only [covariantListCoefficients_nil, List.length_nil, ite_true, slowListDerivative, List.foldl_nil]
  | append_singleton w k ih =>
    rw [covariantListCoefficients_append_singleton, slowListDerivative_append_singleton]
    simp only [List.length_append, List.length_singleton]
    funext X z
    simp only [covariantCoefficientStep,
      covariantListCoefficients_above_degree 1 w f (w.length + 1) (by omega),
      fastPartial_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ite_false, Nat.add_sub_cancel, ih, Real.sqrt_one, one_smul, zero_add]

theorem slowListDerivative_slice (w : List (Fin 2)) (f : Vec 2 → Vec 2 → E) (z : Vec 2) :
    (fun X => slowListDerivative w f X z) =
      w.foldl (fun g k => fun X => fderiv ℝ g X (basisVec k)) (fun X => f X z) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w k ih =>
    rw [slowListDerivative_append_singleton]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (fun X => fderiv ℝ (fun Y => slowListDerivative w f Y z) X (basisVec k)) = _
    rw [ih]

theorem slowListDerivative_word {m : ℕ} (α : DerivativeWord2 m)
    (f : Vec 2 → Vec 2 → E) (X z : Vec 2) :
    slowListDerivative (List.ofFn α) f X z = orderedDerivative α (fun Y => f Y z) X :=
  congrFun (slowListDerivative_slice (List.ofFn α) f z) X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Full polynomial source coefficients retain both fast and slow divergence terms. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D p : ℕ}

theorem source_family_coefficient_all_degrees (edge : ConstituentEdges D h) (η t : ℝ)
    (hcoeff : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} (hΦ : EpsPoly False p D Φ)
    (n : ℕ) (X z : Vec 2) :
    ((n.factorial : ℝ)⁻¹) • iteratedDeriv n
      (fun ε => sourceOp edge η ε t (Φ ε) X z) 0 =
      ∑ k : Fin 2, covariantCoefficientStep η k
        (fun i Y y => sourceFluxCoeff edge η i t Φ k Y y) n X z := by
  simpa only [sourceOp, sourceFluxCoeff] using
    covariant_flux_family_coefficient_all_degrees (p + (D - 1)) n
      (fun k ε => sourceFlux edge η ε t (Φ ε) k)
      (sourceFlux_family_epsPoly_good edge η t hcoeff hΦ) η X z
end

/-! Full polynomial source coefficients retain both fast and slow divergence terms. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D p : ℕ}

theorem source_family_coefficient (edge : ConstituentEdges D h) (η t : ℝ)
    (hcoeff : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} (hΦ : EpsPoly False p D Φ)
    (n : ℕ) (hn : n ≤ p + (D - 1) + 1) (X z : Vec 2) :
    ((n.factorial : ℝ)⁻¹) • iteratedDeriv n
      (fun ε => sourceOp edge η ε t (Φ ε) X z) 0 =
      ∑ k : Fin 2, covariantCoefficientStep η k
        (fun i Y y => sourceFluxCoeff edge η i t Φ k Y y) n X z := by
  simpa only [sourceOp, sourceFluxCoeff] using
    covariant_flux_family_coefficient (p + (D - 1)) n hn
      (fun k ε => sourceFlux edge η ε t (Φ ε) k)
      (sourceFlux_family_epsPoly_good edge η t hcoeff hΦ) η X z
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Joint regularity of the literal flux coefficients of polynomial input families. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D p : ℕ}

theorem sourceFlux_family_coefficient_good (edge : ConstituentEdges D h) (η t : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} (hΦ : EpsPoly False p D Φ)
    (k : Fin 2) (j : ℕ) : GoodField 1 (sourceFluxCoeff edge η j t Φ k) := by
  exact epsPoly_coefficient_good (sourceFlux_family_epsPoly_good edge η t hΓ hΦ k) j
end

/-! The source operator is linear on finite source-regular field sums. -/

section
variable {ι α : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem sourceOp_finset_sum_smul (edge : ConstituentEdges D h) (η ε t : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ β,
      GoodField 1 (fun X z => γ.coeff β t X z))
    (s : Finset α) (c : α → ℝ) (f : α → Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ a ∈ s, GoodField D (f a)) :
    sourceOp edge η ε t (fun X z => ∑ a ∈ s, c a • f a X z) =
      fun X z => ∑ a ∈ s, c a • sourceOp edge η ε t (f a) X z := by
  have hflux (k : Fin 2) := sourceFlux_finset_sum_smul edge η ε t s c f hf k
  have hgood (k : Fin 2) (a : α) (ha : a ∈ s) :
      GoodField 1 (sourceFlux edge η ε t (f a) k) :=
    epsPoly_good_evaluate (sourceFlux_epsPoly_good edge η t hΓ (hf a ha) k) ε
  funext X z
  simp only [sourceOp]
  simp_rw [hflux, dEps_finset_sum_smul s c _ (hgood _) η ε]
  simp only [Finset.smul_sum]
  exact Finset.sum_comm
end

/-! Exponential coarse tests determine the actual symmetric differential coefficients. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem symmetric_lift_coefficient_eq_of_exponential_tests (n m : ℕ) (hm : m ≤ n)
    (c d : LiftCoeff ι h)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (hd : ∀ β (σ : Equiv.Perm (Fin m)), d m (β ∘ σ) = d m β)
    (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u)
    (he : ∀ A : Vec 2 →L[ℝ] ℝ,
      liftApply n c (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z v =
      liftApply n d (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z v)
    (α : DerivativeWord2 m) : c m α t X z v u ξ = d m α t X z v u ξ := by
  have hf : (fun ε : ℝ => ∑ β : DerivativeWord2 m,
      ε ^ wordZeroMultiplicity β • c m β t X z v u ξ) =
      fun ε : ℝ => ∑ β : DerivativeWord2 m,
      ε ^ wordZeroMultiplicity β • d m β t X z v u ξ := by
    funext ε
    have hh := homogeneous_lift_symbol_eq_of_exponential_tests n m hm c d t X z v u ξ
      he (coordinateSymbolDirection ε)
    simpa only [wordSymbol_coordinateDirection] using hh
  have hcs : ∀ β (σ : Equiv.Perm (Fin m)),
      c m (β ∘ σ) t X z v u ξ = c m β t X z v u ξ := by
    intro β σ
    rw [hc]
  have hds : ∀ β (σ : Equiv.Perm (Fin m)),
      d m (β ∘ σ) t X z v u ξ = d m β t X z v u ξ := by
    intro β σ
    rw [hd]
  rw [← symmetric_word_coefficient_extraction (fun β => c m β t X z v u ξ) hcs α,
    ← symmetric_word_coefficient_extraction (fun β => d m β t X z v u ξ) hds α, hf]
end

/-! Finite coefficient calibration separates the spatial test scale from the tested word order. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem symmetric_lift_coefficient_scaled_calibration (n m : ℕ) (hm : m ≤ n)
    (c : LiftCoeff ι h) (lam : ℝ) (hlam : lam ≠ 0)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u) :
    (lam ^ m)⁻¹ •
      ((Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹ •
        (∑ j : Fin (m + 1), polynomialExtractionWeight m (wordZeroMultiplicity α) j •
          ∑ s : Fin (n + 1), polynomialExtractionWeight n m s •
            ((Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
              liftApply n c
                (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) • Pi.single u ξ)
                t X z v))) = c m α t X z v u ξ := by
  simp only [homogeneous_lift_symbol_scaled_finite_extraction n m hm, wordSymbol_coordinateDirection]
  have hs : ∀ β (σ : Equiv.Perm (Fin m)),
      c m (β ∘ σ) t X z v u ξ = c m β t X z v u ξ := by
    intro β σ
    rw [hc]
  have hsum : (∑ j : Fin (m + 1), polynomialExtractionWeight m (wordZeroMultiplicity α) j •
      lam ^ m • ∑ β : DerivativeWord2 m, (j : ℝ) ^ wordZeroMultiplicity β • c m β t X z v u ξ) =
      lam ^ m • ∑ j : Fin (m + 1), polynomialExtractionWeight m (wordZeroMultiplicity α) j •
        ∑ β : DerivativeWord2 m, (j : ℝ) ^ wordZeroMultiplicity β • c m β t X z v u ξ := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _
  rw [hsum]
  rw [smul_comm ((Fintype.card {β : DerivativeWord2 m //
    wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹) (lam ^ m)]
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hlam), one_smul]
  exact symmetric_word_finite_extraction _ hs α
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Every explicit covariant word coefficient retains the transverse source geometry. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariantCoefficientStep_transverse (par k : Fin 2) (I : Set ℝ) (η : ℝ)
    (P : ℕ → ℝ → Vec 2 → Vec 2 → E) (hP : ∀ j, IsTransverseOn par I (P j)) (j : ℕ) :
    IsTransverseOn par I (fun t => covariantCoefficientStep η k (fun i => P i t) j) := by
  have hfast := transverse_fastPartial par k I (P j) (hP j)
  have hslow := transverse_slowPartial par k I (P (j - 1)) (hP (j - 1))
  intro t ht X z s
  change fastPartial k (P j t) (X) (z + s • basisVec par) +
    (if j = 0 then 0 else Real.sqrt η • slowPartial k (P (j - 1) t) X (z + s • basisVec par)) = _
  have hfEq : fastPartial k (P j t) X (z + s • basisVec par) = fastPartial k (P j t) X z :=
    hfast t ht X z s
  have hsEq : slowPartial k (P (j - 1) t) X (z + s • basisVec par) =
      slowPartial k (P (j - 1) t) X z := hslow t ht X z s
  rw [hfEq]
  by_cases hj : j = 0
  · simp only [covariantCoefficientStep, hj, ite_true]
  · simp only [hj, ite_false]
    rw [hsEq]
    simp only [covariantCoefficientStep, hj, ite_false]

theorem covariantListCoefficients_transverse (par : Fin 2) (I : Set ℝ) (η : ℝ)
    (w : List (Fin 2)) (f : ℝ → Vec 2 → Vec 2 → E) (hf : IsTransverseOn par I f) :
    ∀ j, IsTransverseOn par I (fun t => covariantListCoefficients η w (f t) j) := by
  induction w using List.reverseRecOn with
  | nil =>
    intro j
    by_cases hj : j = 0
    · simpa only [covariantListCoefficients_nil, hj, ite_true] using hf
    · simp only [covariantListCoefficients_nil, hj, ite_false]
      exact transverse_slow_field par I (fun _ _ => (0 : E))
  | append_singleton w k ih =>
    intro j
    simp only [covariantListCoefficients_append_singleton]
    exact covariantCoefficientStep_transverse par k I η
      (fun i t => covariantListCoefficients η w (f t) i) ih j

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A coefficient step commutes with output maps without adding slow or fast reserve. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem covariantCoefficientStep_postcomposition (η : ℝ) (k : Fin 2)
    (P : ℕ → Vec 2 → Vec 2 → E) (j : ℕ) (L : E →L[ℝ] F)
    (hf : IsBoxSmooth 0 1 (P j)) (hs : j ≠ 0 → IsBoxSmooth 1 0 (P (j - 1)))
    (X z : Vec 2) :
    covariantCoefficientStep η k (fun i Y y => L (P i Y y)) j X z =
      L (covariantCoefficientStep η k P j X z) := by
  change fastPartial k (fun Y y => L (P j Y y)) X z +
    (if j = 0 then 0 else Real.sqrt η • slowPartial k (fun Y y => L (P (j - 1) Y y)) X z) =
    L (fastPartial k (P j) X z +
      (if j = 0 then 0 else Real.sqrt η • slowPartial k (P (j - 1)) X z))
  rw [fastPartial_postcomposition L (P j) hf]
  by_cases hj : j = 0
  · simp only [hj, ite_true, add_zero]
  · simp only [hj, ite_false, map_add, map_smul]
    rw [slowPartial_postcomposition L (P (j - 1)) (hs hj)]
end

/-! A word coefficient of degree j uses exactly j slow choices and at most the complementary fast choices. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariantListCoefficient_box_reserve (η : ℝ) (w : List (Fin 2)) :
    ∀ m p q (f : Vec 2 → Vec 2 → E), m ≤ w.length →
      IsBoxSmooth (p + m) (q + w.length - m) f →
      IsBoxSmooth p q (covariantListCoefficients η w f m) := by
  induction w using List.reverseRecOn with
  | nil =>
    intro m p q f hm hf
    have hm0 : m = 0 := by simpa using hm
    subst m
    simpa only [covariantListCoefficients_nil, ite_true, Nat.add_zero, List.length_nil,
      Nat.sub_zero] using! hf
  | append_singleton w k ih =>
    intro m p q f hm hf
    have hm' : m ≤ w.length + 1 := by simpa using hm
    rw [covariantListCoefficients_append_singleton]
    apply covariantCoefficientStep_box_reserve
    · by_cases hmw : m ≤ w.length
      · apply ih m p (q + 1) f hmw
        have hq : q + 1 + w.length - m = q + (w ++ [k]).length - m := by
          simp only [List.length_append, List.length_singleton]
          omega
        simpa only [hq] using hf
      · rw [covariantListCoefficients_above_degree η w f m (by omega)]
        exact IsBoxSmooth.zero
    · intro hm0
      apply ih (m - 1) (p + 1) q f (by omega)
      have hp : p + 1 + (m - 1) = p + m := by omega
      have hq : q + w.length - (m - 1) = q + (w ++ [k]).length - m := by
        simp only [List.length_append, List.length_singleton]
        omega
      simpa only [hp, hq] using hf
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Exact parameter coefficients of covariant divergences have the corresponding slow-flux means. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem covariant_polynomial_coefficient_mean (q j : ℕ)
    (P : Fin 2 → ℕ → Vec 2 → Vec 2 → E) (hP : ∀ k i, GoodField 1 (P k i))
    (hz : ∀ k i, q < i → ∀ X z, P k i X z = 0) (η : ℝ) (X : Vec 2) :
    fieldCellMean (fun z => ((j.factorial : ℝ)⁻¹) • iteratedDeriv j (fun ε : ℝ =>
      ∑ k : Fin 2, dEps η ε k
        (fun Y y => ∑ i ∈ Finset.range (q + 1), ε ^ i • P k i Y y) X z) 0) =
      if j = 0 then 0 else Real.sqrt η • ∑ k : Fin 2,
        fderiv ℝ (fun Y => fieldCellMean (P k (j - 1) Y)) X (basisVec k) := by
  let Φ := fun ε X z => ∑ k : Fin 2, dEps η ε k
    (fun Y y => ∑ i ∈ Finset.range (q + 1), ε ^ i • P k i Y y) X z
  let Q := fun i => Real.sqrt η • ∑ k : Fin 2,
    fderiv ℝ (fun Y => fieldCellMean (P k i Y)) X (basisVec k)
  have hp (k : Fin 2) : EpsPoly False q 1
      (fun ε Y y => ∑ i ∈ Finset.range (q + 1), ε ^ i • P k i Y y) :=
    ⟨P k, fun i => ⟨hP k i, False.elim⟩, hz k, fun _ _ _ => rfl⟩
  have hΦ : EpsPoly False (q + 1) 0 Φ :=
    EpsPoly.sum Finset.univ (fun k _ => (hp k).dEps η k)
  have he : (fun ε : ℝ => fieldCellMean (Φ ε X)) =
      fun ε => ε • (∑ i ∈ Finset.range (q + 1), ε ^ i • Q i) := by
    funext ε
    exact covariant_polynomial_divergence_mean q P hP η ε X
  have hQ : ∀ i, q < i → Q i = 0 := by
    intro i hi
    have hpi (k : Fin 2) : P k i = fun _ _ => 0 :=
      funext (fun Y => funext (fun z => hz k i hi Y z))
    dsimp only [Q]
    have hs : (∑ k : Fin 2,
        fderiv ℝ (fun Y => fieldCellMean (P k i Y)) X (basisVec k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [hpi k]
      simp [fieldCellMean]
    rw [hs, smul_zero]
  change fieldCellMean (fun z => ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
    (fun ε => Φ ε X z) 0) = if j = 0 then 0 else Q (j - 1)
  rw [epsPoly_mean_coefficient hΦ j X, he]
  exact normalized_shift_polynomial_coefficient q j Q hQ
end

/-! The degree-two diagonal mean combines the drift flux with the molecular metric flux. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem fieldCellMean_diagonal_second_cross (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j))
    (hw : ∀ q : Fin 2, ContDiff ℝ (1 : ℕ∞) (fun z => Real.sqrt η * v t z q))
    (Φ : Vec 2 → Vec 2 → E) (hΦ : GoodField 2 Φ)
    (f : Vec 2 → E) (hf : ContDiff ℝ 2 f) (X : Vec 2) :
    fieldCellMean (fun z => cellB1 η G v t Φ X z + cellB2 η G t (fun Y _ => f Y) X z) =
      ∑ q : Fin 2, fderiv ℝ (fun Y => fieldCellMean
        (fun z => (Real.sqrt η * v t z q) • Φ Y z) -
          η • ∑ j : Fin 2, G t Y q j • fderiv ℝ f Y (basisVec j)) X (basisVec q) := by
  have hcoarse : GoodField 2 (fun Y _ : Vec 2 => f Y) :=
    ⟨hf.comp contDiff_fst, fun _ _ _ => rfl⟩
  rw [AVRegularity.fieldCellMean_add
    (cellB1_continuous_slice η G v t hG (fun q => (hw q).continuous) Φ hΦ X)
    (cellB2_continuous_slice η G t hG _ hcoarse X),
    fieldCellMean_cellB1_formula η G v t hG hw Φ hΦ X,
    fieldCellMean_cellB2_independent_divergence η G t hG f hf X,
    ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have hflux : ContDiff ℝ 1 (Function.uncurry
      (fun Y z => (Real.sqrt η * v t z q) • Φ Y z)) :=
    ((hw q).comp contDiff_snd).smul (hΦ.1.of_le (by norm_num))
  have hm : DifferentiableAt ℝ (fun Y => fieldCellMean
      (fun z => (Real.sqrt η * v t z q) • Φ Y z)) X :=
    (fieldCellMean_hasFDerivAt hflux X).differentiableAt
  have hc : ContDiff ℝ 1 (fun Y => η • ∑ j : Fin 2,
      G t Y q j • fderiv ℝ f Y (basisVec j)) := by
    apply ContDiff.const_smul
    apply ContDiff.sum
    intro j _
    exact (hG q j).smul ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
  rw [fderiv_fun_sub hm (hc.differentiable one_ne_zero X)]
  simp
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! One finite coefficient-vector synthesis map realizes the existing symmetric word calibration. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def liftCalibrationWeight (n m : ℕ) (α : DerivativeWord2 m) (lam : ℝ)
    (p : Fin (m + 1) × Fin (n + 1)) : ℝ :=
  (lam ^ m)⁻¹ *
    (Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹ *
    (polynomialExtractionWeight m (wordZeroMultiplicity α) p.1 * polynomialExtractionWeight n m p.2)

theorem liftCalibration_synthesis (n m : ℕ) (hm : m ≤ n) (c : LiftCoeff ι h)
    (lam : ℝ) (hlam : lam ≠ 0)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u) :
    (∑ p : Fin (m + 1) × Fin (n + 1), liftCalibrationWeight n m α lam p •
      normalizedLiftTestField c n (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v ξ t X z) =
      c m α t X z v u ξ := by
  let T := fun (j : Fin (m + 1)) (s : Fin (n + 1)) =>
    normalizedLiftTestField c n (lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) u v ξ t X z
  let C := (lam ^ m)⁻¹ *
    (Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹
  have hs (j : Fin (m + 1)) :
      (∑ s : Fin (n + 1), liftCalibrationWeight n m α lam (j, s) • T j s) =
      C • (polynomialExtractionWeight m (wordZeroMultiplicity α) j •
        ∑ s : Fin (n + 1), polynomialExtractionWeight n m s • T j s) := by
    rw [Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [liftCalibrationWeight, C, smul_smul, mul_assoc]
  rw [Fintype.sum_prod_type]
  change (∑ j : Fin (m + 1), ∑ s : Fin (n + 1), liftCalibrationWeight n m α lam (j, s) • T j s) = _
  simp_rw [hs]
  rw [← Finset.smul_sum]
  dsimp only [C]
  rw [mul_smul]
  have he := symmetric_lift_coefficient_scaled_calibration n m hm c lam hlam hc α t X z v u ξ
  have hcomm (s : ℝ) (A : Vec 2 →L[ℝ] ℝ) : s • (lam • A) = lam • (s • A) :=
    smul_comm s lam A
  simpa only [T, normalizedLiftTestField, hcomm] using he
end

/-! Equality of the literal differential operators determines every supported symmetric coefficient. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem symmetric_lift_coefficient_eq_of_operator_eq (n m : ℕ) (hm : m ≤ n)
    (c d : LiftCoeff ι h)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (hd : ∀ β (σ : Equiv.Perm (Fin m)), d m (β ∘ σ) = d m β)
    (t : ℝ) (X z : Vec 2) (v u : ι)
    (he : ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
      liftApply n c (fun _ => a₀) t X z v = liftApply n d (fun _ => a₀) t X z v)
    (α : DerivativeWord2 m) : c m α t X z v u = d m α t X z v u := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply symmetric_lift_coefficient_eq_of_exponential_tests n m hm c d hc hd t X z v u ξ
  intro A
  apply he
  exact (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
end

/-! Explicit finite calibration of the actual centered source, with the tested slow word fixed. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def calibratedLiftSourceEntry {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ) (α : DerivativeWord2 m) (lam : ℝ)
    (u v : ι) (ξ : h u) (t : ℝ) (X z : Vec 2) : h v :=
  ∑ p : Fin (m + 1) × Fin (n + 1), liftCalibrationWeight n m α lam p •
    normalizedLiftSourceField Q Cc hh n
      (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v ξ t X z
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Positive parameter coefficients of polynomial covariant flux families have exact slow-divergence means. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem covariant_flux_family_coefficient_mean (q j : ℕ) (hj : 1 ≤ j)
    (F : Fin 2 → ℝ → Vec 2 → Vec 2 → E)
    (hF : ∀ k, EpsPoly False q 1 (F k)) (η : ℝ) (X : Vec 2) :
    fieldCellMean (fun z => ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
      (fun ε : ℝ => ∑ k : Fin 2, dEps η ε k (F k ε) X z) 0) =
      Real.sqrt η • ∑ k : Fin 2, fderiv ℝ (fun Y => fieldCellMean (fun z =>
        (((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1) (fun ε => F k ε Y z) 0)) X (basisVec k) := by
  choose P hP hz he using hF
  have hp (k : Fin 2) (ε : ℝ) : F k ε =
      fun Y z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P k i Y z :=
    funext (fun Y => funext (fun z => he k ε Y z))
  have hc (k : Fin 2) :
      (fun Y z => (((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1)
        (fun ε => F k ε Y z) 0) = P k (j - 1) := by
    funext Y z
    have hf : (fun ε => F k ε Y z) =
        fun ε => ∑ i ∈ Finset.range (q + 1), ε ^ i • P k i Y z :=
      funext (fun ε => he k ε Y z)
    rw [hf]
    exact normalized_polynomial_coefficient q (j - 1) (fun i => P k i Y z)
      (fun i hi => hz k i hi Y z)
  have hm (k : Fin 2) : (fun Y => fieldCellMean (fun z =>
      (((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1) (fun ε => F k ε Y z) 0)) =
      fun Y => fieldCellMean (P k (j - 1) Y) := by
    funext Y
    exact congrArg fieldCellMean (congrFun (hc k) Y)
  simp_rw [hm, hp]
  simpa only [ite_eq_right (show j ≠ 0 by omega)] using
    covariant_polynomial_coefficient_mean q j P (fun k i => (hP k i).1) hz η X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Centered finite exponential tests recover centered actual symmetric coefficients. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftCoefficient_applied_mean_zero_of_finite_tests (n m : ℕ) (hm : m ≤ n)
    (c : LiftCoeff ι h) (lam : ℝ) (hlam : lam ≠ 0)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (t : ℝ) (X : Vec 2) (v u : ι) (ξ : h u)
    (htest : ∀ j : Fin (m + 1), ∀ s : Fin (n + 1),
      Continuous (fun z =>
        (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
          liftApply n c
            (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) •
              Pi.single u ξ) t X z v) ∧
      fieldCellMean (fun z =>
        (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
          liftApply n c
            (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) •
              Pi.single u ξ) t X z v) = 0) :
    fieldCellMean (fun z => c m α t X z v u ξ) = 0 := by
  let T := fun (j : Fin (m + 1)) (s : Fin (n + 1)) z =>
    (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
      liftApply n c
        (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) •
          Pi.single u ξ) t X z v
  let F := fun (j : Fin (m + 1)) z => ∑ s : Fin (n + 1), polynomialExtractionWeight n m s • T j s z
  have hF (j : Fin (m + 1)) : Continuous (F j) :=
    continuous_finsetSum _ (fun s _ => continuous_const.smul (htest j s).1)
  have hmF (j : Fin (m + 1)) : fieldCellMean (F j) = 0 :=
    fieldCellMean_finset_sum_smul_zero Finset.univ (polynomialExtractionWeight n m) (T j)
      (fun s _ => (htest j s).1) (fun s _ => (htest j s).2)
  have he : (fun z => c m α t X z v u ξ) = fun z =>
      (lam ^ m)⁻¹ •
        ((Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹ •
          ∑ j : Fin (m + 1), polynomialExtractionWeight m (wordZeroMultiplicity α) j • F j z) := by
    funext z
    exact (symmetric_lift_coefficient_scaled_calibration n m hm c lam hlam hc α t X z v u ξ).symm
  rw [he, AVRegularity.fieldCellMean_smul, AVRegularity.fieldCellMean_smul,
    fieldCellMean_finset_sum_smul_zero Finset.univ _ F (fun j _ => hF j) (fun j _ => hmF j)]
  simp only [smul_zero]
end

/-! Finite exponential calibration recovers coefficient mixed bounds with scale division only by tested order. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def finiteTestCalibrationConstant (n m : ℕ) (α : DerivativeWord2 m) : ℝ :=
  |(Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹| *
    (∑ j : Fin (m + 1), |polynomialExtractionWeight m (wordZeroMultiplicity α) j| *
      ∑ s : Fin (n + 1), |polynomialExtractionWeight n m s|)

theorem finiteTestCalibrationConstant_nonneg (n m : ℕ) (α : DerivativeWord2 m) :
    0 ≤ finiteTestCalibrationConstant n m α := by
  exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun s _ => abs_nonneg _))

theorem liftCoefficient_applied_mixed_bound_of_finite_tests (p q n m : ℕ) (hm : m ≤ n)
    (c : LiftCoeff ι h) (lam : ℝ) (hlam : lam ≠ 0)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (t : ℝ) (v u : ι) (ξ : h u)
    (htest : ∀ j : Fin (m + 1), ∀ s : Fin (n + 1),
      IsBoxSmooth p q (fun X z =>
        (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
          liftApply n c
            (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) • Pi.single u ξ)
            t X z v)) (X z : Vec 2) (B : ℝ)
    (hb : ∀ j : Fin (m + 1), ∀ s : Fin (n + 1),
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
        (fun y => (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y))⁻¹ •
          liftApply n c
            (fun _ Z => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Z) • Pi.single u ξ)
            t Y y v) z) X‖ ≤ B) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun y => c m α t Y y v u ξ) z) X‖ ≤
      |(lam ^ m)⁻¹| * finiteTestCalibrationConstant n m α * B := by
  let F := fun (j : Fin (m + 1)) (s : Fin (n + 1)) X z =>
    (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
      liftApply n c
        (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) • Pi.single u ξ)
        t X z v
  let S := fun (j : Fin (m + 1)) X z => ∑ s : Fin (n + 1),
    polynomialExtractionWeight n m s • F j s X z
  let T := fun X z => ∑ j : Fin (m + 1),
    polynomialExtractionWeight m (wordZeroMultiplicity α) j • S j X z
  have hS (j : Fin (m + 1)) : IsBoxSmooth p q (S j) :=
    IsBoxSmooth.sum Finset.univ fun s _ => (htest j s).const_smul _
  have hT : IsBoxSmooth p q T := IsBoxSmooth.sum Finset.univ fun j _ => (hS j).const_smul _
  have he (Y y : Vec 2) : c m α t Y y v u ξ = (lam ^ m)⁻¹ •
      ((Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹ •
        T Y y) := (symmetric_lift_coefficient_scaled_calibration n m hm c lam hlam hc α t Y y v u ξ).symm
  simp_rw [he]
  rw [norm_mixed_jet_const_smul (hT.const_smul _), norm_mixed_jet_const_smul hT]
  have hSn (j : Fin (m + 1)) :
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (S j Y) z) X‖ ≤
        (∑ s : Fin (n + 1), |polynomialExtractionWeight n m s|) * B := by
    apply (norm_mixed_jet_finset_sum_le Finset.univ p q _
      (fun s _ => (htest j s).const_smul _) X z).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _
    rw [norm_mixed_jet_const_smul (htest j s)]
    exact mul_le_mul_of_nonneg_left (hb j s) (abs_nonneg _)
  have hTn : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (T Y) z) X‖ ≤
      (∑ j : Fin (m + 1), |polynomialExtractionWeight m (wordZeroMultiplicity α) j| *
        ∑ s : Fin (n + 1), |polynomialExtractionWeight n m s|) * B := by
    apply (norm_mixed_jet_finset_sum_le Finset.univ p q _
      (fun j _ => (hS j).const_smul _) X z).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mixed_jet_const_smul (hS j)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hSn j) (abs_nonneg _)
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hTn (abs_nonneg _)) (abs_nonneg _)).trans_eq
  dsimp only [finiteTestCalibrationConstant]
  ring
end

end AVRegularity.CycleComparison.Lift
end

section
open AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A universal finite calibration budget is fixed before families, masses, and scales. -/

def finiteLiftCalibrationBudget (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
    ∑ α : DerivativeWord2 m, finiteTestCalibrationConstant n m α

theorem finiteLiftCalibrationBudget_nonneg (N : ℕ) : 0 ≤ finiteLiftCalibrationBudget N := by
  exact Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun m _ =>
    Finset.sum_nonneg fun α _ => finiteTestCalibrationConstant_nonneg n m α

theorem finiteTestCalibrationConstant_le_budget (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ N)
    (α : DerivativeWord2 m) : finiteTestCalibrationConstant n m α ≤ finiteLiftCalibrationBudget N := by
  have hα := Finset.single_le_sum (f := fun β : DerivativeWord2 m => finiteTestCalibrationConstant n m β)
    (fun β _ => finiteTestCalibrationConstant_nonneg n m β) (Finset.mem_univ α)
  have hm' := Finset.single_le_sum
    (f := fun k => ∑ β : DerivativeWord2 k, finiteTestCalibrationConstant n k β)
    (fun k _ => Finset.sum_nonneg fun β _ => finiteTestCalibrationConstant_nonneg n k β)
    (Finset.mem_range.mpr (show m < N + 1 by omega))
  apply (hα.trans hm').trans
  unfold finiteLiftCalibrationBudget
  exact Finset.single_le_sum
    (f := fun k => ∑ i ∈ Finset.range (N + 1),
      ∑ β : DerivativeWord2 i, finiteTestCalibrationConstant k i β)
    (fun k _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun β _ => finiteTestCalibrationConstant_nonneg k i β)
    (Finset.mem_range.mpr (show n < N + 1 by omega))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite calibration has a literal source-dependent bound before inverse construction. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {Ks : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}
  (data : AmbientLiftSourceData par a b hab lam hh n p q Q Cc Ks M)

include data

theorem calibratedLiftSourceEntry_mixed_bound (m : ℕ) (α : DerivativeWord2 m)
    (u v : ι) (ξ : h u) (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t Y y) z) X‖ ≤
      (∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α lam j| *
        Ks ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) * M v u * ‖ξ‖ * lam ^ (n + r) := by
  unfold calibratedLiftSourceEntry
  apply (norm_mixed_jet_finset_sum_le Finset.univ r s _
    (fun j _ => ((data.box ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))
      u v ξ t ht).mono hr hs).const_smul _) X z).trans
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mixed_jet_const_smul
    ((data.box ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) u v ξ t ht).mono hr hs)]
  have hb := mul_le_mul_of_nonneg_left
    (data.bound ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))
      u v ξ r hr s hs t ht X z) (abs_nonneg (liftCalibrationWeight n m α lam j))
  simpa only [mul_assoc] using hb

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite source calibration preserves actual box regularity, cell geometry, and time measurability. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {Ks : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}
  (data : AmbientLiftSourceData par a b hab lam hh n p q Q Cc Ks M)

include data

theorem calibratedLiftSourceEntry_box (m : ℕ) (α : DerivativeWord2 m)
    (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (fun X z => calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z) := by
  unfold calibratedLiftSourceEntry
  exact IsBoxSmooth.sum Finset.univ fun j _ =>
    (data.box ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) u v ξ t ht).const_smul _

theorem calibratedLiftSourceEntry_transverse (m : ℕ) (α : DerivativeWord2 m)
    (u v : ι) (ξ : h u) :
    IsTransverseOn par (Set.Icc a b)
      (fun t X z => calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z) := by
  intro t ht X z s
  unfold calibratedLiftSourceEntry
  apply Finset.sum_congr rfl
  intro j _
  rw [data.transverse ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) u v ξ t ht X z s]

theorem calibratedLiftSourceEntry_periodic (m : ℕ) (α : DerivativeWord2 m)
    (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    AVenhance.IsZ2Periodic (fun z => calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z) := by
  intro k z
  unfold calibratedLiftSourceEntry
  apply Finset.sum_congr rfl
  intro j _
  rw [data.periodic ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) u v ξ t ht X k z]

theorem calibratedLiftSourceEntry_centered (m : ℕ) (α : DerivativeWord2 m)
    (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    fieldCellMean (fun z => calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z) = 0 := by
  unfold calibratedLiftSourceEntry
  apply fieldCellMean_finset_sum_zero Finset.univ
  · intro j _
    exact (((data.box ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) u v ξ t ht).1 X).continuous).const_smul _
  · intro j _
    rw [fieldCellMean_smul,
      data.centered ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) u v ξ t ht X, smul_zero]

theorem calibratedLiftSourceEntry_dual_measurable (m : ℕ) (α : DerivativeWord2 m)
    (u v : ι) (ξ : h u) (l : h v →L[ℝ] ℝ) (X z : Vec 2) :
    Measurable (fun t => l (calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ
      (Set.projIcc a b hab t) X z)) := by
  simp only [calibratedLiftSourceEntry, map_sum, map_smul]
  apply Finset.measurable_sum
  intro j _
  simpa only [Pi.smul_apply] using!
    (data.measurable ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) u v ξ l X z).const_smul
      (liftCalibrationWeight n m α lam j)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Every actual cell solution on a finite closed window has finite energy norm `cellEnergyNorm`. -/

theorem cellSolution_compact_energy_finite (a b : ℝ) (hab : a ≤ b)
    (C : CellCoefficients) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) C src F D) : cellEnergyNorm (Icc a b) D < ⊤ := by
  have hc := cellRawTrace_continuous (Icc a b) D
    (fun t ht => (hD.2.2.1 t ht).1) hD.2.2.2.2.1
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hs : (⨆ t ∈ Icc a b, cellL2Norm (cellValue D t)) ≤ ENNReal.ofReal R := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    rw [cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D t (hD.2.2.1 t ht).1)]
    exact ENNReal.ofReal_le_ofReal (hR t ht)
  have hv : (⨆ t ∈ Icc a b, cellL2Norm (cellValue D t)) < ⊤ :=
    hs.trans_lt ENNReal.ofReal_lt_top
  have hg := hD.2.2.2.2.2.1 a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩
  have hb := cellUlNorm_le_totalEnergy (Icc a b) (fun t => cellGradient (D t))
    (∫⁻ t in Icc a b, cellL2Norm (cellGradient (D t)) ^ 2) le_rfl
  have hgrad : cellUlNorm (Icc a b) (fun t => cellGradient (D t)) < ⊤ :=
    hb.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg.ne)
  exact ENNReal.add_lt_top.mpr ⟨hv, hgrad⟩

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The classical transverse Fourier modes as genuine periodic H¹ states and weak Hilbert curves. -/

def transverseFourierModeH1 (par : Fin 2) (n : ℤ) : TorusHk 1 ℂ :=
  (TorusHkFunction.mk (classicalCellJet (transverseFourierMode par n))
    (classicalCellJet_periodicWeak _
      ((transverseFourierMode_contDiff par n).of_le (by simp))
      (transverseFourierMode_periodic par n))).toHk

theorem transverseFourierMode_scalar_curve {a b : ℝ} (hab : a ≤ b)
    (par : Fin 2) (n : ℤ) (c dc : ℝ → ℂ)
    (hc : StrongTimeRegularity a b c dc)
    (hdc : MemLp dc ⊤ (volume.restrict (Icc a b))) :
    CellWeakHilbertCurve a b
      (fun t => cellScalarCLM (c t) (torusHkValueCLM (transverseFourierModeH1 par n)))
      (fun t => cellH1Scalar (c t) (transverseFourierModeH1 par n))
      (fun t => cellPivotDualCLM
        (cellScalarCLM (dc t) (torusHkValueCLM (transverseFourierModeH1 par n)))) := by
  have h := (cellWeakHilbert_constant a b (transverseFourierModeH1 par n)).variable_complex_scalar
    hab c dc hc hdc
  simpa only [← cellH1ScalarCLM_apply, map_zero, zero_add] using h

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The promoted Fourier state retains its literal value and classical first derivatives. -/

theorem transverseFourierModeH1_jet_ae (par : Fin 2) (n : ℤ) (a : JetIndex2 1) :
    (transverseFourierModeH1 par n).val a =ᵐ[volume.restrict AVenhance.unitCube]
      classicalCellJet (transverseFourierMode par n) a := by
  exact torusJetToL2_ae _ _ a

theorem transverseFourierModeH1_value_ae (par : Fin 2) (n : ℤ) :
    torusHkValueCLM (transverseFourierModeH1 par n) =ᵐ[volume.restrict AVenhance.unitCube]
      transverseFourierMode par n := by
  simpa only [classicalCellJet, valueIndex2, valueIndex, Fin.val_zero, lt_self_iff_false,
    dite_false] using! transverseFourierModeH1_jet_ae par n (valueIndex2 1)

theorem transverseFourierModeH1_derivative_ae (par : Fin 2) (n : ℤ) (j : Fin 2) :
    cellDerivativeCLM j (transverseFourierModeH1 par n) =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => if j = par.rev then profileFourierFrequency n * transverseFourierMode par n z else 0 := by
  have h := transverseFourierModeH1_jet_ae par n ⟨⟨1, by decide⟩, fun _ => j⟩
  filter_upwards [h] with z hz
  change (cellDerivativeCLM j) (transverseFourierModeH1 par n) z =
    classicalCellJet (transverseFourierMode par n) ⟨⟨1, by decide⟩, fun _ => j⟩ z at hz
  rw [hz]
  simp only [classicalCellJet, zero_lt_one, dite_true]
  change fderiv ℝ (fun y : Vec 2 => fourier n (y par.rev : AddCircle (1 : ℝ))) z (basisVec j) = _
  rw [fderiv_profile_basis _ ((profileFourier_character_contDiff n).differentiable (by simp)),
    profileFourier_character_deriv]
  rfl

end AVRegularity.CycleComparison.Lift
end
