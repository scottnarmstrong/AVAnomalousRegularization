-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.NormalizedCellB1ScaledDriftMixedGrading
public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
public import AVRegularity.CycleComparison.Lift.SourceZeroMean
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ordered covariant words preserve finite linear combinations at their exact reserve. -/

variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariant_foldl_finset_sum_smul (η ε : ℝ) (w : List (Fin 2))
    (s : Finset α) (c : α → ℝ) (f : α → Vec 2 → Vec 2 → E)
    (hf : ∀ a ∈ s, GoodField w.length (f a)) :
    w.foldl (fun g i => dEps η ε i g) (fun X z => ∑ a ∈ s, c a • f a X z) =
      fun X z => ∑ a ∈ s, c a • w.foldl (fun g i => dEps η ε i g) (f a) X z := by
  induction w generalizing f with
  | nil => rfl
  | cons i w ih =>
    have h1 : ∀ a ∈ s, GoodField 1 (f a) := fun a ha => (hf a ha).mono (by simp)
    have hnext : ∀ a ∈ s, GoodField w.length (dEps η ε i (f a)) := by
      intro a ha
      apply goodField_dEps
      simpa only [List.length_cons] using hf a ha
    simp only [List.foldl_cons]
    rw [dEps_finset_sum_smul s c f h1 η ε i]
    exact ih (fun a => dEps η ε i (f a)) hnext

theorem dEpsWord_finset_sum_smul {m : ℕ} (β : DerivativeWord2 m)
    (s : Finset α) (c : α → ℝ) (f : α → Vec 2 → Vec 2 → E)
    (hf : ∀ a ∈ s, GoodField m (f a)) (η ε : ℝ) :
    dEpsWord η ε β (fun X z => ∑ a ∈ s, c a • f a X z) =
      fun X z => ∑ a ∈ s, c a • dEpsWord η ε β (f a) X z := by
  exact covariant_foldl_finset_sum_smul η ε (List.ofFn β) s c f
    (fun a ha => by simpa only [List.length_ofFn] using hf a ha)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A finite parameter polynomial is reconstructed from its actual normalized derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem epsPoly_taylor {c : Prop} {q r : ℕ} {Ψ : ℝ → Vec 2 → Vec 2 → E}
    (hΨ : EpsPoly c q r Ψ) (ε : ℝ) (X z : Vec 2) :
    Ψ ε X z = ∑ n ∈ Finset.range (q + 1), ε ^ n •
      (((n.factorial : ℝ)⁻¹) • iteratedDeriv n (fun δ => Ψ δ X z) 0) := by
  obtain ⟨P, _, hz, he⟩ := hΨ
  have hfun : (fun δ => Ψ δ X z) =
      fun δ => ∑ n ∈ Finset.range (q + 1), δ ^ n • P n X z := funext (fun δ => he δ X z)
  rw [he ε X z]
  apply Finset.sum_congr rfl
  intro n _
  rw [hfun, normalized_polynomial_coefficient q n (fun j => P j X z)
    (fun j hj => hz j hj X z)]

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Finite input support turns the diagonal degree test into the usual convolution index. -/

variable {E : Type*} [AddCommMonoid E]

theorem finite_convolution_index (N j l : ℕ) (A : ℕ → E)
    (hz : ∀ i, N < i → A i = 0) :
    (∑ i ∈ Finset.range (N + 1), if j = i + l then A i else 0) =
      if l ≤ j then A (j - l) else 0 := by
  by_cases hl : l ≤ j
  · have he (i : ℕ) : (j = i + l) ↔ i = j - l := by omega
    simp_rw [he]
    simp only [Finset.sum_ite_eq', Finset.mem_range, ite_eq_left hl]
    by_cases hi : j - l < N + 1
    · exact ite_eq_left hi
    · rw [ite_eq_right hi, hz (j - l) (by omega)]
  · rw [ite_eq_right hl]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (by omega : j ≠ i + l)]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A finite calibration-direction budget is fixed before the family, masses, and scales. -/

def finiteLiftTestDirectionBudget (N : ℕ) (K : (Vec 2 →L[ℝ] ℝ) → ℝ) : ℝ :=
  ∑ s ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
    max (K ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) 0

theorem finiteLiftTestDirectionBudget_nonneg (N : ℕ) (K : (Vec 2 →L[ℝ] ℝ) → ℝ) :
    0 ≤ finiteLiftTestDirectionBudget N K :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem finiteLiftTestDirectionBudget_entry_le (N s j : ℕ) (hs : s ≤ N) (hj : j ≤ N)
    (K : (Vec 2 →L[ℝ] ℝ) → ℝ) :
    K ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ≤ finiteLiftTestDirectionBudget N K := by
  apply (le_max_left _ 0).trans
  apply (Finset.single_le_sum (s := Finset.range (N + 1)) (a := j) (fun j _ => le_max_right
    (K ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) 0)
    (Finset.mem_range.mpr (by omega))).trans
  unfold finiteLiftTestDirectionBudget
  exact Finset.single_le_sum (s := Finset.range (N + 1)) (a := s)
    (f := fun s : ℕ => ∑ j ∈ Finset.range (N + 1),
      max (K ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) 0) (fun s _ => Finset.sum_nonneg fun j _ =>
    le_max_right (K ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) 0)
    (Finset.mem_range.mpr (by omega))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! The first source coefficient on a coarse input is centered by cell periodicity. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem slowSourceFluxOrder_periodic (edge : ConstituentEdges D h) (η t : ℝ)
    (f : Vec 2 → ∀ i, h i) (d : Finset.Icc 2 D) (q : Fin 2) (X : Vec 2) :
    AVenhance.IsZ2Periodic (slowSourceFluxOrder edge η t f d q X) := by
  intro n z
  funext v
  simp only [slowSourceFluxOrder]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply List.map_congr_left
  intro γ _
  apply Finset.sum_congr rfl
  intro α _
  rw [γ.periodic α t X n z]

variable [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]

theorem fieldCellMean_sourceCoeff_one_independent (edge : ConstituentEdges D h) (η t : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (D : ℕ∞) f)
    (hfast : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X, ContDiff ℝ 1 (γ.coeff α t X))
    (hslow : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ 1 (fun X => γ.coeff α t X z)) (X : Vec 2) :
    fieldCellMean (fun z => sourceCoeff edge η 1 t (fun X _ => f X) X z) = 0 := by
  have hflux (d : Finset.Icc 2 D) (q : Fin 2) :=
    slowSourceFluxOrder_fast_contDiff edge η t f d q X
      (fun v u γ hγ α => hfast v u d γ hγ α X)
  have hi (d : Finset.Icc 2 D) (q : Fin 2) : IntegrableOn
      (fun z => fastPartial q (slowSourceFluxOrder edge η t f d q) X z) (unitCell 2) :=
    Calculus.continuous_integrableOn_unitCell
      (((hflux d q).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hsum (d : Finset.Icc 2 D) : Continuous
      (fun z => ∑ q : Fin 2, fastPartial q (slowSourceFluxOrder edge η t f d q) X z) := by
    apply continuous_finsetSum
    intro q _
    exact ((hflux d q).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hiTerm (d : Finset.Icc 2 D) : IntegrableOn (fun z =>
      if d.1 = 2 then ∑ q : Fin 2, fastPartial q (slowSourceFluxOrder edge η t f d q) X z
        else 0) (unitCell 2) := by
    by_cases hd : d.1 = 2
    · simpa only [ite_eq_left hd] using Calculus.continuous_integrableOn_unitCell (hsum d)
    · simp only [ite_eq_right hd]
      exact integrable_zero _ _ _
  have he := funext (sourceCoeff_one_independent edge η t f hf hfast hslow X)
  unfold fieldCellMean
  rw [he, ← integral_unitCell_eq_unitCube, integral_finsetSum _ (fun d _ => hiTerm d)]
  apply Finset.sum_eq_zero
  intro d _
  by_cases hd : d.1 = 2
  · simp only [ite_eq_left hd]
    rw [integral_finsetSum _ (fun q _ => hi d q)]
    apply Finset.sum_eq_zero
    intro q _
    have hm := fieldCellMean_fastPartial_eq_zero (slowSourceFluxOrder edge η t f d q X)
      (hflux d q) (slowSourceFluxOrder_periodic edge η t f d q X) q
    simpa only [fieldCellMean, fastPartial, ← integral_unitCell_eq_unitCube] using hm
  · simp only [ite_eq_right hd, integral_zero]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The mean of a periodic covariant flux divergence is its slow divergence. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem fieldCellMean_covariant_divergence (η ε : ℝ)
    (F : Fin 2 → Vec 2 → Vec 2 → E) (hF : ∀ q, GoodField 1 (F q)) (X : Vec 2) :
    fieldCellMean (fun z => ∑ q : Fin 2, dEps η ε q (F q) X z) =
      ∑ q : Fin 2, (Real.sqrt η * ε) •
        fderiv ℝ (fun Y => fieldCellMean (F q Y)) X (basisVec q) := by
  have hc (q : Fin 2) : Continuous (fun z => dEps η ε q (F q) X z) := by
    have hs : Continuous (fun z => (Real.sqrt η * ε) • slowPartial q (F q) X z) := by
      simpa using! continuous_const.smul (((hF q).slowPartial (r := 0) q).continuous_slice X)
    exact ((hF q).fastPartial (r := 0) q).continuous_slice X |>.add hs
  rw [AVRegularity.fieldCellMean_sum Finset.univ (fun q _ => hc q)]
  exact Finset.sum_congr rfl (fun q _ => fieldCellMean_dEps η ε q (F q) (hF q) X)

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! A single monomial contributes only at its exact parameter degree. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalized_monomial_coefficient (j d : ℕ) (c : E) :
    ((j.factorial : ℝ)⁻¹) • iteratedDeriv j (fun ε : ℝ => ε ^ d • c) 0 =
      if j = d then c else 0 := by
  rw [iteratedDeriv_smul_const (contDiff_id.pow d).contDiffAt c, iteratedDeriv_fun_pow_zero]
  by_cases h : j = d
  · subst d
    simp [Nat.factorial_ne_zero]
  · simp [h]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Averaging commutes with parameter coefficient extraction for finite good-field polynomials. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polynomial_field_mean_expand (q : ℕ) (P : ℕ → Vec 2 → Vec 2 → E)
    (hP : ∀ i, GoodField 0 (P i)) (ε : ℝ) (X : Vec 2) :
    fieldCellMean (fun z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z) =
      ∑ i ∈ Finset.range (q + 1), ε ^ i • fieldCellMean (P i X) := by
  have hc (i : ℕ) : Continuous (fun z => ε ^ i • P i X z) := by
    simpa using! continuous_const.smul ((hP i).continuous_slice X)
  rw [AVRegularity.fieldCellMean_sum (Finset.range (q + 1)) (fun i _ => hc i)]
  exact Finset.sum_congr rfl (fun i _ => AVRegularity.fieldCellMean_smul (ε ^ i) (P i X))

theorem polynomial_mean_coefficient (q j : ℕ) (P : ℕ → Vec 2 → Vec 2 → E)
    (hP : ∀ i, GoodField 0 (P i)) (hz : ∀ i, q < i → ∀ X z, P i X z = 0)
    (X : Vec 2) :
    fieldCellMean (fun z => ((j.factorial : ℝ)⁻¹) •
      iteratedDeriv j (fun ε : ℝ => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z) 0) =
      ((j.factorial : ℝ)⁻¹) • iteratedDeriv j (fun ε : ℝ =>
        fieldCellMean (fun z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z)) 0 := by
  have he : (fun z => ((j.factorial : ℝ)⁻¹) •
      iteratedDeriv j (fun ε : ℝ => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z) 0) = P j X := by
    funext z
    exact normalized_polynomial_coefficient q j (fun i => P i X z) (fun i hi => hz i hi X z)
  rw [he]
  have hm : (fun ε : ℝ => fieldCellMean
      (fun z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z)) =
      fun ε => ∑ i ∈ Finset.range (q + 1), ε ^ i • fieldCellMean (P i X) :=
    funext (fun ε => polynomial_field_mean_expand q P hP ε X)
  rw [hm, normalized_polynomial_coefficient q j (fun i => fieldCellMean (P i X))]
  intro i hi
  have hp : P i X = 0 := funext (fun z => hz i hi X z)
  rw [hp]
  exact AVRegularity.fieldCellMean_zero

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Multiplication by the parameter shifts a finite polynomial's normalized coefficients by one. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem parameter_mul_polynomial_expand (q : ℕ) (P : ℕ → E) (ε : ℝ) :
    ε • (∑ i ∈ Finset.range (q + 1), ε ^ i • P i) =
      ∑ i ∈ Finset.range ((q + 1) + 1), ε ^ i • (if i = 0 then 0 else P (i - 1)) := by
  conv_rhs => rw [Finset.sum_range_succ']
  rw [Finset.smul_sum]
  simp only [Nat.add_one_ne_zero, ite_false, ite_true, smul_zero, add_zero, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, pow_succ]
  congr 1
  exact mul_comm _ _

theorem normalized_shift_polynomial_coefficient (q j : ℕ) (P : ℕ → E)
    (hz : ∀ i, q < i → P i = 0) :
    ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
      (fun ε : ℝ => ε • (∑ i ∈ Finset.range (q + 1), ε ^ i • P i)) 0 =
      if j = 0 then 0 else P (j - 1) := by
  have he : (fun ε : ℝ => ε • (∑ i ∈ Finset.range (q + 1), ε ^ i • P i)) =
      fun ε => ∑ i ∈ Finset.range ((q + 1) + 1), ε ^ i • (if i = 0 then 0 else P (i - 1)) :=
    funext (fun ε => parameter_mul_polynomial_expand q P ε)
  rw [he]
  apply normalized_polynomial_coefficient (q + 1) j
  intro i hi
  rw [ite_eq_right (show i ≠ 0 by omega), hz (i - 1) (by omega)]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Source flux polynomials have good periodic coefficients even during active pulses. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem sourceTerm_epsPoly_good {d : ℕ} (hd : 2 ≤ d) (hdD : d ≤ D) (η t : ℝ) {u v : ι}
    (γ : Constituent d (h u) (h v)) (α : DerivativeWord2 (d - 1))
    (hcoeff : GoodField 1 (fun X z => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : GoodField D Φ) (k : Fin 2) :
    EpsPoly False (D - 1) 1 (fun ε X z =>
      γ.coeff α t X z k • γ.map (dEpsWord η ε α Φ X z u)) := by
  have hw : EpsPoly False (0 + (d - 1)) 1 (fun ε => dEpsWord η ε α Φ) :=
    EpsPoly.dEpsWord η α (EpsPoly.const ⟨hΦ.mono (by omega), False.elim⟩)
  have hw' : EpsPoly False (D - 1) 1 (fun ε => dEpsWord η ε α Φ) :=
    hw.mono_deg (by omega)
  have hl := hw'.clm (γ.map.comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u))
  have hg := hcoeff.clm (ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using!
    epsPoly_smul_field hg hl

theorem sourceFlux_epsPoly_good (edge : ConstituentEdges D h) (η t : ℝ)
    (hcoeff : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : GoodField D Φ) (k : Fin 2) :
    EpsPoly False (D - 1) 1 (fun ε => sourceFlux edge η ε t Φ k) := by
  refine EpsPoly.of_forall_apply (ι := ι) (h := h) (Ψ := fun ε => sourceFlux edge η ε t Φ k) fun v => ?_
  simp only [sourceFlux]
  refine EpsPoly.sum _ fun u _ => EpsPoly.sum _ fun d _ => EpsPoly.list_sum _ fun γ hγ =>
    EpsPoly.sum _ fun α _ => ?_
  have hd := Finset.mem_Icc.mp d.2
  exact sourceTerm_epsPoly_good hd.1 hd.2 η t γ α (hcoeff v u d γ hγ α) hΦ k
end

/-! Each covariant coefficient either differentiates fast at the same degree or differentiates slow at the preceding degree. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def covariantCoefficientStep (η : ℝ) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → E) :
    ℕ → Vec 2 → Vec 2 → E := fun i X z =>
  fastPartial k (P i) X z +
    if i = 0 then 0 else Real.sqrt η • slowPartial k (P (i - 1)) X z
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Reuse the centered cross-operator algebra to isolate the exact mean drift divergence at every pulse time. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem fieldCellMean_cellB1_formula (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G t X i j))
    (hw : ∀ q : Fin 2, ContDiff ℝ (1 : ℕ∞) (fun z => Real.sqrt η * v t z q))
    (Φ : Vec 2 → Vec 2 → E) (hΦ : GoodField 2 Φ) (X : Vec 2) :
    fieldCellMean (fun z => cellB1 η G v t Φ X z) =
      ∑ q : Fin 2, fderiv ℝ (fun Y => fieldCellMean
        (fun z => (Real.sqrt η * v t z q) • Φ Y z)) X (basisVec q) := by
  let w := fun q z => Real.sqrt η * v t z q
  have hzero := cellB1_centField η G (fun _ _ => 0) t hG (by simp) hΦ
  have hslow (q : Fin 2) : Continuous (slowPartial q Φ X) :=
    (hΦ.slowPartial (r := 1) q).continuous_slice X
  have hdrift : Continuous (fun z => ∑ q : Fin 2, w q z • slowPartial q Φ X z) :=
    continuous_finsetSum _ (fun q _ => (hw q).continuous.smul (hslow q))
  have he : (fun z => cellB1 η G v t Φ X z) =
      fun z => (∑ q : Fin 2, w q z • slowPartial q Φ X z) +
        cellB1 η G (fun _ _ => 0) t Φ X z := by
    funext z
    simp only [cellB1, w, Pi.zero_apply, mul_zero, zero_smul, Finset.sum_const_zero, zero_sub]
    abel
  rw [he, AVRegularity.fieldCellMean_add hdrift (hzero.1.continuous_slice X),
    hzero.2 trivial X, add_zero]
  rw [AVRegularity.fieldCellMean_sum (f := fun q z => w q z • slowPartial q Φ X z)
    Finset.univ (fun q _ => (hw q).continuous.smul (hslow q))]
  apply Finset.sum_congr rfl
  intro q _
  have hflux : ContDiff ℝ 1 (Function.uncurry (fun Y z => w q z • Φ Y z)) :=
    ((hw q).comp contDiff_snd).smul (hΦ.1.of_le (by norm_num))
  have hp : (fun z => w q z • slowPartial q Φ X z) =
      fun z => slowPartial q (fun Y y => w q y • Φ Y y) X z := by
    funext z
    symm
    change fderiv ℝ (w q z • (fun Y => Φ Y z)) X (basisVec q) = _
    rw [congrFun (fderiv_const_smul_field (w q z)) X]
    rfl
  rw [hp, AVRegularity.fieldCellMean_slowPartial hflux X q]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Good polynomial families admit evaluation and coefficientwise cell averaging. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem epsPoly_good_evaluate {c : Prop} {q r : ℕ} {Ψ : ℝ → Vec 2 → Vec 2 → E}
    (hΨ : EpsPoly c q r Ψ) (ε : ℝ) : GoodField r (Ψ ε) := by
  obtain ⟨P, hP, _, he⟩ := hΨ
  have hp : Ψ ε = fun X z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z :=
    funext (fun X => funext (fun z => he ε X z))
  rw [hp]
  exact GoodField.sum _ (fun i _ => (hP i).1.smul (ε ^ i))

theorem epsPoly_mean_coefficient {c : Prop} {q r : ℕ} {Ψ : ℝ → Vec 2 → Vec 2 → E}
    (hΨ : EpsPoly c q r Ψ) (j : ℕ) (X : Vec 2) :
    fieldCellMean (fun z => ((j.factorial : ℝ)⁻¹) • iteratedDeriv j (fun ε => Ψ ε X z) 0) =
      ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
        (fun ε => fieldCellMean (fun z => Ψ ε X z)) 0 := by
  obtain ⟨P, hP, hz, he⟩ := hΨ
  have hp : Ψ = fun ε X z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z :=
    funext (fun ε => funext (fun Y => funext (fun z => he ε Y z)))
  rw [hp]
  exact polynomial_mean_coefficient q j P (fun i => (hP i).1.mono (Nat.zero_le r)) hz X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Every homogeneous symbol is a fixed finite combination of actual coarse-test outputs. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem homogeneous_lift_symbol_finite_extraction (n m : ℕ) (hm : m ≤ n)
    (c : LiftCoeff ι h) (A : Vec 2 →L[ℝ] ℝ)
    (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u) :
    (∑ j : Fin (n + 1), polynomialExtractionWeight n m j •
      ((Real.exp (((j : ℝ) • A) X))⁻¹ •
        liftApply n c (fun _ Y => Real.exp (((j : ℝ) • A) Y) • Pi.single u ξ) t X z v)) =
      ∑ α : DerivativeWord2 m,
        ((List.ofFn α).map (fun k => A (basisVec k))).prod • c m α t X z v u ξ := by
  simp only [normalized_exponential_lift_polynomial]
  exact finite_polynomial_coefficient_interpolation n m hm
    (fun i => ∑ α : DerivativeWord2 i,
      ((List.ofFn α).map (fun k => A (basisVec k))).prod • c i α t X z v u ξ)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The positive-degree polynomial is exactly the lift minus its prescribed initial carrier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D N H : ℕ} {Q : LiftOperatorData ι h D} {a b : ℝ}

theorem setting_liftPoly_positive_degrees
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    (∑ n ∈ Finset.Icc 1 N, ε ^ n • liftApply n (Cc hh n) (fun _ => f) t X z) =
      liftPolyField Cc N ε hh (fun _ => f) t X z - (if hh = 0 then f X else 0) := by
  classical
  have hz : liftApply 0 (Cc hh 0) (fun _ => f) t X z = if hh = 0 then f X else 0 := by
    by_cases hh0 : hh = 0
    · subst hh
      simpa only [ite_true] using hseq.1 f hf t ht X z
    · simp only [ite_eq_right hh0]
      have he := liftApply_positive_grade_zero_degree Q sX sZ a b N H Cc hseq
        hh (by omega) hhh (fun _ => f)
      exact congrFun (congrFun (congrFun he t) X) z
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnot : 0 ∉ Finset.Icc 1 N := by simp
  unfold liftPolyField
  rw [hrange, Finset.sum_insert hnot, pow_zero, one_smul, hz]
  abel

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Source fluxes of polynomial input families remain polynomial at active times. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D p : ℕ}

theorem sourceTerm_family_epsPoly_good {d : ℕ} (hd : 2 ≤ d) (hdD : d ≤ D) (η t : ℝ) {u v : ι}
    (γ : Constituent d (h u) (h v)) (α : DerivativeWord2 (d - 1))
    (hcoeff : GoodField 1 (fun X z => γ.coeff α t X z))
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} (hΦ : EpsPoly False p D Φ) (k : Fin 2) :
    EpsPoly False (p + (D - 1)) 1 (fun ε X z =>
      γ.coeff α t X z k • γ.map (dEpsWord η ε α (Φ ε) X z u)) := by
  have hw : EpsPoly False (p + (d - 1)) 1 (fun ε => dEpsWord η ε α (Φ ε)) :=
    EpsPoly.dEpsWord η α (hΦ.mono_reg (by omega))
  have hw' : EpsPoly False (p + (D - 1)) 1 (fun ε => dEpsWord η ε α (Φ ε)) :=
    hw.mono_deg (by omega)
  have hl := hw'.clm (γ.map.comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u))
  have hg := hcoeff.clm (ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using!
    epsPoly_smul_field hg hl

theorem sourceFlux_family_epsPoly_good (edge : ConstituentEdges D h) (η t : ℝ)
    (hcoeff : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} (hΦ : EpsPoly False p D Φ) (k : Fin 2) :
    EpsPoly False (p + (D - 1)) 1 (fun ε => sourceFlux edge η ε t (Φ ε) k) := by
  refine EpsPoly.of_forall_apply (ι := ι) (h := h) (Ψ := fun ε => sourceFlux edge η ε t (Φ ε) k) fun v => ?_
  simp only [sourceFlux]
  refine EpsPoly.sum _ fun u _ => EpsPoly.sum _ fun d _ => EpsPoly.list_sum _ fun γ hγ =>
    EpsPoly.sum _ fun α _ => ?_
  have hd := Finset.mem_Icc.mp d.2
  exact sourceTerm_family_epsPoly_good hd.1 hd.2 η t γ α (hcoeff v u d γ hγ α) hΦ k
end

/-! Copy-adapt the finite source-flux interchange for arbitrary smooth input sums. -/

section
variable {ι α : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFlux_finset_sum_smul (edge : ConstituentEdges D h) (η ε t : ℝ)
    (s : Finset α) (c : α → ℝ) (f : α → Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ a ∈ s, GoodField D (f a)) (k : Fin 2) :
    sourceFlux edge η ε t (fun X z => ∑ a ∈ s, c a • f a X z) k =
      fun X z => ∑ a ∈ s, c a • sourceFlux edge η ε t (f a) k X z := by
  funext X z v
  have hw (d : Finset.Icc 2 D) (β : DerivativeWord2 (d.val - 1)) :
      dEpsWord η ε β (fun Y y => ∑ a ∈ s, c a • f a Y y) =
        fun Y y => ∑ a ∈ s, c a • dEpsWord η ε β (f a) Y y :=
    dEpsWord_finset_sum_smul β s c f
      (fun a ha => (hf a ha).mono (by have hd := (Finset.mem_Icc.mp d.2).2; omega)) η ε
  simp only [sourceFlux, Finset.sum_apply, Pi.smul_apply]
  simp_rw [hw]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul,
    Finset.smul_sum, List.smul_sum, List.map_map, Function.comp_def]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have hcomm (l : List (Constituent d.val (h u) (h v)))
      (g : Constituent d.val (h u) (h v) → α → h v) :
      (l.map fun γ => ∑ a ∈ s, g γ a).sum = ∑ a ∈ s, (l.map fun γ => g γ a).sum := by
    induction l with
    | nil => simp
    | cons γ l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  have hγ : ∀ γ ∈ edge v u d,
      (∑ β : DerivativeWord2 (d.val - 1), ∑ a ∈ s,
        γ.coeff β t X z k • (c a • γ.map (dEpsWord η ε β (f a) X z u))) =
      ∑ a ∈ s, ∑ β : DerivativeWord2 (d.val - 1),
        c a • (γ.coeff β t X z k • γ.map (dEpsWord η ε β (f a) X z u)) := by
    intro γ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro β _
    exact smul_comm (γ.coeff β t X z k) (c a) _
  rw [List.map_congr_left hγ]
  exact hcomm (edge v u d) _
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Copy-adapt the existing polynomial mean calculation before taking a cell mean. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariant_flux_family_coefficient (q n : ℕ) (hn : n ≤ q + 1)
    (F : Fin 2 → ℝ → Vec 2 → Vec 2 → E) (hF : ∀ k, EpsPoly False q 1 (F k))
    (η : ℝ) (X z : Vec 2) :
    ((n.factorial : ℝ)⁻¹) • iteratedDeriv n
      (fun ε => ∑ k : Fin 2, dEps η ε k (F k ε) X z) 0 =
      ∑ k : Fin 2, covariantCoefficientStep η k
        (fun i Y y => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i (fun ε => F k ε Y y) 0) n X z := by
  choose P hP hz he using hF
  have hp (k : Fin 2) (ε : ℝ) : F k ε =
      fun Y y => ∑ i ∈ Finset.range (q + 1), ε ^ i • P k i Y y :=
    funext (fun Y => funext (fun y => he k ε Y y))
  have hc (k : Fin 2) (i : ℕ) :
      (fun Y y => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i (fun ε => F k ε Y y) 0) = P k i := by
    funext Y y
    have hpoly : (fun ε => F k ε Y y) = fun ε =>
        ∑ j ∈ Finset.range (q + 1), ε ^ j • P k j Y y :=
      funext (fun ε => he k ε Y y)
    rw [hpoly]
    exact normalized_polynomial_coefficient q i (fun j => P k j Y y) (fun j hj => hz k j hj Y y)
  have hstep (k : Fin 2) (ε : ℝ) : dEps η ε k (F k ε) X z =
      ∑ i ∈ Finset.range ((q + 1) + 1), ε ^ i • covariantCoefficientStep η k (P k) i X z := by
    rw [hp]
    simpa only [covariantCoefficientStep, Nat.add_assoc] using
      dEps_finite_polynomial_expand q (P k) (fun i => (hP k i).1)
        (fun i hi => funext (fun Y => funext (fun y => hz k i hi Y y))) η ε k X z
  have hpoly : (fun ε => ∑ k : Fin 2, dEps η ε k (F k ε) X z) =
      fun ε => ∑ i ∈ Finset.range ((q + 1) + 1), ε ^ i •
        ∑ k : Fin 2, covariantCoefficientStep η k (P k) i X z := by
    funext ε
    simp_rw [hstep]
    rw [Finset.sum_comm]
    simp only [Finset.smul_sum]
  rw [hpoly, iteratedDeriv_epsPoly]
  simp only [hn, ite_true, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]
  congr 1
  funext k
  have hcoeff : (fun i Y y => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i
      (fun ε => F k ε Y y) 0) = P k := funext (fun i => hc k i)
  rw [hcoeff]
end

/-! Copy-adapt the existing polynomial mean calculation before taking a cell mean. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariant_flux_family_coefficient_all_degrees (q n : ℕ)
    (F : Fin 2 → ℝ → Vec 2 → Vec 2 → E) (hF : ∀ k, EpsPoly False q 1 (F k))
    (η : ℝ) (X z : Vec 2) :
    ((n.factorial : ℝ)⁻¹) • iteratedDeriv n
      (fun ε => ∑ k : Fin 2, dEps η ε k (F k ε) X z) 0 =
      ∑ k : Fin 2, covariantCoefficientStep η k
        (fun i Y y => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i (fun ε => F k ε Y y) 0) n X z := by
  choose P hP hz he using hF
  have hp (k : Fin 2) (ε : ℝ) : F k ε =
      fun Y y => ∑ i ∈ Finset.range (q + 1), ε ^ i • P k i Y y :=
    funext (fun Y => funext (fun y => he k ε Y y))
  have hc (k : Fin 2) (i : ℕ) :
      (fun Y y => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i (fun ε => F k ε Y y) 0) = P k i := by
    funext Y y
    have hpoly : (fun ε => F k ε Y y) = fun ε =>
        ∑ j ∈ Finset.range (q + 1), ε ^ j • P k j Y y :=
      funext (fun ε => he k ε Y y)
    rw [hpoly]
    exact normalized_polynomial_coefficient q i (fun j => P k j Y y) (fun j hj => hz k j hj Y y)
  have hstep (k : Fin 2) (ε : ℝ) : dEps η ε k (F k ε) X z =
      ∑ i ∈ Finset.range ((q + 1) + 1), ε ^ i • covariantCoefficientStep η k (P k) i X z := by
    rw [hp]
    simpa only [covariantCoefficientStep, Nat.add_assoc] using
      dEps_finite_polynomial_expand q (P k) (fun i => (hP k i).1)
        (fun i hi => funext (fun Y => funext (fun y => hz k i hi Y y))) η ε k X z
  have hpoly : (fun ε => ∑ k : Fin 2, dEps η ε k (F k ε) X z) =
      fun ε => ∑ i ∈ Finset.range ((q + 1) + 1), ε ^ i •
        ∑ k : Fin 2, covariantCoefficientStep η k (P k) i X z := by
    funext ε
    simp_rw [hstep]
    rw [Finset.sum_comm]
    simp only [Finset.smul_sum]
  have hzstep (i : ℕ) (hi : q + 1 < i) :
      (∑ k : Fin 2, covariantCoefficientStep η k (P k) i X z) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have h0 : P k i = 0 := by
      funext Y y
      exact hz k i (by omega) Y y
    have h1 : P k (i - 1) = 0 := by
      funext Y y
      exact hz k (i - 1) (by omega) Y y
    simp only [covariantCoefficientStep, h0, h1]
    simp [fastPartial, slowPartial]
  rw [hpoly, normalized_polynomial_coefficient (q + 1) n
    (fun i => ∑ k : Fin 2, covariantCoefficientStep η k (P k) i X z) hzstep]
  congr 1
  funext k
  have hcoeff : (fun i Y y => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i
      (fun ε => F k ε Y y) 0) = P k := funext (fun i => hc k i)
  rw [hcoeff]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit finite polynomial coefficients for iterated covariant words. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def covariantListCoefficients (η : ℝ) (w : List (Fin 2)) (f : Vec 2 → Vec 2 → E) :
    ℕ → Vec 2 → Vec 2 → E :=
  w.foldl (fun P k => covariantCoefficientStep η k P)
    (fun i => if i = 0 then f else fun _ _ => 0)

theorem covariantListCoefficients_nil (η : ℝ) (f : Vec 2 → Vec 2 → E) :
    covariantListCoefficients η [] f = fun i => if i = 0 then f else fun _ _ => 0 := rfl

theorem covariantListCoefficients_append_singleton (η : ℝ) (w : List (Fin 2))
    (k : Fin 2) (f : Vec 2 → Vec 2 → E) :
    covariantListCoefficients η (w ++ [k]) f =
      covariantCoefficientStep η k (covariantListCoefficients η w f) := by
  simp only [covariantListCoefficients, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem covariantListCoefficients_above_degree (η : ℝ) (w : List (Fin 2))
    (f : Vec 2 → Vec 2 → E) :
    ∀ i, w.length < i → covariantListCoefficients η w f i = fun _ _ => 0 := by
  induction w using List.reverseRecOn with
  | nil =>
    intro i hi
    simp only [covariantListCoefficients_nil, ite_eq_right (by simpa using Nat.ne_of_gt hi)]
  | append_singleton w k ih =>
    intro i hi
    have hi' : w.length + 1 < i := by simpa using hi
    rw [covariantListCoefficients_append_singleton]
    funext X z
    simp only [covariantCoefficientStep, ih i (by omega), ih (i - 1) (by omega),
      fastPartial_zero, slowPartial_zero, smul_zero, ite_self, add_zero]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Combine the two separately regular flux means into the literal divergence difference. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem fluxMean_difference (c : ℝ) (F G : Fin 2 → Vec 2 → Vec 2 → E)
    (hF : ∀ k, GoodField 1 (F k)) (hG : ∀ k, GoodField 1 (G k)) (X : Vec 2) :
    (∑ k : Fin 2, fderiv ℝ (fun Y => fieldCellMean (G k Y)) X (basisVec k)) -
        c • ∑ k : Fin 2, fderiv ℝ (fun Y => fieldCellMean (F k Y)) X (basisVec k) =
      -∑ k : Fin 2, fderiv ℝ (fun Y => c • fieldCellMean (F k Y) -
        fieldCellMean (G k Y)) X (basisVec k) := by
  have he (k : Fin 2) :
      fderiv ℝ (fun Y => c • fieldCellMean (F k Y) - fieldCellMean (G k Y)) X =
      c • fderiv ℝ (fun Y => fieldCellMean (F k Y)) X -
        fderiv ℝ (fun Y => fieldCellMean (G k Y)) X := by
    have hf := (AVRegularity.fieldCellMean_hasFDerivAt (hF k).1 X).differentiableAt
    have hg := (AVRegularity.fieldCellMean_hasFDerivAt (hG k).1 X).differentiableAt
    exact ((hf.hasFDerivAt.const_smul c).sub hg.hasFDerivAt).fderiv
  simp_rw [he]
  simp only [sub_apply, smul_apply,
    Finset.sum_sub_distrib, ← Finset.smul_sum]
  abel

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Scaling the finite test directions factors out exactly the tested differential order. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem homogeneous_lift_symbol_scaled_finite_extraction (n m : ℕ) (hm : m ≤ n)
    (c : LiftCoeff ι h) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ)
    (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u) :
    (∑ j : Fin (n + 1), polynomialExtractionWeight n m j •
      ((Real.exp (((j : ℝ) • (lam • A)) X))⁻¹ •
        liftApply n c (fun _ Y => Real.exp (((j : ℝ) • (lam • A)) Y) • Pi.single u ξ) t X z v)) =
      lam ^ m • ∑ α : DerivativeWord2 m,
        ((List.ofFn α).map (fun k => A (basisVec k))).prod • c m α t X z v u ξ := by
  rw [homogeneous_lift_symbol_finite_extraction n m hm]
  simp only [wordSymbol_smul, smul_smul, Finset.smul_sum]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The slow derivative of a finite mean polynomial acts coefficient by coefficient. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem mean_polynomial_directional_derivative (q : ℕ) (P : ℕ → Vec 2 → Vec 2 → E)
    (hP : ∀ i, GoodField 1 (P i)) (ε : ℝ) (X : Vec 2) (k : Fin 2) :
    fderiv ℝ (fun Y => fieldCellMean
      (fun z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i Y z)) X (basisVec k) =
      ∑ i ∈ Finset.range (q + 1), ε ^ i •
        fderiv ℝ (fun Y => fieldCellMean (P i Y)) X (basisVec k) := by
  have hp : (fun Y => fieldCellMean
      (fun z => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i Y z)) =
      fun Y => ∑ i ∈ Finset.range (q + 1), ε ^ i • fieldCellMean (P i Y) :=
    funext (fun Y => polynomial_field_mean_expand q P (fun i => (hP i).mono (by omega)) ε Y)
  have hd (i : ℕ) : DifferentiableAt ℝ (fun Y => fieldCellMean (P i Y)) X :=
    (fieldCellMean_hasFDerivAt (hP i).1 X).differentiableAt
  have hd' (i : ℕ) : DifferentiableAt ℝ (fun Y => ε ^ i • fieldCellMean (P i Y)) X := by
    simpa using! (hd i).const_smul (ε ^ i)
  rw [hp, fderiv_fun_sum (u := Finset.range (q + 1)) (fun i _ => hd' i)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_const_smul (hd i)]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Normalized derivatives extract the exact finite degree convolution. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalized_polynomial_convolution (N D j : ℕ) (A : ℕ → ℕ → E)
    (hz : ∀ i, N < i → ∀ l, A i l = 0) :
    ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
      (fun ε : ℝ => ∑ i ∈ Finset.range (N + 1),
        ∑ l ∈ Finset.range (D + 1), ε ^ (i + l) • A i l) 0 =
      ∑ l ∈ Finset.range (min D j + 1), A (j - l) l := by
  have hrow (i : ℕ) :
      ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
        (fun ε : ℝ => ∑ l ∈ Finset.range (D + 1), ε ^ (i + l) • A i l) 0 =
        ∑ l ∈ Finset.range (D + 1), if j = i + l then A i l else 0 := by
    rw [iteratedDeriv_fun_sum (fun l _ =>
      ((contDiff_id.pow (i + l)).smul contDiff_const).contDiffAt), Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    exact normalized_monomial_coefficient j (i + l) (A i l)
  rw [iteratedDeriv_fun_sum (fun i _ => (ContDiff.sum (fun l _ =>
    (contDiff_id.pow (i + l)).smul contDiff_const)).contDiffAt), Finset.smul_sum]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  simp_rw [finite_convolution_index N j _ _ (fun i hi => hz i hi _)]
  have hsmall : (∑ l ∈ Finset.range (min D j + 1), A (j - l) l) =
      ∑ l ∈ Finset.range (min D j + 1), if l ≤ j then A (j - l) l else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    have h := Finset.mem_range.mp hl
    exact (ite_eq_left (by omega : l ≤ j)).symm
  rw [hsmall]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.min_le_left D j) 1))
  intro l hl hn
  have hlD : l ≤ D := by have h := Finset.mem_range.mp hl; omega
  have hlj : ¬ l ≤ j := by
    have h : min D j + 1 ≤ l := Nat.le_of_not_gt (fun hi => hn (Finset.mem_range.mpr hi))
    omega
  exact ite_eq_right hlj

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Actual Taylor coefficients inherit the joint regularity of polynomial coefficients. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem epsPoly_coefficient_good {c : Prop} {q r : ℕ}
    {Ψ : ℝ → Vec 2 → Vec 2 → E} (hΨ : EpsPoly c q r Ψ) (j : ℕ) :
    GoodField r (fun X z => ((j.factorial : ℝ)⁻¹) •
      iteratedDeriv j (fun ε => Ψ ε X z) 0) := by
  obtain ⟨P, hP, hz, he⟩ := hΨ
  have hc : (fun X z => ((j.factorial : ℝ)⁻¹) •
      iteratedDeriv j (fun ε => Ψ ε X z) 0) = P j := by
    funext X z
    have he' : (fun ε => Ψ ε X z) =
        fun ε => ∑ i ∈ Finset.range (q + 1), ε ^ i • P i X z :=
      funext fun ε => he ε X z
    rw [he']
    exact normalized_polynomial_coefficient q j _ (fun i hi => hz i hi X z)
  rw [hc]
  exact (hP j).1
end

/-! The full source operator preserves finite parameter polynomials with its exact degree. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D p : ℕ}

theorem source_family_epsPoly_good (edge : ConstituentEdges D h) (η t : ℝ)
    (hcoeff : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} (hΦ : EpsPoly False p D Φ) :
    EpsPoly False (p + (D - 1) + 1) 0 (fun ε => sourceOp edge η ε t (Φ ε)) := by
  change EpsPoly False (p + (D - 1) + 1) 0
    (fun ε X z => ∑ k : Fin 2, dEps η ε k (sourceFlux edge η ε t (Φ ε) k) X z)
  exact EpsPoly.sum Finset.univ
    (fun k _ => EpsPoly.dEps η k (r := 0)
      (sourceFlux_family_epsPoly_good edge η t hcoeff hΦ k))
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Joint smoothness supplies the algebraic polynomial expansion without changing its rectangular coefficient reserves. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariantListCoefficients_good (η : ℝ) (w : List (Fin 2)) :
    ∀ r (f : Vec 2 → Vec 2 → E), GoodField (r + w.length) f →
      ∀ i, GoodField r (covariantListCoefficients η w f i) := by
  induction w using List.reverseRecOn with
  | nil =>
    intro r f hf i
    rw [covariantListCoefficients_nil]
    by_cases hi : i = 0
    · simpa only [hi, ite_true, List.length_nil, Nat.add_zero] using hf
    · simp only [hi, ite_false]
      exact GoodField.zero
  | append_singleton w k ih =>
    intro r f hf i
    have hh : GoodField ((r + 1) + w.length) f := by
      simpa only [List.length_append, List.length_singleton, Nat.add_assoc,
        Nat.add_comm 1 w.length] using hf
    have hfirst := (ih (r + 1) f hh i).fastPartial k
    rw [covariantListCoefficients_append_singleton]
    have he : covariantCoefficientStep η k (covariantListCoefficients η w f) i =
        fun X z => fastPartial k (covariantListCoefficients η w f i) X z +
          if i = 0 then 0 else Real.sqrt η • slowPartial k (covariantListCoefficients η w f (i - 1)) X z := rfl
    rw [he]
    by_cases hi : i = 0
    · simpa only [hi, ite_true, add_zero] using hfirst
    · have hsecond := ((ih (r + 1) f hh (i - 1)).slowPartial k).smul (Real.sqrt η)
      simpa only [hi, ite_false] using hfirst.add hsecond

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Scalar diffusion interpolations retain uniform slow jets and ellipticity. -/

def scalarMetricInterpolation (θ : ℝ) (g : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ :=
  fun t X => (1 - θ) + θ * g t X

theorem scalarMetricInterpolation_contDiff (θ : ℝ) (p : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t)) (t : ℝ) :
    ContDiff ℝ (p : ℕ∞) (scalarMetricInterpolation θ g t) :=
  contDiff_const.add ((hs t).const_smul θ)

theorem scalarMetricInterpolation_lower (θ κ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hκ : κ ≤ 1) (g : ℝ → Vec 2 → ℝ) (hg : ∀ t X, κ ≤ g t X) (t : ℝ) (X : Vec 2) :
    κ ≤ scalarMetricInterpolation θ g t X := by
  have hh := mul_le_mul_of_nonneg_left (hg t X) hθ.1
  have hneg := mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hκ)
  dsimp [scalarMetricInterpolation]
  nlinarith only [hh, hneg]

theorem scalarConstant_scaled_jet_le (c lam : ℝ) (hlam : 0 ≤ lam) (r : ℕ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun _ : Vec 2 => c) X‖ ≤ |c| * lam ^ r := by
  cases r with
  | zero => simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one, le_refl]
  | succ r =>
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hlam _)

theorem scalarMetricInterpolation_scaled_jet_le (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (p : ℕ) (g : ℝ → Vec 2 → ℝ) (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M lam : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (g t) X‖ ≤ M * lam ^ r)
    (r : ℕ) (hr : r ≤ p) (t : ℝ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (scalarMetricInterpolation θ g t) X‖ ≤ (1 + M) * lam ^ r := by
  have hg : ContDiff ℝ (r : ℕ∞) (g t) := (hs t).of_le (by exact_mod_cast hr)
  have hsum : scalarMetricInterpolation θ g t =
      (fun _ : Vec 2 => 1 - θ) + θ • g t := rfl
  have hc : ContDiff ℝ (r : ℕ∞) (fun _ : Vec 2 => 1 - θ) := contDiff_const
  have he := iteratedFDeriv_add_apply (x := X) (f := fun _ : Vec 2 => 1 - θ)
    (g := θ • g t) hc.contDiffAt (hg.const_smul θ).contDiffAt
  rw [hsum, he, iteratedFDeriv_const_smul_apply (x := X) hg.contDiffAt]
  apply (norm_add_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
  have hc := scalarConstant_scaled_jet_le (1 - θ) lam hlam r X
  rw [abs_of_nonneg (sub_nonneg.mpr hθ.2)] at hc
  have hh := mul_le_mul_of_nonneg_left (hb r hr t X) hθ.1
  have hm := mul_le_mul_of_nonneg_right hθ.2 hM
  have hp := pow_nonneg hlam r
  calc
    _ ≤ (1 - θ) * lam ^ r + θ * (M * lam ^ r) := add_le_add hc hh
    _ ≤ (1 + M) * lam ^ r := by nlinarith only [hθ.1, hp, mul_le_mul_of_nonneg_right hm hp]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Equality on exponential coarse tests identifies every homogeneous symbol of the lift. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem homogeneous_lift_symbol_eq_of_exponential_tests (n m : ℕ) (hm : m ≤ n)
    (c d : LiftCoeff ι h) (t : ℝ) (X z : Vec 2) (v u : ι) (ξ : h u)
    (he : ∀ A : Vec 2 →L[ℝ] ℝ,
      liftApply n c (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z v =
      liftApply n d (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z v)
    (A : Vec 2 →L[ℝ] ℝ) :
    (∑ α : DerivativeWord2 m,
      ((List.ofFn α).map (fun j => A (basisVec j))).prod • c m α t X z v u ξ) =
    ∑ α : DerivativeWord2 m,
      ((List.ofFn α).map (fun j => A (basisVec j))).prod • d m α t X z v u ξ := by
  rw [← homogeneous_lift_symbol_extraction n m hm c,
    ← homogeneous_lift_symbol_extraction n m hm d]
  have hf : (fun ε : ℝ => (Real.exp ((ε • A) X))⁻¹ •
      liftApply n c (fun _ Y => Real.exp ((ε • A) Y) • Pi.single u ξ) t X z v) =
      fun ε : ℝ => (Real.exp ((ε • A) X))⁻¹ •
      liftApply n d (fun _ Y => Real.exp ((ε • A) Y) • Pi.single u ξ) t X z v := by
    funext ε
    rw [he]
  rw [hf]
end

/-! A symmetric word coefficient is a fixed finite linear combination of scalar polynomial values. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem symmetric_word_finite_extraction {m : ℕ} (c : DerivativeWord2 m → E)
    (hs : ∀ β (σ : Equiv.Perm (Fin m)), c (β ∘ σ) = c β) (α : DerivativeWord2 m) :
    (Fintype.card {β : DerivativeWord2 m // wordZeroMultiplicity β = wordZeroMultiplicity α} : ℝ)⁻¹ •
      (∑ j : Fin (m + 1), polynomialExtractionWeight m (wordZeroMultiplicity α) j •
        ∑ β : DerivativeWord2 m, (j : ℝ) ^ wordZeroMultiplicity β • c β) = c α := by
  rw [word_polynomial_finite_extraction _ (wordZeroMultiplicity_le α),
    symmetric_word_orbit_sum c hs α, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [inv_mul_cancel₀, one_smul]
  exact_mod_cast (Nat.ne_of_gt (wordOrbit_card_pos α))
end

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The explicit coefficient step consumes one fast jet or one slow jet in separate branches. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariantCoefficientStep_box_reserve (p q i : ℕ) (η : ℝ) (k : Fin 2)
    (P : ℕ → Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p (q + 1) (P i))
    (hs : i ≠ 0 → IsBoxSmooth (p + 1) q (P (i - 1))) :
    IsBoxSmooth p q (covariantCoefficientStep η k P i) := by
  have heq : covariantCoefficientStep η k P i = fun X z =>
      fastPartial k (P i) X z +
        if i = 0 then 0 else Real.sqrt η • slowPartial k (P (i - 1)) X z := rfl
  rw [heq]
  by_cases hi : i = 0
  · simpa only [hi, ite_true, add_zero] using! hf.fastPartial k
  · have hslow := isBoxSmooth_slow_direction (hs hi) (basisVec k)
    have he : (fun X z => fderiv ℝ (fun Y => P (i - 1) Y z) X (basisVec k)) =
        slowPartial k (P (i - 1)) := rfl
    rw [he] at hslow
    simpa only [hi, ite_false] using!
      (hf.fastPartial k).add (hslow.const_smul (Real.sqrt η))
end

/-! The explicit coefficient array synthesizes the literal ordered covariant derivative word. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariantList_polynomial_identity (η : ℝ) (w : List (Fin 2)) :
    ∀ (f : Vec 2 → Vec 2 → E), GoodField w.length f → ∀ ε X z,
    w.foldl (fun F k => dEps η ε k F) f X z =
      ∑ i ∈ Finset.range (w.length + 1), ε ^ i • covariantListCoefficients η w f i X z := by
  induction w using List.reverseRecOn with
  | nil =>
    intro f _ ε X z
    simp only [List.foldl_nil, List.length_nil, covariantListCoefficients_nil]
    simp
  | append_singleton w k ih =>
    intro f hf ε X z
    have hf' : GoodField (1 + w.length) f := by
      simpa only [List.length_append, List.length_singleton, Nat.add_comm] using hf
    have hP := covariantListCoefficients_good η w 1 f hf'
    have hz := covariantListCoefficients_above_degree η w f
    have he : w.foldl (fun F k => dEps η ε k F) f =
        fun Y y => ∑ i ∈ Finset.range (w.length + 1),
          ε ^ i • covariantListCoefficients η w f i Y y := by
      funext Y y
      exact ih f (hf.mono (by simp)) ε Y y
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [he]
    have hstep := dEps_finite_polynomial_expand w.length
      (covariantListCoefficients η w f) hP hz η ε k X z
    simpa only [List.length_append, List.length_singleton, Nat.add_assoc,
      covariantListCoefficients_append_singleton, covariantCoefficientStep] using hstep
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The averaged divergence of a flux polynomial is an exact shifted slow-flux polynomial. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem covariant_polynomial_divergence_mean (q : ℕ)
    (P : Fin 2 → ℕ → Vec 2 → Vec 2 → E) (hP : ∀ k i, GoodField 1 (P k i))
    (η ε : ℝ) (X : Vec 2) :
    fieldCellMean (fun z => ∑ k : Fin 2, dEps η ε k
      (fun Y y => ∑ i ∈ Finset.range (q + 1), ε ^ i • P k i Y y) X z) =
      ε • (∑ i ∈ Finset.range (q + 1), ε ^ i •
        (Real.sqrt η • ∑ k : Fin 2,
          fderiv ℝ (fun Y => fieldCellMean (P k i Y)) X (basisVec k))) := by
  have hF (k : Fin 2) : GoodField 1
      (fun Y y => ∑ i ∈ Finset.range (q + 1), ε ^ i • P k i Y y) :=
    GoodField.sum _ (fun i _ => (hP k i).smul (ε ^ i))
  rw [fieldCellMean_covariant_divergence η ε _ hF X]
  have he (k : Fin 2) := mean_polynomial_directional_derivative q (P k) (hP k) ε X k
  simp_rw [he, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_smul]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ring

end AVRegularity.CycleComparison.Lift
end
end
