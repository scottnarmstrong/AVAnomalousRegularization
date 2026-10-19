-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.PositiveMeanCoefficientsAmbient
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.Lift.SettingPairedCoefficientOriginalReserve
public import AVRegularity.CycleComparison.Lift.SettingTransverseFieldInverseExistence
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite differential terms for the literal mean of the lift recurrence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

def actualMeanLeftTerms (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (t : ℝ) : List (LeftTerm (∀ i, h i) (∀ i, h i)) :=
  meanFluxLeftTerms n (actualMeanFluxCoefficient Q Cc hh n) t

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, MeasurableSpace (h i)] in
theorem actualMeanLeftTerms_order (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (d : LeftTerm (∀ i, h i) (∀ i, h i))
    (hd : d ∈ actualMeanLeftTerms Q Cc hh n t) : d.order ≤ n :=
  meanFluxLeftTerms_order n hn _ t d hd

include P in
theorem setting_actualMeanLeftTerms_box_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (p q : ℕ) (hreserve : p + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (d : LeftTerm (∀ i, h i) (∀ i, h i))
    (hd : d ∈ actualMeanLeftTerms Q Cc hh n t) : IsBoxSmooth p q d.coeff := by
  apply meanFluxLeftTerms_box n _ t p q ?_ d hd
  intro k₀ m hm α v u
  exact setting_actual_meanFlux_coefficient_contDiff_upto P sX sZ hsZ Cc hseq
    p hreserve hh hhh n hn hnR k₀ t ht m hm α 0 v u

include P in
theorem setting_actualMeanLeftTerms_apply
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    leftTermsApply (actualMeanLeftTerms Q Cc hh n t) f X z =
      liftMean Q Cc (fun _ => f) hh n t X := by
  have hr : 0 + (N + D) ≤ qs := by
    have := setting_ambient_output_supported P
    omega
  unfold actualMeanLeftTerms
  rw [meanFluxLeftTerms_meanApply n hn _ t
    (fun k₀ m hm α v u =>
      (setting_actual_meanFlux_coefficient_contDiff_upto P sX sZ (by omega) Cc hseq
        0 hr hh hhh n hn hnR k₀ t ht m hm α 0 v u).of_le (by norm_num))
    (fun k₀ α Y v u => setting_actual_meanFlux_coefficient_zero_order P sX sZ
      (by omega) Cc hseq 0 hr hh hhh n hn hnR k₀ t ht α Y 0 v u) f hf X z]
  by_cases hh0 : hh = 0
  · subst hh
    simpa only [actualMeanFluxCoefficient, ite_true] using
      (setting_diagonal_mean_flux_meanApply P sX sZ hsX hsZ Cc hseq
        0 hr n hn hnR f hf t ht X).symm
  · simpa only [actualMeanFluxCoefficient, ite_eq_right hh0] using
      (setting_positive_mean_flux_meanApply P sX sZ hsX hsZ Cc hseq
        0 hr hh (by omega) hhh n hn hnR f hf t ht X).symm
end

/-! The mean action retains every supported ambient slow order on smooth coarse inputs. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_mean_action_contDiff_upto
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (p : ℕ) (hreserve : p + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (p : ℕ∞) (fun X => liftMean Q Cc (fun _ => f) hh n t X) := by
  have hb : IsBoxSmooth p 0 (leftTermsApply (actualMeanLeftTerms Q Cc hh n t) f) :=
    leftTermsApply_box _ p 0 (fun d hd =>
      setting_actualMeanLeftTerms_box_upto P sX sZ (by omega) Cc hseq
        p 0 hreserve hh hhh n hn hnR t ht d hd) f hf
  have he : (fun X => leftTermsApply (actualMeanLeftTerms Q Cc hh n t) f X 0) =
      fun X => liftMean Q Cc (fun _ => f) hh n t X := by
    funext X
    exact setting_actualMeanLeftTerms_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnR f hf t ht X 0
  rw [← he]
  exact boxSmooth_slow_contDiff hb 0
end

/-! The recurrence mean is represented also at its vanishing first degree. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

def recurrenceMeanLeftTerms (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (t : ℝ) : List (LeftTerm (∀ i, h i) (∀ i, h i)) :=
  if 2 ≤ n then actualMeanLeftTerms Q Cc hh n t else []

include P in
theorem setting_recurrenceMeanLeftTerms_apply
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    leftTermsApply (recurrenceMeanLeftTerms Q Cc hh n t) f X z =
      liftMean Q Cc (fun _ => f) hh n t X := by
  by_cases hn2 : 2 ≤ n
  · simpa only [recurrenceMeanLeftTerms, ite_eq_left hn2] using
      setting_actualMeanLeftTerms_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn2 hnR f hf t ht X z
  · have hn1 : n = 1 := by omega
    subst n
    simp only [recurrenceMeanLeftTerms, show ¬2 ≤ (1 : ℕ) by omega, ite_false, leftTermsApply_nil]
    by_cases hh0 : hh = 0
    · subst hh
      exact (liftMean_first_diagonal_zero P sX sZ Cc hseq f hf t ht X).symm
    · exact (liftMean_first_positive_zero_ambient P sX sZ (by omega) Cc hseq
        f hf hh (by omega) hhh t ht X).symm
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The first vanishing mean and higher finite actions give the recurrence action. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

theorem recurrenceMeanLeftTerms_apply_of_finite_action
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (hn : 1 ≤ n) (f : Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2)
    (hfirst : n = 1 → liftMean Q Cc (fun _ => f) hh n t X = 0)
    (hactual : 2 ≤ n → leftTermsApply (actualMeanLeftTerms Q Cc hh n t) f X z =
      liftMean Q Cc (fun _ => f) hh n t X) :
    leftTermsApply (recurrenceMeanLeftTerms Q Cc hh n t) f X z =
      liftMean Q Cc (fun _ => f) hh n t X := by
  by_cases hn2 : 2 ≤ n
  · simpa only [recurrenceMeanLeftTerms, ite_eq_left hn2] using hactual hn2
  · simp only [recurrenceMeanLeftTerms, ite_eq_right hn2, leftTermsApply_nil]
    exact (hfirst (by omega)).symm
end

/-! Uncentered finite terms and actual mean fluxes depend only on preceding grades and degrees. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ}

omit [DecidableEq ι] in
theorem liftALeftTerms_congr_predecessors (Q : LiftOperatorData ι h D)
    (C E : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : 1 ≤ n)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → C p q = E p q)
    (t : ℝ) (v : ι) : liftALeftTerms Q C hh n t v = liftALeftTerms Q E hh n t v := by
  have h₁ := he hh (n - 1) (Or.inr ⟨rfl, by omega⟩)
  have h₂ := he hh (n - 2) (Or.inr ⟨rfl, by omega⟩)
  simp only [liftALeftTerms, h₁, h₂]
  by_cases hh0 : hh = 0
  · simp only [ite_eq_left hh0]
  · rw [ite_eq_right hh0, ite_eq_right hh0,
      sourceConvolutionLeftTerms_congr_coefficients Q.edge Q.η t n (C (hh - 1))
        (E (hh - 1)) (fun q _ => he (hh - 1) q (Or.inl (by omega))) v]

theorem actualMeanFluxCoefficient_congr_predecessors (Q : LiftOperatorData ι h D)
    (C E : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : 1 ≤ n)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → C p q = E p q) :
    actualMeanFluxCoefficient Q C hh n = actualMeanFluxCoefficient Q E hh n := by
  have h₁ := he hh (n - 1) (Or.inr ⟨rfl, by omega⟩)
  by_cases hh0 : hh = 0
  · subst hh
    simp only [actualMeanFluxCoefficient, ite_true]
    funext k m α t X z v u
    simp only [diagonalMeanFluxCoefficient, h₁]
  · simp only [actualMeanFluxCoefficient, ite_eq_right hh0]
    funext k m α t X z v u
    simp only [positiveMeanFluxCoefficient, h₁]
    rw [sourceFluxMeanCoefficient_congr_coefficients Q.edge Q.η t (n - 1)
      (C (hh - 1)) (E (hh - 1)) (fun q _ => he (hh - 1) q (Or.inl (by omega))) k]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The ordered lift-mean product has a finite action with the original slow reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
 [DecidableEq ι]
  {D : ℕ} {Q : LiftOperatorData ι h D}

theorem lift_mean_composition_leftTerms_apply_of_representation
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh j n : ℕ)
    (c : LiftCoeff ι h) (v : ι) (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2)
    (hbox : ∀ d ∈ actualMeanLeftTerms Q Cc hh n t, IsBoxSmooth j 0 d.coeff)
    (hmean : ∀ Y, leftTermsApply (actualMeanLeftTerms Q Cc hh n t) f Y z =
      liftMean Q Cc (fun _ => f) hh n t Y) :
    leftTermsApply (leftTermsComposition (liftComponentLeftTerms j c t v)
      (actualMeanLeftTerms Q Cc hh n t)) f X z =
      liftApply j c (liftMean Q Cc (fun _ => f) hh n) t X z v := by
  have hbox' (d : LeftTerm (∀ i, h i) (h v)) (hd : d ∈ liftComponentLeftTerms j c t v)
      (e : LeftTerm (∀ i, h i) (∀ i, h i)) (he : e ∈ actualMeanLeftTerms Q Cc hh n t) :
      IsBoxSmooth d.order 0 e.coeff :=
    (hbox e he).mono (liftComponentLeftTerms_order j c t v d hd) le_rfl
  rw [leftTermsComposition_apply _ _ hbox' f hf X z]
  have he : (fun Y => leftTermsApply (actualMeanLeftTerms Q Cc hh n t) f Y z) =
      fun Y => liftMean Q Cc (fun _ => f) hh n t Y := by
    funext Y
    exact hmean Y
  rw [he, liftComponentLeftTerms_apply]
  rfl
end

/-! The ordered lift-mean product has a finite action with the original slow reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_lift_mean_composition_leftTerms_apply
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (j n : ℕ) (hj : j ≤ N) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (c : LiftCoeff ι h) (v : ι) (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    leftTermsApply (leftTermsComposition (liftComponentLeftTerms j c t v)
      (actualMeanLeftTerms Q Cc hh n t)) f X z =
      liftApply j c (liftMean Q Cc (fun _ => f) hh n) t X z v := by
  have hr : N + (N + D) ≤ qs := by
    have := setting_tail_ambient_supported P
    omega
  have hbox (d : LeftTerm (∀ i, h i) (h v)) (hd : d ∈ liftComponentLeftTerms j c t v)
      (e : LeftTerm (∀ i, h i) (∀ i, h i)) (he : e ∈ actualMeanLeftTerms Q Cc hh n t) :
      IsBoxSmooth d.order 0 e.coeff := by
    have horder := liftComponentLeftTerms_order j c t v d hd
    exact (setting_actualMeanLeftTerms_box_upto P sX sZ (by omega) Cc hseq
      N 0 hr hh hhh n hn hnR t ht e he).mono (by omega) le_rfl
  rw [leftTermsComposition_apply _ _ hbox f hf X z]
  have he : (fun Y => leftTermsApply (actualMeanLeftTerms Q Cc hh n t) f Y z) =
      fun Y => liftMean Q Cc (fun _ => f) hh n t Y := by
    funext Y
    exact setting_actualMeanLeftTerms_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnR f hf t ht Y z
  rw [he, liftComponentLeftTerms_apply]
  rfl
end

/-! A lift applied to the actual mean polynomial has its finite ordered convolution. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
/-- The finite synthesis for a time-dependent field, over a variable family: the kernel then
compares the fields only at the evaluation time. -/
private theorem liftApply_finset_synthesis_at (S : Finset ℕ) (r : ℕ) (c : LiftCoeff ι h)
    (w : ℕ → ℝ) (F : ℕ → ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hF : ∀ n ∈ S, ContDiff ℝ (r : ℕ∞) (F n t)) (X z : Vec 2) :
    liftApply r c (fun s Y => ∑ n ∈ S, w n • F n s Y) t X z =
      ∑ n ∈ S, w n • liftApply r c (F n) t X z :=
  liftApply_input_finset_synthesis S r c w (fun n => F n t) hF t X z

include P in
theorem setting_lift_mean_polynomial_action
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (r : ℕ) (hr : r ≤ N) (c : LiftCoeff ι h) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply r c (liftMeanPoly Q Cc N ε (fun _ => f) hh) t X z =
      ∑ n ∈ Finset.Icc 2 (N + D), ε ^ n •
        liftApply r c (liftMean Q Cc (fun _ => f) hh n) t X z := by
  have hreserve : N + (N + D) ≤ qs := by
    have := setting_tail_ambient_supported P
    omega
  have hreg n (hn : n ∈ Finset.Icc 2 (N + D)) :
      ContDiff ℝ (r : ℕ∞) (fun Y => liftMean Q Cc (fun _ => f) hh n t Y) :=
    (setting_mean_action_contDiff_upto P sX sZ hsX hsZ Cc hseq N hreserve hh hhh
      n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 f hf t ht).of_le
        (by exact_mod_cast hr)
  exact liftApply_finset_synthesis_at (Finset.Icc 2 (N + D)) r c (fun n => ε ^ n)
    (fun n => liftMean Q Cc (fun _ => f) hh n) t hreg X z
end

/-! The truncated lift applied to the mean polynomial is its rectangular finite product. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftPoly_mean_polynomial_action
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (gg : ℕ) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftPolyField Cc N ε gg (liftMeanPoly Q Cc N ε (fun _ => f) hh) t X z =
      ∑ r ∈ Finset.range (N + 1), ∑ n ∈ Finset.Icc 2 (N + D), ε ^ (r + n) •
        liftApply r (Cc gg r) (liftMean Q Cc (fun _ => f) hh n) t X z := by
  unfold liftPolyField
  apply Finset.sum_congr rfl
  intro r hr
  rw [setting_lift_mean_polynomial_action P sX sZ hsX hsZ Cc hseq hh hhh r
    (by have := Finset.mem_range.mp hr; omega) (Cc gg r) ε f hf t ht X z,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [smul_smul, pow_add]
end

/-! The actual low-degree source is minus the uncentered coefficient plus the full ordered composition. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftCellSource_low_degree
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftCellSource Q Cc (fun _ => f) hh n t X z =
      -liftA Q Cc (fun _ => f) hh n t X z +
        liftMeanCompositionCoefficient Q Cc N (fun _ => f) hh n t X z := by
  by_cases hn2 : 2 ≤ n
  · rw [liftMeanComposition_low_degree Q sX sZ a b N H Cc hseq (fun _ => f)
      hh n hhh hn2 hnN t ht X z]
    unfold liftCellSource
    abel
  · have hn1 : n = 1 := by omega
    subst n
    have hm := setting_recurrenceMeanLeftTerms_apply P sX sZ hsX hsZ Cc hseq
      hh hhh 1 (by omega) (by have := P.N_ge; omega) f hf t ht X z
    have hm0 : liftMean Q Cc (fun _ => f) hh 1 t X = 0 := by
      simpa only [recurrenceMeanLeftTerms, show ¬2 ≤ (1 : ℕ) by omega,
        ite_false, leftTermsApply_nil] using hm.symm
    rw [liftMeanComposition_first_zero]
    simp [liftCellSource, hm0]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Literal finite differential terms for the full truncated lift tail. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

def tailCompositionLeftTerms (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (t : ℝ) (v : ι) :
    List (LeftTerm (∀ i, h i) (h v)) :=
  (Finset.range (N + 1)).toList.flatMap fun r =>
    if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
      (Finset.HasAntidiagonal.antidiagonal hh).toList.flatMap fun p =>
        leftTermsComposition (liftComponentLeftTerms r (Cc p.1 r) t v)
          (actualMeanLeftTerms Q Cc p.2 (n - r) t)
    else []

def liftTailLeftTerms (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (t : ℝ) (v : ι) :
    List (LeftTerm (∀ i, h i) (h v)) :=
  liftALeftTerms Q Cc hh n t v ++
    (tailCompositionLeftTerms Q Cc N hh n t v).map (fun c => c.smul (-1))

theorem tailCompositionLeftTerms_order (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (t : ℝ) (v : ι)
    (c : LeftTerm (∀ i, h i) (h v))
    (hc : c ∈ tailCompositionLeftTerms Q Cc N hh n t v) : c.order ≤ n := by
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp hc
  split_ifs at hr with hg
  · obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hr
    have he := leftTermsComposition_order _ _ r (n - r)
      (liftComponentLeftTerms_order r (Cc p.1 r) t v)
      (actualMeanLeftTerms_order Cc p.2 (n - r) (by omega) t) c hp
    omega
  · simp only [List.not_mem_nil] at hr

theorem liftTailLeftTerms_order (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (v : ι)
    (c : LeftTerm (∀ i, h i) (h v))
    (hc : c ∈ liftTailLeftTerms Q Cc N hh n t v) : c.order ≤ n := by
  rcases List.mem_append.mp hc with ha | ht
  · exact liftALeftTerms_order Q Cc hh n hn t v c ha
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ht
    exact tailCompositionLeftTerms_order Q Cc N hh n t v d hd

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The graded product of the truncated lift and mean has the exact explicit tail coefficients. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_lift_mean_composition_polynomial
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => f) p.2) t X z) =
      ∑ n ∈ Finset.Icc 1 (2 * N + D), ε ^ n •
        liftMeanCompositionCoefficient Q Cc N (fun _ => f) hh n t X z := by
  have hexpand : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => f) p.2) t X z) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∑ r ∈ Finset.range (N + 1),
        ∑ l ∈ Finset.Icc 2 (N + D), ε ^ (r + l) •
          liftApply r (Cc p.1 r) (liftMean Q Cc (fun _ => f) p.2 l) t X z := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact setting_liftPoly_mean_polynomial_action P sX sZ hsX hsZ Cc hseq
      p.2 (by omega) p.1 ε f hf t ht X z
  rw [hexpand, Finset.sum_comm]
  have hreorder : (∑ r ∈ Finset.range (N + 1),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∑ l ∈ Finset.Icc 2 (N + D),
        ε ^ (r + l) • liftApply r (Cc p.1 r) (liftMean Q Cc (fun _ => f) p.2 l) t X z) =
      ∑ r ∈ Finset.range (N + 1), ∑ l ∈ Finset.Icc 2 (N + D), ε ^ (r + l) •
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftApply r (Cc p.1 r) (liftMean Q Cc (fun _ => f) p.2 l) t X z) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.smul_sum]
  rw [hreorder, polynomial_rectangular_convolution]
  have hM : N + (N + D) = 2 * N + D := by omega
  rw [hM]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The genuine original-reserve coefficient differences satisfy the uniform energy readout. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem setting_paired_energy_original_reserve
    (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N 0 Cc)
    (hseqi : IsLiftSequence
      (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
      (K + D + 2) (max (k + 1) (L + 2)) a b N 0 Ci)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (n : ℕ) (hnN : n ≤ N) (m : ℕ) (hm : m ≤ n) (r : ℕ) (hr : r ≤ K) :
    schurEnergyJet π (Set.Icc a b) k r
      (fun α t X z v u => Cc 0 n m α t X z v u - Ci 0 n m α t X z v u) ≤
      ENNReal.ofReal (pairedEnergyScalarBudget N K k
        (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) *
        g * lam ^ (n - m + r)) := by
  let Bd := pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI
  have hBd j : 0 ≤ Bd j := pairedCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _
  have data := setting_paired_coefficient_original_reserve P Cc Ci hseq hseqi g hg CGI hGI n (by omega)
  have hp : r ≤ ambientDegreeSlowReserve K (N + D) n := by unfold ambientDegreeSlowReserve; omega
  have hq : k + 1 ≤ ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n :=
    (Nat.le_max_left (k + 1) (L + 2)).trans
      (lift_inverse_order_le_ambient_fast_reserve D N k L n (by have := P.D_ge; omega) hnN)
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  apply (data.paired_diagonal_energy_le (hBd n) hg hlam hm hp hq π P.mass_pos).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pairedEnergyScalarBudget_dominates N K k n m r Bd hBd hnN hm hr) hg)
    (pow_nonneg hlam _)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit ordered finite terms for the centered lift recurrence source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

def liftCellSourceLeftTerms (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (t : ℝ) (v : ι) : List (LeftTerm (∀ i, h i) (h v)) :=
  (liftALeftTerms Q Cc hh n t v).map (fun c => c.smul (-1)) ++
    (recurrenceMeanLeftTerms Q Cc hh n t).map
      (fun c => c.postcompose (ContinuousLinearMap.proj v)) ++
    (Finset.Icc 1 (n - 2)).toList.flatMap fun j =>
      (Finset.HasAntidiagonal.antidiagonal hh).toList.flatMap fun p =>
        leftTermsComposition (liftComponentLeftTerms j (Cc p.1 j) t v)
          (actualMeanLeftTerms Q Cc p.2 (n - j) t)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Actual divergence-form mean grading holds throughout the original ambient data reserve. -/

theorem cycle_lift_mean_grading_upto (P₀ N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      P₀ + N + D ≤ qs →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∀ hh, hh ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
          ∃ Lb : MeanCoeff ι h,
            (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))), Lb d (α ∘ σ) = Lb d α) ∧
            (∀ d α k v u, ∀ t ∈ Set.Icc t₀ t₁,
              ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => Lb d α t X k v u)) ∧
            (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
              liftMean Q Cc (fun _ => a₀) hh n t X = meanApply n Lb (fun _ => a₀) t X) ∧
            (∀ d, 2 ≤ d → d ≤ n → ∀ j, j ≤ P₀ →
              schurSlowJet π (Set.Icc t₀ t₁) j
                (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => Lb d p.1 t X p.2)
                ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - d + j))) :=
by
  refine ⟨ambientMeanGradeConstant P₀ N k L D H CG Cw Cj,
    ambientMeanGradeConstant_nonneg P₀ N k L D H CG Cw Cj, ?_⟩
  classical
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P hreserve
    Cc hseq hh hhh n hn hnR
  rcases isEmpty_or_nonempty ι with hι | hι
  · have := hι
    refine ⟨0, ?_, ?_, ?_, ?_⟩
    · intro d α σ
      rfl
    · intro d α k₀ v u t ht
      exact contDiff_const
    · intro f hf t ht X
      exact Subsingleton.elim _ _
    · intro d hd hdn r hr
      simp [schurSlowJet, schurSums]
  · have := hι
    let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
    have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
    have hΘ : 0 ≤ Θ := (Finset.sum_nonneg (fun u _ => P.envelope.nonneg (Classical.choice hι) u)).trans
      (P.envelope.row_sum (Classical.choice hι))
    have hres : P₀ + (N + D) ≤ qs := by omega
    have hX : 2 ≤ K + D + 2 := by omega
    have hZ : 2 ≤ max (k + 1) (L + 2) := by omega
    by_cases hh0 : hh = 0
    · subst hh
      simpa only [pow_zero, mul_one] using setting_diagonal_mean_coefficients_upto P
        (K + D + 2) (max (k + 1) (L + 2)) hX hZ Cc hseq P₀ hres hΘ n hn hnR
    · exact setting_positive_mean_coefficients_upto P
        (K + D + 2) (max (k + 1) (L + 2)) hX hZ Cc hseq P₀ hres hΘ hh (by omega) hhh n hn hnR

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit ordered finite terms for the centered lift recurrence source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
theorem liftCellSourceLeftTerms_order (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (v : ι)
    (c : LeftTerm (∀ i, h i) (h v)) (hc : c ∈ liftCellSourceLeftTerms Q Cc hh n t v) :
    c.order ≤ n := by
  rcases List.mem_append.mp hc with hleft | hprod
  · rcases List.mem_append.mp hleft with hA | hmean
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hA
      exact liftALeftTerms_order Q Cc hh n hn t v d hd
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmean
      unfold recurrenceMeanLeftTerms at hd
      split_ifs at hd with hn2
      · exact actualMeanLeftTerms_order Cc hh n hn t d hd
      · simp only [List.not_mem_nil] at hd
  · obtain ⟨j, hj, p, hp, hcp⟩ := by
      simpa only [List.mem_flatMap] using hprod
    have hjdata := Finset.mem_Icc.mp (Finset.mem_toList.mp hj)
    have hnj : 1 ≤ n - j := by omega
    have horder := leftTermsComposition_order
      (liftComponentLeftTerms j (Cc p.1 j) t v) (actualMeanLeftTerms Q Cc p.2 (n - j) t)
      j (n - j) (liftComponentLeftTerms_order j (Cc p.1 j) t v)
      (actualMeanLeftTerms_order Cc p.2 (n - j) hnj t) c hcp
    omega

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite tail presentation uses proved actions of its uncentered and mean factors. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

theorem tailCompositionLeftTerms_apply_of_representations
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ)
    (t : ℝ) (v : ι) (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X z : Vec 2)
    (hbox : ∀ r ≤ N, r ≤ n → 2 ≤ n - r → n - r ≤ N + D →
      ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∀ d ∈ actualMeanLeftTerms Q Cc p.2 (n - r) t,
        IsBoxSmooth r 0 d.coeff)
    (hmean : ∀ r ≤ N, r ≤ n → 2 ≤ n - r → n - r ≤ N + D →
      ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∀ Y,
        leftTermsApply (actualMeanLeftTerms Q Cc p.2 (n - r) t) f Y z =
          liftMean Q Cc (fun _ => f) p.2 (n - r) t Y) :
    leftTermsApply (tailCompositionLeftTerms Q Cc N hh n t v) f X z =
      (∑ r ∈ Finset.range (N + 1),
        if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
            liftApply r (Cc p.1 r) (liftMean Q Cc (fun _ => f) p.2 (n - r)) t X z
        else 0) v := by
  unfold tailCompositionLeftTerms
  rw [leftTermsApply_finset_flatMap]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  have hrN : r ≤ N := by have := Finset.mem_range.mp hr; omega
  by_cases hg : r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D
  · rw [ite_eq_left hg, leftTermsApply_finset_flatMap]
    simp only [ite_eq_left hg, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro p hp
    exact lift_mean_composition_leftTerms_apply_of_representation Cc p.2 r (n - r)
      (Cc p.1 r) v f hf t X z
      (hbox r hrN hg.1 hg.2.1 hg.2.2 p hp)
      (hmean r hrN hg.1 hg.2.1 hg.2.2 p hp)
  · simp only [ite_eq_right hg, leftTermsApply_nil, Pi.zero_apply]

theorem liftTailLeftTerms_apply_of_representations
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ)
    (t : ℝ) (v : ι) (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X z : Vec 2)
    (hA : leftTermsApply (liftALeftTerms Q Cc hh n t v) f X z =
      liftA Q Cc (fun _ => f) hh n t X z v)
    (hbox : ∀ r ≤ N, r ≤ n → 2 ≤ n - r → n - r ≤ N + D →
      ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∀ d ∈ actualMeanLeftTerms Q Cc p.2 (n - r) t,
        IsBoxSmooth r 0 d.coeff)
    (hmean : ∀ r ≤ N, r ≤ n → 2 ≤ n - r → n - r ≤ N + D →
      ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∀ Y,
        leftTermsApply (actualMeanLeftTerms Q Cc p.2 (n - r) t) f Y z =
          liftMean Q Cc (fun _ => f) p.2 (n - r) t Y) :
    leftTermsApply (liftTailLeftTerms Q Cc N hh n t v) f X z =
      liftTailCoeff Q Cc N (fun _ => f) hh n t X z v := by
  unfold liftTailLeftTerms
  rw [leftTermsApply_append]
  dsimp only
  rw [leftTermsApply_map_smul]
  dsimp only
  rw [hA, tailCompositionLeftTerms_apply_of_representations Q Cc N hh n t v f hf X z hbox hmean]
  simp only [liftTailCoeff, Pi.sub_apply, neg_one_smul, sub_eq_add_neg]
end

/-! One literal coefficient step of the finite-past lift recurrence. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D : ℕ}

def constructedLiftStep (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2)
    (prior : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) : LiftCoeff ι h :=
  fun m α t X z v u =>
    if n = 0 then
      if hh = 0 ∧ m = 0 then blockIdentityEntry h v u else 0
    else if m ≤ n then
      finiteProfileResponse
        (fun r => Q.G (Set.projIcc a b hab r) X par.rev par.rev)
        (fun s x => leftTermsBlockCoefficient
          (fun w => liftCellSourceLeftTerms Q prior hh n (Set.projIcc a b hab s) w)
          m α s X (Pi.single par.rev x) v u) a t (z par.rev)
    else 0

theorem constructedLiftStep_above_order (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2)
    (prior : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ) (hm : n < m)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    constructedLiftStep Q a b hab par prior hh n m α t X z v u = 0 := by
  by_cases hn : n = 0
  · simp only [constructedLiftStep, hn, ite_eq_left]
    rw [ite_eq_right (by omega : ¬ (hh = 0 ∧ m = 0))]
  · simp only [constructedLiftStep, ite_eq_right hn, ite_eq_right (Nat.not_le.mpr hm)]
end

/-! Time-dependent synthesis is evaluated before comparing its normalized frozen-time action. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

def liftSourceBlockCoefficient (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) : LiftCoeff ι h :=
  fun m α t X z v u =>
    leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w)
      m α t X z v u

theorem liftSourceBlockCoefficient_normalized (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (X z : Vec 2) :
    normalizedLiftTestField (liftSourceBlockCoefficient Q Cc hh n) n A u v ξ t X z =
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z := by
  have he := liftApply_congr_at_time n (liftSourceBlockCoefficient Q Cc hh n)
    (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
    (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t (fun _ _ _ _ _ _ => rfl)
  unfold normalizedLiftTestField
  exact congrArg (fun f : Vec 2 → Vec 2 → ∀ i, h i =>
    (Real.exp (A X))⁻¹ • f X z v) he
end

/-! A finite differential action gives the literal normalized source block. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ}

theorem normalized_source_block_of_finite_action
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (u v : ι) (ξ : h u)
    (A : Vec 2 →L[ℝ] ℝ) (X z : Vec 2)
    (ha : leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v)
      (fun Y => Real.exp (A Y) • Pi.single u ξ) X z =
      liftCellSource Q Cc (fun _ Y => Real.exp (A Y) • Pi.single u ξ) hh n t X z v) :
    normalizedLiftTestField
      (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
      n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z := by
  unfold normalizedLiftTestField normalizedLiftSourceField
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun Y => Real.exp (A Y) • Pi.single u ξ) :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  rw [leftTermsBlockCoefficient_apply (fun w => liftCellSourceLeftTerms Q Cc hh n t w) n
    (fun w c hc => liftCellSourceLeftTerms_order Cc hh n hn t w c hc)
    (fun Y => Real.exp (A Y) • Pi.single u ξ) hf t X z v, ha]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! An exact finite source presentation identifies its calibrated coefficient without assuming a completed sequence. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

theorem calibratedLiftSourceEntry_eq_of_block_action
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0)
    (u v : ι) (ξ : h u) (t : ℝ) (X z : Vec 2)
    (hblock : ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z) :
    calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z =
      leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w)
        m α t X z v u ξ := by
  let c := leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w)
  unfold calibratedLiftSourceEntry
  have he : (∑ p : Fin (m + 1) × Fin (n + 1), liftCalibrationWeight n m α lam p •
      normalizedLiftSourceField Q Cc hh n
        (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v ξ t X z) =
      ∑ p : Fin (m + 1) × Fin (n + 1), liftCalibrationWeight n m α lam p •
        normalizedLiftTestField c n
          (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v ξ t X z := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hblock]
  rw [he]
  exact liftCalibration_synthesis n m hm c lam hlam
    (fun β σ => leftTermsBlockCoefficient_perm _ m β σ) α t X z v u ξ

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Natural-number recursion constructs the finite coefficient array from strictly earlier steps. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D : ℕ}

def constructedLiftRank (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N : ℕ) : ℕ → LiftCoeff ι h :=
  fun r => Nat.strongRecOn r fun r rec =>
    constructedLiftStep Q a b hab par
      (fun hh n => if n ≤ N then
        if hr : ambientRecurrenceRank N hh n < r then
          rec (ambientRecurrenceRank N hh n) hr
        else 0
      else 0) (r / (N + 1)) (r % (N + 1))

theorem constructedLiftRank_eq (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N r : ℕ) :
    constructedLiftRank Q a b hab par N r =
      constructedLiftStep Q a b hab par
        (fun hh n => if n ≤ N then
          if ambientRecurrenceRank N hh n < r then
            constructedLiftRank Q a b hab par N (ambientRecurrenceRank N hh n)
          else 0
        else 0) (r / (N + 1)) (r % (N + 1)) := by
  unfold constructedLiftRank
  rw [Nat.strongRecOn_eq]
  congr 1


def constructedLiftCoefficients (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N : ℕ) : ℕ → ℕ → LiftCoeff ι h :=
  fun hh n => if n ≤ N then
    constructedLiftRank Q a b hab par N (ambientRecurrenceRank N hh n)
  else 0

theorem constructedLiftCoefficients_cutoff (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh n : ℕ) (hn : N < n) :
    constructedLiftCoefficients Q a b hab par N hh n = 0 := by
  simp only [constructedLiftCoefficients, ite_eq_right (Nat.not_le.mpr hn)]
end

/-! The literal centered finite term list is completely determined by earlier coefficients. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ}

theorem liftCellSourceLeftTerms_congr_predecessors (Q : LiftOperatorData ι h D)
    (C E : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : 1 ≤ n)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → C p q = E p q)
    (t : ℝ) (v : ι) :
    liftCellSourceLeftTerms Q C hh n t v = liftCellSourceLeftTerms Q E hh n t v := by
  have hA := liftALeftTerms_congr_predecessors Q C E hh n hn he t v
  have hM := actualMeanFluxCoefficient_congr_predecessors Q C E hh n hn he
  simp only [liftCellSourceLeftTerms, hA, recurrenceMeanLeftTerms, actualMeanLeftTerms, hM]
  congr 1
  apply List.flatMap_congr
  intro j hj
  have hj' := Finset.mem_Icc.mp (Finset.mem_toList.mp hj)
  apply List.flatMap_congr
  intro p hp
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_toList.mp hp)
  have hC := he p.1 j (by
    by_cases hlt : p.1 < hh
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, by omega⟩)
  have hmean := actualMeanFluxCoefficient_congr_predecessors Q C E p.2 (n - j) (by omega)
    (fun r s hrs => he r s (by
      rcases hrs with hrs | ⟨hrs, hsn⟩
      · exact Or.inl (by omega)
      · by_cases hlt : r < hh
        · exact Or.inl hlt
        · exact Or.inr ⟨by omega, by omega⟩))
  simp only [hC, hmean]
end

/-! Symmetric finite coefficient synthesis for the literal tail differential action. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

def tailLeftCoefficient (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) : LiftCoeff ι h :=
  fun m α t X z v u =>
    leftTermsBlockCoefficient (fun w => liftTailLeftTerms Q Cc N hh n t w)
      m α t X z v u

theorem tailLeftCoefficient_perm (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    tailLeftCoefficient Q Cc N hh n m (α ∘ σ) =
      tailLeftCoefficient Q Cc N hh n m α := by
  funext t X z v u
  exact congrFun (congrFun (congrFun (congrFun (congrFun
    (leftTermsBlockCoefficient_perm (fun w => liftTailLeftTerms Q Cc N hh n t w)
      m α σ) t) X) z) v) u

theorem tailLeftCoefficient_action (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply (2 * N + D) (tailLeftCoefficient Q Cc N hh n) (fun _ => f) t X z v =
      leftTermsApply (liftTailLeftTerms Q Cc N hh n t v) f X z := by
  have he := liftApply_congr_at_time (2 * N + D) (tailLeftCoefficient Q Cc N hh n)
    (leftTermsBlockCoefficient (fun w => liftTailLeftTerms Q Cc N hh n t w))
    (fun _ => f) t (fun _ _ _ _ _ _ => rfl)
  have hv := congrArg (fun g : Vec 2 → Vec 2 → ∀ i, h i => g X z v) he
  exact hv.trans (leftTermsBlockCoefficient_apply
    (fun w => liftTailLeftTerms Q Cc N hh n t w) (2 * N + D)
    (fun w c hc => (liftTailLeftTerms_order Q Cc N hh n hn t w c hc).trans hnR)
    f hf t X z v)
end

/-! The constructed array obeys its literal finite-prefix recurrence at every retained degree. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem constructedLiftCoefficients_eq_step (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh n : ℕ) (hn : n ≤ N) :
    constructedLiftCoefficients Q a b hab par N hh n =
      constructedLiftStep Q a b hab par
        (fun p q => if ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n then
          constructedLiftCoefficients Q a b hab par N p q else 0) hh n := by
  rw [constructedLiftCoefficients, ite_eq_left hn, constructedLiftRank_eq,
    ambientRecurrenceRank_div N hh n hn, ambientRecurrenceRank_mod N hh n hn]
  congr 1
  funext p q
  by_cases hq : q ≤ N <;>
    by_cases hr : ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n <;>
    simp only [constructedLiftCoefficients, hq, hr, ite_true, ite_false]
end

/-! Time-dependent source synthesis has the explicit finite differential action. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

theorem liftSourceBlockCoefficient_action (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : 1 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n (liftSourceBlockCoefficient Q Cc hh n) (fun _ => f) t X z v =
      leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z := by
  have he := liftApply_congr_at_time n (liftSourceBlockCoefficient Q Cc hh n)
    (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
    (fun _ => f) t (fun _ _ _ _ _ _ => rfl)
  have hv := congrArg (fun g : Vec 2 → Vec 2 → ∀ i, h i => g X z v) he
  exact hv.trans (leftTermsBlockCoefficient_apply
    (fun w => liftCellSourceLeftTerms Q Cc hh n t w) n
    (fun w c hc => liftCellSourceLeftTerms_order Cc hh n hn t w c hc) f hf t X z v)
end

end AVRegularity.CycleComparison.Lift
end
