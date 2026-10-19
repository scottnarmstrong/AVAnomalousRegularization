-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingAmbientPositiveCoefficientRankStep
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SecondCrossMean
public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget
import AVRegularity.CycleComparison.Lift.CellFieldAmbientBoxReserve
import AVRegularity.CycleComparison.Lift.SettingAmbientCrossTestTransverse
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Lift.SettingTransverseFieldInverseExistence
import AVRegularity.CycleComparison.Lift.SettingWindowInverseClampedTransverse
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

section
section
/-! The simultaneous actual lift induction closes at the original ambient reserve. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_scalar_power_recurrence_data
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hnR : n ≤ N + D) :
    AmbientScalarPowerRecurrenceData par a b P.window lam P₀ (max k (L + 2)) (N + D) N H
      hh n CG Cw Cj Q Cc (physicalEdgeEnvelopeMatrix π edge) := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have main : ∀ r hh, hh ≤ H → ∀ n, n ≤ N + D → ambientRecurrenceRank (N + D) hh n = r →
      AmbientScalarPowerRecurrenceData par a b P.window lam P₀ (max k (L + 2)) (N + D) N H
        hh n CG Cw Cj Q Cc (physicalEdgeEnvelopeMatrix π edge) := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro hh hhh n hnR hr
      have prior : ∀ h' ≤ H, ∀ m ≤ N + D,
          ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
          AmbientScalarPowerRecurrenceData par a b P.window lam P₀ (max k (L + 2)) (N + D) N H
            h' m CG Cw Cj Q Cc (physicalEdgeEnvelopeMatrix π edge) := by
        intro h' hh' m hm hl
        rw [hr] at hl
        exact ih (ambientRecurrenceRank (N + D) h' m) hl h' hh' m hm rfl
      refine ⟨?_, ?_⟩
      · by_cases hn0 : n = 0
        · subst n
          exact liftSequence_degree_zero_scalar_power_data Q sX sZ a b P.window N H Cc hseq
            hh hhh par lam hlam P₀ (max k (L + 2)) (N + D)
            (ambientDegreeSlowReserve P₀ (N + D) 0)
            (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh 0)
            CG Cw Cj (physicalEdgeEnvelopeMatrix π edge)
        · by_cases hnN : n ≤ N
          · exact setting_ambient_positive_coefficient_data_of_earlier_states P sX sZ hsZ Cc hseq
              P₀ hh n hreserve hhh (by omega) hnN prior
          · exact liftSequence_cutoff_scalar_power_data Q sX sZ a b P.window N H Cc hseq hh hhh n
              (by omega) par lam P₀ (max k (L + 2)) (N + D)
              (ambientDegreeSlowReserve P₀ (N + D) n)
              (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) hnR
              CG Cw Cj (physicalEdgeEnvelopeMatrix π edge)
      · intro hn
        exact setting_ambient_uncentered_data_of_earlier_coefficients P sX sZ Cc hseq P₀ hh n
          hreserve hhh hn hnR (fun h hh m hm hl => (prior h hh m hm hl).coefficient)
  exact main (ambientRecurrenceRank (N + D) hh n) hh hhh n hnR rfl

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The completed ambient induction supplies admissibility of the literal centered inverse source. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_actual_source_data
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hhh : hh ≤ H)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∃ Ks : (Vec 2 →L[ℝ] ℝ) → ℝ,
      AmbientLiftSourceData par a b P.window lam hh n
        (ambientDegreeSlowReserve P₀ (N + D) n)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) Q Cc Ks
        (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  have hnR : n ≤ N + D := by omega
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n
  let Budget := fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m
    CG Cw Cj
  let KM := fun h m => ambientUncenteredBudget P₀ (max k (L + 2)) D H (N + D) h m CG Cw Cj Budget
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq P₀ hreserve
    hh hhh n hnR
  have hcoef j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftCoefficientData par a b P.window lam j p q (Cc ab.1 j)
        (fun v u => Budget ab.1 j * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.1 v u) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hd := (setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq P₀ hreserve
      ab.1 (by omega) j (by omega)).coefficient
    exact hd.mono (ambientDegreeSlowReserve_mono P₀ (N + D) n j (by omega))
      (ambientDegreeFastReserve_mono (max k (L + 2)) D H (N + D) hh ab.1 n j (by omega) (by omega))
  have hmean j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftUncenteredData par a b P.window lam ab.2 (n - j) (p + j) q Q Cc
        (KM ab.2 (n - j)) (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.2) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hd := (setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq P₀ hreserve
      ab.2 (by omega) (n - j) (by omega)).uncentered (by omega)
    apply hd.mono
    · have he := ambientDegreeSlowReserve_source P₀ (N + D) n j hnR (by omega)
      change p + j ≤ _
      rw [← he]
    · exact ambientDegreeFastReserve_mono (max k (L + 2)) D H (N + D) hh ab.2 n (n - j)
        (by omega) (Nat.sub_le _ _)
  exact ⟨_, ambient_ordered_centered_source_data par a b P.window lam hlam hh n p q
    sX sZ N H Q Cc hseq hhh hnN (physicalEdgeEnvelopeMatrix π edge)
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) Budget
    (fun h m => ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ h m _ _ _) (KM hh n) KM
    (state.uncentered hn) hcoef hmean⟩

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The completed native induction supplies the literal source with its exact fixed scalar budget. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_actual_source_fixed_data
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hhh : hh ≤ H)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    AmbientLiftSourceData par a b P.window lam hh n
        (ambientDegreeSlowReserve P₀ (N + D) n)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) Q Cc
        (ambientCenteredBudget P₀ (max k (L + 2)) D H (N + D) hh n CG Cw Cj
          (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj))
        (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  have hnR : n ≤ N + D := by omega
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n
  let Budget := fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m
    CG Cw Cj
  let KM := fun h m => ambientUncenteredBudget P₀ (max k (L + 2)) D H (N + D) h m CG Cw Cj Budget
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq P₀ hreserve
    hh hhh n hnR
  have hcoef j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftCoefficientData par a b P.window lam j p q (Cc ab.1 j)
        (fun v u => Budget ab.1 j * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.1 v u) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hd := (setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq P₀ hreserve
      ab.1 (by omega) j (by omega)).coefficient
    exact hd.mono (ambientDegreeSlowReserve_mono P₀ (N + D) n j (by omega))
      (ambientDegreeFastReserve_mono (max k (L + 2)) D H (N + D) hh ab.1 n j (by omega) (by omega))
  have hmean j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftUncenteredData par a b P.window lam ab.2 (n - j) (p + j) q Q Cc
        (KM ab.2 (n - j)) (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.2) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hd := (setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq P₀ hreserve
      ab.2 (by omega) (n - j) (by omega)).uncentered (by omega)
    apply hd.mono
    · have he := ambientDegreeSlowReserve_source P₀ (N + D) n j hnR (by omega)
      change p + j ≤ _
      rw [← he]
    · exact ambientDegreeFastReserve_mono (max k (L + 2)) D H (N + D) hh ab.2 n (n - j)
        (by omega) (Nat.sub_le _ _)
  have source := ambient_ordered_centered_source_data par a b P.window lam hlam hh n p q
    sX sZ N H Q Cc hseq hhh hnN (physicalEdgeEnvelopeMatrix π edge)
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) Budget
    (fun h m => ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ h m _ _ _) (KM hh n) KM
    (state.uncentered hn) hcoef hmean
  dsimp only [p, q, Budget, KM] at source
  rw [orderedCenteredScalarConstant_eq_ambientCenteredBudget P₀ (max k (L + 2)) D H (N + D)
    hh n hnR CG Cw Cj] at source
  exact source

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The first graded mean vanishes whenever the sequence supplies the needed fast source reserve. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftMean_first_positive_zero_ambient (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) hh 1 t X = 0 := by
  have hprev : hh - 1 ≤ H := by omega
  let Φ := liftApply 1 (Cc (hh - 1) 1) (fun _ => f) t
  let Ψ := liftApply 0 (Cc (hh - 1) 0) (fun _ => f) t
  have hres : 0 + (N + D) ≤ qs := by
    have h := setting_ambient_output_supported P
    omega
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq 0 hres
    (hh - 1) hprev 1 (by have hN := P.N_ge; omega)
  have hfast : D ≤ ambientDegreeFastReserve (max k (L + 2)) D H (N + D) (hh - 1) 1 := by
    have hN := P.N_ge
    have he := ambientDegreeFastReserve_original_orders (max k (L + 2)) D H N (hh - 1) 1 hN
    omega
  have hbox : IsBoxSmooth 0 D Φ := liftApply_box_reserve 1 0 D _ (fun _ => f) t
    (hf.of_le (by simp)) (fun m hm α v u =>
      (state.coefficient.box m hm α v u t ht).mono (Nat.zero_le _) hfast)
  have hPhi : ContDiff ℝ (D : ℕ∞) (Φ X) := hbox.1 X
  have hper := liftApply_periodic Q sX sZ a b N H Cc hseq (hh - 1) hprev 1 (fun _ => f) t ht X
  have hc := fun v u d γ hγ α => setting_source_fast_contDiff P t ht v u d γ hγ α X
  have hm0 := fieldCellMean_sourceCoeff_zero Q.edge Q.η t Φ X hPhi hper hc
  have hi0 := Calculus.continuous_integrableOn_unitCell
    (sourceCoeff_zero_continuous Q.edge Q.η t Φ X hPhi hc)
  have hepos : liftApply 0 (Cc hh 0) (fun _ => f) t = 0 := by
    simpa only [Pi.zero_apply] using! congrFun
      (liftApply_positive_grade_zero_degree Q sX sZ a b N H Cc hseq hh hhpos hhh (fun _ => f)) t
  have hB1 : cellB1 Q.η Q.G Q.v t (liftApply 0 (Cc hh 0) (fun _ => f) t) = 0 := by
    rw [hepos]
    exact cellB1_zero_input Q.η Q.G Q.v t
  have heA : liftA Q Cc (fun _ => f) hh 1 t = fun X z =>
      -(sourceCoeff Q.edge Q.η 0 t Φ X z + sourceCoeff Q.edge Q.η 1 t Ψ X z) := by
    have hD : min D 1 = 1 := Nat.min_eq_right (by have hd := P.D_ge; omega)
    funext Y z
    simp [liftA, hB1, show hh ≠ 0 by omega, hD, Finset.sum_range_succ, Φ, Ψ]
  have hΨ : Ψ = if hh = 1 then (fun (X : Vec 2) (_ : Vec 2) => f X) else 0 := by
    by_cases h1 : hh = 1
    · subst hh
      simp only [ite_true]
      funext Y z
      exact hseq.1 f hf t ht Y z
    · simp only [ite_eq_right h1]
      simpa only [Pi.zero_apply] using! congrFun
        (liftApply_positive_grade_zero_degree Q sX sZ a b N H Cc hseq (hh - 1)
          (by omega) hprev (fun _ => f)) t
  have hm1 : fieldCellMean (fun z => sourceCoeff Q.edge Q.η 1 t Ψ X z) = 0 := by
    by_cases h1 : hh = 1
    · rw [hΨ]
      simp only [ite_eq_left h1]
      exact setting_first_source_mean P f hf t ht X
    · rw [hΨ]
      simp only [ite_eq_right h1]
      simp [sourceCoeff_zero_input, fieldCellMean]
  have hi1 : IntegrableOn (fun z => sourceCoeff Q.edge Q.η 1 t Ψ X z) (unitCell 2) := by
    by_cases h1 : hh = 1
    · rw [hΨ]
      simp only [ite_eq_left h1]
      exact Calculus.continuous_integrableOn_unitCell
        (sourceCoeff_one_independent_continuous Q.edge Q.η t f (hf.of_le (by simp))
          (setting_source_fast_contDiff_one P t ht) (setting_source_slow_contDiff_one P t ht) X)
    · rw [hΨ]
      simp only [ite_eq_right h1]
      simp [sourceCoeff_zero_input]
  have hm0' : (∫ z in unitCell 2, sourceCoeff Q.edge Q.η 0 t Φ X z) = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hm0
  have hm1' : (∫ z in unitCell 2, sourceCoeff Q.edge Q.η 1 t Ψ X z) = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hm1
  simp only [liftMean, heA, fieldCellMean, ← integral_unitCell_eq_unitCube,
    integral_neg, integral_add hi0 hi1, hm0', hm1', add_zero, neg_zero]

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The first graded mean vanishes whenever the sequence supplies the needed fast source reserve. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftMean_first_positive_zero_of_predecessor_fields
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hh : ℕ) (hhpos : 1 ≤ hh) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2)
    (hinit : ∀ h₀, liftApply 0 (Cc h₀ 0) (fun _ => f) t =
      fun Y _ => if h₀ = 0 then f Y else 0)
    (hPhi : ContDiff ℝ (D : ℕ∞)
      (liftApply 1 (Cc (hh - 1) 1) (fun _ => f) t X))
    (hper : AVenhance.IsZ2Periodic
      (liftApply 1 (Cc (hh - 1) 1) (fun _ => f) t X)) :
    liftMean Q Cc (fun _ => f) hh 1 t X = 0 := by
  let Φ := liftApply 1 (Cc (hh - 1) 1) (fun _ => f) t
  let Ψ := liftApply 0 (Cc (hh - 1) 0) (fun _ => f) t
  have hc := fun v u d γ hγ α => setting_source_fast_contDiff P t ht v u d γ hγ α X
  have hm0 := fieldCellMean_sourceCoeff_zero Q.edge Q.η t Φ X hPhi hper hc
  have hi0 := Calculus.continuous_integrableOn_unitCell
    (sourceCoeff_zero_continuous Q.edge Q.η t Φ X hPhi hc)
  have hepos : liftApply 0 (Cc hh 0) (fun _ => f) t = 0 := by
    simpa only [ite_eq_right (by omega : hh ≠ 0)] using! hinit hh
  have hB1 : cellB1 Q.η Q.G Q.v t (liftApply 0 (Cc hh 0) (fun _ => f) t) = 0 := by
    rw [hepos]
    exact cellB1_zero_input Q.η Q.G Q.v t
  have heA : liftA Q Cc (fun _ => f) hh 1 t = fun X z =>
      -(sourceCoeff Q.edge Q.η 0 t Φ X z + sourceCoeff Q.edge Q.η 1 t Ψ X z) := by
    have hD : min D 1 = 1 := Nat.min_eq_right (by have hd := P.D_ge; omega)
    funext Y z
    simp [liftA, hB1, show hh ≠ 0 by omega, hD, Finset.sum_range_succ, Φ, Ψ]
  have hΨ : Ψ = if hh = 1 then (fun (X : Vec 2) (_ : Vec 2) => f X) else 0 := by
    dsimp only [Ψ]
    rw [hinit (hh - 1)]
    by_cases h1 : hh = 1
    · subst hh
      simp
    · simp only [ite_eq_right h1, ite_eq_right (by omega : hh - 1 ≠ 0)]
      rfl
  have hm1 : fieldCellMean (fun z => sourceCoeff Q.edge Q.η 1 t Ψ X z) = 0 := by
    by_cases h1 : hh = 1
    · rw [hΨ]
      simp only [ite_eq_left h1]
      exact setting_first_source_mean P f hf t ht X
    · rw [hΨ]
      simp only [ite_eq_right h1]
      simp [sourceCoeff_zero_input, fieldCellMean]
  have hi1 : IntegrableOn (fun z => sourceCoeff Q.edge Q.η 1 t Ψ X z) (unitCell 2) := by
    by_cases h1 : hh = 1
    · rw [hΨ]
      simp only [ite_eq_left h1]
      exact Calculus.continuous_integrableOn_unitCell
        (sourceCoeff_one_independent_continuous Q.edge Q.η t f (hf.of_le (by simp))
          (setting_source_fast_contDiff_one P t ht) (setting_source_slow_contDiff_one P t ht) X)
    · rw [hΨ]
      simp only [ite_eq_right h1]
      simp [sourceCoeff_zero_input]
  have hm0' : (∫ z in unitCell 2, sourceCoeff Q.edge Q.η 0 t Φ X z) = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hm0
  have hm1' : (∫ z in unitCell 2, sourceCoeff Q.edge Q.η 1 t Ψ X z) = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hm1
  simp only [liftMean, heA, fieldCellMean, ← integral_unitCell_eq_unitCube,
    integral_neg, integral_add hi0 hi1, hm0', hm1', add_zero, neg_zero]

end AVRegularity.CycleComparison.Lift
end
end

section
/-! Original native reserves control every source predecessor, including zero coefficients above both cutoffs. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_lift_all_degree_coefficient_transverse
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n m : ℕ) (α : DerivativeWord2 m) (v u : ι) :
    IsTransverseOn par (Set.Icc a b) (fun t X z => Cc hh n m α t X z v u) := by
  by_cases hn : n ≤ N
  · by_cases hm : m ≤ n
    · have hreserve : 0 + (N + D) ≤ qs := by
        have := setting_ambient_output_supported P
        omega
      have data := (setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
        0 hreserve hh hhh n (by omega)).coefficient
      exact data.transverse m hm α v u
    · intro t _ht X z s
      change Cc hh n m α t X (z + s • basisVec par) v u = Cc hh n m α t X z v u
      rw [hseq.2.2.2.1 hh hhh n m (by omega) α t X _ v u,
        hseq.2.2.2.1 hh hhh n m (by omega) α t X z v u]
  · intro t _ht X z s
    change Cc hh n m α t X (z + s • basisVec par) v u = Cc hh n m α t X z v u
    rw [hseq.2.2.1 hh hhh n (by omega) m α t X _ v u,
      hseq.2.2.1 hh hhh n (by omega) m α t X z v u]

include P in
theorem setting_lift_all_degree_apply_transverse
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (f : ℝ → Vec 2 → ∀ i, h i) :
    IsTransverseOn par (Set.Icc a b) (liftApply n (Cc hh n) f) :=
  liftApply_transverse par (Set.Icc a b) n (Cc hh n) f
    (fun m _ α v u => setting_lift_all_degree_coefficient_transverse P sX sZ hsZ
      Cc hseq hh hhh n m α v u)

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The ambient data reserve supplies the full joint source regularity of actual lifts. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftApply_goodField_D (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    GoodField D (liftApply n (Cc hh n) (fun _ => f) t) := by
  have hres : 0 + (N + D) ≤ qs := by
    have h := setting_ambient_output_supported P
    omega
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq 0 hres
    hh hhh n (by omega)
  have hp : D ≤ ambientDegreeSlowReserve 0 (N + D) n := by
    unfold ambientDegreeSlowReserve
    omega
  have hq : D ≤ ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n := by
    have he := ambientDegreeFastReserve_original_orders (max k (L + 2)) D H N hh n hn
    omega
  have hbox := liftApply_box_reserve n D D (Cc hh n) (fun _ => f) t
    (hf.of_le (by simp)) (fun m hm α v u => (state.coefficient.box m hm α v u t ht).mono hp hq)
  exact ⟨hbox.contDiff_uncurry le_rfl le_rfl,
    liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh n (fun _ => f) t ht⟩

include P in
theorem setting_liftApply_goodField_D_all (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    GoodField D (liftApply n (Cc hh n) (fun _ => f) t) := by
  by_cases hn : n ≤ N
  · exact setting_liftApply_goodField_D P sX sZ hsZ Cc hseq hh hhh n hn f hf t ht
  · rw [congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq hh hhh n
      (by omega) (fun _ => f)) t]
    exact GoodField.zero

end AVRegularity.CycleComparison.Lift
end
end

section
/-! Positive source height leaves the coefficient reserves needed for full flux differentiation. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_sourceFlux_left_coefficient_reserve
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (p q : ℕ) (hp : p ≤ D) (hq : q ≤ D + 1)
    (j : ℕ) (hj : j ≤ n) (m : ℕ) (hm : m ≤ n - j) (α : DerivativeWord2 m)
    (u u' : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth (p + j) (q + (D - 1) - j)
      (fun X z => Cc (hh - 1) (n - j) m α t X z u u') := by
  have hres : 0 + (N + D) ≤ qs := by have h := setting_ambient_output_supported P; omega
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    0 hres (hh - 1) (by omega) (n - j) (by omega)
  apply (state.coefficient.box m hm α u u' t ht).mono
  · unfold ambientDegreeSlowReserve
    omega
  · have hheight : 1 ≤ H - (hh - 1) := by omega
    have hD : D ≤ (H - (hh - 1)) * D := by
      simpa only [one_mul] using Nat.mul_le_mul_right D hheight
    have hroom : D ≤ N + D - (n - j) := by omega
    have h2D : 2 * D ≤ 2 * (N + D - (n - j)) := Nat.mul_le_mul_left 2 hroom
    unfold ambientDegreeFastReserve
    have hd := P.D_ge
    omega

end AVRegularity.CycleComparison.Lift
end
end

section
/-! Original native reserves control every source predecessor, including zero coefficients above both cutoffs. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tail_coefficient_data
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (p q : ℕ) (hp : p ≤ K + N + 2 * D + 2) (hq : q ≤ max k (L + 2) + 2 * D)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) :
    AmbientLiftCoefficientData par a b P.window lam n p q (Cc hh n)
      (fun v u => tailCoefficientScalarBudget K k L D H N hh n CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) := by
  by_cases hn : n ≤ N
  · have data := (setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
      (K + N + D + 2) (by have := setting_tail_ambient_supported P; omega) hh hhh n (by omega)).coefficient
    simp only [tailCoefficientScalarBudget, ite_eq_left hn]
    apply data.mono
    · unfold ambientDegreeSlowReserve
      omega
    · have hr : D ≤ N + D - n := by omega
      have := Nat.mul_le_mul_left 2 hr
      unfold ambientDegreeFastReserve
      omega
  · have he : Cc hh n = 0 := by
      funext m α t X z v u
      exact hseq.2.2.1 hh hhh n (by omega) m α t X z v u
    simp only [tailCoefficientScalarBudget, ite_eq_right hn, zero_mul, he]
    exact ambient_zero_coefficient_data par a b P.window lam n p q

end AVRegularity.CycleComparison.Lift
end
end

section
/-! Original native reserves control every source predecessor, including zero coefficients above both cutoffs. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_lift_all_degree_coefficient_box
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (r : ℕ) (hr : r ≤ D) (hh : ℕ) (hhh : hh ≤ H)
    (n m : ℕ) (α : DerivativeWord2 m) (v u : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth r r (fun X z => Cc hh n m α t X z v u) := by
  by_cases hn : n ≤ N
  · by_cases hm : m ≤ n
    · have hreserve : 0 + (N + D) ≤ qs := by
        have := setting_ambient_output_supported P
        omega
      have data := (setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
        0 hreserve hh hhh n (by omega)).coefficient
      apply (data.box m hm α v u t ht).mono
      · unfold ambientDegreeSlowReserve
        omega
      · have hroom : D ≤ N + D - n := by omega
        have := Nat.mul_le_mul_left 2 hroom
        unfold ambientDegreeFastReserve
        omega
    · have he := hseq.2.2.2.1 hh hhh n m (by omega) α t
      simp only [he]
      exact IsBoxSmooth.zero
  · have he := hseq.2.2.1 hh hhh n (by omega) m α t
    simp only [he]
    exact IsBoxSmooth.zero

include P in
theorem setting_lift_all_degree_good_field
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (r : ℕ) (hr : r ≤ D) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    GoodField r (liftApply n (Cc hh n) (fun _ => f) t) := by
  apply liftApply_goodField_of_coefficients r n _ f hf t
  · intro m _ α v u
    exact setting_lift_all_degree_coefficient_box P sX sZ hsZ Cc hseq r hr hh hhh
      n m α v u t ht
  · intro X m _ α v u
    exact (hseq.2.2.2.2.2.1 hh hhh n m α v u t ht).2 X

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The actual truncated lift is a source-regular finite parameter polynomial. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftPolyField_epsPoly_good (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    EpsPoly False N D (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) := by
  refine ⟨fun n => liftApply n (Cc hh n) (fun _ => f) t, ?_, ?_, fun _ _ _ => rfl⟩
  · intro n
    refine ⟨?_, False.elim⟩
    by_cases hn : n ≤ N
    · exact setting_liftApply_goodField_D P sX sZ hsZ Cc hseq hh hhh n hn f hf t ht
    · have he := congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq hh hhh n
        (by omega) (fun _ => f)) t
      dsimp only
      rw [he]
      exact GoodField.zero
  · intro n hn X z
    exact congrFun (congrFun (congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq
      hh hhh n hn (fun _ => f)) t) X) z

end AVRegularity.CycleComparison.Lift
end
end

section
/-! Original native reserves control every source predecessor, including zero coefficients above both cutoffs. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tail_uncentered_data
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (p q : ℕ) (hp : p ≤ K + N + D + 2) (hq : q ≤ max k (L + 2) + D)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) :
    AmbientLiftUncenteredData par a b P.window lam hh n p q Q Cc
      (tailUncenteredScalarBudget K k L D H N hh n p q CG Cw Cj)
      (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  have hdata := setting_tail_ambient_supported P
  have hpdata : p + 1 ≤ qs := by have := P.N_ge; have := P.D_ge; omega
  have hqdata : q + 1 ≤ qf := by
    rw [P.qf_eq]
    have := P.N_ge
    have := P.D_ge
    omega
  apply setting_liftA_power_data_of_predecessors P sX sZ Cc hseq hh n p q hn hhh hpdata hqdata
    (fun h m => tailCoefficientScalarBudget K k L D H N h m CG Cw Cj)
    (fun h m => tailCoefficientScalarBudget_nonneg K k L D H N h m CG Cw Cj)
  · apply setting_tail_coefficient_data P sX sZ hsZ Cc hseq (p + 1) (q + 1)
    · have := P.D_ge; omega
    · have := P.D_ge; omega
    · exact hhh
  · intro _
    apply setting_tail_coefficient_data P sX sZ hsZ Cc hseq (p + 2) q
    · have := P.D_ge; omega
    · have := P.D_ge; omega
    · exact hhh
  · intro hh0 j hj
    have hjD := hj.trans (Nat.min_le_left D n)
    apply setting_tail_coefficient_data P sX sZ hsZ Cc hseq (max D (p + j)) (max D (q + D - j))
    · omega
    · omega
    · omega

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The actual weighted drift coefficient array has ambient regularity and entrywise grading. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_weighted_drift_coefficient_data_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (z : Vec 2) (v u : ι)
    (r : ℕ) (hr : r ≤ P₀ + 1) :
    ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X =>
      weightedLiftCoefficientMean (Cc hh (n - 1))
        (fun t z => Real.sqrt Q.η * Q.v t z k₀) m α t X z v u) ∧
    ∀ X, ‖iteratedFDeriv ℝ r (fun Y =>
      weightedLiftCoefficientMean (Cc hh (n - 1))
        (fun t z => Real.sqrt Q.η * Q.v t z k₀) m α t Y z v u) X‖ ≤
      (2 ^ r * max (Cw 0) 0 *
        ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N hh (n - 1) CG Cw Cj) *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * lam ^ (n - 1 - m + r) := by
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    P₀ hreserve hh hhh (n - 1) (by omega)
  have hp : P₀ + 1 ≤ ambientDegreeSlowReserve P₀ (N + D) (n - 1) := by
    unfold ambientDegreeSlowReserve
    omega
  have hw : Continuous (fun y => Real.sqrt Q.η * Q.v t y k₀) :=
    (setting_normalized_drift_contDiff_one P t ht k₀).continuous
  have hW (y : Vec 2) : ‖Real.sqrt Q.η * Q.v t y k₀‖ ≤ max (Cw 0) 0 := by
    simpa only [norm_iteratedFDeriv_zero] using
      setting_scaled_drift_component_jet_bound P 0 (Nat.zero_le qf) t ht y k₀
  have hd := state.coefficient.weighted_mean_jet_le m hm α v u t ht r (hr.trans hp) _ hw _ hW
  constructor
  · exact hd.1.of_le (show ((P₀ + 1 : ℕ) : WithTop ℕ∞) ≤
      ((ambientDegreeSlowReserve P₀ (N + D) (n - 1) : ℕ) : WithTop ℕ∞) by exact_mod_cast hp)
  · intro X
    simpa only [weightedLiftCoefficientMean, mul_assoc] using hd.2 X

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The actual weighted drift coefficient array has ambient regularity and entrywise grading. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem weightedDriftCoefficient_contDiff_of_data
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n p q : ℕ) (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam (n - 1) p q (Cc hh (n - 1)) M)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (z : Vec 2) (v u : ι) :
    ContDiff ℝ (p : ℕ∞) (fun X =>
      weightedLiftCoefficientMean (Cc hh (n - 1))
        (fun t z => Real.sqrt Q.η * Q.v t z k₀) m α t X z v u) := by
  have hw : Continuous (fun y => Real.sqrt Q.η * Q.v t y k₀) :=
    (setting_normalized_drift_contDiff_one P t ht k₀).continuous
  have hW (y : Vec 2) : ‖Real.sqrt Q.η * Q.v t y k₀‖ ≤ max (Cw 0) 0 := by
    simpa only [norm_iteratedFDeriv_zero] using
      setting_scaled_drift_component_jet_bound P 0 (Nat.zero_le qf) t ht y k₀
  have hd := data.weighted_mean_jet_le m hm α v u t ht 0 (Nat.zero_le p) _ hw _ hW
  simpa only [weightedLiftCoefficientMean] using hd.1

end AVRegularity.CycleComparison.Lift
end
end

section
/-! Every recursion source has a continuous fast slice during its pulse. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem setting_liftA_transverse
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsTransverseOn par (Set.Icc a b) (fun t => liftA Q Cc (fun _ => f) hh n t) := by
  let g := fun (_ : ℝ) => f
  have hΦ (q : ℕ) (hq : q ≤ H) (m : ℕ) :=
    setting_lift_all_degree_apply_transverse P sX sZ hsZ Cc hseq q hq m g
  have hB1 := cellB1_transverse par (Set.Icc a b) Q.η Q.G Q.v
    (liftApply (n - 1) (Cc hh (n - 1)) g) (hΦ hh hhh (n - 1)) (setting_drift_transverse P)
  have hB2 := cellB2_transverse par (Set.Icc a b) Q.η Q.G
    (liftApply (n - 2) (Cc hh (n - 2)) g) (hΦ hh hhh (n - 2))
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have := setting_source_fast_reserve P; have := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, ∀ t ∈ Set.Icc a b,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α t ht =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hS (j : ℕ) : IsTransverseOn par (Set.Icc a b)
      (fun t => sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) g t)) :=
    sourceCoeff_transverse_of_reserved_inputs par (Set.Icc a b) Q.edge
      (by have := P.D_ge; omega) Q.η _ (hΦ (hh - 1) (by omega) (n - j))
      (fun t ht => setting_lift_all_degree_good_field P sX sZ hsZ Cc hseq D le_rfl
        (hh - 1) (by omega) (n - j) f hf t ht) P.transverse hΓ j
  intro t ht X z s
  simp only [liftA]
  have he1 := hB1 t ht X z s
  dsimp only at he1
  rw [he1]
  have he2 : (if 2 ≤ n then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) g t) X (z + s • basisVec par) else 0) =
      if 2 ≤ n then cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) g t) X z else 0 := by
    split_ifs
    · exact hB2 t ht X z s
    · rfl
  rw [he2]
  by_cases hh0 : hh = 0
  · simp only [ite_eq_left hh0]
    rfl
  · simp only [ite_eq_right hh0]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact hS j t ht X z s

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The simultaneous ambient induction controls Wiener jets at every supported slow order. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_sourceFlux_term_grading_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (j : ℕ) (hj : j ≤ n - 1) (A : Vec 2 →L[ℝ] ℝ) (k₀ : Fin 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    IsBoxSmooth (P₀ + 1) 0 (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      sourceFluxComponentCoefficient Q.edge Q.η t
        (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
          (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ j v X z) ∧
    ∀ r ≤ P₀ + 1, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => (Real.exp ((lam • A) Y))⁻¹ •
        sourceFluxComponentCoefficient Q.edge Q.η t
          (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
            (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) k₀ j v Y z) X‖ ≤
        (finiteLiftSymbolBudget (n - 1 - j) A * normalizedSourceUniformConstant D (P₀ + 1) 0 j A Cj *
          ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N
            (hh - 1) (n - 1 - j) CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) *
            lam ^ (n - 1 + r) := by
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    P₀ hreserve (hh - 1) (by omega) (n - 1 - j) (by omega)
  have hres := ambient_flux_predecessor_reserve P₀ (max k (L + 2)) D H (N + D)
    hh n j hhpos hhh hn hnR hj
  have hp : P₀ + 1 ≤ qs := by have hN := P.N_ge; have hD := P.D_ge; omega
  constructor
  · exact setting_ambient_sourceFlux_lift_box P Cc (hh - 1) (n - 1 - j)
      (P₀ + 1) 0 j _ _ hp (Nat.zero_le qf) hres.1 (by simpa only [zero_add] using hres.2)
      _ state.coefficient A k₀ t ht v u ξ
  · intro r hr X z
    have hb := setting_ambient_sourceFlux_lift_bound P Cc (hh - 1) (n - 1 - j)
      (P₀ + 1) 0 j _ _ hp (Nat.zero_le qf) hres.1 (by simpa only [zero_add] using hres.2)
      _ state.coefficient A k₀ t ht v u ξ r 0 hr (Nat.zero_le 0) X z
    have hc : (n - 1 - j) + j = n - 1 := by omega
    rw [finiteMatrixProduct_edge_scalar_power] at hb
    simpa only [norm_mixed_jet_fast_zero, hc, Nat.sub_add_cancel hhpos,
      mul_assoc] using hb

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The simultaneous ambient induction controls Wiener jets at every supported slow order. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_sourceFlux_term_mean_grading_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (j : ℕ) (hj : j ≤ n - 1) (A : Vec 2 →L[ℝ] ℝ) (k₀ : Fin 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) (r : ℕ) (hr : r ≤ P₀ + 1) :
    ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => (Real.exp ((lam • A) X))⁻¹ •
      fieldCellMean (fun z => sourceFluxComponentCoefficient Q.edge Q.η t
        (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
          (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ j v X z)) ∧
    ∀ X, ‖iteratedFDeriv ℝ r (fun Y => (Real.exp ((lam • A) Y))⁻¹ •
      fieldCellMean (fun z => sourceFluxComponentCoefficient Q.edge Q.η t
        (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
          (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) k₀ j v Y z)) X‖ ≤
      (2 ^ r * ambientSourceFluxTermConstant P₀ N k L D H hh n j A CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) *
          lam ^ (n - 1 + r) := by
  have hd := setting_ambient_sourceFlux_term_grading_upto P sX sZ hsZ Cc hseq
    P₀ hreserve hh hhpos hhh n hn hnR j hj A k₀ t ht v u ξ
  let F := fun X z => (Real.exp ((lam • A) X))⁻¹ •
    sourceFluxComponentCoefficient Q.edge Q.η t
      (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ j v X z
  have he : (fun X => fieldCellMean (F X)) = fun X => (Real.exp ((lam • A) X))⁻¹ •
      fieldCellMean (fun z => sourceFluxComponentCoefficient Q.edge Q.η t
        (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
          (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ j v X z) := by
    funext X
    exact AVRegularity.fieldCellMean_smul _ _
  have hb := fieldCellMean_graded_jet_bound (P₀ + 1) r 0 (n - 1) hr F hd.1
    (fun _ => ambientSourceFluxTermConstant P₀ N k L D H hh n j A CG Cw Cj *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) lam
    (fun a ha X z => by simpa only [ambientSourceFluxTermConstant, F] using hd.2 a ha X z)
  rw [he] at hb
  refine ⟨hb.1, fun X => (hb.2 X).trans_eq ?_⟩
  ring

end AVRegularity.CycleComparison.Lift
end
end

section
/-! The ambient recurrence supplies the two cross-operator reserves at every lift degree. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_lift_cross_coefficient_box
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth 2 2 (fun X z => Cc hh n m α t X z v u) := by
  have hr : 0 + (N + D) ≤ qs := by
    have := setting_ambient_output_supported P
    omega
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    0 hr hh hhh n (by omega)
  apply (state.coefficient.box m hm α v u t ht).mono
  · unfold ambientDegreeSlowReserve
    have := P.D_ge
    omega
  · unfold ambientDegreeFastReserve
    have hd := P.D_ge
    have hroom : 2 ≤ N + D - n := by omega
    have hmul := Nat.mul_le_mul_left 2 hroom
    omega

include P in
theorem setting_lift_cross_terms_box
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N) (v : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (d : LeftTerm (∀ i, h i) (h v))
    (hd : d ∈ liftComponentLeftTerms n (Cc hh n) t v) : IsBoxSmooth 2 2 d.coeff :=
  liftComponentLeftTerms_box n (Cc hh n) t v 2 2
    (fun m hm α u => setting_lift_cross_coefficient_box P sX sZ hsZ Cc hseq
      hh hhh n hn m hm α v u t ht) d hd

include P in
theorem setting_lift_cross_field_box
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth 2 2 (liftApply n (Cc hh n) (fun _ => f) t) :=
  liftApply_box_reserve n 2 2 (Cc hh n) (fun _ => f) t (hf.of_le (by simp))
    (fun m hm α v u => setting_lift_cross_coefficient_box P sX sZ hsZ Cc hseq
      hh hhh n hn m hm α v u t ht)

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The simultaneous ambient induction controls energy jets at every supported slow order. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_energy_grading_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hΘ : 0 ≤ Θ) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (m r : ℕ) (hm : m ≤ n) (hr : r ≤ P₀) :
    schurEnergyJet π (Set.Icc a b) k r (Cc hh n m) ≤
      ENNReal.ofReal (((2 ^ m : ℝ) * (k + 1) * 2 ^ (r + 1) *
        ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N hh n CG Cw Cj) *
        Θ ^ hh * lam ^ (n - m + r)) := by
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    P₀ hreserve hh hhh n (by omega)
  have hp : r ≤ ambientDegreeSlowReserve P₀ (N + D) n := by
    unfold ambientDegreeSlowReserve
    omega
  have hq : k + 1 ≤ ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n := by
    have he := ambientDegreeFastReserve_original_orders (max k (L + 2)) D H N hh n hn
    have hD := P.D_ge
    have hk := Nat.le_max_left k (L + 2)
    omega
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  exact physical_power_schurEnergyJet_le π P.mass_pos edge Θ hΘ
    ⟨P.envelope.nonneg, P.envelope.row_sum, P.envelope.col_sum⟩ hh _
    (ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _)
    state.coefficient hlam hm hp hq

end AVRegularity.CycleComparison.Lift
end
end
