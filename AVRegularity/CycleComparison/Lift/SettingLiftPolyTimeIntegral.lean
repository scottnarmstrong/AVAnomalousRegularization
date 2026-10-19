-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
public import AVRegularity.CycleComparison.Lift.LiftSourceBlockCoefficientAction
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original data reserve supports every actual uncentered rank step, including truncated predecessors. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_first_mean_of_predecessors
    (P₀ hh : ℕ) (hhh : hh ≤ H)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh 1 →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q (constructedLiftCoefficients Q a b P.window par N) (fun _ => f) hh 1 t X = 0 := by
  let Cc := constructedLiftCoefficients Q a b P.window par N
  have hinit := fun h₀ => constructedLiftApply_zero_degree Q a b P.window par N h₀ (fun _ => f) t
  by_cases hh0 : hh = 0
  · subst hh
    exact liftMean_first_diagonal_zero_of_initial_action P Cc f t ht X
      (by simpa only [ite_true] using hinit 0)
  · have hg := setting_constructed_source_predecessor_good P P₀ hh 1 hhh (by omega)
      prior f hf t ht 1
    exact liftMean_first_positive_zero_of_predecessor_fields P Cc f hf hh (by omega)
      t ht X hinit (hg.contDiff_slice X) (hg.2 X)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite calibration extracts the actual symmetric centered-source coefficient. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_calibratedLiftSourceEntry_eq
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (hlam : lam ≠ 0)
    (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z =
      leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w)
        m α t X z v u ξ := by
  let c := leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w)
  have hnorm A := setting_liftSource_blockCoefficient_normalized P sX sZ hsX hsZ
    Cc hseq hh hhh n hn hnN A u v ξ t ht X z
  unfold calibratedLiftSourceEntry
  have he : (∑ p : Fin (m + 1) × Fin (n + 1), liftCalibrationWeight n m α lam p •
      normalizedLiftSourceField Q Cc hh n
        (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v ξ t X z) =
      ∑ p : Fin (m + 1) × Fin (n + 1), liftCalibrationWeight n m α lam p •
        normalizedLiftTestField c n
          (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v ξ t X z := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hnorm]
  rw [he]
  exact liftCalibration_synthesis n m hm c lam hlam
    (fun β σ => leftTermsBlockCoefficient_perm _ m β σ) α t X z v u ξ

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original data reserve supports every actual uncentered rank step, including truncated predecessors. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructedLift_uncentered_of_predecessor_data
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hhh : hh ≤ H)
    (hn : 1 ≤ n) (hnR : n ≤ N + D)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u)) :
    AmbientLiftUncenteredData par a b P.window lam hh n (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) Q (constructedLiftCoefficients Q a b P.window par N)
      (ambientUncenteredBudget P₀ (max k (L + 2)) D H (N + D) hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj))
      (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  exact setting_ambient_uncentered_data_of_predecessor_family P
    (constructedLiftCoefficients Q a b P.window par N)
    (fun h n m α v u t _ X =>
      constructedLiftCoefficients_periodic Q a b P.window par N h n m α t X v u)
    (fun h _ n hn => constructedLiftCoefficients_cutoff Q a b P.window par N h n hn)
    P₀ hh n hreserve hhh hn hnR prior

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Earlier constructed coefficient data and means supply the literal centered source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_source_data_of_predecessors
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hhh : hh ≤ H)
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u))
    (hmeans : ∀ h' ≤ H, ∀ m, 1 ≤ m → m ≤ N + D →
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      ∀ d ≤ m, ∀ α : DerivativeWord2 d, ∀ v u, ∀ t ∈ Set.Icc a b, ∀ X, ∀ ξ : h u,
        fieldCellMean (fun z => constructedLiftCoefficients Q a b P.window par N h' m
          d α t X z v u ξ) = 0) :
    AmbientLiftSourceData par a b P.window lam hh n
      (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) Q
      (constructedLiftCoefficients Q a b P.window par N)
      (ambientCenteredBudget P₀ (max k (L + 2)) D H (N + D) hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj))
      (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  have hnR : n ≤ N + D := by omega
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  let Cc := constructedLiftCoefficients Q a b P.window par N
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n
  let Budget := fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m
    CG Cw Cj
  let KM := fun h m => ambientUncenteredBudget P₀ (max k (L + 2)) D H (N + D) h m CG Cw Cj Budget
  have uncentered := setting_constructedLift_uncentered_of_predecessor_data P
    P₀ hh n hreserve hhh hn hnR prior
  have hcoef j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftCoefficientData par a b P.window lam j p q (Cc ab.1 j)
        (fun v u => Budget ab.1 j * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.1 v u) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hlt := ambientRecurrenceRank_composition (N + D) hh n ab.1 j
      (by omega) hnR (by omega)
    have hd := prior ab.1 (by omega) j (by omega) hlt
    exact hd.mono (ambientDegreeSlowReserve_mono P₀ (N + D) n j (by omega))
      (ambientDegreeFastReserve_mono (max k (L + 2)) D H (N + D) hh ab.1 n j (by omega) (by omega))
  have hmean j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftUncenteredData par a b P.window lam ab.2 (n - j) (p + j) q Q Cc
        (KM ab.2 (n - j)) (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.2) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hlt := ambientRecurrenceRank_composition (N + D) hh n ab.2 (n - j)
      (by omega) hnR (by omega)
    have hd := setting_constructedLift_uncentered_of_predecessor_data P P₀ ab.2 (n - j)
      hreserve (by omega) (by omega) (by omega)
      (fun h' hh' m hm hlt' => prior h' hh' m hm (hlt'.trans hlt))
    apply hd.mono
    · have he := ambientDegreeSlowReserve_source P₀ (N + D) n j hnR (by omega)
      change p + j ≤ _
      rw [← he]
    · exact ambientDegreeFastReserve_mono (max k (L + 2)) D H (N + D) hh ab.2 n (n - j)
        (by omega) (Nat.sub_le _ _)
  have source := ambient_ordered_centered_source_data_of_coefficients par a b P.window lam hlam
    hh n p q Q Cc
    (fun j _ ab _ m _ α v u t _ X =>
      constructedLiftCoefficients_periodic Q a b P.window par N ab.1 j m α t X v u)
    (fun j hj ab hab' m hm α v u t ht X ξ => by
      have hj' := Finset.mem_Icc.mp hj
      have hab'' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab'
      exact hmeans ab.1 (by omega) j (by omega) (by omega)
        (ambientRecurrenceRank_composition (N + D) hh n ab.1 j (by omega) hnR (by omega))
        m hm α v u t ht X ξ)
    (physicalEdgeEnvelopeMatrix π edge)
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) Budget
    (fun h m => ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ h m _ _ _) (KM hh n) KM
    uncentered hcoef hmean
  dsimp only [p, q, Budget, KM] at source
  rw [orderedCenteredScalarConstant_eq_ambientCenteredBudget P₀ (max k (L + 2)) D H (N + D)
    hh n hnR CG Cw Cj] at source
  exact source

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original data reserve supports every actual uncentered rank step, including truncated predecessors. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_mean_flux_regular_of_predecessors
    (P₀ hh n p : ℕ) (hhh : hh ≤ H) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (hp : p + D + 1 ≤ P₀) (hreserve : P₀ + (N + D) ≤ qs)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u))
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (z : Vec 2) (v u : ι) :
    ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X =>
      actualMeanFluxCoefficient Q (constructedLiftCoefficients Q a b P.window par N)
        hh n k₀ m α t X z v u) := by
  let Cc := constructedLiftCoefficients Q a b P.window par N
  let M := fun h m v u => ambientCoefficientScalarBudget P₀ (max k (L + 2))
    D H (N + D) N h m CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h v u
  have hd := prior hh hhh (n - 1) (by omega)
    (ambientRecurrenceRank_degree (N + D) hh n 1 (by omega) (by omega))
  have hd' : AmbientLiftCoefficientData par a b P.window lam (n - 1) (p + 1) 0
      (Cc hh (n - 1)) (M hh (n - 1)) := hd.mono
    (by unfold ambientDegreeSlowReserve; omega) (Nat.zero_le _)
  by_cases hh0 : hh = 0
  · subst hh
    simpa only [actualMeanFluxCoefficient, ite_true] using
      diagonalMeanFluxCoefficient_contDiff_of_predecessor_data P Cc n (p + 1) 0
        (by omega) _ hd' k₀ t ht m hm α z v u
  · have hs : ∀ j ≤ min (D - 1) (n - 1),
        AmbientLiftCoefficientData par a b P.window lam (n - 1 - j)
          (p + 1 + j) (D - 1 - j) (Cc (hh - 1) (n - 1 - j)) (M (hh - 1) (n - 1 - j)) := by
      intro j hj
      have hjD := hj.trans (min_le_left _ _)
      by_cases hi : n - 1 - j ≤ N
      · have state := prior (hh - 1) (by omega) (n - 1 - j) (by omega)
          (ambientRecurrenceRank_height (N + D) hh n (hh - 1) (n - 1 - j)
            (by omega) (by omega))
        apply state.mono
        · unfold ambientDegreeSlowReserve
          omega
        · have hroom : D ≤ N + D - (n - 1 - j) := by omega
          have htwice := Nat.mul_le_mul_left 2 hroom
          unfold ambientDegreeFastReserve
          omega
      · dsimp only [M]
        rw [ambientCoefficientScalarBudget_cutoff P₀ (max k (L + 2)) D H (N + D) N
          (hh - 1) (n - 1 - j) (by omega) (by omega)]
        dsimp only [Cc]
        rw [constructedLiftCoefficients_cutoff Q a b P.window par N (hh - 1)
          (n - 1 - j) (by omega)]
        simp only [zero_mul]
        exact ambient_zero_coefficient_data par a b P.window lam (n - 1 - j)
          (p + 1 + j) (D - 1 - j)
    have hg (A : Vec 2 →L[ℝ] ℝ) (ξ : h u) (i : ℕ) :=
      setting_constructed_source_predecessor_good P P₀ hh n hhh (by omega) prior
        (fun Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
        ((Real.contDiff_exp.comp (lam • A).contDiff).smul contDiff_const) t ht i
    have hcut (A : Vec 2 →L[ℝ] ℝ) (ξ : h u) (i : ℕ) (hi : N < i) :=
      congrFun (constructedLiftApply_cutoff Q a b P.window par N (hh - 1) i hi
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)) t
    simpa only [actualMeanFluxCoefficient, ite_eq_right hh0] using
      positiveMeanFluxCoefficient_contDiff_of_predecessor_data P Cc hh n (p + 1) 0
        (by omega) _ hd' (fun j => M (hh - 1) (n - 1 - j)) hs t ht k₀ u v hg hcut m hm α z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal finite tail action holds at every degree under the original lift setting. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftTail_leftTerms_apply
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (liftTailLeftTerms Q Cc N hh n t v) f X z =
      liftTailCoeff Q Cc N (fun _ => f) hh n t X z v := by
  apply liftTailLeftTerms_apply_of_representations Q Cc N hh n t v f hf X z
  · exact setting_liftA_leftTerms_apply_all_degrees P sX sZ (by omega) Cc hseq
      hh hhh n f hf t ht X z v
  · intro r hr _ hn2 hnR p hp d hd
    have hab := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hreserve : r + (N + D) ≤ qs := by
      have := setting_tail_ambient_supported P
      omega
    exact setting_actualMeanLeftTerms_box_upto P sX sZ (by omega) Cc hseq r 0
      hreserve p.2 (by omega) (n - r) hn2 hnR t ht d hd
  · intro r _ _ hn2 hnR p hp Y
    have hab := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact setting_actualMeanLeftTerms_apply P sX sZ hsX hsZ Cc hseq
      p.2 (by omega) (n - r) hn2 hnR f hf t ht Y z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite recurrence right side is exactly the literal truncated lift identity, including its tail. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftPositiveTimeRhs_identity
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    liftPositiveTimeRhs Q Cc N ε hh f t X z =
      -(cellOperator (Q.G t X) (Q.v t) (liftPolyField Cc N ε hh (fun _ => f) t X) z +
        ε • cellB1 Q.η Q.G Q.v t (liftPolyField Cc N ε hh (fun _ => f) t) X z +
        ε ^ 2 • cellB2 Q.η Q.G t (liftPolyField Cc N ε hh (fun _ => f) t) X z) +
      (if hh = 0 then 0 else sourceOp Q.edge Q.η ε t
        (liftPolyField Cc N ε (hh - 1) (fun _ => f) t) X z) +
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => f) p.2) t X z) +
      ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n •
        liftTailCoeff Q Cc N (fun _ => f) hh n t X z := by
  have hlow : liftPositiveTimeRhs Q Cc N ε hh f t X z =
      -(∑ n ∈ Finset.Icc 1 N, ε ^ n •
        cellOperator (Q.G t X) (Q.v t) (liftApply n (Cc hh n) (fun _ => f) t X) z) +
      (-(∑ n ∈ Finset.Icc 1 N, ε ^ n • liftA Q Cc (fun _ => f) hh n t X z) +
        ∑ n ∈ Finset.Icc 1 N, ε ^ n •
          liftMeanCompositionCoefficient Q Cc N (fun _ => f) hh n t X z) := by
    unfold liftPositiveTimeRhs
    have hsource : (∑ n ∈ Finset.Icc 1 N, ε ^ n • liftCellSource Q Cc (fun _ => f) hh n t X z) =
        ∑ n ∈ Finset.Icc 1 N, ε ^ n • (-liftA Q Cc (fun _ => f) hh n t X z +
          liftMeanCompositionCoefficient Q Cc N (fun _ => f) hh n t X z) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [setting_liftCellSource_low_degree P sX sZ hsX hsZ Cc hseq hh hhh n
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 f hf t ht X z]
    simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [hsource]
    simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [hlow, ← setting_liftPoly_cellOperator_positive P sX sZ (by omega) Cc hseq hh hhh ε f hf t ht X z]
  rw [polynomial_tail_cancellation N (2 * N + D) (by omega)]
  rw [setting_liftA_polynomial P sX sZ (by omega) Cc hseq hh hhh
    (2 * N + D) (by omega) ε f hf t ht X z]
  rw [← setting_lift_mean_composition_polynomial P sX sZ hsX hsZ Cc hseq hh hhh ε f hf t ht X z]
  simp only [← liftTailCoeff_eq_difference]
  abel

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The symmetric coefficient array represents the exact tail and its tested fields are centered. -/

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
theorem setting_tail_coefficient_normalized_test_eq
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    normalizedLiftTestField (tailLeftCoefficient Q Cc N hh n) n A u v ξ t X z =
      normalizedLiftTailField Q Cc N hh n A u v ξ t X z := by
  let f : Vec 2 → ∀ i, h i := fun Y => Real.exp (A Y) • Pi.single u ξ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  have he := (tailLeftCoefficient_degree_action Q Cc N hh n hn f hf t X z v).trans
    (setting_liftTail_leftTerms_apply P sX sZ hsX hsZ Cc hseq hh hhh n f hf t ht X z v)
  exact congrArg (fun y => (Real.exp (A X))⁻¹ • y) he
end

/-! The symmetric coefficient array represents the exact tail and its tested fields are centered. -/

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
theorem setting_tailLeftCoefficient_apply
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply (2 * N + D) (tailLeftCoefficient Q Cc N hh n) (fun _ => f) t X z =
      liftTailCoeff Q Cc N (fun _ => f) hh n t X z := by
  funext v
  exact (tailLeftCoefficient_action Q Cc N hh n hn hnR f hf t X z v).trans
    (setting_liftTail_leftTerms_apply P sX sZ hsX hsZ Cc hseq hh hhh n f hf t ht X z v)

include P in
theorem setting_tailLeftCoefficient_apply_mean_zero
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    fieldCellMean (fun z => liftApply (2 * N + D) (tailLeftCoefficient Q Cc N hh n)
      (fun _ => f) t X z) = 0 := by
  have he : (fun z => liftApply (2 * N + D) (tailLeftCoefficient Q Cc N hh n)
      (fun _ => f) t X z) = fun z => liftTailCoeff Q Cc N (fun _ => f) hh n t X z := by
    funext z
    exact setting_tailLeftCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n
      (by omega) hnR f hf t ht X z
  rw [he]
  exact setting_liftTailCoeff_mean_zero P sX sZ hsX hsZ Cc hseq hh hhh n hn f hf t ht X
end

/-! The symmetric coefficient array represents the exact tail and its tested fields are centered. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
theorem setting_liftTailCoeff_constant_zero
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (c0 : ∀ i, h i)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    liftTailCoeff Q Cc N (fun _ _ => c0) hh n t = 0 := by
  have hz := liftSequence_constants_zero P sX sZ Cc hseq c0
  have hA := liftA_const_zero_lex Q sX sZ a b N H Cc hseq c0 hh n hhh
    (fun q hq d hd _ => hz q (hq.trans hhh) d hd)
    hh n le_rfl hn (Or.inr le_rfl) t ht
  funext X z
  simp only [liftTailCoeff, hA, Pi.zero_apply, zero_sub, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro r hr
  split_ifs with hbound
  · apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hm := liftSequence_constant_means_zero P sX sZ Cc hseq c0
      p.2 (by omega) (n - r) (by omega) t ht
    have he := liftApply_congr_time r (Cc p.1 r)
      (liftMean Q Cc (fun _ _ => c0) p.2 (n - r)) 0 t hm
    rw [he, liftApply_zero]
    rfl
  · rfl

include P in
theorem setting_tailLeftCoefficient_zero_order
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (α : DerivativeWord2 0) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (X z : Vec 2) (v u : ι) :
    tailLeftCoefficient Q Cc N hh n 0 α t X z v u = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  have he := setting_tailLeftCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnR
    (fun _ => Pi.single u ξ) contDiff_const t ht X z
  have hz := congrFun (congrFun (congrFun
    (setting_liftTailCoeff_constant_zero P sX sZ Cc hseq (Pi.single u ξ)
      hh hhh n hn t ht) X) z) v
  have hv := congrFun he v
  rw [liftApply_constant_single (2 * N + D) (tailLeftCoefficient Q Cc N hh n)
    α t X z v u ξ] at hv
  exact hv.trans hz
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original data reserve supports every actual uncentered rank step, including truncated predecessors. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_mean_action_of_predecessors
    (P₀ hh n : ℕ) (hhh : hh ≤ H) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (hp : D + 1 ≤ P₀) (hreserve : P₀ + (N + D) ≤ qs)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u))
    (hmeans : ∀ h' ≤ H, ∀ i, 1 ≤ i → i ≤ N + D →
      ambientRecurrenceRank (N + D) h' i < ambientRecurrenceRank (N + D) hh n →
      ∀ m ≤ i, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Set.Icc a b, ∀ X, ∀ ξ : h u,
        fieldCellMean (fun z => constructedLiftCoefficients Q a b P.window par N h' i
          m α t X z v u ξ) = 0)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    leftTermsApply (actualMeanLeftTerms Q
      (constructedLiftCoefficients Q a b P.window par N) hh n t) f X z =
      liftMean Q (constructedLiftCoefficients Q a b P.window par N) (fun _ => f) hh n t X := by
  let Cc := constructedLiftCoefficients Q a b P.window par N
  have hb (i : ℕ) (hi : i < n) (m : ℕ) (hm : m ≤ i)
      (α : DerivativeWord2 m) (v u : ι) :=
    setting_constructed_predecessor_coefficient_box P P₀ hh n prior hh i 2 hhh
      P.D_ge (by omega) (ambientRecurrenceRank_composition (N + D) hh n hh i le_rfl hnR hi)
      m hm α u v t ht
  have hg := setting_constructed_predecessor_good_field P P₀ hh n prior hh (n - 1) 2 hhh
    P.D_ge (by omega) (ambientRecurrenceRank_degree (N + D) hh n 1 (by omega) (by omega))
    f hf t ht
  have hc (k : Fin 2) (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (v u : ι) :=
    setting_constructed_mean_flux_regular_of_predecessors P P₀ hh n 0 hhh hn hnR
      (by simpa only [Nat.zero_add] using hp) hreserve prior k t ht m hm α 0 v u
  have hfast (Y : Vec 2) (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (v u : ι) :=
    ((hb (n - 1) (by omega) m hm α v u).1 Y).continuous
  have hcenter (hi : 1 ≤ n - 2) : CoefField True 2
      (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t) := by
    apply liftApply_centered_field_of_coefficients (n - 2) 2 _ f hf t
    · exact fun m hm α v u => hb (n - 2) (by omega) m hm α v u
    · intro m hm α v u Y
      exact constructedLiftCoefficients_periodic Q a b P.window par N hh (n - 2) m α t Y v u
    · intro m hm α v u Y ξ
      exact hmeans hh hhh (n - 2) hi (by omega)
        (ambientRecurrenceRank_degree (N + D) hh n 2 (by omega) (by omega))
        m hm α v u t ht Y ξ
  unfold actualMeanLeftTerms
  by_cases hh0 : hh = 0
  · subst hh
    simp only [actualMeanFluxCoefficient, ite_true]
    apply setting_diagonal_mean_left_terms_apply_of_coefficients P Cc n hn f hf t ht X z
    · simpa only [Nat.zero_add, Nat.cast_one, WithTop.coe_one, actualMeanFluxCoefficient, ite_true] using hc
    · exact hfast
    · simpa only [ite_true] using constructedLiftApply_zero_degree Q a b P.window par N 0 (fun _ => f) t
    · exact hg
    · intro hn3
      exact hcenter (by omega)
  · simp only [actualMeanFluxCoefficient, ite_eq_right hh0]
    have hgood := setting_constructed_source_predecessor_good P P₀ hh n hhh (by omega) prior f hf t ht
    have hcut (i : ℕ) (hi : N < i) := congrFun
      (constructedLiftApply_cutoff Q a b P.window par N (hh - 1) i hi (fun _ => f)) t
    apply setting_positive_mean_left_terms_apply_of_coefficients P Cc hh (by omega) n hn
      f hf t ht X z
    · simpa only [Nat.zero_add, Nat.cast_one, WithTop.coe_one, actualMeanFluxCoefficient, ite_eq_right hh0] using hc
    · exact hfast
    · exact hg
    · by_cases hn2 : n = 2
      · subst n
        have hz := constructedLiftApply_zero_degree Q a b P.window par N hh (fun _ => f) t
        have he : liftApply 0 (Cc hh 0) (fun _ => f) t = 0 := by
          simpa only [ite_eq_right hh0] using! hz
        simpa only [he] using! (CoefField.zero (c := True) (r := 2) (E := ∀ i, h i))
      · exact hcenter (by omega)
    · intro j hj m hm α u u'
      have box := setting_constructed_source_predecessor_box P P₀ hh n hhh (by omega) prior
        (n - 1 - j) m hm α u' u t ht
      exact box.mono (by have := hj.trans (min_le_left _ _); omega) (by omega)
    · exact hgood
    · exact hcut
    · intro k Y
      exact (setting_sourceFlux_good_of_coefficients P Cc (hh - 1) (n - 1) k f t ht
        hgood hcut).continuous_slice Y

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The actual coefficient primitive has the explicit symmetric recurrence-source coefficient. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_lift_coefficient_source_time_integral
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    IntervalIntegrable (fun s =>
      -cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z +
        leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n s w)
          m α s X z v u ξ) volume a t ∧
      Cc hh n m α t X z v u ξ = ∫ s in a..t,
        -cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z +
          leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n s w)
            m α s X z v u ξ := by
  obtain ⟨hi, he⟩ := setting_lift_coefficient_time_integral P sX sZ hsZ Cc hseq
    P₀ hh n hreserve hhh hn hnN m hm α u v ξ t ht X z
  have hlam : lam ≠ 0 := by
    rw [P.lam_eq]
    exact ne_of_gt (div_pos P.ρ_pos P.E_pos)
  have hsource s (hs : s ∈ uIcc a t) :=
    setting_calibratedLiftSourceEntry_eq P sX sZ hsX hsZ Cc hseq hh hhh n hn hnN
      m hm α hlam u v ξ s (by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩) X z
  refine ⟨hi.congr (fun s hs => congrArg (fun y => _ + y)
    (hsource s (uIoc_subset_uIcc hs))), ?_⟩
  rw [he]
  exact intervalIntegral.integral_congr (fun s hs => congrArg (fun y => _ + y) (hsource s hs))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The symmetric coefficient array represents the exact tail and its tested fields are centered. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tailLeftCoefficient_entry_centered
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D)
    (m : ℕ) (hm : m ≤ 2 * N + D) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (v u : ι) (ξ : h u) :
    fieldCellMean (fun z => tailLeftCoefficient Q Cc N hh n m α t X z v u ξ) = 0 := by
  let c := tailLeftCoefficient Q Cc N hh n
  have hc (A : Vec 2 →L[ℝ] ℝ) : Continuous (fun z => normalizedLiftTestField c
      (2 * N + D) A u v ξ t X z) := by
    let f : Vec 2 → ∀ i, h i := fun Y => Real.exp (A Y) • Pi.single u ξ
    have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
      (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
    have he : (fun z => liftApply (2 * N + D) c (fun _ => f) t X z) =
        fun z => liftTailCoeff Q Cc N (fun _ => f) hh n t X z := by
      funext z
      exact setting_tailLeftCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n
        (by omega) hnR f hf t ht X z
    have hfull := setting_liftTailCoeff_fast_continuous P sX sZ hsX hsZ Cc hseq
      hh hhh n f hf t ht X
    rw [← he] at hfull
    exact ((continuous_apply v).comp hfull).const_smul _
  apply symmetric_lift_coefficient_centered_of_tests (2 * N + D) m hm c
    (fun β σ => tailLeftCoefficient_perm Q Cc N hh n m β σ) α t X v u ξ hc
  intro A
  let f : Vec 2 → ∀ i, h i := fun Y => Real.exp (A Y) • Pi.single u ξ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  have he : (fun z => liftApply (2 * N + D) c (fun _ => f) t X z) =
      fun z => liftTailCoeff Q Cc N (fun _ => f) hh n t X z := by
    funext z
    exact setting_tailLeftCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n
      (by omega) hnR f hf t ht X z
  have hfull := setting_liftTailCoeff_fast_continuous P sX sZ hsX hsZ Cc hseq
    hh hhh n f hf t ht X
  rw [← he] at hfull
  have hz := setting_tailLeftCoefficient_apply_mean_zero P sX sZ hsX hsZ Cc hseq
    hh hhh n hn hnR f hf t ht X
  change fieldCellMean (fun z => (Real.exp (A X))⁻¹ •
    liftApply (2 * N + D) c (fun _ => f) t X z v) = 0
  rw [fieldCellMean_smul, fieldCellMean_pi_apply _ hfull v, hz]
  simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Finite coefficient synthesis gives the actual lift time equation on every smooth coarse input. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftApply_time_integral
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) (v : ι) :
    IntervalIntegrable (fun s =>
      -cellOperator (Q.G s X) (Q.v s) (fun y => liftApply n (Cc hh n) (fun _ => f) s X y v) z +
        liftCellSource Q Cc (fun _ => f) hh n s X z v) volume a t ∧
      liftApply n (Cc hh n) (fun _ => f) t X z v = ∫ s in a..t,
        -cellOperator (Q.G s X) (Q.v s) (fun y => liftApply n (Cc hh n) (fun _ => f) s X y v) z +
          liftCellSource Q Cc (fun _ => f) hh n s X z v := by
  classical
  let c := fun (p : LiftActionIndex ι n) s y =>
    Cc hh n p.1.val p.2.1 s X y v p.2.2 (orderedDerivative p.2.1 f X p.2.2)
  let g := fun (p : LiftActionIndex ι n) s y =>
    leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n s w)
      p.1.val p.2.1 s X y v p.2.2 (orderedDerivative p.2.1 f X p.2.2)
  have hr : 0 + (N + D) ≤ qs := by
    have := setting_ambient_output_supported P
    omega
  have hwindow s (hs : s ∈ uIcc a t) : s ∈ Icc a b := by
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hc p s (hs : s ∈ uIcc a t) : ContDiff ℝ 2 (c p s) := by
    have hm : p.1.val ≤ n := by have := p.1.isLt; omega
    exact (((setting_lift_cross_coefficient_box P sX sZ (by omega) Cc hseq hh hhh
      n hnN p.1.val hm p.2.1 v p.2.2 s (hwindow s hs)).1 X).clm_apply
        contDiff_const).of_le (by norm_num)
  have hp (p : LiftActionIndex ι n) := setting_lift_coefficient_source_time_integral P
    sX sZ hsX hsZ Cc hseq 0 hh n hr hhh hn hnN p.1.val (by have := p.1.isLt; omega)
      p.2.1 p.2.2 v (orderedDerivative p.2.1 f X p.2.2) t ht X z
  obtain ⟨hi, heq⟩ := finite_cell_time_primitives (fun s => Q.G s X) Q.v
    (fun _ : LiftActionIndex ι n => (1 : ℝ)) c g a t z hc hp
  have hfield s : (fun y => ∑ p, (1 : ℝ) • c p s y) =
      fun y => liftApply n (Cc hh n) (fun _ => f) s X y v := by
    funext y
    simpa only [one_smul] using liftApply_finite_vector_synthesis n (Cc hh n) f s X y v
  have hsource s (hs : s ∈ uIcc a t) : (∑ p, (1 : ℝ) • g p s z) =
      liftCellSource Q Cc (fun _ => f) hh n s X z v := by
    simp only [one_smul]
    rw [liftApply_finite_vector_synthesis]
    exact setting_liftSource_blockCoefficient_apply P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnN f hf s (hwindow s hs) X z v
  have he s (hs : s ∈ uIcc a t) :
      -cellOperator (Q.G s X) (Q.v s) (fun y => ∑ p, (1 : ℝ) • c p s y) z +
        (∑ p, (1 : ℝ) • g p s z) =
      -cellOperator (Q.G s X) (Q.v s) (fun y => liftApply n (Cc hh n) (fun _ => f) s X y v) z +
        liftCellSource Q Cc (fun _ => f) hh n s X z v := by
    rw [hfield, hsource s hs]
  refine ⟨hi.congr (fun s hs => he s (uIoc_subset_uIcc hs)), ?_⟩
  rw [← congrFun (hfield t) z, heq]
  exact intervalIntegral.integral_congr he

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The symmetric coefficient array represents the exact tail and its tested fields are centered. -/

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
theorem setting_tailLeftCoefficient_periodic
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (m : ℕ) (hm : m ≤ 2 * N + D) (α : DerivativeWord2 m)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (v u : ι) :
    AVenhance.IsZ2Periodic (fun z => tailLeftCoefficient Q Cc N hh n m α t X z v u) := by
  let c := tailLeftCoefficient Q Cc N hh n
  apply symmetric_lift_coefficient_periodic_of_tests (2 * N + D) m hm c
    (fun β σ => tailLeftCoefficient_perm Q Cc N hh n m β σ) α t X v u
  intro A ξ
  let f : Vec 2 → ∀ i, h i := fun Y => Real.exp (A Y) • Pi.single u ξ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  have he (z : Vec 2) := setting_tailLeftCoefficient_apply P sX sZ hsX hsZ Cc hseq
    hh hhh n hn hnR f hf t ht X z
  have hp := setting_liftTailCoeff_periodic P sX sZ (by omega) Cc hseq
    hh hhh n f hf t ht X
  intro k z
  change (Real.exp (A X))⁻¹ • liftApply (2 * N + D) c (fun _ => f) t X
    (z + AVenhance.latticeShift k) v =
    (Real.exp (A X))⁻¹ • liftApply (2 * N + D) c (fun _ => f) t X z v
  rw [he, he]
  exact congrArg (fun y : ∀ i, h i => (Real.exp (A X))⁻¹ • y v) (hp k z)
end

/-! The symmetric coefficient array represents the exact tail and its tested fields are centered. -/

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
theorem setting_tailLeftCoefficient_transverse
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (m : ℕ) (hm : m ≤ 2 * N + D) (α : DerivativeWord2 m) (v u : ι) :
    IsTransverseOn par (Set.Icc a b)
      (fun t X z => tailLeftCoefficient Q Cc N hh n m α t X z v u) := by
  let c := tailLeftCoefficient Q Cc N hh n
  apply symmetric_lift_coefficient_transverse_of_tests par (Set.Icc a b) (2 * N + D) m hm c
    (fun β σ => tailLeftCoefficient_perm Q Cc N hh n m β σ) α v u
  intro A ξ
  let f : Vec 2 → ∀ i, h i := fun Y => Real.exp (A Y) • Pi.single u ξ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  have hp := setting_liftTailCoeff_transverse P sX sZ (by omega) Cc hseq hh hhh n f hf
  intro t ht X z s
  have he (z : Vec 2) := setting_tailLeftCoefficient_apply P sX sZ hsX hsZ Cc hseq
    hh hhh n hn hnR f hf t ht X z
  change (Real.exp (A X))⁻¹ • liftApply (2 * N + D) c (fun _ => f) t X
    (z + s • basisVec par) v =
    (Real.exp (A X))⁻¹ • liftApply (2 * N + D) c (fun _ => f) t X z v
  rw [he, he]
  exact congrArg (fun y : ∀ i, h i => (Real.exp (A X))⁻¹ • y v) (hp t ht X z s)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The actual lift primitive is an equation in the finite component carrier. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftApply_vector_time_integral
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    IntervalIntegrable (fun s =>
      -cellOperator (Q.G s X) (Q.v s) (liftApply n (Cc hh n) (fun _ => f) s X) z +
        liftCellSource Q Cc (fun _ => f) hh n s X z) volume a t ∧
      liftApply n (Cc hh n) (fun _ => f) t X z = ∫ s in a..t,
        -cellOperator (Q.G s X) (Q.v s) (liftApply n (Cc hh n) (fun _ => f) s X) z +
          liftCellSource Q Cc (fun _ => f) hh n s X z := by
  apply pi_time_primitives
  intro v
  obtain ⟨hi, he⟩ := setting_liftApply_time_integral P sX sZ hsX hsZ Cc hseq
    hh n hhh hn hnN f hf t ht X z v
  have hR s (hs : s ∈ uIcc a t) :
      -cellOperator (Q.G s X) (Q.v s) (fun y => liftApply n (Cc hh n) (fun _ => f) s X y v) z +
        liftCellSource Q Cc (fun _ => f) hh n s X z v =
      (-cellOperator (Q.G s X) (Q.v s) (liftApply n (Cc hh n) (fun _ => f) s X) z +
        liftCellSource Q Cc (fun _ => f) hh n s X z) v := by
    have hsb : s ∈ Icc a b := by
      rw [uIcc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    have hb := setting_lift_cross_field_box P sX sZ (by omega) Cc hseq hh hhh n hnN f hf s hsb
    have heval := cellOperator_postcomposition
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) (Q.G s X) (Q.v s)
      (liftApply n (Cc hh n) (fun _ => f) s X) ((hb.1 X).of_le (by norm_num)) z
    simp only [Pi.add_apply, Pi.neg_apply]
    exact congrArg (fun w : h v => -w + liftCellSource Q Cc (fun _ => f) hh n s X z v) heval
  refine ⟨hi.congr (fun s hs => hR s (uIoc_subset_uIcc hs)), ?_⟩
  rw [he]
  exact intervalIntegral.integral_congr hR

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original data reserve supports every actual uncentered rank step, including truncated predecessors. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_recurrence_mean_action_of_predecessors
    (P₀ hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnR : n ≤ N + D)
    (hp : D + 1 ≤ P₀) (hreserve : P₀ + (N + D) ≤ qs)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u))
    (hmeans : ∀ h' ≤ H, ∀ i, 1 ≤ i → i ≤ N + D →
      ambientRecurrenceRank (N + D) h' i < ambientRecurrenceRank (N + D) hh n →
      ∀ m ≤ i, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Set.Icc a b, ∀ X, ∀ ξ : h u,
        fieldCellMean (fun z => constructedLiftCoefficients Q a b P.window par N h' i
          m α t X z v u ξ) = 0)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    leftTermsApply (recurrenceMeanLeftTerms Q
      (constructedLiftCoefficients Q a b P.window par N) hh n t) f X z =
      liftMean Q (constructedLiftCoefficients Q a b P.window par N) (fun _ => f) hh n t X := by
  apply recurrenceMeanLeftTerms_apply_of_finite_action Q _ hh n hn f t X z
  · intro hn1
    subst n
    exact setting_constructed_first_mean_of_predecessors P P₀ hh hhh prior f hf t ht X
  · intro hn2
    exact setting_constructed_mean_action_of_predecessors P P₀ hh n hhh hn2 hnR hp hreserve
      prior hmeans f hf t ht X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The truncated lift has the finite positive-degree time primitive. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftPoly_time_integral
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    IntervalIntegrable (fun s => liftPositiveTimeRhs Q Cc N ε hh f s X z) volume a t ∧
      liftPolyField Cc N ε hh (fun _ => f) t X z - (if hh = 0 then f X else 0) =
        ∫ s in a..t, liftPositiveTimeRhs Q Cc N ε hh f s X z := by
  obtain ⟨hi, he⟩ := finset_time_primitives (Finset.Icc 1 N) (fun n => ε ^ n)
    (fun n => liftApply n (Cc hh n) (fun _ => f) t X z)
    (fun n s => -cellOperator (Q.G s X) (Q.v s) (liftApply n (Cc hh n) (fun _ => f) s X) z +
      liftCellSource Q Cc (fun _ => f) hh n s X z) a t (fun n hn =>
        setting_liftApply_vector_time_integral P sX sZ hsX hsZ Cc hseq
          hh n hhh (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 f hf t ht X z)
  refine ⟨hi, ?_⟩
  rw [setting_liftPoly_positive_degrees sX sZ Cc hseq hh hhh ε f hf t ht X z] at he
  exact he

end AVRegularity.CycleComparison.Lift
end
