-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingTransverseFieldInverseExistence
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.SettingAmbientPositiveCoefficientRankStep
public import AVRegularity.CycleComparison.Lift.CellFieldAmbientBoxReserve
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The genuine paired source and inverse close one positive coefficient degree. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_positive_paired_coefficient_data_of_earlier_states
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N 0 Cc)
    (hseqi : IsLiftSequence
      (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
      sX sZ a b N 0 Ci) (P₀ n : ℕ)
    (hreserve : P₀ + (N + D) ≤ qs) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hsZq : sZ ≤ ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (Bd : ℕ → ℝ) (hBd : ∀ m, 0 ≤ Bd m)
    (prior : ∀ m < n, AmbientLiftCoefficientData par a b P.window lam m
      (ambientDegreeSlowReserve P₀ (N + D) m)
      (ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 m)
      (fun d α t X z v u => Cc 0 m d α t X z v u - Ci 0 m d α t X z v u)
      (fun v u => (Bd m * (if v = u then 1 else 0)) * g))
    (priorU : ∀ m, 1 ≤ m → m < n → ∀ A u v ξ,
      ∀ r ≤ ambientDegreeSlowReserve P₀ (N + D) m,
      ∀ s ≤ ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 m,
      ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        normalizedLiftUncenteredField Q Cc 0 m (lam • A) u v ξ t Y y -
        normalizedLiftUncenteredField
          (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
          Ci 0 m (lam • A) u v ξ t Y y) z) X‖ ≤
        (pairedAmbientUncenteredBudget P₀ (max k (L + 2)) D (N + D) m CG Cw CGI
          (fun j => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D 0 (N + D) N 0 j
            (identityMetricJetBudget CG) Cw Cj) Bd A * (if v = u then 1 else 0) * ‖ξ‖) *
          g * lam ^ (m + r)) :
    AmbientLiftCoefficientData par a b P.window lam n
      (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n)
      (fun m α t X z v u => Cc 0 n m α t X z v u - Ci 0 n m α t X z v u)
      (fun v u => (pairedCoefficientScalarStep P₀ (max k (L + 2)) D (N + D) N n
        CG Cw Cj CGI Bd * (if v = u then 1 else 0)) * g) := by
  let R := N + D
  let Q₀ := max k (L + 2)
  let p := ambientDegreeSlowReserve P₀ R n
  let q := ambientDegreeFastReserve Q₀ D 0 R 0 n
  let Pi := setting_identity_metric P
  let Bi := fun m => ambientCoefficientScalarBudget P₀ Q₀ D 0 R N 0 m
    (identityMetricJetBudget CG) Cw Cj
  let KM := fun m => ambientUncenteredBudget P₀ Q₀ D 0 R 0 m CG Cw Cj
    (fun h j => ambientCoefficientScalarBudget P₀ Q₀ D 0 R N h j CG Cw Cj)
  let Kd := pairedAmbientCenteredBudget P₀ Q₀ D R n CG Cw CGI Bi Bd KM
  have hnR : n ≤ R := by dsimp only [R]; omega
  have hp : p ≤ qs := ambientDegreeSlowReserve_data P₀ R n qs hreserve
  have hq : 2 ≤ q := ambientDegreeFastReserve_two Q₀ D 0 R 0 n (by dsimp only [Q₀]; omega)
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have native m (hm : m ≤ R) := setting_ambient_scalar_power_recurrence_data P
    sX sZ hsZ Cc hseq P₀ hreserve 0 (Nat.zero_le _) m hm
  have nativei m (hm : m ≤ R) := setting_ambient_scalar_power_recurrence_data Pi
    sX sZ hsZ Ci hseqi P₀ hreserve 0 (Nat.zero_le _) m hm
  have source := setting_ambient_actual_source_fixed_data P sX sZ hsZ Cc hseq P₀ 0 n
    hreserve (Nat.zero_le _) hn hnN
  have sourcei := setting_ambient_actual_source_fixed_data Pi sX sZ hsZ Ci hseqi P₀ 0 n
    hreserve (Nat.zero_le _) hn hnN
  simp only [finiteMatrixPower_zero] at source sourcei
  have hBi m : 0 ≤ Bi m := ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _
  have hKM m A : 0 ≤ KM m A := ambientUncenteredBudget_nonneg _ _ _ _ _ _ _ _ _ _ _
    (fun h j => ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ h j _ _ _) A
  have hKd A : 0 ≤ Kd A := pairedAmbientCenteredBudget_nonneg _ _ _ _ _ _ _ _ _ _
    hBi hBd KM hKM A
  have hb := setting_ambient_centered_paired_grading_of_earlier_states P Cc Ci P₀ n
    hreserve hn hnR g hg CGI hGI Bd hBd native nativei prior priorU
  have hd := liftSequence_paired_ambient_data_of_source P sX sZ hsZ Cc Ci hseq hseqi
    0 n p q (Nat.zero_le _) hn hnN hp hq hsZq g hg CGI hGI
    _ _ _ _ (native n hnR).coefficient (nativei n hnR).coefficient
    _ _ Kd hKd source sourcei hb
  apply hd.enlarge hlam
  intro v u
  apply le_of_eq
  dsimp only [pairedCoefficientScalarStep]
  rw [ite_eq_right (by omega : n ≠ 0), ite_eq_right (by omega : ¬N < n)]
  dsimp only [p, q, R, Q₀, Kd, Bi, KM]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The original setting proves the actual normalized lift-test time primitive. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_lift_test_time_integral
    (sX sZ : ℕ) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    let c := normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ
    let f := normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ
    IntervalIntegrable (fun s => -cellOperator (Q.G s X) (Q.v s) (c s X) z + f s X z) volume a t ∧
      c t X z = ∫ s in a..t, -cellOperator (Q.G s X) (Q.v s) (c s X) z + f s X z := by
  obtain ⟨Ks, source⟩ := setting_ambient_actual_source_data P sX sZ (by omega) Cc hseq
    P₀ hh n hreserve hhh hn hnN
  exact liftSequence_test_time_integral_of_source P sX sZ hsZ Cc hseq hh n
    (ambientDegreeSlowReserve P₀ (N + D) n)
    (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) hhh hn hnN
    (ambientDegreeFastReserve_two (max k (L + 2)) D H (N + D) hh n (by omega))
    Ks (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) source A u v ξ t ht X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The original setting supplies full flux-term coefficient regularity before fast or slow divergence. -/

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
theorem setting_sourceFlux_leftTerms_box
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (p q : ℕ) (hp : p ≤ D) (hq : q ≤ D + 1)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (e₀ : LeftTerm (∀ i, h i) (h v))
    (he : e₀ ∈ sourceFluxConvolutionLeftTerms Q.edge Q.η t n (Cc (hh - 1)) k₀ v) :
    IsBoxSmooth p q e₀.coeff := by
  apply sourceFluxConvolutionLeftTerms_box Q.edge Q.η t n (Cc (hh - 1)) k₀ p q v ?_ ?_ e₀ he
  · intro j hj m hm α u u'
    exact setting_sourceFlux_left_coefficient_reserve P sX sZ hsZ Cc hseq hh hhpos hhh n hn
      p q hp hq j (hj.trans (min_le_right _ _)) m hm α u u' t ht
  · intro u d γ hγ α
    have hpqs : p ≤ qs := by have h := setting_ambient_output_supported P; omega
    have hqqf : q ≤ qf := by rw [P.qf_eq]; have hd := P.D_ge; omega
    exact ((P.coeff_smooth v u d γ hγ α t ht).mono hpqs hqqf).clm_comp
      (ContinuousLinearMap.proj k₀ : Vec 2 →L[ℝ] ℝ)
end

/-! The original setting supplies full flux-term coefficient regularity before fast or slow divergence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_sourceFlux_leftTerms_box_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (p q : ℕ) (hp : p ≤ D) (hq : q ≤ D + 1)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι)
    (hc : ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth (p + j) (q + (D - 1) - j)
        (fun X z => Cc hh (n - j) m α t X z u u'))
    (e₀ : LeftTerm (∀ i, h i) (h v))
    (he : e₀ ∈ sourceFluxConvolutionLeftTerms Q.edge Q.η t n (Cc hh) k₀ v) :
    IsBoxSmooth p q e₀.coeff := by
  apply sourceFluxConvolutionLeftTerms_box Q.edge Q.η t n (Cc hh) k₀ p q v ?_ ?_ e₀ he
  · exact hc
  · intro u d γ hγ α
    have hpqs : p ≤ qs := by have h := setting_ambient_output_supported P; omega
    have hqqf : q ≤ qf := by rw [P.qf_eq]; have hd := P.D_ge; omega
    exact ((P.coeff_smooth v u d γ hγ α t ht).mono hpqs hqqf).clm_comp
      (ContinuousLinearMap.proj k₀ : Vec 2 →L[ℝ] ℝ)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The recurrence source convolution has the actual polynomial flux-divergence mean. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_sourceFlux_lift_convolution (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (j : ℕ) (k : Fin 2)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    sourceFluxCoeff Q.edge Q.η j t
      (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k X z =
      ∑ l ∈ Finset.range (min (D - 1) j + 1),
        sourceFluxCoefficientArray Q.edge Q.η t
          (liftApply (j - l) (Cc hh (j - l)) (fun _ => f) t) k l X z := by
  exact sourceFlux_polynomial_input_coefficient Q.edge (by have hd := P.D_ge; omega)
    Q.η t N j k (fun i => liftApply i (Cc hh i) (fun _ => f) t)
    (fun i => setting_liftApply_goodField_D_all P sX sZ hsZ Cc hseq hh hhh i f hf t ht)
    (fun i hi => congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq
      hh hhh i hi (fun _ => f)) t) X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Original native reserves control every source predecessor, including zero coefficients above both cutoffs. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tail_test_power_grading
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (p q : ℕ) (hp : p ≤ K + D + 2) (hq : q ≤ max k (L + 2) + D)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • liftTailCoeff Q Cc N
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X z v) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftTailCoeff Q Cc N
          (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) hh n t Y y v) z) X‖ ≤
        (tailTestScalarBudget K k L D H N hh n p q CG Cw Cj A *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) * lam ^ (n + r) := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  apply ambient_ordered_tail_power_grading par a b P.window lam hlam N hh n p q Q Cc
    (physicalEdgeEnvelopeMatrix π edge) (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg)
    (fun h m => tailCoefficientScalarBudget K k L D H N h m CG Cw Cj)
    (fun h m => tailCoefficientScalarBudget_nonneg K k L D H N h m CG Cw Cj)
    (tailUncenteredScalarBudget K k L D H N hh n p q CG Cw Cj)
    (fun h m => tailUncenteredScalarBudget K k L D H N h m (p + N) q CG Cw Cj)
    (setting_tail_uncentered_data P sX sZ hsZ Cc hseq p q (by omega) hq hh hhh n hn)
    ?_ ?_ A u v ξ t ht
  · intro j hj _ ab hab
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    exact setting_tail_coefficient_data P sX sZ hsZ Cc hseq p q
      (by omega) (by omega) ab.1 (by omega) j
  · intro j hj hg ab hab
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    exact (setting_tail_uncentered_data P sX sZ hsZ Cc hseq (p + N) q
      (by omega) hq ab.2 (by omega) (n - j) (by omega)).mono (by omega) le_rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The height-zero mean flux is symmetric, has zero constant order, and retains ambient regularity. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem diagonalMeanFluxCoefficient_contDiff_of_predecessor_data
    (Cc : ℕ → ℕ → LiftCoeff ι h) (n p q : ℕ) (hp : p ≤ qs)
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam (n - 1) p q (Cc 0 (n - 1)) M)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (z : Vec 2) (v u : ι) :
    ContDiff ℝ (p : ℕ∞)
      (fun X => diagonalMeanFluxCoefficient Q Cc n k₀ m α t X z v u) := by
  have hd := weightedDriftCoefficient_contDiff_of_data P Cc 0 n p q M data
    k₀ t ht m hm α z v u
  by_cases hn2 : n = 2
  · have hG (i j : Fin 2) : ContDiff ℝ (p : ℕ∞) (fun X => Q.G t X i j) :=
      (P.G_smooth t ht i j).of_le (by exact_mod_cast hp)
    simpa only [diagonalMeanFluxCoefficient, ite_eq_left hn2] using
      hd.add (metricFluxCoefficient_contDiff Q.η Q.G p t hG k₀ m α z v u)
  · simpa only [diagonalMeanFluxCoefficient, ite_eq_right hn2, add_zero] using hd
end

/-! The height-zero mean flux is symmetric, has zero constant order, and retains ambient regularity. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
theorem setting_diagonal_mean_flux_coefficient_perm
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (n : ℕ) (k₀ : Fin 2) (m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    diagonalMeanFluxCoefficient Q Cc n k₀ m (α ∘ σ) =
      diagonalMeanFluxCoefficient Q Cc n k₀ m α := by
  funext t X z v u
  unfold diagonalMeanFluxCoefficient
  rw [weightedLiftCoefficientMean_perm _ _ m
    (hseq.2.2.2.2.1 0 (Nat.zero_le H) (n - 1) m) α σ, metricFluxCoefficient_perm]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
theorem setting_diagonal_mean_flux_coefficient_zero_order
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (n : ℕ) (hn : 2 ≤ n)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (α : DerivativeWord2 0) (X z : Vec 2) (v u : ι) :
    diagonalMeanFluxCoefficient Q Cc n k₀ 0 α t X z v u = 0 := by
  unfold diagonalMeanFluxCoefficient
  rw [weightedLiftCoefficientMean_zero_order _ _ α t X z v u
    (fun y => liftSequence_zero_order_coefficient_zero P sX sZ Cc hseq
      0 (Nat.zero_le H) (n - 1) (by omega) α t ht X y v u)]
  simp only [metricFluxCoefficient_zero, ite_self, add_zero]

include P in
theorem setting_diagonal_mean_flux_coefficient_contDiff_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (z : Vec 2) (v u : ι) :
    ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞)
      (fun X => diagonalMeanFluxCoefficient Q Cc n k₀ m α t X z v u) := by
  have hd := (setting_weighted_drift_coefficient_data_upto P sX sZ hsZ Cc hseq
    P₀ hreserve 0 (Nat.zero_le H) n hn hnR k₀ t ht m hm α z v u 0 (by omega)).1
  by_cases hn2 : n = 2
  · have hp : P₀ + 1 ≤ qs := by have h := P.D_ge; omega
    have hG (i j : Fin 2) : ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => Q.G t X i j) :=
      (P.G_smooth t ht i j).of_le (by exact_mod_cast hp)
    simpa only [diagonalMeanFluxCoefficient, ite_eq_left hn2] using
      hd.add (metricFluxCoefficient_contDiff Q.η Q.G (P₀ + 1) t hG k₀ m α z v u)
  · simpa only [diagonalMeanFluxCoefficient, ite_eq_right hn2, add_zero] using hd
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The explicit lift tail has zero cell mean at every degree above the truncation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)



include P in
theorem setting_liftTailCoeff_transverse
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsTransverseOn par (Set.Icc a b)
      (fun t => liftTailCoeff Q Cc N (fun _ => f) hh n t) := by
  have hA := setting_liftA_transverse P sX sZ hsZ Cc hseq hh hhh n f hf
  intro t ht X z s
  simp only [liftTailCoeff]
  have heA := hA t ht X z s
  dsimp only at heA
  rw [heA]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact setting_lift_all_degree_apply_transverse P sX sZ hsZ Cc hseq p.1 (by omega) r
      (liftMean Q Cc (fun _ => f) p.2 (n - r)) t ht X z s
  · rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The recurrence source convolution has the actual polynomial flux-divergence mean. -/

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
theorem setting_source_lift_convolution_mean (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    fieldCellMean (fun z => ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) =
      Real.sqrt Q.η • ∑ k : Fin 2, fderiv ℝ (fun Y =>
        fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k Y)) X (basisVec k) := by
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hcoef (z : Vec 2) := source_polynomial_input_coefficient Q.edge (by have hd := P.D_ge; omega)
    Q.η t N n (fun i => liftApply i (Cc hh i) (fun _ => f) t)
    (fun i => setting_liftApply_goodField_D_all P sX sZ hsZ Cc hseq hh hhh i f hf t ht)
    (fun i hi => congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq hh hhh i hi (fun _ => f)) t)
    hΓ X z
  have hm := source_family_coefficient_mean Q.edge Q.η t hΓ
    (setting_liftPolyField_epsPoly_good P sX sZ hsZ Cc hseq hh hhh f hf t ht) n hn X
  convert hm using 1
  congr 1
  funext z
  exact (hcoef z).symm
end

/-! The recurrence source convolution has the actual polynomial flux-divergence mean. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_source_lift_convolution_mean_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (n : ℕ) (hn : 1 ≤ n)
    (f : Vec 2 → ∀ i, h i) (_hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2)
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    fieldCellMean (fun z => ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) =
      Real.sqrt Q.η • ∑ k : Fin 2, fderiv ℝ (fun Y =>
        fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k Y)) X (basisVec k) := by
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hcoef (z : Vec 2) := source_polynomial_input_coefficient Q.edge (by have hd := P.D_ge; omega)
    Q.η t N n (fun i => liftApply i (Cc hh i) (fun _ => f) t)
    hgood hcut
    hΓ X z
  have heps : EpsPoly False N D (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) := by
    refine ⟨fun i => liftApply i (Cc hh i) (fun _ => f) t, ?_, ?_, fun _ _ _ => rfl⟩
    · intro i
      exact ⟨hgood i, False.elim⟩
    · intro i hi Y y
      exact congrFun (congrFun (hcut i hi) Y) y
  have hm := source_family_coefficient_mean Q.edge Q.η t hΓ heps n hn X
  convert hm using 1
  congr 1
  funext z
  exact (hcoef z).symm
end

/-! Strong degree induction closes both actual paired coefficients and their uncentered source differences. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_paired_recurrence_data
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N 0 Cc)
    (hseqi : IsLiftSequence
      (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
      sX sZ a b N 0 Ci) (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hfast : ∀ m, 1 ≤ m → m ≤ N →
      sZ ≤ ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 m)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r)) (n : ℕ) (hnR : n ≤ N + D) :
    let Bd := pairedCoefficientScalarBudget P₀ (max k (L + 2)) D (N + D) N CG Cw Cj CGI
    let Bi := fun m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D 0 (N + D) N 0 m
      (identityMetricJetBudget CG) Cw Cj
    AmbientLiftCoefficientData par a b P.window lam n (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n)
      (fun m α t X z v u => Cc 0 n m α t X z v u - Ci 0 n m α t X z v u)
      (fun v u => (Bd n * (if v = u then 1 else 0)) * g) ∧
    (1 ≤ n → ∀ A u v ξ, ∀ r ≤ ambientDegreeSlowReserve P₀ (N + D) n,
      ∀ s ≤ ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n,
      ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        normalizedLiftUncenteredField Q Cc 0 n (lam • A) u v ξ t Y y -
        normalizedLiftUncenteredField
          (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
          Ci 0 n (lam • A) u v ξ t Y y) z) X‖ ≤
        (pairedAmbientUncenteredBudget P₀ (max k (L + 2)) D (N + D) n CG Cw CGI Bi Bd A *
          (if v = u then 1 else 0) * ‖ξ‖) * g * lam ^ (n + r)) := by
  let R := N + D
  let Q₀ := max k (L + 2)
  let Bd := pairedCoefficientScalarBudget P₀ Q₀ D R N CG Cw Cj CGI
  let B₀ := fun m => ambientCoefficientScalarBudget P₀ Q₀ D 0 R N 0 m CG Cw Cj
  let Bi := fun m => ambientCoefficientScalarBudget P₀ Q₀ D 0 R N 0 m (identityMetricJetBudget CG) Cw Cj
  let Qi : LiftOperatorData ι h D := ⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩
  have hBd m : 0 ≤ Bd m := pairedCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _
  have native m (hm : m ≤ R) := setting_ambient_scalar_power_recurrence_data P
    sX sZ hsZ Cc hseq P₀ hreserve 0 (Nat.zero_le _) m hm
  have nativei m (hm : m ≤ R) := setting_ambient_scalar_power_recurrence_data (setting_identity_metric P)
    sX sZ hsZ Ci hseqi P₀ hreserve 0 (Nat.zero_le _) m hm
  have coeff m (hm : m ≤ R) : AmbientLiftCoefficientData par a b P.window lam m
      (ambientDegreeSlowReserve P₀ R m) (ambientDegreeFastReserve Q₀ D 0 R 0 m)
      (Cc 0 m) (fun v u => B₀ m * (if v = u then 1 else 0)) := by
    simpa only [B₀, finiteMatrixPower_zero] using (native m hm).coefficient
  have coeffi m (hm : m ≤ R) : AmbientLiftCoefficientData par a b P.window lam m
      (ambientDegreeSlowReserve P₀ R m) (ambientDegreeFastReserve Q₀ D 0 R 0 m)
      (Ci 0 m) (fun v u => Bi m * (if v = u then 1 else 0)) := by
    simpa only [Bi, finiteMatrixPower_zero] using (nativei m hm).coefficient
  have main : ∀ n, n ≤ R →
      AmbientLiftCoefficientData par a b P.window lam n (ambientDegreeSlowReserve P₀ R n)
        (ambientDegreeFastReserve Q₀ D 0 R 0 n)
        (fun m α t X z v u => Cc 0 n m α t X z v u - Ci 0 n m α t X z v u)
        (fun v u => (Bd n * (if v = u then 1 else 0)) * g) ∧
      (1 ≤ n → ∀ A u v ξ, ∀ r ≤ ambientDegreeSlowReserve P₀ R n,
        ∀ s ≤ ambientDegreeFastReserve Q₀ D 0 R 0 n, ∀ t ∈ Set.Icc a b, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
          normalizedLiftUncenteredField Q Cc 0 n (lam • A) u v ξ t Y y -
          normalizedLiftUncenteredField Qi Ci 0 n (lam • A) u v ξ t Y y) z) X‖ ≤
          (pairedAmbientUncenteredBudget P₀ Q₀ D R n CG Cw CGI Bi Bd A *
            (if v = u then 1 else 0) * ‖ξ‖) * g * lam ^ (n + r)) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hnR
      have prior m (hm : m < n) := (ih m hm (hm.le.trans hnR)).1
      refine ⟨?_, ?_⟩
      · by_cases hn0 : n = 0
        · subst n
          simpa only [Bd, pairedCoefficientScalarBudget_zero, zero_mul] using
            liftSequence_paired_degree_zero_ambient_data Q Qi sX sZ a b P.window N 0 Cc Ci
              hseq hseqi 0 (Nat.zero_le _) par lam (ambientDegreeSlowReserve P₀ R 0)
              (ambientDegreeFastReserve Q₀ D 0 R 0 0)
        · by_cases hnN : n ≤ N
          · have hd := setting_ambient_positive_paired_coefficient_data_of_earlier_states P
              sX sZ hsZ Cc Ci hseq hseqi P₀ n hreserve (by omega) hnN
              (hfast n (by omega) hnN) g hg CGI hGI Bd hBd prior
              (fun m hm hmn => (ih m hmn (hmn.le.trans hnR)).2 hm)
            dsimp only [Bd] at hd
            rw [← pairedCoefficientScalarBudget_eq_step P₀ Q₀ D R N n CG Cw Cj CGI] at hd
            exact hd
          · have hN : N < n := by omega
            change AmbientLiftCoefficientData _ _ _ _ _ _ _ _ _
              (fun v u => (pairedCoefficientScalarBudget P₀ Q₀ D R N CG Cw Cj CGI n *
                (if v = u then 1 else 0)) * g)
            rw [pairedCoefficientScalarBudget_cutoff P₀ Q₀ D R N n hN CG Cw Cj CGI]
            simp only [zero_mul]
            exact liftSequence_paired_cutoff_ambient_data Q Qi sX sZ a b P.window N 0 Cc Ci
              hseq hseqi 0 (Nat.zero_le _) n hN par lam (ambientDegreeSlowReserve P₀ R n)
              (ambientDegreeFastReserve Q₀ D 0 R 0 n)
      · intro hn A u v ξ r hr s hs t ht X z
        have hd := setting_ambient_uncentered_paired_grading_of_predecessors P Cc Ci P₀ n
          hreserve hn hnR g hg CGI hGI B₀ Bi Bd hBd
          (fun m hm => coeff m (hm.le.trans hnR))
          (fun m hm => coeffi m (hm.le.trans hnR)) prior A t ht v u ξ
        exact hd.2 r hr s hs X z
  exact main n hnR
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal cross operator of order 1 has exactly the shifted lift-polynomial coefficients. -/

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
theorem setting_liftPoly_cross1_shift
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H)
    (M : ℕ) (hM : N + D ≤ M) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ε • cellB1 Q.η Q.G Q.v t (liftPolyField Cc N ε hh (fun _ => f) t) X z =
      ∑ n ∈ Finset.Icc 1 M, ε ^ n • cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t) X z := by
  let F := fun n => cellB1 Q.η Q.G Q.v t (liftApply n (Cc hh n) (fun _ => f) t) X z
  have hsum : cellB1 Q.η Q.G Q.v t (liftPolyField Cc N ε hh (fun _ => f) t) X z =
      ∑ n ∈ Finset.range (N + 1), ε ^ n • F n := by
    exact cellB1_finset_synthesis (Finset.range (N + 1)) Q.η Q.G Q.v t
      (fun n => ε ^ n) (fun n => liftApply n (Cc hh n) (fun _ => f) t)
      (fun n hn => (setting_lift_cross_field_box P sX sZ hsZ Cc hseq hh hhh n
        (by have := Finset.mem_range.mp hn; omega) f hf t ht).mono (by omega) (by omega))
      (fun i j => isBoxSmooth_slow_field 1 0 (fun Y => Q.G t Y i j)
        (setting_metric_contDiff_one P t ht i j)) X z
  have hz n (hn : N < n) : F n = 0 := by
    have he := congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq
      hh hhh n hn (fun _ => f)) t
    dsimp only [F]
    rw [he]
    exact congrFun (congrFun (cellB1_const Q.η Q.G Q.v t (0 : ∀ i, h i)) X) z
  have hshift := polynomial_shift_sum N M 1 (by omega)
    (by have := P.D_ge; omega) ε F hz
  rw [hsum]
  calc
    ε • (∑ n ∈ Finset.range (N + 1), ε ^ n • F n) =
        ∑ n ∈ Finset.Icc 1 M, ε ^ n • (if 1 ≤ n then F (n - 1) else 0) := by
      simpa only [pow_one] using hshift
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ite_eq_left (Finset.mem_Icc.mp hn).1]
end

/-! The literal cross operator of order 2 has exactly the shifted lift-polynomial coefficients. -/

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
theorem setting_liftPoly_cross2_shift
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H)
    (M : ℕ) (hM : N + D ≤ M) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ε ^ 2 • cellB2 Q.η Q.G t (liftPolyField Cc N ε hh (fun _ => f) t) X z =
      ∑ n ∈ Finset.Icc 1 M, ε ^ n • (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t) X z else 0) := by
  let F := fun n => cellB2 Q.η Q.G t (liftApply n (Cc hh n) (fun _ => f) t) X z
  have hsum : cellB2 Q.η Q.G t (liftPolyField Cc N ε hh (fun _ => f) t) X z =
      ∑ n ∈ Finset.range (N + 1), ε ^ n • F n := by
    exact cellB2_finset_synthesis (Finset.range (N + 1)) Q.η Q.G t
      (fun n => ε ^ n) (fun n => liftApply n (Cc hh n) (fun _ => f) t)
      (fun n hn => (setting_lift_cross_field_box P sX sZ hsZ Cc hseq hh hhh n
        (by have := Finset.mem_range.mp hn; omega) f hf t ht).mono le_rfl (by omega))
      (fun i j => isBoxSmooth_slow_field 1 0 (fun Y => Q.G t Y i j)
        (setting_metric_contDiff_one P t ht i j)) X z
  have hz n (hn : N < n) : F n = 0 := by
    have he := congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq
      hh hhh n hn (fun _ => f)) t
    dsimp only [F]
    rw [he]
    exact congrFun (congrFun (cellB2_const Q.η Q.G t (0 : ∀ i, h i)) X) z
  have hshift := polynomial_shift_sum N M 2 (by omega)
    (by have := P.D_ge; omega) ε F hz
  rw [hsum]
  exact hshift
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual symmetric coefficient entries inherit the finite-past cell time equation by finite calibration. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_lift_coefficient_time_integral
    (sX sZ : ℕ) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    IntervalIntegrable (fun s =>
      -cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z +
        calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ s X z) volume a t ∧
      Cc hh n m α t X z v u ξ = ∫ s in a..t,
        -cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z +
          calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ s X z := by
  let A := fun p : Fin (m + 1) × Fin (n + 1) =>
    (p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)
  let c := fun p s y => normalizedLiftTestField (Cc hh n) n (lam • A p) u v ξ s X y
  let f := fun p s y => normalizedLiftSourceField Q Cc hh n (lam • A p) u v ξ s X y
  have horder : (2 : ℕ∞) ≤ (sZ : ℕ∞) := by exact_mod_cast hsZ
  have hc p s (hs : s ∈ uIcc a t) : ContDiff ℝ 2 (c p s) := by
    rw [uIcc_of_le ht.1] at hs
    have hsb : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    have hi := liftSequence_normalized_exponential_component_inverse Q sX sZ (by omega)
      a b N H Cc hseq hh n hhh hn hnN (lam • A p) u v ξ X
    exact (hi.1 s hsb).of_le (WithTop.coe_le_coe.mpr horder)
  have hp p := setting_lift_test_time_integral P sX sZ hsZ Cc hseq P₀ hh n hreserve
    hhh hn hnN (A p) u v ξ t ht X z
  obtain ⟨hi, heq⟩ := finite_cell_time_primitives (fun s => Q.G s X) Q.v
    (liftCalibrationWeight n m α lam) c f a t z hc hp
  have hlam : lam ≠ 0 := (by rw [P.lam_eq]; exact ne_of_gt (div_pos P.ρ_pos P.E_pos))
  have hfield (s : ℝ) : (fun y => ∑ p, liftCalibrationWeight n m α lam p • c p s y) =
      fun y => Cc hh n m α s X y v u ξ := by
    funext y
    exact liftCalibration_synthesis n m hm (Cc hh n) lam hlam
      (fun β σ => hseq.2.2.2.2.1 hh hhh n m β σ) α s X y v u ξ
  have he (s : ℝ) :
      -cellOperator (Q.G s X) (Q.v s) (fun y => ∑ p, liftCalibrationWeight n m α lam p • c p s y) z +
        (∑ p, liftCalibrationWeight n m α lam p • f p s z) =
      -cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z +
        calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ s X z := by
    rw [hfield]
    rfl
  refine ⟨hi.congr (fun s _ => he s), ?_⟩
  rw [← congrFun (hfield t) z, heq]
  exact intervalIntegral.integral_congr (fun s _ => he s)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The leading cell operator on the lift polynomial is exactly its positive-degree sum. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftPoly_cellOperator_positive
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    cellOperator (Q.G t X) (Q.v t) (liftPolyField Cc N ε hh (fun _ => f) t X) z =
      ∑ n ∈ Finset.Icc 1 N, ε ^ n •
        cellOperator (Q.G t X) (Q.v t) (liftApply n (Cc hh n) (fun _ => f) t X) z := by
  let F := fun n => cellOperator (Q.G t X) (Q.v t) (liftApply n (Cc hh n) (fun _ => f) t X) z
  have hsum : cellOperator (Q.G t X) (Q.v t) (liftPolyField Cc N ε hh (fun _ => f) t X) z =
      ∑ n ∈ Finset.range (N + 1), ε ^ n • F n := by
    exact cellOperator_finset_synthesis (Finset.range (N + 1)) (Q.G t X) (Q.v t)
      (fun n => ε ^ n) (fun n => liftApply n (Cc hh n) (fun _ => f) t X)
      (fun n hn => ((setting_lift_cross_field_box P sX sZ hsZ Cc hseq hh hhh n
        (by have := Finset.mem_range.mp hn; omega) f hf t ht).1 X).of_le (by norm_num)) z
  have hzero : F 0 = 0 := by
    by_cases hh0 : hh = 0
    · subst hh
      have he : liftApply 0 (Cc 0 0) (fun _ => f) t X = fun _ => f X := by
        funext y
        exact hseq.1 f hf t ht X y
      dsimp only [F]
      rw [he, cellOperator_const]
      rfl
    · have he := congrFun (liftApply_positive_grade_zero_degree Q sX sZ a b N H Cc hseq
        hh (by omega) hhh (fun _ => f)) t
      dsimp only [F]
      rw [he]
      exact congrFun (cellOperator_const (Q.G t X) (Q.v t) (0 : ∀ i, h i)) z
  have hz n (hn : N < n) : F n = 0 := by
    have he := congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq
      hh hhh n hn (fun _ => f)) t
    dsimp only [F]
    rw [he]
    exact congrFun (cellOperator_const (Q.G t X) (Q.v t) (0 : ∀ i, h i)) z
  rw [hsum]
  exact polynomial_positive_padding N N le_rfl ε F hzero hz

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The recurrence source convolution has the actual polynomial flux-divergence mean. -/

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
theorem setting_positive_mean_split (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) hh n t X =
      (∑ k : Fin 2, fderiv ℝ (fun Y => fieldCellMean (fun z =>
        (Real.sqrt Q.η * Q.v t z k) •
          liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y z)) X (basisVec k)) -
      Real.sqrt Q.η • ∑ k : Fin 2, fderiv ℝ (fun Y =>
        fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k Y)) X (basisVec k) := by
  let Φ := liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t
  let Ψ := liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t
  have hG := setting_metric_contDiff_one P t ht
  have hw := setting_normalized_drift_contDiff_one P t ht
  have hΦ : GoodField 2 Φ := liftApply_goodField_of_seq Q hseq hX hZ hhh _ hf ht
  have hΨ : CoefField True 2 Ψ :=
    liftApply_centField_of_seq Q hseq hX hZ hhh (Or.inr hhpos) hf ht
  have hB2 := cellB2_centField Q.η Q.G t hG hΨ
  have hB1 := cellB1_continuous_slice Q.η Q.G Q.v t hG
    (fun k => (hw k).continuous) Φ hΦ X
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hD : 1 ≤ D := by have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hS : Continuous (fun z => ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => f) t) X z) :=
    continuous_finsetSum _ (fun j _ =>
      (sourceCoeff_good_zero Q.edge hD Q.η t _
        (setting_liftApply_goodField_D_all P sX sZ (by omega) Cc hseq
          (hh - 1) (by omega) (n - j) f hf t ht) hΓ j).continuous_slice X)
  have he : liftMean Q Cc (fun _ => f) hh n t X =
      fieldCellMean (fun z => (cellB1 Q.η Q.G Q.v t Φ X z +
        cellB2 Q.η Q.G t Ψ X z) - ∑ j ∈ Finset.range (min D n + 1),
          sourceCoeff Q.edge Q.η j t
            (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => f) t) X z) := by
    simp only [liftMean, liftA, Φ, Ψ, ite_eq_left hn,
      ite_eq_right (show hh ≠ 0 by omega)]
  rw [he, AVRegularity.fieldCellMean_sub
      (f := fun z => cellB1 Q.η Q.G Q.v t Φ X z + cellB2 Q.η Q.G t Ψ X z)
      (hB1.add (hB2.1.continuous_slice X)) hS,
    AVRegularity.fieldCellMean_add hB1 (hB2.1.continuous_slice X), hB2.2 trivial X,
    add_zero, fieldCellMean_cellB1_formula Q.η Q.G Q.v t hG hw Φ hΦ X,
    setting_source_lift_convolution_mean P sX sZ (by omega) Cc hseq (hh - 1)
      (by omega) n (by omega) f hf t ht X]
end

/-! The recurrence source convolution has the actual polynomial flux-divergence mean. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_positive_mean_split_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (hhpos : 1 ≤ hh) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2)
    (hΦ : GoodField 2 (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t))
    (hΨ : CoefField True 2 (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t))
    (hgood : ∀ i, GoodField D (liftApply i (Cc (hh - 1) i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc (hh - 1) i) (fun _ => f) t = 0) :
    liftMean Q Cc (fun _ => f) hh n t X =
      (∑ k : Fin 2, fderiv ℝ (fun Y => fieldCellMean (fun z =>
        (Real.sqrt Q.η * Q.v t z k) •
          liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y z)) X (basisVec k)) -
      Real.sqrt Q.η • ∑ k : Fin 2, fderiv ℝ (fun Y =>
        fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k Y)) X (basisVec k) := by
  let Φ := liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t
  let Ψ := liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t
  have hG := setting_metric_contDiff_one P t ht
  have hw := setting_normalized_drift_contDiff_one P t ht
  have hB2 := cellB2_centField Q.η Q.G t hG hΨ
  have hB1 := cellB1_continuous_slice Q.η Q.G Q.v t hG
    (fun k => (hw k).continuous) Φ hΦ X
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hD : 1 ≤ D := by have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hS : Continuous (fun z => ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => f) t) X z) :=
    continuous_finsetSum _ (fun j _ =>
      (sourceCoeff_good_zero Q.edge hD Q.η t _
        (hgood (n - j)) hΓ j).continuous_slice X)
  have he : liftMean Q Cc (fun _ => f) hh n t X =
      fieldCellMean (fun z => (cellB1 Q.η Q.G Q.v t Φ X z +
        cellB2 Q.η Q.G t Ψ X z) - ∑ j ∈ Finset.range (min D n + 1),
          sourceCoeff Q.edge Q.η j t
            (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => f) t) X z) := by
    simp only [liftMean, liftA, Φ, Ψ, ite_eq_left hn,
      ite_eq_right (show hh ≠ 0 by omega)]
  rw [he, AVRegularity.fieldCellMean_sub
      (f := fun z => cellB1 Q.η Q.G Q.v t Φ X z + cellB2 Q.η Q.G t Ψ X z)
      (hB1.add (hB2.1.continuous_slice X)) hS,
    AVRegularity.fieldCellMean_add hB1 (hB2.1.continuous_slice X), hB2.2 trivial X,
    add_zero, fieldCellMean_cellB1_formula Q.η Q.G Q.v t hG hw Φ hΦ X,
    setting_source_lift_convolution_mean_of_coefficients P Cc (hh - 1)
      n (by omega) f hf t ht X hgood hcut]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal source convolution equals the full divergence of its actual flux coefficients. -/

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
theorem setting_source_lift_convolution (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    (∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) =
      ∑ k : Fin 2, covariantCoefficientStep Q.η k
        (fun i Y y => sourceFluxCoeff Q.edge Q.η i t
          (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k Y y) n X z := by
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y y => γ.coeff α t Y y) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hcoef := source_polynomial_input_coefficient Q.edge (by have hd := P.D_ge; omega)
    Q.η t N n (fun i => liftApply i (Cc hh i) (fun _ => f) t)
    (fun i => setting_liftApply_goodField_D_all P sX sZ hsZ Cc hseq hh hhh i f hf t ht)
    (fun i hi => congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq hh hhh i hi (fun _ => f)) t)
    hΓ X z
  rw [← hcoef]
  exact source_family_coefficient Q.edge Q.η t hΓ
    (setting_liftPolyField_epsPoly_good P sX sZ hsZ Cc hseq hh hhh f hf t ht)
    n (by have hd := P.D_ge; omega) X z
end

/-! The literal source convolution equals the full divergence of its actual flux coefficients. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_source_lift_convolution_of_coefficients_all_degrees
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (n : ℕ)
    (f : Vec 2 → ∀ i, h i) (_hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2)
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    (∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) =
      ∑ k : Fin 2, covariantCoefficientStep Q.η k
        (fun i Y y => sourceFluxCoeff Q.edge Q.η i t
          (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k Y y) n X z := by
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y y => γ.coeff α t Y y) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hcoef := source_polynomial_input_coefficient Q.edge (by have hd := P.D_ge; omega)
    Q.η t N n (fun i => liftApply i (Cc hh i) (fun _ => f) t)
    hgood hcut
    hΓ X z
  rw [← hcoef]
  have heps : EpsPoly False N D (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) := by
    refine ⟨fun i => liftApply i (Cc hh i) (fun _ => f) t, ?_, ?_, fun _ _ _ => rfl⟩
    · intro i
      exact ⟨hgood i, False.elim⟩
    · intro i hi Y y
      exact congrFun (congrFun (hcut i hi) Y) y
  exact source_family_coefficient_all_degrees Q.edge Q.η t hΓ heps
    n X z
end

end AVRegularity.CycleComparison.Lift
end
