-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
public import AVRegularity.CycleComparison.Lift.CellFieldAmbientBoxReserve
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal source convolution equals the full divergence of its actual flux coefficients. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_source_lift_convolution_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (n : ℕ) (_hn : n ≤ N + D)
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
  exact source_family_coefficient Q.edge Q.η t hΓ heps
    n (by have hd := P.D_ge; omega) X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The diagonal mean flux combines drift grading with the degree-two metric contribution. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_diagonal_mean_flux_coefficient_jet_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) (k₀ : Fin 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (m : ℕ) (hmpos : 1 ≤ m) (hm : m ≤ n - 1)
    (α : DerivativeWord2 m) (z X : Vec 2) (v u : ι) (r : ℕ) (hr : r ≤ P₀ + 1) :
    ‖iteratedFDeriv ℝ r (fun Y => diagonalMeanFluxCoefficient Q Cc n k₀ m α t Y z v u) X‖ ≤
      (2 ^ r * max (Cw 0) 0 *
          ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N 0 (n - 1) CG Cw Cj +
        if n = 2 then max (CG r) 0 else 0) *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) 0 v u * lam ^ (n - 1 - m + r) := by
  have hd := setting_weighted_drift_coefficient_data_upto P sX sZ hsZ Cc hseq
    P₀ hreserve 0 (Nat.zero_le H) n hn hnR k₀ t ht m hm α z v u r hr
  change ‖iteratedFDeriv ℝ r (fun Y =>
    weightedLiftCoefficientMean (Cc 0 (n - 1)) (fun t y => Real.sqrt Q.η * Q.v t y k₀) m α t Y z v u +
      if n = 2 then metricFluxCoefficient Q.η Q.G k₀ m α t Y z v u else 0) X‖ ≤ _
  by_cases hn2 : n = 2
  · subst n
    have hm1 : m = 1 := by omega
    subst m
    simp only [ite_true]
    have hrd : ContDiff ℝ (r : ℕ∞) (fun Y =>
        weightedLiftCoefficientMean (Cc 0 (2 - 1))
          (fun t y => Real.sqrt Q.η * Q.v t y k₀) 1 α t Y z v u) :=
      hd.1.of_le (by exact_mod_cast hr)
    have hrqs : r ≤ qs := by have h := P.D_ge; omega
    have hG (i j : Fin 2) : ContDiff ℝ (r : ℕ∞) (fun Y => Q.G t Y i j) :=
      (P.G_smooth t ht i j).of_le (by exact_mod_cast hrqs)
    have hmetric := metricFluxCoefficient_contDiff (h := h) Q.η Q.G r t hG k₀ 1 α z v u
    apply (norm_iteratedFDeriv_add_le r _ _ hrd hmetric X).trans
    have hj := setting_metric_flux_coefficient_jet_le P r hrqs t ht k₀ α X z v u
    apply (add_le_add (hd.2 X) hj).trans_eq
    rw [finiteMatrixPower_zero]
    simp only [Nat.reduceSub, zero_add]
    ring
  · simpa only [ite_eq_right hn2, add_zero] using hd.2 X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Every recursion source has a continuous fast slice during its pulse. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem setting_liftA_fast_continuous (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    Continuous (fun z => liftA Q Cc (fun _ => f) hh n t X z) := by
  have hG := setting_metric_contDiff_one P t ht
  have hw := setting_normalized_drift_contDiff_one P t ht
  have hgood (m : ℕ) := liftApply_goodField_of_seq Q hseq hX hZ hhh m hf ht
  have hB1 := cellB1_continuous_slice Q.η Q.G Q.v t hG
    (fun k₀ => (hw k₀).continuous) _ (hgood (n - 1)) X
  have hB2 := cellB2_continuous_slice Q.η Q.G t hG _ (hgood (n - 2)) X
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have hq := setting_source_fast_reserve P; have hd := P.D_ge; omega
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
  change Continuous (fun z => _ + (if 2 ≤ n then _ else 0) - (if hh = 0 then 0 else _))
  apply Continuous.sub
  · apply hB1.add
    split_ifs
    · exact hB2
    · exact continuous_const
  · split_ifs
    · exact continuous_const
    · exact hS

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original reserve of the lift setting supports every actual paired coefficient state. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_paired_coefficient_original_reserve
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
        ENNReal.ofReal (CGI r * g * lam ^ r)) (n : ℕ) (hnR : n ≤ N + D) :
    AmbientLiftCoefficientData par a b P.window lam n (ambientDegreeSlowReserve K (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n)
      (fun m α t X z v u => Cc 0 n m α t X z v u - Ci 0 n m α t X z v u)
      (fun v u => (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI n *
        (if v = u then 1 else 0)) * g) := by
  have hreserve : K + (N + D) ≤ qs := by
    simpa only [Nat.add_assoc] using setting_ambient_output_supported P
  exact (setting_ambient_paired_recurrence_data P (K + D + 2) (max (k + 1) (L + 2))
    (by omega) Cc Ci hseq hseqi K hreserve
    (fun m _ hm => lift_inverse_order_le_ambient_fast_reserve D N k L m (by have := P.D_ge; omega) hm)
    g hg CGI hGI n hnR).1

end AVRegularity.CycleComparison.Lift
end
