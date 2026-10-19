-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
public import AVRegularity.CycleComparison.Lift.CellFieldAmbientBoxReserve
public import AVRegularity.CycleComparison.Lift.SettingLiftALeftTermsActionOfCoefficients
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Explicit diagonal-height divergence coefficients satisfy the uniform ambient-reserve mean grading. -/

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
theorem setting_diagonal_mean_coefficients_upto
    (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hΘ : 0 ≤ Θ)
    (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) :
    ∃ Lb : MeanCoeff ι h,
      (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))), Lb d (α ∘ σ) = Lb d α) ∧
      (∀ d α k₀ v u, ∀ t ∈ Set.Icc a b,
        ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => Lb d α t X k₀ v u)) ∧
      (∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Set.Icc a b, ∀ X,
        liftMean Q Cc (fun _ => f) 0 n t X = meanApply n Lb (fun _ => f) t X) ∧
      (∀ d, 2 ≤ d → d ≤ n → ∀ r, r ≤ P₀ →
        schurSlowJet π (Set.Icc a b) r
          (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => Lb d p.1 t X p.2) ≤
          ENNReal.ofReal (ambientMeanGradeConstant P₀ N k L D H CG Cw Cj *
            lam ^ (n - d + r))) := by
  let c := diagonalMeanFluxCoefficient Q Cc n
  refine ⟨truncatedMeanCoefficient n c, ?_, ?_, ?_, ?_⟩
  · exact truncatedMeanCoefficient_perm n c (fun k₀ m α σ =>
      setting_diagonal_mean_flux_coefficient_perm sX sZ Cc hseq n k₀ m α σ)
  · intro d α k₀ v u t ht
    exact truncatedMeanCoefficient_contDiff n (P₀ + 1) c t
      (fun k₀ m hm α v u => setting_diagonal_mean_flux_coefficient_contDiff_upto P sX sZ
        (by omega) Cc hseq P₀ hreserve n hn hnR k₀ t ht m hm α 0 v u)
      d α k₀ v u
  · intro f hf t ht X
    rw [truncatedMeanCoefficient_meanApply]
    exact setting_diagonal_mean_flux_meanApply P sX sZ hX hZ Cc hseq
      P₀ hreserve n hn hnR f hf t ht X
  · intro d hd hdn r hr
    have hδ : n - 1 - (d - 1) = n - d := by omega
    have hb := setting_diagonal_mean_flux_coefficient_schur_upto P sX sZ (by omega) Cc hseq
      P₀ hreserve hΘ n hn hnR (d - 1) (by omega) (by omega) r (by omega)
    have he : schurSlowJet π (Set.Icc a b) r
        (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ =>
          truncatedMeanCoefficient n c d p.1 t X p.2) ≤
        ENNReal.ofReal (ambientDiagonalMeanFluxConstant P₀ N k L D H n (d - 1) r CG Cw Cj *
          lam ^ (n - d + r)) := by
      rw [truncatedMeanCoefficient_schurSlowJet n d r hd hdn c π (Set.Icc a b)
        (fun k₀ m α t X z v u => diagonalMeanFluxCoefficient_fast_constant
          Q Cc n k₀ m α t X z v u)]
      simpa only [hδ] using hb
    apply he.trans
    apply ENNReal.ofReal_le_ofReal
    have hC := (le_add_of_nonneg_left
      (ambientPositiveMeanFluxConstant_nonneg P₀ N k L D H 0 n (d - 1) r CG Cw Cj)).trans
      (ambientMeanGradeConstant_entry_le P₀ N k L D H CG Cw Cj 0 n (d - 1) r
        (Nat.zero_le H) hnR (by omega) (by omega))
    have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
    exact mul_le_mul_of_nonneg_right hC (pow_nonneg hlam (n - d + r))
end

/-! The positive mean flux array retains the ambient slow regularity needed for divergence. -/

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
theorem positiveMeanFluxCoefficient_contDiff_of_predecessor_data
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n p q : ℕ) (hp : p ≤ qs)
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam (n - 1) p q (Cc hh (n - 1)) M)
    (Ms : ℕ → ι → ι → ℝ)
    (sourceData : ∀ j ≤ min (D - 1) (n - 1),
      AmbientLiftCoefficientData par a b P.window lam (n - 1 - j)
        (p + j) ((D - 1) - j) (Cc (hh - 1) (n - 1 - j)) (Ms j))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (k₀ : Fin 2) (u v : ι)
    (hgood : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u, ∀ i,
      GoodField D (liftApply i (Cc (hh - 1) i)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t))
    (hcut : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u, ∀ i, N < i →
      liftApply i (Cc (hh - 1) i)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t = 0)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (z : Vec 2) :
    ContDiff ℝ (p : ℕ∞)
      (fun X => positiveMeanFluxCoefficient Q Cc hh n k₀ m α t X z v u) := by
  have hd := weightedDriftCoefficient_contDiff_of_data P Cc hh n p q M data
    k₀ t ht m hm α z v u
  have hs := boxSmooth_slow_contDiff
    (sourceFluxMeanCoefficient_box_of_predecessor_data P Cc (hh - 1) (n - 1) p 0 hp
      Ms sourceData t ht k₀ u v hgood hcut m hm α) z
  exact hd.sub (hs.const_smul (Real.sqrt Q.η))
end

/-! The positive mean flux array retains the ambient slow regularity needed for divergence. -/

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
theorem setting_positive_mean_flux_coefficient_contDiff_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (z : Vec 2) (v u : ι) :
    ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞)
      (fun X => positiveMeanFluxCoefficient Q Cc hh n k₀ m α t X z v u) := by
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
  have hd := (state.coefficient.weighted_mean_jet_le m hm α v u t ht 0
    (Nat.zero_le _) _ hw _ hW).1.of_le (show ((P₀ + 1 : ℕ) : WithTop ℕ∞) ≤
      ((ambientDegreeSlowReserve P₀ (N + D) (n - 1) : ℕ) : WithTop ℕ∞) by exact_mod_cast hp)
  have hsource := boxSmooth_slow_contDiff
    (setting_sourceFlux_mean_coefficient_box_upto P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR k₀ t ht m hm α v u) z
  exact hd.sub (hsource.const_smul (Real.sqrt Q.η))
end

/-! Plain finite-vector synthesis identifies the full actual positive-height mean flux. -/

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
theorem setting_positive_mean_flux_coefficient_vector_apply
    (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k₀) (fun _ => f) t X z =
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) •
        liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t X y) -
      Real.sqrt Q.η • fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X) := by
  let F := sourceFluxCoeff Q.edge Q.η (n - 1) t
    (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X
  let G := fun y => (Real.sqrt Q.η * Q.v t y k₀) •
    liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t X y
  have hfcont : Continuous F := good_field_fast_continuous 1 _
    (setting_lift_polynomial_sourceFlux_good_one P sX sZ (by omega) Cc hseq
      (hh - 1) (by omega) (n - 1) k₀ f hf t ht) X
  have hΦ := liftApply_goodField_of_seq Q hseq (r := 1) (by omega) (by omega) hhh (n - 1) hf ht
  have hgcont : Continuous G :=
    (setting_normalized_drift_contDiff_one P t ht k₀).continuous.smul
      (good_field_fast_continuous 1 _ hΦ X)
  ext v
  rw [setting_positive_mean_flux_coefficient_apply P sX sZ (by omega) Cc hseq
    P₀ hreserve hh hhpos hhh n hn hnR f hf k₀ t ht X z v]
  change fieldCellMean (fun y => G y v) - Real.sqrt Q.η • fieldCellMean (fun y => F y v) =
    (fieldCellMean G - Real.sqrt Q.η • fieldCellMean F) v
  rw [fieldCellMean_pi_apply G hgcont v, fieldCellMean_pi_apply F hfcont v]
  rfl
end

/-! Plain finite-vector synthesis identifies the full actual positive-height mean flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_positive_mean_flux_coefficient_vector_apply_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2)
    (hc : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ v u,
      Continuous (fun y => Cc hh (n - 1) m α t X y v u))
    (hsource : ∀ j ≤ min (D - 1) (n - 1), ∀ m ≤ n - 1 - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc (hh - 1) (n - 1 - j) m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc (hh - 1) i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc (hh - 1) i) (fun _ => f) t = 0)
    (hF : Continuous (sourceFluxCoeff Q.edge Q.η (n - 1) t
      (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X)) :
    liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k₀) (fun _ => f) t X z =
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) •
        liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t X y) -
      Real.sqrt Q.η • fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X) := by
  let F := sourceFluxCoeff Q.edge Q.η (n - 1) t
    (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X
  let G := fun y => (Real.sqrt Q.η * Q.v t y k₀) •
    liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t X y
  have hfcont : Continuous F := hF
  have hΦ : Continuous (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t X) :=
    continuous_pi fun v => liftApply_component_fast_continuous (n - 1) _ _ t X v
      (fun m hm α u => hc m hm α v u)
  have hgcont : Continuous G :=
    (setting_normalized_drift_contDiff_one P t ht k₀).continuous.smul
      hΦ
  ext v
  rw [setting_positive_mean_flux_coefficient_apply_of_coefficients P Cc hh n f hf
    k₀ t ht X z v (fun m hm α u => hc m hm α v u) hsource hgood hcut]
  change fieldCellMean (fun y => G y v) - Real.sqrt Q.η • fieldCellMean (fun y => F y v) =
    (fieldCellMean G - Real.sqrt Q.η • fieldCellMean F) v
  rw [fieldCellMean_pi_apply G hgcont v, fieldCellMean_pi_apply F hfcont v]
  rfl
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite uncentered terms give exactly the literal recurrence action. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftA_leftTerms_apply_of_coefficients_all_degrees
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι)
    (hc₁ : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth 1 1 (fun X z => Cc hh (n - 1) m α t X z u u'))
    (hc₂ : 2 ≤ n → ∀ m ≤ n - 2, ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth 2 0 (fun X z => Cc hh (n - 2) m α t X z u u'))
    (hcS : hh ≠ 0 → ∀ i m, m ≤ i → ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth D D (fun X z => Cc (hh - 1) i m α t X z u u'))
    (hgood : hh ≠ 0 → ∀ i, GoodField D (liftApply i (Cc (hh - 1) i) (fun _ => f) t))
    (hcut : hh ≠ 0 → ∀ i, N < i → liftApply i (Cc (hh - 1) i) (fun _ => f) t = 0) :
    leftTermsApply (liftALeftTerms Q Cc hh n t v) f X z =
      liftA Q Cc (fun _ => f) hh n t X z v := by
  have hB1 := cellB1_liftComponentLeftTerms_apply Q.η Q.G (n - 1) (Cc hh (n - 1))
    Q.v t hc₁ (setting_metric_contDiff_one P t ht) f hf X z v
  have hB2 (hn2 : 2 ≤ n) := cellB2_liftComponentLeftTerms_apply Q.η Q.G
    (n - 2) (Cc hh (n - 2)) t (hc₂ hn2) (setting_metric_contDiff_one P t ht) f hf X z v
  unfold liftALeftTerms
  rw [leftTermsApply_append]
  dsimp only
  rw [leftTermsApply_append]
  dsimp only
  rw [hB1]
  by_cases hn2 : 2 ≤ n <;> by_cases hh0 : hh = 0
  · simp only [ite_eq_left hn2, ite_eq_left hh0, leftTermsApply_nil]
    rw [hB2 hn2]
    simp [liftA, hn2, hh0]
  · simp only [ite_eq_left hn2, ite_eq_right hh0, leftTermsApply_map_smul]
    rw [hB2 hn2, setting_sourceConvolution_leftTerms_apply_of_coefficients_all_degrees P Cc
      (hh - 1) n f hf t ht X z v (hcS hh0) (hgood hh0) (hcut hh0)]
    simp [liftA, hn2, hh0, sub_eq_add_neg]
  · simp [hn2, hh0, leftTermsApply_nil, liftA]
  · simp only [ite_eq_right hn2, ite_eq_right hh0, leftTermsApply_nil, leftTermsApply_map_smul]
    rw [setting_sourceConvolution_leftTerms_apply_of_coefficients_all_degrees P Cc
      (hh - 1) n f hf t ht X z v (hcS hh0) (hgood hh0) (hcut hh0)]
    simp [liftA, hn2, hh0, sub_eq_add_neg]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Actual averaged flux coefficients have the calibrated ambient slow grading. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_sourceFlux_mean_coefficient_jet_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (v u : ι)
    (r : ℕ) (hr : r ≤ P₀ + 1) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y =>
      sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m α t Y z v u) X‖ ≤
      (finiteTestCalibrationConstant (n - 1) m α *
        (2 ^ r * ambientSourceFluxCalibrationConstant P₀ N k L D H hh n m CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u)) *
        lam ^ (n - 1 - m + r) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hM : 0 ≤ finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u :=
    finiteMatrixPower_nonneg _ (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u
  let C := ambientSourceFluxCalibrationConstant P₀ N k L D H hh n m CG Cw Cj
  have hC : 0 ≤ C := ambientSourceFluxCalibrationConstant_nonneg P₀ N k L D H hh n m CG Cw Cj
  let T := sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀
  have htest (ξ : h u) (j : Fin (m + 1)) (s : Fin ((n - 1) + 1)) :=
    setting_sourceFlux_mean_coefficient_normalized_test P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR
      ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) k₀ t ht v u ξ r hr z
  have he (j : Fin (m + 1)) (s : Fin ((n - 1) + 1)) :
      (s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ)) =
        lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) := smul_comm _ _ _
  have hbox : ∀ ξ : h u, ∀ j : Fin (m + 1), ∀ s : Fin ((n - 1) + 1),
      IsBoxSmooth r 0 (fun Y y =>
        (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y))⁻¹ •
          liftApply (n - 1) T
            (fun _ Z => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Z) •
              Pi.single u ξ) t Y y v) := by
    intro ξ j s
    simp only [he]
    have hz : (fun Y y => (Real.exp ((lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) Y))⁻¹ •
        liftApply (n - 1) T
          (fun _ Z => Real.exp ((lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) Z) •
            Pi.single u ξ) t Y y v) =
      fun Y _ => (Real.exp ((lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) Y))⁻¹ •
        liftApply (n - 1) T
          (fun _ Z => Real.exp ((lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) Z) •
            Pi.single u ξ) t Y z v := rfl
    rw [hz]
    exact isBoxSmooth_slow_field r 0 _ ((htest ξ j s).1.of_le (by exact_mod_cast hr))
  have hb : ∀ ξ : h u, ∀ j : Fin (m + 1), ∀ s : Fin ((n - 1) + 1),
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ 0
        (fun y => (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y))⁻¹ •
          liftApply (n - 1) T
            (fun _ Z => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Z) •
              Pi.single u ξ) t Y y v) z) X‖ ≤
        ((2 ^ r * C * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) *
          lam ^ (n - 1 + r)) * ‖ξ‖ := by
    intro ξ j s
    rw [norm_mixed_jet_fast_zero]
    simp only [he]
    have hK : ambientSourceFluxMeanConstant P₀ N k L D H hh n
        ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) CG Cw Cj ≤ C := by
      let s' : Fin n := ⟨s.val, by have h := s.isLt; omega⟩
      exact ambientSourceFluxMeanConstant_calibration_le P₀ N k L D H hh n m CG Cw Cj j s'
    apply ((htest ξ j s).2 X).trans
    have hhK := mul_le_mul_of_nonneg_left hK (show 0 ≤ (2 : ℝ) ^ r by positivity)
    have hhM := mul_le_mul_of_nonneg_right hhK hM
    have hhξ := mul_le_mul_of_nonneg_right hhM (norm_nonneg ξ)
    have hscale := mul_le_mul_of_nonneg_right hhξ (pow_nonneg hlam.le (n - 1 + r))
    simpa only [C, mul_assoc, mul_left_comm, mul_comm] using hscale
  have hbound := liftCoefficient_mixed_grading_of_finite_tests r 0 (n - 1) m hm T lam hlam
    (sourceFluxMeanCoefficient_perm Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m)
    α t v u hbox X z (2 ^ r * C * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u)
    (mul_nonneg (mul_nonneg (by positivity) hC) hM) hb
  rw [norm_mixed_jet_fast_zero] at hbound
  exact hbound

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The original lift sequence supplies the finite uncentered action even in the tail degrees. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftA_leftTerms_apply_all_degrees
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (liftALeftTerms Q Cc hh n t v) f X z =
      liftA Q Cc (fun _ => f) hh n t X z v := by
  apply setting_liftA_leftTerms_apply_of_coefficients_all_degrees P Cc hh n f hf t ht X z v
  · intro m _ α u u'
    exact setting_lift_all_degree_coefficient_box P sX sZ hsZ Cc hseq 1
      (by have := P.D_ge; omega) hh hhh (n - 1) m α u u' t ht
  · intro _ m _ α u u'
    exact (setting_lift_all_degree_coefficient_box P sX sZ hsZ Cc hseq 2
      P.D_ge hh hhh (n - 2) m α u u' t ht).mono le_rfl (Nat.zero_le _)
  · intro _ i m _ α u u'
    exact setting_lift_all_degree_coefficient_box P sX sZ hsZ Cc hseq D le_rfl
      (hh - 1) (by omega) i m α u u' t ht
  · intro _ i
    exact setting_lift_all_degree_good_field P sX sZ hsZ Cc hseq D le_rfl
      (hh - 1) (by omega) i f hf t ht
  · intro _ i hi
    exact congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq
      (hh - 1) (by omega) i hi (fun _ => f)) t

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The explicit positive-height mean flux coefficients give the literal meanApply identity. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_positive_mean_flux_meanApply
    (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) hh n t X =
      meanApply n (fun d α t X k₀ => positiveMeanFluxCoefficient Q Cc hh n k₀ (d - 1) α t X 0)
        (fun _ => f) t X := by
  let C := positiveMeanFluxCoefficient Q Cc hh n
  have hreg (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (k₀ : Fin 2) :
      Differentiable ℝ (fun Y v => ∑ u, C k₀ m α t Y 0 v u (orderedDerivative α f Y u)) := by
    apply (coefficient_word_action_contDiff 1 m α (C k₀) t 0 _ f hf).differentiable (by norm_num)
    intro v u
    exact (setting_positive_mean_flux_coefficient_contDiff_upto P sX sZ (by omega) Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR k₀ t ht m hm α 0 v u).of_le (by norm_num)
  have hzero (k₀ : Fin 2) (α : DerivativeWord2 0) (Y : Vec 2) (v u : ι) :
      C k₀ 0 α t Y 0 v u = 0 :=
    setting_positive_mean_flux_coefficient_zero_order P sX sZ (by omega) Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR k₀ t ht α Y 0 v u
  rw [← meanApply_of_flux_coefficients n hn C (fun _ => f) t X hzero hreg]
  have he (k₀ : Fin 2) : (fun Y => liftApply (n - 1) (C k₀) (fun _ => f) t Y 0) =
      fun Y => -(Real.sqrt Q.η • fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ Y) -
        fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) •
          liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y z)) := by
    funext Y
    rw [setting_positive_mean_flux_coefficient_vector_apply P sX sZ hX hZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR f hf k₀ t ht Y 0]
    exact (neg_sub _ _).symm
  rw [setting_positive_mean_flux_difference P sX sZ hX hZ Cc hseq hh hhpos hhh n hn f hf t ht X]
  simp only [he, fderiv_fun_neg, neg_apply, Finset.sum_neg_distrib]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Select the proved literal diagonal or positive-height mean flux array. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

def actualMeanFluxCoefficient {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) : Fin 2 → LiftCoeff ι h :=
  if hh = 0 then diagonalMeanFluxCoefficient Q Cc n else positiveMeanFluxCoefficient Q Cc hh n

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The actual positive mean flux combines the drift and source coefficient budgets. -/

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
theorem setting_positive_mean_flux_coefficient_jet_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (z X : Vec 2) (v u : ι)
    (r : ℕ) (hr : r ≤ P₀ + 1) :
    ‖iteratedFDeriv ℝ r (fun Y => positiveMeanFluxCoefficient Q Cc hh n k₀ m α t Y z v u) X‖ ≤
      (2 ^ r * max (Cw 0) 0 *
          ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N hh (n - 1) CG Cw Cj +
        finiteTestCalibrationConstant (n - 1) m α *
          (2 ^ r * ambientSourceFluxCalibrationConstant P₀ N k L D H hh n m CG Cw Cj)) *
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
  have hg := boxSmooth_slow_contDiff
    (setting_sourceFlux_mean_coefficient_box_upto P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR k₀ t ht m hm α v u) z
  have hf : ContDiff ℝ (r : ℕ∞) (fun Y => fieldCellMean (fun y =>
      (Real.sqrt Q.η * Q.v t y k₀) • Cc hh (n - 1) m α t Y y v u)) :=
    hd.1.of_le (by exact_mod_cast hr.trans hp)
  have hgr : ContDiff ℝ (r : ℕ∞) (fun Y =>
      sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m α t Y z v u) :=
    hg.of_le (by exact_mod_cast hr)
  have hsqrt : ‖Real.sqrt Q.η‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr P.η_le
  have hnorm := norm_iteratedFDeriv_sub_smul_le r _ _ hf hgr (Real.sqrt Q.η) hsqrt X
  change ‖iteratedFDeriv ℝ r (fun Y =>
    fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) • Cc hh (n - 1) m α t Y y v u) -
      Real.sqrt Q.η • sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m α t Y z v u) X‖ ≤ _
  apply hnorm.trans
  have hs := setting_sourceFlux_mean_coefficient_jet_upto P sX sZ hsZ Cc hseq
    P₀ hreserve hh hhpos hhh n hn hnR k₀ t ht m hm α v u r hr X z
  apply (add_le_add (hd.2 X) hs).trans_eq
  ring
end

/-! Positive mean terms act correctly from predecessor fields and source coefficients. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_positive_mean_left_terms_apply_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (hhpos : 1 ≤ hh)
    (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2)
    (hcoef : ∀ k m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      ContDiff ℝ 1 (fun Y => positiveMeanFluxCoefficient Q Cc hh n k m α t Y 0 v u))
    (hc : ∀ Y m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      Continuous (fun y => Cc hh (n - 1) m α t Y y v u))
    (hΦ : GoodField 2 (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t))
    (hΨ : CoefField True 2 (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t))
    (hsource : ∀ j ≤ min (D - 1) (n - 1), ∀ m ≤ n - 1 - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc (hh - 1) (n - 1 - j) m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc (hh - 1) i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc (hh - 1) i) (fun _ => f) t = 0)
    (hF : ∀ k Y, Continuous (sourceFluxCoeff Q.edge Q.η (n - 1) t
      (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k Y)) :
    leftTermsApply (meanFluxLeftTerms n (positiveMeanFluxCoefficient Q Cc hh n) t) f X z =
      liftMean Q Cc (fun _ => f) hh n t X := by
  rw [meanFluxLeftTerms_apply n _ t hcoef f hf X z]
  have he (k : Fin 2) :
      (fun Y => liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k)
        (fun _ => f) t Y 0) = fun Y =>
      -(Real.sqrt Q.η • fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k Y) -
        fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k) •
          liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y y)) := by
    funext Y
    rw [setting_positive_mean_flux_coefficient_vector_apply_of_coefficients P Cc hh n
      f hf k t ht Y 0 (hc Y) hsource hgood hcut (hF k Y)]
    simp only [neg_sub]
  simp_rw [he, fderiv_fun_neg, neg_apply]
  rw [Finset.sum_neg_distrib]
  exact (setting_positive_mean_flux_difference_of_coefficients P Cc hh hhpos n hn
    f hf t ht X hΦ hΨ hgood hcut).symm
end

/-! The actual positive-height flux array has the ambient literal Schur grading. -/

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
theorem setting_positive_mean_flux_coefficient_schur_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hΘ : 0 ≤ Θ)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (m : ℕ) (hm : m ≤ n - 1) (r : ℕ) (hr : r ≤ P₀ + 1) :
    schurSlowJet π (Set.Icc a b) r
      (fun (p : DerivativeWord2 m × Fin 2) t X z v u =>
        positiveMeanFluxCoefficient Q Cc hh n p.2 m p.1 t X z v u) ≤
      ENNReal.ofReal (ambientPositiveMeanFluxConstant P₀ N k L D H hh n m r CG Cw Cj *
        Θ ^ hh * lam ^ (n - 1 - m + r)) := by
  let M := finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh
  have hM0 := finiteMatrixPower_nonneg _
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh
  have hbudget := physicalEdgeEnvelopeMatrix_power_schur_budget π P.mass_pos edge Θ hΘ
    ⟨P.envelope.nonneg, P.envelope.row_sum, P.envelope.col_sum⟩ hh
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  let A := fun p : DerivativeWord2 m × Fin 2 =>
    ambientPositiveMeanFluxWordConstant P₀ N k L D H hh n m r CG Cw Cj p.1
  have hA (p : DerivativeWord2 m × Fin 2) : 0 ≤ A p :=
    ambientPositiveMeanFluxWordConstant_nonneg P₀ N k L D H hh n m r CG Cw Cj p.1
  have hb (p : DerivativeWord2 m × Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
      (X z : Vec 2) (v u : ι) :
      ‖iteratedFDeriv ℝ r (fun Y =>
        positiveMeanFluxCoefficient Q Cc hh n p.2 m p.1 t Y z v u) X‖ ≤
        A p * M v u * lam ^ (n - 1 - m + r) := by
    have hhjet := setting_positive_mean_flux_coefficient_jet_upto P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR p.2 t ht m hm p.1 z X v u r hr
    simpa only [A, M, ambientPositiveMeanFluxWordConstant] using hhjet
  have hs := schurSlowJet_le_of_word_matrix_budget π (Set.Icc a b) r _ A hA M hM0
    (lam ^ (n - 1 - m + r)) (Θ ^ hh) (pow_nonneg hlam _) hbudget hb
  apply hs.trans_eq
  congr 1
  change (ambientPositiveMeanFluxConstant P₀ N k L D H hh n m r CG Cw Cj *
    lam ^ (n - 1 - m + r)) * Θ ^ hh = _
  ring
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The selected actual mean array inherits ambient regularity and zero constant order. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_actual_meanFlux_coefficient_contDiff_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (z : Vec 2) (v u : ι) :
    ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞)
      (fun X => actualMeanFluxCoefficient Q Cc hh n k₀ m α t X z v u) := by
  by_cases hh0 : hh = 0
  · subst hh
    simpa only [actualMeanFluxCoefficient, ite_true] using
      setting_diagonal_mean_flux_coefficient_contDiff_upto P sX sZ hsZ Cc hseq P₀ hreserve
        n hn hnR k₀ t ht m hm α z v u
  · simpa only [actualMeanFluxCoefficient, ite_eq_right hh0] using
      setting_positive_mean_flux_coefficient_contDiff_upto P sX sZ hsZ Cc hseq P₀ hreserve
        hh (by omega) hhh n hn hnR k₀ t ht m hm α z v u

include P in
theorem setting_actual_meanFlux_coefficient_zero_order
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (α : DerivativeWord2 0) (X z : Vec 2) (v u : ι) :
    actualMeanFluxCoefficient Q Cc hh n k₀ 0 α t X z v u = 0 := by
  by_cases hh0 : hh = 0
  · subst hh
    simpa only [actualMeanFluxCoefficient, ite_true] using
      setting_diagonal_mean_flux_coefficient_zero_order P sX sZ Cc hseq n hn k₀ t ht α X z v u
  · simpa only [actualMeanFluxCoefficient, ite_eq_right hh0] using
      setting_positive_mean_flux_coefficient_zero_order P sX sZ hsZ Cc hseq P₀ hreserve
        hh (by omega) hhh n hn hnR k₀ t ht α X z v u

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Explicit positive-height divergence coefficients satisfy the uniform ambient-reserve mean grading. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_positive_mean_coefficients_upto
    (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hΘ : 0 ≤ Θ)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) :
    ∃ Lb : MeanCoeff ι h,
      (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))), Lb d (α ∘ σ) = Lb d α) ∧
      (∀ d α k₀ v u, ∀ t ∈ Set.Icc a b,
        ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => Lb d α t X k₀ v u)) ∧
      (∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Set.Icc a b, ∀ X,
        liftMean Q Cc (fun _ => f) hh n t X = meanApply n Lb (fun _ => f) t X) ∧
      (∀ d, 2 ≤ d → d ≤ n → ∀ r, r ≤ P₀ →
        schurSlowJet π (Set.Icc a b) r
          (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => Lb d p.1 t X p.2) ≤
          ENNReal.ofReal (ambientMeanGradeConstant P₀ N k L D H CG Cw Cj *
            Θ ^ hh * lam ^ (n - d + r))) := by
  let c := positiveMeanFluxCoefficient Q Cc hh n
  refine ⟨truncatedMeanCoefficient n c, ?_, ?_, ?_, ?_⟩
  · exact truncatedMeanCoefficient_perm n c (fun k₀ m α σ =>
      setting_positive_mean_flux_coefficient_perm sX sZ Cc hseq hh hhh n k₀ m α σ)
  · intro d α k₀ v u t ht
    exact truncatedMeanCoefficient_contDiff n (P₀ + 1) c t
      (fun k₀ m hm α v u => setting_positive_mean_flux_coefficient_contDiff_upto P sX sZ
        (by omega) Cc hseq P₀ hreserve hh hhpos hhh n hn hnR k₀ t ht m hm α 0 v u)
      d α k₀ v u
  · intro f hf t ht X
    rw [truncatedMeanCoefficient_meanApply]
    exact setting_positive_mean_flux_meanApply P sX sZ hX hZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR f hf t ht X
  · intro d hd hdn r hr
    have hδ : n - 1 - (d - 1) = n - d := by omega
    have hb := setting_positive_mean_flux_coefficient_schur_upto P sX sZ (by omega) Cc hseq
      P₀ hreserve hΘ hh hhpos hhh n hn hnR (d - 1) (by omega) r (by omega)
    have he : schurSlowJet π (Set.Icc a b) r
        (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ =>
          truncatedMeanCoefficient n c d p.1 t X p.2) ≤
        ENNReal.ofReal (ambientPositiveMeanFluxConstant P₀ N k L D H hh n (d - 1) r CG Cw Cj *
          Θ ^ hh * lam ^ (n - d + r)) := by
      rw [truncatedMeanCoefficient_schurSlowJet n d r hd hdn c π (Set.Icc a b)
        (fun k₀ m α t X z v u => positiveMeanFluxCoefficient_fast_constant
          Q Cc hh n k₀ m α t X z v u)]
      simpa only [hδ] using hb
    apply he.trans
    apply ENNReal.ofReal_le_ofReal
    have hC := (le_add_of_nonneg_right
      (ambientDiagonalMeanFluxConstant_nonneg P₀ N k L D H n (d - 1) r CG Cw Cj)).trans
      (ambientMeanGradeConstant_entry_le P₀ N k L D H CG Cw Cj hh n (d - 1) r
        hhh hnR (by omega) (by omega))
    have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (pow_nonneg hΘ hh)) (pow_nonneg hlam (n - d + r))

end AVRegularity.CycleComparison.Lift
end
