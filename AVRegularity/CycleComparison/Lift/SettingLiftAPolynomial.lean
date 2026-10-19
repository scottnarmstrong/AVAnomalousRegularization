-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import AVRegularity.CycleComparison.Lift.SettingPairedCoefficientOriginalReserve
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget
import AVRegularity.CycleComparison.Lift.PhysicalPowerSchurWiener
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The simultaneous ambient induction controls Wiener jets at every supported slow order. -/

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
theorem setting_sourceFlux_lift_component_convolution
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (A : Vec 2 →L[ℝ] ℝ) (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v u : ι) (ξ : h u) (X z : Vec 2) :
    sourceFluxCoeff Q.edge Q.η (n - 1) t
      (fun ε => liftPolyField Cc N ε (hh - 1)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ X z v =
      ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
        sourceFluxComponentCoefficient Q.edge Q.η t
          (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
            (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ j v X z := by
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun Y => Real.exp ((lam • A) Y) • Pi.single u ξ) :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul contDiff_const
  rw [setting_sourceFlux_lift_convolution P sX sZ hsZ Cc hseq (hh - 1) (by omega)
    (n - 1) k₀ _ hf t ht X z]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n - 1 := by have h := Finset.mem_range.mp hj; omega
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    P₀ hreserve (hh - 1) (by omega) (n - 1 - j) (by omega)
  have hres := ambient_flux_predecessor_reserve P₀ (max k (L + 2)) D H (N + D)
    hh n j hhpos hhh hn hnR hjn
  have hbox := (state.coefficient.raw_test_box A u ξ t ht).mono
    (show j ≤ ambientDegreeSlowReserve P₀ (N + D) (n - 1 - j) by omega) hres.2
  exact congrFun (congrFun (sourceFluxCoefficientArray_component_eq Q.edge Q.η t _
    k₀ j hbox v) X) z
end

/-! The actual flux convolution identity holds on every smooth coarse input. -/

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
theorem setting_sourceFlux_lift_component_convolution_smooth
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v : ι) (X z : Vec 2) :
    sourceFluxCoeff Q.edge Q.η (n - 1) t
      (fun ε => liftPolyField Cc N ε (hh - 1)
        (fun _ => f) t) k₀ X z v =
      ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
        sourceFluxComponentCoefficient Q.edge Q.η t
          (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
            (fun _ => f) t) k₀ j v X z := by
  rw [setting_sourceFlux_lift_convolution P sX sZ hsZ Cc hseq (hh - 1) (by omega)
    (n - 1) k₀ _ hf t ht X z]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n - 1 := by have h := Finset.mem_range.mp hj; omega
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    P₀ hreserve (hh - 1) (by omega) (n - 1 - j) (by omega)
  have hres := ambient_flux_predecessor_reserve P₀ (max k (L + 2)) D H (N + D)
    hh n j hhpos hhh hn hnR hjn
  have hbox := liftApply_box_reserve (n - 1 - j) j (D - 1 - j)
    (Cc (hh - 1) (n - 1 - j)) (fun _ => f) t (hf.of_le (by simp))
    (fun m hm α v u => (state.coefficient.box m hm α v u t ht).mono
      (show j ≤ ambientDegreeSlowReserve P₀ (N + D) (n - 1 - j) by omega) hres.2)
  exact congrFun (congrFun (sourceFluxCoefficientArray_component_eq Q.edge Q.η t _
    k₀ j hbox v) X) z
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Every recursion source has a continuous fast slice during its pulse. -/

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
theorem setting_liftA_periodic
    (sX sZ : ℕ) (hZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ X, AVenhance.IsZ2Periodic (fun z => liftA Q Cc (fun _ => f) hh n t X z) := by
  let g := fun (_ : ℝ) => f
  have hB1 := cellB1_periodic Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) g t)
    (liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh (n - 1) g t ht)
    (setting_drift_periodic P t ht)
  have hB2 := cellB2_periodic Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) g t)
    (liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh (n - 2) g t ht)
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have := setting_source_fast_reserve P; have := P.D_ge; omega
  have hD : 1 ≤ D := by have := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hS (j : ℕ) : ∀ X, AVenhance.IsZ2Periodic (fun z => sourceCoeff Q.edge Q.η j t
      (liftApply (n - j) (Cc (hh - 1) (n - j)) g t) X z) :=
    (sourceCoeff_good_zero Q.edge hD Q.η t _
      (setting_liftApply_goodField_D_all P sX sZ hZ Cc hseq
        (hh - 1) (by omega) (n - j) f hf t ht) hΓ j).2
  intro X k z
  simp only [liftA]
  rw [hB1 X k z]
  have he2 : (if 2 ≤ n then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) g t) X (z + AVenhance.latticeShift k) else 0) =
      if 2 ≤ n then cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) g t) X z else 0 := by
    split_ifs
    · exact hB2 X k z
    · rfl
  rw [he2]
  by_cases hh0 : hh = 0
  · simp only [ite_eq_left hh0]
    rfl
  · simp only [ite_eq_right hh0]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact hS j X k z
end

/-! The actual source polynomial is the literal finite lift-source convolution. -/

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
theorem setting_source_lift_polynomial (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    sourceOp Q.edge Q.η ε t (liftPolyField Cc N ε hh (fun _ => f) t) X z =
      ∑ n ∈ Finset.range (N + D + 1), ε ^ n •
        (∑ j ∈ Finset.range (min D n + 1), sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) := by
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y y => γ.coeff α t Y y) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hΦ := setting_liftPolyField_epsPoly_good P sX sZ hsZ Cc hseq hh hhh f hf t ht
  have hfull := source_family_epsPoly_good Q.edge Q.η t hΓ hΦ
  have hdegree : N + (D - 1) + 1 = N + D := by have := P.D_ge; omega
  rw [hdegree] at hfull
  rw [epsPoly_taylor hfull ε X z]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  exact source_polynomial_input_coefficient Q.edge (by have := P.D_ge; omega)
    Q.η t N n (fun i => liftApply i (Cc hh i) (fun _ => f) t)
    (fun i => setting_liftApply_goodField_D_all P sX sZ hsZ Cc hseq hh hhh i f hf t ht)
    (fun i hi => congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq
      hh hhh i hi (fun _ => f)) t) hΓ X z
end

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
theorem setting_positive_mean_flux_difference (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) hh n t X =
      -∑ k : Fin 2, fderiv ℝ (fun Y =>
        Real.sqrt Q.η • fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k Y) -
        fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k) •
          liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y z)) X (basisVec k) := by
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have hF (k : Fin 2) := sourceFlux_family_coefficient_good Q.edge Q.η t hΓ
    (setting_liftPolyField_epsPoly_good P sX sZ (by omega) Cc hseq
      (hh - 1) (by omega) f hf t ht) k (n - 1)
  have hΦ := liftApply_goodField_of_seq Q hseq (r := 1) (by omega) (by omega) hhh (n - 1) hf ht
  have hG (k : Fin 2) : GoodField 1 (fun Y z =>
      (Real.sqrt Q.η * Q.v t z k) •
        liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y z) := by
    refine ⟨((setting_normalized_drift_contDiff_one P t ht k).comp contDiff_snd).smul hΦ.1, ?_⟩
    intro Y m z
    dsimp only
    rw [hΦ.2 Y m z, setting_drift_periodic P t ht m z]
  rw [setting_positive_mean_split P sX sZ hX hZ Cc hseq hh hhpos hhh n hn f hf t ht X]
  exact fluxMean_difference (Real.sqrt Q.η) _ _ hF hG X
end

/-! The simultaneous ambient induction controls Wiener jets at every supported slow order. -/

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
theorem setting_sourceFlux_lift_normalized_mean_convolution
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (A : Vec 2 →L[ℝ] ℝ) (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v u : ι) (ξ : h u) (X : Vec 2) :
    (Real.exp ((lam • A) X))⁻¹ • fieldCellMean (fun z =>
      sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1)
          (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ X z v) =
      ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
        (Real.exp ((lam • A) X))⁻¹ • fieldCellMean (fun z =>
          sourceFluxComponentCoefficient Q.edge Q.η t
            (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
              (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ j v X z) := by
  rw [← AVRegularity.fieldCellMean_smul]
  have he : (fun z => (Real.exp ((lam • A) X))⁻¹ •
      sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1)
          (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ X z v) =
      fun z => ∑ j ∈ Finset.range (min (D - 1) (n - 1) + 1),
        (Real.exp ((lam • A) X))⁻¹ • sourceFluxComponentCoefficient Q.edge Q.η t
          (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
            (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ j v X z := by
    funext z
    rw [setting_sourceFlux_lift_component_convolution P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR A k₀ t ht v u ξ X z, Finset.smul_sum]
  rw [he, AVRegularity.fieldCellMean_sum]
  · apply Finset.sum_congr rfl
    intro j _
    exact AVRegularity.fieldCellMean_smul _ _
  · intro j hj
    have hjn : j ≤ n - 1 := by have h := Finset.mem_range.mp hj; omega
    exact ((setting_ambient_sourceFlux_term_grading_upto P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR j hjn A k₀ t ht v u ξ).1.1 X).continuous
end

/-! The actual polynomial source flux is jointly regular before cell averaging. -/

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
theorem setting_lift_polynomial_sourceFlux_good_one
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (j : ℕ) (k₀ : Fin 2)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    GoodField 1 (sourceFluxCoeff Q.edge Q.η j t
      (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀) := by
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  exact sourceFlux_family_coefficient_good Q.edge Q.η t hΓ
    (setting_liftPolyField_epsPoly_good P sX sZ hsZ Cc hseq hh hhh f hf t ht) k₀ j
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
theorem setting_positive_mean_flux_difference_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (hhpos : 1 ≤ hh) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2)
    (hΦ : GoodField 2 (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t))
    (hΨ : CoefField True 2 (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t))
    (hgood : ∀ i, GoodField D (liftApply i (Cc (hh - 1) i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc (hh - 1) i) (fun _ => f) t = 0) :
    liftMean Q Cc (fun _ => f) hh n t X =
      -∑ k : Fin 2, fderiv ℝ (fun Y =>
        Real.sqrt Q.η • fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k Y) -
        fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k) •
          liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y z)) X (basisVec k) := by
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have heps : EpsPoly False N D
      (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) := by
    refine ⟨fun i => liftApply i (Cc (hh - 1) i) (fun _ => f) t, ?_, ?_, fun _ _ _ => rfl⟩
    · intro i
      exact ⟨hgood i, False.elim⟩
    · intro i hi Y y
      exact congrFun (congrFun (hcut i hi) Y) y
  have hF (k : Fin 2) := sourceFlux_family_coefficient_good Q.edge Q.η t hΓ heps k (n - 1)
  have hΦ₁ := hΦ.mono (by omega : 1 ≤ 2)
  have hG (k : Fin 2) : GoodField 1 (fun Y z =>
      (Real.sqrt Q.η * Q.v t z k) •
        liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t Y z) := by
    refine ⟨((setting_normalized_drift_contDiff_one P t ht k).comp contDiff_snd).smul hΦ₁.1, ?_⟩
    intro Y m z
    dsimp only
    rw [hΦ₁.2 Y m z, setting_drift_periodic P t ht m z]
  rw [setting_positive_mean_split_of_coefficients P Cc hh hhpos n hn f hf t ht X
    hΦ hΨ hgood hcut]
  exact fluxMean_difference (Real.sqrt Q.η) _ _ hF hG X
end

/-! The actual diagonal-height flux array has the ambient literal Schur grading. -/

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
theorem setting_diagonal_mean_flux_coefficient_schur_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hΘ : 0 ≤ Θ)
    (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (m : ℕ) (hmpos : 1 ≤ m) (hm : m ≤ n - 1) (r : ℕ) (hr : r ≤ P₀ + 1) :
    schurSlowJet π (Set.Icc a b) r
      (fun (p : DerivativeWord2 m × Fin 2) t X z v u =>
        diagonalMeanFluxCoefficient Q Cc n p.2 m p.1 t X z v u) ≤
      ENNReal.ofReal (ambientDiagonalMeanFluxConstant P₀ N k L D H n m r CG Cw Cj *
        lam ^ (n - 1 - m + r)) := by
  let M := finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) 0
  have hM0 := finiteMatrixPower_nonneg _
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) 0
  have hbudget := physicalEdgeEnvelopeMatrix_power_schur_budget π P.mass_pos edge Θ hΘ
    ⟨P.envelope.nonneg, P.envelope.row_sum, P.envelope.col_sum⟩ 0
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  let A := fun p : DerivativeWord2 m × Fin 2 =>
    ambientDiagonalMeanFluxWordConstant P₀ N k L D H n r CG Cw Cj
  have hA (p : DerivativeWord2 m × Fin 2) : 0 ≤ A p :=
    ambientDiagonalMeanFluxWordConstant_nonneg P₀ N k L D H n r CG Cw Cj
  have hb (p : DerivativeWord2 m × Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
      (X z : Vec 2) (v u : ι) :
      ‖iteratedFDeriv ℝ r (fun Y =>
        diagonalMeanFluxCoefficient Q Cc n p.2 m p.1 t Y z v u) X‖ ≤
        A p * M v u * lam ^ (n - 1 - m + r) := by
    have hhjet := setting_diagonal_mean_flux_coefficient_jet_upto P sX sZ hsZ Cc hseq
      P₀ hreserve n hn hnR p.2 t ht m hmpos hm p.1 z X v u r hr
    simpa only [A, M, ambientDiagonalMeanFluxWordConstant] using hhjet
  have hs := schurSlowJet_le_of_word_matrix_budget π (Set.Icc a b) r _ A hA M hM0
    (lam ^ (n - 1 - m + r)) (Θ ^ 0) (pow_nonneg hlam _) hbudget hb
  simpa only [pow_zero, mul_one, ambientDiagonalMeanFluxConstant, A] using hs
end

/-! The actual polynomial source flux is jointly regular before cell averaging. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_sourceFlux_good_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh j : ℕ) (k₀ : Fin 2)
    (f : Vec 2 → ∀ i, h i) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    GoodField 1 (sourceFluxCoeff Q.edge Q.η j t
      (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀) := by
  have hqs := setting_source_slow_reserve P
  have hqf : 1 ≤ qf := by have h := setting_source_fast_reserve P; have hd := P.D_ge; omega
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩
  have heps : EpsPoly False N D
      (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) := by
    refine ⟨fun i => liftApply i (Cc hh i) (fun _ => f) t, ?_, ?_, fun _ _ _ => rfl⟩
    · intro i
      exact ⟨hgood i, False.elim⟩
    · intro i hi Y y
      exact congrFun (congrFun (hcut i hi) Y) y
  exact sourceFlux_family_coefficient_good Q.edge Q.η t hΓ heps k₀ j
end

/-! The simultaneous ambient induction controls Wiener jets at every supported slow order. -/

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
theorem setting_ambient_sourceFlux_mean_grading_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (A : Vec 2 →L[ℝ] ℝ) (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v u : ι) (ξ : h u) (r : ℕ) (hr : r ≤ P₀ + 1) :
    ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => (Real.exp ((lam • A) X))⁻¹ •
      fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1)
          (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ X z v)) ∧
    ∀ X, ‖iteratedFDeriv ℝ r (fun Y => (Real.exp ((lam • A) Y))⁻¹ •
      fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1)
          (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) k₀ Y z v)) X‖ ≤
      (2 ^ r * ambientSourceFluxMeanConstant P₀ N k L D H hh n A CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) *
          lam ^ (n - 1 + r) := by
  let J := Finset.range (min (D - 1) (n - 1) + 1)
  let T := fun j X => (Real.exp ((lam • A) X))⁻¹ • fieldCellMean (fun z =>
    sourceFluxComponentCoefficient Q.edge Q.η t
      (liftApply (n - 1 - j) (Cc (hh - 1) (n - 1 - j))
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ j v X z)
  have hd (j : ℕ) (hj : j ∈ J) := setting_ambient_sourceFlux_term_mean_grading_upto P
    sX sZ hsZ Cc hseq P₀ hreserve hh hhpos hhh n hn hnR j
    (by have h := Finset.mem_range.mp hj; omega) A k₀ t ht v u ξ r hr
  have he : (fun X => (Real.exp ((lam • A) X))⁻¹ • fieldCellMean (fun z =>
      sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1)
          (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ X z v)) =
      fun X => ∑ j ∈ J, T j X := by
    funext X
    exact setting_sourceFlux_lift_normalized_mean_convolution P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR A k₀ t ht v u ξ X
  rw [he]
  constructor
  · exact ContDiff.sum (fun j hj => (hd j hj).1)
  · intro X
    rw [iteratedFDeriv_fun_sum_apply (fun j hj =>
      (hd j hj).1.contDiffAt.of_le (by exact_mod_cast hr))]
    calc
      _ ≤ ∑ j ∈ J, ‖iteratedFDeriv ℝ r (T j) X‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ J, (2 ^ r * ambientSourceFluxTermConstant P₀ N k L D H hh n j A CG Cw Cj *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) *
            lam ^ (n - 1 + r) := Finset.sum_le_sum fun j hj => (hd j hj).2 X
      _ = _ := by
        simp only [ambientSourceFluxMeanConstant, J, Finset.mul_sum, Finset.sum_mul, mul_assoc]
end

/-! The simultaneous ambient induction controls Wiener jets at every supported slow order. -/

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
theorem setting_ambient_wiener_grading_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hΘ : 0 ≤ Θ) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (m r : ℕ) (hm : m ≤ n) (hr : r ≤ P₀) :
    schurWienerJet π (Set.Icc a b) L r (Cc hh n m) ≤
      ENNReal.ofReal (((2 ^ m : ℝ) * 4 * 2 ^ r * (centeredProfileJetConstant + 1) *
        ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N hh n CG Cw Cj) *
        Θ ^ hh * lam ^ (n - m + r)) := by
  have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
    P₀ hreserve hh hhh n (by omega)
  have hp : r ≤ ambientDegreeSlowReserve P₀ (N + D) n := by
    unfold ambientDegreeSlowReserve
    omega
  have hq : L + 2 ≤ ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n := by
    have he := ambientDegreeFastReserve_original_orders (max k (L + 2)) D H N hh n hn
    have hD := P.D_ge
    have hk := Nat.le_max_right k (L + 2)
    omega
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  exact physical_power_schurWienerJet_le π P.mass_pos edge Θ hΘ
    ⟨P.envelope.nonneg, P.envelope.row_sum, P.envelope.col_sum⟩ hh _
    (ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _)
    state.coefficient hseq hhh hlam hm hp hq
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The source polynomial has its literal positive-degree convolution with any supported padding. -/

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
theorem setting_source_lift_polynomial_positive_degrees (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (M : ℕ) (hM : N + D ≤ M) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    sourceOp Q.edge Q.η ε t (liftPolyField Cc N ε hh (fun _ => f) t) X z =
      ∑ n ∈ Finset.Icc 1 M, ε ^ n • liftSourceConvolution Q Cc (fun _ => f) hh n t X z := by
  rw [setting_source_lift_polynomial P sX sZ hsZ Cc hseq hh hhh ε f hf t ht X z]
  change (∑ n ∈ Finset.range (N + D + 1), ε ^ n •
    liftSourceConvolution Q Cc (fun _ => f) hh n t X z) = _
  exact polynomial_positive_padding (N + D) M hM ε
    (fun n => liftSourceConvolution Q Cc (fun _ => f) hh n t X z)
    (setting_liftSourceConvolution_zero P sX sZ Cc hseq hh hhh f hf t ht X z)
    (fun n hn => liftSourceConvolution_above_cutoff Q sX sZ a b N H Cc hseq
      (fun _ => f) hh n hhh hn t X z)
end

/-! The explicit lift tail has zero cell mean at every degree above the truncation. -/

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
theorem setting_liftTailCoeff_fast_continuous
    (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    Continuous (fun z => liftTailCoeff Q Cc N (fun _ => f) hh n t X z) := by
  have hA := setting_liftA_fast_continuous P sX sZ hX hZ Cc hseq hh hhh n f hf t ht X
  have hT : Continuous (fun z => ∑ r ∈ Finset.range (N + 1),
      if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftApply r (Cc p.1 r) (liftMean Q Cc (fun _ => f) p.2 (n - r)) t X z else 0) :=
    continuous_finsetSum _ (fun r _ => tail_composition_term_fast_continuous Q
      sX sZ a b N H Cc hseq hh n r hhh
      (fun q m => liftMean Q Cc (fun _ => f) q m) t ht X)
  exact hA.sub hT
end

/-! The explicit lift tail has zero cell mean at every degree above the truncation. -/

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
theorem setting_liftTailCoeff_mean_zero (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    fieldCellMean (fun z => liftTailCoeff Q Cc N (fun _ => f) hh n t X z) = 0 := by
  have hn2 : 2 ≤ n := by have := P.N_ge; omega
  let g := fun q m => liftMean Q Cc (fun _ => f) q m
  have hA := setting_liftA_fast_continuous P sX sZ hX hZ Cc hseq hh hhh n f hf t ht X
  have hT : Continuous (fun z => ∑ r ∈ Finset.range (N + 1),
      if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftApply r (Cc p.1 r) (g p.2 (n - r)) t X z else 0) :=
    continuous_finsetSum _ (fun r _ => tail_composition_term_fast_continuous Q
      sX sZ a b N H Cc hseq hh n r hhh g t ht X)
  unfold liftTailCoeff
  rw [fieldCellMean_sub hA hT,
    tail_composition_mean Q sX sZ a b N H Cc hseq hh n hhh hn2 g t ht X]
  by_cases hnR : n ≤ N + D
  · rw [ite_eq_left hnR]
    exact sub_self _
  · rw [ite_eq_right hnR]
    have hz := liftA_above_full_cutoff Q sX sZ a b N H Cc hseq P.D_ge
      (fun _ => f) hh n hhh (by omega) t
    simp [hz, fieldCellMean]
end

/-! The explicit lift tail has zero cell mean at every degree above the truncation. -/

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
theorem setting_liftTailCoeff_periodic
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    AVenhance.IsZ2Periodic (fun z => liftTailCoeff Q Cc N (fun _ => f) hh n t X z) := by
  have hA := setting_liftA_periodic P sX sZ hsZ Cc hseq hh hhh n f hf t ht X
  intro k z
  simp only [liftTailCoeff]
  have heA := hA k z
  dsimp only at heA
  rw [heA]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact liftApply_periodic Q sX sZ a b N H Cc hseq p.1 (by omega) r
      (liftMean Q Cc (fun _ => f) p.2 (n - r)) t ht X k z
  · rfl
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The diagonal-height coefficients give exactly the literal divergence-form mean action. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_diagonal_mean_flux_meanApply
    (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) 0 n t X =
      meanApply n (fun d α t X k₀ => diagonalMeanFluxCoefficient Q Cc n k₀ (d - 1) α t X 0)
        (fun _ => f) t X := by
  let C := diagonalMeanFluxCoefficient Q Cc n
  have hreg (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (k₀ : Fin 2) :
      Differentiable ℝ (fun Y v => ∑ u, C k₀ m α t Y 0 v u (orderedDerivative α f Y u)) := by
    apply (coefficient_word_action_contDiff 1 m α (C k₀) t 0 _ f hf).differentiable (by norm_num)
    intro v u
    exact (setting_diagonal_mean_flux_coefficient_contDiff_upto P sX sZ (by omega) Cc hseq
      P₀ hreserve n hn hnR k₀ t ht m hm α 0 v u).of_le (by norm_num)
  have hzero (k₀ : Fin 2) (α : DerivativeWord2 0) (Y : Vec 2) (v u : ι) :
      C k₀ 0 α t Y 0 v u = 0 :=
    setting_diagonal_mean_flux_coefficient_zero_order P sX sZ Cc hseq n hn k₀ t ht α Y 0 v u
  rw [← meanApply_of_flux_coefficients n hn C (fun _ => f) t X hzero hreg]
  have he (k₀ : Fin 2) : (fun Y => liftApply (n - 1) (C k₀) (fun _ => f) t Y 0) =
      fun Y => fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t Y y) +
        if n = 2 then -Q.η • ∑ j : Fin 2, Q.G t Y k₀ j • fderiv ℝ f Y (basisVec j) else 0 := by
    funext Y
    exact setting_diagonal_mean_flux_coefficient_vector_apply P sX sZ Cc hseq n hn f k₀ t ht Y 0
  simp only [he]
  by_cases hn2 : n = 2
  · subst n
    rw [liftMean_diagonal_second P sX sZ hX hZ Cc hseq f hf t ht X]
    simp only [ite_true, neg_smul, sub_eq_add_neg]
  · rw [liftMean_diagonal_ge_three P sX sZ hX hZ Cc hseq f hf n (by omega) t ht X]
    simp only [ite_eq_right hn2, add_zero]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Full source-flux left terms act on every smooth coarse input under the original setting. -/

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
theorem setting_sourceFlux_leftTerms_apply
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (sourceFluxConvolutionLeftTerms Q.edge Q.η t n (Cc (hh - 1)) k₀ v) f X z =
      sourceFluxCoeff Q.edge Q.η n t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v := by
  have hc : ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc (hh - 1) (n - j) m α t X z u u') := by
    intro j hj m hm α u u'
    simpa only [Nat.zero_add] using setting_sourceFlux_left_coefficient_reserve P sX sZ hsZ Cc hseq
      hh hhpos hhh n hn 0 0 (Nat.zero_le D) (Nat.zero_le _) j
      (hj.trans (min_le_right _ _)) m hm α u u' t ht
  rw [sourceFluxConvolutionLeftTerms_apply Q.edge Q.η t n (Cc (hh - 1)) k₀ v hc f hf X z,
    setting_sourceFlux_lift_convolution P sX sZ hsZ Cc hseq (hh - 1) (by omega)
      n k₀ f hf t ht X z]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ min (D - 1) n := by have h := Finset.mem_range.mp hj; omega
  have hbox := liftApply_box_reserve (n - j) j ((D - 1) - j) (Cc (hh - 1) (n - j))
    (fun _ => f) t (hf.of_le (by simp)) (hc j hj')
  exact (congrFun (congrFun (sourceFluxCoefficientArray_component_eq Q.edge Q.η t _
    k₀ j hbox v) X) z).symm
end

/-! Full source-flux left terms act on every smooth coarse input under the original setting. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem sourceFlux_leftTerms_apply_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (_ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι)
    (hc : ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc hh (n - j) m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    leftTermsApply (sourceFluxConvolutionLeftTerms Q.edge Q.η t n (Cc hh) k₀ v) f X z =
      sourceFluxCoeff Q.edge Q.η n t
        (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀ X z v := by
  have he := sourceFlux_polynomial_input_coefficient Q.edge (by have hd := P.D_ge; omega)
    Q.η t N n k₀ (fun i => liftApply i (Cc hh i) (fun _ => f) t) hgood hcut X z
  change sourceFluxCoeff Q.edge Q.η n t
    (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀ X z = _ at he
  rw [sourceFluxConvolutionLeftTerms_apply Q.edge Q.η t n (Cc hh) k₀ v hc f hf X z, he]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ min (D - 1) n := by have h := Finset.mem_range.mp hj; omega
  have hbox := liftApply_box_reserve (n - j) j ((D - 1) - j) (Cc hh (n - j))
    (fun _ => f) t (hf.of_le (by simp)) (hc j hj')
  exact (congrFun (congrFun (sourceFluxCoefficientArray_component_eq Q.edge Q.η t _
    k₀ j hbox v) X) z).symm
end

/-! Full source-flux left terms act on every smooth coarse input under the original setting. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem sourceFlux_component_convolution_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (_ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι)
    (hc : ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc hh (n - j) m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    sourceFluxCoeff Q.edge Q.η n t
      (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀ X z v =
      ∑ j ∈ Finset.range (min (D - 1) n + 1),
        sourceFluxComponentCoefficient Q.edge Q.η t
          (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) k₀ j v X z := by
  rw [← sourceFlux_leftTerms_apply_of_coefficients P Cc hh n f hf k₀ t _ht X z v hc hgood hcut]
  exact sourceFluxConvolutionLeftTerms_apply Q.edge Q.η t n (Cc hh) k₀ v hc f hf X z
end

/-! Full flux-term synthesis supplies both coordinate derivative reserves of the actual flux field. -/

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
theorem setting_sourceFlux_lift_box_one
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth 1 1 (fun X z => sourceFluxCoeff Q.edge Q.η n t
      (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z) := by
  apply isBoxSmooth_pi
  intro v
  have he : (fun X z => leftTermsApply
      (sourceFluxConvolutionLeftTerms Q.edge Q.η t n (Cc (hh - 1)) k₀ v) f X z) =
      (fun X z => sourceFluxCoeff Q.edge Q.η n t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v) := by
    funext X z
    exact setting_sourceFlux_leftTerms_apply P sX sZ hsZ Cc hseq hh hhpos hhh n hn f hf k₀ t ht X z v
  rw [← he]
  exact leftTermsApply_box _ 1 1 (fun d hd =>
    setting_sourceFlux_leftTerms_box P sX sZ hsZ Cc hseq hh hhpos hhh n hn 1 1
      (by have h := P.D_ge; omega) (by omega) k₀ t ht v d hd) f hf
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The uncentered recurrence polynomial is the literal cross operator minus the preceding source grade. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftA_polynomial
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H)
    (M : ℕ) (hM : N + D ≤ M) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    (∑ n ∈ Finset.Icc 1 M, ε ^ n • liftA Q Cc (fun _ => f) hh n t X z) =
      ε • cellB1 Q.η Q.G Q.v t (liftPolyField Cc N ε hh (fun _ => f) t) X z +
      ε ^ 2 • cellB2 Q.η Q.G t (liftPolyField Cc N ε hh (fun _ => f) t) X z -
      (if hh = 0 then 0 else
        sourceOp Q.edge Q.η ε t (liftPolyField Cc N ε (hh - 1) (fun _ => f) t) X z) := by
  simp only [liftA, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← setting_liftPoly_cross1_shift P sX sZ hsZ Cc hseq hh hhh M hM ε f hf t ht X z,
    ← setting_liftPoly_cross2_shift P sX sZ hsZ Cc hseq hh hhh M hM ε f hf t ht X z]
  split_ifs with hh0
  · simp only [smul_zero, Finset.sum_const_zero]
  · rw [setting_source_lift_polynomial_positive_degrees P sX sZ hsZ Cc hseq
      (hh - 1) (by omega) M hM ε f hf t ht X z]
    rfl

end AVRegularity.CycleComparison.Lift
end
