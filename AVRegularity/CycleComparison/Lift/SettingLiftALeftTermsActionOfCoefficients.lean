-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import AVRegularity.CycleComparison.Lift.SettingPairedCoefficientOriginalReserve
public import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Both lift norms admit one fixed-data constant at every supported ambient slow order. -/

theorem cycle_lift_norm_grading_upto (P₀ N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
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
        ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ P₀ →
          schurEnergyJet π (Set.Icc t₀ t₁) k j (Cc hh n m)
              ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - m + j)) ∧
          schurWienerJet π (Set.Icc t₀ t₁) L j (Cc hh n m)
              ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - m + j)) :=
by
  obtain ⟨C, hC, hbound⟩ := ambient_lift_grade_constants_uniform P₀ N k L D H CG Cw Cj
  refine ⟨C, hC, ?_⟩
  classical
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P hreserve
    Cc hseq hh hhh n hn hnN m hm hmn j hj
  rcases isEmpty_or_nonempty ι with hι | hι
  · have := hι
    simp [schurEnergyJet, schurWienerJet, schurSums]
  · have := hι
    let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
    have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
    have hΘ : 0 ≤ Θ := (Finset.sum_nonneg (fun u _ => P.envelope.nonneg (Classical.choice hι) u)).trans
      (P.envelope.row_sum (Classical.choice hι))
    have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
    have hres : P₀ + (N + D) ≤ qs := by omega
    have hsZ : 1 ≤ max (k + 1) (L + 2) := by omega
    have he := setting_ambient_energy_grading_upto P (K + D + 2) (max (k + 1) (L + 2)) hsZ
      Cc hseq P₀ hres hΘ hh hhh n hnN m j hmn hj
    have hw := setting_ambient_wiener_grading_upto P (K + D + 2) (max (k + 1) (L + 2)) hsZ
      Cc hseq P₀ hres hΘ hh hhh n hnN m j hmn hj
    have hb := hbound hh hhh n hnN m (hmn.trans hnN) j hj
    constructor
    · apply he.trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb.1 (pow_nonneg hΘ hh)) (pow_nonneg hlam _)
    · apply hw.trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb.2 (pow_nonneg hΘ hh)) (pow_nonneg hlam _)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The symmetric source-flux mean coefficients act on the actual lift polynomial. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem sourceFlux_normalized_mean_contDiff_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n p : ℕ) (hp : p ≤ qs)
    (M : ℕ → ι → ι → ℝ)
    (data : ∀ j ≤ min (D - 1) n,
      AmbientLiftCoefficientData par a b P.window lam (n - j)
        (p + j) ((D - 1) - j) (Cc hh (n - j)) (M j))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (k₀ : Fin 2)
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i)
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i)
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t = 0)
    :
    ContDiff ℝ (p : ℕ∞) (fun X => (Real.exp ((lam • A) X))⁻¹ •
      fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η n t
        (fun ε => liftPolyField Cc N ε hh
          (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ X z v)) := by
  let f := fun Y => Real.exp ((lam • A) Y) • Pi.single u ξ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul contDiff_const
  let J := Finset.range (min (D - 1) n + 1)
  let F := fun j X z => (Real.exp ((lam • A) X))⁻¹ •
    sourceFluxComponentCoefficient Q.edge Q.η t
      (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) k₀ j v X z
  have hbox j (hj : j ∈ J) : IsBoxSmooth p 0 (F j) := by
    have hj' : j ≤ min (D - 1) n := by have := Finset.mem_range.mp hj; omega
    exact setting_ambient_sourceFlux_lift_box P Cc hh (n - j) p 0 j _ _ hp
      (Nat.zero_le qf) le_rfl (by simp) _ (data j hj') A k₀ t ht v u ξ
  have hmean j (hj : j ∈ J) : ContDiff ℝ (p : ℕ∞) (fun X => fieldCellMean (F j X)) := by
    have hj' : j ≤ min (D - 1) n := by have := Finset.mem_range.mp hj; omega
    let C := finiteLiftSymbolBudget (n - j) A * normalizedSourceUniformConstant D p 0 j A Cj *
      finiteMatrixProduct (physicalEdgeEnvelopeMatrix π edge) (M j) v u * ‖ξ‖
    apply (fieldCellMean_graded_jet_bound p 0 0 n (Nat.zero_le p) (F j) (hbox j hj)
      (fun _ => C) lam ?_).1
    intro r hr X z
    have hb := setting_ambient_sourceFlux_lift_bound P Cc hh (n - j) p 0 j _ _ hp
      (Nat.zero_le qf) le_rfl (by simp) _ (data j hj') A k₀ t ht v u ξ r 0 hr
      (Nat.zero_le 0) X z
    have he : n - j + j = n := Nat.sub_add_cancel (hj'.trans (min_le_right _ _))
    simpa only [norm_mixed_jet_fast_zero, he, F, C, f] using hb
  have he : (fun X => (Real.exp ((lam • A) X))⁻¹ •
      fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η n t
        (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀ X z v)) =
      fun X => ∑ j ∈ J, fieldCellMean (F j X) := by
    funext X
    rw [← AVRegularity.fieldCellMean_smul]
    have he' : (fun z => (Real.exp ((lam • A) X))⁻¹ •
        sourceFluxCoeff Q.edge Q.η n t
          (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀ X z v) =
        fun z => ∑ j ∈ J, F j X z := by
      funext z
      rw [sourceFlux_component_convolution_of_coefficients P Cc hh n f hf k₀ t ht X z v
        (fun j hj m hm α w w' => ((data j hj).box m hm α w w' t ht).mono
          (by omega) le_rfl) hgood hcut, Finset.smul_sum]
    rw [he', AVRegularity.fieldCellMean_sum J
      (fun j hj => ((hbox j hj).1 X).continuous)]
  rw [he]
  exact ContDiff.sum hmean

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite full source terms reproduce the literal recurrence source convolution. -/

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
theorem setting_sourceConvolution_leftTerms_apply
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (sourceConvolutionLeftTerms Q.edge Q.η t n (Cc (hh - 1)) v) f X z =
      (∑ j ∈ Finset.range (min D n + 1),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => f) t) X z) v := by
  have hfast k d hd := setting_sourceFlux_leftTerms_box P sX sZ hsZ Cc hseq hh hhpos hhh n hn
    0 1 (Nat.zero_le D) (by omega) k t ht v d hd
  have hslow (_hneq : n ≠ 0) k d hd := setting_sourceFlux_leftTerms_box P sX sZ hsZ Cc hseq
    hh hhpos hhh (n - 1) (by omega) 1 0 (by have h := P.D_ge; omega) (Nat.zero_le _)
    k t ht v d hd
  rw [sourceConvolutionLeftTerms_apply Q.edge Q.η t n (Cc (hh - 1)) v hfast hslow f hf X z,
    setting_source_lift_convolution P sX sZ hsZ Cc hseq (hh - 1) (by omega) n (by omega) f hf t ht X z]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  let F := fun m Y y => sourceFluxCoeff Q.edge Q.η m t
    (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k Y y
  let L₀ : (∀ i, h i) →L[ℝ] h v := ContinuousLinearMap.proj v
  have hbox m (hm : m ≤ N) : IsBoxSmooth 1 1 (F m) :=
    setting_sourceFlux_lift_box_one P sX sZ hsZ Cc hseq hh hhpos hhh m hm f hf k t ht
  have he := covariantCoefficientStep_postcomposition Q.η k F n L₀
    ((hbox n hn).mono (by omega) le_rfl)
    (fun _ => (hbox (n - 1) (by omega)).mono le_rfl (by omega)) X z
  change _ = L₀ (covariantCoefficientStep Q.η k F n X z)
  rw [← he]
  have hfield m (hm : m ≤ N) :
      leftTermsApply (sourceFluxConvolutionLeftTerms Q.edge Q.η t m (Cc (hh - 1)) k v) f =
      fun Y y => L₀ (F m Y y) := by
    funext Y y
    exact setting_sourceFlux_leftTerms_apply P sX sZ hsZ Cc hseq hh hhpos hhh m hm f hf k t ht Y y v
  simp only [covariantCoefficientStep, hfield n hn, hfield (n - 1) (by omega)]
end

/-! The finite full source terms reproduce the literal recurrence source convolution. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_sourceConvolution_leftTerms_apply_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι)
    (hc : ∀ i m, m ≤ i → ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth D D (fun X z => Cc hh i m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    leftTermsApply (sourceConvolutionLeftTerms Q.edge Q.η t n (Cc hh) v) f X z =
      (∑ j ∈ Finset.range (min D n + 1),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) v := by
  have hd := P.D_ge
  have hterms (i p q : ℕ) (hp : p ≤ 1) (hq : q ≤ 1) (k : Fin 2) (w : ι)
      (d : LeftTerm (∀ i, h i) (h w))
      (hd' : d ∈ sourceFluxConvolutionLeftTerms Q.edge Q.η t i (Cc hh) k w) :
      IsBoxSmooth p q d.coeff := by
    apply setting_sourceFlux_leftTerms_box_of_coefficients P Cc hh i p q
      (by omega) (by omega) k t ht w ?_ d hd'
    intro j hj m hm α u u'
    exact (hc (i - j) m hm α u u').mono
      (by have := hj.trans (min_le_left _ _); omega) (by omega)
  have hfast k d hd' := hterms n 0 1 (by omega) (by omega) k v d hd'
  have hslow (_hneq : n ≠ 0) k d hd' :=
    hterms (n - 1) 1 0 (by omega) (by omega) k v d hd'
  rw [sourceConvolutionLeftTerms_apply Q.edge Q.η t n (Cc hh) v hfast hslow f hf X z,
    setting_source_lift_convolution_of_coefficients P Cc hh n (by omega) f hf t ht X z
      hgood hcut]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  let F := fun m Y y => sourceFluxCoeff Q.edge Q.η m t
    (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k Y y
  let L₀ : (∀ i, h i) →L[ℝ] h v := ContinuousLinearMap.proj v
  have hfield i w :
      leftTermsApply (sourceFluxConvolutionLeftTerms Q.edge Q.η t i (Cc hh) k w) f =
        fun Y y => F i Y y w := by
    funext Y y
    exact sourceFlux_leftTerms_apply_of_coefficients P Cc hh i f hf k t ht Y y w
      (fun j hj m hm α u u' => (hc (i - j) m hm α u u').mono
        (by have := hj.trans (min_le_left _ _); omega) (by omega)) hgood hcut
  have hbox i : IsBoxSmooth 1 1 (F i) := by
    apply isBoxSmooth_pi
    intro w
    rw [← hfield i w]
    exact leftTermsApply_box _ 1 1 (hterms i 1 1 le_rfl le_rfl k w) f hf
  have he := covariantCoefficientStep_postcomposition Q.η k F n L₀
    ((hbox n).mono (by omega) le_rfl)
    (fun _ => (hbox (n - 1)).mono le_rfl (by omega)) X z
  change _ = L₀ (covariantCoefficientStep Q.η k F n X z)
  rw [← he]
  have hproj i :
      leftTermsApply (sourceFluxConvolutionLeftTerms Q.edge Q.η t i (Cc hh) k v) f =
        fun Y y => L₀ (F i Y y) := hfield i v
  simp only [covariantCoefficientStep, hproj n, hproj (n - 1)]
end

/-! The finite full source terms reproduce the literal recurrence source convolution. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_sourceConvolution_leftTerms_apply_of_coefficients_all_degrees
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι)
    (hc : ∀ i m, m ≤ i → ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth D D (fun X z => Cc hh i m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    leftTermsApply (sourceConvolutionLeftTerms Q.edge Q.η t n (Cc hh) v) f X z =
      (∑ j ∈ Finset.range (min D n + 1),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) v := by
  have hd := P.D_ge
  have hterms (i p q : ℕ) (hp : p ≤ 1) (hq : q ≤ 1) (k : Fin 2) (w : ι)
      (d : LeftTerm (∀ i, h i) (h w))
      (hd' : d ∈ sourceFluxConvolutionLeftTerms Q.edge Q.η t i (Cc hh) k w) :
      IsBoxSmooth p q d.coeff := by
    apply setting_sourceFlux_leftTerms_box_of_coefficients P Cc hh i p q
      (by omega) (by omega) k t ht w ?_ d hd'
    intro j hj m hm α u u'
    exact (hc (i - j) m hm α u u').mono
      (by have := hj.trans (min_le_left _ _); omega) (by omega)
  have hfast k d hd' := hterms n 0 1 (by omega) (by omega) k v d hd'
  have hslow (_hneq : n ≠ 0) k d hd' :=
    hterms (n - 1) 1 0 (by omega) (by omega) k v d hd'
  rw [sourceConvolutionLeftTerms_apply Q.edge Q.η t n (Cc hh) v hfast hslow f hf X z,
    setting_source_lift_convolution_of_coefficients_all_degrees P Cc hh n f hf t ht X z
      hgood hcut]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  let F := fun m Y y => sourceFluxCoeff Q.edge Q.η m t
    (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k Y y
  let L₀ : (∀ i, h i) →L[ℝ] h v := ContinuousLinearMap.proj v
  have hfield i w :
      leftTermsApply (sourceFluxConvolutionLeftTerms Q.edge Q.η t i (Cc hh) k w) f =
        fun Y y => F i Y y w := by
    funext Y y
    exact sourceFlux_leftTerms_apply_of_coefficients P Cc hh i f hf k t ht Y y w
      (fun j hj m hm α u u' => (hc (i - j) m hm α u u').mono
        (by have := hj.trans (min_le_left _ _); omega) (by omega)) hgood hcut
  have hbox i : IsBoxSmooth 1 1 (F i) := by
    apply isBoxSmooth_pi
    intro w
    rw [← hfield i w]
    exact leftTermsApply_box _ 1 1 (hterms i 1 1 le_rfl le_rfl k w) f hf
  have he := covariantCoefficientStep_postcomposition Q.η k F n L₀
    ((hbox n).mono (by omega) le_rfl)
    (fun _ => (hbox (n - 1)).mono le_rfl (by omega)) X z
  change _ = L₀ (covariantCoefficientStep Q.η k F n X z)
  rw [← he]
  have hproj i :
      leftTermsApply (sourceFluxConvolutionLeftTerms Q.edge Q.η t i (Cc hh) k v) f =
        fun Y y => L₀ (F i Y y) := hfield i v
  simp only [covariantCoefficientStep, hproj n, hproj (n - 1)]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The symmetric source-flux mean coefficients act on the actual lift polynomial. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
 [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_sourceFlux_mean_coefficient_apply_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι)
    (hc : ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc hh (n - j) m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    liftApply n (sourceFluxMeanCoefficient Q.edge Q.η t n (Cc hh) k₀)
      (fun _ => f) t X z v =
      fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η n t
        (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀ X z v) := by
  unfold sourceFluxMeanCoefficient
  rw [leftTermsMeanBlockCoefficient_apply _ n
    (sourceFluxConvolutionLeftTerms_order Q.edge Q.η t n (Cc hh) k₀)
    (fun w => setting_sourceFlux_leftTerms_box_of_coefficients P Cc hh n 0 0
      (Nat.zero_le _) (Nat.zero_le _) k₀ t ht w (by simpa only [zero_add] using hc))
    f hf t X z v]
  congr 1
  funext y
  exact sourceFlux_leftTerms_apply_of_coefficients P Cc hh n f hf k₀ t ht X y v hc hgood hcut
end

/-! The symmetric source-flux mean coefficients act on the actual lift polynomial. -/

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
theorem setting_sourceFlux_mean_coefficient_apply
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    liftApply (n - 1) (sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀)
      (fun _ => f) t X z v =
      fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v) := by
  have hc : ∀ j ≤ min (D - 1) (n - 1), ∀ m ≤ n - 1 - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc (hh - 1) (n - 1 - j) m α t X z u u') := by
    intro j hj m hm α u u'
    have hjn : j ≤ n - 1 := le_trans hj (min_le_right _ _)
    have state := setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
      P₀ hreserve (hh - 1) (by omega) (n - 1 - j) (by omega)
    have hres := ambient_flux_predecessor_reserve P₀ (max k (L + 2)) D H (N + D)
      hh n j hhpos hhh hn hnR hjn
    exact (state.coefficient.box m hm α u u' t ht).mono
      (show j ≤ ambientDegreeSlowReserve P₀ (N + D) (n - 1 - j) by omega) hres.2
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 0 0 (fun X z => γ.coeff α t X z k₀) := by
    intro v u d γ hγ α
    exact ((P.coeff_smooth v u d γ hγ α t ht).mono (Nat.zero_le _) (Nat.zero_le _)).clm_comp
      (ContinuousLinearMap.proj k₀ : Vec 2 →L[ℝ] ℝ)
  rw [sourceFluxMeanCoefficient_apply Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ hc hΓ f hf X z v]
  congr 1
  funext z
  exact (setting_sourceFlux_lift_component_convolution_smooth P sX sZ hsZ Cc hseq
    P₀ hreserve hh hhpos hhh n hn hnR f hf k₀ t ht v X z).symm
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite uncentered terms give exactly the literal recurrence action. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftB1_leftTerms_apply
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (cellB1LeftTerms Q.η (Q.G t) (Q.v t)
      (liftComponentLeftTerms n (Cc hh n) t v)) f X z =
      cellB1 Q.η Q.G Q.v t (liftApply n (Cc hh n) (fun _ => f) t) X z v := by
  have hG := setting_metric_contDiff_one P t ht
  have hGb i j := isBoxSmooth_slow_field 1 0 (fun Y => Q.G t Y i j) (hG i j)
  have htms d hd := setting_lift_cross_terms_box P sX sZ hsZ Cc hseq hh hhh n hn v t ht d hd
  rw [cellB1LeftTerms_apply Q.η Q.G Q.v t _ hG
    (fun d hd => (htms d hd).mono (by omega) (by omega)) f hf X z]
  have he : leftTermsApply (liftComponentLeftTerms n (Cc hh n) t v) f =
      fun Y y => liftApply n (Cc hh n) (fun _ => f) t Y y v := by
    funext Y y
    exact liftComponentLeftTerms_apply n (Cc hh n) t v f Y y
  rw [he]
  have hb := setting_lift_cross_field_box P sX sZ hsZ Cc hseq hh hhh n hn f hf t ht
  exact cellB1_postcomposition (ContinuousLinearMap.proj v) Q.η Q.G Q.v t _
    (hb.mono (by omega) (by omega)) hGb X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The actual averaged flux operator has no zero tested-order coefficient. -/

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
theorem setting_sourceFlux_mean_coefficient_zero_order
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (α : DerivativeWord2 0) (X z : Vec 2) (v u : ι) :
    sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ 0 α t X z v u = 0 := by
  ext ξ
  have he := setting_sourceFlux_mean_coefficient_apply P sX sZ hsZ Cc hseq
    P₀ hreserve hh hhpos hhh n hn hnR (fun _ => Pi.single u ξ) contDiff_const k₀ t ht X z v
  rw [liftApply_constant_single (n - 1) _ α t X z v u ξ] at he
  rw [liftPolynomial_sourceFluxCoeff_const P sX sZ Cc hseq (Pi.single u ξ)
    (hh - 1) (by omega) (n - 1) t ht k₀] at he
  simpa only [Pi.zero_apply, fieldCellMean, MeasureTheory.integral_zero, zero_apply] using he
end

/-! The actual positive-height mean flux has a symmetric differential coefficient array. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}

def positiveMeanFluxCoefficient (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (k₀ : Fin 2) : LiftCoeff ι h :=
  fun m α t X z v u =>
    weightedLiftCoefficientMean (Cc hh (n - 1))
      (fun t z => Real.sqrt Q.η * Q.v t z k₀) m α t X z v u -
    Real.sqrt Q.η •
      sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m α t X z v u

variable
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_positive_mean_flux_coefficient_apply
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k₀) (fun _ => f) t X z v =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) •
        liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t X z v) -
      Real.sqrt Q.η • fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v) := by
  let c := weightedLiftCoefficientMean (Cc hh (n - 1))
    (fun t z => Real.sqrt Q.η * Q.v t z k₀)
  let d : LiftCoeff ι h := fun m α t X z v u =>
    sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m α t X z v u
  change liftApply (n - 1) (fun m α t X z v u => c m α t X z v u -
    Real.sqrt Q.η • d m α t X z v u) (fun _ => f) t X z v = _
  rw [liftApply_coefficient_sub, liftApply_coefficient_smul]
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [weightedLiftCoefficientMean_apply (n - 1) _ _ _ t X z v
    ((setting_normalized_drift_contDiff_one P t ht k₀).continuous)
    (fun m _ α u => (hseq.2.2.2.2.2.1 hh hhh (n - 1) m α v u t ht).1.1 X |>.continuous)]
  have hd : liftApply (n - 1) d (fun _ => f) t X z v =
      fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v) := by
    simpa only [liftApply, d] using setting_sourceFlux_mean_coefficient_apply P
      sX sZ hsZ Cc hseq P₀ hreserve hh hhpos hhh n hn hnR f hf k₀ t ht X z v
  rw [hd]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite uncentered terms give exactly the literal recurrence action. -/

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
theorem setting_liftB2_leftTerms_apply
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (cellB2LeftTerms Q.η (Q.G t)
      (liftComponentLeftTerms n (Cc hh n) t v)) f X z =
      cellB2 Q.η Q.G t (liftApply n (Cc hh n) (fun _ => f) t) X z v := by
  apply cellB2_liftComponentLeftTerms_apply Q.η Q.G n (Cc hh n) t ?_
    (setting_metric_contDiff_one P t ht) f hf X z v
  intro m hm α u u'
  exact (setting_lift_cross_coefficient_box P sX sZ hsZ Cc hseq hh hhh
    n hn m hm α u u' t ht).mono le_rfl (by omega)
end

/-! The finite uncentered terms give exactly the literal recurrence action. -/

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
theorem setting_liftA_leftTerms_apply
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (liftALeftTerms Q Cc hh n t v) f X z =
      liftA Q Cc (fun _ => f) hh n t X z v := by
  have hB1 := setting_liftB1_leftTerms_apply P sX sZ hsZ Cc hseq hh hhh
    (n - 1) (by omega) f hf t ht X z v
  have hB2 (_hn2 : 2 ≤ n) := setting_liftB2_leftTerms_apply P sX sZ hsZ Cc hseq hh hhh
    (n - 2) (by omega) f hf t ht X z v
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
    rw [hB2 hn2, setting_sourceConvolution_leftTerms_apply P sX sZ hsZ Cc hseq
      hh (by omega) hhh n hnN f hf t ht X z v]
    simp [liftA, hn2, hh0, sub_eq_add_neg]
  · simp [hn2, hh0, leftTermsApply_nil, liftA]
  · simp only [ite_eq_right hn2, ite_eq_right hh0, leftTermsApply_nil, leftTermsApply_map_smul]
    rw [setting_sourceConvolution_leftTerms_apply P sX sZ hsZ Cc hseq
      hh (by omega) hhh n hnN f hf t ht X z v]
    simp [liftA, hn2, hh0, sub_eq_add_neg]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The symmetric source-flux mean coefficients act on the actual lift polynomial. -/

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
theorem sourceFluxMeanCoefficient_box_of_predecessor_data
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n p q : ℕ) (hp : p ≤ qs)
    (M : ℕ → ι → ι → ℝ)
    (data : ∀ j ≤ min (D - 1) n,
      AmbientLiftCoefficientData par a b P.window lam (n - j)
        (p + j) ((D - 1) - j) (Cc hh (n - j)) (M j))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (k₀ : Fin 2) (u v : ι)
    (hgood : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u, ∀ i,
      GoodField D (liftApply i (Cc hh i)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t))
    (hcut : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u, ∀ i, N < i →
      liftApply i (Cc hh i)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t = 0)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) :
    IsBoxSmooth p q (fun X z =>
      sourceFluxMeanCoefficient Q.edge Q.η t n (Cc hh) k₀ m α t X z v u) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  apply liftCoefficient_box_reserve_of_finite_tests p q n m hm _ lam hlam.ne'
    (sourceFluxMeanCoefficient_perm Q.edge Q.η t n (Cc hh) k₀ m) α t v u
  intro ξ j s
  let A : Vec 2 →L[ℝ] ℝ := (s : ℝ) • coordinateSymbolDirection (j : ℝ)
  have he : (s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ)) = lam • A :=
    smul_comm _ _ _
  simp only [he]
  let f := fun Y => Real.exp ((lam • A) Y) • Pi.single u ξ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul contDiff_const
  have ha : (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftApply n (sourceFluxMeanCoefficient Q.edge Q.η t n (Cc hh) k₀)
        (fun _ => f) t X z v) =
      fun X _ => (Real.exp ((lam • A) X))⁻¹ •
        fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η n t
          (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀ X z v) := by
    funext X z
    rw [setting_sourceFlux_mean_coefficient_apply_of_coefficients P Cc hh n f hf k₀ t ht X z v
      (fun j hj m hm α w w' => ((data j hj).box m hm α w w' t ht).mono
        (by omega) le_rfl) (hgood A ξ) (hcut A ξ)]
  rw [ha]
  exact isBoxSmooth_slow_field p q _
    (sourceFlux_normalized_mean_contDiff_of_coefficients P Cc hh n p hp M data A u v ξ
      t ht k₀ (hgood A ξ) (hcut A ξ))
end

/-! Positive-height flux coefficients are symmetric and have no zero tested order. -/

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
theorem setting_positive_mean_flux_coefficient_perm
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (k₀ : Fin 2) (m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    positiveMeanFluxCoefficient Q Cc hh n k₀ m (α ∘ σ) =
      positiveMeanFluxCoefficient Q Cc hh n k₀ m α := by
  funext t X z v u
  unfold positiveMeanFluxCoefficient
  rw [weightedLiftCoefficientMean_perm _ _ m (hseq.2.2.2.2.1 hh hhh (n - 1) m) α σ,
    sourceFluxMeanCoefficient_perm]

include P in
theorem setting_positive_mean_flux_coefficient_zero_order
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (α : DerivativeWord2 0) (X z : Vec 2) (v u : ι) :
    positiveMeanFluxCoefficient Q Cc hh n k₀ 0 α t X z v u = 0 := by
  unfold positiveMeanFluxCoefficient
  rw [weightedLiftCoefficientMean_zero_order _ _ α t X z v u
    (fun y => liftSequence_zero_order_coefficient_zero P sX sZ Cc hseq
      hh hhh (n - 1) (by omega) α t ht X y v u),
    setting_sourceFlux_mean_coefficient_zero_order P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR k₀ t ht α X z v u]
  simp only [smul_zero, sub_zero]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Averaged divergence coefficients have no fast-variable dependence. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

omit [Fintype ι] in
theorem metricFluxCoefficient_fast_constant (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2) (m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    metricFluxCoefficient (h := h) η G k m α t X z v u =
      metricFluxCoefficient η G k m α t X 0 v u := by
  cases m with
  | zero => rfl
  | succ m => cases m <;> rfl

theorem positiveMeanFluxCoefficient_fast_constant (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (k : Fin 2) (m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    positiveMeanFluxCoefficient Q Cc hh n k m α t X z v u =
      positiveMeanFluxCoefficient Q Cc hh n k m α t X 0 v u := rfl

omit [Fintype ι] in
theorem diagonalMeanFluxCoefficient_fast_constant (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (n : ℕ) (k : Fin 2) (m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    diagonalMeanFluxCoefficient Q Cc n k m α t X z v u =
      diagonalMeanFluxCoefficient Q Cc n k m α t X 0 v u := by
  unfold diagonalMeanFluxCoefficient
  rw [metricFluxCoefficient_fast_constant]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The actual positive-height mean flux has a symmetric differential coefficient array. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
   [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}

variable
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_positive_mean_flux_coefficient_apply_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι)
    (hc : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ u,
      Continuous (fun y => Cc hh (n - 1) m α t X y v u))
    (hsource : ∀ j ≤ min (D - 1) (n - 1), ∀ m ≤ n - 1 - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc (hh - 1) (n - 1 - j) m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc (hh - 1) i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc (hh - 1) i) (fun _ => f) t = 0) :
    liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k₀) (fun _ => f) t X z v =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) •
        liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t X z v) -
      Real.sqrt Q.η • fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v) := by
  let c := weightedLiftCoefficientMean (Cc hh (n - 1))
    (fun t z => Real.sqrt Q.η * Q.v t z k₀)
  let d : LiftCoeff ι h := fun m α t X z v u =>
    sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m α t X z v u
  change liftApply (n - 1) (fun m α t X z v u => c m α t X z v u -
    Real.sqrt Q.η • d m α t X z v u) (fun _ => f) t X z v = _
  rw [liftApply_coefficient_sub, liftApply_coefficient_smul]
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [weightedLiftCoefficientMean_apply (n - 1) _ _ _ t X z v
    ((setting_normalized_drift_contDiff_one P t ht k₀).continuous)
    hc]
  have hd : liftApply (n - 1) d (fun _ => f) t X z v =
      fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v) := by
    simpa only [liftApply, d] using setting_sourceFlux_mean_coefficient_apply_of_coefficients P
      Cc (hh - 1) (n - 1) f hf k₀ t ht X z v hsource hgood hcut
  rw [hd]
end

/-! Finite actual exponential mean tests recover the ambient slow regularity of flux coefficients. -/

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
theorem setting_sourceFlux_mean_coefficient_box_upto
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m) (v u : ι) :
    IsBoxSmooth (P₀ + 1) 0 (fun X z =>
      sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m α t X z v u) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  apply liftCoefficient_box_reserve_of_finite_tests (P₀ + 1) 0 (n - 1) m hm
    _ lam hlam.ne' (sourceFluxMeanCoefficient_perm Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀ m)
  intro ξ j s
  let A : Vec 2 →L[ℝ] ℝ := (s : ℝ) • coordinateSymbolDirection (j : ℝ)
  have he : (s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ)) = lam • A :=
    smul_comm _ _ _
  simp only [he]
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun Y => Real.exp ((lam • A) Y) • Pi.single u ξ) :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul contDiff_const
  have ha : (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftApply (n - 1)
        (sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t X z v) =
      fun X _ => (Real.exp ((lam • A) X))⁻¹ •
        fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε (hh - 1)
            (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ X z v) := by
    funext X z
    rw [setting_sourceFlux_mean_coefficient_apply P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR _ hf k₀ t ht X z v]
  rw [ha]
  exact isBoxSmooth_slow_field (P₀ + 1) 0 _
    (setting_ambient_sourceFlux_mean_grading_upto P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR A k₀ t ht v u ξ 0 (by omega)).1
end

/-! The synthesized mean coefficient operator inherits the actual normalized exponential tests. -/

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
theorem setting_sourceFlux_mean_coefficient_normalized_test
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (A : Vec 2 →L[ℝ] ℝ) (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v u : ι) (ξ : h u) (r : ℕ) (hr : r ≤ P₀ + 1) (z : Vec 2) :
    ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => (Real.exp ((lam • A) X))⁻¹ •
      liftApply (n - 1) (sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t X z v) ∧
    ∀ X, ‖iteratedFDeriv ℝ r (fun Y => (Real.exp ((lam • A) Y))⁻¹ •
      liftApply (n - 1) (sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀)
        (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t Y z v) X‖ ≤
      (2 ^ r * ambientSourceFluxMeanConstant P₀ N k L D H hh n A CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) *
          lam ^ (n - 1 + r) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun Y => Real.exp ((lam • A) Y) • Pi.single u ξ) :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul contDiff_const
  have ha : (fun X => (Real.exp ((lam • A) X))⁻¹ •
      liftApply (n - 1) (sourceFluxMeanCoefficient Q.edge Q.η t (n - 1) (Cc (hh - 1)) k₀)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t X z v) =
      fun X => (Real.exp ((lam • A) X))⁻¹ •
        fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε (hh - 1)
            (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) k₀ X z v) := by
    funext X
    rw [setting_sourceFlux_mean_coefficient_apply P sX sZ hsZ Cc hseq
      P₀ hreserve hh hhpos hhh n hn hnR _ hf k₀ t ht X z v]
  rw [ha]
  exact setting_ambient_sourceFlux_mean_grading_upto P sX sZ hsZ Cc hseq
    P₀ hreserve hh hhpos hhh n hn hnR A k₀ t ht v u ξ r hr
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
theorem setting_liftA_leftTerms_apply_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (n : ℕ) (_hn : 1 ≤ n) (hnN : n ≤ N)
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
    rw [hB2 hn2, setting_sourceConvolution_leftTerms_apply_of_coefficients P Cc
      (hh - 1) n hnN f hf t ht X z v (hcS hh0) (hgood hh0) (hcut hh0)]
    simp [liftA, hn2, hh0, sub_eq_add_neg]
  · simp [hn2, hh0, leftTermsApply_nil, liftA]
  · simp only [ite_eq_right hn2, ite_eq_right hh0, leftTermsApply_nil, leftTermsApply_map_smul]
    rw [setting_sourceConvolution_leftTerms_apply_of_coefficients P Cc
      (hh - 1) n hnN f hf t ht X z v (hcS hh0) (hgood hh0) (hcut hh0)]
    simp [liftA, hn2, hh0, sub_eq_add_neg]

end AVRegularity.CycleComparison.Lift
end
