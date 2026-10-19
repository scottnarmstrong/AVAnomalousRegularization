-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.FirstMeanZero
import AVRegularity.EntryWeakAssembly.CoordinateWordRawHilbertCurves
import AVRegularity.EntryWeak.ActualIndependentCoarseEmptySliceData
public import AVRegularity.CycleComparison.Lift.LiftSourceBlockCoefficientAction
public import AVRegularity.EntryWeak.IndependentCenteredChildReanchorCoordinates
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.EntryWeakAssembly.CoordinateWordFiniteWindowHigherProduction

@[expose] public noncomputable section

section
namespace AVRegularity.WeakEntryProofs

/-! Finite source-flux mean coefficients act under genuine edge and predecessor regularity. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem weakSource_lift_convolution_mean
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (n : ℕ) (hn : 1 ≤ n)
    (f : Vec 2 → ∀ i, h i) (_hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X : Vec 2)
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    fieldCellMean (fun z => ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) =
      Real.sqrt Q.η • ∑ k : Fin 2, fderiv ℝ (fun Y =>
        fieldCellMean (sourceFluxCoeff Q.edge Q.η (n - 1) t
          (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k Y)) X (basisVec k) := by
  have hcoef (z : Vec 2) := source_polynomial_input_coefficient Q.edge hD
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

/-! The literal source convolution follows from genuine polynomial input and edge regularity. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem weakSource_lift_convolution_of_coefficients
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y y => γ.coeff α t Y y))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (n : ℕ) (_hn : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (_hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X z : Vec 2)
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    (∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) =
      ∑ k : Fin 2, covariantCoefficientStep Q.η k
        (fun i Y y => sourceFluxCoeff Q.edge Q.η i t
          (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k Y y) n X z := by
  have hcoef := source_polynomial_input_coefficient Q.edge hD
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
    n (by omega) X z
end

/-! The positive mean splits into genuine drift and source-flux divergences. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem weakPositive_mean_split
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => Q.G t X i j))
    (hw : ∀ k, ContDiff ℝ 1 (fun z => Real.sqrt Q.η * Q.v t z k))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (hhpos : 1 ≤ hh) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X : Vec 2)
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
  have hB2 := cellB2_centField Q.η Q.G t hG hΨ
  have hB1 := cellB1_continuous_slice Q.η Q.G Q.v t hG
    (fun k => (hw k).continuous) Φ hΦ X
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
    weakSource_lift_convolution_mean Q hD N t hΓ Cc (hh - 1)
      n (by omega) f hf X hgood hcut]
end

/-! The positive mean splits into genuine drift and source-flux divergences. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem weakPositive_mean_flux_difference
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hGm : ∀ i j, ContDiff ℝ 1 (fun X => Q.G t X i j))
    (hw : ∀ k, ContDiff ℝ 1 (fun z => Real.sqrt Q.η * Q.v t z k))
    (hvp : AVenhance.IsZ2Periodic (Q.v t))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (hhpos : 1 ≤ hh) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X : Vec 2)
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
    refine ⟨((hw k).comp contDiff_snd).smul hΦ₁.1, ?_⟩
    intro Y m z
    dsimp only
    rw [hΦ₁.2 Y m z, hvp m z]
  rw [weakPositive_mean_split Q hD N t hGm hw hΓ Cc hh hhpos n hn f hf X
    hΦ hΨ hgood hcut]
  exact fluxMean_difference (Real.sqrt Q.η) _ _ hF hG X
end

/-! Actual primitive finite-window production gives every reserved classical slow jet. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
open scoped ContDiff
variable {d H : ℕ}

theorem coordinate_word_window_classical_family_exists {a b : ℝ} (hab : a < b)
    (N K : ℕ) (hH : N + (K + N) + 1 ≤ H) (hN : N + 2 ≤ H) (P : MolecularData)
    (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (hs : ∀ t Y, (G t Y).IsSymm)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hbG : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    (he : ∀ Y t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t Y i j * ξ i * ξ j)
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (hf : ∀ t Y, fieldCellMean (fun z => f t z Y) = 0)
    (Cv : ℕ → ℝ) (hCv : ∀ L, 0 ≤ Cv L)
    (hv : ∀ L, L ≤ H → ∀ t, ContDiff ℝ (L : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hbv : ∀ L, L ≤ H → ∀ t j, j ≤ L → ∀ k x,
      ‖iteratedFDeriv ℝ j (fun z => P.v t z k) x‖ ≤ Cv L) :
    ∃ (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
      (Q : Vec d → MolecularData)
      (u : List (Fin d) → Vec d → ℝ → TorusHk K ℂ) (R : List (Fin d) → ℝ),
      (∀ Y, (Q Y).G = fun t => G t Y) ∧ (∀ Y, (Q Y).v = P.v) ∧
      (∀ Y w, w.length ≤ N → IsCellSolution (Icc a b) (dataCoefficients (Q Y))
        (fun t => cellQ0 (coordinateSourceWord f w Y t))
        (coordinateSourceWord F w Y + independentWordMetricFlux
          (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y)) ∧
      (∀ Y w, w.length ≤ N → cellValue (c w Y) a =ᵐ[volume.restrict AVenhance.unitCube] 0) ∧
      (∀ w, w.length ≤ N → 0 ≤ R w ∧ ∀ Y, StronglyMeasurable (u w Y) ∧
        (∀ t, ‖u w Y t‖ ≤ R w) ∧ ∀ t ∈ Icc a b,
          torusHkValueCLM (u w Y t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c w Y) t) ∧
      (∀ w r, w.length + r ≤ N → ∀ t ∈ Icc a b, ∀ n, n + 4 ≤ K → ∀ z,
        ContDiff ℝ (r : ℕ∞) (fun Y => iteratedFDeriv ℝ n
          (realClassicalLift K (mapTorusHk Complex.reCLM (u w Y t))) z)) ∧
      (∀ w r n, w.length + r ≤ N → n + r + 4 ≤ K → ∀ t ∈ Icc a b,
        ContDiff ℝ (r : ℕ∞) (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n
          (realClassicalLift K (mapTorusHk Complex.reCLM (u w X.1 t))) X.2)) ∧
      (4 ≤ K → ∃ B : ℝ, 0 ≤ B ∧ ∀ w r n, w.length + r ≤ N → n + r + 4 ≤ K →
        ∀ t ∈ Icc a b, ∀ X : Vec d × Vec 2,
          ‖iteratedFDeriv ℝ r (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n
            (realClassicalLift K (mapTorusHk Complex.reCLM (u w X.1 t))) X.2) X‖ ≤
              ((d : ℝ) + 1) ^ r * B) := by
  classical
  obtain ⟨c, Q, hQG, hQv, hsol, hi, hreg, hder⟩ :=
    coordinate_word_raw_Hilbert_regular_family_exists hab.le N hN P G hr hm B hB hbG he hs Qf QF hf
  have hvQ (Y : Vec d) (L : ℕ) (hL : L ≤ H) (t : ℝ) : ContDiff ℝ (L : ℕ∞) ((Q Y).v t) := by rw [hQv]; exact hv L hL t
  have hpQ Y t : AVenhance.IsZ2Periodic ((Q Y).v t) := by rw [hQv]; exact hp t
  have hbQ (Y : Vec d) (L : ℕ) (hL : L ≤ H) (t : ℝ) (j : ℕ) (hj : j ≤ L) (k : Fin 2) (x : Vec 2) :
      ‖iteratedFDeriv ℝ j (fun z => (Q Y).v t z k) x‖ ≤ Cv L := by
    rw [hQv]; exact hbv L hL t j hj k x
  let W := {w : List (Fin d) // w.length ≤ N}
  have hcar (w : W) : ∃ R : ℝ, 0 ≤ R ∧ ∀ Y, ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧ ∀ t ∈ Icc a b,
        torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c w.val Y) t :=
    coordinate_word_finite_window_higher_carrier_exists hab N (by omega) hr hm B hB hbG Qf QF Q
      Cv hCv hvQ hpQ hbQ c hsol hi w.val w.property K (by have := w.property; omega)
  choose R hR uu huu using hcar
  let index : List (Fin d) → W := fun w => if h : w.length ≤ N then ⟨w, h⟩ else ⟨[], by simp⟩
  have hindex w (hw : w.length ≤ N) : (index w).val = w := by simp only [index, dite_eq_left hw]
  let u := fun w => uu (index w)
  let RB := fun w => R (index w)
  have hub w (hw : w.length ≤ N) : 0 ≤ RB w ∧ ∀ Y, StronglyMeasurable (u w Y) ∧
      (∀ t, ‖u w Y t‖ ≤ RB w) ∧ ∀ t ∈ Icc a b,
        torusHkValueCLM (u w Y t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c w Y) t := by
    refine ⟨hR (index w), fun Y => ?_⟩
    have hh := huu (index w) Y
    rw [hindex w hw] at hh
    exact hh
  have hP Y : dataCoefficients (Q Y) = ⟨fun t _ => G t Y, (Q Y).v, 0, 0⟩ := by
    simp only [dataCoefficients, hQG, molecularCoefficients]
  have hread (t : ℝ) (ht : t ∈ Icc a b) p (hp : p.length ≤ N) Y :
      torusHkValueCLM (u p Y t) = cellRawTrace (c p Y) t :=
    Lp.ext (((hub p hp).2 Y).2.2 t ht |>.trans
      (cellRawTrace_ae (c p Y) t ((hsol Y p hp).2.2.1 t ht).1).symm)
  have hquot (t : ℝ) (ht : t ∈ Icc a b) (p : List (Fin d)) (hp : p.length < N) (i : Fin d) :
      ∃ R : ℝ, ∀ Y (h : ℝ), h ≠ 0 → ∃ q : TorusHk K ℂ,
        torusHkValueCLM q = h⁻¹ • (cellRawTrace (c p (Y + h • basisVec i)) t -
          cellRawTrace (c p Y) t) ∧ ‖q‖ ≤ R := by
    obtain ⟨R, _, hq⟩ := coordinate_word_window_quotient_carrier_exists hab N (K + N) hH
      hr hm B hB hbG hs Qf QF Q hP P.v hQv Cv hCv hvQ hpQ hbQ c hsol hi p (by omega) K (by omega) i
    refine ⟨R, fun Y h hh => ?_⟩
    obtain ⟨q, _, hqb, hqv⟩ := hq Y h hh
    refine ⟨q t, ?_, hqb t⟩
    have hraw := higherCarrier_smul_raw_value_ae K _ _ t h⁻¹
      (higherCarrier_sub_raw_value_ae K _ _ _ _ t
        (((hub p (by omega)).2 (Y + h • basisVec i)).2.2 t ht)
        (((hub p (by omega)).2 Y).2.2 t ht))
    have heq : torusHkValueCLM (h⁻¹ • (u p (Y + h • basisVec i) t - u p Y t)) =
        h⁻¹ • (cellRawTrace (c p (Y + h • basisVec i)) t - cellRawTrace (c p Y) t) := by
      rw [map_smul, map_sub, hread t ht p (by omega), hread t ht p (by omega)]
    rw [← heq]
    exact Lp.ext ((hqv t ht).trans hraw.symm)

  refine ⟨c, Q, u, RB, hQG, hQv, hsol, hi, hub, ?_, ?_, ?_⟩
  · intro w r hwr t ht n hn z
    exact higher_trace_word_classical_contDiff N K (fun p Y => cellRawTrace (c p Y) t)
      (fun p Y => u p Y t) (hread t ht)
      (fun p hp => (hreg p 0 (by omega) t ht).continuous)
      (fun p hp Y i => hder p hp Y i t ht) RB
      (fun p hp Y => ((hub p hp).2 Y).2.1 t) (hquot t ht) w r hwr n hn z
  · intro w r n hwr hn t ht
    exact higher_trace_word_classical_joint_contDiff N K (fun p Y => cellRawTrace (c p Y) t)
      (fun p Y => u p Y t) (hread t ht)
      (fun p hp => (hreg p 0 (by omega) t ht).continuous)
      (fun p hp Y i => hder p hp Y i t ht) RB
      (fun p hp Y => ((hub p hp).2 Y).2.1 t) (hquot t ht) w r n hwr hn
  · intro hK
    obtain ⟨S, hS, hRS⟩ := finite_word_uniform_budget_exists d N RB
    refine ⟨∑ m : Fin (K - 4 + 1), cellClassicalSobolevConstant K m.val * S,
      Finset.sum_nonneg (fun m _ => mul_nonneg (cellClassicalSobolevConstant_nonneg K m.val) hS), ?_⟩
    intro w r n hwr hn t ht X
    exact higher_trace_word_classical_joint_bound N K (fun p Y => cellRawTrace (c p Y) t)
      (fun p Y => u p Y t) (hread t ht)
      (fun p hp => (hreg p 0 (by omega) t ht).continuous)
      (fun p hp Y i => hder p hp Y i t ht) RB
      (fun p hp Y => ((hub p hp).2 Y).2.1 t) (hquot t ht) hK S hS hRS w r n hwr hn X
end

/-! The source-flux action uses finite coefficient regularity without a transverse lift setting. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

theorem weakSourceFlux_leftTerms_apply_of_coefficients
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (X z : Vec 2) (v : ι)
    (hc : ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j,
      ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j)
        (fun X z => Cc hh (n - j) m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    leftTermsApply (sourceFluxConvolutionLeftTerms Q.edge Q.η t n (Cc hh) k₀ v) f X z =
      sourceFluxCoeff Q.edge Q.η n t
        (fun ε => liftPolyField Cc N ε hh (fun _ => f) t) k₀ X z v := by
  have he := sourceFlux_polynomial_input_coefficient Q.edge hD
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

/-! Genuine edge and predecessor regularity identify the full finite source action. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem weakSourceConvolution_leftTerms_apply_of_coefficients
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 1 1 (fun Y y => γ.coeff α t Y y))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X z : Vec 2) (v : ι)
    (hc : ∀ i m, m ≤ i → ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth D D (fun X z => Cc hh i m α t X z u u'))
    (hgood : ∀ i, GoodField D (liftApply i (Cc hh i) (fun _ => f) t))
    (hcut : ∀ i, N < i → liftApply i (Cc hh i) (fun _ => f) t = 0) :
    leftTermsApply (sourceConvolutionLeftTerms Q.edge Q.η t n (Cc hh) v) f X z =
      (∑ j ∈ Finset.range (min D n + 1),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc hh (n - j)) (fun _ => f) t) X z) v := by
  have hterms (i p q : ℕ) (hp : p ≤ 1) (hq : q ≤ 1) (k : Fin 2) (w : ι)
      (d : LeftTerm (∀ i, h i) (h w))
      (hd' : d ∈ sourceFluxConvolutionLeftTerms Q.edge Q.η t i (Cc hh) k w) :
      IsBoxSmooth p q d.coeff := by
    apply sourceFluxConvolutionLeftTerms_box Q.edge Q.η t i (Cc hh) k p q w ?_ ?_ d hd'
    · intro j hj m hm α u u'
      exact (hc (i - j) m hm α u u').mono
        (by have := hj.trans (min_le_left _ _); omega) (by omega)
    · intro u d γ hγ α
      exact ((hΓ w u d γ hγ α).mono hp hq).clm_comp
        (ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ)
  have hfast k d hd' := hterms n 0 1 (by omega) (by omega) k v d hd'
  have hslow (_hneq : n ≠ 0) k d hd' :=
    hterms (n - 1) 1 0 (by omega) (by omega) k v d hd'
  rw [sourceConvolutionLeftTerms_apply Q.edge Q.η t n (Cc hh) v hfast hslow f hf X z,
    weakSource_lift_convolution_of_coefficients Q hD N t
      (fun v u d γ hγ α => ⟨(hΓ v u d γ hγ α).contDiff_uncurry le_rfl le_rfl, γ.periodic α t⟩)
      Cc hh n (by omega) f hf X z hgood hcut]
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
    exact weakSourceFlux_leftTerms_apply_of_coefficients Q hD N Cc hh i f hf k t Y y w
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

/-! Finite source-flux mean coefficients act under genuine edge and predecessor regularity. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [DecidableEq ι] {D : ℕ}

theorem weakSourceFlux_mean_coefficient_apply
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 0 0 (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (X z : Vec 2) (v : ι)
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
    (fun w => sourceFluxConvolutionLeftTerms_box Q.edge Q.η t n (Cc hh) k₀ 0 0 w
      (by simpa only [zero_add] using hc)
      (fun u d γ hγ α => (hΓ w u d γ hγ α).clm_comp
        (ContinuousLinearMap.proj k₀ : Vec 2 →L[ℝ] ℝ)))
    f hf t X z v]
  congr 1
  funext y
  exact weakSourceFlux_leftTerms_apply_of_coefficients Q hD N Cc hh n f hf k₀ t X y v hc hgood hcut
end

/-! Positive-grade mean-flux coefficients have their literal action without a transverse setting. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [DecidableEq ι] {D : ℕ}

theorem weakPositive_mean_flux_coefficient_apply
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hv : ∀ k, Continuous (fun z => Real.sqrt Q.η * Q.v t z k))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 0 0 (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (X z : Vec 2) (v : ι)
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
    (hv k₀)
    hc]
  have hd : liftApply (n - 1) d (fun _ => f) t X z v =
      fieldCellMean (fun z => sourceFluxCoeff Q.edge Q.η (n - 1) t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v) := by
    simpa only [liftApply, d] using weakSourceFlux_mean_coefficient_apply Q hD N t hΓ
      Cc (hh - 1) (n - 1) f hf k₀ X z v hsource hgood hcut
  rw [hd]
end

/-! The actual full uncentered recurrence action follows from metric and edge regularity. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem weakLiftA_leftTerms_apply_of_coefficients
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => Q.G t X i j))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 1 1 (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (n : ℕ) (_hn : 1 ≤ n) (hnN : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X z : Vec 2) (v : ι)
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
    Q.v t hc₁ hG f hf X z v
  have hB2 (hn2 : 2 ≤ n) := cellB2_liftComponentLeftTerms_apply Q.η Q.G
    (n - 2) (Cc hh (n - 2)) t (hc₂ hn2) hG f hf X z v
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
    rw [hB2 hn2, weakSourceConvolution_leftTerms_apply_of_coefficients Q hD N t hΓ Cc
      (hh - 1) n hnN f hf X z v (hcS hh0) (hgood hh0) (hcut hh0)]
    simp [liftA, hn2, hh0, sub_eq_add_neg]
  · simp [hn2, hh0, leftTermsApply_nil, liftA]
  · simp only [ite_eq_right hn2, ite_eq_right hh0, leftTermsApply_nil, leftTermsApply_map_smul]
    rw [weakSourceConvolution_leftTerms_apply_of_coefficients Q hD N t hΓ Cc
      (hh - 1) n hnN f hf X z v (hcS hh0) (hgood hh0) (hcut hh0)]
    simp [liftA, hn2, hh0, sub_eq_add_neg]
end

/-! Primitive mixed source reserves produce actual scalar inverses jointly regular in all slow labels. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
open scoped ContDiff
variable {d H : ℕ}

theorem parameter_regular_scalar_inverse_with_reserve {a b : ℝ} (hab : a < b)
    (N K : ℕ) (hH : N + (K + N) + 1 ≤ H) (hN : N + 2 ≤ H) (hK : N + 4 ≤ K)
    (P : MolecularData) (hvD : IsCellDrift P.v)
    (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (hs : ∀ t Y, (G t Y).IsSymm)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hbG : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    (he : ∀ Y t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t Y i j * ξ i * ξ j)
    {g : ℝ → Vec 2 → Vec d → ℝ} (Qg : IndependentParameterSourceReserve H g)
    (hg : ∀ t Y, ∫ z in AVenhance.unitCube, g t z Y = 0)
    (Cv : ℕ → ℝ) (hCv : ∀ L, 0 ≤ Cv L)
    (hv : ∀ L, L ≤ H → ∀ t, ContDiff ℝ (L : ℕ∞) (P.v t))
    (hbv : ∀ L, L ≤ H → ∀ t j, j ≤ L → ∀ k x,
      ‖iteratedFDeriv ℝ j (fun z => P.v t z k) x‖ ≤ Cv L) :
    ∃ c : Vec d → ℝ → Vec 2 → ℝ,
      (∀ Y, IsCellFieldInverse (fun t => G t Y) P.v N a b 0 (fun t z => g t z Y) (c Y)) ∧
      (∀ r, r ≤ N → ∀ t ∈ Icc a b,
        ContDiff ℝ (r : ℕ∞) (fun X : Vec d × Vec 2 => c X.1 t X.2)) ∧
      ∀ S, S ≤ N → Nonempty (IndependentParameterSourceReserve S
        (independentTimeWindowSource (Ioc a b) (fun t z Y => c Y t z))) := by
  let Qf := Qg.map Complex.ofRealCLM
  let QF := IndependentParameterSourceReserve.zero (P := Vec d) (E := ComplexCellVector) H
  have hf t Y : fieldCellMean (fun z => (g t z Y : ℂ)) = 0 := realCellMean_zero _ (hg t Y)
  obtain ⟨D, Q, u, R, hQG, hQv, hsol, hi, hub, _, hjoint, hbound⟩ :=
    coordinate_word_window_classical_family_exists hab N K hH hN P G hr hm hs B hB hbG he Qf QF hf
      Cv hCv hv hvD.2.2.1 hbv
  have hbase Y : IsCellSolution (Icc a b) (dataCoefficients (Q Y))
      (fun t z => (g t z Y : ℂ)) (fun _ _ => 0) (D [] Y) := by
    have hh := hsol Y [] (by simp)
    have hq : (fun t => cellQ0 (fun z => (g t z Y : ℂ))) = fun t z => (g t z Y : ℂ) :=
      funext (fun t => cellQ0_eq_self_of_mean_zero _ (hf t Y))
    have hfnil : coordinateSourceWord (fun t z Y => Complex.ofRealCLM (g t z Y)) [] Y =
        fun t z => (g t z Y : ℂ) := by
      funext t z
      exact iteratedFDeriv_zero_apply _
    have hFNil : coordinateSourceWord (fun (_ : ℝ) (_ : Vec 2) (_ : Vec d) =>
        (0 : ComplexCellVector)) [] Y = fun _ _ => 0 := by
      funext t z
      exact iteratedFDeriv_zero_apply _
    rw [hfnil, hFNil, independentWordMetricFlux_nil, add_zero, hq] at hh
    exact hh
  have hprod Y : ∃ c : ℝ → Vec 2 → ℝ,
      IsCellFieldInverse (Q Y).G (Q Y).v N a b 0 (fun t z => g t z Y) c ∧
      ∀ t ∈ Icc a b, c t = realClassicalLift K (mapTorusHk Complex.reCLM (u [] Y t)) := by
    apply raw_higher_scalar_inverse hab.le (Q Y) (by rw [hQv]; exact hvD) K N (by omega)
      (fun t z => g t z Y) (independent_source_window_memLp Qf a b Y) (fun t => hg t Y)
      (D [] Y) (hbase Y) (hi Y [] (by simp)) (u [] Y)
    exact fun t ht => ((hub [] (by simp)).2 Y).2.2 t ht
  choose c hc hread using hprod
  refine ⟨c, ?_, ?_, ?_⟩
  · intro Y
    simpa only [hQG, hQv] using hc Y
  · intro r hr t ht
    have heq : (fun X : Vec d × Vec 2 => c X.1 t X.2) =
        fun X : Vec d × Vec 2 => realClassicalLift K (mapTorusHk Complex.reCLM (u [] X.1 t)) X.2 := by
      funext X
      exact congrFun (hread X.1 t ht) X.2
    rw [heq]
    have hh := hjoint [] r 0 (by simpa only [List.length_nil, zero_add] using hr) (by omega) t ht
    exact zero_fast_jet_field_contDiff
      (fun Y => realClassicalLift K (mapTorusHk Complex.reCLM (u [] Y t))) r hh
  · intro S hS
    obtain ⟨C, hC, hb⟩ := hbound (by omega)
    let QS := classicalWindowIndependentSourceReserve S K (by omega) a b (u [])
      (fun Y => ((hub [] (by simp)).2 Y).1)
      (fun t ht => hjoint [] S 0 (by simpa only [List.length_nil, zero_add] using hS) (by omega) t ht)
      (fun n => ((d : ℝ) + 1) ^ n * C)
      (fun n => mul_nonneg (by positivity) hC)
      (fun n hn t ht X => hb [] n 0 (by simpa only [List.length_nil, zero_add] using hn.trans hS)
        (by omega) t ht X)
    refine ⟨QS.congrSource ?_⟩
    funext t z Y
    by_cases ht : t ∈ Ioc a b
    · simp only [independentTimeWindowSource, ite_eq_left ht]
      exact (congrFun (hread Y t ⟨ht.1.le, ht.2⟩) z).symm
    · simp only [independentTimeWindowSource, ite_eq_right ht]
end

/-! Positive-grade mean-flux coefficients have their literal action without a transverse setting. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem weakPositive_mean_flux_coefficient_vector_apply
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hv : ∀ k, Continuous (fun z => Real.sqrt Q.η * Q.v t z k))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 0 0 (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (X z : Vec 2)
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
    (hv k₀).smul
      hΦ
  ext v
  rw [weakPositive_mean_flux_coefficient_apply Q hD N t hv hΓ Cc hh n f hf
    k₀ X z v (fun m hm α u => hc m hm α v u) hsource hgood hcut]
  change fieldCellMean (fun y => G y v) - Real.sqrt Q.η • fieldCellMean (fun y => F y v) =
    (fieldCellMean G - Real.sqrt Q.η • fieldCellMean F) v
  rw [fieldCellMean_pi_apply G hgcont v, fieldCellMean_pi_apply F hfcont v]
  rfl
end

/-! Arbitrary positive parameter ellipticity produces genuine jointly regular scalar inverses. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped ContDiff
variable {d H : ℕ}

theorem elliptic_parameter_scalar_inverse_with_reserve {a b : ℝ} (hab : a < b)
    (N K : ℕ) (hH : N + (K + N) + 1 ≤ H) (hN : N + 2 ≤ H) (hK : N + 4 ≤ K)
    (P : MolecularData) (hvD : IsCellDrift P.v)
    (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (hs : ∀ t Y, (G t Y).IsSymm)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hbG : ∀ n t Y i j, ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    (lo : ℝ) (hlo : 0 < lo)
    (he : ∀ t Y (ξ : Vec 2), lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t Y i j * ξ i * ξ j)
    {g : ℝ → Vec 2 → Vec d → ℝ} (Qg : IndependentParameterSourceReserve H g)
    (hg : ∀ t Y, ∫ z in AVenhance.unitCube, g t z Y = 0)
    (Cv : ℕ → ℝ) (hCv : ∀ L, 0 ≤ Cv L)
    (hv : ∀ L, L ≤ H → ∀ t, ContDiff ℝ (L : ℕ∞) (P.v t))
    (hbv : ∀ L, L ≤ H → ∀ t j, j ≤ L → ∀ k x,
      ‖iteratedFDeriv ℝ j (fun z => P.v t z k) x‖ ≤ Cv L) :
    ∃ c : Vec d → ℝ → Vec 2 → ℝ,
      (∀ Y, IsCellFieldInverse (fun t => G t Y) P.v N a b 0 (fun t z => g t z Y) (c Y)) ∧
      (∀ r, r ≤ N → ∀ t ∈ Icc a b,
        ContDiff ℝ (r : ℕ∞) (fun X : Vec d × Vec 2 => c X.1 t X.2)) ∧
      ∀ S, S ≤ N → Nonempty (IndependentParameterSourceReserve S
        (independentTimeWindowSource (Ioc a b) (fun t z Y => c Y t z))) := by
  have hGb t Y i j : |G t Y i j| ≤ B 0 := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hbG 0 t Y i j
  let P' := ellipticRescaledMolecularData (fun t => G t 0) P.v lo (B 0) P.V hlo
    (hm 0) (fun t => hGb t 0) (fun t => he t 0) P.drift_measurable P.drift_bounded
  let G' := clockParameterMetric G lo⁻¹
  let g' := fun t z Y => lo⁻¹ • g (lo⁻¹ * t) z Y
  let Qg' := independentSourceReserve_clock Qg lo⁻¹
  have hvD' : IsCellDrift P'.v := cellDrift_comp_mul P.v lo⁻¹ hvD
  have hvc (L : ℕ) (hL : L ≤ H) t : ContDiff ℝ (L : ℕ∞) (P'.v t) :=
    (hv L hL _).const_smul _
  have hbc (L : ℕ) (hL : L ≤ H) t j (hj : j ≤ L) k x :
      ‖iteratedFDeriv ℝ j (fun z => P'.v t z k) x‖ ≤ |lo⁻¹| * Cv L := by
    change ‖iteratedFDeriv ℝ j (fun z => lo⁻¹ • P.v (lo⁻¹ * t) z k) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply'
      ((contDiff_pi.mp (hv L hL (lo⁻¹ * t)) k).of_le (by exact_mod_cast hj)).contDiffAt,
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbv L hL _ j hj k x) (abs_nonneg _)
  have hmean t Y : ∫ z in AVenhance.unitCube, g' t z Y = 0 := by
    change (∫ z in AVenhance.unitCube, lo⁻¹ • g (lo⁻¹ * t) z Y) = 0
    rw [integral_smul, hg, smul_zero]
  obtain ⟨c, hc, hj, hreserve⟩ := parameter_regular_scalar_inverse_with_reserve
    (mul_lt_mul_of_pos_left hab hlo) N K hH hN hK P' hvD' G'
    (clockParameterMetric_regular G lo⁻¹ hr) (clockParameterMetric_measurable G lo⁻¹ hm)
    (fun t Y => (hs (lo⁻¹ * t) Y).smul lo⁻¹)
    (fun n => |lo⁻¹| * B n) (fun n => mul_nonneg (abs_nonneg _) (hB n))
    (fun n _ => clockParameterMetric_jet_bound G lo⁻¹ hr B hbG n)
    (clockParameterMetric_coercive G lo hlo he) Qg' hmean
    (fun L => |lo⁻¹| * Cv L) (fun L => mul_nonneg (abs_nonneg _) (hCv L))
    hvc hbc
  refine ⟨fun Y t => c Y (lo * t), ?_, ?_, ?_⟩
  · intro Y
    have hout := cellFieldInverse_comp_mul (fun t => G' t Y) P'.v N a b lo hlo hab.le
      0 (fun t z => g' t z Y) (c Y) (hc Y)
    change IsCellFieldInverse (fun t => lo • (lo⁻¹ • G (lo⁻¹ * (lo * t)) Y))
      (fun t z => lo • (lo⁻¹ • P.v (lo⁻¹ * (lo * t)) z)) N a b 0
      (fun t z => lo • (lo⁻¹ • g (lo⁻¹ * (lo * t)) z Y)) (fun t => c Y (lo * t)) at hout
    simpa only [← mul_assoc, inv_mul_cancel₀ hlo.ne', one_mul, smul_smul,
      mul_inv_cancel₀ hlo.ne', one_smul] using hout
  · intro r hr t ht
    exact hj r hr (lo * t) ⟨mul_le_mul_of_nonneg_left ht.1 hlo.le,
      mul_le_mul_of_nonneg_left ht.2 hlo.le⟩
  · intro S hS
    obtain ⟨QS⟩ := hreserve S hS
    exact ⟨independentSourceReserve_windowTimePrecompose a b lo hlo QS⟩
end

/-! The actual diagonal mean term list reproduces the full-cell mean. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] {D : ℕ}

theorem weakPositive_mean_left_terms_apply
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (N : ℕ) (t : ℝ)
    (hGm : ∀ i j, ContDiff ℝ 1 (fun X => Q.G t X i j))
    (hw : ∀ k, ContDiff ℝ 1 (fun z => Real.sqrt Q.η * Q.v t z k))
    (hvp : AVenhance.IsZ2Periodic (Q.v t))
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 1 1 (fun X z => γ.coeff α t X z))
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) (hhpos : 1 ≤ hh)
    (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X z : Vec 2)
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
    rw [weakPositive_mean_flux_coefficient_vector_apply Q hD N t
      (fun k => (hw k).continuous) (fun v u d γ hγ α => (hΓ v u d γ hγ α).mono (by omega) (by omega))
      Cc hh n f hf k Y 0 (hc Y) hsource hgood hcut (hF k Y)]
    simp only [neg_sub]
  simp_rw [he, fderiv_fun_neg, neg_apply]
  rw [Finset.sum_neg_distrib]
  exact (weakPositive_mean_flux_difference Q hD N t hGm hw hvp
    (fun v u d γ hγ α => ⟨(hΓ v u d γ hγ α).contDiff_uncurry le_rfl le_rfl, γ.periodic α t⟩)
    Cc hh hhpos n hn f hf X hΦ hΨ hgood hcut).symm
end

/-! Both branches of the actual weak mean coefficient depend only on predecessor germs. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem actualMeanFluxCoefficient_slow_local_primitive_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Q Q' : LiftOperatorData ι (fun _ => ℝ) D)
    (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (hG : ∀ X ∈ Ω, Q.G t X = Q'.G t X)
    (hΓ : SlowOpenEdgeEq Ω t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q,
      ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u)
    (k : Fin 2) (m : ℕ) (hm : m ≤ n - 1) (α : DerivativeWord2 m)
    (X : Vec 2) (hX : X ∈ Ω) (z : Vec 2) (v u : ι) :
    actualMeanFluxCoefficient Q Cc hh n k m α t X z v u =
      actualMeanFluxCoefficient Q' Dc hh n k m α t X z v u := by
  by_cases hh0 : hh = 0
  · subst hh
    simp only [actualMeanFluxCoefficient, ite_true, diagonalMeanFluxCoefficient]
    rw [← hη, ← hv]
    apply congrArg₂ (fun a b => a + b)
    · unfold weightedLiftCoefficientMean
      apply congrArg fieldCellMean
      funext y
      rw [he 0 (n - 1) (Or.inr ⟨rfl, by omega⟩) m hm α X hX y v u]
    · by_cases hn2 : n = 2
      · simp only [ite_eq_left hn2]
        cases m with
        | zero => rfl
        | succ m =>
          cases m with
          | zero => simp only [metricFluxCoefficient, hG X hX]
          | succ m => rfl
      · simp only [ite_eq_right hn2]
  · simp only [actualMeanFluxCoefficient, ite_eq_right hh0]
    exact positiveMeanFluxCoefficient_slow_local_edge_congr hΩ Q Q' hη hv Cc Dc
      hh n hn hh0 t hΓ he k m hm α X hX z v u
end

/-! The finite weak coefficient step uses a full two-dimensional cell inverse, without a transverse restriction. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def weakLiftStepWithInverse (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ)
    (prior : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) :
    LiftCoeff ι (fun _ => ℝ) :=
  fun m α t X z v u =>
    if n = 0 then
      if hh = 0 ∧ m = 0 then blockIdentityEntry (fun _ : ι => ℝ) v u else 0
    else if m ≤ n then
      inverse X (fun s y =>
        leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q prior hh n s w)
          m α s X y v u 1) t z • ContinuousLinearMap.id ℝ ℝ
    else 0

theorem weakLiftStepWithInverse_above_order (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ)
    (prior : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n m : ℕ) (hm : n < m)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    weakLiftStepWithInverse Q inverse prior hh n m α t X z v u = 0 := by
  by_cases hn : n = 0
  · simp only [weakLiftStepWithInverse, ite_eq_left hn]
    rw [ite_eq_right (by omega : ¬ (hh = 0 ∧ m = 0))]
  · simp only [weakLiftStepWithInverse, ite_eq_right hn, ite_eq_right (Nat.not_le.mpr hm)]

theorem weakLiftStepWithInverse_perm (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ)
    (prior : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    weakLiftStepWithInverse Q inverse prior hh n m (α ∘ σ) =
      weakLiftStepWithInverse Q inverse prior hh n m α := by
  funext t X z v u
  simp only [weakLiftStepWithInverse, leftTermsBlockCoefficient_perm]
end

/-! The full-cell weak lift uses the same finite triangular rank as the proved transverse lift. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def weakLiftInverseRank (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N : ℕ) :
    ℕ → LiftCoeff ι (fun _ => ℝ) :=
  fun r => Nat.strongRecOn r fun r rec =>
    weakLiftStepWithInverse Q inverse (fun hh n => if n ≤ N then
      if hr : ambientRecurrenceRank N hh n < r then rec (ambientRecurrenceRank N hh n) hr
      else 0 else 0) (r / (N + 1)) (r % (N + 1))

theorem weakLiftInverseRank_eq (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N r : ℕ) :
    weakLiftInverseRank Q inverse N r =
      weakLiftStepWithInverse Q inverse (fun hh n => if n ≤ N then
        if ambientRecurrenceRank N hh n < r then
          weakLiftInverseRank Q inverse N (ambientRecurrenceRank N hh n)
        else 0 else 0) (r / (N + 1)) (r % (N + 1)) := by
  unfold weakLiftInverseRank
  rw [Nat.strongRecOn_eq]
  congr 1

def weakLiftInverseCoefficients (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N : ℕ) :
    ℕ → ℕ → LiftCoeff ι (fun _ => ℝ) :=
  fun hh n => if n ≤ N then
    weakLiftInverseRank Q inverse N (ambientRecurrenceRank N hh n) else 0

theorem weakLiftInverseCoefficients_cutoff (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n : ℕ) (hn : N < n) :
    weakLiftInverseCoefficients Q inverse N hh n = 0 := by
  simp only [weakLiftInverseCoefficients, ite_eq_right (Nat.not_le.mpr hn)]
end

/-! The actual and first-degree recurrence means preserve predecessor germs. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem actualMeanLeftTerms_slow_local_primitive_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Q Q' : LiftOperatorData ι (fun _ => ℝ) D)
    (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (hG : ∀ X ∈ Ω, Q.G t X = Q'.G t X)
    (hΓ : SlowOpenEdgeEq Ω t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q,
      ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    List.Forall₂ (LeftTermSlowEq Ω) (actualMeanLeftTerms Q Cc hh n t)
      (actualMeanLeftTerms Q' Dc hh n t) := by
  unfold actualMeanLeftTerms
  apply meanFluxLeftTerms_slow_local_congr Ω hΩ n
  intro k m hm α X hX v u
  exact actualMeanFluxCoefficient_slow_local_primitive_congr Ω hΩ Q Q' hη hv Cc Dc
    hh n hn t hG hΓ he k m hm α X hX 0 v u

theorem recurrenceMeanLeftTerms_slow_local_primitive_congr
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Q Q' : LiftOperatorData ι (fun _ => ℝ) D)
    (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (t : ℝ) (hG : ∀ X ∈ Ω, Q.G t X = Q'.G t X)
    (hΓ : SlowOpenEdgeEq Ω t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q,
      ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u) :
    List.Forall₂ (LeftTermSlowEq Ω) (recurrenceMeanLeftTerms Q Cc hh n t)
      (recurrenceMeanLeftTerms Q' Dc hh n t) := by
  by_cases hn : 2 ≤ n
  · simp only [recurrenceMeanLeftTerms, ite_eq_left hn]
    exact actualMeanLeftTerms_slow_local_primitive_congr Ω hΩ Q Q' hη hv Cc Dc
      hh n (by omega) t hG hΓ he
  · simp only [recurrenceMeanLeftTerms, ite_eq_right hn]
    exact List.Forall₂.nil
end

/-! Exact finite-prefix equation of the full-cell weak coefficient construction. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem weakLiftInverseCoefficients_eq_step (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n : ℕ) (hn : n ≤ N) :
    weakLiftInverseCoefficients Q inverse N hh n =
      weakLiftStepWithInverse Q inverse (fun p q =>
        if ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n then
          weakLiftInverseCoefficients Q inverse N p q else 0) hh n := by
  rw [weakLiftInverseCoefficients, ite_eq_left hn, weakLiftInverseRank_eq,
    ambientRecurrenceRank_div N hh n hn, ambientRecurrenceRank_mod N hh n hn]
  congr 1
  funext p q
  by_cases hq : q ≤ N <;>
    by_cases hr : ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n <;>
    simp only [weakLiftInverseCoefficients, hq, hr, ite_true, ite_false]

theorem weakLiftInverse_prefix_agreement (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n p q : ℕ)
    (he : p < hh ∨ (p = hh ∧ q < n)) :
    (if ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n then
      weakLiftInverseCoefficients Q inverse N p q else 0) =
      weakLiftInverseCoefficients Q inverse N p q := by
  by_cases hq : q ≤ N
  · have hr : ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n := by
      rcases he with hp | ⟨rfl, hqn⟩
      · exact ambientRecurrenceRank_height N hh n p q hp hq
      · unfold ambientRecurrenceRank
        omega
    exact ite_eq_left hr
  · rw [weakLiftInverseCoefficients_cutoff Q inverse N p q (by omega)]
    split <;> rfl
end

/-! The full-cell lift begins with the literal identity at grade zero and zero at positive grades. -/

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem weakLiftInverseCoefficients_zero_degree (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    weakLiftInverseCoefficients Q inverse N hh 0 m α t X z v u =
      if hh = 0 ∧ m = 0 then blockIdentityEntry (fun _ : ι => ℝ) v u else 0 := by
  rw [weakLiftInverseCoefficients_eq_step Q inverse N hh 0 (Nat.zero_le N)]
  simp only [weakLiftStepWithInverse, ite_true]

theorem weakLiftInverseCoefficients_positive_grade_zero (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh : ℕ) (hhh : 1 ≤ hh)
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    weakLiftInverseCoefficients Q inverse N hh 0 m α t X z v u = 0 := by
  rw [weakLiftInverseCoefficients_zero_degree,
    ite_eq_right (by omega : ¬ (hh = 0 ∧ m = 0))]

theorem weakLiftInverseCoefficients_identity (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (inverse : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N : ℕ)
    (f : ℝ → Vec 2 → ι → ℝ) (t : ℝ) (X z : Vec 2) :
    liftApply 0 (weakLiftInverseCoefficients Q inverse N 0 0) f t X z = f t X := by
  funext v
  simp [liftApply, weakLiftInverseCoefficients_zero_degree, blockIdentityEntry_apply,
    orderedDerivative]
end

end AVRegularity.WeakEntryProofs
end
