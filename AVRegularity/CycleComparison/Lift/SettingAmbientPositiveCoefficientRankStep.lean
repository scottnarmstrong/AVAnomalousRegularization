-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingWindowInverseClampedTransverse
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.CellFieldAmbientBoxReserve
public import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients
import AVRegularity.CycleComparison.Lift.SecondCrossMean
public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget
import AVRegularity.CycleComparison.Lift.SettingTransverseFieldInverseExistence
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The actual normalized lift test inherits ambient degree grading from its literal source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftSequence_ambient_test_grading_of_source
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q r j : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hp : p ≤ qs) (hq : 2 ≤ q) (hr : r ≤ p) (hj : j ≤ q)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t))
    (hft : IsTransverseOn par (Icc a b) (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ))
    (hfm : ∀ l : h v →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ k : Fin 2 → ℤ, ∀ z,
      normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X
        (z + AVenhance.Infra.Torus.intVector k) =
          normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X,
      fieldCellMean (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
        (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y) z) X‖ ≤
          C * lam ^ (n + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t Y) z) X‖ ≤
        (ambientInverseUniformConstant p (metricParameterBudget p CG) (3 / 4) * C) * lam ^ (n + r) := by
  have hi (Y : Vec 2) : IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v sZ a b 0
      (fun t z => normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y z)
      (fun t z => normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t Y z) :=
    liftSequence_normalized_exponential_component_inverse Q sX sZ hsZ a b N H Cc hseq
      hh n hhh hn hnN (lam • A) u v ξ Y
  exact setting_window_inverse_clamped_source_graded_bound P p q sZ n r j hp hq hr hj
    (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
    (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ) hi
    hf hft hfm hper hcenter C hC hb t ht X z
end

/-! The actual normalized lift test inherits ambient rectangular regularity from its literal source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftSequence_ambient_test_box_reserve_of_source
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hp : p ≤ qs) (hq : 2 ≤ q)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t))
    (hft : IsTransverseOn par (Icc a b) (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ))
    (hfm : ∀ l : h v →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ k : Fin 2 → ℤ, ∀ z,
      normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X
        (z + AVenhance.Infra.Torus.intVector k) =
          normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X,
      fieldCellMean (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
        (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y) z) X‖ ≤
          C * lam ^ (n + r))
    (t : ℝ) (ht : t ∈ Icc a b) :
    IsBoxSmooth p q (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t) := by
  have hi (Y : Vec 2) : IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v sZ a b 0
      (fun t z => normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y z)
      (fun t z => normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t Y z) :=
    liftSequence_normalized_exponential_component_inverse Q sX sZ hsZ a b N H Cc hseq
      hh n hhh hn hnN (lam • A) u v ξ Y
  exact setting_window_inverse_clamped_source_box_reserve P p q sZ n hp hq
    (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
    (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ) hi
    hf hft hfm hper hcenter C hC hb t ht
end

/-! The original lift setting supplies every coefficient premise for the inverse time equation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_time_integral (q sZ : ℕ) (hq : 2 ≤ q) (hsZ : 2 ≤ sZ)
    (f c : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z, ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    IntervalIntegrable (fun s => -cellOperator (Q.G s X) (Q.v s) (c s X) z + f s X z) volume a t ∧
      c t X z = ∫ s in a..t, -cellOperator (Q.G s X) (Q.v s) (c s X) z + f s X z := by
  obtain ⟨W, hW⟩ := setting_drift_bound P
  have data := setting_inverse_parameter_data P 0 (Nat.zero_le qs) W hW
  have hlocal (Y : Vec 2) : IsCellFieldInverse
      (fun s => Matrix.of (Q.G (Set.projIcc a b P.window s) Y))
      (localCellDrift a b P.window Q.v) sZ a b (0 : Vec 2 → Wspace)
      (fun s z => f s Y z) (fun s z => c s Y z) :=
    cellFieldInverse_local_coefficients (E := Wspace)
      (fun s => Matrix.of (Q.G s Y)) Q.v sZ a b P.window (0 : Vec 2 → Wspace)
      (fun s z => f s Y z) (fun s z => c s Y z) (hc Y)
  obtain ⟨hi, heq⟩ := data.window_clamped_time_integral sZ q hsZ hq a b P.window
    f c hlocal hf hft hfm hper S hS hb t ht X z
  have he (s : ℝ) (hs : s ∈ uIcc a t) :
      -cellOperator (Q.G (Set.projIcc a b P.window s) X)
        (localCellDrift a b P.window Q.v s) (c s X) z + f s X z =
      -cellOperator (Q.G s X) (Q.v s) (c s X) z + f s X z := by
    rw [uIcc_of_le ht.1] at hs
    have hsb : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    rw [Set.projIcc_of_mem P.window hsb, localCellDrift_eq a b P.window Q.v s hsb]
  refine ⟨hi.congr (fun s hs => he s (uIoc_subset_uIcc hs)), ?_⟩
  rw [heq]
  exact intervalIntegral.integral_congr he
end

/-! The actual normalized lift test inherits transverse geometry and clamped measurability from its literal source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftSequence_ambient_test_geometry_of_source
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n q : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N) (hq : 2 ≤ q)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t))
    (hft : IsTransverseOn par (Icc a b) (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ))
    (hfm : ∀ l : h v →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ
        (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ k : Fin 2 → ℤ, ∀ z,
      normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X
        (z + AVenhance.Infra.Torus.intVector k) =
          normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X z)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ j (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X) z‖ ≤ S j) :
    IsTransverseOn par (Icc a b) (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ) ∧
      ∀ l : h v →L[ℝ] ℝ, ∀ X z, Measurable (fun t =>
        l (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ
          (Set.projIcc a b P.window t) X z)) := by
  have hi (Y : Vec 2) : IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v sZ a b 0
      (fun t z => normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y z)
      (fun t z => normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t Y z) :=
    liftSequence_normalized_exponential_component_inverse Q sX sZ hsZ a b N H Cc hseq
      hh n hhh hn hnN (lam • A) u v ξ Y
  refine ⟨?_, ?_⟩
  · exact setting_window_inverse_clamped_transverse P q sZ hq
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
      (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ) hi hf hft hfm hper S hS hb
  · intro l X z
    exact setting_window_inverse_clamped_dual_measurable P q sZ hq
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
      (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ) hi hf hft hfm hper S hS hb l X z
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Original setting data give a fixed inverse constant for genuine window-source grading. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_uniform_metric_difference_bound (p q sZ δ r j : ℕ)
    (hp : p ≤ qs) (hq : 2 ≤ q) (hr : r ≤ p) (hj : j ≤ q)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (f c ci : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hci : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => ci t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => c t Y y - ci t Y y) z) X‖ ≤
      (metricInverseUniformConstant p (metricParameterBudget p CG)
        (metricParameterBudget p CGI) (3 / 4) * C) * g * lam ^ (δ + r) := by
  obtain ⟨W, hW⟩ := setting_drift_bound P
  have data := setting_inverse_parameter_data P p hp W hW
  have hlocal (X : Vec 2) : IsCellFieldInverse
      (fun t => Matrix.of (Q.G (Set.projIcc a b P.window t) X))
      (localCellDrift a b P.window Q.v) sZ a b (0 : Vec 2 → Wspace)
      (fun t z => f t X z) (fun t z => c t X z) :=
    cellFieldInverse_local_coefficients (E := Wspace)
      (fun t => Matrix.of (Q.G t X)) Q.v sZ a b P.window (0 : Vec 2 → Wspace)
      (fun t z => f t X z) (fun t z => c t X z) (hc X)
  have hlocali (X : Vec 2) : IsCellFieldInverse
      (fun _ i j => if i = j then 1 else 0)
      (localCellDrift a b P.window Q.v) sZ a b (0 : Vec 2 → Wspace)
      (fun t z => f t X z) (fun t z => ci t X z) := by
    have hh := cellFieldInverse_local_coefficients (E := Wspace)
      (fun _ i j => if i = j then 1 else 0) Q.v sZ a b P.window
      (0 : Vec 2 → Wspace) (fun t z => f t X z) (fun t z => ci t X z) (hci X)
    exact hh
  have hd := setting_clamped_metric_difference_fixed_data P g hg CGI hGI p hp par.rev
  dsimp only at hd
  exact cellFieldInverse_window_source_uniform_metric_difference_mixed_bound p q sZ δ r j hq hr hj
    _ data.metric _ W data.drift_measurable data.drift_bound par data.transverse
    f c ci a b P.window hlocal hlocali data.diagonal_measurable data.diagonal_smooth
    (metricParameterBudget p CG) (metricParameterBudget p CGI) g lam (3 / 4)
    data.M_nonneg (metricParameterBudget_nonneg p CGI) hg data.lam_nonneg data.kappa_pos
    (by norm_num) data.diagonal_bound hd.2.2 data.diagonal_lower
    hf hft hfm hper hcenter C hC hfb t ht X z
end

/-! Only the clamped source must be measurable; arbitrary values outside the window play no role. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_clamped_source_metric_difference_bound (p q sZ δ r j : ℕ)
    (hp : p ≤ qs) (hq : 2 ≤ q) (hr : r ≤ p) (hj : j ≤ q)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (f c ci : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hci : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => ci t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => c t Y y - ci t Y y) z) X‖ ≤
      (metricInverseUniformConstant p (metricParameterBudget p CG)
        (metricParameterBudget p CGI) (3 / 4) * C) * g * lam ^ (δ + r) := by
  let F := fun t X z => f (Set.projIcc a b P.window t) X z
  have hlocal (X : Vec 2) : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => F t X z) (fun t z => c t X z) := by
    apply cellFieldInverse_source_congr_on (E := Wspace) (fun t => Matrix.of (Q.G t X)) Q.v
      sZ a b 0 (fun t z => f t X z) (fun t z => F t X z) (fun t z => c t X z) _ (hc X)
    intro t ht
    dsimp only [F]
    rw [Set.projIcc_of_mem P.window ht]
  have hlocali (X : Vec 2) : IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) Q.v sZ a b 0
      (fun t z => F t X z) (fun t z => ci t X z) := by
    apply cellFieldInverse_source_congr_on (E := Wspace) (fun _ i j => if i = j then 1 else 0)
      Q.v sZ a b 0 (fun t z => f t X z) (fun t z => F t X z) (fun t z => ci t X z) _ (hci X)
    intro t ht
    dsimp only [F]
    rw [Set.projIcc_of_mem P.window ht]
  have htrans : IsTransverseOn par (Icc a b) F := by
    intro t _ X z s
    exact hft _ (Set.projIcc a b P.window t).2 X z s
  exact setting_window_inverse_uniform_metric_difference_bound P p q sZ δ r j hp hq hr hj
    g hg CGI hGI F c ci hlocal hlocali
    (fun t _ => hf _ (Set.projIcc a b P.window t).2) htrans hfm
    (fun t _ X n z => hper _ (Set.projIcc a b P.window t).2 X n z)
    (fun t _ X => hcenter _ (Set.projIcc a b P.window t).2 X) C hC
    (fun r hr j hj t _ X z => hfb r hr j hj _ (Set.projIcc a b P.window t).2 X z) t ht X z
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual normalized exponential lift tests satisfy their time equation from the proved source reserves. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftSequence_test_time_integral_of_source
    (sX sZ : ℕ) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N) (hq : 2 ≤ q)
    (Ks : (Vec 2 →L[ℝ] ℝ) → ℝ) (M : ι → ι → ℝ)
    (source : AmbientLiftSourceData par a b P.window lam hh n p q Q Cc Ks M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    let c := normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ
    let f := normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ
    IntervalIntegrable (fun s => -cellOperator (Q.G s X) (Q.v s) (c s X) z + f s X z) volume a t ∧
      c t X z = ∫ s in a..t, -cellOperator (Q.G s X) (Q.v s) (c s X) z + f s X z := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hB : 0 ≤ (Ks A * M v u * ‖ξ‖) * lam ^ n :=
    mul_nonneg (mul_nonneg (mul_nonneg (source.constant_nonneg A)
      (source.matrix_nonneg v u)) (norm_nonneg ξ)) (pow_nonneg hlam n)
  apply setting_window_inverse_time_integral P q sZ hq hsZ
    (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
    (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ)
    (fun Y => liftSequence_normalized_exponential_component_inverse Q sX sZ (by omega)
      a b N H Cc hseq hh n hhh hn hnN (lam • A) u v ξ Y)
    (fun s hs => (source.box A u v ξ s hs).mono (Nat.zero_le p) le_rfl)
    (source.transverse A u v ξ) (source.measurable A u v ξ)
    (source.periodic A u v ξ) (fun _ => (Ks A * M v u * ‖ξ‖) * lam ^ n)
    (fun _ _ => hB) ?_ t ht X z
  intro j hj s hs Y w
  simpa only [norm_iteratedFDeriv_zero, Nat.add_zero] using
    source.bound A u v ξ 0 (Nat.zero_le p) j hj s hs Y w

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Only the clamped source must be measurable; arbitrary values outside the window play no role. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_paired_source_bound (p q sZ δ r j : ℕ)
    (hp : p ≤ qs) (hq : 2 ≤ q) (hsZ : 1 ≤ sZ) (hr : r ≤ p) (hj : j ≤ q)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (f fi c mid ci : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hmid : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => mid t X z))
    (hci : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) Q.v sZ a b 0
      (fun t z => fi t X z) (fun t z => ci t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (hdf : ∀ t ∈ Icc a b, IsBoxSmooth p q (fun X z => f t X z - fi t X z))
    (hdft : IsTransverseOn par (Icc a b) (fun t X z => f t X z - fi t X z))
    (hdfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (f (Set.projIcc a b P.window t) X z - fi (Set.projIcc a b P.window t) X z)))
    (hdfper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) - fi t X (z + AVenhance.Infra.Torus.intVector n) =
        f t X z - fi t X z)
    (hdfcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (fun z => f t X z - fi t X z) = 0)
    (Cd : ℝ) (hCd : 0 ≤ Cd)
    (hdfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => f t Y y - fi t Y y) z) X‖ ≤
        (Cd * g) * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => c t Y y - ci t Y y) z) X‖ ≤
      (metricInverseUniformConstant p (metricParameterBudget p CG)
          (metricParameterBudget p CGI) (3 / 4) * C +
        ambientInverseUniformConstant p (metricParameterBudget p (identityMetricJetBudget CG)) (3 / 4) * Cd) *
        g * lam ^ (δ + r) := by
  let Pi := setting_identity_metric P
  let df := fun t X z => f t X z - fi t X z
  let dc := fun t X z => mid t X z - ci t X z
  have hdc (X : Vec 2) : IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) Q.v sZ a b 0
      (fun t z => df t X z) (fun t z => dc t X z) :=
    cellFieldInverse_sub_zero _ Q.v sZ hsZ a b P.window
      (fun t z => f t X z) (fun t z => fi t X z)
      (fun t z => mid t X z) (fun t z => ci t X z) (hmid X) (hci X)
  have hcbox := setting_window_inverse_clamped_source_box_reserve P p q sZ δ hp hq
    f c hc hf hft hfm hper hcenter C hC hfb t ht
  have hmidbox := setting_window_inverse_clamped_source_box_reserve Pi p q sZ δ hp hq
    f mid hmid hf hft hfm hper hcenter C hC hfb t ht
  have hdcbox := setting_window_inverse_clamped_source_box_reserve Pi p q sZ δ hp hq
    df dc hdc hdf hdft hdfm hdfper hdfcenter (Cd * g) (mul_nonneg hCd hg) hdfb t ht
  have hm := setting_window_inverse_clamped_source_metric_difference_bound P p q sZ δ r j hp hq hr hj
    g hg CGI hGI f c mid hc hmid hf hft hfm hper hcenter C hC hfb t ht X z
  have hd := setting_window_inverse_clamped_source_graded_bound Pi p q sZ δ r j hp hq hr hj
    df dc hdc hdf hdft hdfm hdfper hdfcenter (Cd * g) (mul_nonneg hCd hg) hdfb t ht X z
  have htri := norm_mixed_jet_difference_triangle
    ((hcbox.sub hmidbox).mono hr hj) (hdcbox.mono hr hj) X z
  apply htri.trans ((add_le_add hm hd).trans_eq _)
  ring

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
theorem setting_ambient_uncentered_data_of_earlier_coefficients
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hhh : hh ≤ H)
    (hn : 1 ≤ n) (hnR : n ≤ N + D)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (Cc h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u)) :
    AmbientLiftUncenteredData par a b P.window lam hh n (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) Q Cc
      (ambientUncenteredBudget P₀ (max k (L + 2)) D H (N + D) hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj))
      (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n
  have hp : p + 1 ≤ qs :=
    (ambientDegreeSlowReserve_coefficient P₀ (N + D) n hn hnR).trans hreserve
  have hq : q + 1 ≤ qf := by
    have hc := ambientDegreeFastReserve_data (max k (L + 2)) D H (N + D) hh n hn hnR
    rw [P.qf_eq]
    dsimp only [q] at ⊢
    omega
  apply setting_liftA_power_data_of_predecessors P sX sZ Cc hseq hh n p q hn hhh hp hq
    (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj)
    (fun h m => ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ h m _ _ _)
  · have hd := prior hh hhh (n - 1) (by omega)
      (ambientRecurrenceRank_degree (N + D) hh n 1 (by omega) hn)
    apply hd.mono
    · have he := ambientDegreeSlowReserve_source P₀ (N + D) n 1 hnR hn
      change p + 1 ≤ _
      rw [← he]
    · have he := ambientDegreeFastReserve_cross (max k (L + 2)) D H (N + D) hh n 1 hnR hn
      change q + 1 ≤ _
      rw [← he]
      dsimp only [q]
      omega
  · intro hn₂
    have hd := prior hh hhh (n - 2) (by omega)
      (ambientRecurrenceRank_degree (N + D) hh n 2 (by omega) hn₂)
    apply hd.mono
    · have he := ambientDegreeSlowReserve_source P₀ (N + D) n 2 hnR hn₂
      change p + 2 ≤ _
      rw [← he]
    · have he := ambientDegreeFastReserve_cross (max k (L + 2)) D H (N + D) hh n 2 hnR hn₂
      change q ≤ _
      rw [← he]
      dsimp only [q]
      omega
  · intro hh0 j hj
    have hjD : j ≤ D := hj.trans (Nat.min_le_left _ _)
    have hjn : j ≤ n := hj.trans (Nat.min_le_right _ _)
    by_cases hpred : n - j ≤ N
    · have hd := prior (hh - 1) (by omega) (n - j) (by omega)
        (ambientRecurrenceRank_source (N + D) hh n j (by omega) hnR)
      exact hd.mono (ambient_source_slow_box_supported P₀ N D n j hnR hjn hpred)
        (ambient_source_fast_box_supported (max k (L + 2)) N D H hh n j
          (by omega) hhh hnR hjn hjD)
    · exact liftSequence_cutoff_scalar_power_data Q sX sZ a b P.window N H Cc hseq
        (hh - 1) (by omega) (n - j) (by omega) par lam P₀ (max k (L + 2)) (N + D)
        (max D (p + j)) (max D (q + D - j)) (by omega) CG Cw Cj
        (physicalEdgeEnvelopeMatrix π edge)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! A genuine normalized source estimate yields the full common-reserve coefficient state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftCoefficient_ambient_data_of_source
    (sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n p q : ℕ) (hnN : n ≤ N)
    (hsym : ∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
      Cc hh n m (α ∘ σ) = Cc hh n m α)
    (hi : ∀ A u v (ξ : h u) X,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
        (fun t z => normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X z)
        (fun t z => normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t X z))
    (hp : p ≤ qs) (hq : 2 ≤ q) (Bmat : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ Bmat v u)
    (Ks : (Vec 2 →L[ℝ] ℝ) → ℝ) (hKs : ∀ A, 0 ≤ Ks A)
    (hf : ∀ A u v ξ, ∀ t ∈ Icc a b, IsBoxSmooth p q
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t))
    (hft : ∀ A u v ξ, IsTransverseOn par (Icc a b)
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ))
    (hfm : ∀ A u v ξ, ∀ l : h v →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ
        (Set.projIcc a b P.window t) X z)))
    (hper : ∀ A u v ξ, ∀ t ∈ Icc a b, ∀ X, ∀ k : Fin 2 → ℤ, ∀ z,
      normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X
        (z + AVenhance.Infra.Torus.intVector k) =
          normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X z)
    (hcenter : ∀ A u v ξ, ∀ t ∈ Icc a b, ∀ X,
      fieldCellMean (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X) = 0)
    (hb : ∀ A u v ξ, ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
        (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y) z) X‖ ≤
          (Ks A * Bmat v u * ‖ξ‖) * lam ^ (n + r)) :
    AmbientLiftCoefficientData par a b P.window lam n p q (Cc hh n)
      (fun v u => finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N
        (fun A => ambientInverseUniformConstant p (metricParameterBudget p CG) (3 / 4) * Ks A) *
          Bmat v u) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hC (A) (u v) (ξ : h u) : 0 ≤ Ks A * Bmat v u * ‖ξ‖ :=
    mul_nonneg (mul_nonneg (hKs A) (hB v u)) (norm_nonneg ξ)
  have hfast (A) (u v) (ξ : h u) (j : ℕ) (hj : j ≤ q)
      (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
      ‖iteratedFDeriv ℝ j (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X) z‖ ≤
        (Ks A * Bmat v u * ‖ξ‖) * lam ^ n := by
    simpa only [norm_iteratedFDeriv_zero, Nat.add_zero] using
      hb A u v ξ 0 (Nat.zero_le p) j hj t ht X z
  have hg (A) (u v) (ξ : h u) := setting_window_inverse_clamped_transverse P q sZ hq
    (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
    (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ) (hi A u v ξ)
    (fun t ht => (hf A u v ξ t ht).mono (Nat.zero_le p) le_rfl)
    (hft A u v ξ) (hfm A u v ξ) (hper A u v ξ)
    (fun _ => (Ks A * Bmat v u * ‖ξ‖) * lam ^ n)
    (fun _ _ => mul_nonneg (hC A u v ξ) (pow_nonneg hlam.le n))
    (hfast A u v ξ)
  have hm (A) (u v) (ξ : h u) := setting_window_inverse_clamped_dual_measurable P q sZ hq
    (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
    (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ) (hi A u v ξ)
    (fun t ht => (hf A u v ξ t ht).mono (Nat.zero_le p) le_rfl)
    (hft A u v ξ) (hfm A u v ξ) (hper A u v ξ)
    (fun _ => (Ks A * Bmat v u * ‖ξ‖) * lam ^ n)
    (fun _ _ => mul_nonneg (hC A u v ξ) (pow_nonneg hlam.le n))
    (hfast A u v ξ)
  apply liftCoefficient_ambient_data_of_tests a b P.window N n p q (Cc hh n)
    hsym hnN par lam hlam Bmat hB
    (fun A => ambientInverseUniformConstant p (metricParameterBudget p CG) (3 / 4) * Ks A)
  · intro A u v ξ t ht
    exact setting_window_inverse_clamped_source_box_reserve P p q sZ n hp hq
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
      (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ) (hi A u v ξ)
      (hf A u v ξ) (hft A u v ξ)
      (hfm A u v ξ) (hper A u v ξ) (hcenter A u v ξ)
      (Ks A * Bmat v u * ‖ξ‖) (hC A u v ξ) (hb A u v ξ) t ht
  · intro A u v ξ r hr j hj t ht X z
    have hout := setting_window_inverse_clamped_source_graded_bound P p q sZ n r j hp hq hr hj
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
      (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ) (hi A u v ξ)
      (hf A u v ξ) (hft A u v ξ)
      (hfm A u v ξ) (hper A u v ξ) (hcenter A u v ξ)
      (Ks A * Bmat v u * ‖ξ‖) (hC A u v ξ) (hb A u v ξ) t ht X z
    convert hout using 1
    ring
  · exact fun A u v ξ => hg A u v ξ
  · exact fun A u v ξ => hm A u v ξ
end

/-! A genuine normalized source estimate yields the full common-reserve coefficient state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftSequence_ambient_data_of_source
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hp : p ≤ qs) (hq : 2 ≤ q) (Bmat : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ Bmat v u)
    (Ks : (Vec 2 →L[ℝ] ℝ) → ℝ) (hKs : ∀ A, 0 ≤ Ks A)
    (hf : ∀ A u v ξ, ∀ t ∈ Icc a b, IsBoxSmooth p q
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t))
    (hft : ∀ A u v ξ, IsTransverseOn par (Icc a b)
      (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ))
    (hfm : ∀ A u v ξ, ∀ l : h v →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ
        (Set.projIcc a b P.window t) X z)))
    (hper : ∀ A u v ξ, ∀ t ∈ Icc a b, ∀ X, ∀ k : Fin 2 → ℤ, ∀ z,
      normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X
        (z + AVenhance.Infra.Torus.intVector k) =
          normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X z)
    (hcenter : ∀ A u v ξ, ∀ t ∈ Icc a b, ∀ X,
      fieldCellMean (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X) = 0)
    (hb : ∀ A u v ξ, ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
        (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y) z) X‖ ≤
          (Ks A * Bmat v u * ‖ξ‖) * lam ^ (n + r)) :
    AmbientLiftCoefficientData par a b P.window lam n p q (Cc hh n)
      (fun v u => finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N
        (fun A => ambientInverseUniformConstant p (metricParameterBudget p CG) (3 / 4) * Ks A) *
          Bmat v u) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hC (A) (u v) (ξ : h u) : 0 ≤ Ks A * Bmat v u * ‖ξ‖ :=
    mul_nonneg (mul_nonneg (hKs A) (hB v u)) (norm_nonneg ξ)
  have hg (A) (u v) (ξ : h u) := liftSequence_ambient_test_geometry_of_source P
    sX sZ hsZ Cc hseq hh n q hhh hn hnN hq A u v ξ
    (fun t ht => (hf A u v ξ t ht).mono (Nat.zero_le p) le_rfl)
    (hft A u v ξ) (hfm A u v ξ) (hper A u v ξ)
    (fun _ => (Ks A * Bmat v u * ‖ξ‖) * lam ^ n)
    (fun _ _ => mul_nonneg (hC A u v ξ) (pow_nonneg hlam.le n))
    (fun j hj t ht X z => by
      simpa only [norm_iteratedFDeriv_zero, Nat.add_zero] using
        hb A u v ξ 0 (Nat.zero_le p) j hj t ht X z)
  apply liftSequence_ambient_data_of_tests Q sX sZ a b P.window N H Cc hseq
    hh n p q hhh hnN par lam hlam Bmat hB
    (fun A => ambientInverseUniformConstant p (metricParameterBudget p CG) (3 / 4) * Ks A)
  · intro A u v ξ t ht
    exact liftSequence_ambient_test_box_reserve_of_source P sX sZ hsZ Cc hseq
      hh n p q hhh hn hnN hp hq A u v ξ (hf A u v ξ) (hft A u v ξ)
      (hfm A u v ξ) (hper A u v ξ) (hcenter A u v ξ)
      (Ks A * Bmat v u * ‖ξ‖) (hC A u v ξ) (hb A u v ξ) t ht
  · intro A u v ξ r hr j hj t ht X z
    have hh := liftSequence_ambient_test_grading_of_source P sX sZ hsZ Cc hseq
      hh n p q r j hhh hn hnN hp hq hr hj A u v ξ (hf A u v ξ) (hft A u v ξ)
      (hfm A u v ξ) (hper A u v ξ) (hcenter A u v ξ)
      (Ks A * Bmat v u * ‖ξ‖) (hC A u v ξ) (hb A u v ξ) t ht X z
    convert hh using 1
    ring
  · exact fun A u v ξ => (hg A u v ξ).1
  · exact fun A u v ξ => (hg A u v ξ).2
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Only the clamped source must be measurable; arbitrary values outside the window play no role. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace] [CompleteSpace Wspace]

include P in
theorem setting_window_inverse_source_difference_bound (p q sZ δ r j : ℕ)
    (hp : p ≤ qs) (hq : 2 ≤ q) (hsZ : 1 ≤ sZ) (hsZq : sZ ≤ q) (hr : r ≤ p) (hj : j ≤ q)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (f fi c ci : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hci : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) Q.v sZ a b 0
      (fun t z => fi t X z) (fun t z => ci t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (hdf : ∀ t ∈ Icc a b, IsBoxSmooth p q (fun X z => f t X z - fi t X z))
    (hdft : IsTransverseOn par (Icc a b) (fun t X z => f t X z - fi t X z))
    (hdfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (f (Set.projIcc a b P.window t) X z - fi (Set.projIcc a b P.window t) X z)))
    (hdfper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) - fi t X (z + AVenhance.Infra.Torus.intVector n) =
        f t X z - fi t X z)
    (hdfcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (fun z => f t X z - fi t X z) = 0)
    (Cd : ℝ) (hCd : 0 ≤ Cd)
    (hdfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => f t Y y - fi t Y y) z) X‖ ≤
        (Cd * g) * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => c t Y y - ci t Y y) z) X‖ ≤
      (metricInverseUniformConstant p (metricParameterBudget p CG)
          (metricParameterBudget p CGI) (3 / 4) * C +
        ambientInverseUniformConstant p (metricParameterBudget p (identityMetricJetBudget CG)) (3 / 4) * Cd) *
        g * lam ^ (δ + r) := by
  classical
  let Pi := setting_identity_metric P
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hex (X : Vec 2) : ∃ mid : ℝ → Vec 2 → Wspace,
      IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) Q.v q a b 0
        (fun t z => f t X z) mid := by
    apply setting_window_transverse_field_inverse_exists Pi q hq f
      (fun t ht => (hf t ht).mono (Nat.zero_le _) le_rfl) hft hfm hper hcenter
      (fun _ => C * lam ^ δ)
      (fun _ _ => mul_nonneg hC (pow_nonneg hlam _)) _ X
    intro j hj t ht Y z
    simpa only [norm_iteratedFDeriv_zero, Nat.add_zero] using
      hfb 0 (Nat.zero_le p) j hj t ht Y z
  choose mid hmid using hex
  have hmid' (X : Vec 2) : IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) Q.v sZ a b 0
      (fun t z => f t X z) (mid X) :=
    cellFieldInverse_order_mono _ Q.v q sZ hsZq a b 0 (fun t z => f t X z) (mid X) (hmid X)
  exact setting_window_inverse_paired_source_bound P p q sZ δ r j hp hq hsZ hr hj
    g hg CGI hGI f fi c (fun t X z => mid X t z) ci hc hmid' hci
    hf hft hfm hper hcenter C hC hfb hdf hdft hdfm hdfper hdfcenter Cd hCd hdfb t ht X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual paired inverse sources close the quantitative coefficient difference step. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftSequence_paired_ambient_data_of_source
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hseqi : IsLiftSequence (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ :
      LiftOperatorData ι h D) sX sZ a b N H Ci)
    (hh n p q : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hp : p ≤ qs) (hq : 2 ≤ q) (hsZq : sZ ≤ q)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (M Mi Bmat Bi : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p q (Cc hh n) M)
    (datai : AmbientLiftCoefficientData par a b P.window lam n p q (Ci hh n) Mi)
    (Ks Ki Kd : (Vec 2 →L[ℝ] ℝ) → ℝ) (hKd : ∀ A, 0 ≤ Kd A)
    (source : AmbientLiftSourceData par a b P.window lam hh n p q Q Cc Ks Bmat)
    (sourcei : AmbientLiftSourceData par a b P.window lam hh n p q
      (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
      Ci Ki Bi)
    (hb : ∀ A u v ξ, ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
        (fun y => normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t Y y -
          normalizedLiftSourceField
            (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
            Ci hh n (lam • A) u v ξ t Y y) z) X‖ ≤
        (Kd A * Bmat v u * ‖ξ‖ * g) * lam ^ (n + r)) :
    AmbientLiftCoefficientData par a b P.window lam n p q
      (fun m α t X z v u => Cc hh n m α t X z v u - Ci hh n m α t X z v u)
      (fun v u => finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N
        (fun A => metricInverseUniformConstant p (metricParameterBudget p CG)
            (metricParameterBudget p CGI) (3 / 4) * Ks A +
          ambientInverseUniformConstant p (metricParameterBudget p (identityMetricJetBudget CG))
            (3 / 4) * Kd A) * (Bmat v u * g)) := by
  apply ambient_paired_coefficient_data_of_tests data datai hnN
    (by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos)
    (fun m _ => hseq.2.2.2.2.1 hh hhh n m)
    (fun m _ => hseqi.2.2.2.2.1 hh hhh n m)
    (fun v u => Bmat v u * g)
    (fun v u => mul_nonneg (source.matrix_nonneg v u) hg)
  intro A u v ξ r hr j hj t ht X z
  have geometry := ambient_paired_source_geometry source sourcei A u v ξ
  have hc (Y : Vec 2) := liftSequence_normalized_exponential_component_inverse
    Q sX sZ hsZ a b N H Cc hseq hh n hhh hn hnN (lam • A) u v ξ Y
  have hci (Y : Vec 2) := liftSequence_normalized_exponential_component_inverse
    (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
    sX sZ hsZ a b N H Ci hseqi hh n hhh hn hnN (lam • A) u v ξ Y
  have hh := setting_window_inverse_source_difference_bound P p q sZ n r j
    hp hq hsZ hsZq hr hj g hg CGI hGI
    (normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ)
    (normalizedLiftSourceField
      (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
      Ci hh n (lam • A) u v ξ)
    (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ)
    (normalizedLiftTestField (Ci hh n) n (lam • A) u v ξ)
    hc hci (source.box A u v ξ) (source.transverse A u v ξ)
    (source.measurable A u v ξ) (source.periodic A u v ξ) (source.centered A u v ξ)
    (Ks A * Bmat v u * ‖ξ‖)
    (mul_nonneg (mul_nonneg (source.constant_nonneg A) (source.matrix_nonneg v u)) (norm_nonneg ξ))
    (source.bound A u v ξ) geometry.1 geometry.2.1 geometry.2.2.1
    geometry.2.2.2.1 geometry.2.2.2.2 (Kd A * Bmat v u * ‖ξ‖)
    (mul_nonneg (mul_nonneg (hKd A) (source.matrix_nonneg v u)) (norm_nonneg ξ))
    (hb A u v ξ) t ht X z
  exact hh.trans_eq (by ring)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The proved actual centered source closes precisely the fixed scalar-power coefficient recurrence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftCoefficient_scalar_power_data_of_source
    (sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (P₀ Q₀ R hh n : ℕ) (hnR : n ≤ R) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hsym : ∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
      Cc hh n m (α ∘ σ) = Cc hh n m α)
    (hi : ∀ A u v (ξ : h u) X,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
        (fun t z => normalizedLiftSourceField Q Cc hh n (lam • A) u v ξ t X z)
        (fun t z => normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t X z))
    (hp : ambientDegreeSlowReserve P₀ R n ≤ qs)
    (hq : 2 ≤ ambientDegreeFastReserve Q₀ D H R hh n) (F : ι → ι → ℝ)
    (source : AmbientLiftSourceData par a b P.window lam hh n
      (ambientDegreeSlowReserve P₀ R n) (ambientDegreeFastReserve Q₀ D H R hh n) Q Cc
      (fun A => ambientCenteredBudget P₀ Q₀ D H R hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P₀ Q₀ D H R N h m CG Cw Cj) A)
      (finiteMatrixPower F hh)) :
    AmbientLiftCoefficientData par a b P.window lam n (ambientDegreeSlowReserve P₀ R n)
      (ambientDegreeFastReserve Q₀ D H R hh n) (Cc hh n)
      (fun v u => ambientCoefficientScalarBudget P₀ Q₀ D H R N hh n CG Cw Cj *
        finiteMatrixPower F hh v u) := by
  rw [ambientCoefficientScalarBudget_positive P₀ Q₀ D H R N hh n hnR hn hnN]
  exact liftCoefficient_ambient_data_of_source P sZ Cc hh n
    (ambientDegreeSlowReserve P₀ R n) (ambientDegreeFastReserve Q₀ D H R hh n)
    hnN hsym hi hp hq _ source.matrix_nonneg _ source.constant_nonneg
    source.box source.transverse source.measurable source.periodic source.centered source.bound
end

/-! The proved actual centered source closes precisely the fixed scalar-power coefficient recurrence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftSequence_scalar_power_data_of_source
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ Q₀ R hh n : ℕ) (hnR : n ≤ R) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hp : ambientDegreeSlowReserve P₀ R n ≤ qs)
    (hq : 2 ≤ ambientDegreeFastReserve Q₀ D H R hh n) (F : ι → ι → ℝ)
    (source : AmbientLiftSourceData par a b P.window lam hh n
      (ambientDegreeSlowReserve P₀ R n) (ambientDegreeFastReserve Q₀ D H R hh n) Q Cc
      (fun A => ambientCenteredBudget P₀ Q₀ D H R hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P₀ Q₀ D H R N h m CG Cw Cj) A)
      (finiteMatrixPower F hh)) :
    AmbientLiftCoefficientData par a b P.window lam n (ambientDegreeSlowReserve P₀ R n)
      (ambientDegreeFastReserve Q₀ D H R hh n) (Cc hh n)
      (fun v u => ambientCoefficientScalarBudget P₀ Q₀ D H R N hh n CG Cw Cj *
        finiteMatrixPower F hh v u) := by
  rw [ambientCoefficientScalarBudget_positive P₀ Q₀ D H R N hh n hnR hn hnN]
  exact liftSequence_ambient_data_of_source P sX sZ hsZ Cc hseq hh n
    (ambientDegreeSlowReserve P₀ R n) (ambientDegreeFastReserve Q₀ D H R hh n)
    hhh hn hnN hp hq _ source.matrix_nonneg _ source.constant_nonneg
    source.box source.transverse source.measurable source.periodic source.centered source.bound
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original setting closes a positive coefficient rank step from the actual earlier states. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_positive_coefficient_data_of_earlier_states
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hhh : hh ≤ H)
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientScalarPowerRecurrenceData par a b P.window lam P₀ (max k (L + 2)) (N + D) N H
        h' m CG Cw Cj Q Cc (physicalEdgeEnvelopeMatrix π edge)) :
    AmbientLiftCoefficientData par a b P.window lam n (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) (Cc hh n)
      (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N hh n CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) := by
  have hnR : n ≤ N + D := by omega
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n
  let Budget := fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m
    CG Cw Cj
  let KM := fun h m => ambientUncenteredBudget P₀ (max k (L + 2)) D H (N + D) h m CG Cw Cj Budget
  have current := setting_ambient_uncentered_data_of_earlier_coefficients P sX sZ Cc hseq
    P₀ hh n hreserve hhh hn hnR (fun h hh m hm hl => (prior h hh m hm hl).coefficient)
  have hcoef j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftCoefficientData par a b P.window lam j p q (Cc ab.1 j)
        (fun v u => Budget ab.1 j * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.1 v u) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hd := (prior ab.1 (by omega) j (by omega)
      (ambientRecurrenceRank_composition (N + D) hh n ab.1 j (by omega) hnR (by omega))).coefficient
    exact hd.mono (ambientDegreeSlowReserve_mono P₀ (N + D) n j (by omega))
      (ambientDegreeFastReserve_mono (max k (L + 2)) D H (N + D) hh ab.1 n j (by omega) (by omega))
  have hmean j (hj : j ∈ Finset.Icc 1 (n - 2)) ab
      (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      AmbientLiftUncenteredData par a b P.window lam ab.2 (n - j) (p + j) q Q Cc
        (KM ab.2 (n - j)) (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) ab.2) := by
    have hj' := Finset.mem_Icc.mp hj
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hd := (prior ab.2 (by omega) (n - j) (by omega)
      (ambientRecurrenceRank_composition (N + D) hh n ab.2 (n - j) (by omega) hnR
        (by omega))).uncentered (by omega)
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
    current hcoef hmean
  dsimp only [p, q, Budget, KM] at source
  rw [orderedCenteredScalarConstant_eq_ambientCenteredBudget P₀ (max k (L + 2)) D H (N + D)
    hh n hnR CG Cw Cj] at source
  exact setting_liftSequence_scalar_power_data_of_source P sX sZ hsZ Cc hseq P₀ (max k (L + 2))
    (N + D) hh n hnR hhh hn hnN (ambientDegreeSlowReserve_data P₀ (N + D) n qs hreserve)
    (ambientDegreeFastReserve_two (max k (L + 2)) D H (N + D) hh n (by omega)) _ source

end AVRegularity.CycleComparison.Lift
end
