-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.LiftCellSource
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCellFieldInverse
public import AVRegularity.Statements.Intermediate.CycleComparison.IsBoxSmooth
public import AVenhance.Statements.Roots.IsZ2Periodic

/-! `Cc` is the lift sequence (the finite lift of Definition 9.5 of the paper), stated as a relation
since it is characterized by equations; its existence is `cycle_lift_exists`, and its uniqueness is
that of the cell inverse. `Cc hh n` are the coefficient arrays of the grade-`hh` cell-degree-`n`
lifts `C_n^{(hh)}`, `0 ≤ hh ≤ H`, `0 ≤ n`; the recursion:

* `C_0 = I`, i.e. `C_0^{(0)} = I` and `C_0^{(hh)} = 0` for `hh > 0`; `C_n = 0` for `n > N`;
* each `C_n^{(hh)}`, `1 ≤ n ≤ N`, has tested slow order at most `n`, is a symmetric word array of
  smooth `ℤ²`-periodic coefficients;
* for every smooth coarse test field `a` and slow position `X`, the field `C_n^{(hh)} a(·,X,·)` is
  the finite-past, mean-zero, zero-start bounded cell inverse (`IsCellFieldInverse`, built on
  `IsCellSolution`) of the centered source
  `-Q_0 A_n^{(hh)} a + ∑_{j=1}^{n-2} (C_j L_{n-j})^{(hh)} a`; the inverse acts on the left
  coefficients, which is the action on a time-independent test field (the coefficient `∂_𝗍` is the
  cell time derivative).

The test fields are time-independent and smooth; the operators act pointwise in time, so the
relation determines the coefficient arrays. The mean operators `L_n^{(hh)} = P_0 A_n^{(hh)}` are
not stored: they are `liftMean`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `Cc` is the lift sequence (grades `0..H`, degrees up to `N`) of the operator data `Q` on `[t₀,t₁]`. -/
def IsLiftSequence {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}
    (Q : LiftOperatorData ι h D) (sX sZ : ℕ) (t₀ t₁ : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h) : Prop :=
  (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X z,
    liftApply 0 (Cc 0 0) (fun _ => a₀) t X z = a₀ X) ∧
  (∀ hh, 1 ≤ hh → hh ≤ H → ∀ m α t X z v u, Cc hh 0 m α t X z v u = 0) ∧
  (∀ hh, hh ≤ H → ∀ n, N < n → ∀ m α t X z v u, Cc hh n m α t X z v u = 0) ∧
  (∀ hh, hh ≤ H → ∀ n m, n < m → ∀ α t X z v u, Cc hh n m α t X z v u = 0) ∧
  (∀ hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)),
    Cc hh n m (α ∘ σ) = Cc hh n m α) ∧
  (∀ hh, hh ≤ H → ∀ n m α v u, ∀ t ∈ Set.Icc t₀ t₁,
    IsBoxSmooth sX sZ (fun X z => Cc hh n m α t X z v u) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u)) ∧
  (∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
    ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ t₀ t₁ (fun _ => 0)
      (fun t z => liftCellSource Q Cc (fun _ => a₀) hh n t X z)
      (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z))

end AVRegularity
