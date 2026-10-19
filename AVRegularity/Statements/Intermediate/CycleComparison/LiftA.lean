-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.LiftApply
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftOperatorData
public import AVRegularity.Statements.Intermediate.CycleComparison.CellB1
public import AVRegularity.Statements.Intermediate.CycleComparison.CellB2
public import AVRegularity.Statements.Intermediate.CycleComparison.SourceCoeff

/-! The recursion source of the lift of grade `hh` and cell degree `n`,
`A_n^{(hh)} = ℬ_1 C_{n-1}^{(hh)} + ℬ_2 C_{n-2}^{(hh)} - ∑_{j=0}^D 𝒮_j C_{n-j}^{(hh-1)}` applied to a
coarse field, built from the parts `ℬ_1`, `ℬ_2`, `𝒮_j` of the operator of display (9.13) of the
paper. With `C_0 = I` and negative indices zero, the lifts are constructed in increasing source
degree, then cell degree; the term `𝒮_0 C_n` uses the preceding source degree. Source degree `hh`
counts source-coefficient factors along a path, so the source terms feed the previous grade `hh - 1`
(none at `hh = 0`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(A_n^{(hh)} a)(t,X,z)` for `n ≥ 1`, from the coefficient arrays `Cc hh' n'` of the lifts
`C_{n'}^{(hh')}`. -/
def liftA {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) :
    Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z =>
    cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) a t) X z
      + (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) a t) X z else 0)
      - (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
          sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) a t) X z)

end AVRegularity
