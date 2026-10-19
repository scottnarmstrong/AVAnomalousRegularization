-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.LiftA
public import AVRegularity.Statements.Intermediate.CycleComparison.FieldCellMean

/-! The mean operator of the lift of grade `hh` and degree `n`, `L_n^{(hh)} = P_0 A_n^{(hh)}`,
applied to a coarse field (the means of the finite lift, Definition 9.5 of the paper; defined
through degree `N + D`). It is a cell-independent field. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(L_n^{(hh)} a)(t,X) = ∫_{𝕋²} (A_n^{(hh)} a)(t,X,z) dz`. -/
def liftMean {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) :
    ℝ → Vec 2 → ∀ i, h i :=
  fun t X => fieldCellMean (fun z => liftA Q Cc a hh n t X z)

end AVRegularity
