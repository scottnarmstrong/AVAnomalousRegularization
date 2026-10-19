-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.LiftMean

/-! The centered source of the cell inverse in the lift recursion,
`-Q_0 A_n^{(hh)} + ∑_{j=1}^{n-2} (C_j L_{n-j})^{(hh)}` with the graded product
`(C_j L_{n-j})^{(hh)} = ∑_{hh'+hh''=hh} C_j^{(hh')} L_{n-j}^{(hh'')}`, so that
`𝐂_n = 𝒦_G[-Q_0𝐀_n + ∑_{j=1}^{n-2} 𝐂_j 𝐋_{n-j}]`, products in their order (the cell sources of the
finite lift, Definition 9.5 of the paper). `Q_0 = I - P_0`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(-(A_n^{(hh)} - L_n^{(hh)}) a + ∑_{j=1}^{n-2} ∑_{hh'+hh''=hh} C_j^{(hh')}(L_{n-j}^{(hh'')} a))(t,X,z)`. -/
def liftCellSource {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) :
    Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z =>
    -(liftA Q Cc a hh n t X z - liftMean Q Cc a hh n t X)
      + ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.antidiagonal hh,
          liftApply j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) t X z

end AVRegularity
