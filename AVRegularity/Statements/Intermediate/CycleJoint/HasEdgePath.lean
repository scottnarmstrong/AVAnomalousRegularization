-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamily

/-! A directed path of exactly `n` edges `u = p_0 → p_1 → ⋯ → p_n = v` of the source graph of
a family. The source-degree-`h` part `P^{(h)}` of the triangular preparation operator follows a
path of `h` edges, and `P^{(h)}_{vu}` is majorized by `(A^h)_{vu}`; in the comparison, source
degree `r` follows an original path of length `r`. An edge `u → v` is a nonempty set `Γ v u` of
constituent identities. For `n = 0` this is `u = v`. -/

@[expose] public section

namespace AVRegularity

/-- There is a path of `n` edges from `u` to `v` in the graph of the family `F`. -/
def HasEdgePath {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (n : ℕ) (u v : ι) : Prop :=
  ∃ p : Fin (n + 1) → ι, p 0 = u ∧ p (Fin.last n) = v ∧
    ∀ k : Fin n, Nonempty (F.Γ (p k.succ) (p k.castSucc))

end AVRegularity
