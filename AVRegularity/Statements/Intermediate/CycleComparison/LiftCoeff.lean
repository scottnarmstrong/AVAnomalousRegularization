-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-! A slow differential operator with fast-periodic operator coefficients on a Hilbert family, in
the symmetric ordered-word presentation `(c a)(t,X,z) = ∑_m ∑_{|α|=m} c_{m,α}(t,X,z) ∂_X^α a(X)`,
with `c_{m,α}(t,X,z) ∈ (𝗁_u → 𝗁_v)_{v,u}` (the lift operators `C_n^{(h)}` act on coarse fields
`a(𝗍,X)` by left coefficients of tested slow order `m ≤ n`). The array of word coefficients is the
Euclidean tensor of order `m`; the lift relation requires it symmetric in the word, which makes the
coefficients of a given operator unique. -/

@[expose] public section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The type of coefficient arrays: tested order `m`, word `α`, then `(t,X,z)` and the operator matrix. -/
abbrev LiftCoeff (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] : Type _ :=
  (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v

end AVRegularity
