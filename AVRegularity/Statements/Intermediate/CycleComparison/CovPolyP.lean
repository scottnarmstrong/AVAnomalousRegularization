-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.CovOperator
public import Mathlib.Data.Nat.Factorial.Basic

/-! The covariance polynomial `𝖯_p = ∑_{l=0}^p 𝒞^l/l!` on a classical field. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `𝖯_p φ = ∑_{l=0}^p (1/l!) 𝒞^l φ`, with `𝒞^l` the `l`-fold iterate of `covOperator Hc`. -/
def covPolyP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (φ : Vec 2 → E) : Vec 2 → E :=
  ∑ l ∈ Finset.range (p + 1), ((l.factorial : ℝ)⁻¹) • (covOperator Hc)^[l] φ

end AVRegularity
