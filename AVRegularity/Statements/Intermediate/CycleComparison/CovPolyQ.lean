-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.CovOperator
public import Mathlib.Data.Nat.Factorial.Basic

/-! The inverse covariance polynomial `𝖰_p = ∑_{l=0}^p (-𝒞)^l/l!` on a classical field: the
truncated exponential `exp_p(−Hc : ∇²)` of display (4.11) of the paper, with a matrix `Hc` in place
of `Γ_m(t)`. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `𝖰_p φ = ∑_{l=0}^p ((-1)^l/l!) 𝒞^l φ`. -/
def covPolyQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (φ : Vec 2 → E) : Vec 2 → E :=
  ∑ l ∈ Finset.range (p + 1), (((-1 : ℝ) ^ l / (l.factorial : ℝ))) • (covOperator Hc)^[l] φ

end AVRegularity
