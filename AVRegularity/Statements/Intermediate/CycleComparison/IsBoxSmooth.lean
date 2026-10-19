-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Box (mixed) regularity of a field `f(X,z)` of the independent slow variable `X` and fast
variable `z`: `f(X,·)` is `C^{sZ}`, each fast jet of order `b ≤ sZ` is `C^{sX}` in `X`, and the
mixed jets are jointly continuous. This is the regularity the reserved jets of the statements use
(slow parameter maps `C^{sX}` into spaces carrying fast jets up to order `sZ`; `jetSup` takes the
`z`-jet first and then the `X`-derivative), not a total order: the pure slow derivatives are of
order `sX` only and the pure fast ones of order `sZ` only. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `f X` is `C^{sZ}`; for each `b ≤ sZ` and `z`, `X ↦ D_z^b f(X,z)` is `C^{sX}`; and the mixed jets
`D_X^a D_z^b f` are jointly continuous for `a ≤ sX`, `b ≤ sZ`. -/
def IsBoxSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (sX sZ : ℕ)
    (f : Vec 2 → Vec 2 → E) : Prop :=
  (∀ X, ContDiff ℝ (sZ : ℕ∞) (f X)) ∧
  (∀ b, b ≤ sZ → ∀ z, ContDiff ℝ (sX : ℕ∞) (fun X => iteratedFDeriv ℝ b (f X) z)) ∧
  ∀ a b, a ≤ sX → b ≤ sZ →
    Continuous (fun p : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b (f X') p.2) p.1)

end AVRegularity
