-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative
public import AVRegularity.Statements.Intermediate.CycleComparison.TorusJetOrder
public import AVenhance.Statements.Roots.IsZ2Periodic

/-! A classical `C^r` periodic function is the (continuous) representative of a Sobolev field
through order `r` (`r ≤ K`): the retained field of the coarse family has finite regularity
`H^{k+1+D}`, so by the two-dimensional Sobolev embedding it has a classical representative with
`r = k + D - 1` derivatives, on which the lift (a differential operator) acts classically. The
ordered weak jet of order `m ≤ r` of `W` is a.e. the classical `orderedDerivative` of `a`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `a` is `C^r`, `ℤ²`-periodic and its classical ordered derivatives of orders `m ≤ r` are
a.e. the weak jets of `W`. -/
def IsClassicalRep {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (W : TorusHk K E) (a : Vec 2 → E)
    (r : ℕ) : Prop :=
  r ≤ K ∧ ContDiff ℝ r a ∧ AVenhance.IsZ2Periodic a ∧
    ∀ m ≤ r, ∀ w : DerivativeWord2 m,
      torusJetOrder W m w =ᵐ[volume.restrict AVenhance.unitCube] fun x => orderedDerivative w a x

end AVRegularity
