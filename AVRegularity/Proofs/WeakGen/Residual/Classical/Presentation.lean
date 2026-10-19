-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Adj.MulOp
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Classical trajectories.** The classical trajectory of a field `f` is the classical Sobolev
carrier `classicalHilbertHk` of `f t` at the times of the window and `0` elsewhere.
Its time measurability is weak measurability (`aestronglyMeasurable_of_weak`): the pairing with a
smooth periodic test field is the cell integral of the jointly measurable `f`, by Fubini. -/

/-- The value of a `TorusHk` element is the zeroth ordered jet. -/
theorem weakClassical_tval_eq_torusJetOrder {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (W : TorusHk K E) :
    tval W = AVRegularity.torusJetOrder W 0 Fin.elim0 := by
  funext x
  simp [tval, AVRegularity.torusJetOrder, valueIndex2, valueIndex]

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Coarse
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Classical presentations.** The flux `Ψ` and the scalar `q` are presented by their classical
trajectories: `F` is the trajectory of `Ψ` in `TorusHk k (ℝ²)` and `g` that of `q`. The
divergence identity on the cell is an integration by parts; the cost comparison is
`classicalFactorialSq_eq_of_rep`, so the classical cost is equal to the cost of the
presentation. -/


/-- The value class of an element with a classical representative is that representative. -/
theorem weakClassical_value_ae {K r : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {W : TorusHk K E} {a : Vec 2 → E} (hr : IsClassicalRep W a r) :
    (fun x => W.toFunction.jet (valueIndex2 K) x) =ᵐ[volume.restrict AVenhance.unitCube] a := by
  have h0 := hr.2.2.2 0 (Nat.zero_le _) Fin.elim0
  show tval W =ᵐ[volume.restrict AVenhance.unitCube] a
  rw [weakClassical_tval_eq_torusJetOrder]
  simpa [orderedDerivative] using h0

end AVRegularity.Providers.WeakGen.Residual
end
