-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleEvolution.CellWeakIdentity
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellValue
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellGradComp
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellGradient
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellL2Norm
public import AVRegularity.Sobolev

/-! Energy solutions of the cell/fibre equation on a time interval: continuous `L²` energy
fields, whose history and original initial state are part of the data. The predicate has the
shape of `IsCoupledWeakSolutionTorus`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology

namespace AVRegularity

/-- `D` is an energy solution on the interval `I` of the cell/fibre equation with coefficients
`C`, scalar source `src` and vector source `F`: `I` is an interval; for almost every `t ∈ I` the raw
jet `D t` is a periodic order-one weak jet (so `D t` represents an `H¹(𝕋²;ℂ)` function and its
weak gradient), and for every `t ∈ I` the value `c(t)` is periodic and in `L²(𝕋²)`; the
representatives are jointly measurable; `t ↦ c(t)` is continuous into `L²(𝕋²)` on `I` (the
continuous energy trace); `∇c ∈ L²_loc(I; L²)`; and `CellWeakIdentity` holds for all
`s ≤ t` in `I` against every `H¹` test. Initial states are not imposed here; they are imposed
by the statements that use the predicate. -/
def IsCellSolution (I : Set ℝ) (C : CellCoefficients) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (D : ℝ → RawJet2 1 ℂ) : Prop :=
  I.OrdConnected ∧
  (∀ᵐ t ∂(volume.restrict I), HasPeriodicOrderedWeakJet (D t)) ∧
  (∀ t ∈ I, MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube) ∧
    AVenhance.IsZ2Periodic (cellValue D t)) ∧
  (∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
    ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) ∧
  (∀ t₀ ∈ I, Tendsto (fun t => ∫⁻ x in AVenhance.unitCube,
      ‖cellValue D t x - cellValue D t₀ x‖ₑ ^ 2) (𝓝[I] t₀) (𝓝 0)) ∧
  (∀ a ∈ I, ∀ b ∈ I, ∫⁻ τ in Set.Icc a b, cellL2Norm (cellGradient (D τ)) ^ 2 < ⊤) ∧
  ∀ s ∈ I, ∀ t ∈ I, s ≤ t → ∀ ψ : TorusHkFunction 1 ℂ,
    CellWeakIdentity C s t (cellValue D s) (cellValue D t) (ψ.jet (valueIndex2 1))
      (fun k => ψ.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) (cellValue D)
      (fun τ k => cellGradComp (D τ) k) src F

end AVRegularity
