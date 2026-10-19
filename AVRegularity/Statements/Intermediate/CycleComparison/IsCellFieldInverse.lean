-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleEvolution.IsCellSolution
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellEnergyNorm
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellMean
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellCoefficients
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellValue
public import AVRegularity.Statements.Intermediate.CycleComparison.CellJetOfField

/-! The finite-past, mean-zero cell inverse with initial state `c₀` of the centered source `g`
(Lemma 9.4 of the paper), for classical fields with values in a finite-dimensional real space `E`
(operator coefficients of the lift; the inverse acts on left coefficients), keeping the initial
state. It reuses the cell-evolution relation `IsCellSolution`: every real linear functional
`ℓ : E → ℝ` of the field gives a complex cell trajectory (value and weak gradient jets,
`cellJetOfField`) that is an `IsCellSolution` on the window with the coefficients `⟨G, v, 0, 0⟩`,
source `ℓ g`, no vector source, mean zero, initial value `ℓ c₀` (a.e.), and finite `cellEnergyNorm`;
this is the coordinatewise action of the scalar inverse on the finite dimensional `E`. The field is
`C^r` in `z` (finite order `sZ`) so that the jets are classical derivatives. The lift uses `c₀ = 0`.
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

/-- `c` is the finite-past mean-zero cell inverse on `[t₀,t₁]` of `g` with initial state `c₀`,
for the metric `G` and the drift `v`, coordinatewise through the cell-evolution relation
`IsCellSolution`. -/
def IsCellFieldInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (t₀ t₁ : ℝ) (c₀ : Vec 2 → E) (g c : ℝ → Vec 2 → E) : Prop :=
  (∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (sZ : ℕ∞) (c t)) ∧
  ∀ ℓ : E →L[ℝ] ℝ,
    IsCellSolution (Set.Icc t₀ t₁) ⟨fun t _ => G t, v, 0, 0⟩ (fun t x => ((ℓ (g t x) : ℝ) : ℂ))
        (fun _ _ => 0) (cellJetOfField ℓ c) ∧
      (∀ t ∈ Set.Icc t₀ t₁, cellMean (cellValue (cellJetOfField ℓ c) t) = 0) ∧
      cellValue (cellJetOfField ℓ c) t₀ =ᵐ[volume.restrict AVenhance.unitCube]
        (fun x => ((ℓ (c₀ x) : ℝ) : ℂ)) ∧
      cellEnergyNorm (Set.Icc t₀ t₁) (cellJetOfField ℓ c) < ⊤

end AVRegularity
