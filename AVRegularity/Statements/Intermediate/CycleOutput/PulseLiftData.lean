-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.LiftEdges
public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseCellDrift
public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseChartIndex
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftOperatorData
public import AVRegularity.Statements.Intermediate.CycleReference.OcMaterialMetric

/-! The operator data of the lift of the pulse `k` (`LiftOperatorData`), in the renewal chart
`l = ocPulseChartIndex k` of the background velocity `𝐛_{m-1}`: the contrast `η = ν/B`; the metric
`G(𝗍, X) = G_l(ℓ²𝗍, ρX)` (the material metric of the chart, `ocMaterialMetric`, in the lift slow
variable `X = y/ρ`); the drift `v = v_k` of the single pulse (`ocPulseCellDrift`, the shear of
display (9.1) of the paper); the source edges in the lift variables (`liftEdges (ℓ²) (ρ/E)`). -/

@[expose] public noncomputable section

open Homogenization AVenhance

namespace AVRegularity

/-- The operator data `(η, G, v, edge)` of the lift of the pulse `k` of level `m`. -/
def pulseLiftData {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (ν B ρ lam : ℝ) (k : ℤ)
    (edge : ConstituentEdges D h) : LiftOperatorData ι h D where
  η := ν / B
  G := fun s X i j => ocMaterialMetric α q Λ m φ hφ (ocPulseChartIndex α q Λ m k)
    (ocEll q Λ m ν ^ 2 * s) (ρ • X) i j
  v := ocPulseCellDrift α q Λ ζ m ν k
  edge := liftEdges (ocEll q Λ m ν ^ 2) lam edge

end AVRegularity
