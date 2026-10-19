-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.Families.PhysicalCoefficient
public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders

/-! The coupling coefficient of the actual equation, in the shape of the coupled energy estimate
`coupled_energy_torus`, built from the charted family. The coefficient `A_{ii',d}` of
`coupled_energy_torus` is the `physicalCoefficient` of the order-`d` part of the edge `i' → i`: the
sum over the pieces, with the prescribed time partition and the actual contexts, of the exact Piola
transports of the diagonal samples `ν e^{d-2} a♭(t, y/E, y/e)`; orders `d ∈ [2,D]` with
`K_i + d ≤ K_{i'} + 2` (`admissibleOrders`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `A_{ii',d}(t,x) = physicalCoefficient F ν e E actual i i' d t x`: the coupling coefficient, in
the form of `coupled_energy_torus`, of the sources `𝒮_{ii'}` of the charted family `F`. -/
def edgeCoefficient {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (i i' : ι) (d : admissibleOrders K D i i') :
    ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h i)) :=
  physicalCoefficient F ν e E actual i i' d.1

end AVRegularity
