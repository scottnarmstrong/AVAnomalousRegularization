-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CycleJoint.JointOperator
public import AVRegularity.Statements.Intermediate.CycleJoint.HasEdgePath
public import AVRegularity.Statements.Intermediate.CycleJoint.TorusHkNorm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
public import AVRegularity.Statements.Intermediate.Families.ChartedFamily

/-! The model clause of the joint preparation `cycle_joint` (Proposition 11.7 of the paper follows
from `cycle_joint` by a comparison of norms): the operator
`P = P_diag I + ∑_{h=1}^H P^{(h)}` (`jointOperator`) is linear (the blocks are linear maps) and
triangular (the degree-`h` block `P^{(h)}_{vu}` vanishes unless there is a path of `h` edges from `u`
to `v`, `HasEdgePath`), fixes every constant component vector, and, on arbitrary `L²` vectors,
`‖P_diag‖_{2→2} ≤ 1 + C_P E^P`, `|P_diag f|_{cR,M_out} ≤ C‖f‖₂`,
`‖P^{(h)}_{vu}‖_{L²→H_{cR,M_out}} ≤ C (A^h)_{vu}`, `‖P‖_{2→2} ≤ 1 + C_P E^P + CΘ_an`
(`‖·‖_{2→2}` on `L²(𝕋²; 𝗁_π)` is with the mass-weighted norm `∑_v π_v⁻¹‖f_v‖²`).

Representation: the blocks act on `TorusHk 0` (`L²`) and land in `TorusHk (max M_out K_v)`: the
model bound is at order `M_out`, the physical slot `K_v` is needed for the error clause (the model
supplies enhanced derivatives through order at least `max(M_out, K_*)`). `P_diag` is represented by
its blocks `Pd v` on each component, with the same bounds (that all blocks are the same scalar
operator is not stated). The radius `ρm = cR`, the scale `E = ε_{m-1}`, the accuracy `P` and the
constants are arguments. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The model clause of the joint preparation for the blocks `Pd`, `Pg`. -/
def IsJointModel {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*} (π : ι → ℝ) (K : ι → ℕ) (Mout H : ℕ)
    (F : ChartedFamily ι h D P Ctx) (A : Matrix ι ι ℝ) (Θ E Pacc ρm C CP : ℝ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)) : Prop :=
  (∀ h', 1 ≤ h' → h' ≤ H → ∀ v u, ¬ HasEdgePath F h' u v → Pg h' v u = 0) ∧
  (∀ v f, torusHkNorm 1 (Nat.zero_le _) (Pd v f) ≤
    (1 + CP * E ^ Pacc) * torusHkNorm 1 (le_refl 0) f) ∧
  (∀ v f, torusHkNorm ρm (le_max_left Mout (K v)) (Pd v f) ≤ C * torusHkNorm 1 (le_refl 0) f) ∧
  (∀ h', 1 ≤ h' → h' ≤ H → ∀ v u f, torusHkNorm ρm (le_max_left Mout (K v)) (Pg h' v u f) ≤
    C * (A ^ h') v u * torusHkNorm 1 (le_refl 0) f) ∧
  (∀ f : ∀ u, TorusHk 0 (h u),
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.zero_le _) (jointOperator K Mout H Pd Pg f v)).val)) ≤
      (1 + CP * E ^ Pacc + C * Θ) *
        Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun v => (f v).val))) ∧
  ∀ (f : ∀ u, TorusHk 0 (h u)) (c : ∀ v, h v),
    (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => c v) →
    ∀ v, (jointOperator K Mout H Pd Pg f v).toFunction.jet (valueIndex2 (max Mout (K v)))
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => c v

end AVRegularity
