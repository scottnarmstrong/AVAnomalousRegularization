-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CycleJoint.JointOperator
public import AVRegularity.Statements.Intermediate.CycleJoint.TorusHkNorm
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq

/-! The error clause of the joint preparation `cycle_joint`: for prepared data
`|f_v|_{ρ_old,K_v} ≤ F_v` the actual family `u` (the solution of
`(∂_t + 𝐛_m·∇ - νΔ)u_v = ∑_{u→v} 𝒮_{vu}u_u`, `u_v(s) = f_v`, i.e. the solution class
`IsCoupledWeakSolutionTorus` on `[tS, tp]` with the coefficients `A` of the edges, no forcing)
satisfies `(∑_v π_v⁻¹ |u_v(t_p) - (Pf)_v|²_{ρ_*,K_v})^{1/2} ≤ C_P E^P F_π`, `F_π² = ∑_v π_v⁻¹ F_v²`.
The model `P` is applied to the `L²` class of the datum (`truncateTorusHk`), and its component `v`
is read at the slot `K_v` (`max M_out K_v ≥ K_v`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The error clause for the solution class with drift `b`, viscosity `ν`, coefficients `A`, start
`tS` and end `tp`. -/
def IsJointError {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (π : ι → ℝ) (K : ι → ℕ) (Mout H D : ℕ) (ν tS tp ρs ρold E Pacc CP : ℝ)
    (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)) : Prop :=
  ∀ (f : ∀ v, TorusHk (K v) (h v)) (Fv : ι → ℝ),
    (∀ v, torusHkNorm ρold (le_refl (K v)) (f v) ≤ Fv v) →
    ∀ (u : ∀ v, ℝ → TorusHk (K v) (h v)) (w : ∀ v, ℝ → TorusHk (K v + 1) (h v)),
      IsCoupledWeakSolutionTorus ν tS tp b D K A f (fun _ _ => 0) (fun _ _ => 0) u w →
      Real.sqrt (massNormSq (E := h) (K := K) ρs π
          (fun v => (u v tp - truncateTorusHk (le_max_right Mout (K v))
            (jointOperator K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v)).val)) ≤
        CP * E ^ Pacc * Real.sqrt (∑ v, (π v)⁻¹ * Fv v ^ 2)

end AVRegularity
