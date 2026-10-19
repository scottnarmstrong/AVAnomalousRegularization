-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ConstituentEdges

/-! The source edges in the variables of the lift (`IsLiftSetting`): cell time `𝗍` with physical
time `t = ℓ²𝗍` (`c = ℓ²`) and the lift slow variable `X = y/ρ`, in which the normalized slow
variable of the families, `x/E`, is `λ_s X`, `λ_s = ρ/E`. Every constituent keeps its constant map
and positive record; only its scalar coefficients are reparametrised,
`a'(𝗍, X, z) = a(c𝗍, λ_s X, z)` (`a(X) = a'(λ_s X)`; the retained histories and phases of the family
are identified with the lift variables). -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- The edge family with coefficients `a'(𝗍,X,z) = a(c𝗍, lam • X, z)`. -/
def liftEdges {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (c lam : ℝ) (edge : ConstituentEdges D h) :
    ConstituentEdges D h :=
  fun v u d => (edge v u d).map fun γ =>
    { γ with
      coeff := fun α t X z => γ.coeff α (c * t) (lam • X) z
      periodic := fun α t X => γ.periodic α (c * t) (lam • X) }

end AVRegularity
