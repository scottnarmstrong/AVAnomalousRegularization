-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.IsAnalyticEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsMolecularEnvelope

/-! The two independent envelopes, analytic and forward molecular, with one positive conjugated
edge matrix `b_{vu} = √(π_u/π_v) A_{vu}` whose two weighted Schur sums are at most `S`, both
uniform over the declared domains `dom`. The full domain quantification belongs to the envelope
hypothesis, with the domains of the proposition: for the preparation its whole cover, for the
comparison the whole later observation window, for the geometry its chart pieces and Taylor
segments. In the statements `S = C Θ_an`. The two envelopes are hypotheses of the cycle
propositions and conclusions of production. -/

@[expose] public noncomputable section

namespace AVRegularity

/-- `b ≥ 0` has both weighted sums `≤ S` and dominates the analytic envelope (reserve
`(Ks, Ls)`, constant `Ca`) and the forward molecular envelope (radius `ρ`, orders `j ≤ J`,
constants `Cm`) of `F` over `dom`. -/
structure IsEnvelope {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (b : ι → ι → ℝ) (S : ℝ) (Ca : ℝ) (Ks Ls : ℕ) (Cm : ℕ → ℝ) (J : ℕ) :
    Prop where
  nonneg : ∀ v u, 0 ≤ b v u
  row_sum : ∀ v, ∑ u, b v u ≤ S
  col_sum : ∀ u, ∑ v, b v u ≤ S
  analytic : IsAnalyticEnvelope F π dom E Ca Ks Ls b
  molecular : IsMolecularEnvelope F π K dom ν e E ρ Cm J b

end AVRegularity
