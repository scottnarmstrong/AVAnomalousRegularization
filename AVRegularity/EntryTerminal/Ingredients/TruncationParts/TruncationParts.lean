-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.Truncation.Truncation
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients

/-! **Truncation of the internal order** (`truncationParts : TruncationPartsStatement`).
- The preparation and family truncations are the proved `terminalPrepTruncation` and
  `terminalFamilyTruncation`. The truncated map `famTrunc h ∘ₗ P` is
  `terminalTruncateMap`.
- Monotonicity of the retained certificate in the order is proved here. The Schur and
  regularizer clauses are for every order `≤ K`; the coefficient clauses use `ContDiff.of_le` and
  `coefficientSeminorm_order_mono`.

Special cases:
- `K = K₃`: identity truncation.
- An empty retained family: the certificate is about no identities.
- `K = 0`: only order-zero coefficient bounds remain. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- **The preparation truncation** from `terminalPrepTruncation`. -/
theorem prepTrunc : PrepTruncStatement := by
  intro D Dm b j₀ M Kw K K₃ k₀ hKK hk₀w hk₀o c C cr cK QT aM tp law f Gw hmass P₃ V
  exact terminalPrepTruncation Gw M Kw K K₃ k₀ hKK hk₀w hk₀o c C cr cK QT aM tp law hmass f P₃ V

/-- **The family truncation** from `terminalFamilyTruncation`. -/
theorem familyTrunc : FamilyTruncStatement := by
  intro D Dm b j₀ Pt seedKt freshKt φ₀ hφ₀ lawW lawT rootM M K K₃ hKK cr C Centry tp sn tf f Gw Gt
    hmass Ds seed ι g₃ Z₃ h
  exact terminalFamilyTruncation Gw Gt seed ι Pt seedKt freshKt φ₀ hφ₀ lawW lawT hmass rootM M K K₃
    hKK cr C Centry tp sn tf f g₃ Z₃ h

/-- **Monotonicity**, the retained certificate at a smaller order. -/
theorem retainedTrunc : RetainedTruncStatement := by
  intro D Dm b j₀ lawT Pt seedKt freshKt φ₀ hφ₀ cker M K K₃ hKK cr tp tf Gt hR
  refine ⟨fun kk hkk => hR.1 kk (hkk.trans hKK),
    fun v u γ ϱ hϱ kk hkk => hR.2.1 v u γ ϱ hϱ kk (hkk.trans hKK), fun v u γ d => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hR.2.2 v u γ d
  exact ⟨h1, fun t ht => (h2 t ht).of_le (by exact_mod_cast hKK), h3,
    ne_top_of_le_ne_top h4
      (Construction.Preservation.FullLift.coefficientSeminorm_order_mono _ hKK _ _ _)⟩

/-- **Truncation of the internal order.** -/
theorem truncationParts : TruncationPartsStatement :=
  ⟨prepTrunc, familyTrunc, retainedTrunc⟩

end AVRegularity.EntryTerminal.Ingredients
