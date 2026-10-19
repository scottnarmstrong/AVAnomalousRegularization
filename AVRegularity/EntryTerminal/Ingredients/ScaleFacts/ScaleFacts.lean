-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Construction.Stream.NextAdmissible

/-! Positivity of terminal scales and monotonicity of the preparation estimates. -/

@[expose] public noncomputable section

namespace AVRegularity.EntryTerminal.Route

/-- Terminal wavelengths and renewal periods are positive, including at level zero. -/
theorem scaleFacts : ScaleFactsStatement := by
  intro X Λ hΛ
  refine ⟨fun k => (Applications.ocA_pos X.α X.q X.hq.1 Λ k hΛ).le,
    fun k => (Construction.Stream.ocTauPP_pos (α := X.α) (q := X.q) (m := k) (by omega)).le, ?_⟩
  intro D hq hbase k
  simp only [OCData.eps, hq, hbase]
  exact Construction.Stream.ocEpsilon_pos (by omega)

/-- All preparation bounds are monotone in their common constant. -/
theorem prepMonotone : PrepMonotoneStatement := by
  intro D Dm b j₀ M Kw Kh k₀ hk₀w hk₀o c C C' cr cK QT aM tp law f Gw Pterm V htime hE hCC
  constructor
  · intro hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hCC htime)), hp.2.2.2⟩
  · intro hp
    refine ⟨hp.1.trans (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _)),
      hp.2.1.trans ?_, hp.2.2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hE.le _)) (Real.sqrt_nonneg _)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hE.le _)) (Real.sqrt_nonneg _)

end AVRegularity.EntryTerminal.Route
