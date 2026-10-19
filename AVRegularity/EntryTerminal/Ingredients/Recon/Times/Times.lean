-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.EntryTerminal.Ingredients.Deadline.Deadline

/-! **Entrance and the deadline.** The entrance `a_M + τ'_M ≤ t_p` from the
preparation's `a_M + c_P τ''_M ≤ t_p` (`entrance_of_prep_eventually`), the deadline `t_p < a + T₀`
from the composition deadline `deadline` (applied with the context's data, the weak start
`a_M ≤ a + 6 J_w τ''_{M+1}` and the preparation's `t_p ≤ a_M + C_P τ''_M`).

Special cases:
- `c_P ≥ 1`: the entrance needs no threshold.
- the deadline is the composition `t_p + h + 3τ + 4τ'' ≤ a + T₀` with every summand nonnegative. -/

@[expose] public section

open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- **Entrance and deadline.** -/
theorem termReconTimes : TermReconTimesStatement := by
  intro X
  obtain ⟨Λd, hΛd, hd⟩ := deadline X
  refine ⟨Λd, hΛd, fun A hΛ hV _ => ?_⟩
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker hcP
  obtain ⟨M₂, hM₂⟩ := hd A hΛ hV CP
  have hδ : 0 < ocDelta X.α X.q :=
    (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  obtain ⟨M₁, hM₁⟩ := entrance_of_prep_eventually (α := X.α) (q := X.q) (Λ := A.Λ) X.hq.1
    (le_trans hΛd hΛ) hδ hcP
  refine ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨max M₁ M₂, fun M hM c x => ?_⟩⟩
  obtain ⟨h1, h2, h3, -⟩ := c.data
  have hP := c.prep
  have hW := c.weak
  have hdl := hM₂ M (le_trans (le_max_right _ _) hM) c.D c.data c.a c.aM c.tp hW.2.1
    (by simpa [OCData.termH] using hP.2.2.1)
  have hpos : 0 < c.D.termH M := by
    simp only [OCData.termH]
    exact Construction.Stream.ocTauPP_pos (le_trans (by norm_num) (h3 ▸ le_trans le_rfl
      (by omega : 1 ≤ A.Λ)))
  have hτ : 0 ≤ ocTau X.α X.q A.Λ (M - 1) := (Construction.Stream.ocTau_pos (by omega)).le
  have hτ2 : 0 < ocTauPP X.α X.q A.Λ (M - 1) :=
    Construction.Stream.ocTauPP_pos (by omega)
  refine ⟨?_, by linarith⟩
  have := hM₁ M (le_trans (le_max_left _ _) hM) c.aM c.tp
    (by simpa [OCData.termH, h1, h2, h3] using hP.2.1)
  simpa [h1, h2, h3] using this

end AVRegularity.EntryTerminal.Ingredients.Recon
