-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Prep.ModelAssembly

/-! **`RawJointAbsStatement` from the generic core**. The two statements list the same
premises in the same order; the bridge unpacks the bundle `JointPremisesAbs` field by field.

Special cases:
- `r = ρold`: both statements specialise in the same way.
- An edge-free family: the `L²` conjunct passes through unchanged.
- `m = M'`: allowed in both. -/

@[expose] public section

universe u v w x

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- The generic core gives the core at an abstract radius. -/
theorem rawJointAbs_of_gen (h : CycleJointProofs.Assembly.RawJointGenStatement.{u, v, w, x}) :
    RawJointAbsStatement.{u, v, w, x} := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, h1⟩ := h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  obtain ⟨g₀, hg₀, h2⟩ := h1 Λ hΛ
  refine ⟨g₀, hg₀, fun Pacc hPacc Mout H D Kmax hD => ?_⟩
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, hJc, hJm, h3⟩ := h2 Pacc hPacc Mout H D Kmax hD
  refine ⟨Ks, Ls, Jm, qJ, Jchart, hJc, hJm, fun Ca Cth Cb COld Crat Cm CG Cchart Cpad Cage Npad => ?_⟩
  obtain ⟨C, CP, c, mStar, hc, hC, hCP, h_fam⟩ :=
    h3 Ca Cth Cb COld Crat Cm CG Cchart Cpad Cage Npad
  refine ⟨C, CP, c, mStar, hc, hC, hCP, ?_⟩
  intro ι _ _ h' _ _ _ _ _ _ π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ P' Ctx F actual A Θ T r
    ρold hprem
  exact h_fam π hprem.hπ K hprem.hK Φ hprem.hΦ M' κ hprem.hband m hprem.hm2 hprem.hmStar
    hprem.hmM ν B hprem.hν hprem.hB hφ tS g a B₀ lam l₀ P y₀ r hprem.cov F hprem.hwmeas
    hprem.hprep actual hprem.hdepth hprem.hdesc hprem.htorus hprem.hcover hprem.hmeas A Θ
    hprem.hΘ₀ hprem.hΘ₁ hprem.henv hprem.hpointwise hprem.htrans hprem.hquiet T hprem.hTcons
    hprem.hTcov hprem.hTq ρold hprem.hρold hprem.hρR hprem.hρrat

end AVRegularity.EntryTerminal.Ingredients
