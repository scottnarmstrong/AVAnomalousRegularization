-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.FastProfile.Integral
public import AVRegularity.Statements.Construction.IsFastProfile

/-! Existence of a fast profile.

This constructs the smooth partition profile in the helper modules and proves every
clause of the `IsFastProfile` definition. -/

@[expose] public section

namespace AVRegularity.Providers

theorem exists_isFastProfile : ∃ ζ : ℝ → ℝ, AVRegularity.IsFastProfile ζ := by
  refine ⟨AVRegularity.FastProfile.fastProfile, ?_⟩
  exact ⟨AVRegularity.FastProfile.contDiff_fastProfile,
    AVRegularity.FastProfile.fastProfile_even,
    AVRegularity.FastProfile.tsupport_fastProfile_subset,
    (fun t => ⟨AVRegularity.FastProfile.fastProfile_nonneg t,
      AVRegularity.FastProfile.fastProfile_le_one t⟩),
    AVRegularity.FastProfile.fastProfile_periodization,
    AVRegularity.FastProfile.fastProfile_integral_sq⟩

end AVRegularity.Providers
