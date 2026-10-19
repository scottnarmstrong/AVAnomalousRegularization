-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Readout.OperatorMap
public import AVRegularity.Statements.Intermediate.Readout.HolderNorm
public import AVRegularity.Statements.Intermediate.Readout.IsRepresentationAt
public import AVRegularity.Statements.Intermediate.Readout.RepresentationMap
public import AVRegularity.Statements.Intermediate.Readout.RepresentationValue
public import AVRegularity.Statements.Intermediate.Readout.RepresentedSize
import AVRegularity.Readout.RepresentationEstimates

/-! Proof of the readout lemma `iteration_readout` (Lemma 13.2(a) of the paper). -/

@[expose] public section

open Homogenization
open scoped ENNReal

namespace AVRegularity.Providers

theorem iteration_readout (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) (K : ℕ) (hK : 1 ≤ K)
    {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H'] :
    (∀ e E : ℝ, 0 < e → e ≤ E → E ≤ 1 → ∀ F : Vec 2 → H,
      profileSeminorm e K s F ≤
        ENNReal.ofReal ((e / E) ^ (1 - s)) * profileSeminorm E K s F) ∧
    (∀ (e : ℝ) (r : Representation H), IsRepresentationAt e K r →
      supNorm r.value + profileSeminorm e K s r.value ≤ representedSize s K e r ∧
      holderNorm s r.value ≤ 3 * representedSize s K e r) ∧
    (∀ (e : ℝ) (r : Representation H) (R : H →L[ℝ] H'), IsRepresentationAt e K r →
      IsRepresentationAt e K (r.map R) ∧ (r.map R).value = (fun x => R (r.value x)) ∧
      representedSize s K e (r.map R) ≤ ENNReal.ofReal ‖R‖ * representedSize s K e r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e E he heE hE F
    exact Readout.profileSeminorm_scale_le he heE hs₁ F
  · intro e r hr
    exact ⟨Readout.representation_profile_readout hs₀ hs₁ r hr,
      Readout.representation_holder_readout hs₀ hs₁ hK r hr⟩
  · intro e r R hr
    exact ⟨Readout.representation_map_isRepresentationAt r R hr,
      Readout.representation_map_value r R,
      Readout.representedSize_map_le r R hr⟩

end AVRegularity.Providers
