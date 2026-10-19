-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Intermediate.Readout.ReadoutLemma
public import Homogenization.Ambient.Basic
public import AVRegularity.Statements.Intermediate.Readout.PartialDerivative
public import AVRegularity.Statements.Intermediate.Readout.SupNorm
public import AVRegularity.Statements.Intermediate.Readout.HolderSeminorm
public import AVRegularity.Statements.Intermediate.Readout.HolderNorm
public import AVRegularity.Statements.Intermediate.Readout.ProfileSeminorm
public import AVRegularity.Statements.Intermediate.Readout.ProfileNorm
public import AVRegularity.Statements.Intermediate.Readout.Representation
public import AVRegularity.Statements.Intermediate.Readout.RepresentationValue
public import AVRegularity.Statements.Intermediate.Readout.IsRepresentationAt
public import AVRegularity.Statements.Intermediate.Readout.RepresentationMap
public import AVRegularity.Statements.Intermediate.Readout.RepresentedSize

/-! Reading a representation: Lemma 13.2(a) of the paper, with the size of display (4.13), and the
case of a constant map in Lemma 13.2(b). -/

@[expose] public section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- **Reading a representation** (Lemma 13.2(a) of the paper, with the size of display (4.13)),
for the standing Hölder exponent `s`, of which only `0 < s < 1` is used (the global range is
`0 < s < (1-α)/2`), and a derivative order `K ≥ 1`, on fields on `𝕋²` with values in an arbitrary
normed space `H` (the component space `𝗁_π`); the constants `1`, `3` and `‖R‖` do not depend on `H`.
(1) `[F]_{e,K;s} ≤ (e/E)^{1-s} [F]_{E,K;s}` for `0 < e ≤ E` (`E ≤ 1` is the domain of the profile
norm). (2) For every representation at wavelength `e`, with `U = F + ∑_l G_l`:
`‖U‖_∞ + [U]_{e,K;s} ≤ X_e(U;K)` and `‖U‖_{C^s} ≤ 3 X_e(U;K)`. (3) A spatially constant component
map `R` copies the base and every profile with labels unchanged (an exact finite sum again), at
cost at most `‖R‖` (the case of a constant map in Lemma 13.2(b)). -/
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
      representedSize s K e (r.map R) ≤ ENNReal.ofReal ‖R‖ * representedSize s K e r) :=
  by exact AVRegularity.Providers.iteration_readout s hs₀ hs₁ K hK

end AVRegularity
