-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfOpen

/-! # Endgame: `successor_residual_identities` from the last leaf

`successorResidualIdentities_of_native`: the statement
`successor_residual_identities` (the conclusion of `successor_residual_identities_of_cov_three`)
from `NativeTemporalRepresentativesStatement` alone (the native temporal representatives), with
the covariance temporal product `covarianceTemporalProduct` and the lift residual
`liftResidualWeak`. A conditional assembly. -/

@[expose] public section

open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Assembly

namespace AVRegularity.Providers.Endgame

/-- **`successor_residual_identities` from the native temporal representatives.** -/
theorem successorResidualIdentities_of_native (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hNative : NativeTemporalRepresentativesStatement) :
    type_of% (successor_residual_identities_of_cov_three α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hNative
      covarianceTemporalProduct liftResidualWeak) :=
  successor_residual_identities_of_cov_three α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hNative
    covarianceTemporalProduct liftResidualWeak

end AVRegularity.Providers.Endgame
