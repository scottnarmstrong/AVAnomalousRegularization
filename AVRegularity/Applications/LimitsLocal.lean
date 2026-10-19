-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.LimitsLocal.Kern
public import AVRegularity.Applications.LimitsLocal.JointCont
public import AVRegularity.Applications.LimitsLocal.Main

section
section
/-! # Torus energy toolkit (facade)

Energy identities on the periodic window (`l2NormSq_le_of_isHolderDivFreeVelocity`), the local
weak-solution bridge (`isLocalWeakSolution_of_isWeakSolutionOn`), the forced periodic energy
identity (`torus_forced_energy_identity`), the difference of two drifts (`isTorusForced_difference`),
the skew identity (`skew_h1`) and the stream energy comparison (`stream_comparison`,
`stream_comparison_half`; Lemma 8.2 of the paper follows from `stream_comparison`). -/
end

section
/-! # Material (label) coordinates for the local theorem

Facade for `AVRegularity.Applications.Pipe.*`: the chart coefficients `pipeMetric`, `pipeDrift`,
their bounds (`pipe_coeff_bounds_uniform`) and the pulled-back equation of a local energy
solution (`pipe_pullback_weak`, `pipe_pullback_weak_global_core`). -/
end

section
/-! # The physical lift of the local theorem

Facade for `AVRegularity.Applications.LocalPhys.*`: `physLift_holds` proves `PhysLiftStmt`
(`θ - u` is a local weak solution in the comparison pipe). -/
end

section
/-! # The Davies localization for the local theorem (facade)

* `davies_holds` : `DaviesStmt α q Λ Φ b`;
* `localTrace_holds` : `LocalTraceStmt α q Λ Φ b` (local `L²` traces from below).

Modules of `AVRegularity.Applications.Davies`: `Equation` (cutoffs, label coefficients and the
pointwise algebra), `ChartBridge` (cutoff energy and weighted local energy), `UfEnergy` (the
difference equation and the torus solution `u_f` in label coordinates), `UfPackage` (initial
traces and the comparison in label coordinates), `LocalTrace` (the localization and the local
traces). -/
end

section
/-! # Local interior regularity from its tools

Facade for `AVRegularity.Applications.Local.*`: the interfaces of the three analytic inputs
(`DaviesStmt`, `PhysLiftStmt`, `LocalTraceStmt`), the containment of translating tubes in the
comparison pipe, the global part, the smoothing of the difference with its label traces, the top
time from below, and the assembly `local_interior_regularity_of_tools`.
-/
end
end

section
section
/-! # All-distance transfer (facade)

`transfer_holds`: the all-distance transfer for every exponent `s ∈ (0,1)`. Proposition 3.2 of
the paper follows from it. -/
end

section
/-! # Vanishing-diffusivity limits, local part (facade)

Facade for `AVRegularity.Applications.LimitsLocal.*`: the local half of the vanishing-diffusivity
limits, conditional on the statement `OcLocalStatement` of the local theorem
(`vanishing_diffusivity_limits_local_of_local`; Corollary D(b) of the paper follows from it). -/
end
end
