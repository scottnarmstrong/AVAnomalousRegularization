-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Applications.Construction.StreamTail

section
section
/-! # Heat replacement (facade)

Re-exports `AVRegularity.Applications.heat_replacement`; see `HeatReplacement/Main.lean`. -/
end

section
/-! # Statements of the finite and global theorems

`OcFiniteStatement α s q ζ` is interior regularity for the finite velocity fields `b_{M+J}` of
the construction, uniformly in the level `M`, and `OcGlobalStatement α s q ζ` is interior
regularity for every limit `b` of the construction, for fixed strict parameters `α, s`,
admissible `q` and fast profile `ζ`. They are the hypotheses of the conditional theorems
`oc_global_of_finite`, `local_interior_regularity_of_global`, …, which the main results combine.
"The energy solution" is every solution in the weak class
`IsWeakSolutionOn` (it is unique there), and `‖θ(t)‖_{C^s(𝕋²)} ≤ K` means that `θ(t)` has a
periodic representative with `CsNormLe s · K`. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Applications

/-- **The finite-level statement.** For the construction (`Λ ≥ Λ₀`), every integer `J ≥ 1`
and `0 < t₀ < T` there are `M_*` and `C` such that for `M ≥ M_*`, `κ ∈ 𝒦_M`, `a ∈ ℝ` and
`f ∈ L²(𝕋²)`, the energy solution with velocity `b_{M+J}` and `θ(a) = f` satisfies
`‖θ(t)‖_{C^s(𝕋²)} ≤ C ‖f‖₂` for every `t ∈ [a + t₀, a + T]`. -/
def OcFiniteStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ J : ℕ, 1 ≤ J → ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T →
        ∃ Mstar : ℕ, ∃ C : ℝ, ∀ M : ℕ, Mstar ≤ M → 1 ≤ M →
          ∀ κ ∈ Set.Icc (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2)
              (2 * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q)),
          ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
          ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn (streamVel (Φ (M + J))) κ a (a + T) f θ →
            ∀ t ∈ Set.Icc (a + t₀) (a + T), ∃ Θt : Vec 2 → ℝ,
              IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
              CsNormLe s Θt (C * Real.sqrt (l2NormSq f))

/-- **The global statement.** For the construction (`Λ ≥ Λ₀`) with limit velocity `b`,
every `0 < t₀ < T` admits `C` such that for all `a ∈ ℝ`, `κ ∈ 𝒦` and `f ∈ L²(𝕋²)` the energy
solution with `θ(a) = f` has a representative jointly continuous on `[a+t₀, a+T] × 𝕋²` with
`sup_{a+t₀ ≤ t ≤ a+T} ‖θ(t)‖_{C^s(𝕋²)} ≤ C ‖f‖₂`. -/
def OcGlobalStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ b : ℝ → Vec 2 → Vec 2, (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
        ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
          ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
          ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
            ∃ Θ : ℝ → Vec 2 → ℝ,
              ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
              ∀ t ∈ Set.Icc (a + t₀) (a + T),
                IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))

end AVRegularity.Applications
end
end

section
/-! # Interior Lipschitz estimate for weakly caloric functions (facade)

Exports `AVRegularity.Applications.caloric_interior_lipschitz`.
-/
end
end

section
section
/-! # Local energy identity, local `L²` traces, flux form and Caccioppoli (facade)

* `local_energy_identity`, `local_trace_aux` (module `LocalEnergy.Caccioppoli`);
* `skewDrift_flux_form` (module `LocalEnergy.AEIdent`);
* `skewDrift_caccioppoli` (module `LocalEnergy.Caccioppoli`). -/
end

section
/-! # Translating tubes (facade)

`AVRegularity.Applications.tube_regularity` and `tube_regularity_periodic`: the full-velocity
consequence of the microscopic oscillation lemma, proved conditionally on
`OcMicroscopicStatement`. -/
end

section
/-! # Construction-side bounds for the applications layer

Facade for the stream tail bounds (`stream_tail_bounds`, `ocEpsilon_succ_le`,
`ocEpsilon_succ_ge`) and the short-flow bounds (`short_flow_bounds`). -/
end
end
