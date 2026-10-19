-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleWords.OcCellMetric
public import AVRegularity.Statements.Intermediate.CycleWords.OcCellCentre
public import AVRegularity.Statements.Intermediate.CycleEvolution.OcCellDrift
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsMetricNearIdentity
public import AVRegularity.Statements.Intermediate.CoupledEnergy.DriftCoefficient
public import AVRegularity.Statements.Intermediate.CycleReference.OcEll
public import AVRegularity.Statements.Construction.OcTauPP
public import AVRegularity.Statements.Construction.OcTau
public import AVRegularity.Statements.Construction.OcEpsilon

/-! The construction-side premises of the joint preparation `cycle_joint` on the full
preparation cover: the metric jets, the admissibility, the duration and the common-background
chart and weight conditions of the damping and geometry statements of the cell evolution; in
particular `R ≤ E < 1`, `T‖D𝐛_bg‖_∞ ≤ g`, `T‖D²𝐛_bg‖_∞ ≤ Cg/E`.

Same shape as the geometry cover of the cell evolution, with `T = τ_m''` the scale and the cover a
time window `[tA, tZ]` (for the joint preparation `[tS, tS + C_H T]`: the quiet `t_p` lies in
`(tS, tS + C_H T]`, so the cover must contain it; for the comparison the later window
`[t_p, t_p + T_obs]`). The scales: `E = ε_{m-1}`, `e = ε_m`, `R = √(Bτ_m'')`, `ℓ = e/√ν`,
`ρ_* ≤ min{e,R}`; the duration condition `√T ℓ τ⁻¹ exp(-π²τ/(3ℓ²)) ≤ 1` (`τ = τ_m`).

Core blocks and bound charts. `l₀`, `P` and `window` describe the core renewal blocks
`[(l-½)h, (l+½)h]`, `l = l₀, …, l₀+P−1`, `h = τ_m''`. An observed pulse near an endpoint may belong
to chart `l₀−1` or `l₀+P`, so the chart-dependent fields are quantified over `i : Fin (P + 2)`,
chart label `l = l₀ − 1 + i`. The centres are the same background particle in every chart:
`y₋ = ocTransition (l₀−1) l₀ y₀`, the label in chart `l₀−1` of the particle with label `y₀` in chart
`l₀`, and `Y_i = ocCellCentre (l₀−1) y₋ i`; hence `Y_{j+1}` is the old core centre
`ocCellCentre l₀ y₀ j`.

Per-chart metric window. In the cell variables of chart `l` (`ocCellMetric`), the metric bounds
`‖G-I‖ ≤ g ≤ g₀`, `‖D_X^jG‖ ≤ C_j g (e/E)^j` through the reserve `qJ`, and spatial smoothness are
required only on the chart's anchor neighbourhood intersected with the cover, in cell time
`[max{tA, (l−1)h}/ℓ², min{tZ, (l+1)h}/ℓ²]` (max/min taken in physical time; empty if inverted). The
construction gives the material-metric jets for `|t − lh| ≤ h` only, so the window is per chart and
does not grow with `P`.

Uniform background bounds. The short-flow bounds of the background velocity
`𝐛_bg = 𝐛_{m-1} = streamVel (Φ (m-1))`, with the unchanged `h` normalization, hold on the anchor
hull `[min{tA, (l₀−1)h}, max{tZ, (l₀+P)h}]`, which contains every bound chart's anchor path. The
finite molecular drift absorption conditions (condition (11.1) of the paper) of the label-frame
drift `ocCellDrift` at the radius `ρ_*/e` hold for every bound chart centre on the whole cell-time
window `[tA/ℓ², tZ/ℓ²]`.

Admissibility of the renewal blocks (`IsOCAdmissibleInterval`) is not a field: it holds for
`m ≥ m_*` by `cycle_damping`, and the starting level of the proposition is chosen after it. -/

@[expose] public section

open Homogenization AVenhance AVRegularity.Sobolev

namespace AVRegularity

/-- The construction-side premises on a cover `[tA, tZ]` of `P` core charts from `l₀`; the
chart-dependent bounds are on the `P + 2` charts `l₀ − 1 + i`, each on its own anchor window. -/
structure IsWindowCover (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (ν B tA tZ ρs g g0 a B₀ lam Cb : ℝ)
    (qJ Kmax : ℕ) (CG : ℕ → ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2) : Prop where
  pos : 0 < ν ∧ 0 < B ∧ 0 < ρs
  P_pos : 1 ≤ P
  RE : Real.sqrt (B * ocTauPP α q Λ m) ≤ ocEpsilon q Λ (m - 1)
  ellT : ocEll q Λ m ν ^ 2 ≤ ocTauPP α q Λ m
  rho_e : ρs ≤ ocEpsilon q Λ m
  rho_R : ρs ≤ Real.sqrt (B * ocTauPP α q Λ m)
  dur : Real.sqrt (ocTauPP α q Λ m) * ocEll q Λ m ν / ocTau α q Λ m *
    Real.exp (-(Real.pi ^ 2 * ocTau α q Λ m) / (3 * ocEll q Λ m ν ^ 2)) ≤ 1
  short1 : ∀ t ∈ Set.Icc (min tA (((l₀ : ℝ) - 1) * ocTauPP α q Λ m))
      (max tZ (((l₀ : ℝ) + P) * ocTauPP α q Λ m)), ∀ y : Vec 2,
    ocTauPP α q Λ m * ‖fderiv ℝ (streamVel (Φ (m - 1)) t) y‖ ≤ g
  short2 : ∀ t ∈ Set.Icc (min tA (((l₀ : ℝ) - 1) * ocTauPP α q Λ m))
      (max tZ (((l₀ : ℝ) + P) * ocTauPP α q Λ m)), ∀ y : Vec 2,
    ocTauPP α q Λ m * ‖fderiv ℝ (fderiv ℝ (streamVel (Φ (m - 1)) t)) y‖ ≤
      Cb * g / ocEpsilon q Λ (m - 1)
  window : ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ tA ∧
    tA < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m ∧
    ((l₀ : ℝ) + P - 3 / 2) * ocTauPP α q Λ m < tZ ∧
    tZ ≤ ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ m
  g_range : 0 ≤ g ∧ g ≤ g0
  metric_near : ∀ i : Fin (P + 2),
    ∀ t ∈ Set.Icc (max tA ((((l₀ - 1 + i : ℤ) : ℝ) - 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
      (min tZ ((((l₀ - 1 + i : ℤ) : ℝ) + 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2),
    ∀ z (ξ : Vec 2),
    |∑ a', ∑ k, ξ a' * (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1)
          (ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀) i) t z -
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) a' k * ξ k| ≤ g * ∑ a', ξ a' ^ 2
  metric_smooth : ∀ i : Fin (P + 2),
    ∀ t ∈ Set.Icc (max tA ((((l₀ - 1 + i : ℤ) : ℝ) - 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
      (min tZ ((((l₀ - 1 + i : ℤ) : ℝ) + 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2),
    ∀ a' k : Fin 2, ContDiff ℝ qJ (fun z => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
      (ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1)
        (ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀) i) t z a' k)
  metric_jets : ∀ i : Fin (P + 2),
    ∀ t ∈ Set.Icc (max tA ((((l₀ - 1 + i : ℤ) : ℝ) - 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2)
      (min tZ ((((l₀ - 1 + i : ℤ) : ℝ) + 1) * ocTauPP α q Λ m) / ocEll q Λ m ν ^ 2),
    ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ qJ → ∀ a' k : Fin 2,
      ‖iteratedFDeriv ℝ j (fun z' => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1)
          (ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀) i) t z' a' k) z‖ ≤
        CG j * g * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ j
  drift_pos : 0 ≤ a ∧ 1 ≤ B₀ ∧ 0 < lam
  drift_jets : ∀ i : Fin (P + 2), ∀ l : ℕ, 1 ≤ l → l ≤ Kmax →
    ∀ t ∈ Set.Icc (tA / ocEll q Λ m ν ^ 2)
      (tZ / ocEll q Λ m ν ^ 2), ∀ z : Vec 2,
      ‖coefficientDerivativeArray (driftCoefficient (ocCellDrift α q Λ ζ m ν
          (ocCellCentre α q Λ m (Φ (m - 1)) hφ (l₀ - 1)
            (ocTransition α q Λ m (Φ (m - 1)) hφ (l₀ - 1) l₀ y₀) i) t)) l z‖ ≤
        a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)
  drift_scale : B₀ * (ρs / ocEpsilon q Λ m) / lam ≤ 1 / 2
  drift_small : a * B₀ * (ρs / ocEpsilon q Λ m) ^ 2 ≤ 1 / 8

end AVRegularity
