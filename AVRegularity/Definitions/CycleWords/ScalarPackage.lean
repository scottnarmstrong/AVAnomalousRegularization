-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleWords.CoreScalarPackage

/-! **The scalar input package** of the word and seam statements
("The reusable input
must therefore include: the low graph and normalized row jets; centered forward and adjoint decay
and finite-order smoothing; the real Gaussian and its frequency jets; high-band decay; the
pulse-local transverse source bounds and both positive sums; quiet identities with the original
histories; and the chart, weight and duration bounds. The seam also uses negative-order propagation
on an arbitrarily short old piece and the two-sided scalar kernel estimates on the future piece").
It extends the package of a piece (`CoreScalarPackage`) by the properties of a complete
admissible block:

* `gauss`: the real Gaussian `Re Ξ ≤ -cS|ξ|²` on the full window for `|ξ| ≤ 2ξ_*` (also for
  every Taylor truncation `N ≥ 2` of the symbol) and `phase_jets`: the normalized frequency jets of
  `Ξ` (`|∂_ξ Ξ| ≤ C√S·√S|ξ|`, `|∂_ξ^n Ξ| ≤ C S^{n/2}`);
* the high-band decay by marks: `marks_count`, `marks_in`, `marks_sep` (at least `c_adm S/θ_*`
  separated marks of each orientation inside the window) and `high_marks` (for every real `ξ` in
  the Brillouin zone `|ξ| ≥ ξ_*` some orientation has every mark contracting the `L²` norm by `1/2`;
  with `contraction` the complementary intervals do not expand it).

The two-sided scalar kernel estimates of the seam follow from `gauss`,
`phase_jets` and the word estimates by Fourier integration by parts, and the negative-order
propagation of the old piece follows from `weights`, `actual` and `neg_adjoint`; they are proof
steps, not separate fields. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The scalar package of a complete admissible block.

`high_marks` ranges over `IsCellSolution` (`L²` data). -/
structure ScalarPackage (K : ScalarConstants) (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t₀ S ϖ : ℝ) (reg : BlockRegions)
    extends CoreScalarPackage K η G v t₀ S ϖ reg where
  gauss : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → fibreNorm ξ ≤ 2 * K.ξlo →
    (∫ τ in t₀..(t₀ + S), fibreSeriesC actual.lam ξ τ).re ≤ -K.cGauss * S * fibreNorm ξ ^ 2 ∧
    ∀ N : ℕ, 2 ≤ N →
      (∫ τ in t₀..(t₀ + S), ∑ n ∈ Finset.range (N + 1), fibreHomogeneous actual.lam ξ n τ).re ≤
        -K.cGauss * S * fibreNorm ξ ^ 2
  phase_jets : ∀ (n : ℕ) (j : Fin n → Fin 2) (ξ : Fin 2 → ℂ), 1 ≤ n → fibreNorm ξ < K.ξ0 →
    ∀ s t : ℝ, t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
      ‖iteratedFDeriv ℂ n (fun ξ' : Fin 2 → ℂ => ∫ τ in s..t, fibreSeriesC actual.lam ξ' τ) ξ
          (fun i => Pi.single (j i) (1 : ℂ))‖ ≤
        K.Cj n * Real.sqrt S ^ n * (if n = 1 then Real.sqrt S * fibreNorm ξ else 1)
  marks_in : ∀ j, ∀ m ∈ reg.marks j, t₀ ≤ m ∧ m + K.θs ≤ t₀ + S
  marks_sep : ∀ j, ∀ m ∈ reg.marks j, ∀ m' ∈ reg.marks j, m ≠ m' →
    m + K.θs ≤ m' ∨ m' + K.θs ≤ m
  marks_count : ∀ j, K.cadm * S / K.θs ≤ ((reg.marks j).card : ℝ)
  high_marks : ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η) →
    K.ξlo ≤ fibreNorm ξ → ∃ j : Fin 2, ∀ m ∈ reg.marks j, ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc m (m + K.θs)) (fibreCoefficients η G v ξ (fun _ => 0))
        (fun _ _ => 0) (fun _ _ => 0) D →
      cellL2Norm (cellValue D (m + K.θs)) ≤ ENNReal.ofReal (1 / 2) * cellL2Norm (cellValue D m)

end AVRegularity
