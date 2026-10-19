-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Finite.Assembly.WeakParentSettingOfIngredients

@[expose] public noncomputable section

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Finite.WeakLift

/-! The stage-free part of physical chart transfer: positive input derivatives, finite
Schur sums and factorial normalization. No construction, chart or cell datum enters here. -/

/-- The unnormalized positive input jet sum. It vanishes on constants and has no zero jet. -/
def positiveProfileJetSum {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E : ℝ) (J : ℕ) (F : Vec 2 → H) : ℝ≥0∞ :=
  ∑ α ∈ multiIndicesBetween 1 J,
    ENNReal.ofReal (E ^ (α 0 + α 1)) * supNorm (partialDerivative α F)

/-- Pointwise chart output bound after its finite Schur estimate, in the exact positive
partial derivatives of the physical input. The zero output jet is included. -/
def PositivePhysicalJetEstimate {H H' : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (e E : ℝ) (K J : ℕ) (C : ℝ) (F : Vec 2 → H) (corr : Vec 2 → H') : Prop :=
  (∀ x, ‖corr x‖ ≤ C * (e / E) *
    ∑ α ∈ multiIndicesBetween 1 J, E ^ (α 0 + α 1) * ‖partialDerivative α F x‖) ∧
  (∀ β ∈ multiIndicesBetween 1 K, ∀ x,
    e ^ (β 0 + β 1) * ‖partialDerivative β corr x‖ ≤ C * (e / E) *
      ∑ α ∈ multiIndicesBetween 1 J, E ^ (α 0 + α 1) * ‖partialDerivative α F x‖)

/-- Pointwise positive bounds give the raw
profile bound for an arbitrary normed input/output field. Constants precede all data. -/
def PositiveChartNormRestorationStatement : Prop :=
  ∀ (e E s : ℝ) (K J : ℕ) (C : ℝ), 0 < e → 0 < E → 0 < s → s < 1 → 0 ≤ C →
  ∀ {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H'],
  ∀ (r : Representation H) (corr : Vec 2 → H'), IsRepresentationAt E J r →
    PositivePhysicalJetEstimate e E K J C r.value corr →
    RawProfileJetBound e K s corr
      (ENNReal.ofReal (C * J.factorial) * ENNReal.ofReal ((e / E) ^ (1 - s)) *
        representedSize s J E r)

end AVRegularity.Finite.WeakLift
end

section
open Homogenization AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.WeakLift

/-! The chart split: pointwise positive output jets, regularity/periodicity,
and dimension-free restoration of the representation cost. The analytic leaves share
one literal case, retaining the actual weak glued operator and supplied coefficient array. -/

open Construction.Preservation.FullLift CycleComparison.Lift

/-- Data supplied to the chart transfer after all numerical constants were selected. -/
structure WeakPositiveChartCase {N H U : ℕ} (P : WeakPositiveParameters N H U) where
  D : OCData
  Dm : ℕ
  j₀ : ℕ
  bw : ℝ
  i : ℕ
  G : GenStage D ScalarH Dm bw j₀
  π : CompIn G.comps → ℝ
  mass : ∀ v, 0 < π v
  geometry : WeakPositiveGeometry P i G
  slotLift : ∀ slot : OddSlot, WeakPositiveSlot P i G π slot
  coeff : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)
  graded : ∀ slot : OddSlot, WeakPositiveGraded (slotLift slot)
  identified : ∀ slot : OddSlot, WeakPositiveIdentified (slotLift slot) (coeff slot.1)
  Cpath : ℝ
  Cpath_nonneg : 0 ≤ Cpath
  paths : ∀ slot : OddSlot, HasRealSchurBudget (massConjugatedMatrix π (fun v u =>
    ∑ hh ∈ Finset.range (H + 1), weakPositiveMatrix (slotLift slot) hh v u)) Cpath
  K : ℕ
  K_le : K ≤ U
  t : ℝ
  f : CompIn G.comps → Vec 2 → ℝ
  r : Representation (CompSpace G.comps)
  representation : IsRepresentationAt (D.eps (i - 1)) (K + N) r
  value : r.value = compField π (fun x v => f v x)

def WeakPositiveChartCase.correction {N H U : ℕ} {P : WeakPositiveParameters N H U}
    (C : WeakPositiveChartCase P) : Vec 2 → CompSpace C.G.comps :=
  compField C.π (fun x v =>
    weakGluedLift C.i N H C.G (positiveLiftCoefficients C.coeff) C.t C.f v x)

/-- Positive input jets through the literal glued operator. The numerical
constant is fixed before the construction, level, path budget, phase or datum. -/
def WeakPositivePointwiseChartStatement : Prop :=
  ∀ (N H U : ℕ) (P : WeakPositiveParameters N H U), ∃ Ct : ℝ, 0 ≤ Ct ∧
  ∀ C : WeakPositiveChartCase P,
    PositivePhysicalJetEstimate (C.D.eps C.i) (C.D.eps (C.i - 1)) C.K (C.K + N)
      (Ct * C.Cpath) C.r.value C.correction

/-- The actual native recurrence and torus-compatible charts preserve spatial
regularity and periodicity of the positive glued correction. -/
def WeakPositiveChartRegularityStatement : Prop :=
  ∀ (N H U : ℕ) (P : WeakPositiveParameters N H U) (C : WeakPositiveChartCase P),
    ContDiff ℝ (C.K : ℕ) C.correction ∧ IsZ2Periodic C.correction

/-- The exact chart leaf from its three sub-statements. -/
theorem weak_positive_derivative_chart_of_ingredients
    (hpoint : WeakPositivePointwiseChartStatement) (hreg : WeakPositiveChartRegularityStatement)
    (hnorm : PositiveChartNormRestorationStatement) : WeakPositiveDerivativeChartStatement := by
  intro N H U P s hs hs1
  obtain ⟨Ct, hCt, hpoint⟩ := hpoint N H U P
  refine ⟨Ct * (U + N).factorial, mul_nonneg hCt (Nat.cast_nonneg _), ?_⟩
  intro D Dm j₀ bw i G π hπ hgeom A Cc hgraded hidentified Cpath hCpath hpaths
    K hK t f r hr hv corr
  let C : WeakPositiveChartCase P :=
    ⟨D, Dm, j₀, bw, i, G, π, hπ, hgeom, A, Cc, hgraded, hidentified,
      Cpath, hCpath, hpaths, K, hK, t, f, r, hr, hv⟩
  have he : 0 < D.eps i := Construction.Stream.ocEpsilon_pos (by have := hgeom.Λ_ge; omega)
  have hE : 0 < D.eps (i - 1) := Construction.Stream.ocEpsilon_pos
    (by have := hgeom.Λ_ge; omega)
  have hraw := hnorm (D.eps i) (D.eps (i - 1)) s K (K + N) (Ct * Cpath)
    he hE hs hs1 (mul_nonneg hCt hCpath) r C.correction hr (hpoint C)
  have hc : ENNReal.ofReal (Ct * Cpath * (K + N).factorial) ≤
      ENNReal.ofReal (Ct * (U + N).factorial * Cpath) := by
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Ct * Cpath * (U + N).factorial := mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.factorial_le (Nat.add_le_add_right hK N))
        (mul_nonneg hCt hCpath)
      _ = _ := by ring
  have hbound :
      ENNReal.ofReal (Ct * Cpath * (K + N).factorial) *
        ENNReal.ofReal ((D.eps i / D.eps (i - 1)) ^ (1 - s)) * representedSize s (K + N) (D.eps (i - 1)) r ≤
      ENNReal.ofReal (Ct * (U + N).factorial * Cpath) *
        ENNReal.ofReal ((D.eps i / D.eps (i - 1)) ^ (1 - s)) * representedSize s (K + N) (D.eps (i - 1)) r :=
    mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl
  obtain ⟨hcd, hper⟩ := hreg N H U P C
  exact ⟨hcd, hper, hraw.1.trans hbound, fun a ha => (hraw.2 a ha).trans hbound⟩

end AVRegularity.Finite.WeakLift
end
