-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.QuietDecay.Translate.Main
public import AVRegularity.Statements.Intermediate.CycleComparison.SlowPartial
public import AVRegularity.Statements.Intermediate.CycleComparison.FastPartial
import AVRegularity.CycleComparison.Residual.TimeIntegration
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative
public import AVRegularity.Statements.Intermediate.CycleComparison.IsBoxSmooth
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

@[expose] public noncomputable section

section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.QuietDecay

/-! Joint time-cell a.e. strong measurability of the first slow and fast partial derivatives of a
time-dependent two-scale field `F t X z`, as a.e. limits of difference quotients, together with the
trivial stability under slow-only time-measurable factors. -/

/-- The product measure `dt|_J ⊗ dz|_{unit cube}` on time-cell pairs `(t, z)`. -/
abbrev timeCellMeasure (J : Set ℝ) : Measure (ℝ × Vec 2) :=
  (volume.restrict J).prod (volume.restrict AVenhance.unitCube)

theorem ae_timeCell_fst_mem {J : Set ℝ} (hJ : MeasurableSet J) :
    ∀ᵐ p ∂(timeCellMeasure J), p.1 ∈ J :=
  (Measure.quasiMeasurePreserving_fst (μ := volume.restrict J)
    (ν := volume.restrict AVenhance.unitCube)).ae (ae_restrict_mem hJ)

theorem aestronglyMeasurable_fst_comp {J : Set ℝ} {β : Type*} [TopologicalSpace β] {g : ℝ → β}
    (hg : AEStronglyMeasurable g (volume.restrict J)) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => g p.1) (timeCellMeasure J) :=
  hg.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst (μ := volume.restrict J)
    (ν := volume.restrict AVenhance.unitCube))

/-- A family `p ↦ f p s` of a.e. strongly measurable functions whose `s`-derivative at `0` exists
a.e. has an a.e. strongly measurable derivative. -/
theorem aestronglyMeasurable_of_hasDerivAt_zero {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → ℝ → E} {f' : α → E}
    (hf : ∀ s, AEStronglyMeasurable (fun p => f p s) μ)
    (hd : ∀ᵐ p ∂μ, HasDerivAt (f p) (f' p) 0) : AEStronglyMeasurable f' μ := by
  let u : ℕ → α → E := fun k p => ((k : ℝ) + 1) • (f p (1 / ((k : ℝ) + 1)) - f p 0)
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ) (f := u) (fun k => ?_) ?_
  · exact ((hf _).sub (hf 0)).const_smul _
  · filter_upwards [hd] with p hp
    have h := hasDerivAt_iff_tendsto_slope_zero.mp hp
    have h2 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k => one_div_ne_zero (Nat.cast_add_one_ne_zero k)⟩
    refine (h.comp h2).congr fun k => ?_
    simp [u]

section Shift

variable {E : Type*} [TopologicalSpace E]

/-- Joint a.e. strong measurability of fast translates of a time-dependent field that is
`ℤ²`-periodic in `z` for `t ∈ J`. -/
theorem aestronglyMeasurable_joint_shift_gen {J : Set ℝ} (hJ : MeasurableSet J)
    {f : ℝ → Vec 2 → E}
    (hf : AEStronglyMeasurable (fun p : ℝ × Vec 2 => f p.1 p.2) (timeCellMeasure J))
    (hper : ∀ t ∈ J, AVenhance.IsZ2Periodic (f t)) (w : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => f p.1 (p.2 + w)) (timeCellMeasure J) := by
  have hmp : MeasurePreserving (Prod.map id (cubeShift w)) (timeCellMeasure J)
      (timeCellMeasure J) :=
    (MeasurePreserving.id (volume.restrict J)).prod (measurePreserving_cubeShift w)
  refine (hf.comp_measurePreserving hmp).congr ?_
  filter_upwards [ae_timeCell_fst_mem hJ] with p hp
  exact (periodic_add_eq_cubeShift (hper p.1 hp) w p.2).symm

end Shift

section Partial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Slow partial derivative: a.e. limit of difference quotients in `X`. -/
theorem aestronglyMeasurable_slowPartial {J : Set ℝ} (hJ : MeasurableSet J)
    {F : ℝ → Vec 2 → Vec 2 → E}
    (hmeas : ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => F p.1 X p.2) (timeCellMeasure J))
    (hdiff : ∀ t ∈ J, ∀ z, Differentiable ℝ (fun X => F t X z)) (i : Fin 2) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => slowPartial i (F p.1) X p.2)
      (timeCellMeasure J) := by
  refine aestronglyMeasurable_of_hasDerivAt_zero
    (f := fun (p : ℝ × Vec 2) (s : ℝ) => F p.1 (X + s • basisVec i) p.2)
    (fun s => hmeas _) ?_
  filter_upwards [ae_timeCell_fst_mem hJ] with p hp
  have hline : HasDerivAt (fun s : ℝ => X + s • basisVec i) (basisVec i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec i)).const_add X
  have h0 : HasFDerivAt (fun X' => F p.1 X' p.2) (fderiv ℝ (fun X' => F p.1 X' p.2) X)
      (X + (0 : ℝ) • basisVec i) := by
    simpa using ((hdiff p.1 hp p.2) X).hasFDerivAt
  exact h0.comp_hasDerivAt (0 : ℝ) hline

/-- Fast partial derivative, for fields `ℤ²`-periodic in `z` for `t ∈ J`: a.e. limit of difference
quotients in `z`, the fast translates being measurable by the periodic shift lemma. -/
theorem aestronglyMeasurable_fastPartial {J : Set ℝ} (hJ : MeasurableSet J)
    {F : ℝ → Vec 2 → Vec 2 → E}
    (hmeas : ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => F p.1 X p.2) (timeCellMeasure J))
    (hper : ∀ t ∈ J, ∀ X, AVenhance.IsZ2Periodic (F t X))
    (hdiff : ∀ t ∈ J, ∀ X, Differentiable ℝ (F t X)) (i : Fin 2) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => fastPartial i (F p.1) X p.2)
      (timeCellMeasure J) := by
  refine aestronglyMeasurable_of_hasDerivAt_zero
    (f := fun (p : ℝ × Vec 2) (s : ℝ) => F p.1 X (p.2 + s • basisVec i))
    (fun s => aestronglyMeasurable_joint_shift_gen hJ (f := fun t => F t X) (hmeas X)
      (fun t ht => hper t ht X) _) ?_
  filter_upwards [ae_timeCell_fst_mem hJ] with p hp
  have hline : HasDerivAt (fun s : ℝ => p.2 + s • basisVec i) (basisVec i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec i)).const_add p.2
  have h0 : HasFDerivAt (F p.1 X) (fderiv ℝ (F p.1 X) p.2) (p.2 + (0 : ℝ) • basisVec i) := by
    simpa using ((hdiff p.1 hp X) p.2).hasFDerivAt
  exact h0.comp_hasDerivAt (0 : ℝ) hline

end Partial

section Products

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- Multiplication by a slow-only factor that is measurable in time. -/
theorem aestronglyMeasurable_smul_slow {J : Set ℝ} {F : ℝ → Vec 2 → Vec 2 → E}
    {g : ℝ → Vec 2 → ℝ} (X : Vec 2)
    (hg : AEStronglyMeasurable (fun t => g t X) (volume.restrict J))
    (hF : AEStronglyMeasurable (fun p : ℝ × Vec 2 => F p.1 X p.2) (timeCellMeasure J)) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => g p.1 X • F p.1 X p.2) (timeCellMeasure J) :=
  (aestronglyMeasurable_fst_comp hg).smul hF

end Products

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.QuietDecay

/-! Joint time-cell a.e. strong measurability of iterated slow and fast word derivatives, and of
fast word derivatives of slow word derivatives, of a time-dependent box-smooth two-scale field.
The iterates are organised as `slowIter`/`fastIter`, which keep `IsBoxSmooth` (with the order
lowered by the word length) and fast periodicity, so that the one-step lemmas of `Meas.Partial`
apply inductively. -/

section Iter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterated slow partials along a list of letters (first letter innermost). -/
def slowIter (l : List (Fin 2)) (Φ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  l.foldl (fun Φ' i => slowPartial i Φ') Φ

/-- Iterated fast partials along a list of letters (first letter innermost). -/
def fastIter (l : List (Fin 2)) (Φ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  l.foldl (fun Φ' i => fastPartial i Φ') Φ

theorem slowIter_append_single (l : List (Fin 2)) (i : Fin 2) (Φ : Vec 2 → Vec 2 → E) :
    slowIter (l ++ [i]) Φ = slowPartial i (slowIter l Φ) := by
  simp [slowIter, List.foldl_append]

/-- The ordered derivative along a list of letters (first letter innermost). -/
def wordList (l : List (Fin 2)) (g : Vec 2 → E) : Vec 2 → E :=
  l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g

theorem orderedDerivative_eq_wordList {m : ℕ} (α : DerivativeWord2 m) (g : Vec 2 → E) :
    orderedDerivative α g = wordList (List.ofFn α) g := rfl

theorem wordList_slowIter (l : List (Fin 2)) :
    ∀ (Φ : Vec 2 → Vec 2 → E) (X z : Vec 2),
      wordList l (fun X' => Φ X' z) X = slowIter l Φ X z := by
  induction l with
  | nil => intro Φ X z; rfl
  | cons i l ih => intro Φ X z; exact ih (slowPartial i Φ) X z

theorem wordList_fastIter (l : List (Fin 2)) :
    ∀ (Φ : Vec 2 → Vec 2 → E) (X z : Vec 2),
      wordList l (Φ X) z = fastIter l Φ X z := by
  induction l with
  | nil => intro Φ X z; rfl
  | cons i l ih => intro Φ X z; exact ih (fastPartial i Φ) X z

theorem isBoxSmooth_slowIter {sZ : ℕ} (l : List (Fin 2)) :
    ∀ (sX : ℕ) (Φ : Vec 2 → Vec 2 → E), IsBoxSmooth (sX + l.length) sZ Φ →
      IsBoxSmooth sX sZ (slowIter l Φ) := by
  induction l with
  | nil => intro sX Φ h; exact h
  | cons i l ih => intro sX Φ h; exact ih sX _ (IsBoxSmooth.slowPartial h i)

theorem periodic_slowIter (l : List (Fin 2)) :
    ∀ (Φ : Vec 2 → Vec 2 → E), (∀ X, AVenhance.IsZ2Periodic (Φ X)) →
      ∀ X, AVenhance.IsZ2Periodic (slowIter l Φ X) := by
  induction l with
  | nil => intro Φ h; exact h
  | cons i l ih =>
    intro Φ h
    refine ih _ fun X n z => ?_
    show fderiv ℝ (fun X' => Φ X' (z + _)) X (basisVec i) = fderiv ℝ (fun X' => Φ X' z) X _
    simp only [h _ n z]

theorem periodic_fastIter (l : List (Fin 2)) :
    ∀ (Φ : Vec 2 → Vec 2 → E), (∀ X, AVenhance.IsZ2Periodic (Φ X)) →
      ∀ X, AVenhance.IsZ2Periodic (fastIter l Φ X) := by
  induction l with
  | nil => intro Φ h; exact h
  | cons i l ih =>
    intro Φ h
    refine ih _ fun X n z => ?_
    show fderiv ℝ (Φ X) (z + _) (basisVec i) = fderiv ℝ (Φ X) z _
    have e : (fun z' => Φ X (z' + _)) = Φ X := funext (h X n)
    rw [← fderiv_comp_add_right, e]

end Iter

section Meas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {J : Set ℝ}
  {F : ℝ → Vec 2 → Vec 2 → E} {sX sZ : ℕ}

/-- Slow words of length at most `sX`. -/
theorem aestronglyMeasurable_slowIter (hJ : MeasurableSet J)
    (hF : ∀ t ∈ J, IsBoxSmooth sX sZ (F t))
    (hmeas : ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => F p.1 X p.2) (timeCellMeasure J))
    (l : List (Fin 2)) (hl : l.length ≤ sX) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => slowIter l (F p.1) X p.2) (timeCellMeasure J) := by
  induction l using List.reverseRecOn generalizing X with
  | nil => exact hmeas X
  | append_singleton l i ih =>
    simp only [List.length_append, List.length_singleton] at hl
    simp only [slowIter_append_single]
    refine aestronglyMeasurable_slowPartial hJ (F := fun t => slowIter l (F t))
      (fun X' => ih (by omega) X') (fun t ht z => ?_) i X
    have h1 : IsBoxSmooth 1 sZ (slowIter l (F t)) :=
      isBoxSmooth_slowIter l 1 _ ((hF t ht).mono (by omega) le_rfl)
    exact (h1.contDiff_slow z).differentiable (by norm_num)

/-- Ordered slow word derivatives of length `m ≤ sX`. -/
theorem aestronglyMeasurable_orderedDerivative_slow (hJ : MeasurableSet J)
    (hF : ∀ t ∈ J, IsBoxSmooth sX sZ (F t))
    (hmeas : ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => F p.1 X p.2) (timeCellMeasure J))
    {m : ℕ} (α : DerivativeWord2 m) (hm : m ≤ sX) (X : Vec 2) :
    AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => orderedDerivative α (fun X' => F p.1 X' p.2) X)
      (timeCellMeasure J) := by
  have := aestronglyMeasurable_slowIter hJ hF hmeas (List.ofFn α) (by simpa using hm) X
  simpa only [orderedDerivative_eq_wordList, wordList_slowIter] using this

end Meas

end AVRegularity.QuietDecay
end
