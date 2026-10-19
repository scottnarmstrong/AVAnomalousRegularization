-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.ClassicalGradeFlux
public import AVenhance.Statements.Roots.IsZ2Periodic

/-! The coarse letters `(AD, CE)` present the glued physical mean of grade `r`
(`ℓ^{-2}ε_c^nL_n^{(h)}` is a divergence-form operator; the convention is `M I - E`): for every
smooth periodic classical field `a`, time `t ∈ I` and position `x`,
`(ℳ^{(r)}a)(t,x) = -div(classicalGradeFlux r a)(t,x)`. The divergence form is the existential output
(the divergence-form presentation is not unique, but its divergence is). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The mean-field operator `M` of grade `r` is `-div` of the grade-`r` flux of the letters. -/
def IsMeanPresentation {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (I : Set ℝ) (D r : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (M : (ℝ → Vec 2 → ∀ i, h i) → ℝ → Vec 2 → ∀ i, h i) : Prop :=
  ∀ a : ℝ → Vec 2 → ∀ i, h i, (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) →
    (∀ t, AVenhance.IsZ2Periodic (a t)) → ∀ t ∈ I, ∀ x, ∀ v,
      M a t x v = -∑ k : Fin 2, fderiv ℝ (fun y => classicalGradeFlux D r AD CE Jm a v t y k) x
        (basisVec k)

end AVRegularity
