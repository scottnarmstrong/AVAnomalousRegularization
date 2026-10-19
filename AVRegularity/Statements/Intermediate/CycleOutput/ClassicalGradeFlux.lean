-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative

/-! The flux of grade `r` of the coarse mean equation, applied to a classical coarse field `a(t,x)`
(`coarseDefectFlux` for classical fields): the mean operator of grade `0` is `-div(𝖩∇a + F_A a)`,
`F_A a = ∑_d A_d ∇^{d-1}a` (`M = ∂_t + 𝐛·∇ - 𝖩:D² - div F_A`, `𝖩` spatially constant symmetric), and
of grade `r ≥ 1` `-div F_E^{(r)} a`, `(F_E^{(r)} a)_v = ∑_{u,d} C^{[r]}_{vu,d} ∇^{d-1}a_u`
(`E = div F_E`, the convention `M I - E`). The scalar letters `A_d` act on each Hilbert component
diagonally. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The component `k ∈ {0,1}` of the grade-`r` flux of the component `v`, at `(t,x)`. -/
def classicalGradeFlux {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (D r : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ → Vec 2 → ∀ i, h i) (v : ι) (t : ℝ) (x : Vec 2)
    (k : Fin 2) : h v :=
  if r = 0 then
    (∑ l : Fin 2, Jm t k l • fderiv ℝ (fun y => a t y v) x (basisVec l))
      + ∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
          (AD d t x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) •
            orderedDerivative α (fun y => a t y v) x
  else
    ∑ u : ι, ∑ d : Finset.Icc 2 D,
      (CE r v u d t x (WithLp.toLp 2 fun α => orderedDerivative α (fun y => a t y u) x)) k

end AVRegularity
