-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.TorusJetOrder

/-! The total flux of the retained equation `(M I - E) W = div F_coarse` written in the form of the
coupled energy estimate `coupled_energy_torus`, `(∂_t + 𝐛·∇ - BΔ) W = div(flux + F_coarse)`: since
`𝖩` is spatially constant, `-𝖩:D² W = -B ΔW - div((𝖩 - B I)∇W)`, so
`flux = (𝖩 - B I)∇W + F_A W + F_E W`, with `F_A W = ∑_d A_d ∇^{d-1} W` (scalar `A_d` acting
diagonally) and `(F_E W)_v = ∑_{r=1}^H ∑_{u,d} C^{[r]}_{vu,d} ∇^{d-1} W_u`, read from the weak jets
of the order-`K` field `W` (`K ≥ D - 1`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The `v`-component of `(𝖩 - B I)∇W + F_A W + F_E W` at time `s`, position `x`. -/
def coarseDefectFlux {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (B : ℝ) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (v : ι) (s : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h v) :=
  WithLp.toLp 2 fun k =>
    (∑ l : Fin 2, (Jm s k l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k l) •
        torusJetOrder (W v s) 1 (fun _ => l) x)
    + (∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
        (AD d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) • torusJetOrder (W v s) (d.1 - 1) α x)
    + (∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
        (CE r v u d s x (WithLp.toLp 2 fun α => torusJetOrder (W u s) (d.1 - 1) α x)) k)

end AVRegularity
