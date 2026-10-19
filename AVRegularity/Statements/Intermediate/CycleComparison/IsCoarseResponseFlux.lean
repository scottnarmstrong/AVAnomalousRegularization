-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CycleComparison.CellInner
public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseFluxAdjoint
public import AVRegularity.Statements.Intermediate.CycleComparison.EdgeFluxAdjoint
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyQ
public import AVenhance.Statements.Roots.IsZ2Periodic

/-! The forcing flux of a response of the coarse family, `G = -𝖰_p F_p U' + 𝖰_p F_E 𝖯_p U''`, so
that the responses solve `L_c U_{i,h} = div(-𝖰_p F_p U_{i-1,h} + 𝖰_p F_E 𝖯_p U_{i,h-1})`. The
operators `F_p`, `F_E`, `𝖯_p`, `𝖰_p` act on `L²` fields; they are defined by duality against smooth
periodic flux test fields (an object characterized by an equation is stated as a relation). `G` is a
Sobolev flux of order `K`; `U'`, `U''` are the value representatives of the two previous responses
(`U_{i-1,h}`, `U_{i,h-1}`; zero when the index is negative). Pairing is the unweighted `L²(𝕋²;𝗁_v)`
inner product, componentwise; the masses enter only the norms. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- For every `s ∈ [t₀,t₁]` and every smooth periodic flux test `ψ`:
`∑_v ⟨G_v(s), ψ_v⟩ = -∑_v ⟨U'_v(s), (F_p(s)^* 𝖰_p(s) ψ)_v⟩ + ∑_u ⟨U''_u(s), 𝖯_p(s) (F_E(s)^* 𝖰_p(s) ψ)_u⟩`,
with `H_cov(s) = Hcov s`. -/
def IsCoarseResponseFlux {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (t₀ t₁ : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H p : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (K : ℕ)
    (G : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v)))
    (U' U'' : ∀ v, ℝ → Vec 2 → h v) : Prop :=
  ∀ s ∈ Set.Icc t₀ t₁, ∀ ψ : ∀ v, Vec 2 → PiLp 2 (fun _ : Fin 2 => h v),
    (∀ v, ContDiff ℝ (⊤ : ℕ∞) (ψ v)) → (∀ v, AVenhance.IsZ2Periodic (ψ v)) →
    ∑ v, cellInner (fun x => (G v s).toFunction.jet (valueIndex2 K) x) (ψ v)
      = ∑ v, cellInner (U' v s) (fun x => -(coarseFluxAdjoint D b AD (Hcov s) p s
            (covPolyQ (Hcov s) p (ψ v)) x))
        + ∑ u, cellInner (U'' u s) (covPolyP (Hcov s) p
            (edgeFluxAdjoint D H CE s (fun v => covPolyQ (Hcov s) p (ψ v)) u))

end AVRegularity
