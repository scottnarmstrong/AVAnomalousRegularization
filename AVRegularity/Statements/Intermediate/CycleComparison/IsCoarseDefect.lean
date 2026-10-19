-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseDefectFlux
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledWeakIdentity

/-! The exact defect identity `(M I - E) W = div F_coarse` with `W(t₀) = f`, in the integrated
`L²`-duality form `CoupledWeakIdentity` of the coupled energy estimate `coupled_energy_torus`, for
the equation `(∂_t + 𝐛·∇ - BΔ) W = div(flux + F_coarse)` with `flux = coarseDefectFlux`: at every
`v`, every time `t ∈ [t₀,t₁]` and every `H¹` test `φ`. At `t = t₀` it states `⟨W(t₀), φ⟩ = ⟨f, φ⟩`.
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `W` solves `(M I - E) W = div Fc` on `[t₀,t₁]` with initial value `f`. -/
def IsCoarseDefect {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (t₀ t₁ B : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H k N : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (f : ∀ v, TorusHk N (h v))
    (W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v))
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc t₀ t₁, ∀ φ : TorusHk 1 (h v),
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) B t₀ t b
      ((W v t).toFunction.jet (valueIndex2 (k + 1 + D)))
      ((f v).toFunction.jet (valueIndex2 N))
      (φ.toFunction.jet (valueIndex2 1))
      (fun k' => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k'⟩)
      (fun s k' => torusJetOrder (W v s) 1 (fun _ => k'))
      (fun s x => coarseDefectFlux B D H AD CE Jm W v s x)
      (fun s => (Fc v s).toFunction.jet (valueIndex2 k))
      (fun _ _ => 0)

end AVRegularity
