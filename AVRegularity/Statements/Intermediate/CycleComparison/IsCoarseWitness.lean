-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.FamilyValueSum
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseResponseFlux

/-! The retained field `W = 𝖯_p A_sum` and the coarse flux
`F_coarse` of the coarse family as relations:
`A_sum = ∑_{i,h} U_{i,h}`, `W = 𝖯_p A_sum`,
`G_ret = F_p ∑_{i<J,h} U_{i,h} - F_E 𝖯_p ∑_{i,h<H} U_{i,h}`,
`G_end = F_p ∑_h U_{J,h} - F_E 𝖯_p ∑_i U_{i,H}`,
`F_coarse = (I - 𝖯_p 𝖰_p) G_ret + G_end - (𝖩 - B I) ∇ (𝒞^p/p!) A_sum`.
The operators act on `L²` fields, so `W` and `F_coarse` are the unique Sobolev fields (orders
`k + 1 + D` and `k`) whose pairings with every smooth periodic test field equal the dual
expressions. The dual of `(𝖩 - B I)∇(𝒞^p/p!)` against a vector test `ψ` is
`(𝒞^p/p!) ∑_{k,l} (𝖩 - B I)_{kl} ∂_l ψ_k` with a minus sign. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `W` and `Fc` are the `𝖯_p`-image of the total response and the retained flux of the family `U`. -/
def IsCoarseWitness {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (t₀ t₁ B : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H p k J L : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v))
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) : Prop :=
  (∀ t ∈ Set.Icc t₀ t₁, ∀ φ : ∀ v, Vec 2 → h v,
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v)) → (∀ v, AVenhance.IsZ2Periodic (φ v)) →
      ∑ v, cellInner (fun x => (W v t).toFunction.jet (valueIndex2 (k + 1 + D)) x) (φ v)
        = ∑ v, cellInner
            (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v t)
            (covPolyP (Hcov t) p (φ v))) ∧
  (∀ s ∈ Set.Icc t₀ t₁, ∀ ψ : ∀ v, Vec 2 → PiLp 2 (fun _ : Fin 2 => h v),
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (ψ v)) → (∀ v, AVenhance.IsZ2Periodic (ψ v)) →
      ∑ v, cellInner (fun x => (Fc v s).toFunction.jet (valueIndex2 k) x) (ψ v)
        = (∑ v, cellInner
              (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s)
              (coarseFluxAdjoint D b AD (Hcov s) p s
                (ψ v - covPolyQ (Hcov s) p (covPolyP (Hcov s) p (ψ v))))
            - ∑ u, cellInner
              (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
              (covPolyP (Hcov s) p (edgeFluxAdjoint D H CE s
                (fun v => ψ v - covPolyQ (Hcov s) p (covPolyP (Hcov s) p (ψ v))) u)))
        + (∑ v, cellInner
              (familyValueSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s)
              (coarseFluxAdjoint D b AD (Hcov s) p s (ψ v))
            - ∑ u, cellInner
              (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s)
              (covPolyP (Hcov s) p (edgeFluxAdjoint D H CE s ψ u)))
        + ∑ v, cellInner
            (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s)
            ((p.factorial : ℝ)⁻¹ • (covOperator (Hcov s))^[p]
              (fun x => ∑ k' : Fin 2, ∑ l : Fin 2,
                (Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) •
                  fderiv ℝ (fun y => ψ v y k') x (basisVec l))))

end AVRegularity
