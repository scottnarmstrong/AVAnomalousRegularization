-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.PartitionGate
import AVRegularity.Applications.Construction.StreamTail

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon.Coeff

/-! # The drift clauses

Measurability and a uniform bound of `streamVel (D.Φ M)` on the window, from `IsOCStreamSeq`. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)

/-- The drift clauses of `ReconCoeffAt`. -/
theorem reconCoeff_stream (h128 : 128 ≤ A.Λ) :
    ∃ Vb : ℝ, (∀ s ∈ Set.Ioc c.tp (c.tp + rTobs c), ∀ k,
      AEStronglyMeasurable (fun y => streamVel (c.D.Φ M) s y k)
        (volume.restrict AVenhance.unitCube)) ∧
    ∀ s ∈ Set.Ioc c.tp (c.tp + rTobs c), ∀ y k, |streamVel (c.D.Φ M) s y k| ≤ Vb := by
  obtain ⟨-, -, -, -, hseq, -, -⟩ := c.data
  refine ⟨AVRegularity.Applications.velBound X.α X.q A.Λ, fun s _ k => ?_, fun s _ y k => ?_⟩
  · exact ((continuous_apply k).comp ((c.D.hΦ M).vel_continuous.comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (streamVel (c.D.Φ M) s y) k).trans
      (AVRegularity.Applications.streamVel_norm_le X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ
        X.hζ A.Λ h128 c.D.Φ hseq M s y)
end

/-! # Reduction of the coefficient bounds at a context

`ReconCoeffAt` follows from the drift clauses (proved in `Coeff/Stream.lean`) and the edge clauses
`ReconEdgeAt`, which are open. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)

/-- **Open.** The edge clauses of `ReconCoeffAt`: a uniform bound (in `s` of the window and all
`y`) and measurability of the edge coefficients of the actual family at the slots `rK c ℓ`. -/
def ReconEdgeAt (ℓ : ℕ) : Prop :=
  ∃ CA : ℝ, 0 ≤ CA ∧
    (∀ s ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ v u d y,
      ‖(edgeCoefficient c.Gw.actualFamily (c.D.κ M) (ocEpsilon c.D.q c.D.Λ M)
        (ocEpsilon c.D.q c.D.Λ (M - 1)) (fun _ => ()) (rK c ℓ)) v u d s y‖ ≤ CA) ∧
    ∀ s ∈ Set.Icc c.tp (c.tp + rTobs c), ∀ v u d,
      AEStronglyMeasurable ((edgeCoefficient c.Gw.actualFamily (c.D.κ M)
        (ocEpsilon c.D.q c.D.Λ M) (ocEpsilon c.D.q c.D.Λ (M - 1)) (fun _ => ()) (rK c ℓ)) v u d s)
        (volume.restrict AVenhance.unitCube)

/-- **The coefficient bounds at a context** from the edge clauses. -/
theorem reconCoeffAt_of_edge (h128 : 128 ≤ A.Λ) (ℓ : ℕ) (he : ReconEdgeAt c ℓ) :
    ReconCoeffAt c ℓ := by
  obtain ⟨Vb, hm, hb⟩ := reconCoeff_stream c h128
  obtain ⟨CA, hCA, he1, he2⟩ := he
  exact ⟨Vb, CA, hCA, hm, hb, he1, he2⟩
end

end AVRegularity.EntryTerminal.Ingredients.Recon.Coeff
end
