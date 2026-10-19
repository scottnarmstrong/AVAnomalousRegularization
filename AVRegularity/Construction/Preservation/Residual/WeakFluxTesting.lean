-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
public import AVRegularity.Definitions.Construction.Preparation
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep

/-! The readout residual only requires equality after testing fluxes against gradients.
This preserves the pointwise spatial integrability required by the weak identity
`CoupledWeakIdentity`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Construction.Preservation.Residual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Fluxes have the same tested divergence, with legitimate spatial integrals at every time. -/
def TestedFluxAgreement (μ : Measure (Vec 2)) (W : Set ℝ)
    (Q₁ Q₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (dφ : Fin 2 → Vec 2 → E) : Prop :=
  ∀ s ∈ W,
    Integrable (fun x => ∑ j : Fin 2, inner ℝ (Q₁ s x j) (dφ j x)) μ ∧
    Integrable (fun x => ∑ j : Fin 2, inner ℝ (Q₂ s x j) (dφ j x)) μ ∧
    (∫ x, ∑ j : Fin 2, inner ℝ (Q₁ s x j) (dφ j x) ∂μ) =
      ∫ x, ∑ j : Fin 2, inner ℝ (Q₂ s x j) (dφ j x) ∂μ

/-- Replace a flux by a flux with the same tested divergence. No pointwise flux equality or
choice of a divergence-free gauge is imposed. -/
theorem weakIdentity_of_tested_flux_agreement
    (μ : Measure (Vec 2)) (ν a t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (Q₁ F₁ Q₂ F₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hQ : TestedFluxAgreement μ (Set.Ioc a t) (fun s x => Q₁ s x + F₁ s x)
      (fun s x => Q₂ s x + F₂ s x) dφ)
    (h : CoupledWeakIdentity μ ν a t v u f φ dφ du Q₁ F₁ g) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du Q₂ F₂ g := by
  let R (Q F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (s : ℝ) (x : Vec 2) : ℝ :=
    -(∑ j : Fin 2, v s x j * inner ℝ (du s j x) (φ x)) -
      ν * ∑ j : Fin 2, inner ℝ (du s j x) (dφ j x) -
      ∑ j : Fin 2, inner ℝ (Q s x j + F s x j) (dφ j x) + inner ℝ (g s x) (φ x)
  let B (Q F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (s : ℝ) (x : Vec 2) : ℝ :=
    ∑ j : Fin 2, inner ℝ (Q s x j + F s x j) (dφ j x)
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ s ∈ Set.Ioc a t, Integrable (R Q₁ F₁ s) μ) ∧
    IntegrableOn (fun s => ∫ x, R Q₁ F₁ s x ∂μ) (Set.Ioc a t) ∧ _ at h
  have hb (s : ℝ) (hs : s ∈ Set.Ioc a t) :
      Integrable (B Q₁ F₁ s) μ ∧ Integrable (B Q₂ F₂ s) μ ∧
        (∫ x, B Q₁ F₁ s x ∂μ) = ∫ x, B Q₂ F₂ s x ∂μ := by
    simpa only [B, PiLp.add_apply] using hQ s hs
  have he (s : ℝ) : R Q₂ F₂ s = fun x => R Q₁ F₁ s x + B Q₁ F₁ s x - B Q₂ F₂ s x := by
    funext x
    dsimp only [R, B]
    ring
  have hp (s : ℝ) (hs : s ∈ Set.Ioc a t) : Integrable (R Q₂ F₂ s) μ := by
    rw [he]
    exact ((h.2.2.1 s hs).add (hb s hs).1).sub (hb s hs).2.1
  have hi (s : ℝ) (hs : s ∈ Set.Ioc a t) :
      (∫ x, R Q₁ F₁ s x ∂μ) = ∫ x, R Q₂ F₂ s x ∂μ := by
    rw [he]
    change (∫ x, R Q₁ F₁ s x ∂μ) =
      ∫ x, (R Q₁ F₁ s + B Q₁ F₁ s) x - B Q₂ F₂ s x ∂μ
    rw [integral_sub ((h.2.2.1 s hs).add (hb s hs).1) (hb s hs).2.1]
    change (∫ x, R Q₁ F₁ s x ∂μ) =
      (∫ x, R Q₁ F₁ s x + B Q₁ F₁ s x ∂μ) - ∫ x, B Q₂ F₂ s x ∂μ
    rw [integral_add (h.2.2.1 s hs) (hb s hs).1, (hb s hs).2.2]
    ring
  have ht : (fun s => ∫ x, R Q₁ F₁ s x ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun s => ∫ x, R Q₂ F₂ s x ∂μ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hi s hs
  exact ⟨h.1, h.2.1, hp, h.2.2.2.1.congr ht,
    h.2.2.2.2.trans (integral_congr_ae ht)⟩

/-- A chosen representative of the retained readout is the literal constant word sum.
Root casts and numerical birth factors are the same as in `succReadout`. -/
theorem readout_representative_eq {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {S S' : Finset Comp} {K : ℕ} (m : ℕ) (E η : ℝ)
    (Y : ∀ c : CompIn S', Sobolev.TorusHk K (hr c.1.root))
    (aY : ∀ c : CompIn S', Vec 2 → hr c.1.root)
    (aZ : ∀ v : CompIn S, Vec 2 → hr v.1.root)
    (hY : ∀ c, IsClassicalRep (Y c) (aY c) K)
    (hZ : ∀ v, IsClassicalRep (succReadout m E η K Y v) (aZ v) K)
    (v : CompIn S) :
    aZ v = fun x => ∑ c : CompIn S', if h : compParent m c.1 = v.1 then
      E ^ (η * (compWord m c.1).length) •
        cast (congrArg hr ((compParent_root m c.1).symm.trans (congrArg Comp.root h)))
          (aY c x) else 0 := by
  classical
  exact FullLift.classicalRep_unique _ _ _ (hZ v)
    (FullLift.readout_classicalRep (Nat.le_refl K) m E η Y aY hY v)

end AVRegularity.Construction.Preservation.Residual
