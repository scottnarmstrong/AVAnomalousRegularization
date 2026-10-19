-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Uniqueness.SuccessorFluxUnique
public import AVRegularity.Statements.Construction.IsFastProfile
import Mathlib.Algebra.Order.Star.Real

/-! `successor_flux_unique` (the statement of the paper) from the window
data `succ_window_data`: the positive diffusivities give `0 ≤ cellScaleSq`, and the window bounds
of `AVRegularity.SuccWindowData` are the window data of the cell uniqueness argument. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.Uniqueness

open AVRegularity

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem windowData_of_isCellWindowBound {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {a b lo A Mv : ℝ} (h : IsCellWindowBound G v a b lo A Mv) :
    WindowData G v a b lo A Mv :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem succWindowData_of_target {Mn : SuccMenu} {G : GenStage D hr Dm b j₀}
    (hW : AVRegularity.SuccWindowData D b j₀ Mn G) : Uniqueness.SuccWindowData D b j₀ Mn G :=
  fun h π k A hA X => by
    obtain ⟨lo, A', Mv, hb⟩ := hW h π k A hA X
    exact ⟨lo, A', Mv, windowData_of_isCellWindowBound hb⟩

theorem cellScaleSq_nonneg_of_kappa_pos (hκ : ∀ i, 0 < D.κ i) (m : ℕ) :
    0 ≤ D.cellScaleSq m := by
  unfold OCData.cellScaleSq OCData.kap
  exact div_nonneg (sq_nonneg _) (hκ _).le

/-- **`successor_flux_unique` given the window data** (the paper statement plus the
conclusion of `succ_window_data`). -/
theorem successor_flux_unique_of_succ_window_data (P : ProvParams)
    (_hζ : IsFastProfile D.ζ) (hκ : ∀ i, 0 < D.κ i)
    (Mn : SuccMenu) (M : ℕ) (G G₁ G₂ : GenStage D hr Dm b j₀) (hnat : G.IsNatural M)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (h₁ : IsActualSuccessor D P Mn G G₁)
    (h₂ : IsActualSuccessor D P Mn G G₂) (v₁ u₁ : CompIn G₁.comps) (γ₁ : G₁.fam.Γ v₁ u₁)
    (v₂ u₂ : CompIn G₂.comps) (γ₂ : G₂.fam.Γ v₂ u₂) (hv : v₁.1 = v₂.1) (hu : u₁.1 = u₂.1)
    (hγ : G₁.prov v₁ u₁ γ₁ = G₂.prov v₂ u₂ γ₂)
    (hnd : ∀ m', G₁.prov v₁ u₁ γ₁ ≠ Prov.letter m' .diag []) (p : OddSlot)
    (c₁ : StageCtx D b j₀ G₁.level p) (c₂ : StageCtx D b j₀ G₂.level p) (hc : c₁.1 = c₂.1)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2) (hd : 2 ≤ d)
    (hW : AVRegularity.SuccWindowData D b j₀ Mn G)
    (hΩ : ∀ k A, IsAdmissibleChain D b j₀ G.level k A →
      IsOpen (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) ∧
        (0 : Vec 2) ∈ ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level))
    (hΦ : ∀ (A : RealChain) (t : ℝ), ContinuousAt (A.famMapInv D t) 0 ∧ A.famMapInv D t 0 = 0) :
    G₁.fam.flux p c₁ v₁ u₁ γ₁ d I t X z = G₂.fam.flux p c₂ v₂ u₂ γ₂ d I t X z := by
  exact successor_flux_unique_of_window_data P Mn M G G₁ G₂ hnat hold h₁ h₂ v₁ u₁ γ₁ v₂ u₂ γ₂
    hv hu hγ hnd p c₁ c₂ hc d I t X z hd (cellScaleSq_nonneg_of_kappa_pos hκ _)
    (succWindowData_of_target hW) hΩ hΦ

end AVRegularity.Uniqueness
