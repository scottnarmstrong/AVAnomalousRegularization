-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.First.Identity
public import AVRegularity.Proofs.GenSem.Finer.CovLetterRep
import AVRegularity.Proofs.GenSem.Op.FamChart

/-! **D6c: family jets of the push-forward arrays of the appended children.** From the lift setup
of the grade-zero lifts `Cc0 k` (no edges) on a family `𝒜` of base chains over the finer slot `k`,
the push-forward arrays `diagChildArr` of every degree `n ≥ 1` have represented family jets on
`liftFamW`, hence on any subset of it, in particular on the appended children `childW` of the
contexts (`arrJetG_diagChild`). This discharges the hypothesis `hchild` of `firstSource_ctxRep`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev Set

namespace AVRegularity.Providers.GenSem

/-- Family-represented functions restrict to subsets of the index set. -/
theorem famAlg_restrict {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {p : ℤ}
    {W W' : Set (ℝ × RealChain)} (hWW : W' ⊆ W) (F : W → ℝ)
    (hF : famAlg D bw j₀ 𝒮 i p W F) :
    famAlg D bw j₀ 𝒮 i p W' (fun q' => F ⟨q'.1, hWW q'.2⟩) := by
  obtain ⟨G, hG, c, hs, hf, fc, hd, hv⟩ := hF
  exact ⟨G, fun q' => hG _, c, hs, hf, fc, hd, fun q hq => hv q (hWW hq)⟩

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain}
  {ρ : ℝ} {Dm : ℕ} {U : RealChain → Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N : ℕ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

namespace LiftGenSetup

/-- **Family jets of the push-forward arrays of the grade-zero label fluxes**, on any subset `W'`
of the lift index set. -/
theorem arrJetG_diagChild
    (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ
      (fun _ => (fun _ _ _ => [] : ConstituentEdges Dm (fun _ : Fin 1 => ℝ))) U sX sZ t₀ t₁ N 0 (Cc0 k))
    (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) {n : ℕ} (hn1 : 1 ≤ n) (r : ℕ)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁, LiftRegular (diagQ D Dm m k A ρ) (Cc0 k A) 0 τ 0 n
      (max r n + Dm + 2))
    {W' : Set (ℝ × RealChain)} (hW' : W' ⊆ liftFamW D m 𝒜 t₀ t₁) (c : Fin 2) :
    ArrJetG (famAlg D bw j₀ 𝒮 m k W') r
      (fun q => diagChildArr D Dm m ρ Cc0 k n q.1.1 q.1.2 c) := by
  have hR := repAlg_famAlg D bw j₀ 𝒮 m k (liftFamW D m 𝒜 t₀ t₁)
  have hWS : ∀ q ∈ liftFamW D m 𝒜 t₀ t₁, q.2.WellSlotted := fun q hq => (hS.hA q.2 hq.1).1
  have hP : ∀ κ, ArrJetG (famAlg D bw j₀ 𝒮 m k (liftFamW D m 𝒜 t₀ t₁)) r (fun q =>
      pmArr D m ρ (diagQ D Dm m k q.1.2 ρ) (Cc0 k q.1.2) n q.1.1 κ) := fun κ j α =>
    ⟨jetRep_toG (hS.jetRep_pmArr' h0 le_rfl hn1
        (fun A hA τ hτ => (hregn A hA τ hτ).mono le_rfl le_rfl (by omega)) κ j α r),
      fun q => contDiff_pmArr D m ρ _ _ n q.1.1 κ
        ((hregn q.1.2 q.2.1 _ q.2.2).mono le_rfl le_rfl (by omega)) j α⟩
  have hB := arrJetG_push_famMap (K := n) hS.hζ hWS hP c
  exact ArrJetG.comap (fun q' : W' => (⟨q'.1, hW' q'.2⟩ : liftFamW D m 𝒜 t₀ t₁))
    (fun F hF => famAlg_restrict hW' F hF) hB

end LiftGenSetup

end AVRegularity.Providers.GenSem
