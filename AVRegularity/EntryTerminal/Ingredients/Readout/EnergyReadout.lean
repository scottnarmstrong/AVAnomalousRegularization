-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.Finite.Assembly.TerminalLiftProfileBoundsOfIngredients
import AVRegularity.CycleComparison.Error.Main

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.EntryTerminal.Route

/-! Assemble the terminal identity from pointwise control by the strong energy. -/

/-- The retained Sobolev norm at a time in the window is bounded by strong energy.
No sign condition on component masses is needed: negative real contributions are
clamped in the extended nonnegative energy, and zero masses contribute zero. -/
def TerminalReadoutEnergyStatement : Prop :=
  ∀ (S : Finset Comp) (K L : ℕ) (hLK : L ≤ K) (ρ B t₀ t₁ : ℝ)
    (π : CompIn S → ℝ)
    (u : ∀ v : CompIn S, ℝ → TorusHk K (ScalarH v.1.root))
    (w : ∀ v : CompIn S, ℝ → TorusHk (K + 1) (ScalarH v.1.root))
    (t : ℝ), t ∈ Set.Icc t₀ t₁ →
    ENNReal.ofReal (weightedNorm ρ π (fun _ => 1)
      (fun v => truncateTorusHk hLK (u v t))) ≤ strongEnergy ρ B π t₀ t₁ u w

private theorem readout_mono {s A B : ℝ} {f : Vec 2 → ℝ}
    (hf : CsNormLe s f A) (hAB : A ≤ B) : CsNormLe s f B :=
  fun x y z h => (hf x y z h).trans hAB

private theorem readout_price {A N R C E n : ℝ} (hN : 0 ≤ N) (hn : 0 ≤ n)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hNR : N ≤ R * n) (hscale : A * R ≤ C * E) :
    A * N ≤ C * E * n := by
  by_cases hA : 0 ≤ A
  · calc
      A * N ≤ A * (R * n) := mul_le_mul_of_nonneg_left hNR hA
      _ = (A * R) * n := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale hn
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hA) hN).trans
      (mul_nonneg (mul_nonneg hC hE) hn)

/-- The readout glue follows from the closed pointwise energy inequality and existing representation lemmas. -/
theorem readoutGlue_of_ingredients (hpointwise : TerminalReadoutEnergyStatement) :
    ReadoutGlueStatement := by
  intro D Dm b j₀ Gw Gt law M Jw Lw Kw k₀ pT Khat NT depth sX sZ hk₀w
    κ a τ T₀ s Pw PT QT cK Cread Cid CE C tp η₀ cr f θ Ww V Vw Z
    he hE _hτ hLk hCE hC hweak hscale hCid hlift henergy
  refine ⟨hlift.1, ?_⟩
  intro CcT PZ aRep û₀ hû₀ t ht aV haV
  obtain ⟨û, ŵ, hû, hgrad, hrep⟩ := hlift.2 CcT PZ aRep û₀ hû₀
  let u := fun v t => truncateTorusHk hk₀w (V v t) - û v t
  let w := fun v t => truncateTorusHk (Nat.succ_le_succ hk₀w) (Vw v t) - ŵ v t
  let z := fun v => truncateTorusHk hLk (u v t)
  let alift := fun v x => termLiftedRep Gw M NT depth cr CcT aRep t x v
  have hz : ∀ v, IsClassicalRep (z v) (fun x => aV v x - alift v x) (Lw + 3) := by
    intro v
    exact classicalRep_truncate hLk (by omega) _ _
      (CycleComparison.Reconstruction.isClassicalRep_sub
        (classicalRep_truncate hk₀w (by omega) _ _ (haV v)) (hrep v t ht))
  have hR : 0 ≤ CE * D.eps (M - 1) ^ (QT / 2) * Real.sqrt (l2NormSq f) :=
    mul_nonneg (mul_nonneg hCE (Real.rpow_nonneg hE.le _)) (Real.sqrt_nonneg _)
  have hnorm : weightedNorm (D.termRStar cK M) (Gw.mass law) (fun _ => 1) z ≤
      CE * D.eps (M - 1) ^ (QT / 2) * Real.sqrt (l2NormSq f) :=
    (ENNReal.ofReal_le_ofReal_iff hR).mp
      ((hpointwise Gw.comps k₀ (Lw + 5) hLk _ _ tp (a + T₀) (Gw.mass law) u w t ht).trans
        (henergy CcT PZ aRep û ŵ hû hgrad))
  have hfirst : CsNormLe s (Ww t (fun v x => aV v x - alift v x))
      (C * D.eps (M - 1) ^ PT * Real.sqrt (l2NormSq f)) :=
    readout_mono (hweak.2.2.1 t z _ hz)
      (readout_price (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hC
        (Real.rpow_nonneg hE.le _) (by simpa only [mul_assoc] using hnorm) hscale)
  refine ⟨hfirst, ?_⟩
  intro hlate
  obtain ⟨Θ, hperiodic, hθ, hweakid⟩ := hweak.2.2.2 t ⟨hlate, ht.2⟩ aV haV
  refine ⟨Θ, hperiodic, hθ, ?_⟩
  have hid := readout_mono hweakid (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCid (Real.rpow_nonneg he.le _)) (Real.sqrt_nonneg _))
  have hsum := Finite.Assembly.csNormLe_add hid hfirst
  -- the readout is linear on `C^{L_w+3}` fields; both are classical representatives
  have hmap : Ww t (fun v x => aV v x - alift v x) = Ww t aV - Ww t alift := by
    have hlin := hweak.2.1 t aV alift (-1) (fun v => (haV v).2.1) (fun v => (hrep v t ht).2.1)
    have hf : (fun v x => aV v x - alift v x) = fun v => aV v + (-1 : ℝ) • alift v := by
      funext v x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg]
    rw [hf, hlin, neg_one_smul, sub_eq_add_neg]
  rw [hmap] at hsum
  have hfun : (fun x => (Θ x - Ww t aV x) + (Ww t aV - Ww t alift) x) =
      (fun x => Θ x - Ww t alift x) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hfun] at hsum
  convert hsum using 1
  ring

end AVRegularity.EntryTerminal.Route
end
end

section
public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.EntryTerminal.Route

/-! Pointwise retained norms are controlled by the extended strong energy. -/

private theorem readout_ofReal_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, ENNReal.ofReal_zero, le_refl]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

private theorem readout_ofReal_sqrt (x : ℝ) :
    ENNReal.ofReal (Real.sqrt x) = ENNReal.ofReal x ^ (1 / 2 : ℝ) := by
  by_cases hx : 0 ≤ x
  · rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx), ENNReal.ofReal_zero,
      ENNReal.ofReal_of_nonpos (le_of_not_ge hx), ENNReal.zero_rpow_of_pos (by norm_num)]

/-- The pointwise energy inequality remains valid for zero or negative masses. -/
theorem terminalReadoutEnergy : TerminalReadoutEnergyStatement := by
  intro S K L hLK ρ B t₀ t₁ π u w t ht
  unfold weightedNorm strongEnergy
  rw [readout_ofReal_sqrt]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  unfold massNormSq
  simp only [one_pow, div_one]
  refine (readout_ofReal_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro v _
  rw [ENNReal.ofReal_mul' (factorialNormSq_nonneg _ _)]
  apply mul_le_mul_of_nonneg_left _ bot_le
  calc
    ENNReal.ofReal (factorialNormSq ρ (truncateTorusHk hLK (u v t)).val) ≤
        ENNReal.ofReal (factorialNormSq ρ (u v t).val) :=
      ENNReal.ofReal_le_ofReal (CycleComparison.Error.factorialNormSq_truncateTorusHk_le hLK ρ _)
    _ ≤ ⨆ s ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (u v s).val) :=
      le_iSup_of_le t (le_iSup_of_le ht le_rfl)
    _ ≤ _ := le_add_of_nonneg_right bot_le

/-- The revised terminal readout glue, with its pointwise energy ingredient discharged. -/
theorem readoutGlue : ReadoutGlueStatement :=
  readoutGlue_of_ingredients terminalReadoutEnergy

end AVRegularity.EntryTerminal.Route
end
end
