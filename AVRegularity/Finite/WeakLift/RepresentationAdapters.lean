-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.Readout.OperatorMap
public import AVRegularity.Definitions.EntryWeak.WeakReduction

/-! Order restriction and the mass-preserving weak encoding used by the finite lifts. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.Finite.WeakLift

theorem representationAt_order_mono {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {e : ℝ} {k K : ℕ} {r : Representation H} (hk : k ≤ K)
    (hr : IsRepresentationAt e K r) : IsRepresentationAt e k r := by
  refine ⟨hr.1, hr.2.1, hr.2.2.1.of_le (by exact_mod_cast hk), hr.2.2.2.1, ?_⟩
  intro p hp
  obtain ⟨hcd, hper, he, h1⟩ := hr.2.2.2.2 p hp
  exact ⟨hcd.of_le (by exact_mod_cast hk), hper, he, h1⟩

theorem representedSize_order_mono {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (s e : ℝ) {k K : ℕ} (hk : k ≤ K) (r : Representation H) :
    representedSize s k e r ≤ representedSize s K e r := by
  have hsemi (lam : ℝ) (F : Vec 2 → H) : profileSeminorm lam k s F ≤ profileSeminorm lam K s F := by
    unfold profileSeminorm
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro α hα
      simp only [multiIndicesBetween, Finset.mem_filter, Fintype.mem_piFinset,
        Finset.mem_range] at hα ⊢
      exact ⟨fun i => (hα.1 i).trans_le (Nat.add_le_add_right hk 1),
        hα.2.1, hα.2.2.trans hk⟩
    · intro _ _ _
      exact bot_le
  unfold representedSize
  apply add_le_add
  · exact add_le_add (add_le_add le_rfl (hsemi e r.base)) le_rfl
  · apply List.sum_le_sum
    intro p _
    unfold profileNorm
    exact add_le_add le_rfl (hsemi p.2 p.1)

theorem weak_encoding_mass {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ N J : ℕ} {η : ℝ}
    {G Gw : GenStage D ScalarH Dm b j₀} {law : BirthLaw}
    {ι : CompIn G.comps ≃ CompIn Gw.comps}
    (henc : IsWeakEncoding N J η law.rootMass law.rootReadout G Gw ι) (v : CompIn G.comps) :
    Gw.mass law (ι v) = weakMass D N J η v.1 := by
  change compMass D.q D.Λ law (ι v).1 = _
  unfold compMass
  rw [henc.2.1 v]
  simpa only [List.map_nil, List.prod_nil, mul_one] using (henc.2.2.1 v).1

theorem weak_encoding_representation {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ N J : ℕ} {η s e : ℝ}
    {G Gw : GenStage D ScalarH Dm b j₀} {law : BirthLaw}
    {ι : CompIn G.comps ≃ CompIn Gw.comps}
    (henc : IsWeakEncoding N J η law.rootMass law.rootReadout G Gw ι)
    (K : ℕ) (g : Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (r : Representation (CompSpace Gw.comps)) (hr : IsRepresentationAt e K r)
    (hvalue : r.value = compField (Gw.mass law) g) :
    IsRepresentationAt e K (r.map (compReindex ι.symm)) ∧
      (r.map (compReindex ι.symm)).value =
        compField (fun v : CompIn G.comps => weakMass D N J η v.1) (fun x v => g x (ι v)) ∧
      representedSize s K e (r.map (compReindex ι.symm)) ≤ representedSize s K e r := by
  refine ⟨Readout.representation_map_isRepresentationAt r _ hr, ?_, ?_⟩
  · rw [Readout.representation_map_value, hvalue]
    funext x
    apply compReindex_compField
    intro v
    simpa only [Equiv.apply_symm_apply] using (weak_encoding_mass henc (ι.symm v)).symm
  · calc
      _ ≤ ENNReal.ofReal ‖compReindex ι.symm‖ * representedSize s K e r :=
        Readout.representedSize_map_le r _ hr
      _ ≤ 1 * representedSize s K e r :=
        mul_le_mul' (by simpa only [ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (compReindex_norm_le ι.symm)) le_rfl
      _ = _ := one_mul _

end AVRegularity.Finite.WeakLift
