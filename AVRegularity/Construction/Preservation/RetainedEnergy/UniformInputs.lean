-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
public import AVRegularity.Definitions.Construction.ResidualOps
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.KernelEnergy.TorusKernelComponentSup
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.RetainedEnergy

/-! The normalized coefficient of a nonempty birth word retains its small mass factor.
This is independent of the number of root components and of their dimensions. -/

section
open FullLift

/-- The extra half birth exponent is present before counting the word menu. -/
theorem fresh_readout_entry_le {q η : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (hcH : law.cH ≤ 1) (hη : 0 ≤ η)
    (m : ℕ) (c : Comp) (hfresh : compWord m c ≠ []) :
    (Real.sqrt (compMass q Λ law (compParent m c)))⁻¹ /
        (Real.sqrt (compMass q Λ law c))⁻¹ *
      ocEpsilon q Λ (m - 1) ^ (η * (compWord m c).length) ≤
        ocEpsilon q Λ (m - 1) ^ (η + law.etaB / 2) := by
  let E := ocEpsilon q Λ (m - 1)
  have he := Scales.epsilon_basic (m := m - 1) hq hΛ
  have hparent := Buffer.birth_compMass_pos hq hΛ law (compParent m c)
  have hmass : compMass q Λ law c / compMass q Λ law (compParent m c) =
      law.cH / (law.wordCount : ℝ) * E ^ law.etaB := by
    nth_rw 1 [← succComp_parent_word m c]
    rw [succComp_mass law _ hfresh]
    exact mul_div_cancel_right₀ _ hparent.ne'
  have hratio : law.cH / (law.wordCount : ℝ) ≤ 1 := by
    apply (div_le_one₀ (by exact_mod_cast law.wordCount_pos)).mpr
    exact hcH.trans (by exact_mod_cast law.wordCount_pos)
  have hroot : Real.sqrt (compMass q Λ law c / compMass q Λ law (compParent m c)) ≤
      E ^ (law.etaB / 2) := by
    calc
      _ ≤ Real.sqrt (E ^ law.etaB) := by
        apply Real.sqrt_le_sqrt
        rw [hmass]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio
          (Real.rpow_nonneg he.1.le _)
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul he.1.le]
        congr 1
        ring
  have hword : E ^ (η * (compWord m c).length) ≤ E ^ η := by
    apply Real.rpow_le_rpow_of_exponent_ge he.1 he.2.1
    have hlen : (1 : ℝ) ≤ (compWord m c).length := by
      exact_mod_cast List.length_pos_iff.mpr hfresh
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlen hη
  have hdiag : (Real.sqrt (compMass q Λ law (compParent m c)))⁻¹ /
      (Real.sqrt (compMass q Λ law c))⁻¹ =
      Real.sqrt (compMass q Λ law c / compMass q Λ law (compParent m c)) := by
    simpa only [one_mul, div_self (by norm_num : (1 : ℝ) ≠ 0), mul_one] using
      inverse_mass_diagonal_ratio (Buffer.birth_compMass_pos hq hΛ law c).le 1 1
  rw [hdiag]
  calc
    _ ≤ E ^ (law.etaB / 2) * E ^ η := mul_le_mul hroot hword
      (Real.rpow_nonneg he.1.le _) (Real.rpow_nonneg he.1.le _)
    _ = E ^ (η + law.etaB / 2) := by
      rw [← Real.rpow_add he.1]
      congr 1
      ring
end

/-! The fixed birth constant controls the mass of the entire cascade.
The potential proof includes the last passage, where epsilon at level zero is one. -/

section
open FullLift

private theorem epsilon_power_geometric {q η : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hη : 0 ≤ η) (k : ℕ) :
    ocEpsilon q Λ k ^ η ≤ ((128 : ℝ) ^ (-η)) ^ k := by
  induction k with
  | zero => simp [ocEpsilon]
  | succ k ih =>
    have he := Scales.epsilon_basic (m := k + 1) hq hΛ
    have hratio := Scales.epsilon_ratio_lower (m := k + 1) hq hΛ (by omega)
    have hsep : ocEpsilon q Λ (k + 1) ≤ ocEpsilon q Λ k / 128 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 128)]
      have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
      have hh : (Λ : ℝ) * ocEpsilon q Λ (k + 1) ≤ ocEpsilon q Λ k := by
        simpa only [Nat.add_sub_cancel] using (le_div_iff₀ he.1).mp hratio
      simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hΛr he.1.le).trans hh
    calc
      _ ≤ (ocEpsilon q Λ k / 128) ^ η := Real.rpow_le_rpow he.1.le hsep hη
      _ = ocEpsilon q Λ k ^ η * (128 : ℝ) ^ (-η) := by
        rw [Real.div_rpow (Scales.epsilon_basic hq hΛ).1.le (by norm_num),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 128), div_eq_mul_inv]
      _ ≤ ((128 : ℝ) ^ (-η)) ^ k * (128 : ℝ) ^ (-η) :=
        mul_le_mul_of_nonneg_right ih (Real.rpow_nonneg (by norm_num) _)
      _ = _ := (pow_succ _ _).symm

private theorem extended_mass_sum {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (A : Finset WordLetter) (J m : ℕ)
    (hTw : law.wordCount = (wordsUpTo A (J + 1)).card) (S : Finset Comp) :
    (∑ c ∈ succExtComps m A J S, compMass q Λ law c) ≤
      (1 + law.cH * ocEpsilon q Λ (m - 1) ^ law.etaB) *
        ∑ v ∈ S, compMass q Λ law v := by
  classical
  let W := wordsUpTo A (J + 1)
  let f := compMass q Λ law
  have hf (v : Comp) : 0 ≤ f v := (Buffer.birth_compMass_pos hq hΛ law v).le
  have hu : (∑ c ∈ S ∪ (S ×ˢ W).image (fun x => succComp m x.1 x.2), f c) ≤
      (∑ c ∈ S, f c) + ∑ c ∈ (S ×ˢ W).image (fun x => succComp m x.1 x.2), f c := by
    have hi := Finset.sum_union_inter (s₁ := S)
      (s₂ := (S ×ˢ W).image (fun x => succComp m x.1 x.2)) (f := f)
    have hn := Finset.sum_nonneg (s := S ∩ (S ×ˢ W).image (fun x => succComp m x.1 x.2))
      (fun v _ => hf v)
    linarith only [hi, hn]
  have him := Finset.sum_image_le_of_nonneg (s := S ×ˢ W)
    (g := fun x : Comp × List WordLetter => succComp m x.1 x.2) (fun v _ => hf v)
  have hp : (∑ x ∈ S ×ˢ W, f (succComp m x.1 x.2)) =
      law.cH * ocEpsilon q Λ (m - 1) ^ law.etaB * ∑ v ∈ S, f v := by
    rw [Finset.sum_product]
    have hword (v : Comp) (t : List WordLetter) (ht : t ∈ W) :
        f (succComp m v t) =
          (law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (m - 1) ^ law.etaB) * f v := by
      apply succComp_mass law v
      exact List.length_pos_iff.mp (Providers.CascadeInvariants.length_of_mem_wordsUpTo ht).1
    simp_rw [Finset.sum_congr rfl (fun t ht => hword _ t ht), Finset.sum_const, nsmul_eq_mul]
    have hcancel (v : Comp) : (W.card : ℝ) *
        (law.cH / law.wordCount * ocEpsilon q Λ (m - 1) ^ law.etaB * f v) =
        law.cH * ocEpsilon q Λ (m - 1) ^ law.etaB * f v := by
      rw [show (W.card : ℝ) = law.wordCount from congrArg Nat.cast hTw.symm]
      field_simp [ne_of_gt (show (0 : ℝ) < law.wordCount by exact_mod_cast law.wordCount_pos)]
    simp_rw [hcancel]
    exact (Finset.mul_sum _ _ _).symm
  change (∑ c ∈ S ∪ (S ×ˢ W).image (fun x => succComp m x.1 x.2), f c) ≤ _
  calc
    _ ≤ (∑ c ∈ S, f c) + ∑ x ∈ S ×ˢ W, f (succComp m x.1 x.2) :=
      hu.trans (add_le_add le_rfl him)
    _ = _ := by rw [hp]; ring

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Total mass stays within twice the seed mass, including an empty seed and level zero. -/
theorem cascade_mass_sum_le_twice (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (law : BirthLaw) (hη : 0 < law.etaB)
    (hcH : law.cH = (1 - (128 : ℝ) ^ (-law.etaB)) / 2)
    (P : ProvParams) (Mn : SuccMenu)
    (hTw : law.wordCount = (wordsUpTo Mn.A (Mn.J + 1)).card)
    (seed G : GenStage D hr Dm bw j₀) (hc : IsCascadeStage D P Mn seed G) :
    (∑ v, G.mass law v) ≤ 2 * ∑ v, seed.mass law v := by
  classical
  let r := (128 : ℝ) ^ (-law.etaB)
  let F := fun k : ℕ => 1 - r ^ k / 2
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hη.le)
  have hF (k : ℕ) : 1 / 2 ≤ F k ∧ F k ≤ 1 := by
    have hpow := pow_le_one₀ hr0 hr1 (n := k)
    have hp0 := pow_nonneg hr0 k
    dsimp only [F]
    constructor <;> linarith only [hpow, hp0]
  have hpot : ∀ G : GenStage D hr Dm bw j₀, IsCascadeStage D P Mn seed G →
      F G.level * (∑ v, G.mass law v) ≤ ∑ v, seed.mass law v := by
    intro G hG
    induction hG with
    | seed =>
      exact (mul_le_mul_of_nonneg_right (hF seed.level).2
        (Finset.sum_nonneg fun v _ => (Buffer.birth_compMass_pos hq hΛ law v.1).le)).trans_eq
          (one_mul _)
    | @step G G' hcascade hsucc ih =>
      have hstep : (∑ v, (G'.retained G.level Mn.H Mn.J).mass law v) ≤
          (1 + law.cH * r ^ (G.level - 1)) * ∑ v, G.mass law v := by
        have hsub : (G'.retained G.level Mn.H Mn.J).comps ⊆ succExtComps G.level Mn.A Mn.J G.comps := by
          rw [GenStage.retained, GenStage.restrict]
          exact fun c hc => hsucc.2.2.1 ▸ (Finset.mem_filter.mp hc).1
        have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun c _ _ => (Buffer.birth_compMass_pos hq hΛ law c).le)
        have he := extended_mass_sum hq hΛ law Mn.A Mn.J G.level hTw G.comps
        have heps := epsilon_power_geometric hq hΛ hη.le (G.level - 1)
        have hmass := Finset.sum_nonneg (fun v (_ : v ∈ G.comps) =>
          (Buffer.birth_compMass_pos hq hΛ law v).le)
        have hmul := mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ))
          (mul_le_mul_of_nonneg_left heps law.cH_pos.le)) hmass
        simpa only [GenStage.mass, Finset.sum_coe_sort] using hs.trans (he.trans hmul)
      have hlev : (G'.retained G.level Mn.H Mn.J).level = G.level - 1 := hsucc.2.1
      have hfactor : F (G.level - 1) * (1 + law.cH * r ^ (G.level - 1)) ≤ F G.level := by
        have hpositive := hsucc.1
        have hk : G.level - 1 + 1 = G.level := by omega
        have hpow := congrArg (fun k => r ^ k) hk
        rw [pow_succ] at hpow
        dsimp only [F]
        rw [← hpow, hcH]
        change (1 - r ^ (G.level - 1) / 2) * (1 + (1 - r) / 2 * r ^ (G.level - 1)) ≤
          1 - r ^ (G.level - 1) * r / 2
        have hn : 0 ≤ (1 - r) * (r ^ (G.level - 1)) ^ 2 :=
          mul_nonneg (sub_nonneg.mpr hr1) (sq_nonneg _)
        nlinarith only [hn]
      rw [hlev]
      calc
        _ ≤ F (G.level - 1) * ((1 + law.cH * r ^ (G.level - 1)) * ∑ v, G.mass law v) :=
          mul_le_mul_of_nonneg_left hstep (by linarith only [(hF (G.level - 1)).1])
        _ ≤ F G.level * ∑ v, G.mass law v := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hfactor
            (Finset.sum_nonneg fun v _ => (Buffer.birth_compMass_pos hq hΛ law v.1).le)
        _ ≤ _ := ih
  have hn := Finset.sum_nonneg (fun v (_ : v ∈ (Finset.univ : Finset (CompIn G.comps))) =>
    (Buffer.birth_compMass_pos hq hΛ law v.1).le)
  have hh := mul_le_mul_of_nonneg_right (hF G.level).1 hn
  change 1 / 2 * (∑ v, G.mass law v) ≤ F G.level * (∑ v, G.mass law v) at hh
  linarith only [hh, hpot G hc]
end

end AVRegularity.Construction.Preservation.RetainedEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.RetainedEnergy

/-! A parent readout has disjoint row supports. Its norm is controlled by the
sum of squared normalized coefficients, retaining the small fresh-birth factor. -/

section
private theorem parent_square_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : κ → ι) (β y : κ → ℝ) (C : ℝ)
    (hrow : ∀ i, ∑ j, (if p j = i then β j else 0) ^ 2 ≤ C ^ 2) :
    ∑ i, (∑ j, if p j = i then β j * y j else 0) ^ 2 ≤
      C ^ 2 * ∑ j, y j ^ 2 := by
  classical
  calc
    _ ≤ ∑ i, C ^ 2 * ∑ j, if p j = i then y j ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro i _
      have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => if p j = i then β j else 0)
        (fun j => if p j = i then y j else 0)
      simp only [ite_mul, mul_ite, mul_zero, zero_mul, ite_pow, zero_pow
        (by decide : 2 ≠ 0)] at hs
      have hr := hrow i
      simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)] at hr
      have hn : ∀ j, (if p j = i then if p j = i then β j * y j else 0 else 0) =
          (if p j = i then β j * y j else 0) := by
        intro j
        split_ifs <;> rfl
      simp only [hn] at hs
      exact hs.trans (mul_le_mul_of_nonneg_right hr
        (Finset.sum_nonneg fun j _ => by split_ifs <;> positivity))
    _ = C ^ 2 * ∑ j, ∑ i, if p j = i then y j ^ 2 else 0 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by simp

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

/-- The squared row price is enough because each column has exactly one parent. -/
theorem readout_norm_of_supported_square_rows {S S' : Finset Comp} {K : ℕ}
    (m : ℕ) (E η ρ C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (π : CompIn S → ℝ) (σ : CompIn S' → ℝ)
    (hπ : ∀ v, 0 < π v) (hσ : ∀ c, 0 < σ c)
    (hparent : ∀ c : CompIn S', compParent m c.1 ∈ S)
    (sel : CompIn S' → Prop) [DecidablePred sel]
    (hrow : ∀ v : CompIn S, ∑ c : CompIn S',
      (if compParent m c.1 = v.1 ∧ sel c then
        (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ *
          E ^ (η * (compWord m c.1).length) else 0) ^ 2 ≤ C ^ 2)
    (X : ∀ c : CompIn S', TorusHk K (hr c.1.root))
    (hzero : ∀ c, ¬sel c → X c = 0) :
    weightedNorm ρ π (fun _ => 1) (succReadout m E η K X) ≤
      C * weightedNorm ρ σ (fun _ => 1) X := by
  classical
  let p : CompIn S' → CompIn S := fun c => ⟨compParent m c.1, hparent c⟩
  let z := fun c : CompIn S' => (Real.sqrt (σ c))⁻¹
  let w := fun v : CompIn S => (Real.sqrt (π v))⁻¹
  let β := fun c : CompIn S' =>
    if sel c then w (p c) / z c * E ^ (η * (compWord m c.1).length) else 0
  let y := fun c => z c * Real.sqrt (factorialNormSq ρ (X c).val)
  have hs := parent_square_sum p β y C (fun v => by
    apply le_trans _ (hrow v)
    apply Finset.sum_le_sum
    intro c _
    by_cases hc : p c = v
    · have hv : compParent m c.1 = v.1 := congrArg Subtype.val hc
      by_cases hs : sel c
      · simp only [hc, hv, hs, β, and_self, ↓reduceIte, w, z, le_refl]
      · simp only [hc, hv, hs, β, and_false, ↓reduceIte, le_refl]
    · have hv : compParent m c.1 ≠ v.1 := fun h => hc (Subtype.ext h)
      simp only [hc, hv, false_and, ↓reduceIte, le_refl])
  have hpoint (v : CompIn S) :
      (w v * Real.sqrt (factorialNormSq ρ (succReadout m E η K X v).val)) ^ 2 ≤
        (∑ c, if p c = v then β c * y c else 0) ^ 2 := by
    have hb := mul_le_mul_of_nonneg_left
      (FullLift.readout_factorial_amplitude m E η ρ hE X v)
      (inv_nonneg.mpr (Real.sqrt_nonneg (π v)))
    have he : w v * (∑ c : CompIn S', if compParent m c.1 = v.1 then
        E ^ (η * (compWord m c.1).length) * Real.sqrt (factorialNormSq ρ (X c).val)
        else 0) = ∑ c, if p c = v then β c * y c else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : p c = v
      · have hv : compParent m c.1 = v.1 := congrArg Subtype.val hc
        by_cases hs : sel c
        · simp only [hc, hv, hs, ↓reduceIte, β, y]
          dsimp only [z]
          field_simp [ne_of_gt (Real.sqrt_pos.mpr (hσ c))]
        · simp only [hc, hv, hs, ↓reduceIte, β, y, hzero c hs,
            Submodule.coe_zero, CycleComparison.Coarse.factorialNormSq_zero_jet,
            Real.sqrt_zero, mul_zero]
      · have hv : compParent m c.1 ≠ v.1 := fun h => hc (Subtype.ext h)
        simp only [hc, hv, ↓reduceIte, mul_zero]
    exact (sq_le_sq₀ (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (by rw [← he]; positivity)).mpr (hb.trans_eq he)
  have hsq := (Finset.sum_le_sum fun v _ => hpoint v).trans hs
  have hw (v : CompIn S) :
      (w v * Real.sqrt (factorialNormSq ρ (succReadout m E η K X v).val)) ^ 2 =
        (π v)⁻¹ * factorialNormSq ρ (succReadout m E η K X v).val := by
    dsimp only [w]
    rw [FullLift.inverse_sqrt_mass_square (hπ v).le,
      Real.sq_sqrt (factorialNormSq_nonneg _ _)]
  have hy (c : CompIn S') : y c ^ 2 = (σ c)⁻¹ * factorialNormSq ρ (X c).val := by
    dsimp only [y, z]
    rw [FullLift.inverse_sqrt_mass_square (hσ c).le,
      Real.sq_sqrt (factorialNormSq_nonneg _ _)]
  simp_rw [hw, hy] at hsq
  have hh := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC] at hh
  simpa only [weightedNorm, massNormSq, Pi.one_apply, one_pow, div_one] using hh

/-- Unrestricted squared-row readout bound. -/
theorem readout_norm_of_square_rows {S S' : Finset Comp} {K : ℕ}
    (m : ℕ) (E η ρ C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (π : CompIn S → ℝ) (σ : CompIn S' → ℝ)
    (hπ : ∀ v, 0 < π v) (hσ : ∀ c, 0 < σ c)
    (hparent : ∀ c : CompIn S', compParent m c.1 ∈ S)
    (hrow : ∀ v : CompIn S, ∑ c : CompIn S',
      (if compParent m c.1 = v.1 then
        (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ *
          E ^ (η * (compWord m c.1).length) else 0) ^ 2 ≤ C ^ 2)
    (X : ∀ c : CompIn S', TorusHk K (hr c.1.root)) :
    weightedNorm ρ π (fun _ => 1) (succReadout m E η K X) ≤
      C * weightedNorm ρ σ (fun _ => 1) X := by
  classical
  exact readout_norm_of_supported_square_rows m E η ρ C hE hC π σ hπ hσ hparent
    (fun _ => True) (fun v => by simpa only [and_true] using hrow v) X
    (fun _ h => False.elim (h trivial))
end

/-! The identity word and the small fresh words give the literal near-identity
readout norm, uniformly over root spaces and Sobolev orders. -/

section
open FullLift

private theorem word_row_price {m : ℕ} (hm : 1 ≤ m) {A : Finset WordLetter}
    {J : ℕ} {S S' : Finset Comp} (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale)
    (hsub : S' ⊆ succExtComps m A J S) (b : CompIn S' → ℝ) (a : ℝ)
    (v : Comp) (hentry : ∀ c : CompIn S', compParent m c.1 = v →
      b c ^ 2 ≤ if compWord m c.1 = [] then 1 else a ^ 2) :
    (∑ c : CompIn S', if compParent m c.1 = v then b c ^ 2 else 0) ≤
      1 + (wordsUpTo A (J + 1)).card * a ^ 2 := by
  classical
  let s := (Finset.univ : Finset (CompIn S')).filter (fun c => compParent m c.1 = v)
  let W := wordsUpTo A (J + 1)
  have hinj : Set.InjOn (fun c : CompIn S' => compWord m c.1) ↑s := by
    intro c hc d hd hword
    change compWord m c.1 = compWord m d.1 at hword
    apply Subtype.ext
    have hcp := (Finset.mem_filter.mp hc).2
    have hdp := (Finset.mem_filter.mp hd).2
    calc
      c.1 = succComp m v (compWord m c.1) := by
        rw [← hcp]; exact (succComp_parent_word m c.1).symm
      _ = succComp m v (compWord m d.1) := by rw [hword]
      _ = d.1 := by rw [← hdp]; exact succComp_parent_word m d.1
  have him : s.image (fun c => compWord m c.1) ⊆ insert [] W := by
    intro t ht
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ht
    exact readout_word_mem hm hold (hsub c.2)
  have hs := Finset.sum_le_sum_of_injOn
    (f := fun c : CompIn S' => b c ^ 2)
    (g := fun t => if t = [] then (1 : ℝ) else a ^ 2)
    (fun c : CompIn S' => compWord m c.1)
    hinj him (fun c hc => hentry c (Finset.mem_filter.mp hc).2)
    (fun t _ _ => by split_ifs <;> positivity)
  have hnil : [] ∉ W := by
    intro h
    have := Providers.CascadeInvariants.length_of_mem_wordsUpTo h
    simp only [List.length_nil] at this
    omega
  rw [Finset.sum_insert hnil] at hs
  have hw : (∑ t ∈ W, if t = [] then (1 : ℝ) else a ^ 2) = W.card * a ^ 2 := by
    rw [Finset.sum_congr rfl (fun t ht => ite_eq_right (fun h : t = [] => hnil (h ▸ ht)))]
    simp
  rw [ite_eq_left rfl, hw] at hs
  simpa only [s, Finset.sum_filter, W] using hs

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

/-- The sharp ordinary readout bound does not lose the identity word's constant one. -/
theorem birth_readout_near_identity {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hm : 1 ≤ m) (law : BirthLaw) (hcH : law.cH ≤ 1) (hη : 0 ≤ law.eta0)
    {A : Finset WordLetter} {J : ℕ} {S S' : Finset Comp}
    (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale) (hsub : S' ⊆ succExtComps m A J S)
    (K : ℕ) (ρ : ℝ) (X : ∀ c : CompIn S', TorusHk K (hr c.1.root)) :
    weightedNorm ρ (fun v : CompIn S => compMass q Λ law v.1) (fun _ => 1)
        (succReadout m (ocEpsilon q Λ (m - 1)) law.eta0 K X) ≤
      (1 + Real.sqrt (wordsUpTo A (J + 1)).card *
        ocEpsilon q Λ (m - 1) ^ (law.eta0 + law.etaB / 2)) *
          weightedNorm ρ (fun c : CompIn S' => compMass q Λ law c.1) (fun _ => 1) X := by
  let E := ocEpsilon q Λ (m - 1)
  let a := E ^ (law.eta0 + law.etaB / 2)
  let Tw : ℝ := (wordsUpTo A (J + 1)).card
  have ha : 0 ≤ a := Real.rpow_nonneg (Scales.epsilon_basic hq hΛ).1.le _
  have hTw : 0 ≤ Tw := Nat.cast_nonneg _
  apply readout_norm_of_square_rows m E law.eta0 ρ (1 + Real.sqrt Tw * a)
    (Scales.epsilon_basic hq hΛ).1.le (by positivity)
    _ _ (fun v => Buffer.birth_compMass_pos hq hΛ law v.1)
    (fun c => Buffer.birth_compMass_pos hq hΛ law c.1)
    (fun c => readout_parent_mem hm hold (hsub c.2)) _ X
  intro v
  let b := fun c : CompIn S' => (Real.sqrt (compMass q Λ law v.1))⁻¹ /
    (Real.sqrt (compMass q Λ law c.1))⁻¹ * E ^ (law.eta0 * (compWord m c.1).length)
  have hs := word_row_price hm hold hsub b a v.1 (by
    intro c hpar
    by_cases ht : compWord m c.1 = []
    · have heq : c.1 = v.1 := by
        calc
          c.1 = succComp m (compParent m c.1) (compWord m c.1) :=
            (succComp_parent_word m c.1).symm
          _ = compParent m c.1 := by simp only [ht, succComp, ↓reduceDIte]
          _ = v.1 := hpar
      have hmass := congrArg (compMass q Λ law) heq
      simp only [b, ht, List.length_nil, Nat.cast_zero, mul_zero, Real.rpow_zero,
        mul_one, hmass, div_self (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr
          (Buffer.birth_compMass_pos hq hΛ law v.1)))), one_pow, ↓reduceIte, le_refl]
    · rw [ite_eq_right ht]
      have hb : b c ≤ a := by
        dsimp only [b, a, E]
        rw [← hpar]
        exact fresh_readout_entry_le hq hΛ law hcH hη m c.1 ht
      have hb0 : 0 ≤ b c := mul_nonneg
        (div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        (Real.rpow_nonneg (Scales.epsilon_basic hq hΛ).1.le _)
      exact (sq_le_sq₀ hb0 ha).mpr hb)
  have hs' : (∑ c : CompIn S',
      (if compParent m c.1 = v.1 then b c else 0) ^ 2) ≤ 1 + Tw * a ^ 2 := by
    simpa only [ite_pow, zero_pow (by decide : 2 ≠ 0)] using hs
  apply hs'.trans
  have hsqrt := Real.sq_sqrt hTw
  have hcross : 0 ≤ 2 * Real.sqrt Tw * a := by positivity
  nlinarith only [hsqrt, hcross]
end

/-! Use the Sobolev adjoint directly at the endpoint reserve k+2p.
A classical representative with two extra derivatives is unnecessary for a trace. -/

section
open CycleComparison.Coarse FullLift

private theorem covariance_constant_le {M : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (p : ℕ) :
    covPolyConst M p ≤ (p : ℝ) + 1 := by
  unfold covPolyConst
  calc
    _ ≤ ∑ _l ∈ Finset.range (p + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro l _
      exact (div_le_self (pow_nonneg hM0 _) (by exact_mod_cast Nat.factorial_pos l)).trans
        (pow_le_one₀ hM0 hM1)
    _ = _ := by simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Endpoint Sobolev construction, together with its uniform factorial bound. -/
theorem covariance_trace_exists {k R p : ℕ} (horder : k + 2 * p ≤ R)
    {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : fbCovConst ρ Hc R ≤ 1) (Z : TorusHk R E) :
    ∃ W : TorusHk k E, IsCovImage (covPolyQ Hc p) Z W ∧
      Real.sqrt (factorialNormSq ρ W.val) ≤
        ((p : ℝ) + 1) * Real.sqrt (factorialNormSq ρ Z.val) := by
  let A := TorusAdj.covPolyQ (E := E) Hc le_rfl p 0 R
  let Zr := truncateTorusHk horder Z
  let W := A.adj k horder Zr
  have hW : IsCovImage (covPolyQ Hc p) Z W := by
    intro ψ hψ hp
    have hi := A.ident k horder Zr ψ (hψ.of_le (by exact_mod_cast le_top)) hp
    change cellInner (tval W) ψ = cellInner (tval Z) (covPolyQ Hc p ψ)
    simpa only [Zr, tval_truncateTorusHk] using hi
  refine ⟨W, hW, ?_⟩
  have hb := (TorusAdj.FBound.covPolyQ (E := E) hρ Hc le_rfl p 0 R) k horder Zr
  exact hb.trans ((mul_le_mul_of_nonneg_right
    (covariance_constant_le (fbCovConst_nonneg hρ Hc R) hM p) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (sqrt_fNSq_torus_truncate_le ρ horder Z)
        (by positivity)))

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]

/-- The old support is preserved exactly, and the new components have zero trace. -/
theorem retained_trace_exists_bounded {D : OCData} {Dm j₀ k R : ℕ} {bw ρ : ℝ}
    (law : BirthLaw) (G Gr : GenStage D hr Dm bw j₀) (hST : G.comps ⊆ Gr.comps)
    (m p : ℕ) (tp : ℝ) (horder : k + 2 * p ≤ R) (hρ : 0 < ρ)
    (hM : fbCovConst ρ (covPrimitive D m tp) R ≤ 1)
    (Z : ∀ v : CompIn G.comps, TorusHk R (hr v.1.root)) :
    ∃ Y0 : ∀ v : CompIn Gr.comps, TorusHk k (hr v.1.root),
      IsRetainedTrace G Gr m p tp Z Y0 ∧
      ∀ w : Comp → ℝ, (∀ v : CompIn G.comps, 0 < G.mass law v / w v.1 ^ 2) →
        weightedNorm ρ (Gr.mass law) (fun v => w v.1) Y0 ≤
          ((p : ℝ) + 1) * weightedNorm ρ (G.mass law) (fun v => w v.1) Z := by
  classical
  let W (v : CompIn G.comps) := covariance_trace_exists horder hρ (covPrimitive D m tp) hM (Z v)
  let Y0 (v : CompIn Gr.comps) : TorusHk k (hr v.1.root) :=
    if hv : v.1 ∈ G.comps then Classical.choose (W ⟨v.1, hv⟩) else 0
  have htrace : IsRetainedTrace G Gr m p tp Z Y0 := by
    constructor
    · intro v hv
      simp only [Y0, hv, ↓reduceDIte]
      exact (Classical.choose_spec (W ⟨v.1, hv⟩)).1
    · intro v hv
      simp only [Y0, hv, ↓reduceDIte]
  refine ⟨Y0, htrace, ?_⟩
  intro w hπ
  unfold GenStage.mass
  rw [weightedNorm_own_components hST D.q ρ D.Λ law w Y0 htrace.2]
  have hv (v : CompIn G.comps) : factorialNormSq ρ (Y0 ⟨v.1, hST v.2⟩).val ≤
      ((p : ℝ) + 1) ^ 2 * factorialNormSq ρ (Z v).val := by
    have hb := (Classical.choose_spec (W v)).2
    have hb2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
    simpa only [Y0, v.2, ↓reduceDIte, mul_pow, Real.sq_sqrt (factorialNormSq_nonneg _ _)] using hb2
  have hs : massNormSq ρ (fun v => G.mass law v / w v.1 ^ 2)
      (fun v => (Y0 ⟨v.1, hST v.2⟩).val) ≤
      ((p : ℝ) + 1) ^ 2 * massNormSq ρ (fun v => G.mass law v / w v.1 ^ 2)
        (fun v => (Z v).val) := by
    unfold massNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    calc
      _ ≤ (G.mass law v / w v.1 ^ 2)⁻¹ *
          (((p : ℝ) + 1) ^ 2 * factorialNormSq ρ (Z v).val) :=
        mul_le_mul_of_nonneg_left (hv v) (inv_nonneg.mpr (hπ v).le)
      _ = _ := by ring
  have hh := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ p + 1)] at hh
  exact hh
end

end AVRegularity.Construction.Preservation.RetainedEnergy
end
end

section
section
/-! Exact homogeneous contraction for a native retained solution from its compiled operator.
Special cases: EMPTY and singleton families, k = 0 and a zero initial datum are included.
The drift may vanish (identity geometry); no sign of preparation constants is used. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.RetainedEnergy
open AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_homogeneous_contraction (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {a b ρ ν : ℝ} {k : ℕ}
    (R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν k Dm)
    (hB : R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1))
    (hC : R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)))
    (hS : R.S = G.sysS P seedK freshK φ₀ hφ₀)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : α * B * ρ ^ 2 ≤ ν / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν (streamVel φ) k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ R.π (fun v => (U v t).val) +
        (5 * ν / 4) * (∫ r in Set.Icc a t, massGradNormSq ρ R.π (fun v => (W v r).val)) ≤
      massNormSq ρ R.π (fun v => (f v).val) := by
  have hforced := native_reg_solution_forced_at_order P seedK freshK φ₀ hφ₀ G R hB hC hS hφ
    f U W Y hsol
  have hforced' : IsCoupledWeakSolutionTorus ν a b (streamVel φ) 0 (fun _ => k)
      AVRegularity.KernelEnergy.TorusKernelOperator.noLocalCoefficient f
      (fun v t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) + R.carrierFlux W v t)
      (fun _ _ => 0) U W := by
    simpa only [zero_add] using hforced
  obtain ⟨hv, hp, hd, ⟨V, hV⟩, hm⟩ := Buffer.stream_kernel_drift_data hφ a b
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hbV : ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ max V 0 :=
    fun t ht x => (hV t ht x).trans (le_max_left _ _)
  have he := KernelEnergy.TorusKernelOperator.kernelForcedWeakSolution_homogeneous_interval R (streamVel φ) hv hp α B lam hα hBdrift hlam
    hsmall hstrain hd hjets hm (max V 0) hV0 hbV
    (fun _ => driftCarrierBudget k (max V 0) α B lam)
    (fun t ht _ => driftCarrierBudget_bounds k (streamVel φ t) (max V 0) α B lam hV0
      (hbV t ht) (hjets t ht)) W U f hforced'
  intro t ht
  have hh := he a ⟨le_rfl, R.htime⟩ t ht ht.1
  have hinit : (fun v => (U v a).val) = (fun v => (f v).val) := by
    funext v
    rw [hsol.2.2.2.1 v]
  simpa only [hinit, integral_Icc_eq_integral_Ioc] using hh

end AVRegularity.Construction.Preservation.RetainedEnergy
end
end

section
/-! Assemble the literal retained solution clauses from the already compiled native
operator, existence, uniqueness and homogeneous energy estimates. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.RetainedEnergy
open FullLift AVRegularity.CoupledEnergy.Variational
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The operator's literal data, with the chosen effective mass. -/
def NativeEnergyOperatorAt (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    (a b ρ ν : ℝ) (k : ℕ) (π : CompIn G.comps → ℝ) : Prop :=
  ∃ R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ ν k Dm,
    R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1) ∧
    R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root)) ∧
    R.S = G.sysS P seedK freshK φ₀ hφ₀ ∧ R.π = π

/-- Both weights share the same solution; the marked order-zero contraction is applied
separately to obtain the near-unit bound independently of the requested Sobolev order. -/
theorem retained_solution_clauses_of_operators
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    {m k : ℕ} {cr C Q Ain a b : ℝ}
    (hop : ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
      NativeEnergyOperatorAt P seedK freshK φ₀ hφ₀ G a b (rhoEnh D cr m)
        (D.κ (m - 1)) k (fun v => G.mass law v / w v ^ 2))
    (hop0 : NativeEnergyOperatorAt P seedK freshK φ₀ hφ₀ G a b (rhoEnh D cr m)
      (D.κ (m - 1)) 0 (fun v => G.mass law v / G.marker law v ^ 2))
    (hφ : IsAdmissibleStream (D.Φ (m - 1)))
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * rhoEnh D cr m / lam ≤ 1 / 2)
    (hstrain : α * B * rhoEnh D cr m ^ 2 ≤ D.κ (m - 1) / 8)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (m - 1)) t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (Y0 : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (hinit : ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
      weightedNorm (rhoEnh D cr m) (G.mass law) w Y0 ≤ C * Ain)
    (hnear : weightedNorm 1 (G.mass law) (G.marker law)
      (fun v => truncateTorusHk (Nat.zero_le k) (Y0 v)) ≤
        (1 + C * (D.eps (m - 1) ^ Q + D.eps (m - 1) ^ ocDelta D.α D.q)) * Ain) :
    RetainedSolutionClauses law P seedK freshK φ₀ hφ₀ G m k cr C Q Ain a b Y0 := by
  classical
  obtain ⟨R, hRB, hRC, hRS, _⟩ := hop (fun _ => 1) (Or.inl rfl)
  refine ⟨native_reg_solution_exists P seedK freshK φ₀ hφ₀ G R hRB hRC hRS hφ
    α B lam hα hBdrift hlam hsmall hstrain hjets Y0, ?_⟩
  intro U U' W W' Y Y' hsol hsol'
  refine ⟨native_reg_solution_unique P seedK freshK φ₀ hφ₀ G R hRB hRC hRS hφ
    α B lam hα hBdrift hlam hsmall hstrain hjets Y0 U U' W W' Y Y' hsol hsol', ?_⟩
  intro w hw t ht
  obtain ⟨Rw, hB, hC, hS, hπ⟩ := hop w hw
  have he := native_reg_solution_homogeneous_contraction P seedK freshK φ₀ hφ₀ G
    Rw hB hC hS hφ α B lam hα hBdrift hlam hsmall hstrain hjets Y0 U W Y hsol t ht
  have hsq (Z : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)) :
      weightedNorm (rhoEnh D cr m) (G.mass law) w Z ^ 2 =
        massNormSq (rhoEnh D cr m) Rw.π (fun v => (Z v).val) := by
    unfold weightedNorm
    rw [← hπ, Real.sq_sqrt (massNormSq_nonneg _ _ Rw.hπ _)]
  refine ⟨?_, hinit w hw, ?_⟩
  · simpa only [hsq, hπ] using he
  · obtain ⟨R0, hB0, hC0, hS0, hπ0⟩ := hop0
    have hsol0 := native_reg_solution_truncate P seedK freshK φ₀ hφ₀ G
      (D.κ (m - 1)) a b (streamVel (D.Φ (m - 1))) 0 k (Nat.zero_le k) Y0 U W Y hsol
    have he0 := native_reg_solution_homogeneous_contraction P seedK freshK φ₀ hφ₀ G R0 hB0 hC0 hS0
      hφ α B lam hα hBdrift hlam hsmall hstrain (fun _ _ l hl hl0 => by omega)
      _ _ _ _ hsol0 t ht
    have hdiss : 0 ≤ (5 * D.κ (m - 1) / 4) * ∫ r in Set.Icc a t,
        massGradNormSq (rhoEnh D cr m) R0.π
          (fun v => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le k)) (W v r)).val) :=
      mul_nonneg (by have := R0.diffusivity_pos; positivity)
        (integral_nonneg fun r => massGradNormSq_nonneg _ _ R0.hπ _)
    have hval : massNormSq (rhoEnh D cr m) R0.π
        (fun v => (truncateTorusHk (Nat.zero_le k) (U v t)).val) ≤
        massNormSq (rhoEnh D cr m) R0.π
          (fun v => (truncateTorusHk (Nat.zero_le k) (Y0 v)).val) := by
      linarith only [he0, hdiss]
    have hn := Real.sqrt_le_sqrt hval
    rw [hπ0] at hn
    change weightedNorm (rhoEnh D cr m) (G.mass law) (G.marker law)
        (fun v => truncateTorusHk (Nat.zero_le k) (U v t)) ≤
      weightedNorm (rhoEnh D cr m) (G.mass law) (G.marker law)
        (fun v => truncateTorusHk (Nat.zero_le k) (Y0 v)) at hn
    rw [Buffer.weightedNorm_order_zero_radius (rhoEnh D cr m) 1,
      Buffer.weightedNorm_order_zero_radius (rhoEnh D cr m) 1] at hn
    exact hn.trans hnear

end AVRegularity.Construction.Preservation.RetainedEnergy
end
end

section
/-! Named types for the existing uniform certificate, radius, drift and operator inputs.
These repeat the already proved full-lift interfaces to keep the final energy adapter small. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.RetainedEnergy
open FullLift

theorem retained_absorption_threshold {q τ : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hτ : 0 < τ) (A CI : ℝ) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ τ) < 1 / 8 := by
  have hl : Tendsto (fun m : ℕ => A * (CI * ocEpsilon q Λ (m - 1) ^ τ))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_const_nhds.mul (Buffer.preparation_parent_power_tendsto_zero hq hΛ hτ))
  exact eventually_atTop.1
    (hl.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)))


def RetainedCertificatesAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (mStar : ℕ) : Prop :=
  ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ tA : ℝ, tS ≤ tA →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      let Gr := G'.retained m H J
      Gr.IsNatural Mnat ∧ Gr.IsShiftInvariant ∧ Gr.IsSlotTransverse ∧
        Gr.IsContextCertified kI ∧
        markedLedger (Gr.mass law) (Gr.marker law) Gr.fam ≤
          CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe ∧
        (∀ v u (γ : Gr.fam.Γ v u),
          (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
            v u γ).width = (Gr.fam.identity v u γ).record.width ∧
          ∀ ρ : ℝ, 0 < ρ → IsSpatialRegularizerTorus ρ 0
            (succSchedD D₀ N p (H + 1)) (tA + 3 * ocTau α q Λ m) tf kI.cker
            (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              v u γ).width
            (Gr.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              φ₀ hφ₀ v u γ))


def UniformRecordLengths (α q : ℝ) (ζ : ℝ → ℝ) (Λ₀ : ℕ) : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)],
    ∀ D : OCData, D.α = α → D.q = q → D.ζ = ζ → Λ₀ ≤ D.Λ →
    IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (Mn : SuccMenu)
      (Cw cr σ₀ η₀ : ℝ) (N p : ℕ), cr ≤ 1 →
    ∀ seed G : GenStage D hr Dm bw j₀,
    seed.HasTags (succProvParams D Cw cr σ₀ η₀ N p) →
    (∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level) →
    seed.level ≤ D.term →
    IsCascadeStage D (succProvParams D Cw cr σ₀ η₀ N p) Mn seed G → 1 ≤ G.level →
    ∀ v u (γ : G.fam.Γ v u), 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level

def EnhancedRadiusAt (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (c₀ cr : ℝ) (m₀ : ℕ) : Prop :=
  ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ m : ℕ, m₀ ≤ m → m ≤ D.term → rhoEnh D cr m ≤ rhoStar D c₀ (m - 1)

def EnhancedDriftAt (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (cr : ℝ) (m₀ : ℕ) : Prop :=
  ∀ Φ : ℕ → ℝ → Vec 2 → ℝ,
        IsOCStreamSeq α q Λ ζ Φ → ∀ M : ℕ, ∀ κ : ℕ → ℝ,
        IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, m₀ ≤ m → m ≤ M →
        let ρ := cr * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m)
        0 < κ (m - 1) ∧ 0 < ρ ∧
        1024 * ρ / ocEpsilon q Λ (m - 1) ≤ 1 / 2 ∧
        (Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)) * 1024 * ρ ^ 2 ≤
          κ (m - 1) / 8 ∧
        ∀ t : ℝ, ∀ j : ℕ, 1 ≤ j → ∀ x : Vec 2,
          ‖coefficientDerivativeArray (driftCoefficient (streamVel (Φ (m - 1)) t)) j x‖ ≤
            (Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)) *
              1024 ^ j * (j.factorial : ℝ) *
                (ocEpsilon q Λ (m - 1)) ^ ((1 : ℤ) - j)

def NativeKernelOperatorsAt (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (bw : ℝ) (n Dm : ℕ)
    (c : ℕ → ℝ) (A : ℝ) (m₀ : ℕ) : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
        [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
        [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
      ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → ∀ (j₀ M : ℕ) (G : GenStage D hr Dm bw j₀) (k : InvConsts),
      G.IsContextCertified k → G.IsNatural M → G.IsShiftInvariant → m₀ + 1 ≤ G.level →
      ∀ (_hi : 1 ≤ G.level) (_hj : j₀ ≤ G.level),
      0 < D.eps (G.level - 1) → 0 < D.eps G.level → 0 < D.kap G.level →
      G.IsSlotTransverse → (∀ v : CompIn G.comps, 0 ≤ compReserve k v.1) →
      (∀ v : CompIn G.comps, compReserve k v.1 ≤ 2) →
      ∀ (P : ProvParams) (seedK freshK : ℕ → KernelSpec),
      (∀ v u γ, (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width) →
      ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (a b ρ Sbound : ℝ) (π marker : CompIn G.comps → ℝ),
      a ≤ b → 0 < ρ → ρ ≤ D.eps (G.level - 1) → ρ ≤ D.eps G.level →
      (∀ v u (γ : G.fam.Γ v u), 3 ≤ (G.fam.identity v u γ).maxOrder →
        (G.fam.identity v u γ).record.length ≤ D.eps (G.level - 1)) →
      (∀ v, 0 < π v) → (∀ v, 0 < marker v) → markedLedger π marker G.fam ≤ Sbound →
      A * Sbound ≤ 1 / 8 →
      (∀ v u γ, IsSpatialRegularizerTorus ρ 0 Dm a b c
        (G.kernelOf P seedK freshK v u γ).width (G.sysS P seedK freshK φ₀ hφ₀ v u γ)) →
      ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = marker →
      ∃ R : KernelEnergy.TorusKernelOperator (h := fun v : CompIn G.comps => hr v.1.root)
          (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) a b ρ (D.kap G.level) n Dm,
        R.B = (fun (v u : CompIn G.comps) (γ : G.fam.Γ v u)
          (d : ↥(Finset.Icc 2 Dm)) => G.physCoeff v u γ d.1) ∧
        R.C = (fun (v u : CompIn G.comps) (_ : G.fam.Γ v u) =>
          ContinuousLinearMap.id ℝ (hr u.1.root)) ∧
        R.S = G.sysS P seedK freshK φ₀ hφ₀ ∧ R.π = (fun v => π v / w v ^ 2) ∧
        R.r = (fun v u γ => (G.kernelOf P seedK freshK v u γ).width) ∧ R.c = c ∧ R.θ = A * Sbound


end AVRegularity.Construction.Preservation.RetainedEnergy
end
end
end
