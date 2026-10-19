-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
public import AVRegularity.Finite.Assembly.TerminalSeedTransportOfIngredients
import AVRegularity.EntryWeakAssembly.RelabelStage
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.EntryWeakAssembly.MassRecursion
import AVRegularity.Finite.TerminalLift.CovarianceIdentification
import AVRegularity.Finite.WeakLift.RepresentationAdapters
import AVRegularity.Readout.OperatorMap
import AVRegularity.Finite.Lift.PositivePhysicalIdentity
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.WeakLift

/-! Finite iteration of a represented weak-passage estimate, spending exactly N
derivatives per passage and applying the physical root readout once. -/

/-- Compose the unchanged passage estimate from an arbitrary level of the stack. -/
theorem weak_lift_iteration_from : WeakLiftIterationFromStatement := by
  intro D Dm b j₀ s M J N Lr depth η Cstep _hLr hCstep _hε stage CcR W hroot hchain
    hpass m hm hmt K₀ hK₀ hbudget t g₀ r₀ hr₀ hvalue₀
  classical
  let remaining := M + J - m
  have hfinish : m + remaining = M + J := by dsimp [remaining]; omega
  let K (n : ℕ) := 3 + (remaining - n) * N + (K₀ - remaining * N)
  have hK₀ : K 0 = K₀ + 3 := by
    dsimp [K, remaining]
    omega
  have hKstep (n : ℕ) (hn : n < remaining) : K n = K (n + 1) + N := by
    have hsub : remaining - n = remaining - (n + 1) + 1 := by omega
    dsimp [K]
    rw [hsub]
    ring
  have hKle (n : ℕ) : K n ≤ Lr + 3 := by
    have hmul := Nat.mul_le_mul_right N (Nat.sub_le remaining n)
    dsimp [K]
    have hb : remaining * N ≤ K₀ := hbudget
    omega
  have hiter : ∀ n : ℕ, n ≤ remaining →
      ∃ (g : CompIn (stage (m + n)).comps → Vec 2 → ℝ)
        (r : Representation (CompSpace (stage (m + n)).comps)),
        IsRepresentationAt (D.eps (m + n)) (K n) r ∧
        r.value = compField (fun v => weakMass D N J η v.1) (fun x v => g v x) ∧
        W (m + n) t g = W m t g₀ ∧
        representedSize s (K n) (D.eps (m + n)) r ≤
          (ENNReal.ofReal Cstep) ^ n * representedSize s (K₀ + 3) (D.eps m) r₀ := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa only [Nat.add_zero, hK₀, pow_zero, one_mul] using
        (show ∃ (g : CompIn (stage m).comps → Vec 2 → ℝ)
          (r : Representation (CompSpace (stage m).comps)),
          IsRepresentationAt (D.eps m) (K₀ + 3) r ∧
          r.value = compField (fun v => weakMass D N J η v.1) (fun x v => g v x) ∧
          W m t g = W m t g₀ ∧
          representedSize s (K₀ + 3) (D.eps m) r ≤
            representedSize s (K₀ + 3) (D.eps m) r₀ from
          ⟨g₀, r₀, hr₀, hvalue₀, rfl, le_rfl⟩)
    | succ n ih =>
      intro hn
      obtain ⟨g, r, hr, hvalue, hW, hsize⟩ := ih (by omega)
      have hi : m + (n + 1) - 1 = m + n := by omega
      have hstep := hpass (m + (n + 1)) (by omega) (by omega) (K (n + 1))
        (hKle _) t
      rw [hi, ← hKstep n (by omega)] at hstep
      obtain ⟨r', hr', hvalue', hsize'⟩ := hstep g r hr hvalue
      let g' := weakGluedLift (m + (n + 1)) N depth (stage (m + (n + 1)))
        (CcR (m + (n + 1))) t (weakReadoutStep (m + (n + 1)) η
          (stage (m + (n + 1))) (stage (m + n)) g)
      refine ⟨g', r', hr', hvalue', ?_, ?_⟩
      · have hrec := hchain.2 (m + (n + 1)) (by omega) (by omega) t g
        exact hrec.symm.trans hW
      · calc
          _ ≤ ENNReal.ofReal Cstep *
              ((ENNReal.ofReal Cstep) ^ n * representedSize s (K₀ + 3) (D.eps m) r₀) :=
            hsize'.trans (mul_le_mul' le_rfl hsize)
          _ = _ := by rw [pow_succ]; ac_rfl
  have hf := hiter remaining le_rfl
  rw [hfinish] at hf
  obtain ⟨g, r, hr, hvalue, hW, hsize⟩ := hf
  refine ⟨r, representationAt_order_mono (by dsimp [K]; omega) hr, ?_, ?_⟩
  · intro y
    rw [hvalue]
    have hcomps := hroot.2.1
    have hmem : (⟨0, []⟩ : Comp) ∈ (stage (M + J)).comps := by
      rw [hcomps]
      exact Finset.mem_singleton_self _
    let v₀ : CompIn (stage (M + J)).comps := ⟨⟨0, []⟩, hmem⟩
    have hv (v : CompIn (stage (M + J)).comps) : v = v₀ := by
      apply Subtype.ext
      have hv' : v.1 ∈ (stage (M + J)).comps := v.2
      simp only [hcomps, Finset.mem_singleton] at hv'
      exact hv'
    have hmass (v : CompIn (stage (M + J)).comps) : 0 < weakMass D N J η v.1 := by
      rw [hv v]
      norm_num [v₀, weakMass]
    rw [compReadoutCLM_compField _ _ hmass]
    calc
      (∑ v, (1 : ℝ) * g v y) = g v₀ y := by
        simp only [one_mul]
        apply Finset.sum_eq_single v₀
        · intro v _ hne
          exact (hne (hv v)).elim
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = W (M + J) t g y := (hchain.1 t g y hmem).symm
      _ = W m t g₀ y := congrFun hW y
  · calc
      _ ≤ representedSize s (K remaining) (D.eps (M + J)) r :=
        representedSize_order_mono s _ (by dsimp [K]; omega) r
      _ ≤ (ENNReal.ofReal Cstep) ^ remaining * representedSize s (K₀ + 3) (D.eps m) r₀ := hsize
      _ = _ := by rw [ENNReal.ofReal_pow hCstep]

/-- The original M-start theorem is the variable-start theorem at m=M. -/
theorem weak_lift_iteration : WeakLiftIterationStatement := by
  intro D Dm b j₀ s M J N Lr depth η Cstep hLr hCstep hε stage CcR W hroot hchain hpass
  simpa only [Nat.add_sub_cancel_left] using
    weak_lift_iteration_from s M J N Lr depth η Cstep hLr hCstep hε stage CcR W
      hroot hchain hpass M le_rfl (by omega) Lr le_rfl (by simpa using hLr)

/-- Only the uniform analytic one-passage leaf remains. -/
theorem weak_lift_rep_of_passage_bounds (hpass : WeakLiftPassageBoundsStatement) :
    Assembly.WeakLiftRepStatement :=
  weak_lift_rep_of_ingredients hpass weak_lift_iteration

end AVRegularity.Finite.WeakLift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Finite.WeakLift

/-! Positive weak birth masses make each normalized constant readout entry contractive. -/

open Construction.Preservation.FullLift WeakEntryProofs

theorem weakMass_parent_le (D : OCData) (N J m : ℕ) (η : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hη : 0 ≤ η) (c : Comp) : weakMass D N J η c ≤ weakMass D N J η (compParent m c) := by
  have he := Scales.epsilon_basic (m := m - 1) hq hΛ
  have heD : 0 ≤ D.eps (m - 1) := he.1.le
  have hc : 0 ≤ weakCw N J ∧ weakCw N J ≤ 1 := by
    have hn : (1 : ℝ) ≤ (4 * N * J : ℕ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by positivity) : 1 ≤ 4 * N * J)
    exact ⟨inv_nonneg.mpr (le_trans zero_le_one hn), inv_le_one_of_one_le₀ hn⟩
  have hf : 0 ≤ weakCw N J * D.eps (m - 1) ^ (η / 2) ∧
      weakCw N J * D.eps (m - 1) ^ (η / 2) ≤ 1 := by
    exact ⟨mul_nonneg hc.1 (Real.rpow_nonneg heD _),
      (mul_le_mul hc.2 (Real.rpow_le_one heD he.2.1 (div_nonneg hη (by norm_num)))
        (Real.rpow_nonneg heD _) zero_le_one).trans_eq (one_mul 1)⟩
  calc
    _ = weakMass D N J η (succComp m (compParent m c) (compWord m c)) := by
      rw [succComp_parent_word]
    _ = weakMass D N J η (compParent m c) *
        (weakCw N J * D.eps (m - 1) ^ (η / 2)) ^ (compWord m c).length :=
      weakMass_succComp D N J m η _ _
    _ ≤ _ := mul_le_of_le_one_right
      (weakMass_pos D N J η hN hJ (fun i => (Scales.epsilon_basic (m := i) hq hΛ).1) _).le
      (pow_le_one₀ hf.1 hf.2)

theorem weak_readoutMatrix_entry (D : OCData) (N J m : ℕ) (η : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hη : 0 ≤ η) {S S' : Finset Comp} (v : CompIn S) (c : CompIn S') :
    0 ≤ readoutMatrix m (D.eps (m - 1)) η
      (fun v : CompIn S => weakMass D N J η v.1)
      (fun c : CompIn S' => weakMass D N J η c.1) v c ∧
    readoutMatrix m (D.eps (m - 1)) η
      (fun v : CompIn S => weakMass D N J η v.1)
      (fun c : CompIn S' => weakMass D N J η c.1) v c ≤ 1 := by
  classical
  unfold readoutMatrix
  dsimp only
  split_ifs with hp
  · rw [← hp]
    have hpos := weakMass_pos D N J η hN hJ
      (fun i => (Scales.epsilon_basic (m := i) hq hΛ).1) (compParent m c.1)
    have hratio : (Real.sqrt (weakMass D N J η (compParent m c.1)))⁻¹ *
        Real.sqrt (weakMass D N J η c.1) ≤ 1 := by
      rw [← div_eq_inv_mul, div_le_one (Real.sqrt_pos.mpr hpos)]
      exact Real.sqrt_le_sqrt (weakMass_parent_le D N J m η hN hJ hq hΛ hη c.1)
    have hcoeff := readout_coefficient_le_one hq hΛ hη m c.1
    have hcoeff0 : 0 ≤ D.eps (m - 1) ^ (η * (compWord m c.1).length) :=
      Real.rpow_nonneg (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le _
    constructor
    · exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hcoeff0)
        (Real.sqrt_nonneg _)
    · calc
        _ = ((Real.sqrt (weakMass D N J η (compParent m c.1)))⁻¹ *
            Real.sqrt (weakMass D N J η c.1)) *
            D.eps (m - 1) ^ (η * (compWord m c.1).length) := by ring
        _ ≤ 1 * 1 := mul_le_mul hratio hcoeff hcoeff0 zero_le_one
        _ = 1 := one_mul 1
  · exact ⟨le_rfl, zero_le_one⟩

end AVRegularity.Finite.WeakLift
end
end

section
section
/-! Copy the old representation labels and append the physical weak-passage difference. -/

@[expose] public noncomputable section
open Homogenization AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.WeakLift

variable {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup H'] [NormedSpace ℝ H']

def appendPassageCorrection (r : Representation H) (R : H →L[ℝ] H')
    (corr : Vec 2 → H') (e : ℝ) : Representation H' where
  base := (r.map R).base
  profiles := (r.map R).profiles ++ [(corr, e)]

theorem appendPassageCorrection_value (r : Representation H) (R : H →L[ℝ] H')
    (corr : Vec 2 → H') (e : ℝ) :
    (appendPassageCorrection r R corr e).value = fun x => R (r.value x) + corr x := by
  funext x
  simp only [Representation.value, appendPassageCorrection, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  have h := congrFun (Readout.representation_map_value r R) x
  simp only [Representation.value] at h
  rw [← add_assoc, h]

theorem appendPassageCorrection_size (s : ℝ) (K : ℕ) (r : Representation H)
    (R : H →L[ℝ] H') (corr : Vec 2 → H') (e : ℝ) :
    representedSize s K e (appendPassageCorrection r R corr e) =
      representedSize s K e (r.map R) + profileNorm e K s corr := by
  simp only [representedSize, appendPassageCorrection, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  ac_rfl

theorem weak_passage_append : WeakPassageAppendStatement := by
  intro H H' _ _ _ _ s e E Cr Cc K Kin he heE hs hK hCr hCc r R out hr hR hcd hp hcost
  let corr := out - fun x => R (r.value x)
  refine ⟨appendPassageCorrection r R corr e, ?_, ?_, ?_⟩
  · have hprefix := TerminalLift.prefix_representation he heE hK r R hr
    refine ⟨hprefix.1, hprefix.2.1, hprefix.2.2.1, hprefix.2.2.2.1, ?_⟩
    intro p hmem
    simp only [appendPassageCorrection, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hmem
    rcases hmem with hmem | rfl
    · exact hprefix.2.2.2.2 p hmem
    · exact ⟨hcd, hp, le_rfl, hprefix.2.1⟩
  · rw [appendPassageCorrection_value]
    funext x
    exact add_sub_cancel _ _
  · rw [appendPassageCorrection_size]
    calc
      _ ≤ ENNReal.ofReal Cr * representedSize s Kin E r +
          ENNReal.ofReal Cc * representedSize s Kin E r :=
        add_le_add (TerminalLift.prefix_size_le he heE hs hK r R hr hR) hcost
      _ = _ := by rw [← add_mul, ← ENNReal.ofReal_add hCr hCc]

end AVRegularity.Finite.WeakLift
end
end

section
/-! A finite Schur estimate bounds the normalized readout uniformly over a weak stack. -/

@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Finite.WeakLift
open Construction.Preservation.FullLift WeakEntryProofs

/-- The constant component map inherits row and column Schur bounds. -/
theorem readoutCLM_norm_le_schur (m : ℕ) (E η C : ℝ) {S S' : Finset Comp}
    (π : CompIn S → ℝ) (π' : CompIn S' → ℝ) (hC : 0 ≤ C)
    (hb : ∀ v c, 0 ≤ readoutMatrix m E η π π' v c)
    (hrow : ∀ v, ∑ c, readoutMatrix m E η π π' v c ≤ C)
    (hcol : ∀ c, ∑ v, readoutMatrix m E η π π' v c ≤ C) :
    ‖readoutCLM m E η π π'‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro z
  have hz := finiteSchur_amplitudes (readoutMatrix m E η π π')
    (fun c => z c) C hC hb hrow hcol
  change ‖Matrix.toLpLin 2 2 (readoutMatrix m E η π π') z‖ ≤ C * ‖z‖
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    Matrix.mulVec, dotProduct, Real.norm_eq_abs, sq_abs] using hz

/-- Counting both sides suffices when all normalized entries are at most one. -/
theorem weak_readoutCLM_norm_le_card (D : OCData) (N J m : ℕ) (η C : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hη : 0 ≤ η) {S S' : Finset Comp} (hS : (S.card : ℝ) ≤ C)
    (hS' : (S'.card : ℝ) ≤ C) (hC : 0 ≤ C) :
    ‖readoutCLM m (D.eps (m - 1)) η
      (fun v : CompIn S => weakMass D N J η v.1)
      (fun c : CompIn S' => weakMass D N J η c.1)‖ ≤ C := by
  classical
  apply readoutCLM_norm_le_schur _ _ _ _ _ _ hC
  · exact fun v c => (weak_readoutMatrix_entry D N J m η hN hJ hq hΛ hη v c).1
  · intro v
    calc
      _ ≤ ∑ _c : CompIn S', (1 : ℝ) := Finset.sum_le_sum fun c _ =>
        (weak_readoutMatrix_entry D N J m η hN hJ hq hΛ hη v c).2
      _ = (S'.card : ℝ) := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul, mul_one]
      _ ≤ C := hS'
  · intro c
    calc
      _ ≤ ∑ _v : CompIn S, (1 : ℝ) := Finset.sum_le_sum fun v _ =>
        (weak_readoutMatrix_entry D N J m η hN hJ hq hΛ hη v c).2
      _ = (S.card : ℝ) := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul, mul_one]
      _ ≤ C := hS

theorem weak_readout_bounds : WeakReadoutBoundsStatement := by
  intro α s _ _ _ _ q hq ζ _
  refine ⟨128, le_rfl, ?_⟩
  intro Λ hΛ bw _ _ J N R η σ hJ hN hη _ _ _ Lr _
  refine ⟨0, 0, ?_⟩
  intro sX sZ _ _
  refine ⟨(weakStoredWordBudget N R ^ J : ℕ), Nat.cast_nonneg _, ?_⟩
  refine ⟨1, 1, le_rfl, zero_lt_one, ?_⟩
  intro j₀ _hj₀
  refine ⟨0, ?_⟩
  intro M _ D _ hDq hDΛ _ _ _ _ P Dm stage CcR hc _ i hi hit
  have hqD : 1 < D.q := hDq.symm ▸ hq.1
  have hΛD : 128 ≤ D.Λ := hDΛ.symm ▸ hΛ
  apply weak_readoutCLM_norm_le_card D N J i η _ hN hJ hqD hΛD hη.le
  · exact_mod_cast weakConstruction_card_le P _ M J 0 _ stage hc i (by omega) hit
  · exact_mod_cast weakConstruction_card_le P _ M J 0 _ stage hc (i - 1) (by omega) (by omega)
  · exact Nat.cast_nonneg _

/-- The actual physical correction is the only open weak passage ingredient. -/
theorem weak_lift_passage_bounds_of_correction
    (hcorr : WeakLiftCorrectionBoundsStatement) : WeakLiftPassageBoundsStatement := by
  exact weak_lift_passage_bounds_of_ingredients weak_readout_bounds hcorr weak_passage_append

/-- Readout, label bookkeeping and finite iteration are discharged; the correction
profile estimate is the sole remaining weak-lift input. -/
theorem weak_lift_rep_of_correction (hcorr : WeakLiftCorrectionBoundsStatement) :
    Assembly.WeakLiftRepStatement := by
  exact weak_lift_rep_of_passage_bounds (weak_lift_passage_bounds_of_correction hcorr)

end AVRegularity.Finite.WeakLift
end
end
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Finite

/-! Finite-order raw spatial jets control the factorial-normalized profile norm.
No analytic coefficient estimate is assumed by these norm summation lemmas. -/

/-- Raising the tested derivative order enlarges the finite jet index set. -/
theorem profile_indices_subset {K Kmax : ℕ} (hK : K ≤ Kmax) :
    multiIndicesBetween 1 K ⊆ multiIndicesBetween 1 Kmax := by
  intro a ha
  simp only [multiIndicesBetween, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range] at ha ⊢
  exact ⟨fun i => (ha.1 i).trans_le (Nat.add_le_add_right hK 1),
    ha.2.1, ha.2.2.trans hK⟩

/-- A spatial multi-index factorial never increases the cost of a raw jet. -/
theorem profile_factorial_one_le (a : Fin 2 → ℕ) : 1 ≤ multiIndexFactorial a := by
  simp only [multiIndexFactorial, Fin.prod_univ_two]
  have h0 : (1 : ℝ) ≤ (a 0).factorial := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos (a 0))
  have h1 : (1 : ℝ) ≤ (a 1).factorial := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos (a 1))
  exact one_le_mul_of_one_le_of_one_le h0 h1

/-- The norm sum uses no more than the order cap's fixed number of jet slots. -/
theorem profile_jet_packing : ProfileJetPackingStatement := by
  intro H _ _ e s K Kmax F Y he hK hraw
  have hsum : profileSeminorm e K s F ≤ ((multiIndicesBetween 1 K).card : ℝ≥0∞) * Y := by
    unfold profileSeminorm
    calc
      _ ≤ ∑ _a ∈ multiIndicesBetween 1 K, Y := by
        apply Finset.sum_le_sum
        intro a ha
        have hc : ENNReal.ofReal (e ^ (((a 0 + a 1 : ℕ) : ℝ) - s) / multiIndexFactorial a) ≤
            ENNReal.ofReal (e ^ (((a 0 + a 1 : ℕ) : ℝ) - s)) :=
          ENNReal.ofReal_le_ofReal (div_le_self (Real.rpow_nonneg he.le _) (profile_factorial_one_le a))
        exact (mul_le_mul' hc le_rfl).trans (hraw.2 a ha)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((multiIndicesBetween 1 K).card : ℝ≥0∞) ≤
      ((multiIndicesBetween 1 Kmax).card : ℝ≥0∞) := by
    exact_mod_cast Finset.card_le_card (profile_indices_subset hK)
  calc
    profileNorm e K s F ≤ Y + ((multiIndicesBetween 1 K).card : ℝ≥0∞) * Y :=
      add_le_add hraw.1 hsum
    _ ≤ Y + ((multiIndicesBetween 1 Kmax).card : ℝ≥0∞) * Y :=
      add_le_add le_rfl (mul_le_mul' hcard le_rfl)
    _ = _ := by simp only [profileJetCount, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

namespace WeakLift

/-- Only the actual physical scaled-jet estimate remains in the weak correction leaf. -/
theorem weak_lift_correction_bounds_of_jets (hjets : WeakLiftCorrectionJetBoundsStatement) :
    WeakLiftCorrectionBoundsStatement := by
  exact weak_lift_correction_bounds_of_ingredients profile_jet_packing hjets

/-- Readout, factorial packing, label bookkeeping and iteration are all discharged. -/
theorem weak_lift_rep_of_correction_jets (hjets : WeakLiftCorrectionJetBoundsStatement) :
    Assembly.WeakLiftRepStatement := by
  exact weak_lift_rep_of_correction (weak_lift_correction_bounds_of_jets hjets)

end WeakLift

end AVRegularity.Finite
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Finite.WeakLift

/-! The actual weak finite cutoff glue has identity part equal to the normalized readout. -/

open CycleComparison.Lift

/-- A nonzero cutoff lies in the literal finite observation set at that time. -/
theorem active_cutoff_mem_obs {α q : ℝ} {Λ i : ℕ} {t : ℝ} {k : ℤ}
    (hτ : 0 < ocTau α q Λ i) (hk : Odd k) (hcut : ocCutoff α q Λ i k t ≠ 0) :
    k ∈ ocObsPulses α q Λ i t t := by
  classical
  let x := t / ocTau α q Λ i
  have hnear : |x - k| < 5 / 4 := by
    have hn : Real.smoothTransition (5 / 2 - 2 * |x - k|) ≠ 0 := by
      simpa only [x, WeakEntryProofs.ocCutoff_normalized α q Λ i hτ] using hcut
    have hpos : 0 < 5 / 2 - 2 * |x - k| := by
      by_contra hp
      exact hn (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hp))
    linarith only [hpos]
  have hlo : ⌊x⌋ - 1 ≤ k := by
    by_contra h
    have hk' : (k : ℝ) ≤ (⌊x⌋ : ℝ) - 2 := by exact_mod_cast (by omega : k ≤ ⌊x⌋ - 2)
    have hf := Int.floor_le x
    have ha := le_abs_self (x - k)
    linarith only [hk', hf, ha, hnear]
  have hhi : k ≤ ⌈x⌉ + 1 := by
    by_contra h
    have hk' : (⌈x⌉ : ℝ) + 2 ≤ k := by exact_mod_cast (by omega : ⌈x⌉ + 2 ≤ k)
    have hf := Int.le_ceil x
    have ha := neg_le_abs (x - k)
    linarith only [hk', hf, ha, hnear]
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hk, ?_⟩
  exact ⟨t, Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut, ⟨le_rfl, le_rfl⟩⟩

/-- The exact observed finite pulse set has partition sum one. -/
theorem obs_cutoff_sum_one (α q : ℝ) (Λ i : ℕ) (t : ℝ)
    (hτ : 0 < ocTau α q Λ i) :
    ∑ k ∈ ocObsPulses α q Λ i t t, ocCutoff α q Λ i k t = 1 := by
  classical
  let T := ocObsPulses α q Λ i t t
  let U := T.subtype Odd
  have hs : Function.support (fun p : OddSlot => ocCutoff α q Λ i p.1 t) ⊆ (↑U : Set OddSlot) := by
    intro p hp
    exact Finset.mem_subtype.mpr (active_cutoff_mem_obs hτ p.2 hp)
  have hsum := WeakEntryProofs.ocCutoff_finsum_one α q Λ i hτ t
  rw [finsum_eq_sum_of_support_subset _ hs] at hsum
  have he : (∑ p ∈ U, ocCutoff α q Λ i p.1 t) = ∑ k ∈ T, ocCutoff α q Λ i k t := by
    apply Finset.sum_bij (fun p _ => p.1)
    · intro p hp
      exact Finset.mem_subtype.mp hp
    · intro p _ r _ h
      exact Subtype.ext h
    · intro k hk
      exact ⟨⟨k, (Finset.mem_filter.mp hk).2.1⟩, Finset.mem_subtype.mpr hk, rfl⟩
    · intro p _
      rfl
  exact he.symm.trans hsum

/-- The actual flow and inverse label recover the physical point. -/
theorem weak_chart_inverse (D : OCData) (i : ℕ) (t s : ℝ) (x : Vec 2) :
    D.flowOf i t (D.flowOf i s x t) s = x := by
  have hφ := D.hΦ i
  have hf := flow_isFlow (streamVel (D.Φ i)) hφ.vel_continuous hφ.vel_lipschitz
  exact (AVenhance.Infra.Flow.flow_group_law _ hφ.vel_lipschitz hf x t s t).trans (hf.1 x t)

/-- Inverse mass coordinates convert the literal weak scalar readout into its constant matrix. -/
theorem weak_readout_normalized (D : OCData) (N J i : ℕ) (η : ℝ)
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    {S S' : Finset Comp} (g : CompIn S' → Vec 2 → ℝ) (x : Vec 2) :
    readoutCLM i (D.eps (i - 1)) η (fun v : CompIn S => weakMass D N J η v.1)
        (fun v : CompIn S' => weakMass D N J η v.1)
        (compField (fun v => weakMass D N J η v.1) (fun x v => g v x) x) =
      toCompSpace (fun v : CompIn S => weakMass D N J η v.1)
        (fun v => ∑ c : CompIn S', if compParent i c.1 = v.1 then
          (D.eps (i - 1) ^ η) ^ (compWord i c.1).length * g c x else 0) := by
  classical
  ext v
  change (∑ c : CompIn S', readoutMatrix i (D.eps (i - 1)) η _ _ v c *
      ((Real.sqrt (weakMass D N J η c.1))⁻¹ * g c x)) =
    (Real.sqrt (weakMass D N J η v.1))⁻¹ * _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [readoutMatrix]
  split_ifs
  · have hp := WeakEntryProofs.weakMass_pos D N J η hN hJ
      (fun m => (Scales.epsilon_basic (m := m) hq hΛ).1) c.1
    rw [Real.rpow_mul_natCast (x := D.eps (i - 1)) (Scales.epsilon_basic (m := i - 1) hq hΛ).1.le]
    have hn : Real.sqrt (weakMass D N J η c.1) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    calc
      _ = ((Real.sqrt (weakMass D N J η v.1))⁻¹ *
          (D.eps (i - 1) ^ η) ^ (compWord i c.1).length * g c x) *
          (Real.sqrt (weakMass D N J η c.1) * (Real.sqrt (weakMass D N J η c.1))⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hn, mul_one, mul_assoc]
  · simp only [zero_mul, mul_zero]

/-- The scalar weak glued field minus its input is exactly its positive-degree part. -/
theorem weak_glued_positive_difference {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (i N depth sX sZ : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hl : IsWeakReadoutLifts i N depth sX sZ G Cc) (t : ℝ)
    (f : CompIn G.comps → Vec 2 → ℝ) (v : CompIn G.comps) (x : Vec 2) :
    weakGluedLift i N depth G Cc t f v x - f v x =
      weakGluedLift i N depth G (positiveLiftCoefficients Cc) t f v x := by
  classical
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband i
  have hτ := Construction.Stream.ocTau_pos (α := D.α) (q := D.q) hΛ (m := i)
  have hdiff : weakGluedLift i N depth G Cc t f v x -
      weakGluedLift i N depth G (positiveLiftCoefficients Cc) t f v x = f v x := by
    simp only [weakGluedLift, gluedLift, Finset.sum_apply, Pi.smul_apply]
    rw [← Finset.sum_sub_distrib]
    trans ∑ k ∈ ocObsPulses D.α D.q D.Λ i t t, ocCutoff D.α D.q D.Λ i k t • f v x
    · apply Finset.sum_congr rfl
      intro k hk
      by_cases hw : ocCutoff D.α D.q D.Λ i k t = 0
      · simp only [hw, zero_smul, sub_self]
      · have hodd : Odd k := (Finset.mem_filter.mp hk).2.1
        have ht := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hw
        have htcell : (D.cellScaleSq i)⁻¹ * t ∈ Set.Icc
            (D.slotStart i k / D.cellScaleSq i)
            ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / D.cellScaleSq i) := by
          rw [inv_mul_eq_div]
          exact ⟨div_le_div_of_nonneg_right ht.1 hc.le,
            div_le_div_of_nonneg_right ht.2 hc.le⟩
        rw [← smul_sub]
        apply congrArg (fun y : ℝ => ocCutoff D.α D.q D.Λ i k t • y)
        exact pulse_positive_difference_time _ sX sZ _ _ N depth Cc k (hl k hodd)
          _ _ _ _ t hc.ne' (Construction.Stream.ocEpsilon_pos (q := D.q) (n := i - 1) hΛ).ne'
          htcell _ _ (fun _ x v => f v x) x
          (weak_chart_inverse D (i - 1) t (D.slotAnchor i k) x) v
    · rw [← Finset.sum_smul, obs_cutoff_sum_one _ _ _ _ _ hτ, one_smul]
  linarith only [hdiff]

/-- Identity removal is independent of the datum, phase and quantitative lift bounds. -/
theorem weak_identity_separation : WeakIdentitySeparationStatement := by
  intro α s _ _ _ _ q hq ζ hζ
  refine ⟨128, le_rfl, ?_⟩
  intro Λ hΛ bw _ _ J N R η σ hJ hN _ _ _ _ Lr _
  refine ⟨0, 0, ?_⟩
  intro sX sZ _ _
  refine ⟨0, le_rfl, ?_⟩
  refine ⟨1, 1, le_rfl, zero_lt_one, ?_⟩
  intro j₀ _hj₀
  refine ⟨1, ?_⟩
  intro M _ D hDα hDq hDΛ hDζ _ hband hterm P Dm stage CcR _ hl i hi hit K _ t g r _ hv
  have hΛD : 128 ≤ D.Λ := hDΛ.symm ▸ hΛ
  have hqD : 1 < D.q := hDq.symm ▸ hq.1
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]
    exact hband
  funext x
  have hread := weak_readout_normalized D N J i η hN hJ hqD hΛD (S := (stage i).comps) g x
  have hrx := congrFun hv x
  change compField _ _ x - readoutCLM i (D.eps (i - 1)) η _ _ (r.value x) = _
  rw [hrx]
  rw [hread]
  ext v
  change (Real.sqrt (weakMass D N J η v.1))⁻¹ *
      weakGluedLift i N (J * R) (stage i) (CcR i) t
        (weakReadoutStep i η (stage i) (stage (i - 1)) g) v x -
      (Real.sqrt (weakMass D N J η v.1))⁻¹ *
        weakReadoutStep i η (stage i) (stage (i - 1)) g v x =
    (Real.sqrt (weakMass D N J η v.1))⁻¹ *
      weakGluedLift i N (J * R) (stage i) (positiveLiftCoefficients (CcR i)) t
        (weakReadoutStep i η (stage i) (stage (i - 1)) g) v x
  rw [← mul_sub, weak_glued_positive_difference i N (J * R) sX sZ (stage i) (CcR i)
    (by omega) hζD hbandD (hl i hi hit)]

/-- The physical positive-degree estimate is the only remaining weak analytic input. -/
theorem weak_lift_correction_jets_of_positive_response (hpos : WeakPositiveResponseJetStatement) :
    WeakLiftCorrectionJetBoundsStatement := by
  exact weak_lift_correction_jets_of_ingredients weak_identity_separation hpos positive_scale_gain

end AVRegularity.Finite.WeakLift
end
end
