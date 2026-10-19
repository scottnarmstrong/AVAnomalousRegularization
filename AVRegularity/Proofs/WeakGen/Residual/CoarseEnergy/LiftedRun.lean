-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Results.Finite.TraceClosure
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleWords.PeriodicClassicalLiftReadout
import AVRegularity.CycleComparison.Coarse.Bound.FcNorm
import AVRegularity.CycleComparison.Reconstruction.ClassicalBridge
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Proofs.WeakGen.Reduction.QuietTraceHighPassage
import AVRegularity.Proofs.WeakGen.Comparison.RowsHigh

section
@[expose] public noncomputable section

section
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The stored total of a weak passage at general masses**.

`weakFrontier_total_passage_le`: the stored total of the output stage `G'` of a weak passage
`G → G'`, taken at arbitrary masses `μ`, is bounded like `weakStoredTotal_passage_le`,
provided that the inherited sources have the same
mass ratio as for the weak masses and the eddy sources have a bounded weight `C`. -/

open Homogenization AVRegularity.Construction.Preservation.Ledger AVRegularity.WeakEntryProofs

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The weight of a source at the masses `μ`. -/
def weakFrontierSourceWeight (G : GenStage D (fun _ => ℝ) Dm b j₀) (μ : Comp → ℝ)
    (P : ProvParams) (rW η : ℝ) (s : WeakSource G) : ℝ :=
  Real.sqrt (μ (s.srcComp G.level) / μ (s.tgtComp G.level)) * (s.weakTag P G.level rW η).size

/-- The stored total at the masses `μ` is bounded by the sum over the finite source code. -/
theorem weakFrontier_total_le_code (μ : Comp → ℝ) (P : ProvParams) (Mn : WeakMenu) (Din H : ℕ)
    (rW : ℝ) (G G' : GenStage D (fun _ => ℝ) Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht' : G'.HasTags P)
    (hpath : ∀ h, StagePath G h → h ≤ H)
    (hnn : ∀ s : WeakSource G, 0 ≤ weakFrontierSourceWeight G μ P rW Mn.η0 s) :
    ∑ a : LedgerEdge G', Real.sqrt (μ a.2.1.1 / μ a.1.1) *
        (G'.fam.identity a.1 a.2.1 a.2.2).record.size ≤
      ∑ c : WeakStoredSourceCode G Mn.N Mn.R Din H,
        weakFrontierSourceWeight G μ P rW Mn.η0 (weakStoredCodeDecode G Mn.N Mn.R Din H c) := by
  obtain ⟨_, _, _, _, _, e, idx, Cc, Cc0, _, _, _, hd⟩ := hp
  let src (a : LedgerEdge G') : WeakSource G := (e a.1 a.2.1 a.2.2).1
  have hv (a : LedgerEdge G') : (src a).Valid Mn.N Mn.R Din := (e a.1 a.2.1 a.2.2).2.1
  have hinj : Function.Injective src := by
    rintro ⟨v, u, γ⟩ ⟨v', u', γ'⟩ hh
    have htarget : v = v' := Subtype.ext ((e v u γ).2.2.2.symm.trans
      ((congrArg (WeakSource.tgtComp G.level) hh).trans (e v' u' γ').2.2.2))
    have hsource : u = u' := Subtype.ext ((e v u γ).2.2.1.symm.trans
      ((congrArg (WeakSource.srcComp G.level) hh).trans (e v' u' γ').2.2.1))
    subst v'
    subst u'
    have hγ : γ = γ' := (e v u).injective (Subtype.ext hh)
    subst γ'
    rfl
  let code (a : LedgerEdge G') :=
    (weakStoredCode_covers G Mn.N Mn.R Din H hpath (src a) (hv a)).choose
  have hc (a : LedgerEdge G') :
      weakStoredCodeDecode G Mn.N Mn.R Din H (code a) = src a :=
    (weakStoredCode_covers G Mn.N Mn.R Din H hpath (src a) (hv a)).choose_spec
  have hcode : Function.Injective code := by
    intro a b hab
    exact hinj ((hc a).symm.trans
      ((congrArg (weakStoredCodeDecode G Mn.N Mn.R Din H) hab).trans (hc b)))
  have hw (a : LedgerEdge G') : Real.sqrt (μ a.2.1.1 / μ a.1.1) *
      (G'.fam.identity a.1 a.2.1 a.2.2).record.size =
      weakFrontierSourceWeight G μ P rW Mn.η0 (src a) := by
    have hh := ht' a.1 a.2.1 a.2.2
    rw [(hd a.1 a.2.1 a.2.2).1] at hh
    unfold weakFrontierSourceWeight
    rw [hh.1.1, (e a.1 a.2.1 a.2.2).2.2.1, (e a.1 a.2.1 a.2.2).2.2.2]
    rfl
  have hh := sum_comp_le code hcode
    (fun c => weakFrontierSourceWeight G μ P rW Mn.η0
      (weakStoredCodeDecode G Mn.N Mn.R Din H c)) (fun c => hnn _)
  simpa only [hc, ← hw] using hh

/-- The count bound at general masses: inherited sources cost powers of the incoming total,
eddy sources a bounded weight `C` times the source count. -/
theorem weakFrontier_total_passage_le (μ : Comp → ℝ) (C : ℝ) (P : ProvParams)
    (Mn : WeakMenu) (J Din H : ℕ) (rW : ℝ) (G G' : GenStage D (fun _ => ℝ) Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G.HasTags P) (ht' : G'.HasTags P)
    (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i)
    (hpath : ∀ h, StagePath G h → h ≤ H)
    (hinh : ∀ (w : List WordLetter) (h : ℕ) (π : StagePath G (h + 1)),
      Real.sqrt (μ (succComp G.level π.src w) / μ (succComp G.level π.tgt w)) =
        Real.sqrt (weakMass D Mn.N J Mn.η0 (succComp G.level π.src w) /
          weakMass D Mn.N J Mn.η0 (succComp G.level π.tgt w)))
    (hed : ∀ (v : CompIn G.comps) (w : List WordLetter) (n : ℕ),
      Real.sqrt (μ (succComp G.level v.1 w) / μ (succComp G.level v.1 (w ++ [.eddy n]))) *
        (D.eps (G.level - 1) ^ (-Mn.η0) * D.weakPe G.level ^ 2) ≤ C) :
    ∑ a : LedgerEdge G', Real.sqrt (μ a.2.1.1 / μ a.1.1) *
        (G'.fam.identity a.1 a.2.1 a.2.2).record.size ≤
      (Fintype.card (WeakStoredWords Mn.N Mn.R) : ℝ) * (Mn.N + Din + 1) *
        ∑ h : Fin H, weakStoredTotal G Mn.N J Mn.η0 ^ (h.1 + 1) +
      (Fintype.card (CompIn G.comps) : ℝ) * Fintype.card (WeakStoredWords Mn.N Mn.R) *
        (Mn.N + 2) * C := by
  have hinh' : ∀ (w : List WordLetter) (h : ℕ) (π : StagePath G (h + 1)) (n : ℕ),
      weakFrontierSourceWeight G μ P rW Mn.η0 (.inherited w (h + 1) π n) =
        weakStoredSourceWeight G Mn.N J Mn.η0 P rW (.inherited w (h + 1) π n) := by
    intro w h π n
    unfold weakFrontierSourceWeight weakStoredSourceWeight
    exact congrArg (· * _) (hinh w h π)
  have hnn : ∀ s : WeakSource G, 0 ≤ weakFrontierSourceWeight G μ P rW Mn.η0 s := fun s =>
    mul_nonneg (Real.sqrt_nonneg _) (weakSource_tag_size_nonneg G P ht _ rW Mn.η0
      (heps _) s)
  refine (weakFrontier_total_le_code μ P Mn Din H rW G G' hp ht' hpath hnn).trans ?_
  let g : WeakStoredSourceCode G Mn.N Mn.R Din H → ℝ :=
    Sum.elim (fun x => pathWeight (weakStoredEdgeWeight G Mn.N J Mn.η0) x.2.1.2) (fun _ => C)
  have hle : ∀ c : WeakStoredSourceCode G Mn.N Mn.R Din H,
      weakFrontierSourceWeight G μ P rW Mn.η0 (weakStoredCodeDecode G Mn.N Mn.R Din H c) ≤
        g c := by
    rintro (⟨w, π, n⟩ | ⟨v, w, n⟩)
    · simp only [weakStoredCodeDecode, g, Sum.elim_inl]
      rw [hinh', weakStoredSourceWeight_inherited G Mn.N J Mn.η0 hN hJ heps P ht]
    · simp only [weakStoredCodeDecode, g, Sum.elim_inr]
      exact hed v w.1 n.1
  refine (Finset.sum_le_sum fun c _ => hle c).trans ?_
  simp only [g, ← Finset.mul_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    Fintype.sum_sigma, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hpows : (∑ h : Fin H, ∑ π : StagePath G (h.1 + 1),
      pathWeight (weakStoredEdgeWeight G Mn.N J Mn.η0) π) ≤
      ∑ h : Fin H, weakStoredTotal G Mn.N J Mn.η0 ^ (h.1 + 1) :=
    Finset.sum_le_sum (fun h _ => weakStoredPath_sum_le G Mn.N J Mn.η0 (h.1 + 1))
  have hh := mul_le_mul_of_nonneg_left hpows
    (by positivity : 0 ≤ (Fintype.card (WeakStoredWords Mn.N Mn.R) : ℝ) * (Mn.N + Din + 1))
  nlinarith only [hh]

/-- Once the incoming total is at most one, the finite menus bound the stored total at the masses
`μ` by `Q (1 + C)`, `Q` the passage budget. -/
theorem weakFrontier_total_uniform (μ : Comp → ℝ) (C : ℝ) (hC : 0 ≤ C) (P : ProvParams)
    (Mn : WeakMenu) (J Din : ℕ) (rW : ℝ) (G G' : GenStage D (fun _ => ℝ) Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G.HasTags P) (ht' : G'.HasTags P)
    (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i)
    (hpath : ∀ h, StagePath G h → h ≤ J * Mn.R)
    (hsmall : weakStoredTotal G Mn.N J Mn.η0 ≤ 1)
    (hcomp : G.comps.card ≤ weakStoredWordBudget Mn.N Mn.R ^ J)
    (hDin : Din ≤ 1 + J * Mn.N)
    (hinh : ∀ (w : List WordLetter) (h : ℕ) (π : StagePath G (h + 1)),
      Real.sqrt (μ (succComp G.level π.src w) / μ (succComp G.level π.tgt w)) =
        Real.sqrt (weakMass D Mn.N J Mn.η0 (succComp G.level π.src w) /
          weakMass D Mn.N J Mn.η0 (succComp G.level π.tgt w)))
    (hed : ∀ (v : CompIn G.comps) (w : List WordLetter) (n : ℕ),
      Real.sqrt (μ (succComp G.level v.1 w) / μ (succComp G.level v.1 (w ++ [.eddy n]))) *
        (D.eps (G.level - 1) ^ (-Mn.η0) * D.weakPe G.level ^ 2) ≤ C) :
    ∑ a : LedgerEdge G', Real.sqrt (μ a.2.1.1 / μ a.1.1) *
        (G'.fam.identity a.1 a.2.1 a.2.2).record.size ≤
      (weakStoredPassageBudget Mn.N J Mn.R : ℝ) * (1 + C) := by
  let W := weakStoredWordBudget Mn.N Mn.R
  have hw : Fintype.card (WeakStoredWords Mn.N Mn.R) ≤ W := le_max_left _ _
  have ha : Fintype.card (WeakStoredWords Mn.N Mn.R) * (Mn.N + Din + 1) * (J * Mn.R) ≤
      weakStoredPassageBudget Mn.N J Mn.R := by
    have hh := Nat.mul_le_mul_right (J * Mn.R) (Nat.mul_le_mul hw
      (Nat.add_le_add_right (Nat.add_le_add_left hDin Mn.N) 1))
    exact hh.trans (by unfold weakStoredPassageBudget; dsimp [W] at hh ⊢; omega)
  have hb : G.comps.card * Fintype.card (WeakStoredWords Mn.N Mn.R) * (Mn.N + 2) ≤
      weakStoredPassageBudget Mn.N J Mn.R := by
    have hh := Nat.mul_le_mul_right (Mn.N + 2) (Nat.mul_le_mul hcomp hw)
    exact hh.trans (by unfold weakStoredPassageBudget; dsimp [W] at hh ⊢; omega)
  have ha' : (Fintype.card (WeakStoredWords Mn.N Mn.R) : ℝ) * (Mn.N + Din + 1) *
      (J * Mn.R : ℕ) ≤ (weakStoredPassageBudget Mn.N J Mn.R : ℝ) := by exact_mod_cast ha
  have hb' : (Fintype.card (CompIn G.comps) : ℝ) * Fintype.card (WeakStoredWords Mn.N Mn.R) *
      (Mn.N + 2) ≤ (weakStoredPassageBudget Mn.N J Mn.R : ℝ) := by
    rw [Fintype.card_coe]
    exact_mod_cast hb
  have hnonneg := weakStoredTotal_nonneg G Mn.N J Mn.η0
  have hpow (h : Fin (J * Mn.R)) : weakStoredTotal G Mn.N J Mn.η0 ^ (h.1 + 1) ≤
      weakStoredTotal G Mn.N J Mn.η0 := by
    rw [pow_succ]
    exact mul_le_of_le_one_left hnonneg (pow_le_one₀ hnonneg hsmall)
  have hh : (∑ h : Fin (J * Mn.R), weakStoredTotal G Mn.N J Mn.η0 ^ (h.1 + 1)) ≤
      ∑ _h : Fin (J * Mn.R), weakStoredTotal G Mn.N J Mn.η0 := Finset.sum_le_sum (fun h _ => hpow h)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  refine (weakFrontier_total_passage_le μ C P Mn J Din (J * Mn.R) rW G G' hp ht ht' hN hJ heps
    hpath hinh hed).trans ?_
  have hm := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ (Fintype.card (WeakStoredWords Mn.N Mn.R) : ℝ) * (Mn.N + Din + 1))
  have h1 := mul_le_mul ha' hsmall hnonneg (by positivity)
  have h2 := mul_le_mul_of_nonneg_right hb' hC
  nlinarith only [hm, h1, h2]

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift AVRegularity.CycleWords
namespace AVRegularity.Providers.WeakGen.Residual.PartB

/-! **Coarse readout energy, classical representatives**.

* `partB_rep_lift`: a classical representative of the order `L` of the truncation of `W : TorusHk K`
  is a classical representative of `W` of every order `r` with `r + 2 ≤ K` (uniqueness of continuous
  periodic representatives).
* `partB_derivative_continuousOn`: if `W` is continuous in time with values in `TorusHk K` and
  `a t` is a classical representative of `W t`, then the derivatives of `a` of order `≤ r`
  are jointly continuous in `(t, x)`. -/

/-- The zeroth jet of a classical representative is the representative, a.e. on the cell. -/
theorem partB_rep_zero {K r : ℕ} {W : TorusHk K ℝ} {a : Vec 2 → ℝ} (ha : IsClassicalRep W a r) :
    (W.val (valueIndex2 K) : Vec 2 → ℝ) =ᵐ[volume.restrict AVenhance.unitCube] a := by
  have h0 := ha.2.2.2 0 (Nat.zero_le _) Fin.elim0
  have hj := periodicJetRepresentative_ae W.val (valueIndex2 K)
  have : torusJetOrder W 0 Fin.elim0 = W.toFunction.jet (valueIndex2 K) := by
    funext x
    simp [AVRegularity.torusJetOrder, valueIndex2, valueIndex]
  rw [this] at h0
  simp only [orderedDerivative, List.ofFn_zero, List.foldl_nil] at h0
  exact hj.symm.trans h0

/-- A classical representative of the truncation is one of the element itself. -/
theorem partB_rep_lift {K L s r : ℕ} (hLK : L ≤ K) (hr : r + 2 ≤ K) (W : TorusHk K ℝ)
    (a : Vec 2 → ℝ) (ha : IsClassicalRep (truncateTorusHk hLK W) a s) : IsClassicalRep W a r := by
  obtain ⟨a', ha'⟩ := Providers.torusHk_classicalRep_exists K r hr W
  have h1 := partB_rep_zero ha
  have h2 := partB_rep_zero ha'
  have h3 : (truncateTorusHk hLK W).val (valueIndex2 L) =ᵐ[volume.restrict AVenhance.unitCube]
      W.val (valueIndex2 K) := by
    have := KernelEnergy.truncateTorusHk_toFunction_jet_ae hLK W (valueIndex2 L)
    have hl := periodicJetRepresentative_ae (truncateTorusHk hLK W).val (valueIndex2 L)
    have hr' := periodicJetRepresentative_ae W.val (valueIndex2 K)
    refine hl.symm.trans (this.trans ?_)
    have e : truncateJetIndex hLK (valueIndex2 L) = valueIndex2 K := by
      simp [truncateJetIndex, valueIndex2, valueIndex]
    rw [e]
    exact hr'
  have hae : a =ᵐ[volume.restrict AVenhance.unitCube] a' := h1.symm.trans (h3.trans h2)
  have heq : a = a' := periodicContinuous_eq_of_cell_ae a a' ha.2.1.continuous
    ha'.2.1.continuous ha.2.2.1 ha'.2.2.1 hae
  rw [heq]
  exact ha'

/-- The classical representative is the canonical Fourier lift. -/
theorem partB_rep_eq_lift {K r : ℕ} (hK : 2 ≤ K) {W : TorusHk K ℝ} {a : Vec 2 → ℝ}
    (ha : IsClassicalRep W a r) : realClassicalLift K W = a :=
  realClassicalLift_eq_periodic_rep K hK W a ha.2.1.continuous ha.2.2.1 (partB_rep_zero ha)

/-- **Joint continuity of the derivatives**: if `t ↦ W t ∈ TorusHk K` is continuous on `S` and
`a t` represents `W t` classically to the order `r`, `r + 2 ≤ K`, then every derivative of
order `n ≤ r` of `a` is jointly continuous on `S × ℝ²`. -/
theorem partB_derivative_continuousOn {K r : ℕ} (hr : r + 2 ≤ K) (S : Set ℝ)
    (W : ℝ → TorusHk K ℝ) (hW : ContinuousOn W S) (a : ℝ → Vec 2 → ℝ)
    (ha : ∀ t ∈ S, IsClassicalRep (W t) (a t) r) {n : ℕ} (hn : n ≤ r) (w : DerivativeWord2 n) :
    ContinuousOn (fun p : ℝ × Vec 2 => orderedDerivative w (a p.1) p.2) (S ×ˢ Set.univ) := by
  have hK : 2 ≤ K := by omega
  have hn2 : n + 2 ≤ K := by omega
  set f : Fin n → Vec 2 := fun k => basisVec (w (Fin.rev k)) with hf
  set B : ℝ := ∏ k, ‖f k‖ with hB
  have hform : ∀ t ∈ S, ∀ x, orderedDerivative w (a t) x =
      iteratedFDeriv ℝ n (realClassicalLift K (W t)) x f := by
    intro t ht x
    rw [← partB_rep_eq_lift hK (ha t ht)]
    have hd : ContDiff ℝ (n : ℕ∞) (realClassicalLift K (W t)) :=
      realClassicalLift_contDiff K n hn2 (W t)
    rw [orderedDerivative_eq_iteratedFDeriv w hd]
  have hcongr : Set.EqOn (fun p : ℝ × Vec 2 => orderedDerivative w (a p.1) p.2)
      (fun p : ℝ × Vec 2 => iteratedFDeriv ℝ n (realClassicalLift K (W p.1)) p.2 f)
      (S ×ˢ Set.univ) := fun p hp => hform p.1 hp.1 p.2
  refine ContinuousOn.congr ?_ hcongr
  intro p hp
  obtain ⟨t0, x0⟩ := p
  have ht0 : t0 ∈ S := hp.1
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hc0 : Continuous (fun x => iteratedFDeriv ℝ n (realClassicalLift K (W t0)) x f) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Vec 2) ℝ f).continuous.comp
      ((realClassicalLift_contDiff K n hn2 (W t0)).continuous_iteratedFDeriv le_rfl)
  obtain ⟨δ2, hδ2, hx⟩ := Metric.continuousAt_iff.1 (hc0.continuousAt (x := x0)) (ε / 2) (by positivity)
  have hCpos : 0 < classicalSobolevConstant n * B + 1 := by
    have : 0 ≤ classicalSobolevConstant n * B := by
      unfold classicalSobolevConstant
      positivity
    linarith
  obtain ⟨δ1, hδ1, ht⟩ := Metric.continuousWithinAt_iff.1 (hW t0 ht0)
    (ε / 2 / (classicalSobolevConstant n * B + 1)) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  rintro ⟨t, x⟩ ⟨hts, -⟩ hd
  have hd1 : dist t t0 < δ1 := by
    simpa [Prod.dist_eq] using lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hd (min_le_left _ _))
  have hd2 : dist x x0 < δ2 := by
    simpa [Prod.dist_eq] using lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hd (min_le_right _ _))
  have h1 := ht hts hd1
  have h2 := hx hd2
  have hsub : iteratedFDeriv ℝ n (realClassicalLift K (W t)) x f -
      iteratedFDeriv ℝ n (realClassicalLift K (W t0)) x f =
      iteratedFDeriv ℝ n (realClassicalLift K (W t - W t0)) x f := by
    rw [realClassicalLift_jet_sub K n hn2]
    rfl
  have hb : |iteratedFDeriv ℝ n (realClassicalLift K (W t - W t0)) x f| ≤
      classicalSobolevConstant n * B * ‖W t - W t0‖ := by
    calc _ = ‖iteratedFDeriv ℝ n (realClassicalLift K (W t - W t0)) x f‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖iteratedFDeriv ℝ n (realClassicalLift K (W t - W t0)) x‖ * B :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (classicalSobolevConstant n * ‖W t - W t0‖) * B :=
          mul_le_mul_of_nonneg_right (realClassicalLift_derivative_norm_le K _ n hn2 x)
            (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = _ := by ring
  rw [Real.dist_eq] at h2 ⊢
  have h1' : ‖W t - W t0‖ < ε / 2 / (classicalSobolevConstant n * B + 1) := by
    rwa [dist_eq_norm] at h1
  have h3 : classicalSobolevConstant n * B * ‖W t - W t0‖ < ε / 2 := by
    have h4 : classicalSobolevConstant n * B * ‖W t - W t0‖ ≤
        (classicalSobolevConstant n * B + 1) * ‖W t - W t0‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h5 : (classicalSobolevConstant n * B + 1) * ‖W t - W t0‖ < ε / 2 := by
      calc _ < (classicalSobolevConstant n * B + 1) * (ε / 2 / (classicalSobolevConstant n * B + 1)) :=
            mul_lt_mul_of_pos_left h1' hCpos
        _ = ε / 2 := by field_simp
    linarith
  have h6 : |iteratedFDeriv ℝ n (realClassicalLift K (W t)) x f -
      iteratedFDeriv ℝ n (realClassicalLift K (W t0)) x0 f| < ε := by
    have := abs_sub_le (iteratedFDeriv ℝ n (realClassicalLift K (W t)) x f)
      (iteratedFDeriv ℝ n (realClassicalLift K (W t0)) x f)
      (iteratedFDeriv ℝ n (realClassicalLift K (W t0)) x0 f)
    rw [hsub] at this
    linarith
  exact h6

/-- A classical representative of the truncation, of order below the truncation order, is one of
the element. -/
theorem partB_rep_of_truncate {K L r : ℕ} (hKL : K ≤ L) (hrK : r ≤ K) (W : TorusHk L ℝ)
    (a : Vec 2 → ℝ) (ha : IsClassicalRep (truncateTorusHk hKL W) a r) : IsClassicalRep W a r :=
  ⟨hrK.trans hKL, ha.2.1, ha.2.2.1, fun m hm w =>
    (Construction.Preservation.FullLift.torusJetOrder_truncate_ae hKL W (hm.trans hrK) w).symm.trans
      (ha.2.2.2 m hm w)⟩

/-- The classical factorial density is at most the `TorusHk` factorial norm. -/
theorem partB_factorial_le {K r k : ℕ} {W : TorusHk K ℝ} {a : Vec 2 → ℝ}
    (ha : IsClassicalRep W a r) (hk : k ≤ r) (ρ : ℝ) :
    classicalFactorialSq ρ k a ≤ ENNReal.ofReal (factorialNormSq ρ W.val) := by
  rw [CycleComparison.Reconstruction.classicalFactorialSq_eq_of_rep ha ρ hk]
  exact ENNReal.ofReal_le_ofReal
    (CycleComparison.Coarse.factorialNormSqUpTo_le_factorialNormSq ρ k W.val)

/-- The classical gradient factorial density is at most the gradient `TorusHk` factorial norm of
a gradient lift. -/
theorem partB_grad_le {K r k : ℕ} {W : TorusHk (K + 1) ℝ} {a : Vec 2 → ℝ}
    (ha : IsClassicalRep W a r) (hk : k + 1 ≤ r) (ρ : ℝ) :
    classicalGradFactorialSq ρ k a ≤ ENNReal.ofReal (gradFactorialNormSq ρ W.val) := by
  rw [CycleComparison.Reconstruction.classicalGradFactorialSq_eq_of_rep ha ρ hk]
  exact ENNReal.ofReal_le_ofReal
    (CycleComparison.Coarse.gradFactorialNormSqUpTo_le_gradFactorialNormSq ρ k W.val)

end AVRegularity.Providers.WeakGen.Residual.PartB
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The coarse readout energy: the energy of the coarse family at a high reserve**
(`WeakCoarseHighEnergyAt`).

For a request `R` and `m ≤ m_max(R)` there is `C_A ≥ 0` such that, for every passage instance `c`
and run `r` (with `a < t_{M+J_w+1}`), there are the coupled families `Uhi`, `Whi` of the higher-order lemma at the
reserves `K_w + m + …` (every passage solved, truncations to `K_w` equal to `r.Ur`) with, for every
passage `M < i ≤ M + J_w`, every `Φ` bounding the order-zero mass norm of `r.Ur i` on
`[t_{i+1}, a + T₀]` and every `t ∈ [t_i, a + T₀]`, at the radius `ρ = plan.radius R · ε_{i-1}`:
```
∑_v π_v⁻¹ |Uhi (i-1) v t|²_ρ + (κ_M/2) ∫_{[t_i, a+T₀]} ∑_v π_v⁻¹ |∇Whi (i-1) v|²_ρ ≤ C_A Φ².
```
The families are chosen before `i`, `Φ`, `t`. The top family `Uhi (M + J_w)` is the run's on
`[t_{M+J_w+1}, a + T₀]` (the clause `hvr`, exported for the raw frontier estimate): the truncation clause
below reaches the levels `M, …, M + J_w − 1` only. `WeakCoarseHighEnergyAt` is the statement at a
named constant. -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **The high-reserve energy at a constant** `CA`: for every passage instance and run (with `a < t_{M+J_w+1}`)
there are the coupled families `Uhi`, `Whi` at the high reserve, with every passage solved, the
top family equal to the run's on `[t_{M+J_w+1}, a + T₀]` (`hvr`), the truncations to
`K_w` equal to `r.Ur` below the top, and the energy bound `C_A Φ²`. -/
def WeakCoarseHighEnergyAt (plan : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (m : ℕ) (CA : ℝ) : Prop :=
  ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c), r.a < r.tq (c.M + A.Jw + 1) →
    ∃ (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
      (Whi : ∀ i, WeakStageLift (weakPassageRawSetting c) m i),
      (∀ i, c.M < i → i ≤ c.M + A.Jw →
        WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi i) ∧
      (∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
        ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (c.M + A.Jw) v t) =
          r.Ur (c.M + A.Jw) v t) ∧
      (∀ i, c.M < i → i ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (i - 1)).comps,
        ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
          truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
            r.Ur (i - 1) v t) ∧
      ∀ i, c.M < i → i ≤ c.M + A.Jw → ∀ Φ : ℝ,
        (∀ t ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀),
          weightedNorm 1 (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
            (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) ≤ Φ) →
        ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
          ENNReal.ofReal (massNormSq (plan.radius R * c.D.eps (i - 1))
              (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
              (fun v => (Uhi (i - 1) v t).val)) +
            ENNReal.ofReal (c.D.κ c.M / 2) *
              ∫⁻ τ in Set.Icc (r.tq i) (r.a + A.T₀),
                ENNReal.ofReal (massGradNormSq (plan.radius R * c.D.eps (i - 1))
                  (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
                  (fun v => (Whi (i - 1) v τ).val)) ≤
          ENNReal.ofReal (CA * Φ ^ 2)

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.Construction.Preservation.Ledger
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The raw frontier gain: the frontier masses and their stored total**.

The families of a passage are stored with the readout weights: the eddy letter from `(v, w)` to
`(v, w𝔇_n)` has the stored witness `λ_i⁻¹ Pe_i² = ε_{i-1}^{-η₀} Pe_i²` (`WeakSource.weakTag`), and
the readout multiplies the component `(v, w)` by `(ε_{i-1}^{η₀})^{|w|}` (`weakReadoutStep`). The
source's block energy `B_w` is the energy of the block of the word `w`
with the old masses and the old weights, that is with the readout weight inside:
`B_w² = ∑_v π_v⁻¹ (ε_{i-1}^{η₀})^{2|w|} |Ū_{(v,w)}|²`, and `B_{wn} ≤ C Pe_i² B_w ≤ C x^{2a_*} B_w`.
Without the readout weight the gain of a letter is `ε_{i-1}^{-2η₀} Pe_i⁴`, not `x^{4a_*}`.

The route to the gain is the passage energy at the **frontier masses**
`μ_{(v,w)} = π_v θ_i^{|w|}`, `θ_i = ε_{i-1}^{-2η₀} x^{4a_*}`, `x = ε_M`:
* on an old component `μ = π`, so the datum, which vanishes on the new components, costs the same;
* on the frontier `μ⁻¹ = π_v⁻¹ (ε_{i-1}^{η₀})^{2R_w} x^{-4a_*R_w}`, the weight of the raw frontier estimate divided by
  the gain;
* an inherited edge joins two components with the same word, so its stored weight
  `√(μ_src/μ_tgt)·size` is the one of the weak masses;
* an eddy edge has the stored weight `θ_i^{-1/2} ε_{i-1}^{-η₀} Pe_i² = x^{-2a_*} Pe_i²`, at most
  `C_w²` (`Pe_i ≤ C_w ε_{i-1}^{a_*}` and `ε_{i-1} ≤ x`). It is bounded, not small.
So the stored total at the frontier masses (`weakFrontierStoredTotal`) is at most a constant `T₀`
of the menu, and the row recursion of the coupled energy
(`coupledRowData_recursion`, stated for arbitrary masses and row sums) unrolls along the paths of
the stage, of length at most `J_wR_w`, with a constant that does not depend on `x`.

The degenerate cases are included:
- `R_w = 0`: every word is empty, `μ = π`, the total is the stored total, at most `1`.
- A stage with no eddy edge: the same.
- `η₀ → 0`: `θ_i = x^{4a_*}`; the eddy weight is `x^{-2a_*} Pe_i²`, the readout weight is `1`.
- Constants: `T₀` depends on the menu and the base. `D_m`, the level and the datum do not
  enter. -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The factor of one letter in the frontier masses of the passage `i`:
`θ_i = ε_{i-1}^{-2η₀} ε_M^{4a_*}`. -/
def weakFrontierLetter (c : WeakPassageInstance plan R) (i : ℕ) : ℝ :=
  ((c.D.eps (i - 1) ^ A.η₀) ^ 2)⁻¹ * c.D.eps c.M ^ (4 * weakAStar B.α B.q)

/-- The frontier masses of the passage `i` on the components of the stage `i - 1`: the weak mass
of the parent times `θ_i` per letter of the word. -/
def weakFrontierMass (c : WeakPassageInstance plan R) (i : ℕ) (v : Comp) : ℝ :=
  weakMass c.D A.Nw A.Jw A.η₀ (compParent i v) * weakFrontierLetter c i ^ (compWord i v).length

/-- The stored total of the stage `i - 1` at the frontier masses. -/
def weakFrontierStoredTotal (c : WeakPassageInstance plan R) (i : ℕ) : ℝ :=
  ∑ e : LedgerEdge (c.stage (i - 1)),
    Real.sqrt (weakFrontierMass c i e.2.1.1 / weakFrontierMass c i e.1.1) *
      ((c.stage (i - 1)).fam.identity e.1 e.2.1 e.2.2).record.size

end AVRegularity.Providers.WeakGen.Residual
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The unrolled row sum at a general edge weight and total**.

For a nonnegative edge weight `w` on the ledger edges of a stage the sum over the end vertices
of `rowPathSum w q n` is at most `(∑_e w e)^{n+1} ∑ q`, and `sum_unrolled_le` holds with total
`T₀` in place of `1`: if `X_u ≤ φ_u + L ∑_j (∑_γ w ⟨u,j,γ⟩)(μ_u/μ_j) X_j`, `∑_e w e ≤ T₀`,
and the stage has no path of `N + 1` edges, then
`∑ X/μ ≤ (∑_{n ≤ N} (L T₀)^n) ∑ φ/μ`. -/

open Homogenization AVRegularity.Construction.Preservation.Ledger WeakEntryProofs Comparison

/-- The complete path sum of a nonnegative edge weight is at most a power of its total. -/
theorem frontierPath_sum_le {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D (fun _ => ℝ) Dm bw j₀) (w : LedgerEdge G → ℝ) (hw : ∀ e, 0 ≤ w e) (n : ℕ) :
    ∑ π : StagePath G n, pathWeight w π ≤ (∑ e, w e) ^ n := by
  have hh := sum_comp_le (StagePath.step (G := G) (h := n))
    (AVRegularity.Construction.Preservation.Ledger.stagePath_step_injective G n)
    (fun f : Fin n → LedgerEdge G => ∏ j, w (f j))
    (fun f => Finset.prod_nonneg (fun j _ => hw (f j)))
  have he : (∑ f : Fin n → LedgerEdge G, ∏ j, w (f j)) = (∑ e, w e) ^ n := by
    simpa only [Fintype.piFinset_univ] using
      (Finset.sum_pow' (Finset.univ : Finset (LedgerEdge G)) w n).symm
  exact hh.trans_eq he

/-- Row path sums, summed over the end vertex, at a general total `T`. -/
theorem frontier_sum_rowPathSum_le {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D (fun _ => ℝ) Dm bw j₀) (w : LedgerEdge G → ℝ) (hw : ∀ e, 0 ≤ w e)
    (q : CompIn G.comps → ℝ) (hq : ∀ u, 0 ≤ q u) (n : ℕ) :
    ∑ v, rowPathSum w q n v ≤ (∑ e, w e) ^ (n + 1) * ∑ u, q u := by
  classical
  have h1 : ∑ v, rowPathSum w q n v =
      ∑ π : StagePath G (n + 1), pathWeight w π * q (π.step 0).2.1 := by
    unfold rowPathSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp
  rw [h1]
  have hqs : ∀ u, q u ≤ ∑ u, q u := fun u =>
    Finset.single_le_sum (f := q) (fun u _ => hq u) (Finset.mem_univ u)
  calc _ ≤ ∑ π : StagePath G (n + 1), pathWeight w π * ∑ u, q u :=
        Finset.sum_le_sum fun π _ => mul_le_mul_of_nonneg_left (hqs _) (pathWeight_nonneg _ hw π)
    _ = (∑ π : StagePath G (n + 1), pathWeight w π) * ∑ u, q u := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (frontierPath_sum_le G w hw _)
        (Finset.sum_nonneg fun u _ => hq u)

/-- **Summing the unrolled row recursion at a general edge weight with total at most `T₀`.** -/
theorem frontier_sum_unrolled_le {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D (fun _ => ℝ) Dm bw j₀) (w : LedgerEdge G → ℝ) (hw : ∀ e, 0 ≤ w e)
    (T₀ : ℝ) (hT : ∑ e, w e ≤ T₀) (π X φ : CompIn G.comps → ℝ) (hπ : ∀ u, 0 < π u)
    (hX : ∀ u, 0 ≤ X u) (hφ : ∀ u, 0 ≤ φ u) (L : ℝ) (hL : 0 ≤ L)
    (hrec : ∀ u, X u ≤ φ u + L * ∑ j, (∑ γ : G.fam.Γ u j, w ⟨u, j, γ⟩) * (π u / π j) * X j)
    (N : ℕ) (hN : IsEmpty (StagePath G (N + 1))) :
    ∑ v, X v / π v ≤ (∑ n ∈ Finset.range (N + 1), (L * T₀) ^ n) * ∑ v, φ v / π v := by
  classical
  have hq0 : ∀ v, 0 ≤ φ v / π v := fun v => div_nonneg (hφ v) (hπ v).le
  have hS0 : 0 ≤ ∑ e, w e := Finset.sum_nonneg fun e _ => hw e
  have hunroll := fun v => mass_recursion_unroll w hw π X φ hπ hX L hL hrec N hN v
  have hQ0 : 0 ≤ ∑ v, φ v / π v := Finset.sum_nonneg fun v _ => hq0 v
  calc ∑ v, X v / π v
      ≤ ∑ v, (φ v / π v + ∑ n ∈ Finset.range N, L ^ (n + 1) *
        rowPathSum w (fun u => φ u / π u) n v) := Finset.sum_le_sum fun v _ => hunroll v
    _ = ∑ v, φ v / π v + ∑ n ∈ Finset.range N, L ^ (n + 1) *
        ∑ v, rowPathSum w (fun u => φ u / π u) n v := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ v, φ v / π v + ∑ n ∈ Finset.range N, L ^ (n + 1) *
        (T₀ ^ (n + 1) * ∑ v, φ v / π v) := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
          ((frontier_sum_rowPathSum_le G w hw _ hq0 n).trans ?_) (pow_nonneg hL _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hS0 hT _) hQ0
    _ = (∑ n ∈ Finset.range (N + 1), (L * T₀) ^ n) * ∑ v, φ v / π v := by
        rw [Finset.sum_range_succ', add_mul, Finset.sum_mul, pow_zero, one_mul, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [mul_pow]
        ring

end AVRegularity.Providers.WeakGen.Reduction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The passage energy at general masses** (statement only).

`weakPassage_core_energy` with the weak masses replaced by an arbitrary positive mass function
`μ` on the components of the stage, under the hypothesis that the stored total at `μ`,
`∑_e √(μ_src/μ_tgt) · size_e`, is at most `T₀`. The constant
`weakFrontierPassageConst T₀ ρ R = 2 ∑_{n ≤ J_w R_w} (32 T₀² C_edge²)^n` is chosen before the
masses and the data. -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  Construction.Preservation.Ledger CycleJointProofs.PathReduction CoupledEnergy.Variational

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-- The passage constant at stored total `T₀`: `2 ∑_{n ≤ J_w R_w} (32 T₀² C_edge²)^n`. -/
def weakFrontierPassageConst (T₀ ρ : ℝ) (R : WeakPassageRequest A) : ℝ :=
  2 * ∑ n ∈ Finset.range (A.Jw * A.Rw + 1), (32 * T₀ ^ 2 * weakRawEdgeConst ρ R ^ 2) ^ n

/-- **The energy of one passage with data, at arbitrary positive masses `μ` whose stored total
is at most `T₀`.** -/
def WeakGeneralPassageEnergy (R : WeakPassageRequest A) (T₀ : ℝ) : Prop :=
  ∀ (S : WeakRawSetting R)
    (_hfloor : weakEntryPassageCoeffFloor R ≤ S.M) (_hstored : weakQuietStoredFloor A ≤ S.M)
    (L : ℕ) (_hL : S.M ≤ L) (_hLJ : L < S.M + A.Jw) (a b rad : ℝ) (_hab : a ≤ b)
    (_hrad : 0 < rad) (_hrad1 : rad ≤ 1) (m : ℕ) (_hm : m ≤ weakEntryMmax R)
    (_hsmooth : ∀ v u (γ : (S.stage L).fam.Γ v u) d, 2 ≤ d → ∀ k ≤ weakEntryKmax R, ∀ t,
      ContDiff ℝ (k : ℕ) ((S.stage L).physCoeff v u γ d t))
    (μ : CompIn (S.stage L).comps → ℝ) (_hμ : ∀ v, 0 < μ v)
    (_hT : ∑ e : LedgerEdge (S.stage L), Real.sqrt (μ e.2.1 / μ e.1) *
      ((S.stage L).fam.identity e.1 e.2.1 e.2.2).record.size ≤ T₀)
    {Ac : ∀ v u, (d : admissibleOrders
        (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) v u) →
        ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => ScalarH u.1.root) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)}
    (_hA : ∀ v u d, Ac v u d = fun t y => ∑ γ : (S.stage L).fam.Γ v u,
      (S.stage L).physCoeff v u γ d.1 t y)
    (_Rd : TorusCoefficientData (rad * S.D.eps L)
      (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) a b Ac)
    (_hd : TorusDriftData (S.D.κ S.M) (rad * S.D.eps L) a b (streamVel (S.D.Φ L))
      (weakEntryKmax R))
    (_hA_meas : ∀ v u d, Measurable fun p : Set.Icc a b × Vec 2 => Ac v u d p.1 p.2)
    {f : ∀ v : CompIn (S.stage L).comps, TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root)}
    {u : ∀ v : CompIn (S.stage L).comps, ℝ →
      TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root)}
    {w : ∀ v : CompIn (S.stage L).comps, ℝ →
      TorusHk (weakReductionReserve R m v.1 + 1) (ScalarH v.1.root)}
    (_hs : IsCoupledWeakSolutionTorus (S.D.κ S.M) a b (streamVel (S.D.Φ L)) (1 + A.Jw * A.Nw)
      (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) Ac f
      (fun _ _ => 0) (fun _ _ => 0) u w)
    (t : ℝ) (_ht : t ∈ Set.Icc a b),
    ∑ v, (μ v)⁻¹ * factorialNormSq (rad * S.D.eps L) (u v t).val +
      S.D.κ S.M / 2 * ∫ s in Set.Icc a b, ∑ v, (μ v)⁻¹ *
        gradFactorialNormSq (rad * S.D.eps L) (w v s).val ≤
      weakFrontierPassageConst T₀ rad R * ∑ v, (μ v)⁻¹ *
        factorialNormSq (rad * S.D.eps L) (f v).val

end AVRegularity.Providers.WeakGen.Reduction
end
end

section
/-! **Coarse readout energy: the lifted run of a passage instance.**

For a run `r` of a passage instance `c` that starts strictly before the first passage time
(`r.a < r.tq (M + J_w + 1)`), the families of the higher order of the reduction on the clock
with root time `t_{M+J_w+1}` give,
at the offset `m' + D_m - 2`, a weak reduction at the order `K_w + m'`, i.e. a run `rr` of the
instance of the lifted request `weakEntryLiftRequest R m` (the instance `weakCoarseLiftCase`, same
data), on the same clock, whose order-zero values are those of `r`.

Restatements over raw data (the entry lemmas are over `WeakEntryData`):
* `weakReductionReserve_order` -> `weakCoarse_reserve_order`,
  `weakReductionReserve_lift` -> `weakCoarse_reserve_lift`,
  `weakReduction_regSolution_of_coupled` -> `weakCoarse_regSolution_of_coupled`,
  `weakReduction_passageSolution` -> `weakCoarse_passageSolution`,
  `weakReduction_of_coupled` -> `weakCoarse_reduction_of_coupled`.

The degenerate cases are included: `J_w = 1` (one passage, the root window is `[t_{M+2}, T]`),
`m = 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Residual

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  CycleJointProofs Comparison

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The order `K_w + m` lies below the reserves at the offset `m + D_m - 2` (raw data). -/
theorem weakCoarse_reserve_order (S : WeakRawSetting R) (m : ℕ) (c : Comp) :
    R.Kw + m ≤ weakReductionReserve R (m + S.Dm - 2) c := by
  have := S.two_le_Dm
  unfold weakReductionReserve
  omega

/-- The kernel lifts of order `K_w + m + D_m - 1` lie below the lifts at the offset
`m + D_m - 2` (raw data). -/
theorem weakCoarse_reserve_lift (S : WeakRawSetting R) (m : ℕ) (c : Comp) :
    R.Kw + m + S.Dm - 1 ≤ weakReductionReserve R (m + S.Dm - 2) c + 1 := by
  have := S.two_le_Dm
  unfold weakReductionReserve
  omega

/-- **The truncated coupled solution of one passage is the regularized system of the stage**
(raw data version of `weakReduction_regSolution_of_coupled`). -/
theorem weakCoarse_regSolution_of_coupled (S : WeakRawSetting R) (m i : ℕ) (hMi : S.M < i)
    (hi : i ≤ S.M + A.Jw) {t₀ t₁ : ℝ}
    {f : ∀ v : CompIn (S.stage (i - 1)).comps,
      TorusHk (weakReductionReserve R (m + S.Dm - 2) v.1) (ScalarH v.1.root)}
    {u : ∀ v : CompIn (S.stage (i - 1)).comps, ℝ →
      TorusHk (weakReductionReserve R (m + S.Dm - 2) v.1) (ScalarH v.1.root)}
    {w : ∀ v : CompIn (S.stage (i - 1)).comps, ℝ →
      TorusHk (weakReductionReserve R (m + S.Dm - 2) v.1 + 1) (ScalarH v.1.root)}
    (hc : IsCoupledWeakSolutionTorus (S.D.kap (S.stage (i - 1)).level) t₀ t₁
      (streamVel (S.D.Φ (S.stage (i - 1)).level)) (1 + A.Jw * A.Nw)
      (fun v : CompIn (S.stage (i - 1)).comps => weakReductionReserve R (m + S.Dm - 2) v.1)
      (weakStageCoeff S (m + S.Dm - 2) (i - 1)) f (fun _ _ => 0) (fun _ _ => 0) u w) :
    (S.stage (i - 1)).IsRegSolution S.P (fun _ => isoPairedKernel 0 R.nW)
      (fun _ => isoPairedKernel 0 R.nW) A.φ₀ A.hφ₀ (S.D.kap (S.stage (i - 1)).level)
      (streamVel (S.D.Φ (S.stage (i - 1)).level)) (R.Kw + m) t₀ t₁
      (fun v => truncateTorusHk (weakCoarse_reserve_order S m v.1) (f v)) (fun _ _ => 0)
      (fun _ _ => 0) (fun v t => truncateTorusHk (weakCoarse_reserve_order S m v.1) (u v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ (weakCoarse_reserve_order S m v.1)) (w v t))
      (fun _ u' _ t => truncateTorusHk (weakCoarse_reserve_lift S m u'.1) (w u' t)) :=
  regSolution_of_coupled S.P _ _ A.φ₀ A.hφ₀ (S.stage (i - 1)) (by have := S.order_ge; omega)
    (fun v => weakCoarse_reserve_order S m v.1) (fun v => weakCoarse_reserve_lift S m v.1)
    (fun _ _ _ _ _ => rfl)
    (weakStage_physCoeff_nonadmissible S (m + S.Dm - 2) (i - 1)
      (show S.M ≤ i - 1 by omega) (show i - 1 < S.M + A.Jw by omega))
    (fun v u γ s => sysS_isoPairedKernel_zero S.P R.nW A.hφ₀ A.mass (S.stage (i - 1)) v u γ s) hc

/-- **One passage of the families at the offset `m + D_m - 2` is a weak passage solution** after
truncation to `K_w + m` (raw data). -/
theorem weakCoarse_passageSolution (S : WeakRawSetting R) (K : WeakRawClock S) (m : ℕ)
    (Uhi : ∀ i, WeakStageFamily S (m + S.Dm - 2) i)
    (Whi : ∀ i, WeakStageLift S (m + S.Dm - 2) i) (i : ℕ) (hi : S.M < i)
    (hi' : i ≤ S.M + A.Jw) (hp : WeakStagePassage S K (m + S.Dm - 2) Uhi Whi i) :
    IsWeakPassageSolution S.P A.φ₀ A.hφ₀ R.nW (R.Kw + m) (S.stage i) (S.stage (i - 1)) (K.tq i)
      (K.a + A.T₀) (fun v t => truncateTorusHk (weakCoarse_reserve_order S m v.1) (Uhi i v t))
      (fun v t => truncateTorusHk (weakCoarse_reserve_order S m v.1) (Uhi (i - 1) v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ (weakCoarse_reserve_order S m v.1))
        (Whi (i - 1) v t))
      (fun _ u _ t => truncateTorusHk (weakCoarse_reserve_lift S m u.1) (Whi (i - 1) u t)) := by
  have htr := weakStage_terminalTrace S (m + S.Dm - 2) i (Uhi i) (K.tq i)
    (weakCoarse_reserve_order S m)
  have hreg := weakCoarse_regSolution_of_coupled S m i hi hi' hp
  exact ⟨_, htr, hreg⟩

/-- **The clock of a run that starts strictly before the first passage time**: the root time is
`t_{M+J_w+1}`. -/
def weakCoarseClock {c : WeakPassageInstance plan R} (r : WeakPassageRun c)
    (hstart : r.a < r.tq (c.M + A.Jw + 1)) : WeakRawClock (weakPassageRawSetting c) where
  a := r.a
  tq := r.tq
  troot := r.tq (c.M + A.Jw + 1)
  troot_gt := hstart
  troot_ge := le_rfl
  troot_le :=
    (weak_quiet_window c r (c.M + A.Jw) (by have := A.Jw_pos; omega) le_rfl).2.2.1.le
  tq_le := fun i hi hit => (weak_quiet_window c r i hi hit).2.1
  tq_step := fun i hi hit => (weak_quiet_window c r i hi hit).2.2.1.le

/-- **The truncated coupled families at the offset `m + D_m - 2` are a weak reduction** at the
order `K_w + m` for the run `r`, once their root has the value `θ(t)` from `t_{M+J_w+1}` on and
every passage is solved (raw data version of `weakReduction_of_coupled`). -/
theorem weakCoarse_reduction_of_coupled {c : WeakPassageInstance plan R} (r : WeakPassageRun c)
    (hstart : r.a < r.tq (c.M + A.Jw + 1)) (m : ℕ)
    {Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) (m + c.Dm - 2) i}
    {Whi : ∀ i, WeakStageLift (weakPassageRawSetting c) (m + c.Dm - 2) i}
    (hroot : ∀ (hr : (⟨0, []⟩ : Comp) ∈ (c.stage (c.M + A.Jw)).comps),
      ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
        (Uhi (c.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
            (valueIndex2 (weakReductionReserve R (m + c.Dm - 2) (⟨0, []⟩ : Comp))) =ᵐ[
          volume.restrict AVenhance.unitCube] r.θ t)
    (hpass : ∀ i, c.M < i → i ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakCoarseClock r hstart) (m + c.Dm - 2) Uhi Whi
        i) :
    IsWeakReduction c.P A.φ₀ A.hφ₀ R.nW c.M A.Jw (R.Kw + m) 0 r.a (r.a + A.T₀) r.θ c.stage r.tq
      (fun i v t => truncateTorusHk (weakCoarse_reserve_order (weakPassageRawSetting c) m v.1)
        (Uhi i v t))
      (fun i v t => truncateTorusHk
        (Nat.succ_le_succ (weakCoarse_reserve_order (weakPassageRawSetting c) m v.1)) (Whi i v t))
      (fun i _ u _ t => truncateTorusHk
        (weakCoarse_reserve_lift (weakPassageRawSetting c) m u.1) (Whi i u t)) := by
  refine ⟨r.reduction.1, r.reduction.2.1, fun hr t ht => ?_, fun i hi hi' => ?_⟩
  · exact (KernelEnergy.truncateTorusHk_toFunction_jet_ae
      (weakCoarse_reserve_order (weakPassageRawSetting c) m _) (Uhi (c.M + A.Jw) ⟨_, hr⟩ t)
      (valueIndex2 (R.Kw + m))).trans (hroot hr t ht)
  · have hr' := r.reduction.2.2.2 i hi hi'
    exact ⟨hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2.1,
      weakCoarse_passageSolution (weakPassageRawSetting c) (weakCoarseClock r hstart) m Uhi Whi i
        hi hi' (hpass i hi hi')⟩

end AVRegularity.Providers.WeakGen.Residual

namespace AVRegularity.Providers.WeakGen.Residual

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The instance of the lifted request**: the same data as `c`, only the requested Sobolev
order is raised. -/
@[reducible] def weakCoarseLiftCase (pp : WeakPassagePlan) (m : ℕ)
    (hb : pp.baseFloor B ≤ plan.baseFloor B) (hm : pp.momentFloor A ≤ plan.momentFloor A)
    (hl : ∀ j, pp.levelFloor (weakEntryLiftRequest R m) j ≤ plan.levelFloor R j)
    (c : WeakPassageInstance plan R) : WeakPassageInstance pp (weakEntryLiftRequest R m) :=
  { base_ge := hb.trans c.base_ge
    moment_ge := hm.trans c.moment_ge
    j₀ := c.j₀
    carrier := c.carrier
    M := c.M
    level_ge := (hl c.j₀).trans c.level_ge
    D := c.D
    alpha := c.alpha
    q_eq := c.q_eq
    base_eq := c.base_eq
    profile_eq := c.profile_eq
    streams := c.streams
    band := c.band
    terminal := c.terminal
    Dm := c.Dm
    order_ge := c.order_ge
    P := c.P
    stage := c.stage
    construction := c.construction }

/-- The higher reduction at the order `K = K_w + offset`, on the clock of `r`, with the order-zero
values of `r` (raw data version of `weakEntry_high_reduction_at`). -/
theorem weakCoarse_high_reduction_at (hcommon : WeakPassageCommonOK plan)
    {c : WeakPassageInstance plan R} (r : WeakPassageRun c)
    (hstart : r.a < r.tq (c.M + A.Jw + 1)) (offset K : ℕ) (hK : K = R.Kw + offset) :
    ∃ (Ur : (i : ℕ) → ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk K (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (K + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ →
        TorusHk (K + c.Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction c.P A.φ₀ A.hφ₀ R.nW c.M A.Jw K 0 r.a (r.a + A.T₀) r.θ c.stage r.tq
        Ur Urw Urk ∧
      ∀ j, c.M ≤ j → j ≤ c.M + A.Jw → ∀ v : CompIn (c.stage j).comps,
        ∀ t ∈ Set.Icc (r.tq (j + 1)) (r.a + A.T₀),
          truncateTorusHk (Nat.zero_le K) (Ur j v t) =
            truncateTorusHk (Nat.zero_le R.Kw) (r.Ur j v t) := by
  subst K
  refine (weakStage_higher (weakPassageRawSetting c)
    (weakPassage_two_le_M hcommon c) (weakPassage_coeffRegular hcommon c)
    (weakCoarseClock r hstart) r.f r.θ r.scalar r.reduction (offset + c.Dm - 2)).elim
    fun Uhi h1 => h1.elim fun Whi h2 => ?_
  have hroot := h2.1
  have hpass := h2.2.1
  have hvr := h2.2.2.1
  have hval := h2.2.2.2.1
  refine ⟨_, _, _, weakCoarse_reduction_of_coupled r hstart offset hroot hpass, ?_⟩
  intro j hj hj' v t ht
  by_cases hjJ : j = c.M + A.Jw
  · subst hjJ
    exact congrArg (truncateTorusHk (Nat.zero_le R.Kw)) (hvr v t ht)
  · exact congrArg (truncateTorusHk (Nat.zero_le R.Kw))
      (hval (j + 1) (show c.M < j + 1 by omega) (show j + 1 ≤ c.M + A.Jw by omega) v t ht)

/-- **The lifted run**: a run of the instance of the lifted request on the clock of `r`, with the
same order-zero values. -/
theorem weakCoarse_lifted_run (hcommon : WeakPassageCommonOK plan) (pp : WeakPassagePlan) (m : ℕ)
    (hb : pp.baseFloor B ≤ plan.baseFloor B) (hm : pp.momentFloor A ≤ plan.momentFloor A)
    (hl : ∀ j, pp.levelFloor (weakEntryLiftRequest R m) j ≤ plan.levelFloor R j)
    {c : WeakPassageInstance plan R} (r : WeakPassageRun c)
    (hstart : r.a < r.tq (c.M + A.Jw + 1)) :
    ∃ rr : WeakPassageRun (weakCoarseLiftCase pp m hb hm hl c), rr.tq = r.tq ∧ rr.a = r.a ∧
      ∀ j, c.M ≤ j → j ≤ c.M + A.Jw → ∀ v : CompIn (c.stage j).comps,
        ∀ t ∈ Set.Icc (r.tq (j + 1)) (r.a + A.T₀),
          truncateTorusHk (Nat.zero_le _) (rr.Ur j v t) =
            truncateTorusHk (Nat.zero_le R.Kw) (r.Ur j v t) := by
  refine (weakCoarse_high_reduction_at hcommon r hstart
    (m + A.Jw * A.Rw * (A.Jw * A.Nw - 1)) (weakEntryLiftRequest R m).Kw
    (by dsimp [weakEntryLiftRequest]; omega)).elim fun Ur h1 => h1.elim fun Urw h2 =>
    h2.elim fun Urk h3 => ?_
  have hred := h3.1
  have hv := h3.2
  let rr : WeakPassageRun (weakCoarseLiftCase pp m hb hm hl c) :=
    { a := r.a
      f := r.f
      θ := r.θ
      scalar := r.scalar
      tq := r.tq
      Ur := Ur
      Urw := Urw
      Urk := Urk
      reduction := hred }
  exact ⟨rr, rfl, rfl, hv⟩

end AVRegularity.Providers.WeakGen.Residual
end
end
end
