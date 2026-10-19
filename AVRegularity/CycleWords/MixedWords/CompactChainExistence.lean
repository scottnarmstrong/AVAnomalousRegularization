-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.B1WH3Abstract
public import AVRegularity.CycleWords.Assembly.MixedWordsB1SharpSlow
import AVRegularity.CycleJoint.Assembly.MeanNormalizedBlocks
import AVRegularity.Proofs.Intermediate.Weighted.CycleMixedWordsExists
import AVRegularity.Construction.Preservation.Seed.SeedLedgerDecayConversion
public import AVRegularity.CycleJoint.Assembly.CycleJointOfIngredients
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp pass: the activity facts of the package

At an active time (`IsActiveTime`: the drift is nonzero somewhere) the drift is a shear of one
orientation.
* All windows whose enlarged interval `[lo − D, hi + D]` contains an active time have the same
  orientation (`ext_orient_eq`). Two shears of different orientations agree only if both vanish
  (`ext_agree`, `ext_shear`).
* An active time of the piece lies in a window (`active_mem_window`, from `cover` and
  `quiet_zero`).
* Two active times at distance `≤ D` lie in windows of the same orientation (`active_orient_eq`).
* **Where the activity weight exceeds `1`**, in the regime `Λ e^{-cD/2} ≤ 1`, every least window
  at `r` has the orientation `e(r)` of the last activity (`least_orient_eq_activityOrient`). So
  the window clauses of the sharp slow test and the sharp stage-transform families, stated for `IsLeastWindow`, apply with `e(r)`. -/

variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {t₀ S ϖ : ℝ} {reg : BlockRegions}

/-- Windows whose enlarged intervals share an active time have the same orientation. -/
theorem ext_orient_eq (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (p p' : Fin reg.P) {τ : ℝ}
    (hτ : τ ∈ Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer))
    (hτ' : τ ∈ Icc (reg.lo p' - reg.buffer) (reg.hi p' + reg.buffer))
    (hact : IsActiveTime v τ) : reg.orient p = reg.orient p' := by
  by_contra hne
  obtain ⟨z, hz⟩ := hact
  obtain ⟨V, hV⟩ := pkg.ext_shear p
  obtain ⟨V', hV'⟩ := pkg.ext_shear p'
  have h1 := pkg.ext_agree p τ hτ z
  have h2 := pkg.ext_agree p' τ hτ' z
  rw [hV] at h1
  rw [hV'] at h2
  have heq : V τ (z (reg.orient p).rev) • basisVec (reg.orient p) =
      V' τ (z (reg.orient p').rev) • basisVec (reg.orient p') := h1.trans h2.symm
  have hc := congrFun heq (reg.orient p)
  simp only [Pi.smul_apply, basisVec_apply, smul_eq_mul, ite_true, mul_one] at hc
  simp only [hne, ite_false, mul_zero] at hc
  apply hz
  rw [← h1, hc, zero_smul]

/-- An active time of the piece lies in a window. -/
theorem active_mem_window (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {τ : ℝ}
    (hτ : τ ∈ Icc t₀ (t₀ + S)) (hact : IsActiveTime v τ) :
    ∃ p : Fin reg.P, τ ∈ Icc (reg.lo p) (reg.hi p) := by
  rcases pkg.cover τ hτ with hq | hp
  · obtain ⟨z, hz⟩ := hact
    exact absurd (pkg.quiet_zero τ ⟨hq, hτ⟩ z) hz
  · exact hp

/-- Two active times at distance at most `D` lie in windows of the same orientation. -/
theorem active_orient_eq (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {τ₁ τ₂ : ℝ}
    {p₁ p₂ : Fin reg.P} (h₁ : τ₁ ∈ Icc (reg.lo p₁) (reg.hi p₁))
    (h₂ : τ₂ ∈ Icc (reg.lo p₂) (reg.hi p₂)) (hact : IsActiveTime v τ₂)
    (hd : |τ₁ - τ₂| ≤ reg.buffer) : reg.orient p₁ = reg.orient p₂ := by
  have hD := pkg.buffer_nonneg
  have hab := abs_le.1 hd
  refine ext_orient_eq pkg p₁ p₂ ⟨?_, ?_⟩ ⟨?_, ?_⟩ hact
  · linarith [h₁.1]
  · linarith [h₁.2]
  · linarith [h₂.1]
  · linarith [h₂.2]

/-- Where the activity weight exceeds `1`, there is an active time `τ' ∈ (r − D/2, r]`, after
`τ(r) − D`, and the buffer is positive. -/
theorem exists_active_of_weight {Λ c : ℝ} (hc : 0 < c)
    (hΛ : Λ * Real.exp (-c * (reg.buffer / 2)) ≤ 1) {r : ℝ}
    (hΩ : 1 < activityWeight v t₀ Λ c r) :
    0 < reg.buffer ∧ ∃ τ' ∈ activeSet v t₀ r, r - reg.buffer / 2 < τ' ∧
      lastActive v t₀ r - reg.buffer < τ' := by
  have hne : (activeSet v t₀ r).Nonempty := by
    by_contra h
    unfold activityWeight at hΩ
    simp only [h, ite_false] at hΩ
    exact lt_irrefl _ hΩ
  have hτr : lastActive v t₀ r ≤ r := csSup_le hne fun x hx => hx.1.2
  have hgt : 1 < Λ * Real.exp (-c * (r - lastActive v t₀ r)) := by
    unfold activityWeight at hΩ
    simp only [hne, ite_true] at hΩ
    rcases le_total 1 (Λ * Real.exp (-c * (r - lastActive v t₀ r))) with h | h
    · rw [max_eq_right h] at hΩ
      exact hΩ
    · rw [max_eq_left h] at hΩ
      exact absurd hΩ (lt_irrefl _)
  have hΛ0 : 0 < Λ := by
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h (Real.exp_pos (-c * (r - lastActive v t₀ r))).le
    linarith
  have hclose : r - lastActive v t₀ r < reg.buffer / 2 := by
    by_contra h
    push Not at h
    have he : Real.exp (-c * (r - lastActive v t₀ r)) ≤ Real.exp (-c * (reg.buffer / 2)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have := mul_le_mul_of_nonneg_left he hΛ0.le
    linarith
  have hDpos : 0 < reg.buffer := by linarith [hτr]
  obtain ⟨τ', hτ'mem, hτ'gt⟩ := exists_lt_of_lt_csSup hne
    (show max (r - reg.buffer / 2) (lastActive v t₀ r - reg.buffer) < lastActive v t₀ r from
      max_lt (by linarith) (by linarith))
  exact ⟨hDpos, τ', hτ'mem, lt_of_le_of_lt (le_max_left _ _) hτ'gt,
    lt_of_le_of_lt (le_max_right _ _) hτ'gt⟩

/-- **Where the activity weight exceeds `1`, a least window exists.** -/
theorem exists_leastWindow_of_weight (pkg : CoreScalarPackage K η G v t₀ S ϖ reg)
    {Λ c : ℝ} (hc : 0 < c) (hΛ : Λ * Real.exp (-c * (reg.buffer / 2)) ≤ 1) {r : ℝ}
    (hr : r ≤ t₀ + S) (hΩ : 1 < activityWeight v t₀ Λ c r) : ∃ p, IsLeastWindow reg p r := by
  classical
  obtain ⟨-, τ', hτ'mem, hτ'1, -⟩ := exists_active_of_weight hc hΛ hΩ
  obtain ⟨p₁, hp₁⟩ := active_mem_window pkg ⟨hτ'mem.1.1, hτ'mem.1.2.trans hr⟩ hτ'mem.2
  set F := Finset.univ.filter (fun p : Fin reg.P => reg.lo p ≤ reg.hi p ∧
    r ∈ Icc (reg.lo p) (reg.hi p + reg.buffer / 2)) with hF
  have hp₁F : p₁ ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hp₁.1.trans hp₁.2,
    hp₁.1.trans hτ'mem.1.2, by linarith [hp₁.2]⟩
  have hFne : F.Nonempty := ⟨p₁, hp₁F⟩
  have hmin := Finset.min'_mem F hFne
  refine ⟨F.min' hFne, (Finset.mem_filter.1 hmin).2.2, (Finset.mem_filter.1 hmin).2.1,
    fun p' hp' hlo hmem => ?_⟩
  have := Finset.min'_le F p' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlo, hmem⟩)
  exact absurd hp' (not_lt.2 this)

/-- **Where the activity weight exceeds `1`, every least window has the orientation of the last
activity.** -/
theorem least_orient_eq_activityOrient (pkg : CoreScalarPackage K η G v t₀ S ϖ reg)
    {Λ c : ℝ} (hc : 0 < c) (hΛ : Λ * Real.exp (-c * (reg.buffer / 2)) ≤ 1) {r : ℝ}
    (hr : r ∈ Icc t₀ (t₀ + S)) (hΩ : 1 < activityWeight v t₀ Λ c r) (p : Fin reg.P)
    (hp : IsLeastWindow reg p r) : reg.orient p = activityOrient reg v t₀ r := by
  classical
  have hne : (activeSet v t₀ r).Nonempty := by
    by_contra h
    unfold activityWeight at hΩ
    simp only [h, ite_false] at hΩ
    exact lt_irrefl _ hΩ
  have hbdd : BddAbove (activeSet v t₀ r) := ⟨r, fun x hx => hx.1.2⟩
  obtain ⟨-, τ', hτ'mem, hτ'1, hτ'2⟩ := exists_active_of_weight hc hΛ hΩ
  have hτ'le : τ' ≤ lastActive v t₀ r := le_csSup hbdd hτ'mem
  have hτ'S : τ' ∈ Icc t₀ (t₀ + S) := ⟨hτ'mem.1.1, hτ'mem.1.2.trans hr.2⟩
  obtain ⟨p₁, hp₁⟩ := active_mem_window pkg hτ'S hτ'mem.2
  -- the least window has the orientation of `τ'`
  have hpp₁ : reg.orient p = reg.orient p₁ := by
    refine ext_orient_eq pkg p p₁ ⟨?_, ?_⟩ ⟨?_, ?_⟩ hτ'mem.2
    · linarith [hp.1.1]
    · linarith [hp.1.2, hτ'mem.1.2]
    · linarith [hp₁.1]
    · linarith [hp₁.2]
  -- and so has the window chosen by `activityOrient`
  have hex : ∃ p : Fin reg.P, ∃ τ ∈ activeSet v t₀ r, lastActive v t₀ r - reg.buffer < τ ∧
      τ ∈ Icc (reg.lo p) (reg.hi p) := ⟨p₁, τ', hτ'mem, hτ'2, hp₁⟩
  unfold activityOrient
  rw [dite_eq_left hex]
  obtain ⟨τ'', hτ''mem, hτ''gt, hτ''w⟩ := hex.choose_spec
  have hτ''le : τ'' ≤ lastActive v t₀ r := le_csSup hbdd hτ''mem
  rw [hpp₁]
  refine active_orient_eq pkg hp₁ hτ''w hτ''mem.2 (abs_le.2 ⟨?_, ?_⟩) <;> linarith

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleJointProofs
open AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp fast decay: mean plumbing between `H^j` carriers and `L²` classes

Constants in `TorusHk j ℂ` have the norm of their value; removing the mean from an `H^j` carrier
realizes the mean-free `L²` class `cellQ0CLM`. -/

/-- The value of a constant carrier is the constant class. -/
theorem sharpMean_value_const (j : ℕ) (c : ℂ) :
    torusHkValueCLM (torusConstantCarrier j c) = cellConstantCLM c := by
  apply Lp.ext
  filter_upwards [periodicJetRepresentative_ae (torusConstantCarrier j c).val (valueIndex2 j),
    torusConstantCarrier_raw_value_ae j c, cellConstantCLM_ae c] with x h1 h2 h3
  rw [h3]
  exact h1.symm.trans h2

/-- The mean of the carrier is the mean of its value. -/
theorem sharpMean_torusMean (j : ℕ) (w : TorusHk j ℂ) :
    torusMean w = cellMean (torusHkValueCLM w) := by
  unfold torusMean cellMean
  apply integral_congr_ae
  filter_upwards [periodicJetRepresentative_ae w.val (valueIndex2 j)] with x h1
  exact h1

/-- A constant carrier has the norm of its value. -/
theorem sharpMean_const_norm (j : ℕ) (c : ℂ) : ‖torusConstantCarrier j c‖ = ‖c‖ := by
  have hz : ∀ a : JetIndex2 j, a ≠ valueIndex2 j → (torusConstantCarrier j c).val a = 0 := by
    intro a ha
    refine torusConstantCarrier_positive_jet_zero j c a ?_
    obtain ⟨i, w⟩ := a
    rcases Nat.eq_zero_or_pos i.val with h | h
    · exfalso
      apply ha
      have hi : i = 0 := Fin.ext h
      subst hi
      have hk : ∀ k : Fin ((0 : Fin (j + 1)) : ℕ), False := fun k => by
        have := k.isLt
        simp at this
      have : w = Fin.elim0 := by
        funext k
        exact (hk k).elim
      subst this
      rfl
    · exact h
  have hv : ‖(torusConstantCarrier j c).val (valueIndex2 j)‖ = ‖c‖ := by
    have := sharpMean_value_const j c
    change ‖torusHkValueCLM (torusConstantCarrier j c)‖ = _
    rw [this, cellConstantCLM_norm]
  change ‖(torusConstantCarrier j c).val‖ = _
  rw [PiLp.norm_eq_of_L2, Finset.sum_eq_single (valueIndex2 j)]
  · rw [hv, Real.sqrt_sq (norm_nonneg _)]
  · intro a _ ha
    rw [hz a ha]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Mean-free representative: an `H^j` representative of the mean-free class of the value. -/
theorem sharpMean_q0_rep (j : ℕ) (w₀ : TorusHk j ℂ) :
    ∃ w' : TorusHk j ℂ, torusHkValueCLM w' = cellQ0CLM (torusHkValueCLM w₀) ∧
      ‖w'‖ ≤ 2 * ‖w₀‖ := by
  refine ⟨meanComplement j w₀, ?_, ?_⟩
  · rw [meanComplement_apply, map_sub, sharpMean_value_const, sharpMean_torusMean,
      ← cellMeanCLM_apply]
    rfl
  · rw [meanComplement_apply]
    calc ‖w₀ - torusConstantCarrier j (torusMean w₀)‖
        ≤ ‖w₀‖ + ‖torusConstantCarrier j (torusMean w₀)‖ := norm_sub_le _ _
      _ = ‖w₀‖ + ‖torusMean w₀‖ := by rw [sharpMean_const_norm]
      _ ≤ ‖w₀‖ + ‖w₀‖ := by
        have h1 : ‖torusMean w₀‖ ≤ ‖torusHkValueCLM w₀‖ := by
          rw [sharpMean_torusMean, ← cellMeanCLM_apply]
          exact cellMeanCLM_norm_le _
        have h2 : ‖torusHkValueCLM w₀‖ ≤ ‖w₀‖ := PiLp.norm_apply_le w₀.val (valueIndex2 j)
        linarith
      _ = 2 * ‖w₀‖ := by ring

/-- Adding a constant to an `H^j` carrier. -/
theorem sharpMean_add_const (j : ℕ) (w' : TorusHk j ℂ) (c : ℂ) :
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = torusHkValueCLM w' + cellConstantCLM c ∧
      ‖w‖ ≤ ‖w'‖ + ‖c‖ := by
  refine ⟨w' + torusConstantCarrier j c, ?_, ?_⟩
  · rw [map_add, sharpMean_value_const]
  · calc ‖w' + torusConstantCarrier j c‖ ≤ ‖w'‖ + ‖torusConstantCarrier j c‖ := norm_add_le _ _
      _ = ‖w'‖ + ‖c‖ := by rw [sharpMean_const_norm]

end AVRegularity.CycleWords.Assembly
end
end

section
section
/-! # The drift cut off outside `[s, t]`, and transversality along `[s, t]`

`revCurve_transverse` asks the drift to be invariant along `e` at EVERY time. In case 1 of 29b
the drift is a shear along `e` (or zero) only on `[s, t]`, so the drift is cut off outside
`[s, t]` (`cutDrift`). The cut drift keeps the hypotheses (`TransverseLocalHyp.cut`) and agrees
with the drift on `[s, t]`. By `sharpRevCurve_congr`, the reversed curve on `[−t, −s]` is a curve
of the cut drift. So a datum transverse to `e` stays transverse along `[s, t]`
(`revCurve_transverse_cut`).

Where every active time of `[s, t]` lies in a window of orientation `e`, the drift is invariant
along `e` there (`drift_invariant_of_active`, from `ext_agree` and `ext_shear`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Assembly

/-- The drift cut off outside `[s, t]`. -/
def cutDrift (v : ℝ → Vec 2 → Vec 2) (s t : ℝ) : ℝ → Vec 2 → Vec 2 :=
  fun τ z => (Icc s t).indicator (fun τ' => v τ' z) τ

theorem cutDrift_of_mem {v : ℝ → Vec 2 → Vec 2} {s t τ : ℝ} (h : τ ∈ Icc s t) :
    cutDrift v s t τ = v τ := funext fun z => by simp [cutDrift, Set.indicator_of_mem h]

theorem cutDrift_of_notMem {v : ℝ → Vec 2 → Vec 2} {s t τ : ℝ} (h : τ ∉ Icc s t) :
    cutDrift v s t τ = 0 := funext fun z => by simp [cutDrift, Set.indicator_of_notMem h]

/-- The cut drift at a time is the drift or `0`. -/
theorem cutDrift_cases (v : ℝ → Vec 2 → Vec 2) (s t τ : ℝ) :
    cutDrift v s t τ = v τ ∨ cutDrift v s t τ = 0 := by
  by_cases h : τ ∈ Icc s t
  · exact Or.inl (cutDrift_of_mem h)
  · exact Or.inr (cutDrift_of_notMem h)

theorem isCellDrift_cut {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (s t : ℝ) :
    IsCellDrift (cutDrift v s t) := by
  obtain ⟨hmeas, ⟨M, hM⟩, hper, hdiv⟩ := hv
  refine ⟨?_, ⟨M, fun τ z => ?_⟩, fun τ => ?_, fun τ φ => ?_⟩
  · have : (fun p : ℝ × Vec 2 => cutDrift v s t p.1 p.2) =
        (Icc s t ×ˢ (univ : Set (Vec 2))).indicator (fun p : ℝ × Vec 2 => v p.1 p.2) := by
      funext p
      by_cases h : p.1 ∈ Icc s t
      · simp [cutDrift, Set.indicator_of_mem h, Set.indicator_of_mem (show p ∈ Icc s t ×ˢ
          (univ : Set (Vec 2)) from ⟨h, mem_univ _⟩)]
      · simp [cutDrift, Set.indicator_of_notMem h, Set.indicator_of_notMem (show p ∉ Icc s t ×ˢ
          (univ : Set (Vec 2)) from fun hp => h hp.1)]
    rw [this]
    exact hmeas.indicator (measurableSet_Icc.prod MeasurableSet.univ)
  · rcases cutDrift_cases v s t τ with h | h <;> rw [h]
    · exact hM τ z
    · simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero]
      exact sq_nonneg M
  · rcases cutDrift_cases v s t τ with h | h <;> rw [h]
    · exact hper τ
    · intro m y
      rfl
  · rcases cutDrift_cases v s t τ with h | h <;> rw [h]
    · exact hdiv τ φ
    · simp

variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {ξ : Fin 2 → ℂ}

/-- The cut drift keeps the hypotheses. -/
theorem TransverseLocalHyp.cut (H : TransverseLocalHyp K η G v ξ) (s t : ℝ) :
    TransverseLocalHyp K η G (cutDrift v s t) ξ where
  hη0 := H.hη0
  hη := H.hη
  hCg := H.hCg
  hCw := H.hCw
  hG := H.hG
  hv := isCellDrift_cut H.hv s t
  hm := fun τ j => by
    rcases cutDrift_cases v s t τ with h | h <;> rw [h]
    · exact H.hm τ j
    · simp [cellMean]
  hw := fun τ x => by
    rcases cutDrift_cases v s t τ with h | h <;> rw [h]
    · exact H.hw τ x
    · simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, Real.sqrt_zero, mul_zero]
      exact H.hCw
  hreal := H.hreal
  hξ := H.hξ
  hsep := H.hsep

/-- **Transversality along `[s, t]`** when the drift is invariant along `e` there. -/
theorem revCurve_transverse_cut (H : TransverseLocalHyp K η G v ξ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) (e : Fin 2) {s t : ℝ} (hst : s ≤ t)
    (hinv : ∀ τ ∈ Icc s t, ∀ (z : Vec 2) (r : ℝ), v τ (z + r • basisVec e) = v τ z)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (hu : IsRevCurve H V hb' (-t) (-s) u slice)
    (hi : cellTransverseProjection e (u (-t)) = u (-t)) :
    ∀ τ ∈ Icc (-t) (-s), cellTransverseProjection e (u τ) = u τ := by
  have Hc := H.cut s t
  have hbc : ∀ σ x, ∑ i, (-cutDrift v s t (-σ) x) i ^ 2 ≤ V ^ 2 := by
    intro σ x
    rcases cutDrift_cases v s t (-σ) with h | h <;> rw [h]
    · exact hb' σ x
    · simp only [Pi.zero_apply, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero]
      exact sq_nonneg V
  have hagree : ∀ τ ∈ Icc (-t) (-s), v (-τ) = cutDrift v s t (-τ) := fun τ hτ =>
    (cutDrift_of_mem ⟨by linarith [hτ.2], by linarith [hτ.1]⟩).symm
  have huc : IsRevCurve Hc V hbc (-t) (-s) u slice :=
    sharpRevCurve_congr H Hc V V hb' hbc hagree hu
  refine revCurve_transverse Hc V hbc e (fun τ z r => ?_) (by linarith) huc hi
  by_cases h : τ ∈ Icc s t
  · rw [cutDrift_of_mem h]
    exact hinv τ h z r
  · rw [cutDrift_of_notMem h]
    rfl

variable {t₀ S ϖ : ℝ} {reg : BlockRegions}

/-- **The drift is invariant along `e` at a time whose activity, if any, lies in a window of
orientation `e`.** -/
theorem drift_invariant_of_active (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (e : Fin 2)
    {τ : ℝ} (h : IsActiveTime v τ → ∃ p, τ ∈ Icc (reg.lo p) (reg.hi p) ∧ reg.orient p = e) :
    ∀ (z : Vec 2) (r : ℝ), v τ (z + r • basisVec e) = v τ z := by
  intro z r
  by_cases hact : IsActiveTime v τ
  · obtain ⟨p, hp, hpe⟩ := h hact
    have hE : τ ∈ Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer) :=
      ⟨by linarith [hp.1, pkg.buffer_nonneg], by linarith [hp.2, pkg.buffer_nonneg]⟩
    obtain ⟨V, hV⟩ := pkg.ext_shear p
    have hne : e.rev ≠ e := by fin_cases e <;> decide
    rw [← pkg.ext_agree p τ hE, ← pkg.ext_agree p τ hE, hV, hV, hpe]
    congr 2
    simp only [Pi.add_apply, Pi.smul_apply, basisVec_apply, smul_eq_mul, hne, ite_false,
      mul_zero, add_zero]
  · have h0 : ∀ y, v τ y = 0 := fun y => by
      by_contra hy
      exact hact ⟨y, hy⟩
    rw [h0, h0]

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The activity geometry

An active time `τ` of the piece has an orientation: that of any window containing it
(`IsOrientedActive`). Active times of different orientations are more than `D` apart
(`oriented_far`).

* `activityOrient_spec`: with activity before `r` and `D > 0`, there is an active time in
  `(τ(r) − D, τ(r)]`, and every active time within `D` of it has the orientation `e(r)`.
* `weight_close`: where the weight exceeds `1` (regime `Λ e^{-cD/2} ≤ 1`), `r − τ(r) < D/2`.
* `crossing_point` (case 2 of 29b): if the weight at `s` exceeds `1` and `(s, t]` contains an
  active time of the other orientation, there is `γ ∈ [s + D/4, t]` with no active time in
  `(γ − 3D/4, γ]`.
* `same_orient_invariant` (case 1): if every active time of `(s, t]` has the orientation `e(s)`,
  the drift is invariant along `e(s)` on `[s, t]`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Assembly

variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
  {t₀ S ϖ : ℝ} {reg : BlockRegions}

/-- `τ` is an active time lying in a window of orientation `e`. -/
def IsOrientedActive (reg : BlockRegions) (v : ℝ → Vec 2 → Vec 2) (τ : ℝ) (e : Fin 2) : Prop :=
  IsActiveTime v τ ∧ ∃ p : Fin reg.P, τ ∈ Icc (reg.lo p) (reg.hi p) ∧ reg.orient p = e

/-- An active time of the piece is oriented. -/
theorem oriented_of_active (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {τ : ℝ}
    (hτ : τ ∈ Icc t₀ (t₀ + S)) (hact : IsActiveTime v τ) :
    ∃ e, IsOrientedActive reg v τ e := by
  obtain ⟨p, hp⟩ := active_mem_window pkg hτ hact
  exact ⟨reg.orient p, hact, p, hp, rfl⟩

/-- Oriented active times within `D` of each other have the same orientation. -/
theorem oriented_same (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {τ₁ τ₂ : ℝ} {e₁ e₂ : Fin 2}
    (h₁ : IsOrientedActive reg v τ₁ e₁) (h₂ : IsOrientedActive reg v τ₂ e₂)
    (hd : |τ₁ - τ₂| ≤ reg.buffer) : e₁ = e₂ := by
  obtain ⟨-, p₁, hp₁, rfl⟩ := h₁
  obtain ⟨hact₂, p₂, hp₂, rfl⟩ := h₂
  exact active_orient_eq pkg hp₁ hp₂ hact₂ hd

/-- Oriented active times of different orientations are more than `D` apart. -/
theorem oriented_far (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {τ₁ τ₂ : ℝ} {e₁ e₂ : Fin 2}
    (h₁ : IsOrientedActive reg v τ₁ e₁) (h₂ : IsOrientedActive reg v τ₂ e₂) (hne : e₁ ≠ e₂) :
    reg.buffer < |τ₁ - τ₂| := by
  by_contra h
  exact hne (oriented_same pkg h₁ h₂ (not_lt.1 h))

/-- **The orientation of the last activity.** -/
theorem activityOrient_spec (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {r : ℝ}
    (hr : r ≤ t₀ + S) (hne : (activeSet v t₀ r).Nonempty) (hD : 0 < reg.buffer) :
    ∃ τ ∈ activeSet v t₀ r, lastActive v t₀ r - reg.buffer < τ ∧
      IsOrientedActive reg v τ (activityOrient reg v t₀ r) := by
  classical
  have hbdd : BddAbove (activeSet v t₀ r) := ⟨r, fun x hx => hx.1.2⟩
  obtain ⟨τ, hτ, hτgt⟩ := exists_lt_of_lt_csSup hne
    (show lastActive v t₀ r - reg.buffer < lastActive v t₀ r by linarith)
  obtain ⟨p, hp⟩ := active_mem_window pkg ⟨hτ.1.1, hτ.1.2.trans hr⟩ hτ.2
  have hex : ∃ p : Fin reg.P, ∃ τ ∈ activeSet v t₀ r, lastActive v t₀ r - reg.buffer < τ ∧
      τ ∈ Icc (reg.lo p) (reg.hi p) := ⟨p, τ, hτ, hτgt, hp⟩
  obtain ⟨τ'', hτ''mem, hτ''gt, hτ''w⟩ := hex.choose_spec
  refine ⟨τ'', hτ''mem, hτ''gt, hτ''mem.2, hex.choose, hτ''w, ?_⟩
  unfold activityOrient
  rw [dite_eq_left hex]

/-- Where the weight exceeds `1`, the last activity is less than `D/2` behind. -/
theorem weight_close {Λ c : ℝ} (hc : 0 < c) (hΛ : Λ * Real.exp (-c * (reg.buffer / 2)) ≤ 1)
    {r : ℝ} (hΩ : 1 < activityWeight v t₀ Λ c r) :
    (activeSet v t₀ r).Nonempty ∧ 0 < reg.buffer ∧ r - lastActive v t₀ r < reg.buffer / 2 := by
  obtain ⟨hD, τ', hτ'mem, hτ'1, -⟩ := exists_active_of_weight (reg := reg) hc hΛ hΩ
  have hle : τ' ≤ lastActive v t₀ r := le_csSup ⟨r, fun x hx => hx.1.2⟩ hτ'mem
  exact ⟨⟨τ', hτ'mem⟩, hD, by linarith⟩

/-- Every active time of `(τ(r) − D, τ(r)]` has the orientation `e(r)`. -/
theorem oriented_near_last (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {r : ℝ}
    (hr : r ≤ t₀ + S) (hne : (activeSet v t₀ r).Nonempty) (hD : 0 < reg.buffer) {τ : ℝ}
    (hτ : τ ∈ activeSet v t₀ r) (hτgt : lastActive v t₀ r - reg.buffer < τ) :
    IsOrientedActive reg v τ (activityOrient reg v t₀ r) := by
  obtain ⟨τe, hτe, hτegt, hor⟩ := activityOrient_spec pkg hr hne hD
  have hbdd : BddAbove (activeSet v t₀ r) := ⟨r, fun x hx => hx.1.2⟩
  have h1 : τ ≤ lastActive v t₀ r := le_csSup hbdd hτ
  have h2 : τe ≤ lastActive v t₀ r := le_csSup hbdd hτe
  obtain ⟨e', he'⟩ := oriented_of_active pkg ⟨hτ.1.1, hτ.1.2.trans hr⟩ hτ.2
  have := oriented_same pkg he' hor (abs_le.2 ⟨by linarith, by linarith⟩)
  rwa [this] at he'

/-- **The crossing point** (case 2 of 29b). -/
theorem crossing_point (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {Λ c : ℝ} (hc : 0 < c)
    (hΛ : Λ * Real.exp (-c * (reg.buffer / 2)) ≤ 1) {s t : ℝ} (hst : s ≤ t) (ht : t ≤ t₀ + S)
    (hΩ : 1 < activityWeight v t₀ Λ c s) {τ' : ℝ} {e' : Fin 2} (hτ' : τ' ∈ Ioc s t)
    (hor : IsOrientedActive reg v τ' e') (hne : e' ≠ activityOrient reg v t₀ s) :
    ∃ γ ∈ Icc s t, reg.buffer / 4 ≤ γ - s ∧
      ∀ τ ∈ Ioc (γ - 3 * reg.buffer / 4) γ, τ ∈ Icc t₀ (t₀ + S) → ¬ IsActiveTime v τ := by
  classical
  obtain ⟨hnes, hD, hclose⟩ := weight_close (reg := reg) hc hΛ hΩ
  have hs : s ≤ t₀ + S := hst.trans ht
  set e := activityOrient reg v t₀ s with he
  have hbdd : BddAbove (activeSet v t₀ s) := ⟨s, fun x hx => hx.1.2⟩
  -- the active times of the other orientation after `s` lie at `τ(s) + D` or later
  have hfar : ∀ τ ∈ Ioc s t, ∀ e₂, e₂ ≠ e → IsOrientedActive reg v τ e₂ →
      lastActive v t₀ s + reg.buffer ≤ τ := by
    intro τ hτ e₂ he₂ hτo
    by_contra hlt
    push Not at hlt
    obtain ⟨τx, hτx, hτxgt⟩ := exists_lt_of_lt_csSup hnes
      (show max (τ - reg.buffer) (lastActive v t₀ s - reg.buffer) < lastActive v t₀ s from
        max_lt (by linarith) (by linarith))
    have hx := oriented_near_last pkg hs hnes hD hτx (lt_of_le_of_lt (le_max_right _ _) hτxgt)
    have hxle : τx ≤ s := hτx.1.2
    have := oriented_far pkg hτo hx he₂
    rw [abs_of_pos (by linarith [hτ.1])] at this
    linarith [lt_of_le_of_lt (le_max_left _ _) hτxgt]
  -- the first such time
  set A : Set ℝ := {τ | τ ∈ Ioc s t ∧ ∃ e₂, e₂ ≠ e ∧ IsOrientedActive reg v τ e₂} with hA
  have hAne : A.Nonempty := ⟨τ', hτ', e', hne, hor⟩
  have hAbdd : BddBelow A := ⟨s, fun x hx => hx.1.1.le⟩
  set γ₀ := sInf A with hγ₀
  have hγ₀far : lastActive v t₀ s + reg.buffer ≤ γ₀ :=
    le_csInf hAne fun τ hτ => by
      obtain ⟨hτI, e₂, he₂, hτo⟩ := hτ
      exact hfar τ hτI e₂ he₂ hτo
  have hγ₀t : γ₀ ≤ t := (csInf_le hAbdd ⟨hτ', e', hne, hor⟩).trans hτ'.2
  -- no activity in `(γ₀ − D, γ₀)`
  have hgap : ∀ τ ∈ Ioo (γ₀ - reg.buffer) γ₀, τ ∈ Icc t₀ (t₀ + S) → ¬ IsActiveTime v τ := by
    intro τ hτ hτS hact
    obtain ⟨eτ, hτo⟩ := oriented_of_active pkg hτS hact
    by_cases heq : eτ = e
    · -- a later time of the other orientation within `D`
      obtain ⟨τa, hτa, hτalt⟩ := exists_lt_of_csInf_lt hAne
        (show γ₀ < τ + reg.buffer by linarith [hτ.1])
      obtain ⟨hτaI, e₂, he₂, hτao⟩ := hτa
      have hge : γ₀ ≤ τa := csInf_le hAbdd ⟨hτaI, e₂, he₂, hτao⟩
      have := oriented_far pkg hτao hτo (by rw [heq]; exact he₂)
      rw [abs_of_pos (by linarith [hτ.2])] at this
      linarith
    · by_cases hτs : s < τ
      · have hmem : τ ∈ A := ⟨⟨hτs, by linarith [hτ.2]⟩, eτ, heq, hτo⟩
        have := csInf_le hAbdd hmem
        linarith [hτ.2]
      · push Not at hτs
        have hτle : τ ≤ lastActive v t₀ s :=
          le_csSup hbdd ⟨⟨hτS.1, hτs⟩, hact⟩
        linarith [hτ.1]
  refine ⟨γ₀ - reg.buffer / 4, ⟨by linarith, by linarith⟩, by linarith, fun τ hτ hτS => ?_⟩
  exact hgap τ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩ hτS

/-- **Case 1 of 29b: the drift is invariant along `e(s)` on `[s, t]`.** -/
theorem same_orient_invariant (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {s t : ℝ}
    (hs : t₀ ≤ s) (hst : s ≤ t) (ht : t ≤ t₀ + S) (hD : 0 < reg.buffer)
    (hcase : ∀ τ ∈ Ioc s t, ∀ e', IsOrientedActive reg v τ e' →
      e' = activityOrient reg v t₀ s) :
    ∀ τ ∈ Icc s t, ∀ (z : Vec 2) (r : ℝ),
      v τ (z + r • basisVec (activityOrient reg v t₀ s)) = v τ z := by
  intro τ hτ
  apply drift_invariant_of_active pkg
  intro hact
  obtain ⟨p, hp⟩ := active_mem_window pkg ⟨hs.trans hτ.1, hτ.2.trans ht⟩ hact
  refine ⟨p, hp, ?_⟩
  rcases eq_or_lt_of_le hτ.1 with heq | hlt
  · -- `τ = s` is active, so it is the last activity at `s`
    have hacts : IsActiveTime v s := heq ▸ hact
    have hps : s ∈ Icc (reg.lo p) (reg.hi p) := heq ▸ hp
    have hsmem : s ∈ activeSet v t₀ s := ⟨⟨hs, le_rfl⟩, hacts⟩
    have hne : (activeSet v t₀ s).Nonempty := ⟨s, hsmem⟩
    have hlast : lastActive v t₀ s = s :=
      le_antisymm (csSup_le hne fun x hx => hx.1.2) (le_csSup ⟨s, fun x hx => hx.1.2⟩ hsmem)
    have := oriented_near_last pkg (hst.trans ht) hne hD hsmem (by rw [hlast]; linarith)
    exact oriented_same pkg ⟨hacts, p, hps, rfl⟩ this (by simp [hD.le])
  · exact hcase τ ⟨hlt, hτ.2⟩ _ ⟨hact, p, hp, rfl⟩

/-- **Case 1 of 29b: the orientation of the last activity does not change on `[s, t]`.** -/
theorem same_orient_eq (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) {s t : ℝ} (hst : s ≤ t)
    (ht : t ≤ t₀ + S) (hD : 0 < reg.buffer) (hnes : (activeSet v t₀ s).Nonempty)
    (hcase : ∀ τ ∈ Ioc s t, ∀ e', IsOrientedActive reg v τ e' →
      e' = activityOrient reg v t₀ s) :
    activityOrient reg v t₀ t = activityOrient reg v t₀ s := by
  have hsub : activeSet v t₀ s ⊆ activeSet v t₀ t := fun x hx => ⟨⟨hx.1.1, hx.1.2.trans hst⟩, hx.2⟩
  have hnet : (activeSet v t₀ t).Nonempty := hnes.mono hsub
  obtain ⟨τt, hτt, hτtgt, hor⟩ := activityOrient_spec pkg ht hnet hD
  by_cases hτs : s < τt
  · exact hcase τt ⟨hτs, hτt.1.2⟩ _ hor
  · push Not at hτs
    have hτts : τt ∈ activeSet v t₀ s := ⟨⟨hτt.1.1, hτs⟩, hτt.2⟩
    have hmono : lastActive v t₀ s ≤ lastActive v t₀ t :=
      csSup_le_csSup ⟨t, fun x hx => hx.1.2⟩ hnes hsub
    have hors := oriented_near_last pkg (hst.trans ht) hnes hD hτts (by linarith)
    exact oriented_same pkg hor hors (by simp [hD.le])

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The crude adjoint fast curves

The adjoint curves of the word fibre facts are `Ψ(r) = conj u(-r)` for reversed curves `u`
(`CellWeakHilbertCurve.reflected_adjoint`). From an admissible test `ψ` at `T` (an `H^{s_k}`
representative and the fast class of the actual graph, `b1wAdm`), the curve `Ψ` with `Ψ(T) = ψ`
stays admissible at every `r ∈ [a, T]` (the pairing with the forward slow mode is conserved,
`revCurve_pairing`), and its test norm decays: `ν(Ψ(r)) ≤ C P_e^Q e^{-(π²/8)(T-r)} ν(ψ)`
(`b1w_crude_adjoint`, from `revCurve_crude_decay`, so conditional on the cell-equation regularity).
Conjugation acts on `TorusHk n` isometrically and commutes with the value (`torusHkConj_norm`,
`torusHkConj_value`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational

namespace AVRegularity.CycleWords.Assembly

/-- Conjugation on `TorusHk n`. -/
def torusHkConj {n : ℕ} (U : TorusHk n ℂ) : TorusHk n ℂ :=
  mapTorusHk Complex.conjCLE.toContinuousLinearMap U

theorem torusHkConj_value {n : ℕ} (U : TorusHk n ℂ) :
    torusHkValueCLM (torusHkConj U) =
      cellFiberCLM Complex.conjCLE.toContinuousLinearMap (torusHkValueCLM U) := by
  change (mapTorusHk Complex.conjCLE.toContinuousLinearMap U).val (valueIndex2 n) = _
  rw [mapTorusHk_jet_eq_compLp]
  rfl

theorem torusHkConj_norm {n : ℕ} (U : TorusHk n ℂ) : ‖torusHkConj U‖ = ‖U‖ := by
  have hj : ∀ j, ‖(torusHkConj U).val j‖ = ‖U.val j‖ := fun j => by
    change ‖(mapTorusHk Complex.conjCLE.toContinuousLinearMap U).val j‖ = _
    rw [mapTorusHk_jet_eq_compLp]
    exact cellFiberConj_norm (U.val j)
  change ‖(torusHkConj U).val‖ = ‖U.val‖
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2]
  simp only [hj]

variable {K : ScalarConstants}

/-- The test norm is at most any bound valid for every representative. -/
theorem b1wNu_le_of_forall {s : ℕ → ℕ} {k : ℕ} {ψ φ : ComplexCellL2} {c : ℝ} (hc : 0 < c)
    (hψ : ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = ψ)
    (h : ∀ U : TorusHk (s k) ℂ, torusHkValueCLM U = ψ → b1wNu s k φ ≤ c * ‖U‖) :
    b1wNu s k φ ≤ c * b1wNu s k ψ := by
  obtain ⟨U₀, hU₀⟩ := hψ
  rw [← div_le_iff₀' hc]
  refine le_csInf ⟨‖U₀‖, U₀, hU₀, rfl⟩ ?_
  rintro x ⟨U, hU, rfl⟩
  rw [div_le_iff₀' hc]
  exact h U hU

/-- **The crude adjoint fast curves** (conditional on the cell-equation regularity). -/
theorem b1w_crude_adjoint (hR : CellDriftRegularityStatement) (s : ℕ → ℕ) (k : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (J : ℕ → ℝ) (hJ : ∀ l, 0 ≤ J l) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
      (H : TransverseLocalHyp K η G v ξ) {t₀ S : ℝ} (data : FibreScalarData K η G v t₀ S),
      0 < η → fibreNorm ξ ≤ ρ → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt η • v t z') z‖ ≤ J l) →
    ∀ (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) {a T : ℝ}, a ≤ T →
    ∀ ψ : ComplexCellL2, b1wAdm s (cellRawTrace (fibreSeriesJet data.r ξ)) k T ψ →
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve a T Ψv Ψs (fun r =>
          -cellDualDerivative (cellAdjointCoefficients
            ⟨fun t _ => G t, v, fun k => (Real.sqrt η : ℂ) * ξ k, 0⟩) H.hG V
            (cellDrift_neg H.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv T = ψ ∧
        ∀ r ∈ Icc a T, b1wAdm s (cellRawTrace (fibreSeriesJet data.r ξ)) k r (Ψv r) ∧
          b1wNu s k (Ψv r) ≤
            C * peFactor η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * b1wNu s k ψ := by
  obtain ⟨C, Q, hC, hdec⟩ := revCurve_crude_decay (K := K) hR (s k) hρ J hJ
  refine ⟨C, Q, hC, ?_⟩
  intro η G v ξ H t₀ S data hη hξρ hvs hvj V hb a T haT ψ hψ
  have hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2 := rev_bound hb
  set cj := cellFiberCLM Complex.conjCLE.toContinuousLinearMap with hcj
  obtain ⟨u, slice, hu, hu0⟩ := revCurve_exists H V hb' (a := -T) (b := -a) (by linarith)
    (cj ψ)
  have hP : 0 < peFactor η := by unfold peFactor; positivity
  refine ⟨fun r => cj (u (-r)), fun r => cellH1Conj (slice (-r)),
    CellWeakHilbertCurve.reflected_adjoint (fun t _ => G t) H.hG H.hv V hb _ hu, ?_, ?_⟩
  · simp only [hu0, hcj, cellFiberConj_involutive]
  intro r hr
  have hfastT : cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) T + cellConstantCLM 1)
      (cj (u (-T))) = 0 := by
    rw [hu0, hcj, cellFiberConj_involutive]
    exact hψ.2
  have hur : IsRevCurve H V hb' (-T) (-r) u slice :=
    CellWeakHilbertCurve.mono hu (Icc_subset_Icc le_rfl (by linarith [hr.1]))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨U, hU⟩ := hψ.1
    obtain ⟨w, hwv, -⟩ := hdec η G v ξ H data hη hξρ hvs hvj V hb' hr.2 u slice hur hfastT
      (torusHkConj U) (by rw [torusHkConj_value, hU, hu0])
    exact ⟨torusHkConj w, by rw [torusHkConj_value, hwv]⟩
  · have hp := revCurve_pairing H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw data ξ H.hξ V hb' hu
      r hr
    rw [hp, hfastT, mul_zero]
  · refine b1wNu_le_of_forall (by positivity) hψ.1 fun U hU => ?_
    obtain ⟨w, hwv, hwn⟩ := hdec η G v ξ H data hη hξρ hvs hvj V hb' hr.2 u slice hur hfastT
      (torusHkConj U) (by rw [torusHkConj_value, hU, hu0])
    rw [torusHkConj_norm] at hwn
    refine (b1wNu_le s k (torusHkConj w) (by rw [torusHkConj_value, hwv])).trans ?_
    rw [torusHkConj_norm]
    exact hwn

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # The sharp slow test: statements of the steps and the assembly

The argument is a sup-closure. Put `x(r) = ‖q(r) - E(r)·1‖_{H^j} / |E(r)|`. The crude bound
(`b1wSlowTest_full`) makes `M = sup x` finite. One window or gap step then gives
`x(r) ≤ C|ξ| + M/2` (the mean-free part of `q` entering a window has crossed a quiet half buffer,
so costs `P_e^Q e^{-cD} M ≤ M/2`; the slow part is `(1 + c)` times the normalized row, with
`c = O(|ξ|)` from the conserved pairing), whence `M ≤ 2C|ξ|`. The transversality defect of
clause 2 is `P_e^Q e^{-cD}(|ξ| + M)`. No ordering of the windows is needed.

The three steps are `SharpSlowCrudeStatement`, `SharpSlowStepStatement`,
`SharpSlowDefectStatement`; `sharpSlowTest_of_steps` is the assembly. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Assembly

/-- The data of `SharpSlowTestStatement` after the constants, as one structure. -/
structure SharpSlowSetting (K : ScalarConstants) (ρ : ℝ) where
  η : ℝ
  t₀ : ℝ
  S : ℝ
  ϖ : ℝ
  G : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  v : ℝ → Vec 2 → Vec 2
  g : ℝ
  reg : BlockRegions
  pkg : CoreScalarPackage K η G v t₀ S ϖ reg
  hη : 0 < η
  hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)
  hvj : ∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i
  hg0 : 0 ≤ g
  hg : g ≤ K.g0
  hnear : IsMetricNearIdentity (fun t _ => G t) g
  ξ : Fin 2 → ℂ
  H : TransverseLocalHyp K η G v ξ
  hξρ : fibreNorm ξ ≤ ρ
  V : ℝ
  hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2
  a : ℝ
  b : ℝ
  ha : t₀ ≤ a
  hab : a ≤ b
  hbS : b ≤ t₀ + S
  hbq : b ∈ reg.quiet
  u : ℝ → ComplexCellL2
  slice : ℝ → TorusHk 1 ℂ
  hu : IsRevCurve H V hb' (-b) (-a) u slice
  hu1 : u (-b) = cellConstantCLM 1

namespace SharpSlowSetting

variable {K : ScalarConstants} {ρ : ℝ}

/-- `E(r) = e^{∫_r^b λ}`. -/
def E (s : SharpSlowSetting K ρ) (r : ℝ) : ℂ :=
  Complex.exp (∫ τ in r..s.b, fibreSeriesC s.pkg.actual.lam s.ξ τ)

/-- The slow test `q(r) = conj u(-r)`. -/
def q (s : SharpSlowSetting K ρ) (r : ℝ) : ComplexCellL2 :=
  cellFiberCLM Complex.conjCLE.toContinuousLinearMap (s.u (-r))

/-- The well-buffered regime. -/
def WB (s : SharpSlowSetting K ρ) (Cb c : ℝ) (Q : ℕ) : Prop :=
  Cb * (1 + (s.reg.joins : ℝ)) * peFactor s.η ^ Q * Real.exp (-c * s.reg.buffer) ≤ 1

/-- Clause 1 at `r` with constant `M`: `q(r) - star E(r)·1` has an `H^j` representative of norm
`≤ M|E(r)|`. -/
def SlowBound (s : SharpSlowSetting K ρ) (j : ℕ) (M : ℝ) (r : ℝ) : Prop :=
  ∃ w : TorusHk j ℂ, torusHkValueCLM w = s.q r - cellConstantCLM (star (s.E r)) ∧
    ‖w‖ ≤ M * ‖s.E r‖

/-- Clause 2 at `r` with constant `M`. -/
def DefectBound (s : SharpSlowSetting K ρ) (j : ℕ) (M : ℝ) (r : ℝ) : Prop :=
  ∀ p, IsLeastWindow s.reg p r → ∃ w : TorusHk j ℂ, torusHkValueCLM w =
      s.q r - cellTransverseProjection (s.reg.orient p) (s.q r) ∧ ‖w‖ ≤ M * ‖s.E r‖

theorem WB_mono (s : SharpSlowSetting K ρ) {Cb c : ℝ} {Q : ℕ} {Cb' c' : ℝ} {Q' : ℕ}
    (h : s.WB Cb c Q) (hCb0 : 0 ≤ Cb') (hCb : Cb' ≤ Cb) (hc : c ≤ c') (hQ : Q' ≤ Q) :
    s.WB Cb' c' Q' := by
  unfold WB at h ⊢
  have hD := s.pkg.buffer_nonneg
  have hpe : 1 ≤ peFactor s.η := AVRegularity.CycleWords.Assembly.one_le_peFactor s.η
  have hJ : (0 : ℝ) ≤ 1 + (s.reg.joins : ℝ) := by positivity
  have h1 : peFactor s.η ^ Q' ≤ peFactor s.η ^ Q := pow_le_pow_right₀ hpe hQ
  have h2 : Real.exp (-c' * s.reg.buffer) ≤ Real.exp (-c * s.reg.buffer) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h0 : 0 ≤ peFactor s.η ^ Q' := by positivity
  have hC : 0 ≤ Cb := hCb0.trans hCb
  refine le_trans ?_ h
  gcongr

theorem SlowBound.mono {s : SharpSlowSetting K ρ} {j : ℕ} {M M' r : ℝ}
    (h : s.SlowBound j M r) (hM : M ≤ M') : s.SlowBound j M' r := by
  obtain ⟨w, hw, hn⟩ := h
  exact ⟨w, hw, hn.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))⟩

theorem DefectBound.mono {s : SharpSlowSetting K ρ} {j : ℕ} {M M' r : ℝ}
    (h : s.DefectBound j M r) (hM : M ≤ M') : s.DefectBound j M' r := by
  intro p hp
  obtain ⟨w, hw, hn⟩ := h p hp
  exact ⟨w, hw, hn.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))⟩

/-- The sup-closure: from a crude bound `M0` and the one-step inequality `A + M/2`, the bound
`2A` holds (value-injectivity of `TorusHk j ℂ` makes the representative unique). -/
theorem slowBound_closure (s : SharpSlowSetting K ρ) {j : ℕ}
    (hinj : ∀ w w' : TorusHk j ℂ, torusHkValueCLM w = torusHkValueCLM w' → w = w')
    {A M0 : ℝ} (hA : 0 ≤ A) (hM0 : 0 ≤ M0)
    (hstep : ∀ M : ℝ, 0 ≤ M → (∀ r ∈ Icc s.a s.b, s.SlowBound j M r) →
      ∀ r ∈ Icc s.a s.b, s.SlowBound j (A + M / 2) r)
    (h0 : ∀ r ∈ Icc s.a s.b, s.SlowBound j M0 r) :
    ∀ r ∈ Icc s.a s.b, s.SlowBound j (2 * A) r := by
  have hk : ∀ k : ℕ, ∀ r ∈ Icc s.a s.b, s.SlowBound j (2 * A + M0 * (1 / 2) ^ k) r := by
    intro k
    induction k with
    | zero => intro r hr; exact (h0 r hr).mono (by simp; linarith)
    | succ k ih =>
      intro r hr
      refine ((hstep _ (by positivity) ih) r hr).mono (le_of_eq ?_)
      rw [pow_succ]; ring
  intro r hr
  obtain ⟨w, hw, -⟩ := hk 0 r hr
  refine ⟨w, hw, ?_⟩
  have hb : ∀ k : ℕ, ‖w‖ ≤ (2 * A + M0 * (1 / 2) ^ k) * ‖s.E r‖ := by
    intro k
    obtain ⟨w', hw', hn'⟩ := hk k r hr
    have : w' = w := hinj _ _ (hw'.trans hw.symm)
    exact this ▸ hn'
  by_contra hcon
  push Not at hcon
  have hδ : 0 < ‖w‖ - 2 * A * ‖s.E r‖ := by linarith
  have ht : Filter.Tendsto (fun k : ℕ => M0 * ‖s.E r‖ * (1 / 2 : ℝ) ^ k) Filter.atTop
      (nhds (M0 * ‖s.E r‖ * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  rw [mul_zero] at ht
  obtain ⟨k, hk'⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  have := hb k
  nlinarith

end SharpSlowSetting

/-- **The crude bound.**`q(r) - E(r)·1` has a crude `H^j` bound `C P_e^Q |E(r)|`
(`b1wSlowTest_full`, `cellDriftRegularity`, plus uniqueness of the reversed curve). -/
def SharpSlowCrudeStatement : Prop :=
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C : ℝ) (Q : ℕ), ∀ s : SharpSlowSetting K ρ, ∀ r ∈ Icc s.a s.b,
    s.SlowBound j (C * peFactor s.η ^ Q) r

/-- **Step W** (the one-step inequality of the sup-closure): if `x ≤ M` on `[a, b]`, then
`x ≤ C|ξ| + M/2`. Split into `SharpSlowQuietStepStatement` and `SharpSlowWindowStepStatement`. -/
def SharpSlowStepStatement : Prop := QuietHsDecayStatement →
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C Cb c : ℝ) (Q : ℕ), 0 ≤ C ∧ 0 ≤ Cb ∧ 0 < c ∧
  ∀ s : SharpSlowSetting K ρ, s.WB Cb c Q → ∀ M : ℝ, 0 ≤ M →
    (∀ r ∈ Icc s.a s.b, s.SlowBound j M r) →
    ∀ r ∈ Icc s.a s.b, s.SlowBound j (C * fibreNorm s.ξ + M / 2) r

/-- `r` lies in an extended window `[lo_p - D, hi_p + D/2]`. -/
def InExtWindow (reg : BlockRegions) (r : ℝ) : Prop :=
  ∃ p : Fin reg.P, r ∈ Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer / 2)

/-- **Step W-quiet (gap step).** If `x ≤ M` everywhere on `[a, b]` and `r` is in no extended
window, then `x(r) ≤ C|ξ| + M/2`. Then `[r, min(r + D, b)]` is quiet (`cover`; windows ahead
start after `r + D`, windows behind end before `r - D/2`). Proof: `q - E·1 = (mean q - E)·1 + Q0 q`;
the mean part is `O(|ξ|)|E|` by the conserved pairing `revCurve_pairing` and `‖r‖_{L²} ≤ C_g|ξ|`;
`Q0 q(r)` is the `hQ` evolution of `Q0 q(r + D)` (curve-level congruence `dual_congr`), of size
`e^{-π² D/2} M |E(r + D)|` and `|E(r+D)| ≤ e^{π² D/16}|E(r)|` (`b1wGamma_growth`); if `b ≤ r + D`
then `Q0 q(b) = 0`. -/
def SharpSlowQuietStepStatement : Prop := QuietHsDecayStatement →
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C Cb c : ℝ) (Q : ℕ), 0 ≤ C ∧ 0 ≤ Cb ∧ 0 < c ∧
  ∀ s : SharpSlowSetting K ρ, s.WB Cb c Q → ∀ M : ℝ, 0 ≤ M →
    (∀ r ∈ Icc s.a s.b, s.SlowBound j M r) →
    ∀ r ∈ Icc s.a s.b, ¬ InExtWindow s.reg r → s.SlowBound j (C * fibreNorm s.ξ + M / 2) r

/-- **The window step.** Same conclusion for `r` in an extended window `p`. Start the shear curve at
`T = min(b, hi_p + D/2)`: there `q(T) = (1 + c)E(T)·1 + (mean-free part)`, the mean-free part has
crossed a quiet half buffer (`hQ`, size `e^{-π² D/4} M`), is evolved crudely on `[lo_p - D, T]`,
where the drift is the shear `ext p` (`ext_agree`; `sharpRevCurve_congr`), at price `P_e^Q`
(`revCurve_regularity`, with `revCurve_fast_decay` in `L²` against the growth of `E`), and
the slow part is `(1 + c)` times the normalized row, `P_e`-free. If `T = b` the data is `1` and
the bound on the normalized row applies directly. -/
def SharpSlowWindowStepStatement : Prop := QuietHsDecayStatement →
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C Cb c : ℝ) (Q : ℕ), 0 ≤ C ∧ 0 ≤ Cb ∧ 0 < c ∧
  ∀ s : SharpSlowSetting K ρ, s.WB Cb c Q → ∀ M : ℝ, 0 ≤ M →
    (∀ r ∈ Icc s.a s.b, s.SlowBound j M r) →
    ∀ r ∈ Icc s.a s.b, InExtWindow s.reg r → s.SlowBound j (C * fibreNorm s.ξ + M / 2) r

/-- **Step W** from its two cases. -/
theorem sharpSlowStep_of_cases (hq : SharpSlowQuietStepStatement)
    (hw : SharpSlowWindowStepStatement) : SharpSlowStepStatement := by
  intro hQ K j ρ hρ0 hρ1
  obtain ⟨C1, Cb1, c1, Q1, hC1, hCb1, hc1, h1⟩ := hq hQ K j ρ hρ0 hρ1
  obtain ⟨C2, Cb2, c2, Q2, hC2, hCb2, hc2, h2⟩ := hw hQ K j ρ hρ0 hρ1
  refine ⟨max C1 C2, max Cb1 Cb2, min c1 c2, max Q1 Q2, le_max_of_le_left hC1,
    le_max_of_le_left hCb1, lt_min hc1 hc2, ?_⟩
  intro s hs M hM hb r hr
  have hw1 : s.WB Cb1 c1 Q1 :=
    s.WB_mono hs hCb1 (le_max_left _ _) (min_le_left _ _) (le_max_left _ _)
  have hw2 : s.WB Cb2 c2 Q2 :=
    s.WB_mono hs hCb2 (le_max_right _ _) (min_le_right _ _) (le_max_right _ _)
  have hn : 0 ≤ fibreNorm s.ξ := fibreNorm_nonneg s.ξ
  by_cases hex : InExtWindow s.reg r
  · exact (h2 s hw2 M hM hb r hr hex).mono (by
      have := mul_le_mul_of_nonneg_right (le_max_right C1 C2) hn; linarith)
  · exact (h1 s hw1 M hM hb r hr hex).mono (by
      have := mul_le_mul_of_nonneg_right (le_max_left C1 C2) hn; linarith)

/-- **Step T (transversality defect).** If `x ≤ M` everywhere, the non-transverse part of `q(r)`
in the least window costs `P_e^Q e^{-cD}(|ξ| + M)`: it comes from later windows, crossed the
quiet half buffer after `hi_p` (distance `≥ D/2`) and evolved crudely; replacement errors
(`replace_graph/row/symbol`) add `P_e^Q e^{-cD}|ξ|`. If `T` lies after `b`, `u(-b) = 1` is
transverse and the transverse estimate applies directly. -/
def SharpSlowDefectStatement : Prop := QuietHsDecayStatement →
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C Cb c : ℝ) (Q : ℕ), 0 ≤ C ∧ 0 ≤ Cb ∧ 0 < c ∧
  ∀ s : SharpSlowSetting K ρ, s.WB Cb c Q → ∀ M : ℝ, 0 ≤ M →
    (∀ r ∈ Icc s.a s.b, s.SlowBound j M r) →
    ∀ r ∈ Icc s.a s.b, s.DefectBound j
      (C * peFactor s.η ^ Q * Real.exp (-c * s.reg.buffer) * (fibreNorm s.ξ + M)) r

/-- The value map of `TorusHk j ℂ` is injective (the value determines all derivatives). -/
theorem sharpSlow_value_injective (j : ℕ) (w w' : TorusHk j ℂ)
    (h : torusHkValueCLM w = torusHkValueCLM w') : w = w' :=
  TorusHk.ext_value (by exact h)

/-- **Assembly of the sharp slow test from the three steps.** -/
theorem sharpSlowTest_of_steps
    (hQ : QuietHsDecayStatement) (hK : SharpSlowCrudeStatement)
    (hW : SharpSlowStepStatement) (hT : SharpSlowDefectStatement) :
    SharpSlowTestStatement := by
  intro K j ρ hρ0 hρ1
  obtain ⟨Ck, Qk, hk⟩ := hK K j ρ hρ0 hρ1
  obtain ⟨C1, Cb1, c1, Q1, hC1, hCb1, hc1, h1⟩ := hW hQ K j ρ hρ0 hρ1
  obtain ⟨C2, Cb2, c2, Q2, hC2, hCb2, hc2, h2⟩ := hT hQ K j ρ hρ0 hρ1
  have hCmax : 2 * C1 ≤ max (2 * C1) (C2 * (1 + 2 * C1)) := le_max_left _ _
  have hCmax2 : C2 * (1 + 2 * C1) ≤ max (2 * C1) (C2 * (1 + 2 * C1)) := le_max_right _ _
  refine ⟨max (2 * C1) (C2 * (1 + 2 * C1)), max Cb1 Cb2, min c1 c2, max Q1 Q2,
    le_trans (by positivity) hCmax, lt_min hc1 hc2, ?_⟩
  intro η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg hnear ξ H hξρ hwb V hb' a b ha hab hbS hbq u
    slice hu hu1
  let s : SharpSlowSetting K ρ := ⟨η, t₀, S, ϖ, G, v, g, reg, pkg, hη, hvs, hvj, hg0, hg, hnear,
    ξ, H, hξρ, V, hb', a, b, ha, hab, hbS, hbq, u, slice, hu, hu1⟩
  have hs : s.WB (max Cb1 Cb2) (min c1 c2) (max Q1 Q2) := hwb
  have hn : 0 ≤ fibreNorm ξ := fibreNorm_nonneg ξ
  have hw1 : s.WB Cb1 c1 Q1 :=
    s.WB_mono hs hCb1 (le_max_left _ _) (min_le_left _ _) (le_max_left _ _)
  have hw2 : s.WB Cb2 c2 Q2 :=
    s.WB_mono hs hCb2 (le_max_right _ _) (min_le_right _ _) (le_max_right _ _)
  have hM0 : ∀ r ∈ Icc s.a s.b, s.SlowBound j (max (Ck * peFactor η ^ Qk) 0) r :=
    fun r hr => (hk s r hr).mono (le_max_left _ _)
  have hcl := s.slowBound_closure (sharpSlow_value_injective j) (A := C1 * fibreNorm ξ) (mul_nonneg hC1 hn)
    (le_max_right _ _) (fun M hM hb r hr => by
      have := h1 s hw1 M hM hb r hr
      exact this) hM0
  have hcl' : ∀ r ∈ Icc a b, s.SlowBound j (2 * (C1 * fibreNorm ξ)) r := hcl
  intro r hr
  refine ⟨(hcl' r hr).mono ?_, ?_⟩
  · have : 2 * (C1 * fibreNorm ξ) = (2 * C1) * fibreNorm ξ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hCmax hn
  · intro p hp
    have hd := (h2 s hw2 (2 * (C1 * fibreNorm ξ)) (by positivity) hcl' r hr).mono
      (M' := max (2 * C1) (C2 * (1 + 2 * C1)) * peFactor η ^ (max Q1 Q2) *
        Real.exp (-(min c1 c2) * reg.buffer) * fibreNorm ξ) ?_
    · exact hd p hp
    · have hD := pkg.buffer_nonneg
      have hpe : 1 ≤ peFactor η := AVRegularity.CycleWords.Assembly.one_le_peFactor η
      have e1 : peFactor η ^ Q2 ≤ peFactor η ^ (max Q1 Q2) :=
        pow_le_pow_right₀ hpe (le_max_right _ _)
      have e2 : Real.exp (-c2 * reg.buffer) ≤ Real.exp (-(min c1 c2) * reg.buffer) :=
        Real.exp_le_exp.mpr (by nlinarith [min_le_right c1 c2])
      have e3 : C2 * (1 + 2 * C1) ≤ max (2 * C1) (C2 * (1 + 2 * C1)) := hCmax2
      have e4 : C2 * peFactor η ^ Q2 * Real.exp (-c2 * reg.buffer) * (fibreNorm ξ + 2 * (C1 * fibreNorm ξ))
          = (C2 * (1 + 2 * C1)) * peFactor η ^ Q2 * Real.exp (-c2 * reg.buffer) * fibreNorm ξ := by ring
      show C2 * peFactor η ^ Q2 * Real.exp (-c2 * reg.buffer) * (fibreNorm ξ + 2 * (C1 * fibreNorm ξ)) ≤ _
      rw [e4]
      have hC20 : 0 ≤ C2 * (1 + 2 * C1) := by positivity
      gcongr

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Chains from compact data

The proved statement `cycle_mixed_words_exists` at `Kf = 0`, `m = 0` and the base slots
`κ_l = ∑_{i ≥ l} d_i`: letters at the block's reserve are letters at the smaller reserve of the
statement (`isCycleLetter_reserve_mono`), the base slots descend and stay below it, and a
compactly supported datum has finite weighted norms of every order. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- A letter at a fast reserve is a letter at every smaller one. -/
theorem isCycleLetter_reserve_mono {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {π : ι → ℝ}
    {L : CycleLetter ι h D} {dom : Set (ℝ × Vec 2)} {J J' H : ℕ}
    (hL : IsCycleLetter π L dom J H) (hJ : J' ≤ J) : IsCycleLetter π L dom J' H :=
  { hL with
    analytic := AVRegularity.Construction.Preservation.Seed.analyticEnvelope_mono _ π
      (fun _ _ => subset_rfl) 1 1 1 le_rfl hJ L.majorant hL.nonneg le_rfl hL.analytic }

/-- The base slots stay below the total order `∑ d_i`. -/
theorem wordBaseSlots_le_sum {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D Nw : ℕ} (letters : Fin Nw → CycleLetter ι h D)
    (j : Fin (Nw + 1)) (x : ι) :
    wordBaseSlots letters j x ≤ ∑ i, (letters i).order :=
  Finset.sum_le_sum fun i _ => by split_ifs <;> simp

/-- **Compact chains** (`CompactChainExistenceStatement`). -/
theorem compactChainExistence : CompactChainExistenceStatement.{u, v} := by
  intro K
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro ι _ h _ _ _ _ _ _ D Nw H J π letters η S ηg t₀ ϖ G v g reg pkg hB hJ X₀ f hcd
  have hn := AVRegularity.Providers.cycle_mixed_words_exists K Nw D H 0 0 hB.hD
    (fun i => (letters i).order) (fun i => (letters i).slow) (fun i => (letters i).positive)
    π hB.hπ letters (fun _ => ⟨rfl, rfl, rfl⟩) η S ηg t₀ ϖ hB.hη hB.hη1 hB.hS hB.hηg hB.hηg1 hB.hϖ
    G v g hB.hGm hB.hv hB.hvs hB.hv0 hB.hvw hB.hvj hB.hg0 hB.hg₁ hB.hg hB.hGn reg pkg
    (fun i => isCycleLetter_reserve_mono (hB.hlet i) hJ) hB.hmeas X₀ (wordBaseSlots letters)
    (fun _ => Nat.zero_le _) (wordBaseSlots_isWordSlots letters hB.hlet) (fun j x => ?_) f ?_
  · exact hn
  · refine (wordBaseSlots_le_sum letters j.succ x).trans ?_
    unfold wordReserveJstar wordReserveKstar wordReserveN
    beta_reduce
    omega
  · refine lt_top_iff_ne_top.2 (AVRegularity.Weighted.geometryDataNorm_ne_top_of_components
      π _ _ ϖ 0 1 f fun x => ?_)
    obtain ⟨φ, -, hφc, hφ⟩ := hcd x
    refine weightedFactorialNormSq_compact_value_ne_top _ ϖ 0 1 (f x) hφc.isCompact ?_
    have he : (f x).toFunction.jet (valueIndex2 (wordBaseSlots letters 0 x)) =
        planeValue (f x) := (planeValue_eq_stored (f x)).symm
    rw [he]
    filter_upwards [hφ] with z hz hzA
    rw [hz]
    exact image_eq_zero_of_notMem_tsupport hzA

end AVRegularity.CycleWords.Assembly
end
end
end
