-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.WeakCarrierAppend
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftCellSource
public import AVRegularity.Statements.Construction.IsAdmissibleQ
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.EntryScales.TerminalCore
public import AVRegularity.Statements.Intermediate.CycleReference.OcBand
import AVRegularity.Construction.Uniqueness.SuccessorFluxUnique
import Mathlib.Data.List.GetD

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Restriction to the effective source order preserves the actual recurrence at every retained lift degree. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def restrictLiftData (K : ℕ) (hKD : K ≤ D) (Q : LiftOperatorData ι h D) : LiftOperatorData ι h K :=
  ⟨Q.η, Q.G, Q.v, restrictConstituentEdges K hKD Q.edge⟩

theorem liftA_restrict_effective_order (K : ℕ) (hKD : K ≤ D)
    (Q : LiftOperatorData ι h D) (hz : ∀ v u d, K < d.val → Q.edge v u d = [])
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hn : n ≤ K) (t : ℝ) :
    liftA Q Cc f hh n t = liftA (restrictLiftData K hKD Q) Cc f hh n t := by
  unfold liftA
  simp only [restrictLiftData, Nat.min_eq_right (hn.trans hKD), Nat.min_eq_right hn]
  simp_rw [sourceCoeff_restrict_effective_order K hKD Q.edge hz]

theorem liftMean_restrict_effective_order (K : ℕ) (hKD : K ≤ D)
    (Q : LiftOperatorData ι h D) (hz : ∀ v u d, K < d.val → Q.edge v u d = [])
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hn : n ≤ K) :
    liftMean Q Cc f hh n = liftMean (restrictLiftData K hKD Q) Cc f hh n := by
  funext t X
  unfold liftMean
  rw [liftA_restrict_effective_order K hKD Q hz Cc f hh n hn t]

theorem liftCellSource_restrict_effective_order (K : ℕ) (hKD : K ≤ D)
    (Q : LiftOperatorData ι h D) (hz : ∀ v u d, K < d.val → Q.edge v u d = [])
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hn : n ≤ K) (t : ℝ) :
    liftCellSource Q Cc f hh n t = liftCellSource (restrictLiftData K hKD Q) Cc f hh n t := by
  have ha := liftA_restrict_effective_order K hKD Q hz Cc f hh n hn t
  have hm := liftMean_restrict_effective_order K hKD Q hz Cc f hh n hn
  funext X z
  have hs : (∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc f p.2 (n - j)) t X z) =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean (restrictLiftData K hKD Q) Cc f p.2 (n - j)) t X z := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p _
    rw [liftMean_restrict_effective_order K hKD Q hz Cc f p.2 (n - j)
      ((Nat.sub_le n j).trans hn)]
  simp only [liftCellSource, ha, hm, hs]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Openness of an admissible family follows from its finitely many continuous child centers. -/

theorem weak_admissible_family_isOpen
    {E : Type*} [TopologicalSpace E] (D : OCData) (bw : ℝ)
    (j₀ level : ℕ) (slot : ℤ) (A : RealChain) (family : E → RealChain)
    (hA : IsAdmissibleChain D bw j₀ level slot A)
    (hb : ∀ Y, (family Y).baseLevel = A.baseLevel)
    (hs : ∀ Y, (family Y).slots = A.slots)
    (hl : ∀ Y, (family Y).children.length = A.children.length)
    (hc : ∀ j : Fin A.children.length, Continuous (fun Y =>
      ((family Y).children.getD j ⟨0, 0⟩).center)) :
    IsOpen {Y | IsAdmissibleChain D bw j₀ level slot (family Y)} := by
  have he : {Y | IsAdmissibleChain D bw j₀ level slot (family Y)} =
      ⋂ j : Fin A.children.length, {Y | ∑ i : Fin 2,
        |((family Y).children.getD j ⟨0, 0⟩).center i| <
          (1 + 2) * bw / 4 * D.eps (A.baseLevel + 1 + j)} := by
    ext Y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [weak_admissible_iff_child_centers_of_metadata D bw j₀ level slot A
      (family Y) hA (hb Y) (hs Y) (hl Y)]
    constructor
    · intro h j
      have hj : j.val < (family Y).children.length := by rw [hl Y]; exact j.is_lt
      simpa only [List.getD_eq_getElem _ _ hj, hb Y, Fin.eta, Fin.getElem_fin] using h ⟨j, hj⟩
    · intro h j
      have hj : j.val < A.children.length := by rw [← hl Y]; exact j.is_lt
      simpa only [List.getD_eq_getElem _ _ j.is_lt, hb Y, Fin.eta, Fin.getElem_fin] using h ⟨j, hj⟩
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt _ continuous_const
  exact continuous_finsetSum _ (fun i _ => ((continuous_apply i).comp (hc j)).abs)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
namespace AVRegularity.EntryWeakProofs

/-! One terminal-level threshold makes every later renewal window quantitatively small. -/

theorem weak_anchor_eventually_small (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M,
      ocTauPP α q Λ m ≤ 2 ^ (-25 : ℤ) * (ocA α q Λ (m - 1))⁻¹ ∧
      2 ^ 23 * ocTauPP α q Λ m * ocA α q Λ (m - 1) ≤ 1 / 32 := by
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  obtain ⟨M, hM⟩ := weak_epsilon_rpow_eventually_small hq.1 hΛ
    (show 0 < 2 * ocDelta α q by linarith) (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨max 2 (M + 1), le_max_left _ _, ?_⟩
  intro m hm
  have hm1 : 1 ≤ m := by omega
  have hE := hM (m - 1) (by omega)
  have hA : 0 < ocA α q Λ (m - 1) := by
    unfold ocA
    exact Real.rpow_pos_of_pos (Scales.epsilon_basic hq.1 hΛ).1 _
  have hB := (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ hm1).2.2.2.2.1
  have hP : ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) / 8 := by
    exact hB.trans (by
      have h := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ (2 : ℝ) ^ (-25 : ℤ))
      simpa only [mul_one_div] using h)
  constructor
  · rw [← div_eq_mul_inv, le_div_iff₀ hA]
    calc
      _ = ocA α q Λ (m - 1) * ocTauPP α q Λ m := mul_comm _ _
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) / 8 := hP
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) := by norm_num
  · have h := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ (2 : ℝ) ^ 23)
    norm_num at h
    nlinarith [h]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! All weak levels have arbitrarily small molecular Peclet number above one terminal threshold. -/

theorem weak_peclet_eventually_small {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (θ : ℝ) (hθ : 0 < θ) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ ν ∈ ocBand α q Λ M, ∀ m > M,
      ocEpsilon q Λ m ^ (1 + α) / ν ≤ θ := by
  obtain ⟨C, hC, hb⟩ := EntryScales.weak_scales_core hα₀ hα₁ hs₀ hs₁ hq
  have hC₀ : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hC
  have hγ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).1
  have hp : 0 < (q + 2) * ocGamma α q := mul_pos (by linarith [hq.1]) hγ
  obtain ⟨M₀, hsmall⟩ := weak_epsilon_rpow_eventually_small hq.1 hΛ hp (div_pos hθ hC₀)
  refine ⟨M₀, ?_⟩
  intro M hM ν hν m hm
  have h := (hb Λ hΛ M ν hν m hm).1
  have he : 0 ≤ ocEpsilon q Λ (m - 1) := (Scales.epsilon_basic hq.1 hΛ).1.le
  have hpow : ocEpsilon q Λ (m - 1) ^ ((q + 2) * ocGamma α q) ≤
      ocEpsilon q Λ M ^ ((q + 2) * ocGamma α q) :=
    Real.rpow_le_rpow he (EntryScales.epsilon_antitone hq.1 hΛ (by omega : M ≤ m - 1)) hp.le
  calc
    _ ≤ C * ocEpsilon q Λ (m - 1) ^ ((q + 2) * ocGamma α q) := h
    _ ≤ C * (θ / C) := mul_le_mul_of_nonneg_left (hpow.trans (hsmall M hM)) hC₀.le
    _ = θ := by field_simp

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! A uniform finite price for the literal temporal partition in weak transfer. -/

def weakTransferSlots (D : OCData) (m : ℕ) (t : ℝ) : Finset ℤ :=
  Finset.Icc (⌊t / ocTau D.α D.q D.Λ m⌋ - 2) (⌊t / ocTau D.α D.q D.Λ m⌋ + 2)

theorem weakTransferSlots_card (D : OCData) (m : ℕ) (t : ℝ) :
    (weakTransferSlots D m t).card = 5 := by
  simp only [weakTransferSlots, Int.card_Icc]
  omega

theorem weak_cutoff_mem_transferSlots (D : OCData) (m : ℕ) (t : ℝ)
    (hτ : 0 < ocTau D.α D.q D.Λ m) (slot : ℤ)
    (hc : ocCutoff D.α D.q D.Λ m slot t ≠ 0) : slot ∈ weakTransferSlots D m t := by
  obtain ⟨hl, hu⟩ := Uniqueness.cutoff_support D.α D.q D.Λ m slot t hτ hc
  have hleft : (slot : ℝ) - 61 / 48 ≤ t / ocTau D.α D.q D.Λ m :=
    (le_div_iff₀ hτ).mpr hl
  have hright : t / ocTau D.α D.q D.Λ m ≤ (slot : ℝ) + 61 / 48 :=
    (div_le_iff₀ hτ).mpr hu
  have hf := Int.floor_le (t / ocTau D.α D.q D.Λ m)
  have hf' := Int.lt_floor_add_one (t / ocTau D.α D.q D.Λ m)
  have hb : (⌊t / ocTau D.α D.q D.Λ m⌋ : ℝ) - 3 < (slot : ℝ) ∧
      (slot : ℝ) < (⌊t / ocTau D.α D.q D.Λ m⌋ : ℝ) + 3 := by
    constructor <;> linarith
  have hb' : ⌊t / ocTau D.α D.q D.Λ m⌋ - 3 < slot ∧
      slot < ⌊t / ocTau D.α D.q D.Λ m⌋ + 3 := by exact_mod_cast hb
  simp only [weakTransferSlots, Finset.mem_Icc]
  omega

end AVRegularity.EntryWeakProofs
end
end
