-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
public import AVRegularity.CycleComparison.Residual.FastJets.Sampling
import AVRegularity.CycleComparison.Lift.LeftTermsFieldPostcomposition
import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.CycleComparison.Lift.SettingDimensionalScales
public import AVRegularity.Definitions.Construction.Gen.ParShift
public import AVRegularity.Statements.Construction.IsAdmissibleQ
import AVRegularity.Construction.Stream.NextAdmissible

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Physical diagonal words use the reserved mixed jets without a sampling derivative loss. -/

open FastJets
open CycleComparison.Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem norm_mixL_le_mixed_jet {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (γ δ : List (Fin 2)) {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth γ.length δ.length f) (X z : Vec 2) :
    ‖mixL γ δ f X z‖ ≤
      ‖iteratedFDeriv ℝ γ.length
        (fun Y => iteratedFDeriv ℝ δ.length (f Y) z) X‖ := by
  have hb := norm_mixed_orderedDerivative_le hf
    (fun i => γ.get i) (fun i => δ.get i) X z
  simpa only [orderedDerivative_eq_odL, List.ofFn_get, mixL, slowL, fastL] using hb

/-- Real form of the compiled diagonal expansion, convenient before inverse-mass row squaring. -/
theorem norm_rs_odL_diagonal_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth sX sZ f) {ρ e rs : ℝ}
    (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ)
    (l : List (Fin 2)) (hl : l.length ≤ min sX sZ) (x : Vec 2) :
    rs ^ l.length * ‖odL l (fun y => f (ρ⁻¹ • y) (e⁻¹ • y)) x‖ ≤
      ∑ i : Fin (splitTerms l).length,
        ‖mixL ((splitTerms l).get i).1 ((splitTerms l).get i).2 f
          (ρ⁻¹ • x) (e⁻¹ • x)‖ := by
  have hb := enorm_rs_odL_diag_le hf hrs hrse heρ l hl x
  rw [list_sum_map_fin] at hb
  simp only [← ofReal_norm] at hb
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)] at hb
  have hr := (ENNReal.ofReal_le_ofReal_iff
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mp hb
  simpa only [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hrs] using hr

/-- Coordinate mixed words of the action spend only their actual slow input order. -/
theorem norm_mixL_liftApply_le_local_jets
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n : ℕ}
    (γ δ : List (Fin 2)) {c : LiftCoeff ι h} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n γ.length δ.length c M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ ((γ.length + n : ℕ) : ℕ∞) g)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    ‖mixL γ δ (fun Y y => liftApply n c (fun _ => g) t Y y v) X z‖ ≤
      finiteLiftWordCount n * 2 ^ (γ.length + 2 * δ.length) *
        (∑ u, M v u * ∑ j : Fin (γ.length + n + 1),
          ‖iteratedFDeriv ℝ j.1 (fun Y => g Y u) X‖) := by
  have hbox := liftApply_component_box_reserve n γ.length δ.length c (fun _ => g) t v hg
    (fun m hm α u => data.box m hm α v u t ht)
  exact (norm_mixL_le_mixed_jet γ δ hbox X z).trans
    (ambient_liftApply_mixed_pointwise_le data hlam hlam1 g hg t ht X z v)

/-- Positive mixed words of a positive lift retain a positive field derivative. -/
theorem norm_mixL_positive_liftApply_le_local_jets
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n : ℕ}
    (γ δ : List (Fin 2)) {c : LiftCoeff ι h} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n γ.length δ.length c M)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ ((γ.length + n : ℕ) : ℕ∞) g)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hzero : ∀ α : DerivativeWord2 0, ∀ X z v u, c 0 α t X z v u = 0)
    (X z : Vec 2) (v : ι) :
    ‖mixL γ δ (fun Y y => liftApply n c (fun _ => g) t Y y v) X z‖ ≤
      finiteLiftWordCount n * 2 ^ (γ.length + 2 * δ.length) *
        (∑ u, M v u * ∑ j : Fin (γ.length + n + 1),
          if j.1 = 0 then 0 else ‖iteratedFDeriv ℝ j.1 (fun Y => g Y u) X‖) := by
  have hbox := liftApply_component_box_reserve n γ.length δ.length c (fun _ => g) t v hg
    (fun m hm α u => data.box m hm α v u t ht)
  exact (norm_mixL_le_mixed_jet γ δ hbox X z).trans
    (ambient_positive_liftApply_mixed_pointwise_le data hlam hlam1 g hg t ht hzero X z v)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! A diagonal derivative with one unweighted spatial derivative costs the fast length. -/

open FastJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pred_weight_le_of_weight_le {s e a B : ℝ} {r : ℕ}
    (hs : 0 < s) (hse : s ≤ e) (hr : 1 ≤ r) (ha : 0 ≤ a)
    (hb : e ^ r * a ≤ B) : s ^ (r - 1) * a ≤ e⁻¹ * B := by
  have he : 0 < e := hs.trans_le hse
  have hp : e⁻¹ * e ^ r = e ^ (r - 1) := by
    rw [show r = (r - 1) + 1 by omega, pow_succ]
    field_simp
    congr 1
  calc
    _ ≤ e ^ (r - 1) * a :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hse _) ha
    _ = e⁻¹ * (e ^ r * a) := by rw [← mul_assoc, hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr he.le)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The decaying incoming ledger is bounded by its pre-data constant. -/

theorem incoming_ledger_budget_le (D : OCData) {s CI τ : ℝ}
    (hα : 0 < D.α) (hq : IsAdmissibleQ D.α s D.q) (hΛ : 1 ≤ D.Λ)
    (hCI : 0 ≤ CI) (hτ : 0 ≤ τ) (m : ℕ) :
    CI * D.eps m ^ min (ocDelta D.α D.q / 4) τ ≤ CI := by
  have hδ := ocDelta_pos_of_admissible hα hq
  have he : 0 ≤ min (ocDelta D.α D.q / 4) τ := le_min (by positivity) hτ
  have hε : 0 ≤ D.eps m := (Construction.Stream.ocEpsilon_pos hΛ).le
  have hε1 : D.eps m ≤ 1 := ocEpsilon_le_one hΛ m
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.rpow_le_one hε hε1 he) hCI

end AVRegularity.Construction.Preservation.FullLift
end
end
