-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Reduction.QuietTraceHighPassage
import AVRegularity.EntryWeakAssembly.MassRecursion
public import AVRegularity.Proofs.WeakGen.Comparison.RowsHigh
public import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import AVRegularity.CycleComparison.Reconstruction.Continuity
public import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
public import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.CycleComparison.Reconstruction.ReconForcePieces
public import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.IterationPassage.ErrorJets.LiftIdentification
public import AVRegularity.EntryWeakAssembly.Assembly.WeakReadoutBound
import AVRegularity.EntryTerminal.Ingredients.Readout.EnergyReadout
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftField
import Mathlib.Data.Int.Star

section
section
@[expose] public section
namespace AVRegularity.WeakEntryProofs.Identity

/-! **Identity C2: the exponents of the telescoped identity** (abstract-real lemmas).

`ε_m = ⌈Λ^{q^m/(q−1)}⌉⁻¹` for `m ≥ 1`, so `ε_{M+J}` is `ε_M^{q^J}` only up to the ceilings:

* `identityC2_eps_inv_le`: `ε_{M+J}⁻¹ ≤ 2 (ε_M⁻¹)^{q^J}` for `M ≥ 1`;
* `identityC2_main`: `ε_{M+J}^{-(1+s)} ε_M^E ≤ 4 ε_M^P` whenever `P + 2 q^J ≤ E` and `0 < s < 1`.

The degenerate cases are included: `J = 0` is `ε_M^{-(1+s)} ε_M^E ≤ 4 ε_M^P` (true since
`E ≥ P + 2`); `M = 0` is excluded (`ε_0 = 1` is not a ceiling). -/

open AVRegularity

theorem identityC2_eps_inv_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 1 ≤ Λ) {M : ℕ} (hM : 1 ≤ M)
    (J : ℕ) :
    (ocEpsilon q Λ (M + J))⁻¹ ≤ 2 * ((ocEpsilon q Λ M)⁻¹) ^ (q ^ J) := by
  have hq0 : 0 < q - 1 := by linarith
  have hΛr : (1 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  set X : ℝ := (Λ : ℝ) ^ (q ^ M / (q - 1)) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hΛr (div_nonneg (pow_nonneg (by linarith) _) hq0.le)
  have hMne : M ≠ 0 := by omega
  have hMJne : M + J ≠ 0 := by omega
  have hεM : (ocEpsilon q Λ M)⁻¹ = (⌈X⌉₊ : ℝ) := by
    simp [ocEpsilon, hMne, hX]
  have hεMJ : (ocEpsilon q Λ (M + J))⁻¹ = (⌈(Λ : ℝ) ^ (q ^ (M + J) / (q - 1))⌉₊ : ℝ) := by
    simp only [ocEpsilon, hMJne, ↓reduceIte, inv_inv]
  have hexp : q ^ (M + J) / (q - 1) = q ^ M / (q - 1) * q ^ J := by
    rw [pow_add]; ring
  have hXJ : (Λ : ℝ) ^ (q ^ (M + J) / (q - 1)) = X ^ (q ^ J) := by
    rw [hexp, Real.rpow_mul (by linarith)]
  rw [hεM, hεMJ, hXJ]
  have hX0 : 0 ≤ X := by linarith
  have hqJ : 0 ≤ q ^ J := pow_nonneg (by linarith) _
  have h1 : 1 ≤ X ^ (q ^ J) := Real.one_le_rpow hX1 hqJ
  have h2 : (⌈X ^ (q ^ J)⌉₊ : ℝ) ≤ X ^ (q ^ J) + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have h3 : X ^ (q ^ J) ≤ ((⌈X⌉₊ : ℝ)) ^ (q ^ J) :=
    Real.rpow_le_rpow hX0 (Nat.le_ceil X) hqJ
  linarith

theorem identityC2_main {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 1 ≤ Λ) {M : ℕ} (hM : 1 ≤ M)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (J : ℕ) {E P : ℝ} (hE : P + 2 * q ^ J ≤ E) :
    ocEpsilon q Λ (M + J) ^ (-(1 + s)) * ocEpsilon q Λ M ^ E ≤ 4 * ocEpsilon q Λ M ^ P := by
  have hεM : 0 < ocEpsilon q Λ M := Construction.Stream.ocEpsilon_pos hΛ
  have hεMJ : 0 < ocEpsilon q Λ (M + J) := Construction.Stream.ocEpsilon_pos hΛ
  have hε1 : ocEpsilon q Λ M ≤ 1 := ocEpsilon_le_one hΛ M
  have hqJ : 0 ≤ q ^ J := pow_nonneg (by linarith) _
  have hinv := identityC2_eps_inv_le hq hΛ hM J
  have h1s : 0 ≤ 1 + s := by linarith
  -- ε_{M+J}^{-(1+s)} = (ε_{M+J}⁻¹)^{1+s}
  have e1 : ocEpsilon q Λ (M + J) ^ (-(1 + s)) = ((ocEpsilon q Λ (M + J))⁻¹) ^ (1 + s) := by
    rw [Real.rpow_neg hεMJ.le, Real.inv_rpow hεMJ.le]
  have hpos : 0 ≤ (ocEpsilon q Λ (M + J))⁻¹ := inv_nonneg.2 hεMJ.le
  have h2 : ((ocEpsilon q Λ (M + J))⁻¹) ^ (1 + s) ≤
      (2 * ((ocEpsilon q Λ M)⁻¹) ^ (q ^ J)) ^ (1 + s) := Real.rpow_le_rpow hpos hinv h1s
  have hinvM : 0 ≤ ((ocEpsilon q Λ M)⁻¹) ^ (q ^ J) := Real.rpow_nonneg (inv_nonneg.2 hεM.le) _
  have h3 : (2 * ((ocEpsilon q Λ M)⁻¹) ^ (q ^ J)) ^ (1 + s) =
      2 ^ (1 + s) * ((ocEpsilon q Λ M) ^ (-(q ^ J * (1 + s)))) := by
    rw [Real.mul_rpow (by norm_num) hinvM, ← Real.rpow_mul (inv_nonneg.2 hεM.le),
      Real.inv_rpow hεM.le, ← Real.rpow_neg hεM.le]
  have h4 : (2 : ℝ) ^ (1 + s) ≤ 4 := by
    calc (2 : ℝ) ^ (1 + s) ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hpowM : 0 < ocEpsilon q Λ M ^ (-(q ^ J * (1 + s))) := Real.rpow_pos_of_pos hεM _
  have h5 : ocEpsilon q Λ (M + J) ^ (-(1 + s)) ≤ 4 * ocEpsilon q Λ M ^ (-(q ^ J * (1 + s))) := by
    rw [e1]
    refine h2.trans ?_
    rw [h3]
    exact mul_le_mul_of_nonneg_right h4 hpowM.le
  have hEM : 0 ≤ ocEpsilon q Λ M ^ E := Real.rpow_nonneg hεM.le _
  have h6 : ocEpsilon q Λ (M + J) ^ (-(1 + s)) * ocEpsilon q Λ M ^ E ≤
      4 * ocEpsilon q Λ M ^ (-(q ^ J * (1 + s))) * ocEpsilon q Λ M ^ E :=
    mul_le_mul_of_nonneg_right h5 hEM
  have h7 : ocEpsilon q Λ M ^ (-(q ^ J * (1 + s))) * ocEpsilon q Λ M ^ E =
      ocEpsilon q Λ M ^ (-(q ^ J * (1 + s)) + E) := (Real.rpow_add hεM _ _).symm
  have h8 : ocEpsilon q Λ M ^ (-(q ^ J * (1 + s)) + E) ≤ ocEpsilon q Λ M ^ P := by
    apply Real.rpow_le_rpow_of_exponent_ge hεM hε1
    have hh := mul_le_mul_of_nonneg_left hs1.le hqJ
    linarith
  calc ocEpsilon q Λ (M + J) ^ (-(1 + s)) * ocEpsilon q Λ M ^ E
      ≤ 4 * ocEpsilon q Λ M ^ (-(q ^ J * (1 + s))) * ocEpsilon q Λ M ^ E := h6
    _ = 4 * (ocEpsilon q Λ M ^ (-(q ^ J * (1 + s))) * ocEpsilon q Λ M ^ E) := by ring
    _ = 4 * ocEpsilon q Λ M ^ (-(q ^ J * (1 + s)) + E) := by rw [h7]
    _ ≤ 4 * ocEpsilon q Λ M ^ P := by linarith [h8]

end AVRegularity.WeakEntryProofs.Identity
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Identity

/-! **Identity A6: the orders.** The component reserve of a stage `i` covers the order that the
readout of the level `i` needs: `weakComparisonReserve R v ≥ (M + J_w − i)·N_w + 5`.

* `identityA2_gamma_lt`, `identityA2_Rw_pos`: `R_w ≥ 1` from the menu inequality `menu_R`
  (`ocGamma α q < 1/24`, so `2 a_* < 1`);
* `identityA2_Nw_ge`: `N_w ≥ 6` from `menu_N` (`q < 17/16`);
* `identityA2_reserve_ge`: the natural-number count.

The degenerate cases are included: `i = M + J_w` (`d = 0`, rank `0`) needs `5 ≤ R_w(J_wN_w − 1)`;
`J_w = 1` and `R_w = 1` needs `N_w − 1 ≥ 5`. -/

open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly

/-- For an admissible `q` and `α < 1/3`, `ocGamma α q < 1/24`. -/
theorem identityA2_gamma_lt {α q : ℝ} (hα : 0 < α) (hα1 : α < 1 / 3) (hq : 1 < q)
    (hq1 : q < 17 / 16) : ocGamma α q < 1 / 24 := by
  unfold ocGamma
  rw [div_lt_iff₀ (by linarith)]
  have h1 : (q - 1) * (1 + α) ≤ (1 / 16) * (4 / 3) := by
    refine mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  linarith

/-- `R_w ≥ 1` from the menu inequality. -/
theorem identityA2_Rw_pos {Pw : ℝ} {Jw Rw : ℕ} {α q : ℝ} (hα : 0 < α) (hα1 : α < 1 / 3)
    (hq : 1 < q) (hq1 : q < 17 / 16) (hP : 0 < Pw)
    (hmenu : Pw + 2 * q ^ Jw + 1 + q ^ Jw + 1 < 2 * ((q + 2) * ocGamma α q) * (Rw + 1)) :
    1 ≤ Rw := by
  by_contra hR
  have hR0 : Rw = 0 := by omega
  subst hR0
  have hg := identityA2_gamma_lt hα hα1 hq hq1
  have hg0 : 0 < ocGamma α q := by
    unfold ocGamma; positivity
  have hqJ : 1 ≤ q ^ Jw := one_le_pow₀ hq.le
  simp only [Nat.cast_zero, zero_add, mul_one] at hmenu
  nlinarith

/-- `N_w ≥ 6` from the menu inequality. -/
theorem identityA2_Nw_ge {Pw : ℝ} {Jw Nw : ℕ} {q : ℝ} (hq : 1 < q) (hq1 : q < 17 / 16)
    (hP : 0 < Pw) (hmenu : Pw + 2 * q ^ Jw + 1 + 2 < Nw * (q - 1)) : 6 ≤ Nw := by
  by_contra hN
  have hN' : (Nw : ℝ) ≤ 5 := by exact_mod_cast (by omega : Nw ≤ 5)
  have hqJ : 1 ≤ q ^ Jw := one_le_pow₀ hq.le
  nlinarith

/-- The reserve of a component of the stage `i` covers the order `(M + J_w − i) N_w + 5`. -/
theorem identityA2_reserve_ge {Jw Rw Nw d rank : ℕ} (hd : d < Jw) (hR : 1 ≤ Rw) (hN : 6 ≤ Nw)
    (hrank : rank ≤ d * Rw) :
    d * Nw + 5 ≤ (Jw * Rw - rank) * (Jw * Nw - 1) := by
  obtain ⟨e, he⟩ : ∃ e, Jw = d + e + 1 := ⟨Jw - d - 1, by omega⟩
  have h1 : 1 ≤ Jw * Rw - rank := by
    have : d * Rw + Rw ≤ Jw * Rw := by rw [he]; nlinarith
    omega
  have h2 : d * Nw + 5 ≤ Jw * Nw - 1 := by
    have : d * Nw + Nw ≤ Jw * Nw := by rw [he]; nlinarith
    omega
  exact h2.trans (Nat.le_mul_of_pos_left _ (by omega))

end AVRegularity.WeakEntryProofs.Identity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Identity

/-! **Identity A1: the passage instance and run from the entry data**, at the same request `R`
(not the lifted one of `weakEntryHighQuietCase`), and the reserve count at the entry data.

* `identityInstance`: the `WeakPassageInstance pp R` of `x`, `g` (floors of `pp` below those of
  the entry plan);
* `identityRun`: the run of `s`, `θ` and the reduction `red`;
* `identity_reserve_ge`: for `M < i ≤ M + J_w` and a component `v` of the stage `i`,
  `weakComparisonReserve R v.1 ≥ (M + J_w − i)·N_w + 5`.

The degenerate cases are included: `J_w = 1`, `i = M + 1`: reserve `R_w(N_w − 1) ≥ 5`; the root
component has rank `0`. -/

open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

/-- The passage instance of the entry data at the request `R`. -/
def identityInstance (pp : WeakPassagePlan)
    (hb : pp.baseFloor B ≤ plan.baseFloor B)
    (hm : pp.momentFloor A ≤ plan.momentFloor A)
    (hl : ∀ j, pp.levelFloor R j ≤ plan.levelFloor R C j)
    (x : WeakEntryData plan C) (g : WeakEntryStages x) : WeakPassageInstance pp R :=
  { base_ge := hb.trans x.base_ge
    moment_ge := hm.trans x.moment_ge
    j₀ := x.j₀
    carrier := x.carrier400
    M := x.M
    level_ge := (hl x.j₀).trans x.level_ge
    D := x.D
    alpha := x.alpha
    q_eq := x.q_eq
    base_eq := x.base_eq
    profile_eq := x.profile_eq
    streams := x.streams
    band := x.band
    terminal := x.terminal
    Dm := x.Dm
    order_ge := x.order_ge
    P := x.P
    stage := g.stage
    construction := g.construction }

/-- The run of the instance from the schedule and the reduction. -/
def identityRun (pp : WeakPassagePlan)
    (hb : pp.baseFloor B ≤ plan.baseFloor B)
    (hm : pp.momentFloor A ≤ plan.momentFloor A)
    (hl : ∀ j, pp.levelFloor R j ≤ plan.levelFloor R C j)
    {x : WeakEntryData plan C} {g : WeakEntryStages x} (s : WeakEntrySchedule g)
    {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (red : WeakEntryReduced s θ) : WeakPassageRun (identityInstance pp hb hm hl x g) :=
  ⟨x.a, f, θ, hθ, s.tq, red.Ur, red.Urw, red.Urk, red.reduction⟩

/-- The reserve of a component of the stage `i` covers the order `(M + J_w − i) N_w + 5`. -/
theorem identity_reserve_ge {x : WeakEntryData plan C} (g : WeakEntryStages x) (i : ℕ)
    (hMi : x.M < i) (hi : i ≤ x.M + A.Jw) (v : CompIn (g.stage i).comps) :
    (x.M + A.Jw - i) * A.Nw + 5 ≤ weakComparisonReserve R v.1 := by
  have hR := identityA2_Rw_pos B.hα₀ B.hα₁ B.hq.1 B.hq.2.1 A.Pw_pos x.menu_R
  have hN := identityA2_Nw_ge B.hq.1 B.hq.2.1 A.Pw_pos x.menu_N
  have hrank := (weakConstruction_rank_bounds x.P _ _ _ _ _ _ g.construction i hMi.le hi).1 v.1 v.2
  exact identityA2_reserve_ge (by omega) hR hN hrank

end AVRegularity.WeakEntryProofs.Identity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Identity

/-! **The order-zero mass bound of the reduction at every level `i`.**

The raw energy statement (`weak_entry_raw_energy_at_offset`) exports the raw energy of the level `M` only. A comparison
input at the level `i` (`WeakComparisonInput.mass_bound`) needs the order-zero mass norm of
`truncate (r.Ur i)` on `[t_{i+1}, a + T₀]`, for every `M < i ≤ M + J_w`. It follows from the
passage bound `weakHigh_step_total` (the level `i` on the whole window `[t_{i+1}, a + T₀]` is at
most `C_pass C_q Φ_{i+1}`) with the chain `weakHigh_sup_chain` and the root bound.

* `identityA1_orderZero_le`: the squared order-zero norm of the family `Uhi i` is at most
  `max(1, C_pass C_q)^{J_w} · 2 ‖f‖²` on `[t_{i+1}, a + T₀]`.
* `identityA4_mass_bound`: the same for `weightedNorm 1 π 1 (truncate (r.Ur i))`, in the form of
  the field `mass_bound`, with the bound `√(2 max(1, C_pass C_q)^{J_w} ‖f‖²)`.

The degenerate cases are included: `f = 0` gives `0`; `i = M + J_w` is the root value with
`Q^0`; `J_w = 1` has only the root level. -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x} {m : ℕ} {Cp Cq : ℝ}
  {s : WeakEntrySchedule g} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
  {r : WeakEntryReduced s θ} {Uhi : ∀ i, WeakReductionFamily g m i}
  {Whi : ∀ i, WeakReductionLift g m i}

/-- The root level: the squared order-zero norm is at most `2 ‖f‖²` on `[t_{M+J_w+1}, a + T₀]`. -/
theorem identityA1_root_le
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (hfam : WeakHigherFamilies s θ r m Uhi Whi)
    (t : ℝ) (ht : t ∈ Set.Icc (s.tq (x.M + A.Jw + 1)) (x.a + A.T₀)) :
    weakOrderZeroNormSq (x.M + A.Jw) (Uhi (x.M + A.Jw)) t ≤ 2 * l2NormSq f := by
  have hcomp : (g.stage (x.M + A.Jw)).comps = {(⟨0, []⟩ : Comp)} :=
    g.construction.2.1.2.1
  have hr : (⟨0, []⟩ : Comp) ∈ (g.stage (x.M + A.Jw)).comps := by rw [hcomp]; simp
  have key : ∀ c : Comp, c ∈ (g.stage (x.M + A.Jw)).comps → c = ⟨0, []⟩ := fun c hc => by
    rw [hcomp] at hc
    exact Finset.mem_singleton.1 hc
  have : Subsingleton (CompIn (g.stage (x.M + A.Jw)).comps) :=
    ⟨fun v w => Subtype.ext ((key _ v.2).trans (key _ w.2).symm)⟩
  have hT := weakEntrySchedule_tq_le s (x.M + A.Jw) (by have := A.Jw_pos; omega) le_rfl
  have hval := factorialNormSq_orderZero_value (Uhi (x.M + A.Jw) ⟨_, hr⟩ t) (θ t)
    (hfam.1 hr t ht)
  have hoz : weakOrderZeroNormSq (x.M + A.Jw) (Uhi (x.M + A.Jw)) t = 2 * l2NormSq (θ t) := by
    unfold weakOrderZeroNormSq massNormSq
    rw [Fintype.sum_subsingleton _ (⟨⟨0, []⟩, hr⟩ : CompIn (g.stage (x.M + A.Jw)).comps)]
    simp only [weakMass_root]
    rw [hval]
    unfold l2NormSq
    norm_num
  rw [hoz]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  let S := weakEntryRawSetting g
  have hb := isWindowDrift_of_isContDrift
    (streamSeq_isContDrift B.hζ S.base128 S.streams (x.M + A.Jw)) x.a (x.a + A.T₀)
  have hlt : x.a < s.tq (x.M + A.Jw + 1) := s.start
  exact rawEnergy_l2NormSq_le S.kappa_pos.le
    (by linarith [A.τ_small, s.finish, hlt, hT, ht.1, ht.2]) hb hθ t
    ⟨hlt.le.trans ht.1, ht.2⟩

/-- **The order-zero norm at every level `M < i ≤ M + J_w`** on `[t_{i+1}, a + T₀]`. -/
theorem identityA1_orderZero_le (hCp : 0 ≤ Cp) (hCq : 0 ≤ Cq)
    (hAb : WeakEntryPassageEnergyBound plan R C m Cp)
    (hBb : WeakEntryQuietTraceHighBound plan R C m Cq)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (hfam : WeakHigherFamilies s θ r m Uhi Whi) (i : ℕ) (hMi : x.M < i) (hi : i ≤ x.M + A.Jw)
    (t : ℝ) (ht : t ∈ Set.Icc (s.tq (i + 1)) (x.a + A.T₀)) :
    weakOrderZeroNormSq i (Uhi i) t ≤ max 1 (Cp * Cq) ^ A.Jw * (2 * l2NormSq f) := by
  have hQ : 0 ≤ Cp * Cq := mul_nonneg hCp hCq
  have hL : 0 ≤ l2NormSq f := integral_nonneg fun _ => sq_nonneg _
  have hM1 : (1 : ℝ) ≤ max 1 (Cp * Cq) := le_max_left _ _
  rcases Nat.lt_or_ge i (x.M + A.Jw) with hlt | hge
  · -- a passage level
    obtain ⟨n, hn⟩ : ∃ n, x.M + A.Jw - (i + 1) = n := ⟨_, rfl⟩
    have h1 := weakHigh_step_total hCp hAb hBb hθ hfam (i + 1) (by omega) (by omega) t ht
    rw [Nat.add_sub_cancel] at h1
    have h2 := weakOrderZeroNormSq_le g i (Uhi i) t (plan.radius R * x.D.eps i)
    have hchain := weakHigh_sup_chain hCp hAb hBb hθ hfam n (by omega)
    rw [show x.M + A.Jw - n = i + 1 by omega] at hchain
    have hroot := weakHigh_sup_root hθ hfam
    have h3 : ENNReal.ofReal (weakOrderZeroNormSq i (Uhi i) t) ≤
        ENNReal.ofReal ((Cp * Cq) ^ (n + 1) * (2 * l2NormSq f)) := by
      calc ENNReal.ofReal (weakOrderZeroNormSq i (Uhi i) t)
          ≤ ENNReal.ofReal (massNormSq (plan.radius R * x.D.eps i)
              (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
              (fun v => (Uhi i v t).val)) := ENNReal.ofReal_le_ofReal h2
        _ ≤ _ := le_self_add.trans h1
        _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal Cq * ((ENNReal.ofReal Cp * ENNReal.ofReal Cq) ^ n *
              ENNReal.ofReal (2 * l2NormSq f))) :=
            mul_le_mul_right (mul_le_mul_right (hchain.trans (mul_le_mul_right hroot _)) _) _
        _ = ENNReal.ofReal ((Cp * Cq) ^ (n + 1) * (2 * l2NormSq f)) := by
            rw [ENNReal.ofReal_mul (pow_nonneg hQ _), ENNReal.ofReal_pow hQ,
              ENNReal.ofReal_mul hCp, pow_succ']
            ring
    have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
    refine h4.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (Cp * Cq) ^ (n + 1) ≤ max 1 (Cp * Cq) ^ (n + 1) :=
          pow_le_pow_left₀ hQ (le_max_right _ _) _
      _ ≤ max 1 (Cp * Cq) ^ A.Jw := pow_le_pow_right₀ hM1 (by omega)
  · have hieq : i = x.M + A.Jw := le_antisymm hi hge
    subst hieq
    refine (identityA1_root_le hθ hfam t ht).trans ?_
    have : (1 : ℝ) ≤ max 1 (Cp * Cq) ^ A.Jw := one_le_pow₀ hM1
    nlinarith [mul_nonneg hL zero_le_two]

end AVRegularity.WeakEntryProofs.Identity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Identity

/-! **The field `mass_bound` of the comparison input** at every level
`M < i ≤ M + J_w`, in the form `weightedNorm 1 π 1 (truncate (r.Ur i)) ≤ Φ` with the constant
`identityMassConst = √(2 max(1, C_pass C_q)^{J_w} ‖f‖²)` (the constants of the raw energy at the offset `0`).

The degenerate case `f = 0` gives `Φ = 0`; the constants do not depend on `D_m`. -/

open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x}

/-- The raw constant of the comparison inputs: `√(2 max(1, C_pass C_q)^{J_w}) · ‖f‖₂`. -/
def identityMassConst (plan : WeakEntryGluePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (f : Vec 2 → ℝ) : ℝ :=
  Real.sqrt (2 * max 1 (weakEntryPassageConst plan R C 0 * weakEntryQuietConst plan R C 0) ^ A.Jw
    * l2NormSq f)

/-- **The field `mass_bound` at every level** of the reduction `red`. -/
theorem identityA4_mass_bound (hcommon : WeakEntryCommonOK plan)
    (hA : WeakEntryPassageEnergyStatement plan) (hB : WeakEntryQuietTraceHighStatement plan)
    (s : WeakEntrySchedule g) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (red : WeakEntryReduced s θ) (i : ℕ) (hMi : x.M < i) (hi : i ≤ x.M + A.Jw)
    (t : ℝ) (ht : t ∈ Set.Icc (s.tq (i + 1)) (x.a + A.T₀)) :
    weightedNorm 1 (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
      (fun _ => 1) (fun v => truncateTorusHk (Nat.zero_le R.Kw) (red.Ur i v t)) ≤
      identityMassConst plan R C f := by
  obtain ⟨Uhi, Whi, hfam⟩ := weakReduction_higher_families hcommon s f θ hθ red 0
  obtain ⟨hCp, hAb⟩ := weakEntryPassageConst_spec (C := C) hA (Nat.zero_le _)
  obtain ⟨hCq, hBb⟩ := weakEntryQuietConst_spec (C := C) hB (Nat.zero_le _)
  have h := identityA1_orderZero_le hCp hCq hAb hBb hθ hfam i hMi hi t ht
  have htr : ∀ v, truncateTorusHk (Nat.zero_le R.Kw) (red.Ur i v t) =
      truncateTorusHk (Nat.zero_le _) (Uhi i v t) := fun v => by
    rw [← hfam.2.2.1 i hMi.le hi v t ht]
    rfl
  unfold weightedNorm identityMassConst
  refine Real.sqrt_le_sqrt ?_
  have e1 : massNormSq (E := fun v : CompIn (g.stage i).comps => ScalarH v.1.root)
      (K := fun _ => 0) 1 (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1 / 1 ^ 2)
      (fun v => (truncateTorusHk (Nat.zero_le R.Kw) (red.Ur i v t)).val) =
      weakOrderZeroNormSq i (Uhi i) t := by
    unfold weakOrderZeroNormSq massNormSq
    simp only [htr, one_pow, div_one]
  rw [e1]
  nlinarith [h]

end AVRegularity.WeakEntryProofs.Identity
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Identity

/-! **Identity A2, A3, A4: the classical representatives, the errors and the comparison input.**

* `identityAU j t`: classical representatives of order `L_w + 3` of `red.Ur j · t` (by choice;
  `K_w ≥ L_w + 5`);
* `identityLift s red i t`: the glued lift `Λ_i 𝓡_i` of the representatives of the level `i-1`;
* `IdentityLiftOK`: at the times of the window the lift is of class `C^{L_w+3−N_w}` and periodic
  (the smoothness is `readoutLinear_lift_contDiff`; the periodicity of the glued lift is
  `weakEntry_gluedLift_periodic`);
* `identityEw`, `identityE`: the error classes `trunc₁(U_i) − [Λ_i 𝓡_i aU]` in `TorusHk 1` and its
  truncation in `TorusHk 0`; they are classical with the representative `aU_i − Λ_i 𝓡_i aU_{i-1}`;
* `identityInput`: the `WeakComparisonInput` at the level `i` (`start := s.start`).

The degenerate cases are included: `f = 0` gives `Φ = 0`, `U = 0`, `e = 0`; `i = M + J_w` is the
root. -/

section
open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Construction.Preservation.FullLift
  AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x} {s : WeakEntrySchedule g}
  {θ : ℝ → Vec 2 → ℝ}

/-- The classical representatives of order `L_w + 3` of the reduction's family of the level `j`. -/
def identityAU (red : WeakEntryReduced s θ) (j : ℕ) (t : ℝ) :
    CompIn (g.stage j).comps → Vec 2 → ℝ := fun v =>
  Classical.choose (torusHk_classicalRep_exists_vec R.Kw (A.Lw + 3)
    (by have := R.field_order; omega) (red.Ur j v t))

theorem identityAU_rep (red : WeakEntryReduced s θ) (j : ℕ) (t : ℝ) (v : CompIn (g.stage j).comps) :
    IsClassicalRep (red.Ur j v t) (identityAU red j t v) (A.Lw + 3) :=
  Classical.choose_spec (torusHk_classicalRep_exists_vec R.Kw (A.Lw + 3)
    (by have := R.field_order; omega) (red.Ur j v t))

/-- The lift `Λ_i 𝓡_i` of the representatives of the level `i - 1`. -/
def identityLift (red : WeakEntryReduced s θ) (i : ℕ) (t : ℝ) :
    CompIn (g.stage i).comps → Vec 2 → ℝ :=
  weakGluedLift i A.Nw (A.Jw * A.Rw) (g.stage i) (s.CcR i) t
    (weakReadoutStep i A.η₀ (g.stage i) (g.stage (i - 1)) (identityAU red (i - 1) t))

/-- **The lift is of class `C^{L_w+3−N_w}` and periodic** at the times of the window. -/
def IdentityLiftOK (red : WeakEntryReduced s θ) (i : ℕ) : Prop :=
  ∀ t ∈ Set.Icc (s.tq i) (x.a + A.T₀), ∀ v,
    ContDiff ℝ ((A.Lw + 3 - A.Nw : ℕ) : ℕ∞) (identityLift red i t v) ∧
      IsZ2Periodic (identityLift red i t v)

open scoped Classical in
/-- The error in `TorusHk 1`. -/
def identityEw (red : WeakEntryReduced s θ) (i : ℕ) :
    ∀ v : CompIn (g.stage i).comps, ℝ → TorusHk 1 (ScalarH v.1.root) := fun v t =>
  truncateTorusHk (by have := R.field_order; omega : 1 ≤ R.Kw) (red.Ur i v t) -
    if h : ContDiff ℝ ((1 : ℕ) : ℕ∞) (identityLift red i t v) ∧
        IsZ2Periodic (identityLift red i t v) then
      periodicHk 1 (identityLift red i t v) h.1 h.2 else 0

/-- The error in `TorusHk 0`: the truncation of `identityEw`. -/
def identityE (red : WeakEntryReduced s θ) (i : ℕ) :
    ∀ v : CompIn (g.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root) := fun v t =>
  truncateTorusHk (Nat.zero_le 1) (identityEw red i v t)

theorem identityLiftOK_one (hLw : A.Nw ≤ A.Lw) {red : WeakEntryReduced s θ} {i : ℕ}
    (hok : IdentityLiftOK red i) {t : ℝ} (ht : t ∈ Set.Icc (s.tq i) (x.a + A.T₀))
    (v : CompIn (g.stage i).comps) :
    ContDiff ℝ ((1 : ℕ) : ℕ∞) (identityLift red i t v) ∧ IsZ2Periodic (identityLift red i t v) :=
  ⟨(hok t ht v).1.of_le (by exact_mod_cast (by omega : 1 ≤ A.Lw + 3 - A.Nw)), (hok t ht v).2⟩

/-- **The error is classical**, with representative `aU_i − Λ_i 𝓡_i aU_{i-1}`, at the order `0`. -/
theorem identityE_rep (hLw : A.Nw ≤ A.Lw) {red : WeakEntryReduced s θ} {i : ℕ}
    (hok : IdentityLiftOK red i) {t : ℝ} (ht : t ∈ Set.Icc (s.tq i) (x.a + A.T₀))
    (v : CompIn (g.stage i).comps) :
    IsClassicalRep (identityE red i v t)
      (fun y => identityAU red i t v y - identityLift red i t v y) 0 := by
  obtain ⟨h1, h2⟩ := identityLiftOK_one hLw hok ht v
  have hU : IsClassicalRep (truncateTorusHk (by have := R.field_order; omega : 1 ≤ R.Kw)
      (red.Ur i v t)) (identityAU red i t v) 1 :=
    classicalRep_truncate _ le_rfl _ _ (classicalRep_order_mono _ _ (identityAU_rep red i t v)
      (by omega))
  have hP : IsClassicalRep (periodicHk 1 (identityLift red i t v) h1 h2) (identityLift red i t v) 1 :=
    periodicHk_isClassicalRep 1 h1 h2 le_rfl
  have hd := isClassicalRep_sub hU hP
  have : identityEw red i v t = truncateTorusHk (by have := R.field_order; omega : 1 ≤ R.Kw)
      (red.Ur i v t) - periodicHk 1 (identityLift red i t v) h1 h2 := by
    unfold identityEw
    simp only [h1, h2, and_self, ↓reduceDIte]
  unfold identityE
  rw [this]
  exact classicalRep_truncate _ le_rfl _ _ (classicalRep_order_mono _ _ hd (Nat.zero_le _))
end

/-! **Identity A4: the comparison input** `identityInput` at the level `i`, with
`CcR := s.CcR`, `lifts := s.lifts`, `aU := identityAU (i-1)`, `Φ := identityMassConst`,
`start := s.start`, the lift-order floors from the entry data and the floors of `pp`.

The degenerate cases are included: `f = 0`: `Φ = 0`; the fields `identity` and `truncation` hold by
construction. -/

section
open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Construction.Preservation.FullLift
  AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x} {s : WeakEntrySchedule g}
  {θ : ℝ → Vec 2 → ℝ} {f : Vec 2 → ℝ}

/-- **The comparison input at the level `i`** of the entry reduction. -/
def identityInput (pp : WeakPassagePlan)
    (hb : pp.baseFloor B ≤ plan.baseFloor B) (hm : pp.momentFloor A ≤ plan.momentFloor A)
    (hl : ∀ j, pp.levelFloor R j ≤ plan.levelFloor R C j)
    (hlf : pp.liftFloor A ≤ plan.liftFloor A)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (red : WeakEntryReduced s θ) (hLw : A.Nw ≤ A.Lw) (i : ℕ)
    (hok : IdentityLiftOK red i)
    (hmass : ∀ t ∈ Set.Icc (s.tq (i + 1)) (x.a + A.T₀),
      weightedNorm 1 (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
        (fun _ => 1) (fun v => truncateTorusHk (Nat.zero_le R.Kw) (red.Ur i v t)) ≤
        identityMassConst plan R C f) :
    WeakComparisonInput (identityRun pp hb hm hl s hθ red) i where
  CcR := s.CcR
  lifts := s.lifts
  Φ := identityMassConst plan R C f
  aU := identityAU red (i - 1)
  e := identityE red i
  ew := identityEw red i
  mass_bound := hmass
  representative := fun v t _ =>
    classicalRep_order_mono _ _ (identityAU_rep red (i - 1) t v) (by omega)
  identity := fun v t ht => by
    have h0 := identityE_rep hLw hok ht v
    have hU : IsClassicalRep (truncateTorusHk (Nat.zero_le R.Kw) (red.Ur i v t))
        (identityAU red i t v) 0 :=
      classicalRep_truncate _ (le_refl 0) _ _
        (classicalRep_order_mono _ _ (identityAU_rep red i t v) (Nat.zero_le _))
    have e1 := classicalRep_value_ae _ _ h0
    have e2 := classicalRep_value_ae _ _ hU
    filter_upwards [e1, e2] with y h1 h2
    refine h1.trans ?_
    change identityAU red i t v y - identityLift red i t v y =
      ((truncateTorusHk (Nat.zero_le R.Kw) (red.Ur i v t)).toFunction.jet (valueIndex2 0) y -
        identityLift red i t v y)
    rw [h2]
  truncation := fun v => Filter.Eventually.of_forall fun t => rfl
  sX_ge := hlf.trans x.sX_ge
  sZ_ge := hlf.trans x.sZ_ge
  start := s.start
end

/-! **Identity A5, A6: the error at its reserve and as a classical field.**

For `M < i ≤ M + J_w`, with `n_i = (M + J_w − i) N_w`: the comparison I1 on `identityInput`
gives `ehi i v t` in `TorusHk (n_i + 5)` (the truncation of the component reserve) such that

* `ehi i v t` is a classical representative of order `n_i + 3` of the field
  `aE = aU_i − Λ_i 𝓡_i aU_{i-1}` (two continuous periodic representatives agree);
* `∑_v π_v⁻¹ |ehi i v t|²_{ρ ε_i} ≤ (energyC · forceC · ε_M^{P_1} · Φ)²` on the window.

The degenerate cases are included: `Φ = 0` (`f = 0`) gives `ehi = 0` on the window; `i = M + J_w`
has `n_i = 0` and order `5`; `J_w = 1` has only this level. -/

section
open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Construction.Preservation.FullLift
  AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Assembly
  AVRegularity.Providers.WeakGen.Comparison AVRegularity.IterationPassage.ErrorJets

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x} {s : WeakEntrySchedule g}
  {θ : ℝ → Vec 2 → ℝ} {f : Vec 2 → ℝ}

/-- The smoothness orders: `n_i + 3 ≤ L_w + 3 − N_w` for `M < i`. -/
theorem identityA7_order_le (x : WeakEntryData plan C) {i : ℕ} (hMi : x.M < i) :
    (x.M + A.Jw - i) * A.Nw + 3 ≤ A.Lw + 3 - A.Nw := by
  have h := x.readout_order
  have hJ := A.Jw_pos
  have h1 : (x.M + A.Jw - i + 1) * A.Nw ≤ A.Jw * A.Nw :=
    Nat.mul_le_mul_right A.Nw (show x.M + A.Jw - i + 1 ≤ A.Jw by omega)
  have h2 : (x.M + A.Jw - i) * A.Nw + A.Nw ≤ A.Jw * A.Nw := by
    rw [← Nat.succ_mul]; exact h1
  rw [h]
  omega

/-- **The errors at their reserves** (A5 and A6), from I1. -/
theorem identityA7_errors (pp : WeakPassagePlan)
    (hb : pp.baseFloor B ≤ plan.baseFloor B) (hm : pp.momentFloor A ≤ plan.momentFloor A)
    (hl : ∀ j, pp.levelFloor R j ≤ plan.levelFloor R C j)
    (hlf : pp.liftFloor A ≤ plan.liftFloor A)
    (hI1 : WeakPassageComparisonHighStatement pp)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (red : WeakEntryReduced s θ) (hLw : A.Nw ≤ A.Lw) (i : ℕ) (hMi : x.M < i)
    (hi : i ≤ x.M + A.Jw) (hok : IdentityLiftOK red i)
    (hmass : ∀ t ∈ Set.Icc (s.tq (i + 1)) (x.a + A.T₀),
      weightedNorm 1 (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
        (fun _ => 1) (fun v => truncateTorusHk (Nat.zero_le R.Kw) (red.Ur i v t)) ≤
        identityMassConst plan R C f) :
    ∃ ehi : ∀ v : CompIn (g.stage i).comps, ℝ →
        TorusHk ((x.M + A.Jw - i) * A.Nw + 5) (ScalarH v.1.root),
      (∀ t ∈ Set.Icc (s.tq i) (x.a + A.T₀), ∀ v,
        IsClassicalRep (ehi v t)
          (fun y => identityAU red i t v y - identityLift red i t v y)
          ((x.M + A.Jw - i) * A.Nw + 3)) ∧
      ∀ t ∈ Set.Icc (s.tq i) (x.a + A.T₀),
        ∑ v : CompIn (g.stage i).comps, (weakMass x.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
            factorialNormSq (pp.radius R * x.D.eps i) (ehi v t).val ≤
          (pp.energyC R * (pp.forceC R * x.D.eps x.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) *
            identityMassConst plan R C f)) ^ 2 := by
  let h := identityInput pp hb hm hl hlf hθ red hLw i hok hmass
  obtain ⟨e', hrel, hbound⟩ := hI1 x.menu_N x.menu_R (identityInstance pp hb hm hl x g)
    (identityRun pp hb hm hl s hθ red) i hMi hi h
  have hres : ∀ v : CompIn (g.stage i).comps,
      (x.M + A.Jw - i) * A.Nw + 5 ≤ weakComparisonReserve R v.1 :=
    fun v => identity_reserve_ge g i hMi hi v
  refine ⟨fun v t => truncateTorusHk (hres v) (e' v t), fun t ht v => ?_, fun t ht => ?_⟩
  · have hK : (x.M + A.Jw - i) * A.Nw + 3 + 2 ≤ (x.M + A.Jw - i) * A.Nw + 5 := le_rfl
    have hA7 := identityA7_order_le x hMi
    have hc : ContDiff ℝ (((x.M + A.Jw - i) * A.Nw + 3 : ℕ) : ℕ∞)
        (fun y => identityAU red i t v y - identityLift red i t v y) := by
      refine ContDiff.sub ?_ ?_
      · exact (identityAU_rep red i t v).2.1.of_le
          (Nat.cast_le.mpr (show (x.M + A.Jw - i) * A.Nw + 3 ≤ A.Lw + 3 by omega))
      · exact (hok t ht v).1.of_le (by exact_mod_cast hA7)
    have hp : IsZ2Periodic (fun y => identityAU red i t v y - identityLift red i t v y) := by
      intro n y
      show identityAU red i t v (y + latticeShift n) - identityLift red i t v (y + latticeShift n) =
        _
      rw [(identityAU_rep red i t v).2.2.1 n y, (hok t ht v).2 n y]
    refine liftId_isClassicalRep_of_smooth hK _ _ hc hp ?_
    have e0 := classicalRep_value_ae _ _ (identityE_rep hLw hok ht v)
    have e1 : (truncateTorusHk (hres v) (e' v t)).toFunction.jet
        (valueIndex2 ((x.M + A.Jw - i) * A.Nw + 5)) =
        (e' v t).toFunction.jet (valueIndex2 (weakComparisonReserve R v.1)) := rfl
    have e2 : (truncateTorusHk (Nat.zero_le _) (e' v t)).toFunction.jet (valueIndex2 0) =
        (e' v t).toFunction.jet (valueIndex2 (weakComparisonReserve R v.1)) := rfl
    rw [e1, ← e2, hrel v t ht]
    exact e0
  · refine le_trans (Finset.sum_le_sum fun v _ => ?_) (hbound t ht)
    exact mul_le_mul_of_nonneg_left
      (CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ _ _)
      (inv_nonneg.2 (weakEntry_mass_pos g v.1).le)
end

/-! **Identity C1: the telescoping sum, the root value and the window.**

* `identityC1_step`: `W_{j+1}(aU_{j+1}) − W_j(aU_j) = W_{j+1}(aU_{j+1} − Λ_{j+1}𝓡_{j+1} aU_j)`
  (`s.chain.2` and the linearity `readoutLinear_chain`, both fields are `C^{d N_w}`);
* `identityC1_sum`: `W_{M+k}(aU_{M+k}) − W_M(aU_M) = ∑_{j<k} W_{M+j+1}(aE_{M+j+1})`;
* `identityTheta`: the root value `W_{M+J_w}(aU_{M+J_w}) = aU_{M+J_w}` at the root component, which is
  periodic and equal to `θ(t)` almost everywhere (root clause of the reduction);
* `identityC1_tq_le`: `tq i ≤ tq (M+1)` for `M + 1 ≤ i ≤ M + J_w + 1`, so every `t ≥ a + τ` lies in the
  window of every level.

The degenerate cases are included: `k = 0` is the empty sum; `J_w = 1` has the single level `M + 1`.
-/

section
open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Construction.Preservation.FullLift
  AVRegularity.WeakEntryProofs.ReadoutLinear

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x} {s : WeakEntrySchedule g}
  {θ : ℝ → Vec 2 → ℝ}

theorem identityC1_Nw_le (x : WeakEntryData plan C) : A.Nw ≤ A.Lw := by
  have h := x.readout_order
  have hJ := A.Jw_pos
  rw [h]
  exact Nat.le_mul_of_pos_left _ hJ

/-- **One step of the telescoping sum.** -/
theorem identityC1_step (hlin : WeakReadoutLinearPlanOK plan) (red : WeakEntryReduced s θ)
    {j : ℕ} (hMj : x.M ≤ j) (hj : j < x.M + A.Jw) (hok : IdentityLiftOK red (j + 1)) {t : ℝ}
    (ht : t ∈ Set.Icc (s.tq (j + 1)) (x.a + A.T₀)) (y : Vec 2) :
    s.W (j + 1) t (identityAU red (j + 1) t) y - s.W j t (identityAU red j t) y =
      s.W (j + 1) t (fun v y' => identityAU red (j + 1) t v y' - identityLift red (j + 1) t v y')
        y := by
  have hMi : x.M < j + 1 := by omega
  have hi : j + 1 ≤ x.M + A.Jw := by omega
  have hstep : s.W j t (identityAU red j t) =
      s.W (j + 1) t (identityLift red (j + 1) t) :=
    s.chain.2 (j + 1) hMi hi t (identityAU red j t)
  have hA7 := identityA7_order_le x hMi
  have hd : (x.M + A.Jw - (j + 1)) * A.Nw ≤ A.Lw + 3 - A.Nw := by omega
  have h1 : ∀ v, ContDiff ℝ (((x.M + A.Jw - (j + 1)) * A.Nw : ℕ) : ℕ∞)
      (identityAU red (j + 1) t v) := fun v =>
    (identityAU_rep red (j + 1) t v).2.1.of_le
      (Nat.cast_le.mpr (show (x.M + A.Jw - (j + 1)) * A.Nw ≤ A.Lw + 3 by omega))
  have h2 : ∀ v, ContDiff ℝ (((x.M + A.Jw - (j + 1)) * A.Nw : ℕ) : ℕ∞)
      (identityLift red (j + 1) t v) := fun v =>
    (hok t ht v).1.of_le (by exact_mod_cast hd)
  have hl := readoutLinear_chain s hlin (x.M + A.Jw - (j + 1)) (j + 1) (by omega) (by omega) t
    (identityAU red (j + 1) t) (identityLift red (j + 1) t) (-1) h1 h2
  have h4 : (fun v y' => identityAU red (j + 1) t v y' + (-1 : ℝ) • identityLift red (j + 1) t v y')
      = fun v y' => identityAU red (j + 1) t v y' - identityLift red (j + 1) t v y' := by
    funext v y'
    simp [sub_eq_add_neg]
  rw [h4] at hl
  have h3 := congrFun hl y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, one_mul] at h3
  rw [h3, hstep]
  ring

/-- `tq i ≤ tq (M + 1)` for `M + 1 ≤ i ≤ M + J_w + 1`. -/
theorem identityC1_tq_le (s : WeakEntrySchedule g) {i : ℕ} (hlo : x.M + 1 ≤ i)
    (hhi : i ≤ x.M + A.Jw + 1) : s.tq i ≤ s.tq (x.M + 1) := by
  have hΛ : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
  refine quietTimes_antitone s.tq (x.M + 1) (x.M + A.Jw + 1) ?_ (x.M + 1) i le_rfl hlo hhi
  intro k hk1 hk2
  have hc := (s.quietMargins k (by omega) (by omega)).2.1
  have ht := Velocity.Jets.ocTauP_pos (α := x.D.α) (q := x.D.q) (Λ := x.D.Λ) (m := k) hΛ
  exact (le_add_of_nonneg_right ht.le).trans hc

/-- **The telescoping sum.** -/
theorem identityC1_sum (hlin : WeakReadoutLinearPlanOK plan) (red : WeakEntryReduced s θ)
    (hok : ∀ i, x.M < i → i ≤ x.M + A.Jw → IdentityLiftOK red i) {t : ℝ}
    (ht : ∀ i, x.M < i → i ≤ x.M + A.Jw → t ∈ Set.Icc (s.tq i) (x.a + A.T₀)) :
    ∀ k, k ≤ A.Jw → ∀ y : Vec 2,
      s.W (x.M + k) t (identityAU red (x.M + k) t) y - s.W x.M t (identityAU red x.M t) y =
        ∑ j ∈ Finset.range k, s.W (x.M + j + 1) t
          (fun v y' => identityAU red (x.M + j + 1) t v y' -
            identityLift red (x.M + j + 1) t v y') y := by
  intro k
  induction k with
  | zero => intro _ y; simp
  | succ k ih =>
    intro hk y
    rw [Finset.sum_range_succ, ← ih (by omega) y]
    have := identityC1_step hlin red (j := x.M + k) (by omega) (by omega)
      (hok (x.M + k + 1) (by omega) (by omega)) (ht (x.M + k + 1) (by omega) (by omega)) y
    rw [← this]
    have e : x.M + (k + 1) = x.M + k + 1 := (add_assoc _ _ _).symm
    rw [e]
    ring

/-- The root component lies in the top stage. -/
theorem identityC1_root_mem : (⟨0, []⟩ : Comp) ∈ (g.stage (x.M + A.Jw)).comps :=
  readoutLinear_root_mem (g := g)

/-- The root value of the representatives of the top level. -/
def identityTheta (red : WeakEntryReduced s θ) (t : ℝ) : Vec 2 → ℝ :=
  identityAU red (x.M + A.Jw) t ⟨⟨0, []⟩, identityC1_root_mem⟩

theorem identityTheta_eq_W (red : WeakEntryReduced s θ) (t : ℝ) (y : Vec 2) :
    identityTheta red t y = s.W (x.M + A.Jw) t (identityAU red (x.M + A.Jw) t) y :=
  (s.chain.1 t (identityAU red (x.M + A.Jw) t) y identityC1_root_mem).symm

theorem identityTheta_periodic (red : WeakEntryReduced s θ) (t : ℝ) :
    IsZ2Periodic (identityTheta red t) :=
  (identityAU_rep red (x.M + A.Jw) t _).2.2.1

/-- The root value is `θ(t)` almost everywhere on the window of the root level. -/
theorem identityTheta_ae (red : WeakEntryReduced s θ) {t : ℝ}
    (ht : t ∈ Set.Icc (s.tq (x.M + A.Jw + 1)) (x.a + A.T₀)) :
    identityTheta red t =ᵐ[volume.restrict AVenhance.unitCube] θ t := by
  have h1 := red.reduction.2.2.1 identityC1_root_mem t ht
  have h2 := classicalRep_value_ae _ _ (identityAU_rep red (x.M + A.Jw) t ⟨⟨0, []⟩,
    identityC1_root_mem⟩)
  exact h2.symm.trans h1
end

/-! **Identity C3: the last term, the readout of the paired difference.**

`W_M(aU_M) − W_M(aV ∘ ι) = W_M(aU_M − aV ∘ ι)` (linearity at `d = J_w`, both fields are `C^{L_w}`),
and this is the readout of the classical family `aU_M ∘ ι⁻¹ − aV` of the order `L_w + 3`, which
represents the truncation `z` (to the order `L_w + 5`) of `(U − V)(t)`. The readout bound
`weak_entry_readout_bound` (I5) and the pointwise bound of the truncated weighted norm by the strong
energy (`terminalReadoutEnergy`) give

`‖W_M(aU_M) − Ww aV‖_{C^s} ≤ |C_read| ε_{M+J_w}^{-(1+s)} |C_K| ε_M^{χ_w+σ_w L} ‖f‖₂`.

The degenerate cases are included: `U = V` gives `z = 0`; `f = 0` gives the bound `0`. -/

section
open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Construction.Preservation.FullLift
  AVRegularity.CycleComparison.Reconstruction AVRegularity.WeakEntryProofs.ReadoutLinear
  AVRegularity.Providers.WeakGen.Readout

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x} {s : WeakEntrySchedule g}
  {θ : ℝ → Vec 2 → ℝ}

/-- The difference of the readouts of the two classical families is the readout of the
classical family of the difference. -/
theorem identityC3_readout_sub (hlin : WeakReadoutLinearPlanOK plan) (red : WeakEntryReduced s θ)
    (t : ℝ) (aV : CompIn g.Gw.comps → Vec 2 → ℝ)
    (haV : ∀ v, ContDiff ℝ ((A.Lw + 3 : ℕ) : ℕ∞) (aV v)) (y : Vec 2) :
    s.W x.M t (identityAU red x.M t) y - weakEntryReadoutMap s t aV y =
      weakEntryReadoutMap s t
        (fun v' y' => identityAU red x.M t (g.relabel.symm v') y' - aV v' y') y := by
  have hJ : A.Jw * A.Nw ≤ A.Lw + 3 := by have := x.readout_order; omega
  have h1 : ∀ v, ContDiff ℝ (((A.Jw * A.Nw : ℕ)) : ℕ∞) (identityAU red x.M t v) := fun v =>
    (identityAU_rep red x.M t v).2.1.of_le (Nat.cast_le.mpr hJ)
  have h2 : ∀ v : CompIn (g.stage x.M).comps, ContDiff ℝ (((A.Jw * A.Nw : ℕ)) : ℕ∞)
      (fun y' => aV (g.relabel v) y') := fun v =>
    (haV (g.relabel v)).of_le (Nat.cast_le.mpr hJ)
  have hl := readoutLinear_chain s hlin A.Jw x.M rfl le_rfl t (identityAU red x.M t)
    (fun v y' => aV (g.relabel v) y') (-1) h1 h2
  have h4 : (fun v y' => identityAU red x.M t v y' + (-1 : ℝ) • aV (g.relabel v) y') =
      fun v y' => (fun v' y'' => identityAU red x.M t (g.relabel.symm v') y'' - aV v' y'')
        (g.relabel v) y' := by
    funext v y'
    simp [sub_eq_add_neg]
  rw [h4] at hl
  have h3 := congrFun hl y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, one_mul] at h3
  show _ - s.W x.M t (fun v y' => aV (g.relabel v) y') y = s.W x.M t _ y
  rw [h3]
  ring

/-- **The last term.** -/
theorem identityC3_last (hok : WeakReadoutBoundPlanOK weak_readout_base_size plan)
    (hlin : WeakReadoutLinearPlanOK plan) (law : BirthLaw) (hm : law.rootMass = g.rootM)
    (hr : law.rootReadout = g.rootR) (f : Vec 2 → ℝ) (red : WeakEntryReduced s θ)
    (p : WeakEntryPair (g := g)) (hp : WeakEntryPairBounds red law f p) {t : ℝ}
    (ht : t ∈ Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀)) (aV : CompIn g.Gw.comps → Vec 2 → ℝ)
    (haV : ∀ v, IsClassicalRep (p.V v t) (aV v) (A.Lw + 3)) :
    CsNormLe B.s
      (fun y => s.W x.M t (identityAU red x.M t) y - weakEntryReadoutMap s t aV y)
      (|plan.Cread R C| * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        (|plan.CK R C| * x.D.eps x.M ^ (weakChi B.α B.q A.η₀ + A.σw * R.L) *
          Real.sqrt (l2NormSq f))) := by
  have hLK : A.Lw + 5 ≤ R.Kw := R.field_order
  let U : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk R.Kw (ScalarH v.1.root) :=
    rerootFamily g.relabel (red.Ur x.M)
  let z : ∀ v : CompIn g.Gw.comps, TorusHk (A.Lw + 5) (ScalarH v.1.root) := fun v =>
    truncateTorusHk hLK (U v t - p.V v t)
  let az : CompIn g.Gw.comps → Vec 2 → ℝ := fun v' y' =>
    identityAU red x.M t (g.relabel.symm v') y' - aV v' y'
  have haz : ∀ v, IsClassicalRep (z v) (az v) (A.Lw + 3) := fun v =>
    classicalRep_truncate hLK (by omega) _ _
      (isClassicalRep_sub (identityAU_rep red x.M t (g.relabel.symm v)) (haV v))
  have hbound := weak_entry_readout_bound plan hok g s law hm hr t z az haz
  have hcont : ∀ v, ContDiff ℝ ((A.Lw + 3 : ℕ) : ℕ∞) (aV v) := fun v => (haV v).2.1
  have heq : (fun y => s.W x.M t (identityAU red x.M t) y - weakEntryReadoutMap s t aV y) =
      weakEntryReadoutMap s t az := funext (identityC3_readout_sub hlin red t aV hcont)
  rw [heq]
  -- the weighted norm of `z` is at most the strong energy of `U - V`
  have hE := hp.2.2.2.2
  have hen := EntryTerminal.Route.terminalReadoutEnergy g.Gw.comps R.Kw (A.Lw + 5) hLK
    (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) (s.tq (x.M + 1)) (x.a + A.T₀)
    (g.Gw.mass law) (fun v t => U v t - p.V v t) (fun v t => p.Uw v t - p.Vw v t) t ht
  have hen2 := hen.trans hE
  have hw0 : 0 ≤ weightedNorm (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law) (fun _ => 1) z :=
    Real.sqrt_nonneg _
  have hε : 0 ≤ x.D.eps x.M ^ (weakChi B.α B.q A.η₀ + A.σw * R.L) := by
    have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  have hrhs : 0 ≤ |plan.CK R C| * x.D.eps x.M ^ (weakChi B.α B.q A.η₀ + A.σw * R.L) *
      Real.sqrt (l2NormSq f) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hε) (Real.sqrt_nonneg _)
  have hwle : weightedNorm (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law) (fun _ => 1) z ≤
      |plan.CK R C| * x.D.eps x.M ^ (weakChi B.α B.q A.η₀ + A.σw * R.L) *
        Real.sqrt (l2NormSq f) := by
    rcases (ENNReal.ofReal_le_ofReal_iff' ).1 hen2 with h | h
    · refine h.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε)
        (Real.sqrt_nonneg _)
    · exact h.trans hrhs
  refine Applications.csNormLe_mono hbound ?_
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
  have hp0 : 0 ≤ x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) :=
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  have hK : plan.Cread R C * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) ≤
      |plan.Cread R C| * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hp0
  calc plan.Cread R C * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        weightedNorm (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law) (fun _ => 1) z
      ≤ |plan.Cread R C| * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        weightedNorm (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law) (fun _ => 1) z :=
        mul_le_mul_of_nonneg_right hK hw0
    _ ≤ _ := mul_le_mul_of_nonneg_left hwle (mul_nonneg (abs_nonneg _) hp0)
end

end AVRegularity.WeakEntryProofs.Identity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Identity

/-! **Identity B1: the readout of a classical field of the level `i`, one level.**

For a stage `i` with `M ≤ i ≤ M + J_w`, a family `z` of the order `n_i + 5` (with
`n_i = (M + J_w − i) N_w`) and classical representatives `az` of the order `n_i + 3`:
`‖s.W i t az‖_{C^s} ≤ 3 C_st^{M+J_w−i} C_B ε_{M+J_w}^{-(1+s)} ‖z‖_{c ε_i; π_i}`.

It is `weak_readout_bound_of_lift` read at the level `i`, with the lift from the level `i`
(`WeakLiftRepFromStatementAt`) and the profile bound as hypotheses (`IdentityLevelLift`,
`IdentityLevelProfile`); B2 supplies both.

The degenerate cases are included: `i = M + J_w` is the root value with `C_st^0 = 1` and order `3`;
`z = 0` gives `az = 0` and the bound `0`. -/

open AVRegularity WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs
  AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x}

/-- The represented lift from the level `m` on the entry data, with the step constant `Cst`. -/
def IdentityLevelLift (s : WeakEntrySchedule g) (Cst : ℝ) : Prop :=
  ∀ (m : ℕ), x.M ≤ m → m ≤ x.M + A.Jw →
  ∀ (t : ℝ) (a : CompIn (g.stage m).comps → Vec 2 → ℝ)
    (rT : Representation (CompSpace (g.stage m).comps)),
    IsRepresentationAt (x.D.eps m) (3 + (x.M + A.Jw - m) * A.Nw) rT →
    rT.value = compField (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun y v => a v y) →
    ∃ rW : Representation (CompSpace (g.stage (x.M + A.Jw)).comps),
      IsRepresentationAt (x.D.eps (x.M + A.Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
        (rW.value y) = s.W m t a y) ∧
      representedSize B.s 3 (x.D.eps (x.M + A.Jw)) rW ≤
        ENNReal.ofReal (Cst ^ (x.M + A.Jw - m)) *
          representedSize B.s (3 + (x.M + A.Jw - m) * A.Nw) (x.D.eps m) rT

/-- The profile bound at the stage `i`, order `n_i + 3`, radius `c`, constant `CB`. -/
def IdentityLevelProfile (x : WeakEntryData plan C) (g : WeakEntryStages x) (i : ℕ) (c CB : ℝ) :
    Prop :=
  ∀ (e : ℝ), 0 < e → e ≤ 1 →
    ∀ (z : ∀ v : CompIn (g.stage i).comps,
        TorusHk ((x.M + A.Jw - i) * A.Nw + 5) (ScalarH v.1.root))
      (az : CompIn (g.stage i).comps → Vec 2 → ℝ),
      (∀ v, IsClassicalRep (z v) (az v) ((x.M + A.Jw - i) * A.Nw + 3)) →
      profileNorm e ((x.M + A.Jw - i) * A.Nw + 3) B.s (compField
          (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
          (fun y v => az v y)) ≤
        ENNReal.ofReal (CB * e ^ (-(1 + B.s)) *
          weightedNorm (c * e) (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
            (fun _ => 1) z)

/-- **The readout of a classical field of the level `i`** (one level, B1 to B3). -/
theorem identityB1_level_bound (s : WeakEntrySchedule g) {Cst CB c : ℝ} (hCst : 0 ≤ Cst)
    (hCB : 0 ≤ CB) (hlift : IdentityLevelLift s Cst) {i : ℕ} (hMi : x.M ≤ i)
    (hi : i ≤ x.M + A.Jw) (hbase : IdentityLevelProfile x g i c CB) (t : ℝ)
    (z : ∀ v : CompIn (g.stage i).comps,
      TorusHk ((x.M + A.Jw - i) * A.Nw + 5) (ScalarH v.1.root))
    (az : CompIn (g.stage i).comps → Vec 2 → ℝ)
    (haz : ∀ v, IsClassicalRep (z v) (az v) ((x.M + A.Jw - i) * A.Nw + 3)) :
    CsNormLe B.s (s.W i t az)
      (3 * (Cst ^ (x.M + A.Jw - i) * CB) * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        weightedNorm (c * x.D.eps i)
          (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) z) := by
  have hΛ : 128 ≤ x.D.Λ := by rw [x.base_eq]; exact x.base128
  have hΛ1 : 1 ≤ x.D.Λ := (by norm_num : 1 ≤ 128).trans hΛ
  have hq : 1 < x.D.q := by rw [x.q_eq]; exact B.hq.1
  have heM : 0 < x.D.eps i := Construction.Stream.ocEpsilon_pos hΛ1
  have heM1 : x.D.eps i ≤ 1 := ocEpsilon_le_one hΛ1 _
  have heJ : 0 < x.D.eps (x.M + A.Jw) := Construction.Stream.ocEpsilon_pos hΛ1
  have hanti : x.D.eps (x.M + A.Jw) ≤ x.D.eps i := Applications.eps_antitone hq hΛ hi
  have hs1 : B.s < 1 := by have h1 := B.hs₁; have h2 := B.hα₀; linarith
  have hFc := EntryTerminal.Ingredients.compField_contDiff_periodic
    (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
    ((x.M + A.Jw - i) * A.Nw + 3) az (fun v => (haz v).2.1) (fun v => (haz v).2.2.1)
  have hrT : IsRepresentationAt (x.D.eps i) (3 + (x.M + A.Jw - i) * A.Nw)
      (⟨0, [(compField (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
        (fun y v => az v y), x.D.eps i)]⟩ : Representation (CompSpace (g.stage i).comps)) := by
    refine ⟨heM, heM1, contDiff_const, fun _ _ => rfl, fun p hp => ?_⟩
    obtain rfl := List.mem_singleton.mp hp
    rw [Nat.add_comm]
    exact ⟨hFc.1, hFc.2, le_rfl, heM1⟩
  have hval : (⟨0, [(compField (fun v : CompIn (g.stage i).comps =>
      weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun y v => az v y), x.D.eps i)]⟩ :
      Representation (CompSpace (g.stage i).comps)).value =
      compField (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
        (fun y v => az v y) := by
    funext y
    simp only [Representation.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Pi.zero_apply, zero_add, add_zero]
  obtain ⟨rW, hrW, hread, hsize⟩ := hlift i hMi hi t az _ hrT hval
  rw [Nat.add_comm 3, representedSize_single_profile] at hsize
  have hW := hbase (x.D.eps i) heM heM1 z az haz
  have hWn0 : 0 ≤ weightedNorm (c * x.D.eps i)
      (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) z :=
    Real.sqrt_nonneg _
  have hpowM : 0 ≤ x.D.eps i ^ (-(1 + B.s)) := Real.rpow_nonneg heM.le _
  have hCs : 0 ≤ Cst ^ (x.M + A.Jw - i) := pow_nonneg hCst _
  have hA0 : 0 ≤ Cst ^ (x.M + A.Jw - i) * (CB * x.D.eps i ^ (-(1 + B.s)) *
      weightedNorm (c * x.D.eps i)
        (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) z) :=
    mul_nonneg hCs (mul_nonneg (mul_nonneg hCB hpowM) hWn0)
  have hsizeA : representedSize B.s 3 (x.D.eps (x.M + A.Jw)) rW ≤
      ENNReal.ofReal (Cst ^ (x.M + A.Jw - i) * (CB * x.D.eps i ^ (-(1 + B.s)) *
        weightedNorm (c * x.D.eps i)
          (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
          (fun _ => 1) z)) := by
    refine hsize.trans ?_
    rw [ENNReal.ofReal_mul hCs]
    exact mul_le_mul' le_rfl hW
  have hroot : (g.stage (x.M + A.Jw)).comps = {⟨0, []⟩} := g.construction.2.1.2.1
  have hcs := Finite.Assembly.scalar_rep_readout B.s B.hs₀ hs1 (x.D.eps (x.M + A.Jw)) _ hA0 rW hrW
    (compReadoutCLM (fun v : CompIn (g.stage (x.M + A.Jw)).comps =>
      weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1))
    (Finite.Assembly.weak_root_readout_norm x.D A.Nw A.Jw A.η₀ _ hroot) hsizeA
  have hfun : (fun y => compReadoutCLM (fun v : CompIn (g.stage (x.M + A.Jw)).comps =>
      weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) (rW.value y)) = s.W i t az := by
    funext y
    exact hread y
  rw [hfun] at hcs
  refine Applications.csNormLe_mono hcs ?_
  have hpow : x.D.eps i ^ (-(1 + B.s)) ≤ x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) :=
    Real.rpow_le_rpow_of_nonpos heJ hanti (by have h := B.hs₀; linarith)
  have hCC : 0 ≤ Cst ^ (x.M + A.Jw - i) * CB := mul_nonneg hCs hCB
  have hstep : Cst ^ (x.M + A.Jw - i) * CB * x.D.eps i ^ (-(1 + B.s)) *
        weightedNorm (c * x.D.eps i)
          (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) z ≤
      Cst ^ (x.M + A.Jw - i) * CB * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        weightedNorm (c * x.D.eps i)
          (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCC) hWn0
  linarith

end AVRegularity.WeakEntryProofs.Identity
end
end
end
