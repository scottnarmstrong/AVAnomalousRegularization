-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Reduction.QuietTraceHighPassage
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.Proofs.WeakGen.Comparison.RowsHigh

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **Core of the passage energy** (`weakPassage_core_energy`), over the raw data
`WeakRawSetting`.

For a coupled solution on `[a, b]` of the reduction system of stage `L` (`M ≤ L < M + J_w`) at
the reserves `weakReductionReserve R m` (`m ≤ m_max(R)`) with datum `f` and zero forcing, at
radius `ρ ε_L` with `0 < ρ ≤ 1`:
```
∑_v π_v⁻¹ |u_v(t)|²_{ρε_L} + (κ_M/2) ∫_{[a,b]} ∑_v π_v⁻¹ |∇w_v|²_{ρε_L}
  ≤ C_pass ∑_v π_v⁻¹ |f_v|²_{ρε_L},     C_pass = weakRawPassageConst ρ R.
```
The coefficient data `Rd`, the drift data `hd` and the measurability of the coefficients are
hypotheses, since they come from different places in the entry and passage worlds. All the floors
are explicit inequalities (`weakEntryPassageCoeffFloor R ≤ M`, `weakQuietStoredFloor A ≤ M`). -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  Construction.Preservation.Ledger CycleJointProofs.PathReduction CoupledEnergy.Variational

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- **The energy of one passage with data, over raw data.** -/
theorem weakPassage_core_energy (S : WeakRawSetting R)
    (hfloor : weakEntryPassageCoeffFloor R ≤ S.M) (hstored : weakQuietStoredFloor A ≤ S.M)
    (L : ℕ) (hL : S.M ≤ L) (hLJ : L < S.M + A.Jw) (a b rad : ℝ) (hab : a ≤ b)
    (hrad : 0 < rad) (hrad1 : rad ≤ 1) (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (hsmooth : ∀ v u (γ : (S.stage L).fam.Γ v u) d, 2 ≤ d → ∀ k ≤ weakEntryKmax R, ∀ t,
      ContDiff ℝ (k : ℕ) ((S.stage L).physCoeff v u γ d t))
    {Ac : ∀ v u, (d : admissibleOrders
        (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) v u) →
        ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => ScalarH u.1.root) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)}
    (hA : ∀ v u d, Ac v u d = fun t y => ∑ γ : (S.stage L).fam.Γ v u,
      (S.stage L).physCoeff v u γ d.1 t y)
    (Rd : TorusCoefficientData (rad * S.D.eps L)
      (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) a b Ac)
    (hd : TorusDriftData (S.D.κ S.M) (rad * S.D.eps L) a b (streamVel (S.D.Φ L))
      (weakEntryKmax R))
    (hA_meas : ∀ v u d, Measurable fun p : Set.Icc a b × Vec 2 => Ac v u d p.1 p.2)
    {f : ∀ v : CompIn (S.stage L).comps, TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root)}
    {u : ∀ v : CompIn (S.stage L).comps, ℝ →
      TorusHk (weakReductionReserve R m v.1) (ScalarH v.1.root)}
    {w : ∀ v : CompIn (S.stage L).comps, ℝ →
      TorusHk (weakReductionReserve R m v.1 + 1) (ScalarH v.1.root)}
    (hs : IsCoupledWeakSolutionTorus (S.D.κ S.M) a b (streamVel (S.D.Φ L)) (1 + A.Jw * A.Nw)
      (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) Ac f
      (fun _ _ => 0) (fun _ _ => 0) u w)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∑ v, (weakMass S.D A.Nw A.Jw A.η₀ v.1)⁻¹ * factorialNormSq (rad * S.D.eps L) (u v t).val +
      S.D.κ S.M / 2 * ∫ s in Set.Icc a b, ∑ v, (weakMass S.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        gradFactorialNormSq (rad * S.D.eps L) (w v s).val ≤
      weakRawPassageConst rad R * ∑ v, (weakMass S.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        factorialNormSq (rad * S.D.eps L) (f v).val := by
  classical
  have hπ := fun v : CompIn (S.stage L).comps => S.mass_pos v.1
  have hX0 : ∀ v : CompIn (S.stage L).comps, 0 ≤ rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f
      (rowForcingFlux Rd (fun _ _ => 0) w) (fun _ _ => 0) v :=
    fun v => rowDataBound_nonneg _ _ _ _ S.kappa_pos _ _ _ v
  have hrec := weakPassage_core_row_recursion S hfloor hstored L hL hLJ a b rad hab hrad hrad1 m hm
    hsmooth hA Rd hd hA_meas hs
  have hsum := sum_unrolled_le (S.stage L) A.Nw A.Jw A.η₀
    (weakRaw_storedTotal_le S hstored L hL hLJ.le)
    (fun v : CompIn (S.stage L).comps => weakMass S.D A.Nw A.Jw A.η₀ v.1)
    (fun v => rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f
      (rowForcingFlux Rd (fun _ _ => 0) w) (fun _ _ => 0) v)
    (fun v => 2 * factorialNormSq (rad * S.D.eps L) (f v).val) hπ hX0
    (fun v => mul_nonneg (by norm_num) (factorialNormSq_nonneg _ _))
    (32 * 1 * weakRawEdgeConst rad R ^ 2) (by have := weakRawEdgeConst_nonneg hrad.le R; positivity)
    hrec (A.Jw * A.Rw)
    ⟨fun π' => absurd (weakConstruction_path_length_bound S.P _ S.M A.Jw 0 _ S.stage
      S.construction L hL hLJ.le _ π') (by simp)⟩
  have hgi : ∀ v : CompIn (S.stage L).comps,
      Integrable (fun s => gradFactorialNormSq (rad * S.D.eps L) (w v s).val)
        (volume.restrict (Set.Icc a b)) := fun v =>
    CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hs.2.1 v)
  have hint : ∫ s in Set.Icc a b, ∑ v : CompIn (S.stage L).comps,
        (weakMass S.D A.Nw A.Jw A.η₀ v.1)⁻¹ * gradFactorialNormSq (rad * S.D.eps L) (w v s).val =
      ∑ v : CompIn (S.stage L).comps, (weakMass S.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        ∫ s in Set.Icc a b, gradFactorialNormSq (rad * S.D.eps L) (w v s).val := by
    rw [integral_finsetSum _ fun v _ => (hgi v).const_mul _]
    exact Finset.sum_congr rfl fun v _ => integral_const_mul _ _
  have hlhs : ∑ v, (weakMass S.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        factorialNormSq (rad * S.D.eps L) (u v t).val +
      S.D.κ S.M / 2 * ∫ s in Set.Icc a b, ∑ v, (weakMass S.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        gradFactorialNormSq (rad * S.D.eps L) (w v s).val ≤
      ∑ v : CompIn (S.stage L).comps, rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f
        (rowForcingFlux Rd (fun _ _ => 0) w) (fun _ _ => 0) v /
          weakMass S.D A.Nw A.Jw A.η₀ v.1 := by
    rw [hint, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have := weakPassage_core_row_energy S L a b rad m hm Rd hd hA_meas hs v t ht
    calc _ = (weakMass S.D A.Nw A.Jw A.η₀ v.1)⁻¹ * (factorialNormSq (rad * S.D.eps L) (u v t).val +
          S.D.κ S.M / 2 * ∫ s in Set.Icc a b,
            gradFactorialNormSq (rad * S.D.eps L) (w v s).val) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (inv_nonneg.2 (hπ v).le)
      _ = _ := (div_eq_inv_mul _ _).symm
  have hq : ∑ v : CompIn (S.stage L).comps, 2 * factorialNormSq (rad * S.D.eps L) (f v).val /
      weakMass S.D A.Nw A.Jw A.η₀ v.1 = 2 * ∑ v : CompIn (S.stage L).comps,
        (weakMass S.D A.Nw A.Jw A.η₀ v.1)⁻¹ * factorialNormSq (rad * S.D.eps L) (f v).val := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  refine hlhs.trans (hsum.trans (le_of_eq ?_))
  rw [hq]
  unfold weakRawPassageConst
  simp only [mul_one]
  ring

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! Quiet trace assembly: the lifted reduction on the same clock, and restriction
of its factorial mass norm to the old components. The two quiet trace layers are discharged
from the single passage-plan witness of the numerical plan condition. -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
  {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
  {C : WeakEntryAllocation R (plan.radius R)}

/-- The passage instance uses precisely the entry data and construction.
Only the requested Sobolev order is raised. -/
def weakEntryHighQuietCase (pp : WeakPassagePlan) (m : ℕ)
    (hb : pp.baseFloor B ≤ plan.baseFloor B)
    (hm : pp.momentFloor A ≤ plan.momentFloor A)
    (hl : ∀ j, pp.levelFloor (weakEntryLiftRequest R m) j ≤ plan.levelFloor R C j)
    (x : WeakEntryData plan C) (g : WeakEntryStages x) :
    WeakPassageInstance pp (weakEntryLiftRequest R m) :=
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

/-- Lift the native reduction to the maximal finite reserve without changing
its clock or order-zero trajectory. This is shared lemma (H), not an estimate. -/
def WeakEntryHighQuietLiftStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ (pp : WeakPassagePlan) {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (C : WeakEntryAllocation R (plan.radius R)) (m : ℕ)
    (hb : pp.baseFloor B ≤ plan.baseFloor B)
    (hm : pp.momentFloor A ≤ plan.momentFloor A)
    (hl : ∀ j, pp.levelFloor (weakEntryLiftRequest R m) j ≤ plan.levelFloor R C j)
    (x : WeakEntryData plan C) (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
    ∀ r : WeakEntryReduced s θ,
    ∃ rr : WeakPassageRun (weakEntryHighQuietCase pp m hb hm hl x g),
      rr.tq = s.tq ∧
      ∀ j, x.M ≤ j → j ≤ x.M + A.Jw → ∀ v : CompIn (g.stage j).comps,
        ∀ t ∈ Set.Icc (s.tq (j + 1)) (x.a + A.T₀),
          truncateTorusHk (Nat.zero_le _) (rr.Ur j v t) =
            truncateTorusHk (Nat.zero_le R.Kw) (r.Ur j v t)

/-- The quiet trace bound from the higher-reduction adapter and the passage-generic
trace theorem, with both layers invoked on the same priced witness. -/
theorem weak_entry_quiet_trace_high_of_ingredients
    (hok : WeakEntryQuietTraceHighPlanOK plan)
    (hlift : WeakEntryHighQuietLiftStatement plan) :
    WeakEntryQuietTraceHighStatement plan := by
  obtain ⟨pp, prices, hrows, hcoeff, hscalar, hprice, hfit⟩ := hok
  let p := weakQuietCoefficientPlan pp
  intro B A R C m hm
  let Rp := weakEntryLiftRequest R m
  let cQ := max 1 (p.traceC Rp)
  refine ⟨cQ ^ 2, sq_nonneg _, ?_⟩
  intro x g s f θ hθ r Uhi Whi hhi i hi hit
  obtain ⟨hb, hmoment, hl, hradius⟩ := hfit R C m hm
  obtain ⟨rr, hclock, hagree⟩ := hlift p R C m hb hmoment hl x g s f θ hθ r
  let c := weakEntryHighQuietCase p m hb hmoment hl x g
  have htime (t : ℝ) (ht : t ∈ Set.Icc (s.tq (i + 1)) (s.tq i)) :
      t ∈ Set.Icc (s.tq (i + 1)) (x.a + A.T₀) :=
    ⟨ht.1, ht.2.trans (weakEntrySchedule_tq_le s i hi hit)⟩
  have hzero (v : CompIn (g.stage i).comps) (t : ℝ)
      (ht : t ∈ Set.Icc (s.tq (i + 1)) (s.tq i)) :
      truncateTorusHk (Nat.zero_le _) (Uhi i v t) =
        truncateTorusHk (Nat.zero_le Rp.Kw) (rr.Ur i v t) := by
    have hu := congrArg (truncateTorusHk (Nat.zero_le R.Kw))
      (hhi.2.2.1 i hi.le hit v t (htime t ht))
    exact hu.trans (hagree i hi.le hit v t (htime t ht)).symm
  have hpass := weak_passage_quiet_trace_high pp prices hrows hcoeff hscalar hprice
    c rr i hi hit (weakReductionReserve R m) (fun v => weakReductionReserve_le R m v)
    (fun v t => Uhi i v t) (by
      intro t ht v
      rw [hclock] at ht
      exact hzero v t ht)
    (plan.radius R) (weak_entry_radius_spec (plan.radiusBudget R)).1.le hradius
  rw [hclock] at hpass
  exact hpass

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Reduction

/-! The shared higher-order lemma at the maximal finite reserve supplies the same-clock
passage run required by the quiet trace bound. No high-order initial datum is imposed. -/

open WeakEntryProofs WeakEntryProofs.Assembly

private theorem weakEntry_high_reduction_at {plan : WeakEntryGluePlan}
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    {g : WeakEntryStages x} (hcommon : WeakEntryCommonOK plan) (s : WeakEntrySchedule g)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (r : WeakEntryReduced s θ) (offset K : ℕ) (hK : K = R.Kw + offset) :
    ∃ (Ur : (i : ℕ) → ∀ v : CompIn (g.stage i).comps, ℝ → TorusHk K (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (g.stage i).comps, ℝ → TorusHk (K + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (g.stage i).fam.Γ v u), ℝ →
        TorusHk (K + x.Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction x.P A.φ₀ A.hφ₀ R.nW x.M A.Jw K 0 x.a (x.a + A.T₀)
        θ g.stage s.tq Ur Urw Urk ∧
      ∀ j, x.M ≤ j → j ≤ x.M + A.Jw → ∀ v : CompIn (g.stage j).comps,
        ∀ t ∈ Set.Icc (s.tq (j + 1)) (x.a + A.T₀),
          truncateTorusHk (Nat.zero_le K) (Ur j v t) =
            truncateTorusHk (Nat.zero_le R.Kw) (r.Ur j v t) := by
  subst K
  obtain ⟨Ur, Urw, Urk, hred, hv, _hw⟩ :=
    weakReduction_higher_reduction hcommon s f θ hθ r offset
  refine ⟨Ur, Urw, Urk, hred, ?_⟩
  intro j hj hj' v t ht
  exact congrArg (truncateTorusHk (Nat.zero_le R.Kw)) (hv j hj hj' v t ht)

/-- The higher reduction has the same order-zero values on every window. -/
theorem weak_entry_high_quiet_lift {plan : WeakEntryGluePlan}
    (hcommon : WeakEntryCommonOK plan) : WeakEntryHighQuietLiftStatement plan := by
  intro pp B A R C m hb hm hl x g s f θ hθ r
  let Rp := weakEntryLiftRequest R m
  obtain ⟨Ur, Urw, Urk, hred, hv⟩ := weakEntry_high_reduction_at hcommon s f θ hθ r
    (m + A.Jw * A.Rw * (A.Jw * A.Nw - 1)) Rp.Kw
    (by dsimp [Rp, weakEntryLiftRequest]; omega)
  let rr : WeakPassageRun (weakEntryHighQuietCase pp m hb hm hl x g) :=
    { a := x.a
      f := f
      θ := θ
      scalar := hθ
      tq := s.tq
      Ur := Ur
      Urw := Urw
      Urk := Urk
      reduction := hred }
  exact ⟨rr, rfl, hv⟩

/-- The quiet trace bound at every descending reserve, with all analytic and finite adapters
proved. The prices and thresholds precede the data and the ambient cap. -/
theorem weak_entry_quiet_trace_high {plan : WeakEntryGluePlan}
    (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryQuietTraceHighPlanOK plan) :
    WeakEntryQuietTraceHighStatement plan :=
  @weak_entry_quiet_trace_high_of_ingredients plan hok
    (weak_entry_high_quiet_lift hcommon)

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The drift data of the passages of the weak entry** (entry case).

The stream velocity of the level `L ≥ M` has drift data (`TorusDriftData`) at the radius
`ρ ε_L` with the diffusivity `κ_M`:
* `stream_torusDriftData_strain`: from the two strain inequalities `1024 r/ε ≤ 1/2` and
  `C ocA · 1024 r² ≤ ν/8` (the shape that the paired solve proves at the terminal level);
* the level `L = M`: the strain inequalities of the paired solve (`weakPaired_drift`), under
  `WeakEntryPairedPlanOK`;
* the levels `L > M`: Péclet smallness (`weak_peclet_eventually_small`) above the drift floor,
  as in `weakComparison_rowDrift`. -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs Comparison

/-- **Drift data of the actual stream velocity** from the strain inequalities. -/
theorem stream_torusDriftData_strain (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (hm : 1 ≤ m) {ν : ℝ} (t₀ t₁ : ℝ) (Kmax : ℕ)
    (ρ : ℝ) (h1 : 1024 * ρ / ocEpsilon q Λ m ≤ 1 / 2)
    (h2 : Construction.Preservation.Buffer.actualDriftJetConstant * ocA α q Λ m * 1024 * ρ ^ 2 ≤
      ν / 8) :
    TorusDriftData ν ρ t₀ t₁ (streamVel (Φ m)) Kmax := by
  obtain ⟨hsm, hper, hdiv, hbdd, hmeas⟩ :=
    Construction.Preservation.Buffer.stream_kernel_drift_data
      (Velocity.streamSeq_admissible hζ hΛ hΦ m) t₀ t₁
  have he : 0 < ocEpsilon q Λ m := (Scales.epsilon_basic hq.1 hΛ).1
  have ha : 0 ≤ Construction.Preservation.Buffer.actualDriftJetConstant * ocA α q Λ m :=
    mul_nonneg Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
      (Real.rpow_pos_of_pos he _).le
  exact ⟨hbdd, hmeas, hsm, hdiv, hper, _, 1024, ocEpsilon q Λ m, ha, by norm_num, he,
    fun l hl _ t _ x => Construction.Preservation.Buffer.actual_stream_drift_arrays α s hα₀ hα₁
      hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm t l hl x, by simpa only [mul_comm] using h1, h2⟩

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

/-- **The drift data at the levels above the terminal level**, from Péclet smallness. -/
theorem weakEntry_drift_above (x : WeakEntryData plan C)
    (hdrift : weakComparisonDriftFloor A ≤ x.M)
    (hrad : plan.radius R ≤ 1 / 2048) (L : ℕ) (hL : x.M < L)
    (t₀ t₁ : ℝ) (Kmax : ℕ) :
    TorusDriftData (x.D.κ x.M) (plan.radius R * x.D.eps L) t₀ t₁ (streamVel (x.D.Φ L)) Kmax := by
  have hΛ : 128 ≤ A.Λ := x.base128
  have hC0 := Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
  set C := Construction.Preservation.Buffer.actualDriftJetConstant with hCdef
  have hθ : 0 < 1 / (8192 * (C + 1)) := by positivity
  unfold weakComparisonDriftFloor at hdrift
  rw [dite_eq_left hΛ] at hdrift
  have hspec := Classical.choose_spec (weak_peclet_eventually_small B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
    A.Λ hΛ (1 / (8192 * (C + 1))) hθ)
  have hP := hspec x.M hdrift (x.D.κ x.M) x.band.1 L hL
  have hε : 0 < ocEpsilon B.q A.Λ L := (Scales.epsilon_basic B.hq.1 hΛ).1
  have hε1 : ocEpsilon B.q A.Λ L ≤ 1 := (Scales.epsilon_basic B.hq.1 hΛ).2.1
  have hband := x.band.1
  have hκ : 0 < x.D.κ x.M := lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos
    (Scales.epsilon_basic (m := x.M) B.hq.1 hΛ).1 _) two_pos) hband.1
  have heps : x.D.eps L = ocEpsilon B.q A.Λ L := by
    rw [OCData.eps, x.q_eq, x.base_eq]
  have hr := (weak_entry_radius_spec (plan.radiusBudget R)).1
  rw [heps]
  refine stream_torusDriftData_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ A.Λ hΛ x.D.Φ
    x.streams L (by omega) t₀ t₁ Kmax _ ?_ ?_
  · rw [le_div_iff₀ (by norm_num)]
    nlinarith
  · refine drift_scale_le hε hε1 hr.le (by linarith [(weak_entry_radius_spec
      (plan.radiusBudget R)).2.1]) hC0 B.hα₀ (by linarith [B.hα₁]) ?_
    rw [div_le_iff₀ hκ] at hP
    rw [le_div_iff₀ (by positivity)]
    calc ocEpsilon B.q A.Λ L ^ (1 + B.α) * (8192 * (C + 1))
        ≤ 1 / (8192 * (C + 1)) * x.D.κ x.M * (8192 * (C + 1)) :=
          mul_le_mul_of_nonneg_right hP (by positivity)
      _ = x.D.κ x.M := by field_simp

/-- **The drift data of the passage at the level `L ≥ M`** at the radius `ρ ε_L`. -/
theorem weakEntry_passage_drift (hcommon : WeakEntryCommonOK plan)
    (hpair : WeakEntryPairedPlanOK plan) (x : WeakEntryData plan C)
    (hdrift : weakComparisonDriftFloor A ≤ x.M) (L : ℕ) (hL : x.M ≤ L) (t₀ t₁ : ℝ)
    (Kmax : ℕ) :
    TorusDriftData (x.D.κ x.M) (plan.radius R * x.D.eps L) t₀ t₁ (streamVel (x.D.Φ L)) Kmax := by
  rcases hL.eq_or_lt with h | h
  · subst h
    obtain ⟨h1, h2⟩ := weakPaired_drift hpair x
    rw [weakPaired_radius_eq] at h1 h2
    have hM2 := weakEntryData_M_ge_two hcommon x
    rw [weakPaired_eps_eq]
    exact stream_torusDriftData_strain B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ A.Λ
      x.base128 x.D.Φ x.streams x.M (by omega) t₀ t₁ Kmax _ h1 h2
  · exact weakEntry_drift_above x hdrift (hpair.1 R) L h t₀ t₁ Kmax

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The energy of one passage with data** (`weakEntryPassageEnergy`).

`WeakEntryPassageEnergyStatement plan` under the common plan and `WeakEntryPassageEnergyPlanOK
plan`: the corollary, over the entry data `x`, `g`, `s`, of the core `weakPassage_core_energy`
(raw data `WeakRawSetting`), with `C_pass = weakRawPassageConst (plan.radius R) R`. The entry data
supplies the raw setting, the coefficient data (`weakStageCoeff_gate`), the drift data
(`weakEntry_passage_drift`: the paired solve's strain at the last passage, Péclet smallness above)
and the passage `WeakReductionPassage`; the diffusivity `kap` of the level `i - 1` is `κ_M`. -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  CycleJointProofs.PathReduction CoupledEnergy.Variational

/-- Real energy inequality to the extended-real one. -/
theorem ofReal_energy_le {a c ν : ℝ} {g : ℝ → ℝ} {μ : Measure ℝ} (hν : 0 ≤ ν)
    (hg : Integrable g μ) (hg0 : ∀ τ, 0 ≤ g τ) (ha : 0 ≤ a) (h : a + ν * ∫ τ, g τ ∂μ ≤ c) :
    ENNReal.ofReal a + ENNReal.ofReal ν * ∫⁻ τ, ENNReal.ofReal (g τ) ∂μ ≤ ENNReal.ofReal c := by
  rw [← ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hg0),
    ← ENNReal.ofReal_mul hν, ← ENNReal.ofReal_add ha (mul_nonneg hν (integral_nonneg hg0))]
  exact ENNReal.ofReal_le_ofReal h

variable {plan : WeakEntryGluePlan}

/-- **The energy of one passage** (`WeakEntryPassageEnergyStatement`), under the common plan and the plan condition of
the passage energy. -/
theorem weakEntryPassageEnergy (hcommon : WeakEntryCommonOK plan)
    (hok : WeakEntryPassageEnergyPlanOK plan) : WeakEntryPassageEnergyStatement plan := by
  intro B A R C m hm
  refine ⟨weakRawPassageConst (plan.radius R) R, weakRawPassageConst_nonneg _ _, ?_⟩
  intro x g s Uhi Whi i hMi hi hpass t ht
  classical
  obtain ⟨hpair, hrad2048, hfl⟩ := hok
  obtain ⟨hcf, hdf, hsf⟩ := hfl R C x.j₀
  have hlevel := x.level_ge
  set S := weakEntryRawSetting g with hS
  have hL : x.M ≤ i - 1 := by omega
  have hLJ : i - 1 < x.M + A.Jw := by omega
  have hab := weakEntrySchedule_tq_le s i hMi hi
  have hradspec := weak_entry_radius_spec (plan.radiusBudget R)
  have hrad1 : plan.radius R ≤ 1 := (hrad2048 R).trans (by norm_num)
  have hfloor : weakEntryPassageCoeffFloor R ≤ S.M := hcf.trans hlevel
  have hstored : weakQuietStoredFloor A ≤ S.M := hsf.trans hlevel
  have hdrift : weakComparisonDriftFloor A ≤ x.M := hdf.trans hlevel
  have hlev : (g.stage (i - 1)).level = i - 1 :=
    EntryWeakProofs.weakConstruction_level x.P _ x.M A.Jw 0 _ g.stage g.construction (i - 1)
      hL hLJ.le
  have hkap : x.D.kap (g.stage (i - 1)).level = x.D.κ x.M := by
    rw [hlev]; exact S.kap_eq _ hL
  have hΛ' : 128 ≤ x.D.Λ := by rw [x.base_eq]; exact x.base128
  have hq' : 1 < x.D.q := by rw [x.q_eq]; exact B.hq.1
  have hεL : 0 < x.D.eps (i - 1) := S.eps_pos _
  have hρpos : 0 < plan.radius R * x.D.eps (i - 1) := mul_pos hradspec.1 hεL
  have hρe : plan.radius R * x.D.eps (i - 1) ≤ x.D.eps (i - 1 - 1) :=
    (mul_le_of_le_one_left hεL.le hrad1).trans
      (EntryScales.epsilon_antitone hq' hΛ' (Nat.sub_le _ _))
  have hgate := fun v u d => weakStageCoeff_gate S (weakEntryRawSetting_coeffRegular hcommon g) m (i - 1) hL hLJ (s.tq i)
    (x.a + A.T₀) _ hρpos hρe v u d
  have Rd : TorusCoefficientData (plan.radius R * x.D.eps (i - 1))
      (fun v : CompIn (g.stage (i - 1)).comps => weakReductionReserve R m v.1)
      (1 + A.Jw * A.Nw) (s.tq i) (x.a + A.T₀) (weakReductionCoeff g m (i - 1)) :=
    { radius_pos := hρpos
      finite := fun v u d => (hgate v u d).2.2.2
      smooth := fun t ht v u d => (hgate v u d).2.1 t ht
      periodic := fun t ht v u d => (hgate v u d).2.2.1 t ht }
  have hd := weakEntry_passage_drift hcommon hpair x hdrift (i - 1) hL (s.tq i) (x.a + A.T₀)
    (weakEntryKmax R)
  have hs : IsCoupledWeakSolutionTorus (S.D.κ S.M) (s.tq i) (x.a + A.T₀)
      (streamVel (S.D.Φ (i - 1))) (1 + A.Jw * A.Nw)
      (fun v : CompIn (S.stage (i - 1)).comps => weakReductionReserve R m v.1)
      (weakReductionCoeff g m (i - 1)) (weakReductionTrace g m i (Uhi i) (s.tq i))
      (fun _ _ => 0) (fun _ _ => 0) (Uhi (i - 1)) (Whi (i - 1)) := by
    have h := hpass
    dsimp only [WeakReductionPassage, WeakStagePassage, weakEntryRawSetting,
      weakEntryRawClock] at h
    rw [hkap, hlev] at h
    exact h
  have hcore := weakPassage_core_energy S hfloor hstored (i - 1) hL hLJ (s.tq i) (x.a + A.T₀)
    (plan.radius R) hab hradspec.1 hrad1 m hm
    (fun v u γ d hd' k _ t' => (weakEntry_physCoeff_allOrder hcommon g (i - 1) hL hLJ v u γ k d
      (s.tq i) (x.a + A.T₀)).2.1 t')
    (fun v u d => rfl) Rd hd (fun v u d => (hgate v u d).1) hs t ht
  have hgi : ∀ v : CompIn (g.stage (i - 1)).comps,
      Integrable (fun τ => gradFactorialNormSq (plan.radius R * x.D.eps (i - 1))
        (Whi (i - 1) v τ).val) (volume.restrict (Set.Icc (s.tq i) (x.a + A.T₀))) := fun v =>
    CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hs.2.1 v)
  have hπ := fun v : CompIn (g.stage (i - 1)).comps => S.mass_pos v.1
  rw [hkap]
  simp only [massNormSq, massGradNormSq]
  exact ofReal_energy_le (by have := S.kappa_pos; positivity)
    (integrable_finsetSum _ fun v _ => (hgi v).const_mul _)
    (fun τ => Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _))
    (Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
      (factorialNormSq_nonneg _ _)) hcore

end AVRegularity.Providers.WeakGen.Reduction
end
