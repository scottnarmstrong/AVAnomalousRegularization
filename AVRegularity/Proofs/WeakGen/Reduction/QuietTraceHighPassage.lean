-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.QuietScalarPathPrice
import AVRegularity.CycleComparison.Error.WeakSolution
public import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder
import AVRegularity.Proofs.WeakGen.Comparison.RowsHigh
import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.EntryWeakAssembly.MassRecursion
import AVRegularity.EntryWeakAssembly.QuietSmoothingPlan

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The raw energy of the weak entry, as three bounded statements**.

`WeakEntryRawEnergyStatement` is split into
* `WeakEntryPassageEnergyStatement`: the energy of one passage of the coupled families of
  `weakReduction_higher` with data (the trace of the next stage), `C_pass` chosen before the data;
* `WeakEntryQuietTraceHighStatement`: the factorial trace of the next stage at the reserves,
  bounded by the order-zero norm on the preceding quiet window, `C_q` chosen before the data;
* the iteration `weak_entry_raw_energy_of_ingredients`, which assembles them.

All constants (`C_pass`, `C_q`) depend on the request `R`, the
allocation `C` and the order offset `m ≤ m_max(R) = J_w N_w + L`; none depends on `D_m`, the
stage, the data or the family size. The orders are at most
`K_max(R) = K_w + m_max(R) + J_w R_w (J_w N_w - 1)`.

* `WeakHigherFamilies`: the conclusion of the shared higher-order lemma `weakReduction_higher`, as a `Prop`
  on the families.
* `weakEntryRawConst`: `C_raw(R, C, m) = √(B^{J_w} + 2) · √2 · (√(C_pass C_q))^{J_w}` from the chosen
  constants (`B` the stored word budget; see the docstring).
* `WeakEntryRawEnergyPlanOK`: `3 C_raw(R, C, 0) ≤ CK`, plus the two plan conditions (lower bounds
  on the level floor, `CK`, an upper bound on the radius, and the passage-plan floors at the lifted
  request).

The degenerate cases are included:
- `f = 0`: `θ = 0`, every family is `0`, every bound is `0`.
- `J_w = 1`: one passage; `C_raw = √(B + 2) · √(C_pass C_q) · √2`.
- A stage without edges: each row is a forced scalar row, `C_pass = 2` suffices.
- `m = 0`: the reserves are `K_w + d(v) ≥ K_w`. -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

/-! ### Orders and offsets -/

/-- The largest order offset: `m_max(R) = J_w N_w + L`. -/
def weakEntryMmax (R : WeakPassageRequest A) : ℕ := A.Jw * A.Nw + R.L

/-- The largest order of the reduction reserves: `K_max(R) = K_w + m_max(R) + J_w R_w (J_w N_w - 1)`.
It does not depend on `D_m`. -/
def weakEntryKmax (R : WeakPassageRequest A) : ℕ :=
  R.Kw + weakEntryMmax R + A.Jw * A.Rw * (A.Jw * A.Nw - 1)

/-- The request lifted to the reserves at the offset `m`: `K_w + m + J_w R_w (J_w N_w - 1)`. -/
def weakEntryLiftRequest (R : WeakPassageRequest A) (m : ℕ) : WeakPassageRequest A :=
  { R with
    Kw := R.Kw + m + A.Jw * A.Rw * (A.Jw * A.Nw - 1)
    field_order := le_trans R.field_order (by omega) }

/-! ### The families of (H) -/

/-- **The families of the shared lemma (H)** (`weakReduction_higher`) at the offset `m`: the root
value `θ(t)` on `[t_{M+J_w+1}, T]`, every passage `M < i ≤ M + J_w` solved, and the truncations
to `K_w` are the reduction `r` (values on every window, gradient lifts at almost every time). -/
def WeakHigherFamilies {x : WeakEntryData plan C} {g : WeakEntryStages x}
    (s : WeakEntrySchedule g) (θ : ℝ → Vec 2 → ℝ) (r : WeakEntryReduced s θ) (m : ℕ)
    (Uhi : ∀ i, WeakReductionFamily g m i) (Whi : ∀ i, WeakReductionLift g m i) : Prop :=
  (∀ (hr : (⟨0, []⟩ : Comp) ∈ (g.stage (x.M + A.Jw)).comps),
    ∀ t ∈ Set.Icc (s.tq (x.M + A.Jw + 1)) (x.a + A.T₀),
      (Uhi (x.M + A.Jw) ⟨_, hr⟩ t).toFunction.jet
          (valueIndex2 (weakReductionReserve R m (⟨0, []⟩ : Comp))) =ᵐ[volume.restrict
        AVenhance.unitCube] θ t) ∧
  (∀ i, x.M < i → i ≤ x.M + A.Jw → WeakReductionPassage s m Uhi Whi i) ∧
  (∀ j, x.M ≤ j → j ≤ x.M + A.Jw → ∀ v : CompIn (g.stage j).comps,
    ∀ t ∈ Set.Icc (s.tq (j + 1)) (x.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi j v t) = r.Ur j v t) ∧
  ∀ j, x.M ≤ j → j < x.M + A.Jw → ∀ v : CompIn (g.stage j).comps,
    ∀ᵐ t ∂(volume.restrict (Set.Icc (s.tq (j + 1)) (x.a + A.T₀))),
      truncateTorusHk (Nat.succ_le_succ (weakReductionReserve_kw_le R m v.1)) (Whi j v t) =
        r.Urw j v t

/-- `(H)` supplies such families: the statement of `weakReduction_higher` is `WeakHigherFamilies`. -/
theorem weakReduction_higher_families (hcommon : WeakEntryCommonOK plan)
    {x : WeakEntryData plan C} {g : WeakEntryStages x} (s : WeakEntrySchedule g)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (r : WeakEntryReduced s θ) (m : ℕ) :
    ∃ (Uhi : ∀ i, WeakReductionFamily g m i) (Whi : ∀ i, WeakReductionLift g m i),
      WeakHigherFamilies s θ r m Uhi Whi :=
  weakReduction_higher hcommon s f θ hθ r m

/-! ### The energy of one passage with data -/

/-- **`C_pass` works at the offset `m`**: for every `x`, stages `g`, schedule `s`, families
solving passage `i` and every `t ∈ [t_i, T]`, with `ρ_i = plan.radius R · ε_{i-1}`,
```
‖U_{i-1}(t)‖²_{ρ_i,π} + (κ/2) ∫_{[t_i, T]} ‖∇W_{i-1}‖²_{ρ_i,π} ≤ C_pass ‖trace of U_i at t_i‖²_{ρ_i,π}.
```
The diffusivity of the passage system is `kap (stage (i-1)).level`. -/
def WeakEntryPassageEnergyBound (plan : WeakEntryGluePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (m : ℕ) (Cpass : ℝ) : Prop :=
  ∀ (x : WeakEntryData plan C) (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (Uhi : ∀ i, WeakReductionFamily g m i) (Whi : ∀ i, WeakReductionLift g m i) (i : ℕ),
    x.M < i → i ≤ x.M + A.Jw → WeakReductionPassage s m Uhi Whi i →
    ∀ t ∈ Set.Icc (s.tq i) (x.a + A.T₀),
      ENNReal.ofReal (massNormSq (plan.radius R * x.D.eps (i - 1))
          (fun v : CompIn (g.stage (i - 1)).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Uhi (i - 1) v t).val)) +
        ENNReal.ofReal (x.D.kap (g.stage (i - 1)).level / 2) *
          ∫⁻ τ in Set.Icc (s.tq i) (x.a + A.T₀),
            ENNReal.ofReal (massGradNormSq (plan.radius R * x.D.eps (i - 1))
              (fun v : CompIn (g.stage (i - 1)).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
              (fun v => (Whi (i - 1) v τ).val)) ≤
      ENNReal.ofReal (Cpass * massNormSq (plan.radius R * x.D.eps (i - 1))
          (fun v : CompIn (g.stage (i - 1)).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (weakReductionTrace g m i (Uhi i) (s.tq i) v).val))

/-- **The energy of one passage** (`WeakEntryPassageEnergyStatement`): for every `R`, `C` and `m ≤ m_max(R)` there is
`C_pass ≥ 0`, chosen before `x`, `g`, `s` and the data, with `WeakEntryPassageEnergyBound`. -/
def WeakEntryPassageEnergyStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (m : ℕ), m ≤ weakEntryMmax R →
    ∃ Cpass : ℝ, 0 ≤ Cpass ∧ WeakEntryPassageEnergyBound plan R C m Cpass

/-- The level threshold of the weak flux production and of the record-size coefficient seminorms
at the largest order `K_max(R)` of the passage energy (compare `weakComparisonCoeffFloor`, at the order
`J_w R_w (J_w N_w - 1)`). -/
def weakEntryPassageCoeffFloor {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : ℕ :=
  if hΛ : 128 ≤ A.Λ then
    max (Classical.choose (Classical.choose_spec
        (uniform_weak_construction_flux_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
          A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
          (weakEntryKmax R) A.Jw_pos)).2)
      (Classical.choose (Classical.choose_spec
        (uniform_weak_physical_coefficient_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
          A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
          (weakEntryKmax R) A.Jw_pos)).2)
  else 0

/-- **Plan condition of the passage energy** (lower bounds on the level floor, an upper bound on the radius):
the level floor dominates the coefficient threshold at `K_max(R)`, the drift (Péclet) floor and
the stored-ledger floor, and `plan.radius R ≤ 1/2048`. It also contains `WeakEntryPairedPlanOK`
(radius at most `1/2048` and the paired level floor): the last passage (stage `M`, radius
`ρ ε_M`) is at the terminal scale, where the Péclet smallness `weak_peclet_eventually_small`
(which needs `m > M`) does not apply and the drift is paid by the radius budget, as in the paired
solve. -/
def WeakEntryPassageEnergyPlanOK (plan : WeakEntryGluePlan) : Prop :=
  WeakEntryPairedPlanOK plan ∧
  (∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    plan.radius R ≤ 1 / 2048) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (j₀ : ℕ),
    weakEntryPassageCoeffFloor R ≤ plan.levelFloor R C j₀ ∧
      weakComparisonDriftFloor A ≤ plan.levelFloor R C j₀ ∧
      weakQuietStoredFloor A ≤ plan.levelFloor R C j₀

/-! ### The trace at the reserves -/

/-- The squared order-zero norm (at radius `1`) of a family of stage `i` at the reserves, with the
weak masses. -/
def weakOrderZeroNormSq {x : WeakEntryData plan C} {g : WeakEntryStages x} {m : ℕ} (i : ℕ)
    (U : WeakReductionFamily g m i) (t : ℝ) : ℝ :=
  massNormSq 1 (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
    (fun v => (truncateTorusHk (Nat.zero_le _) (U v t)).val)

/-- **`C_q` works at the offset `m`**: for the families of the higher-order lemma at the offset `m` of every
reduction `r` of every weak solution `θ`, and every passage `M < i ≤ M + J_w`,
```
‖trace of U_i at t_i‖²_{ρ_i,π} ≤ C_q · sup_{t ∈ [t_{i+1}, t_i]} (order-zero norm of U_i(t))²
```
(the supremum in `[0, ∞]`). -/
def WeakEntryQuietTraceHighBound (plan : WeakEntryGluePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (m : ℕ) (Cq : ℝ) : Prop :=
  ∀ (x : WeakEntryData plan C) (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
    IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
  ∀ (r : WeakEntryReduced s θ) (Uhi : ∀ i, WeakReductionFamily g m i)
    (Whi : ∀ i, WeakReductionLift g m i), WeakHigherFamilies s θ r m Uhi Whi →
  ∀ i : ℕ, x.M < i → i ≤ x.M + A.Jw →
    ENNReal.ofReal (massNormSq (plan.radius R * x.D.eps (i - 1))
        (fun v : CompIn (g.stage (i - 1)).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (weakReductionTrace g m i (Uhi i) (s.tq i) v).val)) ≤
      ENNReal.ofReal Cq * ⨆ t ∈ Set.Icc (s.tq (i + 1)) (s.tq i),
        ENNReal.ofReal (weakOrderZeroNormSq i (Uhi i) t)

/-- **The quiet trace bound** (`WeakEntryQuietTraceHighStatement`): for every `R`, `C` and `m ≤ m_max(R)` there is
`C_q ≥ 0`, chosen before `x`, `g`, `s`, `f`, `θ`, `r` and the families, with
`WeakEntryQuietTraceHighBound`. -/
def WeakEntryQuietTraceHighStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (m : ℕ), m ≤ weakEntryMmax R →
    ∃ Cq : ℝ, 0 ≤ Cq ∧ WeakEntryQuietTraceHighBound plan R C m Cq

/-- **Plan condition of the quiet trace bound**: there is a passage plan `pp` whose quiet-coefficient refinement
(`weakQuietCoefficientPlan pp`, the plan of the two quiet trace layers) has, at every lifted
request `R' = weakEntryLiftRequest R m` with `m ≤ m_max(R)`, base and level floors below those of
the entry plan, and a radius at least the entry radius. -/
def WeakEntryQuietTraceHighPlanOK (plan : WeakEntryGluePlan) : Prop :=
  ∃ (pp : WeakPassagePlan) (prices : WeakQuietPathPrices),
    WeakQuietRowsPlanOK (weakQuietCoefficientPlan pp) prices ∧
    (∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 ≤ (weakQuietCoefficientPlan pp).coeffC R) ∧
    WeakQuietScalarPricesOK (weakQuietCoefficientPlan pp) prices ∧
    WeakQuietMarginPriceStatement (weakQuietCoefficientPlan pp) prices ∧
    ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
      (C : WeakEntryAllocation R (plan.radius R)) (m : ℕ), m ≤ weakEntryMmax R →
      (weakQuietCoefficientPlan pp).baseFloor B ≤ plan.baseFloor B ∧
      (weakQuietCoefficientPlan pp).momentFloor A ≤ plan.momentFloor A ∧
      (∀ j₀ : ℕ, (weakQuietCoefficientPlan pp).levelFloor (weakEntryLiftRequest R m) j₀ ≤
        plan.levelFloor R C j₀) ∧
      plan.radius R ≤ (weakQuietCoefficientPlan pp).radius (weakEntryLiftRequest R m)

/-! ### Constants and plan condition of the iteration -/

open scoped Classical in
/-- The constant `C_pass` of the passage energy at `(R, C, m)`, chosen classically (`0` if none exists). -/
def weakEntryPassageConst (plan : WeakEntryGluePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (m : ℕ) : ℝ :=
  if h : ∃ Cpass : ℝ, 0 ≤ Cpass ∧ WeakEntryPassageEnergyBound plan R C m Cpass then
    Classical.choose h else 0

open scoped Classical in
/-- The constant `C_q` of the quiet trace bound at `(R, C, m)`, chosen classically (`0` if none exists). -/
def weakEntryQuietConst (plan : WeakEntryGluePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (m : ℕ) : ℝ :=
  if h : ∃ Cq : ℝ, 0 ≤ Cq ∧ WeakEntryQuietTraceHighBound plan R C m Cq then
    Classical.choose h else 0

/-- **The raw constant** `C_raw(R, C, m) = √(B^{J_w} + 2) · √2 · (√(C_pass C_q))^{J_w}`, from the
chosen constants of the passage energy and the quiet trace bound at the offset `m`, where `B = weakStoredWordBudget N_w R_w` bounds
the number of components of the stage `M` by `B^{J_w}` (`weakConstruction_card_le`). The factor
`√(B^{J_w} + 2)` replaces a factor `√3`: `strongEnergy` takes the time supremum of each
component before the mass sum, so the sum of the suprema is at most the component count times the
supremum of the sum (the passage energy), and the gradient part costs `2` (`κ = 2 · κ/2`). -/
def weakEntryRawConst (plan : WeakEntryGluePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (m : ℕ) : ℝ :=
  Real.sqrt ((weakStoredWordBudget A.Nw A.Rw ^ A.Jw : ℕ) + 2) * Real.sqrt 2 *
    Real.sqrt (weakEntryPassageConst plan R C m * weakEntryQuietConst plan R C m) ^ A.Jw

/-- **Plan condition of the raw energy**: the plan conditions of the passage energy and the quiet trace bound, and
`3 C_raw(R, C, 0) ≤ CK`. Lower bounds on `CK` and the level floor, upper bound on the radius. -/
def WeakEntryRawEnergyPlanOK (plan : WeakEntryGluePlan) : Prop :=
  WeakEntryPassageEnergyPlanOK plan ∧ WeakEntryQuietTraceHighPlanOK plan ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)),
    3 * weakEntryRawConst plan R C 0 ≤ plan.CK R C

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **Core of the passage energy, part 1: record-size coupling constants over raw data**.

`WeakRawSetting R` is the raw data of a weak construction: an `OCData`, a stage family with
`IsWeakConstruction`, the streams and the band chain at the terminal level `M`. It is what both the
entry data (`WeakEntryData`, `WeakEntryStages`) and a passage instance carry. Over it, the
coefficient seminorms of stage `L` (`M ≤ L < M + J_w`) at radius `ρ ε_L` and orders up to
`K_max(R)` are at most `C_K · size · κ_M · ε_L^{d-2}` (`weakRaw_physCoeff_seminorm_le`), and the
coupling constants of a row, weighted by the reserve factors, are at most
`κ_M · C_R · (stored weights)` (`weakRaw_edge_le_stored`), with
`C_R = C_K ∑_{n < J_w N_w} ρ^{-n} (K_max + n)!` (`weakRawEdgeConst`). -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs
  Comparison

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

namespace WeakRawSetting

variable {R : WeakPassageRequest A} (S : WeakRawSetting R)

theorem mass_pos (c : Comp) : 0 < weakMass S.D A.Nw A.Jw A.η₀ c :=
  weakMass_pos S.D A.Nw A.Jw A.η₀ A.Nw_pos A.Jw_pos (fun _ => S.eps_pos _) c

end WeakRawSetting

/-- The record-size seminorm constant of the coefficient production at the largest order
`K_max(R)`. -/
def weakRawCK (R : WeakPassageRequest A) : ℝ :=
  if hΛ : 128 ≤ A.Λ then
    Classical.choose (uniform_weak_physical_coefficient_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀
      B.hs₁ B.hq A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
      (weakEntryKmax R) A.Jw_pos)
  else 0

theorem weakRawCK_nonneg (R : WeakPassageRequest A) : 0 ≤ weakRawCK R := by
  unfold weakRawCK
  split
  · exact (Classical.choose_spec (uniform_weak_physical_coefficient_production B.α B.s B.q B.hα₀
      B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ ‹_› B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
      (weakEntryKmax R) A.Jw_pos)).1
  · exact le_rfl

/-- The edge constant of the rows at the orders up to `K_max(R)`, for the radius factor `ρ`. -/
def weakRawEdgeConst (ρ : ℝ) (R : WeakPassageRequest A) : ℝ :=
  weakRawCK R * ∑ n ∈ Finset.range (A.Jw * A.Nw), ρ⁻¹ ^ n * ((weakEntryKmax R + n).factorial : ℝ)

theorem weakRawEdgeConst_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (R : WeakPassageRequest A) :
    0 ≤ weakRawEdgeConst ρ R :=
  mul_nonneg (weakRawCK_nonneg R) (Finset.sum_nonneg fun _ _ =>
    mul_nonneg (pow_nonneg (inv_nonneg.2 hρ) _) (Nat.cast_nonneg _))

/-- The level threshold of the production at `K_max(R)`. -/
theorem weakRaw_threshold (R : WeakPassageRequest A) {M : ℕ}
    (hfloor : weakEntryPassageCoeffFloor R ≤ M) (hΛ : 128 ≤ A.Λ) :
    Classical.choose (Classical.choose_spec (uniform_weak_physical_coefficient_production B.α B.s
      B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw
      R.sZ (weakEntryKmax R) A.Jw_pos)).2 ≤ M := by
  unfold weakEntryPassageCoeffFloor at hfloor
  rw [dite_eq_left hΛ] at hfloor
  exact (le_max_right _ _).trans hfloor

/-- **Record-size seminorms** of the physical coefficients of a stage `L`, `M ≤ L < M + J_w`, at
orders up to `K_max(R)`. -/
theorem weakRaw_physCoeff_seminorm_le {R : WeakPassageRequest A} (S : WeakRawSetting R)
    (hfloor : weakEntryPassageCoeffFloor R ≤ S.M) (L : ℕ) (hL : S.M ≤ L) (hLJ : L < S.M + A.Jw)
    (t₀ t₁ : ℝ) (v u : CompIn (S.stage L).comps) (γ : (S.stage L).fam.Γ v u) (d : ℕ)
    (hd : 2 ≤ d) (k : ℕ) (hk : k ≤ weakEntryKmax R) :
    coefficientSeminorm (S.D.eps L) k t₀ t₁ ((S.stage L).physCoeff v u γ d) ≤
      ENNReal.ofReal (weakRawCK R * ((S.stage L).fam.identity v u γ).record.size *
        S.D.κ S.M * S.D.eps L ^ (d - 2)) := by
  have hΛ := S.base128
  have hκ := S.kappa_pos.le
  have hε := S.eps_pos
  have hM₁ := weakRaw_threshold R hfloor hΛ
  obtain ⟨-, hcoef⟩ := Classical.choose_spec (Classical.choose_spec
    (uniform_weak_physical_coefficient_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
      A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
      (weakEntryKmax R) A.Jw_pos)).2
  have hCK : weakRawCK R = Classical.choose (uniform_weak_physical_coefficient_production
      B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw
      A.Rw R.sZ (weakEntryKmax R) A.Jw_pos) := by
    unfold weakRawCK
    rw [dite_eq_left hΛ]
  by_cases hdn : d ≤ ((S.stage L).fam.identity v u γ).maxOrder
  · refine (hcoef S.D (hM₁.trans S.terminal.symm.le) S.alpha S.q_eq S.base_eq S.profile_eq
      S.streams S.band' S.Dm S.order_ge S.j₀ S.stage S.P S.M R.sX 0 A.η₀ (S.D.termRW A.σw S.M)
      S.terminal S.construction L hL hLJ v u γ d k hd hdn hk t₀ t₁).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [← hCK]
    have hq : 1 < S.D.q := by rw [S.q_eq]; exact B.hq.1
    have hscale := production_scale_le (hε L) (hε (L + 1)).le
      (EntryScales.epsilon_antitone hq (by rw [S.base_eq]; exact hΛ) (Nat.le_succ L)) hd hdn
    have hpos : 0 ≤ weakRawCK R * ((S.stage L).fam.identity v u γ).record.size *
        S.D.κ S.M := mul_nonneg (mul_nonneg (weakRawCK_nonneg R)
          ((S.stage L).fam.identity v u γ).record.size_nonneg) hκ
    calc weakRawCK R * ((S.stage L).fam.identity v u γ).record.size * S.D.κ S.M *
          S.D.eps (L + 1) ^ (((S.stage L).fam.identity v u γ).maxOrder - 2) *
          S.D.eps L ^ ((d : ℝ) - (((S.stage L).fam.identity v u γ).maxOrder : ℝ))
        = weakRawCK R * ((S.stage L).fam.identity v u γ).record.size * S.D.κ S.M *
          (S.D.eps (L + 1) ^ (((S.stage L).fam.identity v u γ).maxOrder - 2) *
          S.D.eps L ^ ((d : ℝ) - (((S.stage L).fam.identity v u γ).maxOrder : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale hpos
  · have hz : (S.stage L).physCoeff v u γ d = fun _ _ => 0 := by
      funext t x
      exact constituentPhysical_zero_above_max (S.stage L).fam _ _ _ (S.stage L).actual v u γ d
        (not_le.mp hdn) t x
    rw [hz, coefficientSeminorm_zero_function]
    exact bot_le
end

/-! **Core of the passage energy, part 2: edge constants against the stored weights**.

For a stage `L` of a `WeakRawSetting`, the coupling coefficients of the reduction system at the
reserves `weakReductionReserve R m` (any offset `m ≤ m_max(R)`) satisfy, at radius `ρ ε_L` with
`0 < ρ ≤ 1`,
`∑_d |A_{vu,d}|_{ρ ε_L, K_v} · (reserve factor) ≤ κ_M · C_R · √(π_v/π_u) · ∑_γ stored weight`
(`weakRaw_edge_le_stored`), the shape of the `hc` input of `coupledRowData_recursion`; and the row
sums of the stored weights are at most one (`weakRaw_storedRow_le`), from
`exists_weak_quiet_stored_threshold`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  Construction.Preservation.Ledger

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

theorem weakReductionReserve_le_kmax (R : WeakPassageRequest A) {m : ℕ}
    (hm : m ≤ weakEntryMmax R) (c : Comp) : weakReductionReserve R m c ≤ weakEntryKmax R :=
  (weakReductionReserve_le R m c).trans (by unfold weakEntryKmax; omega)

/-- **The edge constant of a row against the plain record sizes.** -/
theorem weakRaw_edge_le (S : WeakRawSetting R)
    (hfloor : weakEntryPassageCoeffFloor R ≤ S.M) (L : ℕ) (hL : S.M ≤ L) (hLJ : L < S.M + A.Jw)
    (a b rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (hsmooth : ∀ v u (γ : (S.stage L).fam.Γ v u) d, 2 ≤ d → ∀ k ≤ weakEntryKmax R, ∀ t,
      ContDiff ℝ (k : ℕ) ((S.stage L).physCoeff v u γ d t))
    (v u : CompIn (S.stage L).comps) :
    ∑ d : admissibleOrders (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1)
        (1 + A.Jw * A.Nw) v u,
      (coefficientSeminorm (rad * S.D.eps L) (weakReductionReserve R m v.1) a b
        (fun t y => ∑ γ : (S.stage L).fam.Γ v u, (S.stage L).physCoeff v u γ d.1 t y)).toReal *
        derivativeReserveFactor (rad * S.D.eps L) (weakReductionReserve R m v.1) (d.1 - 2) ≤
      S.D.κ S.M * weakRawEdgeConst rad R *
        ∑ γ : (S.stage L).fam.Γ v u, ((S.stage L).fam.identity v u γ).record.size := by
  classical
  have hε : 0 < S.D.eps L := S.eps_pos L
  have hκ : 0 ≤ S.D.κ S.M := S.kappa_pos.le
  set Sz := ∑ γ : (S.stage L).fam.Γ v u, ((S.stage L).fam.identity v u γ).record.size with hS
  have hS0 : 0 ≤ Sz :=
    Finset.sum_nonneg fun γ _ => ((S.stage L).fam.identity v u γ).record.size_nonneg
  have hK := weakReductionReserve_le_kmax R hm v.1
  have hterm : ∀ d : admissibleOrders (fun v : CompIn (S.stage L).comps =>
      weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) v u,
      (coefficientSeminorm (rad * S.D.eps L) (weakReductionReserve R m v.1) a b
        (fun t y => ∑ γ : (S.stage L).fam.Γ v u, (S.stage L).physCoeff v u γ d.1 t y)).toReal *
        derivativeReserveFactor (rad * S.D.eps L) (weakReductionReserve R m v.1) (d.1 - 2) ≤
      weakRawCK R * Sz * S.D.κ S.M * (rad⁻¹ ^ (d.1 - 2) *
        ((weakEntryKmax R + (d.1 - 2)).factorial : ℝ)) := by
    intro d
    have hd : 2 ≤ d.1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 d.2).1).1
    have hsem : coefficientSeminorm (rad * S.D.eps L) (weakReductionReserve R m v.1) a b
        (fun t y => ∑ γ : (S.stage L).fam.Γ v u, (S.stage L).physCoeff v u γ d.1 t y) ≤
        ENNReal.ofReal (weakRawCK R * Sz * S.D.κ S.M * S.D.eps L ^ (d.1 - 2)) := by
      refine (coefficientSeminorm_radius_mono _ (S.D.eps L) (mul_pos hrad hε).le
        (by nlinarith) _ a b _).trans ?_
      refine (CycleComparison.Error.coefficientSeminorm_finset_sum_le Finset.univ (S.D.eps L)
        hε.le (weakReductionReserve R m v.1) a b (fun γ => (S.stage L).physCoeff v u γ d.1)
        (fun γ _ t _ => hsmooth v u γ d.1 hd _ hK t)).trans ?_
      refine (Finset.sum_le_sum fun γ _ => weakRaw_physCoeff_seminorm_le S hfloor L hL hLJ
        a b v u γ d.1 hd _ hK).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg fun γ _ => mul_nonneg (mul_nonneg (mul_nonneg
        (weakRawCK_nonneg R) ((S.stage L).fam.identity v u γ).record.size_nonneg) hκ)
        (pow_nonneg hε.le _)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [hS, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    have hx : 0 ≤ weakRawCK R * Sz * S.D.κ S.M :=
      mul_nonneg (mul_nonneg (weakRawCK_nonneg R) hS0) hκ
    have hreal := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hx (pow_nonneg hε.le _)) hsem
    have hdrf : 0 ≤ derivativeReserveFactor (rad * S.D.eps L) (weakReductionReserve R m v.1)
        (d.1 - 2) := by
      unfold derivativeReserveFactor
      positivity
    exact (mul_le_mul_of_nonneg_right hreal hdrf).trans
      (edge_order_term_le _ _ _ hx hε hrad (d.1 - 2) _ _ hK)
  refine (Finset.sum_le_sum fun d _ => hterm d).trans ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ d : admissibleOrders (fun v : CompIn (S.stage L).comps =>
      weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) v u,
      (rad⁻¹ ^ (d.1 - 2) * ((weakEntryKmax R + (d.1 - 2)).factorial : ℝ)) ≤
      ∑ n ∈ Finset.range (A.Jw * A.Nw),
        rad⁻¹ ^ n * ((weakEntryKmax R + n).factorial : ℝ) := by
    have himg := Finset.sum_image (s := Finset.univ) (f := fun n : ℕ =>
      rad⁻¹ ^ n * ((weakEntryKmax R + n).factorial : ℝ))
      (g := fun d : admissibleOrders (fun v : CompIn (S.stage L).comps =>
        weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) v u => d.1 - 2) (fun d _ d' _ hdd => by
      have h1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 d.2).1).1
      have h2 := (Finset.mem_Icc.1 (Finset.mem_filter.1 d'.2).1).1
      exact Subtype.ext (by simp only at hdd; omega))
    rw [← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
      mul_nonneg (pow_nonneg (inv_nonneg.2 hrad.le) _) (Nat.cast_nonneg _)
    intro n hn
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hn
    have h := Finset.mem_Icc.1 (Finset.mem_filter.1 d.2).1
    exact Finset.mem_range.2 (by omega)
  calc weakRawCK R * Sz * S.D.κ S.M * ∑ d : admissibleOrders (fun v : CompIn
        (S.stage L).comps => weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) v u,
        (rad⁻¹ ^ (d.1 - 2) * ((weakEntryKmax R + (d.1 - 2)).factorial : ℝ))
      ≤ weakRawCK R * Sz * S.D.κ S.M * ∑ n ∈ Finset.range (A.Jw * A.Nw),
        rad⁻¹ ^ n * ((weakEntryKmax R + n).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (mul_nonneg (weakRawCK_nonneg R) hS0) hκ)
    _ = _ := by unfold weakRawEdgeConst; ring

/-- The total of the stored weights of a stage `L` is at most one above the stored-ledger floor. -/
theorem weakRaw_storedTotal_le (S : WeakRawSetting R) (hstored : weakQuietStoredFloor A ≤ S.M)
    (L : ℕ) (hL : S.M ≤ L) (hLJ : L ≤ S.M + A.Jw) :
    weakStoredTotal (S.stage L) A.Nw A.Jw A.η₀ ≤ 1 :=
  (exists_weak_quiet_stored_threshold A).choose_spec S.base128 S.M hstored S.D S.alpha S.q_eq
    S.base_eq S.terminal S.band S.Dm S.j₀ S.P R.sX R.sZ S.stage S.construction L hL hLJ

/-- The row sums of the stored weights are at most one above the stored-ledger floor. -/
theorem weakRaw_storedRow_le (S : WeakRawSetting R) (hstored : weakQuietStoredFloor A ≤ S.M)
    (L : ℕ) (hL : S.M ≤ L) (hLJ : L ≤ S.M + A.Jw) (v : CompIn (S.stage L).comps) :
    ∑ u, ∑ γ : (S.stage L).fam.Γ v u,
      weakStoredEdgeWeight (S.stage L) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩ ≤ 1 := by
  classical
  refine le_trans ?_ (weakRaw_storedTotal_le S hstored L hL hLJ)
  have hrow : (∑ u, ∑ γ : (S.stage L).fam.Γ v u,
      weakStoredEdgeWeight (S.stage L) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩) ≤
      ∑ v', ∑ u, ∑ γ : (S.stage L).fam.Γ v' u,
        weakStoredEdgeWeight (S.stage L) A.Nw A.Jw A.η₀ ⟨v', u, γ⟩ :=
    Finset.single_le_sum (f := fun v' => ∑ u, ∑ γ : (S.stage L).fam.Γ v' u,
      weakStoredEdgeWeight (S.stage L) A.Nw A.Jw A.η₀ ⟨v', u, γ⟩)
      (fun v' _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun γ _ =>
        weakStoredEdgeWeight_nonneg _ _ _ _ _) (Finset.mem_univ v)
  refine hrow.trans (le_of_eq ?_)
  simp only [weakStoredTotal, LedgerEdge, Fintype.sum_sigma]

/-- **The edge constant of a row against the stored weights**, in the shape of the coupling
hypothesis of `coupledRowData_recursion`. -/
theorem weakRaw_edge_le_stored (S : WeakRawSetting R)
    (hfloor : weakEntryPassageCoeffFloor R ≤ S.M) (L : ℕ) (hL : S.M ≤ L) (hLJ : L < S.M + A.Jw)
    (a b rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (hsmooth : ∀ v u (γ : (S.stage L).fam.Γ v u) d, 2 ≤ d → ∀ k ≤ weakEntryKmax R, ∀ t,
      ContDiff ℝ (k : ℕ) ((S.stage L).physCoeff v u γ d t))
    (v u : CompIn (S.stage L).comps) :
    ∑ d : admissibleOrders (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1)
        (1 + A.Jw * A.Nw) v u,
      (coefficientSeminorm (rad * S.D.eps L) (weakReductionReserve R m v.1) a b
        (fun t y => ∑ γ : (S.stage L).fam.Γ v u, (S.stage L).physCoeff v u γ d.1 t y)).toReal *
        derivativeReserveFactor (rad * S.D.eps L) (weakReductionReserve R m v.1) (d.1 - 2) ≤
      S.D.κ S.M * weakRawEdgeConst rad R *
        Real.sqrt (weakMass S.D A.Nw A.Jw A.η₀ v.1 / weakMass S.D A.Nw A.Jw A.η₀ u.1) *
        ∑ γ : (S.stage L).fam.Γ v u,
          weakStoredEdgeWeight (S.stage L) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩ := by
  have hπ := S.mass_pos
  refine (weakRaw_edge_le S hfloor L hL hLJ a b rad hrad hrad1 m hm hsmooth v u).trans
    (le_of_eq ?_)
  have hs : Real.sqrt (weakMass S.D A.Nw A.Jw A.η₀ v.1 / weakMass S.D A.Nw A.Jw A.η₀ u.1) *
      Real.sqrt (weakMass S.D A.Nw A.Jw A.η₀ u.1 / weakMass S.D A.Nw A.Jw A.η₀ v.1) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg (hπ v.1).le (hπ u.1).le), div_mul_div_comm,
      mul_comm (weakMass S.D A.Nw A.Jw A.η₀ v.1), div_self (mul_pos (hπ u.1) (hπ v.1)).ne',
      Real.sqrt_one]
  rw [mul_assoc (S.D.κ S.M * weakRawEdgeConst rad R)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  unfold weakStoredEdgeWeight
  rw [← mul_assoc, hs, one_mul]
end

end AVRegularity.Providers.WeakGen.Reduction
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The iteration of the raw energy** (steps 1 to 3, at a general order offset `m`).

With `Φ_i = sup_{t ∈ [t_{i+1}, t_i]}` of the order-zero norm of `U_i` (the supremum of the quiet trace bound):
* the root: `Φ_{M+J_w} ≤ 2 ‖f‖²` (`rawEnergy_l2NormSq_le`, root mass `1/2`);
* a passage: `Φ_{i-1} ≤ C_pass C_q Φ_i` (quiet trace bound then passage energy, order zero is at most the factorial norm);
* the last passage: the passage energy at `i = M + 1` bounds the supremum of the mass sum and half the gradient
  integral by `C_pass C_q Φ_{M+1}`, and the strong-energy expression of `(U_M, W_M)` at the radius
  `ρ ε_M` is at most `(#components + 2)` times that (`rawEnergy_inner_le`). -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x}

/-- The number of components of a stage `M` of a weak entry is at most `B^{J_w}`. -/
theorem weakEntry_card_le (i : ℕ) (hMi : x.M ≤ i) (hi : i ≤ x.M + A.Jw) :
    Fintype.card (CompIn (g.stage i).comps) ≤ weakStoredWordBudget A.Nw A.Rw ^ A.Jw := by
  have h := weakConstruction_card_le x.P _ x.M A.Jw 0 _ g.stage g.construction i hMi hi
  simpa using h

/-- The weak masses are positive. -/
theorem weakEntry_mass_pos (g : WeakEntryStages x) (c : Comp) :
    0 < weakMass x.D A.Nw A.Jw A.η₀ c :=
  weakMass_pos x.D A.Nw A.Jw A.η₀ A.Nw_pos A.Jw_pos
    (fun j => (weakEntryRawSetting g).eps_pos j) c

/-- `Φ_i`: the supremum of the order-zero norm of the family of stage `i` on `[t_{i+1}, t_i]`. -/
def weakHighQuietSup {m : ℕ} (s : WeakEntrySchedule g) (Uhi : ∀ i, WeakReductionFamily g m i)
    (i : ℕ) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc (s.tq (i + 1)) (s.tq i), ENNReal.ofReal (weakOrderZeroNormSq i (Uhi i) t)

/-- The order-zero norm is at most the mass norm at any radius. -/
theorem weakOrderZeroNormSq_le (g : WeakEntryStages x) {m : ℕ} (i : ℕ)
    (U : WeakReductionFamily g m i) (t ρ : ℝ) :
    weakOrderZeroNormSq i U t ≤ massNormSq ρ
      (fun v : CompIn (g.stage i).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
      (fun v => (U v t).val) := by
  unfold weakOrderZeroNormSq massNormSq
  exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
    (factorialNormSq_orderZero_le ρ (U v t))
    (inv_nonneg.2 (weakEntry_mass_pos g v.1).le)

section Iteration

variable {m : ℕ} {Cp Cq : ℝ} {s : WeakEntrySchedule g} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
  {r : WeakEntryReduced s θ} {Uhi : ∀ i, WeakReductionFamily g m i}
  {Whi : ∀ i, WeakReductionLift g m i}

/-- **A passage with its trace**: the quiet trace bound inside the passage energy. -/
theorem weakHigh_step_total (hCp : 0 ≤ Cp)
    (hAb : WeakEntryPassageEnergyBound plan R C m Cp)
    (hBb : WeakEntryQuietTraceHighBound plan R C m Cq)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (hfam : WeakHigherFamilies s θ r m Uhi Whi) (i : ℕ) (hMi : x.M < i) (hi : i ≤ x.M + A.Jw)
    (t : ℝ) (ht : t ∈ Set.Icc (s.tq i) (x.a + A.T₀)) :
    ENNReal.ofReal (massNormSq (plan.radius R * x.D.eps (i - 1))
        (fun v : CompIn (g.stage (i - 1)).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (Uhi (i - 1) v t).val)) +
      ENNReal.ofReal (x.D.kap (g.stage (i - 1)).level / 2) *
        ∫⁻ τ in Set.Icc (s.tq i) (x.a + A.T₀),
          ENNReal.ofReal (massGradNormSq (plan.radius R * x.D.eps (i - 1))
            (fun v : CompIn (g.stage (i - 1)).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
            (fun v => (Whi (i - 1) v τ).val)) ≤
      ENNReal.ofReal Cp * (ENNReal.ofReal Cq * weakHighQuietSup s Uhi i) := by
  have hA := hAb x g s Uhi Whi i hMi hi (hfam.2.1 i hMi hi) t ht
  have hB := hBb x g s f θ hθ r Uhi Whi hfam i hMi hi
  refine hA.trans ?_
  rw [ENNReal.ofReal_mul hCp]
  exact mul_le_mul_right hB _

/-- One passage lowers `Φ` by the factor `C_pass C_q`. -/
theorem weakHigh_sup_step (hCp : 0 ≤ Cp)
    (hAb : WeakEntryPassageEnergyBound plan R C m Cp)
    (hBb : WeakEntryQuietTraceHighBound plan R C m Cq)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (hfam : WeakHigherFamilies s θ r m Uhi Whi) (i : ℕ) (hMi : x.M + 1 < i)
    (hi : i ≤ x.M + A.Jw) :
    weakHighQuietSup s Uhi (i - 1) ≤
      ENNReal.ofReal Cp * ENNReal.ofReal Cq * weakHighQuietSup s Uhi i := by
  have hi1 : i - 1 + 1 = i := by omega
  unfold weakHighQuietSup
  rw [hi1]
  refine iSup₂_le fun t ht => ?_
  have hT := weakEntrySchedule_tq_le s (i - 1) (by omega) (by omega)
  have htT : t ∈ Set.Icc (s.tq i) (x.a + A.T₀) := ⟨ht.1, ht.2.trans hT⟩
  have h1 := weakHigh_step_total hCp hAb hBb hθ hfam i (by omega) hi t htT
  have h2 := weakOrderZeroNormSq_le g (i - 1) (Uhi (i - 1)) t (plan.radius R * x.D.eps (i - 1))
  calc ENNReal.ofReal (weakOrderZeroNormSq (i - 1) (Uhi (i - 1)) t)
      ≤ _ := ENNReal.ofReal_le_ofReal h2
    _ ≤ _ := le_self_add.trans h1
    _ = _ := by rw [mul_assoc]; rfl

/-- **The iteration**: `Φ_{M+J_w-n} ≤ (C_pass C_q)^n Φ_{M+J_w}` for `n < J_w`. -/
theorem weakHigh_sup_chain (hCp : 0 ≤ Cp)
    (hAb : WeakEntryPassageEnergyBound plan R C m Cp)
    (hBb : WeakEntryQuietTraceHighBound plan R C m Cq)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (hfam : WeakHigherFamilies s θ r m Uhi Whi) :
    ∀ n, n < A.Jw → weakHighQuietSup s Uhi (x.M + A.Jw - n) ≤
      (ENNReal.ofReal Cp * ENNReal.ofReal Cq) ^ n * weakHighQuietSup s Uhi (x.M + A.Jw) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := weakHigh_sup_step hCp hAb hBb hθ hfam (x.M + A.Jw - n) (by omega) (by omega)
    rw [show x.M + A.Jw - n - 1 = x.M + A.Jw - (n + 1) by omega] at h1
    refine h1.trans ?_
    rw [pow_succ']
    calc _ ≤ ENNReal.ofReal Cp * ENNReal.ofReal Cq *
          ((ENNReal.ofReal Cp * ENNReal.ofReal Cq) ^ n * weakHighQuietSup s Uhi (x.M + A.Jw)) :=
          mul_le_mul_right (ih (by omega)) _
      _ = _ := by ring

/-- **The root**: `Φ_{M+J_w} ≤ 2 ‖f‖²` (the root mass is `1/2` and the value is `θ(t)`). -/
theorem weakHigh_sup_root
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (hfam : WeakHigherFamilies s θ r m Uhi Whi) :
    weakHighQuietSup s Uhi (x.M + A.Jw) ≤ ENNReal.ofReal (2 * l2NormSq f) := by
  have hcomp : (g.stage (x.M + A.Jw)).comps = {(⟨0, []⟩ : Comp)} :=
    g.construction.2.1.2.1
  have hr : (⟨0, []⟩ : Comp) ∈ (g.stage (x.M + A.Jw)).comps := by rw [hcomp]; simp
  have key : ∀ c : Comp, c ∈ (g.stage (x.M + A.Jw)).comps → c = ⟨0, []⟩ := fun c hc => by
    rw [hcomp] at hc
    exact Finset.mem_singleton.1 hc
  have : Subsingleton (CompIn (g.stage (x.M + A.Jw)).comps) :=
    ⟨fun v w => Subtype.ext ((key _ v.2).trans (key _ w.2).symm)⟩
  unfold weakHighQuietSup
  refine iSup₂_le fun t ht => ?_
  have hT := weakEntrySchedule_tq_le s (x.M + A.Jw) (by have := A.Jw_pos; omega) le_rfl
  have htr : t ∈ Set.Icc (s.tq (x.M + A.Jw + 1)) (x.a + A.T₀) := ⟨ht.1, ht.2.trans hT⟩
  have hval := factorialNormSq_orderZero_value (Uhi (x.M + A.Jw) ⟨_, hr⟩ t) (θ t)
    (hfam.1 hr t htr)
  have hoz : weakOrderZeroNormSq (x.M + A.Jw) (Uhi (x.M + A.Jw)) t = 2 * l2NormSq (θ t) := by
    unfold weakOrderZeroNormSq massNormSq
    rw [Fintype.sum_subsingleton _ (⟨⟨0, []⟩, hr⟩ : CompIn (g.stage (x.M + A.Jw)).comps)]
    simp only [weakMass_root]
    rw [hval]
    unfold l2NormSq
    norm_num
  rw [hoz]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ zero_le_two)
  let S := weakEntryRawSetting g
  have hb := isWindowDrift_of_isContDrift
    (streamSeq_isContDrift B.hζ S.base128 S.streams (x.M + A.Jw)) x.a (x.a + A.T₀)
  have hlt : x.a < s.tq (x.M + A.Jw + 1) := s.start
  exact rawEnergy_l2NormSq_le S.kappa_pos.le (by linarith [A.τ_small, s.finish, hlt, hT, ht.1, ht.2]) hb hθ t
    ⟨hlt.le.trans htr.1, htr.2⟩

/-- **The energy of `(U_M, W_M)` at offset `m`, radius `ρ_{M+1} = ρ ε_M`**: the strong-energy
expression of the families at the reserves (before the square root) is at most
`(B^{J_w} + 2) (C_pass C_q)^{J_w} · 2 ‖f‖²`. -/
theorem weakHigh_inner_le (hCp : 0 ≤ Cp) (hCq : 0 ≤ Cq)
    (hAb : WeakEntryPassageEnergyBound plan R C m Cp)
    (hBb : WeakEntryQuietTraceHighBound plan R C m Cq)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (hfam : WeakHigherFamilies s θ r m Uhi Whi) :
    (∑ v : CompIn (g.stage x.M).comps,
      ENNReal.ofReal (weakMass x.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        ((⨆ t ∈ Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀), ENNReal.ofReal
            (factorialNormSq (x.D.termRStar (plan.radius R) x.M) (Uhi x.M v t).val)) +
          ENNReal.ofReal (x.D.κ x.M) * ∫⁻ τ in Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀),
            ENNReal.ofReal (gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M)
              (Whi x.M v τ).val))) ≤
      ENNReal.ofReal (((weakStoredWordBudget A.Nw A.Rw ^ A.Jw : ℕ) + 2 : ℝ) *
        ((Cp * Cq) ^ A.Jw * (2 * l2NormSq f))) := by
  have hJ := A.Jw_pos
  have hlev : (g.stage x.M).level = x.M :=
    (weakEntryRawSetting g).level_eq x.M le_rfl (Nat.le_add_right _ _)
  have hkap : x.D.kap (g.stage x.M).level = x.D.κ x.M := by
    rw [hlev]; exact (weakEntryRawSetting g).kap_eq _ le_rfl
  set X : ℝ≥0∞ := ENNReal.ofReal Cp * (ENNReal.ofReal Cq * weakHighQuietSup s Uhi (x.M + 1))
    with hXdef
  have hX : ∀ t ∈ Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀),
      ENNReal.ofReal (massNormSq (x.D.termRStar (plan.radius R) x.M)
          (fun v : CompIn (g.stage x.M).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Uhi x.M v t).val)) +
        ENNReal.ofReal (x.D.κ x.M / 2) * ∫⁻ τ in Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀),
          ENNReal.ofReal (massGradNormSq (x.D.termRStar (plan.radius R) x.M)
            (fun v : CompIn (g.stage x.M).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
            (fun v => (Whi x.M v τ).val)) ≤ X := by
    intro t ht
    have h : ENNReal.ofReal (massNormSq (x.D.termRStar (plan.radius R) x.M)
          (fun v : CompIn (g.stage x.M).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Uhi x.M v t).val)) +
        ENNReal.ofReal (x.D.kap (g.stage x.M).level / 2) *
          ∫⁻ τ in Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀),
          ENNReal.ofReal (massGradNormSq (x.D.termRStar (plan.radius R) x.M)
            (fun v : CompIn (g.stage x.M).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
            (fun v => (Whi x.M v τ).val)) ≤ X :=
      weakHigh_step_total hCp hAb hBb hθ hfam (x.M + 1) (by omega) (by omega) t ht
    rwa [hkap] at h
  have hinner := rawEnergy_inner_le (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M)
    (fun v : CompIn (g.stage x.M).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
    (fun v => weakEntry_mass_pos g v.1) (s.tq (x.M + 1)) (x.a + A.T₀) (Uhi x.M) (Whi x.M) X hX
  have hcard := weakEntry_card_le (g := g) x.M le_rfl (by omega)
  have hc : ((Fintype.card (CompIn (g.stage x.M).comps) : ℕ) : ℝ≥0∞) + 2 ≤
      ENNReal.ofReal (((weakStoredWordBudget A.Nw A.Rw ^ A.Jw : ℕ) : ℝ) + 2) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num), ENNReal.ofReal_natCast,
      ENNReal.ofReal_ofNat]
    gcongr
  have hchain := weakHigh_sup_chain hCp hAb hBb hθ hfam (A.Jw - 1) (by omega)
  rw [show x.M + A.Jw - (A.Jw - 1) = x.M + 1 by omega] at hchain
  have hroot := weakHigh_sup_root hθ hfam
  have hXle : X ≤ ENNReal.ofReal ((Cp * Cq) ^ A.Jw) * ENNReal.ofReal (2 * l2NormSq f) := by
    rw [hXdef]
    calc ENNReal.ofReal Cp * (ENNReal.ofReal Cq * weakHighQuietSup s Uhi (x.M + 1))
        ≤ ENNReal.ofReal Cp * (ENNReal.ofReal Cq * ((ENNReal.ofReal Cp * ENNReal.ofReal Cq) ^
            (A.Jw - 1) * ENNReal.ofReal (2 * l2NormSq f))) :=
          mul_le_mul_right (mul_le_mul_right (hchain.trans (mul_le_mul_right hroot _)) _) _
      _ = (ENNReal.ofReal Cp * ENNReal.ofReal Cq) ^ A.Jw * ENNReal.ofReal (2 * l2NormSq f) := by
          obtain ⟨k, hk⟩ : ∃ k, A.Jw = k + 1 := ⟨A.Jw - 1, by omega⟩
          rw [hk, Nat.add_sub_cancel]
          ring
      _ = _ := by rw [← ENNReal.ofReal_mul hCp, ← ENNReal.ofReal_pow (mul_nonneg hCp hCq)]
  have hnn : 0 ≤ ((weakStoredWordBudget A.Nw A.Rw ^ A.Jw : ℕ) : ℝ) + 2 := by positivity
  calc _ ≤ _ := hinner
    _ ≤ ENNReal.ofReal (((weakStoredWordBudget A.Nw A.Rw ^ A.Jw : ℕ) : ℝ) + 2) *
          (ENNReal.ofReal ((Cp * Cq) ^ A.Jw) * ENNReal.ofReal (2 * l2NormSq f)) :=
        (mul_le_mul hc hXle bot_le bot_le)
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hnn]

/-- The strong energy of the reduction `r` is at most that of the families at the reserves. -/
theorem weakHigh_strongEnergy_le_inner (hfam : WeakHigherFamilies s θ r m Uhi Whi) :
    strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M)
        (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) (s.tq (x.M + 1)) (x.a + A.T₀)
        (r.Ur x.M) (r.Urw x.M) ≤
      (∑ v : CompIn (g.stage x.M).comps,
      ENNReal.ofReal (weakMass x.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        ((⨆ t ∈ Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀), ENNReal.ofReal
            (factorialNormSq (x.D.termRStar (plan.radius R) x.M) (Uhi x.M v t).val)) +
          ENNReal.ofReal (x.D.κ x.M) * ∫⁻ τ in Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀),
            ENNReal.ofReal (gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M)
              (Whi x.M v τ).val))) ^ (1 / 2 : ℝ) := by
  unfold strongEnergy
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun v _ => ?_) (by norm_num)
  refine mul_le_mul_right (add_le_add (iSup₂_mono fun t ht => ?_) (mul_le_mul_right ?_ _)) _
  · rw [← hfam.2.2.1 x.M le_rfl (Nat.le_add_right _ _) v t ht]
    exact ENNReal.ofReal_le_ofReal
      (CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ _ _)
  · refine lintegral_mono_ae ?_
    filter_upwards [hfam.2.2.2 x.M le_rfl (by have := A.Jw_pos; omega) v] with τ hτ
    rw [← hτ]
    exact ENNReal.ofReal_le_ofReal
      (CycleComparison.Error.gradFactorialNormSq_truncateTorusHk_le
        (weakReductionReserve_kw_le R m v.1) _ _)

theorem rawEnergy_sqrt_eq (b Q L : ℝ) (J : ℕ) (hb : 0 ≤ b) (hQ : 0 ≤ Q) :
    Real.sqrt (b * (Q ^ J * (2 * L))) =
      Real.sqrt b * Real.sqrt 2 * Real.sqrt Q ^ J * Real.sqrt L := by
  have hpow : Real.sqrt (Q ^ J) = Real.sqrt Q ^ J := by
    rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) J), ← pow_mul, mul_comm, pow_mul,
      Real.sq_sqrt hQ]
  rw [Real.sqrt_mul hb, Real.sqrt_mul (pow_nonneg hQ _), Real.sqrt_mul (by norm_num), hpow]
  ring

theorem weakEntryPassageConst_spec (hA : WeakEntryPassageEnergyStatement plan) (hm : m ≤ weakEntryMmax R) :
    0 ≤ weakEntryPassageConst plan R C m ∧
      WeakEntryPassageEnergyBound plan R C m (weakEntryPassageConst plan R C m) := by
  have h := hA R C m hm
  unfold weakEntryPassageConst
  split_ifs
  exact Classical.choose_spec h

theorem weakEntryQuietConst_spec (hB : WeakEntryQuietTraceHighStatement plan) (hm : m ≤ weakEntryMmax R) :
    0 ≤ weakEntryQuietConst plan R C m ∧
      WeakEntryQuietTraceHighBound plan R C m (weakEntryQuietConst plan R C m) := by
  have h := hB R C m hm
  unfold weakEntryQuietConst
  split_ifs
  exact Classical.choose_spec h

/-- **The raw energy at a general offset `m ≤ m_max(R)`**: the strong energy of the truncated
families of the reduction at the radius `ρ ε_M` is at most `C_raw(R, C, m) ‖f‖₂` (the energy of
`U_M` at the reserves at offset `m`, then truncation). -/
theorem weak_entry_raw_energy_at_offset (hA : WeakEntryPassageEnergyStatement plan)
    (hB : WeakEntryQuietTraceHighStatement plan) (hm : m ≤ weakEntryMmax R)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (hfam : WeakHigherFamilies s θ r m Uhi Whi) :
    strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M)
        (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) (s.tq (x.M + 1)) (x.a + A.T₀)
        (r.Ur x.M) (r.Urw x.M) ≤
      ENNReal.ofReal (weakEntryRawConst plan R C m * Real.sqrt (l2NormSq f)) := by
  obtain ⟨hCp, hAb⟩ := weakEntryPassageConst_spec (C := C) hA hm
  obtain ⟨hCq, hBb⟩ := weakEntryQuietConst_spec (C := C) hB hm
  refine (weakHigh_strongEnergy_le_inner hfam).trans ?_
  refine (ENNReal.rpow_le_rpow (weakHigh_inner_le hCp hCq hAb hBb hθ hfam) (by norm_num)).trans ?_
  have hL : 0 ≤ l2NormSq f := integral_nonneg fun _ => sq_nonneg _
  have hQ := mul_nonneg hCp hCq
  have hb : 0 ≤ ((weakStoredWordBudget A.Nw A.Rw ^ A.Jw : ℕ) : ℝ) + 2 := by positivity
  have hy : 0 ≤ (((weakStoredWordBudget A.Nw A.Rw ^ A.Jw : ℕ) : ℝ) + 2) *
      ((weakEntryPassageConst plan R C m * weakEntryQuietConst plan R C m) ^ A.Jw *
        (2 * l2NormSq f)) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num), ← Real.sqrt_eq_rpow,
    rawEnergy_sqrt_eq _ _ _ _ hb hQ]
  unfold weakEntryRawConst
  exact le_of_eq (by ring_nf)

end Iteration

/-- **The raw energy of the weak entry** from the passage energy and the quiet trace
bound: the iteration at the offset `m = 0`, then truncation. -/
theorem weak_entry_raw_energy_of_ingredients (plan : WeakEntryGluePlan)
    (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryRawEnergyPlanOK plan)
    (hA : WeakEntryPassageEnergyStatement plan) (hB : WeakEntryQuietTraceHighStatement plan) :
    WeakEntryRawEnergyStatement plan := by
  intro B A R C x g s f θ hθ r
  obtain ⟨Uhi, Whi, hfam⟩ := weakReduction_higher_families hcommon s f θ hθ r 0
  refine (weak_entry_raw_energy_at_offset hA hB (Nat.zero_le _) hθ hfam).trans ?_
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have := hok.2.2 R C
  linarith

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **Core of the passage energy, part 3: the energy with data over raw data**.

`weakPassage_core_energy` is the energy of one passage of the reduction system of a
`WeakRawSetting`: for a coupled solution on `[a, b]` of stage `L` (`M ≤ L < M + J_w`) at the
reserves `weakReductionReserve R m` with initial datum `f` and zero forcing, at radius `ρ ε_L`,
```
‖u(t)‖²_{ρε_L,π} + (κ_M/2) ∫_{[a,b]} ‖∇w‖²_{ρε_L,π} ≤ C_pass ‖f‖²_{ρε_L,π},
```
`‖·‖²_{ρ,π} = ∑_v π_v⁻¹ |·_v|²_ρ`, with `C_pass = 2 ∑_{n ≤ J_w R_w} (32 C_R²)^n`
(`weakRawPassageConst`), from the row energy and recursion with data
(`coupledRowData_energy`, `coupledRowData_recursion`) unrolled along the stage paths
(`mass_recursion_unroll`) and summed against the stored-weight total (`weakStoredPath_sum_le`).
The coefficient data `Rd`, the drift data `hd` and the measurability of the coefficients are
hypotheses (they differ in the entry and passage worlds). -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  Construction.Preservation.Ledger CycleJointProofs.PathReduction

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- The passage constant `C_pass = 2 ∑_{n ≤ J_w R_w} (32 C_R²)^n`. -/
def weakRawPassageConst (ρ : ℝ) (R : WeakPassageRequest A) : ℝ :=
  2 * ∑ n ∈ Finset.range (A.Jw * A.Rw + 1), (32 * weakRawEdgeConst ρ R ^ 2) ^ n

theorem weakRawPassageConst_nonneg (ρ : ℝ) (R : WeakPassageRequest A) :
    0 ≤ weakRawPassageConst ρ R := by
  unfold weakRawPassageConst
  positivity

/-- Path sums against a nonnegative function, summed over the end vertex, are at most the sum of
the function, when the stored total is at most one. -/
theorem sum_rowPathSum_le {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D (fun _ => ℝ) Dm bw j₀) (N J : ℕ) (η : ℝ) (hT : weakStoredTotal G N J η ≤ 1)
    (q : CompIn G.comps → ℝ) (hq : ∀ u, 0 ≤ q u) (n : ℕ) :
    ∑ v, rowPathSum (weakStoredEdgeWeight G N J η) q n v ≤ ∑ u, q u := by
  classical
  have hw := weakStoredEdgeWeight_nonneg G N J η
  have h1 : ∑ v, rowPathSum (weakStoredEdgeWeight G N J η) q n v =
      ∑ π : StagePath G (n + 1), pathWeight (weakStoredEdgeWeight G N J η) π * q (π.step 0).2.1 := by
    unfold rowPathSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp
  rw [h1]
  have hqs : ∀ u, q u ≤ ∑ u, q u := fun u =>
    Finset.single_le_sum (f := q) (fun u _ => hq u) (Finset.mem_univ u)
  have hQ0 : 0 ≤ ∑ u, q u := Finset.sum_nonneg fun u _ => hq u
  calc _ ≤ ∑ π : StagePath G (n + 1), pathWeight (weakStoredEdgeWeight G N J η) π * ∑ u, q u :=
        Finset.sum_le_sum fun π _ => mul_le_mul_of_nonneg_left (hqs _)
          (pathWeight_nonneg _ hw π)
    _ = (∑ π : StagePath G (n + 1), pathWeight (weakStoredEdgeWeight G N J η) π) * ∑ u, q u := by
        rw [Finset.sum_mul]
    _ ≤ 1 * ∑ u, q u := by
        refine mul_le_mul_of_nonneg_right ?_ hQ0
        exact (weakStoredPath_sum_le G N J η (n + 1)).trans
          (pow_le_one₀ (weakStoredTotal_nonneg G N J η) hT)
    _ = _ := one_mul _

/-- **Summing the unrolled row recursion**: if every row satisfies
`X_u ≤ φ_u + L ∑_j β_{uj} (π_u/π_j) X_j` along the stored weights, with stored total at most one
and no paths of more than `N` edges, then `∑ X/π ≤ (∑_{n ≤ N} L^n) ∑ φ/π`. -/
theorem sum_unrolled_le {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D (fun _ => ℝ) Dm bw j₀) (Nw J : ℕ) (η : ℝ)
    (hT : weakStoredTotal G Nw J η ≤ 1) (π X φ : CompIn G.comps → ℝ) (hπ : ∀ u, 0 < π u)
    (hX : ∀ u, 0 ≤ X u) (hφ : ∀ u, 0 ≤ φ u) (L : ℝ) (hL : 0 ≤ L)
    (hrec : ∀ u, X u ≤ φ u + L * ∑ j, (∑ γ : G.fam.Γ u j,
      weakStoredEdgeWeight G Nw J η ⟨u, j, γ⟩) * (π u / π j) * X j)
    (N : ℕ) (hN : IsEmpty (StagePath G (N + 1))) :
    ∑ v, X v / π v ≤ (∑ n ∈ Finset.range (N + 1), L ^ n) * ∑ v, φ v / π v := by
  classical
  have hq0 : ∀ v, 0 ≤ φ v / π v := fun v => div_nonneg (hφ v) (hπ v).le
  have hunroll := fun v => mass_recursion_unroll (weakStoredEdgeWeight G Nw J η)
    (weakStoredEdgeWeight_nonneg _ _ _ _) π X φ hπ hX L hL hrec N hN v
  calc ∑ v, X v / π v
      ≤ ∑ v, (φ v / π v + ∑ n ∈ Finset.range N, L ^ (n + 1) *
        rowPathSum (weakStoredEdgeWeight G Nw J η) (fun u => φ u / π u) n v) :=
        Finset.sum_le_sum fun v _ => hunroll v
    _ = ∑ v, φ v / π v + ∑ n ∈ Finset.range N, L ^ (n + 1) *
        ∑ v, rowPathSum (weakStoredEdgeWeight G Nw J η) (fun u => φ u / π u) n v := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ v, φ v / π v + ∑ n ∈ Finset.range N, L ^ (n + 1) * ∑ v, φ v / π v := by
        exact add_le_add le_rfl (Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
          (sum_rowPathSum_le G Nw J η hT (fun u => φ u / π u) hq0 n) (pow_nonneg hL _))
    _ = (∑ n ∈ Finset.range (N + 1), L ^ n) * ∑ v, φ v / π v := by
        rw [Finset.sum_range_succ', ← Finset.sum_mul]
        simp only [pow_zero, pow_succ]
        ring
end

/-! **Core of the passage energy, part 4: the rows of a passage with data**.

For a coupled solution of the reduction system of stage `L` with zero forcing, the row bound
`X_v = 2|f_v|² + rowEnergyBound` of `coupledRowData_energy` dominates the energy of each row
(`weakPassage_core_row_energy`) and satisfies the recursion along the stored weights
(`weakPassage_core_row_recursion`) with the forcing term `2|f_v|²`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs Comparison
  Construction.Preservation.Ledger CycleJointProofs.PathReduction CoupledEnergy.Variational

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}

/-- The forcing terms of a row with zero forcing and zero source reduce to the datum. -/
theorem rowData_phi_zero {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (ν ρ a b : ℝ) (f : TorusHk K E) :
    2 * factorialNormSq ρ f.val + 16 / ν * (∫ _s in Set.Icc a b,
        factorialNormSq ρ (0 : TorusHk K (PiLp 2 (fun _ : Fin 2 => E))).val) +
      10 * (∫ _s in Set.Icc a b, Real.sqrt (factorialNormSq ρ (0 : TorusHk K E).val)) ^ 2 =
    2 * factorialNormSq ρ f.val := by
  simp [CycleComparison.Coarse.factorialNormSq_zero_jet]

/-- **The recursion of the rows of a passage, with data.** -/
theorem weakPassage_core_row_recursion (S : WeakRawSetting R)
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
    (v : CompIn (S.stage L).comps) :
    rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f (rowForcingFlux Rd (fun _ _ => 0) w)
        (fun _ _ => 0) v ≤
      2 * factorialNormSq (rad * S.D.eps L) (f v).val +
        32 * 1 * weakRawEdgeConst rad R ^ 2 * ∑ j, (∑ γ : (S.stage L).fam.Γ v j,
          weakStoredEdgeWeight (S.stage L) A.Nw A.Jw A.η₀ ⟨v, j, γ⟩) *
          (weakMass S.D A.Nw A.Jw A.η₀ v.1 / weakMass S.D A.Nw A.Jw A.η₀ j.1) *
          rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f (rowForcingFlux Rd (fun _ _ => 0) w)
            (fun _ _ => 0) j := by
  have hK : ∀ v : CompIn (S.stage L).comps, weakReductionReserve R m v.1 ≤ weakEntryKmax R :=
    fun v => weakReductionReserve_le_kmax R hm v.1
  have hJN : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  have hF : ∀ v : CompIn (S.stage L).comps, MemLp (fun _ : ℝ => (0 : TorusHk
      (weakReductionReserve R m v.1) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))) 2
      (volume.restrict (Set.Icc a b)) := fun v => memLp_const _
  have hg : ∀ v : CompIn (S.stage L).comps, Integrable (fun _ : ℝ => (0 : TorusHk
      (weakReductionReserve R m v.1) (ScalarH v.1.root))) (volume.restrict (Set.Icc a b)) :=
    fun v => integrable_const _
  have hrec := coupledRowData_recursion (F := fun _ _ => 0) (g := fun _ _ => 0) Rd hd
    S.kappa_pos (by omega : 2 ≤ 1 + A.Jw * A.Nw) hK hab hA_meas hF hg hs
    (fun v : CompIn (S.stage L).comps => weakMass S.D A.Nw A.Jw A.η₀ v.1)
    (fun v => S.mass_pos v.1) (weakRawEdgeConst rad R) 1
    (fun v u => ∑ γ : (S.stage L).fam.Γ v u,
      weakStoredEdgeWeight (S.stage L) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩)
    (fun v u => Finset.sum_nonneg fun γ _ => weakStoredEdgeWeight_nonneg _ _ _ _ _)
    (fun v => weakRaw_storedRow_le S hstored L hL hLJ.le v)
    (fun v u => by
      simp only [hA]
      exact weakRaw_edge_le_stored S hfloor L hL hLJ a b rad hrad hrad1 m hm hsmooth v u) v
  have h0 := rowData_phi_zero (S.D.κ S.M) (rad * S.D.eps L) a b (f v)
  rw [h0] at hrec
  exact hrec

/-- **The energy of a row of a passage, with data.** -/
theorem weakPassage_core_row_energy (S : WeakRawSetting R) (L : ℕ) (a b rad : ℝ) (m : ℕ)
    (hm : m ≤ weakEntryMmax R)
    {Ac : ∀ v u, (d : admissibleOrders
        (fun v : CompIn (S.stage L).comps => weakReductionReserve R m v.1) (1 + A.Jw * A.Nw) v u) →
        ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => ScalarH u.1.root) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)}
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
    (v : CompIn (S.stage L).comps) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    factorialNormSq (rad * S.D.eps L) (u v t).val +
        S.D.κ S.M / 2 * ∫ s in Set.Icc a b, gradFactorialNormSq (rad * S.D.eps L) (w v s).val ≤
      rowDataBound (S.D.κ S.M) (rad * S.D.eps L) a b f (rowForcingFlux Rd (fun _ _ => 0) w)
        (fun _ _ => 0) v := by
  have hK : ∀ v : CompIn (S.stage L).comps, weakReductionReserve R m v.1 ≤ weakEntryKmax R :=
    fun v => weakReductionReserve_le_kmax R hm v.1
  have hJN : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  have hF : ∀ v : CompIn (S.stage L).comps, MemLp (fun _ : ℝ => (0 : TorusHk
      (weakReductionReserve R m v.1) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))) 2
      (volume.restrict (Set.Icc a b)) := fun v => memLp_const _
  have hg : ∀ v : CompIn (S.stage L).comps, Integrable (fun _ : ℝ => (0 : TorusHk
      (weakReductionReserve R m v.1) (ScalarH v.1.root))) (volume.restrict (Set.Icc a b)) :=
    fun v => integrable_const _
  exact coupledRowData_energy (F := fun _ _ => 0) (g := fun _ _ => 0) Rd hd S.kappa_pos
    (by omega : 2 ≤ 1 + A.Jw * A.Nw) hK hA_meas hF hg hs v t ht
end

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Reduction

/-! The quiet trace bound in the passage world: a variable-reserve family agreeing at order zero
with a high-reserve passage run has the same parent-scale quiet trace bound.
The entry corollary supplies this run through the shared higher-reduction lemma. -/

open WeakEntryProofs WeakEntryProofs.Assembly

/-- Passage-generic high-reserve quiet trace. The constant depends only on the
request and the priced passage plan, before the construction and ambient cap.
The only times used are the pinned quiet margin and its middle half, through the two quiet trace layers. -/
theorem weak_passage_quiet_trace_high (pp : WeakPassagePlan)
    (prices : WeakQuietPathPrices)
    (hrows : WeakQuietRowsPlanOK (weakQuietCoefficientPlan pp) prices)
    (hcoeff : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 ≤ (weakQuietCoefficientPlan pp).coeffC R)
    (hscalar : WeakQuietScalarPricesOK (weakQuietCoefficientPlan pp) prices)
    (hprice : WeakQuietMarginPriceStatement (weakQuietCoefficientPlan pp) prices)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance (weakQuietCoefficientPlan pp) R) (r : WeakPassageRun c)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (K : Comp → ℕ) (hK : ∀ v, K v ≤ R.Kw)
    (U : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (K v.1) (ScalarH v.1.root))
    (hzero : ∀ t ∈ Set.Icc (r.tq (i + 1)) (r.tq i), ∀ v,
      truncateTorusHk (Nat.zero_le _) (U v t) =
        truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t))
    (radius : ℝ) (hradius0 : 0 ≤ radius) (hradius : radius ≤ (weakQuietCoefficientPlan pp).radius R) :
    ENNReal.ofReal (massNormSq (radius * c.D.eps (i - 1))
      (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (fun v => (if hv : v.1 ∈ (c.stage i).comps then U ⟨v.1, hv⟩ (r.tq i) else
        (0 : TorusHk (K v.1) (ScalarH v.1.root))).val)) ≤
    ENNReal.ofReal ((max 1 ((weakQuietCoefficientPlan pp).traceC R)) ^ 2) *
      ⨆ t ∈ Set.Icc (r.tq (i + 1)) (r.tq i),
        ENNReal.ofReal (massNormSq 1
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (truncateTorusHk (Nat.zero_le _) (U v t)).val)) := by
  let p := weakQuietCoefficientPlan pp
  have hQ2 : WeakQuietSmoothingStatement p :=
    @weak_quiet_smoothing_of_plan_conditions p prices hrows hcoeff hscalar hprice
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (show 1 ≤ 128 by omega).trans ((p.base_ge B).trans c.base_ge)
  have heps : ∀ j, 0 < c.D.eps j := fun _ => Construction.Stream.ocEpsilon_pos hΛ
  have hmass : ∀ v, 0 ≤ weakMass c.D A.Nw A.Jw A.η₀ v := fun v =>
    (weakMass_pos c.D _ _ _ A.Nw_pos A.Jw_pos heps v).le
  have hwin : WeakQuietWindow c r i := weak_quiet_window c r i hi hit
  have hparent : WeakParentQuietMarginBounds c r i := weak_quiet_coefficient pp c r i hi hit hwin
  have hnonempty : r.tq i ∈ Set.Icc (r.tq (i + 1)) (r.tq i) :=
    ⟨hwin.2.2.1.le, le_rfl⟩
  have hmassEq (t : ℝ) (ht : t ∈ Set.Icc (r.tq (i + 1)) (r.tq i)) :
      weightedNorm (hr := ScalarH) 1
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun _ => 1) (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) =
        Real.sqrt (massNormSq 1
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (truncateTorusHk (Nat.zero_le _) (U v t)).val)) := by
    simp only [weightedNorm, one_pow, div_one]
    apply congrArg Real.sqrt
    exact Finset.sum_congr rfl (fun v _ => congrArg
      (fun z : TorusHk 0 (ScalarH v.1.root) =>
        (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ * factorialNormSq 1 z.val)
      (hzero t ht v).symm)
  have hrestriction := weak_entry_high_trace_restriction ScalarH
    (c.stage i).comps (c.stage (i - 1)).comps K R.Kw hK
    (radius * c.D.eps (i - 1)) (p.radius R * c.D.eps (i - 1))
    (mul_nonneg hradius0 (heps _).le) (mul_le_mul_of_nonneg_right hradius (heps _).le)
    (weakMass c.D A.Nw A.Jw A.η₀) hmass
    (fun v => U v (r.tq i)) (fun v => r.Ur i v (r.tq i)) (hzero _ hnonempty)
  have hnorm : 0 ≤ massNormSq (p.radius R * c.D.eps (i - 1))
      (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (fun v => (r.Ur i v (r.tq i)).val) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.mpr (hmass v.1))
      (factorialNormSq_nonneg _ _)
  refine weak_entry_high_trace_supremum _ _ (max 1 (p.traceC R)) _ _
    hnorm hrestriction (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) ?_
  intro bound hbnd
  have hsmooth := hQ2 c r i hi hit hwin hparent bound (by
    intro t ht
    rw [hmassEq t ht]
    exact hbnd t ht)
  have hbound0 : 0 ≤ bound := (Real.sqrt_nonneg _).trans (hbnd _ hnonempty)
  have hsmooth' := hsmooth.trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 (p.traceC R)) hbound0)
  simp only [weightedNorm, one_pow, div_one] at hsmooth'
  exact hsmooth'

end AVRegularity.Providers.WeakGen.Reduction
end
end
end
