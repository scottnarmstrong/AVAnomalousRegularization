-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.QuietParentPhysicalPrice
public import AVRegularity.EntryWeak.UniformWeakPhysicalCoefficientProduction
public import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
public import AVRegularity.EntryWeakAssembly.Assembly.WeakComparisonEnergyOfIngredients
import AVRegularity.EntryWeakAssembly.PairedForcingCostSchur

/-! Descending Sobolev reserves for the comparison energy `WeakComparisonEnergyStatement`, without
strengthening the order-zero solution supplied by its consumer. The bootstrap
(`WeakComparisonBootstrapStatement`) is an explicit hypothesis. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryWeakProofs
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-- A source spends at most Jw*Nw-1 derivatives; lower-rank components have
larger reserves. This integer does not involve the ambient cap Dm. -/
def weakComparisonReserve {B} {A : WeakCoefficientPhysical B}
    (_R : WeakPassageRequest A) (v : Comp) : ℕ :=
  (A.Jw * A.Rw - weakComponentRank v) * (A.Jw * A.Nw - 1)

/-- Every component reserve fits below the uniform maximum loss. -/
theorem weak_comparison_reserve_le {B} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (v : Comp) :
    weakComparisonReserve R v ≤ A.Jw * A.Rw * (A.Jw * A.Nw - 1) :=
  Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- Every actual edge is admissible at every retained source order under the
strict-rank reserve schedule. No derivative allowance is charged to Dm. -/
theorem weak_comparison_edge_admissible {plan : WeakPassagePlan} {B}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
    (d : ℕ) (hd : 2 ≤ d) (hdmax : d ≤ 1 + A.Jw * A.Nw) :
    d ∈ admissibleOrders (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1)
      (1 + A.Jw * A.Nw) v u := by
  obtain ⟨hr, he⟩ := weakConstruction_rank_bounds c.P _ c.M A.Jw 0 _ c.stage c.construction
    i (by omega) hit
  have hruv := he v u γ
  have hrv : weakComponentRank v.1 ≤ A.Jw * A.Rw :=
    (hr v.1 v.2).trans (Nat.mul_le_mul_right A.Rw (by omega))
  have hrem : A.Jw * A.Rw - weakComponentRank v.1 + 1 ≤
      A.Jw * A.Rw - weakComponentRank u.1 := by omega
  have hmul := Nat.mul_le_mul_right (A.Jw * A.Nw - 1) hrem
  rw [Nat.add_mul, Nat.one_mul] at hmul
  have hprod : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hd, hdmax⟩, ?_⟩
  dsimp only [weakComparisonReserve]
  omega

/-- Orders above the uniform weak cap have exactly zero physical coefficients,
including when the ambient cap Dm is larger. -/
theorem weak_comparison_physCoeff_zero_above {plan : WeakPassagePlan} {B}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u)
    (d : ℕ) (hd : 1 + A.Jw * A.Nw < d) :
    (c.stage i).physCoeff v u γ d = fun _ _ => 0 := by
  by_cases heq : i = c.M + A.Jw
  · subst i
    exact ((c.construction.2.1.2.2.1 v u).false γ).elim
  have ho := weakConstruction_output_maxOrder_bound c.P _ c.M A.Jw _ 0 c.stage
    c.construction i (by omega) (by omega) v u γ
  have hord : ((c.stage i).fam.identity v u γ).maxOrder < d := ho.trans_lt hd
  funext t x
  exact CycleJointProofs.constituentPhysical_zero_above_max (c.stage i).fam _ _ _
    (c.stage i).actual v u γ d hord t x

/-- Actual numerical condition required by the descending reserve schedule. -/
def WeakComparisonReservePlanOK (plan : WeakPassagePlan) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    A.Jw * A.Rw * (A.Jw * A.Nw - 1) + 1 ≤ plan.forcingOrder R

/-- Sum the original identities at an admissible heterogeneous order. The maps
are scalar identity maps, as certified by the weak construction. -/
def weakComparisonDescendingCoeff {plan : WeakPassagePlan} {B}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ)
    (v u : CompIn (c.stage i).comps)
    (d : admissibleOrders (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1)
      (1 + A.Jw * A.Nw) v u) (t : ℝ) (x : Vec 2) :=
  ∑ γ : (c.stage i).fam.Γ v u, (c.stage i).physCoeff v u γ d.1 t x

/-- A sufficiently regular representative of the supplied solution, with the
same values at every closed-window time and the same gradients almost everywhere.
The input forcing is unchanged, only truncated to each component's reserve. -/
structure WeakComparisonDescendingSolution {plan : WeakPassagePlan} {B}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {c : WeakPassageInstance plan R} {r : WeakPassageRun c} {i : ℕ}
    (hplan : WeakComparisonReservePlanOK plan) (h : WeakComparisonEnergyInput r i) where
  e : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (weakComparisonReserve R v.1) (ScalarH v.1.root)
  ew : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (weakComparisonReserve R v.1 + 1) (ScalarH v.1.root)
  values : ∀ v t, t ∈ Set.Icc (r.tq i) (r.a + A.T₀) →
    truncateTorusHk (Nat.zero_le _) (e v t) = h.e v t
  gradients : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)),
    truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (ew v t) = h.ew v t
  solution : IsCoupledWeakSolutionTorus (c.D.κ c.M) (r.tq i) (r.a + A.T₀)
    (streamVel (c.D.Φ i)) (1 + A.Jw * A.Nw)
    (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1)
    (weakComparisonDescendingCoeff c i) (fun _ => 0)
    (fun v t => truncateTorusHk ((weak_comparison_reserve_le R v.1).trans
      ((Nat.le_succ _).trans (hplan R))) (h.F v t))
    (fun v t => truncateTorusHk ((weak_comparison_reserve_le R v.1).trans
      ((Nat.le_succ _).trans (hplan R))) (h.g v t)) e ew

/-- The level threshold of the weak flux production and of the record-size coefficient
seminorms at the largest reserve of the comparison energy `J_w R_w (J_w N_w - 1)`. It depends on the
request only through `s_Z`. -/
def weakComparisonCoeffFloor {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : ℕ :=
  if hΛ : 128 ≤ A.Λ then
    max (Classical.choose (Classical.choose_spec
        (uniform_weak_construction_flux_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
          A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
          (A.Jw * A.Rw * (A.Jw * A.Nw - 1)) A.Jw_pos)).2)
      (Classical.choose (Classical.choose_spec
        (uniform_weak_physical_coefficient_production B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
          A.Λ hΛ B.ζ B.hζ A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw R.sZ
          (A.Jw * A.Rw * (A.Jw * A.Nw - 1)) A.Jw_pos)).2)
  else 0

/-- Plan condition of the bootstrap: the level floor dominates the coefficient threshold. -/
def WeakComparisonCoeffPlanOK (plan : WeakPassagePlan) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ),
    weakComparisonCoeffFloor R ≤ plan.levelFloor R j₀

/-- The level threshold of the Péclet smallness `ε_m^{1+α} ≤ θ κ_M` (`m > M`) at
`θ = 1/(8192 (C + 1))`, `C` the drift jet constant: the actual stream drift satisfies the
drift hypotheses of `coupled_energy_torus` at radius `ρ ε_i` for `ρ ≤ 1/2048`. -/
def weakComparisonDriftFloor {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  if hΛ : 128 ≤ A.Λ then
    Classical.choose (weak_peclet_eventually_small B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ hΛ
      (1 / (8192 * (Construction.Preservation.Buffer.actualDriftJetConstant + 1)))
      (by have := Construction.Preservation.Buffer.actualDriftJetConstant_nonneg; positivity))
  else 0

/-- Plan conditions of the descending rows: the coefficient floor, the drift
floor, the whole-stage stored-ledger floor (`weakQuietStoredFloor`), and the radius. -/
def WeakComparisonRowsPlanOK (plan : WeakPassagePlan) : Prop :=
  WeakComparisonCoeffPlanOK plan ∧
  (∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ),
    weakComparisonDriftFloor A ≤ plan.levelFloor R j₀ ∧
      weakQuietStoredFloor A ≤ plan.levelFloor R j₀) ∧
  ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A), plan.radius R ≤ 1 / 2048

/-- The regularity step, stated only when all finite-reserve forcing costs are
finite. Its conclusion concerns the given solution, not a newly assumed one. The coefficient
plan condition gives the finite coefficient seminorms. -/
def WeakComparisonBootstrapStatement (plan : WeakPassagePlan)
    (hplan : WeakComparisonReservePlanOK plan) : Prop :=
  WeakComparisonCoeffPlanOK plan →
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonEnergyInput r i,
    (∀ v, weakComparisonRowForcing h v ≠ ⊤) →
    Nonempty (WeakComparisonDescendingSolution hplan h)

/-- Forced row recursion after the regularity step, with the original record
kernel and the original component suprema. This does not identify quiet margin b with
record weights. -/
def WeakComparisonDescendingRowsStatement (plan : WeakPassagePlan)
    (hplan : WeakComparisonReservePlanOK plan) (prices : WeakQuietPathPrices) : Prop :=
  WeakComparisonRowsPlanOK plan →
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonEnergyInput r i,
    (∀ v, weakComparisonRowForcing h v ≠ ⊤) →
    WeakComparisonDescendingSolution hplan h →
    ∀ v, weakComparisonRowEnergy h v ≤
      ∑ u, ENNReal.ofReal (weakQuietPathKernel prices c i v u) * weakComparisonRowForcing h u

/-- `WeakComparisonEnergyStatement` from a bootstrap of its order-zero solution and the subsequent
finite-reserve row estimates. Infinite total forcing needs no regularity claim. -/
theorem weak_comparison_energy_of_descending_ingredients (plan : WeakPassagePlan)
    (hplan : WeakComparisonReservePlanOK plan) (prices : WeakQuietPathPrices)
    (hpositive : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A), 0 < plan.energyC R)
    (hrowsOK : WeakComparisonRowsPlanOK plan)
    (hbootstrap : WeakComparisonBootstrapStatement plan hplan)
    (hrows : WeakComparisonDescendingRowsStatement plan hplan prices)
    (hprice : WeakComparisonPathPriceStatement plan prices) : WeakComparisonEnergyStatement plan := by
  classical
  intro B A R c r i hi hit F g e ew Y hFm hgm hsol
  let h : WeakComparisonEnergyInput r i := ⟨F, g, e, ew, Y, hFm, hgm, hsol⟩
  by_cases hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤
  · obtain ⟨hd⟩ := hbootstrap hrowsOK.1 c r i hi hit h hf
    obtain ⟨hK, _, _, hcol⟩ := weak_quiet_path_schur plan prices c i
    have hb := hprice (fun R j₀ => (hrowsOK.2.1 R j₀).2) c i hi hit
    have htotal : (∑ v, weakComparisonRowEnergy h v) ≤
        ENNReal.ofReal (plan.energyC R ^ 2) * ∑ u, weakComparisonRowForcing h u :=
      (Finset.sum_le_sum fun v _ => hrows hrowsOK c r i hi hit h hf hd v).trans
        (comparison_column_sum _ _ _ hK (fun u => (hcol u).trans hb))
    have hroot := ENNReal.rpow_le_rpow htotal (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))] at hroot
    have hC : (ENNReal.ofReal (plan.energyC R ^ 2)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (plan.energyC R) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
        ← Real.sqrt_eq_rpow, Real.sqrt_sq (plan.energyC_nonneg R)]
    rw [hC] at hroot
    have hΛ : 1 ≤ c.D.Λ := by
      rw [c.base_eq]
      exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
    have hπ : ∀ v : CompIn (c.stage i).comps, 0 < weakMass c.D A.Nw A.Jw A.η₀ v.1 :=
      fun v => weakMass_pos c.D _ _ _ A.Nw_pos A.Jw_pos
        (fun _ => Construction.Stream.ocEpsilon_pos hΛ) v.1
    have hinv : ∀ v : CompIn (c.stage i).comps,
        ENNReal.ofReal ((weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹) =
          (ENNReal.ofReal (weakMass c.D A.Nw A.Jw A.η₀ v.1))⁻¹ :=
      fun v => ENNReal.ofReal_inv_of_pos (hπ v)
    simpa only [strongEnergy, hinv, weakComparisonRowEnergy, weakComparisonForcingCost,
      weakComparisonRowForcing, h] using hroot
  · obtain ⟨v, hv⟩ := not_forall.mp hf
    have hvtop : weakComparisonRowForcing h v = ⊤ := not_ne_iff.mp hv
    have htop : (∑ u, weakComparisonRowForcing h u) = ⊤ := by
      apply top_unique
      rw [← hvtop]
      exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ v)
    change _ ≤ ENNReal.ofReal (plan.energyC R) * (∑ u, weakComparisonRowForcing h u) ^ (1 / 2 : ℝ)
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num : 0 < (1 / 2 : ℝ)),
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (hpositive R)))]
    exact le_top

end AVRegularity.WeakEntryProofs.Assembly
