-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.QuietParentSlowJets

/-! Forced triangular comparison energy. Every row's supremum is retained
before summation. The analytic ingredient keeps a finite spatial forcing reserve. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-- Literal forced solution objects of the comparison energy, bundled without additional
estimates. -/
structure WeakComparisonEnergyInput {plan : WeakPassagePlan} {B} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} {c : WeakPassageInstance plan R} (r : WeakPassageRun c) (i : ℕ) where
  F : ∀ v : CompIn (c.stage i).comps, ℝ →
    TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
  g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root)
  e : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root)
  ew : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 1 (ScalarH v.1.root)
  Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)
  F_meas : ∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))
  g_meas : ∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))
  solution : WeakErrSol c r i (fun _ => 0)
    (fun v t => truncateTorusHk (Nat.zero_le _) (F v t))
    (fun v t => truncateTorusHk (Nat.zero_le _) (g v t)) e ew Y

/-- The inverse-mass component energy, with the component's own time supremum. -/
def weakComparisonRowEnergy {plan : WeakPassagePlan} {B} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} {c : WeakPassageInstance plan R} {r : WeakPassageRun c}
    {i : ℕ} (h : WeakComparisonEnergyInput r i) (v : CompIn (c.stage i).comps) : ℝ≥0∞ :=
  (ENNReal.ofReal (weakMass c.D A.Nw A.Jw A.η₀ v.1))⁻¹ *
    ((⨆ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ENNReal.ofReal (factorialNormSq 1 (h.e v t).val)) +
      ENNReal.ofReal (c.D.κ c.M) * ∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀),
        ENNReal.ofReal (gradFactorialNormSq 1 (h.ew v t).val))

/-- Each component's forcing cost keeps its own L1-in-time scalar term before
squaring. Its finite reserve is the one selected by the passage plan before Dm. -/
def weakComparisonRowForcing {plan : WeakPassagePlan} {B} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} {c : WeakPassageInstance plan R} {r : WeakPassageRun c}
    {i : ℕ} (h : WeakComparisonEnergyInput r i) (v : CompIn (c.stage i).comps) : ℝ≥0∞ :=
  (ENNReal.ofReal (weakMass c.D A.Nw A.Jw A.η₀ v.1))⁻¹ *
    ((ENNReal.ofReal (c.D.κ c.M))⁻¹ *
      (∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀),
        ENNReal.ofReal (factorialNormSq (plan.radius R * c.D.eps i) (h.F v t).val)) +
      (∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀),
        ENNReal.ofReal (Real.sqrt (factorialNormSq (plan.radius R * c.D.eps i) (h.g v t).val))) ^ 2)

/-- The whole-stage stored-ledger floor of the passage plan (`weakQuietStoredFloor`):
every passage stage then has stored total at most one. -/
def WeakComparisonStoredPlanOK (plan : WeakPassagePlan) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ),
    weakQuietStoredFloor A ≤ plan.levelFloor R j₀

/-- Common-plan domination of the squared energy price. These may be different
scalar path prices from the quiet smoothing prices. The path cost involves the stored totals of
the stage, which the stored floor bounds. -/
def WeakComparisonPathPriceStatement (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : Prop :=
  WeakComparisonStoredPlanOK plan →
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ), c.M < i → i ≤ c.M + A.Jw →
    weakQuietPathCost prices c i ≤ plan.energyC R ^ 2

/-- Finite column summation, valid also for infinite forcing integrals. -/
def ComparisonColumnSumStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] (K : ι → ι → ℝ) (q : ι → ℝ≥0∞) (C : ℝ),
    (∀ v u, 0 ≤ K v u) → (∀ u, ∑ v, K v u ≤ C) →
    (∑ v, ∑ u, ENNReal.ofReal (K v u) * q u) ≤ ENNReal.ofReal C * ∑ u, q u

end AVRegularity.WeakEntryProofs.Assembly
