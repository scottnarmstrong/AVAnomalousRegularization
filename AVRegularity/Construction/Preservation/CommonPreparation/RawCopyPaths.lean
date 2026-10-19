-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.PlainNeutralEnergyPaths
import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleComparison.Error.Main
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual selected positive plain path and the SAME scalar kernel response
satisfy the two physical rows used by the kernel-defect estimate. The source
uses the actual preceding-copy higher lift and its unchanged ambient class.

The degenerate cases are included: depth zero has no positive step. Empty and singleton families,
zero/constants, D=2, identity geometry, edgeless seeds and degenerate windows use the same
identities. No extra integrability premise or mass-specific response is chosen. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul
  preparationWeightedLowSMul preparationWeightedLowSpace
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D H Kbase : ℕ} {Part : Type*} {Ctx : Part → Type*}
  {a b ρ ν : ℝ} {family : ChartedFamily ι h D Part Ctx}
  {Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
    (G := fun _ j _ => h j) a b ρ ν 0 D}

/-- The selected paths retain the actual plain row, actual kernel row and
SAME response higher class, precisely at the preceding-copy moment reserve. -/
def NeutralSelectedStepRowsStatement
    (F : PreparationPlainKernelFrame Q) (l : Fin H)
    (hK : ∀ j, F.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (e E : ℝ) (actual : ∀ p, Ctx p) (v : ℝ → Vec 2 → Vec 2)
    (J : CoupledHighTime (h := h) (fun _ => 0) a b →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b a) : Prop :=
  ∀ (f : ∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i))
    (u : ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1))
    (W : ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y + 1) (h y.1)),
    IsCoupledWeakSolutionTorus ν a b v D (preparationNeutralSlots H D Kbase)
      (edgeCoefficient (preparationNeutralChain family H) ν e E actual
        (preparationNeutralSlots H D Kbase))
      (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) f)
      (fun _ _ => 0) (fun _ _ => 0) u W →
  ∀ (zp zprev : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b a),
    (∀ t : Set.Icc a b, zp.1 t = fun i =>
      truncateTorusHk (Nat.zero_le _) (u (i, l.succ) t)) →
    (zprev.2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i =>
        truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l.castSucc) t))) →
    (∀ i, IsTorusForcedRow ν a b v 2 0 0
      (F.rows.plainSourceFluxTime (preparationNeutralPrecedingInput F l hK W) i)
      (fun _ => 0) (fun t => zp.1 (Set.projIcc a b Q.htime t) i)
      (fun t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l.succ) t))) ∧
    ∃ Z : ∀ i, ℝ → TorusHk 1 (h i),
      (∀ i, IsTorusForcedRow ν a b v 2 0 0
        (Q.carrierFlux (fun j t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (F.K j)))
          (preparationNeutralPrecedingInput F l hK W j t)) i)
        (fun _ => 0) (fun t => (J zprev.2).1 (Set.projIcc a b Q.htime t) i) (Z i)) ∧
      ((J zprev.2).2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        coupledCarrierHighJets (fun _ => 0) (fun i => Z i t))

/-- The actual weak equation and already realized scalar response discharge
both row identities, with no additional PDE or integrability input. -/
theorem neutral_selected_step_rows
    (F : PreparationPlainKernelFrame Q) (l : Fin H)
    (hK : ∀ j, F.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hB : ∀ i j γ d, Q.B i j γ d = constituentPhysical family ν e E actual i j γ d.val)
    (hC : ∀ i j γ, Q.C i j γ = ContinuousLinearMap.id ℝ (h j))
    (v : ℝ → Vec 2 → Vec 2)
    (J : CoupledHighTime (h := h) (fun _ => 0) a b →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b a)
    (hJ : ScalarFamilyEnergyPathRealizes (ν := ν) Q.htime v (preparationKernelScalarDatum Q) J) :
    NeutralSelectedStepRowsStatement F l hK e E actual v J := by
  intro f u W hs zp zprev hnext hprev
  have hp (i : ι) := preparation_neutral_positive_plain_row F l hK e E actual hB hC f hs i
  have hplain (i : ι) := preparation_scalar_trace_congr (E := h i) Q.htime (hp i)
    (u' := fun t => zp.1 (Set.projIcc a b Q.htime t) i)
    (fun t ht => by
      rw [Set.projIcc_of_mem Q.htime ht]
      exact congrFun (hnext ⟨t, ht⟩) i)
  let V := preparationNeutralPrecedingInput F l hK W
  let Vlo := fun j t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (F.K j))) (V j t)
  have hl (j : ι) (t : ℝ) : Vlo j t =
      truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (j, l.castSucc) t) := by
    apply TorusHk.ext_value
    rfl
  have hgraph : zprev.2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun j => Vlo j t) := by
    filter_upwards [hprev] with t ht
    exact ht.trans (congrArg (coupledCarrierHighJets (h := h) (fun _ => 0))
      (funext fun j => (hl j t).symm))
  have hresponse := kernel_response_actual_rows Q (v := v) J hJ zprev.2 Vlo hgraph
  exact ⟨hplain, hresponse.2.2⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Read the genuine full-window copied evolution into the same continuous
low trace and ambient higher class, without a whole-window chart frame.
Only copy zero contains the higher buffered datum. The linear maps precede
weights and data. The degenerate cases are included: H=0, empty and singleton families, D=2, a point
window, zero/constants, identity geometry and an edgeless seed retain the actual
weak equation and its every-time integrability. No energy price is assumed. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationNeutralEnergyAdd
  preparationNeutralEnergyMonoid preparationNeutralEnergyModule
  preparationPlainNativeModule preparationPlainCarrierSMul preparationPlainFamilySMul
  preparationNeutralSlotsMonoid preparationNeutralSlotsModule preparationNeutralTraceModule
  preparationNeutralContinuousMonoid

/-- Select the injected copy solution and all copy paths from the same
actual linear evolution and its genuine higher Sobolev lifts. -/
def RawCopiedEnergyPathsStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (H D Kmax : ℕ) (K : ι × Fin (H + 1) → ℕ), 2 ≤ D → (∀ v, K v ≤ Kmax) →
  ∀ (ν ρ a b : ℝ) (v : ℝ → Vec 2 → Vec 2), 0 < ν → 0 < ρ → a ≤ b →
    Providers.WeakGen.Comparison.TorusDriftData ν ρ a b v Kmax →
  ∀ A : ∀ x y : ι × Fin (H + 1), (d : admissibleOrders K D x y) → ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h y.1)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h x.1)),
    (∀ x y d, coefficientSeminorm ρ (K x) a b (A x y d) ≠ ⊤) →
    (∀ x y d, Measurable (fun p : Set.Icc a b × Vec 2 => A x y d p.1 p.2)) →
    (∀ x y d t, t ∈ Set.Icc a b → ContDiff ℝ (K x : ℕ) (A x y d t)) →
    (∀ x y d t, t ∈ Set.Icc a b → IsZ2Periodic (A x y d t)) →
    (∀ x y d, x.2.val ≠ y.2.val + 1 → ∀ t ∈ Set.Icc a b, A x y d t = 0) →
  ∃ L : (∀ i : ι, TorusHk (K (i, 0)) (h i)) →ₗ[ℝ]
      (∀ x : ι × Fin (H + 1), ℝ → TorusHk (K x) (h x.1)),
  ∃ E : Fin (H + 1) → (∀ i : ι, TorusHk (K (i, 0)) (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b a,
    ∀ f, ∃ W : ∀ x : ι × Fin (H + 1), ℝ → TorusHk (K x + 1) (h x.1),
      IsCoupledWeakSolutionTorus ν a b v D K A (preparationNeutralInitial H K f)
        (fun _ _ => 0) (fun _ _ => 0) (L f) W ∧
      (∀ l, ∀ t : Set.Icc a b, (E l f).1 t =
        fun i => truncateTorusHk (Nat.zero_le (K (i, l))) (L f (i, l) t)) ∧
      (∀ l, (E l f).2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        coupledCarrierHighJets (fun _ => 0) (fun i =>
          truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, l)))) (W (i, l) t)))
end

/-! **`RawCopiedEnergyPathsStatement` from the descending copied evolution**. From `DescendingCopyLinearEvolutionStatement` (one linear genuine weak evolution
`L` of the whole copied family on the full window, with genuine higher lifts `W`):
- the higher buffered datum is injected into copy zero by `J = preparationNeutralInitial`, before
  the datum: the selected solution is `L ∘ J`;
- the energy path of copy `l` is read from the SAME evolution and the SAME lifts: its continuous low
  trace is the truncation of copy `l` of `L (J f)` (`preparation_native_continuous_trace`), and its
  higher class is the class of the higher jets of copy `l` of `W (J f)`, linear by the injective-lift
  argument (`preparation_native_higher_time_class`). This is the copy projection of the whole
  family's path, built directly on each copy.

No chart frame and no energy bound enter.

For `H = 0` there is one copy; zero data give zero paths, and an edgeless seed has all
coefficients zero. In every such degenerate case (including a point window `a = b`) the
equation and the maps are the same. -/

section
universe u v

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationPlainNativeModule preparationPlainCarrierSMul
  preparationPlainFamilySMul

section Copies

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **The energy path of a linear low trace with genuine lifts**: the continuous trace and the
higher class of the SAME lifts, linear in the datum. -/
theorem raw_energy_path_of_trace {X : Type*} [AddCommGroup X] [Module ℝ X] {a b : ℝ}
    (L₀ : X →ₗ[ℝ] (∀ i, ℝ → TorusHk 0 (h i)))
    (hc : ∀ f i, ContinuousOn (L₀ f i) (Set.Icc a b))
    (W₀ : X → ∀ i, ℝ → TorusHk 1 (h i))
    (hm : ∀ f i, MemLp (W₀ f i) 2 (volume.restrict (Set.Icc a b)))
    (ha : ∀ f i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncateTorusHk (Nat.zero_le 1) (W₀ f i t) = L₀ f i t) :
    ∃ E : X →ₗ[ℝ] PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b a,
      ∀ f, (∀ t : Set.Icc a b, (E f).1 t = fun i => L₀ f i t) ∧
        ((E f).2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
          coupledCarrierHighJets (fun _ => 0) (fun i => W₀ f i t)) := by
  obtain ⟨B, hB⟩ := preparation_native_higher_time_class a b L₀ W₀ hm ha
  exact ⟨(preparation_native_continuous_trace L₀ hc).prod B, fun f => ⟨fun _ => rfl, hB f⟩⟩

variable {H : ℕ}

/-- The truncated low trace of copy `l` of a linear evolution of the whole copied family. -/
def RawCopyTrace {X : Type*} [AddCommGroup X] [Module ℝ X] (K : ι × Fin (H + 1) → ℕ)
    (l : Fin (H + 1)) (L : X →ₗ[ℝ] (∀ x : ι × Fin (H + 1), ℝ → TorusHk (K x) (h x.1))) :
    X →ₗ[ℝ] (∀ i, ℝ → TorusHk 0 (h i)) :=
  LinearMap.pi fun i =>
    ((truncateTorusHk (E := h (i, l).1) (Nat.zero_le (K (i, l)))).toLinearMap.compLeft ℝ).comp
      ((LinearMap.proj (R := ℝ) (φ := fun x : ι × Fin (H + 1) => ℝ → TorusHk (K x) (h x.1))
        (i, l)).comp L)

section CopyFacts

variable {X : Type*} [AddCommGroup X] [Module ℝ X]
  {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι × Fin (H + 1) → ℕ}
  {A : ∀ (x y : ι × Fin (H + 1)) (d : admissibleOrders K D x y), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h y.1)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h x.1))}
  (J : X → ∀ x : ι × Fin (H + 1), TorusHk (K x) (h x.1))
  (L : X →ₗ[ℝ] (∀ x : ι × Fin (H + 1), ℝ → TorusHk (K x) (h x.1)))
  (W : X → ∀ x : ι × Fin (H + 1), ℝ → TorusHk (K x + 1) (h x.1))

/-- The low trace of copy `l` is continuous on the window. -/
theorem raw_copy_continuous
    (hs : ∀ f, IsCoupledWeakSolutionTorus ν a b v D K A (J f) (fun _ _ => 0) (fun _ _ => 0)
      (L f) (W f)) (l : Fin (H + 1)) :
    ∀ f i, ContinuousOn (RawCopyTrace K l L f i) (Set.Icc a b) := fun f i =>
  (truncateTorusHk (E := h (i, l).1) (Nat.zero_le (K (i, l)))).continuous.comp_continuousOn
    ((hs f).1 (i, l) : _)

/-- The truncated lifts of copy `l` are square integrable on the window. -/
theorem raw_copy_memLp
    (hs : ∀ f, IsCoupledWeakSolutionTorus ν a b v D K A (J f) (fun _ _ => 0) (fun _ _ => 0)
      (L f) (W f)) (l : Fin (H + 1)) :
    ∀ f i, MemLp (fun t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, l))))
      (W f (i, l) t)) 2 (volume.restrict (Set.Icc a b)) := fun f i =>
  (truncateTorusHk (E := h (i, l).1) (Nat.succ_le_succ (Nat.zero_le (K (i, l))))).comp_memLp'
    ((hs f).2.1 (i, l) : _)

/-- The truncated lifts of copy `l` restrict to its low trace almost everywhere. -/
theorem raw_copy_lift_trace
    (hs : ∀ f, IsCoupledWeakSolutionTorus ν a b v D K A (J f) (fun _ _ => 0) (fun _ _ => 0)
      (L f) (W f)) (l : Fin (H + 1)) :
    ∀ f i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncateTorusHk (Nat.zero_le 1)
        (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, l)))) (W f (i, l) t)) =
        RawCopyTrace K l L f i t := by
  intro f i
  filter_upwards [(hs f).2.2.1 (i, l)] with t ht
  change truncateTorusHk (Nat.zero_le 1)
    (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, l)))) (W f (i, l) t)) =
    truncateTorusHk (Nat.zero_le (K (i, l))) (L f (i, l) t)
  have he := congrArg (truncateTorusHk (E := h (i, l).1) (Nat.zero_le (K (i, l)))) ht
  have hcomp : truncateTorusHk (Nat.zero_le 1)
      (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, l)))) (W f (i, l) t)) =
      truncateTorusHk (Nat.zero_le (K (i, l)))
        (truncateTorusHk (Nat.le_succ (K (i, l))) (W f (i, l) t)) := by
    apply TorusHk.ext_value
    rfl
  exact hcomp.trans he

/-- **The energy path of copy `l`** of a linear evolution of the whole copied family, from the
SAME lifts. -/
theorem raw_copy_energy_path
    (hs : ∀ f, IsCoupledWeakSolutionTorus ν a b v D K A (J f) (fun _ _ => 0) (fun _ _ => 0)
      (L f) (W f)) (l : Fin (H + 1)) :
    ∃ E : X →ₗ[ℝ] PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b a,
      ∀ f, (∀ t : Set.Icc a b, (E f).1 t =
          fun i => truncateTorusHk (Nat.zero_le (K (i, l))) (L f (i, l) t)) ∧
        ((E f).2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
          coupledCarrierHighJets (fun _ => 0) (fun i =>
            truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, l)))) (W f (i, l) t))) :=
  raw_energy_path_of_trace (RawCopyTrace K l L) (raw_copy_continuous J L W hs l)
    (fun f i t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, l)))) (W f (i, l) t))
    (raw_copy_memLp J L W hs l) (raw_copy_lift_trace J L W hs l)

end CopyFacts

end Copies

/-- **`RawCopiedEnergyPathsStatement` from the descending copied evolution.** -/
theorem rawCopiedEnergyPaths_of_descending
    (hdesc : DescendingCopyLinearEvolutionStatement.{u, v}) :
    RawCopiedEnergyPathsStatement.{u, v} := by
  intro ι _ _ h _ _ _ _ _ _ H D Kmax K hD hK ν ρ a b v hν hρ hab hv A hA₁ hA₂ hA₃ hA₄ hA₅
  have hd := hdesc H D Kmax K hD hK ν ρ a b v hν hρ hab hv A hA₁ hA₂ hA₃ hA₄ hA₅
  obtain ⟨L, hL⟩ := hd
  have hL' : ∀ f : (∀ i, TorusHk (K (i, 0)) (h i)), ∃ W : ∀ x : ι × Fin (H + 1), ℝ →
      TorusHk (K x + 1) (h x.1),
      IsCoupledWeakSolutionTorus ν a b v D K A (preparationNeutralInitial H K f)
        (fun _ _ => 0) (fun _ _ => 0) (L.comp (preparationNeutralInitial H K) f) W :=
    fun f => hL (preparationNeutralInitial H K f)
  choose W hs using hL'
  choose E hE using raw_copy_energy_path (preparationNeutralInitial H K)
    (L.comp (preparationNeutralInitial H K)) W hs
  exact ⟨L.comp (preparationNeutralInitial H K), E,
    fun f => ⟨W f, hs f, fun l => (hE l f).1, fun l => (hE l f).2⟩⟩
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Selection and truncation of the same raw higher lift, with the exact
rank-loss dissipation and its moment-price square-root conversion. No
physical/chart regularity is introduced by these norm comparisons. -/

open CycleComparison.Error
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A selected copy's truncated gradient has no greater mass than the
full copied gradient at the original masses. -/
theorem raw_copy_gradient_le {H : ℕ}
    (Kc : ι × Fin (H + 1) → ℕ) (K : ι → ℕ) (l : Fin (H + 1))
    (hK : ∀ j, K j ≤ Kc (j, l)) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (W : ∀ x, ℝ → TorusHk (Kc x + 1) (h x.1)) (t : ℝ) :
    massGradNormSq ρ π (fun j => (preparationPlainCopyHigh Kc K l hK W j t).val) ≤
      massGradNormSq ρ (fun x => π x.1) (fun x => (W x t).val) := by
  classical
  let g := fun x : ι × Fin (H + 1) =>
    (π x.1)⁻¹ * gradFactorialNormSq ρ (W x t).val
  have hg (x : ι × Fin (H + 1)) : 0 ≤ g x :=
    mul_nonneg (inv_nonneg.mpr (hπ x.1).le)
      (CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _)
  have hs : (∑ j, g (j, l)) ≤ ∑ x, g x := by
    rw [Fintype.sum_prod_type_right]
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun j _ => hg (j, k))
      (Finset.mem_univ l)
  unfold massGradNormSq
  apply le_trans ?_ hs
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (gradFactorialNormSq_truncateTorusHk_le (hK j) ρ (W (j, l) t))
    (inv_nonneg.mpr (hπ j).le)

/-- Raw full-slot energy implies the selected-copy dissipation, without
assuming a separate integrability or chart certificate. -/
theorem raw_copy_dissipation {H : ℕ}
    (Kc : ι × Fin (H + 1) → ℕ) (K : ι → ℕ) (l : Fin (H + 1))
    (hK : ∀ j, K j ≤ Kc (j, l)) (ρ ν a b L : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (hν : 0 < ν)
    (f u : ∀ x, TorusHk (Kc x) (h x.1))
    (W : ∀ x, ℝ → TorusHk (Kc x + 1) (h x.1))
    (hW : ∀ x, MemLp (W x) 2 (volume.restrict (Set.Icc a b)))
    (he : massNormSq ρ (fun x => π x.1) (fun x => (u x).val) +
      ν / 2 * ∫ t in Set.Icc a b, massGradNormSq ρ (fun x => π x.1)
        (fun x => (W x t).val) ≤
      (2 * L ^ (2 * H)) * massNormSq ρ (fun x => π x.1) (fun x => (f x).val)) :
    ν * (∫ t in Set.Icc a b,
      massGradNormSq ρ π (fun j => (preparationPlainCopyHigh Kc K l hK W j t).val)) ≤
      (4 * L ^ (2 * H)) * massNormSq ρ (fun x => π x.1) (fun x => (f x).val) := by
  let V := preparationPlainCopyHigh Kc K l hK W
  have hV : ∀ j, MemLp (V j) 2 (volume.restrict (Set.Icc a b)) :=
    fun j => truncate_memLp (Nat.succ_le_succ (hK j)) (hW (j, l))
  have hi := integral_mono (integrable_massGradNormSq ρ π V hV)
    (integrable_massGradNormSq ρ (fun x => π x.1) W hW)
    (fun t => raw_copy_gradient_le Kc K l hK ρ π hπ W t)
  have hnn := massNormSq_nonneg ρ (fun x => π x.1) (fun x => hπ x.1)
    (fun x => (u x).val)
  have hscaled := mul_le_mul_of_nonneg_left hi hν.le
  linarith only [he, hnn, hscaled]

/-- Injecting the datum solely into copy zero preserves its exact mass. -/
theorem raw_injected_mass {H : ℕ} (K : ι × Fin (H + 1) → ℕ)
    (ρ : ℝ) (π : ι → ℝ) (f : ∀ i, TorusHk (K (i, 0)) (h i)) :
    massNormSq ρ (fun x : ι × Fin (H + 1) => π x.1)
      (fun x => (preparationNeutralInitial H K f x).val) =
      massNormSq ρ π (fun i => (f i).val) := by
  classical
  unfold massNormSq
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single (0 : Fin (H + 1))]
  · exact Finset.sum_congr rfl fun i _ => by
      change (π i)⁻¹ * factorialNormSq ρ (preparationNeutralInitial H K f (i, 0)).val =
        (π i)⁻¹ * factorialNormSq ρ (f i).val
      rw [preparation_neutral_initial_zero_copy]
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro i _
    change (π i)⁻¹ * factorialNormSq ρ (preparationNeutralInitial H K f (i, l)).val = 0
    rw [preparation_neutral_initial_positive_copy H K f (i, l) hl]
    simp only [ZeroMemClass.coe_zero, CycleComparison.Coarse.factorialNormSq_zero_jet, mul_zero]
  · exact fun hx => False.elim (hx (Finset.mem_univ _))

/-- The exact factor14 square-root conversion of raw rank dissipation. -/
theorem raw_defect_sqrt_cost {ν X d L A : ℝ} {H : ℕ}
    (hν : 0 < ν) (hX : 0 ≤ X) (hd : 0 ≤ d) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (he : ν * X ≤ (4 * L ^ (2 * H)) * d) :
    7 * (A / Real.sqrt ν) * Real.sqrt X ≤
      14 * (A / ν) * L ^ H * Real.sqrt d := by
  have hLH : 0 ≤ L ^ H := pow_nonneg hL _
  have hr : 0 ≤ 2 * L ^ H * Real.sqrt d :=
    mul_nonneg (mul_nonneg (by norm_num) hLH) (Real.sqrt_nonneg _)
  have hs : (2 * L ^ H * Real.sqrt d) ^ 2 = (4 * L ^ (2 * H)) * d := by
    calc
      _ = 4 * (L ^ H) ^ 2 * (Real.sqrt d) ^ 2 := by ring
      _ = _ := by rw [← pow_mul, Nat.mul_comm H 2, Real.sq_sqrt hd]
  have hroot : Real.sqrt ν * Real.sqrt X ≤ 2 * L ^ H * Real.sqrt d := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hr).mp
    rw [mul_pow, Real.sq_sqrt hν.le, Real.sq_sqrt hX, hs]
    exact he
  have hXroot : Real.sqrt X ≤ (2 * L ^ H * Real.sqrt d) / Real.sqrt ν := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hν)).mpr
    simpa only [mul_comm] using hroot
  calc
    _ ≤ 7 * (A / Real.sqrt ν) * ((2 * L ^ H * Real.sqrt d) / Real.sqrt ν) :=
      mul_le_mul_of_nonneg_left hXroot
        (mul_nonneg (by norm_num) (div_nonneg hA (Real.sqrt_nonneg _)))
    _ = 7 * (A * (2 * L ^ H * Real.sqrt d) / (Real.sqrt ν * Real.sqrt ν)) := by
      rw [mul_assoc, div_mul_div_comm]
    _ = _ := by rw [← pow_two, Real.sq_sqrt hν.le]; ring

/-- The exact selected-copy dissipation of a given raw coupled solution. -/
theorem raw_solution_copy_dissipation {H D : ℕ}
    [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
    (Kc : ι × Fin (H + 1) → ℕ) (K : ι → ℕ) (l : Fin (H + 1))
    (hK : ∀ j, K j ≤ Kc (j, l)) (Kmax : ℕ) (hmax : ∀ x, Kc x ≤ Kmax)
    (ν ρ a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (hν : 0 < ν) (hρ : 0 < ρ)
    (hab : a ≤ b) (hd : TorusDriftData ν ρ a b v Kmax) (hD : 2 ≤ D)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : ∀ x y : ι × Fin (H + 1), (d : admissibleOrders Kc D x y) → ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h y.1)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h x.1)))
    (hfinite : ∀ x y d, coefficientSeminorm ρ (Kc x) a b (A x y d) ≠ ⊤)
    (hmeas : ∀ x y d, Measurable (fun p : Set.Icc a b × Vec 2 => A x y d p.1 p.2))
    (hsmooth : ∀ x y d t, t ∈ Set.Icc a b → ContDiff ℝ (Kc x : ℕ) (A x y d t))
    (hper : ∀ x y d t, t ∈ Set.Icc a b → IsZ2Periodic (A x y d t))
    (hfw : ∀ x y d, x.2.val ≠ y.2.val + 1 → ∀ t ∈ Set.Icc a b, A x y d t = 0)
    (S : ℝ) (hS : 0 ≤ S)
    (hschur : SchurBound S (schurMatrix ν ρ (fun x => π x.1) Kc D a b A))
    (f : ∀ x, TorusHk (Kc x) (h x.1))
    (u : ∀ x, ℝ → TorusHk (Kc x) (h x.1))
    (W : ∀ x, ℝ → TorusHk (Kc x + 1) (h x.1))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D Kc A f
      (fun _ _ => 0) (fun _ _ => 0) u W) :
    ν * (∫ t in Set.Icc a b,
      massGradNormSq ρ π (fun j => (preparationPlainCopyHigh Kc K l hK W j t).val)) ≤
      (4 * (8 * S + 1) ^ (2 * H)) *
        massNormSq ρ (fun x => π x.1) (fun x => (f x).val) := by
  have he := raw_copied_plain_energy H D Kmax Kc hD hmax ν ρ a b v
    hν hρ hab hd π hπ A hfinite hmeas hsmooth hper hfw S hS hschur
    f u W hsol a ⟨le_rfl, hab⟩
  exact raw_copy_dissipation Kc K l hK ρ ν a b (8 * S + 1) π hπ hν
    f (fun x => u x a) W hsol.2.1 he

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The physical moment price on the SAME whole-window finite insertion route.
The actual positive copies have zero initial trace, so the already proved
post-buffer extension costs no extra factor. The original datum pays the
actual high buffered datum through its existing buffer bound.

The degenerate cases are included: H=0 has no positive defect. Empty and singleton families, D=2,
zero/constants, identity geometry, edgeless seeds and degenerate post-buffer windows retain
these maps and bounds. No second evolution or mass-dependent map is chosen. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul
  preparationWeightedLowSMul preparationWeightedLowSpace
  preparationNeutralEnergyAdd preparationNeutralEnergyMonoid preparationNeutralEnergyModule
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D H Kbase : ℕ} {Part : Type*} {Ctx : Part → Type*}
  {family : ChartedFamily ι h D Part Ctx}

/-- The fixed original frame with its requested descending-copy envelopes. -/
structure PreparationNeutralLayerFrame (family : ChartedFamily ι h D Part Ctx)
    (H Kbase : ℕ) where
  base : PreparationPlainFrame family
  max_slot : ∀ v : ι × Fin (H + 1), preparationNeutralSlots H D Kbase v ≤ base.Kmax
  pointwise : ∀ l, IsPointwiseMolecularEnvelope family base.π
    (fun i => preparationNeutralSlots H D Kbase (i, l))
    (ChartedFamily.Domain.onWindow family (Set.Icc base.a base.b))
    base.ν base.e base.E base.ρ base.Cm base.Jm
    (fun v u => Real.sqrt (base.π u / base.π v) * base.A v u)

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **`RawCopiedEnergyPathsStatement` is proved**: the copied energy
paths of `rawCopiedEnergyPaths_of_descending` at `descendingCopyLinearEvolution`.

The degenerate cases are those of the two inputs. -/

/-- **The raw copied energy paths.** -/
theorem rawCopiedEnergyPaths : RawCopiedEnergyPathsStatement :=
  rawCopiedEnergyPaths_of_descending descendingCopyLinearEvolution

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Actual finite-route defect pricing with the SAME native full path,
buffered datum and raw descending-copy solution. Whole-window charts are
replaced by the real Eulerian coefficient hypotheses and its Schur budget;
local-to-global sampling supplies those hypotheses. The fixed-point/restart
and the expansion consumers are already proved. The degenerate cases are included: H=0 has no
defect; empty and singleton types, D=2, constants, zero data, identity geometry, an
edgeless seed and a point post-buffer window retain precisely these maps.
No independent solution or mass-dependent map is chosen. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace preparationNeutralEnergyAdd preparationNeutralEnergyMonoid
  preparationNeutralEnergyModule
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}

/-- The quantitative whole-window row on the actual finite insertion route.
The physical moment factor and copy-rank loss are explicit. This estimate,
together with the already proved generic row/tail expansion, is item (9). -/
def ActualFiniteRouteJoinStatement
    (family : ChartedFamily ι h D Part Ctx) (H Kbase Kmax : ℕ)
    (ν ρ a c b e Esc : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (π : ι → ℝ) (_hπ : ∀ i, 0 < π i)
    (actual : ∀ p, Ctx p)
    (_Kbound : ∀ x : ι × Fin (H + 1), preparationNeutralSlots H D Kbase x ≤ Kmax)
    (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)))
    (u : (∀ i, TorusHk 0 (h i)) →
      ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1))
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (_hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) =
      (M.full f).1 ⟨c, hac, hcb⟩ i)
    (_hhom : ScalarFamilyEnergyPathRealizes (ν := ν) hcb
      v
      (fun i (f : ∀ j, TorusHk 0 (h j)) => (f i, 0)) M.homogeneous)
    (_hreal : ∀ f, ∃ W : ∀ x : ι × Fin (H + 1), ℝ →
        TorusHk (preparationNeutralSlots H D Kbase x + 1) (h x.1),
      IsCoupledWeakSolutionTorus ν c b v D (preparationNeutralSlots H D Kbase)
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))
        (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) (B f))
        (fun _ _ => 0) (fun _ _ => 0) (u f) W ∧
      (∀ l, ∀ t : Set.Icc c b, (E l f).1 t = fun i =>
        truncateTorusHk (Nat.zero_le _) (u f (i, l) t)) ∧
      (∀ l, (E l f).2 =ᵐ[volume.restrict (Set.Icc c b)] fun t =>
        coupledCarrierHighJets (fun _ => 0) (fun i =>
          truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l) t))))
    (Pq : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) c b ρ ν 0 D)
    (P : PreparationPlainKernelFrame Pq)
    (_hcoeff : ∀ i j γ d, Pq.B i j γ d =
      constituentPhysical family ν e Esc actual i j γ d.val)
    (_hincl : ∀ i j γ, Pq.C i j γ = ContinuousLinearMap.id ℝ (h j))
    (_hsource : ScalarFamilyEnergyPathRealizes (ν := ν) Pq.htime
      v (preparationKernelScalarDatum Pq) M.source)
    (_hD : 2 ≤ D)
    (_hd : TorusDriftData ν ρ c b
      v Kmax)
    (_hreserve : ∀ (l : Fin H) j, P.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (q S Sr Cbuf : ℝ) (_hq : 0 ≤ q) (_hSr : 0 ≤ Sr)
    (_hw : ∀ i j γ, (P.spec i j γ).width ≤ q * ρ)
    (_hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * P.rows.basePrice i j))
    (_hraw_schur : SchurBound Sr
      (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1)
        (preparationNeutralSlots H D Kbase) D c b
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))))
    (_hfinite : ∀ x y d, coefficientSeminorm ρ
      (preparationNeutralSlots H D Kbase x) c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d) ≠ ⊤)
    (_hmeas : ∀ x y d, Measurable (fun p : Set.Icc c b × Vec 2 =>
      edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d p.1 p.2))
    (_hsmooth : ∀ x y d t, t ∈ Set.Icc c b → ContDiff ℝ
      (preparationNeutralSlots H D Kbase x : ℕ)
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t))
    (_hper : ∀ x y d t, t ∈ Set.Icc c b → IsZ2Periodic
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t))
    (_hbuf : ∀ f, Real.sqrt (massNormSq ρ π (fun i => (B f i).val)) ≤
      Cbuf * Real.sqrt (massNormSq ρ π (fun i => (f i).val))) : Prop :=
  ∀ (f : ∀ i, TorusHk 0 (h i)) (l : ℕ), l < H →
    preparationWeightedPathEnergy (h := h) ρ π ν a b c
      (preparationBufferedPlainLayer hac hcb M E (l + 1) f -
        preparationBufferedKernelMap hcb M.source
          (preparationBufferedPlainLayer hac hcb M E l f)) ≤
      14 * (q ^ P.L * |S| / ν) * (8 * Sr + 1) ^ H * Cbuf *
        Real.sqrt (massNormSq ρ π (fun i => (f i).val))
end

/-! Actual finite-route defect pricing with the SAME native full path,
buffered datum and raw descending-copy solution. Whole-window charts are
replaced by the real Eulerian coefficient hypotheses and its Schur budget;
local-to-global sampling supplies those hypotheses. The fixed-point/restart
and the expansion consumers are already proved. The degenerate cases are included: H=0 has no
defect; empty and singleton types, D=2, constants, zero data, identity geometry, an
edgeless seed and a point post-buffer window retain precisely these maps.
No independent solution or mass-dependent map is chosen. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace preparationNeutralEnergyAdd preparationNeutralEnergyMonoid
  preparationNeutralEnergyModule
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}


/-- The supplied copied weak solution and its exact selected trace/higher
classes, without any energy or chart assertion. -/
abbrev RawCopyRealizes (family : ChartedFamily ι h D Part Ctx)
    (H : ℕ) (K : ι × Fin (H + 1) → ℕ) (ν a b e Esc : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (actual : ∀ p, Ctx p)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (K (i, 0)) (h i)))
    (u : (∀ i, TorusHk 0 (h i)) → ∀ x, ℝ → TorusHk (K x) (h x.1))
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) a b a) : Prop :=
  ∀ f, ∃ W : ∀ x, ℝ → TorusHk (K x + 1) (h x.1),
    IsCoupledWeakSolutionTorus ν a b v D K
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K)
      (preparationNeutralInitial H K (B f)) (fun _ _ => 0) (fun _ _ => 0) (u f) W ∧
    (∀ l, ∀ t : Set.Icc a b, (E l f).1 t = fun i =>
      truncateTorusHk (Nat.zero_le _) (u f (i, l) t)) ∧
    (∀ l, (E l f).2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i =>
        truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l) t)))

/-- The exact full insertion algebra plus the positive-copy initial trace. -/
def BufferedCopyJoinStatement {a b c : ℝ} {H : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c) : Prop :=
  BufferedPlainLayerJoinStatement hac hcb M E ∧
    ∀ (l : Fin (H + 1)), l ≠ 0 → ∀ f, (E l f).1 ⟨c, le_rfl, hcb⟩ = 0

/-- The selected positive-copy defect price on the post-buffer window,
with the same high datum, response and energy paths. -/
def RawPostPriceStatement (H L : ℕ) (K : ι → ℕ)
    (ρ ν c b q S Sr : ℝ) (π : ι → ℝ)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, TorusHk (K i) (h i)))
    (J : CoupledHighTime (h := h) (fun _ => 0) c b →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c) : Prop :=
  ∀ (f : ∀ i, TorusHk 0 (h i)) (l : Fin H),
    preparationWeightedPathEnergy (h := h) ρ π ν c b c
      (E l.succ f - J (E l.castSucc f).2) ≤
      14 * (q ^ L * |S| / ν) * (8 * Sr + 1) ^ H *
        Real.sqrt (massNormSq ρ π (fun i => (B f i).val))

/-- Whole-window price from the two named raw-path ingredients. The
extension and the supplied buffer norm are discharged in the assembly. -/
theorem actual_finite_route_of_ingredients
    (family : ChartedFamily ι h D Part Ctx) (H Kbase Kmax : ℕ)
    (ν ρ a c b e Esc : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (π : ι → ℝ) (_hπ : ∀ i, 0 < π i)
    (actual : ∀ p, Ctx p)
    (_Kbound : ∀ x : ι × Fin (H + 1), preparationNeutralSlots H D Kbase x ≤ Kmax)
    (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)))
    (u : (∀ i, TorusHk 0 (h i)) →
      ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1))
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (_hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) =
      (M.full f).1 ⟨c, hac, hcb⟩ i)
    (_hhom : ScalarFamilyEnergyPathRealizes (ν := ν) hcb
      v
      (fun i (f : ∀ j, TorusHk 0 (h j)) => (f i, 0)) M.homogeneous)
    (_hreal : ∀ f, ∃ W : ∀ x : ι × Fin (H + 1), ℝ →
        TorusHk (preparationNeutralSlots H D Kbase x + 1) (h x.1),
      IsCoupledWeakSolutionTorus ν c b v D (preparationNeutralSlots H D Kbase)
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))
        (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) (B f))
        (fun _ _ => 0) (fun _ _ => 0) (u f) W ∧
      (∀ l, ∀ t : Set.Icc c b, (E l f).1 t = fun i =>
        truncateTorusHk (Nat.zero_le _) (u f (i, l) t)) ∧
      (∀ l, (E l f).2 =ᵐ[volume.restrict (Set.Icc c b)] fun t =>
        coupledCarrierHighJets (fun _ => 0) (fun i =>
          truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (W (i, l) t))))
    (Pq : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
      (G := fun _ j _ => h j) c b ρ ν 0 D)
    (P : PreparationPlainKernelFrame Pq)
    (_hcoeff : ∀ i j γ d, Pq.B i j γ d =
      constituentPhysical family ν e Esc actual i j γ d.val)
    (_hincl : ∀ i j γ, Pq.C i j γ = ContinuousLinearMap.id ℝ (h j))
    (_hsource : ScalarFamilyEnergyPathRealizes (ν := ν) Pq.htime
      v (preparationKernelScalarDatum Pq) M.source)
    (_hD : 2 ≤ D)
    (_hd : TorusDriftData ν ρ c b
      v Kmax)
    (_hreserve : ∀ (l : Fin H) j, P.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (q S Sr Cbuf : ℝ) (_hq : 0 ≤ q) (_hSr : 0 ≤ Sr)
    (_hw : ∀ i j γ, (P.spec i j γ).width ≤ q * ρ)
    (_hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * P.rows.basePrice i j))
    (_hraw_schur : SchurBound Sr
      (schurMatrix ν ρ (fun x : ι × Fin (H + 1) => π x.1)
        (preparationNeutralSlots H D Kbase) D c b
        (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
          (preparationNeutralSlots H D Kbase))))
    (_hfinite : ∀ x y d, coefficientSeminorm ρ
      (preparationNeutralSlots H D Kbase x) c b
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d) ≠ ⊤)
    (_hmeas : ∀ x y d, Measurable (fun p : Set.Icc c b × Vec 2 =>
      edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d p.1 p.2))
    (_hsmooth : ∀ x y d t, t ∈ Set.Icc c b → ContDiff ℝ
      (preparationNeutralSlots H D Kbase x : ℕ)
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t))
    (_hper : ∀ x y d t, t ∈ Set.Icc c b → IsZ2Periodic
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual
        (preparationNeutralSlots H D Kbase) x y d t))
    (_hbuf : ∀ f, Real.sqrt (massNormSq ρ π (fun i => (B f i).val)) ≤
      Cbuf * Real.sqrt (massNormSq ρ π (fun i => (f i).val)))
    (hjoin : BufferedCopyJoinStatement hac hcb M E)
    (hpost : RawPostPriceStatement H P.L
      (fun i => preparationNeutralSlots H D Kbase (i, 0)) ρ ν c b q S Sr π B M.source E) :
    ActualFiniteRouteJoinStatement family H Kbase Kmax ν ρ a c b e Esc v π _hπ actual _Kbound hac hcb M B u E _hB _hhom _hreal Pq P _hcoeff _hincl _hsource _hD _hd _hreserve q S Sr Cbuf _hq _hSr _hw _hs _hraw_schur _hfinite _hmeas _hsmooth _hper _hbuf := by
  have hstart (X) : (M.source X).1 ⟨c, le_rfl, hcb⟩ = 0 := (_hsource X).1
  have hL : 0 ≤ 8 * Sr + 1 :=
    add_nonneg (mul_nonneg (by norm_num) _hSr) zero_le_one
  have hcost : 0 ≤ 14 * (q ^ P.L * |S| / ν) * (8 * Sr + 1) ^ H :=
    mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (pow_nonneg _hq _) (abs_nonneg _)) Pq.diffusivity_pos.le))
      (pow_nonneg hL _)
  intro f l hl
  have hext := buffered_plain_layer_defect_energy_le hac hcb M E hjoin.1 hjoin.2 hstart
    (massWeightedCarrierCLM (E := h) (fun _ => 0) ρ π)
    (preparationWeightedGradientCLM (h := h) ρ π) ν l hl f
  have hp := hpost f ⟨l, hl⟩
  exact hext.trans (hp.trans ((mul_le_mul_of_nonneg_left (_hbuf f) hcost).trans_eq
    (mul_assoc _ _ _).symm))
end

/-! Raw forward-copy support, the homogeneous copy-zero identity and the
complete buffered insertion algebra. The supplied actual solution and
its genuine higher time classes are retained; no chart frame is used. -/

section
attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul preparationWeightedLowSMul
  preparationWeightedLowSpace preparationNeutralEnergyAdd preparationNeutralEnergyMonoid
  preparationNeutralEnergyModule
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Non-forward copy pairs have identically zero physical coefficients. -/
theorem raw_neutral_edge_zero (family : ChartedFamily ι h D Part Ctx)
    (H : ℕ) (ν e Esc : ℝ) (actual : ∀ p, Ctx p)
    (K : ι × Fin (H + 1) → ℕ) (x y : ι × Fin (H + 1))
    (d : admissibleOrders K D x y) (hxy : x.2.val ≠ y.2.val + 1) :
    edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K x y d = 0 := by
  classical
  let : IsEmpty ((preparationNeutralChain family H).Γ x y) :=
    ⟨fun γ => hxy γ.property⟩
  funext t z
  simp only [edgeCoefficient, physicalCoefficient, Fintype.sum_empty, Pi.zero_apply]

/-- The genuine copy-zero low row is the homogeneous scalar equation. -/
theorem raw_zero_copy_row (family : ChartedFamily ι h D Part Ctx)
    (H : ℕ) (ν a b e Esc : ℝ) (actual : ∀ p, Ctx p) (v : ℝ → Vec 2 → Vec 2)
    (K : ι × Fin (H + 1) → ℕ)
    (f : ∀ x, TorusHk (K x) (h x.1))
    (u : ∀ x, ℝ → TorusHk (K x) (h x.1))
    (W : ∀ x, ℝ → TorusHk (K x + 1) (h x.1))
    (hs : IsCoupledWeakSolutionTorus ν a b v D K
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K) f
      (fun _ _ => 0) (fun _ _ => 0) u W) (i : ι) :
    IsTorusForcedRow ν a b v 2 0 (truncateTorusHk (Nat.zero_le (K (i, 0))) (f (i, 0)))
      (fun _ => 0) (fun _ => 0)
      (fun t => truncateTorusHk (Nat.zero_le (K (i, 0))) (u (i, 0) t))
      (fun t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, 0)))) (W (i, 0) t)) := by
  apply preparation_plain_low_forced_row hs (i, 0) (fun _ => 0)
  intro t _
  apply (CycleJointProofs.torusZero_rawJet_ae (E := PiLp 2 (fun _ : Fin 2 => h i))
    0 (valueIndex2 0)).trans
  apply Filter.Eventually.of_forall
  intro z
  have hz (y : ι × Fin (H + 1)) (d : admissibleOrders K D (i, 0) y) :
      edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K (i, 0) y d t = 0 :=
    congrFun (raw_neutral_edge_zero family H ν e Esc actual K (i, 0) y d (by change 0 ≠ y.2.val + 1; omega)) t
  simp only [torusRawCouplingFlux, hz, Pi.zero_apply, zero_apply, Finset.sum_const_zero]

private theorem raw_same_trace_higher
    {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} (f : ∀ i, TorusHk 0 (h i))
    (up uk : ∀ i, ℝ → TorusHk 0 (h i)) (Wp Wk : ∀ i, ℝ → TorusHk 1 (h i))
    (hp : ∀ i, IsTorusForcedRow ν a b v 2 0 (f i) (fun _ => 0) (fun _ => 0) (up i) (Wp i))
    (hk : ∀ i, IsTorusForcedRow ν a b v 2 0 (f i) (fun _ => 0) (fun _ => 0) (uk i) (Wk i))
    (he : ∀ i, ∀ t ∈ Set.Icc a b, up i t = uk i t)
    (U V : CoupledHighTime (h := h) (fun _ => 0) a b)
    (hU : U =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i => Wp i t))
    (hV : V =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i => Wk i t)) : U = V := by
  have hzero : (0 : CoupledHighTime (h := h) (fun _ => 0) a b) =ᵐ[
      volume.restrict (Set.Icc a b)] fun _ =>
      coupledCarrierHighJets (fun _ => 0) (fun i => (0 : TorusHk 1 (h i))) :=
    (Lp.coeFn_zero (CoupledHighHilbert (h := h) (fun _ => 0)) 2
      (volume.restrict (Set.Icc a b))).trans
        (Filter.Eventually.of_forall fun _ => rfl)
  have htr : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      truncateTorusHk (Nat.zero_le 1) (Wp i t) =
        truncateTorusHk (Nat.zero_le 1) (Wk i t) +
          truncateTorusHk (Nat.zero_le 1) (0 : TorusHk 1 (h i)) := by
    filter_upwards [ae_all_iff.mpr (fun i => (hp i).2.2.1 0),
      ae_all_iff.mpr (fun i => (hk i).2.2.1 0), ae_restrict_mem measurableSet_Icc]
      with t ht htZ htmem
    intro i
    simpa only [map_zero, add_zero] using (ht i).trans ((he i t htmem).trans (htZ i).symm)
  have hh := preparation_native_higher_add_of_traces (h := h) a b
    U V 0 Wp Wk (fun _ _ => 0) hU hV hzero htr
  simpa only [add_zero] using hh

/-- Copy-zero equality retains both the trace and its genuine higher
class, using raw rows and the scalar uniqueness `torusForcedRow_unique`. -/
theorem raw_zero_copy_path (family : ChartedFamily ι h D Part Ctx)
    (H : ℕ) (ν ρ a b e Esc : ℝ) (actual : ∀ p, Ctx p) (v : ℝ → Vec 2 → Vec 2)
    (K : ι × Fin (H + 1) → ℕ) (Kmax : ℕ)
    (hab : a ≤ b) (hd : TorusDriftData ν ρ a b v Kmax) (hν : 0 < ν) (hρ : 0 < ρ)
    (f : ∀ x, TorusHk (K x) (h x.1))
    (u : ∀ x, ℝ → TorusHk (K x) (h x.1))
    (W : ∀ x, ℝ → TorusHk (K x + 1) (h x.1))
    (hsol : IsCoupledWeakSolutionTorus ν a b v D K
      (edgeCoefficient (preparationNeutralChain family H) ν e Esc actual K)
      f (fun _ _ => 0) (fun _ _ => 0) u W)
    (zp zk : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b a)
    (Z : ∀ i, ℝ → TorusHk 1 (h i))
    (hzp : ∀ t : Set.Icc a b, zp.1 t =
      fun i => truncateTorusHk (Nat.zero_le (K (i, 0))) (u (i, 0) t))
    (hWp : zp.2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i =>
        truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, 0)))) (W (i, 0) t)))
    (hz : ∀ i, IsTorusForcedRow ν a b v 2 0
      (truncateTorusHk (Nat.zero_le (K (i, 0))) (f (i, 0)))
      (fun _ => 0) (fun _ => 0)
      (fun t => zk.1 (Set.projIcc a b hab t) i) (Z i))
    (hZ : zk.2 =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      coupledCarrierHighJets (fun _ => 0) (fun i => Z i t)) : zp = zk := by
  have hrow (i : ι) := raw_zero_copy_row family H ν a b e Esc actual v K f u W hsol i
  have he (i : ι) := torusForcedRow_unique (E := h i) hd hab hρ hν
    (by decide) (Nat.zero_le Kmax)
    (timeMemLp_zero (E := TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i))) _ 2)
    (timeIntegrable_zero (E := TorusHk 0 (h i)) _) (hrow i : _) (hz i : _)
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    rw [hzp t]
    funext i
    simpa only [Set.projIcc_of_mem hab t.property] using he i t t.property
  · exact raw_same_trace_higher
      (fun i => truncateTorusHk (Nat.zero_le (K (i, 0))) (f (i, 0)))
      (fun i t => truncateTorusHk (Nat.zero_le (K (i, 0))) (u (i, 0) t))
      (fun i t => zk.1 (Set.projIcc a b hab t) i)
      (fun i t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K (i, 0)))) (W (i, 0) t))
      Z hrow hz he zp.2 zk.2 hWp hZ

private theorem raw_row_initial_congr {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {f g : TorusHk 0 E}
    {u : ℝ → TorusHk 0 E} {W : ℝ → TorusHk 1 E}
    (hfg : f = g)
    (hs : IsTorusForcedRow ν a b v 2 0 g (fun _ => 0) (fun _ => 0) u W) :
    IsTorusForcedRow ν a b v 2 0 f (fun _ => 0) (fun _ => 0) u W := by
  cases hfg
  exact hs

/-- The same actual copy-zero path is the supplied homogeneous response,
with the original buffered low datum and higher class. -/
theorem raw_buffered_zero_copy
    (family : ChartedFamily ι h D Part Ctx)
    (H Kbase Kmax : ℕ)
    (ν ρ a c b e Esc : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (actual : ∀ p, Ctx p)
    (hac : a ≤ c)
    (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)))
    (u : (∀ i, TorusHk 0 (h i)) →
      ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1))
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (_hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) =
      (M.full f).1 ⟨c, hac, hcb⟩ i)
    (_hhom : ScalarFamilyEnergyPathRealizes (ν := ν) hcb
      v
      (fun i (f : ∀ j, TorusHk 0 (h j)) => (f i, 0)) M.homogeneous)
    (_hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase)
      ν c b e Esc v actual B u E)
    (_hd : TorusDriftData ν ρ c b
      v Kmax)
    (hν : 0 < ν) (hρ : 0 < ρ) :
    ∀ f, E 0 f = M.homogeneous ((M.full f).1 ⟨c, hac, hcb⟩) := by
  intro f
  let d : ∀ i, TorusHk 0 (h i) := (M.full f).1 ⟨c, hac, hcb⟩
  have hr := _hreal f
  obtain ⟨W, hs, ht, hW⟩ := hr
  let hn := (_hhom d).2
  let Z : ∀ i, ℝ → TorusHk 1 (h i) := Classical.choose hn
  have hz := (Classical.choose_spec hn).1
  have hZ := (Classical.choose_spec hn).2
  let K : ι × Fin (H + 1) → ℕ := preparationNeutralSlots H D Kbase
  have hmatch (i : ι) : truncateTorusHk (Nat.zero_le (K (i, 0)))
      (preparationNeutralInitial H K (B f) (i, 0)) = d i := by
    rw [preparation_neutral_initial_zero_copy, _hB f i]
  have hk (i : ι) := raw_row_initial_congr (E := h i) (hmatch i) (hz i)
  exact raw_zero_copy_path family H ν ρ c b e Esc actual v K Kmax hcb _hd hν hρ
    (preparationNeutralInitial H K (B f)) (u f) W hs
    (E 0 f) (M.homogeneous d) Z (ht 0) (hW 0) hk hZ

/-- The supplied raw solution yields the exact complete buffered path join. -/
theorem raw_buffered_copy_join
    (family : ChartedFamily ι h D Part Ctx)
    (H Kbase Kmax : ℕ)
    (ν ρ a c b e Esc : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (actual : ∀ p, Ctx p)
    (hac : a ≤ c)
    (hcb : c ≤ b)
    (M : PreparationBufferedMaps (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c)
    (B : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      (∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i)))
    (u : (∀ i, TorusHk 0 (h i)) →
      ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1))
    (E : Fin (H + 1) → (∀ i, TorusHk 0 (h i)) →ₗ[ℝ]
      PreparationEnergyPath (∀ i, TorusHk 0 (h i))
        (CoupledHighHilbert (h := h) (fun _ => 0)) c b c)
    (_hB : ∀ f i, truncateTorusHk (Nat.zero_le _) (B f i) =
      (M.full f).1 ⟨c, hac, hcb⟩ i)
    (_hhom : ScalarFamilyEnergyPathRealizes (ν := ν) hcb
      v
      (fun i (f : ∀ j, TorusHk 0 (h j)) => (f i, 0)) M.homogeneous)
    (_hreal : RawCopyRealizes family H (preparationNeutralSlots H D Kbase)
      ν c b e Esc v actual B u E)
    (_hd : TorusDriftData ν ρ c b
      v Kmax)
    (hν : 0 < ν) (hρ : 0 < ρ) : BufferedCopyJoinStatement hac hcb M E := by
  have hpositive (l : Fin (H + 1)) (hl : l ≠ 0) (f : ∀ i, TorusHk 0 (h i)) :
      (E l f).1 ⟨c, le_rfl, hcb⟩ = 0 := by
    have hr := _hreal f
    obtain ⟨W, hs, ht, _⟩ := hr
    rw [ht l ⟨c, le_rfl, hcb⟩]
    funext i
    change truncateTorusHk (Nat.zero_le _) (u f (i, l) c) = 0
    rw [hs.2.2.2.1 (i, l), preparation_neutral_initial_positive_copy H
      (preparationNeutralSlots H D Kbase) (B f) (i, l) hl, map_zero]
  have hzero := raw_buffered_zero_copy family H Kbase Kmax ν ρ a c b e Esc v actual hac hcb M B u E _hB _hhom _hreal _hd hν hρ
  exact ⟨buffered_plain_layer_join hac hcb M E (fun f => (_hhom f).1) hzero hpositive,
    hpositive⟩
end

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
