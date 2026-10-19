-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.CycleReference.ChartCorrectionIntegrability
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Proofs.CascadeInvariants.Scales
public import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.CycleReference.TorusStreamFluxEquation
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
public import AVRegularity.Definitions.Construction.ScheduleFloor
public import AVRegularity.Definitions.Families.ActualFamily
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The source-insertion route to common preparation (finite expansion and one joint model).
These statements are the ingredients of the proof of common preparation.

For Hpr=0 the statements keep the scalar homogeneous evolution, and an empty component type
or an edgeless seed keeps the same scalar endpoint. No norm or datum is divided out. One
endpoint and map serve both weights. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The actual regularized family and the fixed preparation request, before its datum. -/
structure Request (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) where
  law : BirthLaw
  P : ProvParams
  seedK : ℕ → KernelSpec
  freshK : ℕ → KernelSpec
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  G : GenStage D hr Dm bw j₀
  cr : ℝ
  c₀ : ℝ
  Q : ℝ
  s : ℝ
  tf : ℝ
  p : ℕ
  Nout : ℕ
  Naux : ℕ
  Hpr : ℕ

namespace Request
variable (F : Request hr D Dm bw j₀)

abbrev Data (k : ℕ) := ∀ v : CompIn F.G.comps, TorusHk k (hr v.1.root)

def inputNorm (w : CompIn F.G.comps → ℝ) (f : F.Data 0) : ℝ :=
  weightedNorm 1 (F.G.mass F.law) w f

def bufferEnd : ℝ := F.s + rhoStar D F.c₀ F.G.level ^ 2 / D.κ F.G.level

/-- The concrete operators in the finite source-insertion identity. X is a space
of actual low-order evolution paths; the plain layers are built at descending
orders and then read into X. Their PDE realization is stated separately
(`EvolutionTraceStatement`). -/
structure InsertionRoute (X : Type*) [AddCommGroup X] [Module ℝ X] where
  initial : F.Data 0 →ₗ[ℝ] X
  full : F.Data 0 →ₗ[ℝ] X
  kernel : X →ₗ[ℝ] X
  layer : ℕ → F.Data 0 →ₗ[ℝ] X
  trace : ℝ → X →ₗ[ℝ] F.Data 0

variable {F}

/-- The finite unregularized chain, read back into the original components. -/
def InsertionRoute.plainTrace {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (t : ℝ) (f : F.Data 0) : F.Data 0 :=
  R.trace t (∑ h ∈ Finset.range (F.Hpr + 1), R.layer h f)

/-- A single prepared model map, before both the weight and the datum. -/
structure Model where
  tp : ℝ
  map : F.Data 0 →ₗ[ℝ] F.Data F.Nout

/-- Restart/uniqueness identifies the canonical trace with every supplied solution;
actual contraction gives the leading constant one. -/
def EvolutionTraceStatement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (M : F.Model) : Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ f : F.Data 0,
      F.inputNorm w (R.trace M.tp (R.full f)) ≤ F.inputNorm w f ∧
      ∀ (U : ∀ v : CompIn F.G.comps, ℝ → TorusHk 0 (hr v.1.root))
        (W : ∀ v : CompIn F.G.comps, ℝ → TorusHk 1 (hr v.1.root))
        (Y : ∀ v u (_ : F.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (hr u.1.root)),
        F.G.IsRegSolution F.P F.seedK F.freshK F.φ₀ F.hφ₀ (D.κ F.G.level)
          (streamVel (D.Φ F.G.level)) 0 F.s F.tf f (fun _ _ => 0) (fun _ _ => 0) U W Y →
        R.trace M.tp (R.full f) = fun v => U v M.tp

/-- The exact finite expansion with the regularized tail and kernel-defect differences,
priced in the physical L2 norm. It does not assert enhanced jets of the error. -/
def FiniteExpansionApproximationStatement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (M : F.Model) (Cexp : ℝ) : Prop :=
  (∀ f, R.full f = R.initial f + R.kernel (R.full f)) ∧
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ f : F.Data 0,
      F.inputNorm w (R.plainTrace M.tp f - R.trace M.tp (R.full f)) ≤
        Cexp * D.eps (F.G.level - 1) ^ F.Q * F.inputNorm w f

/-- Scalar restart gives the exact fixed point and the zeroth plain layer.
For Hpr=0 the scalar restart is still required, without any positive plain layer. -/
def ScalarRestartStatement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) : Prop :=
  (∀ f, R.full f = R.initial f + R.kernel (R.full f)) ∧ R.layer 0 = R.initial

/-- The terminal trace is controlled by the path energy seminorm for both weights.
Empty families and zero paths have zero trace norm. -/
def TraceEnergyStatement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (M : F.Model)
    (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ X) : Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ x, F.inputNorm w (R.trace M.tp x) ≤ p w x

/-- Forced scalar energy composed with the priced kernel flux.
No source makes the contraction factor zero, and the two weights share the operator. -/
def KernelSourceEnergyStatement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ X) (β : ℝ) : Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ x, p w (R.kernel x) ≤ β * p w x

/-- The buffered actual solution has bounded path energy, without a norm of its datum divided out.
The zero datum and an empty family give the same inequality with zero right side. -/
def BufferedFullEnergyStatement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ X)
    (Cfull : ℝ) : Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ f, p w (R.full f) ≤ Cfull * F.inputNorm w f

/-- Only defects of layers strictly below Hpr are used. The PDE realization uses
reserve s*+L on that layer; no higher-order norm of the final error is requested.
For Hpr=0 there are no defects, and edgeless families and identical kernels give zero
defects. -/
def PlainSourceDefectStatement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (p : (CompIn F.G.comps → ℝ) → Seminorm ℝ X)
    (Cdef L : ℝ) : Prop :=
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ f h, h < F.Hpr → p w (R.layer (h + 1) f - R.kernel (R.layer h f)) ≤
      Cdef * D.eps (F.G.level - 1) ^ L * F.inputNorm w f

/-- The cycle-joint model of the neutral chain after buffer, injection and readout.
Its one map fixes constants, approximates the plain chain, and has enhanced jets. -/
def NeutralChainModelStatement {X : Type*} [AddCommGroup X] [Module ℝ X]
    (R : F.InsertionRoute X) (M : F.Model) (Cjoint Cjet : ℝ) : Prop :=
  (∀ (cv : ∀ v : CompIn F.G.comps, hr v.1.root) (f : F.Data 0),
    (∀ v, (f v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => cv v) →
    ∀ v, (M.map f v).toFunction.jet (valueIndex2 F.Nout)
      =ᵐ[volume.restrict unitCube] fun _ => cv v) ∧
  ∀ w : CompIn F.G.comps → ℝ, (w = fun _ => 1) ∨ w = F.G.marker F.law →
    ∀ f : F.Data 0,
      F.inputNorm w ((fun v => truncateTorusHk (Nat.zero_le F.Nout) (M.map f v)) -
        R.plainTrace M.tp f) ≤ Cjoint * D.eps (F.G.level - 1) ^ F.Q * F.inputNorm w f ∧
      weightedNorm (rhoEnh D F.cr F.G.level) (F.G.mass F.law) w (M.map f) ≤
        Cjet * F.inputNorm w f

/-- The quiet margin and endpoint of the joint preparation, at the buffer start. The scalar delay
bound translates its two-scale window to the four-scale preparation window. -/
def EndpointStatement (M : F.Model) : Prop :=
  F.s ≤ F.bufferEnd ∧
    F.bufferEnd ≤ F.s + 2 * ocTauPP D.α D.q D.Λ F.G.level ∧
    M.tp ∈ Set.Icc F.bufferEnd (F.bufferEnd + 2 * ocTauPP D.α D.q D.Λ F.G.level) ∧
    M.tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ F.G.level ∧
    Set.Icc (M.tp - ocTauP D.α D.q D.Λ F.G.level)
      (M.tp + ocTauP D.α D.q D.Λ F.G.level) ⊆
        ocQuietTimes D.α D.q D.Λ D.ζ F.G.level

end Request

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The two radii of the joint preparation at every sufficiently late interior
stage. The molecular radius is the actual rhoStar, while the entrance
radius is a fixed multiple of eps^(1+gamma/2+delta) and lies below it.
Uniform interior diffusivity and rounded-power comparisons are reused.

Empty or singleton families, edgeless seeds and every finite order have the same scalar
inequalities. Seeds at n<M are included
numerically but still use their supplied envelope. The terminal m=M
is excluded; its diffusivity scaling is different. The level floor is two. This module states
and proves the two scale comparisons. -/

section
open CycleReference EntryScales

/-- Fixed entrance-radius and comparison constants precede all band chains,
stages and data; the positive molecular coefficient is the only request. -/
def PreparationJointRadiusStatement (α q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ c₀ : ℝ, 0 < c₀ →
  ∃ cOld Crat : ℝ, 0 < cOld ∧ 0 < Crat ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
  ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
  ∀ m : ℕ, m₀ ≤ m → m < M →
    let ρ := c₀ * min (ocEpsilon q Λ m) (Real.sqrt (κ m / ocA α q Λ m))
    let ρold := cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)
    ρ = ocRhoMol α q Λ m c₀ (κ m) ∧ 0 < ρold ∧ ρold ≤ ρ ∧
      ρ / ρold ≤ Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))
end

/-! Uniform entrance and molecular radius comparisons at the original interior
stage. The constants precede every band chain and stage. The square-root
scale eventually lies below the wavelength cap; the extra positive delta
power puts the entrance radius below it. The shared rounded-power bound
converts their quotient to the exact parent exponent. -/

section
open CycleReference EntryScales

/-- The scale comparisons supply exactly the two radius clauses
of the joint preparation, uniformly over every longer band chain. -/
theorem preparation_joint_radius_scales {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    PreparationJointRadiusStatement α q ζ := by
  obtain ⟨Ci, hCi, Λi, hΛi, hdiff⟩ := bandChain_interior_diffusivities hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λq, hΛq, hpower⟩ := epsilon_power_asymp_shared_threshold hq.1
  have hγ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).1
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  let C := Real.sqrt (Ci * 1)
  have hC : 0 < C := Real.sqrt_pos.mpr (mul_pos (zero_lt_one.trans_le hCi) zero_lt_one)
  obtain ⟨Kq, hKq, hpower⟩ := hpower (-(ocDelta α q))
  refine ⟨max Λi Λq, by omega, ?_⟩
  intro Λ hΛ c₀ hc₀
  have h128 : 128 ≤ Λ := by omega
  have hdecay := epsilon_rpow_tendsto_zero hq.1 h128 (half_pos hγ)
  have hlim : Tendsto (fun m : ℕ => C * ocEpsilon q Λ m ^ (ocGamma α q / 2))
      atTop (𝓝 0) := by simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  obtain ⟨mc, hmc⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds zero_lt_one))
  refine ⟨c₀ * C⁻¹, C ^ 2 * Kq, mul_pos hc₀ (inv_pos.mpr hC),
    mul_pos (pow_pos hC 2) (zero_lt_one.trans_le hKq), max 2 mc, by omega, ?_⟩
  intro M κ hband m hm hmM
  have he := (Scales.epsilon_basic (m := m) hq.1 h128).1
  have he1 := (Scales.epsilon_basic (m := m) hq.1 h128).2.1
  have ha : 0 < ocA α q Λ m := Real.rpow_pos_of_pos he _
  have hd := hdiff Λ (by omega) M (by omega) κ hband m (by omega) hmM
  have hA : ocAsymp 1 (ocA α q Λ m) (ocEpsilon q Λ m ^ ((1 + α) - 2)) :=
    asymp_one_self _
  have hdiv := aPow_div he (zero_lt_one.trans_le hCi) zero_lt_one ha hd hA
  have hmol : ocAsymp C (Real.sqrt (κ m / ocA α q Λ m))
      (ocEpsilon q Λ m ^ (1 + ocGamma α q / 2)) :=
    aPow_congr (by ring) (aPow_sqrt he (mul_pos (zero_lt_one.trans_le hCi) zero_lt_one) hdiv)
  have hcap : Real.sqrt (κ m / ocA α q Λ m) ≤ ocEpsilon q Λ m := by
    calc
      _ ≤ C * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2) := hmol.2
      _ = (C * ocEpsilon q Λ m ^ (ocGamma α q / 2)) * ocEpsilon q Λ m := by
        rw [Real.rpow_add he, Real.rpow_one]
        ring
      _ ≤ 1 * ocEpsilon q Λ m := mul_le_mul_of_nonneg_right (hmc m (by omega)) he.le
      _ = _ := one_mul _
  dsimp only
  rw [min_eq_right hcap]
  refine ⟨rfl, mul_pos (mul_pos hc₀ (inv_pos.mpr hC)) (Real.rpow_pos_of_pos he _), ?_, ?_⟩
  · have heδ : ocEpsilon q Λ m ^ ocDelta α q ≤ 1 := Real.rpow_le_one he.le he1 hδ.le
    calc
      _ = c₀ * (C⁻¹ * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2)) *
          ocEpsilon q Λ m ^ ocDelta α q := by rw [Real.rpow_add he]; ring
      _ ≤ (c₀ * Real.sqrt (κ m / ocA α q Λ m)) * ocEpsilon q Λ m ^ ocDelta α q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmol.1 hc₀.le)
          (Real.rpow_nonneg he.le _)
      _ ≤ _ := mul_le_of_le_one_right (mul_nonneg hc₀.le (Real.sqrt_nonneg _)) heδ
  · have heq : ocEpsilon q Λ m ^ (1 + ocGamma α q / 2) /
        ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) =
          ocEpsilon q Λ m ^ (-(ocDelta α q)) := by
      rw [← Real.rpow_sub he]
      congr 1
      ring
    have hden : 0 < (c₀ * C⁻¹) *
        ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) :=
      mul_pos (mul_pos hc₀ (inv_pos.mpr hC)) (Real.rpow_pos_of_pos he _)
    calc
      _ ≤ (c₀ * C * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2)) /
          ((c₀ * C⁻¹) * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)) :=
        div_le_div_of_nonneg_right (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmol.2 hc₀.le) hden.le
      _ = (c₀ * C) / (c₀ * C⁻¹) * (ocEpsilon q Λ m ^ (1 + ocGamma α q / 2) /
          ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)) := mul_div_mul_comm _ _ _ _
      _ = C ^ 2 * ocEpsilon q Λ m ^ (-(ocDelta α q)) := by
        rw [heq]
        congr 1
        field_simp [hc₀.ne', hC.ne']
      _ ≤ C ^ 2 * Kq * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q)) := by
        have hh := (hpower Λ m (by omega) (by omega)).2
        simpa only [mul_neg, mul_assoc] using mul_le_mul_of_nonneg_left hh (sq_nonneg C)
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization MeasureTheory AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual-context structural inputs of the joint preparation of the copied family, read
from the incoming invariant on any contained window. All geometry and
quiet identities are the existing actual-family transfers; this interface
asks for their joint extraction, without new envelopes or chart analysis.

The degenerate cases are included: empty and singleton families, an empty window, identity
geometry, Dm=2, an edgeless seed and smallest orders use the same actual family and atlas.
Fast independence is asked only on the trimmed quiet set `ocTrimmedQuietTimes`. -/

/-- One actual atlas and the native structural inputs on every subwindow of
the incoming invariant. No model, mass or datum is selected in this leaf. -/
def NativePreparationGeometryStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Mnat : ℕ) (k : InvConsts)
    (tA tf S θK : ℝ) (G : GenStage D hr Dm bw j₀),
    IsStageInvariant law P seedK freshK φ₀ hφ₀ Mnat k tA tf S θK G →
    ∀ (a b : ℝ), Set.Icc a b ⊆ Set.Icc tA tf → 1 ≤ D.Λ →
      G.actualFamily.IsTimeMeasurable ∧
      (∀ pc, Measurable (G.actualFamily.weight pc)) ∧
      IsTorusCompatible G.actualFamily (fun _ => ()) (D.eps (G.level - 1)) ∧
      (Set.Icc a b ⊆ ⋃ pc, (G.actualFamily.piece pc).output) ∧
      G.actualFamily.IsTransverseOnPulses (enlargedPulse D G.level (Set.Icc a b)) parallelIndex ∧
      G.actualFamily.IsFastIndependentOn
        (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ G.level ∩ Set.Icc a b) ∧
      ∃ T : G.actualFamily.Atlas,
        T.IsConsecutiveClosed (Set.Icc a b) ∧
        T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ G.level) (Set.Icc a b) ∧
        T.IsQuiet (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1))

/-! Extract the geometry of one incoming invariant on every contained window.
The same incoming atlas is transferred to the actual contexts. No envelope,
chart analysis, model or datum is reconstructed. -/

/-- The incoming invariant supplies all structural geometry of the actual
family, together with one atlas, on every contained preparation window. -/
theorem nativePreparationGeometry : NativePreparationGeometryStatement := by
  intro hr _ _ _ _ _ _ D Dm bw j₀ law P seedK freshK φ₀ hφ₀ Mnat k
    tA tf S θK G hinv a b hsub hΛ
  obtain ⟨hnat, _, _, hshift, _, hcert, _, _, _, _,
    ⟨T, hcons, hcov, hquiet, _, _⟩, htrans, hfast, _⟩ := hinv
  have hcover (t : ℝ) : ∃ p, t ∈ (G.fam.piece p).output := by
    by_contra hnone
    push Not at hnone
    have hzero (p : OddSlot) : ocCutoff D.α D.q D.Λ G.level p.1 t = 0 := by
      rw [← hnat.2.1 p t]
      exact G.fam.weight_zero p t (hnone p)
    obtain ⟨p, hp, _, hpair⟩ := Providers.CascadeInvariants.ocCutoff_active_pair
      (Construction.Stream.ocTau_pos hΛ) t
    rw [hzero ⟨p, hp⟩, hzero ⟨p + 2, hp.add_even even_two⟩] at hpair
    norm_num at hpair
  refine ⟨G.isTimeMeasurable_actualFamily_of_certified hcert
      (fun p => (hnat.1 p).2.1), ?_,
    G.isTorusCompatible_actualFamily
      (GenStage.isTorusCompatible_of_shiftInvariant hnat hshift),
    (fun t _ => Set.mem_iUnion.2 (hcover t)), ?_, ?_, G.actualAtlas T, ?_, ?_,
    G.actualAtlas_isQuiet hquiet⟩
  · intro p
    have hw : G.actualFamily.weight p = ocCutoff D.α D.q D.Λ G.level p.1 :=
      funext (hnat.2.1 p)
    rw [hw]
    exact (CycleReference.ocCutoff_contDiff hΛ p.1).continuous.measurable
  · apply G.isTransverseOnPulses_actualFamily
    intro p pc ctx v u γ d I t ht
    exact htrans p pc ctx v u γ d I t ⟨⟨ht.1.1, hsub ht.1.2⟩, ht.2⟩
  · apply G.isFastIndependentOn_actualFamily
    intro pc ctx v u γ d I t ht
    exact hfast pc ctx v u γ d I t ⟨⟨ht.1.1, hsub ht.1.2⟩, ht.2⟩
  · apply G.actualAtlas_isConsecutiveClosed
    intro p q hpq hlab hne
    exact hcons p q hpq hlab (hne.mono (Set.inter_subset_inter_right _ hsub))
  · apply G.actualAtlas_coversQuiet
    intro p q hpq t ht Y
    exact hcov p q hpq t ⟨⟨⟨ht.1.1.1, hsub ht.1.1.2⟩, ht.1.2⟩, ht.2⟩ Y

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Arithmetic of the literal kernel flux. Representatives are compared almost
 everywhere in space, at every time; this retains every-time integrability in
 the weak solution class.

The degenerate cases are included: empty sums, singleton families, zero coefficients, order zero,
identity fibre maps and an edgeless seed all use the same finite sums. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {k D : ℕ}
  (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem preparation_kernel_input_flux_add_ae
    (y y' : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)) (i : ι) (t : ℝ) :
    P.inputRawFlux (y + y') i t =ᵐ[volume.restrict AVenhance.unitCube]
      P.inputRawFlux y i t + P.inputRawFlux y' i t := by
  have hall : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j, ∀ α : Γ i j,
      ∀ z : JetIndex2 (k + D - 1),
        (y i j α t + y' i j α t).toFunction.jet z x =
          (y i j α t).toFunction.jet z x + (y' i j α t).toFunction.jet z x := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro α
    exact ae_all_iff.mpr (fun z => KernelEnergy.torusJet_add_ae _ _ z)
  filter_upwards [hall] with x hx
  unfold KernelEnergy.TorusKernelOperator.inputRawFlux
  simp only [Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro d _
  rw [← map_add]
  congr 1
  apply (WithLp.ext_iff 2).mpr
  funext word
  exact hx j α _

theorem preparation_kernel_input_flux_smul_ae (c : ℝ)
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)) (i : ι) (t : ℝ) :
    P.inputRawFlux (fun i j α t => c • y i j α t) i t =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => c • P.inputRawFlux y i t x := by
  have hall : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j, ∀ α : Γ i j,
      ∀ z : JetIndex2 (k + D - 1),
        (c • y i j α t).toFunction.jet z x = c • (y i j α t).toFunction.jet z x := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro α
    exact ae_all_iff.mpr (fun z => KernelEnergy.torusJet_smul_ae c _ z)
  filter_upwards [hall] with x hx
  unfold KernelEnergy.TorusKernelOperator.inputRawFlux
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro d _
  rw [← map_smul]
  congr 1
  apply (WithLp.ext_iff 2).mpr
  funext word
  exact hx j α _

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Filter Topology AVRegularity AVenhance Homogenization
open CycleComparison.Coarse
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Positivity and smallness of the enhanced radius covariance constant at late levels.
The constants (`Lam0`, the level threshold) depend only on the profile data, the
radius factor `cr` and the output order, never on stage data.

The degenerate cases are included: `Nout = 0` (constant is zero), `cr` tiny (threshold grows with
`1/cr^2`), levels `m = M` at the terminal level of the band chain. -/

/-- Late-level radius positivity and covariance smallness at the enhanced radius. -/
theorem covariance_small_eventually {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ cr : ℝ, 0 < cr → ∀ Nout : ℕ,
      ∃ mStar : ℕ, 2 ≤ mStar ∧ ∀ (D : OCData) (M : ℕ),
        D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCBandChain α q Λ ζ M D.κ →
        ∀ m : ℕ, mStar ≤ m → m ≤ M → ∀ t : ℝ,
          0 < rhoEnh D cr m ∧
            fbCovConst (rhoEnh D cr m) (covPrimitive D m t) Nout ≤ 1 := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hb⟩ := CycleReference.bandChain_covariance_estimates
    hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ cr hcr Nout => ?_⟩
  have hq1 : 1 < q := hq.1
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hδ := ocDelta_pos_of_admissible hα0 hq
  have hten := (Construction.Preservation.Buffer.preparation_parent_power_tendsto_zero
    (q := q) (Λ := Λ) hq1 hΛ128 hδ).const_mul (4 * (C / cr ^ 2) * (Nout : ℝ) ^ 2)
  rw [mul_zero] at hten
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1
    (hten.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨max m₀ 2, le_max_right _ _, ?_⟩
  intro D M hDα hDq hDΛ hDζ hband m hm hmM t
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hM : 1 ≤ M := by omega
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ M D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ] using hband
  have hκ := CycleReference.bandChain_pos hΛD hζD hbandD (show m - 1 ≤ M by omega)
  have hτ := Construction.Stream.ocTauPP_pos (α := D.α) (q := D.q) (m := m) hΛD
  have hRh : 0 < ocRh D.α D.q D.Λ m (D.κ (m - 1)) := Real.sqrt_pos.mpr (mul_pos hκ hτ)
  have hρ : 0 < rhoEnh D cr m := mul_pos hcr hRh
  refine ⟨hρ, ?_⟩
  have he (i k : Fin 2) := (hb Λ hΛ M hM D.κ hband m hm2 hmM 0 t i k).2.2.2
  have heD (i k : Fin 2) : |covPrimitive D m t i k| / ocRh D.α D.q D.Λ m (D.κ (m - 1)) ^ 2 ≤
      C * D.eps (m - 1) ^ ocDelta D.α D.q := by
    simpa only [covPrimitive, OCData.eps, hDα, hDq, hDΛ, hDζ] using he i k
  have hentry (i k : Fin 2) : |covPrimitive D m t i k| ≤
      (C / cr ^ 2 * D.eps (m - 1) ^ ocDelta D.α D.q) * rhoEnh D cr m ^ 2 := by
    have hb' := (div_le_iff₀ (sq_pos_of_pos hRh)).mp (heD i k)
    convert hb' using 1
    unfold rhoEnh ocRh
    field_simp
  have hp := Construction.Preservation.FullLift.fbCovConst_le_of_radius_entries hρ
    (covPrimitive D m t) (C / cr ^ 2 * D.eps (m - 1) ^ ocDelta D.α D.q) Nout hentry
  refine hp.trans ?_
  have := hm₀ m ((le_max_left _ _).trans hm)
  simp only [OCData.eps, hDα, hDq, hDΛ] at hp ⊢
  convert this using 1
  ring

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Superposition of genuine kernel solutions, including all time traces,
Sobolev lifts and every-time spatial integrability. This adapts the
plane weak-solution proof rather than reconstructing the evolution equation.

Empty and singleton families, zero forcing and datum, and an edgeless seed obey these same
identities. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {k D : ℕ}
  (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
  (v : ℝ → Vec 2 → Vec 2)
  (f f' : ∀ i, TorusHk k (h i))
  (F F' : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g g' u u' : ∀ i, ℝ → TorusHk k (h i))
  (w w' : ∀ i, ℝ → TorusHk (k + 1) (h i))
  (y y' : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))

theorem preparation_kernel_solution_add
    (hs : IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f F g u w y)
    (hs' : IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f' F' g' u' w' y') :
    IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S (f + f') (F + F') (g + g')
      (u + u') (w + w') (y + y') := by
  refine ⟨fun i => (hs.1 i).add (hs'.1 i), fun i => CoupledEnergy.Variational.timeMemLp_pointwise_add _ 2
    (w i) (w' i) (hs.2.1 i) (hs'.2.1 i),
    ?_, ?_, fun i j α => CoupledEnergy.Variational.timeMemLp_pointwise_add _ 2
      (y i j α) (y' i j α) (hs.2.2.2.2.1 i j α) (hs'.2.2.2.2.1 i j α), ?_, ?_⟩
  · intro i
    filter_upwards [hs.2.2.1 i, hs'.2.2.1 i] with s hsu hsu'
    change truncateTorusHk (Nat.le_succ k) (w i s + w' i s) = u i s + u' i s
    rw [map_add, hsu, hsu']
  · intro i
    change u i a + u' i a = f i + f' i
    rw [hs.2.2.2.1 i, hs'.2.2.2.1 i]
  · intro i j α
    filter_upwards [hs.2.2.2.2.2.1 i j α, hs'.2.2.2.2.2.1 i j α] with s hy hy'
    change (y i j α s).val (valueIndex2 (k + D - 1)) +
        (y' i j α s).val (valueIndex2 (k + D - 1)) =
      P.S i j α s (((P.C i j α).compLpL 2 (volume.restrict AVenhance.unitCube))
        ((w j s).val (valueIndex2 (k + 1)) + (w' j s).val (valueIndex2 (k + 1))))
    rw [map_add, map_add, hy, hy']
    rfl
  · intro i t ht φ
    let p := φ.toFunction.jet (valueIndex2 1)
    let dp := fun m => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m⟩
    let du := fun s m => (w i s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m⟩
    let du' := fun s m => (w' i s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m⟩
    let Q := fun s => P.inputRawFlux y i s
    let Q' := fun s => P.inputRawFlux y' i s
    let ff := fun s => (F i s).toFunction.jet (valueIndex2 k)
    let ff' := fun s => (F' i s).toFunction.jet (valueIndex2 k)
    let gg := fun s => (g i s).toFunction.jet (valueIndex2 k)
    let gg' := fun s => (g' i s).toFunction.jet (valueIndex2 k)
    have hsum := coupledWeakIdentity_add (volume.restrict AVenhance.unitCube) ν a t v
      _ _ _ _ p dp du du' Q Q' ff ff' gg gg'
      (hs.2.2.2.2.2.2 i t ht φ) (hs'.2.2.2.2.2.2 i t ht φ)
    apply coupledWeakIdentity_integrands_congr (volume.restrict AVenhance.unitCube) ν a t v v
      _ _ _ _ p p dp dp (du + du') _ (Q + Q') _ (ff + ff') _ (gg + gg') _ _ _ _ hsum
    · filter_upwards [KernelEnergy.torusJet_add_ae (u i t) (u' i t) (valueIndex2 k)] with x hx
      exact congrArg (fun z => inner ℝ z (p x)) hx.symm
    · filter_upwards [KernelEnergy.torusJet_add_ae (f i) (f' i) (valueIndex2 k)] with x hx
      exact congrArg (fun z => inner ℝ z (p x)) hx.symm
    · intro s _
      apply weakIdentityRhs_congr_ae (volume.restrict AVenhance.unitCube) ν s v v p p dp dp
        (du + du') _ (Q + Q') _ (ff + ff') _ (gg + gg') _
        Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
      · intro m
        exact (KernelEnergy.torusJet_add_ae (w i s) (w' i s)
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m⟩).symm
      · exact (preparation_kernel_input_flux_add_ae P y y' i s).symm
      · exact (KernelEnergy.torusJet_add_ae (F i s) (F' i s) (valueIndex2 k)).symm
      · exact (KernelEnergy.torusJet_add_ae (g i s) (g' i s) (valueIndex2 k)).symm

theorem preparation_kernel_solution_smul (c : ℝ)
    (hs : IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f F g u w y) :
    IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S (fun i => c • f i) (fun i t => c • F i t) (fun i t => c • g i t)
      (fun i t => c • u i t) (fun i t => c • w i t) (fun i j α t => c • y i j α t) := by
  refine ⟨fun i => (hs.1 i).const_smul c, fun i => (hs.2.1 i).const_smul c,
    ?_, ?_, fun i j α => (hs.2.2.2.2.1 i j α).const_smul c, ?_, ?_⟩
  · intro i
    filter_upwards [hs.2.2.1 i] with s hsu
    change truncateTorusHk (Nat.le_succ k) (c • w i s) = c • u i s
    rw [map_smul, hsu]
  · intro i
    change c • u i a = c • f i
    rw [hs.2.2.2.1 i]
  · intro i j α
    filter_upwards [hs.2.2.2.2.2.1 i j α] with s hy
    change c • (y i j α s).val (valueIndex2 (k + D - 1)) =
      P.S i j α s (((P.C i j α).compLpL 2 (volume.restrict AVenhance.unitCube))
        (c • (w j s).val (valueIndex2 (k + 1))))
    rw [map_smul, map_smul, hy]
    rfl
  · intro i t ht φ
    let p := φ.toFunction.jet (valueIndex2 1)
    let dp := fun m => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => m⟩
    let du := fun s m => (w i s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m⟩
    let Q := fun s => P.inputRawFlux y i s
    let ff := fun s => (F i s).toFunction.jet (valueIndex2 k)
    let gg := fun s => (g i s).toFunction.jet (valueIndex2 k)
    have hscaled := coupledWeakIdentity_smul (volume.restrict AVenhance.unitCube) c ν a t v
      _ _ p dp du Q ff gg (hs.2.2.2.2.2.2 i t ht φ)
    apply coupledWeakIdentity_integrands_congr (volume.restrict AVenhance.unitCube) ν a t v v
      _ _ _ _ p p dp dp (c • du) _ (c • Q) _ (c • ff) _ (c • gg) _ _ _ _ hscaled
    · filter_upwards [KernelEnergy.torusJet_smul_ae c (u i t) (valueIndex2 k)] with x hx
      exact congrArg (fun z => inner ℝ z (p x)) hx.symm
    · filter_upwards [KernelEnergy.torusJet_smul_ae c (f i) (valueIndex2 k)] with x hx
      exact congrArg (fun z => inner ℝ z (p x)) hx.symm
    · intro s _
      apply weakIdentityRhs_congr_ae (volume.restrict AVenhance.unitCube) ν s v v p p dp dp
        (c • du) _ (c • Q) _ (c • ff) _ (c • gg) _
        Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
      · intro m
        exact (KernelEnergy.torusJet_smul_ae c (w i s)
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => m⟩).symm
      · exact (preparation_kernel_input_flux_smul_ae P c y i s).symm
      · exact (KernelEnergy.torusJet_smul_ae c (F i s) (valueIndex2 k)).symm
      · exact (KernelEnergy.torusJet_smul_ae c (g i s) (valueIndex2 k)).symm

/-- Values outside the solution window are immaterial to the native equation.
This lets the canonical trace use one fixed endpoint projection for all data. -/
theorem preparation_kernel_solution_trace_congr
    (hs : IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f F g u w y)
    (hu : ∀ i, ∀ t ∈ Set.Icc a b, u' i t = u i t) :
    IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f F g u' w y := by
  refine ⟨fun i => (hs.1 i).congr (fun t ht => hu i t ht), hs.2.1, ?_, ?_,
    hs.2.2.2.2.1, hs.2.2.2.2.2.1, ?_⟩
  · intro i
    filter_upwards [hs.2.2.1 i, ae_restrict_mem measurableSet_Icc] with t hwt ht
    exact hwt.trans (hu i t ht).symm
  · intro i
    exact (hu i a ⟨le_rfl, P.htime⟩).trans (hs.2.2.2.1 i)
  · intro i t ht φ
    simpa only [hu i t ht] using hs.2.2.2.2.2.2 i t ht φ

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
