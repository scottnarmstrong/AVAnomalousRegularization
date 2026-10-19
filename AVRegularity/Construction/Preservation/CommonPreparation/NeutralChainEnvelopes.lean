-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Scales.Times
import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
public import AVRegularity.Statements.Intermediate.CycleJoint.IsJointError
public import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleJoint.PathReduction.Paths
import AVRegularity.Families.QuietTransitionBridge
public import AVRegularity.Definitions.CycleJoint.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.IsMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The physical energy carrier for common preparation retains the continuous
trace on the WHOLE solution window and an ambient higher L2 class after the
buffer. Its weighted trace norm is a whole-family supremum, not a sum of
component suprema. Stopping and post-buffer extension are linear, without
closed-submodule instance searches or choices of time representatives.

The degenerate cases are included: zero datum, empty and singleton component families, identity
geometry, order zero, edgeless seeds and zero-length windows use the same
formulas. The post-buffer extension subtracts its own initial value, so it is
zero before the buffer and is contractive for zero-initial paths. -/

variable {H V Q Z : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Native low-order traces and ambient post-buffer higher time classes. -/
abbrev PreparationEnergyPath (H V : Type*) [TopologicalSpace H]
    [NormedAddCommGroup V] (a b c : ℝ) :=
  C(Set.Icc a b, H) × Lp V 2 (volume.restrict (Set.Icc c b))

/-- Clamp a whole-window time to the post-buffer window. -/
def preparationPostTime {a b c : ℝ} (hcb : c ≤ b) :
    C(Set.Icc a b, Set.Icc c b) :=
  ⟨fun t => Set.projIcc c b hcb t, continuous_projIcc.comp continuous_subtype_val⟩

/-- Stop a whole-window path at the buffer endpoint. -/
def preparationStopTime {a b c : ℝ} (hac : a ≤ c) :
    C(Set.Icc a b, Set.Icc a b) :=
  ⟨fun t => ⟨min (t : ℝ) c,
    ⟨le_min t.property.1 hac, (min_le_left _ _).trans t.property.2⟩⟩,
    Continuous.subtype_mk (continuous_subtype_val.min continuous_const) _⟩

/-- A stopped native path is a linear function of the original path. -/
def preparationStoppedPath {a b c : ℝ} (hac : a ≤ c) :
    C(Set.Icc a b, H) →L[ℝ] C(Set.Icc a b, H) :=
  ContinuousMap.compCLM (R := ℝ) (M := H) (preparationStopTime hac)

/-- Zero-initial extension of a post-buffer path to the whole window. -/
def preparationPostExtension {a b c : ℝ} (hcb : c ≤ b) :
    C(Set.Icc c b, H) →L[ℝ] C(Set.Icc a b, H) :=
  ContinuousMap.compCLM (R := ℝ) (M := H) (preparationPostTime hcb) -
    (ContinuousLinearMap.const ℝ (Set.Icc a b)).comp
      (ContinuousMap.evalCLM (R := ℝ) (⟨c, le_rfl, hcb⟩ : Set.Icc c b))

/-- Before the buffer the extension is exactly zero. -/
theorem preparation_post_extension_before {a b c : ℝ} (hcb : c ≤ b)
    (u : C(Set.Icc c b, H)) (t : Set.Icc a b) (ht : (t : ℝ) ≤ c) :
    preparationPostExtension hcb u t = 0 := by
  change u (Set.projIcc c b hcb t) - u ⟨c, le_rfl, hcb⟩ = 0
  rw [Set.projIcc_of_le_left hcb ht, sub_self]

/-- After the buffer the extension is the original path minus its initial value. -/
theorem preparation_post_extension_after {a b c : ℝ} (hcb : c ≤ b)
    (u : C(Set.Icc c b, H)) (t : Set.Icc a b) (ht : c ≤ (t : ℝ)) :
    preparationPostExtension hcb u t = u ⟨t, ht, t.property.2⟩ - u ⟨c, le_rfl, hcb⟩ := by
  change u (Set.projIcc c b hcb t) - u ⟨c, le_rfl, hcb⟩ = _
  rw [Set.projIcc_of_mem hcb ⟨ht, t.property.2⟩]

/-- Stopping preserves the original path before the buffer. -/
theorem preparation_stopped_path_before {a b c : ℝ} (hac : a ≤ c)
    (u : C(Set.Icc a b, H)) (t : Set.Icc a b) (ht : (t : ℝ) ≤ c) :
    preparationStoppedPath hac u t = u t := by
  change u ⟨min (t : ℝ) c, _⟩ = u t
  congr 1
  exact Subtype.ext (min_eq_left ht)

/-- After the buffer a stopped path retains its endpoint. -/
theorem preparation_stopped_path_after {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (u : C(Set.Icc a b, H)) (t : Set.Icc a b) (ht : c ≤ (t : ℝ)) :
    preparationStoppedPath hac u t = u ⟨c, hac, hcb⟩ := by
  change u ⟨min (t : ℝ) c, _⟩ = u ⟨c, hac, hcb⟩
  congr 1
  exact Subtype.ext (min_eq_right ht)

/-- A zero-initial post-buffer response extends without a factor in its supremum norm. -/
theorem preparation_post_extension_norm_le {a b c : ℝ} (hcb : c ≤ b)
    (u : C(Set.Icc c b, H)) (hu : u ⟨c, le_rfl, hcb⟩ = 0) :
    ‖preparationPostExtension (a := a) hcb u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  change ‖u (Set.projIcc c b hcb t) - u ⟨c, le_rfl, hcb⟩‖ ≤ ‖u‖
  rw [hu, sub_zero]
  exact u.norm_coe_le_norm _

/-- Glue the stopped native trace to a scalar response with the same buffer value. -/
def preparationRestartedPath {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    C(Set.Icc a b, H) × C(Set.Icc c b, H) →L[ℝ] C(Set.Icc a b, H) :=
  (preparationStoppedPath hac).comp (ContinuousLinearMap.fst ℝ _ _) +
    (preparationPostExtension hcb).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The glued path is the whole native path up to the buffer. -/
theorem preparation_restarted_path_before {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (u : C(Set.Icc a b, H)) (v : C(Set.Icc c b, H))
    (t : Set.Icc a b) (ht : (t : ℝ) ≤ c) :
    preparationRestartedPath hac hcb (u, v) t = u t := by
  change preparationStoppedPath hac u t + preparationPostExtension hcb v t = u t
  rw [preparation_stopped_path_before hac u t ht,
    preparation_post_extension_before hcb v t ht, add_zero]

/-- The glued path is the scalar response after the buffer, with the full native buffer datum. -/
theorem preparation_restarted_path_after {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (u : C(Set.Icc a b, H)) (v : C(Set.Icc c b, H))
    (hmatch : u ⟨c, hac, hcb⟩ = v ⟨c, le_rfl, hcb⟩)
    (t : Set.Icc a b) (ht : c ≤ (t : ℝ)) :
    preparationRestartedPath hac hcb (u, v) t = v ⟨t, ht, t.property.2⟩ := by
  change preparationStoppedPath hac u t + preparationPostExtension hcb v t = _
  rw [preparation_stopped_path_after hac hcb u t ht,
    preparation_post_extension_after hcb v t ht, hmatch, ← add_sub_assoc, add_sub_cancel_left]

/-- The whole-window weighted trace readout. The family weight is already in L. -/
def preparationPathTraceReadout (a b c : ℝ) (L : H →L[ℝ] Q) :
    PreparationEnergyPath H V a b c →L[ℝ] C(Set.Icc a b, Q) :=
  (ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc a b) L).comp (ContinuousLinearMap.fst ℝ _ _)

/-- The gradient readout acts on its L2 class, hence is representative-independent. -/
def preparationPathGradientReadout (a b c : ℝ) (G : V →L[ℝ] Z) :
    PreparationEnergyPath H V a b c →L[ℝ] Lp Z 2 (volume.restrict (Set.Icc c b)) :=
  (G.compLpL 2 (volume.restrict (Set.Icc c b))).comp (ContinuousLinearMap.snd ℝ _ _)

/-- Physical energy is the weighted trace supremum plus sqrt(nu) times the
weighted gradient L2 norm. The gradient map can include the fixed native graph readout. -/
def preparationPathEnergy (a b c : ℝ) (L : H →L[ℝ] Q) (G : V →L[ℝ] Z) (ν : ℝ) :
    Seminorm ℝ (PreparationEnergyPath H V a b c) :=
  (normSeminorm ℝ _).comp (preparationPathTraceReadout a b c L).toLinearMap +
    (normSeminorm ℝ _).comp
      (Real.sqrt ν • preparationPathGradientReadout (H := H) a b c G).toLinearMap

/-- The energy formula uses one whole-family supremum. -/
theorem preparation_path_energy_eq (a b c : ℝ) (L : H →L[ℝ] Q) (G : V →L[ℝ] Z) (ν : ℝ)
    (x : PreparationEnergyPath H V a b c) :
    preparationPathEnergy a b c L G ν x =
      ‖ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc a b) L x.1‖ + Real.sqrt ν * ‖G.compLpL 2 (volume.restrict (Set.Icc c b)) x.2‖ := by
  change ‖ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc a b) L x.1‖ +
    ‖Real.sqrt ν • (G.compLpL 2 (volume.restrict (Set.Icc c b)) x.2)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ν)]

/-- Every time trace is bounded by the physical energy with leading constant one. -/
theorem preparation_path_trace_le_energy {a b c : ℝ} (L : H →L[ℝ] Q) (G : V →L[ℝ] Z)
    (ν : ℝ) (x : PreparationEnergyPath H V a b c) (t : Set.Icc a b) :
    ‖L (x.1 t)‖ ≤ preparationPathEnergy a b c L G ν x := by
  rw [preparation_path_energy_eq]
  exact ((ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc a b) L x.1).norm_coe_le_norm t).trans
    (le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg ν) (norm_nonneg _)))

/-- Extend a post-buffer energy response, retaining its higher class. -/
def preparationPostEnergyExtension {a b c : ℝ} (hcb : c ≤ b) :
    PreparationEnergyPath H V c b c →L[ℝ] PreparationEnergyPath H V a b c :=
  (preparationPostExtension hcb).prodMap (ContinuousLinearMap.id ℝ _)

/-- Glue the old native trace to a restarted scalar response, keeping the latter's higher class. -/
def preparationRestartEnergyPath {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    C(Set.Icc a b, H) × PreparationEnergyPath H V c b c →L[ℝ]
      PreparationEnergyPath H V a b c := by
  let A : C(Set.Icc a b, H) × PreparationEnergyPath H V c b c →L[ℝ]
      C(Set.Icc a b, H) × C(Set.Icc c b, H) :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
  let B : C(Set.Icc a b, H) × PreparationEnergyPath H V c b c →L[ℝ]
      Lp V 2 (volume.restrict (Set.Icc c b)) :=
    (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  exact ((preparationRestartedPath hac hcb).comp A).prod B

/-- The initial source-insertion path retains the FULL native buffer datum. -/
def preparationBufferedInitialMap {S : Type*} [AddCommGroup S] [Module ℝ S]
    {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (F : S →ₗ[ℝ] PreparationEnergyPath H V a b c)
    (J : H →ₗ[ℝ] PreparationEnergyPath H V c b c) :
    S →ₗ[ℝ] PreparationEnergyPath H V a b c := by
  let U := (ContinuousLinearMap.fst ℝ _ _).toLinearMap.comp F
  let B := (ContinuousMap.evalCLM (R := ℝ) (⟨c, hac, hcb⟩ : Set.Icc a b)).toLinearMap.comp U
  exact (preparationRestartEnergyPath hac hcb).toLinearMap.comp (U.prod (J.comp B))

/-- Kernel insertion acts only on the post-buffer higher class and is zero before the buffer. -/
def preparationBufferedKernelMap {a b c : ℝ} (hcb : c ≤ b)
    (J : Lp V 2 (volume.restrict (Set.Icc c b)) →ₗ[ℝ] PreparationEnergyPath H V c b c) :
    PreparationEnergyPath H V a b c →ₗ[ℝ] PreparationEnergyPath H V a b c :=
  (preparationPostEnergyExtension hcb).toLinearMap.comp
    (J.comp (ContinuousLinearMap.snd ℝ _ _).toLinearMap)

/-- The three actual linear maps used by buffered source insertion. -/
structure PreparationBufferedMaps (H V : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (a b c : ℝ) where
  full : H →ₗ[ℝ] PreparationEnergyPath H V a b c
  homogeneous : H →ₗ[ℝ] PreparationEnergyPath H V c b c
  source : Lp V 2 (volume.restrict (Set.Icc c b)) →ₗ[ℝ]
    PreparationEnergyPath H V c b c

/-- The exact buffered identity in the common physical carrier. -/
def PreparationBufferedMaps.IsFixedPoint {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps H V a b c) : Prop :=
  ∀ f, M.full f = preparationBufferedInitialMap hac hcb M.full M.homogeneous f +
    preparationBufferedKernelMap hcb M.source (M.full f)

/-- Before the buffer the initial path is the original native path. -/
theorem preparation_buffered_initial_before {S : Type*} [AddCommGroup S] [Module ℝ S]
    {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (F : S →ₗ[ℝ] PreparationEnergyPath H V a b c)
    (J : H →ₗ[ℝ] PreparationEnergyPath H V c b c)
    (f : S) (t : Set.Icc a b) (ht : (t : ℝ) ≤ c) :
    (preparationBufferedInitialMap hac hcb F J f).1 t = (F f).1 t := by
  change preparationRestartedPath hac hcb ((F f).1, (J ((F f).1 ⟨c, hac, hcb⟩)).1) t = _
  exact preparation_restarted_path_before hac hcb _ _ t ht

/-- After the buffer the initial path is the scalar homogeneous response with the native buffer datum. -/
theorem preparation_buffered_initial_after {S : Type*} [AddCommGroup S] [Module ℝ S]
    {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (F : S →ₗ[ℝ] PreparationEnergyPath H V a b c)
    (J : H →ₗ[ℝ] PreparationEnergyPath H V c b c)
    (hJ : ∀ d, (J d).1 ⟨c, le_rfl, hcb⟩ = d)
    (f : S) (t : Set.Icc a b) (ht : c ≤ (t : ℝ)) :
    (preparationBufferedInitialMap hac hcb F J f).1 t =
      (J ((F f).1 ⟨c, hac, hcb⟩)).1 ⟨t, ht, t.property.2⟩ := by
  change preparationRestartedPath hac hcb ((F f).1, (J ((F f).1 ⟨c, hac, hcb⟩)).1) t = _
  exact preparation_restarted_path_after hac hcb _ _ (hJ _).symm t ht

/-- Kernel insertion is identically zero on the pre-buffer trace. -/
theorem preparation_buffered_kernel_before {a b c : ℝ} (hcb : c ≤ b)
    (J : Lp V 2 (volume.restrict (Set.Icc c b)) →ₗ[ℝ] PreparationEnergyPath H V c b c)
    (x : PreparationEnergyPath H V a b c) (t : Set.Icc a b) (ht : (t : ℝ) ≤ c) :
    (preparationBufferedKernelMap hcb J x).1 t = 0 := by
  change preparationPostExtension hcb (J x.2).1 t = 0
  exact preparation_post_extension_before hcb _ t ht

/-- After the buffer, insertion is the unmodified zero-initial scalar source response. -/
theorem preparation_buffered_kernel_after {a b c : ℝ} (hcb : c ≤ b)
    (J : Lp V 2 (volume.restrict (Set.Icc c b)) →ₗ[ℝ] PreparationEnergyPath H V c b c)
    (hJ : ∀ U, (J U).1 ⟨c, le_rfl, hcb⟩ = 0)
    (x : PreparationEnergyPath H V a b c) (t : Set.Icc a b) (ht : c ≤ (t : ℝ)) :
    (preparationBufferedKernelMap hcb J x).1 t = (J x.2).1 ⟨t, ht, t.property.2⟩ := by
  change preparationPostExtension hcb (J x.2).1 t = _
  rw [preparation_post_extension_after hcb _ t ht, hJ x.2, sub_zero]

/-- Post-buffer trace and higher-class identities imply the whole buffered identity. -/
theorem preparation_buffered_maps_eq {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (M : PreparationBufferedMaps H V a b c) (f : H)
    (h₀ : ∀ d, (M.homogeneous d).1 ⟨c, le_rfl, hcb⟩ = d)
    (hk : ∀ U, (M.source U).1 ⟨c, le_rfl, hcb⟩ = 0)
    (hpost : ∀ t : Set.Icc a b, ∀ ht : c ≤ (t : ℝ),
      (M.full f).1 t =
        (M.homogeneous ((M.full f).1 ⟨c, hac, hcb⟩)).1 ⟨t, ht, t.property.2⟩ +
        (M.source (M.full f).2).1 ⟨t, ht, t.property.2⟩)
    (hhigher : (M.full f).2 =
      (M.homogeneous ((M.full f).1 ⟨c, hac, hcb⟩)).2 + (M.source (M.full f).2).2) :
    M.full f = preparationBufferedInitialMap hac hcb M.full M.homogeneous f +
      preparationBufferedKernelMap hcb M.source (M.full f) := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    rcases le_total (t : ℝ) c with ht | ht
    · rw [Prod.fst_add, ContinuousMap.add_apply,
        preparation_buffered_initial_before hac hcb M.full M.homogeneous f t ht,
        preparation_buffered_kernel_before hcb M.source (M.full f) t ht, add_zero]
    · rw [Prod.fst_add, ContinuousMap.add_apply,
        preparation_buffered_initial_after hac hcb M.full M.homogeneous h₀ f t ht,
        preparation_buffered_kernel_after hcb M.source hk (M.full f) t ht]
      exact hpost t ht
  · exact hhigher

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Exact finite source expansion and defect recurrence from
The unregularized layers may live initially at
descending Sobolev orders: only their common low-order readouts occur here.
No unregularized endomorphism on a fixed finite Sobolev space is assumed.

The degenerate cases are included: depth zero leaves the actual-solution tail; a zero defect makes
each plain layer its regularized counterpart; a zero source kills the positive tail.
The zero space (empty family) and zero datum satisfy all identities. -/

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- A fixed-point identity has an exact finite expansion, retaining the actual solution in its tail. -/
theorem source_insertion_finite_expansion (T : X →ₗ[ℝ] X) (u u₀ : X)
    (hu : u = u₀ + T u) (n : ℕ) :
    u = (∑ h ∈ Finset.range n, (T ^ h) u₀) + (T ^ n) u := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, pow_zero, Module.End.one_apply, zero_add]
  | succ n ih =>
    have hs : (T ^ n) u = (T ^ n) u₀ + (T ^ (n + 1)) u := by
      conv_lhs => rw [hu]
      rw [map_add, pow_succ, Module.End.mul_apply]
    rw [Finset.sum_range_succ]
    exact ih.trans (hs ▸ (add_assoc _ _ _).symm)

/-- The finite error is the layer-difference sum plus the actual regularized tail. -/
theorem source_insertion_error_identity (TS : X →ₗ[ℝ] X) (Z : ℕ → X) (u u₀ : X)
    (hu : u = u₀ + TS u) (n : ℕ) :
    u - (∑ h ∈ Finset.range n, Z h) =
      (∑ h ∈ Finset.range n, ((TS ^ h) u₀ - Z h)) + (TS ^ n) u := by
  rw [Finset.sum_sub_distrib]
  have he := source_insertion_finite_expansion TS u u₀ hu n
  conv_lhs => rw [he]
  abel

/-- Bounds for the first n defects suffice: no reserve beyond the finite chain is used. -/
theorem source_insertion_difference_le (p : Seminorm ℝ X) (TS : X →ₗ[ℝ] X)
    (Z : ℕ → X) (u₀ : X) (hZ : Z 0 = u₀) (D : ℝ) (hTS : ∀ x, p (TS x) ≤ p x)
    (n : ℕ) : (∀ h, h < n → p (Z (h + 1) - TS (Z h)) ≤ D) →
      p (Z n - (TS ^ n) u₀) ≤ (n : ℝ) * D := by
  induction n with
  | zero => intro _; simp only [hZ, pow_zero, Module.End.one_apply, sub_self,
      map_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    intro hdef
    have he : Z (n + 1) - (TS ^ (n + 1)) u₀ =
        TS (Z n - (TS ^ n) u₀) + (Z (n + 1) - TS (Z n)) := by
      rw [pow_succ', Module.End.mul_apply, map_sub]
      abel
    rw [he]
    calc _ ≤ p (TS (Z n - (TS ^ n) u₀)) + p (Z (n + 1) - TS (Z n)) :=
        map_add_le_add p _ _
      _ ≤ (n : ℝ) * D + D :=
        add_le_add ((hTS _).trans (ih (fun h hh => hdef h (Nat.lt_succ_of_lt hh))))
          (hdef n (Nat.lt_succ_self n))
      _ = _ := by rw [Nat.cast_succ]; ring

/-- Iteration of a bounded source operator gives its geometric tail budget. -/
theorem source_insertion_tail_le (p : Seminorm ℝ X) (T : X →ₗ[ℝ] X)
    (β : ℝ) (hβ : 0 ≤ β) (hT : ∀ x, p (T x) ≤ β * p x) (n : ℕ) (u : X) :
    p ((T ^ n) u) ≤ β ^ n * p u := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, one_mul, le_refl]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hT _).trans ((mul_le_mul_of_nonneg_left ih hβ).trans_eq (by rw [pow_succ]; ring))

/-- The expansion error has separately priced finite defects and actual-solution tail.
The Z layers need no common high-order domain or small unregularized operator norm. -/
theorem source_insertion_error_le (p : Seminorm ℝ X) (TS : X →ₗ[ℝ] X)
    (Z : ℕ → X) (u u₀ : X) (hZ : Z 0 = u₀) (hu : u = u₀ + TS u)
    (β D : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hTS : ∀ x, p (TS x) ≤ β * p x)
    (n : ℕ) (hdef : ∀ h, h + 1 < n → p (Z (h + 1) - TS (Z h)) ≤ D) :
    p (u - (∑ h ∈ Finset.range n, Z h)) ≤
      (∑ h ∈ Finset.range n, (h : ℝ) * D) + β ^ n * p u := by
  rw [source_insertion_error_identity TS Z u u₀ hu n]
  refine (map_add_le_add p _ _).trans (add_le_add ?_ (source_insertion_tail_le p TS β hβ hTS n u))
  have hsum : p (∑ h ∈ Finset.range n, ((TS ^ h) u₀ - Z h)) ≤
      ∑ h ∈ Finset.range n, p ((TS ^ h) u₀ - Z h) := by
    clear hdef
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, map_zero, le_refl]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact (map_add_le_add p _ _).trans (add_le_add ih le_rfl)
  refine hsum.trans (Finset.sum_le_sum fun h hh => ?_)
  have hs : (TS ^ h) u₀ - Z h = -(Z h - (TS ^ h) u₀) := by abel
  rw [hs, map_neg_eq_map]
  exact source_insertion_difference_le p TS Z u₀ hZ D
    (fun x => (hTS x).trans (mul_le_of_le_one_left (apply_nonneg p _) hβ1)) h
      (fun j hj => hdef j ((Nat.succ_le_of_lt hj).trans_lt (Finset.mem_range.mp hh)))

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! If the first-order jets of an element of `TorusHk (K+1) E` vanish, so do all its jets of
positive order. Each ordered jet is the value of an `H^1` element (as in the cell Poincare
argument) and an `H^1` element with zero value is zero.

The degenerate cases are included: `K = 0` has only the first-order jets, which are the hypothesis;
the zero element satisfies the hypothesis; the fibre `E` may be trivial. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The `H^1` field of an ordered jet of a higher element. -/
def OrderedH1 {K : ℕ} (u : TorusHk (K + 1) E) (j : Fin (K + 1))
    (w : DerivativeWord2 j.val) : TorusHk 1 E :=
  derivativeTorusHk w (truncateTorusHk (by omega : 1 + j.val ≤ K + 1) u)

omit [FiniteDimensional ℝ E] in
theorem OrderedH1_value {K : ℕ} (u : TorusHk (K + 1) E) (j : Fin (K + 1))
    (w : DerivativeWord2 j.val) :
    (OrderedH1 u j w).val (valueIndex2 1) = u.val (lowerIndex2 j w) := by
  simp only [OrderedH1, derivativeTorusHk_apply, truncateTorusHk_apply]
  apply congrArg (fun a => u.val a)
  apply Sigma.ext
  · apply Fin.ext
    simp [truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex, lowerIndex2, lowerIndex]
  · simp [truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex, lowerIndex2, lowerIndex]

omit [FiniteDimensional ℝ E] in
theorem OrderedH1_derivative {K : ℕ} (u : TorusHk (K + 1) E)
    (j : Fin (K + 1)) (w : DerivativeWord2 j.val) (i : Fin 2) :
    (OrderedH1 u j w).val ⟨⟨1, by decide⟩, fun _ => i⟩ = u.val (nextIndex2 j w i) := by
  simp only [OrderedH1, derivativeTorusHk_apply, truncateTorusHk_apply]
  apply congrArg (fun a => u.val a)
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · simp [truncateJetIndex, prefixJetIndex, nextIndex2, nextIndex,
      Fin.append_right_eq_snoc]

/-- An `H^1` element with zero value has zero first-order jets. -/
theorem h1_grad_zero (u : TorusHk 1 E) (h : u.val (valueIndex2 1) = 0) (i : Fin 2) :
    u.val ⟨⟨1, by decide⟩, fun _ => i⟩ = 0 := by
  have hu : u = 0 := TorusHk.ext_value (by rw [h]; rfl)
  rw [hu]
  rfl

/-- First-order jets zero implies every jet of positive order zero. -/
theorem jet_zero {K : ℕ} (Y : TorusHk (K + 1) E)
    (h1 : ∀ i, Y.val (nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 i) = 0) :
    ∀ r (hr : r ≤ K) (w : DerivativeWord2 (r + 1)),
      Y.val ⟨⟨r + 1, by omega⟩, w⟩ = 0 := by
  intro r
  induction r with
  | zero =>
    intro hr w
    have he : (⟨⟨0 + 1, by omega⟩, w⟩ : JetIndex2 (K + 1)) =
        nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 (w 0) := by
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · apply heq_of_eq
        show w = Fin.snoc (α := fun _ => Fin 2) Fin.elim0 (w 0)
        funext j
        have hj : j = 0 := Fin.ext (by omega)
        subst hj
        simp [Fin.snoc]
    rw [he]
    exact h1 _
  | succ r ih =>
    intro hr w
    have hlow := ih (by omega) (Fin.init w)
    have hH : (OrderedH1 Y ⟨r + 1, by omega⟩ (Fin.init w)).val (valueIndex2 1) = 0 := by
      rw [OrderedH1_value]
      exact hlow
    have hh := h1_grad_zero _ hH (w (Fin.last (r + 1)))
    rw [OrderedH1_derivative] at hh
    have he : (⟨⟨r + 1 + 1, by omega⟩, w⟩ : JetIndex2 (K + 1)) =
        nextIndex2 (⟨r + 1, by omega⟩ : Fin (K + 1)) (Fin.init w) (w (Fin.last (r + 1))) := by
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · simp [nextIndex2, nextIndex, Fin.snoc_init_self]
    rw [he]
    exact hh

/-- Order-indexed form: from vanishing first-order jets to all jets of order `1 ≤ r ≤ L`. -/
theorem jet_zero_of_order_one {L : ℕ} (hL : 1 ≤ L) (Y : TorusHk L E)
    (h1 : ∀ i : Fin 2, Y.val ⟨⟨1, by omega⟩, fun _ => i⟩ = 0)
    (r : ℕ) (hr : 1 ≤ r) (hrL : r ≤ L) (w : DerivativeWord2 r) :
    Y.val ⟨⟨r, by omega⟩, w⟩ = 0 := by
  obtain ⟨K, rfl⟩ : ∃ K, L = K + 1 := ⟨L - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  refine jet_zero Y (fun i => ?_) r (by omega) w
  have he : nextIndex2 (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) Fin.elim0 i =
      (⟨⟨1, by omega⟩, fun _ => i⟩ : JetIndex2 (K + 1)) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · apply heq_of_eq
      show Fin.snoc (α := fun _ => Fin 2) Fin.elim0 i = fun _ => i
      funext j
      have hj : j = 0 := Fin.ext (by omega)
      subst hj
      simp [Fin.snoc]
  rw [he]
  exact h1 i

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The incoming ledger and its native tower price become small at one
uniform level floor. The rounded adjacent-wavelength estimate supplies
exactly q*theta parent powers for the kernel tail used by the early depth.
The degenerate cases are included: A=0 or CI=0, empty or edgeless families, identity geometry and
zero data do not require division by a coefficient or a datum. The floor
precedes every actual band chain, family, observation window and datum. -/

/-- The original-stage ledger and kernel tail have one deep-level budget,
with the explicit rounded-step constant fixed before every stage datum. -/
theorem preparation_native_price_threshold {q θ : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hq₁ : q < 17 / 16) (hΛ : 128 ≤ Λ) (hθ : 0 < θ)
    (A CI : ℝ) (hA : 0 ≤ A) (hCI : 0 ≤ CI) :
    ∃ mStar : ℕ, 2 ≤ mStar ∧ ∀ m : ℕ, mStar ≤ m →
      CI * ocEpsilon q Λ m ^ θ ≤ 1 ∧
      7 * |A * (CI * ocEpsilon q Λ m ^ θ)| ≤ 1 ∧
      7 * |A * (CI * ocEpsilon q Λ m ^ θ)| ≤
        (7 * A * CI * (2 : ℝ) ^ θ) * ocEpsilon q Λ (m - 1) ^ (q * θ) := by
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hb : 0 < q * θ := mul_pos hq₀ hθ
  obtain ⟨mStar, hm2, hsmall⟩ := Buffer.preparation_parameters_eventually_small
    hq hΛ hb hb (CI * (2 : ℝ) ^ θ) (7 * A * CI * (2 : ℝ) ^ θ)
  refine ⟨mStar, hm2, ?_⟩
  intro m hm
  have hi : 1 ≤ m := (by norm_num : 1 ≤ 2).trans (hm2.trans hm)
  have he := Scales.epsilon_basic (m := m) hq hΛ
  have hE := Scales.epsilon_basic (m := m - 1) hq hΛ
  have hstep := Real.rpow_le_rpow he.1.le (Scales.epsilon_q_step hq hq₁ hΛ hi) hθ.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hE.1.le _),
    ← Real.rpow_mul hE.1.le] at hstep
  have hs : CI * ocEpsilon q Λ m ^ θ ≤
      (CI * (2 : ℝ) ^ θ) * ocEpsilon q Λ (m - 1) ^ (q * θ) := by
    exact (mul_le_mul_of_nonneg_left hstep hCI).trans_eq (mul_assoc _ _ _).symm
  have hβ : 7 * |A * (CI * ocEpsilon q Λ m ^ θ)| ≤
      (7 * A * CI * (2 : ℝ) ^ θ) * ocEpsilon q Λ (m - 1) ^ (q * θ) := by
    rw [abs_of_nonneg (mul_nonneg hA (mul_nonneg hCI (Real.rpow_nonneg he.1.le θ)))]
    calc
      7 * (A * (CI * ocEpsilon q Λ m ^ θ)) =
          (7 * A) * (CI * ocEpsilon q Λ m ^ θ) := by ring
      _ ≤ (7 * A) * ((CI * (2 : ℝ) ^ θ) *
          ocEpsilon q Λ (m - 1) ^ (q * θ)) :=
        mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num) hA)
      _ = _ := by ring
  have hbound := hsmall m hm
  exact ⟨hs.trans (hbound.1.trans (by norm_num)),
    hβ.trans (hbound.2.trans (by norm_num)), hβ⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Copy-rank mass inflation for forward-copy coefficients. If a coefficient vanishes on the window
unless the copy rank is the source rank plus one, the masses `M ^ rank` with
`M = (8C+1)^2` (`C` the total unweighted Schur entry) put every Schur weight at `1/(8C+1)`, so
every row and column sum is at most `C/(8C+1) ≤ 1/8`. No smallness of the coefficients is used.
The degenerate cases are included: zero coefficients give `C = 0`, `M = 1`; one copy rank (`H = 0`)
has no admissible forward pair; an empty index type has empty sums. -/

variable {κ : Type*} {h : κ → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- The unweighted Schur entry: `schurMatrix` without its mass factor. -/
def DescEntry (ν ρ : ℝ) (K : κ → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : κ) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))) (i i' : κ) : ℝ :=
  ∑ d : admissibleOrders K D i i',
    ((coefficientSeminorm ρ (K i) a b (A i i' d)).toReal / (ν * ρ ^ (d.1 - 2))) *
      (((K i + d.1 - 2).factorial : ℝ) / ((K i).factorial : ℝ))

/-- The copy-rank masses. -/
def DescMass (M : ℝ) (r : κ → ℕ) (i : κ) : ℝ := M ^ r i

variable {ν ρ : ℝ} {K : κ → ℕ} {D : ℕ} {a b : ℝ}
  {A : ∀ (i i' : κ) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h i))}

theorem schurMatrix_eq (π : κ → ℝ) (i i' : κ) :
    schurMatrix ν ρ π K D a b A i i' = Real.sqrt (π i' / π i) * DescEntry ν ρ K D a b A i i' :=
  rfl

theorem DescEntry_nonneg (hν : 0 < ν) (hρ : 0 < ρ) (i i' : κ) :
    0 ≤ DescEntry ν ρ K D a b A i i' := by
  unfold DescEntry
  refine Finset.sum_nonneg fun d _ => mul_nonneg ?_ ?_
  · exact div_nonneg ENNReal.toReal_nonneg (mul_pos hν (pow_pos hρ _)).le
  · positivity

/-- A coefficient vanishing on the window has zero unweighted Schur entry. -/
theorem DescEntry_eq_zero {i i' : κ}
    (hz : ∀ d, ∀ t ∈ Set.Icc a b, A i i' d t = 0) :
    DescEntry ν ρ K D a b A i i' = 0 := by
  unfold DescEntry
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [CycleJointProofs.coefficientSeminorm_window_congr ρ (K i) a b
      (fun (_ : ℝ) (_ : Vec 2) => 0) (A i i' d) (fun t ht => by rw [hz d t ht]; rfl),
    CycleComparison.Coarse.coefficientSeminorm_const_zero]
  simp

/-- On a forward pair the copy-rank mass factor is `1/(8C+1)`. -/
theorem desc_weight_eq {C : ℝ} (hC : 0 ≤ C) (r : κ → ℕ) {i i' : κ}
    (hr : r i = r i' + 1) :
    Real.sqrt (DescMass ((8 * C + 1) ^ 2) r i' / DescMass ((8 * C + 1) ^ 2) r i) =
      (8 * C + 1)⁻¹ := by
  have hpos : 0 < 8 * C + 1 := by linarith
  have hM : 0 < (8 * C + 1) ^ 2 := by positivity
  have hq : ((8 * C + 1) ^ 2) ^ r i' / ((8 * C + 1) ^ 2) ^ (r i' + 1) = ((8 * C + 1) ^ 2)⁻¹ := by
    rw [pow_succ ((8 * C + 1) ^ 2) (r i'), div_mul_eq_div_div,
      div_self (pow_ne_zero _ hM.ne'), one_div]
  unfold DescMass
  rw [hr, hq, Real.sqrt_inv, Real.sqrt_sq hpos.le]

theorem DescMass_pos {M : ℝ} (hM : 0 < M) (r : κ → ℕ) (i : κ) : 0 < DescMass M r i :=
  pow_pos hM _

variable [Fintype κ]

/-- Copy-rank mass inflation at any common bound `C` of the unweighted row and column sums. -/
theorem desc_schur_of_bound (r : κ → ℕ)
    (hfw : ∀ i i' d, r i ≠ r i' + 1 → ∀ t ∈ Set.Icc a b, A i i' d t = 0)
    {C : ℝ} (hC : 0 ≤ C) (hrow : ∀ i, ∑ i', DescEntry ν ρ K D a b A i i' ≤ C)
    (hcol : ∀ i', ∑ i, DescEntry ν ρ K D a b A i i' ≤ C) :
    SchurCondition (schurMatrix ν ρ (DescMass ((8 * C + 1) ^ 2) r) K D a b A) := by
  have hpos : 0 < 8 * C + 1 := by linarith
  have hb : ∀ i i', schurMatrix ν ρ (DescMass ((8 * C + 1) ^ 2) r) K D a b A i i' ≤
      (8 * C + 1)⁻¹ * DescEntry ν ρ K D a b A i i' := by
    intro i i'
    rw [schurMatrix_eq]
    by_cases hr : r i = r i' + 1
    · rw [desc_weight_eq hC r hr]
    · rw [DescEntry_eq_zero (fun d t ht => hfw i i' d hr t ht)]
      simp
  have hfin : (8 * C + 1)⁻¹ * C ≤ 1 / 8 := by
    rw [inv_mul_le_iff₀ hpos]
    linarith
  have hinv : 0 ≤ (8 * C + 1)⁻¹ := inv_nonneg.mpr hpos.le
  refine ⟨fun i => ?_, fun i' => ?_⟩
  · calc ∑ i', schurMatrix ν ρ (DescMass ((8 * C + 1) ^ 2) r) K D a b A i i'
        ≤ ∑ i', (8 * C + 1)⁻¹ * DescEntry ν ρ K D a b A i i' :=
          Finset.sum_le_sum fun i' _ => hb i i'
      _ = (8 * C + 1)⁻¹ * ∑ i', DescEntry ν ρ K D a b A i i' :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (8 * C + 1)⁻¹ * C := mul_le_mul_of_nonneg_left (hrow i) hinv
      _ ≤ 1 / 8 := hfin
  · calc ∑ i, schurMatrix ν ρ (DescMass ((8 * C + 1) ^ 2) r) K D a b A i i'
        ≤ ∑ i, (8 * C + 1)⁻¹ * DescEntry ν ρ K D a b A i i' :=
          Finset.sum_le_sum fun i _ => hb i i'
      _ = (8 * C + 1)⁻¹ * ∑ i, DescEntry ν ρ K D a b A i i' :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (8 * C + 1)⁻¹ * C := mul_le_mul_of_nonneg_left (hcol i') hinv
      _ ≤ 1 / 8 := hfin

/-- **Copy-rank mass inflation**: forward-copy coefficients satisfy the Schur condition for the
masses `((8C+1)^2) ^ rank`, `C` the total unweighted Schur entry. -/
theorem desc_schur (hν : 0 < ν) (hρ : 0 < ρ) (r : κ → ℕ)
    (hfw : ∀ i i' d, r i ≠ r i' + 1 → ∀ t ∈ Set.Icc a b, A i i' d t = 0) :
    SchurCondition (schurMatrix ν ρ
      (DescMass ((8 * ∑ i, ∑ i', DescEntry ν ρ K D a b A i i' + 1) ^ 2) r) K D a b A) := by
  have he : ∀ i i', 0 ≤ DescEntry ν ρ K D a b A i i' := DescEntry_nonneg hν hρ
  have hrow : ∀ i, ∑ i', DescEntry ν ρ K D a b A i i' ≤
      ∑ i, ∑ i', DescEntry ν ρ K D a b A i i' := fun i =>
    Finset.single_le_sum (f := fun i => ∑ i', DescEntry ν ρ K D a b A i i')
      (fun i _ => Finset.sum_nonneg fun i' _ => he i i') (Finset.mem_univ i)
  have hcol : ∀ i', ∑ i, DescEntry ν ρ K D a b A i i' ≤
      ∑ i, ∑ i', DescEntry ν ρ K D a b A i i' := fun i' =>
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun i' => DescEntry ν ρ K D a b A i i')
        (fun i' _ => he i i') (Finset.mem_univ i')
  exact desc_schur_of_bound r hfw
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => he i i') hrow hcol

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The finite plain source-insertion family. Each new copy is forced by the
preceding copy with the original unsmoothed coefficients, maps and histories.
Only its copy index changes; its pieces, contexts and partition do not.

The degenerate cases are included: H=0 retains one copy and has no edges; D=2 gives constant
slots. Empty and singleton families, zero data, identity geometry and edgeless
seeds use the same construction. This module constructs the exact family
and proves its geometry; it does not assert existence of its evolution. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- Original constituents between successive source-insertion copies. -/
def preparationNeutralChain (F : ChartedFamily ι h D P Ctx) (H : ℕ) :
    ChartedFamily (ι × Fin (H + 1)) (fun v => h v.1) D P Ctx where
  Γ v u := {γ : F.Γ v.1 u.1 // v.2.val = u.2.val + 1}
  fintypeΓ := fun v u => by
    classical
    letI := F.fintypeΓ v.1 u.1
    infer_instance
  identity v u γ := F.identity v.1 u.1 γ.val
  piece := F.piece
  flux p c v u γ := F.flux p c v.1 u.1 γ.val
  flux_periodic p c v u γ := F.flux_periodic p c v.1 u.1 γ.val
  flux_zero p c v u γ := F.flux_zero p c v.1 u.1 γ.val
  weight := F.weight
  weight_nonneg := F.weight_nonneg
  weight_zero := F.weight_zero
  locally_finite := F.locally_finite
  weight_sum := F.weight_sum

/-- Copies use a finite descending reserve; the last copy keeps Kbase. -/
def preparationNeutralSlots (H D Kbase : ℕ) (v : ι × Fin (H + 1)) : ℕ :=
  Kbase + (H - v.2.val) * (D - 2)

/-- Every edge increases the copy index, independently of the original graph. -/
theorem preparation_neutral_chain_depth (F : ChartedFamily ι h D P Ctx) (H : ℕ) :
    (preparationNeutralChain F H).HasDepthAtMost H := by
  intro p
  classical
  by_contra hfail
  have hs (k : Fin (H + 1)) : (p k.succ).2.val = (p k.castSucc).2.val + 1 := by
    by_contra hk
    apply hfail
    exact ⟨k, ⟨fun γ => hk γ.property⟩⟩
  have hindex : ∀ (n : ℕ) (hn : n < H + 2), n ≤ (p ⟨n, hn⟩).2.val := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hb := ih (by omega)
      have he := hs ⟨n, by omega⟩
      change (p ⟨n + 1, by omega⟩).2.val = (p ⟨n, by omega⟩).2.val + 1 at he
      omega
  have hb := hindex (H + 1) (by omega)
  have ht := (p ⟨H + 1, by omega⟩).2.isLt
  omega

/-- The reserve drop across one copy pays every original constituent order. -/
theorem preparation_neutral_chain_descending (F : ChartedFamily ι h D P Ctx)
    (H Kbase : ℕ) :
    (preparationNeutralChain F H).IsDescending (preparationNeutralSlots H D Kbase) := by
  intro v u γ
  have hv := v.2.isLt
  have hu := u.2.isLt
  have he := γ.property
  have horder := (F.identity v.1 u.1 γ.val).le_D
  have hD := (F.identity v.1 u.1 γ.val).two_le.trans horder
  have hsub : H - u.2.val = H - v.2.val + 1 := by omega
  change Kbase + (H - v.2.val) * (D - 2) + (F.identity v.1 u.1 γ.val).maxOrder ≤
    Kbase + (H - u.2.val) * (D - 2) + 2
  rw [hsub, Nat.add_mul, Nat.one_mul]
  omega

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The insertion depth and finite moment/copy reserve are selected before
seed constants and construction data. This module uses abstract real decay
exponents; the OC exponent is substituted only in the prefix join.
The degenerate cases are included: Dm=2 gives constant slots, depth zero is valid for the slot
bounds, Nout=Lpr=0 and empty and singleton components retain the same formulas. No data
norm or time interval is divided out. -/

/-- A finite insertion depth whose tail exponent strictly exceeds Q. -/
def preparationInsertionDepth (b Q : ℝ) : ℕ := Nat.ceil (Q / b) + 1

/-- The last copy retains both the output jets and the physical moment reserve. -/
def preparationPlainBaseOrder (Dm Nout Lpr : ℕ) : ℕ := max Nout (Dm - 2 + Lpr)

/-- One uniform buffer order contains every descending-copy slot. -/
def preparationBufferOrder (Dm Nout Lpr Hpr : ℕ) : ℕ :=
  preparationPlainBaseOrder Dm Nout Lpr + Hpr * (Dm - 2)

/-- The tail decay is chosen strictly before all seed constants and data. -/
theorem preparation_insertion_tail_order {b : ℝ} (hb : 0 < b) (Q : ℝ) :
    1 ≤ preparationInsertionDepth b Q ∧
      Q < b * ((preparationInsertionDepth b Q : ℝ) + 1) := by
  constructor
  · unfold preparationInsertionDepth
    omega
  · have hceil : Q / b ≤ (Nat.ceil (Q / b) : ℝ) := Nat.le_ceil _
    have hQ : Q ≤ b * (Nat.ceil (Q / b) : ℝ) :=
      (div_le_iff₀ hb).mp hceil |>.trans_eq (mul_comm _ _)
    have hgap : b * (Nat.ceil (Q / b) : ℝ) <
        b * ((Nat.ceil (Q / b) : ℝ) + 2) :=
      mul_lt_mul_of_pos_left (lt_add_of_pos_right _ (by norm_num)) hb
    refine hQ.trans_lt (hgap.trans_eq ?_)
    simp only [preparationInsertionDepth, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

/-- The exact descending slots lie below the common buffer order and above
both the model order and the true moment reserve of every physical source. -/
theorem preparation_descending_copy_orders {ι : Type*} (Dm Nout Lpr Hpr : ℕ)
    (v : ι × Fin (Hpr + 1)) :
    preparationNeutralSlots Hpr Dm (preparationPlainBaseOrder Dm Nout Lpr) v ≤
      preparationBufferOrder Dm Nout Lpr Hpr ∧
    Nout ≤ preparationNeutralSlots Hpr Dm (preparationPlainBaseOrder Dm Nout Lpr) v ∧
    Dm - 2 + Lpr ≤ preparationNeutralSlots Hpr Dm (preparationPlainBaseOrder Dm Nout Lpr) v := by
  unfold preparationNeutralSlots preparationBufferOrder preparationPlainBaseOrder
  refine ⟨Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _, ?_, ?_⟩
  · exact (le_max_left _ _).trans (Nat.le_add_right _ _)
  · exact (le_max_right _ _).trans (Nat.le_add_right _ _)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The finite neutral chain changes neither incidence sum of a nonnegative
majorant. A row has only its preceding copy and a column only its following
copy; the estimate has no factor for the number of copies or components.

The degenerate cases are included: H=0 gives zero incidences; empty families have vacuous sums.
Singletons, D=2, identity geometry, zero data and edgeless seeds use the same
matrix. Normalizing the majorant does not scale the physical coefficients;
its eventual absorption into envelope constants remains explicit. -/

/-- The original edge majorant appears between consecutive copies only. -/
def preparationNeutralMajorant {ι : Type*} (A : ι → ι → ℝ) (H : ℕ)
    (v u : ι × Fin (H + 1)) : ℝ :=
  if v.2.val = u.2.val + 1 then A v.1 u.1 else 0

private theorem preparation_neutral_slice_sum_le {κ : Type*} [Fintype κ]
    (f : κ → ℕ) (hf : Function.Injective f) (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (∑ k, if n = f k then a else 0) ≤ a := by
  classical
  by_cases hex : ∃ k, n = f k
  · obtain ⟨k, hk⟩ := hex
    rw [Finset.sum_eq_single k]
    · rw [ite_eq_left hk]
    · intro j _ hj
      have hne : n ≠ f j := by
        intro he
        exact hj (hf (he.symm.trans hk))
      exact ite_eq_right hne
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  · have hne : ∀ k, n ≠ f k := fun k hk => hex ⟨k, hk⟩
    simp only [ite_eq_right (hne _), Finset.sum_const_zero]
    exact ha

variable {ι : Type*} [Fintype ι]

/-- Only one incoming copy can contribute to a row. -/
theorem preparation_neutral_majorant_row_le (A : ι → ι → ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (H : ℕ) (v : ι × Fin (H + 1)) :
    (∑ u, preparationNeutralMajorant A H v u) ≤ ∑ u, A v.1 u := by
  classical
  simp only [Fintype.sum_prod_type, preparationNeutralMajorant]
  apply Finset.sum_le_sum
  intro u _
  exact preparation_neutral_slice_sum_le (fun k : Fin (H + 1) => k.val + 1)
    (fun i j hij => Fin.ext (by dsimp only at hij; omega)) v.2.val (A v.1 u) (hA v.1 u)

/-- Only one outgoing copy can contribute to a column. -/
theorem preparation_neutral_majorant_col_le (A : ι → ι → ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (H : ℕ) (u : ι × Fin (H + 1)) :
    (∑ v, preparationNeutralMajorant A H v u) ≤ ∑ v, A v u.1 := by
  classical
  simp only [Fintype.sum_prod_type, preparationNeutralMajorant]
  apply Finset.sum_le_sum
  intro v _
  have hs := preparation_neutral_slice_sum_le (fun k : Fin (H + 1) => k.val)
    Fin.val_injective (u.2.val + 1) (A v u.1) (hA v u.1)
  simpa only [eq_comm] using hs

/-- Both original incidence budgets survive copying without a copy-count loss. -/
theorem preparation_neutral_majorant_budgets (A : ι → ι → ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (S : ℝ)
    (hr : ∀ v, ∑ u, A v u ≤ S) (hc : ∀ u, ∑ v, A v u ≤ S) (H : ℕ) :
    (∀ v, ∑ u, preparationNeutralMajorant A H v u ≤ S) ∧
    (∀ u, ∑ v, preparationNeutralMajorant A H v u ≤ S) :=
  ⟨fun v => (preparation_neutral_majorant_row_le A hA H v).trans (hr v.1),
    fun u => (preparation_neutral_majorant_col_le A hA H u).trans (hc u.1)⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The joint preparation does not export positivity of C or CP. On
the actual nonnegative record matrix and scale, enlarging them to max(C,0)
and max(CP,0) keeps the SAME endpoint and blocks and supplies the sign of
the error scale required by CopyJoint.GateParams. This is scalar
monotonicity, not a new preparation, model, mass or time choice.
The degenerate cases are included: empty and singleton families, H=0, D=2, E=0, constants and
zero data, identity geometry and edgeless families, even if C or CP is negative. -/

/-- Nonnegative enlargement of the two constants preserves both actual
conclusions of the joint preparation without changing any witness or any datum. -/
def PreparationJointConstantsMonoStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D : ℕ} {Part : Type*} {Ctx : Part → Type*}
    (family : ChartedFamily ι h D Part Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (Mout H : ℕ) (A : Matrix ι ι ℝ),
    (∀ v u, 0 ≤ A v u) →
  ∀ (Θ E Pacc ρm C CP ν tS tp ρs ρold : ℝ), 0 ≤ Θ → 0 ≤ E →
  ∀ (b : ℝ → Vec 2 → Vec 2)
    (Ac : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)),
    IsJointModel π K Mout H family A Θ E Pacc ρm C CP Pd Pg →
    IsJointError π K Mout H D ν tS tp ρs ρold E Pacc CP b Ac Pd Pg →
      IsJointModel π K Mout H family A Θ E Pacc ρm (max C 0) (max CP 0) Pd Pg ∧
      IsJointError π K Mout H D ν tS tp ρs ρold E Pacc (max CP 0) b Ac Pd Pg

/-! Nonnegative enlargement of the supplied joint constants. All bounds
are monotone on the actual nonnegative record matrix and scales. The same
endpoint, blocks, family, masses and solution are retained throughout. -/

/-- Replacing both joint constants by their nonnegative maxima preserves
the exact model and error clauses, including for empty component families. -/
theorem preparation_joint_constants_mono : PreparationJointConstantsMonoStatement := by
  intro ι _ _ h _ _ _ _ _ _ D Part Ctx family π K Mout H A hA
    Θ E Pacc ρm C CP ν tS tp ρs ρold hΘ hE b Ac Pd Pg hmodel herror
  have hC : C ≤ max C 0 := le_max_left _ _
  have hCP : CP * E ^ Pacc ≤ max CP 0 * E ^ Pacc :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hE _)
  obtain ⟨hsupport, hdiag, hdiagJet, hsource, hmass, hconst⟩ := hmodel
  refine ⟨⟨hsupport, ?_, ?_, ?_, ?_, hconst⟩, ?_⟩
  · intro v f
    exact (hdiag v f).trans (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl hCP) (Real.sqrt_nonneg _))
  · intro v f
    exact (hdiagJet v f).trans
      (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))
  · intro n hn hnH v u f
    exact (hsource n hn hnH v u f).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC
        (CycleJointProofs.positiveMatrix_pow_nonneg A hA n v u))
      (Real.sqrt_nonneg _))
  · intro f
    exact (hmass f).trans (mul_le_mul_of_nonneg_right
      (add_le_add (add_le_add le_rfl hCP) (mul_le_mul_of_nonneg_right hC hΘ))
      (Real.sqrt_nonneg _))
  · intro f Fv hFv u w hsol
    exact (herror f Fv hFv u w hsol).trans
      (mul_le_mul_of_nonneg_right hCP (Real.sqrt_nonneg _))

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The scalar constants of the single copied-model readout, uniformly in
the level and band chain. Its molecular model radius is c times the parent's
lift length; the enhanced output radius is the actual cr-scaled power.
This is the bounded numeric leaf of the same-model join, not an assumption
of the common-preparation construction.

The degenerate cases are included: empty and singleton families, H=Nout=0, Cbuf=0, S=0 (including
0^0=1), identity geometry and an edgeless seed use the same scalar bounds. Interior levels
exclude the terminal diffusivity scale. Constants precede all band chains,
start times, data and masses. -/

/-- The finite copied-readout constants are uniformly bounded at the actual
output and model radii, with the same buffer cost for both weights. -/
def PreparationCopiedModelBudgetStatement (α q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
  ∀ (c cr C CP Cbuf : ℝ) (H Nout : ℕ), 0 < c → 0 < cr → 0 ≤ Cbuf →
  ∃ (Cjoint Cjet : ℝ) (mStar : ℕ), 0 ≤ Cjet ∧ 2 ≤ mStar ∧
  ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
  ∀ m : ℕ, mStar ≤ m → m < M → ∀ S : ℝ, 0 ≤ S → S ≤ 1 →
    ((H : ℝ) + 1) * (CP * Cbuf) ≤ Cjoint ∧
    ((H : ℝ) + 1) * (CycleComparison.Reconstruction.jointModelConst C S H Nout
      ((cr * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q)) /
        (c * Real.sqrt (κ (m - 1) * ocTauPP α q Λ m))) * Cbuf) ≤ Cjet

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The neutral copies retain the original analytic and molecular envelopes.
Each output copy uses its own descending slot. Reindexing keeps each original
constituent once; the existing positive mass-cancellation lemma permits a
new mass on the copied family, including the marked mass.

For H=0 there are no source identities, so all edge bounds are vacuous; empty or singleton
families, zero data and edgeless seeds use the same fields and domains. Original contexts and chart histories are retained.
No new coefficient estimate or bound on marker size is introduced. -/

open CycleJointProofs.PathReduction
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- Original identities appear once on each consecutive-copy edge. -/
def preparationNeutralIdentityEquiv (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (v u : ι × Fin (H + 1)) (hs : v.2.val = u.2.val + 1) :
    (preparationNeutralChain F H).Γ v u ≃ F.Γ v.1 u.1 where
  toFun := Subtype.val
  invFun γ := ⟨γ, hs⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Smoothness is inherited separately at every output-copy slot. -/
theorem preparation_neutral_smooth (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (W : Set ℝ) (E : ℝ) (n : ι × Fin (H + 1) → ℕ)
    (hn : ∀ l, F.IsSmoothOn (ChartedFamily.Domain.onWindow F W) E (fun v => n (v, l))) :
    (preparationNeutralChain F H).IsSmoothOn
      (ChartedFamily.Domain.onWindow (preparationNeutralChain F H) W) E n := by
  intro p c v u γ d I tY htY z
  exact hn v.2 p c v.1 u.1 γ.val d I tY htY z

/-- The analytic envelope permits arbitrary positive copied masses. -/
theorem preparation_neutral_analytic (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (W : Set ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (πc : ι × Fin (H + 1) → ℝ) (hπc : ∀ v, 0 < πc v)
    (E C : ℝ) (Ks Ls : ℕ) (A : ι → ι → ℝ)
    (hF : IsAnalyticEnvelope F π (ChartedFamily.Domain.onWindow F W) E C Ks Ls
      (fun v u => Real.sqrt (π u / π v) * A v u)) :
    IsAnalyticEnvelope (preparationNeutralChain F H) πc
      (ChartedFamily.Domain.onWindow (preparationNeutralChain F H) W) E C Ks Ls
      (fun v u => Real.sqrt (πc u / πc v) * preparationNeutralMajorant A H v u) := by
  classical
  refine ⟨preparation_neutral_smooth F H W E (fun _ => Ks + Ls) (fun _ => hF.1), ?_⟩
  intro v u
  by_cases hs : v.2.val = u.2.val + 1
  · simp only [preparationNeutralMajorant, ite_eq_left hs]
    apply le_trans ?_ (replace_envelope_mass _ _ _ _
      (Real.sqrt_pos.mpr (div_pos (hπ u.1) (hπ v.1)))
      (Real.sqrt_pos.mpr (div_pos (hπc u) (hπc v))) _ (hF.2 v.1 u.1))
    apply le_of_eq
    congr 1
    exact Fintype.sum_equiv (preparationNeutralIdentityEquiv F H v u hs) _ _ (fun _ => rfl)
  · let : IsEmpty ((preparationNeutralChain F H).Γ v u) := ⟨fun γ => hs γ.property⟩
    simp only [Fintype.sum_empty, mul_zero, preparationNeutralMajorant, ite_eq_right hs,
      ENNReal.ofReal_zero, le_refl]

/-- Every copy uses the original molecular envelope at that copy's own slot. -/
theorem preparation_neutral_molecular (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (W : Set ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (πc : ι × Fin (H + 1) → ℝ) (hπc : ∀ v, 0 < πc v)
    (K : ι × Fin (H + 1) → ℕ) (ν e E ρ : ℝ) (C : ℕ → ℝ) (J : ℕ) (A : ι → ι → ℝ)
    (hF : ∀ l, IsMolecularEnvelope F π (fun v => K (v, l))
      (ChartedFamily.Domain.onWindow F W) ν e E ρ C J
      (fun v u => Real.sqrt (π u / π v) * A v u)) :
    IsMolecularEnvelope (preparationNeutralChain F H) πc K
      (ChartedFamily.Domain.onWindow (preparationNeutralChain F H) W) ν e E ρ C J
      (fun v u => Real.sqrt (πc u / πc v) * preparationNeutralMajorant A H v u) := by
  classical
  refine ⟨preparation_neutral_smooth F H W E (fun v => K v + J)
    (fun l => (hF l).1), ?_⟩
  intro v u j hj
  by_cases hs : v.2.val = u.2.val + 1
  · simp only [preparationNeutralMajorant, ite_eq_left hs]
    apply le_trans ?_ (replace_envelope_mass _ _ _ _
      (Real.sqrt_pos.mpr (div_pos (hπ u.1) (hπ v.1)))
      (Real.sqrt_pos.mpr (div_pos (hπc u) (hπc v))) _ ((hF v.2).2 v.1 u.1 j hj))
    apply le_of_eq
    congr 1
    exact Fintype.sum_equiv (preparationNeutralIdentityEquiv F H v u hs) _ _ (fun _ => rfl)
  · let : IsEmpty ((preparationNeutralChain F H).Γ v u) := ⟨fun γ => hs γ.property⟩
    simp only [Fintype.sum_empty, mul_zero, preparationNeutralMajorant, ite_eq_right hs,
      ENNReal.ofReal_zero, le_refl]

/-- Pointwise molecular envelopes retain their EVERY-time quantifier on all copies. -/
theorem preparation_neutral_pointwise (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (W : Set ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (πc : ι × Fin (H + 1) → ℝ) (hπc : ∀ v, 0 < πc v)
    (K : ι × Fin (H + 1) → ℕ) (ν e E ρ : ℝ) (C : ℕ → ℝ) (J : ℕ) (A : ι → ι → ℝ)
    (hF : ∀ l, IsPointwiseMolecularEnvelope F π (fun v => K (v, l))
      (ChartedFamily.Domain.onWindow F W) ν e E ρ C J
      (fun v u => Real.sqrt (π u / π v) * A v u)) :
    IsPointwiseMolecularEnvelope (preparationNeutralChain F H) πc K
      (ChartedFamily.Domain.onWindow (preparationNeutralChain F H) W) ν e E ρ C J
      (fun v u => Real.sqrt (πc u / πc v) * preparationNeutralMajorant A H v u) := by
  classical
  refine ⟨preparation_neutral_smooth F H W E (fun v => K v + J)
    (fun l => (hF l).1), ?_⟩
  intro v u j hj
  by_cases hs : v.2.val = u.2.val + 1
  · simp only [preparationNeutralMajorant, ite_eq_left hs]
    apply le_trans ?_ (replace_envelope_mass _ _ _ _
      (Real.sqrt_pos.mpr (div_pos (hπ u.1) (hπ v.1)))
      (Real.sqrt_pos.mpr (div_pos (hπc u) (hπc v))) _ ((hF v.2).2 v.1 u.1 j hj))
    apply le_of_eq
    congr 1
    exact Fintype.sum_equiv (preparationNeutralIdentityEquiv F H v u hs) _ _ (fun _ => rfl)
  · let : IsEmpty ((preparationNeutralChain F H).Γ v u) := ⟨fun γ => hs γ.property⟩
    simp only [Fintype.sum_empty, mul_zero, preparationNeutralMajorant, ite_eq_right hs,
      ENNReal.ofReal_zero, le_refl]

/-- Measurability, periodicity, pulse transversality and trimmed quiet independence
are all inherited on the same original contexts. -/
theorem preparation_neutral_structural (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (actual : ∀ p, Ctx p) (E : ℝ) {κ : Type*}
    (pulse : κ → Set ℝ) (orient : κ → Fin 2) (S : Set ℝ)
    (hm : F.IsTimeMeasurable) (ht : IsTorusCompatible F actual E)
    (hp : F.IsTransverseOnPulses pulse orient) (hq : F.IsFastIndependentOn S) :
    (preparationNeutralChain F H).IsTimeMeasurable ∧
    IsTorusCompatible (preparationNeutralChain F H) actual E ∧
    (preparationNeutralChain F H).IsTransverseOnPulses pulse orient ∧
    (preparationNeutralChain F H).IsFastIndependentOn S := by
  refine ⟨?_, ⟨ht.1, ?_⟩, ?_, ?_⟩
  · exact fun p c v u γ => hm p c v.1 u.1 γ.val
  · exact fun p t v u γ => ht.2 p t v.1 u.1 γ.val
  · exact fun k p c v u γ => hp k p c v.1 u.1 γ.val
  · exact fun p c v u γ => hq p c v.1 u.1 γ.val

/-- The neutral family uses the original atlas, including context identifications. -/
def preparationNeutralAtlas (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (T : F.Atlas) : (preparationNeutralChain F H).Atlas where
  adjacent := T.adjacent
  tr := T.tr
  sameCtx := T.sameCtx

/-- The inherited atlas keeps quiet coverage and the summed transition. -/
theorem preparation_neutral_atlas (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (T : F.Atlas) (quiet W : Set ℝ) (ν e E : ℝ)
    (hc : T.IsConsecutiveClosed W) (hv : T.CoversQuiet quiet W) (hq : T.IsQuiet ν e E) :
    (preparationNeutralAtlas F H T).IsConsecutiveClosed W ∧
    (preparationNeutralAtlas F H T).CoversQuiet quiet W ∧
    (preparationNeutralAtlas F H T).IsQuiet ν e E := by
  refine ⟨hc, hv, ?_⟩
  intro p q hpq c c' hcc
  have hh := hq p q hpq c c' hcc
  apply ChartedFamily.isQuietTransition_of_summed
  · exact fun tY hY v u γ => hh.fastIndependent tY hY v.1 u.1 γ.val
  · exact fun tY hY z v u γ => hh.summed tY hY z v.1 u.1 γ.val

/-- Preparation charts retain their original schedule and flow certificate. -/
theorem preparation_neutral_preparation (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (tS tZ Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P₀ : ℕ)
    (hF : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart
      Cchart l₀ P₀ F) :
    IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart
      Cchart l₀ P₀ (preparationNeutralChain F H) := by
  refine ⟨?_, hF.flow⟩
  exact ⟨hF.schedule.pad_nonneg, hF.schedule.age_pos, hF.schedule.finite_pieces,
    hF.schedule.reference_mem, hF.schedule.availability_interval, hF.schedule.anchor_label,
    hF.schedule.natural, hF.schedule.geometry_padded, hF.schedule.anchor_age,
    hF.schedule.reference_age, hF.schedule.anchor_segments, hF.schedule.reference_segments,
    hF.schedule.cover_labels, hF.schedule.core_label⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
