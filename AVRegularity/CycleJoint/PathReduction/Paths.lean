-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PeriodicMultiplicationJetEnergy
import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout
public import AVRegularity.Definitions.CycleJoint.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.CycleJoint.HasEdgePath
public import AVRegularity.Statements.Intermediate.Families.AtlasCoversQuiet
public import AVRegularity.Statements.Intermediate.Families.AtlasIsConsecutiveClosed
public import AVRegularity.Statements.Intermediate.Families.AtlasIsQuiet
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTransverseOnPulses
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
public import AVRegularity.Statements.Intermediate.Families.IsMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseMolecularEnvelope
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.ChartedFamily

/-! Restrict a charted family to consecutive vertices of a source path.
Pieces and complete contexts are retained verbatim. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The chain family along a vertex path; an edge retains all its original identities. -/
def pathFamily (F : ChartedFamily ι h D P Ctx) {n : ℕ} (p : Fin (n + 1) → ι) :
    ChartedFamily (Fin (n + 1)) (fun k => h (p k)) D P Ctx where
  Γ v u := {_γ : F.Γ (p v) (p u) // v.val = u.val + 1}
  identity v u γ := F.identity (p v) (p u) γ.val
  piece := F.piece
  flux a c v u γ := F.flux a c (p v) (p u) γ.val
  flux_periodic a c v u γ := F.flux_periodic a c (p v) (p u) γ.val
  flux_zero a c v u γ := F.flux_zero a c (p v) (p u) γ.val
  weight := F.weight
  weight_nonneg := F.weight_nonneg
  weight_zero := F.weight_zero
  locally_finite := F.locally_finite
  weight_sum := F.weight_sum

variable (F : ChartedFamily ι h D P Ctx) {n : ℕ} (p : Fin (n + 1) → ι)

/-- Restricted paths inherit the depth bound of the original graph. -/
theorem pathFamily_depth {H : ℕ} (hF : F.HasDepthAtMost H) :
    (F.pathFamily p).HasDepthAtMost H := by
  intro q
  obtain ⟨k, hk⟩ := hF (p ∘ q)
  exact ⟨k, ⟨fun γ => hk.false γ.val⟩⟩

/-- A trivial path has no edges. -/
theorem pathFamily_zero_edges (p : Fin 1 → ι) (v u : Fin 1) :
    IsEmpty ((F.pathFamily p).Γ v u) := by
  refine ⟨fun γ => ?_⟩
  have hv := v.isLt
  have hu := u.isLt
  have hh := γ.property
  omega

/-- The slots remain descending on every retained identity. -/
theorem pathFamily_descending (K : ι → ℕ) (hF : F.IsDescending K) :
    (F.pathFamily p).IsDescending (K ∘ p) :=
  fun v u γ => hF (p v) (p u) γ.val

/-- Time measurability is constituentwise. -/
theorem pathFamily_measurable (hF : F.IsTimeMeasurable) :
    (F.pathFamily p).IsTimeMeasurable :=
  fun a c v u γ => hF a c (p v) (p u) γ.val

/-- Torus compatibility retains both the material charts and the selected contexts. -/
theorem pathFamily_torus (actual : ∀ a, Ctx a) (E : ℝ)
    (hF : IsTorusCompatible F actual E) : IsTorusCompatible (F.pathFamily p) actual E :=
  ⟨hF.1, fun a t v u γ => hF.2 a t (p v) (p u) γ.val⟩

/-- Transversality is unchanged for each constituent. -/
theorem pathFamily_transverse {κ : Type*} (pulse : κ → Set ℝ) (orient : κ → Fin 2)
    (hF : F.IsTransverseOnPulses pulse orient) :
    (F.pathFamily p).IsTransverseOnPulses pulse orient :=
  fun k a c v u γ => hF k a c (p v) (p u) γ.val

/-- Fast independence is unchanged for each constituent. -/
theorem pathFamily_fastIndependent (S : Set ℝ) (hF : F.IsFastIndependentOn S) :
    (F.pathFamily p).IsFastIndependentOn S :=
  fun a c v u γ => hF a c (p v) (p u) γ.val

/-- Pull back the atlas without changing charts, overlaps or context identifications. -/
def pathAtlas (T : F.Atlas) : (F.pathFamily p).Atlas where
  adjacent := T.adjacent
  tr := T.tr
  sameCtx := T.sameCtx

/-- Closure of the same atlas is a property of its pieces. -/
theorem Atlas.pathFamily_consecutive (T : F.Atlas) (W : Set ℝ)
    (hT : T.IsConsecutiveClosed W) : (pathAtlas F p T).IsConsecutiveClosed W := hT

/-- Quiet-time coverage is a property of the unchanged overlaps. -/
theorem Atlas.pathFamily_coversQuiet (T : F.Atlas) (quiet W : Set ℝ)
    (hT : T.CoversQuiet quiet W) : (pathAtlas F p T).CoversQuiet quiet W := hT

/-- Quiet transitions are restricted to the retained identities. -/
theorem Atlas.pathFamily_quiet (T : F.Atlas) (ν e E : ℝ) (hT : T.IsQuiet ν e E) :
    (pathAtlas F p T).IsQuiet ν e E := by
  intro a b hab c c' hcc
  obtain ⟨hi, ht⟩ := hT a b hab c c' hcc
  exact ⟨fun tY hY v u γ => hi tY hY (p v) (p u) γ.val,
    fun tY hY z v u γ => ht tY hY z (p v) (p u) γ.val⟩

/-- Preparation charts depend on the pieces and not on the restricted graph. -/
theorem pathFamily_preparation (α q : ℝ) (Λ m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (tS tZ Cpad Cage : ℝ) (Npad Jchart : ℕ) (Cchart : ℕ → ℝ) (l₀ : ℤ) (P₀ : ℕ)
    (hF : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart
      Cchart l₀ P₀ F) :
    IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart
      Cchart l₀ P₀ (F.pathFamily p) := by
  refine ⟨?_, hF.flow⟩
  exact ⟨hF.schedule.pad_nonneg, hF.schedule.age_pos, hF.schedule.finite_pieces,
    hF.schedule.reference_mem, hF.schedule.availability_interval, hF.schedule.anchor_label,
    hF.schedule.natural, hF.schedule.geometry_padded, hF.schedule.anchor_age,
    hF.schedule.reference_age, hF.schedule.anchor_segments, hF.schedule.reference_segments,
    hF.schedule.cover_labels, hF.schedule.core_label⟩

/-- Spatial smoothness is restricted with the terminal slot. -/
theorem pathFamily_smooth (W : Set ℝ) (E : ℝ) (r : ι → ℕ)
    (hF : F.IsSmoothOn (Domain.onWindow F W) E r) :
    (F.pathFamily p).IsSmoothOn (Domain.onWindow (F.pathFamily p) W) E (r ∘ p) :=
  fun a c v u γ => hF a c (p v) (p u) γ.val

end AVRegularity.ChartedFamily
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.PathReduction

/-! Entrywise envelopes restrict to paths with any positive path masses.
The original and path mass factors cancel before the comparison. -/

/-- A finite positive real mass factor can be replaced on both sides of an envelope. -/
theorem replace_envelope_mass (a b C A : ℝ) (ha : 0 < a) (hb : 0 < b)
    (S : ℝ≥0∞) (hS : ENNReal.ofReal a * S ≤ ENNReal.ofReal (C * (a * A))) :
    ENNReal.ofReal b * S ≤ ENNReal.ofReal (C * (b * A)) := by
  have hca : C * (a * A) = a * (C * A) := by ring
  have hcb : C * (b * A) = b * (C * A) := by ring
  rw [hca, ENNReal.ofReal_mul ha.le] at hS
  rw [hcb, ENNReal.ofReal_mul hb.le]
  exact mul_le_mul_of_nonneg_left ((ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top).mp hS) zero_le

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  (F : ChartedFamily ι h D P Ctx) {n : ℕ} (p : Fin (n + 1) → ι)

/-- The nonempty consecutive-edge subtype is equivalent to the original identity type. -/
def pathIdentityEquiv (v u : Fin (n + 1)) (hstep : v.val = u.val + 1) :
    (F.pathFamily p).Γ v u ≃ F.Γ (p v) (p u) where
  toFun := Subtype.val
  invFun γ := ⟨γ, hstep⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Nonconsecutive slots carry no identities. -/
theorem pathIdentity_empty (v u : Fin (n + 1)) (hstep : v.val ≠ u.val + 1) :
    IsEmpty ((F.pathFamily p).Γ v u) := ⟨fun γ => hstep γ.property⟩

/-- The matrix of the restricted path retains only consecutive entries. -/
def pathMatrix (A : ι → ι → ℝ) (v u : Fin (n + 1)) : ℝ :=
  if v.val = u.val + 1 then A (p v) (p u) else 0

/-- Analytic envelopes restrict to the path, with arbitrary positive masses. -/
theorem pathFamily_analytic (W : Set ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (πp : Fin (n + 1) → ℝ) (hπp : ∀ k, 0 < πp k)
    (E C : ℝ) (Ks Ls : ℕ) (A : ι → ι → ℝ)
    (hF : IsAnalyticEnvelope F π (ChartedFamily.Domain.onWindow F W) E C Ks Ls
      (fun v u => Real.sqrt (π u / π v) * A v u)) :
    IsAnalyticEnvelope (F.pathFamily p) πp
      (ChartedFamily.Domain.onWindow (F.pathFamily p) W) E C Ks Ls
      (fun v u => Real.sqrt (πp u / πp v) * pathMatrix p A v u) := by
  classical
  refine ⟨F.pathFamily_smooth p W E (fun _ => Ks + Ls) hF.1, ?_⟩
  intro v u
  by_cases hs : v.val = u.val + 1
  · simp only [pathMatrix, ite_eq_left hs]
    rw [show (∑ γ : (F.pathFamily p).Γ v u, ENNReal.ofReal ‖((F.pathFamily p).identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 ((F.pathFamily p).identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1), ∑ r ∈ Finset.range (Ks + 1),
            ∑ q ∈ Finset.range (Ls + 1), ENNReal.ofReal (E ^ r) *
              jetSupFam (fun x : (F.pathFamily p).Index =>
                ChartedFamily.Domain.onWindow (F.pathFamily p) W x.1 x.2) r q
                (fun x => (F.pathFamily p).slowFlux E x.1 x.2 v u γ d I)) =
        (∑ γ : F.Γ (p v) (p u), ENNReal.ofReal ‖(F.identity (p v) (p u) γ).map‖ *
        ∑ d ∈ Finset.Icc 2 (F.identity (p v) (p u) γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1), ∑ r ∈ Finset.range (Ks + 1),
            ∑ q ∈ Finset.range (Ls + 1), ENNReal.ofReal (E ^ r) *
              jetSupFam (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2) r q
                (fun x => F.slowFlux E x.1 x.2 (p v) (p u) γ d I)) from
        by
          exact Fintype.sum_equiv (pathIdentityEquiv F p v u hs) _ _ (fun _ => rfl)]
    exact replace_envelope_mass _ _ _ _
      (Real.sqrt_pos.mpr (div_pos (hπ (p u)) (hπ (p v))))
      (Real.sqrt_pos.mpr (div_pos (hπp u) (hπp v))) _ (hF.2 (p v) (p u))
  · let := pathIdentity_empty F p v u hs
    simp only [Fintype.sum_empty, mul_zero, pathMatrix, ite_eq_right hs, ENNReal.ofReal_zero,
      le_refl]

/-- Forward molecular envelopes restrict to the path, with arbitrary positive masses. -/
theorem pathFamily_molecular (W : Set ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (πp : Fin (n + 1) → ℝ) (hπp : ∀ k, 0 < πp k)
    (K : ι → ℕ) (ν e E ρ : ℝ) (C : ℕ → ℝ) (J : ℕ) (A : ι → ι → ℝ)
    (hF : IsMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J
      (fun v u => Real.sqrt (π u / π v) * A v u)) :
    IsMolecularEnvelope (F.pathFamily p) πp (K ∘ p)
      (ChartedFamily.Domain.onWindow (F.pathFamily p) W) ν e E ρ C J
      (fun v u => Real.sqrt (πp u / πp v) * pathMatrix p A v u) := by
  classical
  refine ⟨F.pathFamily_smooth p W E (fun v => K v + J) hF.1, ?_⟩
  intro v u j hj
  by_cases hs : v.val = u.val + 1
  · simp only [pathMatrix, ite_eq_left hs]
    apply le_trans ?_ (replace_envelope_mass _ _ _ _
      (Real.sqrt_pos.mpr (div_pos (hπ (p u)) (hπ (p v))))
      (Real.sqrt_pos.mpr (div_pos (hπp u) (hπp v))) _ (hF.2 (p v) (p u) j hj))
    apply le_of_eq
    congr 1
    exact Fintype.sum_equiv (pathIdentityEquiv F p v u hs) _ _ (fun _ => rfl)
  · let := pathIdentity_empty F p v u hs
    simp only [Fintype.sum_empty, mul_zero, pathMatrix, ite_eq_right hs, ENNReal.ofReal_zero,
      le_refl]

/-- Pointwise forward envelopes restrict to the path, with arbitrary positive masses. -/
theorem pathFamily_pointwise (W : Set ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (πp : Fin (n + 1) → ℝ) (hπp : ∀ k, 0 < πp k)
    (K : ι → ℕ) (ν e E ρ : ℝ) (C : ℕ → ℝ) (J : ℕ) (A : ι → ι → ℝ)
    (hF : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J
      (fun v u => Real.sqrt (π u / π v) * A v u)) :
    IsPointwiseMolecularEnvelope (F.pathFamily p) πp (K ∘ p)
      (ChartedFamily.Domain.onWindow (F.pathFamily p) W) ν e E ρ C J
      (fun v u => Real.sqrt (πp u / πp v) * pathMatrix p A v u) := by
  classical
  refine ⟨F.pathFamily_smooth p W E (fun v => K v + J) hF.1, ?_⟩
  intro v u j hj
  by_cases hs : v.val = u.val + 1
  · simp only [pathMatrix, ite_eq_left hs]
    apply le_trans ?_ (replace_envelope_mass _ _ _ _
      (Real.sqrt_pos.mpr (div_pos (hπ (p u)) (hπ (p v))))
      (Real.sqrt_pos.mpr (div_pos (hπp u) (hπp v))) _ (hF.2 (p v) (p u) j hj))
    apply le_of_eq
    congr 1
    exact Fintype.sum_equiv (pathIdentityEquiv F p v u hs) _ _ (fun _ => rfl)
  · let := pathIdentity_empty F p v u hs
    simp only [Fintype.sum_empty, mul_zero, pathMatrix, ite_eq_right hs, ENNReal.ofReal_zero,
      le_refl]

end AVRegularity.CycleJointProofs.PathReduction
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.PathReduction

/-! Exact coefficient transfer to the chain family. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  (F : ChartedFamily ι h D P Ctx) {n : ℕ} (p : Fin (n + 1) → ι)

/-- Consecutive path slots retain the full original physical edge coefficient. -/
theorem path_physicalCoefficient (ν e E : ℝ) (actual : ∀ a, Ctx a)
    (v u : Fin (n + 1)) (hs : v.val = u.val + 1) (d : ℕ) (t : ℝ) (x : Vec 2) :
    physicalCoefficient (F.pathFamily p) ν e E actual v u d t x =
      physicalCoefficient F ν e E actual (p v) (p u) d t x := by
  classical
  unfold physicalCoefficient
  exact Fintype.sum_equiv (pathIdentityEquiv F p v u hs) _ _ (fun _ => rfl)

/-- Nonconsecutive slots have zero physical coefficient. -/
theorem path_physicalCoefficient_zero (ν e E : ℝ) (actual : ∀ a, Ctx a)
    (v u : Fin (n + 1)) (hs : v.val ≠ u.val + 1) (d : ℕ) :
    physicalCoefficient (F.pathFamily p) ν e E actual v u d = 0 := by
  let := pathIdentity_empty F p v u hs
  funext t x
  simp only [physicalCoefficient, Fintype.sum_empty, Pi.zero_apply]

/-- The edge coefficients agree at each admissible order on consecutive slots. -/
theorem path_edgeCoefficient [Fintype ι] (ν e E : ℝ) (actual : ∀ a, Ctx a)
    (K : ι → ℕ) (v u : Fin (n + 1)) (hs : v.val = u.val + 1)
    (d : admissibleOrders (K ∘ p) D v u) (t : ℝ) (x : Vec 2) :
    edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p) v u d t x =
      edgeCoefficient F ν e E actual K (p v) (p u) d t x :=
  path_physicalCoefficient F p ν e E actual v u hs d.val t x

/-- The edge coefficients vanish between nonconsecutive slots. -/
theorem path_edgeCoefficient_zero (ν e E : ℝ) (actual : ∀ a, Ctx a)
    (K : ι → ℕ) (v u : Fin (n + 1)) (hs : v.val ≠ u.val + 1)
    (d : admissibleOrders (K ∘ p) D v u) :
    edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p) v u d = 0 :=
  path_physicalCoefficient_zero F p ν e E actual v u hs d.val
end

/-! Product masses of a chain, including positive regularizations of zero edges. -/

section
/-- The mass at vertex `k` is the square of the preceding edge product. -/
def chainMass (a : ℕ → ℝ) (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, a j ^ 2

theorem chainMass_succ (a : ℕ → ℝ) (k : ℕ) :
    chainMass a (k + 1) = chainMass a k * a k ^ 2 := Finset.prod_range_succ _ _

theorem chainMass_pos (a : ℕ → ℝ) {k : ℕ} (ha : ∀ j < k, 0 < a j) :
    0 < chainMass a k :=
  Finset.prod_pos fun j hj => sq_pos_of_pos (ha j (Finset.mem_range.mp hj))

/-- The square root of the adjacent mass ratio cancels its positive edge weight. -/
theorem chainMass_ratio (a : ℕ → ℝ) {k : ℕ} (ha : ∀ j ≤ k, 0 < a j) :
    Real.sqrt (chainMass a k / chainMass a (k + 1)) = (a k)⁻¹ := by
  have hk := ha k le_rfl
  have hm := chainMass_pos a (fun j hj => ha j hj.le)
  have he : chainMass a k / chainMass a (k + 1) = ((a k)⁻¹) ^ 2 := by
    rw [chainMass_succ]
    field_simp
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hk)]

/-- At a vertex the square-root mass is exactly the preceding positive product. -/
theorem chainMass_sqrt (a : ℕ → ℝ) {k : ℕ} (ha : ∀ j < k, 0 < a j) :
    Real.sqrt (chainMass a k) = ∏ j ∈ Finset.range k, a j := by
  rw [chainMass, Finset.prod_pow, Real.sqrt_sq_eq_abs]
  exact abs_of_pos (Finset.prod_pos fun j hj => ha j (Finset.mem_range.mp hj))

variable {ι : Type*} {n : ℕ} (p : Fin (n + 1) → ι) (A : ι → ι → ℝ)
  (a : ℕ → ℝ) (ha : ∀ j < n, 0 < a j)
  (hdom : ∀ v u : Fin (n + 1), v.val = u.val + 1 → A (p v) (p u) ≤ a u.val)

include ha hdom

/-- Each conjugated chain entry is at most one, even for regularized masses. -/
theorem pathMatrix_entry_le_one (v u : Fin (n + 1)) :
    Real.sqrt (chainMass a u.val / chainMass a v.val) * pathMatrix p A v u ≤ 1 := by
  classical
  by_cases hs : v.val = u.val + 1
  · rw [pathMatrix, ite_eq_left hs, hs, chainMass_ratio a
      (fun j hj => ha j (by have hv := v.isLt; omega))]
    have hau := ha u.val (by have hv := v.isLt; omega)
    calc
      (a u.val)⁻¹ * A (p v) (p u) ≤ (a u.val)⁻¹ * a u.val :=
        mul_le_mul_of_nonneg_left (hdom v u hs) (inv_pos.mpr hau).le
      _ = 1 := inv_mul_cancel₀ hau.ne'
  · simp only [pathMatrix, ite_eq_right hs, mul_zero, zero_le_one]

/-- Each conjugated row has at most one nonzero entry. -/
theorem pathMatrix_row_le_one (v : Fin (n + 1)) :
    ∑ u, Real.sqrt (chainMass a u.val / chainMass a v.val) * pathMatrix p A v u ≤ 1 := by
  classical
  by_cases hex : ∃ u : Fin (n + 1), v.val = u.val + 1
  · obtain ⟨u, hu⟩ := hex
    rw [Finset.sum_eq_single u]
    · exact pathMatrix_entry_le_one p A a ha hdom v u
    · intro w _ hwu
      have hs : v.val ≠ w.val + 1 := by
        intro hw
        apply hwu
        apply Fin.ext
        omega
      simp only [pathMatrix, ite_eq_right hs, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · have hs : ∀ u : Fin (n + 1), v.val ≠ u.val + 1 := by simpa only [not_exists] using hex
    simp only [pathMatrix, ite_eq_right (hs _), mul_zero, Finset.sum_const_zero, zero_le_one]

/-- Each conjugated column has at most one nonzero entry. -/
theorem pathMatrix_col_le_one (u : Fin (n + 1)) :
    ∑ v, Real.sqrt (chainMass a u.val / chainMass a v.val) * pathMatrix p A v u ≤ 1 := by
  classical
  by_cases hex : ∃ v : Fin (n + 1), v.val = u.val + 1
  · obtain ⟨v, hv⟩ := hex
    rw [Finset.sum_eq_single v]
    · exact pathMatrix_entry_le_one p A a ha hdom v u
    · intro w _ hwv
      have hs : w.val ≠ u.val + 1 := by
        intro hw
        apply hwv
        apply Fin.ext
        omega
      simp only [pathMatrix, ite_eq_right hs, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · have hs : ∀ v : Fin (n + 1), v.val ≠ u.val + 1 := by simpa only [not_exists] using hex
    simp only [pathMatrix, ite_eq_right (hs _), mul_zero, Finset.sum_const_zero, zero_le_one]

omit ha hdom

/-- The chronological edge weight, extended by one beyond the finite path. -/
def pathEdgeWeight {ι : Type*} {n : ℕ} (p : Fin (n + 1) → ι) (A : ι → ι → ℝ) (j : ℕ) : ℝ :=
  if hj : j < n then A (p ⟨j + 1, by omega⟩) (p ⟨j, by omega⟩) else 1

/-- The canonical adapted path masses. -/
def pathMass {ι : Type*} {n : ℕ} (p : Fin (n + 1) → ι) (A : ι → ι → ℝ)
    (k : Fin (n + 1)) : ℝ := chainMass (pathEdgeWeight p A) k.val

/-- The positive path product, with one matrix entry per chronological edge. -/
def pathProduct {ι : Type*} {n : ℕ} (p : Fin (n + 1) → ι) (A : ι → ι → ℝ) : ℝ :=
  ∏ k : Fin n, A (p k.succ) (p k.castSucc)

/-- On a chronological edge the extended weight is its original matrix entry. -/
theorem pathEdgeWeight_fin {ι : Type*} {n : ℕ} (p : Fin (n + 1) → ι) (A : ι → ι → ℝ)
    (k : Fin n) : pathEdgeWeight p A k.val = A (p k.succ) (p k.castSucc) := by
  rw [pathEdgeWeight, dite_eq_left k.isLt]
  rfl

/-- Every adapted mass is positive on a path with positive entries. -/
theorem pathMass_pos {ι : Type*} {n : ℕ} (p : Fin (n + 1) → ι) (A : ι → ι → ℝ)
    (hpos : ∀ k : Fin n, 0 < A (p k.succ) (p k.castSucc)) (k : Fin (n + 1)) :
    0 < pathMass p A k := by
  apply chainMass_pos
  intro j hj
  have hjn : j < n := by have hk := k.isLt; omega
  rw [pathEdgeWeight_fin p A ⟨j, hjn⟩]
  exact hpos ⟨j, hjn⟩

/-- Adapted masses give both Schur sums at most one. -/
theorem pathMass_schur {ι : Type*} {n : ℕ} (p : Fin (n + 1) → ι) (A : ι → ι → ℝ)
    (hpos : ∀ k : Fin n, 0 < A (p k.succ) (p k.castSucc)) :
    (∀ v, ∑ u, Real.sqrt (pathMass p A u / pathMass p A v) * pathMatrix p A v u ≤ 1) ∧
      (∀ u, ∑ v, Real.sqrt (pathMass p A u / pathMass p A v) * pathMatrix p A v u ≤ 1) := by
  have ha : ∀ j < n, 0 < pathEdgeWeight p A j := by
    intro j hj
    rw [pathEdgeWeight_fin p A ⟨j, hj⟩]
    exact hpos ⟨j, hj⟩
  have hd (v u : Fin (n + 1)) (hs : v.val = u.val + 1) :
      A (p v) (p u) ≤ pathEdgeWeight p A u.val := by
    have hu : u.val < n := by have hv := v.isLt; omega
    rw [pathEdgeWeight, dite_eq_left hu]
    apply le_of_eq
    congr 1
    · apply congrArg p
      apply Fin.ext
      exact hs
  exact ⟨pathMatrix_row_le_one p A _ ha hd, pathMatrix_col_le_one p A _ ha hd⟩

/-- The first adapted mass is one. -/
@[simp] theorem pathMass_first {ι : Type*} {n : ℕ} (p : Fin (n + 1) → ι) (A : ι → ι → ℝ) :
    pathMass p A 0 = 1 := rfl

/-- The terminal square-root mass is the chronological product. -/
theorem pathMass_last_sqrt {ι : Type*} {n : ℕ} (p : Fin (n + 1) → ι) (A : ι → ι → ℝ)
    (hpos : ∀ k : Fin n, 0 < A (p k.succ) (p k.castSucc)) :
    Real.sqrt (pathMass p A (Fin.last n)) = pathProduct p A := by
  rw [pathMass, Fin.val_last, chainMass_sqrt]
  · rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro k _
    exact pathEdgeWeight_fin p A k
  · intro j hj
    rw [pathEdgeWeight_fin p A ⟨j, hj⟩]
    exact hpos ⟨j, hj⟩
end

/-! Finite backward paths and their positive matrix weights. -/

section
universe u

/-- A length-`n` path ending at a separately specified vertex, listed backwards. -/
def Incoming (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => ι × Incoming ι n

instance incomingFintype {ι : Type u} [Fintype ι] (n : ℕ) : Fintype (Incoming ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (Fintype (ι × Incoming ι n))

local instance incomingPathsPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The original source vertex of a backward path. -/
def incomingSource {ι : Type u} : ∀ {n : ℕ}, ι → Incoming ι n → ι
  | 0, v, _ => v
  | _ + 1, _, p => incomingSource p.1 p.2

/-- The chronological vertex sequence of a backward path. -/
def incomingVertices {ι : Type u} : ∀ {n : ℕ}, ι → Incoming ι n → Fin (n + 1) → ι
  | 0, v, _ => fun _ => v
  | n + 1, v, p => fun k => Fin.lastCases (motive := fun _ : Fin (n + 2) => ι)
      v (incomingVertices p.1 p.2) k

@[simp] theorem incomingVertices_last {ι : Type u} {n : ℕ} (v : ι) (p : Incoming ι n) :
    incomingVertices v p (Fin.last n) = v := by
  cases n <;> simp only [incomingVertices, Fin.lastCases_last]

@[simp] theorem incomingVertices_first {ι : Type u} {n : ℕ} (v : ι) (p : Incoming ι n) :
    incomingVertices v p 0 = incomingSource v p := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    change Fin.lastCases (motive := fun _ : Fin (n + 2) => ι) v (incomingVertices p.1 p.2) (Fin.castSucc 0) = _
    rw [Fin.lastCases_castSucc]
    exact ih p.1 p.2

/-- The product of the positive matrix entries along a backward path. -/
def incomingWeight {ι : Type u} (A : ι → ι → ℝ) : ∀ {n : ℕ}, ι → Incoming ι n → ℝ
  | 0, _, _ => 1
  | _ + 1, v, p => A v p.1 * incomingWeight A p.1 p.2

variable {ι : Type u} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- A path retains only actual edges with positive envelope entries. -/
def IncomingValid (F : ChartedFamily ι h D P Ctx) (A : ι → ι → ℝ) :
    ∀ {n : ℕ}, ι → Incoming ι n → Prop
  | 0, _, _ => True
  | _ + 1, v, p => Nonempty (F.Γ v p.1) ∧ 0 < A v p.1 ∧ IncomingValid F A p.1 p.2

/-- Each chronological step retains an actual edge and has a positive envelope entry. -/
theorem incomingVertices_edges (F : ChartedFamily ι h D P Ctx) (A : ι → ι → ℝ)
    {n : ℕ} (v : ι) (p : Incoming ι n) (hp : IncomingValid F A v p) (k : Fin n) :
    Nonempty (F.Γ (incomingVertices v p k.succ) (incomingVertices v p k.castSucc)) ∧
      0 < A (incomingVertices v p k.succ) (incomingVertices v p k.castSucc) := by
  induction n generalizing v with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simpa only [incomingVertices, Fin.succ_last, Fin.lastCases_last,
        Fin.lastCases_castSucc, incomingVertices_last] using And.intro hp.1 hp.2.1
    · simpa only [incomingVertices, ← Fin.castSucc_succ, Fin.lastCases_castSucc]
        using ih p.1 p.2 hp.2.2 j

/-- Each retained path is a literal edge path in the original family. -/
theorem incomingValid_hasEdgePath (F : ChartedFamily ι h D P Ctx) (A : ι → ι → ℝ)
    {n : ℕ} (v : ι) (p : Incoming ι n) (hp : IncomingValid F A v p) :
    HasEdgePath F n (incomingSource v p) v := by
  induction n generalizing v with
  | zero => exact ⟨fun _ => v, rfl, rfl, fun k => Fin.elim0 k⟩
  | succ n ih =>
    have hedge : HasEdgePath F 1 p.1 v := by
      refine ⟨![p.1, v], rfl, rfl, ?_⟩
      intro k
      fin_cases k
      exact hp.1
    exact hasEdgePath_concat (ih p.1 p.2 hp.2.2) hedge

/-- Depth excludes every retained path longer than `H`. -/
theorem incomingValid_length (F : ChartedFamily ι h D P Ctx) (A : ι → ι → ℝ)
    {H n : ℕ} (hdepth : F.HasDepthAtMost H) (v : ι) (p : Incoming ι n)
    (hp : IncomingValid F A v p) : n ≤ H := by
  by_contra hn
  exact not_hasEdgePath_of_depth hdepth (Nat.lt_of_not_ge hn) _ _
    (incomingValid_hasEdgePath F A v p hp)

/-- Arbitrary path weights are nonnegative when the matrix is positive. -/
theorem incomingWeight_nonneg (A : ι → ι → ℝ) (hA : ∀ v u, 0 ≤ A v u)
    {n : ℕ} (v : ι) (p : Incoming ι n) : 0 ≤ incomingWeight A v p := by
  induction n generalizing v with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hA _ _) (ih p.1 p.2)

/-- Matrix powers are sums of all length-`n` path weights with the specified source. -/
theorem incomingWeight_sum [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (n : ℕ) (v u : ι) :
    ∑ p : Incoming ι n, (if incomingSource v p = u then incomingWeight A v p else 0) =
      (A ^ n) v u := by
  classical
  induction n generalizing v with
  | zero =>
    change (∑ _p : PUnit, (if v = u then (1 : ℝ) else 0)) = (A ^ 0) v u
    simp [Matrix.one_apply]
  | succ n ih =>
    change (∑ p : ι × Incoming ι n,
      if incomingSource p.1 p.2 = u then A v p.1 * incomingWeight A p.1 p.2 else 0) = _
    rw [Fintype.sum_prod_type, pow_succ', Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [← ih k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split <;> simp_all only [mul_zero]

/-- Restricting to actual positive paths only decreases a positive matrix-power entry. -/
theorem incomingValid_weight_sum_le [Fintype ι] [DecidableEq ι]
    (F : ChartedFamily ι h D P Ctx) (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (n : ℕ) (v u : ι) :
    ∑ p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u},
      incomingWeight A v p.val ≤ (A ^ n) v u := by
  classical
  rw [← incomingWeight_sum A n v u]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Incoming ι n =>
    IncomingValid F A v p ∧ incomingSource v p = u)) (by simp) (incomingWeight A v)]
  calc
    _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Incoming ι n =>
        IncomingValid F A v p ∧ incomingSource v p = u),
        (if incomingSource v p = u then incomingWeight A v p else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [ite_eq_left (Finset.mem_filter.mp hp).2.2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => by
        split
        · exact incomingWeight_nonneg A hA v p
        · exact le_refl 0)

/-- Chronological and backward products give the same path weight. -/
theorem pathProduct_incomingVertices (A : ι → ι → ℝ) {n : ℕ}
    (v : ι) (p : Incoming ι n) :
    pathProduct (incomingVertices v p) A = incomingWeight A v p := by
  induction n generalizing v with
  | zero => simp only [pathProduct, Finset.univ_eq_empty, Finset.prod_empty, incomingWeight]
  | succ n ih =>
    unfold pathProduct
    rw [Fin.prod_univ_castSucc]
    simp only [incomingVertices, Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc,
      incomingVertices_last, incomingWeight]
    have hp : (∏ k : Fin n,
        A (incomingVertices p.1 p.2 k.succ) (incomingVertices p.1 p.2 k.castSucc)) =
        incomingWeight A p.1 p.2 := ih p.1 p.2
    have he : (∏ k : Fin n,
        A (Fin.lastCases (motive := fun _ : Fin (n + 2) => ι) v
          (incomingVertices p.1 p.2) k.castSucc.succ)
          (incomingVertices p.1 p.2 k.castSucc)) = incomingWeight A p.1 p.2 := by
      simpa only [← Fin.castSucc_succ, Fin.lastCases_castSucc] using hp
    rw [he, mul_comm]

/-- The disjoint source fibres partition the retained backward paths. -/
def incomingSourceFiberEquiv (F : ChartedFamily ι h D P Ctx) (A : ι → ι → ℝ)
    (n : ℕ) (v : ι) :
    (Σ u, {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u}) ≃
      {p : Incoming ι n // IncomingValid F A v p} where
  toFun p := ⟨p.2.val, p.2.property.1⟩
  invFun p := ⟨incomingSource v p.val, ⟨p.val, ⟨p.property, rfl⟩⟩⟩
  left_inv := by
    rintro ⟨u, p, hp, hs⟩
    cases hs
    rfl
  right_inv := fun _ => rfl

/-- Finite sums over retained paths may be grouped by their source vertex. -/
theorem incomingSource_sum [Fintype ι] {E : Type*} [AddCommMonoid E]
    (F : ChartedFamily ι h D P Ctx) (A : ι → ι → ℝ) (n : ℕ) (v : ι)
    [∀ u, Fintype {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u}]
    [Fintype {p : Incoming ι n // IncomingValid F A v p}]
    (g : {p : Incoming ι n // IncomingValid F A v p} → E) :
    (∑ u, ∑ p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u},
      g ⟨p.val, p.property.1⟩) = ∑ p, g p := by
  classical
  rw [← Fintype.sum_sigma' (fun (u : ι)
    (p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u}) =>
      g ⟨p.val, p.property.1⟩)]
  exact Fintype.sum_equiv (incomingSourceFiberEquiv F A n v) _ g (fun _ => rfl)

/-- Summing a majorant over all backward paths is multiplication by the positive matrix power. -/
theorem incomingWeight_majorant_sum [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (n : ℕ) (v : ι) (G : ι → ℝ) :
    (∑ p : Incoming ι n, incomingWeight A v p * G (incomingSource v p)) =
      ∑ u, (A ^ n) v u * G u := by
  classical
  symm
  simp_rw [← incomingWeight_sum A n v, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single (incomingSource v p)]
  · rw [ite_eq_left rfl]
  · intro u _ hu
    rw [ite_eq_right (Ne.symm hu), zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
end

end AVRegularity.CycleJointProofs.PathReduction
end
