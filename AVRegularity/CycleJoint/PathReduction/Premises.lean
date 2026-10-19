-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PathReduction.Paths
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.Error.WeakSolution
public import AVRegularity.CoupledEnergy.Variational.TorusRawSpatialForm
public import AVRegularity.CycleJoint.Assembly.CentreFlowWindow
import AVRegularity.CycleJoint.PreparationReferenceCellInitialHomogeneousResponsePair
import AVRegularity.CycleJoint.PreparationReferenceNormalizedHilbertCurve
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
import AVRegularity.CycleReference.TransitionZero
public import AVRegularity.CycleJoint.Assembly.CycleJointOfIngredients
import AVRegularity.Families.TorusCompatible.WeakStage
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleJointProofs.Assembly
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs.PathReduction

/-! Entrywise corner bounds extracted from the mass-weighted core. -/

/-- A positive mass-weighted square estimate is an entrywise estimate. -/
theorem weighted_corner_bound (πin πout C x y : ℝ) (hπin : 0 < πin) (hπout : 0 < πout)
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : πout⁻¹ * y ^ 2 ≤ C ^ 2 * πin⁻¹ * x ^ 2) :
    y ≤ C * Real.sqrt (πout / πin) * x := by
  have hr : 0 ≤ πout / πin := (div_pos hπout hπin).le
  have hs := Real.sq_sqrt hr
  have hmul := mul_le_mul_of_nonneg_left h hπout.le
  have hinv : πout * (πout⁻¹ * y ^ 2) = y ^ 2 := by
    rw [← mul_assoc, mul_inv_cancel₀ hπout.ne', one_mul]
  rw [hinv] at hmul
  have hright : πout * (C ^ 2 * πin⁻¹ * x ^ 2) =
      (C * Real.sqrt (πout / πin) * x) ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    simp only [div_eq_mul_inv]
    ring
  rw [hright] at hmul
  exact (sq_le_sq₀ hy (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hx)).mp hmul

/-- A component is bounded by a positive weighted sum of squares. -/
theorem weighted_component_sq_le_sum {ι : Type*} [Fintype ι]
    (π y : ι → ℝ) (hπ : ∀ i, 0 < π i) (v : ι) :
    (π v)⁻¹ * y v ^ 2 ≤ ∑ j, (π j)⁻¹ * y j ^ 2 :=
  Finset.single_le_sum (fun j _ => mul_nonneg (inv_nonneg.mpr (hπ j).le) (sq_nonneg _))
    (Finset.mem_univ v)

section Corners
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Truncating a single periodic component keeps exactly that component. -/
theorem truncateTorusHk_single (K : ι → ℕ) (u : ι) (f : TorusHk (K u) (h u)) :
    (fun j => truncateTorusHk (Nat.zero_le (K j))
      ((Pi.single u f : ∀ j, TorusHk (K j) (h j)) j)) =
      (Pi.single u (truncateTorusHk (Nat.zero_le _) f) : ∀ j, TorusHk 0 (h j)) := by
  classical
  funext j
  by_cases hj : j = u
  · subst j
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- A prepared bound on one component extends to its single-component datum. -/
theorem torusSingle_prepared_bound (K : ι → ℕ) (ρ : ℝ) (u : ι)
    (f : TorusHk (K u) (h u)) (G : ℝ) (hf : torusHkNorm ρ (le_refl (K u)) f ≤ G) (j : ι) :
    torusHkNorm ρ (le_refl (K j)) ((Pi.single u f : ∀ j, TorusHk (K j) (h j)) j) ≤
      (Pi.single u G : ι → ℝ) j := by
  classical
  by_cases hj : j = u
  · subst j
    rw [Pi.single_eq_same, Pi.single_eq_same]
    exact hf
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj,
      CycleComparison.Reconstruction.torusHkNorm_zero]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The mass of a single scalar majorant is exactly one weighted square. -/
theorem single_scalar_mass (π : ι → ℝ) (u : ι) (G : ℝ) :
    (∑ j, (π j)⁻¹ * (Pi.single u G : ι → ℝ) j ^ 2) = (π u)⁻¹ * G ^ 2 := by
  classical
  rw [Finset.sum_eq_single u]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- Input at one component, followed by the core and output at one component. -/
def modelCorner (K : ι → ℕ) (Mout : ℕ)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)))
    (v u : ι) : TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v) :=
  (LinearMap.proj v).comp (Tm.comp (LinearMap.single ℝ (fun u => TorusHk 0 (h u)) u))

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The weighted input norm of a single component has exactly one term. -/
theorem single_torus_mass (π : ι → ℝ) (u : ι) (f : TorusHk 0 (h u)) :
    ∑ j, (π j)⁻¹ * torusHkNorm 1 (le_refl 0) ((Pi.single u f : ∀ j, TorusHk 0 (h j)) j) ^ 2 =
      (π u)⁻¹ * torusHkNorm (E := h u) 1 (le_refl 0) f ^ 2 := by
  classical
  rw [Finset.sum_eq_single u]
  · rw [Pi.single_eq_same]
  · intro j _ hju
    rw [Pi.single_eq_of_ne hju]
    rw [torusHkNorm_zero_input]
    simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- A mass model supplies its precise entrywise corner estimate. -/
theorem modelCorner_bound (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (Mout : ℕ)
    (ρ C : ℝ) (hC : 0 ≤ C)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)))
    (hm : IsRawMassModel (h := h) π K Mout ρ C Tm) (v u : ι) (f : TorusHk 0 (h u)) :
    torusHkNorm (E := h v) ρ (le_max_left Mout (K v)) (modelCorner (h := h) K Mout Tm v u f) ≤
      C * Real.sqrt (π v / π u) * torusHkNorm (E := h u) 1 (le_refl 0) f := by
  let fin : ∀ j, TorusHk 0 (h j) := Pi.single u f
  have hh := hm fin
  rw [show fin = Pi.single u f from rfl, single_torus_mass (h := h), ← mul_assoc] at hh
  have hs : (π v)⁻¹ * torusHkNorm (E := h v) ρ (le_max_left Mout (K v))
      (Tm fin v) ^ 2 ≤
      ∑ j, (π j)⁻¹ * torusHkNorm (E := h j) ρ (le_max_left Mout (K j)) (Tm fin j) ^ 2 :=
    weighted_component_sq_le_sum π (fun j => torusHkNorm (E := h j)
      ρ (le_max_left Mout (K j)) (Tm fin j)) hπ v
  exact weighted_corner_bound _ _ _ _ _ (hπ u) (hπ v) hC
    (by exact Real.sqrt_nonneg _) (by exact Real.sqrt_nonneg _) (hs.trans hh)

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- A mass L2 estimate supplies the same corner estimate at order zero. -/
theorem modelCorner_l2 (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (Mout : ℕ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (Tm : (∀ u, TorusHk 0 (h u)) →ₗ[ℝ] (∀ v, TorusHk (max Mout (K v)) (h v)))
    (hm : IsRawMassL2 (h := h) π K Mout δ Tm) (v u : ι) (f : TorusHk 0 (h u)) :
    torusHkNorm (E := h v) 1 (Nat.zero_le _) (modelCorner (h := h) K Mout Tm v u f) ≤
      δ * Real.sqrt (π v / π u) * torusHkNorm (E := h u) 1 (le_refl 0) f := by
  let fin : ∀ j, TorusHk 0 (h j) := Pi.single u f
  have hh := hm fin
  rw [show fin = Pi.single u f from rfl, single_torus_mass (h := h), ← mul_assoc] at hh
  have hs : (π v)⁻¹ * torusHkNorm (E := h v) 1 (Nat.zero_le _) (Tm fin v) ^ 2 ≤
      ∑ j, (π j)⁻¹ * torusHkNorm (E := h j) 1 (Nat.zero_le _) (Tm fin j) ^ 2 :=
    weighted_component_sq_le_sum π (fun j => torusHkNorm (E := h j)
      1 (Nat.zero_le _) (Tm fin j)) hπ v
  exact weighted_corner_bound _ _ _ _ _ (hπ u) (hπ v) hδ
    (by exact Real.sqrt_nonneg _) (by exact Real.sqrt_nonneg _) (hs.trans hh)

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- A component's factorial norm is bounded by the mass norm times its square-root mass. -/
theorem torus_component_mass_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ)
    (ρ : ℝ) (f : ∀ i, TorusHk (K i) (h i)) (v : ι) :
    torusHkNorm (E := h v) ρ (le_refl (K v)) (f v) ≤
      Real.sqrt (π v) * Real.sqrt (massNormSq ρ π (fun i => (f i).val)) := by
  have hs := weighted_component_sq_le_sum π
    (fun i => torusHkNorm (E := h i) ρ (le_refl (K i)) (f i)) hπ v
  simp only [torusHkNorm_full, Real.sq_sqrt (factorialNormSq_nonneg _ _)] at hs
  have hm := mul_le_mul_of_nonneg_left hs (hπ v).le
  rw [← mul_assoc, mul_inv_cancel₀ (hπ v).ne', one_mul] at hm
  change factorialNormSq ρ (f v).val ≤ π v * massNormSq ρ π (fun i => (f i).val) at hm
  have hroot := Real.sqrt_le_sqrt hm
  rw [Real.sqrt_mul (hπ v).le] at hroot
  rw [torusHkNorm_full]
  exact hroot

end Corners

end AVRegularity.CycleJointProofs.PathReduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.PathReduction

/-! Finite superposition of torus solutions, retaining their traces and Sobolev lifts. -/

open AVRegularity.CycleComparison.Error

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
  {A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h i))}

/-- Addition follows from the already proved difference identity, including integrability. -/
theorem torusWeakSolution_add
    {f f' : ∀ i, TorusHk (K i) (h i)}
    {F F' : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g g' u u' : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hs' : IsCoupledWeakSolutionTorus ν a b v D K A f' F' g' u' w') :
    IsCoupledWeakSolutionTorus ν a b v D K A (fun i => f i + f' i)
      (fun i s => F i s + F' i s) (fun i s => g i s + g' i s)
      (fun i s => u i s + u' i s) (fun i s => w i s + w' i s) := by
  have hz := isCoupledWeakSolutionTorus_sub hs hs
  simp only [sub_self] at hz
  have hn := isCoupledWeakSolutionTorus_sub hz hs'
  simp only [zero_sub] at hn
  simpa only [sub_neg_eq_add] using isCoupledWeakSolutionTorus_sub hs hn

/-- A nonempty finite sum of solutions solves the equation with the summed data. -/
theorem torusWeakSolution_finset_sum {J : Type*}
    (f : J → ∀ i, TorusHk (K i) (h i))
    (F : J → ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : J → ∀ i, ℝ → TorusHk (K i) (h i))
    (w : J → ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hs : ∀ j, IsCoupledWeakSolutionTorus ν a b v D K A (f j) (F j) (g j) (u j) (w j))
    (S : Finset J) (hne : S.Nonempty) :
    IsCoupledWeakSolutionTorus ν a b v D K A (fun i => ∑ j ∈ S, f j i)
      (fun i t => ∑ j ∈ S, F j i t) (fun i t => ∑ j ∈ S, g j i t)
      (fun i t => ∑ j ∈ S, u j i t) (fun i t => ∑ j ∈ S, w j i t) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hne).elim
  | @insert j S hj ih =>
    by_cases hS : S.Nonempty
    · simp only [Finset.sum_insert hj]
      exact torusWeakSolution_add (hs j) (ih hS)
    · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simpa only [Finset.sum_insert hj, Finset.sum_empty, add_zero] using hs j

end AVRegularity.CycleJointProofs.PathReduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs.PathReduction

/-! Scalar rows of the coupled system, with their incoming flux as external forcing. -/

section
section Forcing
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}

/-- An almost-everywhere change of external flux forcing preserves the torus weak equation. -/
theorem torusWeakSolution_forcing_time_ae_congr
    {f : ∀ i, TorusHk (K i) (h i)}
    {F F' : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hF : ∀ i, ∀ᵐ s ∂volume.restrict (Set.Icc a b),
      (F i s).toFunction.jet (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
        (F' i s).toFunction.jet (valueIndex2 (K i)))
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionTorus ν a b v D K A f F' g u w := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro i t ht φ
  apply coupledWeakIdentity_time_ae_forcing_congr (volume.restrict AVenhance.unitCube)
    ν a t v _ _ _ _ _ _ _ _ _
    (fun k => φ.toFunction.hasPeriodicWeakJet.2.1 _) _ _ _ (hs.2.2.2.2 i t ht φ)
  · intro s _ k
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).comp_memLp'
        ((F i s).toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 (K i)))
  · intro s _ k
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).comp_memLp'
        ((F' i s).toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 (K i)))
  · exact ae_restrict_of_ae_restrict_of_subset
      (fun s hmem => ⟨hmem.1.le, hmem.2.trans ht.2⟩ : Set.Ioc a t ⊆ Set.Icc a b) (hF i)

end Forcing

section Row
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A scalar row at reserve `k`, with its incoming flux recorded as external forcing. -/
def IsTorusRowSolution (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (D k : ℕ)
    (f : TorusHk k E) (Q : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E)))
    (u : ℝ → TorusHk k E) (w : ℝ → TorusHk (k + 1) E) : Prop :=
  IsCoupledWeakSolutionTorus (ι := Fin 1) (h := fun _ => E) ν a b v D (fun _ => k)
    (fun _ _ _ _ _ => 0) (fun _ => f) (fun _ => Q) (fun _ _ => 0)
    (fun _ => u) (fun _ => w)

/-- A nonempty finite sum of rows solves the scalar row with summed incoming forcing. -/
theorem torusRowSolution_finset_sum {J : Type*} (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D k : ℕ) (f : J → TorusHk k E)
    (Q : J → ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E)))
    (u : J → ℝ → TorusHk k E) (w : J → ℝ → TorusHk (k + 1) E)
    (hs : ∀ j, IsTorusRowSolution ν a b v D k (f j) (Q j) (u j) (w j))
    (S : Finset J) (hS : S.Nonempty) :
    IsTorusRowSolution ν a b v D k (∑ j ∈ S, f j) (fun t => ∑ j ∈ S, Q j t)
      (fun t => ∑ j ∈ S, u j t) (fun t => ∑ j ∈ S, w j t) := by
  have hh := torusWeakSolution_finset_sum (ι := Fin 1) (h := fun _ => E)
    (ν := ν) (a := a) (b := b) (v := v) (D := D) (K := fun _ => k)
    (A := fun _ _ _ _ _ => 0)
    (fun j _ => f j) (fun j _ => Q j) (fun _ _ _ => 0)
    (fun j _ => u j) (fun j _ => w j) hs S hS
  simpa only [IsTorusRowSolution, Finset.sum_const_zero] using hh


/-- Almost-everywhere equality of incoming forcing carriers preserves a scalar row. -/
theorem torusRowSolution_forcing_congr (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D k : ℕ) (f : TorusHk k E)
    (Q Q' : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E)))
    (u : ℝ → TorusHk k E) (w : ℝ → TorusHk (k + 1) E)
    (hQ : Q =ᵐ[volume.restrict (Set.Icc a b)] Q')
    (hs : IsTorusRowSolution ν a b v D k f Q u w) :
    IsTorusRowSolution ν a b v D k f Q' u w := by
  apply torusWeakSolution_forcing_time_ae_congr (ι := Fin 1) (h := fun _ => E) _ hs
  intro _
  filter_upwards [hQ] with t ht
  exact Filter.EventuallyEq.of_eq (congrArg (fun z => z.toFunction.jet (valueIndex2 k)) ht)

end Row

section Extract
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
  {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}

/-- Extract one row of a coupled solution when a carrier represents its full incoming flux. -/
theorem torusWeakSolution_row
    (f : ∀ i, TorusHk (K i) (h i)) (u : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (i : ι) (Q : ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hQ : ∀ s ∈ Set.Icc a b, (Q s).toFunction.jet (valueIndex2 (K i)) =ᵐ[
      volume.restrict AVenhance.unitCube] torusRawCouplingFlux K D s A (fun j => w j s) i) :
    IsTorusRowSolution ν a b v D (K i) (f i) Q (u i) (w i) := by
  refine ⟨fun _ => hs.1 i, fun _ => hs.2.1 i,
    fun _ => hs.2.2.1 i, fun _ => hs.2.2.2.1 i, ?_⟩
  intro _ t ht φ
  have hold := hs.2.2.2.2 i t ht φ
  simp only [zero_apply, Finset.sum_const_zero]
  apply coupledWeakIdentity_flux_reallocation (volume.restrict AVenhance.unitCube) ν a t v
    _ _ _ _ _ _ _ _ _ _ ?_ hold
  intro s hs'
  have hsab : s ∈ Set.Icc a b := ⟨hs'.1.le, hs'.2.trans ht.2⟩
  filter_upwards [hQ s hsab, torusZero_rawJet_ae (E := PiLp 2 (fun _ : Fin 2 => h i))
    (K i) (valueIndex2 (K i))] with x hx hz
  simp only [torusRawCouplingFlux] at hx
  simp only [hx, hz, Pi.zero_apply, add_zero, zero_add]


/-- Scalar rows reconstruct a coupled solution when their external fluxes are its incoming flux. -/
theorem torusWeakSolution_of_rows
    (f : ∀ i, TorusHk (K i) (h i)) (u : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (Q : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hs : ∀ i, IsTorusRowSolution ν a b v D (K i) (f i) (Q i) (u i) (w i))
    (hQ : ∀ i, ∀ s ∈ Set.Icc a b, (Q i s).toFunction.jet (valueIndex2 (K i)) =ᵐ[
      volume.restrict AVenhance.unitCube] torusRawCouplingFlux K D s A (fun j => w j s) i) :
    IsCoupledWeakSolutionTorus ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w := by
  refine ⟨fun i => (hs i).1 0, fun i => (hs i).2.1 0,
    fun i => (hs i).2.2.1 0, fun i => (hs i).2.2.2.1 0, ?_⟩
  intro i t ht φ
  have hold := (hs i).2.2.2.2 0 t ht φ
  simp only [zero_apply, Finset.sum_const_zero] at hold
  apply coupledWeakIdentity_flux_reallocation (volume.restrict AVenhance.unitCube) ν a t v
    _ _ _ _ _ _ _ _ _ _ ?_ hold
  intro s hs'
  have hsab : s ∈ Set.Icc a b := ⟨hs'.1.le, hs'.2.trans ht.2⟩
  filter_upwards [hQ i s hsab, torusZero_rawJet_ae (E := PiLp 2 (fun _ : Fin 2 => h i))
    (K i) (valueIndex2 (K i))] with x hx hz
  simp only [torusRawCouplingFlux] at hx
  simp only [hx, hz, Pi.zero_apply, add_zero, zero_add]


/-- Spatial certificates of the actual coefficient array used to realize incoming flux carriers. -/
structure TorusCoefficientData (r : ℝ) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)) where
  radius_pos : 0 < r
  finite : ∀ i j d, coefficientSeminorm r (K i) a b (A i j d) ≠ ⊤
  smooth : ∀ t ∈ Set.Icc a b, ∀ i j d, ContDiff ℝ (K i : ℕ) (A i j d t)
  periodic : ∀ t ∈ Set.Icc a b, ∀ i j d, AVenhance.IsZ2Periodic (A i j d t)

variable {r : ℝ}

/-- The incoming flux from a single source, extended by zero outside its time window. -/
def TorusCoefficientData.edgeFlux (R : TorusCoefficientData (h := h) r K D a b A)
    (i j : ι) (t : ℝ) (w : TorusHk (K j + 1) (h j)) :
    TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) :=
  if ht : t ∈ Set.Icc a b then
    ∑ d : admissibleOrders K D i j, torusCoupledFluxTerm r R.radius_pos K D a b i j d
      (A i j d) (R.finite i j d) t ht (R.smooth t ht i j d) (R.periodic t ht i j d) w
  else 0

omit [Fintype ι] in
/-- Realizing an incoming flux commutes with subtraction. -/
theorem TorusCoefficientData.edgeFlux_sub (R : TorusCoefficientData (h := h) r K D a b A)
    (i j : ι) (t : ℝ) (w z : TorusHk (K j + 1) (h j)) :
    R.edgeFlux i j t (w - z) = R.edgeFlux i j t w - R.edgeFlux i j t z := by
  classical
  unfold TorusCoefficientData.edgeFlux
  split
  · simp only [torusCoupledFluxTerm_sub, Finset.sum_sub_distrib]
  · exact (sub_self 0).symm

omit [Fintype ι] in
/-- Zero input gives zero incoming flux. -/
theorem TorusCoefficientData.edgeFlux_zero (R : TorusCoefficientData (h := h) r K D a b A)
    (i j : ι) (t : ℝ) : R.edgeFlux i j t 0 = 0 := by
  have hh := R.edgeFlux_sub i j t 0 0
  simpa only [sub_self] using hh

omit [Fintype ι] in
/-- Incoming flux carriers commute with finite superposition. -/
theorem TorusCoefficientData.edgeFlux_add (R : TorusCoefficientData (h := h) r K D a b A)
    (i j : ι) (t : ℝ) (w z : TorusHk (K j + 1) (h j)) :
    R.edgeFlux i j t (w + z) = R.edgeFlux i j t w + R.edgeFlux i j t z := by
  have hh := R.edgeFlux_sub i j t (w + z) z
  rw [add_sub_cancel_right] at hh
  exact (sub_eq_iff_eq_add).mp hh.symm

omit [Fintype ι] in
/-- Incoming flux carriers commute with finite sums. -/
theorem TorusCoefficientData.edgeFlux_sum {J : Type*}
    (R : TorusCoefficientData (h := h) r K D a b A) (i j : ι) (t : ℝ)
    (S : Finset J) (w : J → TorusHk (K j + 1) (h j)) :
    R.edgeFlux i j t (∑ k ∈ S, w k) = ∑ k ∈ S, R.edgeFlux i j t (w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using R.edgeFlux_zero i j t
  | @insert k S hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, R.edgeFlux_add, ih]

/-- The canonical periodic representatives of a carrier sum agree almost everywhere. -/
theorem torusCarrier_jet_sum_ae {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E]
    {k : ℕ} {J : Type*} (S : Finset J)
    (f : J → TorusHk k E) (d : JetIndex2 k) :
    (∑ j ∈ S, f j).toFunction.jet d =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ j ∈ S, (f j).toFunction.jet d x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (torusZero_rawJet_ae k d).trans (Filter.Eventually.of_forall (fun _ => rfl))
  | @insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [(periodicJetRepresentative_add_global (f j).val (∑ k ∈ S, f k).val d).restrict,
      ih] with x hx hi
    exact hx.trans (congrArg ((f j).toFunction.jet d x + ·) hi)

omit [Fintype ι] in
/-- The realized edge flux has precisely the ordered derivative representative in the PDE. -/
theorem TorusCoefficientData.edgeFlux_value_ae (R : TorusCoefficientData (h := h) r K D a b A)
    (i j : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (w : TorusHk (K j + 1) (h j)) :
    (R.edgeFlux i j t w).toFunction.jet (valueIndex2 (K i)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x =>
      ∑ d : admissibleOrders K D i j, A i j d t x
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.val - 1) =>
          w.toFunction.jet ⟨⟨d.val - 1, by
            have hh := Finset.mem_filter.mp d.property
            have hd := Finset.mem_Icc.mp hh.1
            omega⟩, word⟩ x) := by
  classical
  rw [TorusCoefficientData.edgeFlux, dite_eq_left ht]
  apply (torusCarrier_jet_sum_ae Finset.univ _ _).trans
  have hall := ae_all_iff.mpr (fun d : admissibleOrders K D i j =>
    torusCoupledFluxTerm_value_ae r R.radius_pos K D a b i j d (A i j d) (R.finite i j d)
      t ht (R.smooth t ht i j d) (R.periodic t ht i j d) w)
  have hjets := ae_all_iff.mpr (fun d : JetIndex2 (K j + 1) => periodicJetRepresentative_ae w.val d)
  have hout := ae_all_iff.mpr (fun d : admissibleOrders K D i j =>
    periodicJetRepresentative_ae
      (torusCoupledFluxTerm r R.radius_pos K D a b i j d (A i j d) (R.finite i j d)
        t ht (R.smooth t ht i j d) (R.periodic t ht i j d) w).val (valueIndex2 (K i)))
  filter_upwards [hall, hjets, hout] with x hx hjx hox
  apply Finset.sum_congr rfl
  intro d _
  exact (hox d).trans ((hx d).trans (congrArg (fun z : PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) =>
    A i j d t x z) (by apply congrArg (WithLp.toLp 2); funext word; exact (hjx _).symm)))


/-- The sum of realized edge fluxes represents the full coupling in the weak equation. -/
theorem TorusCoefficientData.totalFlux_value_ae (R : TorusCoefficientData (h := h) r K D a b A)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (w : ∀ j, TorusHk (K j + 1) (h j)) :
    (∑ j, R.edgeFlux i j t (w j)).toFunction.jet (valueIndex2 (K i)) =ᵐ[
      volume.restrict AVenhance.unitCube] torusRawCouplingFlux K D t A w i := by
  have hall := ae_all_iff.mpr (fun j => R.edgeFlux_value_ae i j t ht (w j))
  filter_upwards [torusCarrier_jet_sum_ae Finset.univ (fun j => R.edgeFlux i j t (w j))
    (valueIndex2 (K i)), hall] with x hx hj
  apply hx.trans
  exact Finset.sum_congr rfl (fun j _ => hj j)

omit [Fintype ι] in
/-- An edge whose coefficients vanish on the window has zero incoming forcing carrier. -/
theorem TorusCoefficientData.edgeFlux_of_zero (R : TorusCoefficientData (h := h) r K D a b A)
    (i j : ι) (hz : ∀ d, ∀ t ∈ Set.Icc a b, ∀ x, A i j d t x = 0)
    (t : ℝ) (w : TorusHk (K j + 1) (h j)) : R.edgeFlux i j t w = 0 := by
  classical
  by_cases ht : t ∈ Set.Icc a b
  · apply TorusHk.ext_value
    change (R.edgeFlux i j t w).val (valueIndex2 (K i)) =
      (0 : ComponentL2 (volume.restrict AVenhance.unitCube) (PiLp 2 (fun _ : Fin 2 => h i)))
    apply Lp.ext
    have hraw := R.edgeFlux_value_ae i j t ht w
    filter_upwards [hraw,
      periodicJetRepresentative_ae (R.edgeFlux i j t w).val (valueIndex2 (K i)),
      Lp.coeFn_zero (PiLp 2 (fun _ : Fin 2 => h i)) 2
        (volume.restrict AVenhance.unitCube)] with x hx hr hzero
    rw [hzero]
    apply hr.symm.trans
    apply hx.trans
    apply Finset.sum_eq_zero
    intro d _
    rw [hz d t ht x]
    rfl
  · rw [TorusCoefficientData.edgeFlux, dite_eq_right ht]

end Extract
end

/-! Restrict a chain solution to an initial segment. Its earlier vertices do not
receive a source from the deleted terminal vertex. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ a, Ctx a) (K : ι → ℕ)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The coefficients on the retained initial segment are unchanged. -/
theorem pathCoefficient_prefix {n : ℕ} (p : Fin (n + 2) → ι)
    (v u : Fin (n + 1)) (d : admissibleOrders (K ∘ p ∘ Fin.castSucc) D v u)
    (t : ℝ) (x : Vec 2) :
    edgeCoefficient (F.pathFamily (p ∘ Fin.castSucc)) ν e E actual
        (K ∘ p ∘ Fin.castSucc) v u d t x =
      edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p) v.castSucc u.castSucc d t x := by
  by_cases hs : v.val = u.val + 1
  · exact (path_edgeCoefficient F (p ∘ Fin.castSucc) ν e E actual K v u hs d t x).trans
      (path_edgeCoefficient F p ν e E actual K v.castSucc u.castSucc hs d t x).symm
  · rw [path_edgeCoefficient_zero F (p ∘ Fin.castSucc) ν e E actual K v u hs d,
      path_edgeCoefficient_zero F p ν e E actual K v.castSucc u.castSucc hs d]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The sum of incoming fluxes at a retained vertex is the flux of the prefix. -/
theorem pathFlux_prefix {n : ℕ} (p : Fin (n + 2) → ι)
    (w : ∀ k, TorusHk (K (p k) + 1) (h (p k))) (v : Fin (n + 1))
    (t : ℝ) (x : Vec 2) :
    (∑ u : Fin (n + 2), ∑ d : admissibleOrders (K ∘ p) D v.castSucc u,
      edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p) v.castSucc u d t x
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.val - 1) =>
          (w u).toFunction.jet ⟨⟨d.val - 1, by
            have hh := Finset.mem_filter.mp d.property
            have hd := Finset.mem_Icc.mp hh.1
            dsimp only [Function.comp_apply] at hh
            omega⟩, word⟩ x)) =
    (∑ u : Fin (n + 1), ∑ d : admissibleOrders (K ∘ p ∘ Fin.castSucc) D v u,
      edgeCoefficient (F.pathFamily (p ∘ Fin.castSucc)) ν e E actual
        (K ∘ p ∘ Fin.castSucc) v u d t x
        (WithLp.toLp 2 fun word : DerivativeWord2 (d.val - 1) =>
          (w u.castSucc).toFunction.jet ⟨⟨d.val - 1, by
            have hh := Finset.mem_filter.mp d.property
            have hd := Finset.mem_Icc.mp hh.1
            dsimp only [Function.comp_apply] at hh
            omega⟩, word⟩ x)) := by
  classical
  rw [Fin.sum_univ_castSucc]
  have hz : ∀ d : admissibleOrders (K ∘ p) D v.castSucc (Fin.last (n + 1)),
      edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p) v.castSucc
        (Fin.last (n + 1)) d = 0 := by
    intro d
    apply path_edgeCoefficient_zero
    have hv := v.isLt
    simp only [Fin.val_castSucc, Fin.val_last]
    omega
  simp only [hz, Pi.zero_apply, zero_apply, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  apply congrArg (fun B :
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h (p u.castSucc)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h (p v.castSucc)) => B _)
  exact (pathCoefficient_prefix F ν e E actual K p v u d t x).symm

/-- Earlier components of a chain solution solve the prefix chain with their own data. -/
theorem pathWeakSolution_prefix {n : ℕ} (p : Fin (n + 2) → ι) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ k, TorusHk (K (p k)) (h (p k)))
    (u : ∀ k, ℝ → TorusHk (K (p k)) (h (p k)))
    (w : ∀ k, ℝ → TorusHk (K (p k) + 1) (h (p k)))
    (hs : IsCoupledWeakSolutionTorus ν a b v D (K ∘ p)
      (edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p))
      f (fun _ _ => 0) (fun _ _ => 0) u w) :
    IsCoupledWeakSolutionTorus ν a b v D (K ∘ p ∘ Fin.castSucc)
      (edgeCoefficient (F.pathFamily (p ∘ Fin.castSucc)) ν e E actual (K ∘ p ∘ Fin.castSucc))
      (fun k => f k.castSucc) (fun _ _ => 0) (fun _ _ => 0)
      (fun k => u k.castSucc) (fun k => w k.castSucc) := by
  refine ⟨fun k => hs.1 k.castSucc, fun k => hs.2.1 k.castSucc,
    fun k => hs.2.2.1 k.castSucc, fun k => hs.2.2.2.1 k.castSucc, ?_⟩
  intro k t ht φ
  have hh := hs.2.2.2.2 k.castSucc t ht φ
  simp_rw [pathFlux_prefix F ν e E actual K p] at hh
  exact hh


omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The terminal vertex receives precisely the original edge flux from its predecessor. -/
theorem pathRawFlux_last {n : ℕ} (p : Fin (n + 2) → ι)
    (w : ∀ k, TorusHk (K (p k) + 1) (h (p k))) (t : ℝ) (x : Vec 2) :
    torusRawCouplingFlux (K ∘ p) D t
      (edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p)) w (Fin.last (n + 1)) x =
      ∑ d : admissibleOrders K D (p (Fin.last (n + 1))) (p (Fin.last n).castSucc),
        edgeCoefficient F ν e E actual K (p (Fin.last (n + 1))) (p (Fin.last n).castSucc) d t x
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.val - 1) =>
            (w (Fin.last n).castSucc).toFunction.jet
              ⟨⟨d.val - 1, Nat.lt_succ_of_le (admissibleOrders_high_readout_bound K D
                (p (Fin.last (n + 1))) (p (Fin.last n).castSucc) d)⟩, word⟩ x) := by
  classical
  unfold torusRawCouplingFlux
  rw [Finset.sum_eq_single (Fin.last n).castSucc]
  · apply Finset.sum_congr rfl
    intro d _
    apply congrArg (fun B :
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h (p (Fin.last n).castSucc)) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h (p (Fin.last (n + 1)))) => B _)
    exact path_edgeCoefficient F p ν e E actual K _ _ (by simp only [Fin.val_last, Fin.val_castSucc]) d t x
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro d _
    have hz := path_edgeCoefficient_zero F p ν e E actual K (Fin.last (n + 1)) j
      (by intro hh; apply hj; apply Fin.ext; simp only [Fin.val_last, Fin.val_castSucc] at hh ⊢; omega) d
    rw [hz]
    rfl
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The trivial path has no incoming flux. -/
theorem pathRawFlux_zero (p : Fin 1 → ι)
    (w : ∀ k, TorusHk (K (p k) + 1) (h (p k))) (t : ℝ) (x : Vec 2) :
    torusRawCouplingFlux (K ∘ p) D t
      (edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p)) w 0 x = 0 := by
  unfold torusRawCouplingFlux
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro d _
  have hz := path_edgeCoefficient_zero F p ν e E actual K 0 j
    (by have hj := j.isLt; simp only [Fin.val_zero]; omega) d
  rw [hz]
  rfl
end

end AVRegularity.CycleJointProofs.PathReduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.CycleJointProofs.PathReduction

/-! All preparation premises transfer together to a restricted path. -/

universe u v w x

variable (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ)

/-- Restriction to a path preserves every geometric and coefficient premise.
Only the masses, matrix and Schur scale change. -/
theorem pathFamily_jointPremises
    (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold)
    {n : ℕ} (p : Fin (n + 1) → ι) (πp : Fin (n + 1) → ℝ)
    (hπp : ∀ k, 0 < πp k) (Θp : ℝ) (hΘp₀ : 0 ≤ Θp) (hΘp₁ : Θp ≤ 1)
    (hrow : ∀ v, ∑ u, Real.sqrt (πp u / πp v) * pathMatrix p A v u ≤ Θp)
    (hcol : ∀ u, ∑ v, Real.sqrt (πp u / πp v) * pathMatrix p A v u ≤ Θp) :
    JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca 1 Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      πp (K ∘ p) Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀
      (F.pathFamily p) actual (pathMatrix p A) Θp (ChartedFamily.pathAtlas F p T) ρold := by
  have hA (v u : ι) : 0 ≤ A v u :=
    (mul_nonneg_iff_of_pos_left
      (Real.sqrt_pos.mpr (div_pos (hprem.hπ u) (hprem.hπ v)))).mp (hprem.henv.nonneg v u)
  refine {
    hπ := hπp
    hK := fun k => hprem.hK (p k)
    hΦ := hprem.hΦ
    hband := hprem.hband
    hm2 := hprem.hm2
    hmStar := hprem.hmStar
    hmM := hprem.hmM
    hν := hprem.hν
    hB := hprem.hB
    cov := hprem.cov
    hwmeas := hprem.hwmeas
    hprep := F.pathFamily_preparation p α q Λ m (Φ (m - 1)) hφ tS
      (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P hprem.hprep
    hdepth := F.pathFamily_depth p hprem.hdepth
    hdesc := F.pathFamily_descending p K hprem.hdesc
    htorus := F.pathFamily_torus p actual _ hprem.htorus
    hcover := hprem.hcover
    hmeas := F.pathFamily_measurable p hprem.hmeas
    hΘ₀ := hΘp₀
    hΘ₁ := hΘp₁
    henv := ?_
    hpointwise := pathFamily_pointwise F p _ π hprem.hπ πp hπp K _ _ _ _ Cm Jm A hprem.hpointwise
    htrans := F.pathFamily_transverse p _ _ hprem.htrans
    hquiet := F.pathFamily_fastIndependent p _ hprem.hquiet
    hTcons := ChartedFamily.Atlas.pathFamily_consecutive F p T _ hprem.hTcons
    hTcov := ChartedFamily.Atlas.pathFamily_coversQuiet F p T _ _ hprem.hTcov
    hTq := ChartedFamily.Atlas.pathFamily_quiet F p T _ _ _ hprem.hTq
    hρold := hprem.hρold
    hρrat := hprem.hρrat }
  refine ⟨?_, ?_, ?_,
    pathFamily_analytic F p _ π hprem.hπ πp hπp _ Ca Ks Ls A hprem.henv.analytic,
    pathFamily_molecular F p _ π hprem.hπ πp hπp K _ _ _ _ Cm Jm A hprem.henv.molecular⟩
  · intro v u
    apply mul_nonneg (Real.sqrt_nonneg _)
    unfold pathMatrix
    split
    · exact hA _ _
    · exact le_refl 0
  · simpa only [one_mul] using hrow
  · simpa only [one_mul] using hcol

/-- **The renewal endpoint from the cover alone**: the endpoint `t_p = (l₀ + 3/2) τ''` lies in
the preparation window, is quiet, and is the centre of a quiet margin of half-width `τ'`. Only the
cover's window clause is used, so the endpoint precedes the masses. -/
theorem renewal_endpoint_facts {α q : ℝ} {Λ m : ℕ} (ζ : ℝ → ℝ) {tS : ℝ} {l₀ : ℤ}
    (hΛ : 128 ≤ Λ)
    (hw : ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ tS ∧ tS < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m) :
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) ∈ Set.Ioc tS (tS + 2 * ocTauPP α q Λ m) ∧
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) ∈ ocQuietTimes α q Λ ζ m ∧
    Set.Icc ((((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) - ocTauP α q Λ m)
      ((((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m := by
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m)
    (show 1 ≤ Λ by omega)
  have hP : 0 ≤ ocTauP α q Λ m := by
    unfold ocTauP
    exact div_nonneg hT.le (by positivity)
  have hcol := renewal_boundary_quiet_margin (α := α) (q := q) (m := m)
    (show 1 ≤ Λ by omega) ζ (l₀ + 1)
  have hcast : (((l₀ + 1 : ℤ) : ℝ) + 1 / 2) * ocTauPP α q Λ m =
      ((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m := by push_cast; ring
  rw [hcast] at hcol
  refine ⟨⟨?_, ?_⟩, hcol ⟨?_, ?_⟩, hcol⟩
  · linarith [hw.2]
  · linarith [hw.1]
  · linarith
  · linarith

variable {α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
  Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold}

variable (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold)

include hprem

/-- The prescribed renewal endpoint belongs to the preparation window and is quiet. -/
theorem preparation_endpoint (hΛ : 128 ≤ Λ) :
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) ∈
      Set.Ioc tS (tS + 2 * ocTauPP α q Λ m) ∧
    (((l₀ : ℝ) + 3 / 2) * ocTauPP α q Λ m) ∈ ocQuietTimes α q Λ ζ m := by
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m)
    (show 1 ≤ Λ by omega)
  have hw := hprem.cov.window
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · linarith [hw.2.1]
  · linarith [hw.1]
  · apply renewal_boundary_quiet_margin (show 1 ≤ Λ by omega) ζ (l₀ + 1)
    have hP : 0 ≤ ocTauP α q Λ m := by
      unfold ocTauP
      exact div_nonneg hT.le (by positivity)
    simp only [Int.cast_add, Int.cast_one]
    constructor <;> linarith

/-- The fine scale is no larger than its parent at every admissible preparation level. -/
theorem preparation_epsilon_le (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) := by
  have he := CycleReference.epsilon_succ_le (n := m - 1) hq hΛ
  have hm : m - 1 + 1 = m := by have hh := hprem.hm2; omega
  rwa [hm] at he

/-- Every restriction to a vertex chain has a solution; no adapted mass is needed for existence. -/
theorem preparation_path_exists_torus (hq : 1 < q) (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    {n : ℕ} (p : Fin (n + 1) → ι) (f : ∀ k, TorusHk (K (p k)) (h (p k))) :
    ∃ (u : ∀ k, ℝ → TorusHk (K (p k)) (h (p k)))
      (w : ∀ k, ℝ → TorusHk (K (p k) + 1) (h (p k))),
      IsCoupledWeakSolutionTorus ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D (K ∘ p)
        (edgeCoefficient (F.pathFamily p) ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (K ∘ p))
        f (fun _ _ => 0) (fun _ _ => 0) u w := by
  have hT := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m)
    (show 1 ≤ Λ by omega)
  have hA (v u : ι) : 0 ≤ A v u :=
    (mul_nonneg_iff_of_pos_left
      (Real.sqrt_pos.mpr (div_pos (hprem.hπ u) (hprem.hπ v)))).mp (hprem.henv.nonneg v u)
  have hAp (v u : Fin (n + 1)) : 0 ≤ pathMatrix p A v u := by
    unfold pathMatrix
    split
    · exact hA _ _
    · exact le_refl 0
  exact exists_actualPreparation_torus_solution (K ∘ p) Kmax (fun k => hprem.hK (p k))
    (ocRhoMol α q Λ m cMol ν) ν hprem.cov.pos.2.2 hprem.cov.pos.1
    tS (tS + 2 * ocTauPP α q Λ m) (by linarith) D (F.pathFamily p) H
    (F.pathFamily_depth p hprem.hdepth) α q Λ m Φ ζ hζ hprem.hΦ (Φ (m - 1)) hφ
    Cpad Cage Npad Jchart Cchart l₀ P (F.pathFamily_preparation p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hprem.hprep)
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual
    (F.pathFamily_measurable p hprem.hmeas) hprem.hwmeas rfl hprem.cov.rho_e
    (preparation_epsilon_le hprem hq hΛ) Jm hchart hmol Cm (fun _ => 1) (fun _ => zero_lt_one)
    (pathMatrix p A) hAp rfl (F.pathFamily_torus p actual _ hprem.htorus)
    (pathFamily_pointwise F p _ π hprem.hπ (fun _ => 1) (fun _ => zero_lt_one)
      K _ _ _ _ Cm Jm A hprem.hpointwise) f 1 zero_lt_one

/-- Restricted chain solutions with the same data agree on any initial subwindow. -/
theorem preparation_path_unique (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    {n : ℕ} (p : Fin (n + 1) → ι) (τ : ℝ)
    (hτ : τ ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
    (f : ∀ k, TorusHk (K (p k)) (h (p k)))
    (u u' : ∀ k, ℝ → TorusHk (K (p k)) (h (p k)))
    (w w' : ∀ k, ℝ → TorusHk (K (p k) + 1) (h (p k)))
    (hs : IsCoupledWeakSolutionTorus ν tS τ (streamVel (Φ m)) D (K ∘ p)
      (edgeCoefficient (F.pathFamily p) ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (K ∘ p))
      f (fun _ _ => 0) (fun _ _ => 0) u w)
    (hs' : IsCoupledWeakSolutionTorus ν tS τ (streamVel (Φ m)) D (K ∘ p)
      (edgeCoefficient (F.pathFamily p) ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (K ∘ p))
      f (fun _ _ => 0) (fun _ _ => 0) u' w') :
    ∀ k, ∀ t ∈ Set.Icc tS τ, u k t = u' k t := by
  have hB (v u : Fin (n + 1)) :
      0 ≤ Real.sqrt ((1 : ℝ) / 1) * pathMatrix p A v u := by
    simp only [div_self one_ne_zero, Real.sqrt_one, one_mul]
    unfold pathMatrix
    split
    · exact (mul_nonneg_iff_of_pos_left
        (Real.sqrt_pos.mpr (div_pos (hprem.hπ (p u)) (hprem.hπ (p v))))).mp (hprem.henv.nonneg (p v) (p u))
    · exact le_refl 0
  have hFzero (k : Fin (n + 1)) : MemLp
      (fun _ : ℝ => (0 : TorusHk (K (p k)) (PiLp 2 (fun _ : Fin 2 => h (p k)))))
      2 (volume.restrict (Set.Icc tS τ)) :=
    MemLp.zero' (ε := TorusHk (K (p k)) (PiLp 2 (fun _ : Fin 2 => h (p k))))
  have hgzero (k : Fin (n + 1)) : Integrable
      (fun _ : ℝ => (0 : TorusHk (K (p k)) (h (p k))))
      (volume.restrict (Set.Icc tS τ)) :=
    integrable_zero ℝ (TorusHk (K (p k)) (h (p k))) (volume.restrict (Set.Icc tS τ))
  have hprepp := F.pathFamily_preparation p α q Λ m (Φ (m - 1)) hφ
    tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P hprem.hprep
  have hpointp := pathFamily_pointwise F p (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
    π hprem.hπ (fun _ => 1) (fun _ => zero_lt_one) K ν (ocEpsilon q Λ m)
    (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν) Cm Jm A hprem.hpointwise
  have htorusp := F.pathFamily_torus p actual (ocEpsilon q Λ (m - 1)) hprem.htorus
  have hmeasp := F.pathFamily_measurable p hprem.hmeas
  have hdepthp := F.pathFamily_depth p hprem.hdepth
  have hscales := preparation_epsilon_le hprem hq hΛ
  have huniq := actualPreparation_torusWeakSolution_subwindow_unique
    (ι := Fin (n + 1)) (h := fun k => h (p k)) (K ∘ p) Kmax (fun k => hprem.hK (p k))
    (ocRhoMol α q Λ m cMol ν) ν hprem.cov.pos.2.2 hprem.cov.pos.1
    tS (tS + 2 * ocTauPP α q Λ m) D (F.pathFamily p) H
    hdepthp α q Λ m Φ ζ hprem.hΦ (Φ (m - 1)) hφ
    Cpad Cage Npad Jchart Cchart l₀ P hprepp
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual rfl
    htorusp hmeasp hprem.hwmeas
    rfl hprem.cov.rho_e hscales Jm hchart hmol Cm
    (fun _ => 1) (fun _ => zero_lt_one) (fun v u => Real.sqrt ((1 : ℝ) / 1) * pathMatrix p A v u) hB
    hpointp τ hτ.1 hτ.2
    (fun k _ => (0 : TorusHk (K (p k)) (PiLp 2 (fun _ : Fin 2 => h (p k)))))
    (fun k _ => (0 : TorusHk (K (p k)) (h (p k)))) hFzero hgzero
    f
  exact huniq u u' w w' hs hs'

/-- Homogeneous solutions of the original preparation family agree on each initial subwindow. -/
theorem preparation_unique (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (τ : ℝ) (hτ : τ ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
    (f : ∀ i, TorusHk (K i) (h i))
    (u u' : ∀ i, ℝ → TorusHk (K i) (h i))
    (w w' : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionTorus ν tS τ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) u w)
    (hs' : IsCoupledWeakSolutionTorus ν tS τ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) u' w') :
    ∀ i, ∀ t ∈ Set.Icc tS τ, u i t = u' i t := by
  have hFzero (i : ι) : MemLp
      (fun _ : ℝ => (0 : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))))
      2 (volume.restrict (Set.Icc tS τ)) :=
    MemLp.zero' (ε := TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
  have hgzero (i : ι) : Integrable (fun _ : ℝ => (0 : TorusHk (K i) (h i)))
      (volume.restrict (Set.Icc tS τ)) :=
    integrable_zero ℝ (TorusHk (K i) (h i)) (volume.restrict (Set.Icc tS τ))
  exact actualPreparation_torusWeakSolution_subwindow_unique K Kmax hprem.hK
    (ocRhoMol α q Λ m cMol ν) ν hprem.cov.pos.2.2 hprem.cov.pos.1
    tS (tS + 2 * ocTauPP α q Λ m) D F H hprem.hdepth α q Λ m Φ ζ hprem.hΦ
    (Φ (m - 1)) hφ Cpad Cage Npad Jchart Cchart l₀ P hprem.hprep
    (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual rfl hprem.htorus hprem.hmeas hprem.hwmeas
    rfl hprem.cov.rho_e (preparation_epsilon_le hprem hq hΛ) Jm hchart hmol Cm π hprem.hπ
    (fun v u => Real.sqrt (π u / π v) * A v u) hprem.henv.nonneg hprem.hpointwise
    τ hτ.1 hτ.2 (fun _ _ => 0) (fun _ _ => 0) hFzero hgzero f u u' w w' hs hs'

/-- A zero matrix entry gives an identically zero physical edge on the preparation window. -/
theorem preparation_edge_zero (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)
    (v u : ι) (hz : A v u = 0) (d : admissibleOrders K D v u)
    (t : ℝ) (ht : t ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)) (x : Vec 2) :
    edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K v u d t x = 0 := by
  have hA (v u : ι) : 0 ≤ A v u :=
    (mul_nonneg_iff_of_pos_left
      (Real.sqrt_pos.mpr (div_pos (hprem.hπ u) (hprem.hπ v)))).mp (hprem.henv.nonneg v u)
  obtain ⟨Cprep, hCprep, hsample⟩ := preparation_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hsampled := hsample α q Λ m (Φ (m - 1)) hφ tS (tS + 2 * ocTauPP α q Λ m)
    Cpad Cage Npad l₀ P ν (ocEpsilon q Λ m) (ocRhoMol α q Λ m cMol ν)
    hprem.cov.pos.1 hprem.cov.pos.2.2 hprem.cov.rho_e (preparation_epsilon_le hprem hq hΛ)
    F π hprem.hπ K hprem.hK actual (fun v u => Real.sqrt (π u / π v) * A v u)
    hprem.henv.nonneg hprem.hprep hprem.hpointwise
  have hb := sampledEnvelope_edgeCoefficient_bound F π hprem.hπ K actual
    tS (tS + 2 * ocTauPP α q Λ m) ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
    (ocRhoMol α q Λ m cMol ν) Cprep hprem.cov.pos.1 hprem.cov.pos.2.2
    (zero_le_one.trans hCprep) A hA hsampled v u d t ht x
  rw [hz, mul_zero] at hb
  let T : PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h u) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h v) :=
    edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K v u d t x
  have hT : ‖T‖ = 0 := le_antisymm hb (norm_nonneg T)
  exact (norm_eq_zero (a := T)).mp hT

/-- The preparation premises supply all spatial certificates for the actual edge array. -/
theorem preparationCoefficientData (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm) :
    TorusCoefficientData (h := h) (ocRhoMol α q Λ m cMol ν) K D
      tS (tS + 2 * ocTauPP α q Λ m)
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) := by
  obtain ⟨Cprep, _, hsample⟩ := preparation_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart hmol Cm Cchart
  have hsampled := hsample α q Λ m (Φ (m - 1)) hφ tS (tS + 2 * ocTauPP α q Λ m)
    Cpad Cage Npad l₀ P ν (ocEpsilon q Λ m) (ocRhoMol α q Λ m cMol ν)
    hprem.cov.pos.1 hprem.cov.pos.2.2 hprem.cov.rho_e (preparation_epsilon_le hprem hq hΛ)
    F π hprem.hπ K hprem.hK actual (fun v u => Real.sqrt (π u / π v) * A v u)
    hprem.henv.nonneg hprem.hprep hprem.hpointwise
  have hsmooth : F.IsSmoothOn (ChartedFamily.Domain.onWindow F
      (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) (ocEpsilon q Λ (m - 1)) K := by
    intro p c v u γ d I tY htY z
    exact (hprem.hpointwise.1 p c v u γ d I tY htY z).of_le
      (by exact_mod_cast Nat.le_add_right (K v) Jm)
  refine {
    radius_pos := hprem.cov.pos.2.2
    finite := ?_
    smooth := ?_
    periodic := ?_ }
  · exact sampledEnvelope_edge_seminorm_ne_top F π hprem.hπ K actual
      tS (tS + 2 * ocTauPP α q Λ m) ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1))
      (ocRhoMol α q Λ m cMol ν) Cprep hprem.cov.pos.1 hprem.cov.pos.2.2
      (fun v u => Real.sqrt (π u / π v) * A v u) hsampled
  · exact fun t ht v u d => edgeCoefficient_spatial_smooth F hprem.hprep ν
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) K hsmooth actual K v u d t ht
  · exact fun t _ v u d => hprem.htorus.edgeCoefficient_periodic_ocEpsilon ν K v u d t

end AVRegularity.CycleJointProofs.PathReduction
end
