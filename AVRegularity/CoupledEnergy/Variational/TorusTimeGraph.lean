-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Passage of bounded coefficient terms through the common ambient coupled
weak limit. A fixed derivative or tensor readout is applied after compactness. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Any fixed spatial readout preserves scalar weak convergence in time. -/
theorem coupledHighReadout_weak_limit (K : ι → ℕ) (a b : ℝ)
    (U : ℕ → CoupledHighTime (h := h) K a b) (V : CoupledHighTime (h := h) K a b)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (R : CoupledHighHilbert (h := h) K →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) E)
    (ell : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
      (volume.restrict (Set.Icc a b)) →L[ℝ] ℝ) :
    Tendsto (fun n => ell (R.compLpL 2 (volume.restrict (Set.Icc a b)) (U n))) atTop
      (𝓝 (ell (R.compLpL 2 (volume.restrict (Set.Icc a b)) V))) := by
  exact hw (ell.comp (R.compLpL 2 (volume.restrict (Set.Icc a b))))

end AVRegularity.CoupledEnergy.Variational
end

section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Recover the periodic Sobolev graph after ambient spacetime weak compactness. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Project each ambient jet onto its closed periodic weak-derivative graph. -/
def coupledHighGraphProjection (K : ι → ℕ) :
    CoupledHighHilbert (h := h) K →L[ℝ] CoupledHighHilbert (h := h) K :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (torusHkGraph (E := h i) (K i + 1)).toSubmodule.starProjection.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun j => JetL2 (volume.restrict AVenhance.unitCube) (K j + 1) (h j)) i)))

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)] in
@[simp] theorem coupledHighGraphProjection_apply (K : ι → ℕ)
    (D : CoupledHighHilbert (h := h) K) (i : ι) :
    coupledHighGraphProjection K D i =
      (torusHkGraph (E := h i) (K i + 1)).toSubmodule.starProjection (D i) := rfl

/-- The complementary projection measures exactly the periodic graph constraints. -/
def coupledHighGraphConstraint (K : ι → ℕ) :
    CoupledHighHilbert (h := h) K →L[ℝ] CoupledHighHilbert (h := h) K :=
  ContinuousLinearMap.id ℝ _ - coupledHighGraphProjection K

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)] in
/-- Vanishing of the complementary projection is exactly simultaneous graph membership. -/
theorem coupledHighGraphConstraint_eq_zero_iff (K : ι → ℕ)
    (D : CoupledHighHilbert (h := h) K) :
    coupledHighGraphConstraint K D = 0 ↔ ∀ i, D i ∈ torusHkGraph (E := h i) (K i + 1) := by
  constructor
  · intro hd i
    have hi := congrArg (fun x : CoupledHighHilbert (h := h) K => x i) hd
    change D i - (torusHkGraph (E := h i) (K i + 1)).toSubmodule.starProjection (D i) = 0 at hi
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hi).symm
  · intro hd
    apply PiLp.ext
    intro i
    change D i - (torusHkGraph (E := h i) (K i + 1)).toSubmodule.starProjection (D i) = 0
    rw [Submodule.starProjection_eq_self_iff.mpr (hd i), sub_self]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)] in
/-- Ambient spacetime weak limits retain periodic weak jets almost everywhere. -/
theorem highTime_graph_of_weak_limit (K : ι → ℕ) (a b : ℝ)
    {u : ℕ → CoupledHighTime (h := h) K a b} {U : CoupledHighTime (h := h) K a b}
    (hlim : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (u n)) atTop (𝓝 (ell U)))
    (hu : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      ∀ i, u n t i ∈ torusHkGraph (E := h i) (K i + 1)) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i, U t i ∈ torusHkGraph (E := h i) (K i + 1) := by
  let : ∀ i, InnerProductSpace ℝ (JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i)) := fun i => inferInstance
  let : InnerProductSpace ℝ (CoupledHighHilbert (h := h) K) :=
    PiLp.innerProductSpace (fun i => JetL2 (volume.restrict AVenhance.unitCube) (K i + 1) (h i))
  let : InnerProductSpace ℝ (CoupledHighTime (h := h) K a b) := L2.innerProductSpace
  let L := (coupledHighGraphConstraint (h := h) K).compLpL 2 (volume.restrict (Set.Icc a b))
  have hn (n : ℕ) : L (u n) = 0 := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (coupledHighGraphConstraint K) (u n),
      hu n, Lp.coeFn_zero (E := CoupledHighHilbert (h := h) K) (p := 2) (μ := volume.restrict (Set.Icc a b))] with t ht hg hz
    rw [ht, hz]
    exact (coupledHighGraphConstraint_eq_zero_iff K (u n t)).mpr hg
  have hzero := map_eq_zero_of_weak_limit L hlim hn
  have hae := ContinuousLinearMap.coeFn_compLpL (coupledHighGraphConstraint K) U
  rw [hzero] at hae
  filter_upwards [hae, Lp.coeFn_zero (E := CoupledHighHilbert (h := h) K) (p := 2) (μ := volume.restrict (Set.Icc a b))] with t ht hz
  apply (coupledHighGraphConstraint_eq_zero_iff K (U t)).mp
  exact ht.symm.trans hz

end AVRegularity.CoupledEnergy.Variational
end
