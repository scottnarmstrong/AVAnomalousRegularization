-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.CleanupChain.Measurable
public import AVRegularity.CycleComparison.Reconstruction.PiolaTested
import AVRegularity.CycleComparison.Residual.QuietMean.CellMean
import AVRegularity.CycleComparison.Reconstruction.PrimWeak
public import AVRegularity.CycleComparison.CleanupChain.Main
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **A cleanup chain of data that are measurable in time is measurable in time**.

The cleanup chain is unique (`isCleanupChain_unique`), commutes with continuous linear maps of
the values (`IsCleanupChain.clm_comp`), and for complex scalar data it is the explicit Fourier
chain `CleanupChain.Vchain` (`scalar_cleanup_chain`). So for every continuous real linear
`L : E → ℂ`, the image `L ∘ V_j` of any cleanup chain `V` of `(f₀, F₀)` is the explicit chain of
`(L ∘ f₀, L ∘ F₀)` (`clm_cleanupChain_eq_Vchain`), and likewise for the source
`cleanupSource V A = -div_X V_{A-1}` (`clm_cleanupSource_eq_Vchain`). The explicit chain is
measurable in a parameter (`CleanupChain.measurable_Vchain_param`). Finite-dimensional values are
recovered from their functionals (`measurable_of_all_complex_clm`).

* `isCleanupChain_time_measurable_clm`, `cleanupSource_time_measurable_clm`: every continuous
  linear functional of the chain and of its last source is measurable in time;
* `isCleanupChain_time_measurable_pi`, `cleanupSource_time_measurable_pi`: values in a finite
  product, componentwise;
* joint measurability of the ordered derivatives of a jointly measurable family of `C^m` fields
  is `ResidualFlux.measurable_orderedDerivative`. -/

/-! ### Functionals of a cleanup chain at a fixed time -/

section Complete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The scalar data `L ∘ f₀`, `L ∘ F₀` inherit the hypotheses of the cleanup chain. -/
theorem clm_data_facts {N s : ℕ} {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E}
    (hf : IsBoxSmooth N s f₀) (hfp : ∀ X, AVenhance.IsZ2Periodic (f₀ X))
    (hfm : ∀ X, fieldCellMean (f₀ X) = 0)
    (hF : IsBoxSmooth N s F₀) (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0) (L : E →L[ℝ] ℂ) :
    IsBoxSmooth N s (fun X z => L (f₀ X z)) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z => L (f₀ X z))) ∧
      (∀ X, fieldCellMean (fun z => L (f₀ X z)) = 0) ∧
      IsBoxSmooth N s (fun X z k => L (F₀ X z k)) ∧
      (∀ X, AVenhance.IsZ2Periodic (fun z k => L (F₀ X z k))) ∧
      ∀ X (k : Fin 2), fieldCellMean (fun z => L (F₀ X z k)) = 0 := by
  have hg : IsBoxSmooth N s (fun X z => L (f₀ X z)) := hf.map_clm L
  have hG : IsBoxSmooth N s (fun X z k => L (F₀ X z k)) := hF.map_clm (clmVec L)
  have hgp : ∀ X, AVenhance.IsZ2Periodic (fun z => L (f₀ X z)) := fun X n z => by
    show L (f₀ X (z + AVenhance.latticeShift n)) = L (f₀ X z)
    rw [hfp X n z]
  have hGp : ∀ X, AVenhance.IsZ2Periodic (fun z k => L (F₀ X z k)) := fun X n z => by
    funext k
    show L (F₀ X (z + AVenhance.latticeShift n) k) = L (F₀ X z k)
    rw [hFp X n z]
  have hgm : ∀ X, fieldCellMean (fun z => L (f₀ X z)) = 0 := fun X => by
    rw [fieldCellMean_clm L (hf.1 X).continuous, hfm X, map_zero]
  have hGm : ∀ X (k : Fin 2), fieldCellMean (fun z => L (F₀ X z k)) = 0 := fun X k => by
    have hc : Continuous fun z => F₀ X z k := (continuous_apply k).comp (hF.1 X).continuous
    rw [fieldCellMean_clm L hc, hFm X k, map_zero]
  exact ⟨hg, hgp, hgm, hG, hGp, hGm⟩

/-- **A functional of a cleanup chain is the explicit scalar chain of the image data.** -/
theorem clm_cleanupChain_eq_Vchain {sX sZ A : ℕ} (hsX : 1 ≤ sX) (hsZ : 1 ≤ sZ)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hf : IsBoxSmooth (sX + A) (sZ + 1) f₀) (hfp : ∀ X, AVenhance.IsZ2Periodic (f₀ X))
    (hfm : ∀ X, fieldCellMean (f₀ X) = 0)
    (hF : IsBoxSmooth (sX + A) (sZ + 1) F₀) (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0)
    (hV : IsCleanupChain sX sZ A f₀ F₀ V) (L : E →L[ℝ] ℂ) (j : ℕ) (hj : j < A) :
    (fun X z k => L (V j X z k)) =
      AVRegularity.CleanupChain.Vchain (sZ + 1) (fun X z => L (f₀ X z))
        (fun X z k => L (F₀ X z k)) j := by
  obtain ⟨hg, hgp, hgm, hG, hGp, hGm⟩ := clm_data_facts hf hfp hfm hF hFp hFm L
  have hFs : IsSlowSmooth sX F₀ := (hF.mono (Nat.le_add_right sX A) le_rfl).isSlowSmooth
  have h1 : IsCleanupChain sX sZ A (fun X z => L (f₀ X z)) (fun X z k => L (F₀ X z k))
      (fun j X z k => L (V j X z k)) := IsCleanupChain.clm_comp hsX hsZ hFs hV L
  have h2 : IsCleanupChain sX sZ A (fun X z => L (f₀ X z)) (fun X z k => L (F₀ X z k))
      (AVRegularity.CleanupChain.Vchain (sZ + 1) (fun X z => L (f₀ X z))
        (fun X z k => L (F₀ X z k))) :=
    (AVRegularity.CleanupChain.scalar_cleanup_chain (sX := sX) (A := A) hsZ hg hgp hgm hG hGp
      hGm).1
  exact isCleanupChain_unique hsZ h1 h2 j hj

/-- **A functional of the last cleanup source is the source of the explicit scalar chain.** -/
theorem clm_cleanupSource_eq_Vchain {sX sZ A : ℕ} (hsX : 1 ≤ sX) (hsZ : 1 ≤ sZ) (hA : 1 ≤ A)
    {f₀ : Vec 2 → Vec 2 → E} {F₀ : Vec 2 → Vec 2 → Fin 2 → E}
    {V : ℕ → Vec 2 → Vec 2 → Fin 2 → E}
    (hf : IsBoxSmooth (sX + A) (sZ + 1) f₀) (hfp : ∀ X, AVenhance.IsZ2Periodic (f₀ X))
    (hfm : ∀ X, fieldCellMean (f₀ X) = 0)
    (hF : IsBoxSmooth (sX + A) (sZ + 1) F₀) (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0)
    (hV : IsCleanupChain sX sZ A f₀ F₀ V) (L : E →L[ℝ] ℂ) (X z : Vec 2) :
    L (cleanupSource V A X z) =
      cleanupSource (AVRegularity.CleanupChain.Vchain (sZ + 1) (fun X z => L (f₀ X z))
        (fun X z k => L (F₀ X z k))) A X z := by
  have hFs : IsSlowSmooth sX F₀ := (hF.mono (Nat.le_add_right sX A) le_rfl).isSlowSmooth
  have hslow : IsSlowSmooth sX (V (A - 1)) :=
    IsCleanupChain.isSlowSmooth hFs hV (A - 1) (by omega)
  have h1 : cleanupSource (fun i X z k => L (V i X z k)) A =
      fun X z => L (cleanupSource V A X z) :=
    cleanupSource_clm_comp (V := V) (j := A) hsX hslow L
  have h2 : cleanupSource (fun i X z k => L (V i X z k)) A =
      cleanupSource (AVRegularity.CleanupChain.Vchain (sZ + 1) (fun X z => L (f₀ X z))
        (fun X z k => L (F₀ X z k))) A :=
    cleanupSource_congr (V := fun i X z k => L (V i X z k))
      (V' := AVRegularity.CleanupChain.Vchain (sZ + 1) (fun X z => L (f₀ X z))
        (fun X z k => L (F₀ X z k))) (j := A)
      (clm_cleanupChain_eq_Vchain hsX hsZ hf hfp hfm hF hFp hFm hV L (A - 1) (by omega))
  exact (congrFun (congrFun h1 X) z).symm.trans (congrFun (congrFun h2 X) z)

/-! ### Functionals of a cleanup chain with a time parameter -/

/-- **Every functional of a cleanup chain of time-measurable data is measurable in time.** -/
theorem isCleanupChain_time_measurable_clm {sX sZ A : ℕ} (hsX : 1 ≤ sX) (hsZ : 1 ≤ sZ)
    {a b : ℝ} (hab : a ≤ b)
    (f₀ : ℝ → Vec 2 → Vec 2 → E) (F₀ : ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (V : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (hf : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sX + A) (sZ + 1) (f₀ τ))
    (hfp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (f₀ τ X))
    (hfm : ∀ τ ∈ Set.Icc a b, ∀ X, fieldCellMean (f₀ τ X) = 0)
    (hF : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sX + A) (sZ + 1) (F₀ τ))
    (hFp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (F₀ τ X))
    (hFm : ∀ τ ∈ Set.Icc a b, ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ τ X z k) = 0)
    (L : E →L[ℝ] ℂ)
    (hfmeas : ∀ X z, Measurable (fun τ => L (f₀ (Set.projIcc a b hab τ) X z)))
    (hFmeas : ∀ X z k, Measurable (fun τ => L (F₀ (Set.projIcc a b hab τ) X z k)))
    (hV : ∀ τ ∈ Set.Icc a b, IsCleanupChain sX sZ A (f₀ τ) (F₀ τ) (fun j => V j τ)) :
    ∀ j, j < A → ∀ X z k, Measurable (fun τ => L (V j (Set.projIcc a b hab τ) X z k)) := by
  intro j hj X z k
  have hmem : ∀ τ : ℝ, (Set.projIcc a b hab τ : ℝ) ∈ Set.Icc a b := fun τ =>
    (Set.projIcc a b hab τ).2
  have hd := fun τ : ℝ => clm_data_facts (hf _ (hmem τ)) (hfp _ (hmem τ)) (hfm _ (hmem τ))
    (hF _ (hmem τ)) (hFp _ (hmem τ)) (hFm _ (hmem τ)) L
  have e : (fun τ => L (V j (Set.projIcc a b hab τ) X z k)) = fun τ =>
      AVRegularity.CleanupChain.Vchain (sZ + 1)
        (fun X z => L (f₀ (Set.projIcc a b hab τ) X z))
        (fun X z k => L (F₀ (Set.projIcc a b hab τ) X z k)) j X z k := by
    funext τ
    exact congrFun (congrFun (congrFun (clm_cleanupChain_eq_Vchain hsX hsZ (hf _ (hmem τ))
      (hfp _ (hmem τ)) (hfm _ (hmem τ)) (hF _ (hmem τ)) (hFp _ (hmem τ)) (hFm _ (hmem τ))
      (hV _ (hmem τ)) L j hj) X) z) k
  rw [e]
  exact AVRegularity.CleanupChain.measurable_Vchain_param (N := sX + A) hsZ
    (f₀ := fun τ X z => L (f₀ (Set.projIcc a b hab τ) X z))
    (F₀ := fun τ X z k => L (F₀ (Set.projIcc a b hab τ) X z k))
    (fun τ => (hd τ).1) (fun τ => (hd τ).2.1) (fun τ => (hd τ).2.2.1)
    (fun τ => (hd τ).2.2.2.1) (fun τ => (hd τ).2.2.2.2.1) (fun τ => (hd τ).2.2.2.2.2)
    hfmeas hFmeas j (by omega) X z k

/-- **Every functional of the last source of a cleanup chain of time-measurable data is
measurable in time.** -/
theorem cleanupSource_time_measurable_clm {sX sZ A : ℕ} (hsX : 1 ≤ sX) (hsZ : 1 ≤ sZ)
    (hA : 1 ≤ A) {a b : ℝ} (hab : a ≤ b)
    (f₀ : ℝ → Vec 2 → Vec 2 → E) (F₀ : ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (V : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (hf : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sX + A) (sZ + 1) (f₀ τ))
    (hfp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (f₀ τ X))
    (hfm : ∀ τ ∈ Set.Icc a b, ∀ X, fieldCellMean (f₀ τ X) = 0)
    (hF : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sX + A) (sZ + 1) (F₀ τ))
    (hFp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (F₀ τ X))
    (hFm : ∀ τ ∈ Set.Icc a b, ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ τ X z k) = 0)
    (L : E →L[ℝ] ℂ)
    (hfmeas : ∀ X z, Measurable (fun τ => L (f₀ (Set.projIcc a b hab τ) X z)))
    (hFmeas : ∀ X z k, Measurable (fun τ => L (F₀ (Set.projIcc a b hab τ) X z k)))
    (hV : ∀ τ ∈ Set.Icc a b, IsCleanupChain sX sZ A (f₀ τ) (F₀ τ) (fun j => V j τ)) :
    ∀ X z, Measurable
      (fun τ => L (cleanupSource (fun j => V j (Set.projIcc a b hab τ)) A X z)) := by
  intro X z
  have hmem : ∀ τ : ℝ, (Set.projIcc a b hab τ : ℝ) ∈ Set.Icc a b := fun τ =>
    (Set.projIcc a b hab τ).2
  have hd := fun τ : ℝ => clm_data_facts (hf _ (hmem τ)) (hfp _ (hmem τ)) (hfm _ (hmem τ))
    (hF _ (hmem τ)) (hFp _ (hmem τ)) (hFm _ (hmem τ)) L
  have e : (fun τ => L (cleanupSource (fun j => V j (Set.projIcc a b hab τ)) A X z)) =
      fun τ => cleanupSource (AVRegularity.CleanupChain.Vchain (sZ + 1)
        (fun X z => L (f₀ (Set.projIcc a b hab τ) X z))
        (fun X z k => L (F₀ (Set.projIcc a b hab τ) X z k))) A X z := by
    funext τ
    exact clm_cleanupSource_eq_Vchain hsX hsZ hA (hf _ (hmem τ)) (hfp _ (hmem τ))
      (hfm _ (hmem τ)) (hF _ (hmem τ)) (hFp _ (hmem τ)) (hFm _ (hmem τ)) (hV _ (hmem τ)) L X z
  rw [e]
  exact AVRegularity.CleanupChain.measurable_cleanupSource_Vchain_param (N := sX + A) hsZ
    (f₀ := fun τ X z => L (f₀ (Set.projIcc a b hab τ) X z))
    (F₀ := fun τ X z k => L (F₀ (Set.projIcc a b hab τ) X z k))
    (fun τ => (hd τ).1) (fun τ => (hd τ).2.1) (fun τ => (hd τ).2.2.1)
    (fun τ => (hd τ).2.2.2.1) (fun τ => (hd τ).2.2.2.2.1) (fun τ => (hd τ).2.2.2.2.2)
    hfmeas hFmeas hA (by omega) X z

end Complete

/-! ### Finite-dimensional values -/

/-- A map into a finite-dimensional real normed space with its Borel `σ`-algebra is measurable
if its images under all continuous real linear maps into `ℂ` are. -/
theorem measurable_of_all_complex_clm {T : Type*} [MeasurableSpace T] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (g : T → E) (hL : ∀ L : E →L[ℝ] ℂ, Measurable fun t => L (g t)) :
    Measurable g := by
  refine AVRegularity.CycleComparison.Lift.measurable_of_all_real_duals g fun l => ?_
  have e : (fun t => l (g t)) = fun t => ((Complex.ofRealCLM.comp l) (g t)).re := by
    funext t
    rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_re]
  rw [e]
  exact Complex.measurable_re.comp (hL (Complex.ofRealCLM.comp l))

section Finite

end Finite

/-! ### Values in a finite product -/

section Pi

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)]

/-- **A cleanup chain with values in a finite product is measurable in time, componentwise.**
The sup-normed product `∀ i, h i` carries the product `σ`-algebra, so the data and the chain
are measured component by component (compare `exists_isCleanupChain_pi`). -/
theorem isCleanupChain_time_measurable_pi {sX sZ A : ℕ} (hsX : 1 ≤ sX) (hsZ : 1 ≤ sZ)
    {a b : ℝ} (hab : a ≤ b)
    (f₀ : ℝ → Vec 2 → Vec 2 → ∀ i, h i) (F₀ : ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (V : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hf : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sX + A) (sZ + 1) (f₀ τ))
    (hfp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (f₀ τ X))
    (hfm : ∀ τ ∈ Set.Icc a b, ∀ X, fieldCellMean (f₀ τ X) = 0)
    (hF : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sX + A) (sZ + 1) (F₀ τ))
    (hFp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (F₀ τ X))
    (hFm : ∀ τ ∈ Set.Icc a b, ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ τ X z k) = 0)
    (hfmeas : ∀ X z i, Measurable (fun τ => f₀ (Set.projIcc a b hab τ) X z i))
    (hFmeas : ∀ X z k i, Measurable (fun τ => F₀ (Set.projIcc a b hab τ) X z k i))
    (hV : ∀ τ ∈ Set.Icc a b, IsCleanupChain sX sZ A (f₀ τ) (F₀ τ) (fun j => V j τ)) :
    ∀ j, j < A → ∀ X z k i, Measurable (fun τ => V j (Set.projIcc a b hab τ) X z k i) := by
  have : ∀ i, CompleteSpace (h i) := fun i => FiniteDimensional.complete ℝ (h i)
  intro j hj X z k i
  refine measurable_of_all_complex_clm _ fun L => ?_
  exact isCleanupChain_time_measurable_clm hsX hsZ hab f₀ F₀ V hf hfp hfm hF hFp hFm
    (L.comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) i))
    (fun X z => L.continuous.measurable.comp (hfmeas X z i))
    (fun X z k => L.continuous.measurable.comp (hFmeas X z k i)) hV j hj X z k

/-- **The last source of a cleanup chain with values in a finite product is measurable in
time, componentwise.** -/
theorem cleanupSource_time_measurable_pi {sX sZ A : ℕ} (hsX : 1 ≤ sX) (hsZ : 1 ≤ sZ)
    (hA : 1 ≤ A) {a b : ℝ} (hab : a ≤ b)
    (f₀ : ℝ → Vec 2 → Vec 2 → ∀ i, h i) (F₀ : ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (V : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hf : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sX + A) (sZ + 1) (f₀ τ))
    (hfp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (f₀ τ X))
    (hfm : ∀ τ ∈ Set.Icc a b, ∀ X, fieldCellMean (f₀ τ X) = 0)
    (hF : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sX + A) (sZ + 1) (F₀ τ))
    (hFp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (F₀ τ X))
    (hFm : ∀ τ ∈ Set.Icc a b, ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ τ X z k) = 0)
    (hfmeas : ∀ X z i, Measurable (fun τ => f₀ (Set.projIcc a b hab τ) X z i))
    (hFmeas : ∀ X z k i, Measurable (fun τ => F₀ (Set.projIcc a b hab τ) X z k i))
    (hV : ∀ τ ∈ Set.Icc a b, IsCleanupChain sX sZ A (f₀ τ) (F₀ τ) (fun j => V j τ)) :
    ∀ X z i, Measurable
      (fun τ => cleanupSource (fun j => V j (Set.projIcc a b hab τ)) A X z i) := by
  have : ∀ i, CompleteSpace (h i) := fun i => FiniteDimensional.complete ℝ (h i)
  intro X z i
  refine measurable_of_all_complex_clm _ fun L => ?_
  exact cleanupSource_time_measurable_clm hsX hsZ hA hab f₀ F₀ V hf hfp hfm hF hFp hFm
    (L.comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) i))
    (fun X z => L.continuous.measurable.comp (hfmeas X z i))
    (fun X z k => L.continuous.measurable.comp (hFmeas X z k i)) hV X z

end Pi

/-! ### Ordered derivatives of a jointly measurable family -/

section Ordered

end Ordered

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The weak identity of a limit of approximants.** Let `u_M` satisfy, on the unit cell, the
integrated weak identity from `t_A` to every time of `[t_A, t_Z]` against every smooth periodic
test, with data `(∇u_M, flux_M, F_M, g_M)`. If the values converge in `L²` of the cell at every
time, and the four data converge in `L²` of the cell at every time of `(t_A, t_Z]` with a bound of
the differences whose time integral tends to zero, to data bounded in `L²` by an integrable
function of time, then the limit satisfies the integrated weak identity against every first-order
test (`coupledWeakIdentity_limit`). No measurability in time of the limit data is assumed: the
tested right side of the limit is measurable as an `L¹`-dominated limit
(`aestronglyMeasurable_of_integral_bound_tendsto`). This is the passage from the finite-rank
approximants of the coarse field to the coarse field in the reconstruction.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Cell pairings converge when the first factors converge in `L²`. -/
theorem tendsto_integral_inner_of_L2 {μ : Measure (Vec 2)} {uM : ℕ → Vec 2 → H}
    {u φ : Vec 2 → H} (hu : MemLp u 2 μ) (hφ : MemLp φ 2 μ)
    (huM : ∀ M, MemLp (fun x => uM M x - u x) 2 μ)
    (hlim : Tendsto (fun M => (eLpNorm (fun x => uM M x - u x) 2 μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun M => ∫ x, inner ℝ (uM M x) (φ x) ∂μ) atTop (𝓝 (∫ x, inner ℝ (u x) (φ x) ∂μ)) := by
  have hM : ∀ M, MemLp (uM M) 2 μ := fun M => by
    have h := (huM M).add hu
    have he : (fun x => uM M x - u x) + u = uM M := by
      funext x
      simp
    rwa [he] at h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ M, ‖(∫ x, inner ℝ (uM M x) (φ x) ∂μ) - ∫ x, inner ℝ (u x) (φ x) ∂μ‖ ≤
      (eLpNorm (fun x => uM M x - u x) 2 μ).toReal * (eLpNorm φ 2 μ).toReal := by
    intro M
    rw [← integral_sub (Coarse.integrable_inner_memLp (hM M) hφ)
      (Coarse.integrable_inner_memLp hu hφ), Real.norm_eq_abs]
    have he : ∫ x, (inner ℝ (uM M x) (φ x) - inner ℝ (u x) (φ x)) ∂μ =
        ∫ x, inner ℝ (uM M x - u x) (φ x) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => (inner_sub_left _ _ _).symm)
    rw [he]
    exact Coarse.abs_integral_inner_le (huM M) hφ
  refine squeeze_zero (fun M => norm_nonneg _) hb ?_
  simpa using hlim.mul_const (eLpNorm φ 2 μ).toReal

variable [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]

/-- **The weak identity of a limit of approximants**, against every first-order test. -/
theorem coupledWeakIdentity_limit [FiniteDimensional ℝ H] {ν tA tZ : ℝ}
    (v : ℝ → Vec 2 → Vec 2) (Vb : ℝ)
    (hvm : ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      AEStronglyMeasurable (fun x => v s x k) (volume.restrict AVenhance.unitCube))
    (hv : ∀ s ∈ Set.Ioc tA tZ, ∀ x k, |v s x k| ≤ Vb)
    (u : ℝ → Vec 2 → H) (du : ℝ → Fin 2 → Vec 2 → H)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (hu : ∀ t ∈ Set.Icc tA tZ, MemLp (u t) 2 (volume.restrict AVenhance.unitCube))
    (C : ℝ → ℝ) (hC : IntegrableOn C (Set.Ioc tA tZ))
    (hdu : ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      MemLp (du s k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (du s k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hflux : ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      MemLp (fun x => flux s x k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => flux s x k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hF : ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      MemLp (fun x => F s x k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => F s x k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hg : ∀ s ∈ Set.Ioc tA tZ, MemLp (g s) 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (g s) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (uM : ℕ → ℝ → Vec 2 → H) (duM : ℕ → ℝ → Fin 2 → Vec 2 → H)
    (fluxM FM : ℕ → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (gM : ℕ → ℝ → Vec 2 → H)
    (huM : ∀ M, ∀ t ∈ Set.Icc tA tZ,
      MemLp (fun x => uM M t x - u t x) 2 (volume.restrict AVenhance.unitCube))
    (hulim : ∀ t ∈ Set.Icc tA tZ, Tendsto (fun M =>
      (eLpNorm (fun x => uM M t x - u t x) 2 (volume.restrict AVenhance.unitCube)).toReal)
      atTop (𝓝 0))
    (c : ℕ → ℝ → ℝ) (hc : ∀ M, IntegrableOn (c M) (Set.Ioc tA tZ))
    (hc0 : Tendsto (fun M => ∫ s in Set.Ioc tA tZ, c M s) atTop (𝓝 0))
    (hduM : ∀ M, ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      MemLp (fun x => duM M s k x - du s k x) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => duM M s k x - du s k x) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ c M s)
    (hfluxM : ∀ M, ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      MemLp (fun x => (fluxM M s x - flux s x) k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => (fluxM M s x - flux s x) k) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ c M s)
    (hFM : ∀ M, ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      MemLp (fun x => (FM M s x - F s x) k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => (FM M s x - F s x) k) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ c M s)
    (hgM : ∀ M, ∀ s ∈ Set.Ioc tA tZ,
      MemLp (fun x => gM M s x - g s x) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => gM M s x - g s x) 2
          (volume.restrict AVenhance.unitCube)).toReal ≤ c M s)
    (hid : ∀ M, ∀ t ∈ Set.Icc tA tZ, ∀ φ : Vec 2 → H, ContDiff ℝ (⊤ : ℕ∞) φ →
      AVenhance.IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν tA t v (uM M t) (uM M tA) φ
        (fun k x => fderiv ℝ φ x (basisVec k)) (duM M) (fluxM M) (FM M) (gM M)) :
    ∀ t ∈ Set.Icc tA tZ, ∀ φ : TorusHk 1 H,
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν tA t v (u t) (u tA)
        (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) du flux F g := by
  intro t ht
  have htA : tA ∈ Set.Icc tA tZ := ⟨le_rfl, ht.1.trans ht.2⟩
  have hsub : Set.Ioc tA t ⊆ Set.Ioc tA tZ := Set.Ioc_subset_Ioc_right ht.2
  refine coupledWeakIdentity_of_smooth ν tA t v Vb (fun s hs => hvm s (hsub hs))
    (fun s hs => hv s (hsub hs)) (u t) (u tA) (hu t ht) (hu tA htA) du flux F g C
    (hC.mono_set hsub) (fun s hs => hdu s (hsub hs)) (fun s hs => hflux s (hsub hs))
    (fun s hs => hF s (hsub hs)) (fun s hs => hg s (hsub hs)) (fun φ hφ hφp => ?_)
  -- the smooth test and its `L²` bounds
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hφL : MemLp φ 2 (volume.restrict AVenhance.unitCube) :=
    Coarse.memLp_two_cell_of_continuous hφ.continuous
  have hdφL : ∀ k : Fin 2, MemLp (fun x => fderiv ℝ φ x (basisVec k)) 2
      (volume.restrict AVenhance.unitCube) := fun k =>
    Coarse.memLp_two_cell_of_continuous (cell_continuous_partial hφ1 k)
  set Mφ : ℝ := (eLpNorm φ 2 (volume.restrict AVenhance.unitCube)).toReal +
    ∑ k : Fin 2, (eLpNorm (fun x => fderiv ℝ φ x (basisVec k)) 2
      (volume.restrict AVenhance.unitCube)).toReal with hMφ
  have hφb : (eLpNorm φ 2 (volume.restrict AVenhance.unitCube)).toReal ≤ Mφ :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => ENNReal.toReal_nonneg)
  have hdφb : ∀ k : Fin 2, (eLpNorm (fun x => fderiv ℝ φ x (basisVec k)) 2
      (volume.restrict AVenhance.unitCube)).toReal ≤ Mφ := fun k =>
    (Finset.single_le_sum (f := fun k : Fin 2 => (eLpNorm (fun x => fderiv ℝ φ x (basisVec k)) 2
      (volume.restrict AVenhance.unitCube)).toReal) (fun k _ => ENNReal.toReal_nonneg)
      (Finset.mem_univ k)).trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  set Kc : ℝ := 2 * Vb + 2 * |ν| + 5 with hKc
  -- the identities of the approximants at the time `t`
  have hMid := fun M => coupledWeakIdentity_iff.1 (hid M t ht φ hφ hφp)
  have hIM : ∀ M, ∀ s ∈ Set.Ioc tA t, Integrable
      (weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ (fun k x => fderiv ℝ φ x (basisVec k)) s)
      (volume.restrict AVenhance.unitCube) := fun M => (hMid M).2.2.1
  have hTM : ∀ M, IntegrableOn (fun s => ∫ x in AVenhance.unitCube,
      weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ (fun k x => fderiv ℝ φ x (basisVec k)) s x)
      (Set.Ioc tA t) := fun M => (hMid M).2.2.2.1
  -- the limit integrand at one time
  have hlimit := fun s (hs : s ∈ Set.Ioc tA t) =>
    weakRhs_integrable_and_bound (ν := ν) (hvm s (hsub hs)) (hv s (hsub hs)) (hdu s (hsub hs))
      (hflux s (hsub hs)) (hF s (hsub hs)) (hg s (hsub hs)) hφL hφb hdφL hdφb
  have hI : ∀ s ∈ Set.Ioc tA t, Integrable
      (weakRhs ν v du flux F g φ (fun k x => fderiv ℝ φ x (basisVec k)) s)
      (volume.restrict AVenhance.unitCube) := fun s hs => (hlimit s hs).1
  have hpt : ∀ M, ∀ s ∈ Set.Ioc tA t,
      |(∫ x in AVenhance.unitCube, weakRhs ν v (duM M) (fluxM M) (FM M) (gM M) φ
          (fun k x => fderiv ℝ φ x (basisVec k)) s x) -
        ∫ x in AVenhance.unitCube, weakRhs ν v du flux F g φ
          (fun k x => fderiv ℝ φ x (basisVec k)) s x| ≤ Kc * c M s * Mφ :=
    fun M s hs => abs_weakRhs_integral_sub_le (hvm s (hsub hs)) (hv s (hsub hs)) hφL hφb hdφL
      hdφb (hduM M s (hsub hs)) (hfluxM M s (hsub hs)) (hFM M s (hsub hs)) (hgM M s (hsub hs))
      (hIM M s hs) (hI s hs)
  -- the bounds of the differences on the shorter interval
  have hcnn : ∀ M, ∀ s ∈ Set.Ioc tA tZ, 0 ≤ c M s := fun M s hs =>
    ENNReal.toReal_nonneg.trans (hgM M s hs).2
  have hcs0 : Tendsto (fun M => ∫ s in Set.Ioc tA t, c M s) atTop (𝓝 0) := by
    refine squeeze_zero (fun M => setIntegral_nonneg measurableSet_Ioc fun s hs =>
      hcnn M s (hsub hs)) (fun M => ?_) hc0
    exact setIntegral_mono_set (hc M) ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun s hs => hcnn M s hs)) (Eventually.of_forall hsub)
  -- the tested right side of the limit is integrable in time
  have hT : IntegrableOn (fun s => ∫ x in AVenhance.unitCube, weakRhs ν v du flux F g φ
      (fun k x => fderiv ℝ φ x (basisVec k)) s x) (Set.Ioc tA t) := by
    have hmeas : AEStronglyMeasurable (fun s => ∫ x in AVenhance.unitCube,
        weakRhs ν v du flux F g φ (fun k x => fderiv ℝ φ x (basisVec k)) s x)
        (volume.restrict (Set.Ioc tA t)) := by
      refine aestronglyMeasurable_of_integral_bound_tendsto
        (r := fun M s => ∫ x in AVenhance.unitCube, weakRhs ν v (duM M) (fluxM M) (FM M) (gM M)
          φ (fun k x => fderiv ℝ φ x (basisVec k)) s x)
        (c := fun M s => Kc * c M s * Mφ) (fun M => (hTM M).aestronglyMeasurable)
        (fun M => (((hc M).mono_set hsub).const_mul Kc).mul_const Mφ) (fun M => ?_) ?_
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
        rw [Real.norm_eq_abs]
        exact hpt M s hs
      · have he : ∀ M, (∫ s in Set.Ioc tA t, Kc * c M s * Mφ) =
            Kc * Mφ * ∫ s in Set.Ioc tA t, c M s := fun M => by
          rw [← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun s => by ring)
        simp only [he]
        simpa using hcs0.const_mul (Kc * Mφ)
    refine Integrable.mono' (((hC.mono_set hsub).const_mul Kc).mul_const Mφ) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs]
    exact (hlimit s hs).2
  -- the limit
  refine coupledWeakIdentity_of_tendsto (fun M => hid M t ht φ hφ hφp)
    (Coarse.integrable_inner_memLp (hu t ht) hφL) (Coarse.integrable_inner_memLp (hu tA htA) hφL)
    hI hT (tendsto_integral_inner_of_L2 (hu t ht) hφL (fun M => huM M t ht) (hulim t ht))
    (tendsto_integral_inner_of_L2 (hu tA htA) hφL (fun M => huM M tA htA) (hulim tA htA)) ?_
  exact tendsto_weakRhs_integral (fun s hs => hvm s (hsub hs)) (fun s hs => hv s (hsub hs)) hφL
    hφb hdφL hdφb c (fun M => (hc M).mono_set hsub) hcs0 (fun M s hs => hduM M s (hsub hs))
    (fun M s hs => hfluxM M s (hsub hs)) (fun M s hs => hFM M s (hsub hs))
    (fun M s hs => hgM M s (hsub hs)) hIM hI hTM hT

end AVRegularity.CycleComparison.Reconstruction
end
end

section
/-! **The Galerkin cutoff commutes with the divergence of the coarse flux.** The finite-rank
approximant `a_n = ∑_r c_r e_r` of the coarse field (`coarseApprox`) has the time density
`∑_r ċ_r e_r`, where `ċ_r` is the coarse defect identity tested against the mode `e_r`. Its flux
part is `-∫_{cell} ∑_j ⟪(F_coarse)_j, ∂_j e_r⟫`; this file identifies the corresponding
finite-rank field with the classical divergence of the cutoff of the flux:

* (C1) `fluxApprox n Fc x j`: the smooth representative of the Galerkin cutoff `galerkinProj n`
  of the flux, component `j` (`fluxApprox_contDiff`, `fluxApprox_periodic`,
  `fluxApprox_isClassicalRep`);
* (C2) `coarseProj_div_eq`: `∑_r (-∫ ∑_j ⟪F_j, ∂_j e_r⟫) e_r = ∑_j ∂_j (S_n F)_j`;
* (C3) `coarseProj_classical_eq`: `∑_r (∫ ⟪g, e_r⟫) e_r` is the approximant of the torus carrier
  of a continuous periodic field `g`.

The modes are tensor products `e_r = m_f b_e` of a scalar real Fourier mode `m_f` with an
orthonormal fiber vector `b_e`, and `∂_j m_f = λ_{f,j} m_{σ f}` with the cosine/sine swap `σ` and
`λ_{σ f, j} = -λ_{f,j}` (`AVenhance.Infra.Classical.spaceGrad_realFourierModeAmbient`). Summing over
the fiber basis gives the basis-free coefficient `∫ m_f u` (`modeProj`), so the cutoff acts
componentwise on the flux (`modeProj_component`), and (C2) is the finite identity
`∑_f m_f(x) λ_{f,j} m_{σ f}(y) = -∑_f λ_{f,j} m_{σ f}(x) m_f(y)`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.Parabolic.FourierGalerkin (RealFourierDimension RealFourierIndex
  realFourierIndexEquivFin realFourierModeAmbient realFourierModeAmbient_contDiff)
open AVenhance.Infra.Classical (realFourierModeIndexSwap realFourierModeDerivativeScale
  realFourierModeDerivativeScale_swap realFourierModeIndexSwap_involutive
  spaceGrad_realFourierModeAmbient)

namespace AVRegularity.CycleComparison.Reconstruction

/-! ### Scalar real Fourier modes -/

/-- The scalar real Fourier mode `m_f` of the cutoff `n`. -/
def scalarMode (n : ℕ) (f : Fin (RealFourierDimension n)) : Vec 2 → ℝ :=
  realFourierModeAmbient n ((realFourierIndexEquivFin n).symm f)

/-- The frequency factor `λ_{f,j}` of `∂_j m_f = λ_{f,j} m_{σ f}`. -/
def modeScale (n : ℕ) (f : Fin (RealFourierDimension n)) (j : Fin 2) : ℝ :=
  realFourierModeDerivativeScale ((realFourierIndexEquivFin n).symm f) j

/-- The cosine/sine swap `σ` of the scalar modes. -/
def modeSwap (n : ℕ) : Fin (RealFourierDimension n) ≃ Fin (RealFourierDimension n) :=
  AVenhance.Infra.Classical.GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv n

theorem modeSwap_apply (n : ℕ) (f : Fin (RealFourierDimension n)) :
    modeSwap n f = realFourierIndexEquivFin n
      (realFourierModeIndexSwap ((realFourierIndexEquivFin n).symm f)) :=
  rfl

theorem modeSwap_swap (n : ℕ) (f : Fin (RealFourierDimension n)) :
    modeSwap n (modeSwap n f) = f := by
  rw [modeSwap_apply, modeSwap_apply, Equiv.symm_apply_apply,
    realFourierModeIndexSwap_involutive, Equiv.apply_symm_apply]

theorem modeScale_swap (n : ℕ) (f : Fin (RealFourierDimension n)) (j : Fin 2) :
    modeScale n (modeSwap n f) j = -modeScale n f j := by
  unfold modeScale
  rw [modeSwap_apply, Equiv.symm_apply_apply, realFourierModeDerivativeScale_swap]

theorem scalarMode_contDiff (n : ℕ) (f : Fin (RealFourierDimension n)) :
    ContDiff ℝ ⊤ (scalarMode n f) :=
  realFourierModeAmbient_contDiff n _

theorem scalarMode_differentiable (n : ℕ) (f : Fin (RealFourierDimension n)) :
    Differentiable ℝ (scalarMode n f) :=
  ((scalarMode_contDiff n f).of_le le_top : ContDiff ℝ 1 (scalarMode n f)).differentiable
    one_ne_zero

theorem scalarMode_continuous (n : ℕ) (f : Fin (RealFourierDimension n)) :
    Continuous (scalarMode n f) :=
  (scalarMode_contDiff n f).continuous

/-- A coordinate derivative of a real Fourier mode is its frequency factor times the swapped
mode. -/
theorem fderiv_realFourierModeAmbient (n : ℕ) (a : RealFourierIndex n) (j : Fin 2)
    (x : Vec 2) :
    fderiv ℝ (realFourierModeAmbient n a) x (basisVec j) =
      realFourierModeDerivativeScale a j *
        realFourierModeAmbient n (realFourierModeIndexSwap a) x := by
  have h := spaceGrad_realFourierModeAmbient n a j x
  change fderiv ℝ (realFourierModeAmbient n a) x (basisVec j) = _ at h
  rw [h]
  rcases a with _ | ⟨p, _ | _⟩ <;> simp [realFourierModeDerivativeScale]

/-- `∂_j m_f = λ_{f,j} m_{σ f}`. -/
theorem fderiv_scalarMode (n : ℕ) (f : Fin (RealFourierDimension n)) (x : Vec 2)
    (j : Fin 2) :
    fderiv ℝ (scalarMode n f) x (basisVec j) =
      modeScale n f j * scalarMode n (modeSwap n f) x := by
  have hs : scalarMode n (modeSwap n f) = realFourierModeAmbient n
      (realFourierModeIndexSwap ((realFourierIndexEquivFin n).symm f)) := by
    unfold scalarMode
    rw [modeSwap_apply, Equiv.symm_apply_apply]
  rw [hs]
  exact fderiv_realFourierModeAmbient n ((realFourierIndexEquivFin n).symm f) j x

/-! ### The coupled modes are tensor products -/

/-- The mode `e_r` in its own component is `m_{r.2.1} b_{r.2.2}`. -/
theorem coupledModeJet_self_fun {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (r : CoupledFourierModeIndex (h := h) n) :
    coupledModeJet n r r.1 0 Fin.elim0 =
      fun x => scalarMode n r.2.1 x • stdOrthonormalBasis ℝ (h r.1) r.2.2 := by
  simp only [coupledModeJet, dite_true]
  rfl

theorem coupledModeJet_self_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (r : CoupledFourierModeIndex (h := h) n) (x : Vec 2) :
    coupledModeJet n r r.1 0 Fin.elim0 x =
      scalarMode n r.2.1 x • stdOrthonormalBasis ℝ (h r.1) r.2.2 :=
  congrFun (coupledModeJet_self_fun n r) x

theorem coarseMode_mk_self {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (v : ι) (f : Fin (RealFourierDimension n))
    (e : Fin (Module.finrank ℝ (h v))) (x : Vec 2) :
    coarseMode n (⟨v, (f, e)⟩ : CoupledFourierModeIndex (h := h) n) x v =
      scalarMode n f x • stdOrthonormalBasis ℝ (h v) e :=
  coupledModeJet_self_eq n ⟨v, (f, e)⟩ x

/-- `∂_j e_r = λ_{f,j} m_{σ f} b_e`. -/
theorem fderiv_coupledModeJet_self {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (r : CoupledFourierModeIndex (h := h) n) (y : Vec 2)
    (j : Fin 2) :
    fderiv ℝ (coupledModeJet n r r.1 0 Fin.elim0) y (basisVec j) =
      (modeScale n r.2.1 j * scalarMode n (modeSwap n r.2.1) y) •
        stdOrthonormalBasis ℝ (h r.1) r.2.2 := by
  rw [coupledModeJet_self_fun, fderiv_smul_const (scalarMode_differentiable n r.2.1 y),
    ContinuousLinearMap.smulRight_apply, fderiv_scalarMode]

/-! ### The basis-free fiber coefficient -/

/-- The fiber-valued Fourier coefficient `∑_e (∫_{cell} m_f ⟪u, b_e⟫) b_e` (that is,
`∫_{cell} m_f u`) of a field `u`. -/
def modeProj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (f : Fin (RealFourierDimension n)) (u : Vec 2 → E) : E :=
  ∑ e : Fin (Module.finrank ℝ E),
    (∫ y in AVenhance.unitCube, scalarMode n f y * inner ℝ (u y) (stdOrthonormalBasis ℝ E e)) •
      stdOrthonormalBasis ℝ E e

theorem integrable_mode_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (f : Fin (RealFourierDimension n)) {u : Vec 2 → E}
    (hu : MemLp u 2 (volume.restrict AVenhance.unitCube)) (w : E) :
    Integrable (fun y => scalarMode n f y * inner ℝ (u y) w)
      (volume.restrict AVenhance.unitCube) :=
  (AVRegularity.CycleComparison.Coarse.integrable_inner_continuous hu
    ((scalarMode_continuous n f).fun_smul continuous_const)).congr
    (ae_of_all _ fun y => real_inner_smul_right (u y) w (scalarMode n f y))

/-- Pairing with `toLp (Pi.single j z)` reads the component `j`. -/
theorem inner_toLp_single {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : PiLp 2 (fun _ : Fin 2 => E)) (j : Fin 2) (z : E) :
    inner ℝ A (WithLp.toLp 2 (Pi.single j z : Fin 2 → E)) = inner ℝ (A j) z := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · show inner ℝ (A.ofLp j) ((Pi.single j z : Fin 2 → E) j) = _
    rw [Pi.single_eq_same]
  · intro i _ hi
    show inner ℝ (A.ofLp i) ((Pi.single j z : Fin 2 → E) i) = 0
    rw [Pi.single_eq_of_ne hi, inner_zero_right]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem piLp_sum_apply {α E : Type*} [NormedAddCommGroup E] (s : Finset α)
    (A : α → PiLp 2 (fun _ : Fin 2 => E)) (j : Fin 2) :
    (∑ a ∈ s, A a) j = ∑ a ∈ s, A a j := by
  simp only [WithLp.ofLp_sum, Finset.sum_apply]

theorem continuous_toLp_single {E : Type*} [NormedAddCommGroup E] (j : Fin 2)
    {g : Vec 2 → E} (hg : Continuous g) :
    Continuous (fun x => (WithLp.toLp 2 (Pi.single j (g x) : Fin 2 → E) :
      PiLp 2 (fun _ : Fin 2 => E))) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 2 => E)).comp
    ((continuous_single (A := fun _ : Fin 2 => E) j).comp hg)

/-- A component of a square-integrable flux pairs integrably with a continuous field. -/
theorem integrable_component_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}
    (hF : MemLp F 2 (volume.restrict AVenhance.unitCube)) (j : Fin 2) {g : Vec 2 → E}
    (hg : Continuous g) :
    Integrable (fun x => inner ℝ (F x j) (g x)) (volume.restrict AVenhance.unitCube) :=
  (AVRegularity.CycleComparison.Coarse.integrable_inner_continuous hF
    (continuous_toLp_single j hg)).congr
    (ae_of_all _ fun x => inner_toLp_single (F x) j (g x))

theorem integrable_mode_inner_component {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) (f : Fin (RealFourierDimension n))
    {F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}
    (hF : MemLp F 2 (volume.restrict AVenhance.unitCube)) (j : Fin 2) (w : E) :
    Integrable (fun y => scalarMode n f y * inner ℝ (F y j) w)
      (volume.restrict AVenhance.unitCube) :=
  (integrable_mode_inner n f hF (WithLp.toLp 2 (Pi.single j w : Fin 2 → E))).congr
    (ae_of_all _ fun y => by simp only [inner_toLp_single])

/-- **The fiber coefficient is basis free:** `⟪∑_e (∫ m_f ⟪u, b_e⟫) b_e, z⟫ = ∫ m_f ⟪u, z⟫`. -/
theorem modeProj_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (f : Fin (RealFourierDimension n)) {u : Vec 2 → E}
    (hu : ∀ w : E, Integrable (fun y => scalarMode n f y * inner ℝ (u y) w)
      (volume.restrict AVenhance.unitCube)) (z : E) :
    inner ℝ (modeProj n f u) z =
      ∫ y in AVenhance.unitCube, scalarMode n f y * inner ℝ (u y) z := by
  unfold modeProj
  rw [sum_inner]
  calc ∑ e : Fin (Module.finrank ℝ E), inner ℝ ((∫ y in AVenhance.unitCube,
          scalarMode n f y * inner ℝ (u y) (stdOrthonormalBasis ℝ E e)) •
          stdOrthonormalBasis ℝ E e) z
      = ∑ e : Fin (Module.finrank ℝ E), ∫ y in AVenhance.unitCube,
          scalarMode n f y * inner ℝ (u y) (stdOrthonormalBasis ℝ E e) *
            inner ℝ (stdOrthonormalBasis ℝ E e) z :=
        Finset.sum_congr rfl fun e _ => by rw [real_inner_smul_left, integral_mul_const]
    _ = ∫ y in AVenhance.unitCube, ∑ e : Fin (Module.finrank ℝ E),
          scalarMode n f y * inner ℝ (u y) (stdOrthonormalBasis ℝ E e) *
            inner ℝ (stdOrthonormalBasis ℝ E e) z :=
        (integral_finsetSum _ fun e _ => (hu (stdOrthonormalBasis ℝ E e)).mul_const
          (inner ℝ (stdOrthonormalBasis ℝ E e) z)).symm
    _ = ∫ y in AVenhance.unitCube, scalarMode n f y * inner ℝ (u y) z := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [mul_assoc]
        rw [← Finset.mul_sum, (stdOrthonormalBasis ℝ E).sum_inner_mul_inner]

/-- **The cutoff acts componentwise on a flux:** the component `j` of the fiber coefficient of
`F` is the fiber coefficient of `F_j`. -/
theorem modeProj_component {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (f : Fin (RealFourierDimension n))
    {F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}
    (hF : MemLp F 2 (volume.restrict AVenhance.unitCube)) (j : Fin 2) :
    (modeProj n f F) j = modeProj n f (fun y => F y j) := by
  refine ext_inner_right ℝ fun z => ?_
  rw [← inner_toLp_single (modeProj n f F) j z, modeProj_inner n f (integrable_mode_inner n f hF),
    modeProj_inner n f (integrable_mode_inner_component n f hF j)]
  exact integral_congr_ae (ae_of_all _ fun y => by simp only [inner_toLp_single])

/-! ### Synthesis over the coupled modes -/

/-- A finite combination of the coupled modes, read in the component `v`, is
`∑_f m_f(x) ∑_e c_{v,f,e} b_e`. -/
theorem sum_smul_coarseMode_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (c : CoupledFourierModeIndex (h := h) n → ℝ)
    (x : Vec 2) (v : ι) :
    (∑ r : CoupledFourierModeIndex (h := h) n, c r • coarseMode n r x) v =
      ∑ f : Fin (RealFourierDimension n), scalarMode n f x •
        ∑ e : Fin (Module.finrank ℝ (h v)), c ⟨v, (f, e)⟩ • stdOrthonormalBasis ℝ (h v) e := by
  rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single v]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Pi.smul_apply, coarseMode_mk_self, smul_comm]
  · intro i _ hi
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [Pi.smul_apply, coarseMode_eq_single,
      Pi.single_eq_of_ne (show v ≠ (⟨i, p⟩ : CoupledFourierModeIndex (h := h) n).1 from
        Ne.symm hi), smul_zero]
  · intro hv
    exact absurd (Finset.mem_univ v) hv

theorem coarseModeCoeff_mk {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i)) (v : ι)
    (f : Fin (RealFourierDimension n)) (e : Fin (Module.finrank ℝ (h v))) :
    coarseModeCoeff n U ⟨v, (f, e)⟩ = ∫ y in AVenhance.unitCube,
      scalarMode n f y * inner ℝ ((U v).toFunction.jet (valueIndex2 K) y)
        (stdOrthonormalBasis ℝ (h v) e) := by
  unfold coarseModeCoeff
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show inner ℝ ((U v).toFunction.jet (valueIndex2 K) y)
      (coarseMode n (⟨v, (f, e)⟩ : CoupledFourierModeIndex (h := h) n) y v) =
    scalarMode n f y * inner ℝ ((U v).toFunction.jet (valueIndex2 K) y)
      (stdOrthonormalBasis ℝ (h v) e)
  rw [coarseMode_mk_self, real_inner_smul_right]

/-- **Basis-free form of the approximant:** `a_n(x)_v = ∑_f m_f(x) ∫_{cell} m_f U_v`. -/
theorem coarseApprox_apply_eq_modeProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i)) (x : Vec 2)
    (v : ι) :
    coarseApprox n U x v = ∑ f : Fin (RealFourierDimension n),
      scalarMode n f x • modeProj n f ((U v).toFunction.jet (valueIndex2 K)) := by
  unfold coarseApprox
  rw [sum_smul_coarseMode_apply n (coarseModeCoeff n U) x v]
  refine Finset.sum_congr rfl fun f _ => congrArg (scalarMode n f x • ·) ?_
  unfold modeProj
  exact Finset.sum_congr rfl fun e _ =>
    congrArg (· • stdOrthonormalBasis ℝ (h v) e) (coarseModeCoeff_mk n U v f e)

theorem coarseApprox_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i)) :
    ContDiff ℝ (⊤ : ℕ∞) (coarseApprox n U) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x =>
    ∑ r : CoupledFourierModeIndex (h := h) n, coarseModeCoeff n U r • coarseMode n r x)
  exact ContDiff.sum fun r _ => (coarseMode_contDiff n r).const_smul _

theorem coarseApprox_periodic {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {K : ℕ} (U : ∀ i, TorusHk K (h i)) :
    AVenhance.IsZ2Periodic (coarseApprox n U) := fun z x => by
  unfold coarseApprox
  exact Finset.sum_congr rfl fun r _ => by rw [coarseMode_periodic n r z x]

/-! ### (C1) The flux approximant -/

/-- The smooth representative of the Galerkin cutoff `galerkinProj n` of the flux `Fc`,
component `j`. -/
def fluxApprox {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (x : Vec 2) (j : Fin 2) :
    ∀ i, h i :=
  fun v => WithLp.ofLp (coarseApprox (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n Fc x v) j

theorem fluxApprox_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fluxApprox n Fc x j) := by
  have hA := coarseApprox_contDiff (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n Fc
  refine contDiff_pi.2 fun v => ?_
  exact (contDiff_piLp 2).1 (contDiff_pi.1 hA v) j

theorem fluxApprox_periodic {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (j : Fin 2) :
    AVenhance.IsZ2Periodic (fun x => fluxApprox n Fc x j) := fun z x =>
  funext fun v => congrArg (fun A : (∀ i, PiLp 2 (fun _ : Fin 2 => h i)) => WithLp.ofLp (A v) j)
    (coarseApprox_periodic (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n Fc z x)

/-- **(C1)** The flux approximant is a classical representative of the Galerkin cutoff of the
flux at every order `r ≤ k`. -/
theorem fluxApprox_isClassicalRep {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) {r : ℕ} (hr : r ≤ k) :
    IsClassicalRep (galerkinProj n (Fc v))
      (fun x => WithLp.toLp 2 (fun j => fluxApprox n Fc x j v)) r := by
  have he : (fun x => (WithLp.toLp 2 (fun j => fluxApprox n Fc x j v) :
      PiLp 2 (fun _ : Fin 2 => h v))) =
      fun x => coarseApprox (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n Fc x v :=
    funext fun x => rfl
  rw [he]
  exact coarseApprox_isClassicalRep (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n Fc v hr

/-- The flux approximant is `∑_f m_f(x) ∫_{cell} m_f (Fc_v)_j`. -/
theorem fluxApprox_eq_modeProj {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (y : Vec 2) (j : Fin 2) (v : ι) :
    fluxApprox n Fc y j v = ∑ f : Fin (RealFourierDimension n), scalarMode n f y •
      modeProj n f (fun y' => (Fc v).toFunction.jet (valueIndex2 k) y' j) := by
  have hF := (Fc v).toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 k)
  have hA := coarseApprox_apply_eq_modeProj (h := fun v => PiLp 2 (fun _ : Fin 2 => h v))
    n Fc y v
  calc fluxApprox n Fc y j v
      = (coarseApprox (h := fun v => PiLp 2 (fun _ : Fin 2 => h v)) n Fc y v :
          PiLp 2 (fun _ : Fin 2 => h v)) j := rfl
    _ = (∑ f : Fin (RealFourierDimension n), scalarMode n f y •
          modeProj n f ((Fc v).toFunction.jet (valueIndex2 k)) :
          PiLp 2 (fun _ : Fin 2 => h v)) j :=
        congrArg (fun A : PiLp 2 (fun _ : Fin 2 => h v) => A j) hA
    _ = ∑ f : Fin (RealFourierDimension n), (scalarMode n f y •
          modeProj n f ((Fc v).toFunction.jet (valueIndex2 k)) :
          PiLp 2 (fun _ : Fin 2 => h v)) j :=
        piLp_sum_apply _ _ j
    _ = ∑ f : Fin (RealFourierDimension n), scalarMode n f y •
          modeProj n f (fun y' => (Fc v).toFunction.jet (valueIndex2 k) y' j) :=
        Finset.sum_congr rfl fun f _ =>
          congrArg (scalarMode n f y • ·) (modeProj_component n f hF j)

theorem fderiv_sum_smul_const {α E : Type*} [Fintype α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : α → Vec 2 → ℝ) (hs : ∀ a, Differentiable ℝ (s a)) (c : α → E)
    (x d : Vec 2) :
    fderiv ℝ (fun y => ∑ a, s a y • c a) x d = ∑ a, fderiv ℝ (s a) x d • c a := by
  rw [fderiv_fun_sum (A := fun a y => s a y • c a) fun a _ => (hs a x).smul_const (c a),
    _root_.sum_apply]
  exact Finset.sum_congr rfl fun a _ => by
    rw [fderiv_smul_const (hs a x), ContinuousLinearMap.smulRight_apply]

/-- `∂_j (S_n F)_j(x) = ∑_f λ_{f,j} m_{σ f}(x) ∫ m_f F_j`. -/
theorem fderiv_fluxApprox {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (x : Vec 2) (j : Fin 2) (v : ι) :
    fderiv ℝ (fun y => fluxApprox n Fc y j v) x (basisVec j) =
      ∑ f : Fin (RealFourierDimension n), (modeScale n f j * scalarMode n (modeSwap n f) x) •
        modeProj n f (fun y => (Fc v).toFunction.jet (valueIndex2 k) y j) := by
  have hfun : (fun y => fluxApprox n Fc y j v) = fun y =>
      ∑ f : Fin (RealFourierDimension n), scalarMode n f y •
        modeProj n f (fun y' => (Fc v).toFunction.jet (valueIndex2 k) y' j) :=
    funext fun y => fluxApprox_eq_modeProj n Fc y j v
  rw [hfun, fderiv_sum_smul_const (scalarMode n) (scalarMode_differentiable n)]
  exact Finset.sum_congr rfl fun f _ => by rw [fderiv_scalarMode]

/-! ### (C2) The cutoff of a divergence is the divergence of the cutoff -/

/-- The tested flux coefficient of a mode, in terms of the swapped mode. -/
theorem coarseDivCoeff_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (r : CoupledFourierModeIndex (h := h) n) :
    (∫ y in AVenhance.unitCube, ∑ j : Fin 2,
        inner ℝ ((Fc r.1).toFunction.jet (valueIndex2 k) y j)
          (fderiv ℝ (coupledModeJet n r r.1 0 Fin.elim0) y (basisVec j))) =
      ∑ j : Fin 2, modeScale n r.2.1 j * ∫ y in AVenhance.unitCube,
        scalarMode n (modeSwap n r.2.1) y *
          inner ℝ ((Fc r.1).toFunction.jet (valueIndex2 k) y j)
            (stdOrthonormalBasis ℝ (h r.1) r.2.2) := by
  have hF := (Fc r.1).toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 k)
  have hpt : ∀ y, ∑ j : Fin 2, inner ℝ ((Fc r.1).toFunction.jet (valueIndex2 k) y j)
      (fderiv ℝ (coupledModeJet n r r.1 0 Fin.elim0) y (basisVec j)) =
      ∑ j : Fin 2, modeScale n r.2.1 j * (scalarMode n (modeSwap n r.2.1) y *
        inner ℝ ((Fc r.1).toFunction.jet (valueIndex2 k) y j)
          (stdOrthonormalBasis ℝ (h r.1) r.2.2)) := fun y =>
    Finset.sum_congr rfl fun j _ => by
      rw [fderiv_coupledModeJet_self, real_inner_smul_right, mul_assoc]
  have hint : ∀ j : Fin 2, Integrable (fun y => modeScale n r.2.1 j *
      (scalarMode n (modeSwap n r.2.1) y *
        inner ℝ ((Fc r.1).toFunction.jet (valueIndex2 k) y j)
          (stdOrthonormalBasis ℝ (h r.1) r.2.2))) (volume.restrict AVenhance.unitCube) :=
    fun j => (integrable_mode_inner_component n (modeSwap n r.2.1) hF j _).const_mul _
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun j _ => hint j]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

theorem neg_sum_smul_comm {α β E : Type*} [Fintype α] [Fintype β] [AddCommGroup E]
    [Module ℝ E] (l : β → ℝ) (a : β → α → ℝ) (b : α → E) :
    ∑ e, (-(∑ j, l j * a j e)) • b e = -(∑ j, l j • ∑ e, a j e • b e) := by
  simp only [neg_smul, Finset.sum_neg_distrib, Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]

/-- The fiber sum of the tested flux coefficients of the modes `(v, f, ·)`. -/
theorem coarseDiv_fiber {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι)
    (f : Fin (RealFourierDimension n)) :
    ∑ e : Fin (Module.finrank ℝ (h v)),
        (-(∫ y in AVenhance.unitCube, ∑ j : Fin 2,
          inner ℝ ((Fc v).toFunction.jet (valueIndex2 k) y j)
            (fderiv ℝ (coupledModeJet n (⟨v, (f, e)⟩ : CoupledFourierModeIndex (h := h) n) v 0
              Fin.elim0) y (basisVec j)))) • stdOrthonormalBasis ℝ (h v) e =
      -(∑ j : Fin 2, modeScale n f j •
        modeProj n (modeSwap n f) (fun y => (Fc v).toFunction.jet (valueIndex2 k) y j)) := by
  calc _ = ∑ e : Fin (Module.finrank ℝ (h v)), (-(∑ j : Fin 2, modeScale n f j *
          ∫ y in AVenhance.unitCube, scalarMode n (modeSwap n f) y *
            inner ℝ ((Fc v).toFunction.jet (valueIndex2 k) y j)
              (stdOrthonormalBasis ℝ (h v) e))) • stdOrthonormalBasis ℝ (h v) e :=
        Finset.sum_congr rfl fun e _ =>
          congrArg (fun t : ℝ => (-t) • stdOrthonormalBasis ℝ (h v) e)
            (coarseDivCoeff_eq n Fc ⟨v, (f, e)⟩)
    _ = -(∑ j : Fin 2, modeScale n f j •
          modeProj n (modeSwap n f) (fun y => (Fc v).toFunction.jet (valueIndex2 k) y j)) :=
        neg_sum_smul_comm (modeScale n f)
          (fun j e => ∫ y in AVenhance.unitCube, scalarMode n (modeSwap n f) y *
            inner ℝ ((Fc v).toFunction.jet (valueIndex2 k) y j) (stdOrthonormalBasis ℝ (h v) e))
          (fun e => stdOrthonormalBasis ℝ (h v) e)

theorem sum_smul_neg_sum_eq {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E]
    (s : α → ℝ) (l : α → Fin 2 → ℝ) (Q : α → Fin 2 → E) :
    ∑ f, s f • -(∑ j : Fin 2, l f j • Q f j) = ∑ j : Fin 2, ∑ f, (-(l f j) * s f) • Q f j := by
  calc ∑ f, s f • -(∑ j : Fin 2, l f j • Q f j)
      = ∑ f, ∑ j : Fin 2, (-(l f j) * s f) • Q f j := Finset.sum_congr rfl fun f _ => by
        rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, neg_mul, neg_smul, mul_comm]
    _ = ∑ j : Fin 2, ∑ f, (-(l f j) * s f) • Q f j := Finset.sum_comm

/-- Reindexing by the swap: `∑_f λ_{f,j} m_{σ f}(x) G_f = -∑_f λ_{f,j} m_f(x) G_{σ f}`. -/
theorem sum_swap_reindex {E : Type*} [AddCommGroup E] [Module ℝ E] (n : ℕ) (j : Fin 2)
    (G : Fin (RealFourierDimension n) → E) (x : Vec 2) :
    ∑ f, (modeScale n f j * scalarMode n (modeSwap n f) x) • G f =
      ∑ f, (-(modeScale n f j) * scalarMode n f x) • G (modeSwap n f) := by
  calc ∑ f, (modeScale n f j * scalarMode n (modeSwap n f) x) • G f
      = ∑ f, (modeScale n (modeSwap n f) j * scalarMode n (modeSwap n (modeSwap n f)) x) •
          G (modeSwap n f) :=
        (Equiv.sum_comp (modeSwap n)
          (fun f => (modeScale n f j * scalarMode n (modeSwap n f) x) • G f)).symm
    _ = ∑ f, (-(modeScale n f j) * scalarMode n f x) • G (modeSwap n f) :=
        Finset.sum_congr rfl fun f _ => by rw [modeSwap_swap, modeScale_swap]

/-- **(C2), one component.** -/
theorem coarseProj_div_eq_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (x : Vec 2) (v : ι) :
    (∑ r : CoupledFourierModeIndex (h := h) n,
        (-(∫ y in AVenhance.unitCube, ∑ j : Fin 2,
          inner ℝ ((Fc r.1).toFunction.jet (valueIndex2 k) y j)
            (fderiv ℝ (coupledModeJet n r r.1 0 Fin.elim0) y (basisVec j)))) •
          coarseMode n r x) v =
      ∑ j : Fin 2, fderiv ℝ (fun y => fluxApprox n Fc y j v) x (basisVec j) := by
  rw [sum_smul_coarseMode_apply]
  calc _ = ∑ f : Fin (RealFourierDimension n), scalarMode n f x •
          -(∑ j : Fin 2, modeScale n f j •
            modeProj n (modeSwap n f) (fun y => (Fc v).toFunction.jet (valueIndex2 k) y j)) :=
        Finset.sum_congr rfl fun f _ => congrArg (scalarMode n f x • ·) (coarseDiv_fiber n Fc v f)
    _ = ∑ j : Fin 2, ∑ f : Fin (RealFourierDimension n),
          (-(modeScale n f j) * scalarMode n f x) •
            modeProj n (modeSwap n f) (fun y => (Fc v).toFunction.jet (valueIndex2 k) y j) :=
        sum_smul_neg_sum_eq (fun f => scalarMode n f x) (modeScale n)
          (fun f j => modeProj n (modeSwap n f)
            (fun y => (Fc v).toFunction.jet (valueIndex2 k) y j))
    _ = ∑ j : Fin 2, ∑ f : Fin (RealFourierDimension n),
          (modeScale n f j * scalarMode n (modeSwap n f) x) •
            modeProj n f (fun y => (Fc v).toFunction.jet (valueIndex2 k) y j) :=
        Finset.sum_congr rfl fun j _ => (sum_swap_reindex n j
          (fun f => modeProj n f (fun y => (Fc v).toFunction.jet (valueIndex2 k) y j)) x).symm
    _ = ∑ j : Fin 2, fderiv ℝ (fun y => fluxApprox n Fc y j v) x (basisVec j) :=
        Finset.sum_congr rfl fun j _ => (fderiv_fluxApprox n Fc x j v).symm

/-- **(C2) The projection of a divergence is the divergence of the projection:**
`∑_r (-∫_{cell} ∑_j ⟪(Fc_{r.1})_j, ∂_j e_r⟫) e_r(x) = ∑_j ∂_j (S_n Fc)_j(x)`. -/
theorem coarseProj_div_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (x : Vec 2) :
    ∑ r : CoupledFourierModeIndex (h := h) n,
        (-(∫ y in AVenhance.unitCube, ∑ j : Fin 2,
          inner ℝ ((Fc r.1).toFunction.jet (valueIndex2 k) y j)
            (fderiv ℝ (coupledModeJet n r r.1 0 Fin.elim0) y (basisVec j)))) •
          coarseMode n r x =
      fun v => ∑ j : Fin 2, fderiv ℝ (fun y => fluxApprox n Fc y j v) x (basisVec j) :=
  funext fun v => coarseProj_div_eq_apply n Fc x v

/-! ### (C3) The projection of a classical field -/

theorem contDiff_zero_natCast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → E} (hf : Continuous f) : ContDiff ℝ ((0 : ℕ) : ℕ∞) f := by
  exact_mod_cast contDiff_zero.2 hf

/-- The value jet of the carrier of a `C^K` periodic field is a.e. the field. -/
theorem periodicHk_value_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (K : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    (periodicHk K f hf hp).toFunction.jet (valueIndex2 K)
      =ᵐ[volume.restrict AVenhance.unitCube] f :=
  (periodicJetRepresentative_ae (periodicHk K f hf hp).val (valueIndex2 K)).trans
    ((periodicHk_jet_ae K f hf hp (valueIndex2 K)).trans
      (Filter.EventuallyEq.of_eq (AVRegularity.orderedDerivative_zero f _)))

/-- **(C3) The projection of a classical field:** for continuous periodic `g`,
`∑_r (∫_{cell} ⟪g_{r.1}, e_r⟫) e_r` is the approximant of the torus carrier of `g`. -/
theorem coarseProj_classical_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (n : ℕ) (g : ∀ v, Vec 2 → h v) (hg : ∀ v, Continuous (g v))
    (hgp : ∀ v, AVenhance.IsZ2Periodic (g v)) (x : Vec 2) :
    ∑ r : CoupledFourierModeIndex (h := h) n,
        (∫ y in AVenhance.unitCube, inner ℝ (g r.1 y) (coupledModeJet n r r.1 0 Fin.elim0 y)) •
          coarseMode n r x =
      coarseApprox n (fun v => periodicHk 0 (g v) (contDiff_zero_natCast (hg v)) (hgp v)) x := by
  unfold coarseApprox
  refine Finset.sum_congr rfl fun r _ => congrArg (· • coarseMode n r x) ?_
  unfold coarseModeCoeff
  refine integral_congr_ae ?_
  filter_upwards [periodicHk_value_ae 0 (g r.1) (contDiff_zero_natCast (hg r.1)) (hgp r.1)]
    with y hy
  exact congrArg (fun z => inner ℝ z (coupledModeJet n r r.1 0 Fin.elim0 y)) hy.symm

end AVRegularity.CycleComparison.Reconstruction
end
end
