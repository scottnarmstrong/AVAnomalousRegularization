-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.Commutation.TorusBridge
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Analysis.Convolution

/-! Weak derivative commutation for plane convolution averages. -/

theorem hasWeakPartialDerivOn_translate_univ {i : Fin 2} {u g : Vec 2 → ℝ}
    (h : HasWeakPartialDerivOn Set.univ i u g) (z : Vec 2) :
    HasWeakPartialDerivOn Set.univ i (fun x => u (x - z)) (fun x => g (x - z)) := by
  intro φ hφ hc _
  let ψ : Vec 2 → ℝ := fun x => φ (x + z)
  have hs : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcomp : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.addRight z)
  have hw := h ψ hs hcomp (Set.subset_univ _)
  simp only [setIntegral_univ] at hw ⊢
  have hd (x : Vec 2) : fderiv ℝ ψ x = fderiv ℝ φ (x + z) :=
    fderiv_comp_add_right z
  calc
    (∫ x, u (x - z) * (fderiv ℝ φ x) (basisVec i)) =
        ∫ x, u x * (fderiv ℝ φ (x + z)) (basisVec i) := by
      have ht := integral_add_right_eq_self (μ := volume)
        (fun x : Vec 2 => u (x - z) * (fderiv ℝ φ x) (basisVec i)) z
      simpa only [add_sub_cancel_right] using ht.symm
    _ = -(∫ x, g x * ψ x) := by simpa only [hd] using hw
    _ = -(∫ x, g (x - z) * φ x) := by
      congr 1
      have ht := integral_add_right_eq_self (μ := volume)
        (fun x : Vec 2 => g (x - z) * φ x) z
      simpa only [ψ, add_sub_cancel_right] using ht

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
theorem translation_hasWeakPartialDeriv {i : Fin 2}
    {f g : Lp E 2 (volume : Measure (Vec 2))}
    (h : ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (f x)) (fun x => inner ℝ e (g x))) (z : Vec 2) :
    ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (translation z f x))
      (fun x => inner ℝ e (translation z g x)) := by
  intro e
  apply hasWeakPartialDerivOn_congr_ae _ _ (hasWeakPartialDerivOn_translate_univ (h e) z)
  · rw [Measure.restrict_univ]
    filter_upwards [translation_ae z f] with x hx
    rw [hx]
  · rw [Measure.restrict_univ]
    filter_upwards [translation_ae z g] with x hx
    rw [hx]

omit [CompleteSpace E] in
theorem inner_scalar_test_eq {f t : Lp E 2 (volume : Measure (Vec 2))}
    {φ : Vec 2 → ℝ} {e : E} (ht : t =ᵐ[volume] fun x => φ x • e) :
    inner ℝ t f = ∫ x, inner ℝ e (f x) * φ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  rw [hx, real_inner_smul_left, mul_comm]

theorem averagingOperator_hasWeakPartialDeriv {i : Fin 2}
    {f g : Lp E 2 (volume : Measure (Vec 2))}
    (h : ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (f x)) (fun x => inner ℝ e (g x)))
    (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) :
    ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (averagingOperator ρ hρ κ hκ f x))
      (fun x => inner ℝ e (averagingOperator ρ hρ κ hκ g x)) := by
  intro e φ hs hc _
  simp only [setIntegral_univ]
  have hφ : MemLp (fun x => φ x • e) 2 volume :=
    (hs.continuous.smul continuous_const).memLp_of_hasCompactSupport
      (hc.smul_right (f' := fun _ : Vec 2 => e))
  have hderivcont : Continuous fun x => (fderiv ℝ φ x) (basisVec i) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderivcomp : HasCompactSupport fun x => (fderiv ℝ φ x) (basisVec i) :=
    hc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hdφ : MemLp (fun x => (fderiv ℝ φ x) (basisVec i) • e) 2 volume :=
    (hderivcont.smul continuous_const).memLp_of_hasCompactSupport
      (hderivcomp.smul_right (f' := fun _ : Vec 2 => e))
  let t : Lp E 2 volume := hφ.toLp (fun x => φ x • e)
  let dt : Lp E 2 volume := hdφ.toLp (fun x => (fderiv ℝ φ x) (basisVec i) • e)
  have ht : t =ᵐ[volume] fun x => φ x • e := hφ.coeFn_toLp
  have hdt : dt =ᵐ[volume] fun x => (fderiv ℝ φ x) (basisVec i) • e := hdφ.coeFn_toLp
  have htranslated (z : Vec 2) :
      inner ℝ dt (translation (ρ z) f) = -inner ℝ t (translation (ρ z) g) := by
    rw [inner_scalar_test_eq hdt, inner_scalar_test_eq ht]
    exact (by simpa only [setIntegral_univ] using
      translation_hasWeakPartialDeriv h (ρ z) e φ hs hc (Set.subset_univ _))
  rw [← inner_scalar_test_eq hdt, ← inner_scalar_test_eq ht]
  change inner ℝ dt (average ρ κ f) = -inner ℝ t (average ρ κ g)
  unfold average
  rw [← integral_inner (integrable_average_integrand ρ hρ hκ f),
    ← integral_inner (integrable_average_integrand ρ hρ hκ g), ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change inner ℝ dt (κ z • translation (ρ z) f) =
      -inner ℝ t (κ z • translation (ρ z) g)
    rw [real_inner_smul_right, real_inner_smul_right, htranslated, mul_neg]

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.Analysis.Convolution

/-! Weak derivative commutation for normalized torus averages. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem torus_pullback_periodic (f : Lp E 2 torusMeasure) :
    AVenhance.IsZ2Periodic (fun x => f (torusQuotient x)) := by
  intro n x
  change f (torusQuotient (x + AVenhance.latticeShift n)) = f (torusQuotient x)
  rw [map_add, torusQuotient_latticeShift, add_zero]

omit [MeasurableSpace E] [BorelSpace E] in
theorem torus_global_pairing_eq_cell (f : Lp E 2 torusMeasure) (e : E)
    {ψ : Vec 2 → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    (∫ x, inner ℝ e (f (torusQuotient x)) * ψ x) =
      ∫ x in AVenhance.unitCube,
        inner ℝ e (f (torusQuotient x)) * compactTestPeriodization ψ x := by
  have hm := (Lp.memLp f).comp_measurePreserving measurePreserving_torusQuotient_cell
  have hs := (InnerProductSpace.toDual ℝ E e).comp_memLp' hm
  have hp : AVenhance.IsZ2Periodic (fun x => inner ℝ e (f (torusQuotient x))) := by
    intro n x
    exact congrArg (inner ℝ e) (torus_pullback_periodic f n x)
  have h := (WeakGradientPeriodization.integral_periodic_mul_compact_eq_cell_periodization
    hs hp hψ hc).2
  rwa [setIntegral_congr_set WeakGradientPeriodization.periodCell_ae_unitCube] at h

omit [BorelSpace E] [CompleteSpace E] in
theorem torus_inner_cellTest_eq (f : Lp E 2 torusMeasure) (ψ : Vec 2 → ℝ)
    (hψ : MemLp ψ 2 (volume.restrict AVenhance.unitCube)) (e : E) :
    inner ℝ (cellToTorus (cellTestVectorL2 ψ hψ e)) f =
      ∫ x in AVenhance.unitCube, inner ℝ e (f (torusQuotient x)) * ψ x := by
  have hi := (torusToCell (E := E)).inner_map_map
    (cellToTorus (cellTestVectorL2 ψ hψ e)) f
  rw [torusToCell_cellToTorus] at hi
  rw [← hi, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cellTestVectorL2_ae ψ hψ e, torusToCell_ae f] with x hx hfx
  rw [hx, hfx, real_inner_smul_left, mul_comm]

omit [BorelSpace E] in
theorem torus_inner_periodizedTest_eq (f : Lp E 2 torusMeasure)
    (φ : WeakTest (Set.univ : Set (Vec 2))) (e : E) :
    inner ℝ (cellToTorus (periodizedTestVectorL2 φ e)) f =
      ∫ x, inner ℝ e (f (torusQuotient x)) * φ.toFun x := by
  rw [periodizedTestVectorL2, torus_inner_cellTest_eq]
  exact (torus_global_pairing_eq_cell f e φ.smooth.continuous φ.compact).symm

omit [BorelSpace E] in
theorem torus_inner_periodizedPartialTest_eq (f : Lp E 2 torusMeasure)
    (φ : WeakTest (Set.univ : Set (Vec 2))) (i : Fin 2) (e : E) :
    inner ℝ (cellToTorus (periodizedPartialTestVectorL2 φ i e)) f =
      ∫ x, inner ℝ e (f (torusQuotient x)) * φ.coordDeriv i x := by
  rw [periodizedPartialTestVectorL2, torus_inner_cellTest_eq]
  exact (torus_global_pairing_eq_cell f e
    ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    (φ.compact.fderiv_apply (𝕜 := ℝ) (basisVec i))).symm

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem torus_translation_hasWeakPartialDeriv {i : Fin 2}
    {f g : Lp E 2 torusMeasure}
    (h : ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (f (torusQuotient x)))
      (fun x => inner ℝ e (g (torusQuotient x)))) (z : Vec 2) :
    ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (translation (torusQuotient z) f (torusQuotient x)))
      (fun x => inner ℝ e (translation (torusQuotient z) g (torusQuotient x))) := by
  intro e
  apply hasWeakPartialDerivOn_congr_ae _ _ (hasWeakPartialDerivOn_translate_univ (h e) z)
  · rw [Measure.restrict_univ]
    filter_upwards [ae_torusQuotient (translation_ae (torusQuotient z) f)] with x hx
    rw [hx, map_sub]
  · rw [Measure.restrict_univ]
    filter_upwards [ae_torusQuotient (translation_ae (torusQuotient z) g)] with x hx
    rw [hx, map_sub]

omit [BorelSpace E] in
theorem averagingOperator_hasWeakPartialDeriv_torus {i : Fin 2}
    {f g : Lp E 2 torusMeasure}
    (h : ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (f (torusQuotient x)))
      (fun x => inner ℝ e (g (torusQuotient x))))
    (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) :
    ∀ e : E, HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (averagingOperator (torusQuotient.comp ρ)
        (continuous_torusQuotient.comp hρ) κ hκ f (torusQuotient x)))
      (fun x => inner ℝ e (averagingOperator (torusQuotient.comp ρ)
        (continuous_torusQuotient.comp hρ) κ hκ g (torusQuotient x))) := by
  intro e ψ hs hc _
  let φ : WeakTest (Set.univ : Set (Vec 2)) := ⟨ψ, hs, hc, Set.subset_univ _⟩
  simp only [setIntegral_univ]
  let t : Lp E 2 torusMeasure := cellToTorus (periodizedTestVectorL2 φ e)
  let dt : Lp E 2 torusMeasure := cellToTorus (periodizedPartialTestVectorL2 φ i e)
  have htranslated (z : Vec 2) :
      inner ℝ dt (translation (torusQuotient (ρ z)) f) =
        -inner ℝ t (translation (torusQuotient (ρ z)) g) := by
    rw [torus_inner_periodizedPartialTest_eq, torus_inner_periodizedTest_eq]
    exact (by simpa only [setIntegral_univ, φ, WeakTest.coordDeriv] using
      torus_translation_hasWeakPartialDeriv h (ρ z) e ψ hs hc (Set.subset_univ _))
  change (∫ x, inner ℝ e (averagingOperator (torusQuotient.comp ρ)
      (continuous_torusQuotient.comp hρ) κ hκ f (torusQuotient x)) * φ.coordDeriv i x) =
    -(∫ x, inner ℝ e (averagingOperator (torusQuotient.comp ρ)
      (continuous_torusQuotient.comp hρ) κ hκ g (torusQuotient x)) * φ.toFun x)
  rw [← torus_inner_periodizedPartialTest_eq, ← torus_inner_periodizedTest_eq]
  change inner ℝ dt (average (torusQuotient.comp ρ) κ f) =
    -inner ℝ t (average (torusQuotient.comp ρ) κ g)
  unfold average
  rw [← integral_inner (integrable_average_integrand (torusQuotient.comp ρ)
      (continuous_torusQuotient.comp hρ) hκ f),
    ← integral_inner (integrable_average_integrand (torusQuotient.comp ρ)
      (continuous_torusQuotient.comp hρ) hκ g), ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change inner ℝ dt (κ z • translation (torusQuotient (ρ z)) f) =
      -inner ℝ t (κ z • translation (torusQuotient (ρ z)) g)
    rw [real_inner_smul_right, real_inner_smul_right, htranslated, mul_neg]

end AVRegularity.Analysis.Convolution
end
