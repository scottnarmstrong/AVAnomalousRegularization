-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellConjugateClass
import AVenhance.Infra.ODE.Linear.Gronwall
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! The real Hilbert adjoint identity for complex scalar multiplication on the periodic H1 graph. -/

theorem cellH1Scalar_inner (c : ℂ) (u z : TorusHk 1 ℂ) :
    inner ℝ (cellH1Scalar c u) z = inner ℝ u (cellH1Scalar (star c) z) := by
  change inner ℝ (cellH1Scalar c u).val z.val = inner ℝ u.val (cellH1Scalar (star c) z).val
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cellH1Scalar_jet_ae c u a, cellH1Scalar_jet_ae (star c) z a]
    with x hu hz
  rw [hu, hz]
  calc
    _ = inner ℝ (z.val a x) (c * u.val a x) := real_inner_comm _ _
    _ = inner ℝ (star c * z.val a x) (u.val a x) :=
      cellComplex_real_inner_smul (z.val a x) c (u.val a x)
    _ = _ := real_inner_comm _ _

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The existing periodic H1 complex scalar action is literal scalar multiplication of the ambient jet. -/

theorem cellH1Scalar_val (c : ℂ) (z : TorusHk 1 ℂ) :
    (cellH1Scalar c z).val = c • z.val := by
  apply PiLp.ext
  intro a
  apply Lp.ext
  filter_upwards [cellH1Scalar_jet_ae c z a, Lp.coeFn_smul c (z.val a)] with x hc hs
  exact hc.trans hs.symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Complex scalar composition on the realified periodic H¹ graph. -/

theorem cellH1Scalar_mul (c d : ℂ) (u : TorusHk 1 ℂ) :
    cellH1Scalar c (cellH1Scalar d u) = cellH1Scalar (c * d) u := by
  apply TorusHk.ext_value
  change torusHkValueCLM (cellH1Scalar c (cellH1Scalar d u)) =
    torusHkValueCLM (cellH1Scalar (c * d) u)
  rw [cellH1Scalar_value, cellH1Scalar_value, cellH1Scalar_value]
  simp only [cellScalarCLM_smul, smul_smul]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Weak derivative classes commute with genuine complex scalar multiplication. -/

theorem cellH1Scalar_derivative (c : ℂ) (z : TorusHk 1 ℂ) (j : Fin 2) :
    cellDerivativeCLM j (cellH1Scalar c z) = cellScalarCLM c (cellDerivativeCLM j z) := by
  apply Lp.ext
  exact (cellH1Scalar_jet_ae c z ⟨⟨1, by decide⟩, fun _ => j⟩).trans
    (cellScalarCLM_ae c (cellDerivativeCLM j z)).symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Mean projection onto a normalized graph has a uniform entering norm. -/

theorem cellMean_graph_remainder_norm_le_two (u R : ComplexCellL2) (hR : ‖R‖ ≤ 2) :
    ‖u - cellScalarCLM (cellMean u) R‖ ≤ 3 * ‖u‖ := by
  have hA : ‖cellMean u‖ ≤ ‖u‖ := by
    rw [← cellMeanCLM_apply u]
    exact cellMeanCLM_norm_le u
  calc
    _ ≤ ‖u‖ + ‖cellScalarCLM (cellMean u) R‖ := norm_sub_le _ _
    _ = ‖u‖ + ‖cellMean u‖ * ‖R‖ := by rw [cellScalarCLM_norm]
    _ ≤ ‖u‖ + ‖u‖ * 2 := add_le_add le_rfl (mul_le_mul hA hR (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Literal cell means commute with absolutely L2-summable series. -/

/-- Absolute L2 summability justifies the mean of the literal pointwise series. -/
theorem cellMean_tsum_of_cellL2Norm {J : Type*} [Countable J]
    (f : J → Vec 2 → ℂ) (hs : (∑' j, cellL2Norm (f j)) < ⊤) :
    cellMean (fun x => ∑' j, f j x) = ∑' j, cellMean (f j) := by
  change (∑' j, eLpNorm (f j) 2 (volume.restrict AVenhance.unitCube)) < ⊤ at hs
  have hm j : MemLp (f j) 2 (volume.restrict AVenhance.unitCube) :=
    (ENNReal.le_tsum j).trans_lt hs
  let u := fun j => (hm j).toLp (f j)
  have hu : (∑' j, ‖u j‖ₑ) < ⊤ := by
    simpa only [u, Lp.enorm_toLp] using hs
  have hall : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j, u j x = f j x :=
    ae_all_iff.mpr (fun j => (hm j).coeFn_toLp)
  have he : (⇑(∑' j, u j) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => ∑' j, f j x) := by
    filter_upwards [Lp.coeFn_tsum hu.ne, hall] with x hx hx'
    exact hx.trans (tsum_congr (fun j => hx' j))
  calc
    _ = cellMeanCLM (∑' j, u j) := by
      rw [cellMeanCLM_apply]
      exact (integral_congr_ae he).symm
    _ = ∑' j, cellMeanCLM (u j) := cellMeanCLM.map_tsum (Summable.of_enorm hu.ne)
    _ = _ := by
      apply tsum_congr
      intro j
      rw [cellMeanCLM_apply]
      exact integral_congr_ae (hm j).coeFn_toLp

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Conjugate H¹ tests for the public bilinear complex cell identity. -/

/-- A public bilinear test becomes its conjugate in the sesquilinear Hilbert equation. -/
def cellRawTest (ψ : TorusHkFunction 1 ℂ) : TorusHk 1 ℂ := cellH1Conj ψ.toHk

/-- Every conjugate test coordinate is the conjugate of the public raw test coordinate. -/
theorem cellRawTest_jet_ae (ψ : TorusHkFunction 1 ℂ) (a : JetIndex2 1) :
    (cellRawTest ψ).val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => star (ψ.jet a x) := by
  filter_upwards [cellH1Conj_jet_ae ψ.toHk a,
    torusJetToL2_ae ψ.jet ψ.hasPeriodicWeakJet.2.1 a] with x hx hψx
  exact hx.trans (congrArg star hψx)

/-- The raw test value is represented by the conjugate Hilbert test value. -/
theorem cellRawTest_value_ae (ψ : TorusHkFunction 1 ℂ) :
    (torusHkValueCLM (cellRawTest ψ) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      star (ψ.jet (valueIndex2 1)) := cellRawTest_jet_ae ψ _

/-- The raw test derivatives are represented by the conjugate Hilbert test derivatives. -/
theorem cellRawTest_derivative_ae (ψ : TorusHkFunction 1 ℂ) (j : Fin 2) :
    (cellDerivativeCLM j (cellRawTest ψ) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      star (ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) := cellRawTest_jet_ae ψ _

/-- A continuous trace class paired with a conjugate test reads the public bilinear product. -/
theorem cellRawTest_pairing_ae (ψ : TorusHkFunction 1 ℂ) (u : ComplexCellL2)
    (rawu : Vec 2 → ℂ) (hu : (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] rawu) :
    (fun x => u x * star (torusHkValueCLM (cellRawTest ψ) x)) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => rawu x * ψ.jet (valueIndex2 1) x := by
  filter_upwards [hu, cellRawTest_jet_ae ψ (valueIndex2 1)] with x hx hψx
  change torusHkValueCLM (cellRawTest ψ) x = star (ψ.jet (valueIndex2 1) x) at hψx
  rw [hx, hψx, star_star]

/-- All raw endpoint pairings in the public weak identity are integrable. -/
theorem cellRawTest_pairing_integrable (ψ : TorusHkFunction 1 ℂ) (u : ComplexCellL2)
    (rawu : Vec 2 → ℂ) (hu : (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] rawu) :
    Integrable (fun x => rawu x * ψ.jet (valueIndex2 1) x) (volume.restrict AVenhance.unitCube) :=
  (cellComplex_pairing_integrable u _).congr (cellRawTest_pairing_ae ψ u rawu hu)

/-- All raw endpoint pairings in the public weak identity equal the complex Hilbert pairing. -/
theorem cellRawTest_pairing_integral (ψ : TorusHkFunction 1 ℂ) (u : ComplexCellL2)
    (rawu : Vec 2 → ℂ) (hu : (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] rawu) :
    cellComplexPair u (torusHkValueCLM (cellRawTest ψ)) =
      ∫ x in AVenhance.unitCube, rawu x * ψ.jet (valueIndex2 1) x :=
  integral_congr_ae (cellRawTest_pairing_ae ψ u rawu hu)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Complex scalar actions expressed through the real Hilbert module and the fixed i action. -/

theorem cellScalarCLM_real_imag (c : ℂ) (u : ComplexCellL2) :
    cellScalarCLM c u = c.re • u + c.im • cellScalarCLM Complex.I u := by
  apply Lp.ext
  filter_upwards [cellScalarCLM_ae c u, cellScalarCLM_ae Complex.I u,
    Lp.coeFn_smul c.re u, Lp.coeFn_smul c.im (cellScalarCLM Complex.I u),
    Lp.coeFn_add (c.re • u) (c.im • cellScalarCLM Complex.I u)] with x hc hi hr hm ha
  rw [hc, ha]
  change c * u x = (c.re • u) x + (c.im • cellScalarCLM Complex.I u) x
  rw [hr, hm]
  change c * u x = (c.re : ℂ) * u x + (c.im : ℂ) * (cellScalarCLM Complex.I u x)
  rw [hi]
  conv_lhs => rw [← Complex.re_add_im c]
  ring

theorem cellH1Scalar_real_imag (c : ℂ) (u : TorusHk 1 ℂ) :
    cellH1Scalar c u = c.re • u + c.im • cellH1Scalar Complex.I u := by
  apply TorusHk.ext_value
  change torusHkValueCLM (cellH1Scalar c u) =
    torusHkValueCLM (c.re • u + c.im • cellH1Scalar Complex.I u)
  rw [map_add, map_smul, map_smul, cellH1Scalar_value, cellH1Scalar_value]
  exact cellScalarCLM_real_imag c (torusHkValueCLM u)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Grönwall estimates retaining the integrated dissipation term. -/

/-- A weak-time energy inequality retains nonnegative dissipation in its Grönwall bound. -/
theorem CellWeakHilbertCurve.energy_dissipation_le_gronwall {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → AVRegularity.Sobolev.TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g)
    (C : ℝ) (hC : 0 ≤ C) (f d : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b) (hd : IntervalIntegrable d volume a b)
    (hf_nonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ f t)
    (hd_nonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ d t)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * inner ℝ (g t) (slice t) + d t ≤ C * ‖u t‖ ^ 2 + f t) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 + ∫ s in a..t, d s ≤
        (‖u a‖ ^ 2 + ∫ s in a..b, f s) * Real.exp (C * (t - a)) := by
  let E : ℝ → ℝ := fun t => ‖u t‖ ^ 2 + ∫ s in a..t, d s
  have hucont : ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc a b) := by
    exact h.trace.norm.pow 2
  have hdcont : ContinuousOn (fun t => ∫ s in a..t, d s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hd left_mem_uIcc
  have hEcont : ContinuousOn E (Icc a b) := hucont.add hdcont
  have hCEint : IntervalIntegrable (fun t => C * E t) volume a b :=
    (continuousOn_const.mul hEcont).intervalIntegrable_of_Icc hab
  have hCuInt : IntervalIntegrable (fun t => C * ‖u t‖ ^ 2) volume a b :=
    (continuousOn_const.mul hucont).intervalIntegrable_of_Icc hab
  have hule : ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ E t := by
    intro t ht
    have hdt : ∀ᵐ s ∂volume.restrict (Icc a t), 0 ≤ d s := by
      rw [← restrict_Ioc_eq_restrict_Icc]
      exact hd_nonneg.filter_mono (ae_mono
        (Measure.restrict_mono (Ioc_subset_Ioc le_rfl ht.2) le_rfl))
    have hn := intervalIntegral.integral_nonneg_of_ae_restrict ht.1 hdt
    exact le_add_of_nonneg_right hn
  have hineq : ∀ t ∈ Icc a b,
      E t ≤ (‖u a‖ ^ 2 + ∫ s in a..b, f s) + ∫ s in a..t, C * E s := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hsubI : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hg := hgrowth.filter_mono (ae_mono
      (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
    have hbound := intervalIntegral.integral_mono_ae_restrict ht.1
      (((h.mono hsubI).production_intervalIntegrable ht.1).add (hd.mono_set hsub))
      ((hCuInt.mono_set hsub).add (hf.mono_set hsub)) hg
    rw [intervalIntegral.integral_add ((h.mono hsubI).production_intervalIntegrable ht.1) (hd.mono_set hsub),
      ← (h.mono hsubI).energy_increment ht.1,
      intervalIntegral.integral_add (hCuInt.mono_set hsub) (hf.mono_set hsub)] at hbound
    have hfbound := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hf_nonneg hf
    have hCbound : (∫ s in a..t, C * ‖u s‖ ^ 2) ≤ ∫ s in a..t, C * E s := by
      apply intervalIntegral.integral_mono_on ht.1 (hCuInt.mono_set hsub)
        (hCEint.mono_set hsub)
      intro s hs
      exact mul_le_mul_of_nonneg_left (hule s ⟨hs.1, hs.2.trans ht.2⟩) hC
    dsimp only [E]
    linarith
  have hgr := AVenhance.Infra.ODE.integral_gronwall_bound hab
    (continuous_const.intervalIntegrable a b) hCEint (fun _ _ => hC) hineq
  intro t ht
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - a) C]
    using hgr t ht

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Addition of genuine weak Hilbert curves, retaining their time increment equation. -/

theorem CellWeakHilbertCurve.add {a b : ℝ}
    {u v : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g slice' g' : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (h' : CellWeakHilbertCurve a b v slice' g') :
    CellWeakHilbertCurve a b (fun t => u t + v t) (fun t => slice t + slice' t)
      (fun t => g t + g' t) := by
  have hs : MemLp (slice + slice') 2 (volume.restrict (Icc a b)) := by
    simpa only [sub_neg_eq_add] using h.state.sub h'.state.neg
  have hd : MemLp (g + g') 2 (volume.restrict (Icc a b)) := by
    simpa only [sub_neg_eq_add] using h.dual.sub h'.dual.neg
  refine ⟨h.trace.add h'.trace, hs, hd, ?_, ?_⟩
  · filter_upwards [h.agrees, h'.agrees] with t ht ht'
    rw [ht, ht', map_add]
  · intro s hs t ht hst z
    have hg := cellWeakPair_intervalIntegrable hs ht hst g h.dual z
    have hg' := cellWeakPair_intervalIntegrable hs ht hst g' h'.dual z
    simp only [inner_add_left]
    rw [intervalIntegral.integral_add hg hg']
    have hu := h.increment s hs t ht hst z
    have hv := h'.increment s hs t ht hst z
    linarith

end AVRegularity.CycleEvolution
end
end

section
/-! Uniqueness from weak-time energy calculus and a one-sided growth bound. -/

@[expose] public noncomputable section

open MeasureTheory Set AVRegularity.Sobolev

namespace AVRegularity.CycleEvolution

/-- Zero initial trace and a one-sided Gårding growth bound force a weak-time curve to vanish. -/
theorem CellWeakHilbertCurve.eq_zero_of_growth {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g)
    (hinitial : u a = 0) (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * inner ℝ (g t) (slice t) ≤ C * ‖u t‖ ^ 2) :
    ∀ t ∈ Icc a b, u t = 0 := by
  have hcont : ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc a b) := h.trace.norm.pow 2
  have hint : IntervalIntegrable (fun t => C * ‖u t‖ ^ 2) volume a b :=
    (continuousOn_const.mul hcont).intervalIntegrable_of_Icc hab
  have hineq : ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ 0 + ∫ s in a..t, C * ‖u s‖ ^ 2 := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have husub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact hsub
    have hr := h.mono hsub
    have hg := hgrowth.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hb := intervalIntegral.integral_mono_ae_restrict ht.1
      (hr.production_intervalIntegrable ht.1) (hint.mono_set husub) hg
    rw [← hr.energy_increment ht.1] at hb
    simpa [hinitial] using hb
  have hgr := AVenhance.Infra.ODE.integral_gronwall_bound hab
    (continuous_const.intervalIntegrable a b) hint (fun _ _ => hC) hineq
  intro t ht
  have hz : ‖u t‖ ^ 2 = 0 := le_antisymm (by simpa using hgr t ht) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- Weak-time curves with common initial trace and a difference Gårding bound agree. -/
theorem cellWeakHilbert_unique_of_difference_growth {a b : ℝ} (hab : a ≤ b)
    {u v : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g slice' g' : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (h' : CellWeakHilbertCurve a b v slice' g')
    (hinitial : u a = v a) (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * inner ℝ (g t - g' t) (slice t - slice' t) ≤ C * ‖u t - v t‖ ^ 2) :
    ∀ t ∈ Icc a b, u t = v t := by
  have hz := (h.sub h').eq_zero_of_growth hab (sub_eq_zero.mpr hinitial) C hC hgrowth
  intro t ht
  exact sub_eq_zero.mp (hz t ht)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Imaginary components of the actual complex cell forms. -/

/-- Testing the real generator with i times the test extracts the imaginary complex generator. -/
theorem cellComplexGenerator_im (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    (cellComplexGenerator C hG V hv hb t u z).im =
      cellGeneratorForm C hG V hv hb t u (cellH1Scalar Complex.I z) := by
  simp only [cellComplexGenerator, cellGeneratorForm, cellDiffusionForm, Fin.sum_univ_two,
    Complex.add_im, Complex.sub_im, Complex.neg_im, cellComplexPair_im,
    add_apply, sub_apply, neg_apply, pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply,
    cellH1Scalar_value, cellH1Scalar_shift]

/-- Testing the real source with i times the test extracts the imaginary complex source. -/
theorem cellComplexSource_im (θ : Fin 2 → ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (z : TorusHk 1 ℂ) : (cellComplexSource θ S F z).im =
      cellSourceFunctional θ S F (cellH1Scalar Complex.I z) := by
  simp only [cellComplexSource, cellSourceFunctional, Fin.sum_univ_two,
    Complex.add_im, Complex.sub_im, cellComplexPair_im, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, cellH1Scalar_value, cellH1Scalar_shift]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The existing periodic weak H1 graph as a complete complex normed space. -/

def cellComplexH1Submodule : Submodule ℂ (JetL2 (volume.restrict AVenhance.unitCube) 1 ℂ) where
  carrier := torusHkGraph (E := ℂ) 1
  zero_mem' := (torusHkGraph (E := ℂ) 1).zero_mem
  add_mem' := (torusHkGraph (E := ℂ) 1).add_mem
  smul_mem' c u hu := by
    have hz := (cellH1Scalar c ⟨u, hu⟩).property
    rw [cellH1Scalar_val] at hz
    exact hz

abbrev CellComplexH1 := ↥cellComplexH1Submodule

theorem cellComplexH1Submodule_isClosed :
    IsClosed (cellComplexH1Submodule : Set (JetL2 (volume.restrict AVenhance.unitCube) 1 ℂ)) :=
  (torusHkGraph (E := ℂ) 1).isClosed

instance cellComplexH1_complete : CompleteSpace CellComplexH1 :=
  completeSpace_coe_iff_isComplete.mpr cellComplexH1Submodule_isClosed.isComplete

def cellComplexH1RealEquiv : CellComplexH1 ≃ₗᵢ[ℝ] TorusHk 1 ℂ where
  toFun u := ⟨u.val, u.property⟩
  invFun u := ⟨u.val, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

def cellComplexH1ValueCLM : CellComplexH1 →L[ℂ] ComplexCellL2 :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : JetIndex2 1 => ComplexCellL2) (valueIndex2 1)).comp
    cellComplexH1Submodule.subtypeL

theorem cellComplexH1ValueCLM_eq (u : CellComplexH1) :
    cellComplexH1ValueCLM u = torusHkValueCLM (cellComplexH1RealEquiv u) := rfl

end AVRegularity.CycleEvolution
end
end
