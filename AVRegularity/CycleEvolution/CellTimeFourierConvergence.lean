-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.CarrierFamilyProjection
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellEnergyNorm
public import AVRegularity.Statements.Intermediate.CycleEvolution.IsCellSolution
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Temporal Fourier differences controlled by the two vanishing tails. -/

/-- Real square bound for a sum, isolated from the Sobolev carrier. -/
theorem cellSquare_sum_bound {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : z ≤ x + y) : z ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- Both temporal difference integrals are bounded by individual Fourier tails. -/
theorem cellTime_fourier_difference_sq_integral {a b : ℝ} {slice : ℝ → TorusHk 1 ℂ}
    (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (N M : ℕ) :
    (∫ t in Icc a b, ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖ ^ 2) ≤
      2 * (∫ t in Icc a b, ‖galerkinProj N (slice t) - slice t‖ ^ 2) +
      2 * (∫ t in Icc a b, ‖galerkinProj M (slice t) - slice t‖ ^ 2) := by
  have ht (L : ℕ) : MemLp (fun t => galerkinProj L (slice t) - slice t)
      2 (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, Pi.sub_def] using ((galerkinProj L).comp_memLp' hs).sub hs
  have hw : MemLp (fun t => galerkinProj N (slice t) - galerkinProj M (slice t))
      2 (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, Pi.sub_def] using
      ((galerkinProj N).comp_memLp' hs).sub ((galerkinProj M).comp_memLp' hs)
  have htri (t : ℝ) : ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖ ≤
      ‖galerkinProj N (slice t) - slice t‖ + ‖galerkinProj M (slice t) - slice t‖ := by
    calc
      _ = ‖(galerkinProj N (slice t) - slice t) - (galerkinProj M (slice t) - slice t)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_sub_le _ _
  have hN := (ht N).norm.integrable_sq
  have hM := (ht M).norm.integrable_sq
  have hi := integral_mono_ae hw.norm.integrable_sq ((hN.const_mul 2).add (hM.const_mul 2))
    (Filter.Eventually.of_forall (fun t => by
      change ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖ ^ 2 ≤
        2 * ‖galerkinProj N (slice t) - slice t‖ ^ 2 +
        2 * ‖galerkinProj M (slice t) - slice t‖ ^ 2
      exact cellSquare_sum_bound (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (htri t)))
  have he := integral_add (hN.const_mul 2) (hM.const_mul 2)
  simp only [Pi.add_apply] at hi he
  rw [he, integral_const_mul, integral_const_mul] at hi
  exact hi

/-- Both temporal difference integrals are bounded by individual Fourier tails. -/
theorem cellTime_fourier_difference_product_integral {a b : ℝ} {slice g : ℝ → TorusHk 1 ℂ}
    (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b))) (N M : ℕ) :
    (∫ t in Icc a b, ‖g t‖ * ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖) ≤
      (∫ t in Icc a b, ‖g t‖ * ‖galerkinProj N (slice t) - slice t‖) +
      (∫ t in Icc a b, ‖g t‖ * ‖galerkinProj M (slice t) - slice t‖) := by
  have ht (L : ℕ) : MemLp (fun t => galerkinProj L (slice t) - slice t)
      2 (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, Pi.sub_def] using ((galerkinProj L).comp_memLp' hs).sub hs
  have hw : MemLp (fun t => galerkinProj N (slice t) - galerkinProj M (slice t))
      2 (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, Pi.sub_def] using
      ((galerkinProj N).comp_memLp' hs).sub ((galerkinProj M).comp_memLp' hs)
  have htri (t : ℝ) : ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖ ≤
      ‖galerkinProj N (slice t) - slice t‖ + ‖galerkinProj M (slice t) - slice t‖ := by
    calc
      _ = ‖(galerkinProj N (slice t) - slice t) - (galerkinProj M (slice t) - slice t)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_sub_le _ _
  have hp (L : ℕ) : Integrable
      (fun t => ‖g t‖ * ‖galerkinProj L (slice t) - slice t‖) (volume.restrict (Icc a b)) :=
    memLp_one_iff_integrable.mp (hg.norm.mul (ht L).norm : MemLp _ 1 _)
  have hpw : Integrable (fun t => ‖g t‖ *
      ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖) (volume.restrict (Icc a b)) :=
    memLp_one_iff_integrable.mp (hg.norm.mul hw.norm : MemLp _ 1 _)
  have hi := integral_mono_ae hpw ((hp N).add (hp M))
    (Filter.Eventually.of_forall (fun t => by
      change ‖g t‖ * ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖ ≤ _
      simpa only [mul_add, Pi.add_apply] using mul_le_mul_of_nonneg_left (htri t) (norm_nonneg (g t))))
  have he := integral_add (hp N) (hp M)
  simp only [Pi.add_apply] at hi he
  rw [he] at hi
  exact hi

/-- Both temporal difference integrals are bounded by individual Fourier tails. -/
theorem cellTime_fourier_difference_integrals {a b : ℝ} {slice g : ℝ → TorusHk 1 ℂ}
    (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b))) (N M : ℕ) :
    (∫ t in Icc a b, ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖ ^ 2) ≤
      2 * (∫ t in Icc a b, ‖galerkinProj N (slice t) - slice t‖ ^ 2) +
      2 * (∫ t in Icc a b, ‖galerkinProj M (slice t) - slice t‖ ^ 2) ∧
    (∫ t in Icc a b, ‖g t‖ * ‖galerkinProj N (slice t) - galerkinProj M (slice t)‖) ≤
      (∫ t in Icc a b, ‖g t‖ * ‖galerkinProj N (slice t) - slice t‖) +
      (∫ t in Icc a b, ‖g t‖ * ‖galerkinProj M (slice t) - slice t‖) :=
  ⟨cellTime_fourier_difference_sq_integral hs N M,
    cellTime_fourier_difference_product_integral hs hg N M⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The public energy norm depends only on the continuous trace of a cell solution. -/

/-- Periodic weak jets with the same value have identical spatial derivative classes. -/
theorem cellPeriodicWeakJet_congr_value (D E : RawJet2 1 ℂ)
    (hD : HasPeriodicOrderedWeakJet D) (hE : HasPeriodicOrderedWeakJet E)
    (he : D (valueIndex2 1) =ᵐ[volume.restrict AVenhance.unitCube] E (valueIndex2 1)) :
    ∀ a, D a =ᵐ[volume.restrict AVenhance.unitCube] E a := by
  let u : TorusHkFunction 1 ℂ := ⟨D, hD⟩
  let w : TorusHkFunction 1 ℂ := ⟨E, hE⟩
  have hv : u.toHk.val (valueIndex2 1) = w.toHk.val (valueIndex2 1) := by
    apply Lp.ext
    exact (torusJetToL2_ae D hD.2.1 _).trans
      (he.trans (torusJetToL2_ae E hE.2.1 _).symm)
  have hw : u.toHk = w.toHk := TorusHk.ext_value hv
  intro a
  have hc : u.toHk.val a = w.toHk.val a := congrArg (fun z => z.val a) hw
  exact (torusJetToL2_ae D hD.2.1 a).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℂ 2 (volume.restrict AVenhance.unitCube) => (z : Vec 2 → ℂ)) hc)).trans
      (torusJetToL2_ae E hE.2.1 a))

/-- Jointly almost measurable gradients with equal slices have equal uniformly local size. -/
theorem cellUlNorm_congr_sections {E : Type*} [NormedAddCommGroup E]
    (I : Set ℝ) (f g : ℝ → Vec 2 → E)
    (he : ∀ᵐ t ∂volume.restrict I,
      f t =ᵐ[volume.restrict AVenhance.unitCube] g t) :
    cellUlNorm I f = cellUlNorm I g := by
  unfold cellUlNorm
  congr 1
  funext a
  congr 1
  apply lintegral_congr_ae
  have hm : volume.restrict (Set.Icc a (a + 1) ∩ I) ≤ volume.restrict I :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  filter_upwards [ae_mono hm he] with t ht
  rw [cellL2Norm, cellL2Norm, eLpNorm_congr_ae ht]

/-- Solutions with identical continuous spatial traces have identical energy norms. -/
theorem cellSolution_energyNorm_congr {I : Set ℝ} {C C' : CellCoefficients}
    {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution I C src F D) (hE : IsCellSolution I C' src' F' E)
    (he : ∀ t ∈ I, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue E t) :
    cellEnergyNorm I D = cellEnergyNorm I E := by
  have hv : (⨆ t ∈ I, cellL2Norm (cellValue D t)) =
      (⨆ t ∈ I, cellL2Norm (cellValue E t)) := by
    apply iSup_congr
    intro t
    apply iSup_congr
    intro ht
    exact eLpNorm_congr_ae (he t ht)
  have hg : ∀ᵐ t ∂volume.restrict I,
      cellGradient (D t) =ᵐ[volume.restrict AVenhance.unitCube] cellGradient (E t) := by
    have hi : ∀ᵐ t ∂volume.restrict I, t ∈ I := ae_restrict_mem₀
      (hD.1.measurableSet.nullMeasurableSet)
    filter_upwards [hD.2.1, hE.2.1, hi] with t hDt hEt ht
    have ha := cellPeriodicWeakJet_congr_value (D t) (E t) hDt hEt (he t ht)
    have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j : Fin 2,
        cellGradComp (D t) j x = cellGradComp (E t) j x :=
      ae_all_iff.mpr (fun j => ha ⟨⟨1, by decide⟩, fun _ => j⟩)
    filter_upwards [hj] with x hx
    apply PiLp.ext
    exact hx
  unfold cellEnergyNorm
  rw [hv, cellUlNorm_congr_sections I _ _ hg]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Strong temporal convergence of the Fourier tails used in the Hilbert trace construction. -/

/-- Fourier tails vanish in temporal L² and in the L¹ dual-state product. -/
theorem cellTime_fourier_tail_integrals {a b : ℝ} {slice g : ℝ → TorusHk 1 ℂ}
    (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    Tendsto (fun N => ∫ t in Icc a b, ‖galerkinProj N (slice t) - slice t‖ ^ 2)
      atTop (𝓝 0) ∧
    Tendsto (fun N => ∫ t in Icc a b, ‖g t‖ * ‖galerkinProj N (slice t) - slice t‖)
      atTop (𝓝 0) := by
  have htail (N : ℕ) (t : ℝ) : ‖galerkinProj N (slice t) - slice t‖ ≤ 2 * ‖slice t‖ := by
    exact (norm_sub_le _ _).trans ((add_le_add (galerkinProj_norm_le N (slice t)) le_rfl).trans_eq
      (by ring))
  have hmeas (N : ℕ) : AEStronglyMeasurable
      (fun t => galerkinProj N (slice t) - slice t) (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, Pi.sub_def] using
      (((galerkinProj (E := ℂ) (K := 1) N).comp_memLp' hs).sub hs).aestronglyMeasurable
  have hlim (t : ℝ) : Tendsto (fun N => ‖galerkinProj N (slice t) - slice t‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((galerkinProj_tendsto (slice t)).sub (tendsto_const_nhds (x := slice t))).norm
  constructor
  · have hi := tendsto_integral_of_dominated_convergence (fun t => 4 * ‖slice t‖ ^ 2)
      (fun N => (hmeas N).norm.pow 2)
      (hs.norm.integrable_sq.const_mul 4)
      (fun N => Filter.Eventually.of_forall (fun t => by
        change ‖‖galerkinProj N (slice t) - slice t‖ ^ 2‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have ht := htail N t
        nlinarith [norm_nonneg (galerkinProj N (slice t) - slice t), norm_nonneg (slice t)]))
      (Filter.Eventually.of_forall (fun t => by simpa using (hlim t).pow 2))
    simpa only [integral_zero, Pi.pow_apply, Pi.mul_apply] using hi
  · have hp : Integrable (fun t => ‖g t‖ * ‖slice t‖) (volume.restrict (Icc a b)) :=
      memLp_one_iff_integrable.mp (hg.norm.mul hs.norm : MemLp _ 1 _)
    have hi := tendsto_integral_of_dominated_convergence (fun t => 2 * (‖g t‖ * ‖slice t‖))
      (fun N => hg.aestronglyMeasurable.norm.mul (hmeas N).norm) (hp.const_mul 2)
      (fun N => Filter.Eventually.of_forall (fun t => by
        change ‖‖g t‖ * ‖galerkinProj N (slice t) - slice t‖‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        calc
          _ ≤ ‖g t‖ * (2 * ‖slice t‖) := mul_le_mul_of_nonneg_left (htail N t) (norm_nonneg _)
          _ = _ := by ring))
      (Filter.Eventually.of_forall (fun t => by simpa using (hlim t).const_mul ‖g t‖))
    simpa only [integral_zero, Pi.pow_apply, Pi.mul_apply] using hi

end AVRegularity.CycleEvolution
end
