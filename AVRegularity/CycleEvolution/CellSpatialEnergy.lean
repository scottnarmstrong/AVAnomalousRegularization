-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellDriftComplexMultiplier
import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
import AVRegularity.CycleEvolution.FibreCoefficientLinearSeries
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! A real metric multiplier is self-adjoint for the complex cell pairing. -/

theorem cellMetricEntryCLM_complex_adjoint
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (j k : Fin 2) (u z : ComplexCellL2) :
    cellComplexPair (cellMetricEntryCLM hG t j k u) z =
      cellComplexPair u (cellMetricEntryCLM hG t j k z) := by
  unfold cellComplexPair
  apply integral_congr_ae
  filter_upwards [cellMetricEntryCLM_ae hG t j k u,
    cellMetricEntryCLM_ae hG t j k z] with x hu hz
  rw [hu, hz, star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Weak divergence-free transport preserves the mean of every complex periodic H¹ field. -/

/-- The weak drift identity applies to every real linear component of a complex H¹ test. -/
theorem cellDrift_linear_test_zero {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (t : ℝ) (u : TorusHk 1 ℂ) (L : ℂ →L[ℝ] ℝ) :
    (∫ x in AVenhance.unitCube, ∑ j : Fin 2, v t x j * L (cellDerivativeCLM j u x)) = 0 := by
  let q := mapTorusHk L u
  have hq (j : Fin 2) : q.toFunction.jet ⟨⟨1, by decide⟩, fun _ => j⟩ =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => L (cellDerivativeCLM j u x) :=
    (periodicJetRepresentative_ae q.val _).trans (mapTorusHk_jet_ae L u _)
  have h0 := hv.2.2.2 t q.toFunction
  have he : (∫ x in AVenhance.unitCube,
      ∑ j : Fin 2, v t x j * q.toFunction.jet ⟨⟨1, by decide⟩, fun _ => j⟩ x) =
      ∫ x in AVenhance.unitCube, ∑ j : Fin 2, v t x j * L (cellDerivativeCLM j u x) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.2 hq] with x hx
    simp only [hx]
  exact he.symm.trans h0

/-- The actual complex drift-gradient product is integrable. -/
theorem cellDrift_mean_integrable {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    Integrable (fun x => ∑ j : Fin 2, (v t x j : ℂ) * cellDerivativeCLM j u x)
      (volume.restrict AVenhance.unitCube) := by
  let : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩
  have hi (j : Fin 2) : Integrable (fun x => (v t x j : ℂ) * cellDerivativeCLM j u x)
      (volume.restrict AVenhance.unitCube) := by
    apply ((Lp.memLp (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j
      (cellDerivativeCLM j u))).integrable (by norm_num)).congr
    exact cellDriftEntryCLM_ae ⟨0, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j u)
  simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hi j)

/-- Complex transport has zero mean, using the real and imaginary H¹ tests separately. -/
theorem cellDrift_mean_zero {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    (∫ x in AVenhance.unitCube, ∑ j : Fin 2, (v t x j : ℂ) * cellDerivativeCLM j u x) = 0 := by
  have hi := cellDrift_mean_integrable hv V hb t u
  apply Complex.ext
  · have he := Complex.reCLM.integral_comp_comm hi
    change (∫ x in AVenhance.unitCube,
      (∑ j : Fin 2, (v t x j : ℂ) * cellDerivativeCLM j u x).re) =
      (∫ x in AVenhance.unitCube, ∑ j : Fin 2, (v t x j : ℂ) * cellDerivativeCLM j u x).re at he
    rw [← he]
    simpa only [Fin.sum_univ_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.reCLM_apply, Complex.zero_re] using
      cellDrift_linear_test_zero hv t u Complex.reCLM
  · have he := Complex.imCLM.integral_comp_comm hi
    change (∫ x in AVenhance.unitCube,
      (∑ j : Fin 2, (v t x j : ℂ) * cellDerivativeCLM j u x).im) =
      (∫ x in AVenhance.unitCube, ∑ j : Fin 2, (v t x j : ℂ) * cellDerivativeCLM j u x).im at he
    rw [← he]
    simpa only [Fin.sum_univ_two, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.imCLM_apply, Complex.zero_im] using
      cellDrift_linear_test_zero hv t u Complex.imCLM

end AVRegularity.CycleEvolution
end
end

section
/-! Square-integrable actual forcing in the finite cell systems. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleEvolution

/-- Fixed source test moments are square integrable in time. -/
theorem cellRawSourceFunctional_memLp {a b : ℝ} (θ : Fin 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (z : TorusHk 1 ℂ) :
    MemLp (fun t => cellRawSourceFunctional θ src F t z) 2 (volume.restrict (Icc a b)) := by
  have h0 := (innerSL ℝ (torusHkValueCLM z)).comp_memLp'
    (cellSourceSlice_memLp (Icc a b) src hsrc)
  have hfj (j : Fin 2) : MemLp (Function.uncurry (fun t x => F t x j)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF
  have h1 (j : Fin 2) := (innerSL ℝ
    (cellShiftedDerivativeCLM (fun i => star (θ i)) j z)).comp_memLp'
    (cellSourceSlice_memLp (Icc a b) (fun t x => F t x j) (hfj j))
  simp only [cellRawSourceFunctional, ContinuousLinearMap.coe_coe,
    cellSourceFunctional, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  simpa only [Fin.sum_univ_two, Pi.sub_def, Pi.add_def,
    Function.comp_def, ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm] using
    h0.sub ((h1 0).add (h1 1))

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- The actual mass-inverted raw forcing is square integrable in time. -/
theorem cellGalerkin_actualForcing_memLp {a b : ℝ} (N : ℕ) (θ : Fin 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (fun t => cellGalerkinForcing N (cellRawSourceFunctional θ src F t))
      2 (volume.restrict (Icc a b)) := by
  let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
  let mass := cellGalerkinMass (E := ℂ) N
  let q := fun t => cellGalerkinSource N (cellRawSourceFunctional θ src F t)
  have hsum : MemLp (fun t => ∑ i, q t (basis i) •
      weakMassSource mass (cellGalerkinMass_injective N) (basis.coord i))
      2 (volume.restrict (Icc a b)) := by
    apply memLp_finsetSum Finset.univ
    intro i _
    have hqi : MemLp (fun t => q t (basis i)) 2 (volume.restrict (Icc a b)) :=
      cellRawSourceFunctional_memLp θ src F hsrc hF (basis i).val
    exact (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (weakMassSource mass (cellGalerkinMass_injective N) (basis.coord i))).comp_memLp' hqi
  apply hsum.ae_eq
  exact Filter.Eventually.of_forall (fun t =>
    (weakMassSource_eq_sum basis mass (cellGalerkinMass_injective N) (q t)).symm)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The H⁻¹ Riesz representative of actual scalar and divergence sources. -/

/-- Riesz representation of the scalar/divergence source functional. -/
def cellSourceDual (θ : Fin 2 → ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    TorusHk 1 ℂ :=
  (InnerProductSpace.toDual ℝ (TorusHk 1 ℂ)).symm (cellSourceFunctional θ S F)

/-- The source dual has exactly the scalar/divergence pairing. -/
theorem cellSourceDual_pairing (θ : Fin 2 → ℂ) (S : ComplexCellL2)
    (F : Fin 2 → ComplexCellL2) (z : TorusHk 1 ℂ) :
    inner ℝ (cellSourceDual θ S F) z = cellSourceFunctional θ S F z :=
  InnerProductSpace.toDual_symm_apply

/-- The source dual has the direct L² source budget. -/
theorem cellSourceDual_norm_le (θ : Fin 2 → ℂ) (S : ComplexCellL2)
    (F : Fin 2 → ComplexCellL2) : ‖cellSourceDual θ S F‖ ≤
      ‖torusHkValueCLM (E := ℂ) (K := 1)‖ * ‖S‖ +
        ∑ j, ‖cellShiftedDerivativeCLM (fun i => star (θ i)) j‖ * ‖F j‖ := by
  unfold cellSourceDual
  rw [LinearIsometryEquiv.norm_map]
  exact cellSourceFunctional_norm_le θ S F

/-- Bochner L² scalar and flux sources yield a Bochner L² source dual. -/
theorem cellSourceDual_memLp {μ : Measure ℝ} (θ : Fin 2 → ℂ)
    (S : ℝ → ComplexCellL2) (hS : MemLp S 2 μ)
    (F : ℝ → Fin 2 → ComplexCellL2) (hF : ∀ j, MemLp (fun t => F t j) 2 μ) :
    MemLp (fun t => cellSourceDual θ (S t) (F t)) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun t => cellSourceDual θ (S t) (F t)) μ := by
    apply cellH1_aestronglyMeasurable_of_pairings
    intro z
    simp only [cellSourceDual_pairing]
    have h0 := hS.aestronglyMeasurable.inner (𝕜 := ℝ)
      (aestronglyMeasurable_const (b := torusHkValueCLM z))
    have h1 (j : Fin 2) := (hF j).aestronglyMeasurable.inner (𝕜 := ℝ)
      (aestronglyMeasurable_const (b := cellShiftedDerivativeCLM (fun i => star (θ i)) j z))
    simpa only [cellSourceFunctional, sub_apply, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Fin.sum_univ_two, Pi.add_def, Pi.sub_def] using h0.sub ((h1 0).add (h1 1))
  let J := ‖torusHkValueCLM (E := ℂ) (K := 1)‖
  let D := fun j => ‖cellShiftedDerivativeCLM (fun i => star (θ i)) j‖
  let budget := fun t => J * ‖S t‖ + D 0 * ‖F t 0‖ + D 1 * ‖F t 1‖
  have hm : MemLp budget 2 μ := by
    simpa only [budget, Pi.smul_def, smul_eq_mul, Pi.add_def] using
      ((hS.norm.const_smul J).add ((hF 0).norm.const_smul (D 0))).add ((hF 1).norm.const_smul (D 1))
  apply hm.of_le hmeas
  apply Filter.Eventually.of_forall
  intro t
  have hbn : 0 ≤ budget t := by dsimp only [budget, J, D]; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hbn]
  simpa only [budget, J, D, Fin.sum_univ_two, add_assoc] using cellSourceDual_norm_le θ (S t) (F t)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Strong measurability of the actual H⁻¹ derivative of a Bochner H¹ state. -/

/-- Measurable fixed form entries yield measurable entries with a variable H¹ trial state. -/
theorem cellVariableForm_pairing_aestronglyMeasurable {μ : Measure ℝ}
    (B : ℝ → TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ)
    (hB : ∀ u z, AEStronglyMeasurable (fun t => B t u z) μ)
    (f : ℝ → TorusHk 1 ℂ) (hf : AEStronglyMeasurable f μ) (z : TorusHk 1 ℂ) :
    AEStronglyMeasurable (fun t => B t (f t) z) μ := by
  have hproj (N : ℕ) : AEStronglyMeasurable (fun t => B t (galerkinProj N (f t)) z) μ := by
    let basis := Module.finBasis ℝ (CellGalerkinSpace (E := ℂ) N)
    let L := fun i => (basis.coord i).toContinuousLinearMap.comp (cellH1InitialCLM N)
    have hcoord (i) := (L i).continuous.comp_aestronglyMeasurable hf
    have hsum : AEStronglyMeasurable (fun t => ∑ i, L i (f t) * B t (basis i).val z) μ := by
      apply AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator.aestronglyMeasurable_finset_sum
      intro i _
      exact (hcoord i).mul (hB (basis i).val z)
    apply hsum.congr
    apply Filter.Eventually.of_forall
    intro t
    let Ψ := ((B t).flip z).comp (cellGalerkinState N)
    have he := congrArg Ψ (basis.sum_repr (cellH1InitialCLM N (f t)))
    simp only [map_sum, map_smul, smul_eq_mul] at he
    change (∑ i, (basis.repr (cellH1InitialCLM N (f t))) i * Ψ (basis i)) =
      Ψ (cellH1InitialCLM N (f t))
    exact he
  apply aestronglyMeasurable_of_tendsto_ae atTop hproj
  exact Filter.Eventually.of_forall (fun t =>
    (((B t).flip z).continuous.tendsto (f t)).comp (galerkinProj_tendsto (f t)))

/-- The actual generator and sources produce a strongly measurable H¹ Riesz derivative. -/
theorem cellDualDerivative_aestronglyMeasurable {μ : Measure ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Homogenization.Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : Measurable C.κ)
    (f : ℝ → TorusHk 1 ℂ) (hf : AEStronglyMeasurable f μ)
    (S : ℝ → ComplexCellL2) (hS : AEStronglyMeasurable S μ)
    (F : ℝ → Fin 2 → ComplexCellL2) (hF : ∀ j, AEStronglyMeasurable (fun t => F t j) μ) :
    AEStronglyMeasurable (fun t => cellDualDerivative C hG V hv hb t (f t) (S t) (F t)) μ := by
  apply cellH1_aestronglyMeasurable_of_pairings
  intro z
  simp only [cellDualDerivative_pairing]
  have hgen := cellVariableForm_pairing_aestronglyMeasurable (cellGeneratorForm C hG V hv hb)
    (fun u z => (cellGeneratorForm_pairing_stronglyMeasurable C hG V hv hb hκ u z).aestronglyMeasurable)
    f hf z
  have hs : AEStronglyMeasurable (fun t => cellSourceFunctional C.θ (S t) (F t) z) μ := by
    have h0 := hS.inner (𝕜 := ℝ) (aestronglyMeasurable_const (b := torusHkValueCLM z))
    have h1 (j : Fin 2) := (hF j).inner (𝕜 := ℝ)
      (aestronglyMeasurable_const (b := cellShiftedDerivativeCLM (fun i => star (C.θ i)) j z))
    simpa only [cellSourceFunctional, sub_apply, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Fin.sum_univ_two, Pi.add_def, Pi.sub_def] using h0.sub ((h1 0).add (h1 1))
  exact hgen.add hs

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! An almost strongly measurable scalar potential suffices for the actual Riesz derivative. -/

theorem cellDualDerivative_aestronglyMeasurable_aePotential {μ : Measure ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Homogenization.Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : AEStronglyMeasurable C.κ μ)
    (f : ℝ → TorusHk 1 ℂ) (hf : AEStronglyMeasurable f μ)
    (S : ℝ → ComplexCellL2) (hS : AEStronglyMeasurable S μ)
    (F : ℝ → Fin 2 → ComplexCellL2) (hF : ∀ j, AEStronglyMeasurable (fun t => F t j) μ) :
    AEStronglyMeasurable (fun t => cellDualDerivative C hG V hv hb t (f t) (S t) (F t)) μ := by
  let C' : CellCoefficients := { C with κ := hκ.mk C.κ }
  have hk' : Measurable C'.κ := hκ.stronglyMeasurable_mk.measurable
  have ha := cellDualDerivative_aestronglyMeasurable C' hG V hv hb hk' f hf S hS F hF
  apply ha.congr
  filter_upwards [hκ.ae_eq_mk] with t ht
  dsimp only [C']
  unfold cellDualDerivative cellGeneratorForm
  rw [ht]
  rfl

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! The weakly divergence-free drift form is energy neutral on every periodic H¹ class. -/

/-- The unshifted transport form on periodic H¹. -/
def cellDriftForm (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) :
    TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ :=
  ∑ j : Fin 2, pullbackInnerCLM
    ((cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv hb t j).comp (cellDerivativeCLM j)) torusHkValueCLM

/-- Finite Fourier approximants have zero transport energy, directly from weak divergence freedom. -/
theorem cellDriftForm_projection_zero {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) (N : ℕ) :
    cellDriftForm v V hv.1 hb t (galerkinProj N u) (galerkinProj N u) = 0 := by
  let p := galerkinProj N u
  let q := smoothFourierJet (L := 1) N u (valueIndex2 1)
  have hz := cellDrift_smooth_energy_zero hv t q (smoothFourierJet_contDiff N u _)
    (smoothFourierJet_periodic N u _)
  have hval : torusHkValueCLM p =ᵐ[volume.restrict AVenhance.unitCube] q :=
    galerkinProj_jet_ae_smooth N u (valueIndex2 1)
  have hgrad : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ j : Fin 2,
      cellDerivativeCLM j p x = smoothFourierJet (L := 1) N u ⟨⟨1, by decide⟩, fun _ => j⟩ x := by
    exact ae_all_iff.2 (fun j => galerkinProj_jet_ae_smooth N u ⟨⟨1, by decide⟩, fun _ => j⟩)
  have hi (j : Fin 2) := cellDrift_pairing_integrable ⟨0, v, 0, 0⟩ V hv.1 hb t j
    (cellDerivativeCLM j p) (torusHkValueCLM p)
  change (∑ j : Fin 2, inner ℝ
    (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j p))
    (torusHkValueCLM p)) = 0
  simp_rw [cellDrift_pairing_eq_integral]
  rw [← integral_finsetSum Finset.univ (fun j _ => hi j)]
  calc
    _ = (∫ x in AVenhance.unitCube, ∑ j : Fin 2,
      v t x j * inner ℝ (fderiv ℝ q x (basisVec j)) (q x)) := by
      apply integral_congr_ae
      filter_upwards [hval, hgrad] with x hx hd
      apply Finset.sum_congr rfl
      intro j _
      change ((v t x j : ℂ) * cellDerivativeCLM j p x * star (torusHkValueCLM p x)).re = _
      rw [hd j, hx]
      change ((v t x j : ℂ) * smoothFourierJet (L := 1) N u
        (nextIndex2 (0 : Fin 1) Fin.elim0 j) x * star (q x)).re = _
      have hder := smoothFourierJet_fderiv (L := 1) N u (0 : Fin 1) Fin.elim0 j x
      change fderiv ℝ q x (basisVec j) = _ at hder
      rw [hder, mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, ← cellComplexInner_eq]
    _ = 0 := hz

/-- The drift does no work on an arbitrary H¹ field; no smoothness of the drift is used. -/
theorem cellDriftForm_energy_zero {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellDriftForm v V hv.1 hb t u u = 0 := by
  let B := cellDriftForm v V hv.1 hb t
  have hp := galerkinProj_tendsto u
  have hc : Continuous (fun z : TorusHk 1 ℂ => B z z) := B.continuous.clm_apply continuous_id
  have hlim := hc.continuousAt.tendsto.comp hp
  have he : (fun N => B (galerkinProj N u) (galerkinProj N u)) = fun _ : ℕ => 0 := by
    funext N
    exact cellDriftForm_projection_zero hv V hb t u N
  change Tendsto (fun N => B (galerkinProj N u) (galerkinProj N u)) atTop (𝓝 (B u u)) at hlim
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Polarization of the proved divergence-free drift energy identity gives skew symmetry. -/

theorem cellDriftForm_skew {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellDriftForm v V hv.1 hb t u z = -cellDriftForm v V hv.1 hb t z u := by
  let B := cellDriftForm v V hv.1 hb t
  have hu : B u u = 0 := cellDriftForm_energy_zero hv V hb t u
  have hz : B z z = 0 := cellDriftForm_energy_zero hv V hb t z
  have hs : B (u + z) (u + z) = 0 := cellDriftForm_energy_zero hv V hb t (u + z)
  simp only [map_add, add_apply, hu, hz] at hs
  change B u z = -B z u
  linarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! The actual graph source equals the normalized scalar forcing in the Bloch equation. -/

local instance fibreGraphSourceNormalizedProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem fibreDriftCoupling_memLp (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    MemLp (fibreDriftCoupling η v ξ t) 2 (volume.restrict AVenhance.unitCube) := by
  have hm : Measurable (fibreDriftCoupling η v ξ t) := (fibreDriftCoupling_measurable η hv ξ).comp
    (measurable_const.prodMk measurable_id)
  exact MemLp.of_bound hm.aestronglyMeasurable (Cw * fibreNorm ξ)
    (Filter.Eventually.of_forall (fibreDriftCoupling_norm_le η Cw v hw ξ t))

theorem fibreGraphSource_normalized (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (ξ : Fin 2 → ℂ) (ρ : ℝ → Vec 2 → ℂ) (t : ℝ)
    (hρ : MemLp (ρ t) 2 (volume.restrict AVenhance.unitCube)) (x : Vec 2) :
    fibreGraphSource η v ξ ρ t x =
      -Complex.I * fibreDriftCoupling η v ξ t x * (1 + ρ t x) +
        Complex.I * cellMean (fun y => fibreDriftCoupling η v ξ t y * ρ t y) * (1 + ρ t x) := by
  exact cellGraphSource_scalar_identity (fibreDriftCoupling η v ξ t) (ρ t)
    (fibreDriftCoupling_memLp η Cw hv hw ξ t) hρ (fibreDriftCoupling_mean_zero η hv hm ξ t) x

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Integrable spatial energy production of the exact real Hilbert cell generator. -/

/-- Energy production written with representatives of shifted derivative classes. -/
def cellShiftedSpatialProduction (C : CellCoefficients) (t : ℝ) (u : TorusHk 1 ℂ)
    (src : ComplexCellL2) (F : Fin 2 → ComplexCellL2) (x : Vec 2) : ℝ :=
  -(∑ j : Fin 2, ∑ k : Fin 2, ((C.G t x j k : ℂ) *
    cellShiftedDerivativeCLM C.θ j u x *
      star (cellShiftedDerivativeCLM (fun i => star (C.θ i)) k u x)).re)
  - (∑ j : Fin 2, ((C.v t x j : ℂ) * cellShiftedDerivativeCLM C.θ j u x *
      star (torusHkValueCLM u x)).re)
  + (C.κ t * torusHkValueCLM u x * star (torusHkValueCLM u x)).re
  + (src x * star (torusHkValueCLM u x)).re
  - ∑ j : Fin 2, (F j x * star (cellShiftedDerivativeCLM (fun i => star (C.θ i)) j u x)).re

/-- The exact cell spatial production is genuinely integrable. -/
theorem cellShiftedSpatialProduction_integrable
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (src : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    Integrable (cellShiftedSpatialProduction C t u src F) (volume.restrict AVenhance.unitCube) := by
  have hm := integrable_finsetSum' Finset.univ (fun j _ =>
    integrable_finsetSum' Finset.univ (fun k _ => cellMetric_pairing_integrable hG t j k
      (cellShiftedDerivativeCLM C.θ j u) (cellShiftedDerivativeCLM (fun i => star (C.θ i)) k u)))
  have hd := integrable_finsetSum' Finset.univ (fun j _ => cellDrift_pairing_integrable C V hv hb t j
    (cellShiftedDerivativeCLM C.θ j u) (torusHkValueCLM u))
  have hp := cellScalar_pairing_integrable (C.κ t) (torusHkValueCLM u) (torusHkValueCLM u)
  have hs := cellPlain_pairing_integrable src (torusHkValueCLM u)
  have hf := integrable_finsetSum' Finset.univ (fun j _ => cellPlain_pairing_integrable (F j)
    (cellShiftedDerivativeCLM (fun i => star (C.θ i)) j u))
  unfold cellShiftedSpatialProduction
  simpa only [cellShiftedSpatialProduction, Finset.sum_fn, Pi.neg_def, Pi.sub_def, Pi.add_def]
    using ((hm.neg.sub hd).add hp).add hs |>.sub hf

/-- Shifted class representatives agree a.e. with the literal pointwise energy formula. -/
theorem cellShiftedSpatialProduction_ae (C : CellCoefficients) (t : ℝ) (u : TorusHk 1 ℂ)
    (src : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellShiftedSpatialProduction C t u src F =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => cellPointwiseProduction (C.G t x) (C.v t x) C.θ (C.κ t) (src x)
        (torusHkValueCLM u x) (fun j => F j x) (fun j => cellDerivativeCLM j u x) := by
  have hθ := (ae_all_iff.mpr (fun j => cellShiftedDerivativeCLM_ae C.θ j u))
  have hθ' := (ae_all_iff.mpr (fun j => cellShiftedDerivativeCLM_ae (fun i => star (C.θ i)) j u))
  filter_upwards [hθ, hθ'] with x hx hx'
  simp only [cellShiftedSpatialProduction, cellPointwiseProduction, cellMetricPairing,
    cellDriftPairing, cellFluxPairing, Fin.sum_univ_two, Complex.add_re, Pi.add_apply, cellBlochShift, hx, hx']

/-! Identify the actual Hilbert-form energy production with its spatial integral. -/

/-- The form energy production is the literal integral of the pointwise complex cell expression. -/
theorem cellGenerator_source_eq_integral
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (src : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellGeneratorForm C hG V hv hb t u u + cellSourceFunctional C.θ src F u =
      ∫ x in AVenhance.unitCube, cellShiftedSpatialProduction C t u src F x := by
  let m := fun j k x => ((C.G t x j k : ℂ) * cellShiftedDerivativeCLM C.θ j u x *
    star (cellShiftedDerivativeCLM (fun i => star (C.θ i)) k u x)).re
  let d := fun j x => ((C.v t x j : ℂ) * cellShiftedDerivativeCLM C.θ j u x *
    star (torusHkValueCLM u x)).re
  let p := fun x => (C.κ t * torusHkValueCLM u x * star (torusHkValueCLM u x)).re
  let s := fun x => (src x * star (torusHkValueCLM u x)).re
  let f := fun j x => (F j x * star (cellShiftedDerivativeCLM (fun i => star (C.θ i)) j u x)).re
  have hm (j k : Fin 2) : Integrable (m j k) (volume.restrict AVenhance.unitCube) :=
    cellMetric_pairing_integrable hG t j k _ _
  have hd (j : Fin 2) : Integrable (d j) (volume.restrict AVenhance.unitCube) :=
    cellDrift_pairing_integrable C V hv hb t j _ _
  have hp : Integrable p (volume.restrict AVenhance.unitCube) := cellScalar_pairing_integrable _ _ _
  have hs : Integrable s (volume.restrict AVenhance.unitCube) := cellPlain_pairing_integrable _ _
  have hf (j : Fin 2) : Integrable (f j) (volume.restrict AVenhance.unitCube) :=
    cellPlain_pairing_integrable _ _
  have hms (j : Fin 2) : Integrable (fun x => ∑ k : Fin 2, m j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun k _ => hm j k)
  have hmss : Integrable (fun x => ∑ j : Fin 2, ∑ k : Fin 2, m j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hms j)
  have hds : Integrable (fun x => ∑ j : Fin 2, d j x) (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hd j)
  have hfs : Integrable (fun x => ∑ j : Fin 2, f j x) (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hf j)
  have he : (∫ x in AVenhance.unitCube, cellShiftedSpatialProduction C t u src F x) =
      -(∑ j : Fin 2, ∑ k : Fin 2, ∫ x in AVenhance.unitCube, m j k x)
      - (∑ j : Fin 2, ∫ x in AVenhance.unitCube, d j x)
      + (∫ x in AVenhance.unitCube, p x) + (∫ x in AVenhance.unitCube, s x)
      - ∑ j : Fin 2, ∫ x in AVenhance.unitCube, f j x := by
    have h1 := integral_sub (((hmss.neg.sub hds).add hp).add hs) hfs
    have h2 := integral_add ((hmss.neg.sub hds).add hp) hs
    have h3 := integral_add (hmss.neg.sub hds) hp
    have h4 := integral_sub hmss.neg hds
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at h1 h2 h3 h4
    change (∫ x in AVenhance.unitCube,
      -(∑ j : Fin 2, ∑ k : Fin 2, m j k x) - (∑ j : Fin 2, d j x) + p x + s x -
        ∑ j : Fin 2, f j x) = _
    rw [h1, h2, h3, h4, integral_neg,
      integral_finsetSum Finset.univ (fun j _ => hms j),
      integral_finsetSum Finset.univ (fun j _ => hd j),
      integral_finsetSum Finset.univ (fun j _ => hf j)]
    simp_rw [integral_finsetSum Finset.univ (fun k _ => hm _ k)]
  rw [he]
  simp only [cellGeneratorForm, cellDiffusionForm, cellSourceFunctional, add_apply,
    sub_apply, neg_apply, sum_apply, pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  simp_rw [cellMetric_pairing_eq_integral, cellDrift_pairing_eq_integral,
    cellScalar_pairing_eq_integral, cellPlain_pairing_eq_integral]
  dsimp only [m, d, p, s, f]
  ring

/-! Integrated coercivity for the actual measurable complex cell form. -/

/-- The norm of a cell L² class is its literal representative square integral. -/
theorem cellL2_norm_sq_integral (u : ComplexCellL2) :
    (∫ x in AVenhance.unitCube, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
  have h := normSq_toLp_eq_integral (Lp.memLp u)
  rw [Lp.toLp_coeFn] at h
  exact h.symm

/-- Universal spatial energy estimate, with no regularity of the coefficients beyond measurability. -/
theorem cellGenerator_source_energy_bound
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : ∀ t, ‖C.κ t‖ ≤ k)
    (t : ℝ) (u : TorusHk 1 ℂ) (src : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    2 * (cellGeneratorForm C hG V hv hb t u u + cellSourceFunctional C.θ src F u) +
      (1 / 2) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤
      300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * ‖torusHkValueCLM u‖ ^ 2 +
        ‖src‖ ^ 2 + 9 * ∑ j, ‖F j‖ ^ 2 := by
  let P := cellShiftedSpatialProduction C t u src F
  let R := 300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k)
  have hP : Integrable P (volume.restrict AVenhance.unitCube) :=
    cellShiftedSpatialProduction_integrable C hG V hv hb t u src F
  have hd (j : Fin 2) := integrable_normSq_of_memLp (Lp.memLp (cellDerivativeCLM j u))
  have hds := integrable_finsetSum Finset.univ (fun j _ => hd j)
  have hu := integrable_normSq_of_memLp (Lp.memLp (torusHkValueCLM u))
  have hs := integrable_normSq_of_memLp (Lp.memLp src)
  have hf (j : Fin 2) := integrable_normSq_of_memLp (Lp.memLp (F j))
  have hfs := integrable_finsetSum Finset.univ (fun j _ => hf j)
  have hineq := integral_mono_ae ((hP.const_mul 2).add (hds.const_mul (1 / 2)))
    (((hu.const_mul R).add hs).add (hfs.const_mul 9)) (by
      filter_upwards [cellShiftedSpatialProduction_ae C t u src F] with x hx
      change 2 * P x + (1 / 2) * ∑ j, ‖cellDerivativeCLM j u x‖ ^ 2 ≤
        R * ‖torusHkValueCLM u x‖ ^ 2 + ‖src x‖ ^ 2 + 9 * ∑ j, ‖F j x‖ ^ 2
      dsimp only [P, R]
      rw [hx]
      exact cellPointwiseProduction_bound hG t x _ _ _ _ _ _ _ V k
        (fun j => cellDrift_entry_bound hb t x j) (hκ t))
  have hl := integral_add (hP.const_mul 2) (hds.const_mul (1 / 2))
  have hr := integral_add ((hu.const_mul R).add hs) (hfs.const_mul 9)
  have hr' := integral_add (hu.const_mul R) hs
  simp only [Pi.add_apply] at hineq hl hr hr'
  rw [hl, hr, hr'] at hineq
  simp only [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hd j),
    integral_finsetSum Finset.univ (fun j _ => hf j), cellL2_norm_sq_integral] at hineq
  rw [cellGenerator_source_eq_integral C hG V hv hb]
  exact hineq

end AVRegularity.CycleEvolution
end
end
