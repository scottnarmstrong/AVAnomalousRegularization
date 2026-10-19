-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PeriodizedCarrierRawReadout
import AVRegularity.CycleEvolution.FibreCoefficientConvolutionSum
public import AVRegularity.Weighted.GradientCarrierJet
import AVRegularity.CycleJoint.PreparationScaledFlowBudget
public import AVRegularity.CycleJoint.InactiveTimeZeroFamilyPointwiseEnvelope
public import AVRegularity.CycleJoint.CoefficientSeminormAddition
import AVRegularity.CoupledEnergyPlane.Variational.PrincipalMask

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A summable spatial majorant supplies every convergence premise of weak-jet periodization. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem spatialJet_majorant_summable (D : RawJet2 K E) (μ : Measure (Vec 2)) (C : ℝ)
    (hb : ∀ (n : Fin 2 → ℤ) (a : JetIndex2 K),
      eLpNorm (fun x => D a (x + AVenhance.latticeShift n)) 2 μ ≤
        ENNReal.ofReal (C * (1 / spatialLatticeWeight n) ^ 2)) :
    (∑' n : Fin 2 → ℤ, ∑ a : JetIndex2 K,
      eLpNorm (fun x => D a (x + AVenhance.latticeShift n)) 2 μ) < ⊤ := by
  have hs := (spatialLatticeReciprocal_square_summable.mul_left C).tsum_ofReal_lt_top
  have hsum (n : Fin 2 → ℤ) :
      (∑ a : JetIndex2 K, eLpNorm (fun x => D a (x + AVenhance.latticeShift n)) 2 μ) ≤
      (Fintype.card (JetIndex2 K) : ℝ≥0∞) * ENNReal.ofReal (C * (1 / spatialLatticeWeight n) ^ 2) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (JetIndex2 K))) => hb n a)
  refine (ENNReal.tsum_le_tsum hsum).trans_lt ?_
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top (by simp) hs

theorem periodizeRawJet_of_spatial_majorant (D : RawJet2 K E)
    (hw : HasOrderedWeakJetOn Set.univ D)
    (hb : ∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ (n : Fin 2 → ℤ) (a : JetIndex2 K),
      eLpNorm (fun x => D a (x + AVenhance.latticeShift n)) 2
        (volume.restrict (Metric.ball (0 : Vec 2) R)) ≤
        ENNReal.ofReal (C * (1 / spatialLatticeWeight n) ^ 2)) :
    HasPeriodicOrderedWeakJet (periodizeRawJet D) := by
  have hs (R : ℝ) (hR : 0 < R) :
      (∑' n : Fin 2 → ℤ, ∑ a : JetIndex2 K,
        eLpNorm (fun x => D a (x + AVenhance.latticeShift n)) 2
          (volume.restrict (Metric.ball (0 : Vec 2) R))) < ⊤ := by
    obtain ⟨C, hC⟩ := hb R hR
    exact spatialJet_majorant_summable D (volume.restrict (Metric.ball (0 : Vec 2) R)) C hC
  have hsub : AVenhance.unitCube ⊆ Metric.ball (0 : Vec 2) 2 := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    apply (pi_norm_lt_iff (by norm_num)).mpr
    intro i
    have hi := hx i (Set.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_pos hi.1]
    exact hi.2.trans (by norm_num)
  apply periodizeRawJet_hasPeriodicWeakJet D hw _ hs
  refine (ENNReal.tsum_le_tsum (fun n => Finset.sum_le_sum (fun a _ => ?_))).trans_lt (hs 2 (by norm_num))
  exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Fubini reads joint L2 energy from any prescribed Bochner spatial classes. -/

section
variable {T X E : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bochnerProduct_normSq_of_slices (μ : Measure T) (ν : Measure X)
    [SFinite μ] [SFinite ν] (f : T × X → E) (hf : MemLp f 2 (μ.prod ν))
    (u : T → Lp E 2 ν) (he : ∀ᵐ t ∂μ, (u t : X → E) =ᵐ[ν] fun x => f (t, x)) :
    ‖hf.toLp f‖ ^ 2 = ∫ t, ‖u t‖ ^ 2 ∂μ := by
  rw [CycleEvolution.cellL2_normSq_generic _ hf, integral_prod _ hf.norm.integrable_sq]
  apply integral_congr_ae
  filter_upwards [he] with t ht
  have hn : ‖u t‖ ^ 2 = ∫ x, ‖u t x‖ ^ 2 ∂ν := by
    simpa only [Lp.toLp_coeFn] using
      CycleEvolution.cellL2_normSq_generic (fun x => u t x) (Lp.memLp (u t))
  rw [hn]
  exact integral_congr_ae (ht.fun_comp (fun y => ‖y‖ ^ 2)).symm

theorem bochnerProduct_normSq (μ : Measure T) (ν : Measure X)
    [SFinite μ] [SFinite ν] (f : T × X → E) (hf : MemLp f 2 (μ.prod ν))
    (u : T → Lp E 2 ν) (hu : MemLp u 2 μ)
    (he : ∀ᵐ t ∂μ, (u t : X → E) =ᵐ[ν] fun x => f (t, x)) :
    ‖hf.toLp f‖ ^ 2 = ‖hu.toLp u‖ ^ 2 := by
  rw [bochnerProduct_normSq_of_slices μ ν f hf u he,
    CycleEvolution.cellL2_normSq_generic _ hu]
end

/-! Joint representatives preserve the exact Bochner L2 distance. -/

section
variable {T X E : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bochnerProduct_distance (μ : Measure T) (ν : Measure X)
    [SFinite μ] [SFinite ν] (f g : T × X → E)
    (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν))
    (u v : T → Lp E 2 ν) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (he : ∀ᵐ t ∂μ, (u t : X → E) =ᵐ[ν] fun x => f (t, x))
    (hev : ∀ᵐ t ∂μ, (v t : X → E) =ᵐ[ν] fun x => g (t, x)) :
    dist (hf.toLp f) (hg.toLp g) = dist (hu.toLp u) (hv.toLp v) := by
  have hd : ∀ᵐ t ∂μ, ((u t - v t : Lp E 2 ν) : X → E)
      =ᵐ[ν] fun x => f (t, x) - g (t, x) := by
    filter_upwards [he, hev] with t ht hvt
    filter_upwards [ht, hvt, Lp.coeFn_sub (u t) (v t)] with x hx hvx hs
    rw [hs]
    change u t x - v t x = f (t, x) - g (t, x)
    rw [hx, hvx]
  rw [dist_eq_norm, dist_eq_norm]
  apply CycleEvolution.cellNorm_eq_of_square_eq
  rw [← MemLp.toLp_sub hf hg, ← MemLp.toLp_sub hu hv]
  exact bochnerProduct_normSq μ ν (f - g) (hf.sub hg) (u - v) (hu.sub hv) hd
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Time integrability of the physical-viscosity weak dual on the actual time window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A bounded measurable interval drift and time-L² slice and flux give the viscous dual. -/
theorem planeViscousDual_memLp (a b : ℝ) (hab : a ≤ b) (ν : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (u : ℝ → PlaneHk Set.univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (hu : MemLp u 2 (volume.restrict (Set.Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => planeWeakDualRepresentative
      (planeIntervalTransport a b hab v hvc M hvb t)
      (ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) (u t) (F t))
      2 (volume.restrict (Set.Icc a b)) := by
  have hvj := planeIntervalCoefficient_measurable a b hab v hvm
  apply planeWeakDualRepresentative_memLp_of_operator_bounds
    (planeIntervalTransport a b hab v hvc M hvb)
    (fun _ => ν • ContinuousLinearMap.id ℝ (PlaneFluxL2 E))
    (Mt := 2 * max M 0) (Md := |ν|)
  · exact planeScalarTransport_stronglyMeasurable
      (planeIntervalCoefficient a b hab v)
      (planeIntervalVelocity_continuous a b hab v hvc)
      (fun k => (measurable_pi_apply k).comp hvj) (le_max_right M 0)
      (planeIntervalVelocity_bound a b hab v M hvb)
  · intro z
    exact stronglyMeasurable_const
  · exact mul_nonneg (by norm_num) (le_max_right M 0)
  · exact abs_nonneg ν
  · intro t
    exact planeScalarTransport_norm_le _ _ _ _
  · intro t
    apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg ν)
    intro z
    simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs]
    exact le_rfl
  · exact hu
  · exact hF

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The exact centred natural flow in cell coordinates retains each original source anchor. -/

def naturalPreparationCellFlow {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e : ℝ) (yc z : Vec 2) : Vec 2 :=
  e⁻¹ • (streamFlow φ hφ r (yc + e • z) σ - streamFlow φ hφ r yc σ)

theorem naturalPreparationCellFlow_smooth {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e : ℝ) (yc : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (naturalPreparationCellFlow hφ r σ e yc) := by
  have haff : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec 2 => yc + e • z) :=
    contDiff_const.add (contDiff_id.const_smul e)
  exact (((streamFlow_spatial_smooth hφ r σ).comp haff).sub contDiff_const).const_smul (e⁻¹ : ℝ)

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparationCellFlow_norm_le
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (e : ℝ) (he : 0 < e) (yc z : Vec 2) :
    ‖naturalPreparationCellFlow hφ r σ e yc z‖ ≤ (1 + max (Cchart 0) 0 / 2) * ‖z‖ := by
  unfold naturalPreparationCellFlow
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr he.le)]
  have hh := mul_le_mul_of_nonneg_left
    (preparation_natural_flow_cell_displacement_le hc ha r σ hr hσ hage yc z e)
    (inv_nonneg.mpr he.le)
  rw [abs_of_pos he] at hh
  apply hh.trans_eq
  calc
    _ = (1 + max (Cchart 0) 0 / 2) * (e⁻¹ * e) * ‖z‖ := by ring
    _ = _ := by rw [inv_mul_cancel₀ he.ne', mul_one]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every native transition factor of a smooth spatial matrix is smooth. -/

theorem transitionT_spatial_smooth
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (I A : List (Fin 2)) : ContDiff ℝ (⊤ : ℕ∞) (transitionT K I A) := by
  have hj := transitionT_joint_smooth (fun _ => K)
    (fun i j => (hK i j).comp contDiff_snd) I A
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => ((0 : ℝ), x)) :=
    contDiff_const.prodMk contDiff_id
  exact hj.comp he

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The model predicate's order-zero factorial norm is the actual L2 carrier norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem factorialNormSq_order_zero_measure (μ : Measure (Vec 2)) (ρ : ℝ) (D : JetL2 μ 0 E) :
    factorialNormSq ρ D = ‖D‖ ^ 2 := by
  rw [factorialNormSq, Fin.sum_univ_succ]
  simp only [Fin.val_zero, factorialWeight, Nat.mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_pow, div_one, one_mul, Fin.sum_univ_zero, add_zero,
    derivativeNormSq_zero_eq_value, zeroOrderJet_norm_sq]

theorem torusHkNorm_order_zero {L : ℕ} (ρ : ℝ) (f : TorusHk L E) :
    torusHkNorm ρ (Nat.zero_le L) f = ‖truncateTorusHk (Nat.zero_le L) f‖ := by
  unfold torusHkNorm
  rw [factorialNormSq_order_zero_measure, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (norm_nonneg _)

theorem torusHkNorm_zero_input (ρ : ℝ) (f : TorusHk 0 E) :
    torusHkNorm ρ (le_refl 0) f = ‖f‖ := by
  have he : truncateTorusHk (le_refl 0) f = f := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    rfl
  rw [torusHkNorm_order_zero, he]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Exact ordered coefficient supremum prices under affine space and positive time scaling. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iSup_plane_affine {L : Type*} [CompleteLattice L] (e : ℝ) (he : e ≠ 0)
    (y : Vec 2) (f : Vec 2 → L) : (⨆ z, f (y + e • z)) = ⨆ x, f x := by
  have hs : Function.Surjective (fun z : Vec 2 => y + e • z) := by
    intro x
    refine ⟨e⁻¹ • (x - y), ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ he, one_smul, add_sub_cancel]
  exact hs.iSup_comp f

theorem coefficientOrderSup_affine_time (a b ν : ℝ) (hν : 0 < ν)
    (c e : ℝ) (he : e ≠ 0) (y : Vec 2) (A : ℝ → Vec 2 → E →L[ℝ] F) (j : ℕ) :
    coefficientOrderSup (ν * a) (ν * b) (fun t z => c • A (ν⁻¹ * t) (y + e • z)) j =
      ENNReal.ofReal (‖c‖ * ‖e ^ j‖) * coefficientOrderSup a b A j := by
  have hnorm (t : ℝ) (z : Vec 2) :
      (‖coefficientDerivativeArray (fun x => c • A (ν⁻¹ * t) (y + e • x)) j z‖₊ : ℝ≥0∞) =
      ENNReal.ofReal (‖c‖ * ‖e ^ j‖) *
        (‖coefficientDerivativeArray (A (ν⁻¹ * t)) j (y + e • z)‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, coefficientDerivativeArray_const_smul,
      coefficientDerivativeArray_affine, norm_smul, norm_smul, ← mul_assoc,
      ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      ← ENNReal.ofReal_coe_nnreal]
    rfl
  have hspace (t : ℝ) :
      (⨆ z : Vec 2, (‖coefficientDerivativeArray (A (ν⁻¹ * t)) j (y + e • z)‖₊ : ℝ≥0∞)) =
      ⨆ x : Vec 2, (‖coefficientDerivativeArray (A (ν⁻¹ * t)) j x‖₊ : ℝ≥0∞) :=
    iSup_plane_affine e he y (fun x => (‖coefficientDerivativeArray (A (ν⁻¹ * t)) j x‖₊ : ℝ≥0∞))
  unfold coefficientOrderSup
  simp_rw [hnorm, ← ENNReal.mul_iSup]
  congr 1
  simp_rw [hspace]
  exact iSup_comp_inv_mul_Icc ν a b hν
    (fun t => ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞))

end AVRegularity.CycleJointProofs
end

section
namespace AVRegularity.CycleJointProofs

/-! All finite source degrees assemble with a component-independent inverse-mass budget. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourcePathPolynomial (A : Matrix ι ι ℝ) (s : Finset ℕ) : Matrix ι ι ℝ :=
  fun v u => ∑ n ∈ s, (A ^ n) v u

theorem sourcePathPolynomial_nonneg (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (s : Finset ℕ) (v u : ι) : 0 ≤ sourcePathPolynomial A s v u :=
  Finset.sum_nonneg (fun n _ => positiveMatrix_pow_nonneg A hA n v u)

theorem massSourcePolynomial_row (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (θ : ℝ) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ θ) (s : Finset ℕ) (v : ι) :
    ∑ u, massConjugatedMatrix π (sourcePathPolynomial A s) v u ≤ ∑ n ∈ s, θ ^ n := by
  simp only [massConjugatedMatrix, sourcePathPolynomial, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun n _ => massMatrix_pow_row_sum π hπ A hA θ hθ hrow n v)

theorem massSourcePolynomial_col (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (θ : ℝ) (hθ : 0 ≤ θ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ θ) (s : Finset ℕ) (u : ι) :
    ∑ v, massConjugatedMatrix π (sourcePathPolynomial A s) v u ≤ ∑ n ∈ s, θ ^ n := by
  simp only [massConjugatedMatrix, sourcePathPolynomial, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun n _ => massMatrix_pow_col_sum π hπ A hA θ hθ hcol n u)

theorem massSourcePolynomial_operator_bound
    {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ)
    (hA : ∀ v u, 0 ≤ A v u) (C θ : ℝ) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ θ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ θ)
    (s : Finset ℕ) (T : ℕ → ∀ v u, E u → F v)
    (hT : ∀ n ∈ s, ∀ v u f, ‖T n v u f‖ ≤ C * (A ^ n) v u * ‖f‖)
    (f : ∀ u, E u) :
    (∑ v, (π v)⁻¹ * ‖∑ u, ∑ n ∈ s, T n v u (f u)‖ ^ 2) ≤
      (C * ∑ n ∈ s, θ ^ n) ^ 2 * ∑ u, (π u)⁻¹ * ‖f u‖ ^ 2 := by
  have hblock (v u : ι) (z : E u) :
      ‖∑ n ∈ s, T n v u z‖ ≤ C * sourcePathPolynomial A s v u * ‖z‖ := by
    calc
      ‖∑ n ∈ s, T n v u z‖ ≤ ∑ n ∈ s, ‖T n v u z‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ s, C * (A ^ n) v u * ‖z‖ := Finset.sum_le_sum (fun n hn => hT n hn v u z)
      _ = C * sourcePathPolynomial A s v u * ‖z‖ := by
        simp only [sourcePathPolynomial, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact massBlockSchur_norm_sq π hπ (sourcePathPolynomial A s)
    (sourcePathPolynomial_nonneg A hA s) C (∑ n ∈ s, θ ^ n) hC
    (massSourcePolynomial_row π hπ A hA θ hθ hrow s)
    (massSourcePolynomial_col π hπ A hA θ hθ hcol s)
    (fun v u z => ∑ n ∈ s, T n v u z) hblock f

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! Exact slow and fast coordinates for the natural cell map. -/

variable {φ : ℝ → Vec 2 → ℝ}

theorem naturalPreparationCellFlow_reconstruction (hφ : IsAdmissibleStream φ)
    (r σ e : ℝ) (he : e ≠ 0) (yc z : Vec 2) :
    streamFlow φ hφ r (yc + e • z) σ = streamFlow φ hφ r yc σ +
      e • naturalPreparationCellFlow hφ r σ e yc z := by
  simp only [naturalPreparationCellFlow, smul_smul, mul_inv_cancel₀ he, one_smul]
  abel

theorem naturalPreparationCellFlow_fast_coordinates (hφ : IsAdmissibleStream φ)
    (r σ e : ℝ) (he : e ≠ 0) (yc z : Vec 2) :
    e⁻¹ • streamFlow φ hφ r (yc + e • z) σ =
      e⁻¹ • streamFlow φ hφ r yc σ + naturalPreparationCellFlow hφ r σ e yc z := by
  rw [naturalPreparationCellFlow_reconstruction hφ r σ e he yc z, smul_add, smul_smul,
    inv_mul_cancel₀ he, one_smul]

theorem naturalPreparationCellFlow_slow_coordinates (hφ : IsAdmissibleStream φ)
    (r σ e E : ℝ) (he : e ≠ 0) (yc z : Vec 2) :
    E⁻¹ • streamFlow φ hφ r (yc + e • z) σ =
      E⁻¹ • streamFlow φ hφ r yc σ + (e / E) • naturalPreparationCellFlow hφ r σ e yc z := by
  rw [naturalPreparationCellFlow_reconstruction hφ r σ e he yc z, smul_add, smul_smul]
  congr 1
  congr 1
  ring

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Spatial cell dilation transfers the complete integrated weak identity, retaining all integrability clauses. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_affine (ν a t e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (h : CoupledWeakIdentity volume ν a t v u f φ dφ du flux F g) :
    CoupledWeakIdentity volume (ν * (e⁻¹) ^ 2) a t
      (fun r z => e⁻¹ • v r (y + e • z))
      (fun z => u (y + e • z)) (fun z => f (y + e • z))
      (fun z => φ (y + e • z)) (fun k z => e • dφ k (y + e • z))
      (fun r k z => e • du r k (y + e • z))
      (fun r z => e⁻¹ • flux r (y + e • z))
      (fun r z => e⁻¹ • F r (y + e • z)) (fun r z => g r (y + e • z)) := by
  let R := planeWeakSpatialRhs ν v φ dφ du flux F g
  let N := planeWeakSpatialRhs (ν * (e⁻¹) ^ 2) (fun r z => e⁻¹ • v r (y + e • z))
    (fun z => φ (y + e • z)) (fun k z => e • dφ k (y + e • z))
    (fun r k z => e • du r k (y + e • z))
    (fun r z => e⁻¹ • flux r (y + e • z))
    (fun r z => e⁻¹ • F r (y + e • z)) (fun r z => g r (y + e • z))
  have hn (r : ℝ) : N r = fun z => R r (y + e • z) :=
    funext (planeWeakSpatialRhs_affine ν e he y v φ dφ du flux F g r)
  have hi (r : ℝ) : (∫ z : Vec 2, N r z) = |(e ^ 2)⁻¹| * ∫ x : Vec 2, R r x := by
    rw [hn]
    exact integral_plane_affine e he y (R r)
  change Integrable _ volume ∧ Integrable _ volume ∧
    (∀ r ∈ Set.Ioc a t, Integrable (N r) volume) ∧
    IntegrableOn (fun r => ∫ z, N r z) (Set.Ioc a t) ∧ _
  refine ⟨integrable_plane_affine h.1 e he y,
    integrable_plane_affine h.2.1 e he y, ?_, ?_, ?_⟩
  · intro r hr
    rw [hn]
    exact integrable_plane_affine (h.2.2.1 r hr) e he y
  · simp_rw [hi]
    exact h.2.2.2.1.const_mul |(e ^ 2)⁻¹|
  · change (∫ z : Vec 2, inner ℝ (u (y + e • z)) (φ (y + e • z))) -
      (∫ z : Vec 2, inner ℝ (f (y + e • z)) (φ (y + e • z))) =
        ∫ r in Set.Ioc a t, ∫ z : Vec 2, N r z
    rw [integral_plane_affine e he y (fun x => inner ℝ (u x) (φ x)),
      integral_plane_affine e he y (fun x => inner ℝ (f x) (φ x))]
    simp_rw [hi]
    simp only [smul_eq_mul]
    rw [← mul_sub, h.2.2.2.2, integral_const_mul]
    rfl

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The coupled solution class restarts from its full physical trace on a later subwindow. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_restart_subwindow (K : ι → ℕ) (D : ℕ)
    (ν a b c d : ℝ) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν c d v D K A (fun i => u i c) F g u w := by
  have hsub : Set.Icc c d ⊆ Set.Icc a b := by
    intro t ht
    exact ⟨hac.trans ht.1, ht.2.trans hdb⟩
  refine ⟨fun i => (hs.1 i).mono hsub,
    fun i => MemLp.mono_measure (Measure.restrict_mono_set volume hsub) (hs.2.1 i),
    fun i => ae_restrict_of_ae_restrict_of_subset hsub (hs.2.2.1 i), fun _ => rfl, ?_⟩
  intro i t ht φ
  apply coupledWeakIdentity_restart (a := a) (hac := hac) (hct := ht.1)
  · exact hs.2.2.2.2 i c ⟨hac, hcd.trans hdb⟩ φ
  · exact hs.2.2.2.2 i t (hsub ht) φ
end

/-! The genuine finite-moment domain is linear, with no additional analytic assumptions. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem HasRadialPlaneMoments.add {f g : PlaneHk Set.univ K E} {z : Vec 2}
    (hf : HasRadialPlaneMoments f z) (hg : HasRadialPlaneMoments g z) :
    HasRadialPlaneMoments (f + g) z := by
  intro a
  apply ((hf a).add (hg a)).ae_eq
  filter_upwards [planeCarrier_jet_add_ae f g a] with x hx
  simp only [Pi.add_apply, hx, smul_add]

theorem HasRadialPlaneMoments.smul {f : PlaneHk Set.univ K E} {z : Vec 2}
    (hf : HasRadialPlaneMoments f z) (c : ℝ) : HasRadialPlaneMoments (c • f) z := by
  intro a
  apply ((hf a).const_smul c).ae_eq
  filter_upwards [planeCarrier_jet_smul_ae c f a] with x hx
  simp only [Pi.smul_apply, hx, smul_smul, mul_comm]

def radialPlaneMomentSubmodule (K : ℕ) (z : Vec 2) : Submodule ℝ (PlaneHk Set.univ K E) where
  carrier := {f | HasRadialPlaneMoments f z}
  zero_mem' := fun a => zeroPlaneJet_weight_memLp (fun y => (1 + ‖y - z‖) ^ 4) a
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.smul c
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Positive lowered constituent budgets assemble into the literal sampled envelope. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem sampled_envelope_of_lowering_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain) (actual : ∀ p, Ctx p)
    (a z ν e E ρ C : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hE : 0 < E)
    (hρE : ρ ≤ E) (hC : 0 ≤ C) (Cm : ℕ → ℝ) (Jm : ℕ) (b : ι → ι → ℝ)
    (hb : ∀ v u, 0 ≤ b v u)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ Cm Jm b)
    (hs : ∀ v u (γ : F.Γ v u) d, ∀ t ∈ Set.Icc a z,
      ContDiff ℝ (K v : ℕ) (constituentPhysical F ν e E actual v u γ d t))
    (hbudget : ∀ v u (γ : F.Γ v u) dout, dout ∈ Finset.Icc 2 D →
      coefficientSeminorm ρ (K v) a z (constituentPhysical F ν e E actual v u γ dout) ≤
        ENNReal.ofReal (‖(F.identity v u γ).map‖ * C *
          (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
            ∑ I : DerivativeWord2 (din - 1), E⁻¹ ^ (din - dout) *
              (pointwiseMolecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
                (fun x => F.dimFlux ν e E x.1 x.2 v u γ din I)).toReal))) :
    IsSampledEnvelope F π K actual a z ν e E ρ (C * D * |Cm 0|) b := by
  refine ⟨hs, ?_⟩
  intro v u
  let M := fun (γ : F.Γ v u) din (I : DerivativeWord2 (din - 1)) =>
    pointwiseMolecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ din I)
  let T := fun γ : F.Γ v u => ∑ din ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (din - 1), molecularRealPrice ν ρ (K v) (din - 2) (M γ din I)
  have hT γ : 0 ≤ T γ := by
    apply Finset.sum_nonneg
    intro din _
    apply Finset.sum_nonneg
    intro I _
    exact molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _
  have hterm γ := positive_lowered_seminorm_budget ν ρ E ‖(F.identity v u γ).map‖ C
    hν hρ hE hρE (norm_nonneg _) hC (K v) D (F.identity v u γ).maxOrder (M γ)
    (fun dout => coefficientSeminorm ρ (K v) a z
      (constituentPhysical F ν e E actual v u γ dout)) (hbudget v u γ)
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun γ _ => hterm γ)) zero_le).trans
  rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hC) (Nat.cast_nonneg D)) (hT γ)),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hh := pointwiseMolecularRealEnvelope_sum_le F π K dom ν e E ρ hν hE hρ
    Cm Jm b henv v u (hb v u) 0 (Nat.zero_le _)
  simp only [pow_zero, inv_one, mul_one] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hC (Nat.cast_nonneg D))
  have he : (∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ * C * D * T γ) =
      (C * D) * (∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ * T γ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    ring
  rw [he]
  convert hh' using 1 <;> ring

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Joint measurability and scalar linearity of the native Piola array. -/

theorem transportedCoeff_smul_native
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (w : ℝ)
    (r : ℕ) (A : DerivativeWord2 r) (y : Vec 2) :
    transportedCoeff K Dγ (fun d I => w • B d I) r A y =
      w • transportedCoeff K Dγ B r A y := by
  funext a
  simp only [transportedCoeff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem transportedCoeff_joint_measurable
    (tS tZ : ℝ) (K : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => K z.1 z.2 i j))
    (Dγ : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Set.Icc tS tZ × Vec 2 → Vec 2)
    (hB : ∀ d I i, Measurable (fun z => B d I z i))
    (r : ℕ) (A : DerivativeWord2 r) (a : Fin 2) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
      transportedCoeff (K z.1) Dγ (fun d I => B d I z) r A z.2 a) := by
  have hm : Measurable (fun z : Set.Icc tS tZ × Vec 2 => ((z.1 : ℝ), z.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  unfold transportedCoeff
  apply Finset.measurable_sum
  intro d hd
  apply Finset.measurable_sum
  intro I hI
  apply Finset.measurable_sum
  intro i hi
  exact (((hK a i).continuous.measurable.comp hm).mul (hB d I i)).mul
    ((transitionT_joint_smooth K hK (List.ofFn I) (List.ofFn A)).continuous.measurable.comp hm)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Spatial cell dilation preserves the genuine weak derivative identities, with one scale factor per derivative. -/

theorem weakPartialDeriv_affine {i : Fin 2} {u g : Vec 2 → ℝ}
    (h : HasWeakPartialDerivOn Set.univ i u g) (e : ℝ) (he : e ≠ 0) (y : Vec 2) :
    HasWeakPartialDerivOn Set.univ i (fun z => u (y + e • z))
      (fun z => e * g (y + e • z)) := by
  intro φ hφ hc _
  let ψ : Vec 2 → ℝ := fun x => φ (e⁻¹ • (x - y))
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.comp ((contDiff_id.sub contDiff_const).const_smul e⁻¹)
  have hcψ : HasCompactSupport ψ :=
    hc.comp_homeomorph (CycleWords.cellAffineHomeomorph e he y).symm
  have hid (z : Vec 2) : e⁻¹ • (y + e • z - y) = z := by
    simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ he, one_smul]
  have hval (z : Vec 2) : ψ (y + e • z) = φ z := congrArg φ (hid z)
  have hder (z : Vec 2) :
      fderiv ℝ ψ (y + e • z) (basisVec i) = e⁻¹ * fderiv ℝ φ z (basisVec i) := by
    have hd := ((hφ.differentiable (by norm_num))
      (e⁻¹ • (y + e • z - y))).hasFDerivAt.comp (y + e • z)
        (((hasFDerivAt_id (y + e • z)).sub_const y).const_smul e⁻¹)
    have hd' : fderiv ℝ ψ (y + e • z) =
        (fderiv ℝ φ (e⁻¹ • (y + e • z - y))).comp
          (e⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)) := hd.fderiv
    rw [hd']
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, hid]
  have hold := h ψ hψ hcψ (Set.subset_univ _)
  simp only [Measure.restrict_univ] at hold ⊢
  have hl := integral_plane_affine e he y
    (fun x => u x * fderiv ℝ ψ x (basisVec i))
  have hr := integral_plane_affine e he y (fun x => g x * ψ x)
  have hleft : (∫ z : Vec 2, u (y + e • z) * fderiv ℝ φ z (basisVec i)) =
      e * ∫ z : Vec 2, u (y + e • z) * fderiv ℝ ψ (y + e • z) (basisVec i) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    rw [hder]
    field_simp
  rw [hleft, hl, hold]
  simp only [smul_eq_mul] at hr ⊢
  simp_rw [hval] at hr
  simp_rw [mul_assoc e (g (y + e • _))]
  rw [integral_const_mul, hr]
  ring

theorem orderedWeakJet_affine {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : ℕ} {D : RawJet2 K E}
    (h : HasOrderedWeakJetOn Set.univ D) (e : ℝ) (he : e ≠ 0) (y : Vec 2) :
    HasOrderedWeakJetOn Set.univ (fun a z => e ^ a.1.val • D a (y + e • z)) := by
  intro j w i v
  have hh := weakPartialDeriv_affine (h j w i (e ^ j.val • v)) e he y
  convert hh using 1 <;>
    funext z <;>
    simp only [lowerIndex2, lowerIndex, nextIndex2, nextIndex,
      real_inner_smul_right, real_inner_smul_left, pow_succ];
    ring

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Coefficient factorial seminorms have an exact cell price, with no smoothness or finiteness hypothesis. -/

theorem factorialRootWeight_affine (ρ e : ℝ) (he : 0 < e) (j : ℕ) :
    factorialRootWeight (ρ / e) j * ‖e ^ j‖ = factorialRootWeight ρ j := by
  unfold factorialRootWeight
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg he.le _), div_pow]
  field_simp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientSeminorm_affine_time_price (ρ : ℝ) (hρ : 0 ≤ ρ) (K : ℕ)
    (a b ν : ℝ) (hν : 0 < ν) (c e : ℝ) (he : 0 < e) (y : Vec 2)
    (A : ℝ → Vec 2 → E →L[ℝ] F) :
    coefficientSeminorm (ρ / e) K (ν * a) (ν * b)
      (fun t z => c • A (ν⁻¹ * t) (y + e • z)) =
      ENNReal.ofReal ‖c‖ * coefficientSeminorm ρ K a b A := by
  change (∑ j ∈ Finset.range (K + 1),
    ENNReal.ofReal (factorialRootWeight (ρ / e) j) *
      coefficientOrderSup (ν * a) (ν * b) (fun t z => c • A (ν⁻¹ * t) (y + e • z)) j) =
    ENNReal.ofReal ‖c‖ * ∑ j ∈ Finset.range (K + 1),
      ENNReal.ofReal (factorialRootWeight ρ j) * coefficientOrderSup a b A j
  simp_rw [coefficientOrderSup_affine_time a b ν hν c e he.ne' y A]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hw : 0 ≤ factorialRootWeight (ρ / e) j := by
    unfold factorialRootWeight
    positivity
  have hr : factorialRootWeight (ρ / e) j * (‖c‖ * ‖e ^ j‖) =
      ‖c‖ * factorialRootWeight ρ j := by
    calc
      _ = ‖c‖ * (factorialRootWeight (ρ / e) j * ‖e ^ j‖) := by ring
      _ = _ := by rw [factorialRootWeight_affine ρ e he j]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hw, hr,
    ENNReal.ofReal_mul (norm_nonneg c), mul_assoc]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! The inverse affine test makes the spatial weak transfer usable against arbitrary cell tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_affine_inverse_test (ν a t e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (h : CoupledWeakIdentity volume ν a t v u f
      (fun x => φ (e⁻¹ • (x - y))) (fun k x => e⁻¹ • dφ k (e⁻¹ • (x - y))) du flux F g) :
    CoupledWeakIdentity volume (ν * (e⁻¹) ^ 2) a t
      (fun r z => e⁻¹ • v r (y + e • z))
      (fun z => u (y + e • z)) (fun z => f (y + e • z)) φ dφ
      (fun r k z => e • du r k (y + e • z))
      (fun r z => e⁻¹ • flux r (y + e • z))
      (fun r z => e⁻¹ • F r (y + e • z)) (fun r z => g r (y + e • z)) := by
  have hid (z : Vec 2) : e⁻¹ • (y + e • z - y) = z := by
    simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ he, one_smul]
  simpa only [hid, smul_smul, mul_inv_cancel₀ he, one_smul] using
    coupledWeakIdentity_affine ν a t e he y v u f
      (fun x => φ (e⁻¹ • (x - y))) (fun k x => e⁻¹ • dφ k (e⁻¹ • (x - y))) du flux F g h

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Finite native transport preserves every spatial smoothness reserve. -/

theorem transportedCoeff_spatial_smooth
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (Dγ n : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B d I x i))
    (r : ℕ) (A : DerivativeWord2 r) (a : Fin 2) :
    ContDiff ℝ (n : ℕ) (fun x =>
      transportedCoeff K Dγ (fun d I => B d I x) r A x a) := by
  have hT (I' A' : List (Fin 2)) :
      ContDiff ℝ (⊤ : ℕ∞) (transitionT K I' A') := by
    have hj := transitionT_joint_smooth (fun _ => K)
      (fun i j => (hK i j).comp contDiff_snd) I' A'
    have he : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => ((0 : ℝ), x)) :=
      contDiff_const.prodMk contDiff_id
    exact hj.comp he
  unfold transportedCoeff
  apply ContDiff.sum
  intro d hd
  apply ContDiff.sum
  intro I hI
  apply ContDiff.sum
  intro i hi
  exact (((hK a i).of_le (by simp)).mul (hB d I i)).mul
    ((hT (List.ofFn I) (List.ofFn A)).of_le (by simp))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.CycleJointProofs

/-! Identity diffusion contributes no internal scalar-chain coupling. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The one-level scalar chain with identity diffusion has the literal zero coefficient array. -/
theorem planeChainCoefficient_identity (κ : Fin 1 → ι → ℕ)
    (i i' : Fin 1 × ι) (d : admissibleOrders (fun p => κ p.1 p.2) 2 i i')
    (t : ℝ) (z : Vec 2) :
    planeChainCoefficient
      (geometryScalarData (h := h) 2 (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      κ i i' d t z = 0 := by
  have hz {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1) :
      metricFlux (h := h) (0 : Matrix (Fin 2) (Fin 2) ℝ) m hab hm = 0 := by
    subst hab hm
    ext q k
    simp [metricFlux]
  have hsame : i.1 = i'.1 := Subsingleton.elim _ _
  simp [planeChainCoefficient, geometryScalarData, hsame, slowEvalCoefficient, hz]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Spatial cell coordinates act on actual rough native Sobolev carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

def planeCarrierAffineFunction (e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (U : PlaneHk Set.univ K E) : PlaneHkFunction Set.univ K E where
  jet := fun a z => e ^ a.1.val • U.toFunction.jet a (y + e • z)
  memL2 := by
    intro a
    simp only [Measure.restrict_univ]
    have hm := U.toFunction.memL2 a
    simp only [Measure.restrict_univ] at hm
    exact (memLp_plane_affine hm e he y).const_smul (e ^ a.1.val)
  hasWeakJet := orderedWeakJet_affine U.toFunction.hasWeakJet e he y

def planeCarrierAffine (e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (U : PlaneHk Set.univ K E) : PlaneHk Set.univ K E :=
  (planeCarrierAffineFunction e he y U).toHk

theorem planeCarrierAffine_jet_ae (e : ℝ) (he : e ≠ 0) (y : Vec 2)
    (U : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (planeCarrierAffine e he y U).toFunction.jet a =ᵐ[volume]
      fun z => e ^ a.1.val • U.toFunction.jet a (y + e • z) := by
  simpa only [Measure.restrict_univ, planeCarrierAffine, planeCarrierAffineFunction] using
    (planeCarrierAffineFunction e he y U).toHk_toFunction_ae a

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Molecular dimensional envelopes imply literal normalized cell mixed-jet budgets. -/

theorem pointwiseMolecularNative_mixed_reserve {ι : Type*}
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (K d j a b : ℕ) (hab : a + b ≤ K) (dom : ι → Set (ℝ × Vec 2))
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) (i : ι)
    (hf : ∀ t, (∀ Y : Vec 2, (t, Y) ∈ dom i) → IsBoxSmooth (j + a) b (f i t))
    (hM : pointwiseMolecularJet ρ e K j dom
      (fun i t Y z => (ν * e ^ d) • f i t (E⁻¹ • Y) z) ≠ ⊤) :
    ∀ t : ℝ, (∀ Y : Vec 2, (t, Y) ∈ dom i) → ∀ X z,
      (ρ / e) ^ (a + b) * (e / E) ^ a *
        ‖iteratedFDeriv ℝ (j + a) (fun X' => iteratedFDeriv ℝ b (f i t X') z) X‖ *
          derivativeReserveFactor (ρ / e) K d ≤
        ((a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j /
          ((ν * ρ ^ d) * ((K.factorial : ℝ) / ((K + d).factorial : ℝ)))) *
          (pointwiseMolecularJet ρ e K j dom
            (fun i t Y z => (ν * e ^ d) • f i t (E⁻¹ • Y) z)).toReal := by
  intro t hdom X z
  apply CycleWords.molecular_normalized_reserve_le ν e E ρ hν he hE hρ K d j a b
    (hf t hdom) X z
  have hh := pointwiseMolecularJet_real_term ρ e hρ.le he K j dom
    (fun i t Y z => (ν * e ^ d) • f i t (E⁻¹ • Y) z) hM i a b hab
      t (E • X) (hdom (E • X)) z
  rw [Nat.add_comm a j] at hh
  exact hh

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Exact homogeneous scaling of every native order-lowering transition factor. -/

theorem transitionT_spatial_rescaling
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (E : ℝ) (hE : 0 < E) (I A : List (Fin 2)) (x : Vec 2) :
    transitionT (fun y => K (E • y)) I A x =
      E ^ ((I.length : ℤ) - (A.length : ℤ)) * transitionT K I A (E • x) := by
  induction I generalizing A x with
  | nil =>
    cases A <;> simp [transitionT]
  | cons i I ih =>
    cases A with
    | nil =>
      rw [transitionT_empty_output_nonempty_native, transitionT_empty_output_nonempty_native]
      simp
    | cons a A =>
      have hIfun : transitionT (fun y => K (E • y)) I (a :: A) =
          (fun y => E ^ ((I.length : ℤ) - ((a :: A).length : ℤ)) *
            transitionT K I (a :: A) (E • y)) := funext (ih (a :: A))
      have hpow : E ^ ((I.length : ℤ) - ((a :: A).length : ℤ)) * E =
          E ^ (((i :: I).length : ℤ) - ((a :: A).length : ℤ)) := by
        conv_lhs => arg 2; rw [← zpow_one E]
        rw [← zpow_add₀ hE.ne']
        congr 1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring
      have hpowA : E ^ ((I.length : ℤ) - (A.length : ℤ)) =
          E ^ (((i :: I).length : ℤ) - ((a :: A).length : ℤ)) := by
        congr 1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring
      change (∑ b : Fin 2, K (E • x) b i *
        fderiv ℝ (transitionT (fun y => K (E • y)) I (a :: A)) x (basisVec b)) +
          K (E • x) a i * transitionT (fun y => K (E • y)) I A x =
        E ^ (((i :: I).length : ℤ) - ((a :: A).length : ℤ)) *
          ((∑ b : Fin 2, K (E • x) b i *
            fderiv ℝ (transitionT K I (a :: A)) (E • x) (basisVec b)) +
              K (E • x) a i * transitionT K I A (E • x))
      rw [hIfun, ih A x, hpowA, mul_add, Finset.mul_sum]
      have hd := (transitionT_spatial_smooth K hK I (a :: A)).differentiable (by simp)
      have hs : (∑ b : Fin 2, K (E • x) b i *
          fderiv ℝ (fun y => E ^ ((I.length : ℤ) - ((a :: A).length : ℤ)) *
            transitionT K I (a :: A) (E • y)) x (basisVec b)) =
          ∑ b : Fin 2, E ^ (((i :: I).length : ℤ) - ((a :: A).length : ℤ)) *
            (K (E • x) b i * fderiv ℝ (transitionT K I (a :: A)) (E • x) (basisVec b)) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [directional_derivative_rescaling _ hd, hpow]
        ring
      rw [hs]
      ring

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Native external fluxes agreeing almost everywhere in time preserve the full plane solution class. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_forcing_time_ae_congr {ν a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
    {A : ∀ i j, (o : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (o.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
    {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F F' : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hF : ∀ i, ∀ᵐ s ∂volume.restrict (Set.Icc a b),
      (F i s).toFunction.jet (valueIndex2 (K i)) =ᵐ[volume]
        (F' i s).toFunction.jet (valueIndex2 (K i)))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν a b v D K A f F' g u w := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro i t ht φ
  have hold := hs.2.2.2.2 i t ht φ
  simp only [Measure.restrict_univ] at hold ⊢
  apply coupledWeakIdentity_time_ae_forcing_congr volume ν a t v _ _ _ _ _ _ _ _ _
    (fun k => planeRawJet_memLp φ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) _ _ _ hold
  · intro s _ k
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).comp_memLp'
        (planeRawJet_memLp (F i s) (valueIndex2 (K i)))
  · intro s _ k
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).comp_memLp'
        (planeRawJet_memLp (F' i s) (valueIndex2 (K i)))
  · have hsub : Set.Ioc a t ⊆ Set.Icc a b :=
      fun s hmem => ⟨hmem.1.le, hmem.2.trans ht.2⟩
    exact ae_restrict_of_ae_restrict_of_subset hsub (hF i)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Finite radial moments discharge the convergence requirements for weak-jet periodization. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem periodizeRawJet_of_radial_moments (D : RawJet2 K E)
    (hw : HasOrderedWeakJetOn Set.univ D) (z : Vec 2)
    (hf : ∀ a, AEStronglyMeasurable (D a) volume)
    (hm : ∀ a, MemLp (fun y => (1 + ‖y - z‖) ^ 4 • D a y) 2 volume) :
    HasPeriodicOrderedWeakJet (periodizeRawJet D) := by
  apply periodizeRawJet_of_spatial_majorant D hw
  intro R hR
  let L : JetIndex2 K → ℝ := fun a =>
    (eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • D a y) 2 volume).toReal
  refine ⟨(1 + R + ‖z‖) ^ 4 * ∑ a, L a, ?_⟩
  intro n a
  have he := radialMoment_image_eLpNorm_le (D a) z R hR (hf a)
    (hm a).aestronglyMeasurable n
  have hL : eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • D a y) 2 volume =
      ENNReal.ofReal (L a) := (ENNReal.ofReal_toReal (hm a).eLpNorm_lt_top.ne).symm
  rw [hL, ← ENNReal.ofReal_mul (by positivity)] at he
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  have hs : L a ≤ ∑ b, L b :=
    Finset.single_le_sum (fun b _ => (show 0 ≤ L b from ENNReal.toReal_nonneg)) (Finset.mem_univ a)
  have hp : 0 ≤ (1 + R + ‖z‖) ^ 4 * (1 / spatialLatticeWeight n) ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hp
  convert hh using 1; ring

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! Positive jets of the centred natural flow at the rescaled cell length. -/

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparationCellFlow_positive_jets
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (e : ℝ) (he : 0 < e) (yc z : Vec 2)
    (p : ℕ) (hp : 1 ≤ p) (hpJ : p ≤ Jchart + 1) :
    ‖iteratedFDeriv ℝ p (naturalPreparationCellFlow hφ r σ e yc) z‖ ≤
      preparationFlowJetConstant Cchart p * (ocEpsilon q Λ (m - 1) / e)⁻¹ ^ (p - 1) := by
  unfold naturalPreparationCellFlow
  rw [norm_iteratedFDeriv_normalizedAffineIncrement p (by omega)
    _ ((streamFlow_spatial_smooth hφ r σ).of_le (by simp)) e he yc z]
  have hh := mul_le_mul_of_nonneg_left
    (preparation_flow_positive_jets hc ha r σ hr hσ hage p hp hpJ (yc + e • z))
    (pow_nonneg he.le (p - 1))
  apply hh.trans_eq
  rw [inv_div, div_eq_mul_inv, mul_pow]
  ring

theorem naturalPreparationCellFlow_jetBound
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hE : 0 < ocEpsilon q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (e : ℝ) (he : 0 < e) (yc : Vec 2) :
    JetBound (naturalPreparationCellFlow hφ r σ e yc) (Jchart + 1)
      (1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|)
      (ocEpsilon q Λ (m - 1) / e) := by
  exact jetBound_of_Cχ (div_pos hE he)
    (fun p hp hpJ z => naturalPreparationCellFlow_positive_jets hc ha r σ hr hσ hage e he yc z
      p hp hpJ)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Exact affine cell sampling of native order-lowering transition factors. -/

theorem transitionT_spatial_translation
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (yc : Vec 2)
    (I A : List (Fin 2)) (x : Vec 2) :
    transitionT (fun y => K (yc + y)) I A x = transitionT K I A (yc + x) := by
  induction I generalizing A x with
  | nil => cases A <;> simp [transitionT]
  | cons i I ih =>
    cases A with
    | nil =>
      rw [transitionT_empty_output_nonempty_native, transitionT_empty_output_nonempty_native]
      rfl
    | cons a A =>
      have hfun : transitionT (fun y => K (yc + y)) I (a :: A) =
          fun y => transitionT K I (a :: A) (yc + y) := funext (ih (a :: A))
      simp only [transitionT]
      rw [hfun, ih A x, fderiv_comp_add_left]

theorem transitionT_affine_sampling
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (yc : Vec 2) (e : ℝ) (he : 0 < e) (I A : List (Fin 2)) (z : Vec 2) :
    transitionT (fun x => K (yc + e • x)) I A z =
      e ^ ((I.length : ℤ) - (A.length : ℤ)) * transitionT K I A (yc + e • z) := by
  have hshift : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K (yc + x) i j) :=
    fun i j => (hK i j).comp (contDiff_const.add contDiff_id)
  rw [transitionT_spatial_rescaling (fun x => K (yc + x)) hshift e he,
    transitionT_spatial_translation]

end AVRegularity.CycleJointProofs
end
end
