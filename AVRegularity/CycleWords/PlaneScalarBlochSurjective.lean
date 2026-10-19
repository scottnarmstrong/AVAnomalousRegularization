-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.FiniteSmoothPeriodicCarrier
public import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
public import AVRegularity.CoupledEnergy.Galerkin.PlainSynthesis
import AVRegularity.CycleEvolution.CellTimeReverseAdmissibility
import AVRegularity.Analysis.Convolution.Kernel.ApproximationBounds
import AVRegularity.CycleReference.ChartDerivativeBounded
public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.CoupledEnergyPlane.Fourier.HilbertSobolevOperator
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleWords

/-! The native ordered derivative of a smooth periodic state is its actual classical derivative. -/

theorem finiteSmoothPeriodicHk_derivative {K r : ℕ} (w : DerivativeWord2 r)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (K + r : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) :
    derivativeTorusHk (K := K) w (finiteSmoothPeriodicHk (K + r) f hf hp) =
      finiteSmoothPeriodicHk K (orderedDerivative w f)
        (AVRegularity.CycleComparison.Lift.orderedDerivative_contDiff w K f (hf.of_le (by
          exact_mod_cast (by omega : K + r ≤ K + r))))
        (orderedDerivative_periodic w f (hf.of_le (by
          exact_mod_cast (by omega : r ≤ K + r))) hp) := by
  apply TorusHk.ext_value
  apply Lp.ext
  have hl := finiteSmoothPeriodicHk_jet_ae (K + r) f hf hp
    (prefixJetIndex w (valueIndex2 K))
  have hr := finiteSmoothPeriodicHk_jet_ae K (orderedDerivative w f)
    (AVRegularity.CycleComparison.Lift.orderedDerivative_contDiff w K f (hf.of_le (by
      exact_mod_cast (by omega : K + r ≤ K + r))))
    (orderedDerivative_periodic w f (hf.of_le (by
      exact_mod_cast (by omega : r ≤ K + r))) hp) (valueIndex2 K)
  change (derivativeTorusHk w (finiteSmoothPeriodicHk (K + r) f hf hp)).val
    (valueIndex2 K) =ᵐ[_] _
  rw [derivativeTorusHk_apply]
  apply hl.trans
  apply Filter.EventuallyEq.trans _ hr.symm
  apply Filter.Eventually.of_forall
  intro x
  simp only [prefixJetIndex, valueIndex2, valueIndex, Fin.val_zero, Nat.add_zero,
    Fin.append_elim0]
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! Finite weighted stored product jets converge strongly under bounded coefficient-jet convergence. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem weightedRawProduct_toLp_tendsto {K : ℕ}
    (C : ℕ → Vec 2 → E →L[ℝ] F) (C0 : Vec 2 → E →L[ℝ] F)
    (hC : ∀ n, ContDiff ℝ (K : ℕ) (C n)) (hC0 : ContDiff ℝ (K : ℕ) C0)
    (D : RawJet2 K E) (q : Vec 2 → ℝ)
    (hw : JetMemL2On Set.univ (fun b x => q x • D b x))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ n l x, ‖coefficientDerivativeArray (C n) l.val x‖ ≤ A l)
    (hb0 : ∀ l x, ‖coefficientDerivativeArray C0 l.val x‖ ≤ A l)
    (ht : ∀ (l : Fin (K + 1)) (w : DerivativeWord2 l.val) x e,
      Tendsto (fun n => orderedCoefficientDerivative (C n) l.val w x e) atTop
        (𝓝 (orderedCoefficientDerivative C0 l.val w x e))) (a : JetIndex2 K) :
    Tendsto (fun n => (weighted_multiplicationRawJet_memLp (C n) (hC n) D q hw A
      (hb n) a).toLp (fun x => q x • multiplicationRawJet (C n) D a x)) atTop
      (𝓝 ((weighted_multiplicationRawJet_memLp C0 hC0 D q hw A hb0 a).toLp
        (fun x => q x • multiplicationRawJet C0 D a x))) := by
  let f n x := q x • multiplicationRawJet (C n) D a x
  let f0 x := q x • multiplicationRawJet C0 D a x
  let g := weightedRawProductMajorant A D q a
  have hf n : MemLp (f n) 2 (volume.restrict Set.univ) := by
    exact
      weighted_multiplicationRawJet_memLp (C n) (hC n) D q hw A (hb n) a
  have hf0 : MemLp f0 2 (volume.restrict Set.univ) := by
    exact
      weighted_multiplicationRawJet_memLp C0 hC0 D q hw A hb0 a
  have hg : MemLp g 2 (volume.restrict Set.univ) := by
    exact weightedRawProductMajorant_memLp A D q hw a
  have hbound n : ∀ᵐ x ∂(volume.restrict Set.univ), ‖f n x‖ ≤ ‖g x‖ := by
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (weightedRawProductMajorant_nonneg A hA D q a x)]
    exact weightedRawProduct_norm_le_majorant (C n) A (hb n) D q a x
  have hbound0 : ∀ᵐ x ∂(volume.restrict Set.univ), ‖f0 x‖ ≤ ‖g x‖ := by
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (weightedRawProductMajorant_nonneg A hA D q a x)]
    exact weightedRawProduct_norm_le_majorant C0 A hb0 D q a x
  have hpoint : ∀ᵐ x ∂(volume.restrict Set.univ), Tendsto (fun n => f n x) atTop (𝓝 (f0 x)) := by
    apply Eventually.of_forall
    intro x
    change Tendsto (fun n => q x • multiplicationRawJet (C n) D a x) atTop
      (𝓝 (q x • multiplicationRawJet C0 D a x))
    simp_rw [multiplicationRawJet_pointwise_weight]
    simp only [multiplicationRawJet, multiplicationTerm]
    apply tendsto_finsetSum
    intro m _
    exact ht (rawProductMaskOrder a m) (maskWordEquiv 2 a.1.val m a.2).1 x
      (q x • D (maskJetIndex (Nat.le_of_lt_succ a.1.isLt) m a.2) x)
  exact tendsto_L2Field_of_dominated f f0 g hf hf0 hg hbound hbound0 hpoint

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Native real energy pairings are exactly their original finite jet pairings. -/

 theorem torusHigher_inner_eq_sum (K : ℕ) (U V : TorusHk K ℂ) :
    inner ℝ U V = ∑ a : JetIndex2 K, inner ℝ (U.val a) (V.val a) := by
  change inner ℝ U.val V.val = _
  rw [PiLp.inner_apply]

 theorem torusDerivative_zero_value_coordinate (r : ℕ) (w : DerivativeWord2 r)
    (U : TorusHk (0 + r) ℂ) :
    torusHkValueCLM (derivativeTorusHk (K := 0) w U) = U.val ⟨⟨r, by omega⟩, w⟩ := by
  change U.val (prefixJetIndex w (valueIndex2 0)) = _
  have hi : prefixJetIndex w (valueIndex2 0) = (⟨⟨r, by omega⟩, w⟩ : JetIndex2 (0 + r)) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · exact heq_of_eq (by
        funext i
        exact Fin.append_left w Fin.elim0 i)
  rw [hi]

 theorem torusHigher_jet_coordinate {K : ℕ} (a : JetIndex2 K) (U : TorusHk K ℂ) :
    torusHkValueCLM (derivativeTorusHk (K := 0) a.2
      (truncateTorusHk (by omega : 0 + a.1.val ≤ K) U)) = U.val a := by
  rw [torusDerivative_zero_value_coordinate]
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Every positive native jet order is the value of its corresponding ordered derivative. -/

theorem torusOrdered_value_coordinate {r : ℕ} (w : DerivativeWord2 r)
    (U : TorusHk (1 + r) ℂ) :
    torusHkValueCLM (derivativeTorusHk (K := 1) w U) =
      U.val ⟨⟨r, by omega⟩, w⟩ := by
  change U.val (prefixJetIndex w (valueIndex2 1)) = _
  have hi : prefixJetIndex w (valueIndex2 1) = (⟨⟨r, by omega⟩, w⟩ : JetIndex2 (1 + r)) := by
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · exact heq_of_eq (by
        funext i
        exact Fin.append_left w Fin.elim0 i)
  rw [hi]

theorem torusHigher_norm_sq_eq_ordered_values (q : ℕ) (U : TorusHk (q + 1) ℂ) :
    ‖truncateTorusHk (by omega : q ≤ q + 1) U‖ ^ 2 =
      ‖torusHkValueCLM U‖ ^ 2 +
      ∑ r : Fin q, ∑ w : DerivativeWord2 (r.val + 1),
        ‖torusHkValueCLM (derivativeTorusHk (K := 1) w
          (truncateTorusHk (by omega : 1 + (r.val + 1) ≤ q + 1) U))‖ ^ 2 := by
  change ‖(truncateTorusHk (by omega : q ≤ q + 1) U).val‖ ^ 2 = _
  rw [jet_norm_sq_eq_sum, Fin.sum_univ_succ]
  congr 1
  · change (∑ w : DerivativeWord2 0, ‖U.val ⟨⟨0, by omega⟩, w⟩‖ ^ 2) = _
    let : Unique (DerivativeWord2 0) := ⟨⟨Fin.elim0⟩, fun w => funext (fun i => Fin.elim0 i)⟩
    rw [Fintype.sum_unique]
    rfl
  · apply Finset.sum_congr rfl
    intro r _
    simp only [derivativeNormSq, torusOrdered_value_coordinate, truncateTorusHk_apply,
      truncateJetIndex]
    rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Finite spatial coefficient bounds and radius reserves for constant cell metrics. -/

theorem constantCellMetric_spatial_jet_bound
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (t : ℝ) (l : ℕ) (x : Vec 2) (k j : Fin 2) :
    ‖iteratedFDeriv ℝ l (fun _ : Vec 2 => G t k j) x‖ ≤ 2 := by
  by_cases hl : l = 0
  · subst l
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      CycleEvolution.cellMetric_entry_bound hG t x k j
  · simp only [iteratedFDeriv_const_of_ne hl, Pi.zero_apply, norm_zero]
    norm_num

theorem exists_half_radius_reserve (A : ℝ) (hA : 0 ≤ A) :
    ∃ L : ℝ, 1 ≤ L ∧ A / L ^ 2 ≤ 1 / 2 := by
  refine ⟨2 * A + 1, by linarith, ?_⟩
  have hL : 0 < 2 * A + 1 := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith [sq_nonneg A]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Actual integer periodic multiplication intertwines the plane and torus Bloch carriers. -/

local instance planeBlochIntegerModulationMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem planeLatticeEmbedding_one_eq (n : Fin 2 → ℤ) :
    planeLatticeEmbedding 1 n = planeIntegerFrequency n := by
  funext i
  simp only [planeLatticeEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    zsmul_eq_mul, mul_one, planeIntegerFrequency]

theorem planeBloch_integerModulation_coeff_ae (a : Vec 2) (m : Fin 2 → ℤ)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a 1), ∀ n : Fin 2 → ℤ,
      mFourierCoeff (planeScalarBlochTransform a 1 (by norm_num)
        (planeIntegerModulationOperator m f) θ) n =
      mFourierCoeff (planeScalarBlochTransform a 1 (by norm_num) f θ) (n - m) := by
  have hn (n : Fin 2 → ℤ) : ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a 1),
      fourierL2 (planeIntegerModulationOperator m f) (planeLatticeEmbedding 1 n + θ) =
        fourierL2 f (planeLatticeEmbedding 1 n + θ - planeIntegerFrequency m) :=
    ae_restrict_of_ae ((measurePreserving_add_left volume (planeLatticeEmbedding 1 n)).quasiMeasurePreserving.ae
      (planeIntegerModulation_fourier_ae m f))
  filter_upwards [ae_all_iff.mpr hn,
    planeScalarBlochTransform_fourierCoeff_ae a 1 (by norm_num) (planeIntegerModulationOperator m f),
    planeScalarBlochTransform_fourierCoeff_ae a 1 (by norm_num) f] with θ hd hm hf n
  rw [hm n, hf (n - m), hd n]
  have he : planeLatticeEmbedding 1 n + θ - planeIntegerFrequency m =
      planeLatticeEmbedding 1 (n - m) + θ := by
    rw [← planeLatticeEmbedding_one_eq m, map_sub]
    abel
  rw [he]

theorem planeBloch_integerModulation_ae (a : Vec 2) (m : Fin 2 → ℤ)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a 1),
      planeScalarBlochTransform a 1 (by norm_num) (planeIntegerModulationOperator m f) θ =
        scalarTorusIntegerModulationOperator m (planeScalarBlochTransform a 1 (by norm_num) f θ) := by
  filter_upwards [planeBloch_integerModulation_coeff_ae a m f] with θ hθ
  apply (mFourierBasis (d := Fin 2)).repr.injective
  apply lp.ext
  funext n
  rw [mFourierBasis_repr, mFourierBasis_repr, scalarTorusIntegerModulationOperator_fourierCoeff]
  exact hθ n

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Genuine time measurability and uniform bounds for constant-in-space cell metrics. -/

theorem planeCellMetricTimeEntry_measurable
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (i j : Fin 2) : Measurable (fun t => G t i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (hG.1.comp (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))))

theorem planeCellMetricTimeEntry_memLp (μ : Measure ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (i j : Fin 2) : MemLp (fun t => G t i j) ∞ μ :=
  memLp_top_of_bound (planeCellMetricTimeEntry_measurable G hG i j).aestronglyMeasurable 2
    (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using cellMetric_entry_bound hG t 0 i j))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.CycleWords

/-! Strong approximation of existing plane Sobolev data by actual smooth value representatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem exists_smooth_planeHk_approximation {K : ℕ} (U : PlaneHk Set.univ K E) :
    ∃ UN : ℕ → PlaneHk Set.univ K E, ∃ fN : ℕ → Vec 2 → E,
      Tendsto UN atTop (𝓝 U) ∧
      (∀ N, ContDiff ℝ (⊤ : ℕ∞) (fN N)) ∧
      (∀ N, planeValue (UN N) =ᵐ[volume] fN N) := by
  obtain ⟨κ, hc, hd, _, hmass⟩ := exists_normalized_smooth_kernel
  obtain ⟨R, hzero⟩ := exists_shrinking_linearEquiv
  let f := univToPlane (U.val (valueIndex2 K))
  let UN N := planeSmoothing (K := K) (R N) κ hc hd f
  let fN N : Vec 2 → E := fun x => ∫ z, κ z • f (x - R N z)
  refine ⟨UN, fN, tendsto_planeSmoothing R hzero hc hd hmass U, ?_, ?_⟩
  · intro N
    exact contDiff_literalAverage (R N) hc hd
      ((Lp.memLp f).locallyIntegrable (by norm_num))
  · intro N
    have ha := averagingOperator_plane_literal_ae (R N)
      (hd.continuous.integrable_of_hasCompactSupport hc) f
    have hv := planeToUniv_ae (averagingOperator (R N).toLinearEquiv.toAddHom
      (R N).continuous κ (hd.continuous.integrable_of_hasCompactSupport hc) f)
    change ((UN N).val (valueIndex2 K) : Vec 2 → E) =ᵐ[volume] fN N
    rw [planeSmoothing_value]
    exact hv.trans ha

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The zeroth native real Hilbert pairing is exactly the original L2 pairing. -/

theorem torusH0_inner_value (u z : TorusHk 0 ℂ) :
    inner ℝ u z = inner ℝ (torusHkValueCLM u) (torusHkValueCLM z) := by
  let torusH0InnerValueJetUnique : Unique (JetIndex2 0) :=
    { default := valueIndex2 0
      uniq := by
        rintro ⟨j, w⟩
        have hj : j = 0 := Fin.ext (by omega)
        subst j
        have hw : w = Fin.elim0 := by
          funext i
          exact Fin.elim0 i
        cases hw
        rfl }
  rw [torusHigher_inner_eq_sum, Fintype.sum_unique]
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! An enlarged odd pulse window cannot meet another odd pulse's active support. -/

theorem odd_pulse_enlarged_active_unique {τ t : ℝ} (hτ : 0 < τ)
    {k j : ℤ} (hk : Odd k) (hj : Odd j)
    (hwindow : |t - (k : ℝ) * τ| ≤ 3 / 4 * τ)
    (hactive : (j : ℝ) * τ - (2 / 3) * τ < t ∧
      t < (j : ℝ) * τ + (2 / 3) * τ) : k = j := by
  obtain ⟨a, ha⟩ := hk
  obtain ⟨b, hb⟩ := hj
  obtain ⟨hlo, hhi⟩ := abs_le.mp hwindow
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkj | hjk
  · have hgap : k + 2 ≤ j := by omega
    have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgap
    have hmul := mul_le_mul_of_nonneg_right hgapR hτ.le
    linarith
  · have hgap : j + 2 ≤ k := by omega
    have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgap
    have hmul := mul_le_mul_of_nonneg_right hgapR hτ.le
    linarith

theorem pulse_other_zero_on_enlarged {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k j : ℤ}
    (hk : Odd k) (hj : Odd j) (hne : j ≠ k) {t : ℝ}
    (hwindow : |t - (k : ℝ) * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) :
    ocPulse α q Λ ζ m j t = 0 := by
  by_contra hactive
  have he := odd_pulse_enlarged_active_unique
    (AVRegularity.Construction.Stream.ocTau_pos hΛ) hk hj hwindow
    (CycleReference.pulse_nonzero_center_distance hΛ hζ hactive)
  exact hne he.symm

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The actual full-plane L2 class as its unique order-zero Sobolev carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeL2ZeroJetOperator : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
    JetL2 (volume.restrict Set.univ) 0 E :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex2 0 => ComponentL2 (volume.restrict Set.univ) E)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun _ => planeToUniv.toContinuousLinearMap))

def planeL2ZeroCarrier : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] PlaneHk Set.univ 0 E :=
  planeL2ZeroJetOperator.codRestrict (planeHkGraph (E := E) Set.univ 0).toSubmodule (fun f => by
    change planeL2ZeroJetOperator f ∈ planeHkGraph (E := E) Set.univ 0
    rw [mem_planeHkGraph_iff]
    intro j
    exact Fin.elim0 j)

theorem planeL2ZeroCarrier_component (f : Lp E 2 (volume : Measure (Vec 2))) (a : JetIndex2 0) :
    (planeL2ZeroCarrier f).val a = planeToUniv f := rfl

theorem planeL2ZeroCarrier_value (f : Lp E 2 (volume : Measure (Vec 2))) :
    planeHkValueOperator 0 (planeL2ZeroCarrier f) = f := by
  rw [planeHkValueOperator_apply, planeL2ZeroCarrier_component, univToPlane_planeToUniv]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus
namespace AVRegularity.CycleWords

/-! The actual scalar plane Bloch transform is onto its native fibre L2 space. -/

local instance planeScalarBlochSurjectiveMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarFibreSynthesis_surjective : Function.Surjective scalarFibreSynthesis := by
  intro f
  refine ⟨(mFourierBasis (d := Fin 2)).repr f, ?_⟩
  exact (mFourierBasis (d := Fin 2)).repr.symm_apply_apply f

theorem planeBlochCoefficients_scalar_surjective (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Function.Surjective (planeBlochCoefficients (E := ℂ) a P hP) := by
  exact (planeFrequencyL2Isometry_surjective a P hP).comp
    AVRegularity.CoupledEnergyPlane.Fourier.fourierL2.surjective

theorem planeScalarBlochTransform_surjective (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Function.Surjective (planeScalarBlochTransform a P hP) := by
  exact (liftLinearIsometryL2_surjective (volume.restrict (planeFrequencyCell a P))
    scalarFibreSynthesis scalarFibreSynthesis_surjective).comp
      (planeBlochCoefficients_scalar_surjective a P hP)

end AVRegularity.CycleWords
end
end
