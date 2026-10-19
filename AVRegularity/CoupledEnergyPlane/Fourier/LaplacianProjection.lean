-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.Fourier.CarrierPairing
public import AVRegularity.CoupledEnergyPlane.Variational.GradientTensorOperator
import AVRegularity.CoupledEnergyPlane.Variational.DerivativeTensorOperator

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The cutoff gradient operator is the literal gradient Sobolev carrier, at every jet order. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeGradientTensor_band_component (N K : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) (α : JetIndex2 K) :
    (planeGradientTensor (hilbertBandHk N (K + 1) u)).val α =
      planeToUniv (bandGradientOperator (E := E) N (hilbertWordOperator N α.2 u)) := by
  simp only [planeGradientTensor, planeFamilyTensor_jet, derivativePlaneHk_apply,
    hilbertBandHk_component, bandGradientOperator, sum_apply, ContinuousLinearMap.comp_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [planeToUniv_fiberMap]
  congr 1
  change planeToUniv (hilbertWordOperator N (Fin.append (fun _ : Fin 1 => i) α.2) u) =
    planeToUniv (hilbertWordOperator N (fun _ : Fin 1 => i) (hilbertWordOperator N α.2 u))
  rw [hilbertWord_prefix_single, hilbertWord_single_comp]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The plane cutoff diffusion consumes exactly the factorial gradient square. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem sum_word_single_normSq (N j : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    (∑ w : DerivativeWord2 j, ∑ i : Fin 2,
      ‖hilbertWordOperator N (fun _ : Fin 1 => i) (hilbertWordOperator N w u)‖ ^ 2) =
      ∑ w : DerivativeWord2 (j + 1), ‖hilbertWordOperator N w u‖ ^ 2 := by
  simp only [hilbertWord_single_comp]
  rw [← (Fin.snocEquiv (fun _ : Fin (j + 1) => Fin 2)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  rfl

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandLaplacian_factorialPairing (N K : ℕ) (ρ : ℝ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    factorialPairing ρ (hilbertBandHk N K (bandLaplacianOperator N u)).val
      (hilbertBandHk N K u).val =
      -gradFactorialNormSq ρ (hilbertBandHk N (K + 1) u).val := by
  unfold factorialPairing gradFactorialNormSq
  simp only [hilbertBandHk_component, planeToUniv.norm_map]
  change (∑ j : Fin (K + 1), factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 j.val,
      inner ℝ (planeToUniv (hilbertWordOperator N w (bandLaplacianOperator N u)))
        (planeToUniv (hilbertWordOperator N w u))) =
    -(∑ j : Fin (K + 1), factorialWeight ρ j.val *
      ∑ w : DerivativeWord2 (j.val + 1), ‖hilbertWordOperator N w u‖ ^ 2)
  have hi (f g : Lp E 2 (volume : Measure (Vec 2))) :
      inner ℝ (planeToUniv f) (planeToUniv g) = inner ℝ f g := by
    simp only [L2.inner_def, Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [planeToUniv_ae f, planeToUniv_ae g] with x hf hg
    rw [hf, hg]
  simp only [hi, hilbertWord_laplacian_inner, Finset.sum_neg_distrib, mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact sum_word_single_normSq N j.val u

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Literal almost-everywhere representatives of the plane cutoff gradient and its Sobolev jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem bandGradientOperator_ae (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    bandGradientOperator (E := E) N u =ᵐ[volume] fun x =>
      (WithLp.toLp 2 (fun w : Fin 2 => hilbertWordOperator (E := E) N (fun _ : Fin 1 => w) u x) :
        PiLp 2 (fun _ : Fin 2 => E)) := by
  classical
  simp only [bandGradientOperator, sum_apply, ContinuousLinearMap.comp_apply]
  have hs := Lp.coeFn_finsetSum Finset.univ (fun w : Fin 2 =>
    (tensorEntryCLM (J := Fin 2) (E := E) w).compLpL 2 volume (hilbertWordOperator (E := E) N (fun _ : Fin 1 => w) u))
  have ht := ae_all_iff.mpr (fun w : Fin 2 =>
    ContinuousLinearMap.coeFn_compLpL (tensorEntryCLM (J := Fin 2) (E := E) w) (hilbertWordOperator (E := E) N (fun _ : Fin 1 => w) u))
  filter_upwards [hs, ht] with x hx hh
  rw [hx, Finset.sum_apply]
  apply PiLp.ext
  intro w
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [hh]
  change (∑ k : Fin 2, PiLp.single 2 k (hilbertWordOperator N (fun _ : Fin 1 => k) u x) w) = _
  simp

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeGradientTensor_band_ae (N K : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) (α : JetIndex2 K) :
    univToPlane ((planeGradientTensor (hilbertBandHk N (K + 1) u)).val α) =ᵐ[volume]
      fun x => (WithLp.toLp 2 (fun k : Fin 2 =>
        hilbertWordOperator N (Fin.snoc α.2 k) u x) : PiLp 2 (fun _ : Fin 2 => E)) := by
  rw [planeGradientTensor_band_component, univToPlane_planeToUniv]
  simpa only [hilbertWord_single_comp] using
    bandGradientOperator_ae N (hilbertWordOperator N α.2 u)


theorem planeGradientTensor_band_raw_ae (N K : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) (α : JetIndex2 K) :
    (planeGradientTensor (hilbertBandHk N (K + 1) u)).val α =ᵐ[volume]
      fun x => (WithLp.toLp 2 (fun k : Fin 2 =>
        (hilbertBandHk N (K + 1) u).val
          ⟨⟨α.1.val + 1, Nat.succ_lt_succ α.1.isLt⟩, Fin.snoc α.2 k⟩ x) :
        PiLp 2 (fun _ : Fin 2 => E)) := by
  have hh : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      (hilbertBandHk N (K + 1) u).val
        ⟨⟨α.1.val + 1, Nat.succ_lt_succ α.1.isLt⟩, Fin.snoc α.2 k⟩ x =
        hilbertWordOperator N (Fin.snoc α.2 k) u x := by
    apply ae_all_iff.mpr
    intro k
    rw [hilbertBandHk_component]
    exact planeToUniv_ae _
  filter_upwards [planeGradientTensor_band_ae N K u α,
    univToPlane_ae ((planeGradientTensor (hilbertBandHk N (K + 1) u)).val α), hh]
    with x hg hb hx
  rw [hb] at hg
  rw [hg]
  apply PiLp.ext
  intro k
  exact (hx k).symm

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The literal Galerkin derivative tensor is the value of its reserve-compatible Sobolev carrier. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planePositiveDerivativeTensor_band_value {K L : ℕ}
    (N m : ℕ) (hm : 1 ≤ m) (hKL : K + (m - 1) ≤ L)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    planeHkValueOperator K
      (planePositiveDerivativeTensor m hm hKL (hilbertBandHk N (L + 1) u)) =
      bandTensorOperator (E := E) N m u := by
  rw [planeHkValueOperator_apply]
  apply Lp.ext
  have ht := planePositiveDerivativeTensor_value_ae m hm hKL (hilbertBandHk N (L + 1) u)
  simp only [Measure.restrict_univ] at ht
  have hw := ae_all_iff.mpr (fun w : DerivativeWord2 m =>
    planeToUniv_ae (hilbertWordOperator (E := E) N w u))
  filter_upwards [univToPlane_ae
    ((planePositiveDerivativeTensor m hm hKL (hilbertBandHk N (L + 1) u)).val
      (valueIndex2 K)), ht, bandTensorOperator_ae N m u, hw] with x hx ht hb hw
  rw [hx, ht, hb]
  apply PiLp.ext
  intro w
  simpa only [WithLp.ofLp_toLp, hilbertBandHk_component, hilbertWordOperator] using hw w
end

/-! The literal value of the plane cutoff gradient carrier agrees with the projected gradient operator. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem hilbertWord_zero (N : ℕ) (w : Fin 0 → Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertWordOperator N w u = hilbertProjection N u := by
  apply fiberCoordinate_ext
  intro k
  simp only [hilbertWordOperator_coordinate, bandWordRealOperator_apply,
    hilbertProjection_coordinate]
  exact bandWordReal_zero N w _

theorem bandGradient_projection (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    bandGradientOperator (E := E) N (hilbertProjection N u) = bandGradientOperator (E := E) N u := by
  simp only [bandGradientOperator, sum_apply, ContinuousLinearMap.comp_apply, hilbertWord_projection]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeGradientTensor_band_value (N K : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    planeHkValueOperator K (planeGradientTensor (hilbertBandHk N (K + 1) u)) =
      bandGradientOperator (E := E) N u := by
  rw [planeHkValueOperator_apply, planeGradientTensor_band_component, univToPlane_planeToUniv]
  change bandGradientOperator (E := E) N (hilbertWordOperator N (fun _ : Fin 0 => (0 : Fin 2)) u) = _
  rw [hilbertWord_zero, bandGradient_projection]
end

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Exact two-direction gradient dot products and projected diffusion against arbitrary tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem bandGradientOperator_component (N : ℕ) (k : Fin 2)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k).compLpL 2 volume
      (bandGradientOperator (E := E) N u) =
      hilbertWordOperator N (fun _ : Fin 1 => k) u := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (bandGradientOperator (E := E) N u),
    bandGradientOperator_ae N u] with x hx hg
  rw [hx, hg]
  rfl

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem bandGradient_inner (N : ℕ) (u v : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (bandGradientOperator (E := E) N u) (bandGradientOperator (E := E) N v) =
      ∑ k : Fin 2, inner ℝ (hilbertWordOperator N (fun _ : Fin 1 => k) u)
        (hilbertWordOperator N (fun _ : Fin 1 => k) v) := by
  conv_lhs => lhs; unfold bandGradientOperator
  simp only [sum_apply, ContinuousLinearMap.comp_apply, sum_inner,
    tensorEntryLp_inner, bandGradientOperator_component]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem bandLaplacian_gradient_inner (N : ℕ)
    (u v : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (bandLaplacianOperator N u) v =
      -inner ℝ (bandGradientOperator (E := E) N u) (bandGradientOperator (E := E) N v) := by
  rw [bandGradient_inner]
  simp only [bandLaplacianOperator, sum_apply, sum_inner,
    ← hilbertWord_single_comp, hilbertWord_single_inner, Finset.sum_neg_distrib]

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Spectral cutoffs commute with the entire genuine Sobolev gradient carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkCutoff_component (N K : ℕ) (q : PlaneHk Set.univ K E)
    (α : JetIndex2 K) :
    (planeHkCutoff N K q).val α = planeToUniv (hilbertProjection N (univToPlane (q.val α))) :=
  hilbertBandHk_of_planeHk_component N q α

theorem planeHkCutoff_gradient (N K : ℕ) (q : PlaneHk Set.univ (K + 1) E) :
    planeGradientTensor (planeHkCutoff N (K + 1) q) =
      planeHkCutoff N K (planeGradientTensor q) := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  rw [planeHkCutoff_component]
  simp only [planeGradientTensor, planeFamilyTensor_jet, derivativePlaneHk_apply,
    planeHkCutoff_component, map_sum, univToPlane_fiberMap, hilbertProjection_fiberMap,
    planeToUniv_fiberMap]

end AVRegularity.CoupledEnergyPlane.Fourier
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Projected gradients of genuine H¹ tests converge to their literal weak gradient tensor. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandGradient_planeH1_value (N : ℕ) (φ : PlaneHk Set.univ 1 E) :
    bandGradientOperator (E := E) N (planeHkValueOperator 1 φ) =
      hilbertProjection N (planeHkValueOperator 0 (planeGradientTensor φ)) := by
  simp only [bandGradientOperator, sum_apply, ContinuousLinearMap.comp_apply,
    planeHkValueOperator_apply, planeGradientTensor, planeFamilyTensor_jet,
    derivativePlaneHk_apply, map_sum, univToPlane_fiberMap, hilbertProjection_fiberMap]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have hi : prefixJetIndex (fun _ : Fin 1 => k) (valueIndex2 0) =
      (⟨⟨1, Nat.one_lt_two⟩, fun _ : Fin 1 => k⟩ : JetIndex2 1) := by
    simp [prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
  rw [hi]
  exact hilbertWord_planeHk_value N φ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩

theorem tendsto_bandGradient_planeH1_value (φ : PlaneHk Set.univ 1 E) :
    Tendsto (fun N => bandGradientOperator (E := E) N (planeHkValueOperator 1 φ)) atTop
      (𝓝 (planeHkValueOperator 0 (planeGradientTensor φ))) := by
  simp_rw [bandGradient_planeH1_value]
  exact tendsto_hilbertProjection _

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Exact factorial pairing of projected divergence with the genuine gradient carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem hilbertProjection_gradient (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    hilbertProjection N (bandGradientOperator (E := E) N u) =
      bandGradientOperator (E := E) N u := by
  simp only [bandGradientOperator, sum_apply, ContinuousLinearMap.comp_apply,
    map_sum, hilbertProjection_fiberMap, hilbertProjection_word]

theorem bandDivergence_factorialPairing (N K : ℕ) (ρ : ℝ)
    (u : Lp E 2 (volume : Measure (Vec 2)))
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    factorialPairing ρ
      (hilbertBandHk N K (bandDivergenceOperator (E := E) N (planeHkValueOperator K F))).val
      (hilbertBandHk N K u).val =
      -factorialPairing ρ F.val (planeGradientTensor (hilbertBandHk N (K + 1) u)).val := by
  unfold factorialPairing
  simp only [hilbertBandHk_component, planeGradientTensor_band_component]
  change (∑ j : Fin (K + 1), factorialWeight ρ j.val * ∑ w : DerivativeWord2 j.val,
    inner ℝ (planeToUniv (hilbertWordOperator N w
      (bandDivergenceOperator (E := E) N (planeHkValueOperator K F))))
      (planeToUniv (hilbertWordOperator N w u))) = _
  simp only [planeToUniv_inner, hilbertWord_divergence_inner,
    Finset.sum_neg_distrib, mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  have hw := hilbertWord_planeHk_value N F (⟨j, w⟩ : JetIndex2 K)
  rw [hw, hilbertProjection_inner, hilbertProjection_gradient]
  have he := planeToUniv_inner (univToPlane (F.val ⟨j, w⟩))
    (bandGradientOperator (E := E) N (hilbertWordOperator N w u))
  rw [planeToUniv_univToPlane] at he
  exact he.symm

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! A projected gradient of each true weak jet is its projected gradient-carrier jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandGradient_planeHk_jet (N K : ℕ)
    (q : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K) :
    bandGradientOperator (E := E) N
      (univToPlane ((truncatePlaneHk (Nat.le_succ K) q).val α)) =
      hilbertProjection N (univToPlane ((planeGradientTensor q).val α)) := by
  have h := congrArg (fun z : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) =>
    univToPlane (z.val α)) (planeHkCutoff_gradient N K q)
  rw [planeHkCutoff_component, univToPlane_planeToUniv] at h
  change univToPlane ((planeGradientTensor
    (hilbertBandHk N (K + 1) (planeHkValueOperator (K + 1) q))).val α) = _ at h
  rw [planeGradientTensor_band_component, univToPlane_planeToUniv] at h
  have hw := hilbertWord_planeHk_value N q
    (truncateJetIndex (Nat.le_succ K) α)
  change hilbertWordOperator N α.2 (planeHkValueOperator (K + 1) q) =
    hilbertProjection N (univToPlane ((truncatePlaneHk (Nat.le_succ K) q).val α)) at hw
  rw [hw] at h
  have hp (u : Lp E 2 (volume : Measure (Vec 2))) :
      bandGradientOperator (E := E) N (hilbertProjection N u) =
        bandGradientOperator (E := E) N u := by
    simp only [bandGradientOperator, sum_apply, ContinuousLinearMap.comp_apply,
      hilbertWord_projection]
  rw [hp] at h
  exact h
end

/-! The projected divergence is adjoint to the true Sobolev gradient at every jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandDivergence_planeHk_jet_pairing (N K : ℕ)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (q : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K) :
    inner ℝ
      ((hilbertBandHk N K (bandDivergenceOperator (E := E) N (planeHkValueOperator K S))).val α)
      ((truncatePlaneHk (Nat.le_succ K) q).val α) =
      -inner ℝ ((planeHkCutoff N K S).val α) ((planeGradientTensor q).val α) := by
  rw [hilbertBandHk_component, planeHkCutoff_component]
  change inner ℝ (planeToUniv (hilbertWordOperator N α.2
    (bandDivergenceOperator (E := E) N (planeHkValueOperator K S))))
    ((truncatePlaneHk (Nat.le_succ K) q).val α) = _
  have hb := planeToUniv_inner
    (hilbertWordOperator N α.2 (bandDivergenceOperator (E := E) N (planeHkValueOperator K S)))
    (univToPlane ((truncatePlaneHk (Nat.le_succ K) q).val α))
  rw [planeToUniv_univToPlane] at hb
  rw [hb, hilbertWord_divergence, hilbertWord_planeHk_value N S α,
    bandDivergence_gradient_inner, bandGradient_planeHk_jet]
  rw [← hilbertProjection_inner, hilbertProjection_idempotent]
  have ht := planeToUniv_inner
    (hilbertProjection N (univToPlane (S.val α)))
    (univToPlane ((planeGradientTensor q).val α))
  rw [planeToUniv_univToPlane] at ht
  rw [ht]

theorem bandDivergence_planeHk_pairing (N K : ℕ)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (q : PlaneHk Set.univ (K + 1) E) :
    inner ℝ
      (hilbertBandHk N K (bandDivergenceOperator (E := E) N (planeHkValueOperator K S)))
      (truncatePlaneHk (Nat.le_succ K) q) =
      -inner ℝ (planeHkCutoff N K S) (planeGradientTensor q) := by
  change inner ℝ
    (hilbertBandHk N K (bandDivergenceOperator (E := E) N (planeHkValueOperator K S))).val
    (truncatePlaneHk (Nat.le_succ K) q).val =
    -inner ℝ (planeHkCutoff N K S).val (planeGradientTensor q).val
  rw [PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro α _
  exact bandDivergence_planeHk_jet_pairing N K S q α
end

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! Native projected diffusion is the divergence of the genuine weak gradient value. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem bandLaplacian_eq_divergence_gradient (N : ℕ)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    bandLaplacianOperator N u =
      bandDivergenceOperator (E := E) N (bandGradientOperator (E := E) N u) := by
  apply ext_inner_right (𝕜 := ℝ)
  intro z
  rw [bandLaplacian_gradient_inner, bandDivergence_gradient_inner]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem bandDivergence_projection (N : ℕ)
    (F : Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2))) :
    bandDivergenceOperator (E := E) N (hilbertProjection N F) =
      bandDivergenceOperator (E := E) N F := by
  apply ext_inner_right (𝕜 := ℝ)
  intro z
  rw [bandDivergence_gradient_inner, bandDivergence_gradient_inner,
    hilbertProjection_inner, hilbertProjection_gradient]

theorem bandLaplacian_planeH1_eq_divergence (N : ℕ) (q : PlaneHk Set.univ 1 E) :
    bandLaplacianOperator N (planeHkValueOperator 1 q) =
      bandDivergenceOperator (E := E) N (planeHkValueOperator 0 (planeGradientTensor q)) := by
  rw [bandLaplacian_eq_divergence_gradient, bandGradient_planeH1_value,
    bandDivergence_projection]
end

/-! Fixed-band diffusion tests the actual weak gradient of a genuine H¹ carrier. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem bandLaplacian_planeH1_pairing (N : ℕ) (q : PlaneHk Set.univ 1 E)
    (z : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (bandLaplacianOperator N (planeHkValueOperator 1 q)) z =
      -inner ℝ (planeHkValueOperator 0 (planeGradientTensor q))
        (bandGradientOperator (E := E) N z) := by
  rw [bandLaplacian_gradient_inner, bandGradient_planeH1_value, hilbertProjection_inner,
    hilbertProjection_gradient]
end

end AVRegularity.CoupledEnergyPlane.Fourier
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CoupledEnergyPlane.Fourier

/-! The actual band Laplacian depends only on the projected value. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem bandLaplacian_projection (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    bandLaplacianOperator (E := E) N (hilbertProjection (E := E) N u) =
      bandLaplacianOperator (E := E) N u := by
  rw [bandLaplacian_eq_divergence_gradient, bandGradient_projection,
    ← bandLaplacian_eq_divergence_gradient]

end AVRegularity.CoupledEnergyPlane.Fourier
end
end
end
