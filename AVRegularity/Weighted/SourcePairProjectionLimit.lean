-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.WordMomentSlots
public import AVRegularity.Weighted.FluxCoordinateInjection
import AVRegularity.CoupledEnergyPlane.Transport.CarrierTransport
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.MixedTail.Energy
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Split a compact production flux before integration, keeping derivatives of G local. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem compact_scalar_normSq_integrable (U : Lp E 2 (volume : Measure (Vec 2)))
    (c : Vec 2 → ℝ) (hc : Continuous c) (hs : HasCompactSupport c) :
    Integrable (fun x => c x * ‖U x‖ ^ 2) volume := by
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  have hi : Integrable (fun x => ‖U x‖ ^ 2) volume := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) U U
  exact hi.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hM)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem compact_divergence_integrable (U : Lp E 2 (volume : Measure (Vec 2)))
    (c : Fin 2 → Vec 2 → ℝ) (hc : ∀ i, ContDiff ℝ 1 (c i))
    (hs : ∀ i, HasCompactSupport (c i)) :
    Integrable (fun x => (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) * ‖U x‖ ^ 2) volume := by
  have hcont i : Continuous (fun x => fderiv ℝ (c i) x (basisVec i)) :=
    ((hc i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsum : Continuous (fun x => ∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) :=
    continuous_finsetSum _ (fun i _ => hcont i)
  have hsupport : HasCompactSupport (fun x => ∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) := by
    convert ((hs 0).fderiv_apply ℝ (basisVec 0)).add
      ((hs 1).fderiv_apply ℝ (basisVec 1)) using 1
    funext x
    simp only [Fin.sum_univ_two]
    rfl
  exact compact_scalar_normSq_integrable U _ hsum hsupport

theorem planeH1_compact_divergence_split (u : PlaneHk Set.univ 1 E)
    (c a b : Fin 2 → Vec 2 → ℝ)
    (ha : ∀ i, ContDiff ℝ 1 (a i)) (hb : ∀ i, ContDiff ℝ 1 (b i))
    (hsa : ∀ i, HasCompactSupport (a i)) (hsb : ∀ i, HasCompactSupport (b i))
    (he : ∀ i x, c i x = a i x + b i x) :
    (∫ x, (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) *
      ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2) =
    (∫ x, (∑ i : Fin 2, fderiv ℝ (a i) x (basisVec i)) *
      ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2) -
    2 * (∫ x, inner ℝ (∑ i : Fin 2, b i x • planeH1GradientOperator (E := E) u i x)
      (planeHkValueOperator (E := E) 1 u x)) := by
  have hi := planeH1_compact_divergence_identity u b hb hsb
  have hsplit : (∫ x, (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) *
      ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2) =
    (∫ x, (∑ i : Fin 2, fderiv ℝ (a i) x (basisVec i)) *
      ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2) +
    (∫ x, (∑ i : Fin 2, fderiv ℝ (b i) x (basisVec i)) *
      ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2) := by
    rw [← integral_add (compact_divergence_integrable _ a ha hsa)
      (compact_divergence_integrable _ b hb hsb)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      have hd i : fderiv ℝ (c i) x = fderiv ℝ (a i) x + fderiv ℝ (b i) x := by
        have hf : c i = fun y => a i y + b i y := funext (he i)
        rw [hf, fderiv_fun_add ((ha i).differentiable (by norm_num) x)
          ((hb i).differentiable (by norm_num) x)]
      simp_rw [hd]
      simp only [add_apply, Finset.sum_add_distrib, add_mul])
  linarith only [hi, hsplit]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Genuine H1 derivative tests constructed from the actual real Fourier cutoff. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeOrderedCutoffTest (N : ℕ) {m : ℕ} (w : DerivativeWord2 m)
    (Z : PlaneHk Set.univ 1 E) : PlaneHk Set.univ 1 E :=
  derivativePlaneHk (K := 1) w
    (hilbertBandHk N (1 + m) (planeHkValueOperator 1 Z))

theorem planeOrderedCutoffTest_value (N : ℕ) {m : ℕ} (w : DerivativeWord2 m)
    (Z : PlaneHk Set.univ 1 E) :
    planeHkValueOperator 1 (planeOrderedCutoffTest N w Z) =
      hilbertWordOperator N w (planeHkValueOperator 1 Z) := by
  have hi : prefixJetIndex (K := 1) w (valueIndex2 1) =
      (⟨⟨m, by omega⟩, w⟩ : JetIndex2 (1 + m)) := by
    simp [prefixJetIndex, valueIndex2, valueIndex, Fin.append_elim0]
  simp only [planeHkValueOperator_apply, planeOrderedCutoffTest,
    derivativePlaneHk_apply]
  rw [hi]
  simp only [hilbertBandHk_component, univToPlane_planeToUniv,
    hilbertWordOperator]

theorem planeOrderedCutoffTest_gradient (N : ℕ) {m : ℕ} (w : DerivativeWord2 m)
    (Z : PlaneHk Set.univ 1 E) (k : Fin 2) :
    planeH1GradientOperator (planeOrderedCutoffTest N w Z) k =
      hilbertWordOperator N (Fin.snoc w k) (planeHkValueOperator 1 Z) := by
  have hi : prefixJetIndex (K := 1) w (⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ : JetIndex2 1) =
      (⟨⟨m + 1, by omega⟩, Fin.snoc w k⟩ : JetIndex2 (1 + m)) := by
    simp [prefixJetIndex, Fin.append_right_eq_snoc]
  simp only [planeH1GradientOperator_apply, planeOrderedCutoffTest,
    derivativePlaneHk_apply]
  rw [hi]
  simp only [hilbertBandHk_component, univToPlane_planeToUniv,
    hilbertWordOperator]
end

/-! Arbitrary cutoff derivative tests read the actual stored source jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_ordered_cutoff_test_pair (N : ℕ) {K : ℕ}
    (U : PlaneHk Set.univ K E) (α : JetIndex2 K)
    (z : Lp E 2 (volume : Measure (Vec 2))) :
    inner ℝ (planeHkValueOperator K U) (hilbertWordOperator N α.2 z) =
      (-1 : ℝ) ^ α.1.val * inner ℝ (hilbertProjection N (univToPlane (U.val α))) z := by
  calc
    _ = inner ℝ (hilbertWordOperator N α.2 z) (planeHkValueOperator K U) := real_inner_comm _ _
    _ = (-1 : ℝ) ^ α.1.val * inner ℝ z
        (hilbertWordOperator N α.2 (planeHkValueOperator K U)) :=
      hilbertWord_ordered_inner N α.2 z _
    _ = _ := by rw [hilbertWord_planeHk_value N U α, real_inner_comm z]
end

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.Weighted

/-! Genuine derivative tests identify every stored flux derivative in the original weak equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeFluxValue_component_carrier {K : ℕ}
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) (k : Fin 2) :
    planeFluxValueOperator K S k =
      planeHkValueOperator K (mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) S) := by
  simp only [planeHkValueOperator_apply, mapPlaneHk_component]
  exact (univToPlane_fiberMap (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k)
    (S.val (valueIndex2 K))).symm

theorem planeFlux_ordered_cutoff_component_pair (N : ℕ) {K : ℕ}
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) (α : JetIndex2 K)
    (Z : PlaneHk Set.univ 1 E) (k : Fin 2) :
    inner ℝ (planeFluxValueOperator K S k)
      (planeH1GradientOperator (planeOrderedCutoffTest N α.2 Z) k) =
      (-1 : ℝ) ^ α.1.val * inner ℝ
        (hilbertProjection N (univToPlane
          ((mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) S).val α)))
        (planeH1GradientOperator Z k) := by
  rw [planeOrderedCutoffTest_gradient, ← hilbertWord_single_comp,
    ← hilbertWord_comm_single, planeFluxValue_component_carrier,
    planeHk_ordered_cutoff_test_pair]
  have hz := hilbertWord_planeHk_value N Z
    (⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ : JetIndex2 1)
  rw [hz, ← hilbertProjection_inner, hilbertProjection_idempotent]
  rfl

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergyPlane.Transport
namespace AVRegularity.Weighted

/-! Exact unweighted transport cancellation for the scalar weak energy slice. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A bounded divergence-free velocity contributes exactly zero to the actual plane `H¹` energy. -/
theorem planeScalarTransport_energy_zero (v : Vec 2 → Vec 2)
    (hc : ∀ k, Continuous (fun z => v z k)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k z, |v z k| ≤ M) (hv : ContDiff ℝ 1 v)
    (hvb : ∃ B : ℝ, ∀ z, ‖v z‖ ≤ B)
    (hdiv : ∀ z, ∑ k : Fin 2, fderiv ℝ v z (basisVec k) k = 0)
    (u : PlaneHk Set.univ 1 E) :
    inner ℝ (planeScalarTransport v hc hM hb (planeH1GradientOperator (E := E) u))
      (planeHkValueOperator (E := E) 1 u) = 0 := by
  rw [planeScalarTransport_inner_eq_integral]
  have hp := planeHk_principal_transport_zero (K := 0) u ⟨0, by omega⟩
    (fun j => Fin.elim0 j) v hv hvb hdiv
  have hg : ∀ᵐ z ∂volume, ∀ k : Fin 2,
      planeH1GradientOperator (E := E) u k z =
        u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ z :=
    ae_all_iff.mpr (fun k => univToPlane_ae _)
  have he : (∫ z, ∑ k : Fin 2, v z k * inner ℝ
      (planeH1GradientOperator (E := E) u k z) (planeHkValueOperator (E := E) 1 u z)) =
      ∫ z, inner ℝ (∑ k : Fin 2, v z k •
        u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ z)
        (u.val (valueIndex2 1) z) := by
    apply integral_congr_ae
    filter_upwards [hg, univToPlane_ae (u.val (valueIndex2 1))] with z hgz hvz
    simp only [planeHkValueOperator_apply, hvz, sum_inner, real_inner_smul_left]
    exact Finset.sum_congr rfl (fun k _ => by rw [hgz k])
  rw [he]
  have hl : lowerIndex2 (K := 1) ⟨0, by omega⟩ (fun j => Fin.elim0 j) =
      valueIndex2 1 := by
    apply Sigma.ext rfl
    change HEq (fun j : Fin 0 => Fin.elim0 j) (Fin.elim0 : Fin 0 → Fin 2)
    rfl
  rw [hl] at hp
  simpa only [nextIndex2, nextIndex, Fin.snoc_zero] using hp

end AVRegularity.Weighted
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Fast derivatives of a slow Taylor basis coefficient are controlled by the reserved mixed jet. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slow_basis_fast_word_bound {r j : ℕ} (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth r j f) (w : DerivativeWord2 r) (δ : DerivativeWord2 j)
    (X z : Vec 2) :
    ‖orderedDerivative δ (fun z' => iteratedFDeriv ℝ r (fun X' => f X' z') X
      (fun i => basisVec (w i))) z‖ ≤
      ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ := by
  let β : DerivativeWord2 r := fun i => w (Fin.rev i)
  have hs (z' : Vec 2) : iteratedFDeriv ℝ r (fun X' => f X' z') X
      (fun i => basisVec (w i)) = orderedDerivative β (fun X' => f X' z') X := by
    rw [orderedDerivative_eq_iteratedFDeriv β (hf.contDiff_slow z')]
    simp only [β, Fin.rev_rev]
  simp_rw [hs]
  have hcomm := MixedTail.fastL_slowL_comm (List.ofFn β) (List.ofFn δ)
    (F := f) (by simpa using hf)
  have he : orderedDerivative δ (fun z' => orderedDerivative β (fun X' => f X' z') X) z =
      orderedDerivative β (fun X' => orderedDerivative δ (f X') z) X :=
    congrFun (congrFun hcomm X) z
  rw [he]
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec 2) E
    (fun i => basisVec (δ (Fin.rev i)))
  have hz (X' : Vec 2) : orderedDerivative δ (f X') z =
      L (iteratedFDeriv ℝ j (f X') z) := by
    rw [orderedDerivative_eq_iteratedFDeriv δ (hf.1 X')]
    rfl
  simp_rw [hz]
  have hfield : ContDiff ℝ (r : ℕ∞)
      (fun X' => iteratedFDeriv ℝ j (f X') z) := hf.2.1 j le_rfl z
  change ‖orderedDerivative β (L ∘ (fun X' => iteratedFDeriv ℝ j (f X') z)) X‖ ≤ _
  rw [orderedDerivative_eq_iteratedFDeriv β (L.contDiff.comp hfield)]
  dsimp only
  have hi := L.iteratedFDeriv_comp_left (x := X) hfield.contDiffAt
    (by norm_cast : (r : WithTop ℕ∞) ≤ r)
  rw [hi]
  change ‖(iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X
    (fun i => basisVec (β (Fin.rev i)))) (fun i => basisVec (δ (Fin.rev i)))‖ ≤ _
  calc
    _ ≤ ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X
      (fun i => basisVec (β (Fin.rev i)))‖ := by
        simpa only [norm_basisVec, Finset.prod_const_one, mul_one] using
          (ContinuousMultilinearMap.le_opNorm
            (iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X
              (fun i => basisVec (β (Fin.rev i)))) (fun i => basisVec (δ (Fin.rev i))))
    _ ≤ _ := by
      simpa only [norm_basisVec, Finset.prod_const_one, mul_one] using
        (ContinuousMultilinearMap.le_opNorm
          (iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X)
          (fun i => basisVec (β (Fin.rev i))))

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! The original weak source equation implies the exact cutoff increment of every stored jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeProjectedJetSourcePair (N : ℕ) {K : ℕ} (α : JetIndex2 K)
    (H : PlaneHk Set.univ K E)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (Z : PlaneHk Set.univ 1 E) : ℝ :=
  inner ℝ (hilbertProjection N (univToPlane (H.val α))) (planeHkValueOperator 1 Z) -
    ∑ k : Fin 2, inner ℝ (hilbertProjection N (univToPlane
      ((mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) S).val α)))
      (planeH1GradientOperator Z k)

theorem plane_ordered_projected_source_increment (N : ℕ) {K : ℕ}
    (U H : ℝ → PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) (s t : ℝ)
    (heq : ∀ Z : PlaneHk Set.univ 1 E,
      inner ℝ (planeHkValueOperator K (U t)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeHkValueOperator K (U s)) (planeHkValueOperator 1 Z) =
      ∫ r in s..t, inner ℝ (planeHkValueOperator K (H r)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeFluxValueOperator K (S r)) (planeH1GradientOperator Z))
    (α : JetIndex2 K) (Z : PlaneHk Set.univ 1 E) :
    inner ℝ (hilbertProjection N (univToPlane ((U t).val α))) (planeHkValueOperator 1 Z) -
      inner ℝ (hilbertProjection N (univToPlane ((U s).val α))) (planeHkValueOperator 1 Z) =
      ∫ r in s..t, planeProjectedJetSourcePair N α (H r) (S r) Z := by
  have h := heq (planeOrderedCutoffTest N α.2 Z)
  simp_rw [planeOrderedCutoffTest_value, planeHk_ordered_cutoff_test_pair,
    PiLp.inner_apply, planeFlux_ordered_cutoff_component_pair] at h
  simp_rw [← Finset.mul_sum, ← mul_sub] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)) h

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane
open AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.Weighted

/-! Remove the actual Fourier projections from each full stored source time pairing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeJetSourcePair {K : ℕ} (α : JetIndex2 K) (H : PlaneHk Set.univ K E)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (Z : PlaneHk Set.univ 1 E) : ℝ :=
  inner ℝ (univToPlane (H.val α)) (planeHkValueOperator 1 Z) -
    ∑ k : Fin 2, inner ℝ (univToPlane
      ((mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) S).val α))
      (planeH1GradientOperator Z k)

theorem tendsto_planeProjectedJetSourcePair_integral {K : ℕ}
    (H : ℝ → PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (α : JetIndex2 K) (Z : PlaneHk Set.univ 1 E) {s t : ℝ} (hst : s ≤ t)
    (hH : IntervalIntegrable (fun r => univToPlane ((H r).val α)) volume s t)
    (hS : ∀ k : Fin 2, IntervalIntegrable (fun r => univToPlane
      ((mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S r)).val α)) volume s t) :
    Tendsto (fun N => ∫ r in s..t, planeProjectedJetSourcePair N α (H r) (S r) Z)
      atTop (𝓝 (∫ r in s..t, planeJetSourcePair α (H r) (S r) Z)) := by
  let f := fun r => univToPlane ((H r).val α)
  let g := fun k : Fin 2 => fun r => univToPlane
    ((mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S r)).val α)
  have hlim := (tendsto_projection_time_pairing hst f hH (planeHkValueOperator 1 Z)).sub
    (tendsto_finsetSum Finset.univ (fun k _ =>
      tendsto_projection_time_pairing hst (g k) (hS k) (planeH1GradientOperator Z k)))
  have hSP N : IntervalIntegrable (fun r => ∑ k : Fin 2,
      inner ℝ (hilbertProjection N (g k r)) (planeH1GradientOperator Z k)) volume s t := by
    convert IntervalIntegrable.sum Finset.univ
      (fun k _ => intervalIntegrable_projection_pair (g k) (hS k) (planeH1GradientOperator Z k) N) using 1
    funext r
    exact (Finset.sum_apply r (Finset.univ : Finset (Fin 2))
      (fun k r => inner ℝ (hilbertProjection N (g k r)) (planeH1GradientOperator Z k))).symm
  have hSU : IntervalIntegrable (fun r => ∑ k : Fin 2,
      inner ℝ (g k r) (planeH1GradientOperator Z k)) volume s t := by
    convert IntervalIntegrable.sum Finset.univ
      (fun k _ => intervalIntegrable_inner_const (g k) (hS k) (planeH1GradientOperator Z k)) using 1
    funext r
    exact (Finset.sum_apply r (Finset.univ : Finset (Fin 2))
      (fun k r => inner ℝ (g k r) (planeH1GradientOperator Z k))).symm
  have he N : (∫ r in s..t, planeProjectedJetSourcePair N α (H r) (S r) Z) =
      (∫ r in s..t, inner ℝ (hilbertProjection N (f r)) (planeHkValueOperator 1 Z)) -
        ∑ k : Fin 2, ∫ r in s..t, inner ℝ (hilbertProjection N (g k r))
          (planeH1GradientOperator Z k) := by
    rw [show (fun r => planeProjectedJetSourcePair N α (H r) (S r) Z) =
      (fun r => inner ℝ (hilbertProjection N (f r)) (planeHkValueOperator 1 Z) -
        ∑ k : Fin 2, inner ℝ (hilbertProjection N (g k r)) (planeH1GradientOperator Z k)) from rfl]
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_projection_pair f hH (planeHkValueOperator 1 Z) N) (hSP N),
      intervalIntegral.integral_finsetSum (fun k _ => intervalIntegrable_projection_pair (g k) (hS k) (planeH1GradientOperator Z k) N)]
  have hfinal : (∫ r in s..t, planeJetSourcePair α (H r) (S r) Z) =
      (∫ r in s..t, inner ℝ (f r) (planeHkValueOperator 1 Z)) -
        ∑ k : Fin 2, ∫ r in s..t, inner ℝ (g k r) (planeH1GradientOperator Z k) := by
    rw [show (fun r => planeJetSourcePair α (H r) (S r) Z) =
      (fun r => inner ℝ (f r) (planeHkValueOperator 1 Z) -
        ∑ k : Fin 2, inner ℝ (g k r) (planeH1GradientOperator Z k)) from rfl]
    rw [intervalIntegral.integral_sub (intervalIntegrable_inner_const f hH (planeHkValueOperator 1 Z)) hSU,
      intervalIntegral.integral_finsetSum (fun k _ => intervalIntegrable_inner_const (g k) (hS k) (planeH1GradientOperator Z k))]
  rw [hfinal]
  exact hlim.congr (fun N => (he N).symm)

end AVRegularity.Weighted
end
