-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.FluxCoordinateInjection
public import AVRegularity.Weighted.PlaneH1Readouts
public import AVRegularity.CoupledEnergyPlane.Fourier.HilbertSobolevOperator
public import AVRegularity.Definitions.CycleWords.CoreScalarPackage

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Compact divergence identities on the actual plane Sobolev readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_compact_divergence_identity (u : PlaneHk Set.univ 1 E)
    (c : Fin 2 → Vec 2 → ℝ) (hc : ∀ i, ContDiff ℝ 1 (c i))
    (hs : ∀ i, HasCompactSupport (c i)) :
    2 * (∫ x, inner ℝ (∑ i : Fin 2, c i x • planeH1GradientOperator (E := E) u i x)
      (planeHkValueOperator (E := E) 1 u x)) =
      -(∫ x, (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) *
        ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2) := by
  have hu : MemLp (fun x => u.val (valueIndex2 1) x) 2 volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp (u.val (valueIndex2 1))
  have hg i : MemLp (fun x => u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ x) 2 volume := by
    simpa only [Measure.restrict_univ] using
      Lp.memLp (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩)
  have hl : lowerIndex2 (K := 1) ⟨0, by omega⟩ (fun j => Fin.elim0 j) = valueIndex2 1 := by
    apply Sigma.ext rfl
    change HEq (fun j : Fin 0 => Fin.elim0 j) (Fin.elim0 : Fin 0 → Fin 2)
    rfl
  have hw i e : HasWeakPartialDerivOn Set.univ i
      (fun x => inner ℝ e (u.val (valueIndex2 1) x))
      (fun x => inner ℝ e (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ x)) := by
    have h := u.toFunction.hasWeakJet ⟨0, by omega⟩ (fun j => Fin.elim0 j) i e
    rw [hl] at h
    simpa only [nextIndex2, nextIndex, Fin.snoc_zero, PlaneHk.toFunction, planeJetRepresentative] using h
  have he := weak_hilbert_gradient_mul_compact hu hg hw c hc hs
  have ha : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      planeH1GradientOperator (E := E) u i x =
        u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  have hleft : (∫ x, inner ℝ (∑ i : Fin 2, c i x • planeH1GradientOperator (E := E) u i x)
      (planeHkValueOperator (E := E) 1 u x)) =
      ∫ x, inner ℝ (∑ i : Fin 2, c i x • u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ x)
        (u.val (valueIndex2 1) x) := by
    apply integral_congr_ae
    filter_upwards [ha, univToPlane_ae (u.val (valueIndex2 1))] with x hx hv
    simp only [planeHkValueOperator_apply, hv]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [hx i])
  have hright : (∫ x, (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) *
      ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2) =
      ∫ x, (∑ i : Fin 2, fderiv ℝ (c i) x (basisVec i)) * ‖u.val (valueIndex2 1) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [univToPlane_ae (u.val (valueIndex2 1))] with x hx
    simp only [planeHkValueOperator_apply, hx]
  rw [hleft, hright]
  exact he

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Exact moment bookkeeping for the finite chronological word. -/

def wordMomentSlot {N : ℕ} (m : ℕ) (Ks : Fin N → ℕ) (j : Fin (N + 1)) : ℕ :=
  m + ∑ i : Fin N, if j.val ≤ i.val then Ks i else 0

@[simp] theorem wordMomentSlot_zero {N : ℕ} (m : ℕ) (Ks : Fin N → ℕ) :
    wordMomentSlot m Ks 0 = wordReserveN m Ks := by
  simp [wordMomentSlot, wordReserveN]

theorem wordMomentSlot_castSucc {N : ℕ} (m : ℕ) (Ks : Fin N → ℕ) (j : Fin N) :
    wordMomentSlot m Ks j.castSucc = wordMomentSlot m Ks j.succ + Ks j := by
  classical
  have he (i : Fin N) : (if j.val ≤ i.val then Ks i else 0) =
      (if j.val + 1 ≤ i.val then Ks i else 0) + (if i = j then Ks i else 0) := by
    by_cases hij : i = j
    · subst i; simp
    · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      by_cases hji : j.val ≤ i.val
      · simp only [ite_eq_left hji, ite_eq_left (show j.val + 1 ≤ i.val by omega),
          ite_eq_right hij, add_zero]
      · simp only [ite_eq_right hji, ite_eq_right (show ¬j.val + 1 ≤ i.val by omega),
          ite_eq_right hij, add_zero]
  simp only [wordMomentSlot, Fin.val_castSucc, Fin.val_succ]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp [Nat.add_assoc]

end AVRegularity.Weighted
end
end
