-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.DriftCoefficientEmbedding
public import AVRegularity.CycleComparison.Lift.ParameterIntegral
public import AVRegularity.CycleWords.CellTransitionGeometry
public import AVRegularity.Construction.Scales.Times

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Original normalized velocity jets give frequency-linear potential coefficient jet bounds. -/

def normalizedDriftCoefficient (η : ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
    (t : ℝ) (x : Vec 2) : ℂ →L[ℝ] ℂ :=
  normalizedDriftCoefficientEmbedding ξ (Real.sqrt η • v t x)

theorem normalizedDriftCoefficient_array_norm_le (η : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ) (t : ℝ) (j : ℕ)
    (hv : ContDiff ℝ (j : ℕ) (fun x => Real.sqrt η • v t x)) (x : Vec 2) :
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) j x‖ ≤
      ((Fintype.card (DerivativeWord2 j) : ℝ) * (2 * fibreNorm ξ)) *
        ‖iteratedFDeriv ℝ j (fun x => Real.sqrt η • v t x) x‖ := by
  let L := normalizedDriftCoefficientEmbedding ξ
  let f := fun x => Real.sqrt η • v t x
  have hh := coefficient_array_norm_le_card_iterated (L ∘ f) j (L.contDiff.comp hv) x
  have hi := L.iteratedFDeriv_comp_left (x := x) hv.contDiffAt
    (by norm_cast : (j : WithTop ℕ∞) ≤ j)
  rw [hi] at hh
  have hcomp := L.norm_compContinuousMultilinearMap_le (iteratedFDeriv ℝ j f x)
  have hnorm := normalizedDriftCoefficientEmbedding_norm_le ξ
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (hcomp.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))) (by positivity)).trans_eq
      (by ring))

theorem normalizedDriftCoefficient_array_bound (η : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ) (t : ℝ) (j : ℕ)
    (hv : ContDiff ℝ (j : ℕ) (fun x => Real.sqrt η • v t x)) (M : ℝ)
    (hb : ∀ x, ‖iteratedFDeriv ℝ j (fun x => Real.sqrt η • v t x) x‖ ≤ M) (x : Vec 2) :
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) j x‖ ≤
      ((Fintype.card (DerivativeWord2 j) : ℝ) * 2 * M) * fibreNorm ξ := by
  exact (normalizedDriftCoefficient_array_norm_le η v ξ t j hv x).trans
    ((mul_le_mul_of_nonneg_left (hb x)
      (mul_nonneg (by positivity) (mul_nonneg (by norm_num) (fibreNorm_nonneg ξ)))).trans_eq (by ring))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The normalized potential coefficient inherits the actual drift's window regularity. -/

theorem normalizedDriftCoefficient_measurable (η : ℝ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) :
    Measurable (Function.uncurry (normalizedDriftCoefficient η v ξ)) := by
  have hm : Measurable (fun p : ℝ × Vec 2 => Real.sqrt η • v p.1 p.2) := by
    simpa only [Pi.smul_def'] using (measurable_const (a := Real.sqrt η)).smul hv.1
  exact (normalizedDriftCoefficientEmbedding ξ).continuous.measurable.comp hm

theorem normalizedDriftCoefficient_contDiff (η : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ) (t : ℝ) (j : ℕ)
    (hv : ContDiff ℝ (j : ℕ) (v t)) :
    ContDiff ℝ (j : ℕ) (normalizedDriftCoefficient η v ξ t) := by
  have hf : ContDiff ℝ (j : ℕ) (fun x => Real.sqrt η • v t x) := by
    simpa only [Pi.smul_def'] using
      (contDiff_const : ContDiff ℝ (j : ℕ) (fun _ : Vec 2 => Real.sqrt η)).smul hv
  exact (normalizedDriftCoefficientEmbedding ξ).contDiff.comp hf

theorem normalizedDriftCoefficient_periodic (η : ℝ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (t : ℝ) :
    AVenhance.IsZ2Periodic (normalizedDriftCoefficient η v ξ t) := by
  intro n x
  unfold normalizedDriftCoefficient
  rw [hv.2.2.1 t n x]

end AVRegularity.CycleWords
end

section
open Homogenization Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Explicit finite frequency-linear jet budgets on the consumed time window. -/

def normalizedDriftJetBudget (K : ℕ) (M : Fin (K + 1) → ℝ) (ξ : Fin 2 → ℂ) :
    Fin (K + 1) → ℝ :=
  fun l => ((Fintype.card (DerivativeWord2 l.val) : ℝ) * 2 * M l) * fibreNorm ξ

theorem normalizedDriftJetBudget_nonneg (K : ℕ) (M : Fin (K + 1) → ℝ)
    (ξ : Fin 2 → ℂ) (hM : ∀ l, 0 ≤ M l) (l : Fin (K + 1)) :
    0 ≤ normalizedDriftJetBudget K M ξ l :=
  mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by norm_num)) (hM l)) (fibreNorm_nonneg ξ)

theorem normalizedDriftJetBudget_window_bound (K : ℕ) (a b η : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t)) (M : Fin (K + 1) → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l.val (fun x => Real.sqrt η • v t x) x‖ ≤ M l)
    (t : ℝ) (ht : t ∈ Icc a b) (l : Fin (K + 1)) (x : Vec 2) :
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤
      normalizedDriftJetBudget K M ξ l := by
  have hv : ContDiff ℝ (l.val : ℕ) (v t) :=
    (hc t ht).of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt)
  have hs : ContDiff ℝ (l.val : ℕ) (fun x => Real.sqrt η • v t x) := by
    simpa only [Pi.smul_def'] using
      (contDiff_const : ContDiff ℝ (l.val : ℕ) (fun _ : Vec 2 => Real.sqrt η)).smul hv
  exact normalizedDriftCoefficient_array_bound η v ξ t l.val hs (M l) (hj l t ht) x

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleWords

/-! Constant spatial derivatives commute through every smooth ordered word. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_append {r s : ℕ} (w : DerivativeWord2 r)
    (q : DerivativeWord2 s) (f : Vec 2 → E) :
    orderedDerivative (Fin.append w q) f = orderedDerivative q (orderedDerivative w f) := by
  simp only [orderedDerivative, List.ofFn_fin_append, List.foldl_append]

theorem orderedListDerivative_coordinate_commute (w : List (Fin 2)) (i : Fin 2)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    orderedListDerivative w (coordinateDerivative i f) =
      coordinateDerivative i (orderedListDerivative w f) := by
  induction w generalizing f with
  | nil => rfl
  | cons k w ih =>
    change orderedListDerivative w (coordinateDerivative k (coordinateDerivative i f)) =
      coordinateDerivative i (orderedListDerivative w (coordinateDerivative k f))
    rw [coordinateDerivative_commute i k f hf]
    exact ih _ (coordinateDerivative_contDiff k f hf)

theorem orderedDerivative_coordinate_commute {r : ℕ} (w : DerivativeWord2 r)
    (i : Fin 2) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    orderedDerivative w (coordinateDerivative i f) =
      coordinateDerivative i (orderedDerivative w f) :=
  orderedListDerivative_coordinate_commute (List.ofFn w) i f hf

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
open scoped NNReal
namespace AVRegularity.CycleWords

/-! The inverse of every actual normalized renewal has one uniform Lipschitz bound. -/

theorem cellTransition_inverse_lipschitz (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (l : ℤ) (y y' : Vec 2) :
    LipschitzWith ⟨2 * ((2 : ℝ) ^ 23 + 1), by positivity⟩
      ((cellTransitionHomeomorph α q Λ m hφ l y y'
        (Scales.epsilon_basic (m := m) hq.1 hΛ).1.ne').symm : Vec 2 → Vec 2) := by
  have hE := (Scales.epsilon_basic (m := m - 1) hq.1 hΛ).1
  have he := (Scales.epsilon_basic (m := m) hq.1 hΛ).1
  have hb := transition_uniform_jacobian_bar α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
    Φ hseq m hm hφ (l + 1) l (Or.inr rfl)
  have hF : ContDiff ℝ (⊤ : ℕ∞) (ocTransition α q Λ m (Φ (m - 1)) hφ (l + 1) l) :=
    CycleReference.streamFlow_spatial_smooth hφ _ _
  have hlip := jacobian_bar_lipschitz hF (by positivity : 0 < (2 : ℝ) ^ 11 *
    (ocEpsilon q Λ (m - 1))⁻¹) (by positivity : 0 ≤ (2 : ℝ) ^ 23) hb
  exact cell_rescaled_lipschitz _ _ hlip (ocEpsilon q Λ m) he y' y

theorem cellTransition_forward_lipschitz (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (m : ℕ) (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (l : ℤ) (y y' : Vec 2) :
    LipschitzWith ⟨2 * ((2 : ℝ) ^ 23 + 1), by positivity⟩
      (ocCellTransition α q Λ m (Φ (m - 1)) hφ l y y') := by
  have hE := (Scales.epsilon_basic (m := m - 1) hq.1 hΛ).1
  have he := (Scales.epsilon_basic (m := m) hq.1 hΛ).1
  have hb := transition_uniform_jacobian_bar α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
    Φ hseq m hm hφ l (l + 1) (Or.inl rfl)
  have hF : ContDiff ℝ (⊤ : ℕ∞) (ocTransition α q Λ m (Φ (m - 1)) hφ l (l + 1)) :=
    CycleReference.streamFlow_spatial_smooth hφ _ _
  have hlip := jacobian_bar_lipschitz hF (by positivity : 0 < (2 : ℝ) ^ 11 *
    (ocEpsilon q Λ (m - 1))⁻¹) (by positivity : 0 ≤ (2 : ℝ) ^ 23) hb
  exact cell_rescaled_lipschitz _ _ hlip (ocEpsilon q Λ m) he y y'

end AVRegularity.CycleWords
end
