-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.CellGalerkinLinearPrimitive
import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.CycleEvolution.CellEnergySpaceRawSmul
public import AVRegularity.CycleDamping.CellTrigonometricMean
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public noncomputable section

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The exact polynomial chain rule for the scalar adjoint differential operator. -/

def scalarAdjointOperator (v : ℝ → Vec 2 → Vec 2) (F : ℝ → Vec 2 → ℝ)
    (t : ℝ) (z : Vec 2) : ℝ :=
  deriv (fun s => F s z) t +
    (∑ i : Fin 2, v t z i * fderiv ℝ (F t) z (basisVec i)) +
    ∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ (F t) x (basisVec i)) z (basisVec i)

theorem scalarAdjointOperator_power (v : ℝ → Vec 2 → Vec 2) (F : ℝ → Vec 2 → ℝ)
    (hspace : ∀ t, ContDiff ℝ 2 (F t))
    (htime : ∀ z, Differentiable ℝ (fun t => F t z)) (n : ℕ) (t : ℝ) (z : Vec 2) :
    scalarAdjointOperator v (fun s x => F s x ^ n) t z =
      (n : ℝ) * F t z ^ (n - 1) * scalarAdjointOperator v F t z +
      (n : ℝ) * (n - 1 : ℕ) * F t z ^ (n - 2) *
        ∑ i : Fin 2, (fderiv ℝ (F t) z (basisVec i)) ^ 2 := by
  have hd : deriv (fun s => F s z ^ n) t =
      (n : ℝ) * F t z ^ (n - 1) * deriv (fun s => F s z) t := by
    exact ((htime z t).hasDerivAt.fun_pow n).deriv
  unfold scalarAdjointOperator
  rw [hd]
  simp_rw [polynomial_weight_second_derivative (F t) (hspace t),
    polynomial_weight_gradient (F t) ((hspace t).differentiable (by norm_num))]
  simp only [Fin.sum_univ_two]
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Ordered derivatives of actual finite Fourier paths have genuine scalar weak time equations. -/

theorem cellGalerkin_linear_weak_curve {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (J : CellGalerkinSpace (E := ℂ) N →L[ℝ] TorusHk 1 ℂ)
    (A : ℝ → CellGalerkinSpace (E := ℂ) N →L[ℝ] CellGalerkinSpace (E := ℂ) N)
    (f : ℝ → CellGalerkinSpace (E := ℂ) N) (u₀ : CellGalerkinSpace (E := ℂ) N)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution A f u₀ a b (extendCurve hab y))
    (hA : AEStronglyMeasurable A volume) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ t, ‖A t‖ ≤ M) (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    CellWeakHilbertCurve a b (fun t => torusHkValueCLM (J (extendCurve hab y t)))
      (fun t => J (extendCurve hab y t))
      (fun t => cellPivotDualCLM (torusHkValueCLM (J (linearRhs A f (extendCurve hab y) t)))) := by
  have hc : Continuous (fun t => J (extendCurve hab y t)) :=
    J.continuous.comp (continuous_extendCurve hab y)
  have hr := linearRhs_map_memLp A hA M hM hb (extendCurve hab y)
    (continuous_extendCurve hab y).continuousOn f hf J
  apply cellWeakHilbertCurve_of_H1_primitive _ _ hc.continuousOn
    (continuousOn_memLp_Icc _ hc.continuousOn) hr
  intro s hs t ht hst
  exact cellGalerkin_linear_primitive hab N J A f u₀ y hy hA M hM hb hf s hs t ht hst

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Actual retained cell Fourier states have smooth periodic representatives at every native order. -/

def cellGalerkinSmoothValue (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) : Vec 2 → ℂ :=
  smoothFourierJet (K := 1) (L := 0) N u.val (valueIndex2 0)

theorem cellGalerkinSmoothValue_contDiff (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    ContDiff ℝ (⊤ : ℕ∞) (cellGalerkinSmoothValue N u) :=
  (smoothFourierJet_contDiff N u.val (valueIndex2 0)).of_le (by simp)

theorem cellGalerkinSmoothValue_periodic (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    AVenhance.IsZ2Periodic (cellGalerkinSmoothValue N u) :=
  smoothFourierJet_periodic N u.val (valueIndex2 0)

theorem cellGalerkinSmoothValue_ae (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    (cellGalerkinValue N u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      cellGalerkinSmoothValue N u := by
  have h := torusJetToL2_ae (smoothFourierJet (K := 1) (L := 0) N u.val)
    (smoothFourierJet_memLp (K := 1) (L := 0) N u.val) (valueIndex2 0)
  change (torusHkValueCLM (smoothFourierLift (K := 1) (L := 0) N u.val) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellGalerkinSmoothValue N u at h
  have hp : galerkinProj (E := ℂ) (K := 1) N u.val = u.val :=
    galerkinProj_fixed_of_range (E := ℂ) (K := 1) N u
  rw [smoothFourierLift_value_projection, hp] at h
  exact h

theorem cellGalerkinRangeHigher_eq_smooth {L : ℕ} (hL : 1 ≤ L) (N : ℕ)
    (u : CellGalerkinSpace (E := ℂ) N) :
    rangeSmoothFourierLiftCLM hL N u =
      finiteSmoothPeriodicHk L (cellGalerkinSmoothValue N u)
        ((cellGalerkinSmoothValue_contDiff N u).of_le (by simp)) (cellGalerkinSmoothValue_periodic N u) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (rangeSmoothFourierLiftCLM hL N u) =
    torusHkValueCLM (finiteSmoothPeriodicHk L (cellGalerkinSmoothValue N u)
      ((cellGalerkinSmoothValue_contDiff N u).of_le (by simp)) (cellGalerkinSmoothValue_periodic N u))
  rw [cellGalerkinRangeHigher_value]
  apply Lp.ext
  have hjet := finiteSmoothPeriodicHk_jet_ae L (cellGalerkinSmoothValue N u)
    ((cellGalerkinSmoothValue_contDiff N u).of_le (by simp)) (cellGalerkinSmoothValue_periodic N u)
    (valueIndex2 L)
  exact (cellGalerkinSmoothValue_ae N u).trans hjet.symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Exact gradient and its quadratic budget for the polynomial base. -/

theorem quadratic_weight_gradient (f g : Vec 2 → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (z : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun x => 1 + f x ^ 2 + g x ^ 2) z (basisVec i) =
      2 * f z * fderiv ℝ f z (basisVec i) + 2 * g z * fderiv ℝ g z (basisVec i) := by
  rw [fderiv_fun_add ((differentiable_const 1).fun_add (hf.fun_pow 2) z) (hg.fun_pow 2 z), add_apply,
    fderiv_const_add]
  rw [polynomial_weight_gradient f hf, polynomial_weight_gradient g hg]
  norm_num

theorem quadratic_weight_gradient_sum (f g : Vec 2 → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (z : Vec 2) :
    (∑ i : Fin 2, (fderiv ℝ (fun x => 1 + f x ^ 2 + g x ^ 2) z (basisVec i)) ^ 2) ≤
      4 * (1 + f z ^ 2 + g z ^ 2) *
        ((∑ i : Fin 2, (fderiv ℝ f z (basisVec i)) ^ 2) +
          ∑ i : Fin 2, (fderiv ℝ g z (basisVec i)) ^ 2) := by
  simp_rw [quadratic_weight_gradient f g hf hg]
  simp only [Fin.sum_univ_two]
  convert quadratic_coordinate_gradient_bound (f z) (g z)
    (fderiv ℝ f z (basisVec 0)) (fderiv ℝ g z (basisVec 0))
    (fderiv ℝ f z (basisVec 1)) (fderiv ℝ g z (basisVec 1)) using 1
  ring

/-! Linearity of the actual scalar adjoint differential operator on smooth functions. -/

theorem sum_second_derivative (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => f y + g y) x (basisVec i)) z (basisVec i) =
      fderiv ℝ (fun x => fderiv ℝ f x (basisVec i)) z (basisVec i) +
      fderiv ℝ (fun x => fderiv ℝ g x (basisVec i)) z (basisVec i) := by
  have hd := hf.differentiable (by norm_num)
  have he := hg.differentiable (by norm_num)
  have hh : (fun x => fderiv ℝ (fun y => f y + g y) x (basisVec i)) =
      fun x => fderiv ℝ f x (basisVec i) + fderiv ℝ g x (basisVec i) := by
    funext x
    rw [fderiv_fun_add (hd x) (he x), add_apply]
  rw [hh, fderiv_fun_add (weight_gradient_differentiable f hf i z)
    (weight_gradient_differentiable g hg i z), add_apply]

theorem scalarAdjointOperator_add (v : ℝ → Vec 2 → Vec 2) (F H : ℝ → Vec 2 → ℝ)
    (hF : ∀ t, ContDiff ℝ 2 (F t)) (hH : ∀ t, ContDiff ℝ 2 (H t))
    (htF : ∀ z, Differentiable ℝ (fun t => F t z))
    (htH : ∀ z, Differentiable ℝ (fun t => H t z)) (t : ℝ) (z : Vec 2) :
    scalarAdjointOperator v (fun s x => F s x + H s x) t z =
      scalarAdjointOperator v F t z + scalarAdjointOperator v H t z := by
  unfold scalarAdjointOperator
  rw [deriv_fun_add (htF z t) (htH z t)]
  simp_rw [fderiv_fun_add ((hF t).differentiable (by norm_num) z)
    ((hH t).differentiable (by norm_num) z), add_apply,
    sum_second_derivative (F t) (H t) (hF t) (hH t)]
  simp only [Fin.sum_univ_two]
  ring

theorem scalarAdjointOperator_const (v : ℝ → Vec 2 → Vec 2) (c t : ℝ) (z : Vec 2) :
    scalarAdjointOperator v (fun _ _ => c) t z = 0 := by
  simp [scalarAdjointOperator]

/-! The actual cell adjoint coordinate equation, with its literal cutoff residual. -/

theorem adjointCellCoordinate_laplacian {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc : Vec 2)
    (t : ℝ) (z : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ
      (fun y => adjointCellCoordinate α q Λ ζ m ν B T yc t y j) x (basisVec i)) z (basisVec i)) =
      (ocEpsilon q Λ m ^ 2 / Real.sqrt (B * T)) *
        ∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ
          (fun y => adjointCoordinate α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) y j)
            x (basisVec i)) (yc + ocEpsilon q Λ m • z) (basisVec i) := by
  have hf := adjointCoordinate_space_contDiff (α := α) (q := q) (m := m) hΛ hζ ν
    (ocEll q Λ m ν ^ 2 * t) j 2
  have hh := affine_cell_laplacian
    (fun y => adjointCoordinate α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) y j - yc j)
    (hf.sub contDiff_const) yc (ocEpsilon q Λ m) (Real.sqrt (B * T)) z
  simpa only [adjointCellCoordinate, fderiv_sub_const] using hh

theorem adjointCellCoordinate_equation {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T)
    (yc : Vec 2) (t : ℝ) (z : Vec 2) (j : Fin 2) :
    deriv (fun s => adjointCellCoordinate α q Λ ζ m ν B T yc s z j) t +
      (∑ i : Fin 2, ocCellDrift α q Λ ζ m ν yc t z i *
        fderiv ℝ (fun x => adjointCellCoordinate α q Λ ζ m ν B T yc t x j) z (basisVec i)) +
      (∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ
        (fun y => adjointCellCoordinate α q Λ ζ m ν B T yc t y j) x (basisVec i)) z (basisVec i)) =
      (ocEll q Λ m ν ^ 2 / Real.sqrt (B * T)) *
        adjointResidual α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) (yc + ocEpsilon q Λ m • z) j := by
  have hep := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hR := Real.sqrt_pos.2 (mul_pos hB hT)
  rw [adjointCellCoordinate_time_derivative hΛ hζ, adjointCellCoordinate_laplacian hΛ hζ]
  simp_rw [adjointCellCoordinate_gradient hΛ hζ]
  have hp := adjointCoordinate_equation (α := α) (q := q) (m := m) hΛ hζ ν
    (ocEll q Λ m ν ^ 2 * t) (yc + ocEpsilon q Λ m • z) j
  rw [← hp]
  simp only [ocCellDrift, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  rw [CycleReference.ocEll_sq_eq hν]
  field_simp

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The supplied classical cell Sobolev bound controls its genuine native higher jet. -/

theorem finiteSmoothPeriodicHk_component_enorm_le (K : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) (a : JetIndex2 K) :
    ‖(finiteSmoothPeriodicHk K f hf hp).val a‖ₑ ≤ cellSobolevNorm K f := by
  have hfa : ContDiff ℝ (a.1.val : ℕ∞) f :=
    hf.of_le (by exact_mod_cast Nat.le_of_lt_succ a.1.isLt)
  have hcont := (orderedDerivative_contDiff a.2 0 f
    (by simpa only [zero_add] using hfa)).continuous
  have he : ‖(finiteSmoothPeriodicHk K f hf hp).val a‖ₑ = cellL2Norm (orderedDerivative a.2 f) := by
    rw [Lp.enorm_def, cellL2Norm]
    exact eLpNorm_congr_ae (finiteSmoothPeriodicHk_jet_ae K f hf hp a)
  rw [he]
  apply le_trans (eLpNorm_mono_ae_real hcont.aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall (fun x => ChartTransport.norm_orderedDerivative_le hfa a.2 x)))
  change cellL2Norm (fun x => ‖iteratedFDeriv ℝ a.1.val f x‖) ≤ _
  unfold cellSobolevNorm
  exact Finset.single_le_sum (f := fun b : ℕ => cellL2Norm (fun x => ‖iteratedFDeriv ℝ b f x‖))
    (fun _ _ => bot_le)
    (Finset.mem_range.mpr a.1.isLt)

theorem finiteSmoothPeriodicHk_enorm_le (K : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    ‖finiteSmoothPeriodicHk K f hf hp‖ₑ ≤
      (Fintype.card (JetIndex2 K) : ℝ≥0∞) * cellSobolevNorm K f := by
  apply (cellTorusHk_enorm_le_components _).trans
  calc
    (∑ a : JetIndex2 K, ‖(finiteSmoothPeriodicHk K f hf hp).val a‖ₑ) ≤
        ∑ _ : JetIndex2 K, cellSobolevNorm K f :=
      Finset.sum_le_sum (fun a _ => finiteSmoothPeriodicHk_component_enorm_le K f hf hp a)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The quadratic base of a polynomial weight has its exact adjoint defect. -/

theorem scalarAdjointOperator_quadratic (v : ℝ → Vec 2 → Vec 2) (F H : ℝ → Vec 2 → ℝ)
    (hF : ∀ t, ContDiff ℝ 2 (F t)) (hH : ∀ t, ContDiff ℝ 2 (H t))
    (htF : ∀ z, Differentiable ℝ (fun t => F t z))
    (htH : ∀ z, Differentiable ℝ (fun t => H t z)) (t : ℝ) (z : Vec 2) :
    scalarAdjointOperator v (fun s x => 1 + F s x ^ 2 + H s x ^ 2) t z =
      2 * F t z * scalarAdjointOperator v F t z +
      2 * H t z * scalarAdjointOperator v H t z +
      2 * ((∑ i : Fin 2, (fderiv ℝ (F t) z (basisVec i)) ^ 2) +
        ∑ i : Fin 2, (fderiv ℝ (H t) z (basisVec i)) ^ 2) := by
  rw [scalarAdjointOperator_add v (fun s x => 1 + F s x ^ 2) (fun s x => H s x ^ 2)
    (fun s => contDiff_const.add ((hF s).pow 2)) (fun s => (hH s).pow 2)
    (fun x => differentiable_const 1 |>.add ((htF x).pow 2)) (fun x => (htH x).pow 2)]
  rw [scalarAdjointOperator_add v (fun _ _ => 1) (fun s x => F s x ^ 2)
    (fun _ => contDiff_const) (fun s => (hF s).pow 2)
    (fun _ => differentiable_const 1) (fun x => (htF x).pow 2)]
  rw [scalarAdjointOperator_const, scalarAdjointOperator_power v F hF htF,
    scalarAdjointOperator_power v H hH htH]
  norm_num
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Differences of the actual finite smooth periodic carriers have the classical difference norm budget. -/

theorem finiteSmoothPeriodicHk_value_ae (K : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    (torusHkValueCLM (finiteSmoothPeriodicHk K f hf hp) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] f := by
  have h := finiteSmoothPeriodicHk_jet_ae K f hf hp (valueIndex2 K)
  change (torusHkValueCLM (finiteSmoothPeriodicHk K f hf hp) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
    orderedDerivative (Fin.elim0 : DerivativeWord2 0) f at h
  simpa only [orderedDerivative_zero] using h

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A finite classical cell budget gives an explicit real native norm price. -/

theorem finiteSmoothPeriodicHk_norm_le_of_budget (K : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f)
    (A : ℝ) (hA : 0 ≤ A) (hb : cellSobolevNorm K f ≤ ENNReal.ofReal A) :
    ‖finiteSmoothPeriodicHk K f hf hp‖ ≤ (Fintype.card (JetIndex2 K) : ℝ) * A := by
  have he := (finiteSmoothPeriodicHk_enorm_le K f hf hp).trans (mul_le_mul' le_rfl hb)
  have hcard : (Fintype.card (JetIndex2 K) : ℝ≥0∞) =
      ENNReal.ofReal (Fintype.card (JetIndex2 K) : ℝ) := (ENNReal.ofReal_natCast _).symm
  rw [← ofReal_norm, hcard, ← ENNReal.ofReal_mul (by positivity)] at he
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hA)).mp he

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The literal normalized coordinate gradient is uniformly controlled on the cell duration scale. -/

theorem adjointCellCoordinate_gradient_sq_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (yc : Vec 2) (t : ℝ) (z : Vec 2) (j i : Fin 2) :
    (fderiv ℝ (fun x => adjointCellCoordinate α q Λ ζ m ν B T yc t x j) z (basisVec i)) ^ 2 ≤
      2 * C * (ocEll q Λ m ν ^ 2 / T) := by
  rw [adjointCellCoordinate_gradient hΛ hζ, CycleReference.ocEll_sq_eq hν]
  exact normalized_gradient_sq_le hν hB hT
    (adjointCoordinate_gradient_enhancement hΛ hζ hν he _ _ j i)

theorem adjointCellCoordinate_gradient_sum_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (yc : Vec 2) (t : ℝ) (z : Vec 2) :
    (∑ j : Fin 2, ∑ i : Fin 2,
      (fderiv ℝ (fun x => adjointCellCoordinate α q Λ ζ m ν B T yc t x j) z (basisVec i)) ^ 2) ≤
      8 * C * (ocEll q Λ m ν ^ 2 / T) := by
  have h00 := adjointCellCoordinate_gradient_sq_bound hΛ hζ hν hB hT he yc t z 0 0
  have h01 := adjointCellCoordinate_gradient_sq_bound hΛ hζ hν hB hT he yc t z 0 1
  have h10 := adjointCellCoordinate_gradient_sq_bound hΛ hζ hν hB hT he yc t z 1 0
  have h11 := adjointCellCoordinate_gradient_sq_bound hΛ hζ hν hB hT he yc t z 1 1
  simp only [Fin.sum_univ_two]
  linarith only [h00, h01, h10, h11]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact raw and Hilbert representatives of the same fast subtraction. -/

theorem fibreAdjointFast_native_class_ae
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (ell : ℕ × ℕ → ℝ → Vec 2 → ℂ) (ξ : Fin 2 → ℂ)
    (D : ℝ → RawJet2 1 ℂ) (s t : ℝ)
    (hs : MemLp (cellValue D (-t)) 2 (volume.restrict AVenhance.unitCube))
    (ht : MemLp (cellValue D (-s)) 2 (volume.restrict AVenhance.unitCube))
    (hr : MemLp (cellValue (fibreSeriesJet r ξ) t) 2 (volume.restrict AVenhance.unitCube))
    (hl : MemLp (fibreSeriesFun ell ξ s) 2 (volume.restrict AVenhance.unitCube)) :
    let R := cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1
    let c := cellComplexPair (cellRawTrace D (-t))
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R)
    let phase := Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)
    ((cellRawTrace D (-s) - cellScalarCLM c (cellScalarCLM phase
      (cellSourceSlice (fibreSeriesFun ell ξ) s)) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fibreAdjointFastPart r lam ell ξ D s t := by
  let R := cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1
  let c := cellComplexPair (cellRawTrace D (-t))
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R)
  let phase := Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)
  have hc : c = ∫ y in AVenhance.unitCube,
      (1 + cellValue (fibreSeriesJet r ξ) t y) * cellValue D (-t) y := by
    dsimp only [c]
    unfold cellComplexPair
    apply integral_congr_ae
    filter_upwards [cellRawTrace_ae D (-t) hs, cellFiberConj_ae R,
      cellRawTrace_add_one_ae (fibreSeriesJet r ξ) t hr] with y hy hz hR
    rw [hy, hz, star_star, hR]
    ring
  filter_upwards [Lp.coeFn_sub (cellRawTrace D (-s))
      (cellScalarCLM c (cellScalarCLM phase (cellSourceSlice (fibreSeriesFun ell ξ) s))),
    cellRawTrace_ae D (-s) ht,
    cellScalarCLM_ae c (cellScalarCLM phase (cellSourceSlice (fibreSeriesFun ell ξ) s)),
    cellScalarCLM_ae phase (cellSourceSlice (fibreSeriesFun ell ξ) s),
    cellSourceSlice_ae (fibreSeriesFun ell ξ) s hl] with x hx hd h1 h2 he
  rw [hx]
  simp only [Pi.sub_apply]
  rw [hd, h1, h2, he, hc]
  unfold fibreAdjointFastPart
  dsimp only [phase]
  ring

/-! Exact raw and Hilbert representatives of the same fast subtraction. -/

theorem fibreFast_native_class_ae
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (ell : ℕ × ℕ → ℝ → Vec 2 → ℂ) (ξ : Fin 2 → ℂ)
    (D : ℝ → RawJet2 1 ℂ) (s t : ℝ)
    (hs : MemLp (cellValue D s) 2 (volume.restrict AVenhance.unitCube))
    (ht : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube))
    (hr : MemLp (cellValue (fibreSeriesJet r ξ) t) 2 (volume.restrict AVenhance.unitCube))
    (hl : MemLp (fibreSeriesFun ell ξ s) 2 (volume.restrict AVenhance.unitCube)) :
    let c := cellComplexPair (cellRawTrace D s)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellSourceSlice (fibreSeriesFun ell ξ) s))
    let phase := Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)
    ((cellRawTrace D t - cellScalarCLM c (cellScalarCLM phase
      (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1)) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fibreFastPart r lam ell ξ D s t := by
  let c := cellComplexPair (cellRawTrace D s)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
      (cellSourceSlice (fibreSeriesFun ell ξ) s))
  let phase := Complex.exp (∫ τ in s..t, fibreSeriesC lam ξ τ)
  let R := cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1
  have hc : c = ∫ y in AVenhance.unitCube, fibreSeriesFun ell ξ s y * cellValue D s y := by
    dsimp only [c]
    rw [cellComplexPair_conjugate_source_slice _ s hl]
    unfold cellMean
    apply integral_congr_ae
    filter_upwards [cellRawTrace_ae D s hs] with y hy
    rw [hy]
  filter_upwards [Lp.coeFn_sub (cellRawTrace D t) (cellScalarCLM c (cellScalarCLM phase R)),
    cellRawTrace_ae D t ht, cellScalarCLM_ae c (cellScalarCLM phase R),
    cellScalarCLM_ae phase R, cellRawTrace_add_one_ae (fibreSeriesJet r ξ) t hr]
    with x hx hd h1 h2 hR
  rw [hx]
  simp only [Pi.sub_apply]
  rw [hd, h1, h2, hR, hc]
  unfold fibreFastPart
  dsimp only [phase]
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Literal smooth representatives preserve the zero-order norm of graph differences. -/

theorem cellL2Norm_fibreSeries_difference_congr
    (r r' s s' : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (hr : ∀ p t a, r p t a =ᵐ[volume.restrict AVenhance.unitCube] r' p t a)
    (hs : ∀ p t a, s p t a =ᵐ[volume.restrict AVenhance.unitCube] s' p t a)
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellL2Norm (fun x => cellValue (fibreSeriesJet r ξ) t x -
      cellValue (fibreSeriesJet s ξ) t x) =
    cellL2Norm (fun x => cellValue (fibreSeriesJet r' ξ) t x -
      cellValue (fibreSeriesJet s' ξ) t x) := by
  apply eLpNorm_congr_ae
  exact (fibreSeriesJet_congr_ae_sections r r' hr ξ t (valueIndex2 1)).sub
    (fibreSeriesJet_congr_ae_sections s s' hs ξ t (valueIndex2 1))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! A stored source projection pairs the full measurable dual with a contractive H1 test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1SpectralCutoff_gradient (N : ℕ) (Z : PlaneHk Set.univ 1 E) (k : Fin 2) :
    planeH1GradientOperator (planeH1SpectralCutoff N Z) k =
      hilbertProjection N (planeH1GradientOperator Z k) := by
  change univToPlane ((hilbertBandHk N 1 (univToPlane (Z.val (valueIndex2 1)))).val
    ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) = _
  rw [hilbertBandHk_of_planeHk_component, univToPlane_planeToUniv]
  rfl

theorem planeProjectedJetSourcePair_eq_dual (N : ℕ) {K : ℕ} (α : JetIndex2 K)
    (H : PlaneHk Set.univ K E)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (Z : PlaneHk Set.univ 1 E) :
    planeProjectedJetSourcePair N α H S Z =
      inner ℝ (planeSourceDual (planeJetReadoutOperator K α H) (planeJetFluxOperator K α S))
        (planeH1SpectralCutoff N Z) := by
  rw [planeSourceDual_pair, planeH1SpectralCutoff_value]
  simp only [planeProjectedJetSourcePair, planeJetReadoutOperator_apply, PiLp.inner_apply]
  simp_rw [planeH1SpectralCutoff_gradient, planeJetFluxOperator_apply, hilbertProjection_inner]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Periodic classical entrance norms transfer through genuine native propagation. -/

theorem torusHigher_periodic_entrance_sobolev_transfer (J : ℕ)
    (g₀ g₁ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀) (hg₁ : ContDiff ℝ (J : ℕ∞) g₁)
    (W : TorusHk J ℂ)
    (hv : (torusHkValueCLM W : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g₁)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ‖W‖ ^ 2 ≤ C ^ 2 * ‖finiteSmoothPeriodicHk J g₀ hg₀ hp₀‖ ^ 2) :
    cellSobolevNorm J g₁ ≤
      ((∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
        ENNReal.ofReal C * (Fintype.card (JetIndex2 J) : ℝ≥0∞)) * cellSobolevNorm J g₀ := by
  have hn : ‖W‖ ≤ C * ‖finiteSmoothPeriodicHk J g₀ hg₀ hp₀‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    simpa only [mul_pow] using hb
  have he : ‖W‖ₑ ≤ ENNReal.ofReal C * ‖finiteSmoothPeriodicHk J g₀ hg₀ hp₀‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hn
  calc
    cellSobolevNorm J g₁ ≤ _ := torusHigher_smooth_cellSobolevNorm_le W g₁ hg₁ hv
    _ ≤ (∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
        (ENNReal.ofReal C * ((Fintype.card (JetIndex2 J) : ℝ≥0∞) * cellSobolevNorm J g₀)) :=
      mul_le_mul' le_rfl (he.trans (mul_le_mul' le_rfl (finiteSmoothPeriodicHk_enorm_le J g₀ hg₀ hp₀)))
    _ = _ := by simp only [mul_assoc]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Spatial jet bounds for translated cell shears, independent of the translation. -/

 theorem cellCosine_spatial_jet_bound (j : Fin 2) (phase : ℝ) (n : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (CycleDamping.cellCosine j phase) z‖ ≤ (2 * Real.pi) ^ n := by
  let C : Vec 2 →L[ℝ] ℝ := (2 * Real.pi) • ContinuousLinearMap.proj j
  let f : ℝ → ℝ := fun x => Real.cos (x + 2 * Real.pi * phase)
  have hC : ‖C‖ ≤ 2 * Real.pi := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖2 * Real.pi * x j‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (by positivity)
  have hf : ContDiff ℝ n f := by dsimp [f]; fun_prop
  have he : CycleDamping.cellCosine j phase = f ∘ C := by
    funext x
    change Real.cos (2 * Real.pi * (x j + phase)) = Real.cos (2 * Real.pi * x j + 2 * Real.pi * phase)
    congr 1
    ring
  have hb : ‖iteratedFDeriv ℝ n f (C z)‖ ≤ 1 := by
    dsimp [f]
    rw [iteratedFDeriv_comp_add_right, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_cos_le_one n _
  rw [he, C.iteratedFDeriv_comp_right hf z le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (C z)‖ * ∏ _ : Fin n, ‖C‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * ‖C‖ ^ n := by simpa using mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ ‖C‖ ^ n)
    _ ≤ (2 * Real.pi) ^ n := by simpa using pow_le_pow_left₀ (norm_nonneg C) hC n

 theorem cellCosine_scalar_jet_bound (j : Fin 2) (phase A : ℝ) (n : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun x => A * CycleDamping.cellCosine j phase x) z‖ ≤
      |A| * (2 * Real.pi) ^ n := by
  change ‖iteratedFDeriv ℝ n (fun x => A • CycleDamping.cellCosine j phase x) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((CycleDamping.cellCosine_smooth j phase).of_le
    (by simp : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).contDiffAt, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (cellCosine_spatial_jet_bound j phase n z) (abs_nonneg A)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Actual cell weak derivatives have exactly the classical Fourier multipliers. -/

local instance cellH1FourierDerivativeMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem cellH1_fourierDerivative (u : TorusHk 1 ℂ) (i : Fin 2) (n : Fin 2 → ℤ) :
    mFourierCoeff (scalarCellToTorus (cellDerivativeCLM i u)) n =
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) *
        mFourierCoeff (scalarCellToTorus (torusHkValueCLM u)) n := by
  rw [scalarCellToTorus_fourierCoeff_pair, scalarCellToTorus_fourierCoeff_pair]
  have hi := cellComplexDerivative_skew i u (cellComplexFourierModeH1 n)
  rw [cellComplexFourierModeH1_value, cellComplexFourierModeH1_derivative,
    ← cellScalarCLM_smul, cellComplexPair_scalar_right] at hi
  have hs : star (((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ))) =
      -((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) := by
    have he : ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) =
        ((2 * Real.pi * (n i : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, star_mul, show star ((2 * Real.pi * (n i : ℝ) : ℝ) : ℂ) =
      ((2 * Real.pi * (n i : ℝ) : ℝ) : ℂ) from Complex.conj_ofReal _,
      show star Complex.I = -Complex.I by simp]
    ring
  rw [hs, neg_mul, neg_neg] at hi
  exact hi

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual graph inverse equation is preserved by smooth coefficient value representatives. -/

theorem fibreGraph_value_replacement_inverse {η ξ0 Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph η G v ξ0 Cg r lam)
    (f : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (hp : ∀ p t, AVenhance.IsZ2Periodic (f p t))
    (hm : ∀ p, StronglyMeasurable (fun z : ℝ × Vec 2 => f p z.1 z.2))
    (he : ∀ p t, f p t =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) t)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ0) :
    IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fibreGraphSource η v ξ (cellValue (fibreSeriesJet (fibreGraphValueReplacement r f) ξ)))
      (fibreGraphFlux η G ξ (cellValue (fibreSeriesJet (fibreGraphValueReplacement r f) ξ)))
      (fibreSeriesJet (fibreGraphValueReplacement r f) ξ) := by
  let D := fibreSeriesJet r ξ
  let s := fibreSeriesFun f ξ
  let E := fun t => cellValueRepresentativeJet (D t) (s t)
  have hE : fibreSeriesJet (fibreGraphValueReplacement r f) ξ = E := by
    funext t
    exact fibreGraphValueReplacement_series r f ξ t
  have hvalue : cellValue E = s := by
    funext t
    exact cellValueRepresentativeJet_value (D t) (s t)
  have hae : ∀ t, s t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t := by
    intro t
    exact fibreSeriesFun_congr_ae f (fun p => cellValue (r p)) he ξ t
  have hsm : AEStronglyMeasurable (fun z : ℝ × Vec 2 => s z.1 z.2)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) := by
    exact (AEMeasurable.tsum (fun p => ((hm p).aestronglyMeasurable.aemeasurable).const_mul
      (fibreMonomial ξ p))).aestronglyMeasurable
  have hi := (hgraph.2.1 ξ hξ).2.2.1
  have hsol := cellSolution_value_representative_replacement Set.univ _ _ _ D s hi.1
    (fibreSeriesFun_periodic f hp ξ) hsm hae
  have hsol' := cellSolution_source_congr_sections Set.univ _
    (fibreGraphSource η v ξ (cellValue D)) (fibreGraphSource η v ξ s)
    (fibreGraphFlux η G ξ (cellValue D)) (fibreGraphFlux η G ξ s) E
    (Filter.Eventually.of_forall (fibreGraphSource_value_congr η v ξ (cellValue D) s
      (fun t => (hae t).symm)))
    (Filter.Eventually.of_forall (fibreGraphFlux_value_congr η G ξ (cellValue D) s
      (fun t => (hae t).symm))) hsol
  rw [hE, hvalue]
  refine ⟨hsol', ?_, ?_⟩
  · intro t
    change cellMean (s t) = 0
    unfold cellMean
    exact (integral_congr_ae (hae t)).trans (hi.2.1 t)
  · rw [cellValue_replacement_energyNorm Set.univ D s hae]
    exact hi.2.2

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Exact relaxation exponent and displacement size in the quiet residual estimate. -/

theorem adjoint_relaxation_exponent {q α : ℝ} {Λ m : ℕ} {ν : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    ocMu q Λ m ν * (ocTau α q Λ m / 12) =
      Real.pi ^ 2 * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2) := by
  have hep := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  rw [CycleReference.ocEll_sq_eq hν, ocMu]
  field_simp
  ring

theorem adjoint_memory_displacement_sq_bound {α q : ℝ} {Λ m : ℕ} {ν B C : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B) :
    ((ocMu q Λ m ν)⁻¹ *
      |2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) * (ocEpsilon q Λ m)⁻¹|) ^ 2 ≤
        C * B * ocEll q Λ m ν ^ 2 := by
  have hep := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  unfold ocMu
  rw [shear_displacement_memory_cancel _ _ _ hep hν, sq_abs, CycleReference.ocEll_sq_eq hν]
  apply enhanced_shear_displacement_budget hep hν (Real.rpow_pos_of_pos hep _).le hB hC
  simpa only [epsilon_enhancement_power _ _ hep.le] using he

theorem adjointResidual_cell_duration_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m)
    (hdur : Real.sqrt T * ocEll q Λ m ν / ocTau α q Λ m *
      Real.exp (-Real.pi ^ 2 * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) ≤ 1)
    (t : ℝ) (y : Vec 2) (j : Fin 2) :
    |(ocEll q Λ m ν ^ 2 / Real.sqrt (B * T)) * adjointResidual α q Λ ζ m ν t y j| ≤
      K * (1 + C) * (ocEll q Λ m ν ^ 2 / T) := by
  have hep := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hell : 0 ≤ ocEll q Λ m ν := by unfold ocEll; positivity
  have hμ : 0 ≤ (ocMu q Λ m ν)⁻¹ := by unfold ocMu; positivity
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  apply quiet_residual_cell_bound hB hT hτ hell (Real.exp_pos _).le hC hK
    (mul_nonneg hμ (abs_nonneg _))
    (adjoint_memory_displacement_sq_bound hΛ hν hB.le hC he) hdur
  have hr := adjointResidual_abs_bound (α := α) (q := q) (m := m) hΛ hζ hν K hK hb t y j
  have hex : -ocMu q Λ m ν * (ocTau α q Λ m / 12) =
      -Real.pi ^ 2 * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2) := by
    rw [neg_mul, adjoint_relaxation_exponent hΛ hν]
    ring
  rw [hex] at hr
  convert hr using 1
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane
open AVRegularity.Analysis.Convolution AVRegularity.Weighted
open scoped Topology
namespace AVRegularity.CycleWords

/-! Actual Bochner Sobolev sources differentiate the original weak time equation at every order. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem plane_ordered_source_increment_of_dual_memLp {K : ℕ} {a b s t : ℝ}
    (U H : ℝ → PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (heq : ∀ Z : PlaneHk Set.univ 1 E,
      inner ℝ (planeHkValueOperator K (U t)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeHkValueOperator K (U s)) (planeHkValueOperator 1 Z) =
      ∫ r in s..t, inner ℝ (planeHkValueOperator K (H r)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeFluxValueOperator K (S r)) (planeH1GradientOperator Z))
    (α : JetIndex2 K)
    (hdual : MemLp (fun r => planeSourceDual (planeJetReadoutOperator K α (H r))
      (planeJetFluxOperator K α (S r))) 2 (volume.restrict (Set.Icc a b)))
    (Z : PlaneHk Set.univ 1 E) :
    inner ℝ (univToPlane ((U t).val α)) (planeHkValueOperator 1 Z) -
      inner ℝ (univToPlane ((U s).val α)) (planeHkValueOperator 1 Z) =
      ∫ r in s..t, planeJetSourcePair α (H r) (S r) Z := by
  let dual := fun r => planeSourceDual (planeJetReadoutOperator K α (H r))
    (planeJetFluxOperator K α (S r))
  have hi : IntervalIntegrable dual volume s t := by
    apply intervalIntegrable_iff.mpr
    rw [Set.uIoc_of_le hst]
    exact (hdual.integrable (by norm_num)).mono_measure
      (Measure.restrict_mono
        (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)) le_rfl)
  have hl := ((tendsto_hilbertProjection (univToPlane ((U t).val α))).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := planeHkValueOperator 1 Z))).sub
      ((tendsto_hilbertProjection (univToPlane ((U s).val α))).inner (𝕜 := ℝ)
        (tendsto_const_nhds (x := planeHkValueOperator 1 Z)))
  have hr := tendsto_contractive_test_time_pairing hst dual hi Z
    (fun N => planeH1SpectralCutoff N Z)
    (fun N => planeH1SpectralCutoff_norm_le N Z) (tendsto_planeH1SpectralCutoff Z)
  simp only [dual, planeSourceDual_pair, PiLp.inner_apply, planeJetReadoutOperator_apply,
    planeJetFluxOperator_apply] at hr
  have hr' : Tendsto (fun N => ∫ r in s..t, planeProjectedJetSourcePair N α (H r) (S r) Z)
      atTop (𝓝 (∫ r in s..t, planeJetSourcePair α (H r) (S r) Z)) := by
    simpa only [planeProjectedJetSourcePair_eq_dual, planeJetSourcePair,
      planeSourceDual_pair, PiLp.inner_apply, planeJetReadoutOperator_apply,
      planeJetFluxOperator_apply] using hr
  exact tendsto_nhds_unique hl
    (hr'.congr (fun N => (plane_ordered_projected_source_increment N U H S s t heq α Z).symm))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Actual weak plane H1 data gives almost every Bloch fibre in the committed cell H1 graph. -/

local instance planeBlochH1GraphMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

def planeBlochRealCellJet (a : Vec 2) (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2))) (θ : Vec 2) :
    JetL2 (volume.restrict AVenhance.unitCube) 1 ℂ :=
  scalarCellFirstJet (planeScalarBlochTransform a 1 (by norm_num) (ofRealL2 volume f) θ)
    (fun i => planeBlochCellDerivative θ i
      (planeScalarBlochTransform a 1 (by norm_num) (ofRealL2 volume f) θ)
      (planeScalarBlochTransform a 1 (by norm_num) (ofRealL2 volume (g i)) θ))

theorem planeBlochRealCellJet_mem_H1_ae (a : Vec 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, HasWeakPartialDerivOn Set.univ i f (g i)) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a 1),
      planeBlochRealCellJet a f g θ ∈ cellComplexH1Submodule := by
  have hd (i : Fin 2) := planeBlochCellDerivative_real_weakDerivative_ae a f (g i) i (hfg i)
  filter_upwards [ae_all_iff.mpr hd] with θ hθ
  apply scalarCellFirstJet_mem_H1
  exact hθ

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution Metric Filter Topology
open AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The literal homogeneous coefficient of the original L2 series is a native frequency derivative. -/

theorem torusHigher_native_homogeneous_coefficient (K n : ℕ)
    (c : ℕ × ℕ → ComplexCellL2) (R : ℝ≥0) (hR : 0 < R)
    (hs : Summable (fun p => ‖c p‖ * (R : ℝ) ^ (p.1 + p.2)))
    (F : (Fin 2 → ℂ) → TorusHk K ℂ)
    (hF : ∀ ξ ∈ ball (0 : Fin 2 → ℂ) (R : ℝ),
      torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p)
    (hf : ContDiffAt ℂ (n : WithTop ℕ∞) F 0) (ξ : Fin 2 → ℂ) :
    ∃ U : TorusHk K ℂ,
      torusHkValueCLM U = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, fibreMonomial ξ p • c p := by
  let g := fun ξ => ∑' p, fibreMonomial ξ p • c p
  have hp := fibreBivariateSum_hasFPowerSeriesOnBall c R hR hs
  have he : g =ᶠ[𝓝 (0 : Fin 2 → ℂ)] (torusHigherComplexValueCLM K) ∘ F := by
    filter_upwards [ball_mem_nhds (0 : Fin 2 → ℂ) (show (0 : ℝ) < R from hR)] with x hx
    exact (hF x hx).symm
  have hd : torusHkValueCLM (iteratedFDeriv ℂ n F 0 (fun _ => ξ)) =
      iteratedFDeriv ℂ n g 0 (fun _ => ξ) := by
    rw [(he.iteratedFDeriv (𝕜 := ℂ) n).self_of_nhds]
    rw [(torusHigherComplexValueCLM K).iteratedFDeriv_comp_left hf le_rfl]
    rfl
  refine ⟨((n.factorial : ℂ)⁻¹) • iteratedFDeriv ℂ n F 0 (fun _ => ξ), ?_⟩
  rw [torusHigher_complex_value_smul, hd, ← hp.factorial_smul ξ n, fibreFormalSeries_diag]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The full graph predicate survives smooth periodic changes of its coefficient values. -/

theorem fibreGraph_value_replacement_isFibreGraph {η ξ0 Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph η G v ξ0 Cg r lam)
    (f : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (hp : ∀ p t, AVenhance.IsZ2Periodic (f p t))
    (hm : ∀ p, StronglyMeasurable (fun z : ℝ × Vec 2 => f p z.1 z.2))
    (he : ∀ p t, f p t =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) t) :
    IsFibreGraph η G v ξ0 Cg (fibreGraphValueReplacement r f) lam := by
  let R := fibreGraphValueReplacement r f
  have hae : ∀ p t a, R p t a =ᵐ[volume.restrict AVenhance.unitCube] r p t a := by
    intro p t a
    exact cellValueRepresentativeJet_ae (r p t) (f p t) (he p t) a
  have hnorm : ∀ p, cellEnergyNorm Set.univ (R p) = cellEnergyNorm Set.univ (r p) := by
    intro p
    exact cellEnergyNorm_congr_all_sections Set.univ _ _ (hae p)
  refine ⟨hgraph.1, ?_, ?_, hgraph.2.2.2⟩
  · intro ξ hξ
    have h := hgraph.2.1 ξ hξ
    refine ⟨?_, h.2.1, fibreGraph_value_replacement_inverse r lam hgraph f hp hm he ξ hξ,
      ?_, ?_⟩
    · change (∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * cellEnergyNorm Set.univ (R p)) < ⊤
      simpa only [hnorm] using h.1
    · intro t
      have hev := fibreSeriesJet_congr_ae_sections R r hae ξ t (valueIndex2 1)
      have hmean : cellMean (fun x => ((Real.sqrt η : ℂ) *
          ∑ k, (v t x k : ℂ) * ξ k) * cellValue (fibreSeriesJet R ξ) t x) =
          cellMean (fun x => ((Real.sqrt η : ℂ) * ∑ k, (v t x k : ℂ) * ξ k) *
            cellValue (fibreSeriesJet r ξ) t x) := by
        unfold cellMean
        apply integral_congr_ae
        filter_upwards [hev] with x hx
        exact congrArg (fun z : ℂ => ((Real.sqrt η : ℂ) *
          ∑ k, (v t x k : ℂ) * ξ k) * z) hx
      rw [hmean]
      exact h.2.2.2.1 t
    · rw [cellEnergyNorm_congr_all_sections Set.univ _ _
        (fibreSeriesJet_congr_ae_sections R r hae ξ)]
      exact h.2.2.2.2
  · intro n ξ
    rw [cellEnergyNorm_congr_all_sections Set.univ _ _
      (fibreHomogeneousJet_congr_ae_sections R r hae ξ n)]
    exact hgraph.2.2.1 n ξ

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Genuine Bloch H1 fields are strongly measurable in the committed closed graph. -/

local instance planeBlochH1MeasurableMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem planeBlochCellDerivative_aestronglyMeasurable (μ : Measure (Vec 2))
    (u v : Vec 2 → ScalarTorusL2) (hu : AEStronglyMeasurable u μ)
    (hv : AEStronglyMeasurable v μ) (i : Fin 2) :
    AEStronglyMeasurable (fun θ => planeBlochCellDerivative θ i (u θ) (v θ)) μ := by
  have hc : Continuous (fun θ : Vec 2 => (2 * (Real.pi : ℂ) * Complex.I) * (θ i : ℂ)) := by
    fun_prop
  exact hv.sub (hc.aestronglyMeasurable.smul hu)

theorem scalarCellFirstJet_aestronglyMeasurable (μ : Measure (Vec 2))
    (u : Vec 2 → ScalarTorusL2) (d : Fin 2 → Vec 2 → ScalarTorusL2)
    (hu : AEStronglyMeasurable u μ) (hd : ∀ i, AEStronglyMeasurable (d i) μ) :
    AEStronglyMeasurable (fun θ => scalarCellFirstJet (u θ) (fun i => d i θ)) μ := by
  apply finitePiLp_aestronglyMeasurable
  intro a
  change AEStronglyMeasurable (fun θ => if h : a.1.val = 0 then scalarTorusToCell (u θ)
    else scalarTorusToCell (d (a.2 ⟨0, by omega⟩) θ)) μ
  split_ifs
  · exact scalarTorusToCell.continuous.comp_aestronglyMeasurable hu
  · exact scalarTorusToCell.continuous.comp_aestronglyMeasurable (hd _)

theorem planeBlochRealCellJet_aestronglyMeasurable (a : Vec 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2))) :
    AEStronglyMeasurable (planeBlochRealCellJet a f g)
      (volume.restrict (planeFrequencyCell a 1)) := by
  apply scalarCellFirstJet_aestronglyMeasurable
  · exact Lp.aestronglyMeasurable _
  · intro i
    exact planeBlochCellDerivative_aestronglyMeasurable _ _ _
      (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) i

def planeBlochRealH1 (a : Vec 2) (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2))) (θ : Vec 2) : CellComplexH1 := by
  classical
  exact if h : planeBlochRealCellJet a f g θ ∈ cellComplexH1Submodule then
    ⟨planeBlochRealCellJet a f g θ, h⟩ else 0

theorem planeBlochRealH1_val_ae (a : Vec 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, HasWeakPartialDerivOn Set.univ i f (g i)) :
    (fun θ => (planeBlochRealH1 a f g θ).val) =ᵐ[volume.restrict (planeFrequencyCell a 1)]
      planeBlochRealCellJet a f g := by
  filter_upwards [planeBlochRealCellJet_mem_H1_ae a f g hfg] with θ hθ
  simp only [planeBlochRealH1, dite_eq_left hθ]

theorem planeBlochRealH1_aestronglyMeasurable (a : Vec 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, HasWeakPartialDerivOn Set.univ i f (g i)) :
    AEStronglyMeasurable (planeBlochRealH1 a f g)
      (volume.restrict (planeFrequencyCell a 1)) := by
  apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
  exact (planeBlochRealCellJet_aestronglyMeasurable a f g).congr
    (planeBlochRealH1_val_ae a f g hfg).symm

end AVRegularity.CycleWords
end
