-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
public import AVRegularity.CoupledEnergy.Variational.TorusCoupledFluxValue
import AVRegularity.CoupledEnergy.Variational.TorusTimeGraph
import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Schur absorption for the actual differentiated coupling fluxes. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- Pairing one actual coupling flux with the target gradient costs exactly its reserve budget. -/
theorem torusCoupledFluxTerm_pairing_abs_le (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t))
    (wi : TorusHk (K i + 1) (h i)) (wj : TorusHk (K i' + 1) (h i')) :
    |inner ℝ
      (factorialWeightedJet ρ (torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp wj).val)
      (factorialWeightedJet ρ (torusGradientTensor wi).val)| ≤
    ((coefficientSeminorm ρ (K i) a b A).toReal * derivativeReserveFactor ρ (K i) (d.1 - 2)) *
      Real.sqrt (gradFactorialNormSq ρ wj.val) * Real.sqrt (gradFactorialNormSq ρ wi.val) := by
  have hc := abs_real_inner_le_norm
    (factorialWeightedJet ρ (torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp wj).val)
    (factorialWeightedJet ρ (torusGradientTensor wi).val)
  simp only [factorialWeightedJet_norm, torusGradientTensor_factorialNormSq] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (torusCoupledFluxTerm_factorialNorm_le ρ hρ K D a b i i' d A hA t ht hC hp wj)
      (Real.sqrt_nonneg _))

/-- The sum of absolute differentiated coupling pairings is absorbed by ν/8 of dissipation. -/
theorem torusCoupledFlux_schurEnergy_abs_sum_le (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (D : ℕ) (a b : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d t))
    (hp : ∀ i i' d, AVenhance.IsZ2Periodic (A i i' d t))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (w : ∀ i, TorusHk (K i + 1) (h i)) :
    (∑ i, ∑ i', ∑ d : admissibleOrders K D i i', (π i)⁻¹ * |inner ℝ
      (factorialWeightedJet ρ (torusCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d)
        (hA i i' d) t ht (hC i i' d) (hp i i' d) (w i')).val)
      (factorialWeightedJet ρ (torusGradientTensor (w i)).val)|) ≤
      (ν / 8) * massGradNormSq ρ π (fun i => (w i).val) := by
  let Y := fun i => Real.sqrt (gradFactorialNormSq ρ (w i).val)
  have hbound : (∑ i, ∑ i', ∑ d : admissibleOrders K D i i', (π i)⁻¹ * |inner ℝ
      (factorialWeightedJet ρ (torusCoupledFluxTerm ρ hρ K D a b i i' d (A i i' d)
        (hA i i' d) t ht (hC i i' d) (hp i i' d) (w i')).val)
      (factorialWeightedJet ρ (torusGradientTensor (w i)).val)|) ≤
      ∑ i, ∑ i', (π i)⁻¹ * couplingReserveBudget ρ K D a b A i i' * Y i * Y i' := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro i' _
    unfold couplingReserveBudget
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d _
    have hb := torusCoupledFluxTerm_pairing_abs_le ρ hρ K D a b i i' d (A i i' d)
        (hA i i' d) t ht (hC i i' d) (hp i i' d) (w i) (w i')
    have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (hπ i).le)
    simpa only [Y, mul_assoc, mul_comm, mul_left_comm] using hm
  have hs := couplingReserveBudget_quadratic_le ν ρ hν hρ π hπ K D a b A hschur Y
  refine hbound.trans (hs.trans_eq ?_)
  congr 1
  unfold massGradNormSq
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Real.sq_sqrt
  rw [← torusGradientTensor_factorialNormSq ρ (w i)]
  exact factorialNormSq_nonneg _ _
end

/-! Native fixed jet and tensor coefficient pairings commute with
subtraction of the common ambient Bochner classes. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [CompleteSpace E] in
theorem coupledHighCoefficient_integral_sub (K : ι → ℕ) {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (P : CoupledHighHilbert (h := h) K →L[ℝ] ComponentL2 (volume.restrict AVenhance.unitCube) E)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖C r x‖ ≤ M)
    (U V : CoupledHighTime (h := h) K a b) (z : ComponentL2 (volume.restrict AVenhance.unitCube) F) :
    (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (P ((U - V) r) x)) (z x)) =
      (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (P (U r) x)) (z x)) -
        (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (P (V r) x)) (z x)) := by
  let Pt := P.compLpL 2 (volume.restrict (Set.Icc a b))
  have he (W : CoupledHighTime (h := h) K a b) :
      (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (Pt W r x)) (z x)) =
      ∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (P (W r) x)) (z x) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : Set.uIoc s t ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le hst]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (ContinuousLinearMap.coeFn_compLpL P W)] with r hr
    rw [hr]
  have hh := Galerkin.intervalCoefficient_integral_sub hs ht hst C hC hc M hM hb (Pt U) (Pt V) z
  rw [← Pt.map_sub U V] at hh
  simpa only [he] using hh
end

/-! Literal temporal integrability for bounded coefficients of common
ambient Sobolev readouts, under interval-only assumptions. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Every bounded native coefficient pairing of the common Sobolev limit is time integrable. -/
theorem coupledHighCoefficient_pairing_integrable (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (U : CoupledHighTime (h := h) K a b)
    (P : CoupledHighHilbert (h := h) K →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) E)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖C r x‖ ≤ M)
    (z : ℝ → Lp F 2 (volume.restrict AVenhance.unitCube))
    (hz : MemLp z 2 (volume.restrict (Set.Icc a b))) :
    Integrable (fun r => ∫ x in AVenhance.unitCube,
      inner ℝ (C r x (P (U r) x)) (z r x)) (volume.restrict (Set.Icc a b)) := by
  have hi := Galerkin.intervalCoefficientTime_pairing_integrable hab C hC hc M hM hb
    (P.compLpL 2 (volume.restrict (Set.Icc a b)) U) z hz
  apply hi.congr
  filter_upwards [ContinuousLinearMap.coeFn_compLpL P U] with r hr
  rw [hr]
end

/-! The native integrated drift term commutes with subtraction, under the
original value-level measurability and bounded velocity assumptions. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusDrift_integral_sub (K : ι → ℕ) {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (v r)) (B : ℝ)
    (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B) (i : ι) (k : Fin 2)
    (U V : CoupledHighTime (h := h) K a b) (φ : TorusHk 1 (h i)) :
    (∫ r in s..t, ∫ x in AVenhance.unitCube, v r x k *
      inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
        fun _ => k⟩ ((U - V) r) x) (Galerkin.torusHkValueCLM φ x)) =
      (∫ r in s..t, ∫ x in AVenhance.unitCube, v r x k *
        inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
          fun _ => k⟩ (U r) x) (Galerkin.torusHkValueCLM φ x)) -
      (∫ r in s..t, ∫ x in AVenhance.unitCube, v r x k *
        inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
          fun _ => k⟩ (V r) x) (Galerkin.torusHkValueCLM φ x)) := by
  let C := fun r x => (v r x k) • ContinuousLinearMap.id ℝ (h i)
  have hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2) :=
    ((measurable_pi_apply k).comp hv).smul measurable_const
  have hCc (r : ℝ) (hr : r ∈ Set.Icc a b) : Continuous (C r) :=
    ((continuous_apply k).comp (hc r hr)).smul continuous_const
  have hB : 0 ≤ B := (norm_nonneg (v s 0)).trans (hb s hs 0)
  have hCb (r : ℝ) (hr : r ∈ Set.Icc a b) (x : Vec 2) : ‖C r x‖ ≤ B := by
    change ‖(v r x k) • ContinuousLinearMap.id ℝ (h i)‖ ≤ B
    rw [norm_smul]
    calc
      ‖v r x k‖ * ‖ContinuousLinearMap.id ℝ (h i)‖ ≤ ‖v r x k‖ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖v r x k‖ := mul_one _
      _ ≤ ‖v r x‖ := norm_le_pi_norm (v r x) k
      _ ≤ B := hb r hr x
  have hh := coupledHighCoefficient_integral_sub K hs ht hst
    (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
    C hC hCc B hB hCb U V (Galerkin.torusHkValueCLM φ)
  simpa only [C, smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left] using hh
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! The native interval coefficient limit for fixed coupled derivative and
tensor readouts, allowing strongly converging projected spatial tests. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Actual interval-only coefficient premises suffice for the coupled weak limit with moving tests. -/
theorem coupledHighCoefficient_moving_test_weak_limit (K : ι → ℕ) {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (U : ℕ → CoupledHighTime (h := h) K a b) (V : CoupledHighTime (h := h) K a b)
    (Q : ℝ) (hu : ∀ n, ‖U n‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (P : CoupledHighHilbert (h := h) K →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) E)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖C r x‖ ≤ M)
    (z : ℕ → Lp F 2 (volume.restrict AVenhance.unitCube))
    (w : Lp F 2 (volume.restrict AVenhance.unitCube)) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => ∫ r in s..t, ∫ x in AVenhance.unitCube,
      inner ℝ (C r x (P (U n r) x)) (z n x)) atTop
      (𝓝 (∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (C r x (P (V r) x)) (w x))) := by
  let Pt := P.compLpL 2 (volume.restrict (Set.Icc a b))
  have hp (n : ℕ) : ‖Pt (U n)‖ ≤ ‖Pt‖ * Q :=
    (Pt.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg Pt))
  have he (W : CoupledHighTime (h := h) K a b)
      (q : Lp F 2 (volume.restrict AVenhance.unitCube)) :
      (∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (C r x (Pt W r x)) (q x)) =
      ∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (C r x (P (W r) x)) (q x) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hsub : Set.uIoc s t ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le hst]
      exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (ContinuousLinearMap.coeFn_compLpL P W)] with r hr
    rw [hr]
  have hlim := Galerkin.intervalCoefficient_integral_weak_limit_moving_test hs ht hst C hC hc
    M hM hb (fun n => Pt (U n)) (Pt V) (‖Pt‖ * Q) hp
    (coupledHighReadout_weak_limit K a b U V hw P) z w hz
  simpa only [he] using hlim

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The native integrated diffusion term commutes with subtraction. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusDiffusion_integral_sub (K : ι → ℕ) {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) (i : ι)
    (U V : CoupledHighTime (h := h) K a b) (φ : TorusHk 1 (h i)) :
    (∫ r in s..t, ∫ x in AVenhance.unitCube,
      inner ℝ (coupledHighGradientCLM (h := h) K i ((U - V) r) x)
        (torusH1GradientL2CLM (E := h i) φ x)) =
      (∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (coupledHighGradientCLM (h := h) K i (U r) x) (torusH1GradientL2CLM (E := h i) φ x)) -
      (∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (coupledHighGradientCLM (h := h) K i (V r) x) (torusH1GradientL2CLM (E := h i) φ x)) := by
  have hh := coupledHighCoefficient_integral_sub K hs ht hst (coupledHighGradientCLM (h := h) K i)
    (fun _ _ => ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin 2 => h i)))
    measurable_const (fun _ _ => continuous_const) 1 (by norm_num)
    (fun _ _ _ => ContinuousLinearMap.norm_id_le) U V (torusH1GradientL2CLM (E := h i) φ)
  simpa only [ContinuousLinearMap.id_apply] using hh

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! The physical diffusion gradient pairing passes through the common coupled
weak limit against strongly converging Fourier-projected H¹ tests. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The original diffusion term converges on every subinterval against projected weak tests. -/
theorem torusDiffusion_projected_test_weak_limit (K : ι → ℕ) {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) (i : ι)
    (U : ℕ → CoupledHighTime (h := h) K a b) (V : CoupledHighTime (h := h) K a b)
    (Q : ℝ) (hu : ∀ n, ‖U n‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (N : ℕ → ℕ) (hN : StrictMono N) (φ : TorusHk 1 (h i)) :
    Tendsto (fun n => ∫ r in s..t, ∫ x in AVenhance.unitCube,
      inner ℝ (coupledHighGradientCLM (h := h) K i (U n r) x)
        (torusH1GradientL2CLM (E := h i) (Galerkin.galerkinProj (N n) φ) x)) atTop
      (𝓝 (∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (coupledHighGradientCLM (h := h) K i (V r) x)
          (torusH1GradientL2CLM (E := h i) φ x))) := by
  have hlim := coupledHighCoefficient_moving_test_weak_limit K hs ht hst U V Q hu hw
    (coupledHighGradientCLM (h := h) K i)
    (fun _ _ => ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin 2 => h i))) measurable_const
    (fun _ _ => continuous_const) 1 (by norm_num)
    (fun _ _ _ => ContinuousLinearMap.norm_id_le)
    (fun n => torusH1GradientL2CLM (E := h i) (Galerkin.galerkinProj (N n) φ))
    (torusH1GradientL2CLM (E := h i) φ)
    ((torusH1Gradient_projected_tendsto φ).comp hN.tendsto_atTop)
  simpa only [ContinuousLinearMap.id_apply] using hlim

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Time measurability of a genuine Sobolev coefficient product follows
from value-level coefficient measurability, independently of its spatial
higher derivatives. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem torusCoefficientCarrier_aestronglyMeasurable (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (U : CoupledHighTime (h := h) K a b)
    (P : CoupledHighHilbert (h := h) K →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) E)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖C r x‖ ≤ M)
    (L : ℕ) (T : ℝ → TorusHk L F)
    (hT : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (T t).val (valueIndex2 L) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => C t x (P (U t) x)) :
    AEStronglyMeasurable T (volume.restrict (Set.Icc a b)) := by
  apply torusCarrier_aestronglyMeasurable_of_integrable_tests _ L T
  intro φ
  have hi := coupledHighCoefficient_pairing_integrable K hab U P C hC hc M hM hb
    (fun _ => torusHkValueCLM φ) (memLp_const _)
  apply hi.congr
  filter_upwards [hT] with t ht
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  change inner ℝ (C t x (P (U t) x)) (torusHkValueCLM φ x) =
    inner ℝ ((T t).val (valueIndex2 L) x) (torusHkValueCLM φ x)
  rw [hx]

end AVRegularity.CoupledEnergy.Variational
end
