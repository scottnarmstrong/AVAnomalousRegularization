-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients
public import AVRegularity.CycleComparison.Lift.SettingAmbientSourceTestPeriodicOfCoefficients
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Lift.SettingAmbientCrossTestTransverse

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal normalized inverse source combines centering and the ordered correction budgets. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem liftCellSource_normalized_mixed_grading_of_terms (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n p q : ℕ) (t : ℝ) (v : ι) (A : Vec 2 →L[ℝ] ℝ) (lam C : ℝ)
    (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hA : ∀ u, IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n t X z u))
    (hbA : ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftA Q Cc f hh n t Y y v) z) X‖ ≤
          C * lam ^ (n + r))
    (B : ℕ → ℕ × ℕ → ℝ)
    (hT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
        liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t X z v))
    (hbT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => (Real.exp ((lam • A) Y))⁻¹ •
            liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t Y y v) z) X‖ ≤
              B j ab * lam ^ (n + r)) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftCellSource Q Cc f hh n t X z v) ∧
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => (Real.exp ((lam • A) Y))⁻¹ • liftCellSource Q Cc f hh n t Y y v) z) X‖ ≤
            (((1 + (2 : ℝ) ^ p) * C) +
              ∑ j ∈ Finset.Icc 1 (n - 2), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, B j ab) *
                lam ^ (n + r) := by
  let F := fun X z => (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f hh n t X z v -
    (Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc f hh n t X v
  let T := fun j (ab : ℕ × ℕ) X z => (Real.exp ((lam • A) X))⁻¹ •
    liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t X z v
  have hm (X : Vec 2) : fieldCellMean (fun z => liftA Q Cc f hh n t X z v) =
      liftMean Q Cc f hh n t X v :=
    AVRegularity.fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
      (liftA_fast_continuous_of_normalized_box Q Cc f hh n p q t A lam hA X)
  have hc := exponential_centered_source_mixed_grading p q n A
    (fun X z => liftA Q Cc f hh n t X z v) C lam hC hlam (hA v) hbA
  simp only [hm, smul_sub] at hc
  have hF : IsBoxSmooth p q F := hc.1
  have hsum j (hj : j ∈ Finset.Icc 1 (n - 2)) :
      IsBoxSmooth p q (fun X z => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab X z) :=
    IsBoxSmooth.sum _ (fun ab hab => hT j hj ab hab)
  have hS : IsBoxSmooth p q (fun X z => ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab X z) := IsBoxSmooth.sum _ hsum
  simp_rw [liftCellSource_normalized_component_expansion]
  change IsBoxSmooth p q (fun X z => -F X z + ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab X z) ∧ _
  refine ⟨hF.neg.add hS, ?_⟩
  intro r hr s hs X z
  have hn := norm_mixed_jet_const_smul (hF.mono hr hs) (-1 : ℝ) X z
  simp only [neg_one_smul, abs_neg, abs_one, one_mul] at hn
  have hsb := norm_mixed_jet_finset_sum_le (Finset.Icc 1 (n - 2)) r s
    (fun j X z => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab X z)
    (fun j hj => (hsum j hj).mono hr hs) X z
  have hsb' : ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => ∑ j ∈ Finset.Icc 1 (n - 2),
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab Y y) z) X‖ ≤
      (∑ j ∈ Finset.Icc 1 (n - 2), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, B j ab) *
        lam ^ (n + r) := by
    apply hsb.trans
    simp only [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    apply (norm_mixed_jet_finset_sum_le _ r s (T j)
      (fun ab hab => (hT j hj ab hab).mono hr hs) X z).trans
    exact Finset.sum_le_sum fun ab hab => hbT j hj ab hab r hr s hs X z
  have hb := norm_mixed_jet_add_le (hF.neg.mono hr hs) (hS.mono hr hs) X z
  rw [hn] at hb
  exact hb.trans ((add_le_add (hc.2 r hr s hs X z) hsb').trans_eq (by ring))
end

/-! Actual normalized mean differences inherit the quantitative uncentered difference bound. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D hh n p q : ℕ} {Q Qi : LiftOperatorData ι h D} {Cc Ci : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {K Ki : (Vec 2 →L[ℝ] ℝ) → ℝ} {M Mi : ι → ι → ℝ}

theorem ambient_paired_uncentered_mean_grading
    (data : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K M)
    (datai : AmbientLiftUncenteredData par a b hab lam hh n p q Qi Ci Ki Mi)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (C g : ℝ)
    (hb : ∀ j ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ j (fun Y =>
        normalizedLiftUncenteredField Q Cc hh n (lam • A) u v ξ t Y z -
        normalizedLiftUncenteredField Qi Ci hh n (lam • A) u v ξ t Y z) X‖ ≤
        (C * g) * lam ^ (n + j)) (r : ℕ) (hr : r ≤ p) :
    ContDiff ℝ (p : ℕ∞) (fun X =>
      (Real.exp ((lam • A) X))⁻¹ •
        liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X v -
      (Real.exp ((lam • A) X))⁻¹ •
        liftMean Qi Ci (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X v) ∧
    ∀ X, ‖iteratedFDeriv ℝ r (fun Y =>
      (Real.exp ((lam • A) Y))⁻¹ •
        liftMean Q Cc (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) hh n t Y v -
      (Real.exp ((lam • A) Y))⁻¹ •
        liftMean Qi Ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) hh n t Y v) X‖ ≤
        ((2 : ℝ) ^ p * C) * g * lam ^ (n + r) := by
  let f := fun (_ : ℝ) Y => Real.exp ((lam • A) Y) • Pi.single u ξ
  have hc (X : Vec 2) := liftA_fast_continuous_of_normalized_box Q Cc f hh n p q t A lam
    (fun w => data.box A u w ξ t ht) X
  have hci (X : Vec 2) := liftA_fast_continuous_of_normalized_box Qi Ci f hh n p q t A lam
    (fun w => datai.box A u w ξ t ht) X
  have he (X : Vec 2) :
      fieldCellMean (normalizedLiftUncenteredField Q Cc hh n (lam • A) u v ξ t X) =
      (Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc f hh n t X v := by
    unfold normalizedLiftUncenteredField
    rw [AVRegularity.fieldCellMean_smul]
    congr 1
    exact AVRegularity.fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) (hc X)
  have hei (X : Vec 2) :
      fieldCellMean (normalizedLiftUncenteredField Qi Ci hh n (lam • A) u v ξ t X) =
      (Real.exp ((lam • A) X))⁻¹ • liftMean Qi Ci f hh n t X v := by
    unfold normalizedLiftUncenteredField
    rw [AVRegularity.fieldCellMean_smul]
    congr 1
    exact AVRegularity.fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) (hci X)
  have hm := weighted_cell_mean_paired_graded_jet_bound p r q n hr
    (normalizedLiftUncenteredField Q Cc hh n (lam • A) u v ξ t)
    (normalizedLiftUncenteredField Qi Ci hh n (lam • A) u v ξ t)
    (data.box A u v ξ t ht) (datai.box A u v ξ t ht)
    (fun _ => 1) continuous_const 1 (fun _ => by simp only [norm_one]; exact le_rfl)
    C g lam hb
  simp only [one_smul, he, hei, one_mul] at hm
  refine ⟨hm.1, ?_⟩
  intro X
  apply (hm.2 X).trans
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
  have hbound : 0 ≤ C * g * lam ^ (n + r) := (norm_nonneg _).trans (hb r hr X 0)
  have hh := mul_le_mul_of_nonneg_right hp hbound
  convert hh using 1 <;> ring
end

/-! Centering and the ordered correction combine into the genuine paired inverse-source bound. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem liftCellSource_zero_height_paired_grading_of_terms
    (Q Qi : LiftOperatorData ι h D) (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (n p q : ℕ) (t : ℝ) (v : ι)
    (A : Vec 2 →L[ℝ] ℝ) (lam eps C : ℝ) (hlam : 0 ≤ lam) (heps : 0 ≤ eps) (hC : 0 ≤ C)
    (hA : ∀ u, IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f 0 n t X z u))
    (hAi : ∀ u, IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Qi Ci f 0 n t X z u))
    (hbA : ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        (Real.exp ((lam • A) Y))⁻¹ • liftA Q Cc f 0 n t Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • liftA Qi Ci f 0 n t Y y v) z) X‖ ≤
        (C * eps) * lam ^ (n + r))
    (B : ℕ → ℝ)
    (hT : ∀ j ∈ Finset.Icc 1 (n - 2), IsBoxSmooth p q (fun X z =>
      (Real.exp ((lam • A) X))⁻¹ • liftApply j (Cc 0 j) (liftMean Q Cc f 0 (n - j)) t X z v -
      (Real.exp ((lam • A) X))⁻¹ • liftApply j (Ci 0 j) (liftMean Qi Ci f 0 (n - j)) t X z v))
    (hbT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        (Real.exp ((lam • A) Y))⁻¹ • liftApply j (Cc 0 j) (liftMean Q Cc f 0 (n - j)) t Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • liftApply j (Ci 0 j) (liftMean Qi Ci f 0 (n - j)) t Y y v) z) X‖ ≤
        (B j * eps) * lam ^ (n + r)) :
    IsBoxSmooth p q (fun X z =>
      (Real.exp ((lam • A) X))⁻¹ • liftCellSource Q Cc f 0 n t X z v -
      (Real.exp ((lam • A) X))⁻¹ • liftCellSource Qi Ci f 0 n t X z v) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        (Real.exp ((lam • A) Y))⁻¹ • liftCellSource Q Cc f 0 n t Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • liftCellSource Qi Ci f 0 n t Y y v) z) X‖ ≤
        (((1 + (2 : ℝ) ^ p) * C) + ∑ j ∈ Finset.Icc 1 (n - 2), B j) *
          eps * lam ^ (n + r) := by
  let F := fun X z =>
    ((Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f 0 n t X z v -
      (Real.exp ((lam • A) X))⁻¹ • liftA Qi Ci f 0 n t X z v) -
    ((Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc f 0 n t X v -
      (Real.exp ((lam • A) X))⁻¹ • liftMean Qi Ci f 0 n t X v)
  let T := fun j X z =>
    (Real.exp ((lam • A) X))⁻¹ • liftApply j (Cc 0 j) (liftMean Q Cc f 0 (n - j)) t X z v -
    (Real.exp ((lam • A) X))⁻¹ • liftApply j (Ci 0 j) (liftMean Qi Ci f 0 (n - j)) t X z v
  have hm (X : Vec 2) : fieldCellMean (fun z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f 0 n t X z v) = (Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc f 0 n t X v := by
    rw [AVRegularity.fieldCellMean_smul]
    congr 1
    exact AVRegularity.fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
      (liftA_fast_continuous_of_normalized_box Q Cc f 0 n p q t A lam hA X)
  have hmi (X : Vec 2) : fieldCellMean (fun z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Qi Ci f 0 n t X z v) = (Real.exp ((lam • A) X))⁻¹ • liftMean Qi Ci f 0 n t X v := by
    rw [AVRegularity.fieldCellMean_smul]
    congr 1
    exact AVRegularity.fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
      (liftA_fast_continuous_of_normalized_box Qi Ci f 0 n p q t A lam hAi X)
  have hc := fieldCellMean_centered_paired_graded_mixed_bound p q n
    (fun X z => (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f 0 n t X z v)
    (fun X z => (Real.exp ((lam • A) X))⁻¹ • liftA Qi Ci f 0 n t X z v)
    (hA v) (hAi v) C eps lam hC heps hlam hbA
  simp only [hm, hmi] at hc
  have he (X z : Vec 2) :
      ((Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f 0 n t X z v -
        (Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc f 0 n t X v) -
      ((Real.exp ((lam • A) X))⁻¹ • liftA Qi Ci f 0 n t X z v -
        (Real.exp ((lam • A) X))⁻¹ • liftMean Qi Ci f 0 n t X v) = F X z := by
    dsimp only [F]
    abel
  simp_rw [he] at hc
  have hF : IsBoxSmooth p q F := hc.1
  have hS : IsBoxSmooth p q (fun X z => ∑ j ∈ Finset.Icc 1 (n - 2), T j X z) :=
    IsBoxSmooth.sum _ (fun j hj => hT j hj)
  simp_rw [liftCellSource_zero_height_normalized_paired_expansion]
  change IsBoxSmooth p q (fun X z => -F X z + ∑ j ∈ Finset.Icc 1 (n - 2), T j X z) ∧ _
  refine ⟨hF.neg.add hS, ?_⟩
  intro r hr s hs X z
  have hn := norm_mixed_jet_const_smul (hF.mono hr hs) (-1 : ℝ) X z
  simp only [neg_one_smul, abs_neg, abs_one, one_mul] at hn
  have hsb : ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => ∑ j ∈ Finset.Icc 1 (n - 2), T j Y y) z) X‖ ≤
      (∑ j ∈ Finset.Icc 1 (n - 2), B j) * eps * lam ^ (n + r) := by
    apply (norm_mixed_jet_finset_sum_le (Finset.Icc 1 (n - 2)) r s T
      (fun j hj => (hT j hj).mono hr hs) X z).trans
    simp only [Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj => hbT j hj r hr s hs X z
  have hb := norm_mixed_jet_add_le (hF.neg.mono hr hs) (hS.mono hr hs) X z
  rw [hn] at hb
  exact hb.trans ((add_le_add (hc.2 r hr s hs X z) hsb).trans_eq (by ring))
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Both divergence branches inherit the same original edge envelope, including degree zero. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceArrayMatrix_weighted_entry_le
    (π : ι → ℝ) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (p q j : ℕ) (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    Real.sqrt (π u / π v) * normalizedSourceArrayMatrix edge I p q j lam A v u ≤
      normalizedSourceArrayConstant D p q j A Cj * b v u := by
  have hf := normalizedSourceUniformMatrix_weighted_entry_le π edge I lam hlam Cj qs qf b Θ he
    p (q + 1) j (by omega) hq A v u
  have hs := normalizedSourceUniformMatrix_weighted_entry_le π edge I lam hlam Cj qs qf b Θ he
    (p + 1) q (j - 1) hp (by omega) A v u
  have hF : 0 ≤ sourceDivergenceFastFactor p q A := by unfold sourceDivergenceFastFactor; positivity
  have hS : 0 ≤ sourceDivergenceSlowFactor p q A := by unfold sourceDivergenceSlowFactor; positivity
  unfold normalizedSourceArrayMatrix normalizedSourceArrayConstant
  by_cases hj : j = 0
  · subst j
    simp only [ite_true, add_zero]
    convert mul_le_mul_of_nonneg_left hf hF using 1 <;> ring
  · simp only [hj, ite_false]
    convert add_le_add (mul_le_mul_of_nonneg_left hf hF) (mul_le_mul_of_nonneg_left hs hS)
      using 1 <;> ring

theorem normalizedFullSourceUniformMatrix_weighted_entry_le
    (π : ι → ℝ) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (p q j : ℕ) (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    Real.sqrt (π u / π v) * normalizedFullSourceUniformMatrix edge I p q j lam A v u ≤
      normalizedFullSourceUniformConstant D p q j A Cj * b v u := by
  simp only [normalizedFullSourceUniformMatrix, normalizedFullSourceUniformConstant,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro s hs
  exact normalizedSourceArrayMatrix_weighted_entry_le π edge I lam hlam Cj qs qf b Θ he r s j
    (by have hh := Finset.mem_range.mp hr; omega)
    (by have hh := Finset.mem_range.mp hs; omega) A v u
end

/-! A fixed physical edge matrix controls the literal normalized source at every test direction. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceUniformMatrix_physical_entry_le
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (p q j : ℕ) (hp : p ≤ qs) (hq : q ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    normalizedSourceUniformMatrix edge I p q j lam A v u ≤
      normalizedSourceUniformConstant D p q j A Cj * physicalEdgeEnvelopeMatrix π b v u :=
  physical_matrix_entry_le_of_weighted π hπ b _ _ v u
    (normalizedSourceUniformMatrix_weighted_entry_le π edge I lam hlam Cj qs qf b Θ he
      p q j hp hq A v u)

theorem normalizedSourceUniformMatrix_physical_product_le
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (p q j : ℕ) (hp : p ≤ qs) (hq : q ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (v u : ι) :
    (∑ r, normalizedSourceUniformMatrix edge I p q j lam A v r * M r u) ≤
      normalizedSourceUniformConstant D p q j A Cj *
        finiteMatrixProduct (physicalEdgeEnvelopeMatrix π b) M v u := by
  calc
    _ ≤ ∑ r, (normalizedSourceUniformConstant D p q j A Cj *
        physicalEdgeEnvelopeMatrix π b v r) * M r u :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right
        (normalizedSourceUniformMatrix_physical_entry_le π hπ edge I lam hlam Cj qs qf
          b Θ he p q j hp hq A v r) (hM r u)
    _ = _ := by simp only [finiteMatrixProduct, Finset.mul_sum, mul_assoc]
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Fixed finite sums preserve actual zero-start field inverses, including the empty coefficient carrier. -/

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq J]

theorem cellFieldInverse_finset_sum
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (hsZ : 1 ≤ sZ) (a b : ℝ) (hab : a ≤ b)
    (S : Finset J) (g c : J → ℝ → Vec 2 → E)
    (hc : ∀ j ∈ S, IsCellFieldInverse G v sZ a b 0 (g j) (c j)) :
    IsCellFieldInverse G v sZ a b 0 (fun t z => ∑ j ∈ S, g j t z)
      (fun t z => ∑ j ∈ S, c j t z) := by
  induction S using Finset.induction_on with
  | empty =>
    have hg : (fun t z => ∑ j ∈ (∅ : Finset J), g j t z) = (0 : ℝ → Vec 2 → E) := by
      funext t z
      exact Finset.sum_empty
    have hh : (fun t z => ∑ j ∈ (∅ : Finset J), c j t z) = (0 : ℝ → Vec 2 → E) := by
      funext t z
      exact Finset.sum_empty
    rw [hg, hh]
    exact cellFieldInverse_zero_field G v sZ a b hab
  | @insert j S hj ih =>
    have hjc := hc j (Finset.mem_insert_self j S)
    have hSc := ih (fun k hk => hc k (Finset.mem_insert_of_mem hk))
    have hsum := cellFieldInverse_add_zero G v sZ hsZ a b hab
      (g j) (fun t z => ∑ k ∈ S, g k t z) (c j) (fun t z => ∑ k ∈ S, c k t z) hjc hSc
    simpa only [Finset.sum_insert hj] using hsum

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual positive-degree source arrays inherit the componentwise normalized grading. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceComponentArray_positive_mixed_bound
    (π : ι → ℝ) (edge : ConstituentEdges D h) (hD : 1 ≤ D) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (hj : j ≠ 0) (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (C : ι → ℝ) (hC : ∀ u, 0 ≤ C u)
    (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ u, IsBoxSmooth (p + j) (q + D - j) (fun Y y => f Y y u))
    (t : ℝ) (ht : t ∈ I)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth (p + 1) (q + 1) (γ.coeff α t))
    (X : Vec 2)
    (hbf : ∀ u, ∀ a ≤ p + j, ∀ s ≤ q + D - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (fun y => f Y y u) z) X‖ ≤
        C u * lam ^ (δ + a)) (v : ι) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceComponentCoefficientArray edge η t
        (fun Z y => Real.exp ((lam • A) Z) • f Z y) j v Y y) z) X‖ ≤
      ∑ _k : Fin 2, (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p *
        (2 ^ (p + 2 * (q + 1)) * (max 1 ‖A‖) ^ p *
            (∑ u, normalizedSourceUniformMatrix edge I p (q + 1) j lam A v u * C u) +
          2 ^ ((p + 1) + 2 * q) * (max 1 ‖A‖) ^ (p + 1) *
            (∑ u, normalizedSourceUniformMatrix edge I (p + 1) q (j - 1) lam A v u * C u))) *
        lam ^ (δ + j + p) := by
  let Φ := fun Z y => Real.exp ((lam • A) Z) • f Z y
  have hΦ : ∀ u, IsBoxSmooth (p + j) (q + D - j) (fun Y y => Φ Y y u) := by
    intro u
    exact isBoxSmooth_bilinear
      (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) (hf u)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h u →L[ℝ] h u)
  let U := ∑ u, normalizedSourceUniformMatrix edge I p (q + 1) j lam A v u * C u
  let V := ∑ u, normalizedSourceUniformMatrix edge I (p + 1) q (j - 1) lam A v u * C u
  have hU : 0 ≤ U := Finset.sum_nonneg fun u _ => mul_nonneg
    (normalizedSourceUniformMatrix_nonneg edge I p (q + 1) j lam hlam.le A v u) (hC u)
  have hV : 0 ≤ V := Finset.sum_nonneg fun u _ => mul_nonneg
    (normalizedSourceUniformMatrix_nonneg edge I (p + 1) q (j - 1) lam hlam.le A v u) (hC u)
  apply normalizedSourceComponentStep_mixed_bound edge η t lam hη hlam.le Φ δ p q j hj A v
    (fun _ => U) (fun _ => V) (fun _ => hU) (fun _ => hV)
  · intro k
    apply sourceFluxComponentCoefficient_box_reserve
    · intro v u d γ hm α
      exact (hΓ v u d γ hm α).mono (by omega) le_rfl
    · intro u
      exact (hΦ u).mono le_rfl (by omega)
  · intro k
    apply sourceFluxComponentCoefficient_box_reserve
    · intro v u d γ hm α
      exact (hΓ v u d γ hm α).mono le_rfl (by omega)
    · intro u
      exact (hΦ u).mono (by omega) (by omega)
  · intro k a ha s hs y
    have hh := normalizedSourceFluxComponent_uniform_mixed_bound π edge I lam hlam Cj qs qf b Θ he
      hπ η hη δ p (q + 1) j (by omega) hq A C hC f
      (fun u => (hf u).mono le_rfl (by omega)) t ht
      (fun v u d γ hm α => (hΓ v u d γ hm α).mono (by omega) le_rfl) X
      (fun u a ha s hs y => hbf u a ha s (by omega) y) a s ha hs k v y
    simpa only [U, Finset.sum_mul] using hh
  · intro k a ha s hs y
    have hh := normalizedSourceFluxComponent_uniform_mixed_bound π edge I lam hlam Cj qs qf b Θ he
      hπ η hη δ (p + 1) q (j - 1) hp (by omega) A C hC f
      (fun u => (hf u).mono (by omega) (by omega)) t ht
      (fun v u d γ hm α => (hΓ v u d γ hm α).mono le_rfl (by omega)) X
      (fun u a ha s hs y => hbf u a (by omega) s (by omega) y) a s ha hs k v y
    simpa only [V, Finset.sum_mul] using hh
end

/-! The actual degree-zero source array has a full normalized bound with no slow loss. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceComponentArray_zero_mixed_bound
    (π : ι → ℝ) (edge : ConstituentEdges D h) (hD : 1 ≤ D) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (δ p q : ℕ) (hp : p ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (C : ι → ℝ) (hC : ∀ u, 0 ≤ C u)
    (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ u, IsBoxSmooth p (q + D) (fun Y y => f Y y u))
    (t : ℝ) (ht : t ∈ I)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth p (q + 1) (γ.coeff α t))
    (X : Vec 2)
    (hbf : ∀ u, ∀ a ≤ p, ∀ s ≤ q + D, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (fun y => f Y y u) z) X‖ ≤
        C u * lam ^ (δ + a)) (v : ι) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceComponentCoefficientArray edge η t
        (fun Z y => Real.exp ((lam • A) Z) • f Z y) 0 v Y y) z) X‖ ≤
      ∑ _k : Fin 2, (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p *
        (2 ^ (p + 2 * (q + 1)) * (max 1 ‖A‖) ^ p *
          (∑ u, normalizedSourceUniformMatrix edge I p (q + 1) 0 lam A v u * C u))) *
        lam ^ (δ + p) := by
  let Φ := fun Z y => Real.exp ((lam • A) Z) • f Z y
  have hΦ : ∀ u, IsBoxSmooth p (q + D) (fun Y y => Φ Y y u) := by
    intro u
    exact isBoxSmooth_bilinear
      (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) (hf u)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h u →L[ℝ] h u)
  let U := ∑ u, normalizedSourceUniformMatrix edge I p (q + 1) 0 lam A v u * C u
  have hU : 0 ≤ U := Finset.sum_nonneg fun u _ => mul_nonneg
    (normalizedSourceUniformMatrix_nonneg edge I p (q + 1) 0 lam hlam.le A v u) (hC u)
  apply normalizedSourceComponentZeroStep_mixed_bound edge η t lam hlam.le Φ δ p q A v
    (fun _ => U) (fun _ => hU)
  · intro k
    apply sourceFluxComponentCoefficient_box_reserve
    · exact hΓ
    · intro u
      exact (hΦ u).mono (by omega) (by omega)
  · intro k a ha s hs y
    have hh := normalizedSourceFluxComponent_uniform_mixed_bound π edge I lam hlam Cj qs qf b Θ he
      hπ η hη δ p (q + 1) 0 hp hq A C hC f
      (fun u => (hf u).mono (by omega) (by omega)) t ht hΓ X
      (fun u a ha s hs y => hbf u a (by omega) s (by omega) y) a s ha hs k v y
    simpa only [U, Finset.sum_mul, Nat.add_zero] using hh
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Earlier actual coefficient and mean states supply time measurability of ordered corrections. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D : ℕ}

theorem ambient_ordered_mean_clamped_dual_measurable
    (par : Fin 2) (a b : ℝ) (hab : a ≤ b) (lam : ℝ) (hlam : 0 ≤ lam)
    (j δ p q p' q' hh : ℕ) (hj : j ≤ p')
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (c : LiftCoeff ι h)
    (M M' : ι → ι → ℝ) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (coef : AmbientLiftCoefficientData par a b hab lam j p q c M)
    (mean : AmbientLiftUncenteredData par a b hab lam hh δ p' q' Q Cc K M')
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (l : h v →L[ℝ] ℝ) (X z : Vec 2) :
    Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ • liftApply j c
      (liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh δ)
        (Set.projIcc a b hab t) X z v)) := by
  have hm := coef.liftApply_clamped_measurable
    (liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh δ)
    (fun t ht => (mean.mean_raw_contDiff hlam A u ξ t ht).of_le (by exact_mod_cast hj))
    (mean.mean_raw_measurable A u ξ) v X z
  exact l.continuous.measurable.comp (hm.const_smul _)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A fixed physical edge matrix controls the literal normalized source at every test direction. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedFullSourceUniformConstant_nonneg (D p q j : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ normalizedFullSourceUniformConstant D p q j A Cj :=
  Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
    normalizedSourceArrayConstant_nonneg D r s j A Cj

theorem normalizedFullSourceUniformMatrix_physical_entry_le
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (p q j : ℕ) (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    normalizedFullSourceUniformMatrix edge I p q j lam A v u ≤
      normalizedFullSourceUniformConstant D p q j A Cj * physicalEdgeEnvelopeMatrix π b v u :=
  physical_matrix_entry_le_of_weighted π hπ b _ _ v u
    (normalizedFullSourceUniformMatrix_weighted_entry_le π edge I lam hlam Cj qs qf b Θ he
      p q j hp hq A v u)

theorem normalizedFullSourceUniformMatrix_physical_product_le
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (p q j : ℕ) (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (v u : ι) :
    (∑ r, normalizedFullSourceUniformMatrix edge I p q j lam A v r * M r u) ≤
      normalizedFullSourceUniformConstant D p q j A Cj *
        finiteMatrixProduct (physicalEdgeEnvelopeMatrix π b) M v u := by
  calc
    _ ≤ ∑ r, (normalizedFullSourceUniformConstant D p q j A Cj *
        physicalEdgeEnvelopeMatrix π b v r) * M r u :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right
        (normalizedFullSourceUniformMatrix_physical_entry_le π hπ edge I lam hlam Cj qs qf
          b Θ he p q j hp hq A v r) (hM r u)
    _ = _ := by simp only [finiteMatrixProduct, Finset.mul_sum, mul_assoc]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Actual cell response metric differences have fully mixed, scale-graded perturbation bounds. -/

theorem profileCellResponse_graded_metric_difference_mixed_bound (p q δ r j : ℕ) (hr : r ≤ p) (hj : j ≤ q)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M Md eps lam κ a b : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hab : a ≤ b)
    (hb : ∀ s ≤ p, ∀ t X, ‖iteratedFDeriv ℝ s (g t) X‖ ≤ M * lam ^ s)
    (hdb : ∀ s ≤ p, ∀ t X, ‖iteratedFDeriv ℝ s (fun Y => g t Y - 1) X‖ ≤ Md * eps * lam ^ s)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → ℝ → ℂ)
    (hfm : ∀ X, Measurable (Function.uncurry (fun t z => f t X z)))
    (hff : ∀ t X, ContDiff ℝ (q : ℕ∞) (f t X))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ j ≤ q, ∀ t z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f t X) z))
    (S : ℕ → ℕ → ℝ) (hS : ∀ s ≤ p, ∀ i ≤ q, 0 ≤ S s i)
    (hfb : ∀ s ≤ p, ∀ i ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ s (fun Y => iteratedDeriv i (f t Y) z) X‖ ≤ S s i * lam ^ (δ + s))
    (hcenter : ∀ t X, unitProfileFourierCoeff (f t X) 0 = 0)
    (l : Vec 2 →L[ℝ] ℝ) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (fun y => profileCellResponse (fun t => g t Y) (fun t => f t Y) a b (l y) -
        profileCellResponse (fun _ => 1) (fun t => f t Y) a b (l y)) z) X‖ ≤
      (‖l‖ ^ j * (metricDifferenceModeJetConstant p r M Md κ
        (fun s => (2 : ℝ) ^ s * S s j) * centeredProfileJetConstant)) * eps * lam ^ (δ + r) := by
  let S' := fun s i => S s i * lam ^ δ
  have hS' : ∀ s ≤ p, ∀ i ≤ q, 0 ≤ S' s i :=
    fun s hs i hi => mul_nonneg (hS s hs i hi) (pow_nonneg hlam δ)
  have hfb' : ∀ s ≤ p, ∀ i ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ s (fun Y => iteratedDeriv i (f t Y) z) X‖ ≤ S' s i * lam ^ s := by
    intro s hs i hi t z X
    simpa only [S', pow_add, mul_assoc] using hfb s hs i hi t z X
  have hi : ∀ X, IntegrableOn (fun t => g t X) (Icc a b) := by
    intro X
    apply (integrable_const M).mono' (hm X).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simpa using hb 0 (Nat.zero_le p) t X)
  have hfast : ∀ i ≤ q, ∀ t X z, ‖iteratedDeriv i (f t X) z‖ ≤ S' 0 i := by
    intro i hi t X z
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using!
      hfb' 0 (Nat.zero_le p) i hi t z X
  have hresponseG : ∀ Y, ContDiff ℝ (q : ℕ∞)
      (profileCellResponse (fun t => g t Y) (fun t => f t Y) a b) := by
    intro Y
    exact profileCellResponse_contDiff (fun t => g t Y) (fun t => f t Y) a b κ hab hκ (hi Y)
      (fun t _ => hgl t Y) q (S' 0) (hS' 0 (Nat.zero_le p))
      (fun t _ => hff t Y) (fun t _ => hper t Y) (fun i hi t _ y _ => hfast i hi t Y y)
  have hresponseI : ∀ Y, ContDiff ℝ (q : ℕ∞)
      (profileCellResponse (fun _ => 1) (fun t => f t Y) a b) := by
    intro Y
    exact profileCellResponse_contDiff (fun _ => 1) (fun t => f t Y) a b κ hab hκ (integrable_const 1)
      (fun _ _ => hκ1) q (S' 0) (hS' 0 (Nat.zero_le p))
      (fun t _ => hff t Y) (fun t _ => hper t Y) (fun i hi t _ y _ => hfast i hi t Y y)
  have he (y : ℝ) :
      (fun Y => iteratedDeriv j (fun x =>
        profileCellResponse (fun t => g t Y) (fun t => f t Y) a b x -
          profileCellResponse (fun _ => 1) (fun t => f t Y) a b x) y) =
      fun Y => profileWeightedResponse (fun t => g t Y) (fun t => f t Y) a b y j -
        profileWeightedResponse (fun _ => 1) (fun t => f t Y) a b y j := by
    funext Y
    have hGj : ContDiff ℝ (j : ℕ∞) (profileCellResponse (fun t => g t Y) (fun t => f t Y) a b) :=
      (hresponseG Y).of_le (by exact_mod_cast hj)
    have hIj : ContDiff ℝ (j : ℕ∞) (profileCellResponse (fun _ => 1) (fun t => f t Y) a b) :=
      (hresponseI Y).of_le (by exact_mod_cast hj)
    change iteratedDeriv j (profileCellResponse (fun t => g t Y) (fun t => f t Y) a b -
      profileCellResponse (fun _ => 1) (fun t => f t Y) a b) y = _
    rw [iteratedDeriv_sub (x := y) hGj.contDiffAt hIj.contDiffAt]
    rw [profileCellResponse_fast_jet_identity (fun t => g t Y) (fun t => f t Y) a b κ hab hκ
      (hi Y) (fun t _ => hgl t Y) j (S' 0)
      (fun i hi => hS' 0 (Nat.zero_le p) i (hi.trans hj))
      (fun t _ => (hff t Y).of_le (by exact_mod_cast hj)) (fun t _ => hper t Y)
      (fun i hi t _ y _ => hfast i (hi.trans hj) t Y y) y]
    rw [profileCellResponse_fast_jet_identity (fun _ => 1) (fun t => f t Y) a b κ hab hκ
      (integrable_const 1) (fun _ _ => hκ1) j (S' 0)
      (fun i hi => hS' 0 (Nat.zero_le p) i (hi.trans hj))
      (fun t _ => (hff t Y).of_le (by exact_mod_cast hj)) (fun t _ => hper t Y)
      (fun i hi t _ y _ => hfast i (hi.trans hj) t Y y) y]
  have hres := profileWeightedResponse_graded_metric_difference_reserve p j δ g hm hs
    M Md eps lam κ a b hM hMd heps hlam hκ hκ1 hab hb hdb hgl f hfm
    (fun t Y => (hff t Y).of_le (by exact_mod_cast hj)) hper (hfs j hj)
    (fun s => S s j) (fun s hs => hS s hs j hj) (fun s hs => hfb s hs j hj) hcenter
  have hslow : ContDiff ℝ (p : ℕ∞) (fun Y => iteratedDeriv j (fun x =>
        profileCellResponse (fun t => g t Y) (fun t => f t Y) a b x -
          profileCellResponse (fun _ => 1) (fun t => f t Y) a b x) (l z)) := by
    rw [he (l z)]
    exact hres.1 (l z)
  have hh := scalar_fast_mixed_jet_norm_le p q r j hr hj
    (fun Y x => profileCellResponse (fun t => g t Y) (fun t => f t Y) a b x -
      profileCellResponse (fun _ => 1) (fun t => f t Y) a b x)
    (fun Y => (hresponseG Y).sub (hresponseI Y)) l z X hslow
  apply hh.trans
  rw [he (l z)]
  apply (mul_le_mul_of_nonneg_left (hres.2.2 r hr X (l z)) (pow_nonneg (norm_nonneg l) j)).trans_eq
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual source operator on a lift test combines its physical matrix with the lift row budgets. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

theorem normalizedSourceFlux_lift_test_uniform_matrix_grading
    (π : ι → ℝ) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (n p q j : ℕ) (k : Fin 2) (hp : p ≤ qs) (hq : q ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (B : ι → ℝ) (hB : ∀ u, 0 ≤ B u)
    (c : LiftCoeff ι h) (t : ℝ) (ht : t ∈ I) (v u₀ : ι) (ξ : h u₀)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v' u',
      IsBoxSmooth (p + j) (q + (D - 1) - j)
        (fun X z => c m α t X z v' u'))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth p q (γ.coeff α t))
    (X : Vec 2)
    (hbc : ∀ u, ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ a ≤ p + j, ∀ s ≤ q + (D - 1) - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s
        (fun y => c m α t Y y u u₀) z) X‖ ≤ B u * lam ^ (n - m + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceFluxComponentCoefficient edge η t
        (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u₀ ξ) t) k j v Y y) z) X‖ ≤
      (finiteLiftSymbolBudget n A *
        (∑ u, normalizedSourceUniformMatrix edge I p q j lam A v u * B u) * ‖ξ‖) *
          lam ^ (n + j + r) := by
  let F := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u₀ ξ) t Y y
  have hf u : IsBoxSmooth (p + j) (q + (D - 1) - j) (fun Y y => F Y y u) :=
    normalized_lift_test_box_reserve n _ _ c lam A t u u₀ ξ (fun m hm α => hc m hm α u u₀)
  have hb u a (ha : a ≤ p + j) s (hs : s ≤ q + (D - 1) - j) y :
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (fun w => F Y w u) y) X‖ ≤
        (finiteLiftSymbolBudget n A * B u * ‖ξ‖) * lam ^ (n + a) := by
    have hh := normalized_lift_test_mixed_grading n a s c lam (B u) hlam.le A t u u₀ ξ
      (fun m hm α => (hc m hm α u u₀).mono (by omega) (by omega)) X y
      (fun m hm α => hbc u m hm α a ha s hs y)
    simpa only [F, Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm] using! hh
  have hrecover : (fun Y y => Real.exp ((lam • A) Y) • F Y y) =
      liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u₀ ξ) t := by
    funext Y y
    dsimp only [F]
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  rw [← hrecover]
  have hh := normalizedSourceFluxComponent_uniform_mixed_bound π edge I lam hlam Cj qs qf b Θ he hπ η hη
    n p q j hp hq A (fun u => finiteLiftSymbolBudget n A * B u * ‖ξ‖)
    (fun u => mul_nonneg (mul_nonneg (finiteLiftSymbolBudget_nonneg n A) (hB u)) (norm_nonneg ξ))
    F hf
    t ht hΓ X hb r s hr hs k v z
  apply hh.trans_eq
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun u _ => by ring)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The actual unshifted shear generator has the scalar Fourier diffusion eigenvalue. -/

theorem transverseFourierModeH1_weak_generator
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (t : ℝ) (n : ℤ) (z : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨fun t _ => G t, v, 0, 0⟩ hG V hv hb t
      (transverseFourierModeH1 par n) z =
      -((‖profileFourierFrequency n‖ ^ 2 * G t par.rev par.rev : ℝ) : ℂ) *
        cellComplexPair (torusHkValueCLM (transverseFourierModeH1 par n)) (torusHkValueCLM z) := by
  have hd (j : Fin 2) := transverseFourierModeH1_drift_zero
    ⟨fun t _ => G t, v, 0, 0⟩ V hv hb par ht t n j
  simp only [cellComplexGenerator, Pi.zero_apply, star_zero,
    show (fun _ : Fin 2 => (0 : ℂ)) = 0 from rfl, cellShiftedDerivative_zero,
    cellScalarCLM_smul, zero_smul, cellComplexPair_zero_left, add_zero]
  simp_rw [hd, cellComplexPair_zero_left]
  simp only [Finset.sum_const_zero, sub_zero]
  exact transverseFourierModeH1_weak_diffusion G hG t par n z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual component inverses assemble through the standard finite Pi carrier. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem cellFieldInverse_dependent_pi
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (hsZ : 1 ≤ sZ) (a b : ℝ) (hab : a ≤ b)
    (g c : ℝ → Vec 2 → ∀ i, E i)
    (hc : ∀ i, IsCellFieldInverse G v sZ a b 0
      (fun t z => g t z i) (fun t z => c t z i)) :
    IsCellFieldInverse G v sZ a b 0 g c := by
  have hi (i : ι) := cellFieldInverse_postcomposition
    (ContinuousLinearMap.single ℝ E i) G v sZ hsZ a b 0
    (fun t z => g t z i) (fun t z => c t z i) (hc i)
  have hz (i : ι) : (fun _ : Vec 2 => (ContinuousLinearMap.single ℝ E i) 0) = 0 := by
    funext z
    exact map_zero _
  have hsum := cellFieldInverse_finset_sum G v sZ hsZ a b hab Finset.univ
    (fun i t z => (ContinuousLinearMap.single ℝ E i) (g t z i))
    (fun i t z => (ContinuousLinearMap.single ℝ E i) (c t z i))
    (fun i _ => by simpa only [Pi.zero_apply, hz i] using hi i)
  have hg : (fun t z => ∑ i, (ContinuousLinearMap.single ℝ E i) (g t z i)) = g := by
    funext t z i
    simp
  have hh : (fun t z => ∑ i, (ContinuousLinearMap.single ℝ E i) (c t z i)) = c := by
    funext t z i
    simp
  simpa only [hg, hh] using hsum

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! One explicit linear map synthesizes the scalar coefficient inverses into any finite carrier. -/

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype J] [DecidableEq J]

theorem cellFieldInverse_pi_synthesis
    (L : (J → ℝ) →L[ℝ] E)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (hsZ : 1 ≤ sZ) (a b : ℝ) (hab : a ≤ b)
    (g c : J → ℝ → Vec 2 → ℝ)
    (hc : ∀ j, IsCellFieldInverse G v sZ a b 0 (g j) (c j)) :
    IsCellFieldInverse G v sZ a b 0
      (fun t z => L (fun j => g j t z)) (fun t z => L (fun j => c j t z)) := by
  let Lj := fun j => L.comp (ContinuousLinearMap.single ℝ (fun _ : J => ℝ) j)
  have hs := cellFieldInverse_finset_sum (E := E) G v sZ hsZ a b hab Finset.univ
    (fun j t z => Lj j (g j t z)) (fun j t z => Lj j (c j t z))
    (fun j _ => by
      have hi := cellFieldInverse_postcomposition (Lj j) G v sZ hsZ a b 0 (g j) (c j) (hc j)
      have hz : (fun z => Lj j ((0 : Vec 2 → ℝ) z)) = (0 : Vec 2 → E) := by
        funext z
        exact map_zero (Lj j)
      rw [hz] at hi
      exact hi)
  have he (x : J → ℝ) : (∑ j, Lj j (x j)) = L x := by
    simp only [Lj, ContinuousLinearMap.comp_apply, ← map_sum]
    congr 1
    ext j
    simp
  have hg : (fun t z => ∑ j, Lj j (g j t z)) = fun t z => L (fun j => g j t z) :=
    funext (fun t => funext (fun z => he (fun j => g j t z)))
  have hh : (fun t z => ∑ j, Lj j (c j t z)) = fun t z => L (fun j => c j t z) :=
    funext (fun t => funext (fun z => he (fun j => c j t z)))
  rw [hg, hh] at hs
  exact hs

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Actual cross lift terms retain their separate slow and fast predecessor reserves. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_first_cross_lift_box
    (n p q p' q' : ℕ) (hp : p + 1 ≤ qs) (hq : q ≤ qf)
    (hp' : p + 1 ≤ p') (hq' : q + 1 ≤ q')
    (c : LiftCoeff ι h) (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' c M)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η Q.G Q.v t
      (liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  have hraw := (data.raw_test_box A u ξ t ht).mono hp' hq'
  have hc := cellB1_box_reserve p q Q.η Q.G Q.v t _ hraw
    (fun i j => setting_metric_entry_box P (p + 1) q hp t ht i j)
    (fun i => setting_raw_drift_fast_box P p q hq t ht i)
  exact exponential_normalization_box_reserve p q (lam • A) _
    (hc.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v))

include P in
theorem setting_ambient_second_cross_lift_box
    (n p q p' q' : ℕ) (hp : p + 1 ≤ qs)
    (hp' : p + 2 ≤ p') (hq' : q ≤ q')
    (c : LiftCoeff ι h) (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' c M)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
      (liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  have hraw := (data.raw_test_box A u ξ t ht).mono hp' hq'
  have hc := cellB2_box_reserve p q Q.η Q.G t _ hraw
    (fun i j => setting_metric_entry_box P (p + 1) q hp t ht i j)
  exact exponential_normalization_box_reserve p q (lam • A) _
    (hc.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v))
end

/-! Actual source predecessor states supply periodicity of the full uncentered lift test. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftA_normalized_test_periodic
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q : ℕ) (hhh : hh ≤ H) (hqs : 1 ≤ qs) (hqf : 1 ≤ qf)
    (M : ℕ → ι → ι → ℝ)
    (dataS : hh ≠ 0 → ∀ j ≤ min D n,
      AmbientLiftCoefficientData par a b P.window lam (n - j) (max D (p + j))
        (max D (q + D - j)) (Cc (hh - 1) (n - j)) (M j))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X z v) := by
  let f := fun (_ : ℝ) Y => Real.exp ((lam • A) Y) • Pi.single u ξ
  apply liftA_normalized_periodic_of_terms Q Cc f hh n t v A lam
  · have hp := cellB1_periodic Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) f t)
      (liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh (n - 1) f t ht)
      (setting_drift_periodic P t ht)
    intro X k z
    exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hp X k z)
  · intro _
    have hp := cellB2_periodic Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) f t)
      (liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh (n - 2) f t ht)
    intro X k z
    exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hp X k z)
  · intro hh0 j hj
    exact setting_ambient_source_test_periodic P sX sZ Cc hseq (hh - 1) (n - j) _ _
      (by omega) (Nat.le_max_left _ _) (Nat.le_max_left _ _) hqs hqf _ (dataS hh0 j hj)
      A u v ξ j t ht
end

/-! Actual source predecessor states supply periodicity of the full uncentered lift test. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftA_normalized_test_periodic_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u))
    (hh n p q : ℕ) (hqs : 1 ≤ qs) (hqf : 1 ≤ qf)
    (M : ℕ → ι → ι → ℝ)
    (dataS : hh ≠ 0 → ∀ j ≤ min D n,
      AmbientLiftCoefficientData par a b P.window lam (n - j) (max D (p + j))
        (max D (q + D - j)) (Cc (hh - 1) (n - j)) (M j))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X z v) := by
  let f := fun (_ : ℝ) Y => Real.exp ((lam • A) Y) • Pi.single u ξ
  apply liftA_normalized_periodic_of_terms Q Cc f hh n t v A lam
  · have hp := cellB1_periodic Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) f t)
      (fun Y => liftApply_periodic_of_coefficients (n - 1) (Cc hh (n - 1)) f t Y
        (fun m _ α v u => hper hh (n - 1) m α v u t ht Y))
      (setting_drift_periodic P t ht)
    intro X k z
    exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hp X k z)
  · intro _
    have hp := cellB2_periodic Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) f t)
      (fun Y => liftApply_periodic_of_coefficients (n - 2) (Cc hh (n - 2)) f t Y
        (fun m _ α v u => hper hh (n - 2) m α v u t ht Y))
    intro X k z
    exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hp X k z)
  · intro hh0 j hj
    exact setting_ambient_source_test_periodic_of_coefficients P Cc hper (hh - 1) (n - j) _ _
      (Nat.le_max_left _ _) (Nat.le_max_left _ _) hqs hqf _ (dataS hh0 j hj)
      A u v ξ j t ht
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Subtracting actual weak solutions removes their common forcing before applying energy uniqueness. -/

theorem cellSolution_common_source_unique {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D D' : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution (Icc a b) C src F D)
    (hD' : IsCellSolution (Icc a b) C src F D')
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' a) :
    ∀ t ∈ Icc a b, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' t := by
  have hdiff : IsCellSolution (Icc a b) C 0 0 (D - D') := by
    simpa only [neg_one_smul, sub_eq_add_neg, add_neg_cancel] using
      cellSolution_add hD (cellSolution_smul hD' (-1))
  have hz : IsCellSolution (Icc a b) C 0 0 (0 : ℝ → RawJet2 1 ℂ) := by
    simpa only [zero_smul] using cellSolution_smul hD 0
  have hinit : cellValue (D - D') a =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (0 : ℝ → RawJet2 1 ℂ) a := by
    filter_upwards [hi] with x hx
    change cellValue D a x - cellValue D' a x = 0
    rw [hx, sub_self]
  have he := cellActual_unique_raw hab C hG V k hv hb hκ hκb 0 0
    (by simpa only [Function.uncurry, Pi.zero_apply] using! (MemLp.zero : MemLp (0 : ℝ × Vec 2 → ℂ) 2 _))
    (by simpa only [Function.uncurry, Pi.zero_apply] using!
      (MemLp.zero : MemLp (0 : ℝ × Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) 2 _))
    (D - D') 0 hdiff hz hinit
  intro t ht
  filter_upwards [he t ht] with x hx
  exact sub_eq_zero.mp hx

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual normalized source arrays obey a matrix majorant closed under weighted row and column budgets. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceArray_positive_matrix_bound
    (π : ι → ℝ) (edge : ConstituentEdges D h) (hD : 1 ≤ D) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (hj : j ≠ 0) (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (C : ι → ℝ) (hC : ∀ u, 0 ≤ C u)
    (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ u, IsBoxSmooth (p + j) (q + D - j) (fun Y y => f Y y u))
    (t : ℝ) (ht : t ∈ I)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth (p + 1) (q + 1) (γ.coeff α t))
    (X : Vec 2)
    (hbf : ∀ u, ∀ a ≤ p + j, ∀ s ≤ q + D - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (fun y => f Y y u) z) X‖ ≤
        C u * lam ^ (δ + a)) (v : ι) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceComponentCoefficientArray edge η t
        (fun Z y => Real.exp ((lam • A) Z) • f Z y) j v Y y) z) X‖ ≤
      (∑ u, normalizedSourceArrayMatrix edge I p q j lam A v u * C u) * lam ^ (δ + j + p) := by
  have hh := normalizedSourceComponentArray_positive_mixed_bound π edge hD I lam hlam Cj qs qf
    b Θ he hπ η hη δ p q j hj hp hq A C hC f hf t ht hΓ X hbf v z
  apply hh.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    normalizedSourceArrayMatrix, hj, ite_false, sourceDivergenceFastFactor,
    sourceDivergenceSlowFactor, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring
end

/-! The degree-zero source matrix estimate preserves the common slow reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceArray_zero_matrix_bound
    (π : ι → ℝ) (edge : ConstituentEdges D h) (hD : 1 ≤ D) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (δ p q : ℕ) (hp : p ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (C : ι → ℝ) (hC : ∀ u, 0 ≤ C u)
    (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ u, IsBoxSmooth p (q + D) (fun Y y => f Y y u))
    (t : ℝ) (ht : t ∈ I)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth p (q + 1) (γ.coeff α t))
    (X : Vec 2)
    (hbf : ∀ u, ∀ a ≤ p, ∀ s ≤ q + D, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (fun y => f Y y u) z) X‖ ≤
        C u * lam ^ (δ + a)) (v : ι) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceComponentCoefficientArray edge η t
        (fun Z y => Real.exp ((lam • A) Z) • f Z y) 0 v Y y) z) X‖ ≤
      (∑ u, normalizedSourceArrayMatrix edge I p q 0 lam A v u * C u) * lam ^ (δ + p) := by
  have hh := normalizedSourceComponentArray_zero_mixed_bound π edge hD I lam hlam Cj qs qf
    b Θ he hπ η hη δ p q hp hq A C hC f hf t ht hΓ X hbf v z
  apply hh.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    normalizedSourceArrayMatrix, ite_true, add_zero, sourceDivergenceFastFactor,
    mul_assoc, ← Finset.mul_sum]
  ring
end

end AVRegularity.CycleComparison.Lift
end
