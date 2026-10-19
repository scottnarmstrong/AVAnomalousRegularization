-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients
public import AVRegularity.CycleComparison.Lift.AmbientPairedCoefficientDataOfTests
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.Construction.InitialLayer.Comparison
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! An actual ambient predecessor state supplies measurable clamped source-operator tests. -/

section
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] {D : ℕ}

variable [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]

omit [MeasurableSpace T] in
theorem ambient_source_lift_test_clamped_measurable
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D) (sX sZ N H : ℕ)
    (a b : ℝ) (hab : a ≤ b) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q : ℕ) (hhh : hh ≤ H) (hp : D ≤ p) (hq : D ≤ q)
    (par : Fin 2) (lam : ℝ) (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b hab lam n p q (Cc hh n) M)
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z,
      Measurable (fun t => γ.coeff α t X z))
    (hΓbox : ∀ t ∈ Set.Icc a b, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 1 1 (γ.coeff α t))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (j : ℕ) (X z : Vec 2) :
    Measurable (fun t => (Real.exp ((lam • A) X))⁻¹ •
      sourceCoeff Q.edge Q.η j (Set.projIcc a b hab t)
        (liftApply n (Cc hh n) (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
          (Set.projIcc a b hab t)) X z v) := by
  let Φ := fun t => liftApply n (Cc hh n)
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) (Set.projIcc a b hab t)
  have hm (Y y : Vec 2) : Measurable (fun t => Φ t Y y) :=
    data.raw_test_measurable A u ξ Y y
  have hf (t : ℝ) : IsBoxSmooth D D (Φ t) :=
    (data.raw_test_box A u ξ _ (Set.projIcc a b hab t).2).mono hp hq
  have hper (t : ℝ) (Y : Vec 2) : AVenhance.IsZ2Periodic (Φ t Y) :=
    liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh n _ _
      (Set.projIcc a b hab t).2 Y
  have hproj : Measurable (fun t : ℝ => (Set.projIcc a b hab t : ℝ)) :=
    (continuous_projIcc (a := a) (b := b) (h := hab)).measurable.subtype_val
  have hs := sourceCoeff_parameter_measurable_of_ambient_inputs Q.edge hD Q.η
    (fun t : ℝ => (Set.projIcc a b hab t : ℝ)) Φ hm hf hper
    (fun v u d γ hγ α Y y => (hΓ v u d γ hγ α Y y).comp hproj)
    (fun t => hΓbox _ (Set.projIcc a b hab t).2) j X z
  exact ((measurable_pi_apply v).comp hs).const_smul _
end

/-! An actual ambient predecessor state supplies measurable clamped source-operator tests. -/

section
variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] {D : ℕ}

variable [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]

omit [MeasurableSpace T] in
theorem ambient_source_lift_test_clamped_measurable_of_coefficients
    (Q : LiftOperatorData ι h D) (hD : 1 ≤ D)
    (a b : ℝ) (hab : a ≤ b) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hperCoeff : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u))
    (hh n p q : ℕ) (hp : D ≤ p) (hq : D ≤ q)
    (par : Fin 2) (lam : ℝ) (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b hab lam n p q (Cc hh n) M)
    (hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z,
      Measurable (fun t => γ.coeff α t X z))
    (hΓbox : ∀ t ∈ Set.Icc a b, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      IsBoxSmooth 1 1 (γ.coeff α t))
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (j : ℕ) (X z : Vec 2) :
    Measurable (fun t => (Real.exp ((lam • A) X))⁻¹ •
      sourceCoeff Q.edge Q.η j (Set.projIcc a b hab t)
        (liftApply n (Cc hh n) (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
          (Set.projIcc a b hab t)) X z v) := by
  let Φ := fun t => liftApply n (Cc hh n)
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) (Set.projIcc a b hab t)
  have hm (Y y : Vec 2) : Measurable (fun t => Φ t Y y) :=
    data.raw_test_measurable A u ξ Y y
  have hf (t : ℝ) : IsBoxSmooth D D (Φ t) :=
    (data.raw_test_box A u ξ _ (Set.projIcc a b hab t).2).mono hp hq
  have hper (t : ℝ) (Y : Vec 2) : AVenhance.IsZ2Periodic (Φ t Y) :=
    liftApply_periodic_of_coefficients n (Cc hh n) _ _ Y
      (fun m _ α v u => hperCoeff hh n m α v u _ (Set.projIcc a b hab t).2 Y)
  have hproj : Measurable (fun t : ℝ => (Set.projIcc a b hab t : ℝ)) :=
    (continuous_projIcc (a := a) (b := b) (h := hab)).measurable.subtype_val
  have hs := sourceCoeff_parameter_measurable_of_ambient_inputs Q.edge hD Q.η
    (fun t : ℝ => (Set.projIcc a b hab t : ℝ)) Φ hm hf hper
    (fun v u d γ hγ α Y y => (hΓ v u d γ hγ α Y y).comp hproj)
    (fun t => hΓbox _ (Set.projIcc a b hab t).2) j X z
  exact ((measurable_pi_apply v).comp hs).const_smul _
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Weighted profile metric differences retain the actual rectangular quantitative jets. -/

theorem profileWeightedResponse_metric_difference_reserve (p j : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M Md eps lam κ a b : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hab : a ≤ b)
    (hb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (g t) X‖ ≤ M * lam ^ r)
    (hdb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (fun Y => g t Y - 1) X‖ ≤ Md * eps * lam ^ r)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → ℝ → ℂ)
    (hfm : ∀ X, Measurable (Function.uncurry (fun t z => f t X z)))
    (hff : ∀ t X, ContDiff ℝ (j : ℕ∞) (f t X))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ t z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f t X) z))
    (S : ℕ → ℝ) (hS : ∀ r ≤ p, 0 ≤ S r)
    (hfb : ∀ r ≤ p, ∀ t z X,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f t Y) z) X‖ ≤ S r * lam ^ r)
    (hcenter : ∀ t X, unitProfileFourierCoeff (f t X) 0 = 0) :
    (∀ z, ContDiff ℝ (p : ℕ∞)
      (fun X => profileWeightedResponse (fun t => g t X) (fun t => f t X) a b z j -
        profileWeightedResponse (fun _ => 1) (fun t => f t X) a b z j)) ∧
    (∀ q ≤ p, Continuous (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ q
      (fun X => profileWeightedResponse (fun t => g t X) (fun t => f t X) a b x.2 j -
        profileWeightedResponse (fun _ => 1) (fun t => f t X) a b x.2 j) x.1)) ∧
    ∀ q ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ q
        (fun Y => profileWeightedResponse (fun t => g t Y) (fun t => f t Y) a b z j -
          profileWeightedResponse (fun _ => 1) (fun t => f t Y) a b z j) X‖ ≤
      (metricDifferenceModeJetConstant p q M Md κ (fun r => (2 : ℝ) ^ r * S r) * eps * lam ^ q) * centeredProfileJetConstant := by
  obtain ⟨hUm, hUs, hUb, hU0⟩ := weightedParameterSource_data p j f hfm hff hper hfs S lam hfb hcenter
  have hS' : ∀ r ≤ p, 0 ≤ (2 : ℝ) ^ r * S r := fun r hr =>
    mul_nonneg (pow_nonneg (by norm_num) r) (hS r hr)
  have hh := parameterizedProfileResponse_metric_difference_reserve p g hm hs M Md eps lam κ a b
    hM hMd heps hlam hκ hκ1 hab hb hdb hgl (weightedParameterSource f j) hUm hUs
    (fun r => (2 : ℝ) ^ r * S r) hS' hUb hU0
  simpa only [parameterizedProfileResponse_weighted_eq] using hh

/-! Metric profile differences retain the source base grade at every supported slow order. -/

theorem profileWeightedResponse_graded_metric_difference_reserve (p j δ : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M Md eps lam κ a b : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hab : a ≤ b)
    (hb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (g t) X‖ ≤ M * lam ^ r)
    (hdb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (fun Y => g t Y - 1) X‖ ≤ Md * eps * lam ^ r)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → ℝ → ℂ)
    (hfm : ∀ X, Measurable (Function.uncurry (fun t z => f t X z)))
    (hff : ∀ t X, ContDiff ℝ (j : ℕ∞) (f t X))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ t z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f t X) z))
    (S : ℕ → ℝ) (hS : ∀ r ≤ p, 0 ≤ S r)
    (hfb : ∀ r ≤ p, ∀ t z X,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f t Y) z) X‖ ≤ S r * lam ^ (δ + r))
    (hcenter : ∀ t X, unitProfileFourierCoeff (f t X) 0 = 0) :
    (∀ z, ContDiff ℝ (p : ℕ∞)
      (fun X => profileWeightedResponse (fun t => g t X) (fun t => f t X) a b z j -
        profileWeightedResponse (fun _ => 1) (fun t => f t X) a b z j)) ∧
    (∀ q ≤ p, Continuous (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ q
      (fun X => profileWeightedResponse (fun t => g t X) (fun t => f t X) a b x.2 j -
        profileWeightedResponse (fun _ => 1) (fun t => f t X) a b x.2 j) x.1)) ∧
    ∀ q ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ q
        (fun Y => profileWeightedResponse (fun t => g t Y) (fun t => f t Y) a b z j -
          profileWeightedResponse (fun _ => 1) (fun t => f t Y) a b z j) X‖ ≤
      (metricDifferenceModeJetConstant p q M Md κ (fun r => (2 : ℝ) ^ r * S r) *
        centeredProfileJetConstant) * eps * lam ^ (δ + q) := by
  let S' := fun r => S r * lam ^ δ
  have hS' : ∀ r ≤ p, 0 ≤ S' r := fun r hr => mul_nonneg (hS r hr) (pow_nonneg hlam δ)
  have hfb' : ∀ r ≤ p, ∀ t z X,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f t Y) z) X‖ ≤ S' r * lam ^ r := by
    intro r hr t z X
    simpa only [S', pow_add, mul_assoc] using hfb r hr t z X
  obtain ⟨hreg, hcont, hbound⟩ := profileWeightedResponse_metric_difference_reserve p j
    g hm hs M Md eps lam κ a b hM hMd heps hlam hκ hκ1 hab hb hdb hgl f hfm hff hper hfs S' hS' hfb' hcenter
  refine ⟨hreg, hcont, ?_⟩
  intro q hq X z
  apply (hbound q hq X z).trans_eq
  have he : (fun r => (2 : ℝ) ^ r * S' r) =
      fun r => ((2 : ℝ) ^ r * S r) * lam ^ δ := by
    funext r
    exact (mul_assoc _ _ _).symm
  rw [he, metricDifferenceModeJetConstant_base_grade]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual paired second-cross tests retain the metric factor and the two-degree gain. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalizedCellB2_paired_lift_test_grading (n p q : ℕ) (η lam M Md g B Bd : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hMd : 0 ≤ Md)
    (hg : 0 ≤ g) (hB : 0 ≤ B) (hBd : 0 ≤ Bd)
    (A : Vec 2 →L[ℝ] ℝ) (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (c ci : LiftCoeff ι h) (v u : ι) (ξ : h u)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v' u',
      IsBoxSmooth (p + 2) q (fun X z => c m α t X z v' u'))
    (hci : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v' u',
      IsBoxSmooth (p + 2) q (fun X z => ci m α t X z v' u'))
    (hJ : ∀ i j, IsBoxSmooth (p + 1) q (fun X (_ : Vec 2) => J t X i j))
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun X (_ : Vec 2) => G t X i j))
    (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbD : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j - J t Y i j) z) X‖ ≤ (Md * g) * lam ^ a)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => ci m α t Y y v u) z) X‖ ≤ B * lam ^ (n - m + a))
    (hbcd : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => c m α t Y y v u - ci m α t Y y v u) z) X‖ ≤ (Bd * g) * lam ^ (n - m + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB2 η G t
        (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • cellB2 η J t
          (liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      ((normalizedCellB2UniformConstant p q A M * finiteLiftSymbolBudget n A * Bd +
        normalizedCellB2UniformConstant p q A Md * finiteLiftSymbolBudget n A * B) * ‖ξ‖) * g *
        lam ^ ((n + 2) + r) := by
  let F := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t Y y
  let Fi := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t Y y
  let dc : LiftCoeff ι h := fun d β s Y y i j => c d β s Y y i j - ci d β s Y y i j
  have hf : IsBoxSmooth (p + 2) q F := by
    apply isBoxSmooth_pi
    intro w
    exact normalized_lift_test_box_reserve n (p + 2) q c lam A t w u ξ
      (fun m hm α => hc m hm α w u)
  have hfi : IsBoxSmooth (p + 2) q Fi := by
    apply isBoxSmooth_pi
    intro w
    exact normalized_lift_test_box_reserve n (p + 2) q ci lam A t w u ξ
      (fun m hm α => hci m hm α w u)
  have hbfi : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun w => Fi Y w v) y) X‖ ≤
        (finiteLiftSymbolBudget n A * B * ‖ξ‖) * lam ^ (n + a) := by
    intro a ha b hb y
    have hh := normalized_lift_test_mixed_grading n a b ci lam B hlam A t v u ξ
      (fun m hm α => (hci m hm α v u).mono ha hb) X y
      (fun m hm α => hbc m hm α a ha b hb y)
    simpa only [Fi, Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm] using! hh
  have hbdf : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun w => F Y w v - Fi Y w v) y) X‖ ≤
        ((finiteLiftSymbolBudget n A * Bd * ‖ξ‖) * g) * lam ^ (n + a) := by
    intro a ha b hb y
    have hh := normalized_lift_test_mixed_grading n a b dc lam (Bd * g) hlam A t v u ξ
      (fun m hm α => ((hc m hm α v u).sub (hci m hm α v u)).mono ha hb) X y
      (fun m hm α => hbcd m hm α a ha b hb y)
    change ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
      (normalizedLiftTestField dc n (lam • A) u v ξ t Y) y) X‖ ≤ _ at hh
    change ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
      (fun w => normalizedLiftTestField c n (lam • A) u v ξ t Y w -
        normalizedLiftTestField ci n (lam • A) u v ξ t Y w) y) X‖ ≤ _
    dsimp only [dc] at hh
    rw [normalizedLiftTestField_sub] at hh
    exact hh.trans_eq (by ring)
  have he : (fun Y y => Real.exp ((lam • A) Y) • F Y y) =
      liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t := by
    funext Y y
    dsimp only [F]
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hei : (fun Y y => Real.exp ((lam • A) Y) • Fi Y y) =
      liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t := by
    funext Y y
    dsimp only [Fi]
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  rw [← he, ← hei]
  have hh := normalizedCellB2_paired_component_mixed_grading p q n r s hr hs
    η lam M Md g (finiteLiftSymbolBudget n A * B * ‖ξ‖)
    (finiteLiftSymbolBudget n A * Bd * ‖ξ‖) hη0 hη hlam hM hMd hg
    (mul_nonneg (mul_nonneg (finiteLiftSymbolBudget_nonneg n A) hB) (norm_nonneg ξ))
    (mul_nonneg (mul_nonneg (finiteLiftSymbolBudget_nonneg n A) hBd) (norm_nonneg ξ))
    A G J t F Fi v hf hfi hG hJ X hbG hbD hbfi hbdf z
  exact hh.trans_eq (by ring)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Uniform normalized flux matrices retain the original weighted row and column bounds. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def normalizedSourceUniformConstant (D p q j : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
    normalizedSourceOrderConstant D r s j A * sourceEnvelopeJetConstant r s Cj

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Recover real-dual weak equations of a real classical scalar solution by proved constant scaling. -/

theorem real_linear_functional_mul (l : ℝ →L[ℝ] ℝ) (x : ℝ) : l x = l 1 * x := by
  have he := map_smul l x (1 : ℝ)
  simpa only [smul_eq_mul, mul_one, mul_comm] using he

theorem real_dual_scalar_solution (I : Set ℝ) (hI : MeasurableSet I) (C : CellCoefficients)
    (src c : ℝ → Vec 2 → ℂ)
    (hsreal : ∀ t z, ((src t z).re : ℂ) = src t z)
    (hcreal : ∀ t z, ((c t z).re : ℂ) = c t z)
    (hc : ∀ t ∈ I, Differentiable ℝ (fun z => (c t z).re))
    (hsol : IsCellSolution I C src 0 (fun t => classicalCellJet (c t)))
    (l : ℝ →L[ℝ] ℝ) :
    IsCellSolution I C (fun t z => ((l ((src t z).re) : ℝ) : ℂ)) 0
      (cellJetOfField l (fun t z => (c t z).re)) := by
  have hfield t : (fun z : Vec 2 => ((l ((c t z).re) : ℝ) : ℂ)) = fun z => l 1 • c t z := by
    funext z
    rw [real_linear_functional_mul, Complex.ofReal_mul, hcreal]
    rfl
  have hjet t (ht : t ∈ I) : (l 1 • (fun t => classicalCellJet (c t))) t =
      cellJetOfField l (fun t z => (c t z).re) t := by
    rw [cellJetOfField_eq_classical_at l _ t (hc t ht), hfield, classicalCellJet_const_smul]
    rfl
  have hsrc : (l 1 • src) = (fun t z => ((l ((src t z).re) : ℝ) : ℂ)) := by
    funext t z
    rw [real_linear_functional_mul l ((src t z).re), Complex.ofReal_mul, hsreal]
    rfl
  have hs := cellSolution_smul hsol (l 1)
  rw [hsrc, smul_zero] at hs
  exact AVRegularity.InitialLayer.cellSolution_congr_jet hI hjet hs

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The literal source lift term inherits rectangular regularity from its actual ambient predecessor state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_source_lift_box
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q j p' q' : ℕ) (hhh : hh ≤ H)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (hp' : max D (p + j) ≤ p') (hq' : max D (q + D - j) ≤ q')
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • sourceCoeff Q.edge Q.η j t
      (liftApply n (Cc hh n) (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  have hraw := (data.raw_test_box A u ξ t ht).mono hp' hq'
  have hc := sourceCoeff_box_reserve_of_ambient_inputs Q.edge
    (by have hd := P.D_ge; omega) Q.η t _ p q j
    (fun v u d γ hγ α => (P.coeff_smooth v u d γ hγ α t ht).mono hp hq)
    (fun v u d γ _ α Y => γ.periodic α t Y) hraw
    (fun Y => liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh n _ t ht Y)
  exact exponential_normalization_box_reserve p q (lam • A) _
    (hc.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v))
end

/-! The literal source lift term inherits rectangular regularity from its actual ambient predecessor state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_source_lift_box_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u))
    (hh n p q j p' q' : ℕ)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (hp' : max D (p + j) ≤ p') (hq' : max D (q + D - j) ≤ q')
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • sourceCoeff Q.edge Q.η j t
      (liftApply n (Cc hh n) (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  have hraw := (data.raw_test_box A u ξ t ht).mono hp' hq'
  have hc := sourceCoeff_box_reserve_of_ambient_inputs Q.edge
    (by have hd := P.D_ge; omega) Q.η t _ p q j
    (fun v u d γ hγ α => (P.coeff_smooth v u d γ hγ α t ht).mono hp hq)
    (fun v u d γ _ α Y => γ.periodic α t Y) hraw
    (fun Y => liftApply_periodic_of_coefficients n (Cc hh n) _ t Y
      (fun m _ α v u => hper hh n m α v u t ht Y))
  exact exponential_normalization_box_reserve p q (lam • A) _
    (hc.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) v))
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The simultaneous uncentered state supplies actual normalized means and their time measurability. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {K : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}

theorem AmbientLiftUncenteredData.mean_component_grading
    (data : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K M)
    (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (r : ℕ) (hr : r ≤ p) :
    ContDiff ℝ (p : ℕ∞) (fun X => (Real.exp ((lam • A) X))⁻¹ •
      liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X v) ∧
    ∀ X, ‖iteratedFDeriv ℝ r (fun Y => (Real.exp ((lam • A) Y))⁻¹ •
      liftMean Q Cc (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) hh n t Y v) X‖ ≤
        ((2 : ℝ) ^ p * K A * M v u * ‖ξ‖) * lam ^ (n + r) := by
  have hm := liftMean_normalized_component_grading_of_liftA Q Cc
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n p q r hr t v A lam
    (K A * M v u * ‖ξ‖) hlam
    (mul_nonneg (mul_nonneg (data.constant_nonneg A) (data.matrix_nonneg v u)) (norm_nonneg ξ))
    (fun v' => data.box A u v' ξ t ht)
    (fun j hj X z => by
      simpa only [norm_mixed_jet_fast_zero, normalizedLiftUncenteredField] using!
        data.bound A u v ξ j hj 0 (Nat.zero_le q) t ht X z)
  simpa only [mul_assoc] using hm

theorem AmbientLiftUncenteredData.mean_component_measurable
    (data : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (X : Vec 2) :
    Measurable (fun t => (Real.exp ((lam • A) X))⁻¹ •
      liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
        hh n (Set.projIcc a b hab t) X v) := by
  apply liftMean_clamped_normalized_measurable_of_liftA Q Cc
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n p q a b hab A lam
    (fun t ht v' => data.box A u v' ξ t ht)
  intro v' Y z
  exact measurable_of_all_real_duals _ (fun l => data.measurable A u v' ξ l Y z)

theorem AmbientLiftUncenteredData.mean_normalized_contDiff
    (data : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K M)
    (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (u : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (p : ℕ∞) (fun X => (Real.exp ((lam • A) X))⁻¹ •
      liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X) := by
  apply contDiff_pi.mpr
  intro v
  exact (data.mean_component_grading hlam A u v ξ t ht 0 (Nat.zero_le p)).1

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Full source-divergence matrix majorants preserve the physical constituent row and column budgets. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceDivergenceFastFactor (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  2 * (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p) *
    (2 ^ (p + 2 * (q + 1)) * (max 1 ‖A‖) ^ p)

def sourceDivergenceSlowFactor (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  2 * (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p) *
    (2 ^ ((p + 1) + 2 * q) * (max 1 ‖A‖) ^ (p + 1))

def normalizedSourceArrayMatrix (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q j : ℕ) (lam : ℝ) (A : Vec 2 →L[ℝ] ℝ) (v u : ι) : ℝ :=
  sourceDivergenceFastFactor p q A * normalizedSourceUniformMatrix edge I p (q + 1) j lam A v u +
    if j = 0 then 0 else sourceDivergenceSlowFactor p q A *
      normalizedSourceUniformMatrix edge I (p + 1) q (j - 1) lam A v u

def normalizedSourceArrayConstant (D p q j : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (Cj : ℕ → ℕ → ℝ) : ℝ :=
  sourceDivergenceFastFactor p q A * normalizedSourceUniformConstant D p (q + 1) j A Cj +
    if j = 0 then 0 else sourceDivergenceSlowFactor p q A *
      normalizedSourceUniformConstant D (p + 1) q (j - 1) A Cj

omit [Fintype ι] in
theorem normalizedSourceArrayMatrix_nonneg (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q j : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    0 ≤ normalizedSourceArrayMatrix edge I p q j lam A v u := by
  unfold normalizedSourceArrayMatrix
  have hf := normalizedSourceUniformMatrix_nonneg edge I p (q + 1) j lam hlam A v u
  have hs := normalizedSourceUniformMatrix_nonneg edge I (p + 1) q (j - 1) lam hlam A v u
  have hF : 0 ≤ sourceDivergenceFastFactor p q A := by unfold sourceDivergenceFastFactor; positivity
  have hS : 0 ≤ sourceDivergenceSlowFactor p q A := by unfold sourceDivergenceSlowFactor; positivity
  split_ifs <;> positivity
end

/-! The original edge envelope controls every normalized flux entry, uniformly over families. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceUniformMatrix_weighted_entry_le
    (π : ι → ℝ) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (p q j : ℕ) (hp : p ≤ qs) (hq : q ≤ qf) (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    Real.sqrt (π u / π v) * normalizedSourceUniformMatrix edge I p q j lam A v u ≤
      normalizedSourceUniformConstant D p q j A Cj * b v u := by
  have hb r (hr : r ∈ Finset.range (p + 1)) s (hs : s ∈ Finset.range (q + 1)) :=
    sourceUniformMixedBudget_weighted_le π edge I lam hlam Cj qs qf b Θ he r s
      (by have hh := Finset.mem_range.mp hr; omega)
      (by have hh := Finset.mem_range.mp hs; omega) v u
  calc
    _ = ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
        normalizedSourceOrderConstant D r s j A *
          (Real.sqrt (π u / π v) * sourceUniformMixedBudget edge I r s lam v u) := by
      simp only [normalizedSourceUniformMatrix, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
        normalizedSourceOrderConstant D r s j A * (sourceEnvelopeJetConstant r s Cj * b v u) :=
      Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun s hs =>
        mul_le_mul_of_nonneg_left (hb r hr s hs) (normalizedSourceOrderConstant_nonneg D r s j A)
    _ = _ := by simp only [normalizedSourceUniformConstant, Finset.sum_mul, mul_assoc]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Genuine source tests retain transverse geometry using only the ambient predecessor state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_source_test_transverse
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh n p q : ℕ)
    (hhh : hh ≤ H) (hp : D ≤ p) (hq : D ≤ q) (hqs : 1 ≤ qs) (hqf : 1 ≤ qf)
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p q (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (j : ℕ) :
    IsTransverseOn par (Set.Icc a b) (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
      sourceCoeff Q.edge Q.η j t (liftApply n (Cc hh n)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  let Φ := fun t => liftApply n (Cc hh n)
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t
  have hΦ : IsTransverseOn par (Set.Icc a b) Φ :=
    liftApply_transverse par (Set.Icc a b) n (Cc hh n) _ data.transverse
  have hg (t : ℝ) (ht : t ∈ Set.Icc a b) : GoodField D (Φ t) :=
    ⟨(data.raw_test_box A u ξ t ht).contDiff_uncurry hp hq,
      liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh n _ t ht⟩
  have hs := sourceCoeff_transverse_of_reserved_inputs par (Set.Icc a b) Q.edge
    (by have hd := P.D_ge; omega) Q.η Φ hΦ hg P.transverse
    (fun v u d γ hγ α t ht =>
      ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩) j
  intro t ht X z s
  exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v)
    (hs t ht X z s)
end

/-! Genuine source tests retain transverse geometry using only the ambient predecessor state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_source_test_transverse_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u)) (hh n p q : ℕ)
    (hp : D ≤ p) (hq : D ≤ q) (hqs : 1 ≤ qs) (hqf : 1 ≤ qf)
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p q (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (j : ℕ) :
    IsTransverseOn par (Set.Icc a b) (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
      sourceCoeff Q.edge Q.η j t (liftApply n (Cc hh n)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  let Φ := fun t => liftApply n (Cc hh n)
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t
  have hΦ : IsTransverseOn par (Set.Icc a b) Φ :=
    liftApply_transverse par (Set.Icc a b) n (Cc hh n) _ data.transverse
  have hg (t : ℝ) (ht : t ∈ Set.Icc a b) : GoodField D (Φ t) :=
    ⟨(data.raw_test_box A u ξ t ht).contDiff_uncurry hp hq,
      fun Y => liftApply_periodic_of_coefficients n (Cc hh n) _ t Y
        (fun m _ α v u => hper hh n m α v u t ht Y)⟩
  have hs := sourceCoeff_transverse_of_reserved_inputs par (Set.Icc a b) Q.edge
    (by have hd := P.D_ge; omega) Q.η Φ hΦ hg P.transverse
    (fun v u d γ hγ α t ht =>
      ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩) j
  intro t ht X z s
  exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v)
    (hs t ht X z s)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Recover raw mean fields for the genuine ordered composition in the lift recurrence. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {K : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}

theorem AmbientLiftUncenteredData.mean_raw_contDiff
    (data : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K M)
    (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (u : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (p : ℕ∞)
      (liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t) := by
  apply contDiff_pi.mpr
  intro v
  have hg := (data.mean_component_grading hlam A u v ξ t ht 0 (Nat.zero_le p)).1
  have he : (fun X => liftMean Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X v) =
      fun X => Real.exp ((lam • A) X) • ((Real.exp ((lam • A) X))⁻¹ •
        liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t X v) := by
    funext X
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  rw [he]
  exact (Real.contDiff_exp.comp (lam • A).contDiff).smul hg

theorem AmbientLiftUncenteredData.mean_raw_measurable
    (data : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K M)
    (A : Vec 2 →L[ℝ] ℝ) (u : ι) (ξ : h u) (X : Vec 2) :
    Measurable (fun t => liftMean Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
        hh n (Set.projIcc a b hab t) X) := by
  apply Measurable.of_eval
  intro v
  have hm := (data.mean_component_measurable A u v ξ X).const_smul (Real.exp ((lam • A) X))
  have hme : Measurable (fun t => Real.exp ((lam • A) X) •
      ((Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
          hh n (Set.projIcc a b hab t) X v)) := hm
  simpa only [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul] using hme

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual zero-start field inverses are closed under finite addition through the original scalar weak equations. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_add_zero
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (hsZ : 1 ≤ sZ) (a b : ℝ) (hab : a ≤ b)
    (g f c d : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b 0 g c)
    (hd : IsCellFieldInverse G v sZ a b 0 f d) :
    IsCellFieldInverse G v sZ a b 0 (fun t z => g t z + f t z)
      (fun t z => c t z + d t z) := by
  have hsZ0 : ((sZ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hsZ)
  refine ⟨fun t ht => (hc.1 t ht).add (hd.1 t ht), ?_⟩
  intro l
  have hs := cellSolution_add (hc.2 l).1 (hd.2 l).1
  have hsrc : (fun t z => ((l (g t z) : ℝ) : ℂ)) + (fun t z => ((l (f t z) : ℝ) : ℂ)) =
      (fun t z => ((l (g t z + f t z) : ℝ) : ℂ)) := by
    funext t z
    simp only [Pi.add_apply, map_add, Complex.ofReal_add]
  rw [hsrc] at hs
  have hF : (fun (_ : ℝ) (_ : Vec 2) => (0 : PiLp 2 (fun _ : Fin 2 => ℂ))) +
      (fun (_ : ℝ) (_ : Vec 2) => (0 : PiLp 2 (fun _ : Fin 2 => ℂ))) = 0 := by
    funext t z
    exact zero_add 0
  rw [hF] at hs
  have hjet t (ht : t ∈ Icc a b) := (cellJetOfField_add_at l c d t
    ((hc.1 t ht).differentiable hsZ0) ((hd.1 t ht).differentiable hsZ0)).symm
  have hsol := AVRegularity.InitialLayer.cellSolution_congr_jet measurableSet_Icc hjet hs
  refine ⟨hsol, ?_, ?_, cellSolution_compact_energy_finite a b hab _ _ _ _ hsol⟩
  · intro t ht
    let : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weak_unitCube_volume_lt_top⟩
    have hi := ((hc.2 l).1.2.2.1 t ht).1.integrable (by norm_num)
    have hj := ((hd.2 l).1.2.2.1 t ht).1.integrable (by norm_num)
    change Integrable (fun z => ((l (c t z) : ℝ) : ℂ))
      (volume.restrict AVenhance.unitCube) at hi
    change Integrable (fun z => ((l (d t z) : ℝ) : ℂ))
      (volume.restrict AVenhance.unitCube) at hj
    change cellMean (fun z => ((l (c t z + d t z) : ℝ) : ℂ)) = 0
    simp only [map_add, Complex.ofReal_add]
    rw [cellMean, integral_add hi hj]
    change cellMean (cellValue (cellJetOfField l c) t) +
      cellMean (cellValue (cellJetOfField l d) t) = 0
    rw [(hc.2 l).2.1 t ht, (hd.2 l).2.1 t ht, add_zero]
  · filter_upwards [(hc.2 l).2.2.1, (hd.2 l).2.2.1] with z hz hz'
    change ((l (c a z) : ℝ) : ℂ) = ((l (0 : E) : ℝ) : ℂ) at hz
    change ((l (d a z) : ℝ) : ℂ) = ((l (0 : E) : ℝ) : ℂ) at hz'
    change ((l (c a z + d a z) : ℝ) : ℂ) = ((l (0 : E) : ℝ) : ℂ)
    simp only [map_add, Complex.ofReal_add, hz, hz', map_zero, Complex.ofReal_zero, add_zero]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Full source constants are nonnegative and are fixed by finite orders and data envelopes. -/

theorem normalizedSourceUniformConstant_nonneg (D p q j : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (Cj : ℕ → ℕ → ℝ) : 0 ≤ normalizedSourceUniformConstant D p q j A Cj := by
  unfold normalizedSourceUniformConstant
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg (normalizedSourceOrderConstant_nonneg D r s j A)
  unfold sourceEnvelopeJetConstant
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _

theorem normalizedSourceArrayConstant_nonneg (D p q j : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (Cj : ℕ → ℕ → ℝ) : 0 ≤ normalizedSourceArrayConstant D p q j A Cj := by
  have hf := normalizedSourceUniformConstant_nonneg D p (q + 1) j A Cj
  have hs := normalizedSourceUniformConstant_nonneg D (p + 1) q (j - 1) A Cj
  have hF : 0 ≤ sourceDivergenceFastFactor p q A := by unfold sourceDivergenceFastFactor; positivity
  have hS : 0 ≤ sourceDivergenceSlowFactor p q A := by unfold sourceDivergenceSlowFactor; positivity
  unfold normalizedSourceArrayConstant
  split_ifs <;> positivity

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! A finite C² periodic source is the literal scalar source of its absolute Hilbert Fourier sum. -/

theorem unitProfileFourierCoeff_summable (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hp : Function.Periodic f 1) (C : ℝ)
    (hj : ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv 2 f x‖ ≤ C) :
    Summable (unitProfileFourierCoeff f) := by
  have hs := profileFourier_jet_summable (unitProfileFourierCoeff f) 0 C (fun n hn =>
    unitProfileFourierCoeff_frequency_weight_bound 2 f hf hp n hn C hj)
  simpa only [pow_zero, one_mul] using hs

theorem profileSource_synthesis (f : ℝ → ℝ → ℂ) (t : ℝ) (par : Fin 2)
    (hf : ContDiff ℝ 2 (f t)) (hp : Function.Periodic (f t) 1) (C : ℝ)
    (hj : ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv 2 (f t) x‖ ≤ C) :
    cellSourceSlice (fun s z => f s (z par.rev)) t =
      ∑' n : ℤ, cellScalarCLM (unitProfileFourierCoeff (f t) n)
        (torusHkValueCLM (transverseFourierModeH1 par n)) := by
  have hc := unitProfileFourierCoeff_summable (f t) hf hp C hj
  apply cellSourceSlice_eq_of_ae
  have hs := transverseFourierMode_synthesis_ae par (unitProfileFourierCoeff (f t)) hc
  rw [profileFourierSeries_reconstruct (f t) hf.continuous hp hc] at hs
  exact hs

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Real duals preserve the literal mean-zero condition of real classical scalar fields. -/

theorem real_dual_scalar_mean_zero (c : Vec 2 → ℂ)
    (hreal : ∀ z, ((c z).re : ℂ) = c z) (hm : cellMean c = 0) (l : ℝ →L[ℝ] ℝ) :
    cellMean (fun z => ((l ((c z).re) : ℝ) : ℂ)) = 0 := by
  have he : (fun z : Vec 2 => ((l ((c z).re) : ℝ) : ℂ)) = fun z => l 1 • c z := by
    funext z
    rw [real_linear_functional_mul, Complex.ofReal_mul, hreal]
    rfl
  rw [he, cellMean, integral_smul]
  change l 1 • cellMean c = 0
  rw [hm, smul_zero]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Actual zero-start field inverses are closed under subtraction through their original weak equations. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_sub_zero
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (hsZ : 1 ≤ sZ) (a b : ℝ) (hab : a ≤ b)
    (g f c d : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b 0 g c)
    (hd : IsCellFieldInverse G v sZ a b 0 f d) :
    IsCellFieldInverse G v sZ a b 0 (fun t z => g t z - f t z)
      (fun t z => c t z - d t z) := by
  have hneg : IsCellFieldInverse G v sZ a b 0 (fun t z => -f t z) (fun t z => -d t z) := by
    have hz : (fun x : Vec 2 => (-1 : ℝ) • (0 : Vec 2 → E) x) = (0 : Vec 2 → E) := by
      funext x
      simp only [Pi.zero_apply, smul_zero]
    have hn := cellFieldInverse_const_smul G v sZ a b 0 f d hd (-1)
    rw [hz] at hn
    simpa only [neg_one_smul] using hn
  simpa only [sub_eq_add_neg] using
    cellFieldInverse_add_zero G v sZ hsZ a b hab g (fun t z => -f t z) c (fun t z => -d t z) hc hneg

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual paired first-cross tests retain the metric factor and the single-degree gain. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalizedCellB1_paired_lift_test_grading (n p q : ℕ) (η lam M Md W g B Bd : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (hW : 0 ≤ W)
    (hg : 0 ≤ g) (hB : 0 ≤ B) (hBd : 0 ≤ Bd)
    (A : Vec 2 →L[ℝ] ℝ) (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (drift : ℝ → Vec 2 → Vec 2) (t : ℝ) (c ci : LiftCoeff ι h) (v u : ι) (ξ : h u)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v' u',
      IsBoxSmooth (p + 1) (q + 1) (fun X z => c m α t X z v' u'))
    (hci : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v' u',
      IsBoxSmooth (p + 1) (q + 1) (fun X z => ci m α t X z v' u'))
    (hJ : ∀ i j, IsBoxSmooth (p + 1) q (fun X (_ : Vec 2) => J t X i j))
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun X (_ : Vec 2) => G t X i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => drift t z k)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbD : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j - J t Y i j) z) X‖ ≤ (Md * g) * lam ^ a)
    (hbv : ∀ k, ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun (_ : Vec 2) => iteratedFDeriv ℝ b
        (fun y => Real.sqrt η * drift t y k) z) X‖ ≤ W * lam ^ a)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => ci m α t Y y v u) z) X‖ ≤ B * lam ^ (n - m + a))
    (hbcd : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => c m α t Y y v u - ci m α t Y y v u) z) X‖ ≤ (Bd * g) * lam ^ (n - m + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB1 η G drift t
        (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • cellB1 η J drift t
          (liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      ((normalizedCellB1UniformConstant p q A M W * finiteLiftSymbolBudget n A * Bd +
        normalizedCellB1UniformConstant p q A Md 0 * finiteLiftSymbolBudget n A * B) * ‖ξ‖) * g *
        lam ^ ((n + 1) + r) := by
  let F := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t Y y
  let Fi := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t Y y
  let dc : LiftCoeff ι h := fun d β s Y y i j => c d β s Y y i j - ci d β s Y y i j
  have hf : IsBoxSmooth (p + 1) (q + 1) F := by
    apply isBoxSmooth_pi
    intro w
    exact normalized_lift_test_box_reserve n (p + 1) (q + 1) c lam A t w u ξ
      (fun m hm α => hc m hm α w u)
  have hfi : IsBoxSmooth (p + 1) (q + 1) Fi := by
    apply isBoxSmooth_pi
    intro w
    exact normalized_lift_test_box_reserve n (p + 1) (q + 1) ci lam A t w u ξ
      (fun m hm α => hci m hm α w u)
  have hbfi : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun w => Fi Y w v) y) X‖ ≤
        (finiteLiftSymbolBudget n A * B * ‖ξ‖) * lam ^ (n + a) := by
    intro a ha b hb y
    have hh := normalized_lift_test_mixed_grading n a b ci lam B hlam A t v u ξ
      (fun m hm α => (hci m hm α v u).mono ha hb) X y
      (fun m hm α => hbc m hm α a ha b hb y)
    simpa only [Fi, Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm] using! hh
  have hbdf : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun w => F Y w v - Fi Y w v) y) X‖ ≤
        ((finiteLiftSymbolBudget n A * Bd * ‖ξ‖) * g) * lam ^ (n + a) := by
    intro a ha b hb y
    have hh := normalized_lift_test_mixed_grading n a b dc lam (Bd * g) hlam A t v u ξ
      (fun m hm α => ((hc m hm α v u).sub (hci m hm α v u)).mono ha hb) X y
      (fun m hm α => hbcd m hm α a ha b hb y)
    change ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
      (normalizedLiftTestField dc n (lam • A) u v ξ t Y) y) X‖ ≤ _ at hh
    change ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
      (fun w => normalizedLiftTestField c n (lam • A) u v ξ t Y w -
        normalizedLiftTestField ci n (lam • A) u v ξ t Y w) y) X‖ ≤ _
    dsimp only [dc] at hh
    rw [normalizedLiftTestField_sub] at hh
    exact hh.trans_eq (by ring)
  have he : (fun Y y => Real.exp ((lam • A) Y) • F Y y) =
      liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t := by
    funext Y y
    dsimp only [F]
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hei : (fun Y y => Real.exp ((lam • A) Y) • Fi Y y) =
      liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t := by
    funext Y y
    dsimp only [Fi]
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  rw [← he, ← hei]
  have hh := normalizedCellB1_paired_component_mixed_grading p q n r s hr hs
    η lam M Md W g (finiteLiftSymbolBudget n A * B * ‖ξ‖)
    (finiteLiftSymbolBudget n A * Bd * ‖ξ‖) hη hlam hM hMd hW hg
    (mul_nonneg (mul_nonneg (finiteLiftSymbolBudget_nonneg n A) hB) (norm_nonneg ξ))
    (mul_nonneg (mul_nonneg (finiteLiftSymbolBudget_nonneg n A) hBd) (norm_nonneg ξ))
    A G J drift t F Fi v hf hfi hG hJ hv X hbG hbD hbv hbfi hbdf z
  exact hh.trans_eq (by ring)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! One finite full-source matrix controls every suborder of a common ambient reserve. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def normalizedFullSourceUniformMatrix (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q j : ℕ) (lam : ℝ) (A : Vec 2 →L[ℝ] ℝ) (v u : ι) : ℝ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
    normalizedSourceArrayMatrix edge I r s j lam A v u

def normalizedFullSourceUniformConstant (D p q j : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
    normalizedSourceArrayConstant D r s j A Cj

omit [Fintype ι] in
theorem normalizedFullSourceUniformMatrix_entry_le (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q r s j : ℕ) (hr : r ≤ p) (hs : s ≤ q)
    (lam : ℝ) (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    normalizedSourceArrayMatrix edge I r s j lam A v u ≤
      normalizedFullSourceUniformMatrix edge I p q j lam A v u := by
  have hn r s := normalizedSourceArrayMatrix_nonneg edge I r s j lam hlam A v u
  apply (Finset.single_le_sum (fun s _ => hn r s)
    (show s ∈ Finset.range (q + 1) by simp only [Finset.mem_range]; omega)).trans
  exact Finset.single_le_sum (fun r _ => Finset.sum_nonneg fun s _ => hn r s)
    (show r ∈ Finset.range (p + 1) by simp only [Finset.mem_range]; omega)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Genuine source tests retain fast periodicity under the original ambient reserves. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_source_test_periodic
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh n p q : ℕ)
    (hhh : hh ≤ H) (hp : D ≤ p) (hq : D ≤ q) (hqs : 1 ≤ qs) (hqf : 1 ≤ qf)
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p q (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (j : ℕ) :
    ∀ t ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
      sourceCoeff Q.edge Q.η j t (liftApply n (Cc hh n)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  intro t ht
  let Φ := liftApply n (Cc hh n)
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t
  have hg : GoodField D Φ :=
    ⟨(data.raw_test_box A u ξ t ht).contDiff_uncurry hp hq,
      liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh n _ t ht⟩
  have hs := sourceCoeff_good_zero Q.edge (by have hd := P.D_ge; omega) Q.η t Φ hg
    (fun v u d γ hγ α =>
      ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩) j
  intro X k z
  exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hs.2 X k z)
end

/-! Genuine source tests retain fast periodicity under the original ambient reserves. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_source_test_periodic_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u)) (hh n p q : ℕ)
    (hp : D ≤ p) (hq : D ≤ q) (hqs : 1 ≤ qs) (hqf : 1 ≤ qf)
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p q (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (j : ℕ) :
    ∀ t ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
      sourceCoeff Q.edge Q.η j t (liftApply n (Cc hh n)
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  intro t ht
  let Φ := liftApply n (Cc hh n)
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t
  have hg : GoodField D Φ :=
    ⟨(data.raw_test_box A u ξ t ht).contDiff_uncurry hp hq,
      fun Y => liftApply_periodic_of_coefficients n (Cc hh n) _ t Y
        (fun m _ α v u => hper hh n m α v u t ht Y)⟩
  have hs := sourceCoeff_good_zero Q.edge (by have hd := P.D_ge; omega) Q.η t Φ hg
    (fun v u d γ hγ α =>
      ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry hqs hqf, γ.periodic α t⟩) j
  intro X k z
  exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hs.2 X k z)
end

end AVRegularity.CycleComparison.Lift
end
