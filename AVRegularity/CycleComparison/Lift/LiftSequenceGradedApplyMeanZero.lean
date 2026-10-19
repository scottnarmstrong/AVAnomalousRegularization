-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.NormalizedSourceArrayZeroMatrixBound
import AVRegularity.CycleEvolution.FibreCoefficientWeightedForcing
import AVRegularity.CycleComparison.Lift.SecondCrossMean
public import AVRegularity.CycleComparison.Lift.SettingAmbientSourceTestPeriodicOfCoefficients
import AVRegularity.CycleComparison.Lift.PhysicalPowerSchurWiener
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite left-coefficient inverses synthesize the tested lift without any assumed lift sequence. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem liftApply_coefficient_inverse
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (hsZ : 1 ≤ sZ) (a b : ℝ) (hab : a ≤ b)
    (n : ℕ) (S C : LiftCoeff ι h) (f : Vec 2 → ∀ i, h i) (X : Vec 2)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v₀ u,
      IsCellFieldInverse G v sZ a b 0
        (fun t z => S m α t X z v₀ u) (fun t z => C m α t X z v₀ u)) :
    IsCellFieldInverse G v sZ a b 0
      (fun t z => liftApply n S (fun _ => f) t X z)
      (fun t z => liftApply n C (fun _ => f) t X z) := by
  apply cellFieldInverse_dependent_pi G v sZ hsZ a b hab
  intro v₀
  have he (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u : ι) :=
    cellFieldInverse_postcomposition
      (ContinuousLinearMap.apply ℝ (h v₀) (orderedDerivative α f X u))
      G v sZ hsZ a b 0
      (fun t z => S m α t X z v₀ u) (fun t z => C m α t X z v₀ u)
      (hc m hm α v₀ u)
  have hu (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) :=
    cellFieldInverse_finset_sum G v sZ hsZ a b hab Finset.univ
      (fun u t z => S m α t X z v₀ u (orderedDerivative α f X u))
      (fun u t z => C m α t X z v₀ u (orderedDerivative α f X u))
      (fun u _ => by
        have hi := he m hm α u
        have hz : (fun z : Vec 2 => (ContinuousLinearMap.apply ℝ (h v₀)
            (orderedDerivative α f X u)) ((0 : Vec 2 → (h u →L[ℝ] h v₀)) z)) =
            (0 : Vec 2 → h v₀) := by
          funext z
          exact map_zero _
        rw [hz] at hi
        exact hi)
  have ha (m : ℕ) (hm : m ≤ n) :=
    cellFieldInverse_finset_sum G v sZ hsZ a b hab Finset.univ
      (fun α t z => ∑ u, S m α t X z v₀ u (orderedDerivative α f X u))
      (fun α t z => ∑ u, C m α t X z v₀ u (orderedDerivative α f X u))
      (fun α _ => hu m hm α)
  have hs := cellFieldInverse_finset_sum G v sZ hsZ a b hab (Finset.range (n + 1))
    (fun m t z => ∑ α : DerivativeWord2 m, ∑ u, S m α t X z v₀ u (orderedDerivative α f X u))
    (fun m t z => ∑ α : DerivativeWord2 m, ∑ u, C m α t X z v₀ u (orderedDerivative α f X u))
    (fun m hm => by
      have hm' : m ≤ n := by have := Finset.mem_range.mp hm; omega
      exact ha m hm')
  simpa only [liftApply] using hs
end

/-! The literal source coefficients `sourceCoeff` inherit the full normalized matrix bound under the
ambient reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem normalizedSourceCoeff_matrix_bound
    (π : ι → ℝ) (edge : ConstituentEdges D h) (hD : 1 ≤ D) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (hj : j ≤ D) (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (C : ι → ℝ) (hC : ∀ u, 0 ≤ C u)
    (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ u, IsBoxSmooth (max D (p + j)) (max D (q + D - j)) (fun Y y => f Y y u))
    (hper : ∀ X, AVenhance.IsZ2Periodic (f X))
    (t : ℝ) (ht : t ∈ I)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth (p + 1) (q + 1) (γ.coeff α t))
    (hΓper : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X,
      AVenhance.IsZ2Periodic (fun z => γ.coeff α t X z))
    (X : Vec 2)
    (hbf : ∀ u, ∀ a ≤ p + j, ∀ s ≤ q + D - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (fun y => f Y y u) z) X‖ ≤
        C u * lam ^ (δ + a)) (v : ι) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceCoeff edge η j t
        (fun Z y => Real.exp ((lam • A) Z) • f Z y) Y y v) z) X‖ ≤
      (∑ u, normalizedSourceArrayMatrix edge I p q j lam A v u * C u) * lam ^ (δ + j + p) := by
  let Φ := fun Z y => Real.exp ((lam • A) Z) • f Z y
  have hΦ : IsBoxSmooth (max D (p + j)) (max D (q + D - j)) Φ := by
    apply isBoxSmooth_pi
    intro u
    exact isBoxSmooth_bilinear
      (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) (hf u)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h u →L[ℝ] h u)
  have hgood : GoodField D Φ := ⟨hΦ.contDiff_uncurry (Nat.le_max_left _ _)
    (Nat.le_max_left _ _), fun X n y => congrArg (fun c => Real.exp ((lam • A) X) • c)
      (hper X n y)⟩
  have hΓgood : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z) := by
    intro v u d γ hm α
    exact ⟨(hΓ v u d γ hm α).contDiff_uncurry (by omega) (by omega), hΓper v u d γ hm α⟩
  have ha := sourceCoeff_eq_sourceCoefficientArray edge hD η t Φ hgood hΓgood j
  have hb := sourceCoefficientArray_component_eq edge hD η t Φ j hj
    (fun v u d γ hm α => (hΓ v u d γ hm α).mono (by omega) (by omega))
    (hΦ.mono (by omega) (by omega)) v
  have hpoint (Y y : Vec 2) : sourceCoeff edge η j t Φ Y y v =
      sourceComponentCoefficientArray edge η t Φ j v Y y := by
    rw [ha]
    exact congrFun (congrFun hb Y) y
  simp_rw [show ∀ Y y, sourceCoeff edge η j t
      (fun Z y => Real.exp ((lam • A) Z) • f Z y) Y y v =
      sourceComponentCoefficientArray edge η t Φ j v Y y from hpoint]
  by_cases hj0 : j = 0
  · subst j
    simpa only [Nat.add_zero, Nat.sub_zero, Nat.zero_add, Φ] using
      normalizedSourceArray_zero_matrix_bound π edge hD I lam hlam Cj qs qf b Θ he hπ η hη
        δ p q (by omega) hq A C hC f
        (fun u => (hf u).mono (by omega) (by omega)) t ht
        (fun v u d γ hm α => (hΓ v u d γ hm α).mono (by omega) le_rfl) X
        (by simpa only [Nat.add_zero, Nat.sub_zero] using hbf) v z
  · exact normalizedSourceArray_positive_matrix_bound π edge hD I lam hlam Cj qs qf b Θ he
      hπ η hη δ p q j hj0 hp hq A C hC f
      (fun u => (hf u).mono (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      t ht hΓ X hbf v z
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The Riesz derivative of each actual Fourier state agrees with the projected scalar ODE. -/

theorem transverseFourierModeH1_dual_equation
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (t : ℝ) (n : ℤ) (c f : ℂ) :
    cellDualDerivative ⟨fun t _ => G t, v, 0, 0⟩ hG V hv hb t
      (cellH1Scalar c (transverseFourierModeH1 par n))
      (cellScalarCLM f (torusHkValueCLM (transverseFourierModeH1 par n))) (fun _ => 0) =
      cellPivotDualCLM (cellScalarCLM
        ((-(‖profileFourierFrequency n‖ ^ 2) * G t par.rev par.rev) • c + f)
        (torusHkValueCLM (transverseFourierModeH1 par n))) := by
  apply ext_inner_right ℝ
  intro z
  rw [← cellDualComplexPair_re, ← cellDualComplexPair_re]
  apply congrArg Complex.re
  rw [cellDualComplexPair_derivative, cellPivotDual_complex_pair,
    cellComplexGenerator_scalar, transverseFourierModeH1_weak_generator G hG v V hv hb par ht,
    cellComplexPair_scalar_left]
  simp only [cellComplexSource, cellComplexPair_zero_left, Finset.sum_const_zero, sub_zero,
    cellComplexPair_scalar_left]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Paired actual cross terms inherit the native rectangular reserves. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_first_cross_paired_lift_box
    (n p q p' q' : ℕ) (hp : p + 1 ≤ qs) (hq : q ≤ qf)
    (hp' : p + 1 ≤ p') (hq' : q + 1 ≤ q')
    (c ci : LiftCoeff ι h) (M Mi : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' c M)
    (datai : AmbientLiftCoefficientData par a b P.window lam n p' q' ci Mi)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η Q.G Q.v t
      (liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v -
      (Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η
        (fun _ _ i j => if i = j then 1 else 0) Q.v t
        (liftApply n ci (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  exact (setting_ambient_first_cross_lift_box P n p q p' q' hp hq hp' hq'
    c M data A t ht v u ξ).sub
    (setting_ambient_first_cross_lift_box (setting_identity_metric P) n p q p' q'
      hp hq hp' hq' ci Mi datai A t ht v u ξ)

include P in
theorem setting_ambient_second_cross_paired_lift_box
    (n p q p' q' : ℕ) (hp : p + 1 ≤ qs)
    (hp' : p + 2 ≤ p') (hq' : q ≤ q')
    (c ci : LiftCoeff ι h) (M Mi : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' c M)
    (datai : AmbientLiftCoefficientData par a b P.window lam n p' q' ci Mi)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
      (liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v -
      (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η
        (fun _ _ i j => if i = j then 1 else 0) t
        (liftApply n ci (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  exact (setting_ambient_second_cross_lift_box P n p q p' q' hp hp' hq'
    c M data A t ht v u ξ).sub
    (setting_ambient_second_cross_lift_box (setting_identity_metric P) n p q p' q'
      hp hp' hq' ci Mi datai A t ht v u ξ)
end

/-! The actual source lift term has a fixed-data budget under its ambient predecessor state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_sourceFlux_lift_box
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n p q j p' q' : ℕ)
    (hp : p ≤ qs) (hq : q ≤ qf) (hp' : p + j ≤ p') (hq' : q + (D - 1) - j ≤ q')
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (v u : ι) (ξ : h u) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      sourceFluxComponentCoefficient Q.edge Q.η t
        (liftApply n (Cc hh n) (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t)
        k₀ j v X z) := by
  let F := fun X z => (Real.exp ((lam • A) X))⁻¹ •
    liftApply n (Cc hh n) (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t X z
  have hF (w : ι) : IsBoxSmooth (p + j) (q + (D - 1) - j) (fun X z => F X z w) :=
    normalized_lift_test_box_reserve n _ _ (Cc hh n) lam A t w u ξ
      (fun m hm α => (data.box m hm α w u t ht).mono hp' hq')
  have hrecover : (fun Y y => Real.exp ((lam • A) Y) • F Y y) =
      liftApply n (Cc hh n) (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t := by
    funext Y y
    dsimp only [F]
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  rw [← hrecover]
  exact normalizedSourceFluxComponent_box_reserve Q.edge Q.η t lam A k₀ p q j
    (fun v u d γ hγ α => (P.coeff_smooth v u d γ hγ α t ht).mono hp hq) F hF v
end

/-! The actual source lift term has a fixed-data budget under its ambient predecessor state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_sourceFlux_lift_bound
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n p q j p' q' : ℕ)
    (hp : p ≤ qs) (hq : q ≤ qf)
    (hp' : p + j ≤ p') (hq' : q + (D - 1) - j ≤ q')
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceFluxComponentCoefficient Q.edge Q.η t
        (liftApply n (Cc hh n) (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) k₀ j v Y y) z) X‖ ≤
      (finiteLiftSymbolBudget n A * normalizedSourceUniformConstant D p q j A Cj *
        finiteMatrixProduct (physicalEdgeEnvelopeMatrix π edge) M v u * ‖ξ‖) *
          lam ^ (n + j + r) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hΓ v u d γ (hγ : γ ∈ Q.edge v u d) α :
      IsBoxSmooth p q (γ.coeff α t) :=
    (P.coeff_smooth v u d γ hγ α t ht).mono (by omega) (by omega)
  have hb := normalizedSourceFlux_lift_test_uniform_matrix_grading π Q.edge
    (Set.Icc a b) lam hlam Cj qs qf edge Θ P.envelope
    P.mass_pos Q.η P.η_le n p q j k₀ (by omega) (by omega) A (fun w => M w u) (fun w => data.nonneg w u)
    (Cc hh n) t ht v u ξ
    (fun m hm α v' u' => (data.box m hm α v' u' t ht).mono hp' (by omega))
    hΓ X
    (fun w m hm α a ha b hb y => data.bound m hm α w u a
      (ha.trans hp')
      b (by omega) t ht X y) r s hr hs z
  apply hb.trans
  have hmat := normalizedSourceUniformMatrix_physical_product_le π P.mass_pos Q.edge
    (Set.Icc a b) lam hlam Cj qs qf edge Θ P.envelope p q j (by omega) (by omega) A M data.nonneg v u
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmat (finiteLiftSymbolBudget_nonneg n A)) (norm_nonneg ξ))
      (pow_nonneg hlam.le (n + j + r))
  convert hmul using 1
  ring
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Weak energy uniqueness identifies continuous representatives of any two actual finite-past inverses. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_unique
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (sZ sZ' : ℕ) (a b : ℝ) (hab : a ≤ b)
    (c0 : Vec 2 → E) (g c d : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b c0 g c)
    (hd : IsCellFieldInverse G v sZ' a b c0 g d) :
    ∀ t ∈ Icc a b, c t = d t := by
  intro t ht
  funext x
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro l
  have he := cellSolution_common_source_unique hab ⟨fun r _ => G r, v, 0, 0⟩ hG V 0
    hv hb measurable_const (fun _ => by simp)
    (fun r y => ((l (g r y) : ℝ) : ℂ)) 0
    (cellJetOfField l c) (cellJetOfField l d) (hc.2 l).1 (hd.2 l).1
    ((hc.2 l).2.2.1.trans (hd.2 l).2.2.1.symm)
  have hccont : Continuous (cellValue (cellJetOfField l c) t) :=
    Complex.ofRealCLM.continuous.comp (l.continuous.comp (hc.1 t ht).continuous)
  have hdcont : Continuous (cellValue (cellJetOfField l d) t) :=
    Complex.ofRealCLM.continuous.comp (l.continuous.comp (hd.1 t ht).continuous)
  have hp := periodicContinuous_eq_of_cell_ae _ _ hccont hdcont
    ((hc.2 l).1.2.2.1 t ht).2 ((hd.2 l).1.2.2.1 t ht).2 (he t ht)
  exact Complex.ofReal_injective (congrFun hp x)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! One full physical matrix majorant grades every reserved suborder of the actual literal source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem normalizedSourceCoeff_uniform_matrix_bound
    (π : ι → ℝ) (edge : ConstituentEdges D h) (hD : 1 ≤ D) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (hj : j ≤ D) (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (C : ι → ℝ) (hC : ∀ u, 0 ≤ C u)
    (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ u, IsBoxSmooth (max D (p + j)) (max D (q + D - j)) (fun Y y => f Y y u))
    (hper : ∀ X, AVenhance.IsZ2Periodic (f X))
    (t : ℝ) (ht : t ∈ I)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth (p + 1) (q + 1) (γ.coeff α t))
    (hΓper : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X,
      AVenhance.IsZ2Periodic (fun z => γ.coeff α t X z))
    (X : Vec 2)
    (hbf : ∀ u, ∀ a ≤ p + j, ∀ s ≤ q + D - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (fun y => f Y y u) z) X‖ ≤
        C u * lam ^ (δ + a)) (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (v : ι) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceCoeff edge η j t
        (fun Z y => Real.exp ((lam • A) Z) • f Z y) Y y v) z) X‖ ≤
      (∑ u, normalizedFullSourceUniformMatrix edge I p q j lam A v u * C u) * lam ^ (δ + j + r) := by
  have hh := normalizedSourceCoeff_matrix_bound π edge hD I lam hlam Cj qs qf b Θ he hπ η hη
    δ r s j hj (by omega) (by omega) A C hC f
    (fun u => (hf u).mono (by omega) (by omega)) hper t ht
    (fun v u d γ hm α => (hΓ v u d γ hm α).mono (by omega) (by omega)) hΓper X
    (fun u a ha b hb y => hbf u a (by omega) b (by omega) y) v z
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam.le _)
  apply Finset.sum_le_sum
  intro u _
  exact mul_le_mul_of_nonneg_right
    (normalizedFullSourceUniformMatrix_entry_le edge I p q r s j hr hs lam hlam.le A v u)
    (hC u)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The weak inverse's scalar mean conditions give the literal vector cell mean. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_fieldCellMean_zero
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (a b : ℝ) (c0 : Vec 2 → E) (g c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b c0 g c)
    (t : ℝ) (ht : t ∈ Set.Icc a b) : fieldCellMean (c t) = 0 := by
  have hi : IntegrableOn (c t) AVenhance.unitCube :=
    (AVenhance.Infra.Torus.Calculus.continuous_integrableOn_unitCell (hc.1 t ht).continuous).congr_set_ae
       AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.symm
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro l
  apply Complex.ofReal_injective
  let A := Complex.ofRealCLM.comp l
  have hm := (hc.2 l).2.1 t ht
  change (∫ z in AVenhance.unitCube, ((l (c t z) : ℝ) : ℂ)) = 0 at hm
  have he := A.integral_comp_comm hi
  change (∫ z in AVenhance.unitCube, ((l (c t z) : ℝ) : ℂ)) =
    ((l (fieldCellMean (c t)) : ℝ) : ℂ) at he
  rw [← he, hm, map_zero, Complex.ofReal_zero]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual source operator on a lift test combines its physical matrix with the lift row budgets. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem normalizedSourceCoeff_lift_test_uniform_matrix_grading
    (π : ι → ℝ) (edge : ConstituentEdges D h) (hD : 1 ≤ D) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (n p q j : ℕ) (hj : j ≤ D) (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (A : Vec 2 →L[ℝ] ℝ) (B : ι → ℝ) (hB : ∀ u, 0 ≤ B u)
    (c : LiftCoeff ι h) (t : ℝ) (ht : t ∈ I) (v u₀ : ι) (ξ : h u₀)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v' u',
      IsBoxSmooth (max D (p + j)) (max D (q + D - j))
        (fun X z => c m α t X z v' u'))
    (hper : ∀ X, AVenhance.IsZ2Periodic
      (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u₀ ξ) t X))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth (p + 1) (q + 1) (γ.coeff α t))
    (hΓper : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X,
      AVenhance.IsZ2Periodic (fun z => γ.coeff α t X z))
    (X : Vec 2)
    (hbc : ∀ u, ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ a ≤ p + j, ∀ s ≤ q + D - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s
        (fun y => c m α t Y y u u₀) z) X‖ ≤ B u * lam ^ (n - m + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceCoeff edge η j t
        (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u₀ ξ) t) Y y v) z) X‖ ≤
      (finiteLiftSymbolBudget n A *
        (∑ u, normalizedFullSourceUniformMatrix edge I p q j lam A v u * B u) * ‖ξ‖) *
          lam ^ (n + j + r) := by
  let F := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u₀ ξ) t Y y
  have hf u : IsBoxSmooth (max D (p + j)) (max D (q + D - j)) (fun Y y => F Y y u) :=
    normalized_lift_test_box_reserve n _ _ c lam A t u u₀ ξ (fun m hm α => hc m hm α u u₀)
  have hfper : ∀ Y, AVenhance.IsZ2Periodic (F Y) := by
    intro Y k y
    dsimp only [F]
    rw [hper Y k y]
  have hb u a (ha : a ≤ p + j) s (hs : s ≤ q + D - j) y :
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
  have hh := normalizedSourceCoeff_uniform_matrix_bound π edge hD I lam hlam Cj qs qf b Θ he hπ η hη
    n p q j hj hp hq A (fun u => finiteLiftSymbolBudget n A * B u * ‖ξ‖)
    (fun u => mul_nonneg (mul_nonneg (finiteLiftSymbolBudget_nonneg n A) (hB u)) (norm_nonneg ξ))
    F hf hfper t ht hΓ hΓper X hb r s hr hs v z
  apply hh.trans_eq
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun u _ => by ring)
end

/-! Entry inverses and a finite source presentation give genuine normalized component inverses. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftCoefficient_normalized_test_inverse
    (Q : LiftOperatorData ι h D) (a b : ℝ) (hab : a ≤ b)
    (q : ℕ) (hq : 1 ≤ q) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (S : LiftCoeff ι h) (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (X : Vec 2)
    (hi : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v₀ u₀,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
        (fun t z => S m α t X z v₀ u₀) (fun t z => Cc hh n m α t X z v₀ u₀))
    (hblock : ∀ t ∈ Set.Icc a b, ∀ z,
      normalizedLiftTestField S n A u v ξ t X z =
        normalizedLiftSourceField Q Cc hh n A u v ξ t X z) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
      (fun t z => normalizedLiftSourceField Q Cc hh n A u v ξ t X z)
      (fun t z => normalizedLiftTestField (Cc hh n) n A u v ξ t X z) := by
  have hf := liftApply_coefficient_inverse (fun t => Matrix.of (Q.G t X)) Q.v q hq
    a b hab n S (Cc hh n) (fun Y => Real.exp (A Y) • Pi.single u ξ) X hi
  have hp := cellFieldInverse_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
    (fun t => Matrix.of (Q.G t X)) Q.v q hq a b 0 _ _ hf
  have hs := cellFieldInverse_const_smul (fun t => Matrix.of (Q.G t X)) Q.v q a b
    _ _ _ hp ((Real.exp (A X))⁻¹)
  have hs' : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
      (fun t z => normalizedLiftTestField S n A u v ξ t X z)
      (fun t z => normalizedLiftTestField (Cc hh n) n A u v ξ t X z) := by
    simpa only [normalizedLiftTestField, ContinuousLinearMap.proj_apply,
      Pi.zero_apply, smul_zero] using! hs
  exact cellFieldInverse_source_congr_on (fun t => Matrix.of (Q.G t X)) Q.v q a b
    0 _ _ _ (fun t ht => funext (hblock t ht)) hs'
end

/-! Actual normalized exponential lift tests retain the vector mean-zero inverse condition. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_normalized_exponential_mean_zero (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (A : Vec 2 →L[ℝ] ℝ) (u : ι) (ξ : h u) (X : Vec 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    fieldCellMean (fun z => (Real.exp (A X))⁻¹ •
      liftApply n (Cc hh n) (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z) = 0 := by
  exact cellFieldInverse_fieldCellMean_zero _ _ sZ a b 0 _ _
    (liftSequence_normalized_exponential_inverse Q sX sZ a b N H Cc hc hh n hhh hn hnN
      A u ξ X) t ht
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The actual source lift term has a fixed-data budget under its ambient predecessor state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_source_lift_bound
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q j p' q' : ℕ) (hhh : hh ≤ H) (hj : j ≤ D)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (hp' : max D (p + j) ≤ p') (hq' : max D (q + D - j) ≤ q')
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceCoeff Q.edge Q.η j t
        (liftApply n (Cc hh n) (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      (finiteLiftSymbolBudget n A * normalizedFullSourceUniformConstant D p q j A Cj *
        finiteMatrixProduct (physicalEdgeEnvelopeMatrix π edge) M v u * ‖ξ‖) *
          lam ^ (n + j + r) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hΓ v u d γ (hγ : γ ∈ Q.edge v u d) α :
      IsBoxSmooth (p + 1) (q + 1) (γ.coeff α t) :=
    (P.coeff_smooth v u d γ hγ α t ht).mono hp hq
  have hb := normalizedSourceCoeff_lift_test_uniform_matrix_grading π Q.edge
    (by have hd := P.D_ge; omega) (Set.Icc a b) lam hlam Cj qs qf edge Θ P.envelope
    P.mass_pos Q.η P.η_le n p q j hj hp hq A (fun w => M w u) (fun w => data.nonneg w u)
    (Cc hh n) t ht v u ξ
    (fun m hm α v' u' => (data.box m hm α v' u' t ht).mono hp' hq')
    (fun Y => liftApply_periodic Q sX sZ a b N H Cc hseq hh hhh n _ t ht Y)
    hΓ (fun v u d γ _ α Y => γ.periodic α t Y) X
    (fun w m hm α a ha b hb y => data.bound m hm α w u a
      (ha.trans ((Nat.le_max_right _ _).trans hp'))
      b (hb.trans ((Nat.le_max_right _ _).trans hq')) t ht X y) r s hr hs z
  apply hb.trans
  have hmat := normalizedFullSourceUniformMatrix_physical_product_le π P.mass_pos Q.edge
    (Set.Icc a b) lam hlam Cj qs qf edge Θ P.envelope p q j hp hq A M data.nonneg v u
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmat (finiteLiftSymbolBudget_nonneg n A)) (norm_nonneg ξ))
      (pow_nonneg hlam.le (n + j + r))
  convert hmul using 1
  ring
end

/-! The actual source lift term has a fixed-data budget under its ambient predecessor state. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_source_lift_bound_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u))
    (hh n p q j p' q' : ℕ) (hj : j ≤ D)
    (hp : p + 1 ≤ qs) (hq : q + 1 ≤ qf)
    (hp' : max D (p + j) ≤ p') (hq' : max D (q + D - j) ≤ q')
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' (Cc hh n) M)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceCoeff Q.edge Q.η j t
        (liftApply n (Cc hh n) (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      (finiteLiftSymbolBudget n A * normalizedFullSourceUniformConstant D p q j A Cj *
        finiteMatrixProduct (physicalEdgeEnvelopeMatrix π edge) M v u * ‖ξ‖) *
          lam ^ (n + j + r) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hΓ v u d γ (hγ : γ ∈ Q.edge v u d) α :
      IsBoxSmooth (p + 1) (q + 1) (γ.coeff α t) :=
    (P.coeff_smooth v u d γ hγ α t ht).mono hp hq
  have hb := normalizedSourceCoeff_lift_test_uniform_matrix_grading π Q.edge
    (by have hd := P.D_ge; omega) (Set.Icc a b) lam hlam Cj qs qf edge Θ P.envelope
    P.mass_pos Q.η P.η_le n p q j hj hp hq A (fun w => M w u) (fun w => data.nonneg w u)
    (Cc hh n) t ht v u ξ
    (fun m hm α v' u' => (data.box m hm α v' u' t ht).mono hp' hq')
    (fun Y => liftApply_periodic_of_coefficients n (Cc hh n) _ t Y
      (fun m _ α v u => hper hh n m α v u t ht Y))
    hΓ (fun v u d γ _ α Y => γ.periodic α t Y) X
    (fun w m hm α a ha b hb y => data.bound m hm α w u a
      (ha.trans ((Nat.le_max_right _ _).trans hp'))
      b (hb.trans ((Nat.le_max_right _ _).trans hq')) t ht X y) r s hr hs z
  apply hb.trans
  have hmat := normalizedFullSourceUniformMatrix_physical_product_le π P.mass_pos Q.edge
    (Set.Icc a b) lam hlam Cj qs qf edge Θ P.envelope p q j hp hq A M data.nonneg v u
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmat (finiteLiftSymbolBudget_nonneg n A)) (norm_nonneg ξ))
      (pow_nonneg hlam.le (n + j + r))
  convert hmul using 1
  ring
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Every actual positive lift coefficient is centered, by finite calibration of its inverse tests. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_coefficient_applied_mean_zero (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n m : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (X : Vec 2) (v u : ι) (ξ : h u) :
    fieldCellMean (fun z => Cc hh n m α t X z v u ξ) = 0 := by
  apply liftCoefficient_applied_mean_zero_of_finite_tests n m hm (Cc hh n) 1 one_ne_zero
    (fun β σ => hc.2.2.2.2.1 hh hhh n m β σ) α t X v u ξ
  intro j s
  let A : Vec 2 →L[ℝ] ℝ := (s : ℝ) • ((1 : ℝ) • coordinateSymbolDirection (j : ℝ))
  let F := fun z => (Real.exp (A X))⁻¹ •
    liftApply n (Cc hh n) (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z
  have hi := liftSequence_normalized_exponential_inverse Q sX sZ a b N H Cc hc
    hh n hhh hn hnN A u ξ X
  have hF : Continuous F := (hi.1 t ht).continuous
  have hmF := liftSequence_normalized_exponential_mean_zero Q sX sZ a b N H Cc hc
    hh n hhh hn hnN A u ξ X t ht
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, F, A, Pi.smul_apply] using!
      (continuous_apply v).comp hF
  · have he := AVRegularity.fieldCellMean_clm
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) hF
    change fieldCellMean (fun z => F z v) = _ at he
    have hmean : fieldCellMean (fun z => F z v) = 0 := by
      rw [he]
      change (fieldCellMean F) v = 0
      rw [hmF]
      rfl
    simpa only [F, A, Pi.smul_apply] using! hmean

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The absolute Fourier response solves the actual scalar-forced shear cell equation on the finite window. -/

theorem profileResponse_cell_curve
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) (hfm : Measurable (Function.uncurry f))
    (C : Fin 3 → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ 2 (f t))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (f t) 1)
    (hj : ∀ j : Fin 3, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j.val (f t) x‖ ≤ C j) :
    let c := fun t n => profileModeResponse (fun r => G r par.rev par.rev) f a t n
    let m := fun n => transverseFourierModeH1 par n
    CellWeakHilbertCurve a b
      (fun t => ∑' n : ℤ, cellScalarCLM (c t n) (torusHkValueCLM (m n)))
      (fun t => ∑' n : ℤ, cellH1Scalar (c t n) (m n))
      (fun t => cellDualDerivative ⟨fun t _ => G t, v, 0, 0⟩ hG V hv hb t
        (∑' n : ℤ, cellH1Scalar (c t n) (m n))
        (cellSourceSlice (fun s z => f s (z par.rev)) t) (fun _ => 0)) := by
  dsimp only
  let g := fun r => G r par.rev par.rev
  have hgm : AEStronglyMeasurable g volume :=
    ((cellMetric_entry_measurable hG par.rev par.rev).comp
      (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))).aestronglyMeasurable
  have hgb (r : ℝ) : |g r| ≤ 2 := cellMetric_entry_bound hG r 0 par.rev par.rev
  have hgl (r : ℝ) (_ : r ∈ Icc a b) : (1 / 2 : ℝ) ≤ g r := by
    simpa [basisVec_apply, g] using (hG.2.2.2 r 0 (basisVec par.rev)).1
  have hi : IntegrableOn g (Icc a b) := by
    apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne hgm
    exact Filter.Eventually.of_forall fun r => by simpa only [Real.norm_eq_abs] using hgb r
  have hz (r : ℝ) (hr : r ∈ Icc a b) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : ‖f r x‖ ≤ C 0 := by
    simpa using hj 0 r hr x hx
  have hs := profileResponseSeries_hilbert_curve g f a b (1 / 2) 2 hab (by norm_num)
    (by norm_num) hgm hgb hgl hfm C hC hf hp hj par
  apply hs.dual_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have hc : Summable (fun n => profileModeResponse g f a r n) := by
    apply (profileJetMajorant_summable (C 0 / (1 / 2)) (C 0 * (b - a))).of_norm_bounded
    intro n
    simpa only [pow_zero, one_mul] using profileModeResponse_uniform_jet_bound g f a b
      (1 / 2) hab (by norm_num) hi hgl 0 (C 0) (C 0) (hC 0) (hC 0)
      (fun s hs => (hf s hs).of_le (by norm_num)) hp (hj 0) hz n r hr
  have hd : Summable (fun n => profileFourierFrequency n * profileModeResponse g f a r n) := by
    apply (profileJetMajorant_summable (C 1 / (1 / 2)) (C 0 * (b - a))).of_norm_bounded
    intro n
    simpa only [pow_one] using profileModeResponse_uniform_jet_bound g f a b
      (1 / 2) hab (by norm_num) hi hgl 1 (C 1) (C 0) (hC 1) (hC 0)
      (fun s hs => (hf s hs).of_le (by norm_num)) hp (hj 1) hz n r hr
  rw [profileSource_synthesis f r par (hf r hr) (hp r hr) (C 2) (hj 2 r hr)]
  rw [cellDualDerivative_scalar_source_tsum _ _ _ _ _ _ _ _
    (transverseFourierMode_state_summable par _ hc hd)
    (transverseFourierMode_value_summable par _
      (unitProfileFourierCoeff_summable (f r) (hf r hr) (hp r hr) (C 2) (hj 2 r hr)))]
  apply tsum_congr
  intro n
  exact (transverseFourierModeH1_dual_equation G hG v V hv hb par ht r n _ _).symm

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The original lift setting suffices for uniqueness across different stored regularity orders. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

include P in
theorem setting_cellFieldInverse_unique (X : Vec 2) (sZ sZ' : ℕ)
    (c0 : Vec 2 → F) (g g' c d : ℝ → Vec 2 → F)
    (hc : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b c0 g c)
    (hd : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ' a b c0 g' d)
    (hg : ∀ t ∈ Set.Icc a b, g t = g' t) : ∀ t ∈ Set.Icc a b, c t = d t := by
  have hc' := cellFieldInverse_source_congr_on _ _ sZ a b c0 g g' c hg hc
  have hc'' := cellFieldInverse_local_coefficients _ _ sZ a b P.window c0 g' c hc'
  have hd' := cellFieldInverse_local_coefficients _ _ sZ' a b P.window c0 g' d hd
  obtain ⟨W, hW⟩ := setting_drift_bound P
  apply cellFieldInverse_unique _ (setting_cell_metric P X) _ W
    (localCellDrift_measurable a b P.window Q.v (setting_drift_continuous P) P.v_meas)
    (fun t z => hW _ (Set.projIcc a b P.window t).2 z)
    sZ sZ' a b P.window c0 g' c d hc'' hd'

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Recurrence constants depend only on the declared data budgets and finite orders. -/

def ambientFirstCrossScalarConstant (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG Cw : ℕ → ℝ) : ℝ :=
  normalizedCellB1UniformConstant p q A (metricParameterBudget (p + 1) CG)
    (metricParameterBudget q Cw) * finiteLiftSymbolBudget n A

def ambientSecondCrossScalarConstant (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG : ℕ → ℝ) : ℝ :=
  normalizedCellB2UniformConstant p q A (metricParameterBudget (p + 1) CG) *
    finiteLiftSymbolBudget n A

def ambientSourceScalarConstant (D n p q j : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (Cj : ℕ → ℕ → ℝ) : ℝ :=
  finiteLiftSymbolBudget n A * normalizedFullSourceUniformConstant D p q j A Cj

theorem ambientFirstCrossScalarConstant_nonneg (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG Cw : ℕ → ℝ) : 0 ≤ ambientFirstCrossScalarConstant n p q A CG Cw := by
  apply mul_nonneg _ (finiteLiftSymbolBudget_nonneg n A)
  exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
    normalizedCellB1MixedConstant_nonneg r s A _ _
      (metricParameterBudget_nonneg (p + 1) CG) (metricParameterBudget_nonneg q Cw)

theorem ambientSecondCrossScalarConstant_nonneg (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG : ℕ → ℝ) : 0 ≤ ambientSecondCrossScalarConstant n p q A CG := by
  apply mul_nonneg _ (finiteLiftSymbolBudget_nonneg n A)
  exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
    normalizedCellB2MixedConstant_nonneg r s A _ (metricParameterBudget_nonneg (p + 1) CG)

theorem exponentialLiftCompositionNormalizedConstant_nonneg (n p q : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) : 0 ≤ exponentialLiftCompositionNormalizedConstant n p q A := by
  unfold exponentialLiftCompositionNormalizedConstant exponentialLiftCompositionRawConstant
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (mul_nonneg (mul_nonneg (finiteLiftWordCount_nonneg n) (by positivity)) (by positivity))

theorem ambientSourceScalarConstant_nonneg (D n p q j : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (Cj : ℕ → ℕ → ℝ) : 0 ≤ ambientSourceScalarConstant D n p q j A Cj :=
  mul_nonneg (finiteLiftSymbolBudget_nonneg n A)
    (normalizedFullSourceUniformConstant_nonneg D p q j A Cj)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Every positive actual lift has zero tested component mean for arbitrary coarse inputs. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_tested_component_mean_zero (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (X : Vec 2) (v : ι) : fieldCellMean (fun z => liftApply n (Cc hh n) f t X z v) = 0 := by
  apply liftApply_component_mean_zero_of_centered_coefficients n (Cc hh n) f t X v
  · intro m _ α u
    exact ((hc.2.2.2.2.2.1 hh hhh n m α v u t ht).1.1 X).continuous
  · intro m hm α u ξ
    exact liftSequence_coefficient_applied_mean_zero Q sX sZ a b N H Cc hc hh n m hhh hn hnN
      hm α t ht X v u ξ

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The fixed composition constant controls every mixed suborder of a common rectangle. -/

theorem exponentialLiftCompositionNormalizedConstant_mono (n r s p q : ℕ)
    (hr : r ≤ p) (hs : s ≤ q) (A : Vec 2 →L[ℝ] ℝ) :
    exponentialLiftCompositionNormalizedConstant n r s A ≤
      exponentialLiftCompositionNormalizedConstant n p q A := by
  have hcount := finiteLiftWordCount_nonneg n
  have hA : 1 ≤ max 1 ‖A‖ := le_max_left _ _
  unfold exponentialLiftCompositionNormalizedConstant exponentialLiftCompositionRawConstant
  gcongr <;> norm_num

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal recurrence source is centered because its ordered positive-lift terms are centered. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftCellSource_component_mean_zero (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hnN : n ≤ N)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (v : ι)
    (hA : Continuous (fun z => liftA Q Cc f hh n t X z)) :
    fieldCellMean (fun z => liftCellSource Q Cc f hh n t X z v) = 0 := by
  let T := fun j (p : ℕ × ℕ) z =>
    liftApply j (Cc p.1 j) (liftMean Q Cc f p.2 (n - j)) t X z v
  have hpH (p : ℕ × ℕ) (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) : p.1 ≤ H := by
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    omega
  have hjN j (hj : j ∈ Finset.Icc 1 (n - 2)) : 1 ≤ j ∧ j ≤ N := by
    have he := Finset.mem_Icc.mp hj
    omega
  have hT j (hj : j ∈ Finset.Icc 1 (n - 2)) p (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      Continuous (T j p) := by
    apply liftApply_component_fast_continuous
    intro m _ α u
    exact ((hc.2.2.2.2.2.1 p.1 (hpH p hp) j m α v u t ht).1.1 X).continuous
  have hmT j (hj : j ∈ Finset.Icc 1 (n - 2)) p (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      fieldCellMean (T j p) = 0 :=
    liftSequence_tested_component_mean_zero Q sX sZ a b N H Cc hc p.1 j (hpH p hp)
      (hjN j hj).1 (hjN j hj).2 _ t ht X v
  have hsum j (hj : j ∈ Finset.Icc 1 (n - 2)) :
      Continuous (fun z => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z) :=
    continuous_finsetSum _ (fun p hp => hT j hj p hp)
  have hcorr : Continuous (fun z => ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z) :=
    continuous_finsetSum _ hsum
  have hmcorr : fieldCellMean (fun z => ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z) = 0 := by
    apply fieldCellMean_finset_sum_zero _ _ hsum
    intro j hj
    exact fieldCellMean_finset_sum_zero _ _ (hT j hj) (hmT j hj)
  have hAc : Continuous (fun z => liftA Q Cc f hh n t X z v) :=
    (continuous_apply v).comp hA
  have hmA := AVRegularity.fieldCellMean_clm
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) hA
  change fieldCellMean (fun z => liftA Q Cc f hh n t X z v) = liftMean Q Cc f hh n t X v at hmA
  simp only [liftCellSource, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Finset.sum_apply]
  change fieldCellMean (fun z => -(liftA Q Cc f hh n t X z v - liftMean Q Cc f hh n t X v) +
    ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z) = 0
  rw [AVRegularity.fieldCellMean_add
      (f := fun z => -(liftA Q Cc f hh n t X z v - liftMean Q Cc f hh n t X v))
      (g := fun z => ∑ j ∈ Finset.Icc 1 (n - 2),
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T j p z)
      (hAc.sub (continuous_const : Continuous (fun _ : Vec 2 => liftMean Q Cc f hh n t X v))).neg hcorr,
    AVRegularity.fieldCellMean_neg, AVRegularity.fieldCellMean_sub
      (f := fun z => liftA Q Cc f hh n t X z v)
      (g := fun _ => liftMean Q Cc f hh n t X v) hAc continuous_const,
    AVRegularity.fieldCellMean_const, hmA, hmcorr]
  simp only [sub_self, neg_zero, add_zero]
end

/-! Every positive lift has zero vector cell mean for arbitrary coarse inputs. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem liftSequence_tested_mean_zero (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    fieldCellMean (fun z => liftApply n (Cc hh n) f t X z) = 0 := by
  have hc := liftApply_fast_continuous n (Cc hh n) f t X
    (fun m _ α v u => ((hseq.2.2.2.2.2.1 hh hhh n m α v u t ht).1.1 X).continuous)
  funext v
  rw [← fieldCellMean_pi_apply _ hc v]
  exact liftSequence_tested_component_mean_zero Q sX sZ a b N H Cc hseq
    hh n hhh hn hnN f t ht X v
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Literal dimension-independent scalar budgets for paired height-zero cross terms. -/

def pairedFirstCrossScalarBudget (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG Cw CGI Bi Bd : ℕ → ℝ) : ℝ :=
  (normalizedCellB1UniformConstant p q A (metricParameterBudget (p + 1) CG)
      (metricParameterBudget q Cw) * Bd n +
    normalizedCellB1UniformConstant p q A (metricParameterBudget (p + 1) CGI) 0 * Bi n) *
    finiteLiftSymbolBudget n A

def pairedSecondCrossScalarBudget (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG CGI Bi Bd : ℕ → ℝ) : ℝ :=
  (normalizedCellB2UniformConstant p q A (metricParameterBudget (p + 1) CG) * Bd n +
    normalizedCellB2UniformConstant p q A (metricParameterBudget (p + 1) CGI) * Bi n) *
    finiteLiftSymbolBudget n A

def pairedUncenteredScalarBudget (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG Cw CGI Bi Bd : ℕ → ℝ) : ℝ :=
  pairedFirstCrossScalarBudget (n - 1) p q A CG Cw CGI Bi Bd +
    if 2 ≤ n then pairedSecondCrossScalarBudget (n - 2) p q A CG CGI Bi Bd else 0

theorem pairedFirstCrossScalarBudget_nonneg (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG Cw CGI Bi Bd : ℕ → ℝ) (hBi : ∀ m, 0 ≤ Bi m) (hBd : ∀ m, 0 ≤ Bd m) :
    0 ≤ pairedFirstCrossScalarBudget n p q A CG Cw CGI Bi Bd := by
  unfold pairedFirstCrossScalarBudget
  apply mul_nonneg _ (finiteLiftSymbolBudget_nonneg n A)
  apply add_nonneg
  · apply mul_nonneg _ (hBd n)
    exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
      normalizedCellB1MixedConstant_nonneg r s A _ _
        (metricParameterBudget_nonneg (p + 1) CG) (metricParameterBudget_nonneg q Cw)
  · apply mul_nonneg _ (hBi n)
    exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
      normalizedCellB1MixedConstant_nonneg r s A _ 0
        (metricParameterBudget_nonneg (p + 1) CGI) le_rfl

theorem pairedSecondCrossScalarBudget_nonneg (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG CGI Bi Bd : ℕ → ℝ) (hBi : ∀ m, 0 ≤ Bi m) (hBd : ∀ m, 0 ≤ Bd m) :
    0 ≤ pairedSecondCrossScalarBudget n p q A CG CGI Bi Bd := by
  unfold pairedSecondCrossScalarBudget
  apply mul_nonneg _ (finiteLiftSymbolBudget_nonneg n A)
  apply add_nonneg
  · apply mul_nonneg _ (hBd n)
    exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
      normalizedCellB2MixedConstant_nonneg r s A _ (metricParameterBudget_nonneg (p + 1) CG)
  · apply mul_nonneg _ (hBi n)
    exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
      normalizedCellB2MixedConstant_nonneg r s A _ (metricParameterBudget_nonneg (p + 1) CGI)

theorem pairedUncenteredScalarBudget_nonneg (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (CG Cw CGI Bi Bd : ℕ → ℝ) (hBi : ∀ m, 0 ≤ Bi m) (hBd : ∀ m, 0 ≤ Bd m) :
    0 ≤ pairedUncenteredScalarBudget n p q A CG Cw CGI Bi Bd := by
  unfold pairedUncenteredScalarBudget
  apply add_nonneg (pairedFirstCrossScalarBudget_nonneg _ _ _ _ _ _ _ _ _ hBi hBd)
  split_ifs
  · exact pairedSecondCrossScalarBudget_nonneg _ _ _ _ _ _ _ _ hBi hBd
  · exact le_rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Positive lift degrees stay centered after summing all source-height compositions. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem liftSequence_graded_apply_mean_zero (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh r : ℕ) (hhh : hh ≤ H) (hr : 1 ≤ r) (hrN : r ≤ N)
    (f : ℕ → ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    fieldCellMean (fun z => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply r (Cc p.1 r) (f p.2) t X z) = 0 := by
  apply fieldCellMean_finset_sum_zero (Finset.HasAntidiagonal.antidiagonal hh)
    (fun (p : ℕ × ℕ) z => liftApply r (Cc p.1 r) (f p.2) t X z)
  · intro p hp
    have hq : p.1 ≤ H := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega
    exact liftApply_fast_continuous r (Cc p.1 r) (f p.2) t X
      (fun m _ α v u => ((hseq.2.2.2.2.2.1 p.1 hq r m α v u t ht).1.1 X).continuous)
  · intro p hp
    have hq : p.1 ≤ H := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega
    exact liftSequence_tested_mean_zero Q sX sZ a b N H Cc hseq
      p.1 r hq hr hrN (f p.2) t ht X

end AVRegularity.CycleComparison.Lift
end
