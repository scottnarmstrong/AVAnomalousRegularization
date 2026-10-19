-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import AVRegularity.CycleComparison.CleanupChain
public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.TailConstructed

/-! The cross-diffusion flux `Φ ↦ -√η ∑_j (G_{kj} ∂_{X_j} Φ + ∂_{X_j}(G_{jk} Φ))` of the constructed
tail raw flux is a finite left-term action whose tested
order exceeds that of `Φ` by one. -/

section
section Generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The cross-diffusion flux in the direction `k`, with a frozen-time metric `G`. -/
def crossFluxField (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2)
    (Φ : Vec 2 → Vec 2 → F) : Vec 2 → Vec 2 → F :=
  fun X z => -Real.sqrt η • ∑ j : Fin 2,
    (G X k j • slowPartial j Φ X z + slowPartial j (fun X' z' => G X' j k • Φ X' z') X z)

/-- The literal finite left terms of the cross-diffusion flux of a finite left-term action. -/
def crossFluxListTerms (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2)
    (l : List (LeftTerm E F)) : List (LeftTerm E F) :=
  ((Finset.univ.toList : List (Fin 2)).flatMap fun j =>
    (leftTermsSlowPartial j l).map (fun c => c.fieldSmul (fun X _ => G X k j)) ++
      leftTermsSlowPartial j (l.map (fun c => c.fieldSmul (fun X _ => G X j k)))).map
    (fun c => c.smul (-Real.sqrt η))

theorem crossFluxListTerms_order (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2)
    (l : List (LeftTerm E F)) (n : ℕ) (hl : ∀ c ∈ l, c.order ≤ n)
    (c : LeftTerm E F) (hc : c ∈ crossFluxListTerms η G k l) : c.order ≤ n + 1 := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨j, _, hdj⟩ := List.mem_flatMap.mp hd
  rcases List.mem_append.mp hdj with h1 | h2
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h1
    exact leftTermsSlowPartial_order j l n hl e he
  · apply leftTermsSlowPartial_order j _ n ?_ d h2
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact hl e' he'

theorem crossFluxListTerms_apply (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2)
    (l : List (LeftTerm E F))
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G X i j))
    (hl : ∀ c ∈ l, IsBoxSmooth 1 0 c.coeff) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    leftTermsApply (crossFluxListTerms η G k l) f = crossFluxField η G k (leftTermsApply l f) := by
  have hmult (j : Fin 2) (d : LeftTerm E F)
      (hd : d ∈ l.map (fun c => c.fieldSmul (fun X _ => G X j k))) : IsBoxSmooth 1 0 d.coeff := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact e.fieldSmul_box _ 1 0 (hl e he) (isBoxSmooth_slow_field 1 0 _ (hG j k))
  funext X z
  have h1 (j : Fin 2) : leftTermsApply ((leftTermsSlowPartial j l).map
      (fun c => c.fieldSmul (fun X _ => G X k j))) f X z =
      G X k j • slowPartial j (leftTermsApply l f) X z := by
    simp only [leftTermsApply_map_fieldSmul, leftTermsSlowPartial_apply j l hl f hf]
  have h2 (j : Fin 2) : leftTermsApply (leftTermsSlowPartial j
      (l.map (fun c => c.fieldSmul (fun X _ => G X j k)))) f X z =
      slowPartial j (fun X' z' => G X' j k • leftTermsApply l f X' z') X z := by
    simp only [leftTermsSlowPartial_apply j _ (hmult j) f hf, leftTermsApply_map_fieldSmul]
  rw [crossFluxListTerms, leftTermsApply_map_smul]
  dsimp only
  rw [leftTermsApply_finset_flatMap]
  simp only [leftTermsApply_append, h1, h2]
  rfl

end Generic

section Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The finite left terms of the `v`-component of the cross flux of the degree-`d` lift `c`. -/
def crossFluxLeftTerms (Q : LiftOperatorData ι h D) (c : LiftCoeff ι h) (d : ℕ) (t : ℝ)
    (k : Fin 2) (v : ι) : List (LeftTerm (∀ i, h i) (h v)) :=
  crossFluxListTerms Q.η (Q.G t) k (liftComponentLeftTerms d c t v)

theorem crossFluxLeftTerms_order (Q : LiftOperatorData ι h D) (c : LiftCoeff ι h)
    (d : ℕ) (t : ℝ) (k : Fin 2) (v : ι) (e : LeftTerm (∀ i, h i) (h v))
    (he : e ∈ crossFluxLeftTerms Q c d t k v) : e.order ≤ d + 1 :=
  crossFluxListTerms_order Q.η (Q.G t) k _ d (liftComponentLeftTerms_order d c t v) e he

/-- The cross terms act as the cross flux of the `v`-component of the lift. -/
theorem crossFluxLeftTerms_apply_field (Q : LiftOperatorData ι h D) (c : LiftCoeff ι h)
    (d : ℕ) (t : ℝ) (k : Fin 2) (v : ι)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j))
    (hc : ∀ m ≤ d, ∀ α : DerivativeWord2 m, ∀ u,
      IsBoxSmooth 1 0 (fun X z => c m α t X z v u))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (crossFluxLeftTerms Q c d t k v) f X z =
      crossFluxField Q.η (Q.G t) k (fun Y y => liftApply d c (fun _ => f) t Y y v) X z := by
  have hl := crossFluxListTerms_apply Q.η (Q.G t) k (liftComponentLeftTerms d c t v) hG
    (liftComponentLeftTerms_box d c t v 1 0 hc) f hf
  have he : leftTermsApply (liftComponentLeftTerms d c t v) f =
      fun Y y => liftApply d c (fun _ => f) t Y y v := by
    funext Y y
    exact liftComponentLeftTerms_apply d c t v f Y y
  rw [crossFluxLeftTerms, hl, he]

/-- The `v`-component of the literal cross flux of a vector field is the cross flux of its
`v`-component. -/
theorem crossFlux_literal_apply (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (hΦ : IsBoxSmooth 1 0 Φ)
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => G X i j)) (X z : Vec 2) (v : ι) :
    (-Real.sqrt η • ∑ j : Fin 2,
        (G X k j • fderiv ℝ (fun X' => Φ X' z) X (basisVec j) +
          fderiv ℝ (fun X' => G X' j k • Φ X' z) X (basisVec j)) : ∀ i, h i) v =
      crossFluxField η G k (fun Y y => Φ Y y v) X z := by
  have hs (j : Fin 2) : (fderiv ℝ (fun X' => Φ X' z) X (basisVec j)) v =
      fderiv ℝ (fun X' => Φ X' z v) X (basisVec j) :=
    (slowPartial_postcomposition (ContinuousLinearMap.proj v) Φ hΦ j X z).symm
  have hd (j : Fin 2) : (fderiv ℝ (fun X' => G X' j k • Φ X' z) X (basisVec j)) v =
      fderiv ℝ (fun X' => G X' j k • Φ X' z v) X (basisVec j) := by
    have hb : IsBoxSmooth 1 0 (fun Y y => G Y j k • Φ Y y) :=
      isBoxSmooth_bilinear (isBoxSmooth_slow_field 1 0 _ (hG j k)) hΦ
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (∀ i, h i) →L[ℝ] (∀ i, h i))
    exact (slowPartial_postcomposition (ContinuousLinearMap.proj v) _ hb j X z).symm
  simp only [Pi.smul_apply, Finset.sum_apply, Pi.add_apply, hs, hd]
  rfl

end Lift
end

/-! The cross flux raises the slow grade by exactly one: one slow derivative falls either on the
field or on the product with a metric entry. On normalized exponential lift tests of degree `d`
the cross flux is graded at degree `d + 1` with a fixed finite-order constant. -/

section
/-- The mixed-jet constant of the cross flux at mixed order `(p, q)`, per metric budget. -/
def crossFluxMixedConstant (p q : ℕ) (M : ℝ) : ℝ :=
  2 * ((2 ^ (p + 2 * q) + 2 ^ ((p + 1) + 2 * q)) * M)

theorem crossFluxMixedConstant_nonneg (p q : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ crossFluxMixedConstant p q M := by
  unfold crossFluxMixedConstant
  positivity

theorem crossFluxMixedConstant_mono {p q r s : ℕ} (hr : r ≤ p) (hs : s ≤ q) (M : ℝ)
    (hM : 0 ≤ M) : crossFluxMixedConstant r s M ≤ crossFluxMixedConstant p q M := by
  unfold crossFluxMixedConstant
  have h1 : (2 : ℝ) ^ (r + 2 * s) ≤ 2 ^ (p + 2 * q) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ ((r + 1) + 2 * s) ≤ 2 ^ ((p + 1) + 2 * q) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (add_le_add h1 h2) hM)
    (by norm_num)

/-- The mixed-jet constant of the cross flux on a normalized exponential test. -/
def normalizedCrossFluxMixedConstant (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M C : ℝ) : ℝ :=
  (2 ^ (p + 2 * q) * max 1 ‖A‖ ^ p) *
    (crossFluxMixedConstant p q M * (2 ^ ((p + 1) + 2 * q) * max 1 ‖A‖ ^ (p + 1) * C))

theorem normalizedCrossFluxMixedConstant_nonneg (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M C : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) : 0 ≤ normalizedCrossFluxMixedConstant p q A M C := by
  unfold normalizedCrossFluxMixedConstant
  have := crossFluxMixedConstant_nonneg p q M hM
  positivity

theorem normalizedCrossFluxMixedConstant_mono {p q r s : ℕ} (hr : r ≤ p) (hs : s ≤ q)
    (A : Vec 2 →L[ℝ] ℝ) (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    normalizedCrossFluxMixedConstant r s A M C ≤ normalizedCrossFluxMixedConstant p q A M C := by
  unfold normalizedCrossFluxMixedConstant
  have hA : (1 : ℝ) ≤ max 1 ‖A‖ := le_max_left _ _
  have h1 : (2 : ℝ) ^ (r + 2 * s) ≤ 2 ^ (p + 2 * q) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ ((r + 1) + 2 * s) ≤ 2 ^ ((p + 1) + 2 * q) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : max 1 ‖A‖ ^ r ≤ max 1 ‖A‖ ^ p := pow_le_pow_right₀ hA hr
  have h4 : max 1 ‖A‖ ^ (r + 1) ≤ max 1 ‖A‖ ^ (p + 1) := pow_le_pow_right₀ hA (by omega)
  have h5 := crossFluxMixedConstant_mono hr hs M hM
  have h0 := crossFluxMixedConstant_nonneg r s M hM
  have h0' := crossFluxMixedConstant_nonneg p q M hM
  have hinner : 2 ^ ((r + 1) + 2 * s) * max 1 ‖A‖ ^ (r + 1) * C ≤
      2 ^ ((p + 1) + 2 * q) * max 1 ‖A‖ ^ (p + 1) * C :=
    mul_le_mul_of_nonneg_right (mul_le_mul h2 h4 (by positivity) (by positivity)) hC
  exact mul_le_mul (mul_le_mul h1 h3 (by positivity) (by positivity))
    (mul_le_mul h5 hinner (by positivity) h0') (by positivity) (by positivity)

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem crossFluxField_box (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2)
    (f : Vec 2 → Vec 2 → E) (p q : ℕ) (hf : IsBoxSmooth (p + 1) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G Y i j)) :
    IsBoxSmooth p q (crossFluxField η G k f) := by
  let T : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hS (j : Fin 2) : IsBoxSmooth p q (fun Y y => G Y k j • slowPartial j f Y y +
      slowPartial j (fun Z w => G Z j k • f Z w) Y y) := by
    have h1 : IsBoxSmooth p q (fun Y y => G Y k j • slowPartial j f Y y) :=
      isBoxSmooth_bilinear ((hG k j).mono (by omega) le_rfl) (hf.slowPartial j) T
    have h2 : IsBoxSmooth (p + 1) q (fun Y y => G Y j k • f Y y) :=
      isBoxSmooth_bilinear (hG j k) hf T
    exact h1.add (h2.slowPartial j)
  exact (IsBoxSmooth.sum Finset.univ fun j _ => hS j).const_smul (-Real.sqrt η)

/-- The cross flux raises the slow grade of a graded field by one. -/
theorem crossFluxField_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M C : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth (p + 1) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G Y i j)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G Y i j) z) X‖ ≤ M * lam ^ a)
    (hbf : ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (crossFluxField η G k f Y) z) X‖ ≤
      (crossFluxMixedConstant p q M * C) * lam ^ ((δ + 1) + p) := by
  let T : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hfirst (j : Fin 2) : IsBoxSmooth p q (fun Y y => G Y k j • slowPartial j f Y y) :=
    isBoxSmooth_bilinear ((hG k j).mono (by omega) le_rfl) (hf.slowPartial j) T
  have hprod (j : Fin 2) : IsBoxSmooth (p + 1) q (fun Y y => G Y j k • f Y y) :=
    isBoxSmooth_bilinear (hG j k) hf T
  have hbfirst (j : Fin 2) : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => G Y k j • slowPartial j f Y y) z) X‖ ≤
      (2 ^ (p + 2 * q) * M * C) * lam ^ ((δ + 1) + p) := by
    have hbs := slowPartial_mixed_grading_at_slow_point p q δ lam C f hf X hbf j
    have hh := norm_mixed_bilinear_uniform_graded_le_at_slow_point p q 0 (δ + 1)
      lam M C hlam hM hC T ContinuousLinearMap.opNorm_lsmul_le (fun Y (_ : Vec 2) => G Y k j)
      (slowPartial j f) ((hG k j).mono (by omega) le_rfl) (hf.slowPartial j) X
      (fun a ha b hb y => by simpa only [Nat.zero_add] using hbG k j a (by omega) b hb y) hbs
    simpa only [T, Nat.zero_add] using! hh p le_rfl q le_rfl z
  have hbsecond (j : Fin 2) : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (slowPartial j (fun Z w => G Z j k • f Z w) Y) z) X‖ ≤
      (2 ^ ((p + 1) + 2 * q) * M * C) * lam ^ ((δ + 1) + p) := by
    have hbprod := norm_mixed_bilinear_uniform_graded_le_at_slow_point (p + 1) q 0 δ
      lam M C hlam hM hC T ContinuousLinearMap.opNorm_lsmul_le (fun Y (_ : Vec 2) => G Y j k) f
      (hG j k) hf X (fun a ha b hb y => by simpa only [Nat.zero_add] using hbG j k a ha b hb y)
      hbf
    exact slowPartial_mixed_grading_at_slow_point p q δ lam
      (2 ^ ((p + 1) + 2 * q) * M * C) (fun Y y => G Y j k • f Y y) (hprod j) X
      (by simpa only [T, Nat.zero_add] using! hbprod) j p le_rfl q le_rfl z
  have hS (j : Fin 2) : IsBoxSmooth p q (fun Y y => G Y k j • slowPartial j f Y y +
      slowPartial j (fun Z w => G Z j k • f Z w) Y y) := (hfirst j).add ((hprod j).slowPartial j)
  have hSb (j : Fin 2) : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => G Y k j • slowPartial j f Y y +
        slowPartial j (fun Z w => G Z j k • f Z w) Y y) z) X‖ ≤
      ((2 ^ (p + 2 * q) + 2 ^ ((p + 1) + 2 * q)) * M * C) * lam ^ ((δ + 1) + p) := by
    apply (norm_mixed_jet_add_le (hfirst j) ((hprod j).slowPartial j) X z).trans
    calc
      _ ≤ (2 ^ (p + 2 * q) * M * C) * lam ^ ((δ + 1) + p) +
          (2 ^ ((p + 1) + 2 * q) * M * C) * lam ^ ((δ + 1) + p) :=
        add_le_add (hbfirst j) (hbsecond j)
      _ = _ := by ring
  have hsum : IsBoxSmooth p q (fun Y y => ∑ j : Fin 2, (G Y k j • slowPartial j f Y y +
      slowPartial j (fun Z w => G Z j k • f Z w) Y y)) :=
    IsBoxSmooth.sum Finset.univ fun j _ => hS j
  have he : crossFluxField η G k f = fun Y y => -Real.sqrt η • ∑ j : Fin 2,
      (G Y k j • slowPartial j f Y y + slowPartial j (fun Z w => G Z j k • f Z w) Y y) := rfl
  rw [he, norm_mixed_jet_const_smul hsum, abs_neg, abs_of_nonneg (Real.sqrt_nonneg η)]
  have hsqrt : Real.sqrt η ≤ 1 := by simpa using Real.sqrt_le_sqrt hη
  apply (mul_le_of_le_one_left (norm_nonneg _) hsqrt).trans
  apply (norm_mixed_jet_finset_sum_le Finset.univ p q _ (fun j _ => hS j) X z).trans
  calc
    _ ≤ ∑ _j : Fin 2, ((2 ^ (p + 2 * q) + 2 ^ ((p + 1) + 2 * q)) * M * C) *
        lam ^ ((δ + 1) + p) := Finset.sum_le_sum fun j _ => hSb j
    _ = (crossFluxMixedConstant p q M * C) * lam ^ ((δ + 1) + p) := by
      rw [Fin.sum_univ_two]
      unfold crossFluxMixedConstant
      ring

/-- The cross flux on a normalized exponential multiple keeps the single grading power. -/
theorem normalizedCrossFlux_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M C : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth (p + 1) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G Y i j)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G Y i j) z) X‖ ≤ M * lam ^ a)
    (hbf : ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • crossFluxField η G k
        (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y) z) X‖ ≤
      normalizedCrossFluxMixedConstant p q A M C * lam ^ ((δ + 1) + p) := by
  have hCexp : 0 ≤ 2 ^ ((p + 1) + 2 * q) * max 1 ‖A‖ ^ (p + 1) * C := by positivity
  have hΦ : IsBoxSmooth (p + 1) q (fun Y y => Real.exp ((lam • A) Y) • f Y y) :=
    isBoxSmooth_bilinear
      (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hf
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hΦb := norm_mixed_exponential_smul_graded_le (p + 1) q δ A lam C hlam hC f hf X hbf
  have hb : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (crossFluxField η G k (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y) y) X‖ ≤
        (Real.exp ((lam • A) X) * (crossFluxMixedConstant p q M *
          (2 ^ ((p + 1) + 2 * q) * max 1 ‖A‖ ^ (p + 1) * C))) * lam ^ ((δ + 1) + a) := by
    intro a ha b hb y
    have hE : 0 ≤ Real.exp ((lam • A) X) *
        (2 ^ ((p + 1) + 2 * q) * max 1 ‖A‖ ^ (p + 1) * C) := by positivity
    have hh := crossFluxField_mixed_grading_at_slow_point a b δ η lam M
      (Real.exp ((lam • A) X) * (2 ^ ((p + 1) + 2 * q) * max 1 ‖A‖ ^ (p + 1) * C))
      hη hlam hM hE G k _ (hΦ.mono (by omega) hb)
      (fun i j => (hG i j).mono (by omega) hb) X
      (fun i j a' ha' b' hb' y' => hbG i j a' (by omega) b' (hb'.trans hb) y')
      (fun a' ha' b' hb' y' => hΦb a' b' (by omega) (hb'.trans hb) y') y
    apply hh.trans
    have hmono := crossFluxMixedConstant_mono ha hb M hM
    calc
      _ ≤ (crossFluxMixedConstant p q M * (Real.exp ((lam • A) X) *
          (2 ^ ((p + 1) + 2 * q) * max 1 ‖A‖ ^ (p + 1) * C))) * lam ^ ((δ + 1) + a) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hE) (pow_nonneg hlam _)
      _ = _ := by ring
  have hn := norm_mixed_exponential_normalized_le p q (δ + 1) A lam
    (crossFluxMixedConstant p q M * (2 ^ ((p + 1) + 2 * q) * max 1 ‖A‖ ^ (p + 1) * C))
    hlam (mul_nonneg (crossFluxMixedConstant_nonneg p q M hM) hCexp)
    (crossFluxField η G k (fun Z w => Real.exp ((lam • A) Z) • f Z w))
    (crossFluxField_box η G k _ p q hΦ hG) X hb z
  apply hn.trans_eq
  rfl

/-- Every reserved suborder of the normalized cross flux has the common constant. -/
theorem normalizedCrossFlux_uniform_mixed_grading (p q δ : ℕ) (η lam M C : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth (p + 1) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G Y i j)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G Y i j) z) X‖ ≤ M * lam ^ a)
    (hbf : ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • crossFluxField η G k
        (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y) z) X‖ ≤
      normalizedCrossFluxMixedConstant p q A M C * lam ^ ((δ + 1) + r) := by
  have hh := normalizedCrossFlux_mixed_grading_at_slow_point r s δ η lam M C hη hlam hM hC
    A G k f (hf.mono (by omega) hs) (fun i j => (hG i j).mono (by omega) hs) X
    (fun i j a ha b hb y => hbG i j a (by omega) b (hb.trans hs) y)
    (fun a ha b hb y => hbf a (by omega) b (hb.trans hs) y) z
  exact hh.trans (mul_le_mul_of_nonneg_right
    (normalizedCrossFluxMixedConstant_mono hr hs A M C hM hC) (pow_nonneg hlam _))

end Generic

section Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The cross flux of a degree-`d` lift test is graded at degree `d + 1`. -/
theorem normalizedCrossFlux_lift_test_grading (d p q : ℕ) (η lam M B : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (A : Vec 2 →L[ℝ] ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2) (t : ℝ)
    (c : LiftCoeff ι h) (v u : ι) (ξ : h u)
    (hc : ∀ m ≤ d, ∀ α : DerivativeWord2 m,
      IsBoxSmooth (p + 1) q (fun X z => c m α t X z v u))
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G Y i j)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G Y i j) z) X‖ ≤ M * lam ^ a)
    (hbc : ∀ m ≤ d, ∀ α : DerivativeWord2 m, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => c m α t Y y v u) z) X‖ ≤ B * lam ^ (d - m + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • crossFluxField η G k
        (fun Z w => liftApply d c (fun _ Z' => Real.exp ((lam • A) Z') • Pi.single u ξ)
          t Z w v) Y y) z) X‖ ≤
      (normalizedCrossFluxMixedConstant p q A M 1 * (finiteLiftSymbolBudget d A * B * ‖ξ‖)) *
        lam ^ ((d + 1) + r) := by
  let F := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply d c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t Y y v
  have hF : IsBoxSmooth (p + 1) q F :=
    normalized_lift_test_box_reserve d (p + 1) q c lam A t v u ξ hc
  have hFb : ∀ a ≤ p + 1, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (F Y) y) X‖ ≤
        (finiteLiftSymbolBudget d A * B * ‖ξ‖) * lam ^ (d + a) := by
    intro a ha b hb y
    have hh := normalized_lift_test_mixed_grading d a b c lam B hlam A t v u ξ
      (fun m hm α => (hc m hm α).mono ha hb) X y (fun m hm α => hbc m hm α a ha b hb y)
    calc
      _ ≤ (finiteLiftSymbolBudget d A * B) * lam ^ (d + a) * ‖ξ‖ := hh
      _ = _ := by ring
  have he : (fun Z w => liftApply d c (fun _ Z' => Real.exp ((lam • A) Z') • Pi.single u ξ)
      t Z w v) = fun Z w => Real.exp ((lam • A) Z) • F Z w := by
    funext Z w
    dsimp only [F]
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  rw [he]
  have hC : 0 ≤ finiteLiftSymbolBudget d A * B * ‖ξ‖ := by
    have := finiteLiftSymbolBudget_nonneg d A
    positivity
  have hh := normalizedCrossFlux_uniform_mixed_grading p q d η lam M
    (finiteLiftSymbolBudget d A * B * ‖ξ‖) hη hlam hM hC A G k F hF hG X hbG hFb r s hr hs z
  apply hh.trans_eq
  unfold normalizedCrossFluxMixedConstant
  ring

end Lift
end

end AVRegularity.CycleComparison.TailConstructed
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.TailConstructed

/-! Every lift coefficient, at every degree and every grade up to `H`, carries the ambient
coefficient data with one uniform scalar budget. Below the cutoff the data come from the ambient
recurrence at the tail reserve `K + N + D + 2`; above it the coefficients vanish. -/

section
/-- A uniform scalar budget for every lift coefficient of grade at most `H`. -/
def tailRawCoefficientBudget (K k L D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  ∑ hh ∈ Finset.range (H + 1), ∑ d ∈ Finset.range (N + 1),
    ambientCoefficientScalarBudget (K + N + D + 2) (max k (L + 2)) D H (N + D) N hh d CG Cw Cj

theorem tailRawCoefficientBudget_nonneg (K k L D H N : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) : 0 ≤ tailRawCoefficientBudget K k L D H N CG Cw Cj :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _

theorem ambientCoefficientScalarBudget_le_tailRawCoefficientBudget (K k L D H N : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (hh d : ℕ) (hhh : hh ≤ H) (hd : d ≤ N) :
    ambientCoefficientScalarBudget (K + N + D + 2) (max k (L + 2)) D H (N + D) N hh d CG Cw Cj ≤
      tailRawCoefficientBudget K k L D H N CG Cw Cj := by
  unfold tailRawCoefficientBudget
  have hin : ambientCoefficientScalarBudget (K + N + D + 2) (max k (L + 2)) D H (N + D) N
      hh d CG Cw Cj ≤ ∑ d' ∈ Finset.range (N + 1), ambientCoefficientScalarBudget
        (K + N + D + 2) (max k (L + 2)) D H (N + D) N hh d' CG Cw Cj :=
    Finset.single_le_sum (f := fun d' => ambientCoefficientScalarBudget
        (K + N + D + 2) (max k (L + 2)) D H (N + D) N hh d' CG Cw Cj)
      (fun _ _ => ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _)
      (Finset.mem_range.mpr (by omega))
  exact hin.trans (Finset.single_le_sum (f := fun hh' => ∑ d' ∈ Finset.range (N + 1),
      ambientCoefficientScalarBudget (K + N + D + 2) (max k (L + 2)) D H (N + D) N
        hh' d' CG Cw Cj)
    (fun _ _ => Finset.sum_nonneg fun _ _ =>
      ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _)
    (Finset.mem_range.mpr (by omega)))

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The ambient coefficient data of every lift coefficient, with the uniform budget. -/
theorem setting_tailRaw_coefficient_data
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (p q : ℕ) (hp : p ≤ K + N + 2 * D + 2) (hq : q ≤ max k (L + 2) + 2 * D)
    (hh : ℕ) (hhh : hh ≤ H) (d : ℕ) :
    AmbientLiftCoefficientData par a b P.window lam d p q (Cc hh d)
      (fun v u => tailRawCoefficientBudget K k L D H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hpow := finiteMatrixPower_nonneg _
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh
  by_cases hd : d ≤ N
  · have data := (setting_ambient_scalar_power_recurrence_data P sX sZ hsZ Cc hseq
      (K + N + D + 2) (by have := setting_tail_ambient_supported P; omega)
      hh hhh d (by omega)).coefficient
    have hfast : q ≤ ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh d := by
      have hr : D ≤ N + D - d := by omega
      have h2 := Nat.mul_le_mul_left 2 hr
      unfold ambientDegreeFastReserve
      omega
    have hslow : p ≤ ambientDegreeSlowReserve (K + N + D + 2) (N + D) d := by
      unfold ambientDegreeSlowReserve
      omega
    refine (data.mono hslow hfast).enlarge hlam ?_
    intro v u
    exact mul_le_mul_of_nonneg_right
      (ambientCoefficientScalarBudget_le_tailRawCoefficientBudget K k L D H N CG Cw Cj
        hh d hhh hd) (hpow v u)
  · have he : Cc hh d = 0 := by
      funext m α t X z v u
      exact hseq.2.2.1 hh hhh d (by omega) m α t X z v u
    rw [he]
    refine (ambient_zero_coefficient_data par a b P.window lam d p q).enlarge hlam ?_
    intro v u
    exact mul_nonneg (tailRawCoefficientBudget_nonneg K k L D H N CG Cw Cj) (hpow v u)

include P in
/-- Every coefficient of every lift is box smooth through the tail reserves on the window. -/
theorem setting_tailRaw_coefficient_box
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (p q : ℕ) (hp : p ≤ K + N + 2 * D + 2) (hq : q ≤ max k (L + 2) + 2 * D)
    (hh : ℕ) (hhh : hh ≤ H) (d m : ℕ) (α : DerivativeWord2 m) (v u : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (fun X z => Cc hh d m α t X z v u) := by
  by_cases hm : m ≤ d
  · exact (setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq p q hp hq hh hhh d).box
      m hm α v u t ht
  · have he : (fun X z => Cc hh d m α t X z v u) = fun _ _ => 0 := by
      funext X z
      exact hseq.2.2.2.1 hh hhh d m (by omega) α t X z v u
    rw [he]
    exact IsBoxSmooth.zero
end

/-! The raw flux of the constructed tail presentation as a
symmetric coefficient array: the cross flux of the degree-`n-1` lift minus, at positive grade, the
degree-`n` source flux of the preceding grade. Its action is the literal raw flux at every positive
degree, including the tail degrees above the lift cutoff `N`. -/

section
section Terms
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The finite left terms of the `v`-component of the raw flux. -/
def rawFluxLeftTerms (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (t : ℝ) (k : Fin 2) (v : ι) : List (LeftTerm (∀ i, h i) (h v)) :=
  crossFluxLeftTerms Q (Cc hh (n - 1)) (n - 1) t k v ++
    (if hh = 0 then [] else
      (sourceFluxConvolutionLeftTerms Q.edge Q.η t n (Cc (hh - 1)) k v).map
        (fun c => c.smul (-1)))

theorem rawFluxLeftTerms_order (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (k : Fin 2) (v : ι) (e : LeftTerm (∀ i, h i) (h v))
    (he : e ∈ rawFluxLeftTerms Q Cc hh n t k v) : e.order ≤ n := by
  rcases List.mem_append.mp he with hc | hs
  · have := crossFluxLeftTerms_order Q (Cc hh (n - 1)) (n - 1) t k v e hc
    omega
  · by_cases hh0 : hh = 0
    · rw [ite_eq_left hh0] at hs
      simp only [List.not_mem_nil] at hs
    · rw [ite_eq_right hh0] at hs
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hs
      exact sourceFluxConvolutionLeftTerms_order Q.edge Q.η t n (Cc (hh - 1)) k v d hd

/-- The `v`-component of the raw flux, split into the cross flux of the `v`-component of the
degree-`n-1` lift and the source part. -/
theorem constructedLiftTailRawFlux_apply (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (X z : Vec 2) (k : Fin 2) (v : ι)
    (hΦ : IsBoxSmooth 1 0 (liftApply (n - 1) (Cc hh (n - 1)) a t))
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j)) :
    constructedLiftTailRawFlux Q Cc N hh n a t X z k v =
      crossFluxField Q.η (Q.G t) k (fun Y y => liftApply (n - 1) (Cc hh (n - 1)) a t Y y v)
          X z -
        (if hh = 0 then 0 else
          sourceFluxCoeff Q.edge Q.η n t (fun ε => liftPolyField Cc N ε (hh - 1) a t) k X z v) := by
  have hpoly : (fun (ε : ℝ) (X' z' : Vec 2) => ∑ d ∈ Finset.range (N + 1),
      ε ^ d • liftApply d (Cc (hh - 1) d) a t X' z') =
      fun ε => liftPolyField Cc N ε (hh - 1) a t := rfl
  rw [constructedLiftTailRawFlux, Pi.sub_apply,
    crossFlux_literal_apply Q.η (Q.G t) k _ hΦ hG X z v, hpoly]
  simp only [ite_apply, Pi.zero_apply]

end Terms

section Coefficient
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem leftTermsSymmetricCoefficient_eq_zero_of_lt (l : List (LeftTerm E F)) (n : ℕ)
    (hl : ∀ c ∈ l, c.order ≤ n) (m : ℕ) (hm : n < m) (α : DerivativeWord2 m) (X z : Vec 2) :
    leftTermsSymmetricCoefficient l m α X z = 0 := by
  have hβ (β : DerivativeWord2 m) : leftTermsCoefficient l m β X z = 0 := by
    change (l.map (fun c => c.coeffAt m β X z)).sum = 0
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have hne : c.order ≠ m := by have := hl c hc; omega
    rw [c.coeffAt_ne_order m β hne]
  simp only [leftTermsSymmetricCoefficient, wordSymmetrize, hβ, Finset.sum_const_zero, smul_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The symmetric coefficient array of the raw flux in the direction `k`. -/
def rawFluxCoefficient (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (k : Fin 2) : LiftCoeff ι h :=
  fun m α t X z v u =>
    leftTermsBlockCoefficient (fun w => rawFluxLeftTerms Q Cc hh n t k w) m α t X z v u

theorem rawFluxCoefficient_perm (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (k : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    rawFluxCoefficient Q Cc hh n k m (α ∘ σ) = rawFluxCoefficient Q Cc hh n k m α := by
  funext t X z v u
  exact congrFun (congrFun (congrFun (congrFun (congrFun
    (leftTermsBlockCoefficient_perm (fun w => rawFluxLeftTerms Q Cc hh n t k w)
      m α σ) t) X) z) v) u

/-- The raw-flux array has no coefficient above its cell degree. -/
theorem rawFluxCoefficient_above_order (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : 1 ≤ n) (k : Fin 2)
    (m : ℕ) (hm : n < m) (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    rawFluxCoefficient Q Cc hh n k m α t X z v u = 0 := by
  change (leftTermsSymmetricCoefficient (rawFluxLeftTerms Q Cc hh n t k v) m α X z).comp
    (ContinuousLinearMap.single ℝ h u) = 0
  rw [leftTermsSymmetricCoefficient_eq_zero_of_lt _ n
    (rawFluxLeftTerms_order Q Cc hh n hn t k v) m hm α X z, ContinuousLinearMap.zero_comp]

end Coefficient

section Setting
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- Every source predecessor has the reserve of the full source-flux differentiation. -/
theorem setting_tailRaw_sourceFlux_reserve
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j, ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j) (fun X z => Cc hh (n - j) m α t X z u u') := by
  intro j hj m _ α u u'
  exact setting_tailRaw_coefficient_box P sX sZ hsZ Cc hseq j ((D - 1) - j)
    (by omega) (by omega) hh hhh (n - j) m α u u' t ht

include P in
/-- The full source-flux left terms act at every degree, including the tail degrees. -/
theorem setting_sourceFlux_leftTerms_apply_all
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (_hh0 : hh ≠ 0) (hhh : hh ≤ H) (n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (sourceFluxConvolutionLeftTerms Q.edge Q.η t n (Cc (hh - 1)) k₀ v) f X z =
      sourceFluxCoeff Q.edge Q.η n t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v := by
  have hc := setting_tailRaw_sourceFlux_reserve P sX sZ hsZ Cc hseq (hh - 1) (by omega) n t ht
  rw [sourceFluxConvolutionLeftTerms_apply Q.edge Q.η t n (Cc (hh - 1)) k₀ v hc f hf X z,
    setting_sourceFlux_lift_convolution P sX sZ hsZ Cc hseq (hh - 1) (by omega)
      n k₀ f hf t ht X z]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ min (D - 1) n := by have h := Finset.mem_range.mp hj; omega
  have hbox := liftApply_box_reserve (n - j) j ((D - 1) - j) (Cc (hh - 1) (n - j))
    (fun _ => f) t (hf.of_le (by simp)) (hc j hj')
  exact (congrFun (congrFun (sourceFluxCoefficientArray_component_eq Q.edge Q.η t _
    k₀ j hbox v) X) z).symm

include P in
/-- At positive grade the source part of the raw flux is the sum of its word-length terms. -/
theorem setting_sourceFluxCoeff_component_sum
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hh0 : hh ≠ 0) (hhh : hh ≤ H) (n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    sourceFluxCoeff Q.edge Q.η n t
        (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) k₀ X z v =
      ∑ j ∈ Finset.range (min (D - 1) n + 1), sourceFluxComponentCoefficient Q.edge Q.η t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => f) t) k₀ j v X z := by
  rw [← setting_sourceFlux_leftTerms_apply_all P sX sZ hsZ Cc hseq hh hh0 hhh n f hf
    k₀ t ht X z v]
  exact sourceFluxConvolutionLeftTerms_apply Q.edge Q.η t n (Cc (hh - 1)) k₀ v
    (setting_tailRaw_sourceFlux_reserve P sX sZ hsZ Cc hseq (hh - 1) (by omega) n t ht)
    f hf X z

include P in
/-- The literal raw-flux left terms act as the `v`-component of the raw flux. -/
theorem setting_rawFlux_leftTerms_apply
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (k₀ : Fin 2)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (rawFluxLeftTerms Q Cc hh n t k₀ v) f X z =
      constructedLiftTailRawFlux Q Cc N hh n (fun _ => f) t X z k₀ v := by
  have hG := setting_metric_contDiff_one P t ht
  have hcross := crossFluxLeftTerms_apply_field Q (Cc hh (n - 1)) (n - 1) t k₀ v hG
    (fun m _ α u => setting_tailRaw_coefficient_box P sX sZ hsZ Cc hseq 1 0
      (by omega) (by omega) hh hhh (n - 1) m α v u t ht) f hf X z
  have hΦ : IsBoxSmooth 1 0 (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => f) t) :=
    liftApply_box_reserve (n - 1) 1 0 (Cc hh (n - 1)) (fun _ => f) t (hf.of_le (by simp))
      (fun m _ α v' u => setting_tailRaw_coefficient_box P sX sZ hsZ Cc hseq 1 0
        (by omega) (by omega) hh hhh (n - 1) m α v' u t ht)
  rw [constructedLiftTailRawFlux_apply Q Cc N hh n _ t X z k₀ v hΦ hG, rawFluxLeftTerms,
    leftTermsApply_append]
  dsimp only
  rw [hcross]
  by_cases hh0 : hh = 0
  · rw [ite_eq_left hh0, ite_eq_left hh0, leftTermsApply_nil]
    simp only [add_zero, sub_zero]
  · rw [ite_eq_right hh0, ite_eq_right hh0, leftTermsApply_map_smul]
    dsimp only
    rw [setting_sourceFlux_leftTerms_apply_all P sX sZ hsZ Cc hseq hh hh0 hhh n f hf
      k₀ t ht X z v]
    simp only [neg_one_smul, sub_eq_add_neg]

include P in
/-- The raw-flux array acts as the raw flux under every lift cutoff at least its degree. -/
theorem setting_rawFluxCoefficient_action_of_le
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (R : ℕ) (hR : n ≤ R) (k₀ : Fin 2)
    (a₀ : Vec 2 → ∀ i, h i) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply R (rawFluxCoefficient Q Cc hh n k₀) (fun _ => a₀) t X z =
      constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z k₀ := by
  funext v
  have he := liftApply_congr_at_time R (rawFluxCoefficient Q Cc hh n k₀)
    (leftTermsBlockCoefficient (fun w => rawFluxLeftTerms Q Cc hh n t k₀ w)) (fun _ => a₀) t
    (fun _ _ _ _ _ _ => rfl)
  have hv := congrArg (fun g : Vec 2 → Vec 2 → ∀ i, h i => g X z v) he
  exact hv.trans ((leftTermsBlockCoefficient_apply
    (fun w => rawFluxLeftTerms Q Cc hh n t k₀ w) R
    (fun w c hc => (rawFluxLeftTerms_order Q Cc hh n hn t k₀ w c hc).trans hR)
    a₀ ha₀ t X z v).trans
    (setting_rawFlux_leftTerms_apply P sX sZ hsZ Cc hseq hh hhh n k₀ a₀ ha₀ t ht X z v))

include P in
/-- The raw-flux array acts as the raw flux under the global tail cutoff `2N+D`. -/
theorem setting_rawFluxCoefficient_action
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D) (k₀ : Fin 2)
    (a₀ : Vec 2 → ∀ i, h i) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply (2 * N + D) (rawFluxCoefficient Q Cc hh n k₀) (fun _ => a₀) t X z =
      constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z k₀ :=
  setting_rawFluxCoefficient_action_of_le P sX sZ hsZ Cc hseq hh hhh n hn (2 * N + D) hnR
    k₀ a₀ ha₀ t ht X z

include P in
/-- The raw-flux array acts as the raw flux under its own cell degree. -/
theorem setting_rawFluxCoefficient_degree_action
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (k₀ : Fin 2)
    (a₀ : Vec 2 → ∀ i, h i) (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply n (rawFluxCoefficient Q Cc hh n k₀) (fun _ => a₀) t X z =
      constructedLiftTailRawFlux Q Cc N hh n (fun _ => a₀) t X z k₀ :=
  setting_rawFluxCoefficient_action_of_le P sX sZ hsZ Cc hseq hh hhh n hn n le_rfl
    k₀ a₀ ha₀ t ht X z

include P in
/-- The normalized exponential test field of the raw-flux array is the normalized raw flux. -/
theorem setting_rawFluxCoefficient_normalized_test_eq
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (k₀ : Fin 2)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    normalizedLiftTestField (rawFluxCoefficient Q Cc hh n k₀) n A u v ξ t X z =
      (Real.exp (A X))⁻¹ • constructedLiftTailRawFlux Q Cc N hh n
        (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z k₀ v := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun Y => Real.exp (A Y) • (Pi.single u ξ : ∀ i, h i)) :=
    (Real.contDiff_exp.comp A.contDiff).smul contDiff_const
  have he := setting_rawFluxCoefficient_degree_action P sX sZ hsZ Cc hseq hh hhh n hn k₀
    _ hf t ht X z
  exact congrArg (fun y : ∀ i, h i => (Real.exp (A X))⁻¹ • y v) he

end Setting
end

/-! The raw-flux array has no order-zero coefficient on the window at the degrees `n ≥ 2`,
provided the positive lifts annihilate constants (the first assertion of `cycle_lift_structure`,
taken here as a plain hypothesis on `Cc`). On a constant coarse field the cross part vanishes
because the degree-`n-1` lift does, and the source part vanishes because the source-flux
polynomial is then constant and every source word has positive length. -/

section
section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_const_ite {j : ℕ} (β : DerivativeWord2 j) (c0 : E) :
    orderedDerivative β (fun _ : Vec 2 => c0) = fun _ => if j = 0 then c0 else 0 := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    funext x
    simp [orderedDerivative]
  · rw [orderedDerivative_const β c0 hj]
    funext x
    simp [hj.ne']

theorem crossFluxField_zero (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2) :
    crossFluxField η G k (fun _ _ => (0 : E)) = fun _ _ => 0 := by
  funext X z
  simp [crossFluxField, slowPartial]

end Generic

section Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- An array whose action annihilates every constant field has no order-zero coefficient. -/
theorem liftCoeff_zero_of_const (c : LiftCoeff ι h) (n : ℕ) (t : ℝ) (X z : Vec 2)
    (hc : ∀ c0 : ∀ i, h i, liftApply n c (fun _ _ => c0) t X z = 0) (α : DerivativeWord2 0)
    (v u : ι) : c 0 α t X z v u = 0 := by
  classical
  ext w
  have h1 := congrFun (hc (Pi.single u w)) v
  simp only [liftApply, Pi.zero_apply] at h1
  have hm0 : ∀ m ∈ Finset.range (n + 1), m ≠ 0 → ∑ α' : DerivativeWord2 m, ∑ u' : ι,
      c m α' t X z v u'
        (orderedDerivative α' (fun _ : Vec 2 => (Pi.single u w : ∀ i, h i)) X u') = 0 := by
    intro m _ hm
    refine Finset.sum_eq_zero fun α' _ => Finset.sum_eq_zero fun u' _ => ?_
    simp [orderedDerivative_const_ite, hm]
  rw [Finset.sum_eq_single 0 hm0
    (fun h0 => absurd (Finset.mem_range.2 (Nat.succ_pos n)) h0)] at h1
  have hα : ∀ α' ∈ (Finset.univ : Finset (DerivativeWord2 0)), α' ≠ α → ∑ u' : ι,
      c 0 α' t X z v u'
        (orderedDerivative α' (fun _ : Vec 2 => (Pi.single u w : ∀ i, h i)) X u') = 0 :=
    fun α' _ hα' => absurd (funext fun i => i.elim0) hα'
  rw [Finset.sum_eq_single α hα (fun h0 => absurd (Finset.mem_univ _) h0)] at h1
  rw [Finset.sum_eq_single u] at h1
  · simpa [orderedDerivative_const_ite] using h1
  · intro u' _ hu'
    simp [orderedDerivative_const_ite, Pi.single_eq_of_ne hu']
  · simp

end Lift

section Setting
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **No order-zero coefficient.** If the positive lifts annihilate constants on the window, the
raw-flux array has no order-zero coefficient there, at every degree `n ≥ 2`. -/
theorem setting_rawFluxCoefficient_order_zero
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hconst : ∀ c0 : ∀ i, h i, ∀ hh', hh' ≤ H → ∀ t ∈ Set.Icc a b, ∀ X z,
      ∀ d, 1 ≤ d → d ≤ N → liftApply d (Cc hh' d) (fun _ _ => c0) t X z = 0)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (k₀ : Fin 2)
    (α : DerivativeWord2 0) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v u : ι) :
    rawFluxCoefficient Q Cc hh n k₀ 0 α t X z v u = 0 := by
  apply liftCoeff_zero_of_const (rawFluxCoefficient Q Cc hh n k₀) n t X z _ α v u
  intro c0
  have hlift : liftApply (n - 1) (Cc hh (n - 1)) (fun _ _ => c0) t = fun _ _ => 0 := by
    by_cases hnN : n - 1 ≤ N
    · funext X' z'
      exact hconst c0 hh hhh t ht X' z' (n - 1) (by omega) hnN
    · exact congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq hh hhh (n - 1)
        (by omega) _) t
  have hpoly : (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ _ => c0) t) =
      fun _ _ _ => if hh - 1 = 0 then c0 else 0 := by
    funext ε X' z'
    simp only [liftPolyField]
    rw [Finset.sum_range_succ']
    have hzero : ∀ d ∈ Finset.range N, ε ^ (d + 1) •
        liftApply (d + 1) (Cc (hh - 1) (d + 1)) (fun _ _ => c0) t X' z' = 0 := by
      intro d hd
      have hdN := Finset.mem_range.mp hd
      rw [hconst c0 (hh - 1) (by omega) t ht X' z' (d + 1) (by omega) (by omega), smul_zero]
    rw [Finset.sum_eq_zero hzero, zero_add, pow_zero, one_smul,
      liftApply_const_degree_zero Q sX sZ a b N H Cc hseq c0 (hh - 1) (by omega) t ht]
  rw [setting_rawFluxCoefficient_degree_action P sX sZ hsZ Cc hseq hh hhh n (by omega) k₀
    (fun _ => c0) contDiff_const t ht X z]
  funext w
  have hΦ : IsBoxSmooth 1 0 (liftApply (n - 1) (Cc hh (n - 1)) (fun _ _ => c0) t) := by
    rw [hlift]
    exact IsBoxSmooth.zero
  rw [constructedLiftTailRawFlux_apply Q Cc N hh n _ t X z k₀ w hΦ
    (setting_metric_contDiff_one P t ht)]
  simp only [hlift, Pi.zero_apply, crossFluxField_zero]
  by_cases hh0 : hh = 0
  · rw [ite_eq_left hh0, sub_zero]
  · rw [ite_eq_right hh0, hpoly, sourceFluxCoeff_const_eq_zero]
    simp only [Pi.zero_apply, sub_zero]

end Setting
end

end AVRegularity.CycleComparison.TailConstructed
end
