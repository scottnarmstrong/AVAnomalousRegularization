-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingWindowInverseClampedTransverse
public import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import AVRegularity.CycleComparison.Lift.SettingLiftPolyTimeIntegral
import AVRegularity.CycleComparison.Lift.SettingLiftAPolynomial
import AVRegularity.CycleComparison.Lift.SettingAmbientPositiveCoefficientRankStep

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The explicit finite-coordinate response solves the original lift setting cell equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]

include P in
theorem setting_sourceBlock_response_inverse
    (p q hh n : ℕ) (hq : 2 ≤ q) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (Ks : (Vec 2 →L[ℝ] ℝ) → ℝ) (M : ι → ι → ℝ)
    (data : AmbientLiftSourceData par a b P.window lam hh n p q Q Cc Ks M)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (hblock : ∀ ξ : h u, ∀ t ∈ Icc a b, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z)
    (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
      (fun t z => leftTermsBlockCoefficient
        (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u)
      (fun t z => finiteProfileResponse
        (fun r => Q.G (Set.projIcc a b P.window r) X par.rev par.rev)
        (fun s x => leftTermsBlockCoefficient
          (fun w => liftCellSourceLeftTerms Q Cc hh n (Set.projIcc a b P.window s) w)
          m α s X (x • basisVec par.rev) v u) a t (z par.rev)) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  let S := fun t X z => leftTermsBlockCoefficient
    (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u
  let B := (∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α lam j| *
    Ks ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) * M v u * lam ^ n
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (data.constant_nonneg _)) (data.matrix_nonneg v u))
    (pow_nonneg hlam.le _)
  apply setting_transverse_field_response_inverse P q hq S
    (fun t ht => (sourceBlockCoefficient_box_of_presentation data hlam.ne' m hm α u v t ht
      (fun ξ => hblock ξ t ht)).mono (Nat.zero_le p) le_rfl)
    (sourceBlockCoefficient_transverse_of_presentation data hlam.ne' m hm α u v hblock)
    (fun l X z => sourceBlockCoefficient_dual_measurable_of_presentation data hlam.ne'
      m hm α u v hblock l X z)
    (fun t ht X => sourceBlockCoefficient_periodic_of_presentation data hlam.ne'
      m hm α u v t ht X (fun ξ => hblock ξ t ht))
    (fun t ht X => sourceBlockCoefficient_centered_of_presentation data hlam.ne'
      m hm α u v t ht X (fun ξ => hblock ξ t ht))
    (fun _ => B) (fun _ _ => hB) _ X
  intro j hj t ht Y z
  have hb := sourceBlockCoefficient_mixed_bound_of_presentation data hlam m hm α u v
    0 j (Nat.zero_le p) hj t ht Y z (fun ξ => hblock ξ t ht)
  simpa only [S, B, norm_iteratedFDeriv_zero, Nat.add_zero] using hb

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Original native reserves control every source predecessor, including zero coefficients above both cutoffs. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tail_coefficient_box_and_bound
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (p q : ℕ) (hp : p ≤ K + D + 2) (hq : q ≤ max k (L + 2) + D)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m)
    (u v : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (fun X z => tailLeftCoefficient Q Cc N hh n m α t X z v u) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => tailLeftCoefficient Q Cc N hh n m α t Y y v u) z) X‖ ≤
        ((∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α 1 j| *
          tailTestScalarBudget K k L D H N hh n p q CG Cw Cj
            ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * lam ^ (n - m + r) := by
  let c := tailLeftCoefficient Q Cc N hh n
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  have hbox (ξ : h u) (A : Vec 2 →L[ℝ] ℝ) :
      IsBoxSmooth p q (normalizedLiftTestField c n (lam • A) u v ξ t) := by
    have he : normalizedLiftTestField c n (lam • A) u v ξ t =
        normalizedLiftTailField Q Cc N hh n (lam • A) u v ξ t := by
      funext X z
      exact setting_tail_coefficient_normalized_test_eq P sX sZ hsX hsZ Cc hseq
        hh hhh n hn (lam • A) u v ξ t ht X z
    rw [he]
    exact (setting_tail_test_power_grading P sX sZ (by omega) Cc hseq p q hp hq
      hh hhh n hn A u v ξ t ht).1
  have hb (ξ : h u) (A : Vec 2 →L[ℝ] ℝ) (r : ℕ) (hr : r ≤ p)
      (s : ℕ) (hs : s ≤ q) (X z : Vec 2) :
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (normalizedLiftTestField c n (lam • A) u v ξ t Y) z) X‖ ≤
        (tailTestScalarBudget K k L D H N hh n p q CG Cw Cj A *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u * ‖ξ‖) * lam ^ (n + r) := by
    have he : normalizedLiftTestField c n (lam • A) u v ξ t =
        normalizedLiftTailField Q Cc N hh n (lam • A) u v ξ t := by
      funext Y y
      exact setting_tail_coefficient_normalized_test_eq P sX sZ hsX hsZ Cc hseq
        hh hhh n hn (lam • A) u v ξ t ht Y y
    rw [he]
    exact (setting_tail_test_power_grading P sX sZ (by omega) Cc hseq p q hp hq
      hh hhh n hn A u v ξ t ht).2 r hr s hs X z
  refine ⟨symmetric_lift_coefficient_box_of_tests c n m p q hm
    (fun β σ => tailLeftCoefficient_perm Q Cc N hh n m β σ) α lam hlam.ne' u v t hbox, ?_⟩
  intro r hr s hs X z
  exact symmetric_lift_coefficient_graded_bound_of_tests c n m p q hm
    (fun β σ => tailLeftCoefficient_perm Q Cc N hh n m β σ) α lam hlam u v t
    (tailTestScalarBudget K k L D H N hh n p q CG Cw Cj)
    (tailTestScalarBudget_nonneg K k L D H N hh n p q CG Cw Cj)
    (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u)
    (finiteMatrixPower_nonneg _ (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u)
    hbox hb r s hr hs X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The explicit finite-coordinate response solves the original lift setting cell equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]

include P in
theorem setting_constructed_source_step_inverse
    (p q hh n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n)
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (Ks : (Vec 2 →L[ℝ] ℝ) → ℝ) (M : ι → ι → ℝ)
    (data : AmbientLiftSourceData par a b P.window lam hh n p q Q Cc Ks M)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (hblock : ∀ ξ : h u, ∀ t ∈ Icc a b, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z)
    (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
      (fun t z => leftTermsBlockCoefficient
        (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u)
      (fun t z => constructedLiftStep Q a b P.window par Cc hh n m α t X z v u) := by
  have hline (x : ℝ) : Pi.single par.rev x = x • basisVec par.rev := by
    ext j
    by_cases hj : j = par.rev
    · subst j
      simp [basisVec_apply]
    · simp [hj, basisVec_apply]
  simpa only [constructedLiftStep, ite_eq_right (by omega : n ≠ 0),
    ite_eq_left hm, hline] using
    setting_sourceBlock_response_inverse P p q hh n hq Cc Ks M data m hm α u v hblock X

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The ambient grading exposes both original-fast-order lift norms and actual
mean coefficient surplus. -/

theorem cycle_lift_grading_upto (P₀ N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      P₀ + N + D ≤ qs →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h, IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
      (∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ P₀ →
          schurEnergyJet π (Set.Icc t₀ t₁) k j (Cc hh n m)
              ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - m + j)) ∧
          schurWienerJet π (Set.Icc t₀ t₁) L j (Cc hh n m)
              ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - m + j))) ∧
      (∀ hh, hh ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
          ∃ Lb : MeanCoeff ι h,
            (∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))), Lb d (α ∘ σ) = Lb d α) ∧
            (∀ d α k v u, ∀ t ∈ Set.Icc t₀ t₁,
              ContDiff ℝ ((P₀ + 1 : ℕ) : ℕ∞) (fun X => Lb d α t X k v u)) ∧
            (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
              liftMean Q Cc (fun _ => a₀) hh n t X = meanApply n Lb (fun _ => a₀) t X) ∧
            (∀ d, 2 ≤ d → d ≤ n → ∀ j, j ≤ P₀ →
              schurSlowJet π (Set.Icc t₀ t₁) j
                (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => Lb d p.1 t X p.2)
                ≤ ENNReal.ofReal (C * Θ ^ hh * lam ^ (n - d + j)))) :=
by
  obtain ⟨Cn, hCn, hn⟩ := cycle_lift_norm_grading_upto P₀ N K k L D H CG Cw Cj
  obtain ⟨Cm, hCm, hm⟩ := cycle_lift_mean_grading_upto P₀ N K k L D H CG Cw Cj
  refine ⟨Cn + Cm, add_nonneg hCn hCm, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P hreserve Cc hseq
  have hnorm := hn Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P hreserve Cc hseq
  have hmean := hm Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf edge Θ P hreserve Cc hseq
  constructor
  · intro hh hhh n hnpos hnN m hmpos hmn r hr
    have hg := hnorm hh hhh n hnpos hnN m hmpos hmn r hr
    have he : ENNReal.ofReal (Cn * Θ ^ hh * lam ^ (n - m + r)) ≤
        ENNReal.ofReal ((Cn + Cm) * Θ ^ hh * lam ^ (n - m + r)) := by
      simpa only [mul_assoc] using
        ofReal_constant_mul_mono Cn (Cn + Cm) (Θ ^ hh * lam ^ (n - m + r)) hCn
          (le_add_of_nonneg_right hCm)
    exact ⟨hg.1.trans he, hg.2.trans he⟩
  · intro hh hhh n hnpos hnR
    obtain ⟨Lb, hsym, hreg, hact, hbound⟩ := hmean hh hhh n hnpos hnR
    refine ⟨Lb, hsym, hreg, hact, ?_⟩
    intro d hd hdn r hr
    apply (hbound d hd hdn r hr).trans
    simpa only [mul_assoc] using
      ofReal_constant_mul_mono Cm (Cn + Cm) (Θ ^ hh * lam ^ (n - d + r)) hCm
        (le_add_of_nonneg_left hCn)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The explicit finite-coordinate response solves the original lift setting cell equation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]

include P in
theorem setting_constructed_coefficient_inverse_of_source
    (p q hh n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hnN : n ≤ N)
    (Ks : (Vec 2 →L[ℝ] ℝ) → ℝ) (M : ι → ι → ℝ)
    (data : AmbientLiftSourceData par a b P.window lam hh n p q Q (constructedLiftCoefficients Q a b P.window par N) Ks M)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (hblock : ∀ ξ : h u, ∀ t ∈ Icc a b, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q (constructedLiftCoefficients Q a b P.window par N) hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q (constructedLiftCoefficients Q a b P.window par N) hh n A u v ξ t X z)
    (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
      (fun t z => leftTermsBlockCoefficient
        (fun w => liftCellSourceLeftTerms Q (constructedLiftCoefficients Q a b P.window par N) hh n t w) m α t X z v u)
      (fun t z => constructedLiftCoefficients Q a b P.window par N hh n m α t X z v u) := by
  have hi := setting_constructed_source_step_inverse P p q hh n hq hn
    (constructedLiftCoefficients Q a b P.window par N) Ks M data m hm α u v hblock X
  have he := constructedLiftCoefficients_eq_full_step Q a b P.window par N hh n hn hnN
  convert hi using 1
  exact congrArg (fun c : LiftCoeff ι h => fun t z => c m α t X z v u) he
end

/-! The explicit finite-coordinate response solves the original lift setting cell equation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]

include P in
theorem setting_constructed_normalized_test_inverse_of_source
    (p q hh n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hnN : n ≤ N)
    (Ks : (Vec 2 →L[ℝ] ℝ) → ℝ) (M : ι → ι → ℝ)
    (data : AmbientLiftSourceData par a b P.window lam hh n p q Q (constructedLiftCoefficients Q a b P.window par N) Ks M)
    (hblock : ∀ u v, ∀ ξ : h u, ∀ t ∈ Icc a b, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q (constructedLiftCoefficients Q a b P.window par N) hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q (constructedLiftCoefficients Q a b P.window par N) hh n A u v ξ t X z)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
      (fun t z => normalizedLiftSourceField Q
        (constructedLiftCoefficients Q a b P.window par N) hh n A u v ξ t X z)
      (fun t z => normalizedLiftTestField
        (constructedLiftCoefficients Q a b P.window par N hh n) n A u v ξ t X z) := by
  let Cc := constructedLiftCoefficients Q a b P.window par N
  let S := liftSourceBlockCoefficient Q Cc hh n
  apply liftCoefficient_normalized_test_inverse Q a b P.window q (by omega) Cc hh n
    S A u v ξ X
  · intro m hm α v₀ u₀
    exact setting_constructed_coefficient_inverse_of_source P p q hh n hq hn hnN
      Ks M data m hm α u₀ v₀ (hblock u₀ v₀) X
  · intro t ht z
    exact (liftSourceBlockCoefficient_normalized Q Cc hh n A u v ξ t X z).trans
      (hblock u v ξ t ht X z A)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original data reserve supports every actual uncentered rank step, including truncated predecessors. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_source_action_of_predecessors
    (P₀ hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hp : N + D + 1 ≤ P₀) (hreserve : P₀ + (N + D) ≤ qs)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u))
    (hmeans : ∀ h' ≤ H, ∀ i, 1 ≤ i → i ≤ N + D →
      ambientRecurrenceRank (N + D) h' i < ambientRecurrenceRank (N + D) hh n →
      ∀ m ≤ i, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Set.Icc a b, ∀ X, ∀ ξ : h u,
        fieldCellMean (fun z => constructedLiftCoefficients Q a b P.window par N h' i
          m α t X z v u ξ) = 0)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (liftCellSourceLeftTerms Q
      (constructedLiftCoefficients Q a b P.window par N) hh n t v) f X z =
      liftCellSource Q (constructedLiftCoefficients Q a b P.window par N)
        (fun _ => f) hh n t X z v := by
  let Cc := constructedLiftCoefficients Q a b P.window par N
  have hb (i : ℕ) (hi : i < n) (m : ℕ) (hm : m ≤ i)
      (α : DerivativeWord2 m) (v u : ι) :=
    setting_constructed_predecessor_coefficient_box P P₀ hh n prior hh i 2 hhh
      P.D_ge (by omega) (ambientRecurrenceRank_composition (N + D) hh n hh i le_rfl (by omega) hi)
      m hm α u v t ht
  apply liftCellSource_leftTerms_apply_of_representations Cc hh n f hf t X z v
  · apply setting_liftA_leftTerms_apply_of_coefficients P Cc hh n hn hnN f hf t ht X z v
    · intro m hm α u u'
      exact (hb (n - 1) (by omega) m hm α u u').mono (by omega) (by omega)
    · intro hn2 m hm α u u'
      exact (hb (n - 2) (by omega) m hm α u u').mono le_rfl (Nat.zero_le _)
    · intro hh0 i m hm α u u'
      exact setting_constructed_source_predecessor_box P P₀ hh n hhh (by omega) prior
        i m hm α u' u t ht
    · intro hh0
      exact setting_constructed_source_predecessor_good P P₀ hh n hhh (by omega) prior f hf t ht
    · intro hh0 i hi
      exact congrFun (constructedLiftApply_cutoff Q a b P.window par N (hh - 1) i hi (fun _ => f)) t
  · intro Y
    exact setting_constructed_recurrence_mean_action_of_predecessors P P₀ hh n hhh hn
      (by omega) (by omega) hreserve prior hmeans f hf t ht Y z
  · intro j hj ab hab' d hd
    have hj' := Finset.mem_Icc.mp hj
    have hab'' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab'
    have hlt := ambientRecurrenceRank_composition (N + D) hh n ab.2 (n - j)
      (by omega) (by omega) (by omega)
    apply meanFluxLeftTerms_box (n - j) _ t j 0 ?_ d hd
    intro k m hm α u u'
    exact setting_constructed_mean_flux_regular_of_predecessors P P₀ ab.2 (n - j) j
      (by omega) (by omega) (by omega) (by omega) hreserve
      (fun h' hh' i hi hi' => prior h' hh' i hi (hi'.trans hlt))
      k t ht m hm α 0 u u'
  · intro j hj ab hab' Y
    have hj' := Finset.mem_Icc.mp hj
    have hab'' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab'
    have hlt := ambientRecurrenceRank_composition (N + D) hh n ab.2 (n - j)
      (by omega) (by omega) (by omega)
    exact setting_constructed_mean_action_of_predecessors P P₀ ab.2 (n - j)
      (by omega) (by omega) (by omega) (by omega) hreserve
      (fun h' hh' i hi hi' => prior h' hh' i hi (hi'.trans hlt))
      (fun h' hh' i hi hiR hi' => hmeans h' hh' i hi hiR (hi'.trans hlt))
      f hf t ht Y z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The proved actual centered source closes precisely the fixed scalar-power coefficient recurrence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_coefficient_state_of_source
    (P₀ hh n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hreserve : P₀ + (N + D) ≤ qs)
    (source : AmbientLiftSourceData par a b P.window lam hh n
      (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) Q
      (constructedLiftCoefficients Q a b P.window par N)
      (ambientCenteredBudget P₀ (max k (L + 2)) D H (N + D) hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj))
      (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh))
    (hblock : ∀ u v, ∀ ξ : h u, ∀ t ∈ Icc a b, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q
          (constructedLiftCoefficients Q a b P.window par N) hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q
          (constructedLiftCoefficients Q a b P.window par N) hh n A u v ξ t X z) :
    AmbientLiftCoefficientData par a b P.window lam n
      (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n)
      (constructedLiftCoefficients Q a b P.window par N hh n)
      (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N hh n CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) ∧
    (∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Icc a b, ∀ X, ∀ ξ : h u,
      fieldCellMean (fun z => constructedLiftCoefficients Q a b P.window par N hh n
        m α t X z v u ξ) = 0) := by
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n
  have hq : 2 ≤ q := ambientDegreeFastReserve_two (max k (L + 2)) D H (N + D) hh n (by omega)
  have hdata := setting_liftCoefficient_scalar_power_data_of_source P q
    (constructedLiftCoefficients Q a b P.window par N) P₀ (max k (L + 2)) (N + D) hh n
    (by omega) hn hnN (constructedLiftCoefficients_perm Q a b P.window par N hh n)
    (fun A u v ξ X => setting_constructed_normalized_test_inverse_of_source P
      p q hh n hq hn hnN _ _ source hblock (lam • A) u v ξ X)
    (ambientDegreeSlowReserve_data P₀ (N + D) n qs hreserve) hq _ source
  refine ⟨hdata, ?_⟩
  intro m hm α v u t ht X ξ
  have hi := setting_constructed_coefficient_inverse_of_source P p q hh n hq hn hnN
    _ _ source m hm α u v (hblock u v) X
  have hmean := cellFieldInverse_fieldCellMean_zero _ _ q a b 0 _ _ hi t ht
  have he := fieldCellMean_clm (ContinuousLinearMap.apply ℝ (h v) ξ) ((hi.1 t ht).continuous)
  change fieldCellMean (fun z => constructedLiftCoefficients Q a b P.window par N hh n
      m α t X z v u ξ) =
    (fieldCellMean (fun z => constructedLiftCoefficients Q a b P.window par N hh n
      m α t X z v u)) ξ at he
  rw [he, hmean]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Positive truncation preserves every literal tail coefficient on its time window. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tailLeftCoefficient_fast_continuous
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (α : DerivativeWord2 m) (u v : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    Continuous (fun z => tailLeftCoefficient Q Cc N hh n m α t X z v u) := by
  by_cases hm : m ≤ n
  · exact ((setting_tail_coefficient_box_and_bound P sX sZ hsX hsZ Cc hseq
      0 0 (by omega) (by omega) hh hhh n hn m hm α u v t ht).1.1 X).continuous
  · have he : (fun z => tailLeftCoefficient Q Cc N hh n m α t X z v u) = 0 := by
      funext z
      exact tailLeftCoefficient_above_order Q Cc N hh n hn m (by omega) α t X z v u
    rw [he]
    exact continuous_const

include P in
theorem setting_tail_positive_coefficient_eq
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (m : ℕ) (α : DerivativeWord2 m) (X z : Vec 2) (v u : ι) :
    positiveLiftCoefficient (2 * N + D) (tailLeftCoefficient Q Cc N hh n) m α t X z v u =
      tailLeftCoefficient Q Cc N hh n m α t X z v u := by
  apply positiveLiftCoefficient_eq_at_time
  intro m hm α X z v u
  by_cases hz : m = 0
  · subst m
    exact setting_tailLeftCoefficient_zero_order P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnR α t ht X z v u
  · exact tailLeftCoefficient_above_order Q Cc N hh n hn m (by omega) α t X z v u
end

/-! The scale restriction removes all nonnegative-order powers from tail primitive bounds. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tail_entry_primitive_slow_bound
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (dir : Fin 2)
    (j : ℕ) (hj : j ≤ K) (X z : Vec 2) (hz : z par.rev ∈ Set.Icc (0 : ℝ) 1) :
    ‖iteratedFDeriv ℝ j (fun Y => transverseCenteredFlux par (fun r =>
      tailLeftCoefficient Q Cc N hh n m α t Y (r • basisVec par.rev) v u) dir z) X‖ ≤
      (2 : ℝ) ^ (j + 1) *
        (tailEntryTestScalarBudget K k L D H N hh n m (K + D + 2)
          (max (k + 1) (L + 2) - 1) CG Cw Cj α *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) := by
  let p := K + D + 2
  let q := max (k + 1) (L + 2) - 1
  have hq : q ≤ max k (L + 2) + D := by dsimp [q]; omega
  let f := fun X z => tailLeftCoefficient Q Cc N hh n m α t X z v u
  let B := tailEntryTestScalarBudget K k L D H N hh n m p q CG Cw Cj α *
    finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u
  let C := fun r => B * lam ^ (n - m + r)
  have hd := setting_tail_coefficient_box_and_bound P sX sZ hsX hsZ Cc hseq
    p q le_rfl hq hh hhh n hn m hm α u v t ht
  have hb : ∀ r ≤ p, ∀ (y : ℝ) (Y : Vec 2),
      ‖iteratedFDeriv ℝ r (fun Z => f Z (y • basisVec par.rev)) Y‖ ≤ C r := by
    intro r hr y Y
    have he := hd.2 r hr 0 (Nat.zero_le q) Y (y • basisVec par.rev)
    rw [norm_mixed_jet_fast_zero] at he
    exact he
  have he := transverseCenteredFlux_slow_norm_le par dir p q f hd.1 C hb j (by dsimp [p]; omega) X z hz
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hB : 0 ≤ B := mul_nonneg
    (tailEntryTestScalarBudget_nonneg K k L D H N hh n m p q CG Cw Cj α)
    (finiteMatrixPower_nonneg _ (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u)
  have hc : C j ≤ B := by
    exact mul_le_of_le_one_right hB (pow_le_one₀ hlam P.lam_le)
  calc
    _ ≤ (2 : ℝ) ^ j * (2 * C j) := he
    _ ≤ (2 : ℝ) ^ j * (2 * B) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (by norm_num)) (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (j + 1) * B := by rw [pow_succ]; ring
end

/-! Tested tail flux synthesis equals the centered primitive of the literal tail. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tailFluxCoefficient_apply
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) (dir : Fin 2) :
    liftApply (2 * N + D) (tailFluxCoefficient par Q Cc N hh n dir) (fun _ => f) t X z v =
      transverseCenteredFlux par (fun r =>
        liftTailCoeff Q Cc N (fun _ => f) hh n t X (r • basisVec par.rev) v) dir z := by
  let c := tailLeftCoefficient Q Cc N hh n
  let cp := positiveLiftCoefficient (2 * N + D) c
  have he := setting_tail_positive_coefficient_eq P sX sZ hsX hsZ Cc hseq
    hh hhh n hn hnR t ht
  have hc (m : ℕ) (_hm : m ≤ 2 * N + D) (α : DerivativeWord2 m) (u : ι) :
      Continuous (fun r : ℝ => cp m α t X (r • basisVec par.rev) v u) := by
    have heq : (fun r : ℝ => cp m α t X (r • basisVec par.rev) v u) =
        fun r => c m α t X (r • basisVec par.rev) v u := by
      funext r
      exact he m α X (r • basisVec par.rev) v u
    rw [heq]
    exact (setting_tailLeftCoefficient_fast_continuous P sX sZ hsX hsZ Cc hseq
      hh hhh n hn m α u v t ht X).comp (continuous_id.smul continuous_const)
  change liftApply (2 * N + D) (centeredFluxLiftCoefficient par cp dir) (fun _ => f) t X z v = _
  rw [liftApply_centeredFluxLiftCoefficient par dir (2 * N + D) cp (fun _ => f) t X z v hc]
  have happly := liftApply_congr_at_time (2 * N + D) cp c (fun _ => f) t he
  have hprofile : (fun r : ℝ => liftApply (2 * N + D) cp (fun _ => f) t X
        (r • basisVec par.rev) v) =
      fun r => liftTailCoeff Q Cc N (fun _ => f) hh n t X (r • basisVec par.rev) v := by
    funext r
    rw [happly]
    exact congrFun (setting_tailLeftCoefficient_apply P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnR f hf t ht X (r • basisVec par.rev)) v
  rw [hprofile]
end

/-! The supported primitive array presents the exact literal tail by fast divergence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tailFluxCoefficient_vector_action
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (dir : Fin 2) :
    liftApply (2 * N + D) (tailFluxCoefficient par Q Cc N hh n dir) (fun _ => f) t X z =
      transverseCenteredFlux par (fun r =>
        liftTailCoeff Q Cc N (fun _ => f) hh n t X (r • basisVec par.rev)) dir z := by
  have hc : Continuous (fun r : ℝ =>
      liftTailCoeff Q Cc N (fun _ => f) hh n t X (r • basisVec par.rev)) :=
    (setting_liftTailCoeff_fast_continuous P sX sZ hsX hsZ Cc hseq
      hh hhh n f hf t ht X).comp (continuous_id.smul continuous_const)
  funext v
  rw [setting_tailFluxCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnR f hf t ht X z v dir]
  exact transverseCenteredFlux_clm par dir (ContinuousLinearMap.proj v) _ hc z

include P in
theorem setting_tailFluxCoefficient_divergence
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    (∑ dir : Fin 2, fastPartial dir (fun Y y =>
      liftApply (2 * N + D) (tailFluxCoefficient par Q Cc N hh n dir) (fun _ => f) t Y y) X z) =
      liftTailCoeff Q Cc N (fun _ => f) hh n t X z := by
  have he (dir : Fin 2) : (fun Y y =>
      liftApply (2 * N + D) (tailFluxCoefficient par Q Cc N hh n dir) (fun _ => f) t Y y) =
      fun Y y => transverseCenteredFlux par (fun r =>
        liftTailCoeff Q Cc N (fun _ => f) hh n t Y (r • basisVec par.rev)) dir y := by
    funext Y y
    exact setting_tailFluxCoefficient_vector_action P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnR f hf t ht Y y dir
  simp_rw [he]
  exact transverseCenteredFlux_field_div par _
    (setting_liftTailCoeff_fast_continuous P sX sZ hsX hsZ Cc hseq hh hhh n f hf t ht)
    (fun Y y => transverse_field_factorization par (Set.Icc a b) _
      (setting_liftTailCoeff_transverse P sX sZ (by omega) Cc hseq hh hhh n f hf) t ht Y y) X z
end

/-! Every tested tail flux has exactly zero fast cell mean. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tailFluxCoefficient_mean_zero
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnR : n ≤ 2 * N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (dir : Fin 2) :
    fieldCellMean (fun z =>
      liftApply (2 * N + D) (tailFluxCoefficient par Q Cc N hh n dir) (fun _ => f) t X z) = 0 := by
  have he : (fun z =>
      liftApply (2 * N + D) (tailFluxCoefficient par Q Cc N hh n dir) (fun _ => f) t X z) =
      transverseCenteredFlux par (fun r =>
        liftTailCoeff Q Cc N (fun _ => f) hh n t X (r • basisVec par.rev)) dir := by
    funext z
    exact setting_tailFluxCoefficient_vector_action P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnR f hf t ht X z dir
  rw [he]
  exact transverseCenteredFlux_mean_zero par dir _
    ((setting_liftTailCoeff_fast_continuous P sX sZ hsX hsZ Cc hseq
      hh hhh n f hf t ht X).comp (continuous_id.smul continuous_const))
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Two actual divergence-form mean arrays and their metric comparison under the original reserve. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem setting_paired_mean_coefficients_original_reserve
    (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N 0 Cc)
    (hseqi : IsLiftSequence
      (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
      (K + D + 2) (max (k + 1) (L + 2)) a b N 0 Ci)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) :
    ∃ Lb Lbi : MeanCoeff ι h,
      (∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Set.Icc a b, ∀ X,
        liftMean Q Cc (fun _ => f) 0 n t X = meanApply n Lb (fun _ => f) t X) ∧
      (∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Set.Icc a b, ∀ X,
        liftMean (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
          Ci (fun _ => f) 0 n t X = meanApply n Lbi (fun _ => f) t X) ∧
      ∀ d, 2 ≤ d → d ≤ n → ∀ r, r ≤ K →
        schurSlowJet π (Set.Icc a b) r
          (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X _ => Lb d p.1 t X p.2 - Lbi d p.1 t X p.2) ≤
        ENNReal.ofReal (pairedMeanScalarBudget (N + D) K
          (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI *
          g * lam ^ (n - d + r)) := by
  let Qi : LiftOperatorData ι h D := ⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩
  let c := diagonalMeanFluxCoefficient Q Cc n
  let ci := diagonalMeanFluxCoefficient Qi Ci n
  have hreserve : K + (N + D) ≤ qs := by
    simpa only [Nat.add_assoc] using setting_ambient_output_supported P
  refine ⟨truncatedMeanCoefficient n c, truncatedMeanCoefficient n ci, ?_, ?_, ?_⟩
  · intro f hf t ht X
    rw [truncatedMeanCoefficient_meanApply]
    exact setting_diagonal_mean_flux_meanApply P (K + D + 2) (max (k + 1) (L + 2))
      (by omega) (by omega) Cc hseq K hreserve n hn hnR f hf t ht X
  · intro f hf t ht X
    rw [truncatedMeanCoefficient_meanApply]
    exact setting_diagonal_mean_flux_meanApply (setting_identity_metric P)
      (K + D + 2) (max (k + 1) (L + 2)) (by omega) (by omega) Ci hseqi K hreserve n hn hnR f hf t ht X
  · intro d hd hdn r hr
    have he : (fun (p : DerivativeWord2 (d - 1) × Fin 2) t X (_z : Vec 2) =>
        truncatedMeanCoefficient n c d p.1 t X p.2 - truncatedMeanCoefficient n ci d p.1 t X p.2) =
        fun (p : DerivativeWord2 (d - 1) × Fin 2) t X z v u =>
          c p.2 (d - 1) p.1 t X z v u - ci p.2 (d - 1) p.1 t X z v u := by
      funext p t X z v u
      simp only [Pi.sub_apply]
      rw [truncatedMeanCoefficient_eq n d hd hdn, truncatedMeanCoefficient_eq n d hd hdn]
      exact congrArg₂ (fun x y => x - y)
        (diagonalMeanFluxCoefficient_fast_constant Q Cc n p.2 (d - 1) p.1 t X z v u).symm
        (diagonalMeanFluxCoefficient_fast_constant Qi Ci n p.2 (d - 1) p.1 t X z v u).symm
    rw [he]
    have hb := setting_paired_mean_flux_schur_original_reserve P Cc Ci hseq hseqi g hg CGI hGI
      n hn hnR (d - 1) (by omega) (by omega) r hr
    have hδ : n - 1 - (d - 1) = n - d := by omega
    simpa only [hδ] using hb

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Native tail coefficient reserves give regular periodic transverse primitives. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tail_entry_primitive_geometry
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m)
    (u v : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (dir : Fin 2) :
    IsBoxSmooth (K + D + 2) (max (k + 1) (L + 2))
      (fun X z => transverseCenteredFlux par (fun r =>
        tailLeftCoefficient Q Cc N hh n m α t X (r • basisVec par.rev) v u) dir z) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => transverseCenteredFlux par (fun r =>
      tailLeftCoefficient Q Cc N hh n m α t X (r • basisVec par.rev) v u) dir z) := by
  let p := K + D + 2
  let q := max (k + 1) (L + 2) - 1
  have hq : q ≤ max k (L + 2) + D := by dsimp [q]; omega
  have hqsucc : q + 1 = max (k + 1) (L + 2) := by dsimp [q]; omega
  let f := fun X z => tailLeftCoefficient Q Cc N hh n m α t X z v u
  have hd := setting_tail_coefficient_box_and_bound P sX sZ hsX hsZ Cc hseq
    p q le_rfl hq hh hhh n (by omega) m hm α u v t ht
  let C := fun j => ((∑ i : Fin (m + 1) × Fin (n + 1),
    |liftCalibrationWeight n m α 1 i| *
      tailTestScalarBudget K k L D H N hh n p q CG Cw Cj
        ((i.2 : ℝ) • coordinateSymbolDirection (i.1 : ℝ))) *
      finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) * lam ^ (n - m + j)
  have hb : ∀ j ≤ p, ∀ (r : ℝ) (X : Vec 2),
      ‖iteratedFDeriv ℝ j (fun Y => f Y (r • basisVec par.rev)) X‖ ≤ C j := by
    intro j hj r X
    have he := hd.2 j hj 0 (Nat.zero_le q) X (r • basisVec par.rev)
    rw [norm_mixed_jet_fast_zero] at he
    exact he
  have hz : ∀ X, fieldCellMean (f X) = 0 := by
    intro X
    apply ContinuousLinearMap.ext
    intro ξ
    have he := fieldCellMean_clm (ContinuousLinearMap.apply ℝ (h v) ξ)
      (hd.1.1 X).continuous
    change (ContinuousLinearMap.apply ℝ (h v) ξ) (fieldCellMean (f X)) = 0
    rw [← he]
    exact setting_tailLeftCoefficient_entry_centered P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnR m (by omega) α t ht X v u ξ
  have hg := transverseCenteredFlux_box_and_periodic par dir p q f hd.1
    (fun X z => transverse_field_factorization par (Set.Icc a b)
      (fun t X z => tailLeftCoefficient Q Cc N hh n m α t X z v u)
      (setting_tailLeftCoefficient_transverse P sX sZ hsX hsZ Cc hseq
        hh hhh n (by omega) hnR m (by omega) α v u) t ht X z)
    C hb
    (fun X => setting_tailLeftCoefficient_periodic P sX sZ hsX hsZ Cc hseq
      hh hhh n (by omega) hnR m (by omega) α t ht X v u) hz
  rw [hqsucc] at hg
  exact hg
end

/-! Every tail flux entry has the required box regularity and periodicity. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tailFluxCoefficient_geometry
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D)
    (m : ℕ) (α : DerivativeWord2 m) (u v : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (dir : Fin 2) :
    IsBoxSmooth (K + D + 2) (max (k + 1) (L + 2))
      (fun X z => tailFluxCoefficient par Q Cc N hh n dir m α t X z v u) ∧
    ∀ X, AVenhance.IsZ2Periodic
      (fun z => tailFluxCoefficient par Q Cc N hh n dir m α t X z v u) := by
  by_cases hm : 1 ≤ m ∧ m ≤ 2 * N + D
  · by_cases hmn : m ≤ n
    · have he : (fun X z => tailFluxCoefficient par Q Cc N hh n dir m α t X z v u) =
          fun X z => transverseCenteredFlux par (fun r =>
            tailLeftCoefficient Q Cc N hh n m α t X (r • basisVec par.rev) v u) dir z := by
        funext X z
        simp only [tailFluxCoefficient, positiveFluxLiftCoefficient,
          centeredFluxLiftCoefficient, positiveLiftCoefficient, ite_eq_left hm]
      have hg := setting_tail_entry_primitive_geometry P sX sZ hsX hsZ Cc hseq
        hh hhh n hn hnR m hmn α u v t ht dir
      refine ⟨?_, ?_⟩
      · rw [he]; exact hg.1
      · intro X
        rw [congrFun he X]
        exact hg.2 X
    · have he : (fun X z => tailFluxCoefficient par Q Cc N hh n dir m α t X z v u) = 0 := by
        funext X z
        apply centeredFluxLiftCoefficient_entry_eq_zero
        intro Y y
        change (if 1 ≤ m ∧ m ≤ 2 * N + D then
          tailLeftCoefficient Q Cc N hh n m α t Y y v u else 0) = 0
        rw [ite_eq_left hm]
        exact tailLeftCoefficient_above_order Q Cc N hh n (by omega) m (by omega) α t Y y v u
      refine ⟨?_, ?_⟩
      · rw [he]; exact IsBoxSmooth.zero
      · intro X
        rw [congrFun he X]
        exact fun _ _ => rfl
  · have he : (fun X z => tailFluxCoefficient par Q Cc N hh n dir m α t X z v u) = 0 := by
      funext X z
      exact positiveFluxLiftCoefficient_outside par dir (2 * N + D) _ m hm α t X z v u
    refine ⟨?_, ?_⟩
    · rw [he]; exact IsBoxSmooth.zero
    · intro X
      rw [congrFun he X]
      exact fun _ _ => rfl
end

/-! Truncated flux arrays retain the primitive unit-cell slow-jet bounds. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tailFluxCoefficient_slow_bound
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (_hnR : n ≤ 2 * N + D)
    (m : ℕ) (α : DerivativeWord2 m) (u v : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (dir : Fin 2)
    (j : ℕ) (hj : j ≤ K) (X z : Vec 2) (hz : z par.rev ∈ Set.Icc (0 : ℝ) 1) :
    ‖iteratedFDeriv ℝ j (fun Y => tailFluxCoefficient par Q Cc N hh n dir m α t Y z v u) X‖ ≤
      (2 : ℝ) ^ (j + 1) *
        (tailEntryTestScalarBudget K k L D H N hh n m (K + D + 2)
          (max (k + 1) (L + 2) - 1) CG Cw Cj α *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) := by
  have hB : 0 ≤ (2 : ℝ) ^ (j + 1) *
        (tailEntryTestScalarBudget K k L D H N hh n m (K + D + 2)
          (max (k + 1) (L + 2) - 1) CG Cw Cj α *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg
      (tailEntryTestScalarBudget_nonneg K k L D H N hh n m _ _ CG Cw Cj α)
      (finiteMatrixPower_nonneg _ (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u))
  by_cases hm : 1 ≤ m ∧ m ≤ 2 * N + D
  · by_cases hmn : m ≤ n
    · have he : (fun Y => tailFluxCoefficient par Q Cc N hh n dir m α t Y z v u) =
          fun Y => transverseCenteredFlux par (fun r =>
            tailLeftCoefficient Q Cc N hh n m α t Y (r • basisVec par.rev) v u) dir z := by
        funext Y
        simp only [tailFluxCoefficient, positiveFluxLiftCoefficient,
          centeredFluxLiftCoefficient, positiveLiftCoefficient, ite_eq_left hm]
      rw [he]
      exact setting_tail_entry_primitive_slow_bound P sX sZ hsX hsZ Cc hseq
        hh hhh n (by omega) m hmn α u v t ht dir j hj X z hz
    · have he : (fun Y => tailFluxCoefficient par Q Cc N hh n dir m α t Y z v u) = 0 := by
        funext Y
        apply centeredFluxLiftCoefficient_entry_eq_zero
        intro Z y
        change (if 1 ≤ m ∧ m ≤ 2 * N + D then
          tailLeftCoefficient Q Cc N hh n m α t Z y v u else 0) = 0
        rw [ite_eq_left hm]
        exact tailLeftCoefficient_above_order Q Cc N hh n (by omega) m (by omega) α t Z y v u
      rw [he]
      change ‖iteratedFDeriv ℝ j (fun _ : Vec 2 => (0 : h u →L[ℝ] h v)) X‖ ≤ _
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hB
  · have he : (fun Y => tailFluxCoefficient par Q Cc N hh n dir m α t Y z v u) = 0 := by
      funext Y
      exact positiveFluxLiftCoefficient_outside par dir (2 * N + D) _ m hm α t Y z v u
    rw [he]
    change ‖iteratedFDeriv ℝ j (fun _ : Vec 2 => (0 : h u →L[ℝ] h v)) X‖ ≤ _
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hB
end

/-! Every primitive flux entry obeys its literal uniform-time cell norm estimate. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_tailFluxCoefficient_cell_bound
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D)
    (m : ℕ) (α : DerivativeWord2 m) (u v : ι) (dir : Fin 2)
    (j : ℕ) (hj : j ≤ K) :
    cellL2Jet (Set.Icc a b) j
      (fun t X z => tailFluxCoefficient par Q Cc N hh n dir m α t X z v u) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (j + 1) *
        (tailEntryTestScalarBudget K k L D H N hh n m (K + D + 2)
          (max (k + 1) (L + 2) - 1) CG Cw Cj α *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u)) := by
  apply cellL2Jet_le_box_unit_bound (Set.Icc a b) (K + D + 2)
    (max (k + 1) (L + 2)) j (by omega)
  · intro t ht
    exact (setting_tailFluxCoefficient_geometry P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnR m α u v t ht dir).1
  · intro t ht X z hz
    have hcoord : z par.rev ∈ Set.Icc (0 : ℝ) 1 := by
      have hc : z par.rev ∈ Set.Ioo (0 : ℝ) 1 := hz par.rev (Set.mem_univ _)
      exact ⟨hc.1.le, hc.2.le⟩
    exact setting_tailFluxCoefficient_slow_bound P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnR m α u v t ht dir j hj X z hcoord
end

end AVRegularity.CycleComparison.Lift
end
