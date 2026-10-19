-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingTailFluxCoefficientCellBound
import AVRegularity.CycleComparison.Lift.SettingLiftPolyTimeIntegral
public import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient
import AVRegularity.CycleComparison.Lift.SecondCrossMean

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Primitive entry bounds sum to a component-free physical envelope power budget. -/

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
theorem setting_tailFluxCoefficient_word_schur
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hΘ : 0 ≤ Θ) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D)
    (m j : ℕ) (hj : j ≤ K) :
    schurCellL2Jet π (Set.Icc a b) j (fun p : DerivativeWord2 m × Fin 2 =>
      tailFluxCoefficient par Q Cc N hh n p.2 m p.1) ≤
      ENNReal.ofReal (tailWordScalarBudget K k L D H N hh n m j CG Cw Cj * Θ ^ hh) := by
  let M := finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh
  let A := fun p : DerivativeWord2 m × Fin 2 => (2 : ℝ) ^ (j + 1) *
    tailEntryTestScalarBudget K k L D H N hh n m (K + D + 2)
      (max (k + 1) (L + 2) - 1) CG Cw Cj p.1
  have hA (p : DerivativeWord2 m × Fin 2) : 0 ≤ A p :=
    mul_nonneg (pow_nonneg (by norm_num) _)
      (tailEntryTestScalarBudget_nonneg K k L D H N hh n m _ _ CG Cw Cj p.1)
  have hbudget := physicalEdgeEnvelopeMatrix_power_schur_budget π P.mass_pos edge Θ hΘ
    ⟨P.envelope.nonneg, P.envelope.row_sum, P.envelope.col_sum⟩ hh
  have hs := schurCellL2Jet_le_of_word_matrix_budget π (Set.Icc a b) j
    (fun p : DerivativeWord2 m × Fin 2 => tailFluxCoefficient par Q Cc N hh n p.2 m p.1)
    A hA M
    (finiteMatrixPower_nonneg _ (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh)
    (Θ ^ hh) hbudget (fun p v u => ?_)
  · apply hs.trans_eq
    congr 1
    congr 1
    dsimp [A, tailWordScalarBudget]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    simp_rw [← two_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [pow_succ, pow_succ]
    ring
  · have he := setting_tailFluxCoefficient_cell_bound P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnR m p.1 u v p.2 j hj
    apply he.trans_eq
    congr 1
    dsimp [A, M]
    ring
end

/-! One permitted order-only constant controls every tail flux coefficient order. -/

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
theorem setting_tailFluxCoefficient_schur
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D)
    (m j : ℕ) (hj : j ≤ K) :
    schurCellL2Jet π (Set.Icc a b) j (fun p : DerivativeWord2 m × Fin 2 =>
      tailFluxCoefficient par Q Cc N hh n p.2 m p.1) ≤
      ENNReal.ofReal (tailPresentationScalarBudget K k L D H N CG Cw Cj * Θ ^ hh) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · have := hι
    simp [schurCellL2Jet, schurSums]
  · have := hι
    have hΘ : 0 ≤ Θ := (Finset.sum_nonneg (fun u _ => P.envelope.nonneg (Classical.choice hι) u)).trans
      (P.envelope.row_sum (Classical.choice hι))
    by_cases hm : m ≤ 2 * N + D
    · apply (setting_tailFluxCoefficient_word_schur P sX sZ hsX hsZ Cc hseq
        hΘ hh hhh n hn hnR m j hj).trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (tailWordScalarBudget_le_presentation K k L D H N hh n m j CG Cw Cj hhh hnR hm hj)
        (pow_nonneg hΘ _)
    · let c := fun p : DerivativeWord2 m × Fin 2 =>
        tailFluxCoefficient par Q Cc N hh n p.2 m p.1
      have hc : ∀ p t X z v u, c p t X z v u = 0 := by
        intro p t X z v u
        exact tailFluxCoefficient_outside par p.2 Q Cc N hh n m p.1 t X z v u
          (Or.inr (by omega))
      exact (schurCellL2Jet_eq_zero π (Set.Icc a b) j c hc).le.trans bot_le
end

/-! The literal lift tail has the supported centered flux presentation with order-only bounds. -/

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
theorem setting_tail_presentation
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D) :
    IsLiftTailPresentation Q Cc (K + D + 2) (max (k + 1) (L + 2)) π a b N K
      (tailPresentationScalarBudget K k L D H N CG Cw Cj) Θ hh n
      (0 : LiftCoeff ι h) (tailFluxCoefficient par Q Cc N hh n) := by
  have hzero (f : ℝ → Vec 2 → ∀ i, h i) :
      liftApply (2 * N + D) (0 : LiftCoeff ι h) f = 0 :=
    liftApply_of_coeff_zero _ _ (fun _ _ _ _ _ _ _ => rfl) f
  unfold IsLiftTailPresentation
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ _ _ _ _ _ _ => rfl
  · intro dir m α t X z v u hm
    exact tailFluxCoefficient_outside par dir Q Cc N hh n m α t X z v u hm
  · exact fun _ _ _ _ _ _ _ _ => rfl
  · exact fun _ _ _ => rfl
  · exact fun dir m α σ => tailFluxCoefficient_perm par dir Q Cc N hh n m α σ
  · intro m α v u t ht
    exact ⟨IsBoxSmooth.zero, fun _ _ _ => rfl⟩
  · intro dir m α v u t ht
    exact setting_tailFluxCoefficient_geometry P sX sZ hsX hsZ Cc hseq
      hh hhh n hn hnR m α u v t ht dir
  · intro f hf t ht X z
    rw [hzero]
    change liftTailCoeff Q Cc N (fun _ => f) hh n t X z = 0 + _
    rw [zero_add]
    exact (setting_tailFluxCoefficient_divergence P sX sZ hsX hsZ Cc hseq
      hh hhh n (by omega) hnR f hf t ht X z).symm
  · intro f hf t ht X
    refine ⟨?_, ?_⟩
    · rw [hzero]
      exact fieldCellMean_const 0
    · intro dir
      exact setting_tailFluxCoefficient_mean_zero P sX sZ hsX hsZ Cc hseq
        hh hhh n (by omega) hnR f hf t ht X dir
  · intro j hj m
    refine ⟨?_, ?_⟩
    · exact (schurCellL2Jet_eq_zero π (Set.Icc a b) j ((0 : LiftCoeff ι h) m)
        (fun _ _ _ _ _ _ => rfl)).le.trans bot_le
    · exact setting_tailFluxCoefficient_schur P sX sZ hsX hsZ Cc hseq
        hh hhh n hn hnR m j hj
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The proved actual centered source closes precisely the fixed scalar-power coefficient recurrence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_ambient_data_and_means
    (P₀ : ℕ) (hp : N + D + 1 ≤ P₀) (hreserve : P₀ + (N + D) ≤ qs)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hnR : n ≤ N + D) :
    AmbientLiftCoefficientData par a b P.window lam n
      (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n)
      (constructedLiftCoefficients Q a b P.window par N hh n)
      (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N hh n CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) ∧
    (1 ≤ n → ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Icc a b, ∀ X, ∀ ξ : h u,
      fieldCellMean (fun z => constructedLiftCoefficients Q a b P.window par N hh n
        m α t X z v u ξ) = 0) := by
  let Cc := constructedLiftCoefficients Q a b P.window par N
  let State := fun hh n =>
    AmbientLiftCoefficientData par a b P.window lam n
      (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) (Cc hh n)
      (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N hh n CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) ∧
    (1 ≤ n → ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u, ∀ t ∈ Icc a b, ∀ X, ∀ ξ : h u,
      fieldCellMean (fun z => Cc hh n m α t X z v u ξ) = 0)
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have main : ∀ r hh, hh ≤ H → ∀ n, n ≤ N + D →
      ambientRecurrenceRank (N + D) hh n = r → State hh n := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro hh hhh n hnR hr
      have prior : ∀ h' ≤ H, ∀ i ≤ N + D,
          ambientRecurrenceRank (N + D) h' i < ambientRecurrenceRank (N + D) hh n → State h' i := by
        intro h' hh' i hi hlt
        rw [hr] at hlt
        exact ih (ambientRecurrenceRank (N + D) h' i) hlt h' hh' i hi rfl
      by_cases hn0 : n = 0
      · subst n
        refine ⟨?_, fun hzero => False.elim (by omega)⟩
        exact constructedLiftCoefficients_degree_zero_scalar_power_data Q a b P.window N H hh
          par lam hlam P₀ (max k (L + 2)) (N + D)
          (ambientDegreeSlowReserve P₀ (N + D) 0)
          (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh 0)
          CG Cw Cj (physicalEdgeEnvelopeMatrix π edge)
      · by_cases hnN : n ≤ N
        · have hcoef := fun h' hh' i hi hlt => (prior h' hh' i hi hlt).1
          have hmean := fun h' hh' i hi hiR hlt => (prior h' hh' i hiR hlt).2 hi
          have source := setting_constructed_source_data_of_predecessors P P₀ hh n
            hreserve hhh (by omega) hnN hcoef hmean
          have hblock (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Icc a b)
              (X z : Vec 2) (A : Vec 2 →L[ℝ] ℝ) :=
            normalized_source_block_of_finite_action Q Cc hh n (by omega) t u v ξ A X z
              (setting_constructed_source_action_of_predecessors P P₀ hh n hhh (by omega) hnN
                hp hreserve hcoef hmean (fun Y => Real.exp (A Y) • Pi.single u ξ)
                ((Real.contDiff_exp.comp A.contDiff).smul contDiff_const) t ht X z v)
          have step := setting_constructed_coefficient_state_of_source P P₀ hh n (by omega) hnN
            hreserve source hblock
          exact ⟨step.1, fun _ => step.2⟩
        · refine ⟨?_, ?_⟩
          · exact constructedLiftCoefficients_cutoff_scalar_power_data Q a b P.window N H hh n
              (by omega) par lam P₀ (max k (L + 2)) (N + D)
              (ambientDegreeSlowReserve P₀ (N + D) n)
              (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) hnR
              CG Cw Cj (physicalEdgeEnvelopeMatrix π edge)
          · intro _ m _ α v u t _ X ξ
            dsimp only [Cc]
            rw [constructedLiftCoefficients_cutoff Q a b P.window par N hh n (by omega)]
            simp only [Pi.zero_apply, zero_apply, fieldCellMean_zero]
  exact main (ambientRecurrenceRank (N + D) hh n) hh hhh n hnR rfl
end

/-! The proved actual centered source closes precisely the fixed scalar-power coefficient recurrence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_lift_inverse
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v (max (k + 1) (L + 2)) a b 0
      (fun t z => liftCellSource Q (constructedLiftCoefficients Q a b P.window par N)
        (fun _ => f) hh n t X z)
      (fun t z => liftApply n (constructedLiftCoefficients Q a b P.window par N hh n)
        (fun _ => f) t X z) := by
  let P₀ := K + N + D + 2
  let Cc := constructedLiftCoefficients Q a b P.window par N
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n
  have hp : N + D + 1 ≤ P₀ := by dsimp only [P₀]; omega
  have hreserve : P₀ + (N + D) ≤ qs := by
    rw [P.qs_eq]
    exact constructedLiftExistence_slow_reserve K N D H P.D_ge
  have state := setting_constructed_ambient_data_and_means P P₀ hp hreserve
  have prior := fun h' hh' i hi (_hlt : ambientRecurrenceRank (N + D) h' i <
      ambientRecurrenceRank (N + D) hh n) => (state h' hh' i hi).1
  have hmean := fun h' hh' i hi hiR (_hlt : ambientRecurrenceRank (N + D) h' i <
      ambientRecurrenceRank (N + D) hh n) => (state h' hh' i hiR).2 hi
  have source := setting_constructed_source_data_of_predecessors P P₀ hh n hreserve hhh hn hnN
    prior hmean
  have hblock (u v : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Icc a b)
      (Y z : Vec 2) (A : Vec 2 →L[ℝ] ℝ) :=
    normalized_source_block_of_finite_action Q Cc hh n hn t u v ξ A Y z
      (setting_constructed_source_action_of_predecessors P P₀ hh n hhh hn hnN hp hreserve
        prior hmean (fun Y => Real.exp (A Y) • Pi.single u ξ)
        ((Real.contDiff_exp.comp A.contDiff).smul contDiff_const) t ht Y z v)
  let S := liftSourceBlockCoefficient Q Cc hh n
  have hq : 2 ≤ q := ambientDegreeFastReserve_two (max k (L + 2)) D H (N + D) hh n (by omega)
  have hi := liftApply_coefficient_inverse (fun t => Matrix.of (Q.G t X)) Q.v q (by omega)
    a b P.window n S (Cc hh n) f X
    (fun m hm α v u => setting_constructed_coefficient_inverse_of_source P p q hh n hq hn hnN
      _ _ source m hm α u v (hblock u v) X)
  have hi' : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
      (fun t z => liftCellSource Q Cc (fun _ => f) hh n t X z)
      (fun t z => liftApply n (Cc hh n) (fun _ => f) t X z) := by
    apply cellFieldInverse_source_congr_on (fun t => Matrix.of (Q.G t X)) Q.v q a b 0 _ _ _ ?_ hi
    intro t ht
    funext z
    ext v
    change liftApply n (liftSourceBlockCoefficient Q Cc hh n) (fun _ => f) t X z v = _
    rw [liftSourceBlockCoefficient_action Q Cc hh n hn f hf t X z v]
    exact setting_constructed_source_action_of_predecessors P P₀ hh n hhh hn hnN hp hreserve
      prior hmean f hf t ht X z v
  exact cellFieldInverse_order_mono _ _ q _
    (constructedLiftExistence_fast_reserve k L D H N hh n P.D_ge hnN) a b 0 _ _ hi'
end

/-! The explicit finite coefficient recurrence is a lift sequence under the original reserves. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_lift_sequence :
    IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H
      (constructedLiftCoefficients Q a b P.window par N) := by
  let Cc := constructedLiftCoefficients Q a b P.window par N
  let P₀ := K + N + D + 2
  have hp : N + D + 1 ≤ P₀ := by dsimp only [P₀]; omega
  have hr : P₀ + (N + D) ≤ qs := by
    rw [P.qs_eq]
    exact constructedLiftExistence_slow_reserve K N D H P.D_ge
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f _ t _ X z
    exact constructedLiftCoefficients_identity Q a b P.window par N (fun _ => f) t X z
  · intro hh hhh _ m α t X z v u
    exact constructedLiftCoefficients_positive_grade_zero Q a b P.window par N hh hhh
      m α t X z v u
  · intro hh _ n hn m α t X z v u
    rw [constructedLiftCoefficients_cutoff Q a b P.window par N hh n hn]
    rfl
  · intro hh _ n m hm α t X z v u
    exact constructedLiftCoefficients_above_order Q a b P.window par N hh n m hm α t X z v u
  · intro hh _ n m α σ
    exact constructedLiftCoefficients_perm Q a b P.window par N hh n m α σ
  · intro hh hhh n m α v u t ht
    refine ⟨?_, fun X => constructedLiftCoefficients_periodic Q a b P.window par N
      hh n m α t X v u⟩
    by_cases hn : n ≤ N
    · by_cases hm : m ≤ n
      · have data := (setting_constructed_ambient_data_and_means P P₀ hp hr hh hhh n
          (by omega)).1
        apply (data.box m hm α v u t ht).mono
        · dsimp only [P₀, ambientDegreeSlowReserve]
          omega
        · exact constructedLiftExistence_fast_reserve k L D H N hh n P.D_ge hn
      · have he := constructedLiftCoefficients_above_order Q a b P.window par N hh n m
          (by omega) α t
        simp only [he]
        exact IsBoxSmooth.zero
    · rw [constructedLiftCoefficients_cutoff Q a b P.window par N hh n (by omega)]
      change IsBoxSmooth _ _ (fun _ _ => (0 : h u →L[ℝ] h v))
      exact IsBoxSmooth.zero
  · intro hh hhh n hn hnN f hf X
    exact setting_constructed_lift_inverse P hh n hhh hn hnN f hf X
end

end AVRegularity.CycleComparison.Lift
end
