-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.LiftSourceBlockCoefficientAction
public import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SettingPairedCoefficientOriginalReserve
import AVRegularity.CycleComparison.Lift.PhysicalPowerSchurWiener
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Calibration may test the exact tail at its own cell degree rather than the global tail cutoff. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

theorem tailLeftCoefficient_degree_action (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (hn : 1 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n (tailLeftCoefficient Q Cc N hh n) (fun _ => f) t X z v =
      leftTermsApply (liftTailLeftTerms Q Cc N hh n t v) f X z := by
  have he := liftApply_congr_at_time n (tailLeftCoefficient Q Cc N hh n)
    (leftTermsBlockCoefficient (fun w => liftTailLeftTerms Q Cc N hh n t w))
    (fun _ => f) t (fun _ _ _ _ _ _ => rfl)
  have hv := congrArg (fun g : Vec 2 → Vec 2 → ∀ i, h i => g X z v) he
  exact hv.trans (leftTermsBlockCoefficient_apply
    (fun w => liftTailLeftTerms Q Cc N hh n t w) n
    (fun w c hc => liftTailLeftTerms_order Q Cc N hh n hn t w c hc) f hf t X z v)
end

/-! The finite recursion starts with the identity and vanishing positive-grade degree-zero coefficients. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem constructedLiftCoefficients_zero_degree (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    constructedLiftCoefficients Q a b hab par N hh 0 m α t X z v u =
      if hh = 0 ∧ m = 0 then blockIdentityEntry h v u else 0 := by
  rw [constructedLiftCoefficients_eq_step Q a b hab par N hh 0 (Nat.zero_le N)]
  simp only [constructedLiftStep, ite_true]

theorem constructedLiftCoefficients_positive_grade_zero (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh : ℕ) (hhh : 1 ≤ hh)
    (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    constructedLiftCoefficients Q a b hab par N hh 0 m α t X z v u = 0 := by
  rw [constructedLiftCoefficients_zero_degree,
    ite_eq_right (by omega : ¬ (hh = 0 ∧ m = 0))]

theorem constructedLiftCoefficients_identity (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N : ℕ)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) :
    liftApply 0 (constructedLiftCoefficients Q a b hab par N 0 0) f t X z = f t X := by
  funext v
  simp [liftApply, constructedLiftCoefficients_zero_degree, blockIdentityEntry_apply,
    orderedDerivative]
end

/-! The literal finite prefix agrees with the constructed family at every preceding grade or degree. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem constructedLift_prefix_agreement (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh n p q : ℕ)
    (he : p < hh ∨ (p = hh ∧ q < n)) :
    (if ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n then
      constructedLiftCoefficients Q a b hab par N p q else 0) =
      constructedLiftCoefficients Q a b hab par N p q := by
  by_cases hq : q ≤ N
  · have hr : ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n := by
      rcases he with hp | ⟨rfl, hqn⟩
      · exact ambientRecurrenceRank_height N hh n p q hp hq
      · unfold ambientRecurrenceRank
        omega
    exact ite_eq_left hr
  · rw [constructedLiftCoefficients_cutoff Q a b hab par N p q (by omega)]
    split <;> rfl
end

/-! Finite source presentation and predecessor source data yield genuine operator coefficient regularity. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {Ks : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}

theorem sourceBlockCoefficient_box_of_presentation
    (data : AmbientLiftSourceData par a b hab lam hh n p q Q Cc Ks M)
    (hlam : lam ≠ 0) (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hblock : ∀ ξ : h u, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z) :
    IsBoxSmooth p q (fun X z => leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u) := by
  apply isBoxSmooth_clm_of_apply
  intro ξ
  have he : (fun X z => leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u ξ) =
      (fun X z => calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z) := by
    funext X z
    exact (calibratedLiftSourceEntry_eq_of_block_action Q Cc hh n m hm α lam hlam
      u v ξ t X z (hblock ξ X z)).symm
  rw [he]
  exact calibratedLiftSourceEntry_box data m α u v ξ t ht
end

/-! The exact tail array has no coefficient above its cell degree. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

theorem tailLeftCoefficient_above_order (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (hm : n < m) (α : DerivativeWord2 m)
    (t : ℝ) (X z : Vec 2) (v u : ι) :
    tailLeftCoefficient Q Cc N hh n m α t X z v u = 0 := by
  have he := leftTermsSymmetricCoefficient_above_order (liftTailLeftTerms Q Cc N hh n t v)
    n (liftTailLeftTerms_order Q Cc N hh n hn t v) m hm α
  ext ξ
  change leftTermsSymmetricCoefficient (liftTailLeftTerms Q Cc N hh n t v) m α X z
    (Pi.single u ξ) = 0
  rw [he]
  rfl
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual identity and zero degrees supply the initial common-reserve induction states. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem constructedLiftCoefficients_identity_ambient_data (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (N : ℕ) (par : Fin 2) (lam : ℝ) (hlam : 0 ≤ lam)
    (p q : ℕ) : AmbientLiftCoefficientData par a b hab lam 0 p q
      (constructedLiftCoefficients Q a b hab par N 0 0)
      (fun v u => if v = u then 1 else 0) := by
  let Cc := constructedLiftCoefficients Q a b hab par N
  have hi (α : DerivativeWord2 0) (t : ℝ) (X z : Vec 2) (v u : ι) :
      Cc 0 0 0 α t X z v u = blockIdentityEntry h v u := by
    dsimp only [Cc]
    rw [constructedLiftCoefficients_zero_degree]
    rfl
  refine ⟨fun v u => by split_ifs <;> norm_num, ?_, ?_, ?_, ?_⟩
  · intro m hm α v u t ht
    have hm0 : m = 0 := by omega
    subst m
    have he : (fun X z => Cc 0 0 0 α t X z v u) =
        fun (_ _ : Vec 2) => blockIdentityEntry h v u := by
      funext X z
      exact hi α t X z v u
    change IsBoxSmooth p q (fun X z => Cc 0 0 0 α t X z v u)
    rw [he]
    exact isBoxSmooth_slow_field p q _ contDiff_const
  · intro m hm α v u r hr s hs t ht X z
    have hm0 : m = 0 := by omega
    subst m
    let T := (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp (ContinuousLinearMap.single ℝ h u)
    have he : (fun Y y => Cc 0 0 0 α t Y y v u) = fun (_ _ : Vec 2) => T :=
      funext fun Y => funext fun y => hi α t Y y v u
    have hej : (fun Y => iteratedFDeriv ℝ s (fun y => Cc 0 0 0 α t Y y v u) z) =
        fun Y => iteratedFDeriv ℝ s (fun _ : Vec 2 => T) z := by
      funext Y
      exact congrArg (fun f : Vec 2 → (h u →L[ℝ] h v) => iteratedFDeriv ℝ s f z)
        (congrFun he Y)
    rw [hej]
    simpa only [Nat.sub_self, Nat.zero_add] using
      norm_mixed_constant_graded_le r s T _ lam (by split_ifs <;> norm_num) hlam
        (identity_component_map_norm_le v u) X z
  · intro m hm α v u t ht X z s
    have hm0 : m = 0 := by omega
    subst m
    change Cc 0 0 0 α t X (z + s • basisVec par) v u = Cc 0 0 0 α t X z v u
    rw [hi α t X (z + s • basisVec par) v u, hi α t X z v u]
  · intro m hm α v u l X z
    have hm0 : m = 0 := by omega
    subst m
    have he : (fun t => l (Cc 0 0 0 α (Set.projIcc a b hab t) X z v u)) = fun (_ : ℝ) =>
        l ((ContinuousLinearMap.proj (R := ℝ) (φ := h) v).comp (ContinuousLinearMap.single ℝ h u)) := by
      funext t
      exact congrArg l (hi α _ X z v u)
    rw [he]
    exact measurable_const

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual inverse step has symmetric words, periodic cells, and literal zero start. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem constructedLiftStep_periodic (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2)
    (prior : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X : Vec 2) (v u : ι) :
    AVenhance.IsZ2Periodic (fun z =>
      constructedLiftStep Q a b hab par prior hh n m α t X z v u) := by
  by_cases hn : n = 0
  · intro k z
    simp only [constructedLiftStep, ite_eq_left hn]
  · simp only [constructedLiftStep, ite_eq_right hn]
    by_cases hm : m ≤ n
    · simp only [ite_eq_left hm]
      exact periodic_scalar_profile par.rev _ (finiteProfileResponse_periodic _ _ a t)
    · intro k z
      simp only [ite_eq_right hm]

theorem constructedLiftStep_perm (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2)
    (prior : ℕ → ℕ → LiftCoeff ι h) (hh n m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    constructedLiftStep Q a b hab par prior hh n m (α ∘ σ) =
      constructedLiftStep Q a b hab par prior hh n m α := by
  funext t X z v u
  simp only [constructedLiftStep, leftTermsBlockCoefficient_perm]
end

/-! Finite source presentation and predecessor source data yield genuine operator coefficient regularity. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {Ks : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}

theorem sourceBlockCoefficient_centered_of_presentation
    (data : AmbientLiftSourceData par a b hab lam hh n p q Q Cc Ks M)
    (hlam : lam ≠ 0) (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2)
    (hblock : ∀ ξ : h u, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z) :
    fieldCellMean (fun z => leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u) = 0 := by
  ext ξ
  have hbox := sourceBlockCoefficient_box_of_presentation data hlam m hm α u v t ht hblock
  have he := fieldCellMean_clm (ContinuousLinearMap.apply ℝ (h v) ξ) ((hbox.1 X).continuous)
  change fieldCellMean (fun z => leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u ξ) =
    (fieldCellMean (fun z => leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u)) ξ at he
  rw [← he]
  have hh : (fun z => leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u ξ) =
      (fun z => calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z) := by
    funext z
    exact (calibratedLiftSourceEntry_eq_of_block_action Q Cc hh n m hm α lam hlam
      u v ξ t X z (hblock ξ X z)).symm
  rw [hh]
  exact calibratedLiftSourceEntry_centered data m α u v ξ t ht X
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite calibrated applied sources recover scalar-dual time measurability of operator entries. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {Ks : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}

theorem sourceBlockCoefficient_dual_measurable_of_presentation
    (data : AmbientLiftSourceData par a b hab lam hh n p q Q Cc Ks M)
    (hlam : lam ≠ 0) (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (hblock : ∀ ξ : h u, ∀ t ∈ Set.Icc a b, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z)
    (l : (h u →L[ℝ] h v) →L[ℝ] ℝ) (X z : Vec 2) :
    Measurable (fun t => l (leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n (Set.projIcc a b hab t) w)
      m α (Set.projIcc a b hab t) X z v u)) := by
  apply operator_dual_measurable_of_applied_duals
  intro ξ μ
  have he : (fun t => μ (leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n (Set.projIcc a b hab t) w)
      m α (Set.projIcc a b hab t) X z v u ξ)) =
      (fun t => μ (calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ
        (Set.projIcc a b hab t) X z)) := by
    funext t
    rw [calibratedLiftSourceEntry_eq_of_block_action Q Cc hh n m hm α lam hlam
      u v ξ (Set.projIcc a b hab t) X z
      (hblock ξ _ (Set.projIcc a b hab t).2 X z)]
  rw [he]
  exact calibratedLiftSourceEntry_dual_measurable data m α u v ξ μ X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Calibrated source geometry gives literal periodic operator-valued source coefficients. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {Ks : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}

theorem sourceBlockCoefficient_periodic_of_presentation
    (data : AmbientLiftSourceData par a b hab lam hh n p q Q Cc Ks M)
    (hlam : lam ≠ 0) (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2)
    (hblock : ∀ ξ : h u, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z) :
    AVenhance.IsZ2Periodic (fun z => leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u) := by
  intro k z
  ext ξ
  rw [← calibratedLiftSourceEntry_eq_of_block_action Q Cc hh n m hm α lam hlam
      u v ξ t X (z + AVenhance.latticeShift k) (hblock ξ X _),
    ← calibratedLiftSourceEntry_eq_of_block_action Q Cc hh n m hm α lam hlam
      u v ξ t X z (hblock ξ X z)]
  exact calibratedLiftSourceEntry_periodic data m α u v ξ t ht X k z
end

/-! Calibrated source geometry gives literal periodic operator-valued source coefficients. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {Ks : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}

theorem sourceBlockCoefficient_transverse_of_presentation
    (data : AmbientLiftSourceData par a b hab lam hh n p q Q Cc Ks M)
    (hlam : lam ≠ 0) (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (hblock : ∀ ξ : h u, ∀ t ∈ Set.Icc a b, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z) :
    IsTransverseOn par (Set.Icc a b) (fun t X z => leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u) := by
  intro t ht X z s
  ext ξ
  rw [← calibratedLiftSourceEntry_eq_of_block_action Q Cc hh n m hm α lam hlam
      u v ξ t X (z + s • basisVec par) (hblock ξ t ht X _),
    ← calibratedLiftSourceEntry_eq_of_block_action Q Cc hh n m hm α lam hlam
      u v ξ t X z (hblock ξ t ht X z)]
  exact calibratedLiftSourceEntry_transverse data m α u v ξ t ht X z s
end

/-! Identity, zero height, and truncation match the fixed scalar-power majorant exactly. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem constructedLiftCoefficients_degree_zero_scalar_power_data (Qdata : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (N H hh : ℕ) (par : Fin 2) (lam : ℝ) (hlam : 0 ≤ lam) (P Q R p q : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (F : ι → ι → ℝ) :
    AmbientLiftCoefficientData par a b hab lam 0 p q (constructedLiftCoefficients Qdata a b hab par N hh 0)
      (fun v u => ambientCoefficientScalarBudget P Q D H R N hh 0 CG Cw Cj *
        finiteMatrixPower F hh v u) := by
  rw [ambientCoefficientScalarBudget_zero]
  by_cases hh0 : hh = 0
  · subst hh
    simp only [ite_true, finiteMatrixPower_zero, one_mul]
    exact constructedLiftCoefficients_identity_ambient_data Qdata a b hab N par lam hlam p q
  · simp only [ite_eq_right hh0, zero_mul]
    have hz : constructedLiftCoefficients Qdata a b hab par N hh 0 = 0 := by
      funext m α t X z v u
      exact constructedLiftCoefficients_positive_grade_zero Qdata a b hab par N hh
        (by omega) m α t X z v u
    rw [hz]
    exact ambient_zero_coefficient_data par a b hab lam 0 p q

theorem constructedLiftCoefficients_cutoff_scalar_power_data (Qdata : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (N H hh n : ℕ) (hN : N < n) (par : Fin 2) (lam : ℝ) (P Q R p q : ℕ) (hn : n ≤ R)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (F : ι → ι → ℝ) :
    AmbientLiftCoefficientData par a b hab lam n p q (constructedLiftCoefficients Qdata a b hab par N hh n)
      (fun v u => ambientCoefficientScalarBudget P Q D H R N hh n CG Cw Cj *
        finiteMatrixPower F hh v u) := by
  rw [ambientCoefficientScalarBudget_cutoff P Q D H R N hh n hn hN]
  simp only [zero_mul]
  rw [constructedLiftCoefficients_cutoff Qdata a b hab par N hh n hN]
  exact ambient_zero_coefficient_data par a b hab lam n p q
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The literal paired mean flux is graded under the original ambient reserve. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem setting_paired_mean_flux_original_reserve
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
    (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (m : ℕ) (hmpos : 1 ≤ m) (hm : m ≤ n - 1) (α : DerivativeWord2 m)
    (r : ℕ) (hr : r ≤ K) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (k₀ : Fin 2) (X z : Vec 2) (v u : ι) :
    ‖iteratedFDeriv ℝ r (fun Y => diagonalMeanFluxCoefficient Q Cc n k₀ m α t Y z v u -
      diagonalMeanFluxCoefficient
        (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
        Ci n k₀ m α t Y z v u) X‖ ≤
      pairedMeanFluxWordBudget n r
        (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI *
        g * (if v = u then 1 else 0) * lam ^ (n - 1 - m + r) := by
  have hreserve : K + (N + D) ≤ qs := by
    simpa only [Nat.add_assoc] using setting_ambient_output_supported P
  have data := setting_paired_coefficient_original_reserve P Cc Ci hseq hseqi g hg CGI hGI (n - 1) (by omega)
  have native := setting_ambient_scalar_power_recurrence_data P (K + D + 2) (max (k + 1) (L + 2))
    (by omega) Cc hseq K hreserve 0 (Nat.zero_le _) (n - 1) (by omega)
  have nativei := setting_ambient_scalar_power_recurrence_data (setting_identity_metric P)
    (K + D + 2) (max (k + 1) (L + 2)) (by omega) Ci hseqi K hreserve 0 (Nat.zero_le _) (n - 1) (by omega)
  have hp : ambientDegreeSlowReserve K (N + D) (n - 1) ≤ qs := by
    unfold ambientDegreeSlowReserve
    omega
  have hrp : r ≤ ambientDegreeSlowReserve K (N + D) (n - 1) := by
    unfold ambientDegreeSlowReserve
    omega
  exact setting_paired_mean_flux_jet_of_coefficient_data P Cc Ci n _ _ hn hp _ g hg CGI hGI data
    (fun m hm α v u t ht X => (native.coefficient.box m hm α v u t ht).1 X |>.continuous)
    (fun m hm α v u t ht X => (nativei.coefficient.box m hm α v u t ht).1 X |>.continuous)
    m hmpos hm α r hrp t ht k₀ X z v u

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite source presentation and predecessor source data yield genuine operator coefficient regularity. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D hh n p q : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {Ks : (Vec 2 →L[ℝ] ℝ) → ℝ} {M : ι → ι → ℝ}

theorem sourceBlockCoefficient_mixed_bound_of_presentation
    (data : AmbientLiftSourceData par a b hab lam hh n p q Q Cc Ks M)
    (hlam : 0 < lam) (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2)
    (hblock : ∀ ξ : h u, ∀ X z, ∀ A : Vec 2 →L[ℝ] ℝ,
      normalizedLiftTestField
        (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
        n A u v ξ t X z = normalizedLiftSourceField Q Cc hh n A u v ξ t X z) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => leftTermsBlockCoefficient
        (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t Y y v u) z) X‖ ≤
      (∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α lam j| *
        Ks ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) * M v u * lam ^ (n + r) := by
  have hbox := sourceBlockCoefficient_box_of_presentation data hlam.ne' m hm α u v t ht hblock
  have hsum : 0 ≤ ∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α lam j| *
      Ks ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (data.constant_nonneg _)
  apply mixed_operator_jet_norm_le_from_apply r s _ (hbox.mono hr hs) X z _
    (mul_nonneg (mul_nonneg hsum (data.matrix_nonneg v u)) (pow_nonneg hlam.le _))
  intro ξ
  have he : (fun X z => leftTermsBlockCoefficient
      (fun w => liftCellSourceLeftTerms Q Cc hh n t w) m α t X z v u ξ) =
      (fun X z => calibratedLiftSourceEntry Q Cc hh n m α lam u v ξ t X z) := by
    funext X z
    exact (calibratedLiftSourceEntry_eq_of_block_action Q Cc hh n m hm α lam hlam.ne'
      u v ξ t X z (hblock ξ X z)).symm
  have hp (Y y : Vec 2) := congrFun (congrFun he Y) y
  simp_rw [hp]
  have hb := calibratedLiftSourceEntry_mixed_bound data m α u v ξ r s hr hs t ht X z
  convert hb using 1
  ring
end

/-! The recursively constructed coefficient family satisfies literal support, symmetry, and periodicity. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem constructedLiftCoefficients_above_order (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh n m : ℕ) (hm : n < m)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    constructedLiftCoefficients Q a b hab par N hh n m α t X z v u = 0 := by
  by_cases hn : n ≤ N
  · rw [constructedLiftCoefficients_eq_step Q a b hab par N hh n hn]
    exact constructedLiftStep_above_order Q a b hab par _ hh n m hm α t X z v u
  · rw [constructedLiftCoefficients_cutoff Q a b hab par N hh n (by omega)]
    rfl

theorem constructedLiftCoefficients_perm (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh n m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    constructedLiftCoefficients Q a b hab par N hh n m (α ∘ σ) =
      constructedLiftCoefficients Q a b hab par N hh n m α := by
  by_cases hn : n ≤ N
  · rw [constructedLiftCoefficients_eq_step Q a b hab par N hh n hn]
    exact constructedLiftStep_perm Q a b hab par _ hh n m α σ
  · rw [constructedLiftCoefficients_cutoff Q a b hab par N hh n (by omega)]
    rfl

theorem constructedLiftCoefficients_periodic (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh n m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X : Vec 2) (v u : ι) :
    AVenhance.IsZ2Periodic (fun z =>
      constructedLiftCoefficients Q a b hab par N hh n m α t X z v u) := by
  by_cases hn : n ≤ N
  · rw [constructedLiftCoefficients_eq_step Q a b hab par N hh n hn]
    exact constructedLiftStep_periodic Q a b hab par _ hh n m α t X v u
  · intro k z
    rw [constructedLiftCoefficients_cutoff Q a b hab par N hh n (by omega)]
    rfl
end

/-! The explicit coefficient array solves the same finite source recurrence evaluated on the completed array. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem constructedLiftCoefficients_eq_full_step (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    constructedLiftCoefficients Q a b hab par N hh n =
      constructedLiftStep Q a b hab par
        (constructedLiftCoefficients Q a b hab par N) hh n := by
  rw [constructedLiftCoefficients_eq_step Q a b hab par N hh n hnN]
  have he (p q : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n)) :=
    constructedLift_prefix_agreement Q a b hab par N hh n p q hpq
  have hsrc (s : ℝ) (w : ι) := liftCellSourceLeftTerms_congr_predecessors Q
    (fun p q => if ambientRecurrenceRank N p q < ambientRecurrenceRank N hh n then
      constructedLiftCoefficients Q a b hab par N p q else 0)
    (constructedLiftCoefficients Q a b hab par N) hh n hn he s w
  funext m α t X z v u
  simp only [constructedLiftStep, ite_eq_right (by omega : n ≠ 0), hsrc]
end

/-! The explicit coefficient cutoff gives the literal tested-operator cutoff. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem constructedLiftApply_cutoff (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh n : ℕ) (hn : N < n)
    (f : ℝ → Vec 2 → ∀ i, h i) :
    liftApply n (constructedLiftCoefficients Q a b hab par N hh n) f = 0 := by
  apply liftApply_of_coeff_zero
  intro m α t X z v u
  rw [constructedLiftCoefficients_cutoff Q a b hab par N hh n hn]
  rfl

theorem constructedLiftApply_zero_degree (Q : LiftOperatorData ι h D)
    (a b : ℝ) (hab : a ≤ b) (par : Fin 2) (N hh : ℕ)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) :
    liftApply 0 (constructedLiftCoefficients Q a b hab par N hh 0) f t =
      fun X _ => if hh = 0 then f t X else 0 := by
  by_cases hh0 : hh = 0
  · subst hh
    funext X z
    simpa only [ite_true] using constructedLiftCoefficients_identity Q a b hab par N f t X z
  · have he := liftApply_of_coeff_zero 0
      (constructedLiftCoefficients Q a b hab par N hh 0)
      (constructedLiftCoefficients_positive_grade_zero Q a b hab par N hh (by omega)) f
    simpa only [ite_eq_right hh0] using! congrFun he t
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Every earlier constructed coefficient supplies the fixed fast and slow reserve for tested fields. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_predecessor_coefficient_box
    (P₀ hh n : ℕ)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u)) (h' i r : ℕ) (hh' : h' ≤ H) (hr : r ≤ D)
    (hiR : i ≤ N + D)
    (hlt : ambientRecurrenceRank (N + D) h' i < ambientRecurrenceRank (N + D) hh n)
    (m : ℕ) (hm : m ≤ i) (α : DerivativeWord2 m)
    (u v : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth r r (fun X z =>
      constructedLiftCoefficients Q a b P.window par N h' i m α t X z v u) := by
  by_cases hi : i ≤ N
  · have state := prior h' hh' i hiR hlt
    apply (state.box m hm α v u t ht).mono
    · unfold ambientDegreeSlowReserve
      omega
    · have hroom : D ≤ N + D - i := by omega
      have htwice := Nat.mul_le_mul_left 2 hroom
      unfold ambientDegreeFastReserve
      omega
  · have he := constructedLiftCoefficients_cutoff Q a b P.window par N h' i (by omega)
    simp only [he, Pi.zero_apply]
    exact IsBoxSmooth.zero
end

/-! The original data reserve supports every actual uncentered rank step, including truncated predecessors. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_source_predecessor_box
    (P₀ hh n : ℕ) (hhh : hh ≤ H) (hhpos : 1 ≤ hh)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u)) (i m : ℕ) (hm : m ≤ i) (α : DerivativeWord2 m)
    (u v : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth D D (fun X z =>
      constructedLiftCoefficients Q a b P.window par N (hh - 1) i m α t X z v u) := by
  by_cases hi : i ≤ N
  · have state := prior (hh - 1) (by omega) i (by omega)
      (ambientRecurrenceRank_height (N + D) hh n (hh - 1) i (by omega) (by omega))
    apply (state.box m hm α v u t ht).mono
    · unfold ambientDegreeSlowReserve
      omega
    · have hroom : D ≤ N + D - i := by omega
      have htwice := Nat.mul_le_mul_left 2 hroom
      unfold ambientDegreeFastReserve
      omega
  · have he := constructedLiftCoefficients_cutoff Q a b P.window par N (hh - 1) i (by omega)
    simp only [he, Pi.zero_apply]
    exact IsBoxSmooth.zero
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The tail flux is the positive supported primitive of its literal coefficient array. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

def tailFluxCoefficient (par : Fin 2) (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (k : Fin 2) : LiftCoeff ι h :=
  positiveFluxLiftCoefficient par (2 * N + D) (tailLeftCoefficient Q Cc N hh n) k

theorem tailFluxCoefficient_outside (par k : Fin 2) (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (X z : Vec 2) (v u : ι) (hm : m = 0 ∨ 2 * N + D < m) :
    tailFluxCoefficient par Q Cc N hh n k m α t X z v u = 0 :=
  positiveFluxLiftCoefficient_outside par k (2 * N + D) _ m (by omega) α t X z v u

theorem tailFluxCoefficient_perm (par k : Fin 2) (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    tailFluxCoefficient par Q Cc N hh n k m (α ∘ σ) =
      tailFluxCoefficient par Q Cc N hh n k m α :=
  positiveFluxLiftCoefficient_perm par k (2 * N + D) _ m α σ
    (tailLeftCoefficient_perm Q Cc N hh n m α σ)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original data reserve supports every actual uncentered rank step, including truncated predecessors. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_source_predecessor_good
    (P₀ hh n : ℕ) (hhh : hh ≤ H) (hhpos : 1 ≤ hh)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (i : ℕ) :
    GoodField D (liftApply i
      (constructedLiftCoefficients Q a b P.window par N (hh - 1) i) (fun _ => f) t) := by
  apply liftApply_goodField_of_coefficients D i _ f hf t
  · intro m hm α v u
    exact setting_constructed_source_predecessor_box P P₀ hh n hhh hhpos prior i m hm α u v t ht
  · intro X m hm α v u
    exact constructedLiftCoefficients_periodic Q a b P.window par N (hh - 1) i m α t X v u
end

/-! Literal mean flux differences have a scalar Schur budget independent of component dimensions. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)


include P in
theorem setting_paired_mean_flux_schur_original_reserve
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
    (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (m : ℕ) (hmpos : 1 ≤ m) (hm : m ≤ n - 1) (r : ℕ) (hr : r ≤ K) :
    schurSlowJet π (Set.Icc a b) r
      (fun (p : DerivativeWord2 m × Fin 2) t X z v u =>
        diagonalMeanFluxCoefficient Q Cc n p.2 m p.1 t X z v u -
        diagonalMeanFluxCoefficient
          (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
          Ci n p.2 m p.1 t X z v u) ≤
      ENNReal.ofReal (pairedMeanScalarBudget (N + D) K
        (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI *
        g * lam ^ (n - 1 - m + r)) := by
  let Bd := pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI
  have hBd j : 0 ≤ Bd j := pairedCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _
  let A := fun _p : DerivativeWord2 m × Fin 2 => pairedMeanFluxWordBudget n r Bd Cw CGI * g
  have hA p : 0 ≤ A p := mul_nonneg (pairedMeanFluxWordBudget_nonneg n r Bd Cw CGI hBd) hg
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hb (p : DerivativeWord2 m × Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b)
      (X z : Vec 2) (v u : ι) :
      ‖iteratedFDeriv ℝ r (fun Y =>
        diagonalMeanFluxCoefficient Q Cc n p.2 m p.1 t Y z v u -
        diagonalMeanFluxCoefficient
          (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
          Ci n p.2 m p.1 t Y z v u) X‖ ≤
        A p * (if v = u then 1 else 0) * lam ^ (n - 1 - m + r) :=
    setting_paired_mean_flux_original_reserve P Cc Ci hseq hseqi g hg CGI hGI
      n hn hnR m hmpos hm p.1 r hr t ht p.2 X z v u
  have hs := schurSlowJet_le_of_word_matrix_budget π (Set.Icc a b) r _ A hA
    (fun v u => if v = u then 1 else 0) (fun v u => by split_ifs <;> norm_num)
    (lam ^ (n - 1 - m + r)) 1 (pow_nonneg hlam _)
    (mass_identity_matrix_schur_budget π P.mass_pos) hb
  have he : schurSlowJet π (Set.Icc a b) r
      (fun (p : DerivativeWord2 m × Fin 2) t X z v u =>
        diagonalMeanFluxCoefficient Q Cc n p.2 m p.1 t X z v u -
        diagonalMeanFluxCoefficient
          (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
          Ci n p.2 m p.1 t X z v u) ≤
      ENNReal.ofReal (pairedMeanFluxScalarBudget n m r Bd Cw CGI * g * lam ^ (n - 1 - m + r)) := by
    simpa only [A, ← Finset.sum_mul, pairedMeanFluxScalarBudget, mul_one] using hs
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pairedMeanScalarBudget_dominates (N + D) K n m r Bd Cw CGI
      hBd hnR (by omega) hr) hg) (pow_nonneg hlam _)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite centered terms reproduce the literal cell-inverse source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D : ℕ} {Q : LiftOperatorData ι h D}

theorem liftCellSource_leftTerms_apply_of_representations
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2) (v : ι)
    (hA : leftTermsApply (liftALeftTerms Q Cc hh n t v) f X z =
      liftA Q Cc (fun _ => f) hh n t X z v)
    (hmean : ∀ Y, leftTermsApply (recurrenceMeanLeftTerms Q Cc hh n t) f Y z =
      liftMean Q Cc (fun _ => f) hh n t Y)
    (hbox : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ d ∈ actualMeanLeftTerms Q Cc p.2 (n - j) t, IsBoxSmooth j 0 d.coeff)
    (hactual : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ Y, leftTermsApply (actualMeanLeftTerms Q Cc p.2 (n - j) t) f Y z =
        liftMean Q Cc (fun _ => f) p.2 (n - j) t Y) :
    leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z =
      liftCellSource Q Cc (fun _ => f) hh n t X z v := by
  have hmean : leftTermsApply
      ((recurrenceMeanLeftTerms Q Cc hh n t).map
        (fun c => c.postcompose (ContinuousLinearMap.proj v))) f X z =
      liftMean Q Cc (fun _ => f) hh n t X v := by
    rw [leftTermsApply_map_postcompose]
    dsimp only
    rw [hmean X]
    rfl
  unfold liftCellSourceLeftTerms
  rw [leftTermsApply_append]
  dsimp only
  rw [leftTermsApply_append]
  dsimp only
  rw [leftTermsApply_map_smul]
  dsimp only
  rw [hA,
    hmean, leftTermsApply_finset_flatMap]
  simp only [liftCellSource, Pi.add_apply, Pi.neg_apply,
    neg_one_smul, sub_eq_add_neg, add_comm]
  congr 1
  · abel
  · rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [leftTermsApply_finset_flatMap, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro p hp
    exact lift_mean_composition_leftTerms_apply_of_representation Cc p.2 j (n - j)
      (Cc p.1 j) v f hf t X z (hbox j hj p hp) (hactual j hj p hp)
end

/-! The finite centered terms reproduce the literal cell-inverse source. -/

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
theorem setting_liftCellSource_leftTerms_apply
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z =
      liftCellSource Q Cc (fun _ => f) hh n t X z v := by
  have hmean : leftTermsApply
      ((recurrenceMeanLeftTerms Q Cc hh n t).map
        (fun c => c.postcompose (ContinuousLinearMap.proj v))) f X z =
      liftMean Q Cc (fun _ => f) hh n t X v := by
    rw [leftTermsApply_map_postcompose]
    dsimp only
    rw [setting_recurrenceMeanLeftTerms_apply P sX sZ hsX hsZ Cc hseq
      hh hhh n hn (by omega) f hf t ht X z]
    rfl
  unfold liftCellSourceLeftTerms
  rw [leftTermsApply_append]
  dsimp only
  rw [leftTermsApply_append]
  dsimp only
  rw [leftTermsApply_map_smul]
  dsimp only
  rw [setting_liftA_leftTerms_apply P sX sZ (by omega) Cc hseq hh hhh n hn hnN f hf t ht X z v,
    hmean, leftTermsApply_finset_flatMap]
  simp only [liftCellSource, Pi.add_apply, Pi.neg_apply,
    neg_one_smul, sub_eq_add_neg, add_comm]
  congr 1
  · abel
  · rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hjdata := Finset.mem_Icc.mp hj
    rw [leftTermsApply_finset_flatMap, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro p hp
    have hpdata := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact setting_lift_mean_composition_leftTerms_apply P sX sZ hsX hsZ Cc hseq
      p.2 (by omega) j (n - j) (by omega) (by omega) (by omega)
      (Cc p.1 j) v f hf t ht X z
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Every earlier constructed coefficient supplies the fixed fast and slow reserve for tested fields. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_constructed_predecessor_good_field
    (P₀ hh n : ℕ)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (constructedLiftCoefficients Q a b P.window par N h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u))
    (h' i r : ℕ) (hh' : h' ≤ H) (hr : r ≤ D) (hiR : i ≤ N + D)
    (hlt : ambientRecurrenceRank (N + D) h' i < ambientRecurrenceRank (N + D) hh n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    GoodField r (liftApply i (constructedLiftCoefficients Q a b P.window par N h' i)
      (fun _ => f) t) := by
  apply liftApply_goodField_of_coefficients r i _ f hf t
  · intro m hm α v u
    exact setting_constructed_predecessor_coefficient_box P P₀ hh n prior
      h' i r hh' hr hiR hlt m hm α u v t ht
  · intro X m hm α v u
    exact constructedLiftCoefficients_periodic Q a b P.window par N h' i m α t X v u

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Symmetric block synthesis of the actual centered source on exponential tests. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftSource_blockCoefficient_apply
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    liftApply n (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w))
      (fun _ => f) t X z v = liftCellSource Q Cc (fun _ => f) hh n t X z v := by
  rw [leftTermsBlockCoefficient_apply _ n (fun w => liftCellSourceLeftTerms_order Cc hh n hn t w)
    f hf t X z v]
  exact setting_liftCellSource_leftTerms_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnN f hf t ht X z v

include P in
theorem setting_liftSource_blockCoefficient_normalized
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    normalizedLiftTestField
      (leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n t w)) n A u v ξ t X z =
      normalizedLiftSourceField Q Cc hh n A u v ξ t X z := by
  unfold normalizedLiftTestField normalizedLiftSourceField
  congr 1
  exact setting_liftSource_blockCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnN
    (fun Y => Real.exp (A Y) • Pi.single u ξ)
    ((Real.contDiff_exp.comp A.contDiff).smul contDiff_const) t ht X z v

end AVRegularity.CycleComparison.Lift
end
