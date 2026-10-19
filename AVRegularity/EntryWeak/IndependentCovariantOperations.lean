-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentTransportedCoefficientJetBound

section
section
/-! Independent covariant polynomial operations restrict to the actual intrinsic planar formulas. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] [SecondCountableTopology E] in
theorem independent_covariant_step_affine_slice {H : ℕ}
    (F : ℕ → ℝ → Vec 2 → P → E)
    (QF : ∀ j, IndependentParameterSourceReserve H (F j)) (hH : 1 ≤ H)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ)
    (η : ℝ) (a : P) (k : Fin 2) (j : ℕ) (t : ℝ) (z X : Vec 2) :
    (Real.exp (A X))⁻¹ • covariantCoefficientStep η k
      (fun j X z => Real.exp (A X) • F j t z (L X + a)) j X z =
      independentCovariantCoefficientStep L A η k F j t z (L X + a) := by
  let Qs := fun j => (QF j).affineSlice L hL a
  have hf := normalized_fastPartial_exp_smul A k
    (fun t z X => F j t z (L X + a)) t z X
    (((Qs j).fast_contDiff t X).differentiable (by exact_mod_cast (show H ≠ 0 by omega)) z)
  by_cases hj : j = 0
  · simpa only [covariantCoefficientStep, independentCovariantCoefficientStep,
      hj, ite_true, add_zero, AVRegularity.fastPartial] using hf
  · have hs := normalized_slowPartial_exp_smul A k
      (fun t z X => F (j - 1) t z (L X + a)) t z X
      ((((Qs (j - 1)).regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable
        (by exact_mod_cast (show H ≠ 0 by omega)) X)
    simp only [covariantCoefficientStep, independentCovariantCoefficientStep,
      ite_eq_right hj, smul_add]
    rw [smul_comm (Real.exp (A X))⁻¹ (Real.sqrt η), hf, hs]
    rw [independent_covariant_slow_affine_slice (QF (j - 1)) hH L A a k t z X]
    rfl

theorem independent_covariant_list_affine_slice {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (w : List (Fin 2)) (hw : w.length ≤ H)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ)
    (η : ℝ) (a : P) (j : ℕ) (t : ℝ) (z X : Vec 2) :
    (Real.exp (A X))⁻¹ • covariantListCoefficients η w
      (fun X z => Real.exp (A X) • f t z (L X + a)) j X z =
      independentCovariantListCoefficients L A η w f j t z (L X + a) := by
  induction w using List.reverseRecOn generalizing j t z X with
  | nil =>
    by_cases hj : j = 0
    · simp only [covariantListCoefficients_nil, independentCovariantListCoefficients_nil,
        hj, ite_true, smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
    · simp only [covariantListCoefficients_nil, independentCovariantListCoefficients_nil,
        ite_eq_right hj, smul_zero]
  | append_singleton w k ih =>
    have hw' : w.length + 1 ≤ H := by simpa only [List.length_append, List.length_singleton] using hw
    have he (t : ℝ) : covariantListCoefficients η w
        (fun X z => Real.exp (A X) • f t z (L X + a)) =
        fun j X z => Real.exp (A X) •
          independentCovariantListCoefficients L A η w f j t z (L X + a) := by
      funext j X z
      have hh := ih (by omega) j t z X
      calc
        _ = Real.exp (A X) • ((Real.exp (A X))⁻¹ •
            covariantListCoefficients η w
              (fun X z => Real.exp (A X) • f t z (L X + a)) j X z) := by
          rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
        _ = _ := by rw [hh]
    rw [covariantListCoefficients_append_singleton, he,
      independentCovariantListCoefficients_append_singleton]
    exact independent_covariant_step_affine_slice _
      (fun i => Q.covariantList 1 L hL A η w (by omega) i) le_rfl L hL A η a k j t z X

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine independent means retain full joint reserves, with a finite primitive menu price. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def independentSourceMenuBudget {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) : ℝ := ∑ r : Fin (H + 1), Q.budget r.val

omit [BorelSpace E] [SecondCountableTopology E] in
theorem independentSourceMenuBudget_nonneg {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) : 0 ≤ independentSourceMenuBudget Q :=
  Finset.sum_nonneg (fun _ _ => Q.budget_nonneg _)

omit [BorelSpace E] [SecondCountableTopology E] in
theorem independentSourceBudget_le_menu {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) (r : ℕ) (hr : r ≤ H) :
    Q.budget r ≤ independentSourceMenuBudget Q :=
  Finset.single_le_sum (f := fun j : Fin (H + 1) => Q.budget j.val)
    (fun j _ => Q.budget_nonneg j.val) (Finset.mem_univ ⟨r, by omega⟩)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem independentCoordinateMeanWord_nil (f : ℝ → Vec 2 → Vec d → E) (t : ℝ) :
    independentCoordinateMeanWord f t [] = fun Y => fieldCellMean (fun z => f t z Y) := by
  funext Y
  apply congrArg fieldCellMean
  funext z
  exact iteratedFDeriv_zero_apply _

theorem independent_source_mean_contDiff_bound {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) (t : ℝ) :
    ContDiff ℝ (H : ℕ∞) (fun Y => fieldCellMean (fun z => f t z Y)) ∧
    ∀ r, r ≤ H → ∀ Y,
      ‖iteratedFDeriv ℝ r (fun X => fieldCellMean (fun z => f t z X)) Y‖ ≤
        (d : ℝ) ^ r * independentSourceMenuBudget Q := by
  let J := independentCoordinateMeanWord f t
  have hc w (hw : w.length ≤ H) : Continuous (J w) :=
    independent_coordinate_mean_word_continuous Q t w hw
  have hd w (hw : w.length < H) i Y :=
    independent_coordinate_mean_word_derivative Q t w (by omega) i Y
  have hb w (hw : w.length ≤ H) Y : ‖J w Y‖ ≤ independentSourceMenuBudget Q :=
    (independent_coordinate_mean_word_bound Q t w hw Y).trans (independentSourceBudget_le_menu Q _ hw)
  have hreg := finite_coordinate_word_family_contDiff d H J hc hd [] H (by simp)
  change ContDiff ℝ (H : ℕ∞) (independentCoordinateMeanWord f t []) at hreg
  rw [independentCoordinateMeanWord_nil] at hreg
  refine ⟨hreg, ?_⟩
  intro r hr Y
  have hh := finite_coordinate_word_family_derivative_bound d H J hc hd
    (independentSourceMenuBudget Q) (independentSourceMenuBudget_nonneg Q) hb [] r (by simpa using hr) Y
  change ‖iteratedFDeriv ℝ r (independentCoordinateMeanWord f t []) Y‖ ≤ _ at hh
  rw [independentCoordinateMeanWord_nil] at hh
  exact hh

def IndependentParameterSourceReserve.mean {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) :
    IndependentParameterSourceReserve H (fun t _ Y => fieldCellMean (fun z => f t z Y)) where
  regular t := (independent_source_mean_contDiff_bound Q t).1.comp contDiff_snd
  periodic _ _ _ _ := rfl
  measurable Y := by
    have hm : Measurable (fun t => fieldCellMean (fun z => f t z Y)) :=
      AVRegularity.CycleComparison.Lift.fieldCellMean_parameter_measurable (fun t z => f t z Y)
        (fun z => (Q.measurable Y).comp (measurable_id.prodMk measurable_const))
        (fun t => ((Q.regular t).comp₂ contDiff_id (contDiff_const (c := Y))).continuous)
    exact hm.comp measurable_fst
  budget r := (d : ℝ) ^ r * independentSourceMenuBudget Q
  budget_nonneg _ := mul_nonneg (by positivity) (independentSourceMenuBudget_nonneg Q)
  derivative_bound r hr t X := by
    have hreg : ContDiff ℝ (r : ℕ∞) (fun Y => fieldCellMean (fun z => f t z Y)) :=
      (independent_source_mean_contDiff_bound Q t).1.of_le (by exact_mod_cast hr)
    have hL : ‖ContinuousLinearMap.snd ℝ (Vec 2) (Vec d)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        (fun U => by
          change ‖U.2‖ ≤ 1 * ‖U‖
          rw [one_mul]
          exact norm_snd_le U)
    have hb := finite_affine_derivative_norm_le
      (fun Y => fieldCellMean (fun z => f t z Y)) r hreg
      (ContinuousLinearMap.snd ℝ (Vec 2) (Vec d))
      hL 0 X
    have he : (fun U : Vec 2 × Vec d => fieldCellMean (fun z => f t z (U.2 + 0))) =
        fun U : Vec 2 × Vec d => fieldCellMean (fun z => f t z U.2) := by
      funext U
      rw [add_zero]
    change ‖iteratedFDeriv ℝ r (fun U : Vec 2 × Vec d => fieldCellMean (fun z => f t z (U.2 + 0))) X‖ ≤ _ at hb
    rw [he] at hb
    exact hb.trans ((independent_source_mean_contDiff_bound Q t).2 r hr (X.2 + 0))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Equivalent open intrinsic slices have the same covariant slow derivatives. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {H : ℕ} {U : Set (Vec 2)}

def IndependentSourceSlowSliceEqOn (L : Vec 2 →L[ℝ] P) (U : Set (Vec 2))
    (Y Z : P) (f g : ℝ → Vec 2 → P → E) : Prop :=
  ∀ t X, X ∈ U → ∀ z, f t z (L X + Y) = g t z (L X + Z)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem IndependentSourceSlowSliceEqOn.recenter
    {L : Vec 2 →L[ℝ] P} {Y Z : P} {f g : ℝ → Vec 2 → P → E}
    (he : IndependentSourceSlowSliceEqOn L U Y Z f g) (W : Vec 2) :
    IndependentSourceSlowSliceEqOn L ((fun X => X + W) ⁻¹' U)
      (L W + Y) (L W + Z) f g := by
  intro t X hX z
  have h := he t (X + W) hX z
  simpa only [map_add, add_assoc] using h

omit [BorelSpace E] [SecondCountableTopology E] in
theorem IndependentSourceSlowSliceEqOn.covariantSlow
    {L : Vec 2 →L[ℝ] P} {Y Z : P} {f g : ℝ → Vec 2 → P → E}
    (he : IndependentSourceSlowSliceEqOn L U Y Z f g) (hU : IsOpen U)
    (Qf : IndependentParameterSourceReserve H f) (Qg : IndependentParameterSourceReserve H g)
    (hH : 1 ≤ H) (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentSourceCovariantSlow L A i f) (independentSourceCovariantSlow L A i g) := by
  intro t X hX z
  rw [← independent_covariant_slow_affine_slice Qf hH L A Y i t z X,
    ← independent_covariant_slow_affine_slice Qg hH L A Z i t z X]
  have hs : SlowOpenFieldEq U (fun X z => f t z (L X + Y))
      (fun X z => g t z (L X + Z)) := he t
  change AVRegularity.slowPartial i (fun X z => f t z (L X + Y)) X z +
      A (basisVec i) • f t z (L X + Y) =
    AVRegularity.slowPartial i (fun X z => g t z (L X + Z)) X z +
      A (basisVec i) • g t z (L X + Z)
  rw [hs.slowPartial hU i X hX z, he t X hX z]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem IndependentSourceSlowSliceEqOn.fastPartial
    {L : Vec 2 →L[ℝ] P} {Y Z : P} {f g : ℝ → Vec 2 → P → E}
    (he : IndependentSourceSlowSliceEqOn L U Y Z f g) (i : Fin 2) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (fun t z W => fderiv ℝ (fun w => f t w W) z (basisVec i))
      (fun t z W => fderiv ℝ (fun w => g t w W) z (basisVec i)) := by
  intro t X hX z
  have hs : (fun w => f t w (L X + Y)) = fun w => g t w (L X + Z) :=
    funext (he t X hX)
  dsimp only
  rw [hs]

theorem independentSourceCovariantWord_slow_slice_congr
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (Y Z : P)
    {f g : ℝ → Vec 2 → P → E}
    (Qf : IndependentParameterSourceReserve H f) (Qg : IndependentParameterSourceReserve H g)
    (hU : IsOpen U) (he : IndependentSourceSlowSliceEqOn L U Y Z f g)
    (A : Vec 2 →L[ℝ] ℝ) (n : ℕ) (hn : n ≤ H) (α : DerivativeWord2 n) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentSourceCovariantWord L A f n α) (independentSourceCovariantWord L A g n α) := by
  induction n with
  | zero => exact he
  | succ n ih =>
    let β : DerivativeWord2 n := fun i => α i.castSucc
    exact (ih (by omega) β).covariantSlow hU
      (Qf.covariantWord n 1 (by omega) L hL A β)
      (Qg.covariantWord n 1 (by omega) L hL A β) le_rfl A (α (Fin.last n))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Time clocks, physical scalar dimensions, and restrictions preserve actual source germs. -/
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {L : Vec 2 →L[ℝ] P} {U V : Set (Vec 2)} {Y Z : P}
  {f g : ℝ → Vec 2 → P → E}

theorem IndependentSourceSlowSliceEqOn.mono
    (he : IndependentSourceSlowSliceEqOn L U Y Z f g) (hVU : V ⊆ U) :
    IndependentSourceSlowSliceEqOn L V Y Z f g := fun t X hX z => he t X (hVU hX) z

theorem IndependentSourceSlowSliceEqOn.timeReparam
    (he : IndependentSourceSlowSliceEqOn L U Y Z f g) (clock : ℝ → ℝ) :
    IndependentSourceSlowSliceEqOn L U Y Z (fun t z W => f (clock t) z W) (fun t z W => g (clock t) z W) :=
  fun t X hX z => he (clock t) X hX z

theorem IndependentSourceSlowSliceEqOn.constSmul [NormedAddCommGroup E] [NormedSpace ℝ E]
    (he : IndependentSourceSlowSliceEqOn L U Y Z f g) (c : ℝ) :
    IndependentSourceSlowSliceEqOn L U Y Z (fun t z W => c • f t z W) (fun t z W => c • g t z W) :=
  fun t X hX z => congrArg (fun v : E => c • v) (he t X hX z)

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Stored-parameter translations commute with the literal intrinsic differential operators. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def IndependentSourceTranslationInvariant (δ : P) (f : ℝ → Vec 2 → P → E) : Prop :=
  ∀ t z Y, f t z (Y + δ) = f t z Y

omit [NormedSpace ℝ P] in
theorem IndependentSourceTranslationInvariant.fastPartial {δ : P} {f : ℝ → Vec 2 → P → E}
    (h : IndependentSourceTranslationInvariant δ f) (i : Fin 2) :
    IndependentSourceTranslationInvariant δ (fun t z Y => fderiv ℝ (fun x => f t x Y) z (basisVec i)) := by
  intro t z Y
  have he : (fun x => f t x (Y + δ)) = fun x => f t x Y := funext (fun x => h t x Y)
  dsimp only
  rw [he]

theorem IndependentSourceTranslationInvariant.directional {δ : P} {f : ℝ → Vec 2 → P → E}
    (h : IndependentSourceTranslationInvariant δ f) (v : P) :
    IndependentSourceTranslationInvariant δ (fun t z Y => fderiv ℝ (f t z) Y v) := by
  intro t z Y
  have he : (fun X => f t z (X + δ)) = f t z := funext (h t z)
  have hd := congrArg (fun q => fderiv ℝ q Y) he
  rw [fderiv_comp_add_right] at hd
  exact congrArg (fun L => L v) hd

theorem IndependentSourceTranslationInvariant.covariantSlow {δ : P} {f : ℝ → Vec 2 → P → E}
    (h : IndependentSourceTranslationInvariant δ f)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2) :
    IndependentSourceTranslationInvariant δ (independentSourceCovariantSlow L A i f) := by
  intro t z Y
  dsimp only [independentSourceCovariantSlow]
  have hd := h.directional (L (basisVec i)) t z Y
  dsimp only at hd
  rw [hd, h t z Y]

theorem IndependentSourceTranslationInvariant.covariantStep {δ : P}
    (F : ℕ → ℝ → Vec 2 → P → E)
    (h : ∀ j, IndependentSourceTranslationInvariant δ (F j))
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ) (k : Fin 2) (j : ℕ) :
    IndependentSourceTranslationInvariant δ (independentCovariantCoefficientStep L A η k F j) := by
  intro t z Y
  dsimp only [independentCovariantCoefficientStep]
  have hd := (h j).fastPartial k t z Y
  dsimp only at hd
  rw [hd]
  by_cases hj : j = 0
  · rw [ite_eq_left hj, ite_eq_left hj]
  · rw [ite_eq_right hj, ite_eq_right hj, (h (j - 1)).covariantSlow L A k t z Y]

theorem IndependentSourceTranslationInvariant.covariantList {δ : P} {f : ℝ → Vec 2 → P → E}
    (h : IndependentSourceTranslationInvariant δ f)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ) (w : List (Fin 2)) (j : ℕ) :
    IndependentSourceTranslationInvariant δ (independentCovariantListCoefficients L A η w f j) := by
  have hbase : ∀ j, IndependentSourceTranslationInvariant δ
      ((fun j => if j = 0 then f else fun _ _ _ => 0) j) := by
    intro j t z Y
    by_cases hj : j = 0
    · simp only [ite_eq_left hj]
      exact h t z Y
    · simp only [ite_eq_right hj]
  have hfold : ∀ w : List (Fin 2), ∀ F : ℕ → ℝ → Vec 2 → P → E,
      (∀ j, IndependentSourceTranslationInvariant δ (F j)) →
      ∀ j, IndependentSourceTranslationInvariant δ
        (w.foldl (fun Q k => independentCovariantCoefficientStep L A η k Q) F j) := by
    intro w
    induction w with
    | nil => intro F hF j; exact hF j
    | cons k w ih =>
      intro F hF j
      exact ih _ (fun j => IndependentSourceTranslationInvariant.covariantStep F hF L A η k j) j
  exact hfold w _ hbase j

omit [NormedSpace ℝ P] in
theorem IndependentSourceTranslationInvariant.smul {δ : P}
    {a : ℝ → Vec 2 → P → ℝ} {f : ℝ → Vec 2 → P → E}
    (ha : IndependentSourceTranslationInvariant δ a) (hf : IndependentSourceTranslationInvariant δ f) :
    IndependentSourceTranslationInvariant δ (fun t z Y => a t z Y • f t z Y) := by
  intro t z Y
  dsimp only
  rw [ha t z Y, hf t z Y]

theorem IndependentSourceTranslationInvariant.covariantWord {δ : P} {f : ℝ → Vec 2 → P → E}
    (h : IndependentSourceTranslationInvariant δ f)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (n : ℕ) (α : DerivativeWord2 n) :
    IndependentSourceTranslationInvariant δ (independentSourceCovariantWord L A f n α) := by
  induction n with
  | zero => exact h
  | succ n ih => exact (ih (fun i => α i.castSucc)).covariantSlow L A (α (Fin.last n))

omit [NormedSpace ℝ P] in
theorem IndependentSourceTranslationInvariant.cellMean {δ : P} {f : ℝ → Vec 2 → P → E}
    (h : IndependentSourceTranslationInvariant δ f) :
    IndependentSourceTranslationInvariant δ (fun t _ Y => fieldCellMean (fun z => f t z Y)) := by
  intro t z Y
  dsimp only
  congr 1
  funext w
  exact h t w Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! Unit cutoff germs at two comparison points give a common open intrinsic slice. -/
@[expose] public noncomputable section
open Homogenization Set Filter Topology
namespace AVRegularity.EntryWeakProofs

theorem independent_unit_cutoff_slice_neighborhood {d : ℕ}
    (χ ψ : Vec d → ℝ) (L : Vec 2 →L[ℝ] Vec d) (Y Z : Vec d)
    (hχ : χ =ᶠ[𝓝 Y] fun _ => 1) (hψ : ψ =ᶠ[𝓝 Z] fun _ => 1) :
    ∃ U : Set (Vec 2), IsOpen U ∧ (0 : Vec 2) ∈ U ∧
      (∀ X ∈ U, χ (L X + Y) = 1) ∧ (∀ X ∈ U, ψ (L X + Z) = 1) := by
  have hY : Tendsto (fun X : Vec 2 => L X + Y) (𝓝 0) (𝓝 Y) := by
    have hc : Continuous (fun X : Vec 2 => L X + Y) := L.continuous.add continuous_const
    simpa only [map_zero, zero_add] using hc.tendsto (0 : Vec 2)
  have hZ : Tendsto (fun X : Vec 2 => L X + Z) (𝓝 0) (𝓝 Z) := by
    have hc : Continuous (fun X : Vec 2 => L X + Z) := L.continuous.add continuous_const
    simpa only [map_zero, zero_add] using hc.tendsto (0 : Vec 2)
  have hb : ∀ᶠ X in 𝓝 (0 : Vec 2), χ (L X + Y) = 1 ∧ ψ (L X + Z) = 1 :=
    (hχ.comp_tendsto hY).and (hψ.comp_tendsto hZ)
  obtain ⟨U, hsub, hU, hzero⟩ := mem_nhds_iff.mp hb
  exact ⟨U, hU, hzero, fun X hX => (hsub hX).1, fun X hX => (hsub hX).2⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine classical carriers and produced joint jets supply the next independent source reserve. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs
variable {d : ℕ}

def classicalWindowIndependentSourceReserve (S K : ℕ) (hK : 2 ≤ K) (a b : ℝ)
    (u : Vec d → ℝ → TorusHk K ℂ) (hu : ∀ Y, StronglyMeasurable (u Y))
    (hr : ∀ t ∈ Icc a b, ContDiff ℝ (S : ℕ∞) (fun X : Vec d × Vec 2 =>
      iteratedFDeriv ℝ 0 (realClassicalLift K (mapTorusHk Complex.reCLM (u X.1 t))) X.2))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n, n ≤ S → ∀ t ∈ Icc a b, ∀ X : Vec d × Vec 2,
      ‖iteratedFDeriv ℝ n (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ 0
        (realClassicalLift K (mapTorusHk Complex.reCLM (u X.1 t))) X.2) X‖ ≤ B n) :
    IndependentParameterSourceReserve S (independentTimeWindowSource (Ioc a b)
      (fun t z Y => realClassicalLift K (mapTorusHk Complex.reCLM (u Y t)) z)) := by
  exact windowIndependentReserveOfZeroFastJets S (Ioc a b) measurableSet_Ioc
    (fun t Y z => realClassicalLift K (mapTorusHk Complex.reCLM (u Y t)) z)
    (fun t ht => hr t ⟨ht.1.le, ht.2⟩)
    (fun t ht Y => realClassicalLift_periodic K _)
    (fun Y => realHigherCarrier_lift_joint_measurable K hK (u Y) (hu Y))
    B hB (fun n hn t ht X => hb n hn t ⟨ht.1.le, ht.2⟩ X)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The physical-to-cell clock changes no spatial or stored-family jet budget. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {H : ℕ}

def IndependentParameterSourceReserve.timeReparam {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (clock : ℝ → ℝ) (hclock : Measurable clock) :
    IndependentParameterSourceReserve H (fun t z Y => f (clock t) z Y) where
  regular t := Q.regular (clock t)
  periodic t := Q.periodic (clock t)
  measurable Y := (Q.measurable Y).comp ((hclock.comp measurable_fst).prodMk measurable_snd)
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound n hn t X := Q.derivative_bound n hn (clock t) X

omit [MeasurableSpace E] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem IndependentSourceTranslationInvariant.timeReparam {δ : P} {f : ℝ → Vec 2 → P → E}
    (hf : IndependentSourceTranslationInvariant δ f) (clock : ℝ → ℝ) :
    IndependentSourceTranslationInvariant δ (fun t z Y => f (clock t) z Y) :=
  fun t z Y => hf (clock t) z Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! Coefficient productions (`IndependentScalarCoefficientProduction`) retain the full independent
parameters, exact copies of the coefficient, centering and support. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

structure IndependentScalarCoefficientProduction {ι : Type*} (d H n : ℕ)
    (a b : ℝ) (U : Set (Vec d)) (c : Vec d → LiftCoeff ι (fun _ => ℝ))
    (slowPoint : Vec d → Vec 2) (m : ℕ) (α : DerivativeWord2 m) (v u : ι) (θ C : ℝ) where
  field : ℝ → Vec 2 → Vec d → ℝ
  reserve : IndependentParameterSourceReserve H field
  bound : ∀ k ≤ H, reserve.budget k ≤ θ * C
  copy : ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
    field t z Y = c Y m α t (slowPoint Y) z v u 1
  mean_zero : 1 ≤ n → ∀ t Y, fieldCellMean (fun z => field t z Y) = 0
  past_zero : 1 ≤ n → ∀ t, t ≤ a → ∀ z Y, field t z Y = 0

variable {ι : Type*} {d H n m : ℕ} {a b θ C : ℝ} {U : Set (Vec d)}
  {c : Vec d → LiftCoeff ι (fun _ => ℝ)} {slowPoint : Vec d → Vec 2}
  {α : DerivativeWord2 m} {v u : ι}

def IndependentScalarCoefficientProduction.monoOrder
    (P : IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u θ C)
    (H' : ℕ) (hH : H' ≤ H) :
    IndependentScalarCoefficientProduction d H' n a b U c slowPoint m α v u θ C where
  field := P.field
  reserve := P.reserve.restrictOrder H' hH
  bound k hk := P.bound k (hk.trans hH)
  copy := P.copy
  mean_zero := P.mean_zero
  past_zero := P.past_zero

def IndependentScalarCoefficientProduction.enlargeBudget
    (P : IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u θ C)
    (C' : ℝ) (hC : C ≤ C') (hθ : 0 ≤ θ) :
    IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u θ C' where
  field := P.field
  reserve := P.reserve
  bound k hk := (P.bound k hk).trans (mul_le_mul_of_nonneg_left hC hθ)
  copy := P.copy
  mean_zero := P.mean_zero
  past_zero := P.past_zero

end AVRegularity.EntryWeakProofs
end
end
end
