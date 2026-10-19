-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentCenteredChildReanchorCoordinates
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
import AVRegularity.CycleEvolution.FibreCoefficientStage

@[expose] public noncomputable section

section
namespace AVRegularity.EntryWeakProofs

/-! Birth-scale centers enter the parent chart through a contraction by the birth-to-parent ratio. -/

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def centeredChildScaleCenterCoordinates (ell : ℝ) :
    (P × (V × (V × V))) →L[ℝ] (P × (V × (V × V))) :=
  (ContinuousLinearMap.fst ℝ P (V × (V × V))).prod
    ((ell • centeredChildCenterProjection).prod
      (centeredChildPhaseProjection.prod centeredChildSlowProjection))

theorem centeredChildScaleCenterCoordinates_apply (ell : ℝ) (Y : P × (V × (V × V))) :
    centeredChildScaleCenterCoordinates ell Y = (Y.1, ell • Y.2.1, Y.2.2.1, Y.2.2.2) := rfl

theorem centeredChildScaleCenterCoordinates_norm_le (ell : ℝ) (hell : |ell| ≤ 1) :
    ‖centeredChildScaleCenterCoordinates (P := P) (V := V) ell‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, centeredChildScaleCenterCoordinates_apply]
  have hcenter : ‖ell • Y.2.1‖ ≤ ‖Y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right hell (norm_nonneg _)).trans_eq (one_mul _)).trans
      ((norm_fst_le Y.2).trans (norm_snd_le Y))
  have hphase := (norm_fst_le Y.2.2).trans ((norm_snd_le Y.2).trans (norm_snd_le Y))
  have hslow := (norm_snd_le Y.2.2).trans ((norm_snd_le Y.2).trans (norm_snd_le Y))
  simp only [Prod.norm_def]
  exact max_le (norm_fst_le Y) (max_le hcenter (max_le hphase hslow))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Independent coordinates include only newly appended children, keeping the older history fixed. -/

/-- Each new child has two normalized center coordinates and two independent phase coordinates. -/
def independentFreshChildCoordinate {r : ℕ} (j : Fin r) (phase : Bool) (k : Fin 2) : Fin (4 * r) :=
  ⟨4 * j.val + (if phase then 2 else 0) + k.val, by split <;> omega⟩

def independentFreshChildProjection {r : ℕ} (j : Fin r) (phase : Bool) :
    Vec (4 * r) →L[ℝ] Vec 2 :=
  ContinuousLinearMap.pi (fun k => ContinuousLinearMap.proj (independentFreshChildCoordinate j phase k))

theorem independentFreshChildProjection_apply {r : ℕ} (j : Fin r) (phase : Bool)
    (Y : Vec (4 * r)) (k : Fin 2) :
    independentFreshChildProjection j phase Y k = Y (independentFreshChildCoordinate j phase k) := rfl

theorem independentFreshChildProjection_norm_le {r : ℕ} (j : Fin r) (phase : Bool) :
    ‖independentFreshChildProjection j phase‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
  intro k
  exact norm_le_pi_norm Y (independentFreshChildCoordinate j phase k)

/-- The center is normalized by its birth length; the phase remains independent. -/
def independentFreshChild {r : ℕ} (birthLength : Fin r → ℝ) (j : Fin r)
    (Y : Vec (4 * r)) : ChainChild :=
  ⟨birthLength j • independentFreshChildProjection j false Y,
    independentFreshChildProjection j true Y⟩

theorem independentFreshChild_center {r : ℕ} (birthLength : Fin r → ℝ)
    (j : Fin r) (Y : Vec (4 * r)) :
    (independentFreshChild birthLength j Y).center =
      birthLength j • independentFreshChildProjection j false Y := rfl

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Exact triangular word equations and genuine primitive jets produce energy-continuous word inverses. -/

variable {d H : ℕ}

theorem coordinate_word_inverse_family_continuous (K : ℕ) (hK : K + 1 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ K → IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y)) :
    ∀ w, w.length ≤ K → ∀ Y,
      Tendsto (fun X => cellEnergyNorm univ (c w X - c w Y)) (𝓝 Y) (𝓝 0) := by
  have hp (w : List (Fin d)) (hw : w.length ≤ K) (Y : Vec d) :=
    coordinate_word_primitive_data QG Qf QF w (by omega) Y
  have hflux (w : List (Fin d)) (hw : w.length ≤ K) (Y : Vec d) :=
    independentWordMetricFlux_finite (fun p => coordinateMetricWord G p Y)
      (fun p => c p Y) w
      (fun p hm => (hp p.1 (by
        have hl := (independentWordForcing_lengths w p hm).2.1
        omega) Y).1)
      (fun p hm => (hp p.1 (by
        have hl := (independentWordForcing_lengths w p hm).2.1
        omega) Y).2.1)
      (fun p hm => (hsol Y p.2 (by
        have hl := (independentWordForcing_lengths w p hm).2.2
        omega)).2.2)
      (fun p hm => (hsol Y p.2 (by
        have hl := (independentWordForcing_lengths w p hm).2.2
        omega)).1.2.2.2.1)
  intro w hw
  generalize he : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    intro Y
    apply cellInverse_norm_continuous (fun X t _ => G t X)
      (fun X => coordinateSourceWord f w X)
      (fun X => coordinateSourceWord F w X + independentWordMetricFlux
        (fun p => coordinateMetricWord G p X) (fun p => c p X) w)
      (c w) hv QG.metric
      (fun X => ⟨(hp w hw X).2.2.2.2.1, (hp w hw X).2.2.1⟩)
      (fun X => ⟨(hp w hw X).2.2.2.2.2.add (hflux w hw X).1,
        (cellUlNorm_add univ _ _ (hp w hw X).2.2.2.2.2 (hflux w hw X).1).trans_lt
          (ENNReal.add_lt_top.mpr ⟨(hp w hw X).2.2.2.1, (hflux w hw X).2⟩)⟩)
      (fun X => hsol X w hw) Y (QG.norm_difference_tendsto_zero (by omega) Y)
      (coordinate_source_word_norm_continuous Qf w (by omega) Y)
    apply cellUlNorm_add_tendsto (𝓝 Y) (fun X => coordinateSourceWord F w X)
      (fun X => independentWordMetricFlux (fun p => coordinateMetricWord G p X) (fun p => c p X) w)
      _ _ (fun X => (hp w hw X).2.2.2.2.2) (fun X => (hflux w hw X).1)
      (hp w hw Y).2.2.2.2.2 (hflux w hw Y).1
      (coordinate_source_word_norm_continuous QF w (by omega) Y)
    apply (independent_flux_list_tendsto (independentWordForcing w) (𝓝 Y)
      (fun p X => cellMetricFlux (coordinateMetricWord G p.1 X) (c p.2 X))
      (fun p => cellMetricFlux (coordinateMetricWord G p.1 Y) (c p.2 Y)) ?_ ?_ ?_).2.2
    · intro p hm X
      exact cellMetricFlux_aestronglyMeasurable univ _ _
        (hp p.1 (by have hl := (independentWordForcing_lengths w p hm).2.1; omega) X).2.1
        (hsol X p.2 (by have hl := (independentWordForcing_lengths w p hm).2.2; omega)).1.2.2.2.1
    · intro p hm
      exact cellMetricFlux_aestronglyMeasurable univ _ _
        (hp p.1 (by have hl := (independentWordForcing_lengths w p hm).2.1; omega) Y).2.1
        (hsol Y p.2 (by have hl := (independentWordForcing_lengths w p hm).2.2; omega)).1.2.2.2.1
    · intro p hm
      have hl := independentWordForcing_lengths w p hm
      have hg : p.1.length ≤ K := by omega
      have hc : p.2.length ≤ K := by omega
      exact cellMetricFlux_tendsto (𝓝 Y) (fun X => coordinateMetricWord G p.1 X)
        (coordinateMetricWord G p.1 Y) (c p.2) (c p.2 Y)
        (fun X => ⟨(hp p.1 hg X).1, (hp p.1 hg X).2.1⟩)
        ⟨(hp p.1 hg Y).1, (hp p.1 hg Y).2.1⟩ (hsol Y p.2 hc).2.2
        (fun X => (hsol X p.2 hc).1.2.2.2.1) (hsol Y p.2 hc).1.2.2.2.1
        (coordinate_metric_word_norm_continuous QG p.1 (by omega) Y)
        (ih p.2.length (by omega) p.2 hc rfl Y)

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Earlier centered chart jets produce the full independent return-map jets. -/

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def independentCenteredReturnCost (K : ℕ) (C R : ℝ) : ℝ :=
  K.factorial * (max C ((2 : ℝ) ^ K * C * (R + K))) ^ (K + 1)

theorem independentCenteredReturnCost_ge_one (K : ℕ) (C R : ℝ) (hC : 1 ≤ C) :
    1 ≤ independentCenteredReturnCost K C R :=
  positiveJetCompositionBudget_ge_one K _ (hC.trans (le_max_left _ _))

theorem independentCenteredReturn_positive_jet_bound (Fi Fa : P × V → V)
    (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi) (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (C : ℝ) (hC : 1 ≤ C)
    (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (Y : P × (V × V))
    (R : ℝ) (hY : ‖Y.2.2‖ ≤ R)
    (hbFa : ∀ i, 1 ≤ i → i ≤ K → ‖iteratedFDeriv ℝ i Fa (Y.1, Y.2.1)‖ ≤ C)
    (hbFi : ∀ i, 1 ≤ i → i ≤ K + 1 →
      ∀ Z ∈ segment ℝ (Y.1, Fa (Y.1, Y.2.1))
        (Y.1, Fa (Y.1, Y.2.1) + θ • Y.2.2), ‖iteratedFDeriv ℝ i Fi Z‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (independentCenteredReturn Fi Fa θ) Y‖ ≤
      independentCenteredReturnCost K C R := by
  let F : P × (V × V) → V := fun Z =>
    θ⁻¹ • (Fi (Z.1, Z.2.1 + θ • Z.2.2) - Fi (Z.1, Z.2.1))
  let G := centeredReturnInnerMap Fa
  let B := max C ((2 : ℝ) ^ K * C * (R + K))
  have hB : 1 ≤ B := hC.trans (le_max_left _ _)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    independentCenteredReturn_contDiff Fi (fun Z => Z.2) hFi contDiff_snd θ
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := centeredReturnInnerMap_contDiff Fa hFa
  have he : independentCenteredReturn Fi Fa θ = F ∘ G := rfl
  rw [he]
  apply finite_positive_jet_composition_bound F G hF hG K n hn hnK Y B hB
  · intro i _ hiK
    have hh := independent_spatial_difference_joint_menu_bound Fi K i
      (hFi.of_le (by simp)) hiK C (zero_le_one.trans hC) θ hθ hθ₁
      Y.1 (Fa (Y.1, Y.2.1)) Y.2.2 R hY hbFi
    exact hh.trans (le_max_right _ _)
  · intro i hi hiK
    exact (centeredReturnInnerMap_positive_jet_bound Fa hFa i hi Y C hC
      (hbFa i hi hiK)).trans (le_max_left _ _)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Every literal finite child family is represented by normalized independent coordinates. -/

def independentFreshChildPacking {r : ℕ} (birthLength : Fin r → ℝ)
    (c : Fin r → ChainChild) : Vec (4 * r) := fun i =>
  let j : Fin r := ⟨i.val / 4, by have := i.is_lt; omega⟩
  if hi : i.val % 4 < 2 then
    (birthLength j)⁻¹ * (c j).center ⟨i.val % 4, hi⟩
  else (c j).phase ⟨i.val % 4 - 2, by omega⟩

theorem independentFreshChildPacking_center {r : ℕ} (birthLength : Fin r → ℝ)
    (c : Fin r → ChainChild) (j : Fin r) :
    independentFreshChildProjection j false (independentFreshChildPacking birthLength c) =
      (birthLength j)⁻¹ • (c j).center := by
  funext k
  simp only [independentFreshChildProjection_apply, independentFreshChildPacking,
    independentFreshChildCoordinate, Bool.false_eq_true, ite_false]
  have hd : (4 * j.val + 0 + k.val) / 4 = j.val := by omega
  have hm : (4 * j.val + 0 + k.val) % 4 = k.val := by omega
  simp only [hd, hm, dite_eq_left k.is_lt, Pi.smul_apply, smul_eq_mul]

theorem independentFreshChildPacking_phase {r : ℕ} (birthLength : Fin r → ℝ)
    (c : Fin r → ChainChild) (j : Fin r) :
    independentFreshChildProjection j true (independentFreshChildPacking birthLength c) =
      (c j).phase := by
  funext k
  simp only [independentFreshChildProjection_apply, independentFreshChildPacking,
    independentFreshChildCoordinate, ite_true]
  have hd : (4 * j.val + 2 + k.val) / 4 = j.val := by omega
  have hm : (4 * j.val + 2 + k.val) % 4 = 2 + k.val := by omega
  simp only [hd, hm, dite_eq_right (by omega : ¬ 2 + k.val < 2)]
  have hk : (⟨2 + k.val - 2, by omega⟩ : Fin 2) = k := by
    apply Fin.ext
    simp only [Nat.add_sub_cancel_left]
  rw [hk]

theorem independentFreshChildPacking_reconstruct {r : ℕ} (birthLength : Fin r → ℝ)
    (hbirth : ∀ j, birthLength j ≠ 0) (c : Fin r → ChainChild) (j : Fin r) :
    independentFreshChild birthLength j (independentFreshChildPacking birthLength c) = c j := by
  cases hc : c j with
  | mk center phase =>
    simp only [independentFreshChild, independentFreshChildPacking_center,
      independentFreshChildPacking_phase, hc, smul_smul, mul_inv_cancel₀ (hbirth j), one_smul]

/-! The full intrinsic vector separates slow coordinates from the finite fresh history. -/

def independentFreshParameterCoordinates (r : ℕ) :
    Vec (2 + 4 * r) →L[ℝ] Vec (4 * r) × Vec 2 :=
  (independentStoredParameterProjection (4 * r)).prod (independentIntrinsicSlowProjection (4 * r))

theorem independentFreshParameterCoordinates_apply (r : ℕ) (Y : Vec (2 + 4 * r)) :
    independentFreshParameterCoordinates r Y =
      (independentStoredParameterProjection (4 * r) Y, independentIntrinsicSlowProjection (4 * r) Y) := rfl

theorem independentFreshParameterCoordinates_norm_le (r : ℕ) :
    ‖independentFreshParameterCoordinates r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, independentFreshParameterCoordinates_apply, Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
    intro i
    exact norm_le_pi_norm Y (i.natAdd 2)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
    intro i
    exact norm_le_pi_norm Y (i.castAdd (4 * r))

/-! Coordinate transport commutes with splitting intrinsic and stored variables. -/

theorem independentIntrinsicParameterPacking_cast {r s : ℕ} (he : r = s)
    (X : Vec 2) (P : Vec (4 * r)) :
    Eq.rec (motive := fun n _ => Vec (2 + 4 * n))
      (independentIntrinsicParameterPacking (4 * r) X P) he =
      independentIntrinsicParameterPacking (4 * s) X
        (Eq.rec (motive := fun n _ => Vec (4 * n)) P he) := by
  subst s
  rfl

theorem independentFreshChildProjection_cast_bound {r s : ℕ} (he : r = s)
    (P : Vec (4 * r)) (C : ℝ)
    (hP : ∀ j, ‖independentFreshChildProjection j false P‖ ≤ C) :
    ∀ j, ‖independentFreshChildProjection j false
      (Eq.rec (motive := fun n _ => Vec (4 * n)) P he)‖ ≤ C := by
  subst s
  exact hP

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Introducing an independent child phase preserves the native centered-return budget. -/

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def independentCenteredChildReturn (Fi Fa : P × V → V) (θ : ℝ)
    (Y : P × (V × (V × V))) : V :=
  independentCenteredReturn Fi Fa θ (Y.1, Y.2.1, Y.2.2.2)

theorem independentCenteredChildReturn_contDiff (Fi Fa : P × V → V)
    (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi) (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) (θ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentCenteredChildReturn Fi Fa θ) :=
  (independentCenteredReturn_contDiff Fi Fa hFi hFa θ).comp (centeredChildReturnProjection (P := P) (V := V)).contDiff

theorem independentCenteredChildReturn_positive_jet_bound (Fi Fa : P × V → V)
    (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi) (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (C : ℝ) (hC : 1 ≤ C)
    (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1) (Y : P × (V × (V × V)))
    (R : ℝ) (hY : ‖Y.2.2.2‖ ≤ R)
    (hbFa : ∀ i, 1 ≤ i → i ≤ K → ‖iteratedFDeriv ℝ i Fa (Y.1, Y.2.1)‖ ≤ C)
    (hbFi : ∀ i, 1 ≤ i → i ≤ K + 1 →
      ∀ Z ∈ segment ℝ (Y.1, Fa (Y.1, Y.2.1))
        (Y.1, Fa (Y.1, Y.2.1) + θ • Y.2.2.2), ‖iteratedFDeriv ℝ i Fi Z‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (independentCenteredChildReturn Fi Fa θ) Y‖ ≤
      independentCenteredReturnCost K C R := by
  let T := centeredChildReturnProjection (P := P) (V := V)
  have hh := finite_affine_derivative_norm_le (independentCenteredReturn Fi Fa θ) n
    ((independentCenteredReturn_contDiff Fi Fa hFi hFa θ).of_le (by simp)) T
    centeredChildReturnProjection_norm_le 0 Y
  simp only [add_zero] at hh
  exact hh.trans (independentCenteredReturn_positive_jet_bound Fi Fa hFi hFa
    K n hn hnK C hC θ hθ hθ₁ (Y.1, Y.2.1, Y.2.2.2) R hY hbFa hbFi)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Contracting the native slow scale leaves every independently stored family parameter fixed. -/

def independentIntrinsicSlowScaling (d : ℕ) (ell : ℝ) : Vec (2 + d) →L[ℝ] Vec (2 + d) :=
  ContinuousLinearMap.pi (Fin.addCases
    (fun i : Fin 2 => ell • ContinuousLinearMap.proj (i.castAdd d))
    (fun i : Fin d => ContinuousLinearMap.proj (i.natAdd 2)))

theorem independentIntrinsicSlowScaling_slow (d : ℕ) (ell : ℝ) (Y : Vec (2 + d)) :
    independentIntrinsicSlowProjection d (independentIntrinsicSlowScaling d ell Y) =
      ell • independentIntrinsicSlowProjection d Y := by
  funext i
  simp only [independentIntrinsicSlowScaling, independentIntrinsicSlowProjection,
    ContinuousLinearMap.pi_apply, Fin.addCases_left, smul_apply,
    ContinuousLinearMap.proj_apply, Pi.smul_apply]

theorem independentIntrinsicSlowScaling_stored (d : ℕ) (ell : ℝ) (Y : Vec (2 + d)) :
    independentStoredParameterProjection d (independentIntrinsicSlowScaling d ell Y) =
      independentStoredParameterProjection d Y := by
  funext i
  simp only [independentIntrinsicSlowScaling, independentStoredParameterProjection,
    ContinuousLinearMap.pi_apply, Fin.addCases_right, ContinuousLinearMap.proj_apply]

theorem independentIntrinsicSlowScaling_norm_le (d : ℕ) (ell : ℝ) (hell : |ell| ≤ 1) :
    ‖independentIntrinsicSlowScaling d ell‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [independentIntrinsicSlowScaling, ContinuousLinearMap.pi_apply, Fin.addCases_left,
      smul_apply, ContinuousLinearMap.proj_apply, norm_smul, Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right hell (norm_nonneg (Y (j.castAdd d)))).trans_eq (one_mul _)).trans
      (norm_le_pi_norm Y (j.castAdd d))
  · simpa only [independentIntrinsicSlowScaling, ContinuousLinearMap.pi_apply,
      Fin.addCases_right, ContinuousLinearMap.proj_apply] using norm_le_pi_norm Y (j.natAdd 2)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! The actual slow block and both cell coordinates spend their literal independent joint reserve. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def IndependentParameterSourceReserve.fastPartial {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H) (i : Fin 2) :
    IndependentParameterSourceReserve R (fun t z Y => fderiv ℝ (fun y => f t y Y) z (basisVec i)) := by
  have he : independentSourceFastWord f 1 (fun _ => basisVec i) =
      fun t z Y => fderiv ℝ (fun y => f t y Y) z (basisVec i) := by
    funext t z Y
    simp only [independentSourceFastWord, realWordJet, iteratedFDeriv_one_apply]
  exact (Q.fastWordReserve 1 R hR (fun _ => basisVec i)
    (fun _ => by simp [basisVec, Pi.norm_single])).congrSource he

def IndependentParameterSourceReserve.directional {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H)
    (v : P) (hv : ‖v‖ ≤ 1) :
    IndependentParameterSourceReserve R (fun t z Y => fderiv ℝ (f t z) Y v) := by
  have he : (fun t z Y => realWordJet (f t z) 1 (fun _ => v) Y) =
      fun t z Y => fderiv ℝ (f t z) Y v := by
    funext t z Y
    simp only [realWordJet, iteratedFDeriv_one_apply]
  exact (Q.wordJet 1 R hR (fun _ => v) (fun _ => hv)).congrSource he

def independentSourceCovariantSlow (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2)
    (f : ℝ → Vec 2 → P → E) (t : ℝ) (z : Vec 2) (Y : P) : E :=
  fderiv ℝ (f t z) Y (L (basisVec i)) + A (basisVec i) • f t z Y

def IndependentParameterSourceReserve.covariantSlow {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2) :
    IndependentParameterSourceReserve R (independentSourceCovariantSlow L A i f) := by
  have hi : ‖L (basisVec i)‖ ≤ 1 := (L.le_opNorm _).trans
    ((mul_le_mul hL (by simp [basisVec, Pi.norm_single]) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  exact (Q.directional R hR _ hi).add
    ((Q.restrictOrder R (by omega)).map (A (basisVec i) • ContinuousLinearMap.id ℝ E))

def IndependentParameterSourceReserve.scalarProduct {H : ℕ} {f : ℝ → Vec 2 → P → ℝ}
    {g : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (R : IndependentParameterSourceReserve H g) :
    IndependentParameterSourceReserve H (fun t z Y => f t z Y • g t z Y) :=
  Q.bilinear R (ContinuousLinearMap.lsmul ℝ ℝ)

omit [BorelSpace E] [SecondCountableTopology E] in
theorem independent_covariant_slow_affine_slice {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (hH : 1 ≤ H)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (a : P) (i : Fin 2)
    (t : ℝ) (z X : Vec 2) :
    sourceCovariantSlow A i (fun t z Y => f t z (L Y + a)) t z X =
      independentSourceCovariantSlow L A i f t z (L X + a) := by
  have hf : DifferentiableAt ℝ (f t z) (L X + a) :=
    (((Q.regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable
      (by exact_mod_cast (show H ≠ 0 by omega))) (L X + a)
  have hd := hf.hasFDerivAt.comp X (L.hasFDerivAt.add_const a)
  change HasFDerivAt (fun Y => f t z (L Y + a)) _ X at hd
  unfold sourceCovariantSlow AVRegularity.slowPartial independentSourceCovariantSlow
  rw [hd.fderiv]
  rfl

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Literal intrinsic drift and metric flux terms retain full independent parameter derivatives. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentLiftFluxCrossSource (J : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f₁ f₂ : ℝ → Vec 2 → P → ℝ) (k : Fin 2) (t : ℝ) (z : Vec 2) (Y : P) : ℝ :=
  (Real.sqrt η * v t z k) • f₁ t z Y -
    Real.sqrt η • ∑ j : Fin 2, G t Y k j • fderiv ℝ (fun y => f₁ t y Y) z (basisVec j) -
    η • ∑ j : Fin 2, G t Y k j • independentSourceCovariantSlow J A j f₂ t z Y

def independentLiftFluxCrossSourceReserve (H : ℕ)
    (J : Vec 2 →L[ℝ] P) (hJ : ‖J‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f₁ f₂ : ℝ → Vec 2 → P → ℝ)
    (QG : ∀ i j, IndependentParameterSourceReserve H (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i))
    (Q₁ : IndependentParameterSourceReserve (H + 1) f₁)
    (Q₂ : IndependentParameterSourceReserve (H + 1) f₂) (k : Fin 2) :
    IndependentParameterSourceReserve H (independentLiftFluxCrossSource J A η G v f₁ f₂ k) := by
  let L : ℝ →L[ℝ] ℝ := Real.sqrt η • ContinuousLinearMap.id ℝ ℝ
  let D := ((Qv k).map L).scalarProduct (Q₁.restrictOrder H (Nat.le_succ H))
  let F := fun j : Fin 2 => (QG k j).scalarProduct (Q₁.fastPartial H (by omega) j)
  let S := fun j : Fin 2 => (QG k j).scalarProduct (Q₂.covariantSlow H (by omega) J hJ A j)
  let LF : ℝ →L[ℝ] ℝ := (-Real.sqrt η) • ContinuousLinearMap.id ℝ ℝ
  let LS : ℝ →L[ℝ] ℝ := (-η) • ContinuousLinearMap.id ℝ ℝ
  exact ((D.add ((IndependentParameterSourceReserve.fintypeSum H _ F).map LF)).add
    ((IndependentParameterSourceReserve.fintypeSum H _ S).map LS)).congrSource (by
      funext t z Y
      simp only [L, LF, LS, independentLiftFluxCrossSource, smul_apply,
        ContinuousLinearMap.id_apply, sub_eq_add_neg, neg_smul]
      simp only [smul_eq_mul])

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Actual zero-start production from bundled natural higher source data. -/

theorem HigherSourceCarrierData.zero_production {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {K : ℕ} {src : ℝ → Vec 2 → ℂ}
    {flux : ℝ → Vec 2 → ComplexCellVector}
    (Q : HigherSourceCarrierData (Icc a b) K src flux) (V : MolecularFiniteDriftBudget P K)
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧ ‖w‖ ≤ fluxProductionConstant K * (Q.Ns + Q.Nf) := by
  have hs : ∀ t ∈ Icc a b, ‖Q.S t‖ ≤ Q.Ns + Q.Nf := fun t ht =>
    (Q.scalar_bound t ht).trans (le_add_of_nonneg_right Q.flux_budget_nonneg)
  have hf : ∀ t ∈ Icc a b, ‖Q.F t‖ ≤ Q.Ns + Q.Nf := fun t ht =>
    (Q.flux_bound t ht).trans (le_add_of_nonneg_left Q.scalar_budget_nonneg)
  exact dataActual_flux_higher_zero_carrier_bound (P := P) (src := src) (flux := flux)
    hlt Q.scalar_memLp Q.flux_memLp V.admissible K V.Cv V.nonneg V.smooth V.periodic V.bound
    Q.S Q.scalar_value Q.scalar_mean_zero Q.F Q.scalar_carrier_memLp Q.flux_carrier_memLp
    Q.flux_value V.small (Q.Ns + Q.Nf) (add_nonneg Q.scalar_budget_nonneg Q.flux_budget_nonneg)
    hs hf D hD hi

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Intrinsic slow words remain genuine operations inside the full independent parameter reserve. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def independentSourceCovariantWord (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ)
    (f : ℝ → Vec 2 → P → E) : (n : ℕ) → DerivativeWord2 n → ℝ → Vec 2 → P → E
  | 0, _ => f
  | n + 1, α => independentSourceCovariantSlow L A (α (Fin.last n))
      (independentSourceCovariantWord L A f n (fun i => α i.castSucc))

def IndependentParameterSourceReserve.covariantWord {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (n R : ℕ) (hR : n + R ≤ H)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (α : DerivativeWord2 n) :
    IndependentParameterSourceReserve R (independentSourceCovariantWord L A f n α) := by
  induction n generalizing R with
  | zero => exact Q.restrictOrder R (by omega)
  | succ n ih =>
    exact (ih (R + 1) (by omega) (fun i => α i.castSucc)).covariantSlow R
      (by omega) L hL A (α (Fin.last n))

theorem independent_covariant_word_affine_slice {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (n : ℕ) (hn : n ≤ H)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (a : P)
    (α : DerivativeWord2 n) (t : ℝ) (z X : Vec 2) :
    sourceCovariantWord A (fun t z Y => f t z (L Y + a)) n α t z X =
      independentSourceCovariantWord L A f n α t z (L X + a) := by
  induction n generalizing t z X with
  | zero => rfl
  | succ n ih =>
    let β : DerivativeWord2 n := fun i => α i.castSucc
    have he : sourceCovariantWord A (fun t z Y => f t z (L Y + a)) n β =
        fun t z X => independentSourceCovariantWord L A f n β t z (L X + a) := by
      funext t z X
      exact ih (by omega) β t z X
    change sourceCovariantSlow A (α (Fin.last n))
      (sourceCovariantWord A (fun t z Y => f t z (L Y + a)) n β) t z X = _
    rw [he]
    exact independent_covariant_slow_affine_slice
      (Q.covariantWord n 1 (by omega) L hL A β) le_rfl L A a (α (Fin.last n)) t z X

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! The genuine lower-word product rule identifies the next actual inverse derivative. -/

section
variable {d H : ℕ}

theorem coordinate_word_inverse_forcing_derivative_admissible (K : ℕ) (hK : K + 2 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    {v : ℝ → Vec 2 → Vec 2}
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ K → IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (w : List (Fin d)) (hw : w.length < K) (Y : Vec d) (i : Fin d) :
    AEStronglyMeasurable (Function.uncurry (independentWordMetricFluxDerivative
      (fun p => coordinateMetricWord G p Y) (fun p => c p Y) i w))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
    cellUlNorm univ (independentWordMetricFluxDerivative
      (fun p => coordinateMetricWord G p Y) (fun p => c p Y) i w) < ⊤ := by
  have hp (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :=
    coordinate_word_primitive_data QG Qf QF u (by omega) X
  have hc (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :
      cellEnergyNorm univ (c u X) < ⊤ ∧ ∀ a,
        AEStronglyMeasurable (fun T : ℝ × Vec 2 => c u X T.1 a T.2)
          ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    ⟨(hsol X u hu).2.2, (hsol X u hu).1.2.2.2.1⟩
  have hl p (hm : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hm
  have hL1 := independentWordMetricFluxDerivative_finite
    (fun p => coordinateMetricWord G p Y) (fun p => c p Y) i w
    (fun p hm => ⟨(hp p.1 (by have hh := hl p hm; omega) Y).1,
      (hp p.1 (by have hh := hl p hm; omega) Y).2.1⟩)
    (fun p hm => ⟨(hp (i :: p.1) (by have hh := hl p hm; simp only [List.length_cons]; omega) Y).1,
      (hp (i :: p.1) (by have hh := hl p hm; simp only [List.length_cons]; omega) Y).2.1⟩)
    (fun p hm => hc p.2 (by have hh := hl p hm; omega) Y)
    (fun p hm => hc (i :: p.2) (by have hh := hl p hm; simp only [List.length_cons]; omega) Y)
  exact hL1
end

/-! The genuine lower-word product rule identifies the next actual inverse derivative. -/

section
variable {d H : ℕ}

theorem coordinate_word_inverse_forcing_admissible (K : ℕ) (hK : K + 2 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    {v : ℝ → Vec 2 → Vec 2}
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ K → IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :
    AEStronglyMeasurable (Function.uncurry (independentWordMetricFlux
      (fun p => coordinateMetricWord G p X) (fun p => c p X) u))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
    cellUlNorm univ (independentWordMetricFlux
      (fun p => coordinateMetricWord G p X) (fun p => c p X) u) < ⊤ := by
  have hp (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :=
    coordinate_word_primitive_data QG Qf QF u (by omega) X
  have hc (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :
      cellEnergyNorm univ (c u X) < ⊤ ∧ ∀ a,
        AEStronglyMeasurable (fun T : ℝ × Vec 2 => c u X T.1 a T.2)
          ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    ⟨(hsol X u hu).2.2, (hsol X u hu).1.2.2.2.1⟩
  have hflux (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :=
    independentWordMetricFlux_finite (fun p => coordinateMetricWord G p X) (fun p => c p X) u
      (fun p hm => (hp p.1 (by have hh := independentWordForcing_lengths u p hm; omega) X).1)
      (fun p hm => (hp p.1 (by have hh := independentWordForcing_lengths u p hm; omega) X).2.1)
      (fun p hm => (hc p.2 (by have hh := independentWordForcing_lengths u p hm; omega) X).1)
      (fun p hm => (hc p.2 (by have hh := independentWordForcing_lengths u p hm; omega) X).2)
  exact hflux u hu X
end

/-! The genuine lower-word product rule identifies the next actual inverse derivative. -/

section
variable {d H : ℕ}

theorem coordinate_word_inverse_forcing_derivative_tendsto (K : ℕ) (hK : K + 2 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ K → IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (w : List (Fin d)) (hw : w.length < K) (Y : Vec d) (i : Fin d)
    (hcd : ∀ p ∈ independentWordForcing w,
      Tendsto (fun h : ℝ => cellEnergyNorm univ
        (h⁻¹ • (c p.2 (Y + h • basisVec i) - c p.2 Y) - c (i :: p.2) Y))
        (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => cellUlNorm univ
      (h⁻¹ • (independentWordMetricFlux
        (fun p => coordinateMetricWord G p (Y + h • basisVec i))
        (fun p => c p (Y + h • basisVec i)) w - independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) -
        independentWordMetricFluxDerivative
          (fun p => coordinateMetricWord G p Y) (fun p => c p Y) i w))
      (𝓝[≠] 0) (𝓝 0) := by
  let Z : ℝ → Vec d := fun h => Y + h • basisVec i
  have hZ : Tendsto Z (𝓝[≠] 0) (𝓝 Y) := by
    have hc : Continuous Z := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [Z, zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hp (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :=
    coordinate_word_primitive_data QG Qf QF u (by omega) X
  have hc (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :
      cellEnergyNorm univ (c u X) < ⊤ ∧ ∀ a,
        AEStronglyMeasurable (fun T : ℝ × Vec 2 => c u X T.1 a T.2)
          ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    ⟨(hsol X u hu).2.2, (hsol X u hu).1.2.2.2.1⟩
  have hl p (hm : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hm
  let L := fun X => independentWordMetricFlux (fun p => coordinateMetricWord G p X) (fun p => c p X) w
  let L1 := independentWordMetricFluxDerivative (fun p => coordinateMetricWord G p Y) (fun p => c p Y) i w
  have hcont := coordinate_word_inverse_family_continuous K (by omega) QG Qf QF hv c hsol
  have hLd : Tendsto (fun h : ℝ => cellUlNorm univ (h⁻¹ • (L (Z h) - L Y) - L1))
      (𝓝[≠] 0) (𝓝 0) := by
    apply independent_word_metric_flux_derivative_tendsto (𝓝[≠] (0 : ℝ)) (fun h : ℝ => h⁻¹)
      (fun p h => coordinateMetricWord G p (Z h)) (fun p => coordinateMetricWord G p Y)
      (fun p h => c p (Z h)) (fun p => c p Y) i w
    · intro p hm h
      exact ⟨(hp p.1 (by have hh := hl p hm; omega) (Z h)).1,
        (hp p.1 (by have hh := hl p hm; omega) (Z h)).2.1⟩
    · intro p hm
      exact ⟨(hp p.1 (by have hh := hl p hm; omega) Y).1,
        (hp p.1 (by have hh := hl p hm; omega) Y).2.1⟩
    · intro p hm
      exact ⟨(hp (i :: p.1) (by have hh := hl p hm; simp only [List.length_cons]; omega) Y).1,
        (hp (i :: p.1) (by have hh := hl p hm; simp only [List.length_cons]; omega) Y).2.1⟩
    · intro p hm
      exact (hc p.2 (by have hh := hl p hm; omega) Y).1
    · intro p hm h
      exact (hc p.2 (by have hh := hl p hm; omega) (Z h)).2
    · intro p hm
      exact (hc p.2 (by have hh := hl p hm; omega) Y).2
    · intro p hm
      exact (hc (i :: p.2) (by have hh := hl p hm; simp only [List.length_cons]; omega) Y).2
    · intro p hm
      exact coordinate_metric_word_quotient_tendsto QG i p.1 (by have hh := hl p hm; omega) Y
    · intro p hm
      exact (hcont p.2 (by have hh := hl p hm; omega) Y).comp hZ
    · exact hcd
  exact hLd
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Genuine admissible centers occupy a fixed inner native strip independent of the birth wavelength. -/

theorem norm_vec_two_le_sum_abs (X : Vec 2) : ‖X‖ ≤ ∑ i : Fin 2, |X i| := by
  have hS : 0 ≤ ∑ i : Fin 2, |X i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hS).2
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun k _ => abs_nonneg (X k)) (Finset.mem_univ i)

theorem normalized_center_norm_lt (e δ : ℝ) (he : 0 < e) (X : Vec 2)
    (hX : ∑ i : Fin 2, |X i| < δ * e) : ‖e⁻¹ • X‖ < δ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he)]
  have hh := mul_lt_mul_of_pos_left ((norm_vec_two_le_sum_abs X).trans_lt hX) (inv_pos.mpr he)
  exact hh.trans_eq (by rw [mul_comm δ e, ← mul_assoc, inv_mul_cancel₀ he.ne', one_mul])

theorem admissible_fresh_packing_center_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (bw : ℝ) (hbw : bw ≤ 1 / 10000) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) (j : Fin A.children.length) :
    ‖independentFreshChildProjection j false
      (independentFreshChildPacking (fun k : Fin A.children.length => D.eps (A.baseLevel + 1 + k))
        (fun k => A.children[k]) )‖ ≤ 1 / 8 := by
  rw [independentFreshChildPacking_center]
  have hc := hA.2.2.2.2.2.2 j.val j.is_lt
  have hc' : (∑ i : Fin 2, |A.children[j].center i|) <
      ((1 + 2) * bw / 4) * D.eps (A.baseLevel + 1 + j) := hc
  have hh := normalized_center_norm_lt (D.eps (A.baseLevel + 1 + j)) ((1 + 2) * bw / 4)
    (Construction.Stream.ocEpsilon_pos hΛ) A.children[j].center hc'
  exact hh.le.trans (by linarith only [hbw])

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Intrinsic derivatives retain the exact shifted primitive budget and its stored scalar factor. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem IndependentParameterSourceReserve.directional_budget {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H)
    (v : P) (hv : ‖v‖ ≤ 1) (r : ℕ) :
    (Q.directional R hR v hv).budget r = Q.budget (1 + r) := by
  unfold IndependentParameterSourceReserve.directional
  rw [IndependentParameterSourceReserve.congrSource_budget]
  rfl

theorem IndependentParameterSourceReserve.fastPartial_budget {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H) (i : Fin 2) (r : ℕ) :
    (Q.fastPartial R hR i).budget r = Q.budget (1 + r) := by
  unfold IndependentParameterSourceReserve.fastPartial
  rw [IndependentParameterSourceReserve.congrSource_budget]
  rfl

theorem IndependentParameterSourceReserve.covariantSlow_budget {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (R : ℕ) (hR : 1 + R ≤ H)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2) (r : ℕ) :
    (Q.covariantSlow R hR L hL A i).budget r = Q.budget (1 + r) +
      ‖A (basisVec i) • ContinuousLinearMap.id ℝ E‖ * Q.budget r := by
  unfold IndependentParameterSourceReserve.covariantSlow
  change (Q.directional R hR _ _).budget r + _ = _
  rw [IndependentParameterSourceReserve.directional_budget]
  rfl

theorem IndependentParameterSourceReserve.covariantSlow_uniform_budget {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (θ B : ℝ) (hb : ∀ r, r ≤ H → Q.budget r ≤ θ * B)
    (R : ℕ) (hR : 1 + R ≤ H) (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1)
    (A : Vec 2 →L[ℝ] ℝ) (i : Fin 2) (r : ℕ) (hr : r ≤ R) :
    (Q.covariantSlow R hR L hL A i).budget r ≤ θ * ((1 + ‖A‖) * B) := by
  rw [IndependentParameterSourceReserve.covariantSlow_budget]
  have hm := mul_le_mul (covariant_scalar_map_norm_le (E := E) A i)
    (hb r (by omega)) (Q.budget_nonneg r) (norm_nonneg A)
  exact (add_le_add (hb (1 + r) (by omega)) hm).trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Enlarging the center normalization length contracts every normalized center norm. -/

theorem normalized_center_norm_le_of_length_le (e f B : ℝ)
    (he : 0 < e) (hf : 0 < f) (hef : e ≤ f) (X : Vec 2)
    (hX : ‖e⁻¹ • X‖ ≤ B) : ‖f⁻¹ • X‖ ≤ B := by
  have hid : (e / f) * e⁻¹ = f⁻¹ := by
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ he.ne', one_mul]
  have hs : f⁻¹ • X = (e / f) • (e⁻¹ • X) := by
    rw [smul_smul, hid]
  have hr : e / f ≤ 1 := (div_le_one hf).mpr hef
  rw [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg he.le hf.le)]
  exact ((mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans_eq (one_mul _)).trans hX

/-! Linear source operations preserve the original stored amplitude in independent parameters. -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [SecondCountableTopology E] [SecondCountableTopology F] in
theorem IndependentParameterSourceReserve.map_uniform_budget {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (L : E →L[ℝ] F) (θ B : ℝ)
    (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B) (r : ℕ) (hr : r ≤ H) :
    (Q.map L).budget r ≤ θ * (‖L‖ * B) := by
  change ‖L‖ * Q.budget r ≤ _
  exact (mul_le_mul_of_nonneg_left (hQ r hr) (norm_nonneg L)).trans_eq (by ring)

theorem IndependentParameterSourceReserve.add_uniform_budget {H : ℕ} {f g : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (R : IndependentParameterSourceReserve H g) (θ B C : ℝ)
    (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B) (hR : ∀ r ≤ H, R.budget r ≤ θ * C)
    (r : ℕ) (hr : r ≤ H) :
    (Q.add R).budget r ≤ θ * (B + C) := by
  change Q.budget r + R.budget r ≤ _
  exact (add_le_add (hQ r hr) (hR r hr)).trans_eq (mul_add θ B C).symm

theorem IndependentParameterSourceReserve.fastPartial_uniform_budget {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f) (θ B : ℝ)
    (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B)
    (R : ℕ) (hR : 1 + R ≤ H) (i : Fin 2) (r : ℕ) (hr : r ≤ R) :
    (Q.fastPartial R hR i).budget r ≤ θ * B := by
  rw [IndependentParameterSourceReserve.fastPartial_budget]
  exact hQ (1 + r) (by omega)
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! The genuine lower-word product rule identifies the next actual inverse derivative. -/

variable {d H : ℕ}


theorem coordinate_word_inverse_derivative_step (K : ℕ) (hK : K + 2 ≤ H)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ K → IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (w : List (Fin d)) (hw : w.length < K) (Y : Vec d) (i : Fin d)
    (hcd : ∀ p ∈ independentWordForcing w,
      Tendsto (fun h : ℝ => cellEnergyNorm univ
        (h⁻¹ • (c p.2 (Y + h • basisVec i) - c p.2 Y) - c (i :: p.2) Y))
        (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => cellEnergyNorm univ
      (h⁻¹ • (c w (Y + h • basisVec i) - c w Y) - c (i :: w) Y))
      (𝓝[≠] 0) (𝓝 0) := by
  let Z : ℝ → Vec d := fun h => Y + h • basisVec i
  have hZ : Tendsto Z (𝓝[≠] 0) (𝓝 Y) := by
    have hc : Continuous Z := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [Z, zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hp (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :=
    coordinate_word_primitive_data QG Qf QF u (by omega) X
  have hflux (u : List (Fin d)) (hu : u.length ≤ K) (X : Vec d) :=
    coordinate_word_inverse_forcing_admissible K hK QG Qf QF c hsol u hu X
  let L := fun X => independentWordMetricFlux (fun p => coordinateMetricWord G p X) (fun p => c p X) w
  let L1 := independentWordMetricFluxDerivative (fun p => coordinateMetricWord G p Y) (fun p => c p Y) i w
  have hL1 := coordinate_word_inverse_forcing_derivative_admissible K hK QG Qf QF c hsol w hw Y i
  have hcont := coordinate_word_inverse_family_continuous K (by omega) QG Qf QF hv c hsol
  have hLd := coordinate_word_inverse_forcing_derivative_tendsto K hK QG Qf QF hv c hsol w hw Y i hcd
  let R := fun X => coordinateSourceWord F w X + L X
  let R1 := coordinateSourceWord F (i :: w) Y + L1
  have hR X : cellUlNorm univ (R X) < ⊤ ∧ AEStronglyMeasurable (Function.uncurry (R X))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    ⟨(cellUlNorm_add univ _ _ (hp w (by omega) X).2.2.2.2.2 (hflux w (by omega) X).1).trans_lt
      (ENNReal.add_lt_top.mpr ⟨(hp w (by omega) X).2.2.2.1, (hflux w (by omega) X).2⟩),
      (hp w (by omega) X).2.2.2.2.2.add (hflux w (by omega) X).1⟩
  have hn : (i :: w).length ≤ K := by simp only [List.length_cons]; omega
  have hR1 : cellUlNorm univ R1 < ⊤ ∧ AEStronglyMeasurable (Function.uncurry R1)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    ⟨(cellUlNorm_add univ _ _ (hp (i :: w) hn Y).2.2.2.2.2 hL1.1).trans_lt
      (ENNReal.add_lt_top.mpr ⟨(hp (i :: w) hn Y).2.2.2.1, hL1.2⟩),
      (hp (i :: w) hn Y).2.2.2.2.2.add hL1.1⟩
  have hRd : Tendsto (fun h : ℝ => cellUlNorm univ (h⁻¹ • (R (Z h) - R Y) - R1))
      (𝓝[≠] 0) (𝓝 0) := by
    have hh := cellUlNorm_add_tendsto (𝓝[≠] (0 : ℝ))
      (fun h : ℝ => h⁻¹ • (coordinateSourceWord F w (Z h) - coordinateSourceWord F w Y))
      (fun h : ℝ => h⁻¹ • (L (Z h) - L Y)) (coordinateSourceWord F (i :: w) Y) L1
      (fun h => ((hp w (by omega) (Z h)).2.2.2.2.2.sub (hp w (by omega) Y).2.2.2.2.2).const_smul h⁻¹)
      (fun h => ((hflux w (by omega) (Z h)).1.sub (hflux w (by omega) Y).1).const_smul h⁻¹)
      (hp (i :: w) hn Y).2.2.2.2.2 hL1.1
      (coordinate_source_word_quotient_tendsto QF i w (by omega) Y) hLd
    have he (h : ℝ) : h⁻¹ • (R (Z h) - R Y) =
        h⁻¹ • (coordinateSourceWord F w (Z h) - coordinateSourceWord F w Y) + h⁻¹ • (L (Z h) - L Y) := by
      dsimp only [R]
      rw [show coordinateSourceWord F w (Z h) + L (Z h) - (coordinateSourceWord F w Y + L Y) =
        (coordinateSourceWord F w (Z h) - coordinateSourceWord F w Y) + (L (Z h) - L Y) by abel,
        smul_add]
    simpa only [he, R1] using hh
  have hfinal : Tendsto (fun h : ℝ => cellEnergyNorm univ
      (h⁻¹ • (c w (Z h) - c w (Z 0)) - c (i :: w) Y)) (𝓝[≠] 0) (𝓝 0) := by
    refine cellInverse_directional_derivative_identified
      (fun h t _ => G t (Z h)) (fun h => coordinateSourceWord f w (Z h))
      (fun h => R (Z h)) (fun h => c w (Z h)) hv (fun h => QG.metric (Z h))
      (fun h => ⟨(hp w (by omega) (Z h)).2.2.1, (hp w (by omega) (Z h)).2.2.2.2.1⟩)
      (fun h => hR (Z h)) (fun h => hsol (Z h) w (by omega))
      (coordinateMetricWord G [i] Y) (coordinateSourceWord f (i :: w) Y) R1
      ⟨(hp [i] (by simp; omega) Y).1, (hp [i] (by simp; omega) Y).2.1⟩
      ⟨(hp (i :: w) hn Y).2.2.1, (hp (i :: w) hn Y).2.2.2.2.1⟩ hR1
      ?_ ?_ ?_ ?_ (c (i :: w) Y) ?_
    · simpa only [coordinateMetricWord_nil, Z, zero_smul, add_zero] using
        coordinate_metric_word_quotient_tendsto QG i [] (by simp; omega) Y
    · simpa only [Z, zero_smul, add_zero] using coordinate_source_word_quotient_tendsto Qf i w (by omega) Y
    · simpa only [Z, zero_smul, add_zero] using hRd
    · simpa only [Function.comp_def, Z, zero_smul, add_zero] using (hcont w (by omega) Y).comp hZ
    · have hh := hsol Y (i :: w) hn
      rw [independentWordMetricFlux_cons] at hh
      have he : R1 + cellMetricFlux (coordinateMetricWord G [i] Y) (c w Y) =
          coordinateSourceWord F (i :: w) Y + (cellMetricFlux (coordinateMetricWord G [i] Y) (c w Y) + L1) := by
        dsimp only [R1]
        abel
      simpa only [he, Z, zero_smul, add_zero] using hh
  simpa only [Z, zero_smul, add_zero] using hfinal

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The intrinsic full-parameter flux cross field equals the normalized native expression. -/

variable {d H : ℕ}

theorem independent_lift_flux_cross_affine
    (J : Vec 2 →L[ℝ] Vec d) (hJ : ‖J‖ ≤ 1) (offset : Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f₁ f₂ : ℝ → Vec 2 → Vec d → ℝ)
    (Q₁ : IndependentParameterSourceReserve (H + 1) f₁)
    (Q₂ : IndependentParameterSourceReserve (H + 1) f₂)
    (k : Fin 2) (t : ℝ) (z X : Vec 2) :
    normalizedLiftFluxCrossSource A η (fun t X => G t (J X + offset)) v
      (fun t z X => f₁ t z (J X + offset)) (fun t z X => f₂ t z (J X + offset)) k t z X =
      independentLiftFluxCrossSource J A η G v f₁ f₂ k t z (J X + offset) := by
  let fs₁ := fun t z X => f₁ t z (J X + offset)
  let fs₂ := fun t z X => f₂ t z (J X + offset)
  let Qs₁ := Q₁.affineSlice J hJ offset
  let Qs₂ := Q₂.affineSlice J hJ offset
  have hd₁ : DifferentiableAt ℝ (fun y => fs₁ t y X) z :=
    (((Qs₁.regular t).comp₂ contDiff_id (contDiff_const (c := X))).differentiable (by simp)) z
  have hd₂ : DifferentiableAt ℝ (fs₂ t z) X :=
    (((Qs₂.regular t).comp₂ (contDiff_const (c := z)) contDiff_id).differentiable (by simp)) X
  have hfast j : (Real.exp (A X))⁻¹ •
      (G t (J X + offset) k j • AVRegularity.fastPartial j
        (fun X z => Real.exp (A X) • fs₁ t z X) X z) =
      G t (J X + offset) k j • fderiv ℝ (fun y => f₁ t y (J X + offset)) z (basisVec j) := by
    rw [smul_comm, normalized_fastPartial_exp_smul A j fs₁ t z X hd₁]
    rfl
  have hslow j : (Real.exp (A X))⁻¹ •
      (G t (J X + offset) k j • AVRegularity.slowPartial j
        (fun X z => Real.exp (A X) • fs₂ t z X) X z) =
      G t (J X + offset) k j • independentSourceCovariantSlow J A j f₂ t z (J X + offset) := by
    rw [smul_comm, normalized_slowPartial_exp_smul A j fs₂ t z X hd₂,
      independent_covariant_slow_affine_slice Q₂ (by omega) J A offset j t z X]
  have hdrift : (Real.exp (A X))⁻¹ •
      ((Real.sqrt η * v t z k) • (Real.exp (A X) • fs₁ t z X)) =
      (Real.sqrt η * v t z k) • fs₁ t z X := by
    rw [smul_comm ((Real.exp (A X))⁻¹) (Real.sqrt η * v t z k),
      smul_smul (Real.exp (A X))⁻¹ (Real.exp (A X)),
      inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
  change (Real.exp (A X))⁻¹ •
    (((Real.sqrt η * v t z k) • (Real.exp (A X) • fs₁ t z X) -
      Real.sqrt η • ∑ j : Fin 2, G t (J X + offset) k j •
        AVRegularity.fastPartial j (fun X z => Real.exp (A X) • fs₁ t z X) X z) -
      η • ∑ j : Fin 2, G t (J X + offset) k j •
        AVRegularity.slowPartial j (fun X z => Real.exp (A X) • fs₂ t z X) X z) = _
  rw [smul_sub, smul_sub, hdrift, smul_comm ((Real.exp (A X))⁻¹) (Real.sqrt η),
    smul_comm ((Real.exp (A X))⁻¹) η]
  simp only [Finset.smul_sum, hfast, hslow, independentLiftFluxCrossSource]
  rfl

end AVRegularity.EntryWeakProofs
end
