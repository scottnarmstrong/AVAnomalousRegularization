-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentCovariantOperations

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Every finite covariant coefficient depends only on its open intrinsic slice. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {H : ℕ} {U : Set (Vec 2)}

omit [BorelSpace E] [SecondCountableTopology E] in
theorem independentCovariantCoefficientStep_slow_slice_congr
    (L : Vec 2 →L[ℝ] P) (Y Z : P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (F G : ℕ → ℝ → Vec 2 → P → E)
    (QF : ∀ i, IndependentParameterSourceReserve (H + 1) (F i))
    (QG : ∀ i, IndependentParameterSourceReserve (H + 1) (G i))
    (hU : IsOpen U) (he : ∀ i, IndependentSourceSlowSliceEqOn L U Y Z (F i) (G i))
    (k : Fin 2) (j : ℕ) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentCovariantCoefficientStep L A η k F j)
      (independentCovariantCoefficientStep L A η k G j) := by
  intro t X hX z
  dsimp only [independentCovariantCoefficientStep]
  have hfast := (he j).fastPartial k t X hX z
  dsimp only at hfast
  rw [hfast]
  by_cases hj : j = 0
  · simp only [ite_eq_left hj]
  · have hslow := (he (j - 1)).covariantSlow hU (QF (j - 1)) (QG (j - 1)) (by omega) A k t X hX z
    rw [ite_eq_right hj, ite_eq_right hj, hslow]

theorem independentCovariantListCoefficients_slow_slice_congr
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (Y Z : P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    {f g : ℝ → Vec 2 → P → E}
    (Qf : IndependentParameterSourceReserve H f) (Qg : IndependentParameterSourceReserve H g)
    (hU : IsOpen U) (he : IndependentSourceSlowSliceEqOn L U Y Z f g)
    (w : List (Fin 2)) (hw : w.length ≤ H) (j : ℕ) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentCovariantListCoefficients L A η w f j)
      (independentCovariantListCoefficients L A η w g j) := by
  induction w using List.reverseRecOn generalizing j with
  | nil =>
    intro t X hX z
    by_cases hj : j = 0
    · simpa only [independentCovariantListCoefficients_nil, ite_eq_left hj] using he t X hX z
    · simp only [independentCovariantListCoefficients_nil, ite_eq_right hj]
  | append_singleton w k ih =>
    have hroom : w.length + 1 ≤ H := by
      simpa only [List.length_append, List.length_singleton] using hw
    rw [independentCovariantListCoefficients_append_singleton,
      independentCovariantListCoefficients_append_singleton]
    exact independentCovariantCoefficientStep_slow_slice_congr (H := 0) L Y Z A η _ _
      (fun i => Qf.covariantList 1 L hL A η w hroom i)
      (fun i => Qg.covariantList 1 L hL A η w hroom i)
      hU (fun i => ih (by omega) i) k j

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Centering an actual forcing retains its finite joint derivative budget. -/

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def IndependentParameterSourceReserve.center {H : ℕ} {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) :
    IndependentParameterSourceReserve H (fun t z Y => f t z Y - fieldCellMean (fun x => f t x Y)) := by
  let L : E →L[ℝ] E := -ContinuousLinearMap.id ℝ E
  have he : (fun t z Y => f t z Y + L (fieldCellMean (fun x => f t x Y))) =
      fun t z Y => f t z Y - fieldCellMean (fun x => f t x Y) := by
    funext t z Y
    simp only [L, neg_apply, ContinuousLinearMap.id_apply, sub_eq_add_neg]
  exact (Q.add (Q.mean.map L)).congrSource he

theorem IndependentParameterSourceReserve.center_budget {H : ℕ}
    {f : ℝ → Vec 2 → Vec d → E} (Q : IndependentParameterSourceReserve H f) (n : ℕ) :
    Q.center.budget n = Q.budget n + ‖ContinuousLinearMap.id ℝ E‖ *
      ((d : ℝ) ^ n * independentSourceMenuBudget Q) := by
  unfold IndependentParameterSourceReserve.center
  rw [IndependentParameterSourceReserve.congrSource_budget]
  change Q.budget n + ‖-ContinuousLinearMap.id ℝ E‖ * _ = _
  rw [norm_neg]
  rfl

variable [CompleteSpace E]

omit [BorelSpace E] [SecondCountableTopology E] in
theorem IndependentParameterSourceReserve.center_mean_zero {H : ℕ}
    {f : ℝ → Vec 2 → Vec d → E} (Q : IndependentParameterSourceReserve H f)
    (t : ℝ) (Y : Vec d) :
    fieldCellMean (fun z => f t z Y - fieldCellMean (fun x => f t x Y)) = 0 := by
  have hf : Continuous (fun z => f t z Y) :=
    ((Q.regular t).comp₂ contDiff_id (contDiff_const (c := Y))).continuous
  rw [fieldCellMean_sub hf continuous_const, fieldCellMean_const, sub_self]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Centering discards any fast-constant term, without estimating its parameter derivatives. -/

variable {d H : ℕ} {f : ℝ → Vec 2 → Vec d → ℝ}

theorem independent_center_add_fast_constant (Q : IndependentParameterSourceReserve H f)
    (c : ℝ → Vec d → ℝ) (t : ℝ) (z : Vec 2) (Y : Vec d) :
    f t z Y + c t Y - fieldCellMean (fun w => f t w Y + c t Y) =
      f t z Y - fieldCellMean (fun w => f t w Y) := by
  have hf : Continuous (fun w => f t w Y) :=
    ((Q.regular t).comp₂ contDiff_id (contDiff_const (c := Y))).continuous
  rw [fieldCellMean_add hf continuous_const, fieldCellMean_const]
  ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Full independent coefficient recursion retains the genuine input amplitude at one finite word price. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem independentCovariantStepReserve_uniform_budget (H : ℕ)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (F : ℕ → ℝ → Vec 2 → P → E) (k : Fin 2) (j : ℕ)
    (QF : ∀ i, IndependentParameterSourceReserve (H + 1) (F i))
    (θ B : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQF : ∀ i r, r ≤ H + 1 → (QF i).budget r ≤ θ * B) (r : ℕ) (hr : r ≤ H) :
    (independentCovariantStepReserve H L hL A η F k j QF).budget r ≤
      θ * ((1 + ‖Real.sqrt η • ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖)) * B) := by
  unfold independentCovariantStepReserve
  split_ifs with hj
  · rw [IndependentParameterSourceReserve.congrSource_budget]
    have hf := (QF j).fastPartial_uniform_budget θ B (hQF j) H (by omega) k r hr
    have hC : 1 ≤ 1 + ‖Real.sqrt η • ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖) :=
      le_add_of_nonneg_right (mul_nonneg (norm_nonneg _)
        (add_nonneg zero_le_one (norm_nonneg A)))
    have hm := mul_le_mul_of_nonneg_right hC (mul_nonneg hθ hB)
    rw [one_mul] at hm
    exact hf.trans (hm.trans_eq (by ring))
  · dsimp only
    rw [IndependentParameterSourceReserve.congrSource_budget]
    change ((QF j).fastPartial H _ k).budget r +
      ‖Real.sqrt η • ContinuousLinearMap.id ℝ E‖ *
        ((QF (j - 1)).covariantSlow H _ L hL A k).budget r ≤ _
    have hf := (QF j).fastPartial_uniform_budget θ B (hQF j) H (by omega) k r hr
    have hs := (QF (j - 1)).covariantSlow_uniform_budget θ B (hQF (j - 1))
      H (by omega) L hL A k r hr
    exact (add_le_add hf (mul_le_mul_of_nonneg_left hs (norm_nonneg _))).trans_eq (by ring)

theorem IndependentParameterSourceReserve.covariantList_uniform_budget {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (θ B : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B)
    (R : ℕ) (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ) (w : List (Fin 2)) (hR : w.length + R ≤ H)
    (j : ℕ) (r : ℕ) (hr : r ≤ R) :
    (Q.covariantList R L hL A η w hR j).budget r ≤
      θ * ((1 + ‖Real.sqrt η • ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖)) ^ w.length * B) := by
  let C := 1 + ‖Real.sqrt η • ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖)
  have hC : 0 ≤ C := add_nonneg zero_le_one
    (mul_nonneg (norm_nonneg _) (add_nonneg zero_le_one (norm_nonneg A)))
  induction w using List.reverseRecOn generalizing R j r with
  | nil =>
    simp only [IndependentParameterSourceReserve.covariantList, List.reverseRecOn_nil]
    split_ifs with hj
    · rw [IndependentParameterSourceReserve.congrSource_budget]
      change Q.budget r ≤ _
      simpa only [List.length_nil, pow_zero, one_mul] using hQ r (by simp only [List.length_nil, zero_add] at hR; omega)
    · rw [IndependentParameterSourceReserve.congrSource_budget]
      change 0 ≤ θ * (_ ^ 0 * B)
      rw [pow_zero, one_mul]
      exact mul_nonneg hθ hB
  | append_singleton w k ih =>
    have hw : w.length + (R + 1) ≤ H := by
      simp only [List.length_append, List.length_singleton] at hR
      omega
    simp only [IndependentParameterSourceReserve.covariantList, List.reverseRecOn_concat]
    rw [IndependentParameterSourceReserve.congrSource_budget]
    have hh := independentCovariantStepReserve_uniform_budget R L hL A η
      (independentCovariantListCoefficients L A η w f) k j
      (fun i => Q.covariantList (R + 1) L hL A η w hw i)
      θ (C ^ w.length * B) hθ (mul_nonneg (pow_nonneg hC _) hB)
      (fun i s hs => ih (R + 1) hw i s hs) r hr
    apply hh.trans_eq
    simp only [List.length_append, List.length_singleton, pow_succ]
    dsimp only [C]
    ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! A coherently produced native mean becomes the literal signed physical flux source. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentProducedFluxSource (c : ℝ) (clock : ℝ → ℝ)
    (f : ℝ → Vec 2 → P → Vec 2) : ℝ → Vec 2 → P → Vec 2 :=
  fun t z Y => (-c) • f (clock t) z Y

def independentProducedFluxReserve (H : ℕ) (c : ℝ) (clock : ℝ → ℝ) (hclock : Measurable clock)
    (f : ℝ → Vec 2 → P → Vec 2) (Q : IndependentParameterSourceReserve H f) :
    IndependentParameterSourceReserve H (independentProducedFluxSource c clock f) :=
  (Q.timeReparam clock hclock).constSmul (-c)

theorem independentProducedFluxReserve_budget (H : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (clock : ℝ → ℝ) (hclock : Measurable clock)
    (f : ℝ → Vec 2 → P → Vec 2) (Q : IndependentParameterSourceReserve H f)
    (θ B : ℝ) (hQ : ∀ n ≤ H, Q.budget n ≤ θ * B) (n : ℕ) (hn : n ≤ H) :
    (independentProducedFluxReserve H c clock hclock f Q).budget n ≤ θ * (c * B) := by
  change |-c| * Q.budget n ≤ _
  rw [abs_neg, abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left (hQ n hn) hc).trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! A produced small-response production also supplies the unscaled predecessor reserve without
changing its field. -/

variable {ι : Type*} {d H n m : ℕ} {a b θ w C : ℝ} {U : Set (Vec d)}
  {c : Vec d → LiftCoeff ι (fun _ => ℝ)} {slowPoint : Vec d → Vec 2}
  {α : DerivativeWord2 m} {v u : ι}

def IndependentScalarCoefficientProduction.forgetResponse
    (P : IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u (θ * w) C)
    (hθ : θ ≤ 1) (hw : 0 ≤ w) (hC : 0 ≤ C) :
    IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u w C where
  field := P.field
  reserve := P.reserve
  bound k hk := (P.bound k hk).trans (by
    rw [mul_assoc]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ (mul_nonneg hw hC))
  copy := P.copy
  mean_zero := P.mean_zero
  past_zero := P.past_zero

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Independent cell means and centering retain one menu price and the stored amplitude. -/

variable {d H : ℕ} {f : ℝ → Vec 2 → Vec d → ℝ}

theorem independentSourceMenuBudget_uniform_le (Q : IndependentParameterSourceReserve H f)
    (θ B : ℝ) (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B) :
    independentSourceMenuBudget Q ≤ θ * ((H + 1 : ℕ) * B) := by
  unfold independentSourceMenuBudget
  apply (Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hQ r.val (by omega))).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem IndependentParameterSourceReserve.mean_uniform_budget (Q : IndependentParameterSourceReserve H f)
    (θ B : ℝ) (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B)
    (r : ℕ) (hr : r ≤ H) :
    Q.mean.budget r ≤ θ * (((d : ℝ) + 1) ^ H * ((H + 1 : ℕ) * B)) := by
  change (d : ℝ) ^ r * independentSourceMenuBudget Q ≤ _
  have hp : (d : ℝ) ^ r ≤ ((d : ℝ) + 1) ^ H :=
    (pow_le_pow_left₀ (show (0 : ℝ) ≤ (d : ℝ) by positivity)
      (le_add_of_nonneg_right zero_le_one) r).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)) hr)
  have hh := mul_le_mul hp (independentSourceMenuBudget_uniform_le Q θ B hQ)
    (by unfold independentSourceMenuBudget; exact Finset.sum_nonneg (fun _ _ => Q.budget_nonneg _))
    (pow_nonneg (by positivity) H)
  exact hh.trans_eq (by ring)

theorem IndependentParameterSourceReserve.center_uniform_budget (Q : IndependentParameterSourceReserve H f)
    (θ B : ℝ) (hQ : ∀ r ≤ H, Q.budget r ≤ θ * B)
    (r : ℕ) (hr : r ≤ H) :
    Q.center.budget r ≤ θ * ((1 + ((d : ℝ) + 1) ^ H * (H + 1 : ℕ)) * B) := by
  rw [IndependentParameterSourceReserve.center_budget, ContinuousLinearMap.norm_id, one_mul]
  have hh := Q.mean_uniform_budget θ B hQ r hr
  exact (add_le_add (hQ r hr) hh).trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! The actual molecular construction solves the regular scalar inverse. -/

theorem dataRegular_scalar_inverse {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (hvD : IsCellDrift P.v) (K r : ℕ)
    (hr : r + 2 ≤ K) (hK : 3 ≤ K) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (c₀ : Vec 2 → ℝ) (g : ℝ → Vec 2 → ℝ) (Ng : ℝ)
    (hc₀ : ContDiff ℝ (K : ℕ∞) c₀) (hp₀ : AVenhance.IsZ2Periodic c₀)
    (hm₀ : ∫ x in AVenhance.unitCube, c₀ x = 0)
    (hgm : Measurable (Function.uncurry g))
    (hgc : ∀ t, ContDiff ℝ (K : ℕ∞) (g t))
    (hgp : ∀ t, AVenhance.IsZ2Periodic (g t))
    (hgb : ∀ t j, j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (g t) x‖ ≤ Ng)
    (hg₀ : ∀ t, ∫ x in AVenhance.unitCube, g t x = 0) :
    ∃ c : ℝ → Vec 2 → ℝ, IsCellFieldInverse P.G P.v r a b c₀ g c := by
  let u₀ : TorusHk K ℂ :=
    (TorusHkFunction.mk (complexFiniteJet K c₀)
      (complexFiniteJet_periodicWeak K c₀ hc₀ hp₀)).toHk
  have h₀ : (torusHkValueCLM u₀ : Vec 2 → ℂ) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => (c₀ x : ℂ) := by
    exact torusJetToL2_ae _ (complexFiniteJet_periodicWeak K c₀ hc₀ hp₀).2.1 (valueIndex2 K)
  have hg := complexFiniteJet_memLp K a b g hgc hgm Ng hgb (valueIndex2 K)
  let S := dataHkSlice K (fun t => complexFiniteJet K (g t))
  obtain ⟨u, slice, hu, heq, hi, hh, hreal⟩ := dataRegular_exists_trace hab P K Cv hCv
    hv hp hb g hgm hg S (complexFiniteData_memLp K a b g hgc hgm Ng hgb)
    (complexFiniteData_value K g hgc hgp) u₀ c₀ h₀
  have hmax : max r 1 + 2 ≤ K := by omega
  obtain ⟨hc, hD, he⟩ := dataRegular_classical_solution P K (max r 1) hmax
    (Nat.le_max_right _ _) (fun t x => (g t x : ℂ)) hg u slice hu heq hh hreal
  have hinit : (u a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (c₀ x : ℂ) := by
    rw [hi]
    exact h₀
  have hmean := dataWeak_classical_mean_zero hab P hvD g hg hg₀ u slice heq
    ((integral_congr_ae hinit).trans (realCellMean_zero c₀ hm₀))
    (cellClassicalWindow a b u) he
  refine ⟨cellClassicalWindow a b u, scalarFieldInverse_of_id hab P.G P.v r c₀ g _
    (fun t _ => (hc t).of_le (by exact_mod_cast Nat.le_max_left r 1)) hD hmean ?_⟩
  exact (he a ⟨le_rfl, hab⟩).symm.trans hinit

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Genuine mixed reserves produce uniformly priced coordinate-word source quotients. -/

variable {d H : ℕ}

def coordinateWordQuotientHigherSourceData
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : ℝ → Vec 2 → Vec d → ComplexCellVector}
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (w : List (Fin d)) (K : ℕ) (hK : K + 1 + w.length ≤ H)
    (a b : ℝ) (Y : Vec d) (i : Fin d) (h : ℝ) (hh : h ≠ 0) :
    HigherSourceCarrierData (Set.Icc a b) K
      (h⁻¹ • ((fun t => cellQ0 (coordinateSourceWord f w (Y + h • basisVec i) t)) -
        (fun t => cellQ0 (coordinateSourceWord f w Y t))))
      (h⁻¹ • (coordinateSourceWord F w (Y + h • basisVec i) - coordinateSourceWord F w Y)) :=
  (Qf.wordJet w.length (K + 1) (by omega) (coordinateWordDirections w) (coordinateWordDirections_norm w)).quotientHigherSourceData
    (QF.wordJet w.length (K + 1) (by omega) (coordinateWordDirections w) (coordinateWordDirections_norm w))
    K (le_refl _) a b Y (basisVec i) (by simp [basisVec, Pi.norm_single]) h hh

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Birth-normalized stored parameters feed the parent chart through a norm-one scaled slice. -/

def independentFreshScaledStepCoordinates (r : ℕ) (ell : ℝ) :
    (Vec (4 * (r + 1)) × Vec 2) →L[ℝ] (Vec (4 * r) × (Vec 2 × (Vec 2 × Vec 2))) :=
  (centeredChildScaleCenterCoordinates ell).comp (independentFreshStepCoordinates r)

theorem independentFreshScaledStepCoordinates_norm_le (r : ℕ) (ell : ℝ) (hell : |ell| ≤ 1) :
    ‖independentFreshScaledStepCoordinates r ell‖ ≤ 1 := by
  have hh := ContinuousLinearMap.opNorm_comp_le
    (centeredChildScaleCenterCoordinates (P := Vec (4 * r)) (V := Vec 2) ell)
    (independentFreshStepCoordinates r)
  exact hh.trans ((mul_le_mul (centeredChildScaleCenterCoordinates_norm_le ell hell)
    (independentFreshStepCoordinates_norm_le r) (norm_nonneg _) zero_le_one).trans_eq (by norm_num))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Piola transport and measurable time windows preserve exact parameter translation invariance. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
theorem independentPiolaSource_translation (δ : P)
    (K : ℝ → Vec 2 → P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ t z Y h, K t z (Y + δ) h = K t z Y h)
    (Dγ r : ℕ) (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ → Vec 2 → P → Vec 2)
    (hB : ∀ d J, IndependentSourceTranslationInvariant δ (B d J)) (A : DerivativeWord2 r) :
    IndependentSourceTranslationInvariant δ
      (fun t z Y a => transportedCoeff (K t z Y) Dγ (fun d J => B d J t z Y) r A 0 a) := by
  intro t z Y
  have heK : K t z (Y + δ) = K t z Y := funext (hK t z Y)
  have heB : (fun d J => B d J t z (Y + δ)) = fun d J => B d J t z Y :=
    funext (fun d => funext (fun J => hB d J t z Y))
  dsimp only
  rw [heK, heB]

omit [NormedSpace ℝ P] in
theorem IndependentSourceTranslationInvariant.timeWindow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (δ : P)
    (I : Set ℝ) (f : ℝ → Vec 2 → P → E) (hf : IndependentSourceTranslationInvariant δ f) :
    IndependentSourceTranslationInvariant δ (independentTimeWindowSource I f) := by
  intro t z Y
  unfold independentTimeWindowSource
  rw [hf t z Y]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

/-! A shared time window and unit carrier cutoffs preserve a genuine metric slow-germ comparison. -/

theorem cutoff_clamped_metric_slow_slice_congr {d : ℕ}
    (χ ψ : Vec d → ℝ)
    (G F : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ)
    (L : Vec 2 →L[ℝ] Vec d) (U : Set (Vec 2)) (Y Z : Vec d)
    (hχ : ∀ X ∈ U, χ (L X + Y) = 1) (hψ : ∀ X ∈ U, ψ (L X + Z) = 1)
    (hG : ∀ i j, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t (_ : Vec 2) W => G t W i j) (fun t _ W => F t W i j)) (i j : Fin 2) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (fun t (_ : Vec 2) W => clampedParameterMetric (cutoffParameterMetric χ G) a b t W i j)
      (fun t _ W => clampedParameterMetric (cutoffParameterMetric ψ F) a b t W i j) := by
  intro t X hX z
  simp only [clampedParameterMetric, cutoffParameterMetric, hχ X hX, hψ X hX,
    one_smul, add_sub_cancel]
  exact hG i j _ X hX z

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Centering and the literal ordered mean corrections produce genuine independent inverse forcing. -/

variable {d H : ℕ}

def independentCenteredRecurrenceSource (hh n : ℕ)
    (f : ℝ → Vec 2 → Vec d → ℝ)
    (T : ℕ → (ℕ × ℕ) → ℝ → Vec 2 → Vec d → ℝ) (t : ℝ) (z : Vec 2) (Y : Vec d) : ℝ :=
  -(f t z Y - fieldCellMean (fun w => f t w Y)) +
    ∑ j ∈ Finset.Icc 1 (n - 2), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab t z Y

def independentCenteredRecurrenceSourceReserve (hh n : ℕ)
    (f : ℝ → Vec 2 → Vec d → ℝ)
    (T : ℕ → (ℕ × ℕ) → ℝ → Vec 2 → Vec d → ℝ)
    (Qf : IndependentParameterSourceReserve H f)
    (QT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      IndependentParameterSourceReserve H (T j ab)) :
    IndependentParameterSourceReserve H (independentCenteredRecurrenceSource hh n f T) :=
  (Qf.center.map (-ContinuousLinearMap.id ℝ ℝ)).add
    (IndependentParameterSourceReserve.finsetSum _ H _ (fun j hj =>
      IndependentParameterSourceReserve.finsetSum _ H _ (QT j hj)))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Canonical full-parameter productions retain symmetry, true reserves and actual coefficient
values. -/

variable {ι : Type*} {d H n : ℕ} {a b C : ℝ} {U : Set (Vec d)}
  {c : Vec d → LiftCoeff ι (fun _ => ℝ)} {slowPoint : Vec d → Vec 2} {M : ι → ι → ℝ}

def independentCoefficientProductionFields
    (P : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u (M v u) C) :
    ∀ m : ℕ, DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ :=
  fun m α t z Y v u => if hm : m ≤ n then (P m hm (canonicalDerivativeWord α) v u).field t z Y else 0

def independentCoefficientProductionFields_reserve
    (P : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u (M v u) C)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι) :
    IndependentParameterSourceReserve H (fun t z Y => independentCoefficientProductionFields P m α t z Y v u) :=
  (P m hm (canonicalDerivativeWord α) v u).reserve.congrSource (by
    funext t z Y
    simp only [independentCoefficientProductionFields, dite_eq_left hm])

theorem independentCoefficientProductionFields_bound
    (P : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u (M v u) C)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι) (r : ℕ) (hr : r ≤ H) :
    (independentCoefficientProductionFields_reserve P m hm α v u).budget r ≤ M v u * C := by
  rw [independentCoefficientProductionFields_reserve, IndependentParameterSourceReserve.congrSource_budget]
  exact (P m hm (canonicalDerivativeWord α) v u).bound r hr

theorem independentCoefficientProductionFields_copy
    (P : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u (M v u) C)
    (m : ℕ) (hm : m ≤ n)
    (hs : ∀ Y β (σ : Equiv.Perm (Fin m)), c Y m (β ∘ σ) = c Y m β)
    (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Icc a b)
    (Y : Vec d) (hY : Y ∈ U) (z : Vec 2) (v u : ι) :
    independentCoefficientProductionFields P m α t z Y v u = c Y m α t (slowPoint Y) z v u 1 := by
  rw [independentCoefficientProductionFields, dite_eq_left hm,
    (P m hm (canonicalDerivativeWord α) v u).copy t ht Y hY z]
  rw [symmetric_word_canonical_value (fun β => c Y m β) (hs Y) α]

theorem independentCoefficientProductionFields_mean_zero
    (P : ∀ m, m ≤ n → ∀ α : DerivativeWord2 m, ∀ v u,
      IndependentScalarCoefficientProduction d H n a b U c slowPoint m α v u (M v u) C)
    (hn : 1 ≤ n) (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m)
    (t : ℝ) (Y : Vec d) (v u : ι) :
    fieldCellMean (fun z => independentCoefficientProductionFields P m α t z Y v u) = 0 := by
  simp only [independentCoefficientProductionFields, dite_eq_left hm]
  exact (P m hm (canonicalDerivativeWord α) v u).mean_zero hn t Y

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Cell forcing is natural under equivalent open intrinsic slow slices. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {H : ℕ} {U : Set (Vec 2)}

theorem independentNormalizedCellB1Source_slow_slice_congr
    (L : Vec 2 →L[ℝ] P) (_hL : ‖L‖ ≤ 1) (Y Z : P)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G G' : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f g : ℝ → Vec 2 → P → E)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ W => G t W i j))
    (QG' : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ W => G' t W i j))
    (Qf : IndependentParameterSourceReserve (H + 2) f)
    (Qg : IndependentParameterSourceReserve (H + 2) g)
    (hU : IsOpen U)
    (hG : ∀ i j, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t (_ : Vec 2) W => G t W i j) (fun t _ W => G' t W i j))
    (hf : IndependentSourceSlowSliceEqOn L U Y Z f g) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentNormalizedCellB1Source L A η G v f)
      (independentNormalizedCellB1Source L A η G' v g) := by
  have hs i := hf.covariantSlow hU Qf Qg (by omega) A i
  have hfast i := hf.fastPartial i
  have hmix (i j : Fin 2) : IndependentSourceSlowSliceEqOn L U Y Z
      (fun t z W => G t W i j • fderiv ℝ (fun w => f t w W) z (basisVec j))
      (fun t z W => G' t W i j • fderiv ℝ (fun w => g t w W) z (basisVec j)) := by
    intro t X hX z
    dsimp only
    have hg := hG i j t X hX z
    dsimp only at hg
    have hff := hfast j t X hX z
    dsimp only at hff
    rw [hg, hff]
  have hdg (i j : Fin 2) := (hmix i j).covariantSlow hU
    ((QG i j).scalarProduct (Qf.fastPartial (H + 1) (by omega) j))
    ((QG' i j).scalarProduct (Qg.fastPartial (H + 1) (by omega) j)) (by omega) A i
  have hds (i j : Fin 2) := (hs j).fastPartial i
  dsimp only [IndependentSourceSlowSliceEqOn] at hG hs hds hdg
  intro t X hX z
  dsimp only [independentNormalizedCellB1Source]
  simp_rw [hs _ t X hX z, hG _ _ t X hX z, hds _ _ t X hX z, hdg _ _ t X hX z]

theorem independentNormalizedCellB2Source_slow_slice_congr
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (Y Z : P)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G G' : ℝ → P → Fin 2 → Fin 2 → ℝ)
    (f g : ℝ → Vec 2 → P → E)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ W => G t W i j))
    (QG' : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ W => G' t W i j))
    (Qf : IndependentParameterSourceReserve (H + 2) f)
    (Qg : IndependentParameterSourceReserve (H + 2) g)
    (hU : IsOpen U)
    (hG : ∀ i j, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t (_ : Vec 2) W => G t W i j) (fun t _ W => G' t W i j))
    (hf : IndependentSourceSlowSliceEqOn L U Y Z f g) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentNormalizedCellB2Source L A η G f)
      (independentNormalizedCellB2Source L A η G' g) := by
  have hs j := hf.covariantSlow hU Qf Qg (by omega) A j
  have hmix (i j : Fin 2) : IndependentSourceSlowSliceEqOn L U Y Z
      (fun t z W => G t W i j • independentSourceCovariantSlow L A j f t z W)
      (fun t z W => G' t W i j • independentSourceCovariantSlow L A j g t z W) := by
    intro t X hX z
    dsimp only
    have hg := hG i j t X hX z
    dsimp only at hg
    rw [hg, hs j t X hX z]
  have hm (i j : Fin 2) := (hmix i j).covariantSlow hU
    ((QG i j).scalarProduct (Qf.covariantSlow (H + 1) (by omega) L hL A j))
    ((QG' i j).scalarProduct (Qg.covariantSlow (H + 1) (by omega) L hL A j)) (by omega) A i
  dsimp only [IndependentSourceSlowSliceEqOn] at hm
  intro t X hX z
  dsimp only [independentNormalizedCellB2Source]
  simp_rw [hm _ _ t X hX z]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The molecular cell operators preserve every primitive stored-parameter translation. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independentNormalizedCellB1Source_translation_invariant
    (δ : P) (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → P → E)
    (hG : ∀ t Y i j, G t (Y + δ) i j = G t Y i j)
    (hf : IndependentSourceTranslationInvariant δ f) :
    IndependentSourceTranslationInvariant δ (independentNormalizedCellB1Source L A η G v f) := by
  have hg (i j : Fin 2) : IndependentSourceTranslationInvariant δ (fun t (_ : Vec 2) Y => G t Y i j) :=
    fun t _ Y => hG t Y i j
  have hs (i : Fin 2) := hf.covariantSlow L A i
  have hfast (i : Fin 2) := hf.fastPartial i
  have hmix (i j : Fin 2) := (hg i j).smul (hfast j)
  intro t z Y
  dsimp only [independentNormalizedCellB1Source]
  have hds (i j : Fin 2) := (hs j).fastPartial i t z Y
  dsimp only at hds
  have hdg (i j : Fin 2) := (hmix i j).covariantSlow L A i t z Y
  simp_rw [hs _ t z Y, hG t Y, hds, hdg]

theorem independentNormalizedCellB2Source_translation_invariant
    (δ : P) (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (f : ℝ → Vec 2 → P → E)
    (hG : ∀ t Y i j, G t (Y + δ) i j = G t Y i j)
    (hf : IndependentSourceTranslationInvariant δ f) :
    IndependentSourceTranslationInvariant δ (independentNormalizedCellB2Source L A η G f) := by
  have hg (i j : Fin 2) : IndependentSourceTranslationInvariant δ (fun t (_ : Vec 2) Y => G t Y i j) :=
    fun t _ Y => hG t Y i j
  have hm (i j : Fin 2) := ((hg i j).smul (hf.covariantSlow L A j)).covariantSlow L A i
  intro t z Y
  dsimp only [independentNormalizedCellB2Source]
  simp_rw [hm _ _ t z Y]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The centered ordered forcing has the literal mean and past-support properties needed by inverse production. -/

variable {d H : ℕ}

theorem independent_centered_recurrence_mean_zero (hh n : ℕ)
    (f : ℝ → Vec 2 → Vec d → ℝ)
    (T : ℕ → (ℕ × ℕ) → ℝ → Vec 2 → Vec d → ℝ)
    (Qf : IndependentParameterSourceReserve H f)
    (QT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      IndependentParameterSourceReserve H (T j ab))
    (hT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ t Y, fieldCellMean (fun z => T j ab t z Y) = 0) (t : ℝ) (Y : Vec d) :
    fieldCellMean (fun z => independentCenteredRecurrenceSource hh n f T t z Y) = 0 := by
  let S := IndependentParameterSourceReserve.finsetSum (Finset.Icc 1 (n - 2)) H
    (fun j t z Y => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab t z Y)
    (fun j hj => IndependentParameterSourceReserve.finsetSum _ H _ (QT j hj))
  have hc : Continuous (fun z => -(f t z Y - fieldCellMean (fun w => f t w Y))) :=
    ((Qf.center.regular t).comp₂ contDiff_id (contDiff_const (c := Y))).continuous.neg
  have hs : Continuous (fun z => ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab t z Y) :=
    ((S.regular t).comp₂ contDiff_id (contDiff_const (c := Y))).continuous
  unfold independentCenteredRecurrenceSource
  rw [fieldCellMean_add hc hs, fieldCellMean_neg, Qf.center_mean_zero, neg_zero, zero_add]
  have hjcont j (hj : j ∈ Finset.Icc 1 (n - 2)) :
      Continuous (fun z => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, T j ab t z Y) :=
    ((IndependentParameterSourceReserve.finsetSum _ H _ (QT j hj)).regular t).continuous.comp
      (continuous_id.prodMk (continuous_const (y := Y)))
  rw [fieldCellMean_sum _ hjcont]
  apply Finset.sum_eq_zero
  intro j hj
  have habcont ab (hab : ab ∈ Finset.HasAntidiagonal.antidiagonal hh) :
      Continuous (fun z => T j ab t z Y) :=
    ((QT j hj ab hab).regular t).continuous.comp
      (continuous_id.prodMk (continuous_const (y := Y)))
  rw [fieldCellMean_sum _ habcont]
  exact Finset.sum_eq_zero (fun ab hab => hT j hj ab hab t Y)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Separately priced ordered corrections retain the common stored amplitude under centering. -/

variable {d H : ℕ}

theorem independentCenteredRecurrenceSourceReserve_priced_budget (hh n : ℕ)
    (f : ℝ → Vec 2 → Vec d → ℝ)
    (T : ℕ → (ℕ × ℕ) → ℝ → Vec 2 → Vec d → ℝ)
    (Qf : IndependentParameterSourceReserve H f)
    (QT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      IndependentParameterSourceReserve H (T j ab)) (θ BF : ℝ) (BT : ℕ → (ℕ × ℕ) → ℝ)
    (hf : ∀ r ≤ H, Qf.budget r ≤ θ * BF)
    (ht : ∀ j hj ab hab r, r ≤ H → (QT j hj ab hab).budget r ≤ θ * BT j ab)
    (r : ℕ) (hr : r ≤ H) :
    (independentCenteredRecurrenceSourceReserve hh n f T Qf QT).budget r ≤ θ *
      ((1 + ((d : ℝ) + 1) ^ H * (H + 1 : ℕ)) * BF +
        ∑ j ∈ Finset.Icc 1 (n - 2), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, BT j ab) := by
  change ‖-ContinuousLinearMap.id ℝ ℝ‖ * Qf.center.budget r + _ ≤ _
  rw [norm_neg, ContinuousLinearMap.norm_id, one_mul,
    IndependentParameterSourceReserve.finsetSum_budget]
  have hs : (∑ j : Finset.Icc 1 (n - 2),
      (IndependentParameterSourceReserve.finsetSum _ H _ (QT j.val j.property)).budget r) ≤
      θ * ∑ j ∈ Finset.Icc 1 (n - 2), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, BT j ab := by
    have hi (j : Finset.Icc 1 (n - 2)) :
        (IndependentParameterSourceReserve.finsetSum _ H _ (QT j.val j.property)).budget r ≤
          ∑ ab : Finset.HasAntidiagonal.antidiagonal hh, θ * BT j.val ab.val := by
      rw [IndependentParameterSourceReserve.finsetSum_budget]
      exact Finset.sum_le_sum (fun ab (_ : ab ∈ Finset.univ) => ht j.val j.property ab.val ab.property r hr)
    apply (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hi j)).trans_eq
    have hinner (j : Finset.Icc 1 (n - 2)) :
        (∑ ab : Finset.HasAntidiagonal.antidiagonal hh, θ * BT j.val ab.val) =
          θ * ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, BT j.val ab := by
      rw [Finset.mul_sum]
      exact Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal hh) (fun ab => θ * BT j.val ab)
    have houter : (∑ j : Finset.Icc 1 (n - 2),
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, BT j.val ab) =
        ∑ j ∈ Finset.Icc 1 (n - 2), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, BT j ab :=
      Finset.sum_coe_sort (Finset.Icc 1 (n - 2))
        (fun j => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, BT j ab)
    calc
      _ = ∑ j : Finset.Icc 1 (n - 2), θ *
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, BT j.val ab :=
        Finset.sum_congr rfl (fun j _ => hinner j)
      _ = θ * ∑ j : Finset.Icc 1 (n - 2),
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh, BT j.val ab := (Finset.mul_sum ..).symm
      _ = _ := congrArg (fun x => θ * x) houter
  exact (add_le_add (Qf.center_uniform_budget θ BF hf r hr) hs).trans_eq (mul_add _ _ _).symm

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift Set
namespace AVRegularity.EntryWeakProofs

/-! Local finite calibration retains the global mean-free extensions needed by the next lift degree. -/

section
variable {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Fintype ι] [DecidableEq ι]

theorem independent_scalar_lift_calibration_meanfree_extension (H n m : ℕ) (hm : m ≤ n)
    (c : P → LiftCoeff ι (fun _ => ℝ)) (x : P → Vec 2)
    (hc : ∀ Y β (σ : Equiv.Perm (Fin m)), c Y m (β ∘ σ) = c Y m β)
    (α : DerivativeWord2 m) (a b lam : ℝ) (hlam : lam ≠ 0) (U : Set P) (v u : ι)
    (f : (Fin (m + 1) × Fin (n + 1)) → ℝ → Vec 2 → P → ℝ)
    (Q : ∀ p, IndependentParameterSourceReserve H (f p))
    (hf : ∀ p, ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
      f p t z Y = normalizedLiftTestField (c Y) n
        (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v 1 t (x Y) z)
    (hmean : ∀ p t Y, fieldCellMean (fun z => f p t z Y) = 0)
    (hpast : ∀ p t, t ≤ a → ∀ z Y, f p t z Y = 0) :
    ∃ (fext : ℝ → Vec 2 → P → ℝ) (Qext : IndependentParameterSourceReserve H fext),
      (∀ r, Qext.budget r = ∑ p : Fin (m + 1) × Fin (n + 1),
        ‖liftCalibrationWeight n m α lam p • ContinuousLinearMap.id ℝ ℝ‖ * (Q p).budget r) ∧
      (∀ t Y, fieldCellMean (fun z => fext t z Y) = 0) ∧
      (∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, fext t z Y = c Y m α t (x Y) z v u 1) ∧
      ∀ t, t ≤ a → ∀ z Y, fext t z Y = 0 := by
  let L := fun p : Fin (m + 1) × Fin (n + 1) =>
    liftCalibrationWeight n m α lam p • ContinuousLinearMap.id ℝ ℝ
  let fext := fun t z Y => ∑ p : Fin (m + 1) × Fin (n + 1), L p (f p t z Y)
  obtain ⟨Qext, hQ⟩ := independentSourceReserve_sum_with_budget Finset.univ H
    (fun p t z Y => L p (f p t z Y)) (fun p => (Q p).map (L p))
  refine ⟨fext, Qext, hQ, ?_, ?_, ?_⟩
  · intro t Y
    change fieldCellMean (fun z => ∑ p, L p (f p t z Y)) = 0
    rw [fieldCellMean_sum Finset.univ (f := fun p z => L p (f p t z Y))
      (fun p _ => (L p).continuous.comp
      ((Q p).regular t |>.comp₂ contDiff_id (contDiff_const (c := Y))).continuous)]
    apply Finset.sum_eq_zero
    intro p _
    have hfast : Continuous (fun z => f p t z Y) :=
      ((Q p).regular t |>.comp₂ contDiff_id (contDiff_const (c := Y))).continuous
    have he : fieldCellMean (fun z => L p (f p t z Y)) =
        L p (fieldCellMean (fun z => f p t z Y)) := fieldCellMean_clm (L p) hfast
    rw [he, hmean p t Y, map_zero]
  · intro t ht Y hY z
    dsimp only [fext]
    simp only [hf _ t ht Y hY z, L, smul_apply, ContinuousLinearMap.id_apply]
    exact liftCalibration_synthesis n m hm (c Y) lam hlam (hc Y) α t (x Y) z v u 1
  · intro t ht z Y
    simp only [fext, hpast _ t ht z Y, map_zero, Finset.sum_const_zero]
end

/-! Local finite calibration retains the global mean-free extensions needed by the next lift degree. -/

section
variable {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Fintype ι] [DecidableEq ι]

theorem independent_scalar_lift_calibration_explicit_natural_meanfree_extension (H n m : ℕ) (hm : m ≤ n)
    (c : P → LiftCoeff ι (fun _ => ℝ)) (x : P → Vec 2)
    (hc : ∀ Y β (σ : Equiv.Perm (Fin m)), c Y m (β ∘ σ) = c Y m β)
    (α : DerivativeWord2 m) (a b lam : ℝ) (hlam : lam ≠ 0) (U : Set P) (v u : ι)
    (f : (Fin (m + 1) × Fin (n + 1)) → ℝ → Vec 2 → P → ℝ)
    (Q : ∀ p, IndependentParameterSourceReserve H (f p))
    (hf : ∀ p, ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
      f p t z Y = normalizedLiftTestField (c Y) n
        (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v 1 t (x Y) z)
    (hmean : ∀ p t Y, fieldCellMean (fun z => f p t z Y) = 0)
    (Rel : P → P → Prop)
    (hnat : ∀ p t Y Z, Rel Y Z → ∀ z, f p t z Y = f p t z Z)
    (hpast : ∀ p t, t ≤ a → ∀ z Y, f p t z Y = 0) :
    ∃ (fext : ℝ → Vec 2 → P → ℝ) (Qext : IndependentParameterSourceReserve H fext),
      (∀ r, Qext.budget r = ∑ p : Fin (m + 1) × Fin (n + 1),
        ‖liftCalibrationWeight n m α lam p • ContinuousLinearMap.id ℝ ℝ‖ * (Q p).budget r) ∧
      (∀ t Y, fieldCellMean (fun z => fext t z Y) = 0) ∧
      (∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, fext t z Y = c Y m α t (x Y) z v u 1) ∧
      (∀ t, t ≤ a → ∀ z Y, fext t z Y = 0) ∧
      (∀ t Y Z, Rel Y Z → ∀ z, fext t z Y = fext t z Z) ∧
      fext = (fun t z Y => ∑ p : Fin (m + 1) × Fin (n + 1),
        (liftCalibrationWeight n m α lam p • ContinuousLinearMap.id ℝ ℝ) (f p t z Y)) := by
  let L := fun p : Fin (m + 1) × Fin (n + 1) =>
    liftCalibrationWeight n m α lam p • ContinuousLinearMap.id ℝ ℝ
  let fext := fun t z Y => ∑ p : Fin (m + 1) × Fin (n + 1), L p (f p t z Y)
  obtain ⟨Qext, hQ⟩ := independentSourceReserve_sum_with_budget Finset.univ H
    (fun p t z Y => L p (f p t z Y)) (fun p => (Q p).map (L p))
  refine ⟨fext, Qext, hQ, ?_, ?_, ?_, ?_, rfl⟩
  · intro t Y
    change fieldCellMean (fun z => ∑ p, L p (f p t z Y)) = 0
    rw [fieldCellMean_sum Finset.univ (f := fun p z => L p (f p t z Y))
      (fun p _ => (L p).continuous.comp
      ((Q p).regular t |>.comp₂ contDiff_id (contDiff_const (c := Y))).continuous)]
    apply Finset.sum_eq_zero
    intro p _
    have hfast : Continuous (fun z => f p t z Y) :=
      ((Q p).regular t |>.comp₂ contDiff_id (contDiff_const (c := Y))).continuous
    have he : fieldCellMean (fun z => L p (f p t z Y)) =
        L p (fieldCellMean (fun z => f p t z Y)) := fieldCellMean_clm (L p) hfast
    rw [he, hmean p t Y, map_zero]
  · intro t ht Y hY z
    dsimp only [fext]
    simp only [hf _ t ht Y hY z, L, smul_apply, ContinuousLinearMap.id_apply]
    exact liftCalibration_synthesis n m hm (c Y) lam hlam (hc Y) α t (x Y) z v u 1
  · intro t ht z Y
    simp only [fext, hpast _ t ht z Y, map_zero, Finset.sum_const_zero]

  · intro t Y Z hYZ z
    dsimp only [fext]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hnat p t Y Z hYZ z]
end

end AVRegularity.EntryWeakProofs
end
